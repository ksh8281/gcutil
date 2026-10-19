/*
 * Cross-isolate write recovery for GC_THREAD_ISOLATE + MPROTECT_VDB builds.
 * See include/private/vdb_isolate.h for the design.
 *
 * GC_THREAD_ISOLATE makes every other GC data structure (heap sections,
 * dirty bitmap, header table, ...) thread-local, so none of it can be
 * used to recognize a page that belongs to a *different* thread's heap.
 * The registries below are the only process-global (non-TLS) state this
 * scheme needs, and none of it is on any allocation hot path: heap
 * sections are added once per mmap'd chunk, committed/decommitted state
 * only changes when a block is actually (de)committed with the OS, and
 * the pending queue is touched only for faults this thread's own lookup
 * already failed to resolve.
 *
 * Both registries are plain malloc()/realloc()'d arrays, not fixed-size
 * static tables: GC_THREAD_ISOLATE + MPROTECT_VDB already requires an
 * environment with a working mprotect()/SIGSEGV, which means a full
 * libc with malloc() is available too, so there is no reason to impose
 * an arbitrary compile-time cap on how many heap sections or pending
 * faults this scheme can track.
 *
 * GC_write_fault_handler (os_dep.c) takes range_lock/pending_lock from
 * inside a SIGSEGV/SIGBUS handler (or, on ANY_MSWIN, a vectored
 * exception handler running on the faulting thread), so a plain,
 * non-reentrant lock is only safe here because none of these locks'
 * critical sections ever touch VDB-protected memory: a fault can only
 * re-enter this file while the faulting thread already holds one of
 * these locks if that critical section itself takes a fault, and
 * register_heap_sect()/note_unmap()/note_remap()/classify_fault()/
 * drain_pending() only ever read or write the process-global registries
 * below and locals, never a mprotect'd heap page. That rules out
 * same-thread reentrant self-deadlock. Cross-thread deadlock (another
 * isolate pausing this one while it holds a lock) is separately ruled
 * out because GC_THREAD_ISOLATE and GC_THREADS -- hence
 * stop-the-world -- are mutually exclusive at compile time (gcconfig.h).
 *
 * GC_isolate_vdb_push_pending() (the one entry point reached from inside
 * the fault handler) can grow pending_queue via realloc(), which raises
 * a similar question for libc's own allocator lock: could the faulting
 * thread already hold it? No -- the fault here is synchronous on a
 * specific store instruction into a mprotect'd GC heap page, so the
 * thread is executing *that* instruction, not sitting inside malloc's
 * own bookkeeping (which never writes into a GC-managed heap section).
 * A SIGSEGV/SIGBUS on such a store cannot itself originate from inside
 * a malloc() call on the same thread, so realloc() here cannot
 * self-deadlock on libc's allocator lock either.
 */
#include "private/vdb_isolate.h"
#include <stdlib.h>

#if defined(GC_THREAD_ISOLATE) && defined(MPROTECT_VDB)

/* This file's locks guard only the process-global registries below,
   never GC_THREADS-managed state, so they are independent of (and must
   work without) the GC_THREADS-only lock abstraction in gc_locks.h --
   GC_THREAD_ISOLATE and GC_THREADS are mutually exclusive (gcconfig.h).
   windows.h (for ANY_MSWIN builds) is already pulled in by gc_priv.h
   unconditionally, so SRWLOCK is available without linking pthreads,
   which Windows builds of this project do not otherwise use. */
#  ifdef ANY_MSWIN
typedef SRWLOCK GC_isolate_mutex_t;
#    define GC_ISOLATE_MUTEX_INITIALIZER SRWLOCK_INIT
#    define GC_isolate_mutex_lock(m) AcquireSRWLockExclusive(m)
#    define GC_isolate_mutex_unlock(m) ReleaseSRWLockExclusive(m)
#  else
#    include <pthread.h>
typedef pthread_mutex_t GC_isolate_mutex_t;
#    define GC_ISOLATE_MUTEX_INITIALIZER PTHREAD_MUTEX_INITIALIZER
#    define GC_isolate_mutex_lock(m) pthread_mutex_lock(m)
#    define GC_isolate_mutex_unlock(m) pthread_mutex_unlock(m)
#  endif

/* Starting element count for either registry's backing array, first
   allocated on its first use; both grow by doubling afterward. */
#  ifndef GC_ISOLATE_INITIAL_CAPACITY
#    define GC_ISOLATE_INITIAL_CAPACITY 256
#  endif

/*
 * A sorted registry of the original, disjoint heap sections.  A bitmap
 * records committed state per HBLKSIZE block; OS unmap/remap boundaries
 * are multiples of HBLKSIZE.  Changing state never splits a registry
 * entry or moves its tail.  An address outside these sections remains
 * UNKNOWN, while a cleared bit identifies decommitted memory.
 *
 * GC_remap() is not guaranteed to be called with the exact same (start,
 * bytes) as the GC_unmap() that decommitted that memory -- blocks can
 * be split/merged in between (allchblk.c) -- so this is modeled as
 * proper interval state, not as a set of (un)commit events paired up by
 * matching address+length. GC_isolate_vdb_note_unmap()/_remap() mark an
 * arbitrary block-aligned sub-range's committed state without changing
 * section boundaries, so a remap of different shape than the unmap that
 * preceded it still lands on the correct final state everywhere.
 */
typedef struct {
  ptr_t start;
  ptr_t end; /*< exclusive */
  unsigned char *committed;
} GC_isolate_range;

/* Marks a page dirty in the *calling* thread's own TLS bitmap, bypassing
   the GC_manual_vdb assertion in GC_dirty_inner() -- this path is only
   ever reached by an isolate draining pages it just confirmed (via
   GC_find_header()) are its own, regardless of whether manual VDB mode
   is enabled for it. Defined in os_dep.c, where async_set_pht_entry_
   from_index()/PHT_HASH() are visible. */
GC_INNER void GC_isolate_dirty_page(const void *p);

static GC_isolate_mutex_t range_lock = GC_ISOLATE_MUTEX_INITIALIZER;
static GC_isolate_range *range_registry = NULL;
static size_t range_count = 0;
STATIC MAY_THREAD_LOCAL GC_bool isolate_has_registered_ranges = FALSE;
static size_t range_capacity = 0;
/* Once foreign recovery has changed an owner's physical permissions,
   its private protection bitmap is no longer sufficient to skip RO
   syscalls.  Keep that optimization disabled for the process lifetime. */
/* Keep the before/after permission checks ordered without entering the
   registry lock.  Fault recovery must never use an emulated atomic lock. */
#  if defined(__ATOMIC_SEQ_CST) && defined(__GCC_ATOMIC_CHAR_LOCK_FREE) \
      && __GCC_ATOMIC_CHAR_LOCK_FREE == 2
#    define GC_ISOLATE_ATOMIC_FOREIGN_WRITES
#  endif
static unsigned char foreign_writes_seen = FALSE;

static GC_isolate_mutex_t pending_lock = GC_ISOLATE_MUTEX_INITIALIZER;
static ptr_t *pending_queue = NULL;
static size_t pending_count = 0;
static size_t pending_capacity = 0;

/* Must be called with range_lock held. Ensures range_registry has room
   for range_count + `needed` entries, growing it via realloc() (by
   doubling) if not. Returns FALSE, leaving range_registry/range_capacity
   untouched, if the allocation fails. */
static GC_bool
ensure_range_capacity_locked(size_t needed)
{
  size_t new_capacity;
  GC_isolate_range *new_registry;

  if (range_count + needed <= range_capacity)
    return TRUE;
  new_capacity
      = 0 == range_capacity ? GC_ISOLATE_INITIAL_CAPACITY : range_capacity * 2;
  while (new_capacity < range_count + needed)
    new_capacity *= 2;
  new_registry = (GC_isolate_range *)realloc(
      range_registry, new_capacity * sizeof(GC_isolate_range));
  if (NULL == new_registry)
    return FALSE;
  range_registry = new_registry;
  range_capacity = new_capacity;
  return TRUE;
}

/* Same as ensure_range_capacity_locked(), for pending_queue; must be
   called with pending_lock held. */
static GC_bool
ensure_pending_capacity_locked(size_t needed)
{
  size_t new_capacity;
  ptr_t *new_queue;

  if (pending_count + needed <= pending_capacity)
    return TRUE;
  new_capacity = 0 == pending_capacity ? GC_ISOLATE_INITIAL_CAPACITY
                                        : pending_capacity * 2;
  while (new_capacity < pending_count + needed)
    new_capacity *= 2;
  new_queue = (ptr_t *)realloc(pending_queue, new_capacity * sizeof(ptr_t));
  if (NULL == new_queue)
    return FALSE;
  pending_queue = new_queue;
  pending_capacity = new_capacity;
  return TRUE;
}

/* Both registries preserve address order at every mutation. */
static size_t
first_range_ending_after(ptr_t address)
{
  size_t low = 0, high = range_count;
  while (low < high) {
    size_t mid = low + (high - low) / 2;
    if (ADDR_GE(address, range_registry[mid].end))
      low = mid + 1;
    else
      high = mid;
  }
  return low;
}

static size_t
first_range_starting_at_or_after(ptr_t address)
{
  size_t low = 0, high = range_count;
  while (low < high) {
    size_t mid = low + (high - low) / 2;
    if (ADDR_LT(range_registry[mid].start, address))
      low = mid + 1;
    else
      high = mid;
  }
  return low;
}

/* Sorted unique pending pages: no FIFO ordering is required. */
static size_t
first_pending_at_or_after(ptr_t address)
{
  size_t low = 0, high = pending_count;
  while (low < high) {
    size_t mid = low + (high - low) / 2;
    if (ADDR_LT(pending_queue[mid], address))
      low = mid + 1;
    else
      high = mid;
  }
  return low;
}

/* Update only registered blocks; gaps keep their UNKNOWN classification.
   Must be called with range_lock held.  Metadata is allocated only when
   registering a section, never while changing committed state. */
static void
mark_range_locked(ptr_t start, ptr_t end, GC_bool committed)
{
  size_t i = first_range_ending_after(start);

  for (; i < range_count && ADDR_LT(range_registry[i].start, end); ++i) {
    GC_isolate_range *range = &range_registry[i];
    ptr_t begin = ADDR_LT(start, range->start) ? range->start : start;
    ptr_t stop = ADDR_LT(end, range->end) ? end : range->end;
    size_t first = divHBLKSZ((size_t)(begin - range->start));
    size_t last = divHBLKSZ((size_t)(stop - range->start));

    GC_ASSERT((size_t)(begin - range->start) % HBLKSIZE == 0);
    GC_ASSERT((size_t)(stop - range->start) % HBLKSIZE == 0);
    while (first < last && (first & 7) != 0) {
      unsigned char mask = (unsigned char)(1U << (first & 7));
      if (committed)
        range->committed[first >> 3] |= mask;
      else
        range->committed[first >> 3] &= (unsigned char)~mask;
      ++first;
    }
    if (last - first >= 8) {
      size_t bytes = (last - first) / 8;
      memset(range->committed + (first >> 3), committed ? 0xff : 0, bytes);
      first += bytes * 8;
    }
    while (first < last) {
      unsigned char mask = (unsigned char)(1U << (first & 7));
      if (committed)
        range->committed[first >> 3] |= mask;
      else
        range->committed[first >> 3] &= (unsigned char)~mask;
      ++first;
    }
  }
}

/* Remove an original heap section at isolate deinitialization.  Sections
   retain their registration boundaries even after arbitrary remaps. */
static void
delete_range_locked(ptr_t start, ptr_t end)
{
  size_t index = first_range_ending_after(start);

  if (index == range_count || ADDR_GE(range_registry[index].start, end))
    return;
  GC_ASSERT(range_registry[index].start == start);
  GC_ASSERT(range_registry[index].end == end);
  free(range_registry[index].committed);
  memmove(&range_registry[index], &range_registry[index + 1],
          (range_count - index - 1) * sizeof(*range_registry));
  --range_count;
}

GC_INNER void
GC_isolate_vdb_register_heap_sect(ptr_t start, size_t bytes)
{
  /* Keep registered sections tracked even after a VMA-limit fallback
     disables incremental mode.  Reserve their bitmap before publishing
     the section, so allocation failure leaves its addresses UNKNOWN. */
  if (!GC_incremental && !GC_incremental_start_pending)
    return;
  GC_isolate_mutex_lock(&range_lock);
  {
    size_t index = first_range_starting_at_or_after(start);
    size_t bitmap_bytes = (divHBLKSZ(bytes) + 7) / 8;
    ptr_t end = start + bytes;
    unsigned char *committed;

    GC_ASSERT(bytes % HBLKSIZE == 0);
    GC_ASSERT(index == 0 || ADDR_GE(start, range_registry[index - 1].end));
    GC_ASSERT(index == range_count || ADDR_GE(range_registry[index].start, end));
    committed = (unsigned char *)malloc(bitmap_bytes);
    if (committed != NULL) {
      if (ensure_range_capacity_locked(1)) {
        memset(committed, 0xff, bitmap_bytes);
        memmove(&range_registry[index + 1], &range_registry[index],
                (range_count - index) * sizeof(*range_registry));
        range_registry[index].start = start;
        range_registry[index].end = end;
        range_registry[index].committed = committed;
        ++range_count;
        isolate_has_registered_ranges = TRUE;
      } else {
        free(committed);
      }
    }
  }
  GC_isolate_mutex_unlock(&range_lock);
}

/* The caller holds range_lock and has checked the block is in range. */
static GC_bool
block_is_committed(const GC_isolate_range *range, size_t block)
{
  return (range->committed[block >> 3] & (1U << (block & 7))) != 0;
}

static size_t
committed_begin(const GC_isolate_range *range, size_t block)
{
  while (block != 0) {
    if ((block & 7) == 0 && range->committed[(block >> 3) - 1] == 0xff) {
      block -= 8;
    } else if (block_is_committed(range, block - 1)) {
      --block;
    } else {
      break;
    }
  }
  return block;
}

static size_t
committed_end(const GC_isolate_range *range, size_t block)
{
  size_t blocks = divHBLKSZ((size_t)(range->end - range->start));

  while (block < blocks) {
    if ((block & 7) == 0 && blocks - block >= 8
        && range->committed[block >> 3] == 0xff) {
      block += 8;
    } else if (block_is_committed(range, block)) {
      ++block;
    } else {
      break;
    }
  }
  return block;
}

GC_INNER void
GC_isolate_vdb_note_unmap(ptr_t start, size_t bytes)
{
  /* See the comment in GC_isolate_vdb_register_heap_sect(): a section
     never registered (because GC_incremental was off when it was added)
     has nothing to update here either. */
  if (!isolate_has_registered_ranges || NULL == start || 0 == bytes)
    return;
  GC_isolate_mutex_lock(&range_lock);
  mark_range_locked(start, start + bytes, FALSE);
  GC_isolate_mutex_unlock(&range_lock);
}

GC_INNER void
GC_isolate_vdb_note_remap(ptr_t start, size_t bytes)
{
  if (!isolate_has_registered_ranges || NULL == start || 0 == bytes)
    return;
  GC_isolate_mutex_lock(&range_lock);
  mark_range_locked(start, start + bytes, TRUE);
  GC_isolate_mutex_unlock(&range_lock);
}

GC_INNER GC_isolate_vdb_fault_kind
GC_isolate_vdb_classify_fault(const void *addr)
{
  ptr_t a = (ptr_t)addr;
  GC_isolate_vdb_fault_kind result = GC_ISOLATE_VDB_UNKNOWN;

  GC_isolate_mutex_lock(&range_lock);
  if (range_count > 0) {
    size_t low = 0;
    size_t high = range_count;
    while (low < high) {
      size_t mid = low + (high - low) / 2;
      if (a >= range_registry[mid].start && a < range_registry[mid].end) {
        size_t block = divHBLKSZ((size_t)(a - range_registry[mid].start));
        result = block_is_committed(&range_registry[mid], block)
                     ? GC_ISOLATE_VDB_CROSS_ISOLATE
                     : GC_ISOLATE_VDB_DECOMMITTED;
        break;
      } else if (a < range_registry[mid].start) {
        high = mid;
      } else {
        low = mid + 1;
      }
    }
  }
  GC_isolate_mutex_unlock(&range_lock);
  return result;
}

GC_INNER GC_bool
GC_isolate_vdb_committed_bounds(const void *addr, ptr_t *start, ptr_t *end)
{
  ptr_t a = (ptr_t)addr;
  GC_bool found = FALSE;
  size_t high;

  GC_isolate_mutex_lock(&range_lock);
  high = first_range_ending_after(a);
  if (high < range_count && ADDR_GE(a, range_registry[high].start)) {
    size_t block = divHBLKSZ((size_t)(a - range_registry[high].start));
    if (block_is_committed(&range_registry[high], block)) {
      const GC_isolate_range *range = &range_registry[high];
      size_t first = committed_begin(range, block);
      size_t last = committed_end(range, block + 1);
      size_t index = high;

      *start = range->start + first * HBLKSIZE;
      *end = range->start + last * HBLKSIZE;
      while (first == 0 && index > 0
             && range_registry[index - 1].end == *start) {
        range = &range_registry[--index];
        first = committed_begin(
            range, divHBLKSZ((size_t)(range->end - range->start)));
        *start = range->start + first * HBLKSIZE;
      }
      index = high;
      while (*end == range_registry[index].end && index + 1 < range_count
             && range_registry[index + 1].start == *end) {
        range = &range_registry[++index];
        last = committed_end(range, 0);
        *end = range->start + last * HBLKSIZE;
      }
      found = TRUE;
    }
  }
  GC_isolate_mutex_unlock(&range_lock);
  return found;
}

GC_INNER GC_bool
GC_isolate_vdb_has_foreign_writes(void)
{
#  ifdef GC_ISOLATE_ATOMIC_FOREIGN_WRITES
  return (GC_bool)__atomic_load_n(&foreign_writes_seen, __ATOMIC_SEQ_CST);
#  else
  GC_bool result;
  GC_isolate_mutex_lock(&range_lock);
  result = (GC_bool)foreign_writes_seen;
  GC_isolate_mutex_unlock(&range_lock);
  return result;
#  endif
}

GC_INNER GC_bool
GC_isolate_vdb_push_pending(struct hblk *h, unsigned n)
{
  unsigned i;
  size_t missing = 0;

#  ifdef GC_ISOLATE_ATOMIC_FOREIGN_WRITES
  __atomic_store_n(&foreign_writes_seen, TRUE, __ATOMIC_SEQ_CST);
#  else
  GC_isolate_mutex_lock(&range_lock);
  foreign_writes_seen = TRUE;
  GC_isolate_mutex_unlock(&range_lock);
#  endif
  GC_isolate_mutex_lock(&pending_lock);
  for (i = 0; i < n; ++i) {
    ptr_t address = (ptr_t)(h + i);
    size_t index = first_pending_at_or_after(address);
    if (index == pending_count || pending_queue[index] != address)
      ++missing;
  }
  /* Reserve the whole batch before changing the set.  Existing duplicate
     pages are already durable; missing pages must never be dropped. */
  if (!ensure_pending_capacity_locked(missing)) {
    GC_isolate_mutex_unlock(&pending_lock);
    return FALSE;
  }
  for (i = 0; i < n; ++i) {
    ptr_t address = (ptr_t)(h + i);
    size_t index = first_pending_at_or_after(address);
    if (index < pending_count && pending_queue[index] == address)
      continue;
    memmove(&pending_queue[index + 1], &pending_queue[index],
            (pending_count - index) * sizeof(*pending_queue));
    pending_queue[index] = address;
    ++pending_count;
  }
  GC_isolate_mutex_unlock(&pending_lock);
  return TRUE;
}

GC_INNER void
GC_isolate_vdb_drain_pending(void)
{
  size_t section;

  GC_isolate_mutex_lock(&pending_lock);
  for (section = 0; section < GC_n_heap_sects && pending_count != 0; ++section) {
    ptr_t start = GC_heap_sects[section].hs_start;
    ptr_t end = start + GC_heap_sects[section].hs_bytes;
    size_t first = first_pending_at_or_after(start);
    size_t last = first_pending_at_or_after(end);
    size_t read, write = first;
    for (read = first; read < last; ++read) {
      ptr_t address = pending_queue[read];
      if (GC_find_header(address) != NULL) {
#  if defined(LINUX)
        GC_coarse_note_foreign_write(address, HBLKSIZE);
#  endif
        GC_isolate_dirty_page(address);
        GC_COND_LOG_PRINTF("Claiming cross-isolate dirty page %p into this thread's own dirty bitmap\n",
                           (void *)address);
      } else {
        pending_queue[write++] = address;
      }
    }
    if (write != last) {
      memmove(&pending_queue[write], &pending_queue[last],
              (pending_count - last) * sizeof(*pending_queue));
      pending_count -= last - write;
    }
  }
  GC_isolate_mutex_unlock(&pending_lock);
}

GC_INNER void
GC_isolate_vdb_deinit(void)
{
  size_t i;

  if (!isolate_has_registered_ranges)
    return;
  isolate_has_registered_ranges = FALSE;

  GC_isolate_mutex_lock(&range_lock);
  for (i = 0; i < GC_n_heap_sects; i++) {
    delete_range_locked(GC_heap_sects[i].hs_start,
                         GC_heap_sects[i].hs_start + GC_heap_sects[i].hs_bytes);
  }
  GC_isolate_mutex_unlock(&range_lock);

  /* Drop only this isolate's sorted pending ranges before its header
     table disappears; other isolates retain their queued dirty pages. */
  GC_isolate_mutex_lock(&pending_lock);
  for (i = 0; i < GC_n_heap_sects && pending_count != 0; ++i) {
    ptr_t start = GC_heap_sects[i].hs_start;
    ptr_t end = start + GC_heap_sects[i].hs_bytes;
    size_t first = first_pending_at_or_after(start);
    size_t last = first_pending_at_or_after(end);
    if (first != last) {
      memmove(&pending_queue[first], &pending_queue[last],
              (pending_count - last) * sizeof(*pending_queue));
      pending_count -= last - first;
    }
  }
  GC_isolate_mutex_unlock(&pending_lock);
}

GC_INNER void
GC_isolate_vdb_destroy_for_shared_library_unload(void)
{
  GC_ASSERT(range_count == 0 && pending_count == 0);
  free(range_registry);
  range_registry = NULL;
  range_capacity = 0;
  free(pending_queue);
  pending_queue = NULL;
  pending_capacity = 0;
}

#endif /* GC_THREAD_ISOLATE && MPROTECT_VDB */
