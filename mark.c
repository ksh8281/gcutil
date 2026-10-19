/*
 * Copyright 1988, 1989 Hans-J. Boehm, Alan J. Demers
 * Copyright (c) 1991-1995 by Xerox Corporation.  All rights reserved.
 * Copyright (c) 2000 by Hewlett-Packard Company.  All rights reserved.
 * Copyright (c) 2008-2025 Ivan Maidanski
 *
 * THIS MATERIAL IS PROVIDED AS IS, WITH ABSOLUTELY NO WARRANTY EXPRESSED
 * OR IMPLIED.  ANY USE IS AT YOUR OWN RISK.
 *
 * Permission is hereby granted to use or copy this program
 * for any purpose, provided the above notices are retained on all copies.
 * Permission to modify the code and to distribute modified code is granted,
 * provided the above notices are retained, and a notice that the code was
 * modified is included with the above copyright notice.
 */

#include "private/gc_pmark.h"
#include "private/vdb_isolate.h"
#ifdef LINUX
# include <errno.h>
# include <sys/mman.h>
# include <stdint.h>
#endif

/* candidates, inactive table, rejected address, unregistered block,
   already marked, unmarked registered target, reused header, cache miss. */
GC_INNER MAY_THREAD_LOCAL word GC_target_reuse_stats[16];
/* epochs, registrations, invalidations, capped blocks, OOM, max committed
   table bytes, virtual bytes, hugepage-advice failures. */
GC_INNER MAY_THREAD_LOCAL word GC_target_table_stats[8];
GC_INNER MAY_THREAD_LOCAL word GC_source_page_stats[20];
STATIC MAY_THREAD_LOCAL GC_bool GC_source_page_slice;
STATIC MAY_THREAD_LOCAL GC_bool GC_source_page_audit;
STATIC MAY_THREAD_LOCAL unsigned GC_source_batch_mode;
#ifdef GC_SOURCE_BATCH_AUDIT
GC_INNER MAY_THREAD_LOCAL word GC_source_batch_stats[12];
GC_INNER MAY_THREAD_LOCAL word GC_source_batch_kinds[192][3];
#endif

#ifdef GC_HAS_TARGET_MARK_TABLE
STATIC MAY_THREAD_LOCAL const word **GC_target_table_storage;
STATIC MAY_THREAD_LOCAL word GC_target_table_page_seen[2048 / CPP_WORDSZ];
STATIC MAY_THREAD_LOCAL size_t GC_target_table_pages;
# define GC_TARGET_TABLE_BYTES \
    (((size_t)1 << 32) / HBLKSIZE * sizeof(word *))
#endif

GC_INNER void
GC_target_mark_table_end(void)
{
  GC_marker_cold_arrays._target_mark_table = NULL;
  GC_marker_cold_arrays._target_header_reuse = FALSE;
#ifdef GC_HAS_TARGET_MARK_TABLE
  if (GC_target_table_storage != NULL)
    (void)munmap((void *)GC_target_table_storage, GC_TARGET_TABLE_BYTES);
  GC_target_table_storage = NULL;
#endif
}

#ifdef GC_HAS_TARGET_MARK_TABLE
static void GC_CALLBACK
GC_target_register_block(struct hblk *h, void *unused)
{
  hdr *hhdr = HDR(h);
  word offset, slot, page, mask;
  UNUSED_ARG(unused);
  if (HBLK_IS_FREE(hhdr) || IS_UNCOLLECTABLE(hhdr->hb_obj_kind)
      || hhdr->hb_sz > MAXOBJBYTES || hhdr->hb_block != h)
    return;
  offset = ADDR(h) - GC_cage_base;
  if (offset >= ((word)1 << 32))
    return;
  slot = offset >> LOG_HBLKSIZE;
  page = slot * sizeof(word *) / GC_page_size;
  GC_ASSERT(page < 2048);
  mask = (word)1 << modWORDSZ(page);
  if ((GC_target_table_page_seen[divWORDSZ(page)] & mask) == 0) {
    if (GC_target_table_pages >= (1024 * 1024) / GC_page_size) {
      ++GC_target_table_stats[3];
      return;
    }
    GC_target_table_page_seen[divWORDSZ(page)] |= mask;
    ++GC_target_table_pages;
  }
  GC_target_table_storage[slot] = hhdr->hb_marks;
  ++GC_target_table_stats[1];
}
#endif

GC_ATTR_NOINLINE GC_INNER void
GC_target_mark_table_begin(void)
{
  GC_target_mark_table_end();
#ifdef GC_HAS_TARGET_MARK_TABLE
  {
    const char *setting = GETENV("GC_BENCH_TARGET_MARK_TABLE");
    int mode = setting != NULL ? atoi(setting) : 0;
    void *memory;
    size_t bytes;
    if (mode == 0 || (!GC_young_mark_active && mode < 3)
        || GC_young_mark_aborted || GC_find_leak_inner
        || GC_is_enumerate_reachable_objects || GC_page_size < 4096
        || GC_page_size > 1024 * 1024
        || (GC_cage_base & (HBLKSIZE - 1)) != 0)
      return;
    memory = mmap(NULL, GC_TARGET_TABLE_BYTES, PROT_READ | PROT_WRITE,
                  MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (memory == MAP_FAILED) {
      ++GC_target_table_stats[4];
      return;
    }
# ifdef MADV_NOHUGEPAGE
    if (madvise(memory, GC_TARGET_TABLE_BYTES, MADV_NOHUGEPAGE) != 0) {
      int advice_errno = errno;
      ++GC_target_table_stats[7];
      /* Linux rejects an unsupported advice even for an empty range.
         Keep the table if THP advice itself is unavailable, while retaining
         the fallback for errors on a kernel that supports the advice. */
      if (advice_errno != EINVAL
          || madvise(NULL, 0, MADV_NOHUGEPAGE) == 0 || errno != EINVAL) {
        (void)munmap(memory, GC_TARGET_TABLE_BYTES);
        return;
      }
    }
# endif
    GC_target_table_storage = (const word **)memory;
    GC_target_table_pages = 0;
    BZERO(GC_target_table_page_seen, sizeof(GC_target_table_page_seen));
    GC_apply_to_all_blocks(GC_target_register_block, NULL);
    bytes = GC_target_table_pages * GC_page_size;
    if (bytes > GC_target_table_stats[5])
      GC_target_table_stats[5] = (word)bytes;
    GC_target_table_stats[6] = GC_TARGET_TABLE_BYTES;
    ++GC_target_table_stats[0];
    /* Publish only after registration. Invalidation disables it immediately,
       while storage remains owned until the stopped mark returns. */
    GC_target_header_reuse = mode >= 2;
    GC_target_mark_table = GC_target_table_storage;
  }
#endif
}


/*
 * Make arguments appear live to compiler.  Put here to minimize the
 * risk of inlining.  Used to minimize junk left in registers.
 */
GC_ATTR_NOINLINE
void
GC_noop6(word arg1, word arg2, word arg3, word arg4, word arg5, word arg6)
{
  UNUSED_ARG(arg1);
  UNUSED_ARG(arg2);
  UNUSED_ARG(arg3);
  UNUSED_ARG(arg4);
  UNUSED_ARG(arg5);
  UNUSED_ARG(arg6);
  /* Avoid `GC_noop6` calls to be optimized away. */
#if defined(AO_HAVE_compiler_barrier) && !defined(BASE_ATOMIC_OPS_EMULATED)
  AO_compiler_barrier(); /*< to serve as a special side-effect */
#else
  GC_noop1(0);
#endif
}

GC_API void GC_CALL
GC_noop1(GC_word x)
{
#if defined(AO_HAVE_store) && defined(THREAD_SANITIZER)
  AO_store(&GC_noop_sink, (AO_t)x);
#else
  GC_noop_sink = x;
#endif
}

GC_API void GC_CALL
GC_noop1_ptr(volatile void *p)
{
#if CPP_PTRSZ > CPP_WORDSZ || defined(CPPCHECK)
#  if defined(AO_HAVE_store) && defined(THREAD_SANITIZER)
  GC_cptr_store(&GC_noop_sink_ptr, (ptr_t)CAST_AWAY_VOLATILE_PVOID(p));
#  elif defined(CPPCHECK)
  GC_noop_sink_ptr = (ptr_t)(/* no volatile */ void *)p;
#  else
  GC_noop_sink_ptr = (ptr_t)CAST_AWAY_VOLATILE_PVOID(p);
#  endif
#else
  GC_noop1(ADDR(p));
#endif
}

/*
 * Initialize `GC_obj_kinds` properly and standard free lists properly.
 * This must be done statically since they may be accessed before
 * `GC_init` is called.  It is done here, since we need to deal with
 * mark descriptors.  Note: `GC_obj_kinds[NORMAL].ok_descriptor` is
 * adjusted in `GC_init()` for `EXTRA_BYTES`.
 */
#if defined(ENABLE_TLS_ACCESS_BY_ADDRESS) \
    || defined(ENABLE_TLS_ACCESS_BY_PTHREAD_KEY)
GC_INNER MAY_THREAD_LOCAL struct obj_kind GC_obj_kinds_instance[MAXOBJKINDS]
    = {
#else
GC_INNER MAY_THREAD_LOCAL struct obj_kind GC_obj_kinds[MAXOBJKINDS] = {
#endif
        /* `PTRFREE` */
        { 0, 0 /*< filled in dynamically */,
          /* `0 |` */ GC_DS_LENGTH, FALSE,
          FALSE OK_EAGER_SWEEP_INITZ
              /*, */ OK_DISCLAIM_INITZ },
        /* `NORMAL` */
        { 0, 0,
          /* `0 |` */ GC_DS_LENGTH,
          TRUE /*< add length to descriptor template */,
          TRUE OK_EAGER_SWEEP_INITZ
              /*, */ OK_DISCLAIM_INITZ },
        /* `UNCOLLECTABLE` */
        { 0, 0,
          /* `0 |` */ GC_DS_LENGTH,
          TRUE /*< add length to descriptor template */,
          TRUE OK_EAGER_SWEEP_INITZ
              /*, */ OK_DISCLAIM_INITZ },
#ifdef GC_ATOMIC_UNCOLLECTABLE
        /* `AUNCOLLECTABLE` */
        { 0, 0,
          /* `0 |` */ GC_DS_LENGTH, FALSE,
          FALSE OK_EAGER_SWEEP_INITZ
              /*, */ OK_DISCLAIM_INITZ },
#endif
      };

#ifndef GC_NO_DEINIT
/* Note: keep this close to `GC_obj_kinds` definition. */
GC_INNER void
GC_reset_obj_kinds(void)
{
  unsigned i;

  for (i = 0; i < GC_N_KINDS_INITIAL_VALUE; i++)
    GC_obj_kinds[i].ok_reclaim_list = NULL;
  GC_obj_kinds[PTRFREE].ok_freelist = &GC_aobjfreelist[0];
  GC_obj_kinds[NORMAL].ok_freelist = &GC_objfreelist[0];
  GC_obj_kinds[UNCOLLECTABLE].ok_freelist = &GC_uobjfreelist[0];
#  ifdef GC_ATOMIC_UNCOLLECTABLE
  GC_obj_kinds[AUNCOLLECTABLE].ok_freelist = &GC_auobjfreelist[0];
#  endif
  GC_obj_kinds[NORMAL].ok_descriptor = GC_DS_LENGTH;
  GC_n_kinds = GC_N_KINDS_INITIAL_VALUE;
}
#endif

#ifndef INITIAL_MARK_STACK_SIZE
/*
 * `INITIAL_MARK_STACK_SIZE * sizeof(mse)` should be a multiple of `HBLKSIZE`.
 * The incremental collector actually likes a larger size, since it wants to
 * push all marked dirty objects before marking anything new.
 * Currently we let it grow dynamically.
 */
#  define INITIAL_MARK_STACK_SIZE (1 * HBLKSIZE)
#endif

#if !defined(GC_DISABLE_INCREMENTAL)
/*
 * The number of dirty pages we marked from, excluding pointer-free pages,
 * etc.  Used for logging only.
 */
STATIC MAY_THREAD_LOCAL word GC_n_rescuing_pages = 0;
#endif

GC_API void GC_CALL
GC_set_pointer_mask(GC_word value)
{
#ifdef DYNAMIC_POINTER_MASK
  GC_ASSERT(value >= 0xff); /*< a simple sanity check */
  GC_pointer_mask = value;
#else
  if (value
#  ifdef POINTER_MASK
      != (word)(POINTER_MASK)
#  else
      != GC_WORD_MAX
#  endif
  ) {
    ABORT("Dynamic pointer mask/shift is unsupported");
  }
#endif
}

GC_API GC_word GC_CALL
GC_get_pointer_mask(void)
{
#ifdef DYNAMIC_POINTER_MASK
  GC_word value = GC_pointer_mask;

  if (0 == value) {
    GC_ASSERT(!GC_is_initialized);
    value = GC_WORD_MAX;
  }
  return value;
#elif defined(POINTER_MASK)
  return POINTER_MASK;
#else
  return GC_WORD_MAX;
#endif
}

GC_API void GC_CALL
GC_set_pointer_shift(unsigned value)
{
#ifdef DYNAMIC_POINTER_MASK
  GC_ASSERT(value < CPP_WORDSZ);
  GC_pointer_shift = (unsigned char)value;
#else
  if (value
#  ifdef POINTER_SHIFT
      != (unsigned)(POINTER_SHIFT)
#  endif
  ) {
    ABORT("Dynamic pointer mask/shift is unsupported");
  }
#endif
}

GC_API unsigned GC_CALL
GC_get_pointer_shift(void)
{
#ifdef DYNAMIC_POINTER_MASK
  return GC_pointer_shift;
#elif defined(POINTER_SHIFT)
  GC_STATIC_ASSERT((unsigned)(POINTER_SHIFT) < CPP_WORDSZ);
  return POINTER_SHIFT;
#else
  return 0;
#endif
}

GC_INNER GC_bool
GC_collection_in_progress(void)
{
  return GC_mark_state != MS_NONE;
}

GC_INNER void
GC_clear_hdr_marks(hdr *hhdr)
{
  size_t last_bit;

#ifdef AO_HAVE_load
  /* Atomic access is used to avoid racing with `GC_realloc`. */
  last_bit = FINAL_MARK_BIT(AO_load((volatile AO_t *)&hhdr->hb_sz));
#else
  /*
   * No race as `GC_realloc` holds the allocator lock while updating
   * `hb_sz` field.
   */
  last_bit = FINAL_MARK_BIT(hhdr->hb_sz);
#endif

  BZERO(CAST_AWAY_VOLATILE_PVOID(hhdr->hb_marks), sizeof(hhdr->hb_marks));
  set_mark_bit_from_hdr(hhdr, last_bit);
  hhdr->hb_n_marks = 0;
}

GC_INNER void
GC_set_hdr_marks(hdr *hhdr)
{
  size_t i;
  size_t sz = hhdr->hb_sz;
  size_t n_marks = FINAL_MARK_BIT(sz);

#ifdef USE_MARK_BYTES
  for (i = 0; i <= n_marks; i += MARK_BIT_OFFSET(sz)) {
    hhdr->hb_marks[i] = 1;
  }
#else
  /*
   * Note that all bits are set even in case of not `MARK_BIT_PER_OBJ`,
   * instead of setting every `n`-th bit where `n` is `MARK_BIT_OFFSET(sz)`.
   *  This is done for a performance reason.
   */
  for (i = 0; i < divWORDSZ(n_marks); ++i) {
    hhdr->hb_marks[i] = GC_WORD_MAX;
  }
  /* Set the remaining bits near the end (plus one bit past the end). */
  hhdr->hb_marks[i] = ((((word)1 << modWORDSZ(n_marks)) - 1) << 1) | 1;
#endif
#ifdef MARK_BIT_PER_OBJ
  hhdr->hb_n_marks = n_marks;
#else
  hhdr->hb_n_marks = HBLK_OBJS(sz);
#endif
}

/* Clear all mark bits associated with block `h`. */
static void GC_CALLBACK
clear_marks_for_block(struct hblk *h, void *dummy)
{
  hdr *hhdr = HDR(h);

  UNUSED_ARG(dummy);
  if (IS_UNCOLLECTABLE(hhdr->hb_obj_kind)) {
    /*
     * Mark bit for these is cleared only once the object is deallocated
     * explicitly.  This either frees the block, or the bit is cleared
     * once the object is on the free list.
     */
    return;
  }
  GC_clear_hdr_marks(hhdr);
#if defined(CPPCHECK)
  GC_noop1_ptr(h);
#endif
}

STATIC MAY_THREAD_LOCAL GC_bool GC_young_baseline_pending;
STATIC void GC_invalidate_young_baseline(void);
STATIC GC_bool GC_young_clear_requires_full(const hdr *hhdr, size_t bit_no);
GC_INNER MAY_THREAD_LOCAL word GC_young_old_source_blocks;
GC_INNER MAY_THREAD_LOCAL word GC_young_bit_source_blocks;
GC_INNER MAY_THREAD_LOCAL word GC_young_old_source_empty;
GC_INNER MAY_THREAD_LOCAL word GC_young_old_source_recoveries;
STATIC MAY_THREAD_LOCAL GC_bool GC_young_source_filter_disabled;
STATIC MAY_THREAD_LOCAL GC_bool GC_sparse_sources_armed;

/* Keep this armed after the map is released: a late callback can change a
   source whose earlier scan was deliberately omitted. */
GC_INNER void
GC_note_sparse_source_mutation(void)
{
#ifdef GC_TEST_ZERO_SOURCE_MUTATION
  if (GC_test_zero_suppress_mutation)
    return;
#endif
  if (GC_young_mark_active && GC_sparse_sources_armed)
    GC_young_source_recovery_pending = TRUE;
}

/* Slow but general routines for setting/clearing/getting mark bits. */

GC_API void GC_CALL
GC_set_mark_bit(const void *p)
{
  struct hblk *h = HBLKPTR(p);
  hdr *hhdr = HDR(h);
  size_t bit_no = MARK_BIT_NO((size_t)((ptr_t)p - (ptr_t)h), hhdr->hb_sz);

  if (GC_young_mark_active && !IS_PTRFREE(hhdr))
    GC_note_sparse_source_mutation();
  if (!mark_bit_from_hdr(hhdr, bit_no)) {
    set_mark_bit_from_hdr(hhdr, bit_no);
    INCR_MARKS(hhdr);
    if (UNLIKELY(GC_young_mark_active)) {
      (void)GC_charge_young_mark(hhdr, p);
      /* The public mark-bit API does not enqueue the object's fields.
         A rescuer which omits young sources cannot rely on that bit alone.
         Preserve even a callback's one-shot mark while revisiting sources
         already passed by the cursor, just like mark-stack recovery. */
      if (GC_young_old_sources && !IS_PTRFREE(hhdr))
        GC_young_source_recovery_pending = TRUE;
    }
  }
}

STATIC void
GC_clear_mark_bit_inner(const void *p, GC_bool invalidate_young)
{
  struct hblk *h = HBLKPTR(p);
  hdr *hhdr = HDR(h);
  size_t bit_no = MARK_BIT_NO((size_t)((ptr_t)p - (ptr_t)h), hhdr->hb_sz);

  if (mark_bit_from_hdr(hhdr, bit_no)) {
    size_t n_marks = hhdr->hb_n_marks;

    /* A late census cannot reconstruct a live old object's removed bit.
       Ordinary allocation/free do not use this explicit marking API. */
    if (invalidate_young && GC_young_retrace
        && GC_young_clear_requires_full(hhdr, bit_no)) {
      GC_young_mark_clear_invalidated = TRUE;
      GC_invalidate_young_baseline();
      if ((GC_young_block_retrace || GC_young_dense_retrace || GC_young_log_retrace)
          && GC_young_mark_active)
        GC_young_mark_aborted = TRUE;
    }

    GC_ASSERT(n_marks != 0);
    clear_mark_bit_from_hdr(hhdr, bit_no);
    n_marks--;
#ifdef PARALLEL_MARK
    /*
     * Do not decrement to zero.  The counts are approximate due to
     * concurrency issues, but we need to ensure that a count of zero
     * implies an empty block.
     */
    if (n_marks != 0 || !GC_parallel)
      hhdr->hb_n_marks = n_marks;
#else
    hhdr->hb_n_marks = n_marks;
#endif
  }
}

GC_API void GC_CALL
GC_clear_mark_bit(const void *p)
{
  GC_clear_mark_bit_inner(p, TRUE);
}

/* Only for a collector-owned entry already unlinked from its last owner.
   Clearing that deliberately dead entry cannot remove a live old root. */
GC_INNER void
GC_clear_unlinked_mark_bit(const void *p)
{
  GC_clear_mark_bit_inner(p, FALSE);
}

GC_API int GC_CALL
GC_is_marked(const void *p)
{
  struct hblk *h = HBLKPTR(p);
  hdr *hhdr = HDR(h);
  size_t bit_no = MARK_BIT_NO((size_t)((ptr_t)p - (ptr_t)h), hhdr->hb_sz);

  return (int)mark_bit_from_hdr(hhdr, bit_no); /*< 0 or 1 */
}

GC_INNER void
GC_clear_marks(void)
{
  /* The initialization is needed for `GC_push_roots()`. */
  GC_ASSERT(GC_is_initialized);

  if (GC_young_retrace)
    GC_invalidate_young_baseline();
  if (GC_young_mark_clear_invalidated)
    GC_admission_forget_repair();
  GC_young_mark_clear_invalidated = FALSE;
  GC_apply_to_all_blocks(clear_marks_for_block, NULL);
  GC_objects_are_marked = FALSE;
  GC_mark_state = MS_INVALID;
  GC_scan_ptr = NULL;
}

/* Experimental old-generation census.  libc storage is outside the GC heap;
   it records mark bits, not owning references to object payloads. */
typedef struct {
  struct hblk *block;
  hdr *header;
  size_t size;
  word descriptor;
  size_t n_marks;
  unsigned char kind;
  unsigned char flags;
  unsigned char marks[sizeof(((hdr *)0)->hb_marks)];
} GC_young_old_entry;

STATIC MAY_THREAD_LOCAL GC_young_old_entry *GC_young_old_entries;
STATIC MAY_THREAD_LOCAL size_t GC_young_old_count;
STATIC MAY_THREAD_LOCAL size_t GC_young_old_capacity;
STATIC MAY_THREAD_LOCAL GC_bool GC_young_old_valid;
GC_INNER MAY_THREAD_LOCAL word GC_young_retained_bytes;
GC_INNER MAY_THREAD_LOCAL word GC_young_snapshot_bytes;
STATIC MAY_THREAD_LOCAL GC_bool GC_young_full_was_tracked;
STATIC MAY_THREAD_LOCAL GC_bool GC_young_captured_since_full;
STATIC MAY_THREAD_LOCAL GC_word GC_young_baseline_gc_no;
GC_INNER MAY_THREAD_LOCAL word GC_young_baseline_captures;
GC_INNER MAY_THREAD_LOCAL word GC_young_preflight_rejections;

/* Bounded experimental young-survivor log.  Storage is outside the GC
   heap and is released at every full.  Overflow completes this minor with
   sticky marks and forces the next collection through full preparation. */
#ifdef ESCARGOT_USE_32BIT_IN_64BIT
typedef uint32_t GC_young_log_address;
#else
typedef word GC_young_log_address;
#endif
#define GC_YOUNG_LOG_BLOCK_BITS ((size_t)1 << 16)
#define GC_YOUNG_LOG_BLOCK_WORDS (GC_YOUNG_LOG_BLOCK_BITS / CPP_WORDSZ)
#define GC_YOUNG_LOG_HASH(block) (PHT_HASH(block) & (GC_YOUNG_LOG_BLOCK_BITS - 1))
STATIC MAY_THREAD_LOCAL GC_young_log_address *GC_young_log_entries;
STATIC MAY_THREAD_LOCAL size_t GC_young_log_count;
STATIC MAY_THREAD_LOCAL size_t GC_young_log_mapped;
STATIC MAY_THREAD_LOCAL word *GC_young_log_blocks;
STATIC MAY_THREAD_LOCAL GC_bool GC_young_log_failed;
GC_INNER MAY_THREAD_LOCAL GC_bool GC_young_log_recording;
GC_INNER MAY_THREAD_LOCAL word GC_young_log_limit = 1024 * 1024;
GC_INNER MAY_THREAD_LOCAL word GC_young_log_events;
GC_INNER MAY_THREAD_LOCAL word GC_young_log_overflows;
GC_INNER MAY_THREAD_LOCAL word GC_young_log_cleared;
GC_INNER MAY_THREAD_LOCAL word GC_young_log_compacted;
GC_INNER MAY_THREAD_LOCAL word GC_young_log_max_entries;
GC_INNER MAY_THREAD_LOCAL word GC_young_log_max_bytes;

STATIC void
GC_release_young_log(void)
{
#ifdef LINUX
  if (GC_young_log_entries != NULL)
    (void)munmap(GC_young_log_entries, GC_young_log_mapped);
#endif
  GC_young_log_entries = NULL;
  GC_young_log_count = GC_young_log_mapped = 0;
  free(GC_young_log_blocks);
  GC_young_log_blocks = NULL;
  GC_young_log_failed = FALSE;
  GC_young_log_recording = FALSE;
}

/* Once the last permitted minor starts, no later trace may whiten its
   unlogged survivors.  Keep the mandatory full even if the API raises the
   full frequency before the next request.  Earlier logs are already
   consumed, so their mapping can be returned before this trace. */
GC_INNER void
GC_begin_young_log(GC_bool can_repeat)
{
  GC_young_log_recording = can_repeat;
  if (!can_repeat) {
    GC_release_young_log();
    GC_young_snapshot_bytes = 0;
    GC_young_log_failed = TRUE;
  }
}

GC_INNER void
GC_record_young_log_mark(const void *base)
{
#ifdef LINUX
  word address = ADDR(base);

  if (!GC_young_old_valid || GC_young_log_failed)
    return;
  if (GC_young_log_entries == NULL) {
    void *memory = mmap(NULL, (size_t)GC_young_log_limit,
                        PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS,
                        -1, 0);
    if (memory == MAP_FAILED)
      goto failed;
    GC_young_log_entries = (GC_young_log_address *)memory;
    GC_young_log_mapped = (size_t)GC_young_log_limit;
    GC_young_snapshot_bytes = GC_young_log_mapped
                             + GC_YOUNG_LOG_BLOCK_WORDS * sizeof(word);
    if (GC_young_log_max_bytes < GC_young_snapshot_bytes)
      GC_young_log_max_bytes = GC_young_snapshot_bytes;
  }
  if (GC_young_log_count
      == GC_young_log_mapped / sizeof(*GC_young_log_entries))
    goto failed;
# ifdef ESCARGOT_USE_32BIT_IN_64BIT
  if (GC_cage_base == 0 || address < GC_cage_base
      || address - GC_cage_base > (word)UINT32_MAX)
    goto failed;
  address -= GC_cage_base;
# endif
  GC_young_log_entries[GC_young_log_count++] = (GC_young_log_address)address;
  set_pht_entry_from_index(GC_young_log_blocks,
                          GC_YOUNG_LOG_HASH(HBLKPTR(base)));
  ++GC_young_log_events;
  if (GC_young_log_max_entries < GC_young_log_count)
    GC_young_log_max_entries = GC_young_log_count;
  return;
failed:
  GC_young_log_failed = TRUE;
  GC_young_log_recording = FALSE;
  ++GC_young_log_overflows;
#else
  UNUSED_ARG(base);
#endif
}

/* A false free-list root may have been cleared and its entire block freed
   or reused after logging.  Never install or remove a bit using an old
   layout.  A matching address reused between fulls remains young. */
STATIC hdr *
GC_current_young_log_mark(size_t index, ptr_t *base)
{
  word address = (word)GC_young_log_entries[index];
  struct hblk *block;
  hdr *hhdr;
  size_t offset, size, bit;
#ifdef ESCARGOT_USE_32BIT_IN_64BIT
  address += GC_cage_base;
#endif
  *base = (ptr_t)address;
  block = HBLKPTR(*base);
  hhdr = HDR(block);
  if (IS_FORWARDING_ADDR_OR_NIL(hhdr) || HBLK_IS_FREE(hhdr)
      || IS_UNCOLLECTABLE(hhdr->hb_obj_kind) || hhdr->hb_block != block)
    return NULL;
  offset = (size_t)(*base - (ptr_t)block);
  size = hhdr->hb_sz;
  if (size == 0 || offset % size != 0
      || (size > HBLKSIZE ? offset != 0 : offset > HBLKSIZE - size))
    return NULL;
  bit = MARK_BIT_NO(offset, size);
  if (bit >= FINAL_MARK_BIT(size) || !mark_bit_from_hdr(hhdr, bit))
    return NULL;
  return hhdr;
}

STATIC void
GC_clear_young_log_marks(void)
{
  size_t i;
  for (i = 0; i < GC_young_log_count; ++i) {
    ptr_t base;
    if (GC_current_young_log_mark(i, &base) != NULL) {
      GC_clear_mark_bit_inner(base, FALSE);
      ++GC_young_log_cleared;
    }
  }
  GC_young_log_count = 0;
  if (GC_young_log_blocks != NULL)
    BZERO(GC_young_log_blocks, GC_YOUNG_LOG_BLOCK_WORDS * sizeof(word));
}

GC_INNER void
GC_finish_young_log(void)
{
  size_t i, count = 0;
  if (!GC_young_log_retrace || GC_young_log_failed)
    return;
  {
    const char *setting = GETENV("GC_GENERATIONAL_LOG_COMPACT");
    if (setting != NULL && atoi(setting) == 0)
      return;
  }
  for (i = 0; i < GC_young_log_count; ++i) {
    ptr_t base;
    if (GC_current_young_log_mark(i, &base) != NULL)
      GC_young_log_entries[count++] = GC_young_log_entries[i];
  }
  GC_young_log_compacted += GC_young_log_count - count;
  GC_young_log_count = count;
}


#if !defined(MARK_BIT_PER_OBJ) && !defined(USE_MARK_BYTES)
#  define GC_YOUNG_DENSE_WORDS (MARK_BITS_PER_HBLK / CPP_WORDSZ)
typedef struct {
  ptr_t start;
  size_t bytes;
  word *marks;
} GC_young_dense_section;

STATIC MAY_THREAD_LOCAL GC_young_dense_section *GC_young_dense_sections;
STATIC MAY_THREAD_LOCAL size_t GC_young_dense_count;
STATIC MAY_THREAD_LOCAL size_t GC_young_dense_last;

STATIC void
GC_release_dense_baseline(void)
{
  size_t i;
  for (i = 0; i < GC_young_dense_count; ++i)
    free(GC_young_dense_sections[i].marks);
  free(GC_young_dense_sections);
  GC_young_dense_sections = NULL;
  GC_young_dense_count = GC_young_dense_last = 0;
}

/* This census owns its section map independently of the protection cache.
   A late heap section is young; losing an existing mapping is not. */
STATIC GC_bool
GC_dense_sections_valid(void)
{
  size_t i;
  if (GC_young_dense_count > GC_n_heap_sects)
    return FALSE;
  for (i = 0; i < GC_young_dense_count; ++i)
    if (GC_young_dense_sections[i].start != GC_heap_sects[i].hs_start
        || GC_young_dense_sections[i].bytes != GC_heap_sects[i].hs_bytes)
      return FALSE;
  return TRUE;
}

STATIC word *
GC_dense_old_marks(const struct hblk *block)
{
  size_t i = GC_young_dense_last, remaining = GC_young_dense_count;
  while (remaining-- != 0) {
    GC_young_dense_section *section = &GC_young_dense_sections[i];
    if (ADDR_GE((ptr_t)block, section->start)
        && (size_t)((ptr_t)block - section->start) < section->bytes) {
      GC_young_dense_last = i;
      return section->marks
             + ((size_t)((ptr_t)block - section->start) / HBLKSIZE)
                   * GC_YOUNG_DENSE_WORDS;
    }
    if (++i == GC_young_dense_count)
      i = 0;
  }
  return NULL;
}

STATIC void GC_CALLBACK
GC_capture_dense_marks(struct hblk *block, void *data)
{
  const hdr *hhdr = HDR(block);
  word *marks;
  size_t last_bit;

  UNUSED_ARG(data);
  if (IS_UNCOLLECTABLE(hhdr->hb_obj_kind) || hhdr->hb_n_marks == 0)
    return;
  marks = GC_dense_old_marks(block);
  GC_ASSERT(marks != NULL);
  BCOPY(CAST_AWAY_VOLATILE_PVOID(hhdr->hb_marks), marks,
        GC_YOUNG_DENSE_WORDS * sizeof(word));
  last_bit = FINAL_MARK_BIT(hhdr->hb_sz);
  if (last_bit < MARK_BITS_PER_HBLK)
    marks[divWORDSZ(last_bit)] &= ~((word)1 << modWORDSZ(last_bit));
}

STATIC GC_bool
GC_capture_dense_baseline(void)
{
  size_t i, bytes = 0;

  if (GC_young_dense_count != GC_n_heap_sects || !GC_dense_sections_valid())
    GC_release_dense_baseline();
  if (GC_young_dense_sections == NULL) {
    GC_young_dense_sections = (GC_young_dense_section *)calloc(
        GC_n_heap_sects, sizeof(*GC_young_dense_sections));
    if (GC_young_dense_sections == NULL)
      return FALSE;
    GC_young_dense_count = GC_n_heap_sects;
    for (i = 0; i < GC_young_dense_count; ++i) {
      GC_young_dense_sections[i].start = GC_heap_sects[i].hs_start;
      GC_young_dense_sections[i].bytes = GC_heap_sects[i].hs_bytes;
    }
  }
  for (i = 0; i < GC_young_dense_count; ++i) {
    GC_young_dense_section *section = &GC_young_dense_sections[i];
    size_t size = section->bytes / HBLKSIZE
                  * GC_YOUNG_DENSE_WORDS * sizeof(word);
    if (section->marks == NULL) {
      section->marks = (word *)calloc(1, size);
      if (section->marks == NULL) {
        GC_release_dense_baseline();
        GC_young_snapshot_bytes = 0;
        return FALSE;
      }
    } else {
      BZERO(section->marks, size);
    }
    bytes += size;
  }
  GC_young_dense_last = 0;
  GC_apply_to_all_blocks(GC_capture_dense_marks, NULL);
  GC_young_snapshot_bytes = bytes
                           + GC_young_dense_count * sizeof(*GC_young_dense_sections);
  return TRUE;
}

/* Keep only current marks at addresses present in the old census.  An old
   address reused with another layout can promote extra cells, but cannot
   install marks for cells which do not exist in the current layout. */
STATIC void
GC_intersect_dense_marks(hdr *hhdr, const word *old)
{
  size_t i, last_bit = FINAL_MARK_BIT(hhdr->hb_sz);
  size_t removed_count = 0;

  if (old == NULL) {
    GC_clear_hdr_marks(hhdr);
    return;
  }
  for (i = 0; i < GC_YOUNG_DENSE_WORDS; ++i) {
    word current = hhdr->hb_marks[i];
    word keep = current & old[i];
    word removed;
    if (i == divWORDSZ(last_bit))
      keep |= (word)1 << modWORDSZ(last_bit);
    removed = current & ~keep;
    if (removed != 0) {
#  if defined(__GNUC__) || defined(__clang__)
      removed_count += (size_t)__builtin_popcountll(removed);
#  else
      do {
        ++removed_count;
        removed &= removed - 1;
      } while (removed != 0);
#  endif
    }
    if (keep != current)
      hhdr->hb_marks[i] = keep;
  }
  GC_ASSERT(removed_count <= hhdr->hb_n_marks);
  hhdr->hb_n_marks -= removed_count;
}
#endif

GC_INNER GC_bool
GC_young_block_is_old(const hdr *hhdr)
{
  return IS_UNCOLLECTABLE(hhdr->hb_obj_kind)
         || (GC_young_old_block_map != NULL
             && get_pht_entry_from_index(GC_young_old_block_map,
                                         PHT_HASH(hhdr->hb_block)) != 0);
}

STATIC GC_bool
GC_young_clear_requires_full(const hdr *hhdr, size_t bit_no)
{
  GC_bool required = GC_young_baseline_pending
         || (GC_young_log_retrace && GC_young_old_valid
             && !IS_UNCOLLECTABLE(hhdr->hb_obj_kind))
         || (GC_young_block_retrace && GC_young_old_valid
             && !IS_UNCOLLECTABLE(hhdr->hb_obj_kind)
             && GC_young_block_is_old(hhdr));
#if !defined(MARK_BIT_PER_OBJ) && !defined(USE_MARK_BYTES)
  if (!required && GC_young_dense_retrace && GC_young_old_valid
      && !IS_UNCOLLECTABLE(hhdr->hb_obj_kind)
      && bit_no < MARK_BITS_PER_HBLK) {
    const word *old = GC_dense_old_marks(hhdr->hb_block);
    required = old != NULL
               && (old[divWORDSZ(bit_no)] & ((word)1 << modWORDSZ(bit_no))) != 0;
  }
#else
  UNUSED_ARG(bit_no);
#endif
  return required;
}

STATIC void
GC_invalidate_young_baseline(void)
{
  GC_young_baseline_pending = GC_young_old_valid = FALSE;
  GC_young_old_count = 0;
  GC_young_log_count = 0;
  GC_young_log_recording = FALSE;
}

GC_INNER void
GC_defer_young_baseline(void)
{
  if (GC_young_log_retrace) {
    GC_release_young_log();
    GC_young_snapshot_bytes = 0;
  }
  /* A full epoch which never used its census need not retain its capacity.
     Keep storage across productive epochs to avoid repeated large mallocs. */
  if (!GC_young_captured_since_full && GC_young_old_entries != NULL) {
    free(GC_young_old_entries);
    GC_young_old_entries = NULL;
    GC_young_old_capacity = 0;
    GC_young_snapshot_bytes = 0;
  }
  if (!GC_young_captured_since_full && GC_young_old_block_map != NULL) {
    free(GC_young_old_block_map);
    GC_young_old_block_map = NULL;
    GC_young_snapshot_bytes = 0;
  }
#if !defined(MARK_BIT_PER_OBJ) && !defined(USE_MARK_BYTES)
  if (!GC_young_captured_since_full && GC_young_dense_sections != NULL) {
    GC_release_dense_baseline();
    GC_young_snapshot_bytes = 0;
  }
#endif
  GC_young_captured_since_full = FALSE;
  GC_invalidate_young_baseline();
  GC_young_baseline_pending = GC_young_full_was_tracked;
  GC_young_baseline_gc_no = GC_gc_no;
  GC_young_retained_bytes = 0;
}
GC_INNER MAY_THREAD_LOCAL word GC_young_retrace_restores;
GC_INNER MAY_THREAD_LOCAL word GC_young_retrace_rejections;

STATIC void GC_CALLBACK
GC_count_old_entries(struct hblk *block, void *data)
{
  const hdr *hhdr = HDR(block);
  if (!IS_UNCOLLECTABLE(hhdr->hb_obj_kind) && hhdr->hb_n_marks != 0)
    ++*(size_t *)data;
}

static void GC_CALLBACK
GC_capture_old_block(struct hblk *block, void *data)
{
  const hdr *hhdr = HDR(block);

  UNUSED_ARG(data);
  if (!IS_UNCOLLECTABLE(hhdr->hb_obj_kind) && hhdr->hb_n_marks != 0)
    set_pht_entry_from_index(GC_young_old_block_map, PHT_HASH(block));
}

STATIC void GC_CALLBACK
GC_capture_old_entry(struct hblk *block, void *data)
{
  hdr *hhdr = HDR(block);
  GC_young_old_entry *entry;

  UNUSED_ARG(data);
  if (IS_UNCOLLECTABLE(hhdr->hb_obj_kind) || hhdr->hb_n_marks == 0)
    return;
  GC_ASSERT(GC_young_old_count < GC_young_old_capacity);
  entry = &GC_young_old_entries[GC_young_old_count++];
  entry->block = block;
  entry->header = hhdr;
  entry->size = hhdr->hb_sz;
  entry->descriptor = hhdr->hb_descr;
  entry->n_marks = hhdr->hb_n_marks;
  entry->kind = hhdr->hb_obj_kind;
  entry->flags = hhdr->hb_flags;
  BCOPY(CAST_AWAY_VOLATILE_PVOID(hhdr->hb_marks), entry->marks,
        sizeof(entry->marks));
}

STATIC int
GC_compare_old_entries(const void *left, const void *right)
{
  const GC_young_old_entry *a = (const GC_young_old_entry *)left;
  const GC_young_old_entry *b = (const GC_young_old_entry *)right;
  return ADDR_LT(a->block, b->block) ? -1
         : ADDR_LT(b->block, a->block) ? 1 : 0;
}

STATIC const GC_young_old_entry *
GC_find_old_entry(const struct hblk *block)
{
  size_t low = 0, high = GC_young_old_count;
  while (low < high) {
    size_t mid = low + (high - low) / 2;
    if (ADDR_LT(GC_young_old_entries[mid].block, block))
      low = mid + 1;
    else
      high = mid;
  }
  return low < GC_young_old_count && GC_young_old_entries[low].block == block
             ? &GC_young_old_entries[low] : NULL;
}

STATIC void
GC_capture_young_baseline(void)
{
  size_t count = 0;
  GC_young_old_entry *entries;

  GC_young_old_valid = FALSE;
  GC_young_retained_bytes = 0;
  if (!GC_young_full_was_tracked)
    return;
  if (GC_young_log_retrace) {
    if (GC_young_log_blocks == NULL)
      GC_young_log_blocks = (word *)calloc(GC_YOUNG_LOG_BLOCK_WORDS, sizeof(word));
    if (GC_young_log_blocks == NULL)
      return;
    BZERO(GC_young_log_blocks, GC_YOUNG_LOG_BLOCK_WORDS * sizeof(word));
    GC_young_snapshot_bytes = GC_YOUNG_LOG_BLOCK_WORDS * sizeof(word);
    GC_young_old_valid = GC_young_captured_since_full = TRUE;
    ++GC_young_baseline_captures;
    return;
  }
#if !defined(MARK_BIT_PER_OBJ) && !defined(USE_MARK_BYTES)
  if (GC_young_dense_retrace) {
    if (!GC_capture_dense_baseline())
      return;
    GC_young_old_valid = GC_young_captured_since_full = TRUE;
    ++GC_young_baseline_captures;
    return;
  }
#endif
  if (GC_young_block_retrace) {
    if (GC_young_old_block_map == NULL) {
      GC_young_old_block_map = (word *)calloc(PHT_SIZE, sizeof(word));
      if (GC_young_old_block_map == NULL)
        return;
    } else {
      BZERO(GC_young_old_block_map, sizeof(page_hash_table));
    }
    /* A collision only promotes an extra block.  No saved mark bits or
       layouts are ever installed in a reused header. */
    GC_apply_to_all_blocks(GC_capture_old_block, NULL);
    GC_young_snapshot_bytes = sizeof(page_hash_table);
    GC_young_old_valid = GC_young_captured_since_full = TRUE;
    ++GC_young_baseline_captures;
    return;
  }
  GC_apply_to_all_blocks(GC_count_old_entries, &count);
  if (count > GC_young_old_capacity) {
    if (count > GC_SIZE_MAX / sizeof(*entries))
      return;
    entries = (GC_young_old_entry *)realloc(
        GC_young_old_entries, count * sizeof(*entries));
    if (entries == NULL)
      return;
    GC_young_old_entries = entries;
    GC_young_old_capacity = count;
  }
  GC_young_snapshot_bytes = GC_young_old_capacity * sizeof(*entries);
  GC_young_old_count = 0;
  GC_apply_to_all_blocks(GC_capture_old_entry, NULL);
  if (GC_young_old_count > 1)
    qsort(GC_young_old_entries, GC_young_old_count, sizeof(*entries),
          GC_compare_old_entries);
  GC_young_old_valid = TRUE;
  GC_young_captured_since_full = TRUE;
  ++GC_young_baseline_captures;
}

STATIC void GC_CALLBACK
GC_restore_old_entry(struct hblk *block, void *data)
{
  hdr *hhdr = HDR(block);
  const GC_young_old_entry *entry;

  UNUSED_ARG(data);
  if (IS_UNCOLLECTABLE(hhdr->hb_obj_kind))
    return;
#if !defined(MARK_BIT_PER_OBJ) && !defined(USE_MARK_BYTES)
  if (GC_young_dense_retrace) {
    GC_intersect_dense_marks(hhdr, GC_dense_old_marks(block));
    GC_ASSERT(hhdr->hb_n_marks == GC_n_set_marks(hhdr));
    return;
  }
#endif
  if (GC_young_block_retrace) {
    if (!GC_young_block_is_old(hhdr))
      GC_clear_hdr_marks(hhdr);
    GC_ASSERT(hhdr->hb_n_marks == GC_n_set_marks(hhdr));
    return;
  }
  entry = GC_find_old_entry(block);
  if (entry == NULL) {
    GC_clear_hdr_marks(hhdr);
  } else {
    BCOPY(entry->marks, CAST_AWAY_VOLATILE_PVOID(hhdr->hb_marks),
          sizeof(entry->marks));
    hhdr->hb_n_marks = entry->n_marks;
  }
  GC_ASSERT(hhdr->hb_n_marks == GC_n_set_marks(hhdr));
}

/* A pending block with no marks outside the old census loses no marked
   live object on restore.  Its lazy sweep can remain pending: allocation
   normally sweeps and removes such a block before handing out its cells. */
GC_INNER GC_bool
GC_young_pending_reclaim_safe(const hdr *hhdr)
{
  const GC_young_old_entry *entry;
  const unsigned char *current;
  size_t i;

  if (IS_UNCOLLECTABLE(hhdr->hb_obj_kind))
    return TRUE;
  if (GC_young_log_retrace)
    return GC_young_log_count == 0
           || !get_pht_entry_from_index(GC_young_log_blocks,
                                        GC_YOUNG_LOG_HASH(hhdr->hb_block));
#if !defined(MARK_BIT_PER_OBJ) && !defined(USE_MARK_BYTES)
  if (GC_young_dense_retrace) {
    const word *old = GC_dense_old_marks(hhdr->hb_block);
    size_t last_bit = FINAL_MARK_BIT(hhdr->hb_sz);
    if (old == NULL)
      return FALSE;
    for (i = 0; i < GC_YOUNG_DENSE_WORDS; ++i) {
      word outside = hhdr->hb_marks[i] & ~old[i];
      if (i == divWORDSZ(last_bit))
        outside &= ~((word)1 << modWORDSZ(last_bit));
      if (outside != 0)
        return FALSE;
    }
    return TRUE;
  }
#endif
  if (GC_young_block_retrace)
    return GC_young_block_is_old(hhdr);
  entry = GC_find_old_entry(hhdr->hb_block);
  if (entry == NULL || hhdr != entry->header || hhdr->hb_sz != entry->size
      || hhdr->hb_descr != entry->descriptor || hhdr->hb_obj_kind != entry->kind
      || hhdr->hb_flags != entry->flags)
    return FALSE;
  current = (const unsigned char *)CAST_AWAY_VOLATILE_PVOID(hhdr->hb_marks);
  for (i = 0; i < sizeof(entry->marks); ++i)
    if ((current[i] & ~entry->marks[i]) != 0)
      return FALSE;
  return TRUE;
}

/* Pending reclaim lists must consume the still-valid previous marks before
   a young survivor is made white again.  In particular an aborted trace's
   full fallback must not lazily reclaim an unvisited, live young object. */
GC_INNER GC_ATTR_NOINLINE GC_bool
GC_prepare_young_retrace(void)
{
#if defined(LINUX) && defined(GC_THREAD_ISOLATE) && defined(MPROTECT_VDB)
  size_t i;
  GC_bool valid = TRUE;

  if (GC_young_log_retrace && GC_young_log_failed) {
    ++GC_young_retrace_rejections;
    return FALSE;
  }
  if ((!GC_young_old_valid && !GC_young_baseline_pending)
      || !GC_incremental || GC_manual_vdb
      || GC_get_actual_vdb() != GC_VDB_MPROTECT
      || GC_isolate_vdb_has_foreign_writes())
    return FALSE;
#  ifdef PARALLEL_MARK
  if (GC_parallel)
    return FALSE;
#  endif
  ++GC_dont_gc;
  if (GC_young_baseline_pending) {
    if (GC_young_baseline_gc_no != GC_gc_no || GC_mark_state != MS_NONE) {
      GC_invalidate_young_baseline();
    } else {
      GC_young_baseline_pending = FALSE;
      /* No collection has changed the full marks. Newly allocated cells
         remain white; explicit set-mark may only conservatively promote. */
      GC_capture_young_baseline();
    }
  }
  if (!GC_young_old_valid) {
    ++GC_young_retrace_rejections;
    --GC_dont_gc;
    return FALSE;
  }
#  if !defined(MARK_BIT_PER_OBJ) && !defined(USE_MARK_BYTES)
  if (GC_young_dense_retrace && !GC_dense_sections_valid()) {
    ++GC_young_retrace_rejections;
    --GC_dont_gc;
    return FALSE;
  }
#  endif
  valid = GC_reclaim_before_young();
  GC_isolate_vdb_drain_pending();
  if (!GC_young_old_valid || !GC_young_retrace
      || GC_isolate_vdb_has_foreign_writes())
    valid = FALSE;
#  if !defined(MARK_BIT_PER_OBJ) && !defined(USE_MARK_BYTES)
  if (GC_young_dense_retrace && !GC_dense_sections_valid())
    valid = FALSE;
#  endif
  /* Check every surviving old layout before changing any marks.  A freed
     address may have been reused or absorbed by another large allocation.
     A matching reused layout can only conservatively retain extra objects. */
  for (i = 0; valid && !GC_young_block_retrace && !GC_young_dense_retrace
              && !GC_young_log_retrace
              && i < GC_young_old_count; ++i) {
    const GC_young_old_entry *entry = &GC_young_old_entries[i];
    hdr *hhdr = HDR(entry->block);
    if (hhdr == NULL || (!IS_FORWARDING_ADDR_OR_NIL(hhdr)
                         && HBLK_IS_FREE(hhdr)))
      continue;
    if (IS_FORWARDING_ADDR_OR_NIL(hhdr) || hhdr != entry->header
        || hhdr->hb_sz != entry->size || hhdr->hb_descr != entry->descriptor
        || hhdr->hb_obj_kind != entry->kind || hhdr->hb_flags != entry->flags)
      valid = FALSE;
  }
  if (valid) {
    if (GC_young_log_retrace)
      GC_clear_young_log_marks();
    else
      GC_apply_to_all_blocks(GC_restore_old_entry, NULL);
    ++GC_young_retrace_restores;
  } else {
    ++GC_young_retrace_rejections;
  }
  --GC_dont_gc;
  return valid;
#else
  return FALSE;
#endif
}

GC_INNER void
GC_young_retrace_deinit(void)
{
  GC_target_mark_table_end();
  if (!GC_is_init_called())
    return;
  GC_sparse_sources_deinit();
  GC_release_young_log();
  GC_young_log_limit = 1024 * 1024;
  GC_young_log_events = GC_young_log_overflows = 0;
  GC_young_log_cleared = GC_young_log_compacted = 0;
  GC_young_log_max_entries = GC_young_log_max_bytes = 0;
  if (!GC_young_retrace && GC_young_old_entries == NULL
      && GC_young_old_block_map == NULL
#if !defined(MARK_BIT_PER_OBJ) && !defined(USE_MARK_BYTES)
      && GC_young_dense_sections == NULL
#endif
  )
    return;
#if !defined(MARK_BIT_PER_OBJ) && !defined(USE_MARK_BYTES)
  GC_release_dense_baseline();
#endif
  free(GC_young_old_block_map);
  GC_young_old_block_map = NULL;
  free(GC_young_old_entries);
  GC_young_old_entries = NULL;
  GC_young_old_count = GC_young_old_capacity = 0;
  GC_young_old_valid = GC_young_full_was_tracked = FALSE;
  GC_young_baseline_pending = GC_young_captured_since_full = FALSE;
  GC_young_mark_clear_invalidated = FALSE;
  GC_young_baseline_gc_no = 0;
  GC_young_baseline_captures = GC_young_preflight_rejections = 0;
  GC_young_retrace_restores = GC_young_retrace_rejections = 0;
  GC_young_pending_kept = GC_young_pending_drained = 0;
  GC_young_old_source_blocks = GC_young_old_source_empty = 0;
  GC_young_old_source_recoveries = 0;
  GC_young_source_recovery_pending = GC_young_source_filter_disabled = FALSE;
  GC_young_retained_bytes = GC_young_snapshot_bytes = 0;
#ifndef GC_DISABLE_INCREMENTAL
  GC_reset_young_remembered(FALSE);
#endif
}


#ifdef GC_TEST_ZERO_SOURCE_MUTATION
GC_INNER MAY_THREAD_LOCAL word GC_test_zero_hidden_block;
GC_INNER MAY_THREAD_LOCAL word GC_test_zero_hidden_child;
GC_INNER MAY_THREAD_LOCAL word GC_test_zero_hidden_field;
GC_INNER MAY_THREAD_LOCAL GC_bool GC_test_zero_skipped;
GC_INNER MAY_THREAD_LOCAL GC_bool GC_test_zero_child_from_field;
GC_INNER MAY_THREAD_LOCAL GC_bool GC_test_zero_suppress_mutation;
#endif
STATIC MAY_THREAD_LOCAL struct hblk *GC_sparse_current_source;
GC_INNER MAY_THREAD_LOCAL word GC_sparse_attempts, GC_sparse_cache_hits;
GC_INNER MAY_THREAD_LOCAL word GC_sparse_captures, GC_sparse_zero_captures;
GC_INNER MAY_THREAD_LOCAL word GC_sparse_queries, GC_sparse_hits;
GC_INNER MAY_THREAD_LOCAL word GC_sparse_caps, GC_sparse_oom;
GC_INNER MAY_THREAD_LOCAL word GC_sparse_layout_fallbacks, GC_sparse_max_entries;
GC_INNER MAY_THREAD_LOCAL word GC_sparse_mapping_bytes;
GC_INNER MAY_THREAD_LOCAL word GC_sparse_zero_queries;

#if defined(LINUX) && !defined(MARK_BIT_PER_OBJ) && !defined(USE_MARK_BYTES)
#define GC_SPARSE_SLOTS 16384
#define GC_SPARSE_LIMIT (GC_SPARSE_SLOTS / 2)
#ifdef ESCARGOT_USE_32BIT_IN_64BIT
#define GC_SPARSE_BITMAP_WORDS \
  ((size_t)0x100000000ULL / HBLKSIZE / CPP_WORDSZ)
#endif
STATIC MAY_THREAD_LOCAL word *GC_sparse_slots;
STATIC MAY_THREAD_LOCAL size_t GC_sparse_count, GC_sparse_bytes;
STATIC MAY_THREAD_LOCAL GC_bool GC_sparse_capped;
STATIC const word GC_sparse_zero_marks[GC_YOUNG_DENSE_WORDS];

STATIC void
GC_sparse_sources_end(void)
{
  GC_marker_cold_arrays._young_sparse_active = FALSE;
  if (GC_sparse_slots != NULL)
    (void)munmap(GC_sparse_slots, GC_sparse_bytes);
  GC_sparse_slots = NULL;
  GC_sparse_current_source = NULL;
  GC_sparse_count = 0;
}

STATIC void
GC_sparse_sources_begin(void)
{
  void *memory;
  GC_sparse_sources_end();
  GC_sparse_sources_armed = FALSE;
  GC_sparse_capped = FALSE;
  if (!GC_young_mark_active || !GC_young_sparse_sources
      || GC_young_roots_first || GC_get_actual_vdb() != GC_VDB_MPROTECT)
    return;
#ifdef PARALLEL_MARK
  if (GC_parallel)
    return;
#endif
#ifdef ESCARGOT_USE_32BIT_IN_64BIT
  GC_sparse_bytes = GC_SPARSE_BITMAP_WORDS * sizeof(word);
#else
  GC_sparse_bytes = GC_SPARSE_SLOTS * sizeof(word);
#endif
  memory = mmap(NULL, GC_sparse_bytes, PROT_READ | PROT_WRITE,
                MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  if (memory == MAP_FAILED) {
    ++GC_sparse_oom;
    return;
  }
  GC_sparse_slots = (word *)memory;
  GC_young_sparse_active = GC_sparse_sources_armed = TRUE;
  GC_sparse_mapping_bytes = GC_sparse_bytes;
}

STATIC GC_bool
GC_sparse_kind_eligible(const hdr *hhdr)
{
  if (IS_UNCOLLECTABLE(hhdr->hb_obj_kind) || IS_PTRFREE(hhdr))
    return FALSE;
#ifdef ENABLE_DISCLAIM
  if ((hhdr->hb_flags & (MARK_UNCONDITIONALLY | HAS_DISCLAIM)) != 0
      || GC_obj_kinds[hhdr->hb_obj_kind].ok_disclaim_proc != NULL)
    return FALSE;
#endif
  return TRUE;
}

#ifndef ESCARGOT_USE_32BIT_IN_64BIT
STATIC word *
GC_sparse_find(word key)
{
  size_t index = (size_t)(key * (word)2654435761U)
                 & (GC_SPARSE_SLOTS - 1);
  while (GC_sparse_slots[index] != 0 && GC_sparse_slots[index] != key)
    index = (index + 1) & (GC_SPARSE_SLOTS - 1);
  return &GC_sparse_slots[index];
}
#endif

GC_INNER void
GC_sparse_record_new_mark(const hdr *hhdr, const void *base)
{
  struct hblk *block = HBLKPTR(base);
  word key, *slot;
#ifdef ESCARGOT_USE_32BIT_IN_64BIT
  word mask;
#endif
  if (!GC_young_sparse_active || GC_sparse_capped || hhdr->hb_n_marks != 1
      || GC_mark_state != MS_PUSH_RESCUERS || !GC_sparse_kind_eligible(hhdr))
    return;
  if (GC_sparse_current_source != NULL) {
    if (!ADDR_LT(GC_sparse_current_source, block))
      return;
  } else if (GC_scan_ptr != NULL && ADDR_LT(block, GC_scan_ptr)) {
    return;
  }
  ++GC_sparse_attempts;
#ifdef ESCARGOT_USE_32BIT_IN_64BIT
  if (ADDR(block) < GC_cage_base
      || ADDR(block) - GC_cage_base >= (word)0x100000000ULL)
    return;
  key = (ADDR(block) - GC_cage_base) / HBLKSIZE;
  slot = &GC_sparse_slots[divWORDSZ(key)];
  mask = (word)1 << modWORDSZ(key);
  if ((*slot & mask) != 0)
    return;
  *slot |= mask;
#else
  key = ADDR(block) / HBLKSIZE + 1;
  slot = GC_sparse_find(key);
  if (*slot == key)
    return;
  if (GC_sparse_count == GC_SPARSE_LIMIT) {
    GC_sparse_capped = TRUE;
    ++GC_sparse_caps;
    return;
  }
  *slot = key;
#endif
  ++GC_sparse_count;
  ++GC_sparse_captures;
  ++GC_sparse_zero_captures;
  if (GC_sparse_max_entries < GC_sparse_count)
    GC_sparse_max_entries = GC_sparse_count;
}

STATIC const word *
GC_sparse_old_marks(struct hblk *block, const hdr *hhdr)
{
  word key;
  if (!GC_young_sparse_active || GC_young_source_filter_disabled
      || !GC_sparse_kind_eligible(hhdr))
    return NULL;
  ++GC_sparse_queries;
#ifdef ESCARGOT_USE_32BIT_IN_64BIT
  if (ADDR(block) < GC_cage_base
      || ADDR(block) - GC_cage_base >= (word)0x100000000ULL)
    return NULL;
  key = (ADDR(block) - GC_cage_base) / HBLKSIZE;
  if ((GC_sparse_slots[divWORDSZ(key)] & ((word)1 << modWORDSZ(key))) == 0)
    return NULL;
#else
  key = ADDR(block) / HBLKSIZE + 1;
  if (*GC_sparse_find(key) != key)
    return NULL;
#endif
  ++GC_sparse_hits;
  ++GC_sparse_zero_queries;
#ifdef GC_TEST_ZERO_SOURCE_MUTATION
  if (GC_test_zero_hidden_block == ~ADDR(block))
    GC_test_zero_skipped = TRUE;
#endif
  return GC_sparse_zero_marks;
}
#else
STATIC void GC_sparse_sources_end(void) { GC_young_sparse_active = FALSE; }
STATIC const word *GC_sparse_old_marks(struct hblk *block, const hdr *hhdr)
{ UNUSED_ARG(block); UNUSED_ARG(hhdr); return NULL; }

STATIC void GC_sparse_sources_begin(void) { GC_sparse_sources_armed = FALSE; }
GC_INNER void GC_sparse_record_new_mark(const hdr *hhdr, const void *base)
{ UNUSED_ARG(hhdr); UNUSED_ARG(base); }
#endif

GC_INNER void
GC_sparse_sources_deinit(void)
{
  GC_sparse_sources_end();
  GC_sparse_sources_armed = FALSE;
  GC_sparse_attempts = GC_sparse_cache_hits = GC_sparse_captures = 0;
  GC_sparse_zero_captures = GC_sparse_queries = GC_sparse_hits = 0;
  GC_sparse_caps = GC_sparse_oom = GC_sparse_layout_fallbacks = 0;
  GC_sparse_max_entries = GC_sparse_mapping_bytes = GC_sparse_zero_queries = 0;
}

STATIC MAY_THREAD_LOCAL GC_bool GC_young_roots_done = FALSE;

/* A performance filter only: compare like-for-like pointer-bearing payload
   estimates before paying for a remembered-source scan.  The index returns
   each allocation once, including large objects spanning dirty pages. */
STATIC GC_bool
GC_young_cost_exceeds_live(GC_bool pending)
{
#if defined(LINUX) && defined(GC_THREAD_ISOLATE) && defined(MPROTECT_VDB)
  struct hblk *cursor = NULL, *block;
  word dirty = 0, limit = GC_composite_in_use;

  if (GC_young_dirty_percent == 0 || limit == 0)
    return FALSE;
  if (GC_young_dirty_percent < 100)
    limit = limit / 100 * GC_young_dirty_percent;
  if (pending) {
    GC_isolate_vdb_drain_pending();
    if (GC_isolate_vdb_has_foreign_writes())
      return FALSE;
  }
  for (;;) {
    hdr *hhdr;
    word marks;

    if (!(pending ? GC_next_pending_candidate(cursor, &block)
                  : GC_next_dirty_candidate(cursor, &block)) || block == NULL)
      return FALSE;
    hhdr = HDR(block);
    marks = hhdr->hb_n_marks;
    if (marks != 0) {
      if (hhdr->hb_sz > (limit - dirty) / marks)
        return TRUE;
      dirty += marks * hhdr->hb_sz;
      if (dirty >= limit)
        return TRUE;
    }
    cursor = block + OBJ_SZ_TO_BLOCKS(hhdr->hb_sz);
  }
#else
  return FALSE;
#endif
}

GC_INNER GC_bool
GC_young_pending_cost_exceeds_live(void)
{
  return GC_young_cost_exceeds_live(TRUE);
}

GC_INNER void
GC_initiate_gc(void)
{
  GC_ASSERT(I_HOLD_LOCK());
  GC_ASSERT(GC_is_initialized);
#ifndef GC_DISABLE_INCREMENTAL
  if (GC_generational && GC_young_retrace && GC_mark_state == MS_INVALID
      && !GC_young_mark_active) {
    /* The first deferred activation has no complete write history.  Its
       baseline stays invalid until a full mark starts with tracking on. */
    GC_young_full_was_tracked = GC_incremental
                                && !GC_admission_skip_protect
                                && GC_get_actual_vdb() == GC_VDB_MPROTECT;
    GC_reset_young_remembered(FALSE);
  }
  if (GC_incremental) {
    GC_isolate_vdb_drain_pending();
#  ifdef CHECKSUMS
    GC_read_dirty(FALSE);
    GC_check_dirty();
#  else
    GC_read_dirty(GC_mark_state == MS_INVALID);
#  endif
  }
  {
    const char *mode = GETENV("GC_BENCH_SOURCE_BATCH");
    GC_source_batch_mode = mode != NULL ? (unsigned)atoi(mode) : 0;
  }
  GC_n_rescuing_pages = 0;
#endif
  if (GC_mark_state == MS_NONE) {
    GC_mark_state = MS_PUSH_RESCUERS;
  } else {
    /* This is really a full collection, and mark bits are invalid. */
    GC_ASSERT(GC_mark_state == MS_INVALID);
  }
  GC_scan_ptr = NULL;
  GC_young_roots_done = FALSE;
  GC_young_source_recovery_pending = GC_young_source_filter_disabled = FALSE;
  if (GC_young_mark_active) {
    if (GC_young_retrace && GC_isolate_vdb_has_foreign_writes()) {
      ++GC_young_retrace_rejections;
      GC_young_mark_aborted = TRUE;
    } else if (GC_young_cost_exceeds_live(FALSE)) {
      ++GC_young_dirty_rejections;
      GC_young_mark_aborted = TRUE;
    } else if (GC_young_roots_first) {
      GC_mark_state = MS_PUSH_ROOTS_FIRST;
    }
  }
  GC_sparse_sources_begin();
  {
    const char *audit = GETENV("GC_BENCH_SOURCE_PAGE_AUDIT");
    const char *slice = GETENV("GC_BENCH_SOURCE_PAGE_SLICE");
    GC_source_page_audit = audit != NULL && atoi(audit) != 0;
    GC_source_page_slice = slice != NULL && atoi(slice) != 0;
  }
}

#ifdef PARALLEL_MARK
/* Initiate parallel marking. */
STATIC void GC_do_parallel_mark(void);
#endif

#ifdef GC_DISABLE_INCREMENTAL
#  define GC_push_next_marked_dirty(h) GC_push_next_marked(h)
#else
STATIC struct hblk *GC_push_next_marked_dirty(struct hblk *h);
#endif /* !GC_DISABLE_INCREMENTAL */

STATIC struct hblk *GC_push_next_marked(struct hblk *h);
STATIC struct hblk *GC_push_next_marked_uncollectable(struct hblk *h);
#if !defined(GC_DISABLE_INCREMENTAL) && !defined(MARK_BIT_PER_OBJ) \
    && !defined(USE_MARK_BYTES)
STATIC void GC_push_marked_word_bits(struct hblk *h, const hdr *hhdr,
                                      GC_bool old_only, const word *saved);
#endif

static void alloc_mark_stack(size_t);

static void
push_roots_and_advance(GC_bool push_all, ptr_t cold_gc_frame)
{
  if (GC_scan_ptr != NULL) {
    /* Not ready to push. */
    return;
  }
  GC_push_roots(push_all, cold_gc_frame);
  GC_objects_are_marked = TRUE;
  if (GC_mark_state != MS_INVALID)
    GC_mark_state = MS_ROOTS_PUSHED;
}

STATIC MAY_THREAD_LOCAL GC_on_mark_stack_empty_proc GC_on_mark_stack_empty = 0;

GC_API void GC_CALL
GC_set_on_mark_stack_empty(GC_on_mark_stack_empty_proc fn)
{
  LOCK();
  GC_on_mark_stack_empty = fn;
  UNLOCK();
}

GC_API GC_on_mark_stack_empty_proc GC_CALL
GC_get_on_mark_stack_empty(void)
{
  GC_on_mark_stack_empty_proc fn;

  READER_LOCK();
  fn = GC_on_mark_stack_empty;
  READER_UNLOCK();
  return fn;
}

#ifdef WRAP_MARK_SOME
/*
 * This is called after we establish a structured exception or signal
 * handler, in case of a root segment is unmapped by the OS asynchronously.
 * Note that this code should never generate an incremental GC write fault.
 */
STATIC GC_bool
GC_mark_some_inner(ptr_t cold_gc_frame)
#else
GC_INNER GC_bool
GC_mark_some(ptr_t cold_gc_frame)
#endif
{
  GC_ASSERT(I_HOLD_LOCK());
  if (GC_young_mark_active && GC_young_source_recovery_pending) {
    GC_young_source_recovery_pending = FALSE;
    GC_young_source_filter_disabled = TRUE;
    GC_mark_state = MS_INVALID;
    GC_scan_ptr = NULL;
    GC_objects_are_marked = TRUE;
    ++GC_young_old_source_recoveries;
  }
  if (GC_young_sparse_active && GC_mark_state != MS_PUSH_RESCUERS)
    GC_sparse_sources_end();
  switch (GC_mark_state) {
  case MS_NONE:
    return TRUE;

  case MS_PUSH_ROOTS_FIRST:
    GC_young_root_marking = TRUE;
    GC_push_roots(FALSE, cold_gc_frame);
    GC_young_root_marking = FALSE;
    GC_objects_are_marked = TRUE;
    GC_young_roots_done = TRUE;
    if (GC_mark_state != MS_INVALID)
      GC_mark_state = MS_TRACE_ROOTS_FIRST;
    break;

  case MS_TRACE_ROOTS_FIRST:
    if (ADDR_GE((ptr_t)GC_mark_stack_top, (ptr_t)GC_mark_stack)) {
      GC_young_root_marking = TRUE;
      MARK_FROM_MARK_STACK();
      GC_young_root_marking = FALSE;
    } else {
      GC_mark_state = MS_PUSH_RESCUERS;
      GC_scan_ptr = NULL;
    }
    break;

  case MS_PUSH_RESCUERS:
    GC_young_rescuer_marking = GC_young_mark_active;
    if (ADDR_GE((ptr_t)GC_mark_stack_top,
                (ptr_t)(GC_young_mark_active
                            ? GC_mark_stack + GC_mark_stack_size / 4
                            : GC_mark_stack_limit
                                  - INITIAL_MARK_STACK_SIZE / 2))) {
      /*
       * Go ahead and mark, even though that might cause us to see more
       * marked dirty objects later on.  Avoid this in the future.
       */
      /* Leave room for the closure of dirty sources, including custom
         mark procedures which may push many children in one call.  A
         stopped minor can drain this queue without a growth hint; genuine
         overflow still invalidates marking and requests growth. */
      if (!GC_young_mark_active) {
        GC_mark_stack_too_small = TRUE;
      }
      MARK_FROM_MARK_STACK();
    } else {
      GC_scan_ptr = GC_push_next_marked_dirty(GC_scan_ptr);
#ifndef GC_DISABLE_INCREMENTAL
      if (NULL == GC_scan_ptr) {
        GC_COND_LOG_PRINTF("Marked from %lu dirty pages\n",
                           (unsigned long)GC_n_rescuing_pages);
      }
#endif
      GC_young_rescuer_marking = FALSE;
      if (GC_scan_ptr == NULL && GC_young_sparse_active)
        GC_sparse_sources_end();
      if (GC_young_roots_done) {
        if (GC_scan_ptr == NULL && GC_mark_state != MS_INVALID)
          GC_mark_state = MS_ROOTS_PUSHED;
      } else {
        push_roots_and_advance(FALSE, cold_gc_frame);
      }
    }
    GC_young_rescuer_marking = FALSE;
    GC_ASSERT(GC_mark_state == MS_PUSH_RESCUERS
              || GC_mark_state == MS_ROOTS_PUSHED
              || GC_mark_state == MS_INVALID);
    break;

  case MS_PUSH_UNCOLLECTABLE:
    if (ADDR_GE((ptr_t)GC_mark_stack_top,
                (ptr_t)(GC_mark_stack + GC_mark_stack_size / 4))) {
#ifdef PARALLEL_MARK
      /* Avoid this, since we do not parallelize the marker here. */
      if (GC_parallel)
        GC_mark_stack_too_small = TRUE;
#endif
      MARK_FROM_MARK_STACK();
    } else {
      GC_scan_ptr = GC_push_next_marked_uncollectable(GC_scan_ptr);
      push_roots_and_advance(TRUE, cold_gc_frame);
    }
    GC_ASSERT(GC_mark_state == MS_PUSH_UNCOLLECTABLE
              || GC_mark_state == MS_ROOTS_PUSHED
              || GC_mark_state == MS_INVALID);
    break;

  case MS_ROOTS_PUSHED:
#ifdef PARALLEL_MARK
    /*
     * Eventually, incremental marking should run asynchronously
     * in multiple threads, without acquiring the allocator lock.
     * For now, parallel marker is disabled if there is a chance that
     * marking could be interrupted by a client-supplied time limit
     * or custom stop function.
     */
    if (GC_parallel && !GC_parallel_mark_disabled) {
      GC_do_parallel_mark();
      GC_ASSERT(ADDR_LT((ptr_t)GC_mark_stack_top, GC_first_nonempty));
      GC_mark_stack_top = GC_mark_stack - 1;
      if (GC_mark_stack_too_small) {
        alloc_mark_stack(2 * GC_mark_stack_size);
      }
      if (GC_mark_state == MS_ROOTS_PUSHED) {
        GC_mark_state = MS_NONE;
        return TRUE;
      }
      GC_ASSERT(GC_mark_state == MS_INVALID);
      break;
    }
#endif
    if (ADDR_GE((ptr_t)GC_mark_stack_top, (ptr_t)GC_mark_stack)) {
      MARK_FROM_MARK_STACK();
    } else {
      GC_on_mark_stack_empty_proc on_ms_empty = GC_on_mark_stack_empty;

      if (on_ms_empty != 0) {
        GC_mark_stack_top
            = on_ms_empty(GC_mark_stack_top, GC_mark_stack_limit);
        /* If we pushed new items, we need to continue processing. */
        if (ADDR_GE((ptr_t)GC_mark_stack_top, (ptr_t)GC_mark_stack))
          break;
      }
      if (GC_young_mark_active && GC_young_source_recovery_pending)
        break;
      if (GC_mark_stack_too_small) {
        alloc_mark_stack(2 * GC_mark_stack_size);
      }
      GC_mark_state = MS_NONE;
      return TRUE;
    }
    GC_ASSERT(GC_mark_state == MS_ROOTS_PUSHED || GC_mark_state == MS_INVALID);
    break;

  case MS_INVALID:
  case MS_PARTIALLY_INVALID:
    if (!GC_objects_are_marked) {
      GC_mark_state = MS_PUSH_UNCOLLECTABLE;
      break;
    }
    if (ADDR_GE((ptr_t)GC_mark_stack_top, (ptr_t)GC_mark_stack)) {
      MARK_FROM_MARK_STACK();
      GC_ASSERT(GC_mark_state == MS_PARTIALLY_INVALID
                || GC_mark_state == MS_INVALID);
      break;
    }
    if (NULL == GC_scan_ptr && GC_mark_state == MS_INVALID) {
      /*
       * About to start a heap scan for marked objects.
       * Mark stack is empty.  OK to reallocate.
       */
      if (GC_mark_stack_too_small) {
        alloc_mark_stack(2 * GC_mark_stack_size);
      }
      GC_mark_state = MS_PARTIALLY_INVALID;
    }
    GC_scan_ptr = GC_push_next_marked(GC_scan_ptr);
    if (GC_mark_state == MS_PARTIALLY_INVALID)
      push_roots_and_advance(TRUE, cold_gc_frame);
    GC_ASSERT(GC_mark_state == MS_ROOTS_PUSHED
              || GC_mark_state == MS_PARTIALLY_INVALID
              || GC_mark_state == MS_INVALID);
    break;

  default:
    ABORT("GC_mark_some: bad state");
  }
  return FALSE;
}

#ifdef PARALLEL_MARK
GC_INNER GC_bool GC_parallel_mark_disabled = FALSE;
#endif

#ifdef WRAP_MARK_SOME
GC_INNER GC_bool
GC_mark_some(ptr_t cold_gc_frame)
{
  GC_bool ret_val;

  if (GC_no_dls) {
    ret_val = GC_mark_some_inner(cold_gc_frame);
  } else {
    /*
     * Windows appears to asynchronously create and remove writable memory
     * mappings, in particular in case of `DllMain`-based thread tracking.
     * Since we look for writable regions to determine the root set, we may
     * try to mark from an address range that disappeared since we started
     * the collection.  Thus we have to recover from faults here.
     * This code also seems to be necessary for WinCE (at least in the case
     * we would decide to add `MEM_PRIVATE` sections to data roots in
     * `GC_register_dynamic_libraries`).
     *
     * If `USE_PROC_FOR_LIBRARIES` is defined, then we are handling the case
     * in which `/proc` is used for root finding, and we have threads.
     * We may find a stack for a thread that is in the process of exiting,
     * and disappears while we are marking it.  This seems extremely
     * difficult to avoid otherwise.
     */
#  ifndef NO_SEH_AVAILABLE
#    if GC_CLANG_PREREQ(3, 6)
#      pragma GCC diagnostic push
#      pragma GCC diagnostic ignored "-Wlanguage-extension-token"
#    endif
    __try {
      ret_val = GC_mark_some_inner(cold_gc_frame);
    } __except (GetExceptionCode() == EXCEPTION_ACCESS_VIOLATION
                    ? EXCEPTION_EXECUTE_HANDLER
                    : EXCEPTION_CONTINUE_SEARCH) {
      goto handle_ex;
    }
#    if GC_CLANG_PREREQ(3, 6)
#      pragma GCC diagnostic pop
#    endif
#  else
    GC_setup_temporary_fault_handler();
    if (SETJMP(GC_jmp_buf) != 0)
      goto handle_ex;
    ret_val = GC_mark_some_inner(cold_gc_frame);
    GC_reset_fault_handler();
#  endif
  }

#  ifdef HAS_WIN32_THREADS_DISCOVERY
  /*
   * With `DllMain`-based thread tracking, a thread may have started
   * while we were marking.  This is logically equivalent to the
   * exception case; our results are invalid and we have to start over.
   * This cannot be prevented since we cannot block in `DllMain()`.
   */
  if (GC_started_thread_while_stopped())
    goto handle_thr_start;
#  endif
  return ret_val;

handle_ex:
  /* Exception handler starts here for all cases. */
#  if defined(NO_SEH_AVAILABLE)
  GC_reset_fault_handler();
#  endif
  {
    static MAY_THREAD_LOCAL word warned_gc_no;

    /* Report caught `ACCESS_VIOLATION`, once per collection. */
    if (warned_gc_no != GC_gc_no) {
      GC_COND_LOG_PRINTF("Memory mapping disappeared at collection #%lu\n",
                         (unsigned long)GC_gc_no + 1);
      warned_gc_no = GC_gc_no;
    }
  }
#  ifdef HAS_WIN32_THREADS_DISCOVERY
handle_thr_start:
#  endif
  /*
   * We have bad roots on the mark stack - discard it.
   * Rescan from the marked objects; redetermine the roots.
   */
#  ifdef USE_PROC_FOR_LIBRARIES
  {
    size_t idx_p1 = GC_push_root_idx_p1;

    if (0 == idx_p1)
      ABORT("SIGSEGV occurred outside GC_push_conditional_with_exclusions");
    GC_remove_root_at_pos(idx_p1 - 1);
    GC_push_root_idx_p1 = 0;
  }
#  endif
  GC_invalidate_mark_state();
  GC_scan_ptr = NULL;
  return FALSE;
}
#endif /* WRAP_MARK_SOME */

GC_INNER void
GC_invalidate_mark_state(void)
{
  GC_mark_state = MS_INVALID;
  GC_mark_stack_top = GC_mark_stack - 1;
}

GC_ATTR_NOINLINE STATIC mse *
GC_signal_mark_stack_overflow(mse *msp)
{
  GC_mark_state = MS_INVALID;
#ifdef PARALLEL_MARK
  /*
   * We are using a `local_mark_stack` in parallel mode, so do
   * not signal the global mark stack to be resized.
   * That will be done in `GC_return_mark_stack` if required.
   */
  if (!GC_parallel)
    GC_mark_stack_too_small = TRUE;
#else
  GC_mark_stack_too_small = TRUE;
#endif
  GC_COND_LOG_PRINTF("Mark stack overflow; current size: %lu entries\n",
                     (unsigned long)GC_mark_stack_size);
#if defined(CPPCHECK)
  GC_noop1_ptr(msp);
#endif
  return msp - GC_MARK_STACK_DISCARDS;
}

GC_ATTR_NO_SANITIZE_ADDR_MEM_THREAD
GC_INNER mse *
GC_mark_from(mse *mark_stack_top, const mse *mark_stack, mse *mark_stack_limit)
{
  GC_signed_word credit = HBLKSIZE; /*< remaining credit for marking work */
  word descr;
  ptr_t current_p;    /*< pointer to the current candidate pointer */
  ptr_t q;            /*< the candidate pointer itself */
  ptr_t limit = NULL; /*< the limit (incl.) of the current candidate range */
  ptr_t greatest_ha = (ptr_t)GC_greatest_plausible_heap_addr;
  ptr_t least_ha = (ptr_t)GC_least_plausible_heap_addr;
  DECLARE_HDR_CACHE;

#define SPLIT_RANGE_PTRS 128 /*< must be power of 2 */

  GC_objects_are_marked = TRUE;
  INIT_HDR_CACHE;
#if defined(OS2) || CPP_PTRSZ > CPP_WORDSZ
  /* OS/2: avoid the tweaked variant to circumvent a compiler problem. */
  while (ADDR_GE((ptr_t)mark_stack_top, (ptr_t)mark_stack) && credit >= 0)
#else
  while (((((word)mark_stack_top - (word)mark_stack) | (word)credit) & SIGNB)
         == 0)
#endif
  {
    if (UNLIKELY(GC_young_mark_aborted))
      break;
    current_p = mark_stack_top->mse_start;
    descr = mark_stack_top->mse_descr;
#if defined(ESCARGOT_USE_32BIT_IN_64BIT)
    if (UNLIKELY(((word)current_p & 3) != 0)) {
      if (UNLIKELY(((word)current_p & 2) != 0)) {
        ptr_t payload = (ptr_t)((word)current_p & ~(word)2);
        word upper = (word)payload & ~(word)0xffffffffU;
        size_t bytes = descr;
        ptr_t scan_end;

        GC_ASSERT((descr & GC_DS_TAGS) == GC_DS_LENGTH);
        /* Retain a bounded continuation in this entry.  This also limits the
         * number of referents pushed before other marking work can proceed. */
        if (bytes > PTRS_TO_BYTES(SPLIT_RANGE_PTRS)) {
          bytes = PTRS_TO_BYTES(SPLIT_RANGE_PTRS);
          mark_stack_top->mse_start = (ptr_t)((word)(payload + bytes) | 2);
          mark_stack_top->mse_descr = descr - bytes;
        } else {
          --mark_stack_top;
        }
        credit -= (GC_signed_word)bytes;
        scan_end = payload + bytes;
        for (; ADDR_LT(payload, scan_end); payload += 4) {
          unsigned32 low = *(unsigned32 *)payload;

          if (low == 0 || (low & 1) != 0)
            continue;
          q = (ptr_t)(upper | (word)low);
          if (ADDR_LT(least_ha, q) && ADDR_LT(q, greatest_ha)) {
            PREFETCH(q);
            PUSH_CONTENTS(q, mark_stack_top, mark_stack_limit, payload);
          }
        }
        continue;
      }
      {
        const GC_compressed_bitmap_descr *bitmap;
        ptr_t payload;
        word upper;
        size_t slot;
        word bits;

        payload = (ptr_t)((word)current_p & ~(word)1);
        --mark_stack_top;
        if (descr == 0)
          continue;
        bitmap = (const GC_compressed_bitmap_descr *)descr;
        if (bitmap == NULL)
          continue;
        upper = (word)payload & ~(word)0xffffffffU;
        credit -= (GC_signed_word)(bitmap->object_size < HBLKSIZE
                                      ? bitmap->object_size : HBLKSIZE);
        if (bitmap->slots == 0)
          continue;
        if (UNLIKELY(bitmap->slots > GC_WORDSZ)) {
          mark_stack_top = GC_mark_compressed_bitmap_multi(
              payload, bitmap, mark_stack_top, mark_stack_limit,
              least_ha, greatest_ha);
          continue;
        }
        /* Restrict the single word before scanning, including slots ==
         * GC_WORDSZ without ever shifting by the word width. */
        bits = GC_COMPRESSED_BITMAP(bitmap)[0]
               & ~(~(word)0 << (bitmap->slots - 1) << 1);
        while (bits != 0) {
          unsigned32 low;
          ptr_t source;
  #if defined(__GNUC__) || defined(__clang__)
          slot = (unsigned)__builtin_ctzll((unsigned long long)bits);
  #else
          word remaining = bits;
          slot = 0;
          while ((remaining & 1) == 0) {
            remaining >>= 1;
            ++slot;
          }
  #endif
          bits &= bits - 1;
          source = payload + slot * 4;
          low = *(unsigned32 *)source;
          if (slot == bitmap->tagged_slot)
            low &= ~bitmap->tag_mask;
          /* Compressed pointer kinds are even.  Odd slots can hold tagged
           * counts or integer values instead of a pointer. */
          if (low == 0 || (low & 1) != 0)
            continue;
          q = (ptr_t)(upper | (word)low);
          if (ADDR_LT(least_ha, q) && ADDR_LT(q, greatest_ha)) {
            PREFETCH(q);
            PUSH_CONTENTS(q, mark_stack_top, mark_stack_limit, source);
          }
        }
        continue;
      }
    }
#endif
  retry:
    /*
     * `current_p` and `descr` describe the current object.
     * `*mark_stack_top` is vacant.
     * The following is zero only for small objects described by a simple
     * length descriptor.  For many applications this is the common case,
     * so we try to detect it quickly.
     */
    if (descr & (~(word)(PTRS_TO_BYTES(SPLIT_RANGE_PTRS) - 1) | GC_DS_TAGS)) {
      word tag = descr & GC_DS_TAGS;

      GC_STATIC_ASSERT(GC_DS_TAGS == 0x3);
      switch (tag) {
      case GC_DS_LENGTH:
        /*
         * Large length.  Process part of the range to avoid pushing
         * too much on the stack.
         */

        /* Either it is a heap object or a region outside the heap. */
        GC_ASSERT(descr < GC_greatest_real_heap_addr - GC_least_real_heap_addr
                  || GC_least_real_heap_addr + sizeof(ptr_t)
                         >= ADDR(current_p) + descr
                  || ADDR(current_p) >= GC_greatest_real_heap_addr);
#ifdef PARALLEL_MARK
#  define SHARE_BYTES 2048
        if (descr > SHARE_BYTES && GC_parallel
            && ADDR_LT((ptr_t)mark_stack_top, (ptr_t)(mark_stack_limit - 1))) {
          word new_size = (descr >> 1) & ~(word)(sizeof(ptr_t) - 1);

          mark_stack_top->mse_start = current_p;
          /* This makes sure we handle misaligned pointers. */
          mark_stack_top->mse_descr
              = (new_size + sizeof(ptr_t)) | GC_DS_LENGTH;
          mark_stack_top++;
#  ifdef ENABLE_TRACE
          if (ADDR_INSIDE(GC_trace_ptr, current_p, current_p + descr)) {
            GC_log_printf("GC #%lu: large section; start %p, len %lu,"
                          " splitting (parallel) at %p\n",
                          (unsigned long)GC_gc_no, (void *)current_p,
                          (unsigned long)descr,
                          (void *)(current_p + new_size));
          }
#  endif
          current_p += new_size;
          descr -= new_size;
          goto retry;
        }
#endif /* PARALLEL_MARK */
        limit = current_p + PTRS_TO_BYTES(SPLIT_RANGE_PTRS - 1);
        mark_stack_top->mse_start = limit;
        mark_stack_top->mse_descr
            = descr - PTRS_TO_BYTES(SPLIT_RANGE_PTRS - 1);
#ifdef ENABLE_TRACE
        if (ADDR_INSIDE(GC_trace_ptr, current_p, current_p + descr)) {
          GC_log_printf(
              "GC #%lu: large section; start %p, len %lu, splitting at %p\n",
              (unsigned long)GC_gc_no, (void *)current_p, (unsigned long)descr,
              (void *)limit);
        }
#endif
        /*
         * Make sure that pointers overlapping the two ranges are
         * considered.
         */
        limit += sizeof(ptr_t) - ALIGNMENT;
        break;
      case GC_DS_BITMAP:
        mark_stack_top--;
#ifdef ENABLE_TRACE
        if (ADDR_INSIDE(GC_trace_ptr, current_p,
                        current_p + PTRS_TO_BYTES(BITMAP_BITS))) {
          GC_log_printf("GC #%lu: tracing from %p bitmap descr 0x%lx\n",
                        (unsigned long)GC_gc_no, (void *)current_p,
                        (unsigned long)descr);
        }
#endif
        descr &= ~(word)GC_DS_TAGS;
        credit -= (GC_signed_word)PTRS_TO_BYTES(CPP_PTRSZ / 2); /*< guess */
        for (; descr != 0;
             descr <<= 1, current_p += sizeof(ptr_t)) { /*< not `ALIGNMENT` */
          if ((descr & SIGNB) == 0)
            continue;
          LOAD_PTR_OR_CONTINUE(q, current_p);
          FIXUP_POINTER(q);
          if (ADDR_LT(least_ha, q) && ADDR_LT(q, greatest_ha)) {
            PREFETCH(q);
#ifdef ENABLE_TRACE
            if (GC_trace_ptr == current_p) {
              GC_log_printf("GC #%lu: considering(3) %p -> %p\n",
                            (unsigned long)GC_gc_no, (void *)current_p,
                            (void *)q);
            }
#endif
            PUSH_CONTENTS(q, mark_stack_top, mark_stack_limit, current_p);
          }
        }
        continue;
      case GC_DS_PROC:
        mark_stack_top--;
#ifdef ENABLE_TRACE
        if (ADDR_GE(GC_trace_ptr, current_p)) {
          const void *base = GC_base(current_p);

          if (base != NULL && GC_base(GC_trace_ptr) == base) {
            GC_log_printf("GC #%lu: tracing from %p, proc descr 0x%lx\n",
                          (unsigned long)GC_gc_no, (void *)current_p,
                          (unsigned long)descr);
          }
        }
#endif
        credit -= GC_PROC_BYTES;
        mark_stack_top = (*PROC(descr))((word *)current_p, mark_stack_top,
                                        mark_stack_limit, ENV(descr));
        continue;
      case GC_DS_PER_OBJECT:
        if (!(descr & SIGNB)) {
          /* Descriptor is in the object. */
          descr = *(word *)(current_p + descr - GC_DS_PER_OBJECT);
        } else {
          /*
           * Descriptor is in the type descriptor pointed to by the first
           * "pointer-sized" word of the object.
           */
          ptr_t type_descr = *(ptr_t *)current_p;

          /*
           * `type_descr` is either a valid pointer to the descriptor
           * structure, or this object was on a free list.
           * If it was anything but the last object on the free list,
           * we will misinterpret the next object on the free list as
           * the type descriptor, and get a zero GC descriptor, which
           * is ideal.  Unfortunately, we need to check for the last
           * object case explicitly.
           */
          if (UNLIKELY(NULL == type_descr)) {
            mark_stack_top--;
            continue;
          }
          descr = *(word *)(type_descr
                            - ((GC_signed_word)descr
                               + (GC_INDIR_PER_OBJ_BIAS - GC_DS_PER_OBJECT)));
        }
        if (0 == descr) {
          /*
           * Can happen either because we generated a zero GC descriptor
           * or we saw a pointer to a free object.
           */
          mark_stack_top--;
          continue;
        }
        goto retry;
      }
    } else {
      /* Small object with length descriptor. */
      mark_stack_top--;
#ifndef SMALL_CONFIG
      if (descr < sizeof(ptr_t))
        continue;
#endif
#ifdef ENABLE_TRACE
      if (ADDR_INSIDE(GC_trace_ptr, current_p, current_p + descr)) {
        GC_log_printf("GC #%lu: small object; start %p, len %lu\n",
                      (unsigned long)GC_gc_no, (void *)current_p,
                      (unsigned long)descr);
      }
#endif
      limit = current_p + descr;
    }
    /* The simple case in which we are scanning a range. */
    GC_ASSERT((ADDR(current_p) & (ALIGNMENT - 1)) == 0);
    credit -= limit - current_p;
    limit -= sizeof(ptr_t);
    {
#define PREF_DIST 4

#if !defined(SMALL_CONFIG) && !(defined(E2K) && defined(USE_PTR_HWTAG))
      ptr_t deferred;

#  ifdef CHERI_PURECAP
      /*
       * Check each pointer for validity before dereferencing to prevent
       * capability exceptions.  Utilize the pointer meta-data to speed-up
       * the loop.  If the loop is below the pointer bounds, skip the rest
       * of marking for that chunk.  If the limit capability restricts us to
       * reading fewer than size of a pointer, then there cannot possibly be
       * a pointer at `limit`'s pointer, and reading at that location will
       * raise a capability exception.
       */
      {
        word cap_limit = cheri_base_get(limit) + cheri_length_get(limit);

        if (ADDR(limit) + sizeof(ptr_t) > cap_limit) {
          /* Decrement limit so that it to be within bounds of `current_p`. */
          GC_ASSERT(cap_limit > sizeof(ptr_t));
          limit = (ptr_t)cheri_address_set(
              current_p, (cap_limit - sizeof(ptr_t)) & ~(sizeof(ptr_t) - 1));
          goto check_limit;
        }
      }
#  endif
      /*
       * Try to prefetch the next pointer to be examined as soon as possible.
       * Empirically, this also seems to help slightly without prefetches,
       * at least on Linux/i686.  Presumably this loop ends up with less
       * register pressure, and gcc thus ends up generating slightly better
       * code.  Overall gcc code quality for this loop is still not great.
       */
      for (;;) {
        PREFETCH(limit - PREF_DIST * CACHE_LINE_SIZE);
        GC_ASSERT(ADDR_GE(limit, current_p));
#  ifdef CHERI_PURECAP
        if (ADDR(limit) < cheri_base_get(limit))
          goto next_object;
        if (!HAS_TAG_AND_PERM_LOAD(limit)) {
          limit -= ALIGNMENT;
          goto check_limit;
        }
#  endif
        deferred = *(ptr_t *)limit;
        FIXUP_POINTER(deferred);
        limit -= ALIGNMENT;
#  ifdef CHERI_PURECAP
        if (!HAS_TAG_AND_PERM_LOAD(deferred))
          goto check_limit;
#  endif
        if (ADDR_LT(least_ha, deferred) && ADDR_LT(deferred, greatest_ha)) {
          PREFETCH(deferred);
          break;
        }
#  ifndef CHERI_PURECAP
        if (ADDR_LT(limit, current_p))
          goto next_object;
        /*
         * Unroll once, so we do not do too many of the prefetches based
         * on `limit`.
         */
        deferred = *(ptr_t *)limit;
        FIXUP_POINTER(deferred);
        limit -= ALIGNMENT;
        if (ADDR_LT(least_ha, deferred) && ADDR_LT(deferred, greatest_ha)) {
          PREFETCH(deferred);
          break;
        }
#  else
      check_limit:
#  endif
        if (ADDR_LT(limit, current_p))
          goto next_object;
      }
#endif

      for (; ADDR_GE(limit, current_p); current_p += ALIGNMENT) {
        /*
         * Empirically, unrolling this loop does not help a lot.
         * Since `PUSH_CONTENTS` expands to a lot of code, we do not.
         */
        LOAD_PTR_OR_CONTINUE(q, current_p);
        FIXUP_POINTER(q);
        PREFETCH(current_p + PREF_DIST * CACHE_LINE_SIZE);
        if (ADDR_LT(least_ha, q) && ADDR_LT(q, greatest_ha)) {
          /*
           * Prefetch the contents of the object we just pushed.
           * It is likely we will need them soon.
           */
          PREFETCH(q);
#ifdef ENABLE_TRACE
          if (GC_trace_ptr == current_p) {
            GC_log_printf("GC #%lu: considering(1) %p -> %p\n",
                          (unsigned long)GC_gc_no, (void *)current_p,
                          (void *)q);
          }
#endif
          PUSH_CONTENTS(q, mark_stack_top, mark_stack_limit, current_p);
        }
      }

#if !defined(SMALL_CONFIG) && !(defined(E2K) && defined(USE_PTR_HWTAG))
      /*
       * We still need to mark the entry we previously prefetched.
       * We already know that it passes the preliminary pointer validity test.
       */
#  ifdef ENABLE_TRACE
      if (GC_trace_ptr == current_p) {
        GC_log_printf("GC #%lu: considering(2) %p -> %p\n",
                      (unsigned long)GC_gc_no, (void *)current_p,
                      (void *)deferred);
      }
#  endif
      PUSH_CONTENTS(deferred, mark_stack_top, mark_stack_limit, current_p);
    next_object:;
#endif
    }
  }
  return mark_stack_top;
}

GC_API mse * GC_CALL
GC_mark_and_push_ptrs(mse *mark_stack_ptr,
                      mse *mark_stack_limit,
                      struct GC_mark_pair *arr,
                      const int number_of_sub_pointer)
{
  DECLARE_HDR_CACHE;
  INIT_HDR_CACHE;

  ptr_t least_ha = (ptr_t)GC_least_plausible_heap_addr;
  ptr_t greatest_ha = (ptr_t)GC_greatest_plausible_heap_addr;
  for (int j = 0; j < number_of_sub_pointer; j++) {
    if (UNLIKELY(GC_young_mark_aborted))
      break;
    ptr_t q = (ptr_t)arr[j].to;
    if (ADDR_LT(least_ha, q) && ADDR_LT(q, greatest_ha)) {
      PREFETCH(q);
      PUSH_CONTENTS(q, mark_stack_ptr, mark_stack_limit, (ptr_t)arr[j].from);
    }
  }
  return mark_stack_ptr;
}


#ifdef PARALLEL_MARK

/* Note: this is protected by the mark lock. */
STATIC MAY_THREAD_LOCAL GC_bool GC_help_wanted = FALSE;

/* Number of running helpers.  Protected by the mark lock. */
STATIC MAY_THREAD_LOCAL unsigned GC_helper_count = 0;

/*
 * Number of active helpers.  May increase and decrease within each
 * mark cycle; but once it returns to zero, it stays for the cycle.
 * Protected by the mark lock.
 */
STATIC MAY_THREAD_LOCAL unsigned GC_active_count = 0;

GC_INNER MAY_THREAD_LOCAL GC_signed_word GC_fl_builder_count = 0;

#  ifdef LINT2
#    define LOCAL_MARK_STACK_SIZE (HBLKSIZE / 8)
#  else
/*
 * Under normal circumstances, this is big enough to guarantee we do not
 * overflow half of it in a single call to `GC_mark_from`.
 */
#    define LOCAL_MARK_STACK_SIZE HBLKSIZE
#  endif

GC_INNER void
GC_wait_for_markers_init(void)
{
  GC_signed_word count;

  GC_ASSERT(I_HOLD_LOCK());
  if (0 == GC_markers_m1)
    return;

#  ifndef CAN_HANDLE_FORK
  GC_ASSERT(NULL == GC_main_local_mark_stack);
#  else
  if (NULL == GC_main_local_mark_stack)
#  endif
  {
    size_t bytes_to_get
        = ROUNDUP_PAGESIZE_IF_MMAP(LOCAL_MARK_STACK_SIZE * sizeof(mse));

    /*
     * Allocate the local mark stack for the thread that holds the
     * allocator lock.
     */
    GC_ASSERT(GC_page_size != 0);
    GC_main_local_mark_stack = (mse *)GC_os_get_mem(bytes_to_get);
    if (NULL == GC_main_local_mark_stack)
      ABORT("Insufficient memory for main local_mark_stack");
  }

  /*
   * Reuse the mark lock and builders count to synchronize marker threads
   * startup.
   */
  GC_acquire_mark_lock();
  GC_fl_builder_count += GC_markers_m1;
  count = GC_fl_builder_count;
  GC_release_mark_lock();
  if (count != 0) {
    GC_ASSERT(count > 0);
    GC_wait_for_reclaim();
  }
}

/*
 * Steal mark stack entries starting at `mse` `low` into mark stack `local`
 * until we either steal `mse` `high`, or we have `n_to_get` entries.
 * Return a pointer to the top of the local mark stack.  `*next` is replaced
 * by a pointer to the next unscanned mark stack entry.
 */
STATIC mse *
GC_steal_mark_stack(mse *low, mse *high, mse *local, size_t n_to_get,
                    mse **next)
{
  mse *p;
  mse *top = local - 1;
  size_t i = 0;

  GC_ASSERT(ADDR_GE((ptr_t)high, (ptr_t)(low - 1))
            && (word)(high - low + 1) <= GC_mark_stack_size);
  for (p = low; ADDR_GE((ptr_t)high, (ptr_t)p) && i <= n_to_get; ++p) {
    word descr = AO_load(&p->mse_descr);

    if (descr != 0) {
      /* Must be ordered after read of `mse_descr`. */
      AO_store_release_write(&p->mse_descr, 0);
      /*
       * More than one thread may get this entry, but that is only
       * a minor performance problem.
       */
      ++top;
      top->mse_start = p->mse_start;
      top->mse_descr = descr;
      GC_ASSERT((descr & GC_DS_TAGS) != GC_DS_LENGTH /* 0 */
                || descr < GC_greatest_real_heap_addr - GC_least_real_heap_addr
                || GC_least_real_heap_addr + sizeof(ptr_t)
                       >= ADDR(p->mse_start) + descr
                || ADDR(p->mse_start) >= GC_greatest_real_heap_addr);
      /* If this is a big object, count it as `descr / 256 + 1` objects. */
      ++i;
      if ((descr & GC_DS_TAGS) == GC_DS_LENGTH)
        i += (size_t)(descr >> 8);
    }
  }
  *next = p;
  return top;
}

/* Copy back a local mark stack.  `low` and `high` are inclusive bounds. */
STATIC void
GC_return_mark_stack(mse *low, mse *high)
{
  mse *my_top;
  mse *my_start;
  size_t stack_size;

  if (ADDR_LT((ptr_t)high, (ptr_t)low))
    return;
  stack_size = high - low + 1;
  GC_acquire_mark_lock();
  /* Note: the concurrent modification is impossible. */
  my_top = GC_mark_stack_top;
  my_start = my_top + 1;
  if ((word)(my_start - GC_mark_stack + stack_size)
      > (word)GC_mark_stack_size) {
    GC_COND_LOG_PRINTF("No room to copy back mark stack\n");
    GC_mark_state = MS_INVALID;
    GC_mark_stack_too_small = TRUE;
    /* We drop the local mark stack.  We will fix things later. */
  } else {
    BCOPY(low, my_start, stack_size * sizeof(mse));
    GC_ASSERT((mse *)GC_cptr_load((volatile ptr_t *)&GC_mark_stack_top)
              == my_top);
    /* Ensures visibility of previously written stack contents. */
    GC_cptr_store_release_write((volatile ptr_t *)&GC_mark_stack_top,
                                (ptr_t)(my_top + stack_size));
  }
  GC_release_mark_lock();
  GC_notify_all_marker();
}

#  ifndef N_LOCAL_ITERS
#    define N_LOCAL_ITERS 1
#  endif

/*
 * Note: called only when the local and the main mark stacks are both
 * empty.
 */
static GC_bool
has_inactive_helpers(void)
{
  GC_bool res;

  GC_acquire_mark_lock();
  res = GC_active_count < GC_helper_count;
  GC_release_mark_lock();
  return res;
}

/*
 * Mark from the local mark stack.  On return, the local mark stack
 * is empty.  But this may be achieved by copying the local mark stack
 * back into the global one.  We do not hold the mark lock.
 */
STATIC void
GC_do_local_mark(mse *local_mark_stack, mse *local_top)
{
  unsigned n;

  for (;;) {
    for (n = 0; n < N_LOCAL_ITERS; ++n) {
      local_top = GC_mark_from(local_top, local_mark_stack,
                               local_mark_stack + LOCAL_MARK_STACK_SIZE);
      if (ADDR_LT((ptr_t)local_top, (ptr_t)local_mark_stack))
        return;
      if ((word)(local_top - local_mark_stack) >= LOCAL_MARK_STACK_SIZE / 2) {
        GC_return_mark_stack(local_mark_stack, local_top);
        return;
      }
    }
    if (ADDR_LT(GC_cptr_load((volatile ptr_t *)&GC_mark_stack_top),
                GC_cptr_load(&GC_first_nonempty))
        && ADDR_LT((ptr_t)(local_mark_stack + 1), (ptr_t)local_top)
        && has_inactive_helpers()) {
      /*
       * Try to share the load, since the main stack is empty, and the helper
       * threads are waiting for a refill.  The entries near the bottom of
       * the stack are likely to require more work.  Thus we return those,
       * even though it is harder.
       */
      mse *new_bottom = local_mark_stack + (local_top - local_mark_stack) / 2;

      GC_ASSERT(ADDR_LT((ptr_t)local_mark_stack, (ptr_t)new_bottom)
                && ADDR_LT((ptr_t)new_bottom, (ptr_t)local_top));
      GC_return_mark_stack(local_mark_stack, new_bottom - 1);
      memmove(local_mark_stack, new_bottom,
              (local_top - new_bottom + 1) * sizeof(mse));
      local_top -= new_bottom - local_mark_stack;
    }
  }
}

#  ifndef ENTRIES_TO_GET
#    define ENTRIES_TO_GET 5
#  endif

/*
 * Mark using the local mark stack until the global mark stack is empty and
 * there are no active workers.  Update `GC_first_nonempty` to reflect the
 * progress.  Caller holds the mark lock.  Caller has already incremented
 * `GC_helper_count`; we decrement it, and maintain `GC_active_count`.
 */
STATIC void
GC_mark_local(mse *local_mark_stack, int id)
{
  mse *my_first_nonempty;

  GC_active_count++;
  my_first_nonempty = (mse *)GC_cptr_load(&GC_first_nonempty);
  GC_ASSERT(ADDR_GE((ptr_t)my_first_nonempty, (ptr_t)GC_mark_stack));
  GC_ASSERT(
      ADDR_GE(GC_cptr_load((volatile ptr_t *)&GC_mark_stack_top) + sizeof(mse),
              (ptr_t)my_first_nonempty));
  GC_VERBOSE_LOG_PRINTF("Starting mark helper %d\n", id);
  GC_release_mark_lock();
  for (;;) {
    size_t n_on_stack, n_to_get;
    mse *my_top, *local_top;
    mse *global_first_nonempty = (mse *)GC_cptr_load(&GC_first_nonempty);

    GC_ASSERT(ADDR_GE((ptr_t)my_first_nonempty, (ptr_t)GC_mark_stack)
              && ADDR_GE(GC_cptr_load((volatile ptr_t *)&GC_mark_stack_top)
                             + sizeof(mse),
                         (ptr_t)my_first_nonempty));
    GC_ASSERT(ADDR_GE((ptr_t)global_first_nonempty, (ptr_t)GC_mark_stack));
    if (ADDR_LT((ptr_t)my_first_nonempty, (ptr_t)global_first_nonempty)) {
      my_first_nonempty = global_first_nonempty;
    } else if (ADDR_LT((ptr_t)global_first_nonempty,
                       (ptr_t)my_first_nonempty)) {
      (void)GC_cptr_compare_and_swap(&GC_first_nonempty,
                                     (ptr_t)global_first_nonempty,
                                     (ptr_t)my_first_nonempty);
      /*
       * If this fails, then we just go ahead, without updating
       * `GC_first_nonempty`.
       */
    }
    /*
     * Perhaps we should also update `GC_first_nonempty`, if it is less.
     * But that would require usage of the atomic updates.
     */
    my_top = (mse *)GC_cptr_load_acquire((volatile ptr_t *)&GC_mark_stack_top);
    if (ADDR_LT((ptr_t)my_top, (ptr_t)my_first_nonempty)) {
      GC_acquire_mark_lock();
      /*
       * Note: asynchronous modification is impossible here, since
       * we hold the mark lock.
       */
      my_top = GC_mark_stack_top;
      n_on_stack = my_top - my_first_nonempty + 1;
      if (0 == n_on_stack) {
        GC_active_count--;
        GC_ASSERT(GC_active_count <= GC_helper_count);
        /* Other markers may redeposit objects on the stack. */
        if (0 == GC_active_count)
          GC_notify_all_marker();
        while (GC_active_count > 0
               && ADDR_LT((ptr_t)GC_mark_stack_top,
                          GC_cptr_load(&GC_first_nonempty))) {
          /*
           * We will be notified if either `GC_active_count` reaches zero,
           * or if more objects are pushed on the global mark stack.
           */
          GC_wait_marker();
        }
        if (0 == GC_active_count
            && ADDR_LT((ptr_t)GC_mark_stack_top,
                       GC_cptr_load(&GC_first_nonempty))) {
          GC_bool need_to_notify = FALSE;

          /*
           * The above conditions cannot be falsified while we hold
           * the mark lock, since neither `GC_active_count` nor
           * `GC_mark_stack_top` can change.  `GC_first_nonempty` can
           * only be incremented asynchronously.  Thus we know that
           * both conditions are actually held simultaneously.
           */
          GC_helper_count--;
          if (0 == GC_helper_count)
            need_to_notify = TRUE;
          GC_VERBOSE_LOG_PRINTF("Finished mark helper %d\n", id);
          if (need_to_notify)
            GC_notify_all_marker();
          return;
        }
        /*
         * Else there is something on the stack again, or another helper
         * may push something.
         */
        GC_active_count++;
        GC_ASSERT(GC_active_count > 0);
        GC_release_mark_lock();
        continue;
      } else {
        GC_release_mark_lock();
      }
    } else {
      n_on_stack = my_top - my_first_nonempty + 1;
    }
    n_to_get = ENTRIES_TO_GET;
    if (n_on_stack < 2 * ENTRIES_TO_GET)
      n_to_get = 1;
    local_top
        = GC_steal_mark_stack(my_first_nonempty, my_top, local_mark_stack,
                              n_to_get, &my_first_nonempty);
    GC_ASSERT(ADDR_GE((ptr_t)my_first_nonempty, (ptr_t)GC_mark_stack)
              && ADDR_GE(GC_cptr_load((volatile ptr_t *)&GC_mark_stack_top)
                             + sizeof(mse),
                         (ptr_t)my_first_nonempty));
    GC_do_local_mark(local_mark_stack, local_top);
  }
}

/*
 * Perform parallel mark.  We hold the allocator lock, but not the mark lock.
 * Currently runs until the mark stack is empty.
 */
STATIC void
GC_do_parallel_mark(void)
{
  GC_ASSERT(I_HOLD_LOCK());
  GC_acquire_mark_lock();
  GC_ASSERT(!GC_help_wanted);
  GC_ASSERT(0 == GC_active_count && 0 == GC_helper_count);
  GC_VERBOSE_LOG_PRINTF("Starting marking for mark phase number %lu\n",
                        (unsigned long)GC_mark_no);

  GC_cptr_store(&GC_first_nonempty, (ptr_t)GC_mark_stack);
  GC_active_count = 0;
  GC_helper_count = 1;
  GC_help_wanted = TRUE;
  /* Wake up potential helpers. */
  GC_notify_all_marker();
  GC_mark_local(GC_main_local_mark_stack, 0);
  GC_help_wanted = FALSE;
  /* Done; clean up. */
  while (GC_helper_count > 0) {
    GC_wait_marker();
  }
  /* `GC_helper_count` cannot be incremented while not `GC_help_wanted`. */
  GC_VERBOSE_LOG_PRINTF("Finished marking for mark phase number %lu\n",
                        (unsigned long)GC_mark_no);
  GC_mark_no++;
  GC_release_mark_lock();
  GC_notify_all_marker();
}

GC_INNER void
GC_help_marker(word my_mark_no)
{
#  define my_id my_id_mse.mse_descr
  /*
   * Put `my_id` inside the structure to keep `local_mark_stack` aligned
   * explicitly.
   */
  mse my_id_mse;
  mse local_mark_stack[LOCAL_MARK_STACK_SIZE];
  /* Note: `local_mark_stack` is quite big (up to 128 KiB). */

  GC_ASSERT(I_DONT_HOLD_LOCK());
  GC_ASSERT(GC_parallel);
  while (GC_mark_no < my_mark_no
         || (!GC_help_wanted && GC_mark_no == my_mark_no)) {
    GC_wait_marker();
  }
  my_id = GC_helper_count;
  if (GC_mark_no != my_mark_no || my_id > (unsigned)GC_markers_m1) {
    /*
     * The second test is useful only if the original threads can also
     * act as helpers.  Under Linux they cannot.
     */
    return;
  }
  GC_helper_count = (unsigned)my_id + 1;
  GC_mark_local(local_mark_stack, (int)my_id);
  /* `GC_mark_local` decrements `GC_helper_count`. */
#  undef my_id
}

#endif /* PARALLEL_MARK */

/*
 * Allocate or reallocate space for mark stack of size `n` entries.
 * May silently fail.
 */
static void
alloc_mark_stack(size_t n)
{
  mse *new_stack;
#ifdef GWW_VDB
  GC_bool recycle_old;
#endif

  GC_ASSERT(I_HOLD_LOCK());
  new_stack = (mse *)GC_scratch_alloc(n * sizeof(struct GC_ms_entry));
#ifdef GWW_VDB
  /*
   * Do not recycle a stack segment obtained with the wrong flags.
   * Win32 `GetWriteWatch` requires the right kind of memory.
   */
  recycle_old = !GC_auto_incremental || GC_incremental_at_stack_alloc;
  GC_incremental_at_stack_alloc = GC_auto_incremental;
#endif

  GC_mark_stack_too_small = FALSE;
  if (GC_mark_stack != NULL) {
    if (new_stack != NULL) {
#ifdef GWW_VDB
      if (recycle_old)
#endif
      {
        /* Recycle old space. */
        GC_scratch_recycle_inner(
            GC_mark_stack, GC_mark_stack_size * sizeof(struct GC_ms_entry));
      }
      GC_mark_stack = new_stack;
      GC_mark_stack_size = n;
      /* FIXME: Do we need some way to reset `GC_mark_stack_size`? */
      GC_mark_stack_limit = new_stack + n;
      GC_COND_LOG_PRINTF("Grew mark stack to %lu frames\n",
                         (unsigned long)GC_mark_stack_size);
    } else {
      WARN("Failed to grow mark stack to %" WARN_PRIuPTR " frames\n", n);
    }
  } else if (NULL == new_stack) {
    GC_err_printf("No space for mark stack\n");
    EXIT();
  } else {
    GC_mark_stack = new_stack;
    GC_mark_stack_size = n;
    GC_mark_stack_limit = new_stack + n;
  }
  GC_mark_stack_top = GC_mark_stack - 1;
}

GC_INNER void
GC_mark_init(void)
{
  alloc_mark_stack(INITIAL_MARK_STACK_SIZE);
}

GC_API void GC_CALL
GC_push_all(void *bottom, void *top)
{
  GC_mark_stack_top
      = GC_ms_push_all(bottom, top, GC_mark_stack_top, GC_mark_stack_limit);
}

GC_API struct GC_ms_entry *GC_CALL
GC_ms_push_all(void *bottom, void *top, struct GC_ms_entry *mark_stack_top,
               struct GC_ms_entry *mark_stack_limit)
{
  word length;

  bottom = PTR_ALIGN_UP((ptr_t)bottom, ALIGNMENT);
  top = PTR_ALIGN_DOWN((ptr_t)top, ALIGNMENT);
  if (ADDR_GE((ptr_t)bottom, (ptr_t)top))
    return mark_stack_top;

  length = (word)((ptr_t)top - (ptr_t)bottom);
#if GC_DS_TAGS > ALIGNMENT - 1
  length = (length + GC_DS_TAGS) & ~(word)GC_DS_TAGS; /*< round up */
#endif
  return GC_ms_push_obj_descr(bottom, length | GC_DS_LENGTH, mark_stack_top,
                              mark_stack_limit);
}

GC_API struct GC_ms_entry *GC_CALL
GC_ms_push_obj_descr(void *obj, GC_word descr,
                     struct GC_ms_entry *mark_stack_top,
                     struct GC_ms_entry *mark_stack_limit)
{
  mark_stack_top++;
  if (ADDR_GE((ptr_t)mark_stack_top, (ptr_t)mark_stack_limit)) {
    mark_stack_top = GC_signal_mark_stack_overflow(mark_stack_top);
  }
  mark_stack_top->mse_start = (ptr_t)obj;
  mark_stack_top->mse_descr = descr;
  return mark_stack_top;
}

GC_API void GC_CALL
GC_push_obj_descr(void *obj, GC_word descr)
{
  GC_mark_stack_top = GC_ms_push_obj_descr(obj, descr, GC_mark_stack_top,
                                           GC_mark_stack_limit);
}

#ifndef GC_DISABLE_INCREMENTAL

typedef GC_bool (*dirty_func_t)(const struct hblk *);

/*
 * Analogous to `GC_push_all`, but push only those pages `h` with
 * `dirty_fn(h) != 0`.  We use `GC_push_all` to actually push the block.
 * Used both to selectively push dirty pages, or to push a block in
 * a piecemeal fashion, to allow for more marking concurrency.
 * Will not overflow mark stack if `GC_push_all` pushes a small fixed
 * number of entries.  (This is invoked only if `GC_push_all` pushes
 * a single entry, or if it marks each object before pushing it, thus
 * ensuring progress in the event of a stack overflow.)
 */
STATIC void
GC_push_selected(ptr_t bottom, ptr_t top, dirty_func_t dirty_fn)
{
  struct hblk *h;

  bottom = PTR_ALIGN_UP(bottom, ALIGNMENT);
  top = PTR_ALIGN_DOWN(top, ALIGNMENT);
  if (ADDR_GE(bottom, top))
    return;

  h = HBLKPTR(bottom + HBLKSIZE); /*< round up to the next block */
  if (ADDR_GE((ptr_t)h, top)) {
    if ((*dirty_fn)(h - 1)) {
      GC_push_all(bottom, top);
    }
    return;
  }
  if ((*dirty_fn)(h - 1)) {
    if ((word)(GC_mark_stack_top - GC_mark_stack)
        > 3 * GC_mark_stack_size / 4) {
      GC_push_all(bottom, top);
      return;
    }
    GC_push_all(bottom, h);
  }

  while (ADDR_GE(top, (ptr_t)(h + 1))) {
    if ((*dirty_fn)(h)) {
      if ((word)(GC_mark_stack_top - GC_mark_stack)
          > 3 * GC_mark_stack_size / 4) {
        /* Danger of mark stack overflow. */
        GC_push_all(h, top);
        return;
      } else {
        GC_push_all(h, h + 1);
      }
    }
    h++;
  }

  if ((ptr_t)h != top && (*dirty_fn)(h)) {
    GC_push_all(h, top);
  }
}

GC_API void GC_CALL
GC_push_conditional(void *bottom, void *top, int all)
{
  if (!all) {
    GC_push_selected((ptr_t)bottom, (ptr_t)top, GC_page_was_dirty);
  } else {
#  ifdef PROC_VDB
    if (GC_auto_incremental) {
      /* Pages that were never dirtied cannot contain pointers. */
      GC_push_selected((ptr_t)bottom, (ptr_t)top, GC_page_was_ever_dirty);
    } else
#  endif
    /* else */ {
      GC_push_all(bottom, top);
    }
  }
}

#  if !defined(NO_VDB_FOR_STATIC_ROOTS) && !defined(PROC_VDB)
/*
 * Same as `GC_page_was_dirty` but `h` is allowed to point to some page
 * in the registered static roots only.  Not used if the manual VDB is on.
 */
STATIC GC_bool
GC_static_page_was_dirty(const struct hblk *h)
{
  return get_pht_entry_from_index(GC_grungy_pages, PHT_HASH(h));
}
#  endif

#else
GC_API void GC_CALL
GC_push_conditional(void *bottom, void *top, int all)
{
  UNUSED_ARG(all);
  GC_push_all(bottom, top);
}
#endif /* GC_DISABLE_INCREMENTAL */

#if !defined(NO_VDB_FOR_STATIC_ROOTS) || defined(USE_PROC_FOR_LIBRARIES)
GC_INNER void
GC_push_conditional_static(void *bottom, void *top, GC_bool all)
{
#  if defined(USE_PROC_FOR_LIBRARIES) && defined(WRAP_MARK_SOME)
  if (LIKELY(ADDR_LT((ptr_t)bottom, (ptr_t)top))) {
    CHECK_MEMORY_READ(bottom);
    CHECK_MEMORY_READ((ptr_t)top - 1);
  }
#  endif
#  ifdef PROC_VDB
  /*
   * Just redirect to the generic routine because `PROC_VDB`
   * implementation gets the dirty bits map for the whole process memory.
   */
  GC_push_conditional(bottom, top, all);
#  else
#    ifndef NO_VDB_FOR_STATIC_ROOTS
  if (!all && GC_is_vdb_for_static_roots()) {
    GC_push_selected((ptr_t)bottom, (ptr_t)top, GC_static_page_was_dirty);
  } else
#    endif
  /* else */ {
    GC_push_all(bottom, top);
    UNUSED_ARG(all);
  }
#  endif
}
#endif

#if defined(DARWIN) && defined(THREADS)
void
GC_push_one(word p)
{
  GC_PUSH_ONE_STACK((ptr_t)p, MARKED_FROM_REGISTER);
#  if defined(ESCARGOT_USE_32BIT_IN_64BIT)
  if (GC_cage_base != 0) {
    word low = (word)(unsigned32)p;
    word high = (word)(unsigned32)(p >> 32);
    if (low > 0x1e && !(low & 1))
      GC_PUSH_ONE_STACK((ptr_t)(GC_cage_base + low), MARKED_FROM_REGISTER);
    if (high > 0x1e && !(high & 1))
      GC_PUSH_ONE_STACK((ptr_t)(GC_cage_base + high), MARKED_FROM_REGISTER);
  }
#  endif
}
#endif /* DARWIN && THREADS */

#if defined(GC_WIN32_THREADS)
GC_INNER void
GC_push_many_regs(const word *regs, unsigned count)
{
  unsigned i;

  for (i = 0; i < count; i++)
    GC_PUSH_ONE_STACK((ptr_t)regs[i], MARKED_FROM_REGISTER);
}
#endif /* GC_WIN32_THREADS */

#if defined(ESCARGOT_USE_32BIT_IN_64BIT)
GC_API struct GC_ms_entry *GC_CALL
GC_push_32bit_range(const void *start, size_t bytes, mse *mark_stack_top,
                    mse *mark_stack_limit)
{
  GC_ASSERT((ADDR(start) & 3) == 0);
  GC_ASSERT((bytes & 3) == 0);
  if (bytes == 0)
    return mark_stack_top;
  return GC_ms_push_obj_descr((ptr_t)(ADDR(start) | 2), (word)bytes,
                              mark_stack_top, mark_stack_limit);
}
#endif

GC_API struct GC_ms_entry *GC_CALL
GC_mark_and_push(void *obj, mse *mark_stack_top, mse *mark_stack_limit,
                 void **src)
{
  hdr *hhdr = NULL;

  PREFETCH(obj);
  if (GC_target_probe((ptr_t)obj, &hhdr))
    return mark_stack_top;
  if (hhdr == NULL)
    GET_HDR(obj, hhdr);
  if ((UNLIKELY(IS_FORWARDING_ADDR_OR_NIL(hhdr))
       && (!GC_all_interior_pointers
           || NULL == (hhdr = GC_find_header(GC_base(obj)))))
      || UNLIKELY(HBLK_IS_FREE(hhdr))) {
    GC_ADD_TO_BLACK_LIST_NORMAL((ptr_t)obj, (ptr_t)src);
    return mark_stack_top;
  }
  return GC_ms_push_contents_hdr((ptr_t)obj, hhdr, mark_stack_top,
                                 mark_stack_limit, (ptr_t)src, TRUE);
}

GC_ATTR_NO_SANITIZE_ADDR
GC_INNER void
#if defined(PRINT_BLACK_LIST) || defined(KEEP_BACK_PTRS)
GC_mark_and_push_stack(ptr_t p, ptr_t source)
#else
GC_mark_and_push_stack(ptr_t p)
#  define source ((ptr_t)NULL)
#endif
{
  hdr *hhdr;
  ptr_t r = p;

  PREFETCH(p);
  GET_HDR(p, hhdr);
  if (UNLIKELY(IS_FORWARDING_ADDR_OR_NIL(hhdr))) {
    if (NULL == hhdr || (r = (ptr_t)GC_base(p)) == NULL
        || (hhdr = HDR(r)) == NULL) {
      GC_ADD_TO_BLACK_LIST_STACK(p, source);
      return;
    }
  }
  if (UNLIKELY(HBLK_IS_FREE(hhdr))) {
    GC_ADD_TO_BLACK_LIST_NORMAL(p, source);
    return;
  }
#ifdef THREADS
  /*
   * Pointer is on the stack.  We may have dirtied the object it points to,
   * but have not called `GC_dirty` yet.
   */
  GC_dirty(p); /*< entire object */
#endif
  GC_mark_stack_top = GC_ms_push_contents_hdr(
      r, hhdr, GC_mark_stack_top, GC_mark_stack_limit, source, FALSE);
  /*
   * We silently ignore pointers to near the end of a block, which is
   * very mildly suboptimal.
   */
  /* FIXME: We should probably add a header word to address this. */
#undef source
}

#ifdef TRACE_BUF
#  ifndef TRACE_ENTRIES
#    define TRACE_ENTRIES 1000
#  endif

struct trace_entry {
  const char *caller_fn_name;
  word gc_no;
  word bytes_allocd;
  GC_hidden_pointer arg1;
  GC_hidden_pointer arg2;
} GC_trace_buf[TRACE_ENTRIES] = { { (const char *)NULL, 0, 0, 0, 0 } };

void
GC_add_trace_entry(const char *caller_fn_name, ptr_t arg1, ptr_t arg2)
{
  size_t i = GC_trace_buf_pos;

  GC_trace_buf[i].caller_fn_name = caller_fn_name;
  GC_trace_buf[i].gc_no = GC_gc_no;
  GC_trace_buf[i].bytes_allocd = GC_bytes_allocd;
  GC_trace_buf[i].arg1 = GC_HIDE_POINTER(arg1);
  GC_trace_buf[i].arg2 = GC_HIDE_POINTER(arg2);
  i++;
  if (i >= TRACE_ENTRIES)
    i = 0;
  GC_trace_buf_pos = i;
}

GC_API void GC_CALL
GC_print_trace_inner(GC_word gc_no)
{
  size_t i;

  for (i = GC_trace_buf_pos;; i--) {
    struct trace_entry *p;

    if (0 == i)
      i = TRACE_ENTRIES;
    p = &GC_trace_buf[i - 1];
    /*
     * Compare `gc_no` values (`p->gc_no` is less than given `gc_no`)
     * taking into account that the counter may overflow.
     */
    if (((p->gc_no - gc_no) & SIGNB) != 0 || NULL == p->caller_fn_name) {
      return;
    }
    GC_printf("Trace:%s (gc:%lu, bytes:%lu) %p, %p\n", p->caller_fn_name,
              (unsigned long)p->gc_no, (unsigned long)p->bytes_allocd,
              GC_REVEAL_POINTER(p->arg1), GC_REVEAL_POINTER(p->arg2));
    if (i == GC_trace_buf_pos + 1)
      break;
  }
  GC_printf("Trace incomplete\n");
}

GC_API void GC_CALL
GC_print_trace(GC_word gc_no)
{
  READER_LOCK();
  GC_print_trace_inner(gc_no);
  READER_UNLOCK();
}
#endif /* TRACE_BUF */

GC_ATTR_NO_SANITIZE_ADDR_MEM_THREAD
GC_API void GC_CALL
GC_push_all_eager(void *bottom, void *top)
{
  REGISTER ptr_t current_p;
  REGISTER word lim_addr;
  REGISTER ptr_t greatest_ha = (ptr_t)GC_greatest_plausible_heap_addr;
  REGISTER ptr_t least_ha = (ptr_t)GC_least_plausible_heap_addr;
#define GC_greatest_plausible_heap_addr greatest_ha
#define GC_least_plausible_heap_addr least_ha

  if (NULL == top)
    return;
  /* Check all pointers in range and push if they appear to be valid. */
  current_p = PTR_ALIGN_UP((ptr_t)bottom, ALIGNMENT);
  lim_addr = ADDR(PTR_ALIGN_DOWN((ptr_t)top, ALIGNMENT)) - sizeof(ptr_t);
#ifdef CHERI_PURECAP
  {
    word cap_limit = cheri_base_get(current_p) + cheri_length_get(current_p);

    if (lim_addr >= cap_limit)
      lim_addr = cap_limit - sizeof(ptr_t);
  }
#endif
  for (; ADDR(current_p) <= lim_addr; current_p += ALIGNMENT) {
    REGISTER ptr_t q;

    LOAD_PTR_OR_CONTINUE(q, current_p);
    GC_PUSH_ONE_STACK(q, current_p);
#if defined(ESCARGOT_USE_32BIT_IN_64BIT)
    /* A compressed heap reference may occupy either half of this word,
     * including a callee-saved register spilled into a GC stack frame. */
    {
      word low = (word)(unsigned32)(word)q;
      word high = (word)(unsigned32)((word)q >> 32);
      if (GC_cage_base && low > 0x1e && !(low & 1))
        GC_PUSH_ONE_STACK((ptr_t)(GC_cage_base + low), current_p);
      if (GC_cage_base && high > 0x1e && !(high & 1))
        GC_PUSH_ONE_STACK((ptr_t)(GC_cage_base + high),
                          current_p + sizeof(unsigned32));
    }
#endif
  }
#undef GC_greatest_plausible_heap_addr
#undef GC_least_plausible_heap_addr
}

#if !defined(NEED_FIXUP_POINTER) && !defined(NO_ALL_INTERIOR_POINTERS)   \
    && (!defined(STACK_NOT_SCANNED) || defined(IA64) || defined(THREADS) \
        || (defined(EMSCRIPTEN) && defined(EMSCRIPTEN_ASYNCIFY)))
GC_INNER void
GC_push_all_stack(void *bottom, void *top)
{
  GC_ASSERT(I_HOLD_LOCK());
#if defined(ESCARGOT_USE_32BIT_IN_64BIT)
  /* Deferred descriptor scanning only considers pointer-sized words. */
  GC_push_all_eager(bottom, top);
#else
  if (GC_all_interior_pointers
#  if defined(THREADS) && defined(MPROTECT_VDB)
      /* TODO: Should we avoid `GC_push_all()` if using `userfaultfd`? */
      && !GC_is_mprotect_vdb()
#  endif
      && ADDR_LT((ptr_t)GC_mark_stack_top,
                 (ptr_t)(GC_mark_stack_limit - INITIAL_MARK_STACK_SIZE / 8))) {
    GC_push_all(bottom, top);
  } else {
    GC_push_all_eager(bottom, top);
  }
#endif
}
#endif

#if defined(WRAP_MARK_SOME) && defined(PARALLEL_MARK)
GC_ATTR_NO_SANITIZE_ADDR_MEM_THREAD
GC_INNER void
GC_push_conditional_eager(void *bottom, void *top, GC_bool all)
{
  REGISTER ptr_t current_p;
  REGISTER ptr_t lim;
  REGISTER ptr_t greatest_ha = (ptr_t)GC_greatest_plausible_heap_addr;
  REGISTER ptr_t least_ha = (ptr_t)GC_least_plausible_heap_addr;
#  define GC_greatest_plausible_heap_addr greatest_ha
#  define GC_least_plausible_heap_addr least_ha

  if (NULL == top)
    return;

  /* TODO: If not `all`, then scan only dirty pages. */
  (void)all;

  current_p = PTR_ALIGN_UP((ptr_t)bottom, ALIGNMENT);
  lim = PTR_ALIGN_DOWN((ptr_t)top, ALIGNMENT) - sizeof(ptr_t);
  for (; ADDR_GE(lim, current_p); current_p += ALIGNMENT) {
    REGISTER ptr_t q;

    LOAD_PTR_OR_CONTINUE(q, current_p);
    GC_PUSH_ONE_HEAP(q, current_p, GC_mark_stack_top);
  }
#  undef GC_greatest_plausible_heap_addr
#  undef GC_least_plausible_heap_addr
}
#endif /* WRAP_MARK_SOME && PARALLEL_MARK */

#if !defined(SMALL_CONFIG) && !defined(USE_MARK_BYTES) \
    && !defined(MARK_BIT_PER_OBJ) && GC_GRANULE_PTRS <= 4
#  define USE_PUSH_MARKED_ACCELERATORS
#  if GC_GRANULE_PTRS == 1
#    define PUSH_GRANULE(q)                                 \
      do {                                                  \
        ptr_t q_contents = (q)[0];                          \
        GC_PUSH_ONE_HEAP(q_contents, q, GC_mark_stack_top); \
      } while (0)
#  elif GC_GRANULE_PTRS == 2
#    define PUSH_GRANULE(q)                                       \
      do {                                                        \
        ptr_t q_contents = (q)[0];                                \
        GC_PUSH_ONE_HEAP(q_contents, q, GC_mark_stack_top);       \
        q_contents = (q)[1];                                      \
        GC_PUSH_ONE_HEAP(q_contents, (q) + 1, GC_mark_stack_top); \
      } while (0)
#  else
#    define PUSH_GRANULE(q)                                       \
      do {                                                        \
        ptr_t q_contents = (q)[0];                                \
        GC_PUSH_ONE_HEAP(q_contents, q, GC_mark_stack_top);       \
        q_contents = (q)[1];                                      \
        GC_PUSH_ONE_HEAP(q_contents, (q) + 1, GC_mark_stack_top); \
        q_contents = (q)[2];                                      \
        GC_PUSH_ONE_HEAP(q_contents, (q) + 2, GC_mark_stack_top); \
        q_contents = (q)[3];                                      \
        GC_PUSH_ONE_HEAP(q_contents, (q) + 3, GC_mark_stack_top); \
      } while (0)
#  endif

/*
 * Push all objects reachable from marked objects in the given block
 * containing objects of size 1 granule.
 */
GC_ATTR_NO_SANITIZE_THREAD
STATIC void
GC_push_marked1(struct hblk *h, const hdr *hhdr)
{
  const word *mark_word_addr
      = (word *)CAST_AWAY_VOLATILE_PVOID(hhdr->hb_marks);
  ptr_t *p;
  ptr_t plim;

  /*
   * Allow registers to be used for some frequently accessed global variables.
   * Otherwise aliasing issues are likely to prevent that.
   */
  ptr_t greatest_ha = (ptr_t)GC_greatest_plausible_heap_addr;
  ptr_t least_ha = (ptr_t)GC_least_plausible_heap_addr;
  mse *mark_stack_top = GC_mark_stack_top;
  mse *mark_stack_limit = GC_mark_stack_limit;

#  undef GC_mark_stack_top
#  undef GC_mark_stack_limit
#  define GC_mark_stack_top mark_stack_top
#  define GC_mark_stack_limit mark_stack_limit
#  define GC_greatest_plausible_heap_addr greatest_ha
#  define GC_least_plausible_heap_addr least_ha

  p = (ptr_t *)h->hb_body;
  plim = (ptr_t)h + HBLKSIZE;

  /* Go through all granules in block. */
  while (ADDR_LT((ptr_t)p, plim)) {
    word mark_word = *mark_word_addr++;
    ptr_t *q;

    for (q = p; mark_word != 0; mark_word >>= 1) {
      if ((mark_word & 1) != 0)
        PUSH_GRANULE(q);
      q += GC_GRANULE_PTRS;
    }
    p += CPP_WORDSZ * GC_GRANULE_PTRS;
  }

#  undef GC_greatest_plausible_heap_addr
#  undef GC_least_plausible_heap_addr
#  undef GC_mark_stack_top
#  undef GC_mark_stack_limit
#  define GC_mark_stack_limit GC_arrays._mark_stack_limit
#  define GC_mark_stack_top GC_arrays._mark_stack_top
  GC_mark_stack_top = mark_stack_top;
}

#  ifndef UNALIGNED_PTRS
/*
 * Push all objects reachable from marked objects in the given block
 * of two-granule objects.
 */
GC_ATTR_NO_SANITIZE_THREAD
STATIC void
GC_push_marked2(struct hblk *h, const hdr *hhdr)
{
  const word *mark_word_addr
      = (word *)CAST_AWAY_VOLATILE_PVOID(hhdr->hb_marks);
  ptr_t *p;
  ptr_t plim;
  ptr_t greatest_ha = (ptr_t)GC_greatest_plausible_heap_addr;
  ptr_t least_ha = (ptr_t)GC_least_plausible_heap_addr;
  mse *mark_stack_top = GC_mark_stack_top;
  mse *mark_stack_limit = GC_mark_stack_limit;

#    undef GC_mark_stack_top
#    undef GC_mark_stack_limit
#    define GC_mark_stack_top mark_stack_top
#    define GC_mark_stack_limit mark_stack_limit
#    define GC_greatest_plausible_heap_addr greatest_ha
#    define GC_least_plausible_heap_addr least_ha

  p = (ptr_t *)h->hb_body;
  plim = (ptr_t)h + HBLKSIZE;

  /* Go through all granules in block. */
  while (ADDR_LT((ptr_t)p, plim)) {
    word mark_word = *mark_word_addr++;
    ptr_t *q;

    for (q = p; mark_word != 0; mark_word >>= 2) {
      if (mark_word & 1) {
        PUSH_GRANULE(q);
        PUSH_GRANULE(q + GC_GRANULE_PTRS);
      }
      q += 2 * GC_GRANULE_PTRS;
    }
    p += CPP_WORDSZ * GC_GRANULE_PTRS;
  }

#    undef GC_greatest_plausible_heap_addr
#    undef GC_least_plausible_heap_addr
#    undef GC_mark_stack_top
#    undef GC_mark_stack_limit
#    define GC_mark_stack_limit GC_arrays._mark_stack_limit
#    define GC_mark_stack_top GC_arrays._mark_stack_top
  GC_mark_stack_top = mark_stack_top;
}

#    if GC_GRANULE_PTRS < 4
/*
 * Push all objects reachable from marked objects in the given block of
 * four-granule objects.  There is a risk of mark stack overflow here.
 * But we handle that.  And only unmarked objects get pushed, so it is
 * not very likely.
 */
GC_ATTR_NO_SANITIZE_THREAD
STATIC void
GC_push_marked4(struct hblk *h, const hdr *hhdr)
{
  const word *mark_word_addr
      = (word *)CAST_AWAY_VOLATILE_PVOID(hhdr->hb_marks);
  ptr_t *p;
  ptr_t plim;
  ptr_t greatest_ha = (ptr_t)GC_greatest_plausible_heap_addr;
  ptr_t least_ha = (ptr_t)GC_least_plausible_heap_addr;
  mse *mark_stack_top = GC_mark_stack_top;
  mse *mark_stack_limit = GC_mark_stack_limit;

#      undef GC_mark_stack_top
#      undef GC_mark_stack_limit
#      define GC_mark_stack_top mark_stack_top
#      define GC_mark_stack_limit mark_stack_limit
#      define GC_greatest_plausible_heap_addr greatest_ha
#      define GC_least_plausible_heap_addr least_ha

  p = (ptr_t *)h->hb_body;
  plim = (ptr_t)h + HBLKSIZE;

  /* Go through all granules in block. */
  while (ADDR_LT((ptr_t)p, plim)) {
    word mark_word = *mark_word_addr++;
    ptr_t *q;

    for (q = p; mark_word != 0; mark_word >>= 4) {
      if (mark_word & 1) {
        PUSH_GRANULE(q);
        PUSH_GRANULE(q + GC_GRANULE_PTRS);
        PUSH_GRANULE(q + 2 * GC_GRANULE_PTRS);
        PUSH_GRANULE(q + 3 * GC_GRANULE_PTRS);
      }
      q += 4 * GC_GRANULE_PTRS;
    }
    p += CPP_WORDSZ * GC_GRANULE_PTRS;
  }
#      undef GC_greatest_plausible_heap_addr
#      undef GC_least_plausible_heap_addr
#      undef GC_mark_stack_top
#      undef GC_mark_stack_limit
#      define GC_mark_stack_limit GC_arrays._mark_stack_limit
#      define GC_mark_stack_top GC_arrays._mark_stack_top
  GC_mark_stack_top = mark_stack_top;
}
#    endif
#  endif
#endif /* !USE_MARK_BYTES && !MARK_BIT_PER_OBJ && !SMALL_CONFIG */

/* Push all objects reachable from marked objects in the given block. */
STATIC void
GC_push_marked(struct hblk *h, const hdr *hhdr)
{
  size_t sz = hhdr->hb_sz;
  ptr_t p;
  size_t bit_no;
  ptr_t plim;
  mse *mark_stack_top;
  mse *mark_stack_limit = GC_mark_stack_limit;

  /* Some quick shortcuts: */
  if ((/* `0 |` */ GC_DS_LENGTH) == hhdr->hb_descr)
    return;
  if (GC_block_empty(hhdr))
    return; /*< nothing marked */

#if !defined(GC_DISABLE_INCREMENTAL)
  GC_n_rescuing_pages++;
#endif
  GC_objects_are_marked = TRUE;
  /*
   * The accelerated paths below ignore `hb_descr` and just scan every word
   * of the object conservatively.  That is a safe superset for length and
   * bitmap descriptors, but NOT for a mark procedure: a procedure may derive
   * referents that are not stored as plain aligned pointers (e.g. compressed
   * 32-bit pointers packed two per word).  Force such blocks down the general
   * path, which honours the descriptor.  `BYTES_TO_GRANULES(sz)` is never 0
   * for a real object, so 0 reliably selects `default`.
   */
  switch (
#if defined(ESCARGOT_USE_32BIT_IN_64BIT)
          (hhdr->hb_flags & COMPRESSED_FORMAT_MASK) != 0 ||
#endif
          (hhdr->hb_descr & GC_DS_TAGS) == GC_DS_PROC
              ? 0
              : BYTES_TO_GRANULES(sz)) {
#ifdef USE_PUSH_MARKED_ACCELERATORS
  case 1:
    GC_push_marked1(h, hhdr);
    break;
#  ifndef UNALIGNED_PTRS
  case 2:
    GC_push_marked2(h, hhdr);
    break;
#    if GC_GRANULE_PTRS < 4
  case 4:
    GC_push_marked4(h, hhdr);
    break;
#    endif
#  endif /* !UNALIGNED_PTRS */
#else
  case 1: /*< to suppress "switch statement contains no case" warning */
#endif
  default:
#if !defined(GC_DISABLE_INCREMENTAL) && !defined(MARK_BIT_PER_OBJ) \
    && !defined(USE_MARK_BYTES)
    if (GC_young_mark_active && GC_young_marked_bits
        && !IS_UNCOLLECTABLE(hhdr->hb_obj_kind)) {
      GC_push_marked_word_bits(h, hhdr, FALSE, NULL);
      break;
    }
#endif
    plim = sz > MAXOBJBYTES ? h->hb_body
                            : CAST_THRU_UINTPTR(ptr_t, (h + 1)->hb_body) - sz;
    mark_stack_top = GC_mark_stack_top;
    for (p = h->hb_body, bit_no = 0; ADDR_GE(plim, p);
         p += sz, bit_no += MARK_BIT_OFFSET(sz)) {
      /* Mark from fields inside the object. */
      if (mark_bit_from_hdr(hhdr, bit_no)) {
        mark_stack_top
            = GC_ms_push_obj_hdr(p, hhdr, mark_stack_top, mark_stack_limit);
      }
    }
    GC_mark_stack_top = mark_stack_top;
  }
}

#ifdef ENABLE_DISCLAIM
/*
 * Unconditionally mark from all objects that have not been reclaimed.
 * This is useful in order to retain pointers reachable from the disclaim
 * notifiers.  To determine whether an object has been reclaimed, we
 * require that any live object has a nonzero as one of the two least
 * significant bits of the first "pointer-sized" word.  On the other hand,
 * the reclaimed object is a member of free lists, and thus contains
 * a pointer-aligned next-pointer as the first "pointer-sized" word.
 */
GC_ATTR_NO_SANITIZE_THREAD
STATIC void
GC_push_unconditionally(struct hblk *h, const hdr *hhdr)
{
  size_t sz = hhdr->hb_sz;
  ptr_t p;
  ptr_t plim;
  mse *mark_stack_top;
  mse *mark_stack_limit = GC_mark_stack_limit;

  if ((/* `0 |` */ GC_DS_LENGTH) == hhdr->hb_descr)
    return;

#  if !defined(GC_DISABLE_INCREMENTAL)
  GC_n_rescuing_pages++;
#  endif
  GC_objects_are_marked = TRUE;
  plim = sz > MAXOBJBYTES ? h->hb_body
                          : CAST_THRU_UINTPTR(ptr_t, (h + 1)->hb_body) - sz;
  mark_stack_top = GC_mark_stack_top;
  for (p = h->hb_body; ADDR_GE(plim, p); p += sz) {
    if ((ADDR(*(ptr_t *)p) & 0x3) != 0) {
      mark_stack_top
          = GC_ms_push_obj_hdr(p, hhdr, mark_stack_top, mark_stack_limit);
    }
  }
  GC_mark_stack_top = mark_stack_top;
}
#endif /* ENABLE_DISCLAIM */

#ifndef GC_DISABLE_INCREMENTAL
/* Test whether any page in the given block is dirty. */
STATIC GC_bool
GC_block_was_dirty(const struct hblk *h, const hdr *hhdr)
{
  size_t sz;
  ptr_t p;

#  ifdef AO_HAVE_load
  /* Atomic access is used to avoid racing with `GC_realloc`. */
  sz = AO_load((volatile AO_t *)&hhdr->hb_sz);
#  else
  sz = hhdr->hb_sz;
#  endif
  if (sz <= MAXOBJBYTES) {
    return GC_page_was_dirty(h);
  }

  for (p = (ptr_t)h; ADDR_LT(p, (ptr_t)h + sz); p += HBLKSIZE) {
    if (GC_page_was_dirty((const struct hblk *)p))
      return TRUE;
  }
  return FALSE;
}
#endif /* GC_DISABLE_INCREMENTAL */

/*
 * Similar to `GC_push_marked`, but skip over unallocated blocks and
 * return address of next plausible block.
 */
STATIC struct hblk *
GC_push_next_marked(struct hblk *h)
{
  const hdr *hhdr = HDR(h);

  if (UNLIKELY(IS_FORWARDING_ADDR_OR_NIL(hhdr) || HBLK_IS_FREE(hhdr))) {
    h = GC_next_block(h, FALSE);
    if (NULL == h)
      return NULL;
    hhdr = GC_find_header(h);
  } else {
#ifdef LINT2
    if (NULL == h)
      ABORT("Bad HDR() definition");
#endif
  }
  GC_push_marked(h, hhdr);
  return h + OBJ_SZ_TO_BLOCKS(hhdr->hb_sz);
}

#ifndef GC_DISABLE_INCREMENTAL
/* Young objects are traced on their first mark.  Rescuing them again from
   dirty pages duplicates that work, including cells mixed into old blocks.
   Only old starts need remembered-source scans; retain current descriptors. */
#  if !defined(MARK_BIT_PER_OBJ) && !defined(USE_MARK_BYTES)
#include "source-batch.inc"

STATIC void
GC_push_marked_word_bits(struct hblk *h, const hdr *hhdr, GC_bool old_only,
                           const word *saved)
{
  const word *old = NULL;
  size_t i, last_bit;
  mse *top;
  GC_bool pushed = FALSE;

  if (hhdr->hb_descr == 0 || GC_block_empty(hhdr))
    return;
  if (old_only) {
    ++GC_young_old_source_blocks;
    old = saved != NULL ? saved : GC_dense_old_marks(h);
    if (old == NULL) {
      ++GC_young_old_source_empty;
      return;
    }
  } else {
    ++GC_young_bit_source_blocks;
  }
#if defined(ESCARGOT_USE_32BIT_IN_64BIT)
  if (!old_only && GC_scan_compressed_sources(h, hhdr))
    return;
#endif
  top = GC_mark_stack_top;
  last_bit = FINAL_MARK_BIT(hhdr->hb_sz);
  for (i = 0; i < GC_YOUNG_DENSE_WORDS; ++i) {
    word bits = hhdr->hb_marks[i];
    if (old_only)
      bits &= old[i];
    if (i == divWORDSZ(last_bit))
      bits &= ~((word)1 << modWORDSZ(last_bit));
    while (bits != 0) {
      size_t bit;
#    if defined(__GNUC__) || defined(__clang__)
      bit = (size_t)__builtin_ctzll(bits);
#    else
      word remaining = bits;
      for (bit = 0; (remaining & 1) == 0; ++bit)
        remaining >>= 1;
#    endif
      bits &= bits - 1;
      top = GC_ms_push_obj_hdr(h->hb_body
                                   + (i * CPP_WORDSZ + bit) * GC_GRANULE_BYTES,
                              hhdr, top, GC_mark_stack_limit);
      pushed = TRUE;
    }
  }
  GC_mark_stack_top = top;
  if (pushed && old_only) {
    ++GC_n_rescuing_pages;
    GC_objects_are_marked = TRUE;
  } else if (!pushed && old_only) {
    ++GC_young_old_source_empty;
  }
}
#  endif

/* A marked old large length object needs to rescue references only from
   pages written since the previous trace.  This is a source-only filter:
   first marks still enqueue the complete descriptor.  Require the existing
   callback-mutation recovery to be armed; its invalid-mark fallback rescans
   whole objects without this filter.  Non-length/custom kinds retain their
   original descriptor, including any derived referents. */
STATIC GC_bool
GC_push_dirty_large_length(struct hblk *h, const hdr *hhdr)
{
#if defined(ESCARGOT_USE_32BIT_IN_64BIT) && defined(LINUX)
  size_t bytes, offset;
  unsigned format;
  ptr_t run = NULL;
  mse *top;
  GC_bool pushed = FALSE;

  if (!GC_source_page_slice || !GC_young_mark_active
      || GC_mark_state != MS_PUSH_RESCUERS || !GC_sparse_sources_armed
      || GC_young_source_filter_disabled || GC_page_size != HBLKSIZE
      || GC_get_actual_vdb() != GC_VDB_MPROTECT
      || hhdr->hb_sz <= HBLKSIZE || !GC_sparse_kind_eligible(hhdr)
      || (hhdr->hb_descr & GC_DS_TAGS) != GC_DS_LENGTH
      || hhdr->hb_descr == 0 || hhdr->hb_descr > hhdr->hb_sz)
    return FALSE;
  format = hhdr->hb_flags & COMPRESSED_FORMAT_MASK;
  if ((format != 0 && format != COMPRESSED_POINTERS)
      || (format == 0 && ALIGNMENT != sizeof(ptr_t)))
    return FALSE;
  if (!mark_bit_from_hdr(hhdr, 0))
    return TRUE;
  bytes = hhdr->hb_descr;
  top = GC_mark_stack_top;
  ++GC_source_page_stats[16];
  GC_source_page_stats[17] += bytes;
  for (offset = 0; offset < bytes; offset += HBLKSIZE) {
    ptr_t page = (ptr_t)h + offset;
    size_t part = bytes - offset;
    if (part > HBLKSIZE)
      part = HBLKSIZE;
    if (GC_page_was_dirty((const struct hblk *)page)) {
      if (run == NULL)
        run = page;
      GC_source_page_stats[18] += part;
    } else if (run != NULL) {
      size_t length = (size_t)(page - run);
      top = format == COMPRESSED_POINTERS
                ? GC_push_32bit_range(run, length, top, GC_mark_stack_limit)
                : GC_ms_push_obj_descr(run, (word)length, top,
                                        GC_mark_stack_limit);
      ++GC_source_page_stats[19];
      pushed = TRUE;
      run = NULL;
    }
  }
  if (run != NULL) {
    size_t length = (size_t)((ptr_t)h + bytes - run);
    top = format == COMPRESSED_POINTERS
              ? GC_push_32bit_range(run, length, top, GC_mark_stack_limit)
              : GC_ms_push_obj_descr(run, (word)length, top,
                                      GC_mark_stack_limit);
    ++GC_source_page_stats[19];
    pushed = TRUE;
  }
  GC_mark_stack_top = top;
  if (pushed) {
    ++GC_n_rescuing_pages;
    GC_objects_are_marked = TRUE;
  }
  return TRUE;
#else
  UNUSED_ARG(h);
  UNUSED_ARG(hhdr);
  return FALSE;
#endif
}

/* Diagnostic only: payload estimates and exact dirty coverage of plain
   large length descriptors.  Counters do not affect marking decisions. */
STATIC void
GC_audit_dirty_source(struct hblk *h, const hdr *hhdr)
{
  size_t size = hhdr->hb_sz;
  word objects;
  unsigned category;
  if (hhdr->hb_descr == 0 || GC_block_empty(hhdr))
    return;
  if (size <= MAXOBJBYTES) {
    GC_source_page_stats[0]++;
    GC_source_page_stats[1] += size * hhdr->hb_n_marks;
    return;
  }
  if (!mark_bit_from_hdr(hhdr, 0))
    return;
  category = 2 + (hhdr->hb_descr & GC_DS_TAGS) * 2;
  ++GC_source_page_stats[category];
  GC_source_page_stats[category + 1] += size;
  if ((hhdr->hb_descr & GC_DS_TAGS) != GC_DS_LENGTH
      || hhdr->hb_descr > size)
    return;
  objects = 0;
#if defined(ESCARGOT_USE_32BIT_IN_64BIT)
  objects = hhdr->hb_flags & COMPRESSED_FORMAT_MASK;
  if (objects != 0 && objects != COMPRESSED_POINTERS)
    return;
#endif
  {
    size_t offset, bytes = hhdr->hb_descr;
    word dirty_bytes = 0;
    for (offset = 0; offset < bytes; offset += HBLKSIZE) {
      size_t part = bytes - offset;
      if (part > HBLKSIZE)
        part = HBLKSIZE;
      if (GC_page_was_dirty((const struct hblk *)((ptr_t)h + offset)))
        dirty_bytes += part;
    }
    ++GC_source_page_stats[10];
    GC_source_page_stats[11] += bytes;
    GC_source_page_stats[12] += dirty_bytes;
#if defined(ESCARGOT_USE_32BIT_IN_64BIT)
    if (objects == COMPRESSED_POINTERS) {
      GC_source_page_stats[13]++;
      GC_source_page_stats[14] += bytes;
      GC_source_page_stats[15] += dirty_bytes;
    }
#endif
  }
}

/* Identical to `GC_push_next_marked`, but mark only from dirty pages. */
STATIC struct hblk *
GC_push_next_marked_dirty(struct hblk *h)
{
  const hdr *hhdr;
  GC_bool indexed = FALSE;

  GC_ASSERT(I_HOLD_LOCK());
  if (!GC_incremental)
    ABORT("Dirty bits not set up");
#  if defined(LINUX) && defined(GC_THREAD_ISOLATE) && defined(MPROTECT_VDB)
  {
#    if defined(GC_ASSERTIONS) || !defined(NDEBUG)
    struct hblk *reference = h;
#    endif
    indexed = GC_next_dirty_candidate(h, &h);
#    if defined(GC_ASSERTIONS) || !defined(NDEBUG)
    if (indexed) {
      const hdr *reference_hdr;
      for (;;) {
        reference_hdr = HDR(reference);
        if (IS_FORWARDING_ADDR_OR_NIL(reference_hdr)
            || HBLK_IS_FREE(reference_hdr)) {
          reference = GC_next_block(reference, FALSE);
          if (reference == NULL)
            break;
          reference_hdr = HDR(reference);
        }
        if (!IS_PTRFREE(reference_hdr)
            && GC_block_was_dirty(reference, reference_hdr))
          break;
        reference += OBJ_SZ_TO_BLOCKS(reference_hdr->hb_sz);
      }
      if (reference != h)
        ABORT("Dirty candidate index differs from block headers");
    }
#    endif
  }
#  endif
  if (indexed) {
    if (h == NULL)
      return NULL;
    hhdr = HDR(h);
  } else {
    for (;; h += OBJ_SZ_TO_BLOCKS(hhdr->hb_sz)) {
      hhdr = HDR(h);
      if (UNLIKELY(IS_FORWARDING_ADDR_OR_NIL(hhdr) || HBLK_IS_FREE(hhdr))) {
        h = GC_next_block(h, FALSE);
        if (NULL == h)
          return NULL;
        hhdr = GC_find_header(h);
      } else {
#  ifdef LINT2
        if (NULL == h)
          ABORT("Bad HDR() definition");
#  endif
      }
      if (GC_block_was_dirty(h, hhdr))
        break;
    }
  }
  if (GC_young_mark_active && GC_source_page_audit)
    GC_audit_dirty_source(h, hhdr);
  GC_sparse_current_source = h;
#  ifdef ENABLE_DISCLAIM
  if ((hhdr->hb_flags & MARK_UNCONDITIONALLY) != 0) {
    GC_push_unconditionally(h, hhdr);

    /*
     * Then we may ask, why not also add the `MARK_UNCONDITIONALLY`
     * case to `GC_push_next_marked`, which is also applied to
     * uncollectible blocks?  But it seems to me that the function
     * does not need to scan uncollectible (and unconditionally
     * marked) blocks since those are already handled in the
     * `MS_PUSH_UNCOLLECTABLE` phase.
     */
  } else
#  endif
  /* else */ {
#  if !defined(MARK_BIT_PER_OBJ) && !defined(USE_MARK_BYTES)
    if (GC_young_mark_active && GC_young_dense_retrace && GC_young_old_sources
        && !GC_young_source_filter_disabled
        && !IS_UNCOLLECTABLE(hhdr->hb_obj_kind))
      GC_push_marked_word_bits(h, hhdr, TRUE, NULL);
    else if (GC_young_sparse_active) {
      const word *saved = GC_sparse_old_marks(h, hhdr);
      if (saved != NULL) {
        ++GC_young_old_source_blocks;
        ++GC_young_old_source_empty;
      } else if (!GC_push_dirty_large_length(h, hhdr))
        GC_push_marked(h, hhdr);
    } else
#  endif
    if (!GC_push_dirty_large_length(h, hhdr))
      GC_push_marked(h, hhdr);
  }
  GC_sparse_current_source = NULL;
  return h + OBJ_SZ_TO_BLOCKS(hhdr->hb_sz);
}
#endif /* !GC_DISABLE_INCREMENTAL */

/*
 * Similar to `GC_push_next_marked`, but for uncollectible pages.
 * Needed since we do not clear marks for such pages, even for full
 * collections.
 */
STATIC struct hblk *
GC_push_next_marked_uncollectable(struct hblk *h)
{
  const hdr *hhdr = HDR(h);

  for (;;) {
    if (UNLIKELY(IS_FORWARDING_ADDR_OR_NIL(hhdr) || HBLK_IS_FREE(hhdr))) {
      h = GC_next_block(h, FALSE);
      if (NULL == h)
        return NULL;
      hhdr = GC_find_header(h);
    } else {
#ifdef LINT2
      if (NULL == h)
        ABORT("Bad HDR() definition");
#endif
    }
    if (hhdr->hb_obj_kind == UNCOLLECTABLE) {
      GC_push_marked(h, hhdr);
      break;
    }
#ifdef ENABLE_DISCLAIM
    if ((hhdr->hb_flags & MARK_UNCONDITIONALLY) != 0) {
      GC_push_unconditionally(h, hhdr);
      break;
    }
#endif
    h += OBJ_SZ_TO_BLOCKS(hhdr->hb_sz);
    hhdr = HDR(h);
  }
  return h + OBJ_SZ_TO_BLOCKS(hhdr->hb_sz);
}

