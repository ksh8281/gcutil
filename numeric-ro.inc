/* Linux local experiment: complete supported plain stores while retaining RO.
   x86 MOV/byte OR and ARM/Thumb STR families share the same complete-slot
   classifier. Atomic/exclusive stores, unknown formats and possible new
   references retain the ordinary dirty path. */
#include <fcntl.h>
#include <stdint.h>

GC_INNER MAY_THREAD_LOCAL word GC_numeric_ro_stats[16];
GC_INNER MAY_THREAD_LOCAL word GC_or_ro_stats[8];
GC_INNER MAY_THREAD_LOCAL word GC_minor_kind_stats[192][8];
GC_INNER MAY_THREAD_LOCAL word GC_minor_phase_ns[8];

STATIC MAY_THREAD_LOCAL int GC_numeric_ro_fd = -1;
STATIC MAY_THREAD_LOCAL unsigned GC_numeric_ro_mode;
STATIC MAY_THREAD_LOCAL unsigned GC_numeric_ro_cap;
STATIC MAY_THREAD_LOCAL GC_bool GC_numeric_ro_or;
typedef struct { word page, epoch, count; } GC_numeric_ro_entry;
STATIC MAY_THREAD_LOCAL GC_numeric_ro_entry GC_numeric_ro_recent[1024];

STATIC void GC_numeric_ro_deinit(void)
{
  if (GC_numeric_ro_fd >= 0) close(GC_numeric_ro_fd);
  GC_numeric_ro_fd = -1;
  GC_numeric_ro_mode = 0;
  GC_numeric_ro_or = FALSE;
  BZERO(GC_numeric_ro_recent, sizeof(GC_numeric_ro_recent));
}

STATIC void GC_numeric_ro_init(void)
{
  const char *setting;
  GC_numeric_ro_deinit();
  setting = GETENV("GC_BENCH_NUMERIC_RO");
  GC_numeric_ro_mode = setting != NULL ? (unsigned)atoi(setting) : 0;
  setting = GETENV("GC_BENCH_NUMERIC_RO_CAP");
  GC_numeric_ro_cap = setting != NULL ? (unsigned)atoi(setting) : 1;
  if (GC_numeric_ro_cap > 1024) GC_numeric_ro_cap = 1024;
  setting = GETENV("GC_BENCH_NUMERIC_RO_OR");
  GC_numeric_ro_or = setting != NULL && atoi(setting) != 0;
  GC_or_ro_stats[0] = GC_numeric_ro_or;
  if (GC_numeric_ro_mode != 0 && GC_page_size == HBLKSIZE)
    GC_numeric_ro_fd = open("/proc/self/mem", O_RDWR | O_CLOEXEC);
  GC_numeric_ro_stats[0] = GC_numeric_ro_mode;
  GC_numeric_ro_stats[15] = GC_numeric_ro_fd >= 0;
}

#if defined(LINUX) && defined(GC_THREAD_ISOLATE) \
    && (defined(__x86_64__) || defined(__aarch64__) || defined(__arm__)) \
    && defined(__BYTE_ORDER__) && __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
typedef struct {
  ptr_t dest;
  unsigned char value[32];
  size_t width, length;
  GC_bool is_or, writeback;
  unsigned base_reg;
  word base_value;
} GC_numeric_ro_store;

#if defined(__x86_64__)
STATIC word GC_numeric_ro_register(const ucontext_t *uc, unsigned reg)
{
  static const unsigned regs[16] = {
    REG_RAX,REG_RCX,REG_RDX,REG_RBX,REG_RSP,REG_RBP,REG_RSI,REG_RDI,
    REG_R8,REG_R9,REG_R10,REG_R11,REG_R12,REG_R13,REG_R14,REG_R15
  };
  return (word)uc->uc_mcontext.gregs[regs[reg]];
}

STATIC GC_bool GC_numeric_ro_decode(const ucontext_t *uc, ptr_t fault,
                                    word *value, size_t *width, size_t *length,
                                    GC_bool *is_or)
{
  const unsigned char *pc = (const unsigned char *)uc->uc_mcontext.gregs[REG_RIP];
  size_t n = 0;
  unsigned rex = 0, op, modrm, mod, rm, reg, rawreg;
  GC_bool small = FALSE, relative = FALSE, has_disp32 = FALSE;
  word addr = 0;
  int32_t disp = 0;
  while (n < 4 && (pc[n] == 0x66 || (pc[n] >= 0x40 && pc[n] <= 0x4f))) {
    if (pc[n] == 0x66) { if (rex != 0) return FALSE; small = TRUE; }
    else { if (rex != 0) return FALSE; rex = pc[n]; }
    ++n;
  }
  op = pc[n++];
  *is_or = op == 0x80 && GC_numeric_ro_or && !small;
  if (op != 0x88 && op != 0x89 && op != 0xc6 && op != 0xc7 && !*is_or)
    return FALSE;
  *width = (op == 0x88 || op == 0xc6 || *is_or) ? 1
              : (rex & 8) ? 8 : small ? 2 : 4;
  modrm = pc[n++]; mod = modrm >> 6; rm = modrm & 7; rawreg = (modrm >> 3) & 7;
  reg = rawreg + ((rex & 4) ? 8 : 0);
  if (mod == 3 || ((op == 0xc6 || op == 0xc7) && reg != 0)
      || (*is_or && reg != 1)) return FALSE;
  if (rm == 4) {
    unsigned sib = pc[n++], index = (sib >> 3) & 7, base = sib & 7;
    if (index != 4 || (rex & 2))
      addr += GC_numeric_ro_register(uc,index + ((rex & 2) ? 8 : 0)) << (sib >> 6);
    if (base == 5 && mod == 0) has_disp32 = TRUE;
    else addr += GC_numeric_ro_register(uc,base + ((rex & 1) ? 8 : 0));
  } else if (rm == 5 && mod == 0) {
    relative = TRUE; has_disp32 = TRUE;
  } else addr = GC_numeric_ro_register(uc,rm + ((rex & 1) ? 8 : 0));
  if (mod == 1) disp = (int8_t)pc[n++];
  else if (mod == 2 || has_disp32) { memcpy(&disp,pc+n,4); n += 4; }
  addr += (word)(GC_signed_word)disp;
  if (*is_or) {
    *value = pc[n++];
  } else if (op == 0xc6 || op == 0xc7) {
    size_t bytes = *width == 8 ? 4 : *width;
    word immediate = 0;
    memcpy(&immediate,pc+n,bytes); n += bytes;
    *value = *width == 8 ? (word)(GC_signed_word)(int32_t)immediate : immediate;
  } else if (*width == 1 && rex == 0 && rawreg >= 4)
    *value = GC_numeric_ro_register(uc,rawreg-4) >> 8;
  else *value = GC_numeric_ro_register(uc,reg);
  if (relative) addr += (word)pc+n;
  if (n > 15 || addr != (word)fault
      || (addr & (HBLKSIZE-1)) + *width > HBLKSIZE) return FALSE;
  if (*is_or) {
    /* RMW reads the existing byte before classifying the complete GC slot.
       No write has happened yet: every rejection can retry the real OR. */
    *value |= *(const unsigned char *)addr;
  }
  *length = n;
  return TRUE;
}

#endif /* __x86_64__ */

#if defined(__aarch64__) || defined(__arm__)
# include "numeric-ro-arm.inc"
#endif

STATIC GC_bool GC_numeric_ro_possible(word value)
{
  if (value < GC_least_plausible_heap_addr
      || value > GC_greatest_plausible_heap_addr) return FALSE;
  return GC_base((void *)value) != NULL;
}

/* Check the complete collector-visible slot, including bytes not overwritten
   by a narrow store. A non-pointer byte alone says nothing about its slot. */
STATIC GC_bool GC_numeric_ro_slot(ptr_t slot, size_t bytes, word tag_mask,
                                 GC_bool compressed, ptr_t dest,
                                 size_t width, const unsigned char *value)
{
  word before = 0, after;
  ptr_t a = ADDR_LT(dest,slot) ? slot : dest;
  ptr_t b = ADDR_LT(slot+bytes,dest+width) ? slot+bytes : dest+width;
  memcpy(&before,slot,bytes); after = before;
  memcpy((char *)&after+(a-slot),value+(a-dest),(size_t)(b-a));
  before &= ~tag_mask; after &= ~tag_mask;
  if (compressed) {
    word upper = (word)slot & ~(word)0xffffffffU;
    before = before != 0 && (before & 1) == 0 ? upper|before : 0;
    after = after != 0 && (after & 1) == 0 ? upper|after : 0;
  }
  {
    GC_bool old_ref = GC_numeric_ro_possible(before);
    GC_bool new_ref = GC_numeric_ro_possible(after);
    void *base;
    if (!old_ref && !new_ref) return TRUE;
    if (GC_numeric_ro_mode < 3 || GC_collection_in_progress()
        || GC_young_reclaim_active) return FALSE;
    if (!new_ref) { ++GC_numeric_ro_stats[14]; return TRUE; }
    /* Retrace can clear a marked young survivor at the next minor. A current
       mark then does not prove that the target is in the retained baseline. */
    if (GC_young_retrace) return FALSE;
    base = GC_base((void *)after);
    if (base == NULL || !GC_is_marked(base)) return FALSE;
    ++GC_numeric_ro_stats[13];
    return TRUE;
  }
}

/* 0: unknown/reference; 1: descriptor excludes every touched slot;
   2: all complete traced slots contain non-references before and after. */
STATIC unsigned GC_numeric_ro_classify(ptr_t dest, size_t width,
                                      const unsigned char *value)
{
  ptr_t base = (ptr_t)GC_base(dest), stop = dest+width, slot;
  hdr *hhdr;
  GC_bool traced = FALSE, compressed = FALSE;
  size_t unit = sizeof(word);
  if (base == NULL) return 0;
  hhdr = GC_find_header(base);
  if (hhdr == NULL || IS_FORWARDING_ADDR_OR_NIL(hhdr)
      || HBLK_IS_FREE(hhdr) || ADDR_LT(base+hhdr->hb_sz,stop)) return 0;
#if defined(ESCARGOT_USE_32BIT_IN_64BIT)
  unsigned format = hhdr->hb_flags & COMPRESSED_FORMAT_MASK;
  compressed = format == COMPRESSED_BITMAP || format == COMPRESSED_POINTERS;
  if (compressed) unit = 4;
#endif
  if (!compressed && ((hhdr->hb_descr & GC_DS_TAGS) == GC_DS_PROC
           || (hhdr->hb_descr & GC_DS_TAGS) == GC_DS_PER_OBJECT)) return 0;
  for (slot=base+((dest-base)/unit)*unit; ADDR_LT(slot,stop); slot+=unit) {
    size_t index = (size_t)(slot-base)/unit;
    GC_bool pointer = TRUE;
    word tag_mask = 0;
#if defined(ESCARGOT_USE_32BIT_IN_64BIT)
    if (format == COMPRESSED_BITMAP) {
      const GC_compressed_bitmap_descr *bitmap = (const GC_compressed_bitmap_descr *)hhdr->hb_descr;
      pointer = index < bitmap->slots
          && (GC_COMPRESSED_BITMAP(bitmap)[divWORDSZ(index)] & ((word)1<<modWORDSZ(index))) != 0;
      if (index == bitmap->tagged_slot) tag_mask = bitmap->tag_mask;
    } else
#endif
    if ((hhdr->hb_descr & GC_DS_TAGS) == GC_DS_BITMAP) {
      pointer = index < CPP_WORDSZ
          && ((hhdr->hb_descr & ~(word)GC_DS_TAGS)
              & ((word)1<<(CPP_WORDSZ-1-index))) != 0;
    } else if ((hhdr->hb_descr & GC_DS_TAGS) == GC_DS_LENGTH) {
      pointer = ADDR_LT(slot,base+hhdr->hb_descr);
    } else return 0;
    if (!pointer) continue;
    traced = TRUE;
    if (GC_numeric_ro_mode < 2
        || !GC_numeric_ro_slot(slot,unit,tag_mask,compressed,dest,width,value)) return 0;
  }
  return traced ? 2 : 1;
}

#if defined(__x86_64__)
/* Even an idempotent OR updates flags. Copy the defined arithmetic flags
   into the saved context; preserve all unrelated flags. AF is undefined for
   OR, so leaving its saved value is permitted. MOV must not change flags. */
STATIC void GC_numeric_ro_or_flags(ucontext_t *uc, unsigned char result)
{
  word flags = (word)uc->uc_mcontext.gregs[REG_EFL] & ~(word)0x8c5;
  unsigned parity = result;
  parity ^= parity >> 4;
  parity ^= parity >> 2;
  parity ^= parity >> 1;
  if ((parity & 1) == 0) flags |= 0x04;
  if (result == 0) flags |= 0x40;
  if (result & 0x80) flags |= 0x80;
  uc->uc_mcontext.gregs[REG_EFL] = (greg_t)flags;
}

#endif /* __x86_64__ */

STATIC GC_bool GC_try_numeric_ro(void *raw_addr, void *raw_uc)
{
  ptr_t fault = (ptr_t)raw_addr, addr;
  ucontext_t *uc = (ucontext_t *)raw_uc;
  GC_numeric_ro_entry *entry;
  GC_numeric_ro_store store = { 0 };
  word page;
  unsigned category;
  int saved_errno = errno;
  if (GC_numeric_ro_fd < 0 || GC_numeric_ro_mode == 0
      || GC_isolate_vdb_has_foreign_writes()) return FALSE;
#if defined(__x86_64__)
  {
    word value = 0;
    if ((uc->uc_mcontext.gregs[REG_ERR] & 2) == 0) return FALSE;
    ++GC_numeric_ro_stats[1];
    if (!GC_numeric_ro_decode(uc,fault,&value,&store.width,&store.length,
                              &store.is_or)) {
      ++GC_numeric_ro_stats[5]; return FALSE;
    }
    store.dest = fault; memcpy(store.value, &value, store.width);
  }
#else
  ++GC_numeric_ro_stats[1];
  if (!GC_numeric_ro_decode_arm(uc, &store)) {
    ++GC_numeric_ro_stats[5]; return FALSE;
  }
#endif
  addr = store.dest;
  if (store.width == 0 || store.width > sizeof(store.value)
      || ADDR_LT(fault, addr) || !ADDR_LT(fault, addr + store.width)
      || ((word)addr & (HBLKSIZE - 1)) + store.width > HBLKSIZE) {
    ++GC_numeric_ro_stats[5]; return FALSE;
  }
  page = (word)HBLKPTR(addr);
  if (store.is_or) ++GC_or_ro_stats[1];
  entry = &GC_numeric_ro_recent[(page>>LOG_HBLKSIZE)&1023];
  if (entry->page != page || entry->epoch != GC_gc_no) {
    entry->page=page;entry->epoch=GC_gc_no;entry->count=0;
  }
  if (entry->count >= GC_numeric_ro_cap) { ++GC_numeric_ro_stats[9]; return FALSE; }
  category = GC_numeric_ro_classify(addr,store.width,store.value);
  if (category == 0) { ++GC_numeric_ro_stats[6]; return FALSE; }
  if (memcmp(addr,store.value,store.width) == 0) {
    ++GC_numeric_ro_stats[3];
    if (store.is_or) ++GC_or_ro_stats[3];
  }
  else {
    /* ARM32 heaps may be above 2 GiB. A signed 32-bit off_t truncates the
       address; use the Linux large-file API even for a single small store. */
    ssize_t written = pwrite64(GC_numeric_ro_fd,store.value,store.width,
                               (off64_t)(word)addr);
    errno = saved_errno;
    if (written != (ssize_t)store.width) { ++GC_numeric_ro_stats[7]; return FALSE; }
    ++GC_numeric_ro_stats[4];
    if (store.is_or) ++GC_or_ro_stats[4];
  }
  ++entry->count;
  ++GC_numeric_ro_stats[category == 1 ? 2 : 8];
  ++GC_numeric_ro_stats[10+category];
#if defined(__x86_64__)
  if (store.is_or) {
    ++GC_or_ro_stats[2];
    ++GC_or_ro_stats[category == 1 ? 5 : 6];
    GC_numeric_ro_or_flags(uc,store.value[0]);
  }
  uc->uc_mcontext.gregs[REG_RIP] += (greg_t)store.length;
#else
  GC_numeric_ro_commit_arm(uc, &store);
#endif
  errno = saved_errno;
  return TRUE;
}
#else
STATIC GC_bool GC_try_numeric_ro(void *addr, void *uc)
{ UNUSED_ARG(addr); UNUSED_ARG(uc); return FALSE; }
#endif
