/* Architecture decoding only. GC slot classification and the RO-preserving
   write are shared with x86. ARM ORR has already updated its destination (and,
   for flag-setting ARM/Thumb forms, flags) before the following STR faults.
   Exclusive, atomic and release stores are deliberately not plain stores. */
STATIC GC_signed_word
GC_numeric_ro_signed(unsigned value, unsigned bits)
{
  unsigned sign = 1U << (bits - 1);
  return (GC_signed_word)(value ^ sign) - (GC_signed_word)sign;
}

#if defined(__aarch64__)
STATIC word GC_numeric_ro_arm_reg(const ucontext_t *uc, unsigned reg,
                                  GC_bool address)
{
  return reg == 31 ? (address ? (word)uc->uc_mcontext.sp : 0)
                   : (word)uc->uc_mcontext.regs[reg];
}

STATIC const unsigned char *
GC_numeric_ro_arm_fp(const ucontext_t *uc, unsigned reg, size_t width)
{
  const unsigned char *p = uc->uc_mcontext.__reserved;
  size_t remaining = sizeof(uc->uc_mcontext.__reserved);
  while (remaining >= sizeof(struct _aarch64_ctx)) {
    const struct _aarch64_ctx *head = (const struct _aarch64_ctx *)p;
    if (head->size < sizeof(*head) || head->size > remaining
        || (head->size & 15) != 0) return NULL;
    if (head->magic == FPSIMD_MAGIC) {
      const struct fpsimd_context *fp = (const struct fpsimd_context *)p;
      if (head->size < sizeof(*fp) || reg >= 32 || width > 16) return NULL;
      return (const unsigned char *)&fp->vregs[reg];
    }
    p += head->size; remaining -= head->size;
  }
  return NULL;
}

STATIC GC_bool
GC_numeric_ro_arm_value(const ucontext_t *uc, GC_numeric_ro_store *store,
                        unsigned rt, unsigned rt2, size_t size,
                        GC_bool fp, GC_bool pair)
{
  unsigned n;
  for (n = 0; n < (pair ? 2U : 1U); ++n) {
    unsigned reg = n == 0 ? rt : rt2;
    if (fp) {
      const unsigned char *value = GC_numeric_ro_arm_fp(uc, reg, size);
      if (value == NULL) return FALSE;
      memcpy(store->value + n * size, value, size);
    } else {
      word value = GC_numeric_ro_arm_reg(uc, reg, FALSE);
      memcpy(store->value + n * size, &value, size);
    }
  }
  store->width = size * (pair ? 2 : 1);
  return TRUE;
}

STATIC GC_bool
GC_numeric_ro_decode_arm(const ucontext_t *uc, GC_numeric_ro_store *store)
{
  uint32_t insn;
  unsigned rn, rt, rt2 = 0, opc, mode;
  GC_bool fp, pair = FALSE;
  word base, address, updated = 0;
  GC_signed_word offset;
  size_t size;
  memcpy(&insn, (const void *)(word)uc->uc_mcontext.pc, sizeof(insn));
  rn = (insn >> 5) & 31; rt = insn & 31;
  fp = (insn & (1U << 26)) != 0;
  base = GC_numeric_ro_arm_reg(uc, rn, TRUE);
  store->length = 4;
  if ((insn & 0x3a000000U) == 0x28000000U) {
    /* STP, including SIMD/FP, offset/pre/post-indexed. Not LDPSW/STNP. */
    if ((insn & (1U << 22)) != 0) return FALSE;
    opc = insn >> 30;
    if (fp ? opc == 3 : (opc != 0 && opc != 2)) return FALSE;
    size = fp ? (size_t)4 << opc : opc == 2 ? 8 : 4;
    mode = (insn >> 23) & 3;
    if (mode == 0) return FALSE;
    rt2 = (insn >> 10) & 31;
    pair = TRUE;
    offset = GC_numeric_ro_signed((insn >> 15) & 127, 7)
               * (GC_signed_word)size;
    updated = base + (word)offset;
    address = mode == 1 ? base : updated;
    store->writeback = mode != 2;
  } else if ((insn & 0x3b000000U) == 0x39000000U
             || (insn & 0x3b000000U) == 0x38000000U) {
    /* STR/STUR scalar or SIMD, unsigned/signed immediate or register offset. */
    opc = (insn >> 22) & 3;
    if (fp ? (opc != 0 && !(opc == 2 && (insn >> 30) == 0))
           : opc != 0) return FALSE;
    size = fp && opc == 2 ? 16 : (size_t)1 << (insn >> 30);
    if ((insn & (1U << 24)) != 0) {
      address = base + ((word)((insn >> 10) & 4095) * size);
    } else if ((insn & (1U << 21)) != 0) {
      unsigned rm = (insn >> 16) & 31, option = (insn >> 13) & 7;
      word index = GC_numeric_ro_arm_reg(uc, rm, FALSE);
      if (((insn >> 10) & 3) != 2) return FALSE;
      switch (option) {
      case 2: index = (uint32_t)index; break;
      case 3: break;
      case 6: index = (word)(GC_signed_word)(int32_t)index; break;
      case 7: break;
      default: return FALSE;
      }
      address = base + index * ((insn & (1U << 12)) != 0 ? size : 1);
    } else {
      mode = (insn >> 10) & 3;
      if (mode == 2) return FALSE; /* Unprivileged STTR. */
      offset = GC_numeric_ro_signed((insn >> 12) & 511, 9);
      updated = base + (word)offset;
      address = mode == 1 ? base : updated;
      store->writeback = mode != 0;
    }
  } else return FALSE;
  /* Base/data overlap with writeback is constrained-unpredictable for GPRs. */
  if (store->writeback && !fp && rn != 31
      && (rn == rt || (pair && rn == rt2))) return FALSE;
  if (!GC_numeric_ro_arm_value(uc, store, rt, rt2, size, fp, pair))
    return FALSE;
  store->dest = (ptr_t)address;
  store->base_reg = rn; store->base_value = updated;
  return TRUE;
}

STATIC void GC_numeric_ro_commit_arm(ucontext_t *uc,
                                     const GC_numeric_ro_store *store)
{
  if (store->writeback) {
    if (store->base_reg == 31) uc->uc_mcontext.sp = store->base_value;
    else uc->uc_mcontext.regs[store->base_reg] = store->base_value;
  }
  uc->uc_mcontext.pc += store->length;
}

#elif defined(__arm__)
STATIC word GC_numeric_ro_arm_reg(const ucontext_t *uc, unsigned reg)
{
  unsigned long value;
  memcpy(&value, (const char *)&uc->uc_mcontext
                    + offsetof(mcontext_t, arm_r0) + reg * sizeof(value),
         sizeof(value));
  return (word)value;
}

STATIC void GC_numeric_ro_arm_set_reg(ucontext_t *uc, unsigned reg, word value)
{
  unsigned long raw = (unsigned long)value;
  memcpy((char *)&uc->uc_mcontext + offsetof(mcontext_t, arm_r0)
                    + reg * sizeof(raw), &raw, sizeof(raw));
}

STATIC const unsigned char *
GC_numeric_ro_arm_fp(const ucontext_t *uc, unsigned reg, size_t width)
{
  const unsigned char *p = (const unsigned char *)uc->uc_regspace;
  size_t remaining = sizeof(uc->uc_regspace);
  /* Linux ARM signal ABI: magic,size,user_vfp{32 x u64, fpscr},exceptions. */
  while (remaining >= 8) {
    uint32_t magic, size;
    memcpy(&magic, p, 4); memcpy(&size, p + 4, 4);
    if (size < 8 || size > remaining || (size & 7) != 0) return NULL;
    if (magic == 0x56465001U) {
      if (size < 8 + 32 * 8 || reg >= 32) return NULL;
      return p + 8 + (width == 8 ? reg * 8 : reg * 4);
    }
    p += size; remaining -= size;
  }
  return NULL;
}

STATIC word GC_numeric_ro_arm_shift(word value, unsigned type,
                                    unsigned amount, word cpsr)
{
  switch (type) {
  case 0: return value << amount;
  case 1: return amount == 0 ? 0 : value >> amount;
  case 2: return amount == 0 ? (word)-(GC_signed_word)(value >> 31)
                            : (word)((GC_signed_word)value >> amount);
  default: return amount == 0 ? ((cpsr & (1UL << 29)) << 2) | (value >> 1)
                             : (value >> amount) | (value << (32 - amount));
  }
}

STATIC GC_bool
GC_numeric_ro_arm32_scalar(const ucontext_t *uc, GC_numeric_ro_store *store,
                           unsigned rn, unsigned rt, word offset,
                           GC_bool pre, GC_bool add, GC_bool writeback,
                           size_t width, unsigned rt2, GC_bool pair)
{
  word base, updated, value;
  if (rn == 15 || rt == 15 || (pair && rt2 == 15)
      || (writeback && (rn == rt || (pair && rn == rt2)))) return FALSE;
  base = GC_numeric_ro_arm_reg(uc, rn);
  updated = add ? base + offset : base - offset;
  value = GC_numeric_ro_arm_reg(uc, rt);
  memcpy(store->value, &value, pair ? 4 : width);
  if (pair) {
    value = GC_numeric_ro_arm_reg(uc, rt2);
    memcpy(store->value + 4, &value, 4);
  }
  store->dest = (ptr_t)(pre ? updated : base);
  store->width = width; store->writeback = writeback;
  store->base_reg = rn; store->base_value = updated;
  return TRUE;
}

STATIC GC_bool
GC_numeric_ro_decode_arm(const ucontext_t *uc, GC_numeric_ro_store *store)
{
  uint32_t insn;
  unsigned rn, rt, type;
  word offset;
  GC_bool thumb = (uc->uc_mcontext.arm_cpsr & 32) != 0;
  const unsigned char *pc = (const unsigned char *)((word)uc->uc_mcontext.arm_pc
                                                   & ~(word)1);
  store->length = 4;
  if (thumb) {
    uint16_t first, second;
    memcpy(&first, pc, 2);
    if ((first & 0xe000) == 0x6000 || (first & 0xf800) == 0x8000) {
      size_t width = (first & 0xf800) == 0x8000 ? 2
                         : (first & 0x1000) != 0 ? 1 : 4;
      if ((first & 0x0800) != 0) return FALSE;
      store->length = 2;
      return GC_numeric_ro_arm32_scalar(uc, store, (first >> 3) & 7,
          first & 7, ((first >> 6) & 31) * width, TRUE, TRUE, FALSE,
          width, 0, FALSE);
    }
    if ((first & 0xf000) == 0x5000) {
      static const unsigned widths[3] = { 4, 2, 1 };
      type = (first >> 9) & 7;
      if (type > 2) return FALSE;
      store->length = 2;
      return GC_numeric_ro_arm32_scalar(uc, store, (first >> 3) & 7,
          first & 7, GC_numeric_ro_arm_reg(uc, (first >> 6) & 7),
          TRUE, TRUE, FALSE, widths[type], 0, FALSE);
    }
    if ((first & 0xf800) == 0x9000) {
      store->length = 2;
      return GC_numeric_ro_arm32_scalar(uc, store, 13, (first >> 8) & 7,
          (first & 255) * 4, TRUE, TRUE, FALSE, 4, 0, FALSE);
    }
    if ((first & 0xf800) < 0xe800) return FALSE;
    memcpy(&second, pc + 2, 2);
    insn = ((uint32_t)first << 16) | second;
    rn = first & 15; rt = second >> 12;
    if ((first & 0xffe0) == 0xf880 || (first & 0xffe0) == 0xf8a0
        || (first & 0xffe0) == 0xf8c0) {
      size_t width = (first & 0x60) == 0 ? 1
                            : (first & 0x60) == 0x20 ? 2 : 4;
      /* Each accepted first-halfword group has the load bit clear. */
      if ((first & 0x10) != 0) return FALSE;
      return GC_numeric_ro_arm32_scalar(uc, store, rn, rt, second & 4095,
          TRUE, TRUE, FALSE, width, 0, FALSE);
    }
    if ((first & 0xffe0) == 0xf800 || (first & 0xffe0) == 0xf820
        || (first & 0xffe0) == 0xf840) {
      size_t width = (first & 0x60) == 0 ? 1
                            : (first & 0x60) == 0x20 ? 2 : 4;
      if ((first & 0x10) != 0) return FALSE;
      if ((second & 0x0800) == 0) {
        if ((second & 0x0fc0) != 0 || (second & 15) == 15) return FALSE;
        offset = GC_numeric_ro_arm_reg(uc, second & 15)
                   << ((second >> 4) & 3);
        return GC_numeric_ro_arm32_scalar(uc, store, rn, rt, offset,
              TRUE, TRUE, FALSE, width, 0, FALSE);
      } else {
        GC_bool pre = (second & 0x0400) != 0;
        GC_bool wb = (second & 0x0100) != 0;
        if (!pre && !wb) return FALSE;
        if (pre && !wb && (second & 0x0200) != 0)
          return FALSE; /* Unprivileged STRT/STRBT/STRHT. */
        return GC_numeric_ro_arm32_scalar(uc, store, rn, rt, second & 255,
            pre, (second & 0x0200) != 0, wb, width, 0, FALSE);
      }
    }
    if ((first & 0xfe50) == 0xe840) {
      GC_bool pre = (first & 0x0100) != 0;
      GC_bool wb = (first & 0x0020) != 0;
      if (!pre && !wb) return FALSE;
      return GC_numeric_ro_arm32_scalar(uc, store, rn, rt,
          (second & 255) * 4, pre, (first & 0x0080) != 0, wb,
          8, (second >> 8) & 15, TRUE);
    }
  } else {
    memcpy(&insn, pc, 4);
    if ((insn >> 28) == 15) return FALSE;
    rn = (insn >> 16) & 15; rt = (insn >> 12) & 15;
    if ((insn & 0x0c100000U) == 0x04000000U) {
      GC_bool pre = (insn & (1U << 24)) != 0;
      GC_bool wb = !pre || (insn & (1U << 21)) != 0;
      if (!pre && (insn & (1U << 21)) != 0) return FALSE;
      if ((insn & (1U << 25)) != 0) {
        if ((insn & 16) != 0 || (insn & 15) == 15) return FALSE;
        offset = GC_numeric_ro_arm_shift(GC_numeric_ro_arm_reg(uc, insn & 15),
                   (insn >> 5) & 3, (insn >> 7) & 31,
                   uc->uc_mcontext.arm_cpsr);
      } else offset = insn & 4095;
      return GC_numeric_ro_arm32_scalar(uc, store, rn, rt, offset, pre,
          (insn & (1U << 23)) != 0, wb,
          (insn & (1U << 22)) != 0 ? 1 : 4, 0, FALSE);
    }
    if ((insn & 0x0e100090U) == 0x00000090U) {
      GC_bool pre = (insn & (1U << 24)) != 0;
      GC_bool wb = !pre || (insn & (1U << 21)) != 0;
      type = (insn >> 5) & 3;
      if ((type != 1 && type != 3)
          || (type == 3 && (rt & 1) != 0)
          || (!pre && (insn & (1U << 21)) != 0)) return FALSE;
      if ((insn & (1U << 22)) != 0)
        offset = ((insn >> 4) & 240) | (insn & 15);
      else {
        if ((insn & 0xf00) != 0 || (insn & 15) == 15) return FALSE;
        offset = GC_numeric_ro_arm_reg(uc, insn & 15);
      }
      return GC_numeric_ro_arm32_scalar(uc, store, rn, rt, offset, pre,
          (insn & (1U << 23)) != 0, wb, type == 1 ? 2 : 8,
          rt + 1, type == 3);
    }
  }
  /* VSTR S/D has the same encoding in ARM and Thumb-2. It has no writeback. */
  if ((insn & 0x0f300e00U) == 0x0d000a00U) {
    size_t width = (insn & 0x100) != 0 ? 8 : 4;
    unsigned vd = (insn >> 12) & 15, high = (insn >> 22) & 1;
    const unsigned char *value;
    rn = (insn >> 16) & 15;
    if (rn == 15) return FALSE;
    vd = width == 8 ? vd | (high << 4) : (vd << 1) | high;
    value = GC_numeric_ro_arm_fp(uc, vd, width);
    if (value == NULL) return FALSE;
    offset = (insn & 255) * 4;
    store->dest = (ptr_t)((insn & (1U << 23)) != 0
          ? GC_numeric_ro_arm_reg(uc, rn) + offset
          : GC_numeric_ro_arm_reg(uc, rn) - offset);
    store->width = width; memcpy(store->value, value, width);
    return TRUE;
  }
  return FALSE;
}

STATIC void GC_numeric_ro_commit_arm(ucontext_t *uc,
                                     const GC_numeric_ro_store *store)
{
  if (store->writeback)
    GC_numeric_ro_arm_set_reg(uc, store->base_reg, store->base_value);
  uc->uc_mcontext.arm_pc += store->length;
  if ((uc->uc_mcontext.arm_cpsr & 32) != 0) {
    /* Emulating a Thumb store also consumes its IT slot. The kernel restores
       the faulting instruction's ITSTATE, so only advancing PC is incorrect. */
    word cpsr = uc->uc_mcontext.arm_cpsr;
    unsigned state = ((cpsr >> 25) & 3) | ((cpsr >> 8) & 0xfc);
    state = (state & 7) == 0 ? 0 : (state & 0xe0) | ((state << 1) & 31);
    uc->uc_mcontext.arm_cpsr = (cpsr & ~((word)3 << 25 | (word)0xfc << 8))
                               | ((word)(state & 3) << 25)
                               | ((word)(state & 0xfc) << 8);
  }
}
#endif
