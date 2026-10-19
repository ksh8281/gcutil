/* Compressed equivalents of the native push_marked accelerators.  Restrict
 * this experiment to stopped serial minor rescuers.  Full/invalid marking,
 * dense old-only snapshots, custom descriptors and large objects keep the
 * ordinary queue path.  No strong-edge or object-offset check is omitted. */
#if defined(ESCARGOT_USE_32BIT_IN_64BIT) \
    && !defined(MARK_BIT_PER_OBJ) && !defined(USE_MARK_BYTES)
# ifdef GC_SOURCE_BATCH_AUDIT
#   define GC_BATCH_COUNT(index, amount) \
      (GC_source_batch_stats[index] += (word)(amount))
# else
#   define GC_BATCH_COUNT(index, amount) ((void)0)
# endif

/* Probe only at the containing granule when the byte displacement is
 * registered.  A set bit then belongs to that exact object's first granule.
 * On a miss, pass the ORIGINAL tagged pointer through the ordinary header,
 * displacement, mark and enqueue checks. */
#define GC_BATCH_PUSH(current, top, limit, source) do { \
    hdr *my_hhdr = NULL; \
    ptr_t probe = (current); \
    word displacement = ADDR(current) & (GC_GRANULE_BYTES - 1); \
    if (fast_tags && displacement != 0 && GC_valid_offsets[displacement]) { \
      probe = (ptr_t)(ADDR(current) - displacement); \
      GC_BATCH_COUNT(8, 1); \
    } \
    if (GC_target_probe(probe, &my_hhdr)) { \
      if (probe != (current)) GC_BATCH_COUNT(9, 1); \
      break; \
    } \
    if (probe != (current)) GC_BATCH_COUNT(10, 1); \
    if (my_hhdr == NULL) { \
      HC_GET_HDR(current, my_hhdr, source); \
    } \
    (top) = GC_ms_push_contents_hdr(current, my_hhdr, top, limit, source, TRUE); \
  } while (0)

STATIC GC_bool
GC_scan_compressed_sources(struct hblk *h, const hdr *hhdr)
{
  word selected[GC_YOUNG_DENSE_WORDS];
  unsigned format = hhdr->hb_flags & COMPRESSED_FORMAT_MASK;
  const GC_compressed_bitmap_descr *bitmap = NULL;
  word fields = 0, upper;
  GC_bool fast_tags = (GC_source_batch_mode & 4) != 0;
  size_t i, last_bit, length = 0;
  mse *top, *limit;
  ptr_t greatest_ha, least_ha;
# ifdef GC_SOURCE_BATCH_AUDIT
  word before_live = GC_young_live_bytes;
  word objects = 0, slot_bytes = 0;
# endif
  DECLARE_HDR_CACHE;

  if (!GC_source_batch_mode || !GC_young_mark_active
      || GC_mark_state != MS_PUSH_RESCUERS
      || GC_young_source_filter_disabled
      || IS_UNCOLLECTABLE(hhdr->hb_obj_kind)
      || hhdr->hb_sz > MAXOBJBYTES)
    return FALSE;
# ifdef PARALLEL_MARK
  if (GC_parallel)
    return FALSE;
# endif
  if (format == COMPRESSED_BITMAP && (GC_source_batch_mode & 1)) {
    bitmap = (const GC_compressed_bitmap_descr *)hhdr->hb_descr;
    if (bitmap == NULL || bitmap->slots == 0 || bitmap->slots > CPP_WORDSZ
        || bitmap->slots > hhdr->hb_sz / 4)
      return FALSE;
    fields = GC_COMPRESSED_BITMAP(bitmap)[0]
             & ~(~(word)0 << (bitmap->slots - 1) << 1);
    GC_BATCH_COUNT(0, 1);
  } else if (format == COMPRESSED_POINTERS && (GC_source_batch_mode & 2)) {
    length = hhdr->hb_descr;
    if (length == 0 || (length & 3) != 0 || length > hhdr->hb_sz)
      return FALSE;
    GC_BATCH_COUNT(1, 1);
  } else {
    return FALSE;
  }

  /* Marking a child can change a later word of this same block.  Snapshot
   * the selected starts before tracing any field, as the enqueue-only path
   * does, so newly marked children are traced by their own queue entry. */
  last_bit = FINAL_MARK_BIT(hhdr->hb_sz);
  for (i = 0; i < GC_YOUNG_DENSE_WORDS; ++i) {
    selected[i] = hhdr->hb_marks[i];
    if (i == divWORDSZ(last_bit))
      selected[i] &= ~((word)1 << modWORDSZ(last_bit));
  }
  top = GC_mark_stack_top;
  limit = GC_mark_stack_limit;
  greatest_ha = (ptr_t)GC_greatest_plausible_heap_addr;
  least_ha = (ptr_t)GC_least_plausible_heap_addr;
  upper = (word)h & ~(word)0xffffffffU;
  INIT_HDR_CACHE;
  for (i = 0; i < GC_YOUNG_DENSE_WORDS; ++i) {
    word starts = selected[i];
    while (starts != 0) {
      size_t bit = (size_t)__builtin_ctzll(starts);
      ptr_t payload = h->hb_body
                      + (i * CPP_WORDSZ + bit) * GC_GRANULE_BYTES;
      starts &= starts - 1;
      if (bitmap != NULL) {
        word bits = fields;
# ifdef GC_SOURCE_BATCH_AUDIT
        ++objects;
        slot_bytes += (word)__builtin_popcountll(fields) * 4;
# endif
        while (bits != 0) {
          size_t slot = (size_t)__builtin_ctzll(bits);
          ptr_t source = payload + slot * 4;
          unsigned32 low = *(unsigned32 *)source;
          ptr_t q;
          bits &= bits - 1;
          if (slot == bitmap->tagged_slot)
            low &= ~bitmap->tag_mask;
          if (low == 0 || (low & 1) != 0)
            continue;
          q = (ptr_t)(upper | (word)low);
          if (ADDR_LT(least_ha, q) && ADDR_LT(q, greatest_ha)) {
            PREFETCH(q);
            GC_BATCH_PUSH(q, top, limit, source);
          }
        }
      } else {
        ptr_t end = payload + length;
# ifdef GC_SOURCE_BATCH_AUDIT
        ++objects;
        slot_bytes += length;
# endif
        for (; ADDR_LT(payload, end); payload += 4) {
          unsigned32 low = *(unsigned32 *)payload;
          ptr_t q;
          if (low == 0 || (low & 1) != 0)
            continue;
          q = (ptr_t)(upper | (word)low);
          if (ADDR_LT(least_ha, q) && ADDR_LT(q, greatest_ha)) {
            PREFETCH(q);
            GC_BATCH_PUSH(q, top, limit, payload);
          }
        }
      }
      /* The ordinary marker tests aborts between objects, too.  Keep the
       * already-marked pointer hot path free of an extra flag load per slot. */
      if (UNLIKELY(GC_young_mark_aborted
                   || GC_mark_state != MS_PUSH_RESCUERS))
        goto done;
    }
  }
done:
  GC_mark_stack_top = top;
  GC_BATCH_COUNT(6, GC_young_mark_aborted
                       || GC_mark_state != MS_PUSH_RESCUERS);
# ifdef GC_SOURCE_BATCH_AUDIT
  GC_BATCH_COUNT(bitmap != NULL ? 2 : 3, objects);
  GC_BATCH_COUNT(bitmap != NULL ? 4 : 5, slot_bytes);
  GC_BATCH_COUNT(7, GC_young_live_bytes - before_live);
  ++GC_source_batch_kinds[hhdr->hb_obj_kind][0];
  GC_source_batch_kinds[hhdr->hb_obj_kind][1] += objects;
  GC_source_batch_kinds[hhdr->hb_obj_kind][2] += slot_bytes;
# endif
  return TRUE;
}
# undef GC_BATCH_PUSH
# undef GC_BATCH_COUNT
#endif
