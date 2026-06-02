# =============================================================================
#  lp1_conj_lsm.jl  —  Staged RAM+SSD LP1-conj index (LSM-tree style)
#
#  Drop-in replacement for ShardedLP1Conj that caps RAM usage at O(buffer size)
#  rather than O(total entries) by spilling sorted runs to a flat binary file
#  on SSD.
#
#  Design
#  ──────
#  Hot path (RAM):
#    • A sharded open-addressing table (LP1ConjLSM.hot) holds recently inserted
#      entries.  Same ConjShard{V} primitives as before.
#    • When any shard's live count crosses its flush threshold, the shard is
#      sorted by fingerprint and appended as a new "run" to the spill file.
#
#  Cold path (SSD, pread):
#    • All flushed runs live in a single flat binary file.  Each record is
#      exactly RECORD_BYTES (48) bytes; see lp1_conj_lsm_constants.jl for
#      the field layout.
#    • Each RunMeta stores (byte_offset, len, min_fp, max_fp) and a tombstone
#      bitvector in RAM.
#    • Lookup: check Bloom filter → skip run if fp outside [min,max] → binary
#      search on fp field (stride RECORD_BYTES) → verify full key → return
#      payload.
#
#  Public API  (same as ShardedLP1Conj)
#  ─────────────────────────────────────
#    conj_shard_idx / canonical_lp1_conj_key  (defined in trial3_config.jl)
#    conj_total_entries, conj_haskey, conj_getval, conj_pop!, conj_insert!
#    conj_insert_or_pop!
#    lsm_flush_all!, lsm_close!, lsm_info
#
#  Module layout
#  ─────────────
#    lp1_conj_lsm_constants.jl  — compile-time constants and _lsm_fp
#    lp1_conj_lsm_bloom.jl      — BloomFilter struct and helpers
#    lp1_conj_lsm_disk.jl       — RunMeta, record encode/decode, pread I/O
#    lp1_conj_lsm_topk.jl       — TopKMultiplicity min-heap reservoir
#    lp1_conj_lsm_core.jl       — LP1ConjLSM struct, hot-shard layer, public API
#    lp1_conj_lsm_renyi.jl      — AMS sketch, cold bitmap, Rényi-2 estimators
#                                  (after core: functions take sc::LP1ConjLSM)
# =============================================================================

include("lp1_conj_lsm_constants.jl")
include("lp1_conj_lsm_bloom.jl")
include("lp1_conj_lsm_disk.jl")
include("lp1_conj_lsm_topk.jl")
include("lp1_conj_lsm_core.jl")
include("lp1_conj_lsm_renyi.jl")
