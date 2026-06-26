# =============================================================================
#  lp1_conj_lsm_constants.jl — compile-time constants for LP1ConjLSM
# =============================================================================

const RECORD_BYTES = 48   # fp(8) + u0u1v0v1(16) + i0(2) + step(4) + pad(2) + al(8) + be(8)

# ---------------------------------------------------------------------------
#  Rényi-2 / S₂ estimator — AMS sketch (Alon-Matias-Szegedy)
#
#  AMS_GROUPS = 32  (groups for median — controls tail probability)
#  AMS_WIDTH  = 16  (estimators per group — controls variance within group)
#  Total sketch: 32×16 = 512 Int64 accumulators = 4 KB.  Never saturates.
# ---------------------------------------------------------------------------
const AMS_GROUPS = 32
const AMS_WIDTH  = 16
const AMS_K      = AMS_GROUPS * AMS_WIDTH   # 512 total hash functions

# Precomputed salts: AMS_K distinct 64-bit constants, two independent families.
#
# AMS_SALTS    — multiplier for the low  64 bits of the CanonicalLP1Key (UInt128).
# AMS_SALTS_HI — multiplier for the high 64 bits of the CanonicalLP1Key (UInt128).
#
# Using two independent families is required for correctness: the AMS sign
# function must be defined over the FULL 128-bit key, not a 64-bit lossy
# fingerprint.  If we hashed only _lsm_fp(key) (a UInt64), any two distinct
# keys that collide in fp-space would receive identical sign vectors across
# ALL hash functions simultaneously, causing a systematic overestimate of F₂
# (and therefore a systematic underestimate of S₂ and α₂).
#
# With two independent tables the sign for hash function j is:
#   σ_j(key) = MSB( lo(key) * AMS_SALTS[j]  +  hi(key) * AMS_SALTS_HI[j] )
# This is a proper linear sketch over GF(2^64) applied to the full 128-bit key.
# The two tables are seeded from separate rand() calls so they are statistically
# independent (Julia's global RNG advances between the two let-blocks).
const AMS_SALTS = let
    s = rand(UInt64)
    v = Vector{UInt64}(undef, AMS_K)
    for i in 1:AMS_K
        s = s ⊻ (s << 13)
        s = s ⊻ (s >> 7)
        s = s ⊻ (s << 17)
        v[i] = s
    end
    Tuple(v)
end

const AMS_SALTS_HI = let
    s = rand(UInt64)
    v = Vector{UInt64}(undef, AMS_K)
    for i in 1:AMS_K
        s = s ⊻ (s << 13)
        s = s ⊻ (s >> 7)
        s = s ⊻ (s << 17)
        v[i] = s
    end
    Tuple(v)
end

# ---------------------------------------------------------------------------
#  Cold-filter bitmap — separate from the S₂ estimator.
#
#  2^COLD_BITS-bucket presence bitmap: bit (fp >> COLD_SHIFT) is set on
#  first emission to that coarse bucket.  Used only by the flush cold-filter;
#  NOT for S₂ estimation.
# ---------------------------------------------------------------------------
const COLD_BITS  = 20                    # 1M buckets, 128 KB bitmap
const COLD_SHIFT = 64 - COLD_BITS
const COLD_WORDS = (1 << COLD_BITS) ÷ 64  # 16384 UInt64 words

# Circular buffer capacity for the partial fingerprint log.
# Stores COLD_BITS-bit bucket indices as UInt32 (20 bits fits in UInt32).
# At 4 bytes/entry this costs 4 MB and always reflects the most recent
# PARTIAL_FP_LOG_CAP emissions regardless of total walk length.
const PARTIAL_FP_LOG_CAP = 1_000_000

# Top-K multiplicity tracker capacity.
const TOPK_K = 200   # track top-200 keys by raw emission count

# Per-shard base cap on hot_rows (the Dict{CanonicalLP1Key,Dict{Int,Int}}
# side-channel that stores fb_rows for live hot entries so closes can
# reconstruct relations).
#
# Without a cap, hot_rows grows with every insertion and is only trimmed on
# closure (rare: ~0.001% rate) or shard flush (only happens when the hot table
# reaches ~75% load).  At 278K entries/LSM × 32 LSMs × ~200B/entry the hot_rows
# alone consume ~1.8 GB, and they grow continuously throughout the walk.
#
# When the per-shard cap is hit we skip storing the fb_row.  The key/val are
# still inserted into the hot table so same-partial detection keeps working; a
# subsequent closure attempt returns row_missing (existing path) and is discarded.
#
# K-scaling: with K-tuple anchors the fb_row Dict has K entries instead of 1,
# so each stored Dict{Int,Int} is ~K× larger.  More importantly the effective
# keyspace grows with K (more distinct Mumford residuals reachable), so the
# store fills faster per unit time.  The effective per-shard cap is therefore
# HOT_ROWS_CAP_BASE_PER_SHARD ÷ K, matching the CONJ_ROW_STORE_CAP_BASE ÷ K
# scaling used for the (now-defunct) per-thread conj_row_store.
#
# This value is the BASE (K=1) cap per shard.  The runtime cap is computed at
# LP1ConjLSM construction time (see LP1ConjLSM{V} inner constructor) and stored
# in the hot_rows_cap field of the struct.  The constant here must NOT be used
# directly in hot-path code — always use sc.hot_rows_cap instead.
#
# Sizing (K=1): 500 rows/shard × 64 shards × 32 LSMs × ~200B ≈ 200 MB total.
# K=2 → 250/shard ≈ 100 MB total.  The cap is a safety bound; in practice
# closures are so rare that the shard row-dict stays small.
const HOT_ROWS_CAP_BASE_PER_SHARD = 500

# Compaction write buffer.
const COMPACT_WRITE_BUF_BYTES = 4 * 1024 * 1024   # 4 MB write buffer

# ---------------------------------------------------------------------------
#  Record field offsets within a record (0-based byte offsets from record start):
#   0: fp   UInt64
#   8: u0   UInt32
#  12: u1   UInt32
#  16: v0   UInt32
#  20: v1   UInt32
#  24: i0   UInt16
#  26: step UInt32   ← store_step (D8 diagnostic: raw_step at insert time, truncated to UInt32)
#  30: pad  UInt16   (2 bytes, zeroed)
#  32: al   UInt64
#  40: be   UInt64
# total: 48
# ---------------------------------------------------------------------------
const OFF_FP   = 0
const OFF_U0   = 8
const OFF_U1   = 12
const OFF_V0   = 16
const OFF_V1   = 20
const OFF_I0   = 24
const OFF_STEP = 26   # UInt32 store_step for D8 closure-depth diagnostic
# bytes 30-31: padding (zeroed)
const OFF_AL   = 32
const OFF_BE   = 40

# ---------------------------------------------------------------------------
#  Fingerprint
# ---------------------------------------------------------------------------
@inline function _lsm_fp(key::CanonicalLP1Key)::UInt64
    lo = UInt64(key & 0xffffffffffffffff)
    hi = UInt64(key >> 64)
    h  = lo * 0x9e3779b97f4a7c15 +
         hi * 0x6c62272e07bb0142
    h = h ⊻ (h >> 32)
    h = h * 0x45d9f3b37197344d
    h = h ⊻ (h >> 32)
    h
end
