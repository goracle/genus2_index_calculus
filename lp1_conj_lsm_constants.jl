# =============================================================================
#  lp1_conj_lsm_constants.jl — compile-time constants for LP1ConjLSM
# =============================================================================

# ---------------------------------------------------------------------------
#  Record field offsets within a record (0-based byte offsets from record start):
#    0: fp      UInt64
#    8: u0      UInt32
#   12: u1      UInt32
#   16: v0      UInt32
#   20: v1      UInt32
#   24: i[1..K_MAX]   K_MAX × UInt16  ← anchor_indices, one slot per
#                      multiplicity unit; unused trailing slots are
#                      ANCHOR_IDX_NONE (0xffff)
#   24+2*K_MAX: step  UInt32   ← store_step (D8 closure-depth diagnostic)
#   28+2*K_MAX: al    UInt64
#   36+2*K_MAX: be    UInt64
#  total: 44 + 2*K_MAX bytes
# ---------------------------------------------------------------------------
const OFF_FP   = 0
const OFF_U0   = 8
const OFF_U1   = 12
const OFF_V0   = 16
const OFF_V1   = 20
const OFF_I0   = 24                     # start of the K_MAX anchor-index slots
const OFF_STEP = 24 + 2*K_MAX
const OFF_AL   = 28 + 2*K_MAX
const OFF_BE   = 36 + 2*K_MAX

const RECORD_BYTES = 44 + 2*K_MAX   # fp(8) + u0u1v0v1(16) + i[1..K_MAX](2*K_MAX) + step(4) + al(8) + be(8)

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

# HOT_ROWS_CAP_PER_SHARD — REMOVED.
# Anchor FB indices are now stored in LP1ConjVal.anchor_indices; the hot_rows
# side-channel Dict has been eliminated from LP1ConjLSM entirely.

# Compaction write buffer.
const COMPACT_WRITE_BUF_BYTES = 4 * 1024 * 1024   # 4 MB write buffer

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
