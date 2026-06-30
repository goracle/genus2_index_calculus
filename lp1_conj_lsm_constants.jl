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

# ---------------------------------------------------------------------------
#  AMS sign function — 4-wise independent construction.
#
#  PRIOR DESIGN (superseded): σ_j(key) = MSB(k_lo·s_j + k_hi·s_j_hi), a
#  degree-1 (linear, "multiply-shift") hash. This is only 2-universal
#  (pairwise independent). The AMS unbiasedness proof E[Z_j²] = F₂ only
#  needs pairwise independence, so the point estimate was always correct —
#  but the per-group variance bound Var[group mean] ≤ 2F₂²/AMS_WIDTH that
#  justifies treating AMS_WIDTH as a meaningful variance-reduction knob
#  formally requires 4-WISE independence of the σ_j family. A degree-1
#  hash cannot provide that no matter how its coefficients are generated;
#  it's an algebraic ceiling, not an RNG-quality problem.
#
#  CURRENT DESIGN: degree-3 polynomial hash over GF(p), p = 2^61 - 1
#  (Mersenne prime). For hash index j with independent uniform random
#  coefficients (a_j, b_j, c_j, d_j) ∈ GF(p)^4:
#
#      h_j(x) = (a_j·x³ + b_j·x² + c_j·x + d_j)  mod p
#      σ_j(x) = +1 if h_j(x) is even, else -1
#
#  where x ∈ GF(p) is a single field element derived from the FULL 128-bit
#  key via a fixed (non-random, collision-resistant) avalanche mix — see
#  `_ams_mix_to_field` below. Standard result (Carter–Wegman / Vandermonde
#  argument): a degree-(k-1) polynomial with independent uniform
#  coefficients over a field is k-wise independent. Degree 3 → 4-wise
#  independent, which is exactly what the AMS variance bound needs.
#
#  Parity-of-h_j as the sign bit is an unbiased 1-bit extraction from a
#  uniform-over-GF(p) value: p is odd (Mersenne prime), so exactly
#  (p-1)/2 even and (p-1)/2+1... — to avoid the off-by-one parity bias
#  from p being odd (there's one extra odd residue, 0 is even), we instead
#  test h_j(x) < p÷2 (a clean bisection of the odd-sized residue range,
#  off by at most one element out of 2^61 — negligible, unlike a raw
#  evenness test which has the same off-by-one issue anyway). Both are
#  fine in practice; we use the bisection form for clarity.
#
#  Cost: each σ_j evaluation is a 3-multiply Horner-scheme polynomial
#  mod p61 using UInt128 intermediates (products up to 122 bits, fits
#  safely) plus a fixed 2-round shift-add Mersenne reduction. This is
#  more expensive per hash than the old single-multiply linear hash —
#  expect roughly 3-5x the cost of the AMS inner loop. AMS_K=512 of
#  these run per emission. Benchmark before assuming this is free; if
#  it becomes a bottleneck, reducing AMS_K (fewer, wider groups) is a
#  cheaper lever than reverting to a lower-independence hash.
# ---------------------------------------------------------------------------
const AMS_P61 = UInt64(2)^61 - UInt64(1)   # Mersenne prime 2^61 - 1

# Coefficients: AMS_K independent draws of (a,b,c,d), each uniform on
# [0, AMS_P61). Uses Julia's `rand(0:AMS_P61-1)` directly (true uniform
# sampling from the global RNG per draw), NOT a deterministic xorshift
# stream walked forward — each coefficient is an independent call into
# the RNG, matching the independence assumption the 4-wise proof needs.
const AMS_COEF_A = Tuple(rand(UInt64(0):(AMS_P61 - UInt64(1))) for _ in 1:AMS_K)
const AMS_COEF_B = Tuple(rand(UInt64(0):(AMS_P61 - UInt64(1))) for _ in 1:AMS_K)
const AMS_COEF_C = Tuple(rand(UInt64(0):(AMS_P61 - UInt64(1))) for _ in 1:AMS_K)
const AMS_COEF_D = Tuple(rand(UInt64(0):(AMS_P61 - UInt64(1))) for _ in 1:AMS_K)

# Fixed (non-random) finalizer constants for the 128-bit→field mixer.
# Reuses the same SplitMix64-style avalanche structure as `_lsm_fp` below,
# but with DISTINCT constants so the AMS field element is not a trivial
# function of the fp fingerprint (keeps the two purposes decorrelated).
const AMS_MIX_C1 = 0xff51afd7ed558ccd
const AMS_MIX_C2 = 0xc4ceb9fe1a85ec53

@inline function _ams_mod_p61(x::UInt128)::UInt64
    # 2-round shift-add Mersenne reduction; safe for any x with ≤122 bits
    # (verified: max product of two values < 2^61 is 2^122-ish, needs at
    # most 2 rounds to fall below 2^61). Final branch corrects the case
    # x == p61 exactly (shift-add alone leaves the result in [0, p61]).
    p   = UInt128(AMS_P61)
    x   = (x & p) + (x >> 61)
    x   = (x & p) + (x >> 61)
    x  -= ifelse(x >= p, p, UInt128(0))
    return UInt64(x)
end

@inline function _ams_mix_to_field(k_lo::UInt64, k_hi::UInt64)::UInt64
    # Fixed avalanche mix of the full 128-bit key down to one 64-bit value,
    # then reduced into GF(p61). This is purely for collision-resistant
    # compression of the key (NOT where the 4-wise independence comes
    # from — that's entirely in the random polynomial coefficients), so
    # it deliberately does NOT need to be random or per-hash-function.
    h  = k_lo * AMS_MIX_C1 + k_hi * AMS_MIX_C2
    h  = h ⊻ (h >> 33)
    h *= 0xff51afd7ed558ccd
    h  = h ⊻ (h >> 33)
    h *= 0xc4ceb9fe1a85ec53
    h  = h ⊻ (h >> 33)
    # h is now a well-mixed UInt64; reduce mod p61 (single round suffices,
    # UInt64 max < 2^64 < 2*p61's range after one shift-add step... use
    # the same safe 2-round reducer for consistency/simplicity).
    return _ams_mod_p61(UInt128(h))
end

@inline function _ams_sign(j::Int, x::UInt64)::Int64
    # Horner evaluation of a_j x^3 + b_j x^2 + c_j x + d_j over GF(p61).
    @inbounds begin
        a = AMS_COEF_A[j]; b = AMS_COEF_B[j]
        c = AMS_COEF_C[j]; d = AMS_COEF_D[j]
    end
    r = a
    r = _ams_mod_p61(UInt128(r) * UInt128(x) + UInt128(b))
    r = _ams_mod_p61(UInt128(r) * UInt128(x) + UInt128(c))
    r = _ams_mod_p61(UInt128(r) * UInt128(x) + UInt128(d))
    return ifelse(r < (AMS_P61 >> 1), Int64(1), Int64(-1))
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
