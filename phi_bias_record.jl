# =============================================================================
#  phi_bias_record.jl  --  Hot-path accumulator functions and math helpers.
#
#  Exports:
#    record_phi_step!          — called once per valid phi step in phase2_worker
#    record_lp1_conj_partial!  — called for every LP1-conj partial (stored+closed)
#    record_lp1_conj_hit!      — called on birthday-match closure
#    record_random_anchor!     — clears the post-LP anchor flag
#    _phi_fp, _rotl64, _mix_u64, _mix_event_hash  — internal hash utilities
#    _moment4, _kl_divergence_counts, _top_share   — post-hoc stat helpers
# =============================================================================

# ---------------------------------------------------------------------------
#  Fingerprint constants (must match lsm_bday_report's Rényi granularity)
# ---------------------------------------------------------------------------
const _PHI_RENYI_BITS  = 14
const _PHI_RENYI_SHIFT = 64 - _PHI_RENYI_BITS

# ---------------------------------------------------------------------------
#  record_phi_step! — called once per valid phi step in phase2_worker.
#
#  Arguments:
#    stat     — per-thread PhiBiasStat
#    a        — the scalar a from build_phi_mumford (already reduced mod p)
#    c1_rs    — first Mumford coeff of residual quadratic
#    c0_rs    — second Mumford coeff of residual quadratic
#    split    — true iff the residual split over 𝔽ₚ (rs_split)
#    r_in_fb  — true iff R is in the factor base (iR != 0), ignored when !split
#    s_in_fb  — true iff S is in the factor base (iS != 0), ignored when !split
#    d_key    — (u0,u1,v0,v1) Mumford representation of the current divisor D
#    p        — field characteristic (used for bucket index)
# ---------------------------------------------------------------------------
@inline function record_phi_step!(stat   ::PhiBiasStat,
                                   a      ::Int,
                                   c1_rs  ::Int,
                                   c0_rs  ::Int,
                                   split  ::Bool,
                                   r_in_fb::Bool,
                                   s_in_fb::Bool,
                                   d_key  ::NTuple{4,Int},
                                   p      ::Int)
    stat.total += 1

    # --- Bucket index for a (0-based bucket, 1-indexed in array) ---
    nbuckets = length(stat.split_hist)
    # a is already in [0, p-1].  Multiply-then-shift is branch-free.
    bucket = 1 + (a * nbuckets) ÷ p   # integer division, result in [1,nbuckets]
    bucket = clamp(bucket, 1, nbuckets)

    if split
        stat.split_hist[bucket] += 1
    else
        stat.nonsplit_hist[bucket] += 1
    end

    # --- a=0 slice ---
    if a == 0
        stat.a_zero += 1
        if split
            stat.a_zero_split += 1
            if r_in_fb && s_in_fb
                stat.a_zero_fb += 1
            end
        end
    end

    # --- Image-collision tracking (rolling per-D window) ---
    if d_key !== stat._img_key
        # Divisor changed: reset window.
        empty!(stat._img_seen)
        stat._img_key = d_key
    end
    img_pair = (c1_rs, c0_rs)
    if img_pair in stat._img_seen
        stat.image_collisions += 1
    else
        push!(stat._img_seen, img_pair)
    end

    # --- Seq 1: run-length tracking ---
    if stat._run_len == 0
        # First step ever: initialise run state.
        stat._run_is_split = split
        stat._run_len      = 1
    elseif split == stat._run_is_split
        stat._run_len += 1
    else
        # Run ended — commit it.
        k = clamp(stat._run_len, 1, MAX_RUN_LEN)
        if stat._run_is_split
            stat.run_hist_split[k] += 1
        else
            stat.run_hist_nonsplit[k] += 1
        end
        # Start new run.
        stat._run_is_split = split
        stat._run_len      = 1
    end

    # --- Seq 3: post-LP anchor histogram ---
    if stat._prev_anchor_was_lp
        stat.post_lp_a_hist[bucket] += 1
    else
        stat.baseline_a_hist[bucket] += 1
    end
    # _prev_anchor_was_lp is set externally by record_lp1_conj_anchor! /
    # record_random_anchor! — those are called by the walk loop after updating
    # cur_pt, not here, so the flag read above reflects the *previous* step's
    # anchor choice, which is what we want.

    # --- provenance hash chain (thread-local scalar only, no per-step vector) ---
    stat._event_hash_state = _mix_event_hash(stat._event_hash_state, bucket, split, a, c1_rs, c0_rs, stat.total)

    return nothing
end

# ---------------------------------------------------------------------------
#  record_lp1_conj_partial! — called inside handle_1lp_conj! on EVERY partial
#  (both stored and closed), to build the full LP1-conj key stream for α₂ scaling.
#  Uses the same fingerprint hash as the LSM (_lsm_fp) so the bucket indices are
#  consistent with lsm_bday_report's Rényi estimator.
#  RENYI_BITS = 14 → 16384 buckets; UInt16 bucket index is stored per partial.
# ---------------------------------------------------------------------------
@inline function _phi_fp(key::UInt128)::UInt64
    lo = UInt64(key & 0xffffffffffffffff)
    hi = UInt64(key >> 64)
    h  = lo * UInt64(0x9e3779b97f4a7c15) +
         hi * UInt64(0x6c62272e07bb0142)
    h  = h ⊻ (h >> 32)
    h  = h * UInt64(0x45d9f3b37197344d)
    h  = h ⊻ (h >> 32)
    h
end

@inline function record_lp1_conj_partial!(stat::PhiBiasStat, lp_key::UInt128)
    length(stat.lp1_conj_key_blog) >= MAX_LP1_CONJ_BLOG && return nothing
    bkt = UInt16(_phi_fp(lp_key) >> _PHI_RENYI_SHIFT)
    push!(stat.lp1_conj_key_blog, bkt)
    return nothing
end

# ---------------------------------------------------------------------------
#  record_lp1_conj_hit! — called inside handle_1lp_conj! only when a relation
#  is actually emitted (i.e. a birthday match is closed).  raw_step is the
#  current s.raw_steps counter passed through from the worker.
#  lp_key is the CanonicalLP1Key (UInt128) of the emitted LP1-conj hit.
#  a_bucket is the 1-based bucket index of the triggering a-value (same
#  bucketing as split_hist); pass 0 if not available to skip hotness tracking.
# ---------------------------------------------------------------------------
@inline function record_lp1_conj_hit!(stat::PhiBiasStat, raw_step::Int,
                                       lp_key::UInt128 = zero(UInt128),
                                       a_bucket::Int   = 0)
    if length(stat.lp1_conj_arrivals) < MAX_LP1_CONJ_ARRIVALS
        push!(stat.lp1_conj_arrivals, raw_step)
        push!(stat.lp1_conj_keys,     lp_key)
        push!(stat.lp1_conj_bucket_log, a_bucket > 0 ? a_bucket : 1)
    end
    if 1 <= a_bucket <= length(stat.lp1_conj_a_hist)
        stat.lp1_conj_a_hist[a_bucket] += 1
    end
    stat._prev_anchor_was_lp = true
    return nothing
end

# ---------------------------------------------------------------------------
#  record_random_anchor! — called when cur_pt is set to a random FB element
#  (i.e. NOT from an LP event).  Clears the post-LP flag.
# ---------------------------------------------------------------------------
@inline function record_random_anchor!(stat::PhiBiasStat)
    stat._prev_anchor_was_lp = false
    return nothing
end

# ---------------------------------------------------------------------------
#  Internal hash utilities
# ---------------------------------------------------------------------------
@inline function _rotl64(x::UInt64, r::Int)::UInt64
    rr = r & 63
    return (x << rr) | (x >> ((64 - rr) & 63))
end

@inline function _mix_u64(x::UInt64)::UInt64
    # SplitMix64 finalizer.
    x ⊻= x >> 30
    x *= UInt64(0xbf58476d1ce4e5b9)
    x ⊻= x >> 27
    x *= UInt64(0x94d049bb133111eb)
    x ⊻= x >> 31
    return x
end

@inline function _mix_event_hash(prev::UInt64, bucket::Int, split::Bool,
                                 a::Int, c1::Int, c0::Int, step::Int)::UInt64
    h = prev ⊻ UInt64(0x9e3779b97f4a7c15)
    h ⊻= _mix_u64(UInt64(bucket) + (split ? UInt64(0x1111111111111111) : UInt64(0x2222222222222222)))
    h ⊻= _mix_u64(UInt64(abs(a)) + UInt64(0x9e3779b97f4a7c15))
    h ⊻= _mix_u64(UInt64(abs(c1)) ⊻ _rotl64(UInt64(abs(c0)), 17))
    h ⊻= _mix_u64(UInt64(step) * UInt64(0x5851f42d4c957f2d))
    return _mix_u64(h)
end

# ---------------------------------------------------------------------------
#  Post-hoc statistical helpers (used in print_phi_bias_report)
# ---------------------------------------------------------------------------

function _moment4(xs::AbstractVector{<:Real})
    n = length(xs)
    n == 0 && return (NaN, NaN, NaN, NaN)
    μ = sum(float(x) for x in xs) / n
    if n == 1
        return (μ, 0.0, 0.0, 0.0)
    end
    diffs = [float(x) - μ for x in xs]
    m2 = sum(d*d for d in diffs) / n
    if m2 < 1e-30
        return (μ, 0.0, 0.0, 0.0)
    end
    m3 = sum(d^3 for d in diffs) / n
    m4 = sum(d^4 for d in diffs) / n
    σ = sqrt(m2)
    skew = m3 / (σ^3)
    kurt = m4 / (σ^4) - 3.0
    return (μ, m2, skew, kurt)
end

function _kl_divergence_counts(p::Vector{Int}, q::Vector{Int}; pseudo::Float64 = 0.5)
    @assert length(p) == length(q)
    sp = sum(p) + pseudo * length(p)
    sq = sum(q) + pseudo * length(q)
    kl = 0.0
    for i in eachindex(p)
        pi = (p[i] + pseudo) / sp
        qi = (q[i] + pseudo) / sq
        kl += pi * log2(pi / max(1e-300, qi))
    end
    return kl
end

function _top_share(hist::Vector{Int}, frac::Float64)
    n = sum(hist)
    n == 0 && return 0.0
    k = max(1, ceil(Int, frac * length(hist)))
    vals = sort(hist, rev=true)
    return sum(vals[1:min(k, length(vals))]) / n
end
