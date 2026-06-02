# =============================================================================
#  lp1_conj_lsm_renyi.jl — Rényi-2 / collision-entropy estimators
#
#  Covers:
#    • _lsm_record_sample!  — update AMS sketch, cold bitmap, partial_fp_log,
#                              TopK, and bday counters for one genuine emission
#    • _bday_record_collision! — record the first cross-col collision time
#    • _ams_estimate_S2_stats  — median-of-means F₂/S₂/α₂ from AMS Z vector
#    • _ams_estimate_S2        — thin wrapper returning (F2, S2)
#    • _ams_group_quantile     — interpolating quantile on sorted Float64 vector
# =============================================================================

# ---------------------------------------------------------------------------
#  _lsm_record_sample! — update all estimators for one genuine emission.
#
#  Called only for true misses (insert) and true cross-col hits.
#  Same-col re-inserts are invisible so α₂ reflects the actual walk
#  distribution rather than artifact duplicates.
#
#  AMS update: for each of the AMS_K hash functions h_j, compute the sign
#  h_j(fp) = (-1)^{high bit of fp*salt_j} and add it to ams_Z[j].
#  After N emissions, E[ams_Z[j]^2] = F₂ = Σcᵢ², and S₂ = N²/F₂.
#
#  Cold-filter bitmap update: set the COLD_BITS-bit bucket presence bit
#  (used by the flush path, not for S₂).
# ---------------------------------------------------------------------------
@inline function _lsm_record_sample!(sc::LP1ConjLSM, fp::UInt64, now_t::Float64, key::CanonicalLP1Key)
    # Cold-filter bitmap — lockless bit-set (bits only ever set, never cleared).
    cb_idx  = Int(fp >> COLD_SHIFT)
    cb_word = cb_idx >> 6
    cb_bit  = cb_idx & 63
    # Capture was_zero BEFORE setting the bit so occ_unique counts correctly.
    @inbounds was_zero = (sc.cold_bitmap[cb_word + 1] >> cb_bit) & UInt64(1) == UInt64(0)
    @inbounds sc.cold_bitmap[cb_word + 1] |= UInt64(1) << cb_bit

    lock(sc.bday_lock)
    try
        sc.bday_emissions == 0 && (sc.bday_t0 = now_t)
        sc.bday_emissions += 1
        sc.occ_n          += 1

        # AMS sketch update: 512 sign-hash projections.
        # h_j(fp) = +1 if high bit of (fp * salt_j) is 0, else -1.
        Z = sc.ams_Z
        @inbounds for j in 1:AMS_K
            h = fp * AMS_SALTS[j]
            Z[j] += ifelse((h >> 63) == UInt64(0), Int64(1), Int64(-1))
        end

        # Occupancy: increment for newly-observed coarse buckets.
        was_zero && (sc.occ_unique += 1)

        # Partial fp log: record the COLD_BITS-bit bucket index for windowed
        # α₂ diagnostics.  Uses UInt32 since COLD_BITS = 20 fits easily.
        log_n      = length(sc.partial_fp_log)
        bucket_idx = UInt32(cb_idx)
        if log_n < PARTIAL_FP_LOG_CAP
            push!(sc.partial_fp_log, bucket_idx)
        else
            circ_idx = ((sc.bday_emissions - 1) % PARTIAL_FP_LOG_CAP) + 1
            @inbounds sc.partial_fp_log[circ_idx] = bucket_idx
        end

        # Top-K multiplicity: record this key emission (under bday_lock).
        _topk_record!(sc.topk, key)
    finally
        unlock(sc.bday_lock)
    end
end

# ---------------------------------------------------------------------------
#  _bday_record_collision! — record first cross-col LP1-conj collision.
#
#  Called on every confirmed cross-col collision; only the first is stored.
#  bday_emissions >= 1 here because _lsm_record_sample! was called just before.
# ---------------------------------------------------------------------------
@inline function _bday_record_collision!(sc::LP1ConjLSM, now_t::Float64)
    lock(sc.bday_lock)
    try
        sc.bday_first_coll_m == 0 || return
        sc.bday_first_coll_m = sc.bday_emissions
        sc.bday_first_coll_t = now_t
    finally
        unlock(sc.bday_lock)
    end
    nothing
end

# ---------------------------------------------------------------------------
#  AMS estimator internals
# ---------------------------------------------------------------------------

@inline function _ams_group_quantile(sorted_vals::Vector{Float64}, q::Float64)::Float64
    n = length(sorted_vals)
    n == 0 && return NaN
    n == 1 && return sorted_vals[1]
    q_clamped = clamp(q, 0.0, 1.0)
    pos = 1.0 + q_clamped * Float64(n - 1)
    lo  = clamp(floor(Int, pos), 1, n)
    hi  = min(lo + 1, n)
    t   = pos - Float64(lo)
    return (1.0 - t) * sorted_vals[lo] + t * sorted_vals[hi]
end

function _ams_estimate_S2_stats(Z::Vector{Int64}, N::Int64)
    N == 0 && return (
        F2=0.0, S2=0.0,
        F2_lo=0.0, F2_hi=0.0,
        S2_lo=0.0, S2_hi=0.0,
        alpha2=0.0, alpha2_lo=0.0, alpha2_hi=0.0
    )

    group_means = Vector{Float64}(undef, AMS_GROUPS)
    @inbounds for g in 1:AMS_GROUPS
        base = (g - 1) * AMS_WIDTH
        m = 0.0
        for j in 1:AMS_WIDTH
            m += Float64(Z[base + j])^2
        end
        group_means[g] = m / AMS_WIDTH
    end
    sort!(group_means)

    # Median-of-means point estimate.
    F2 = if iseven(AMS_GROUPS)
        (group_means[AMS_GROUPS ÷ 2] + group_means[AMS_GROUPS ÷ 2 + 1]) / 2.0
    else
        group_means[(AMS_GROUPS + 1) ÷ 2]
    end
    F2 = max(F2, 1.0)

    # Robust spread band from the central 68% of group means.
    F2_lo = max(1.0, _ams_group_quantile(group_means, 0.15865525393145707))
    F2_hi = max(F2_lo, _ams_group_quantile(group_means, 0.8413447460685429))

    S2    = Float64(N)^2 / F2
    S2_lo = Float64(N)^2 / F2_hi
    S2_hi = Float64(N)^2 / F2_lo

    logp = log(Float64(p))
    alpha2    = log(S2)    / (2.0 * logp)
    alpha2_lo = log(S2_lo) / (2.0 * logp)
    alpha2_hi = log(S2_hi) / (2.0 * logp)

    return (
        F2=F2, S2=S2,
        F2_lo=F2_lo, F2_hi=F2_hi,
        S2_lo=S2_lo, S2_hi=S2_hi,
        alpha2=alpha2, alpha2_lo=alpha2_lo, alpha2_hi=alpha2_hi
    )
end

function _ams_estimate_S2(Z::Vector{Int64}, N::Int64)::Tuple{Float64, Float64}
    stats = _ams_estimate_S2_stats(Z, N)
    return (stats.F2, stats.S2)
end
