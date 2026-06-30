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
#  AMS update: the 128-bit key is first mixed down to a single GF(p61) field
#  element x = _ams_mix_to_field(k_lo, k_hi), then for each of the AMS_K hash
#  functions, σ_j(x) = sign(degree-3 polynomial h_j over GF(p61)) is computed
#  via _ams_sign(j, x) and added to ams_Z[j]. This degree-3 construction is
#  4-wise independent (see lp1_conj_lsm_constants.jl), which is what the AMS
#  per-group variance bound formally requires — the prior degree-1
#  multiply-shift sign function was only 2-universal (pairwise independent).
#  Using the FULL 128-bit key (compressed via a collision-resistant mixer,
#  not fp) is critical: hashing fp would cause distinct keys that collide
#  in fp-space to receive identical sign vectors, biasing F₂ upward and α₂
#  downward.  After N emissions, E[ams_Z[j]²] = F₂ = Σcᵢ², S₂ = N²/F₂.
#
#  Partial key log: stores a COLD_BITS-bit hash of the full 128-bit key (not
#  fp >> COLD_SHIFT) for the windowed α₂ diagnostic.
#
#  Cold-filter bitmap update: set the COLD_BITS-bit bucket presence bit using
#  fp (correct: this is a flush-path presence test, not an entropy estimate).
# ---------------------------------------------------------------------------
@inline function _lsm_record_sample!(sc::LP1ConjLSM, fp::UInt64, now_t::Float64, key::CanonicalLP1Key)
    # Split the full 128-bit key into two 64-bit halves for use in the AMS
    # sketch and the partial-key log.  We must NOT use fp (a lossy 64-bit
    # projection) for either: distinct keys that collide in fp-space would
    # receive identical sign vectors, biasing F₂ upward and α₂ downward.
    k_lo = UInt64(key & 0xffffffffffffffff)
    k_hi = UInt64(key >> 64)

    # Cold-filter bitmap — lockless bit-set (bits only ever set, never cleared).
    # fp is still correct here: the cold filter is a coarse presence test used
    # only by the flush path, not for any entropy estimate.
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

        # AMS sketch update: 512 sign-hash projections over the FULL 128-bit key.
        #
        # x = _ams_mix_to_field(k_lo, k_hi)   — collision-resistant compression
        # σ_j(x) = _ams_sign(j, x)            — 4-wise independent (degree-3
        #                                        polynomial over GF(p61))
        #
        # Mixing both halves of the key into a single field element before
        # hashing ensures the sign function separates every pair of distinct
        # keys in expectation, giving an unbiased estimate of F₂ = Σᵢ fᵢ² over
        # the true key distribution rather than the fp-fingerprint distribution.
        Z = sc.ams_Z
        x = _ams_mix_to_field(k_lo, k_hi)
        @inbounds for j in 1:AMS_K
            Z[j] += _ams_sign(j, x)
        end

        # Occupancy: increment for newly-observed coarse buckets.
        was_zero && (sc.occ_unique += 1)

        # Partial key log for windowed α₂ diagnostics.
        #
        # Store a COLD_BITS-bit hash of the FULL key (not fp >> COLD_SHIFT).
        # fp >> COLD_SHIFT is the top 20 bits of a 64-bit projection of the
        # 128-bit key, which discards information and biases the windowed α₂
        # estimate for the same reason as the AMS bug above.
        #
        # We derive a 20-bit bucket index by mixing both halves of the key with
        # a fixed constant (distinct from the AMS salts), then taking the top
        # COLD_BITS bits.  The constant 0xc4ceb9fe1a85ec53 is the finaliser
        # from MurmurHash3_x64_128; using a fixed value (not rand()) ensures
        # the bucket index is reproducible across diagnostic calls on the same
        # run, which matters for the windowed scaling analysis.
        log_n = length(sc.partial_fp_log)
        h_key = k_lo * 0xc4ceb9fe1a85ec53 + k_hi * 0x94d049bb133111eb
        h_key = h_key ⊻ (h_key >> 32)
        bucket_idx = UInt32(h_key >> (64 - COLD_BITS))   # top COLD_BITS bits
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

# ---------------------------------------------------------------------------
#  _ams_estimate_S2_stats_ngroups — D31 helper.
#
#  Same median-of-means procedure as _ams_estimate_S2_stats, but restricted
#  to the first n_groups of AMS_GROUPS (i.e. the first n_groups*AMS_WIDTH
#  accumulators of Z). This reuses the SAME sketch data — no new hashing,
#  no new accumulators — just asks "what would S2/alpha2 have looked like
#  if we'd only budgeted n_groups groups instead of AMS_GROUPS?".
#
#  Rationale (D31): the full AMS_GROUPS=32 estimate already reports a 68%
#  band from inter-group spread, but that band only reflects variance
#  AROUND the 32-group median — it says nothing about whether 32 groups is
#  enough groups in the first place. If alpha2 computed from a 4- or 8-group
#  prefix already agrees with the 32-group answer, the estimator has
#  converged and alpha2's value is a property of the data, not the sketch
#  resolution. If alpha2 keeps shifting as n_groups grows, the 32-group
#  estimate hasn't converged either, and the reported alpha2 ~ 0.59-0.60
#  pinning could still be (partly) a sketch-width artifact rather than a
#  genuine property of the walk.
#
#  p must be the same field characteristic used elsewhere in this file
#  (closes over the global `p`, exactly like _ams_estimate_S2_stats).
#  Requires n_groups <= AMS_GROUPS and n_groups >= 1.
#
#  Wired into lsm_bday_report below: prints alpha2 at n_groups = 4, 8, 16, 32
#  (doubling prefixes of the aggregated ams_Z_global) and flags whether the
#  last doubling step still moves alpha2 by more than ~0.01-0.03.
# ---------------------------------------------------------------------------
# ---------------------------------------------------------------------------
#  _ams_estimate_S2_stats_ngroups — single source of truth for the AMS
#  median-of-means F₂/S₂/α₂ estimator, restricted to the first n_groups of
#  the sketch (n_groups == AMS_GROUPS reproduces the full-budget estimate;
#  this is also the D31 helper, reusing the SAME Z data with no new hashing).
#
#  Bias note (Jensen correction):
#    α₂ = log(S₂) / (2 log p) is a *nonlinear* (concave-log) transform of
#    S₂ = N²/F₂, and F₂_hat (median-of-means) is unbiased for F₂ in
#    expectation but its log is not unbiased for log(F₂) — by Jensen's
#    inequality, E[log F̂₂] ≤ log E[F̂₂], so the naive α₂ above is biased
#    LOW (S₂ biased high, since S₂ = N²/F₂ inverts the direction) by an
#    amount that shrinks as the group-mean sample variance shrinks.
#
#    First-order (delta-method) correction, using f(x) = log(x):
#      E[log F̂₂] ≈ log(E[F̂₂]) - Var(F̂₂) / (2 E[F̂₂]²)
#    so the bias-corrected estimate of log(F₂) is
#      log(F₂)_corrected ≈ log(F̂₂) + Var(F̂₂) / (2 F̂₂²)
#    where Var(F̂₂) is estimated here as the sample variance of the
#    per-group means (group_means), divided by n_groups (variance of the
#    mean-of-groups statistic) — NOT the variance of the raw group means
#    themselves, and NOT a substitute for the median's own variance, which
#    has no closed form. This correction targets the MEAN-of-groups
#    estimator; since the median and mean coincide asymptotically and
#    track each other closely in practice for n_groups ~ 32, we apply the
#    same correction to the (more robust) median-based F2 point estimate.
#    This is an approximation, not an exact correction for the median —
#    flagged via `alpha2_bias_est` below so it can be audited rather than
#    silently trusted.
#
#  This bias is DISTINCT from the inter-group spread (alpha2_lo/hi band):
#    - the spread band reflects VARIANCE (how much the estimate would move
#      under a fresh batch of independent groups)
#    - the Jensen term reflects BIAS (a systematic offset from log/ratio
#      nonlinearity that does not average away with more groups at fixed
#      n_groups, only shrinks as n_groups/AMS_WIDTH grows)
#    Both should be inspected; neither one alone tells the full story.
# ---------------------------------------------------------------------------
function _ams_estimate_S2_stats_ngroups(Z::Vector{Int64}, N::Int64, n_groups::Int)
    n_groups = clamp(n_groups, 1, AMS_GROUPS)
    N == 0 && return (
        F2=0.0, S2=0.0,
        F2_lo=0.0, F2_hi=0.0,
        S2_lo=0.0, S2_hi=0.0,
        alpha2=0.0, alpha2_lo=0.0, alpha2_hi=0.0,
        alpha2_bias_est=0.0, alpha2_corrected=0.0
    )

    group_means = Vector{Float64}(undef, n_groups)
    @inbounds for g in 1:n_groups
        base = (g - 1) * AMS_WIDTH
        m = 0.0
        for j in 1:AMS_WIDTH
            m += Float64(Z[base + j])^2
        end
        group_means[g] = m / AMS_WIDTH
    end
    sort!(group_means)

    F2 = if iseven(n_groups)
        (group_means[n_groups ÷ 2] + group_means[n_groups ÷ 2 + 1]) / 2.0
    else
        group_means[(n_groups + 1) ÷ 2]
    end
    F2 = max(F2, 1.0)

    F2_lo = max(1.0, _ams_group_quantile(group_means, 0.15865525393145707))
    F2_hi = max(F2_lo, _ams_group_quantile(group_means, 0.8413447460685429))

    S2    = Float64(N)^2 / F2
    S2_lo = Float64(N)^2 / F2_hi
    S2_hi = Float64(N)^2 / F2_lo

    logp = log(Float64(p))
    alpha2    = log(S2)    / (2.0 * logp)
    alpha2_lo = log(S2_lo) / (2.0 * logp)
    alpha2_hi = log(S2_hi) / (2.0 * logp)

    # Jensen bias correction (delta method, applied to mean-of-groups
    # estimator as an approximation for the median; see docstring above).
    # Sample variance of the group means (ddof=1), then divide by n_groups
    # to get Var of the mean-of-groups statistic.
    alpha2_bias_est = 0.0
    if n_groups >= 2
        gm_mean = sum(group_means) / n_groups
        ss = 0.0
        @inbounds for g in 1:n_groups
            d = group_means[g] - gm_mean
            ss += d * d
        end
        var_gm_of_mean = (ss / (n_groups - 1)) / n_groups
        # bias in log(F2_hat) ≈ -Var(F2_hat) / (2 F2_hat^2)  (Jensen, downward)
        # bias in log(S2_hat) = -bias in log(F2_hat) since S2 = N^2/F2
        log_F2_bias = var_gm_of_mean / (2.0 * F2 * F2)
        # propagate into alpha2 = log(S2)/(2 log p); S2 bias has opposite
        # sign to F2 bias since S2 = N^2/F2.
        alpha2_bias_est = log_F2_bias / (2.0 * logp)
    end
    alpha2_corrected = alpha2 + alpha2_bias_est

    return (
        F2=F2, S2=S2,
        F2_lo=F2_lo, F2_hi=F2_hi,
        S2_lo=S2_lo, S2_hi=S2_hi,
        alpha2=alpha2, alpha2_lo=alpha2_lo, alpha2_hi=alpha2_hi,
        alpha2_bias_est=alpha2_bias_est, alpha2_corrected=alpha2_corrected
    )
end

# ---------------------------------------------------------------------------
#  _ams_estimate_S2_stats — full-budget (AMS_GROUPS) wrapper. Kept as a
#  separate name (rather than inlining call sites to *_ngroups directly)
#  since it's part of the public-ish API of this file and several call
#  sites depend on the name.
# ---------------------------------------------------------------------------
function _ams_estimate_S2_stats(Z::Vector{Int64}, N::Int64)
    return _ams_estimate_S2_stats_ngroups(Z, N, AMS_GROUPS)
end

function _ams_estimate_S2(Z::Vector{Int64}, N::Int64)::Tuple{Float64, Float64}
    stats = _ams_estimate_S2_stats(Z, N)
    return (stats.F2, stats.S2)
end

# ---------------------------------------------------------------------------
#  lsm_bday_report — birthday / Rényi diagnostics report (global across peers)
# ---------------------------------------------------------------------------
function lsm_bday_report(sc::LP1ConjLSM, p::Integer, r::Real; io::IO = stdout)
    # ── Aggregate across all peer LSMs ─────────────────────────────────────
    # Each thread has its own LP1ConjLSM instance linked via `peers`.
    # We must aggregate across all peers to see the true global first collision.
    actual_peers = isempty(sc.peers) ? Any[sc] : sc.peers

    total_emitted = 0
    m_first       = 0
    t_coll_first  = Inf
    t0_earliest   = Inf
    occ_n_global  = 0
    ams_Z_global  = zeros(Int64, AMS_K)   # aggregate AMS sketch across all peers

    for peer in actual_peers
        # Dynamic dispatch is fine here (diagnostic path)
        lock(peer.bday_lock)
        total_emitted += peer.bday_emissions
        occ_n_global  += peer.occ_n
        
        if peer.bday_first_coll_m > 0
            if peer.bday_first_coll_t < t_coll_first
                t_coll_first = peer.bday_first_coll_t
                # m_first is the LOCAL emission count on the peer that saw the
                # collision.  Multiplying by npeers was a bad approximation that
                # assumes perfectly equal per-thread emission rates.  Instead we
                # use total_emitted (accumulated after unlocking all peers below),
                # which requires a second pass; for now store the local value and
                # fix it up after the loop.
                m_first = peer.bday_first_coll_m
            end
        end
        
        if peer.bday_t0 > 0.0 && peer.bday_t0 < t0_earliest
            t0_earliest = peer.bday_t0
        end

        # Aggregate AMS sketch: Z_global[j] = Σ_peers Z_peer[j].
        # Linearity of expectation: E[(Z_global[j])²] ≠ Σ E[(Z_peer[j])²] in general,
        # but since each peer sees an independent sub-stream with the same distribution,
        # and the sign functions are deterministic, summing the Z vectors gives
        # Z_global[j] = Σ_k c_k · h_j(k) over all emissions across all peers,
        # which is exactly what we want.
        for i in 1:AMS_K
            ams_Z_global[i] += peer.ams_Z[i]
        end
        unlock(peer.bday_lock)
    end

    # Occupancy from cold_bitmap: count set bits across all peers' cold bitmaps.
    # Union of peer bitmaps gives the global set of observed coarse buckets.
    cold_union = zeros(UInt64, COLD_WORDS)
    for peer in actual_peers
        for i in 1:COLD_WORDS
            cold_union[i] |= peer.cold_bitmap[i]
        end
    end
    occ_u_global = sum(count_ones(w) for w in cold_union)  # distinct cold-buckets seen

    # Calculate true global emission rate from actual elapsed time
    t_elapsed = t0_earliest < Inf ? (time_ns() * 1e-9) - t0_earliest : 0.0
    lam_global = t_elapsed > 0.0 ? (total_emitted / t_elapsed) : (r * length(actual_peers))
    pf = Float64(p)

    # Fix up m_first: convert from local-peer count to global count.
    # We know the wall-clock time of the collision (t_coll_first) and the
    # overall emission rate (lam_global).  The best estimate of how many
    # emissions had occurred globally at collision time is:
    #   m_first_global ≈ lam_global * (t_coll_first - t0_earliest)
    # This is unbiased regardless of per-thread rate variation, unlike the
    # old "local_m * npeers" approximation.
    if m_first > 0 && t_coll_first < Inf && t0_earliest < Inf && lam_global > 0.0
        t_at_coll = t_coll_first - t0_earliest
        m_first   = max(m_first, round(Int, lam_global * t_at_coll))
    end

    @printf(io, "\n[LP1-conj birthday diagnostics (Global across %d peers)]\n", length(actual_peers))
    @printf(io, "  total LP1-conj emitted : %d\n", total_emitted)

    if m_first == 0
        @printf(io, "  first collision        : not yet observed\n")
        t_naive = lam_global > 0.0 ? (sqrt(2.0) * pf / lam_global) : Inf
        m_naive = lam_global * t_naive
        @printf(io, "  naive prediction       : m_first ~ %.3g,  t_first ~ %.3g s\n", m_naive, t_naive)
        if t0_earliest < Inf
            frac = t_elapsed / t_naive
            @printf(io, "  elapsed / t_naive      : %.4f  (%s)\n",
                    frac, frac >= 1.0 ? "OVERDUE — support may be smaller than p^2" : "still within naive expectation")
        end
        @printf(io, "\n")
        return
    end

    t_first   = t_coll_first - t0_earliest
    # Birthday paradox: expected first collision at m steps over a space of size
    # S gives m ≈ sqrt(2S), so S_eff = m²/2.  The old code used m² (off by 2).
    S_eff     = Float64(m_first)^2 / 2.0
    S_naive   = pf^2 / 2.0
    ratio     = S_eff / S_naive
    alpha     = log(Float64(m_first) / sqrt(2.0)) / log(pf)
    m_naive   = sqrt(S_naive)
    t_naive   = lam_global > 0.0 ? (m_naive / lam_global) : Inf

    @printf(io, "  first collision at     : m ≈ %d  (t_wall = %.3f s)\n", m_first, t_first)
    @printf(io, "  S_eff  = m^2/2         : %.6g\n", S_eff)
    @printf(io, "  S_naive = p^2/2        : %.6g\n", S_naive)
    @printf(io, "  S_eff / S_naive        : %.5g\n", ratio)
    @printf(io, "  alpha  (S ~ p^{2*alpha}): %.4f   [alpha=1 ↔ S~p^2, alpha=0.75 ↔ S~p^1.5, ...]\n", alpha)
    @printf(io, "  t_first (observed)     : %.3f s\n", t_first)
    @printf(io, "  t_first (naive p^2/2)  : %.3f s   (= sqrt(2)*p/lam_global)\n", t_naive)
    @printf(io, "  t_obs / t_naive        : %.4f\n", t_first / t_naive)
    
    if ratio < 0.1
        @printf(io, "  *** support is << p^2: effective space ~ p^{%.2f} ***\n", 2*alpha)
    elseif ratio < 0.5
        @printf(io, "  support is moderately smaller than p^2\n")
    else
        @printf(io, "  support is consistent with naive p^2 model\n")
    end

    # ── Occupancy estimator: U(N) = S(1 - e^{-N/S}), solve for S ─────────────
    @printf(io, "\n  Occupancy estimator (U(N) = S·(1−e^{−N/S})):\n")
    if occ_n_global >= 10 && occ_u_global >= 1 && occ_u_global < occ_n_global
        scale   = Float64(1 << COLD_BITS)
        U_f     = Float64(occ_u_global) * scale
        N_f     = Float64(occ_n_global)
        lo_s = max(U_f, 1.0)
        hi_s = max(N_f^2, U_f * 10.0)
        for _ in 1:80
            mid = (lo_s + hi_s) / 2.0
            val = mid * (1.0 - exp(-N_f / mid)) - U_f
            val < 0.0 ? (lo_s = mid) : (hi_s = mid)
        end
        S_occ   = (lo_s + hi_s) / 2.0
        r_occ   = S_occ / S_naive
        a_occ   = log(S_occ) / (2.0 * log(pf))
        @printf(io, "    unique cold-buckets U  : %d  (N=%d, scale=2^%d)\n",
                occ_u_global, occ_n_global, COLD_BITS)
        @printf(io, "    S_occ (MLE)            : %.6g\n", S_occ)
        @printf(io, "    S_occ / S_naive        : %.5g\n", r_occ)
        @printf(io, "    alpha_occ (S ~ p^{2α}) : %.4f\n", a_occ)
    else
        @printf(io, "    (need ≥10 emissions with some bucket collisions)\n")
    end

    # ── Rényi-2 / collision-entropy estimator — AMS sketch ───────────────────
    @printf(io, "\n  Rényi-2 / collision-entropy estimator (AMS sketch, %d×%d):\n",
            AMS_GROUPS, AMS_WIDTH)
    N_global = Int64(total_emitted)
    if N_global >= 2
        ams_stats = _ams_estimate_S2_stats(ams_Z_global, N_global)
        r2  = ams_stats.S2 / S_naive
        burst_flag = if S_eff > 0.0 && ams_stats.S2 > 0.0
            ratio_be = S_eff / ams_stats.S2
            ratio_be > 4.0 ? @sprintf(" ← BURSTS DOMINATE (birthday %.1f× > entropy)", ratio_be) :
            ratio_be < 0.25 ? " ← ENTROPY > BIRTHDAY (unusual)" :
                              " (birthday ≈ entropy, consistent)"
        else
            ""
        end
        a2_pm = 0.5 * (ams_stats.alpha2_hi - ams_stats.alpha2_lo)
        s2_pm = 0.5 * (ams_stats.S2_hi - ams_stats.S2_lo)
        @printf(io, "    N (total emissions)    : %d\n", N_global)
        @printf(io, "    F₂ estimate (AMS)      : %.6g  [68%% band %.6g .. %.6g]\n",
                ams_stats.F2, ams_stats.F2_lo, ams_stats.F2_hi)
        @printf(io, "    S₂ = N²/F₂            : %.6g ± %.6g  [68%% band %.6g .. %.6g]\n",
                ams_stats.S2, s2_pm, ams_stats.S2_lo, ams_stats.S2_hi)
        @printf(io, "    S₂ / S_naive           : %.5g\n", r2)
        @printf(io, "    α₂  (S₂ ~ p^{2α₂})    : %.4f ± %.4f  [68%% band %.4f .. %.4f]%s\n",
                ams_stats.alpha2, a2_pm, ams_stats.alpha2_lo, ams_stats.alpha2_hi, burst_flag)
        @printf(io, "    [band is the inter-group spread (VARIANCE); not a formal CI]\n")
        @printf(io, "    [AMS never saturates; valid for any N]\n")
        @printf(io, "    α₂ Jensen-bias estimate: %+.5f  → bias-corrected α₂ ≈ %.4f\n",
                ams_stats.alpha2_bias_est, ams_stats.alpha2_corrected)
        @printf(io, "    [bias is a SEPARATE effect from the spread band above — see\n")
        @printf(io, "     _ams_estimate_S2_stats_ngroups docstring. Correction is a\n")
        @printf(io, "     delta-method approximation (exact for mean-of-groups, applied\n")
        @printf(io, "     here to the median-of-groups estimator); treat as directional,\n")
        @printf(io, "     not exact, especially if |bias_est| approaches a_pm in size.]\n")

        # ── D31: group-budget convergence check ─────────────────────────────
        # Re-derives alpha2 from doubling PREFIXES of the same sketch (4, 8, 16,
        # ... groups) using _ams_estimate_S2_stats_ngroups. No new hashing — just
        # asks whether alpha2 had already settled before the full AMS_GROUPS
        # budget was spent, or whether it's still moving group-by-group (in
        # which case the AMS_GROUPS=32 estimate may itself be under-resolved).
        @printf(io, "\n    [D31] α₂ vs. group budget (prefix of same sketch, no new data):\n")
        @printf(io, "      n_groups   F₂          S₂          α₂       Δα₂(doubling)  bias_est   α₂_corr\n")
        prev_ng_a2  = NaN
        ng          = 4
        ng_a2_vals  = Float64[]
        while ng <= AMS_GROUPS
            ngs = _ams_estimate_S2_stats_ngroups(ams_Z_global, N_global, ng)
            dstr = isnan(prev_ng_a2) ? "        —" : @sprintf("%+9.4f", ngs.alpha2 - prev_ng_a2)
            @printf(io, "      %8d   %.6g   %.6g   %7.4f  %s%s  %+8.5f   %7.4f\n",
                    ng, ngs.F2, ngs.S2, ngs.alpha2, dstr,
                    ng == AMS_GROUPS ? "  (= full budget, above)" : "",
                    ngs.alpha2_bias_est, ngs.alpha2_corrected)
            push!(ng_a2_vals, ngs.alpha2)
            prev_ng_a2 = ngs.alpha2
            ng *= 2
        end
        @printf(io, "      [bias_est should shrink faster than the raw α₂ spread as\n")
        @printf(io, "       n_groups grows (bias ~1/(groups·width), variance ~1/groups);\n")
        @printf(io, "       if α₂_corr is markedly flatter across doublings than the raw\n")
        @printf(io, "       α₂ column, that's evidence some of the apparent drift above\n")
        @printf(io, "       was Jensen bias decaying, not the walk distribution resolving.]\n")
        # ── Verdict: look at the SHAPE of the delta sequence, not just the
        #    last step. A single small last-step can hide a flat-then-jump
        #    pattern (e.g. 8→16 flat, 16→32 jumps) that's evidence of noise
        #    re-entering as fresh groups join the pool, not of convergence.
        #    Genuine asymptotic convergence should show |Δ| roughly
        #    non-increasing across doublings, not just "small at the end".
        if length(ng_a2_vals) >= 2
            deltas = [ng_a2_vals[i+1] - ng_a2_vals[i] for i in 1:length(ng_a2_vals)-1]
            abs_deltas = abs.(deltas)
            last_step  = abs_deltas[end]
            max_step   = maximum(abs_deltas)
            # "Monotone decay" = each |delta| no more than ~1.5x the previous
            # one (allows minor noise without calling a 6x rebound "decaying").
            is_decaying = length(abs_deltas) < 2 ||
                          all(abs_deltas[i+1] <= 1.5 * max(abs_deltas[i], 1e-6)
                              for i in 1:length(abs_deltas)-1)
            @printf(io, "      Δ sequence: %s   (max |Δ|=%.4f, last |Δ|=%.4f)\n",
                    join([@sprintf("%+.4f", d) for d in deltas], "  "), max_step, last_step)
            if last_step < 0.01 && is_decaying
                @printf(io, "      → CONVERGED before full budget: α₂ is a property of the data,\n")
                @printf(io, "        not the %d-group sketch resolution.\n", AMS_GROUPS)
            elseif last_step < 0.03 && is_decaying
                @printf(io, "      → nearly converged (Δ=%.4f on last doubling); weak resolution dependence.\n",
                        last_step)
            elseif !is_decaying
                @printf(io, "      → NON-MONOTONIC: Δ shrinks then rebounds (max |Δ|=%.4f vs last |Δ|=%.4f).\n",
                        max_step, last_step)
                @printf(io, "        This looks like inter-group sampling noise re-entering as new groups\n")
                @printf(io, "        join the median pool, not a stable trend either way. The full-budget\n")
                @printf(io, "        ±%.4f spread band above is a better-justified uncertainty estimate\n",
                        a2_pm)
                @printf(io, "        than this %d-point delta sequence — too few doublings to fit a trend.\n",
                        length(ng_a2_vals))
            else
                @printf(io, "      → STILL MOVING at full budget (Δ=%.4f on last doubling): the\n", last_step)
                @printf(io, "        α₂ ≈ %.2f estimate above may be (partly) a sketch-width artifact —\n",
                        ams_stats.alpha2)
                @printf(io, "        consider raising AMS_GROUPS before trusting the pinning.\n")
            end
        end
    else
        @printf(io, "    (no emissions recorded yet)\n")
    end

    @printf(io, "\n")

    # ── α₂ scaling diagnostics on the partial key stream ─────────────────────
    # (Thread-local view; cross-thread merge of ring buffers is non-trivial.)
    # The windowed estimator computes α₂ over windows of Tw emissions using
    # the 2^COLD_BITS coarse bucket index stored in partial_fp_log.
    # It is unbiased when Tw << 2^COLD_BITS (average < 1 hit/bucket per window),
    # and saturates when Tw >> 2^COLD_BITS.  We annotate saturated rows.
    let blog = copy(sc.partial_fp_log)
        nb       = 1 << COLD_BITS    # number of coarse buckets
        n_blog   = length(blog)
        sat_warn = nb ÷ 4            # warn when Tw > nb/4

        @printf(io, "  LP1-conj partial stream α₂ scaling (Thread Local view, 2^%d buckets):\n",
                COLD_BITS)
        if n_blog < 64
            @printf(io, "    (need ≥64 partials; got %d)\n\n", n_blog)
        else
            @printf(io, "    nb=%d fp-buckets  N=%d partials\n", nb, n_blog)
            @printf(io, "    window_T    n_events   α₂(T)    S_occ(T)   ρ=S_occ/S₂  dα₂/dlogT  note\n")

            T0   = max(32, n_blog ÷ 64)
            Tw   = T0
            prev_a2 = NaN; prev_logT = NaN
            a2_vals = Float64[]; logT_vals = Float64[]

            while Tw <= n_blog
                n_wins = n_blog ÷ Tw
                n_wins < 1 && break
                s2_acc = 0.0; socc_acc = 0.0; n_valid = 0
                counts_T = zeros(Int, nb)
                for wi in 0:(n_wins - 1)
                    fill!(counts_T, 0)
                    for k in (wi*Tw + 1):((wi+1)*Tw)
                        counts_T[Int(blog[k]) + 1] += 1
                    end
                    n_T = sum(counts_T)
                    n_T == 0 && continue
                    p2sum = sum((counts_T[i] / n_T)^2 for i in 1:nb)
                    s2_T  = p2sum > 0.0 ? -log2(p2sum) : NaN
                    n_occ = count(>(0), counts_T)
                    socc_T = n_occ > 0 ? log2(Float64(n_occ)) : 0.0
                    if !isnan(s2_T)
                        s2_acc += s2_T; socc_acc += socc_T; n_valid += 1
                    end
                end
                n_valid == 0 && (Tw *= 2; continue)

                a2_T    = s2_acc   / n_valid
                socc_T  = socc_acc / n_valid
                rho_T   = a2_T > 0.0 ? socc_T / a2_T : NaN
                logT    = log2(Float64(Tw))
                da2     = (!isnan(prev_a2) && !isnan(prev_logT) && logT > prev_logT) ?
                          (a2_T - prev_a2) / (logT - prev_logT) : NaN
                da_str  = isnan(da2)  ? "        —" : @sprintf("%+9.4f", da2)
                rho_str = isnan(rho_T) ? "         —" : @sprintf("%10.4f", rho_T)
                note    = Tw > sat_warn ? " [SAT?]" : ""
                @printf(io, "    %9d  %9d  %8.4f  %9.4f  %s  %s%s\n",
                        Tw, n_wins * Tw, a2_T, socc_T, rho_str, da_str, note)
                push!(a2_vals, a2_T); push!(logT_vals, logT)
                prev_a2 = a2_T; prev_logT = logT
                Tw *= 2
            end

            # Only use un-saturated rows for the verdict.
            unsaturated_a2 = [a2_vals[i] for i in eachindex(a2_vals)
                              if exp2(logT_vals[i]) <= sat_warn]

            if length(a2_vals) >= 3
                da2_late  = (a2_vals[end]   - a2_vals[end-1]) / (logT_vals[end]   - logT_vals[end-1])
                da2_early = (a2_vals[2]     - a2_vals[1])     / (logT_vals[2]     - logT_vals[1])
                verdict = if abs(da2_late) < 0.02
                    "  → α₂ CONVERGED — single exponent (Case A)"
                elseif da2_early > 0.05 && abs(da2_late) < 0.05
                    "  → α₂ CROSSOVER — two plateaus (Case B: burst then mixing)"
                elseif da2_late > 0.05
                    "  → α₂ DRIFTING UPWARD — no fixed exponent (Case C)"
                else
                    "  → α₂ trend inconclusive"
                end
                @printf(io, "    %s\n", verdict)
            end

            # Report the converged windowed α₂.
            # Prefer unsaturated rows (Tw ≤ nb/4); fall back to all rows if none.
            ref_vals = isempty(unsaturated_a2) ? a2_vals : unsaturated_a2
            if !isempty(ref_vals) && pf > 1.0
                a2_w = ref_vals[end]
                sat_note = isempty(unsaturated_a2) ? " [all rows saturated — lower bound only]" : ""
                @printf(io, "    converged α₂ (bucket-entropy bits) : %.4f%s\n", a2_w, sat_note)
                @printf(io, "    [This is H₂ in bits over 2^%d buckets, NOT directly comparable\n", COLD_BITS)
                @printf(io, "     to AMS α₂ above.  Use AMS α₂ for the calibrated exponent.]\n")
                @printf(io, "    [Windowed diagnostic value: does α₂(T) converge as T grows?\n")
                @printf(io, "     Flat → single-exponent walk.  Rising → mixing across scales.]\n")
            end
        end
    end

    @printf(io, "\n  Cold-filter (bucket zero-count drop at flush) [Local Thread]:\n")
    n_dropped = sc.n_cold_dropped
    n_spilled = sc.n_disk_live + n_dropped
    if n_spilled > 0
        frac_dropped = n_dropped / Float64(n_spilled)
        @printf(io, "    entries cold-dropped   : %d  (%.1f%% of flush candidates)\n",
                n_dropped, 100.0 * frac_dropped)
        @printf(io, "    entries spilled to SSD : %d\n", sc.n_disk_live)
    else
        @printf(io, "    (no flushes yet, or warmup not reached)\n")
    end
    @printf(io, "\n")
    nothing
end
