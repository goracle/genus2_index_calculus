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
                # Approximate global emissions at the exact time of the earliest local collision
                m_first = peer.bday_first_coll_m * length(actual_peers)
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
    S_eff     = Float64(m_first)^2
    S_naive   = pf^2 / 2.0
    ratio     = S_eff / S_naive
    alpha     = log(Float64(m_first)) / log(pf)
    m_naive   = sqrt(S_naive)
    t_naive   = lam_global > 0.0 ? (m_naive / lam_global) : Inf

    @printf(io, "  first collision at     : m ≈ %d  (t_wall = %.3f s)\n", m_first, t_first)
    @printf(io, "  S_eff  = m^2           : %.6g\n", S_eff)
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
        @printf(io, "    [band is the inter-group spread; not a formal CI]\n")
        @printf(io, "    [AMS never saturates; valid for any N]\n")
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

            # Report the converged windowed α₂ (prefer unsaturated rows).
            ref_vals = isempty(unsaturated_a2) ? a2_vals : unsaturated_a2
            if !isempty(ref_vals) && pf > 1.0
                a2_w = ref_vals[end]
                # Windowed α₂ is in bucket-entropy bits (log₂ scale).
                # Convert: S₂_bucket = 2^a2_w, S₂_keys = S₂_bucket × 2^COLD_BITS.
                S2_w_bucket = exp2(a2_w)
                S2_w_keys   = S2_w_bucket * Float64(1 << COLD_BITS)
                a2_w_keys   = log(S2_w_keys) / (2.0 * log(pf))
                sat_note    = isempty(unsaturated_a2) ? " [all rows saturated — treat as lower bound]" : ""
                @printf(io, "    converged α₂ (bucket-space)  : %.4f bits%s\n", a2_w, sat_note)
                @printf(io, "    S₂_keys (bucket × 2^%d)     : %.5g\n", COLD_BITS, S2_w_keys)
                @printf(io, "    α₂_keys (S₂ ~ p^{2α₂})      : %.4f  [compare AMS α₂ above]\n", a2_w_keys)
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
