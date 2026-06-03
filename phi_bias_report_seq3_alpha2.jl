# =============================================================================
#  phi_bias_report_seq3_alpha2.jl  --  Seq 3 and α₂-1 through α₂-12.
#
#  Seq 3: post-LP anchor KS test.
#  α₂-1 through α₂-12: Rényi-2 collision entropy scaling diagnostics
#  over the LP1-conj key stream.
#
#  Called from _report_seq3_alpha2!; not intended to be called directly.
# =============================================================================

# ---------------------------------------------------------------------------
#  _report_seq3_alpha2! — Seq 3 block + full α₂ scaling diagnostics.
#  stat     : PhiBiasStat
#  (no return value; writes to stdout)
# ---------------------------------------------------------------------------
function _report_seq3_alpha2!(stat::PhiBiasStat)
    # --- Seq 3: post-LP anchor bias (KS on a-histograms) ---
    @printf("  Seq 3 — Post-LP anchor a-histogram divergence:\n")
    n_post = sum(stat.post_lp_a_hist)
    n_base = sum(stat.baseline_a_hist)
    @printf("    post-LP steps    : %d\n", n_post)
    @printf("    baseline steps   : %d\n", n_base)
    if n_post >= 20 && n_base >= 20
        # KS statistic between the two normalised histograms.
        ks3 = 0.0
        cum_post = 0.0; cum_base = 0.0
        for i in eachindex(stat.post_lp_a_hist)
            cum_post += stat.post_lp_a_hist[i] / n_post
            cum_base += stat.baseline_a_hist[i] / n_base
            ks3 = max(ks3, abs(cum_post - cum_base))
        end
        flag3 = ks3 > 0.05 ? " ← DIVERGES (LP anchors bias a-dist)" :
                              " (consistent with uniform)"
        @printf("    KS(post vs base) : %.4f%s\n", ks3, flag3)
    else
        @printf("    (insufficient data for KS test)\n")
    end
    println()

    # ════════════════════════════════════════════════════════════════════════
    # α₂ SCALING DIAGNOSTICS  (α₂-1 through α₂-7)
    # ════════════════════════════════════════════════════════════════════════
    # All seven diagnostics run from lp1_conj_bucket_log (sorted by arrival time),
    # focusing exclusively on the LP1-conj key space.  The birthday block already
    # measures the same object via key collision statistics.
    #
    # Helper: compute Rényi-2 (collision) entropy and occupancy entropy from a
    # bucket count vector.  Returns (S2, S_occ, n_steps).
    #   S2    = -log2( Σ (cᵢ/n)² )   — collision entropy
    #   S_occ = -log2( #occupied / nb ) when uniform, or Shannon of occupancy
    #           We use the simpler effective-support: log2(#buckets_hit)
    # Both are in bits.  nb = number of buckets.
    function _bucket_entropies(counts::Vector{Int}, nb::Int)
        n = sum(counts)
        n == 0 && return (NaN, NaN, 0)
        p2sum = sum((counts[i] / n)^2 for i in 1:nb)
        S2    = p2sum > 0.0 ? -log2(p2sum) : NaN
        n_occ = count(>(0), counts)
        S_occ = n_occ > 0 ? log2(Float64(n_occ)) : 0.0
        return (S2, S_occ, n)
    end

    # ── α₂ sections: operate on the full LP1-conj partial key stream ────────────
    # blog = lp1_conj_key_blog: one UInt16 fp-bucket index per LP1-conj partial
    # (both stored and closed), populated by record_lp1_conj_partial! on every
    # call to handle_1lp_conj!.  nb = 2^±14 = 16384 fp-buckets, matching the
    # LSM’s Rényi granularity.  This is the quantity whose scaling exponent
    # α₂ governs the complexity of genus-2 IC via LP1-conj.
    blog   = stat.lp1_conj_key_blog   # Vector{UInt16}, 0-based bucket indices
    nb_a2  = 1 << _PHI_RENYI_BITS     # 16384 fp-buckets for α₂ diagnostics
    n_blog = length(blog)

    if n_blog < 32
        @printf("  α₂ scaling diagnostics (LP1-conj): need ≥32 LP1-conj emissions; got %d\n", n_blog)
    else

    # ── α₂-1: Time-resolved α₂(T) over dyadic windows ───────────────────────
    @printf("  α₂-1 — Time-resolved α₂(T) of LP1-conj a-bucket sequence:\n")
    @printf("    window_T   n_events   α₂(T)   S_occ(T)   ρ(T)=S_occ/S₂   dα₂/dlogT\n")
    # Build dyadic window sizes: T₀, 2T₀, 4T₀, … up to n_blog
    T0_a2 = max(16, n_blog ÷ 64)
    dyadic_windows = Int[]
    Tw = T0_a2
    while Tw <= n_blog
        push!(dyadic_windows, Tw)
        Tw *= 2
    end
    # For each window size, compute α₂(T) by sliding the window across the log
    # with stride = T (non-overlapping), averaging S₂ across windows.
    prev_a2  = NaN
    prev_logT = NaN
    da2_vals  = Float64[]
    a2_vals   = Float64[]
    logT_vals = Float64[]
    for T in dyadic_windows
        n_wins_a2 = n_blog ÷ T
        n_wins_a2 < 1 && continue
        s2_acc = 0.0; socc_acc = 0.0; n_valid = 0
        counts_T = zeros(Int, nb_a2)
        for wi in 0:(n_wins_a2 - 1)
            fill!(counts_T, 0)
            for k in (wi*T + 1):((wi+1)*T)
                counts_T[Int(blog[k]) + 1] += 1
            end
            (s2, socc, _) = _bucket_entropies(counts_T, nb_a2)
            if !isnan(s2)
                s2_acc += s2; socc_acc += socc; n_valid += 1
            end
        end
        n_valid == 0 && continue
        a2_T   = s2_acc   / n_valid
        socc_T = socc_acc / n_valid
        rho_T  = a2_T > 0.0 ? socc_T / a2_T : NaN
        logT   = log2(Float64(T))
        da2_dlogT = (!isnan(prev_a2) && !isnan(prev_logT) && logT > prev_logT) ?
                    (a2_T - prev_a2) / (logT - prev_logT) : NaN
        da_str  = isnan(da2_dlogT) ? "       —" : @sprintf("%+8.4f", da2_dlogT)
        rho_str = isnan(rho_T)     ? "        —" : @sprintf("%9.4f", rho_T)
        @printf("    %9d  %8d   %7.4f  %9.4f  %s  %s\n",
                T, n_wins_a2 * T, a2_T, socc_T, rho_str, da_str)
        push!(a2_vals, a2_T)
        push!(logT_vals, logT)
        push!(da2_vals, isnan(da2_dlogT) ? 0.0 : da2_dlogT)
        prev_a2 = a2_T; prev_logT = logT
    end
    # Classify the flow
    if length(da2_vals) >= 3
        da2_late = da2_vals[end]
        da2_early = da2_vals[2]
        a2_flag = if abs(da2_late) < 0.02
            "  → α₂ CONVERGED (single exponent, Case A)"
        elseif da2_early > 0.05 && abs(da2_late) < 0.05
            "  → α₂ CROSSOVER (two plateaus, Case B — burst then mixing)"
        elseif da2_late > 0.05
            "  → α₂ DRIFTING UPWARD (no fixed exponent, Case C)"
        else
            "  → α₂ trend inconclusive"
        end
        @printf("    %s\n", a2_flag)
    end
    println()

    # ── α₂-2: Intra vs inter-regime collision split ───────────────────────────
    @printf("  α₂-2 — Intra vs inter-regime collision split:\n")
    # Classify each LP1-conj emission as hot/cold by a sliding window over
    # lp1_conj_arrivals.  blog[i] is the a-bucket of the i-th emission in
    # chronological order; hot_mask[i] = true iff the surrounding arrival
    # density in the walk-step dimension exceeds the global median.
    # Simple density vector over fixed windows of n_blog ÷ 50 emissions.
    let
        T_rc   = max(8, n_blog ÷ 50)
        n_rc   = n_blog ÷ T_rc
        if n_rc >= 4
            # Count LP1-conj hits per window using lp1_conj_arrivals.
            # Map raw_steps to step-ordinal windows via the fraction
            # raw_step / total_span_approx * n_blog.
            arrivals_lc = stat.lp1_conj_arrivals
            total_span_lc = isempty(arrivals_lc) ? 0 :
                            arrivals_lc[end] - arrivals_lc[1] + 1
            lc_window_counts = zeros(Int, n_rc)
            if !isempty(arrivals_lc) && total_span_lc > 0
                for a in arrivals_lc
                    wi = clamp(round(Int, (a - arrivals_lc[1]) / total_span_lc * n_rc) + 1, 1, n_rc)
                    lc_window_counts[wi] += 1
                end
            else
                # No LP1-conj arrivals — use raw step density as proxy
                # (every window has equal density → all cold; diagnostics still run)
                fill!(lc_window_counts, 0)
            end
            sorted_lc = sort(lc_window_counts)
            median_lc = length(sorted_lc) % 2 == 0 ?
                (sorted_lc[length(sorted_lc)÷2] + sorted_lc[length(sorted_lc)÷2+1]) / 2.0 :
                Float64(sorted_lc[(length(sorted_lc)+1)÷2])
            # hot_mask[i] = true iff step i belongs to a hot window
            hot_mask = [lc_window_counts[clamp((i-1)÷T_rc + 1, 1, n_rc)] >= median_lc
                        for i in 1:n_blog]

            # Compute S₂ for four subsets of step pairs:
            # intra-hot, intra-cold, inter (hot-cold or cold-hot)
            counts_hot  = zeros(Int, nb_a2)
            counts_cold = zeros(Int, nb_a2)
            for i in 1:n_blog
                if hot_mask[i]
                    counts_hot[Int(blog[i]) + 1]  += 1
                else
                    counts_cold[Int(blog[i]) + 1] += 1
                end
            end
            n_hot_steps  = sum(counts_hot)
            n_cold_steps = sum(counts_cold)

            # Intra-collision entropy: S₂ computed within each regime
            (s2_hot,  socc_hot,  _) = _bucket_entropies(counts_hot,  nb_a2)
            (s2_cold, socc_cold, _) = _bucket_entropies(counts_cold, nb_a2)

            # Inter-collision entropy: use mixing formula
            # S₂^inter ≈ -log2( Σᵢ (n_hot[i]/n_hot) * (n_cold[i]/n_cold) )
            if n_hot_steps > 0 && n_cold_steps > 0
                cross = sum((counts_hot[i] / n_hot_steps) * (counts_cold[i] / n_cold_steps)
                            for i in 1:nb_a2)
                s2_inter = cross > 0.0 ? -log2(cross) : NaN
            else
                s2_inter = NaN
            end

            # Overall S₂ from combined counts (for reference)
            counts_all = counts_hot .+ counts_cold
            (s2_all, _, _) = _bucket_entropies(counts_all, nb_a2)

            @printf("    Regime split: T_window=%d, n_windows=%d, median_density=%.2f hits/window\n",
                    T_rc, n_rc, median_lc)
            @printf("    hot steps:  %d  α₂^hot  = %.4f  S_occ^hot  = %.4f\n",
                    n_hot_steps, s2_hot, socc_hot)
            @printf("    cold steps: %d  α₂^cold = %.4f  S_occ^cold = %.4f\n",
                    n_cold_steps, s2_cold, socc_cold)
            @printf("    inter-regime α₂: %.4f\n", isnan(s2_inter) ? -1.0 : s2_inter)
            @printf("    overall α₂:      %.4f\n", s2_all)
            if !isnan(s2_hot) && !isnan(s2_cold)
                delta_a2 = s2_hot - s2_cold
                flag_rc  = abs(delta_a2) > 0.05 ?
                    @sprintf("  ← Δα₂=%.4f, α₂ NOT invariant of walk kernel", delta_a2) :
                    "  (α₂ consistent across regimes)"
                @printf("    Δα₂ = α₂^hot − α₂^cold = %+.4f%s\n", delta_a2, flag_rc)
            end
        else
            @printf("    (need ≥4 regime windows; n_blog=%d too short)\n", n_blog)
        end
    end
    println()

    # ── α₂-3: Regime-conditioned α₂ (standalone summary) ─────────────────────
    # Already reported as part of α₂-2 above (Δα₂).  Print brief cross-ref.
    @printf("  α₂-3 — Regime-conditioned α₂: see Δα₂ in α₂-2 above.\n")
    println()

    # ── α₂-4: Collision autocorrelation C(τ) ─────────────────────────────────
    @printf("  α₂-4 — Collision autocorrelation C(τ) = E[cᵢ(t)·cᵢ(t+τ)]:\n")
    # Compute the autocorrelation of the squared-occupancy series:
    # at each time t, define x(t) = c_{blog[t]}(t) / n_T, i.e. the fractional
    # count of the occupied bucket in a sliding window.  For tractability we
    # use a coarse version: bin steps into windows of T_acf steps, compute the
    # vector of bucket counts, take the dot-product (collision count) of
    # adjacent windows, and compute its ACF.
    let
        T_acf   = max(8, n_blog ÷ 100)
        n_wins_acf = n_blog ÷ T_acf
        if n_wins_acf >= 16
            # Collision count per window: Σᵢ cᵢ² (unnormalised)
            coll_series = zeros(Float64, n_wins_acf)
            counts_w    = zeros(Int, nb_a2)
            for wi in 0:(n_wins_acf - 1)
                fill!(counts_w, 0)
                for k in (wi*T_acf + 1):((wi+1)*T_acf)
                    counts_w[Int(blog[k]) + 1] += 1
                end
                coll_series[wi+1] = Float64(sum(x^2 for x in counts_w))
            end
            mn_c  = sum(coll_series) / n_wins_acf
            var_c = n_wins_acf > 1 ?
                sum((x - mn_c)^2 for x in coll_series) / (n_wins_acf - 1) : 0.0
            max_lag_c4 = min(20, n_wins_acf ÷ 2)
            c_acf = zeros(Float64, max_lag_c4)
            if var_c > 0.0
                for lag in 1:max_lag_c4
                    cov = sum((coll_series[t] - mn_c) * (coll_series[t+lag] - mn_c)
                              for t in 1:(n_wins_acf - lag)) / (n_wins_acf - lag)
                    c_acf[lag] = cov / var_c
                end
            end
            acf_str = join([@sprintf("%+.3f", c_acf[k]) for k in 1:min(8, max_lag_c4)], "  ")
            @printf("    T_window=%d steps, %d windows\n", T_acf, n_wins_acf)
            @printf("    C(τ) lags 1..%d: %s\n", min(8, max_lag_c4), acf_str)
            # Classify decay
            inv_e_c = exp(-1.0)
            decor_c = findfirst(r -> abs(r) < inv_e_c, c_acf)
            if decor_c !== nothing
                @printf("    Decorr lag: %d windows ≈ %d steps\n",
                        decor_c, decor_c * T_acf)
            else
                @printf("    ACF does not decay below 1/e within %d lags — long-memory C(τ)\n",
                        max_lag_c4)
            end
            # Hurst proxy from log-log slope of |C(τ)|
            if max_lag_c4 >= 4
                lags_fit = [log(Float64(k)) for k in 1:max_lag_c4 if abs(c_acf[k]) > 1e-6]
                acf_fit  = [log(abs(c_acf[k])) for k in 1:max_lag_c4 if abs(c_acf[k]) > 1e-6]
                if length(lags_fit) >= 4
                    mlag = sum(lags_fit)/length(lags_fit); macf = sum(acf_fit)/length(acf_fit)
                    num_h = sum((lags_fit[i]-mlag)*(acf_fit[i]-macf) for i in eachindex(lags_fit))
                    den_h = sum((lags_fit[i]-mlag)^2 for i in eachindex(lags_fit))
                    slope_c4 = den_h > 0 ? num_h / den_h : 0.0
                    flag_c4  = slope_c4 > -0.5 ? "  ← POWER-LAW decay (α₂ ill-defined globally)" :
                               slope_c4 > -1.5 ? "  (intermediate decay)" :
                                                  "  (fast / exponential decay)"
                    @printf("    log|C(τ)| vs log τ slope: %.3f%s\n", slope_c4, flag_c4)
                end
            end
        else
            @printf("    (need ≥16 coarse windows; n_blog=%d with T=%d gives %d)\n",
                    n_blog, T_acf, n_wins_acf)
        end
    end
    println()

    # ── α₂-5: Collision burst size spectrum ──────────────────────────────────
    @printf("  α₂-5 — Per-bucket collision burst size spectrum:\n")
    # For each bucket b: find all maximal runs of consecutive steps where
    # blog[t] == b.  Collect the run-length distribution across all buckets.
    let
        burst_lengths = Int[]
        cur_b   = blog[1]
        cur_len = 1
        for t in 2:n_blog
            if blog[t] == cur_b
                cur_len += 1
            else
                cur_len > 1 && push!(burst_lengths, cur_len)
                cur_b   = blog[t]
                cur_len = 1
            end
        end
        cur_len > 1 && push!(burst_lengths, cur_len)

        if length(burst_lengths) >= 10
            n_bl    = length(burst_lengths)
            mean_bl = sum(burst_lengths) / n_bl
            max_bl  = maximum(burst_lengths)
            cnt1_bl = count(==(1), burst_lengths)   # handled above as cur_len==1 skip
            cnt2_bl = count(==(2), burst_lengths)
            cnt3p_bl = count(>=(3), burst_lengths)
            # KS vs Geometric(1/mean)
            p_geo_bl = mean_bl > 1.0 ? 1.0 / mean_bl : 1.0
            bsorted_bl = sort(burst_lengths)
            ks_bl = 0.0; cumul_bl = 0.0
            for bs in bsorted_bl
                cumul_bl += 1.0 / n_bl
                geo_cdf_bl = 1.0 - (1.0 - p_geo_bl)^bs
                ks_bl = max(ks_bl, abs(cumul_bl - geo_cdf_bl))
            end
            flag_bl = ks_bl > 0.1 ? "  ← POWER-LAW BURST (α₂ dominated by rare-event geometry)" :
                                     "  (consistent with geometric burst sizes)"
            @printf("    %d multi-step bursts detected (steps that re-hit same bucket)\n", n_bl)
            @printf("    mean_len=%.2f  max_len=%d\n", mean_bl, max_bl)
            @printf("    len=2: %d (%.1f%%)  len=3+: %d (%.1f%%)\n",
                    cnt2_bl, 100.0*cnt2_bl/n_bl, cnt3p_bl, 100.0*cnt3p_bl/n_bl)
            @printf("    KS vs Geometric(1/mean)=%.4f%s\n", ks_bl, flag_bl)
            # Log-log tail slope for power-law fit
            max_len_fit = min(max_bl, 30)
            len_counts  = [count(==(k), burst_lengths) for k in 2:max_len_fit]
            nonzero_idx = [k for k in eachindex(len_counts) if len_counts[k] > 0]
            if length(nonzero_idx) >= 4
                log_k   = [log(Float64(k+1)) for k in nonzero_idx]
                log_cnt = [log(Float64(len_counts[k])) for k in nonzero_idx]
                mk = sum(log_k)/length(log_k); mc = sum(log_cnt)/length(log_cnt)
                num_pl = sum((log_k[i]-mk)*(log_cnt[i]-mc) for i in eachindex(log_k))
                den_pl = sum((log_k[i]-mk)^2 for i in eachindex(log_k))
                slope_pl = den_pl > 0 ? num_pl / den_pl : 0.0
                flag_pl = slope_pl < -1.5 ? "  (steeper than geometric — sub-Poisson)" :
                          slope_pl > -0.5 ? "  ← SHALLOW SLOPE (power-law tail)" :
                                            "  (moderate slope)"
                @printf("    log-log tail slope: %.3f%s\n", slope_pl, flag_pl)
            end
        else
            @printf("    (fewer than 10 multi-step bursts detected; walk well-mixing at bucket level)\n")
        end
    end
    println()

    # ── α₂-6: ρ(T) = S_occ(T)/S₂(T) over dyadic windows ────────────────────
    @printf("  α₂-6 — ρ(T) = S_occ(T)/S₂(T) (effective-support vs collision-space ratio):\n")
    @printf("    window_T   α₂(T)   S_occ(T)   ρ(T)   dρ/dlogT   interpretation\n")
    prev_rho   = NaN
    prev_logT6 = NaN
    rho_vals   = Float64[]
    for T in dyadic_windows
        n_wins_r = n_blog ÷ T
        n_wins_r < 1 && continue
        s2_acc6 = 0.0; socc_acc6 = 0.0; n_v6 = 0
        counts_T6 = zeros(Int, nb_a2)
        for wi in 0:(n_wins_r - 1)
            fill!(counts_T6, 0)
            for k in (wi*T + 1):((wi+1)*T)
                counts_T6[Int(blog[k]) + 1] += 1
            end
            (s2, socc, _) = _bucket_entropies(counts_T6, nb_a2)
            if !isnan(s2)
                s2_acc6 += s2; socc_acc6 += socc; n_v6 += 1
            end
        end
        n_v6 == 0 && continue
        a2_T6   = s2_acc6   / n_v6
        socc_T6 = socc_acc6 / n_v6
        rho_T6  = a2_T6 > 0.0 ? socc_T6 / a2_T6 : NaN
        logT6   = log2(Float64(T))
        drho = (!isnan(prev_rho) && !isnan(prev_logT6) && logT6 > prev_logT6) ?
               (rho_T6 - prev_rho) / (logT6 - prev_logT6) : NaN
        drho_str = isnan(drho)  ? "        —" : @sprintf("%+9.4f", drho)
        rho_str6 = isnan(rho_T6) ? "     —" : @sprintf("%6.4f", rho_T6)
        interp = if isnan(rho_T6)
            "—"
        elseif !isnan(drho) && drho > 0.05
            "ρ GROWING → decoupled geometry"
        elseif !isnan(drho) && drho < -0.05
            "ρ SHRINKING → collapsing state space"
        else
            "ρ stable"
        end
        @printf("    %9d  %7.4f  %9.4f  %s  %s  %s\n",
                T, a2_T6, socc_T6, rho_str6, drho_str, interp)
        push!(rho_vals, isnan(rho_T6) ? 0.0 : rho_T6)
        prev_rho = rho_T6; prev_logT6 = logT6
    end
    if length(rho_vals) >= 3
        rho_range = maximum(rho_vals) - minimum(rho_vals)
        flag_rho  = rho_range < 0.05 ?
            "  → ρ CONSTANT: consistent scaling dimension" :
            @sprintf("  → ρ VARIES (range=%.4f): geometry and collision space decouple", rho_range)
        @printf("    %s\n", flag_rho)
    end
    println()

    # ── α₂-7: LP1-conj key collision geometry ────────────────────────────────
    # Since blog is now the LP1-conj a-bucket sequence, all events are split steps.
    # Instead of split/non-split (vacuous), compare α₂ on the first vs second half
    # of the emission sequence to detect non-stationarity in key geometry.
    @printf("  α₂-7 — LP1-conj collision geometry: first-half vs second-half α₂:\n")
    if n_blog >= 8
        mid = n_blog ÷ 2
        counts_h1 = zeros(Int, nb_a2); counts_h2 = zeros(Int, nb_a2)
        for i in 1:mid;        counts_h1[Int(blog[i]) + 1] += 1; end
        for i in (mid+1):n_blog; counts_h2[Int(blog[i]) + 1] += 1; end
        (s2_h1, socc_h1, n_h1) = _bucket_entropies(counts_h1, nb_a2)
        (s2_h2, socc_h2, n_h2) = _bucket_entropies(counts_h2, nb_a2)
        @printf("    first  half: %d events  α₂=%s  S_occ=%s\n",
                n_h1, isnan(s2_h1) ? "—" : @sprintf("%.4f", s2_h1),
                      isnan(socc_h1) ? "—" : @sprintf("%.4f", socc_h1))
        @printf("    second half: %d events  α₂=%s  S_occ=%s\n",
                n_h2, isnan(s2_h2) ? "—" : @sprintf("%.4f", s2_h2),
                      isnan(socc_h2) ? "—" : @sprintf("%.4f", socc_h2))
        if !isnan(s2_h1) && !isnan(s2_h2)
            delta_a2_halves = s2_h2 - s2_h1
            flag_halves = abs(delta_a2_halves) > 0.1 ?
                @sprintf("  ← NON-STATIONARY key geometry (Δα₂=%+.4f)", delta_a2_halves) :
                "  (key geometry stationary across run)"
            @printf("    Δα₂ = second − first = %+.4f%s\n", delta_a2_halves, flag_halves)
        end
    else
        @printf("    (need ≥8 LP1-conj emissions)\n")
    end
    println()

    # ── α₂-8: fluctuation curvature + per-window dispersion ───────────────────
    @printf("  α₂-8 — fluctuation curvature and dispersion across dyadic windows:\n")
    if length(a2_vals) >= 3
        d2_vals = [a2_vals[i+1] - 2a2_vals[i] + a2_vals[i-1] for i in 2:(length(a2_vals)-1)]
        max_abs_d2 = maximum(abs.(d2_vals))
        mean_abs_d2 = sum(abs.(x) for x in d2_vals) / length(d2_vals)
        @printf("    max |Δ²α₂| over logT   : %.6f\n", max_abs_d2)
        @printf("    mean |Δ²α₂| over logT  : %.6f\n", mean_abs_d2)
        flag_d2 = max_abs_d2 < 0.03 ? "  (curvature essentially flat)" :
                  max_abs_d2 < 0.10 ? "  (small residual curvature)" :
                                     "  ← curvature drift / hidden crossover"
        @printf("    curvature verdict      :%s\n", flag_d2)
    else
        @printf("    (need ≥3 dyadic windows for curvature)\n")
    end

    # Per-window dispersion of the α₂ estimator itself.
    @printf("  α₂ dispersion by window size:\n")
    for T in dyadic_windows
        n_wins_a2 = n_blog ÷ T
        n_wins_a2 < 2 && continue
        window_a2 = Float64[]
        counts_T = zeros(Int, nb_a2)
        for wi in 0:(n_wins_a2 - 1)
            fill!(counts_T, 0)
            for k in (wi*T + 1):((wi+1)*T)
                counts_T[Int(blog[k]) + 1] += 1
            end
            (s2w, _, _) = _bucket_entropies(counts_T, nb_a2)
            !isnan(s2w) && push!(window_a2, s2w)
        end
        if length(window_a2) >= 2
            μw, varw, skeww, kurtw = _moment4(window_a2)
            @printf("    T=%-8d  μ=%.4f  σ²=%.6f  skew=%+.3f  kurt=%+.3f\n",
                    T, μw, varw, skeww, kurtw)
        end
    end
    println()

    # ── α₂-9: measure-preserving / KL drift and perturbation susceptibility ───
    @printf("  α₂-9 — measure-preserving test and perturbation susceptibility:\n")
    if length(dyadic_windows) >= 2
        for T in dyadic_windows[1:min(4, length(dyadic_windows))]
            n_wins_a2 = n_blog ÷ T
            n_wins_a2 < 2 && continue
            kls = Float64[]
            prev_counts = zeros(Int, nb_a2)
            for wi in 0:(n_wins_a2 - 1)
                counts_T = zeros(Int, nb_a2)
                for k in (wi*T + 1):((wi+1)*T)
                    counts_T[Int(blog[k]) + 1] += 1
                end
                if wi > 0
                    push!(kls, _kl_divergence_counts(prev_counts, counts_T))
                end
                prev_counts .= counts_T
            end
            if !isempty(kls)
                @printf("    T=%-8d  mean KL(prev||curr)=%.5f  max KL=%.5f\n",
                        T, sum(kls)/length(kls), maximum(kls))
            end
        end
    end
    # Susceptibility proxy: KL drift between consecutive coarse blocks.
    # (slog is all-true for LP1-conj emissions, so split/non-split partition
    # is degenerate; instead measure inter-block KL divergence as a proxy for
    # stationarity — large KL → the a-bucket distribution is drifting.)
    if length(blog) >= 64
        block_T = max(8, n_blog ÷ 32)
        n_blocks = n_blog ÷ block_T
        if n_blocks >= 4
            kl_drift_vals = Float64[]
            prev_cnts = zeros(Int, nb_a2)
            for bi in 0:(n_blocks - 1)
                lo = bi * block_T + 1
                hi = min((bi + 1) * block_T, n_blog)
                cur_cnts = zeros(Int, nb_a2)
                for j in lo:hi
                    cur_cnts[Int(blog[j]) + 1] += 1
                end
                if bi > 0 && sum(prev_cnts) > 0 && sum(cur_cnts) > 0
                    push!(kl_drift_vals, _kl_divergence_counts(prev_cnts, cur_cnts))
                end
                prev_cnts .= cur_cnts
            end
            if !isempty(kl_drift_vals)
                mean_kl = sum(kl_drift_vals) / length(kl_drift_vals)
                max_kl  = maximum(kl_drift_vals)
                flag_kl = mean_kl > 0.5 ? "  ← HIGH DRIFT (a-dist non-stationary)" :
                          mean_kl > 0.1 ? "  (moderate drift)" :
                                          "  (a-dist stable across blocks)"
                @printf("    KL drift proxy (block_T=%d): mean=%.5f  max=%.5f%s\n",
                        block_T, mean_kl, max_kl, flag_kl)
            else
                @printf("    KL drift proxy        : insufficient block data\n")
            end
        end
    end
    println()

    # ── α₂-10: collision entropy decomposition and hot-bucket concentration ──
    # Operates on the full LP1-conj partial key stream (blog / lp1_conj_key_blog),
    # exactly as α₂-1 through α₂-9.  Accumulate bucket counts from the entire
    # blog vector and compute S₂ (Rényi-2 entropy) and concentration metrics.
    @printf("  α₂-10 — collision entropy decomposition / entropy whales (LP1-conj keys):\n")
    if n_blog >= 1
        counts_a10 = zeros(Int, nb_a2)
        for b in blog
            counts_a10[Int(b) + 1] += 1
        end
        (s2_all, socc_all, n_all) = _bucket_entropies(counts_a10, nb_a2)
        if n_all > 0
            top1  = _top_share(counts_a10, 0.01)
            top5  = _top_share(counts_a10, 0.05)
            top10 = _top_share(counts_a10, 0.10)
            @printf("    n_partials             : %d  (nb_fp_buckets=%d)\n", n_all, nb_a2)
            @printf("    α₂(lp1_conj keys)      : %.5f\n", s2_all)
            @printf("    top 1%% / 5%% / 10%% share : %.3f  %.3f  %.3f\n", top1, top5, top10)
            @printf("    occupancy entropy      : %.5f\n", socc_all)
            if top1 > 0.25
                @printf("    verdict                 :  ← entropy dominated by rare hot buckets\n")
            else
                @printf("    verdict                 :  (no extreme entropy whales)\n")
            end
        end
    else
        @printf("    (no LP1-conj partials recorded)\n")
    end
    println()

    # ── α₂-11: effective independence, motifs, and provenance hash ───────────
    @printf("  α₂-11 — effective independence, motifs, and provenance hash:\n")
    if length(arrivals) >= 8
        # Reuse the same coarse-window count model as the ACF section.
        total_span_eff = arrivals[end] - arrivals[1] + 1
        T_eff = max(100, total_span_eff ÷ 200)
        n_bins_eff = max(8, total_span_eff ÷ T_eff)
        counts_eff = zeros(Float64, n_bins_eff)
        t0_eff = arrivals[1]
        for a in arrivals
            wi = min(n_bins_eff, (a - t0_eff) ÷ T_eff + 1)
            counts_eff[wi] += 1.0
        end
        mn_eff = sum(counts_eff) / n_bins_eff
        var_eff = sum((c - mn_eff)^2 for c in counts_eff) / max(1, n_bins_eff - 1)
        if var_eff > 1e-30
            ρsum = 0.0
            max_lag = min(10, n_bins_eff - 1)
            for lag in 1:max_lag
                cov = sum((counts_eff[w] - mn_eff) * (counts_eff[w + lag] - mn_eff)
                          for w in 1:(n_bins_eff - lag)) / (n_bins_eff - lag)
                ρ = cov / var_eff
                ρsum += max(0.0, ρ)
            end
            neff = n_bins_eff / max(1e-9, 1.0 + 2.0 * ρsum)
            @printf("    N_eff (coarse windows) : %.2f of %d windows\n", neff, n_bins_eff)
        end
    end

    if length(blog) >= 4
        # a-bucket 4-gram motifs: detect repeated local patterns in the LP1-conj
        # a-bucket sequence.  Under i.i.d. uniform over nb buckets, every 4-gram
        # has probability 1/nb³; excess repetitions flag structural correlation.
        motif_counts_b = Dict{NTuple{4,Int},Int}()
        for i in 1:(length(blog)-3)
            mot = (blog[i], blog[i+1], blog[i+2], blog[i+3])
            motif_counts_b[mot] = get(motif_counts_b, mot, 0) + 1
        end
        if !isempty(motif_counts_b)
            top_motif_b = first(sort(collect(motif_counts_b), by = x -> -last(x)))
            n_4grams    = length(blog) - 3
            # Expected count for most-probable 4-gram under empirical marginal:
            # use product of empirical bucket frequencies as independence baseline.
            bkt_freq = zeros(Float64, nb_a2)
            for b in blog; bkt_freq[Int(b)+1] += 1.0; end
            bkt_freq ./= max(1.0, length(blog))
            p_indep = prod(bkt_freq[Int(b)+1] for b in top_motif_b[1])
            expected_b = p_indep * max(1, n_4grams)
            lift_b = top_motif_b[2] / max(1e-9, expected_b)
            flag_b = lift_b > 3.0 ? "  ← REPEATED STRUCTURAL MOTIF" :
                     lift_b > 1.5 ? "  (mild motif excess)" :
                                    "  (consistent with independence)"
            @printf("    top a-bucket 4-gram    : (%d,%d,%d,%d)  count=%d  expected≈%.2f  lift=%.2f%s\n",
                    top_motif_b[1]..., top_motif_b[2], expected_b, lift_b, flag_b)
        end
    end

    if stat._event_hash_state != UInt64(0x9e3779b97f4a7c15)
        @printf("    provenance digest      : 0x%016x  (XOR of per-thread hash chains)\n",
                stat._event_hash_state)
    end
    println()

    # ── α₂-12: Per-bucket identity autocorrelation Pr(X_{t+h} = X_t) ─────────
    #
    #  The existing α₂-4 tracks Cor(Σcᵢ²(window t), Σcᵢ²(window t+τ)) — a scalar
    #  summary that aggregates all buckets.  This section answers the finer question:
    #
    #    P_obs(h)  = Pr(X_{t+h} = X_t)   (empirical same-bucket rate at lag h)
    #    P_base    = Σᵢ pᵢ²               (baseline under i.i.d. with empirical marginal)
    #    lift(h)   = P_obs(h) / P_base
    #
    #  lift(h) > 1 means the walk returns to the same bucket more often than chance
    #  at lag h — bucket self-attraction / persistence.
    #  lift(h) → 1 as h → ∞ is expected for any ergodic chain; the decorrelation
    #  lag h* where lift first crosses 1+ε is the bucket-level mixing time.
    #
    #  We also compute the per-bucket conditional return probability:
    #    p_return(b, h) = Pr(X_{t+h} = b | X_t = b)
    #  and report the top-5 stickiest buckets (highest lift_b = p_return / p_b).
    #  A bucket with lift_b >> 1 is a genuine attractor in the partial stream.
    #
    #  Baseline P_base is estimated from the empirical marginal of the full blog
    #  sequence (not assumed uniform — this correctly handles the factor-base
    #  non-uniformity already observed in the a-histogram).
    #
    #  Computational cost: O(n_blog × max_lag) with a tight inner loop over the
    #  raw UInt16 stream — no allocation inside the lag loop.
    @printf("  α₂-12 — Per-bucket identity autocorrelation Pr(X_{{t+h}} = X_t) vs baseline:\n")
    let
        # Empirical marginal pᵢ and baseline P_base = Σ pᵢ²
        marginal = zeros(Float64, nb_a2)
        @inbounds for b in blog; marginal[Int(b) + 1] += 1.0; end
        marginal ./= max(1.0, Float64(n_blog))
        P_base = sum(x^2 for x in marginal)   # Rényi-2 collision probability

        # Lag grid: dense at short lags (where self-attraction is most likely),
        # then geometric to ~n_blog/4.  We cap at 64 lags total.
        max_lag_id = min(64, n_blog ÷ 4)
        lag_grid = Int[]
        for h in 1:min(20, max_lag_id)
            push!(lag_grid, h)
        end
        h = 24
        while h <= max_lag_id && length(lag_grid) < 64
            push!(lag_grid, h)
            h = max(h + 1, round(Int, h * 1.5))
        end

        if isempty(lag_grid)
            @printf("    (need n_blog ≥ 4; got %d)\n", n_blog)
        else
            # For each lag h: count matches X_{t+h} == X_t.
            # Inner loop is a tight scan over the raw UInt16 array — no Dict, no alloc.
            n_lags = length(lag_grid)
            P_obs  = zeros(Float64, n_lags)
            @inbounds for (li, h) in enumerate(lag_grid)
                n_pairs = n_blog - h
                n_pairs <= 0 && continue
                hits = 0
                for t in 1:n_pairs
                    hits += (blog[t] == blog[t + h]) ? 1 : 0
                end
                P_obs[li] = Float64(hits) / Float64(n_pairs)
            end

            # Analytic null: for an i.i.d. sequence with empirical marginal pᵢ,
            # Pr(X_{t+h} = X_t) = Σᵢ pᵢ² = P_base for all h ≥ 1.
            # A Monte-Carlo shuffle would converge to exactly this; computing it
            # analytically avoids a 125 MB copy and O(n_blog × n_lags) null scan.
            P_null = P_base

            @printf("    Baseline P_base (Σpᵢ²)        : %.6e  (analytic i.i.d. null)\n", P_base)
            @printf("    %-6s  %-12s  %-12s  %-8s  %s\n",
                    "lag h", "P_obs", "P_null(=P_base)", "lift_obs", "interpretation")
            decor_lag_id = -1
            for (li, h) in enumerate(lag_grid)
                P_base_local = max(1e-30, P_null)
                lift_obs  = P_obs[li]  / P_base_local
                flag = if lift_obs > 2.0;  "← STRONG self-attraction"
                       elseif lift_obs > 1.3; "← moderate self-attraction"
                       elseif lift_obs > 1.05; "← mild self-attraction"
                       elseif lift_obs < 0.95; "← AVOIDANCE"
                       else;                   "(≈ random)"
                       end
                @printf("    %-6d  %-12.6e  %-12.6e  %-8.4f  %s\n",
                        h, P_obs[li], P_null, lift_obs, flag)
                if decor_lag_id < 0 && lift_obs < 1.05
                    decor_lag_id = h
                end
            end
            if decor_lag_id > 0
                @printf("    Decorrelation lag h*           : %d partials (lift first < 1.05)\n",
                        decor_lag_id)
            else
                @printf("    Decorrelation lag h*           : > %d partials (lift never drops below 1.05)\n",
                        lag_grid[end])
            end
            println()

            # Per-bucket conditional return probability p_return(b) = Pr(X_{t+1}=b|X_t=b)
            # vs marginal pᵢ.  Only at lag h=1 (most diagnostic for stickiness).
            # lift_b = p_return(b) / p_b.  Top-5 stickiest and bottom-5 most-repelled.
            @printf("    Per-bucket stickiness at lag h=1 (top-5 attractors / bottom-5 repellers):\n")
            if n_blog >= 4
                # Count per-bucket: n_stays[b] = #{t : blog[t]==b AND blog[t+1]==b}
                #                   n_depart[b] = #{t : blog[t]==b}   (= n_blog*pᵢ approx)
                n_stays   = zeros(Int, nb_a2)
                n_depart  = zeros(Int, nb_a2)
                @inbounds for t in 1:(n_blog - 1)
                    b = Int(blog[t]) + 1
                    n_depart[b] += 1
                    blog[t] == blog[t+1] && (n_stays[b] += 1)
                end
                # Only report buckets with ≥10 departures to suppress noise.
                min_dep = 10
                p_return_b = [(n_depart[b] >= min_dep) ?
                               (Float64(n_stays[b]) / Float64(n_depart[b])) : NaN
                              for b in 1:nb_a2]
                # lift_b = p_return_b / max(pᵢ, 1/nb_a2)  (guard against 0-marginal buckets)
                lift_b_vec = [(isnan(p_return_b[b]) || marginal[b] < 1e-12) ? NaN :
                               p_return_b[b] / marginal[b]
                              for b in 1:nb_a2]

                # Sort by lift (NaN last)
                valid_idx = [b for b in 1:nb_a2 if !isnan(lift_b_vec[b])]
                sort!(valid_idx, by = b -> -lift_b_vec[b])

                @printf("      %5s  %8s  %8s  %8s  %8s\n",
                        "bucket", "p_i", "p_ret(1)", "lift_b", "n_dep")
                for b in valid_idx[1:min(5, end)]
                    @printf("      %5d  %8.5f  %8.5f  %8.3f  %8d\n",
                            b - 1, marginal[b], p_return_b[b], lift_b_vec[b], n_depart[b])
                end
                @printf("      --- bottom 5 ---\n")
                for b in valid_idx[max(1,end-4):end]
                    @printf("      %5d  %8.5f  %8.5f  %8.3f  %8d\n",
                            b - 1, marginal[b], p_return_b[b], lift_b_vec[b], n_depart[b])
                end

                # Summary statistic: mean lift_b weighted by n_depart (traffic-weighted stickiness)
                total_dep  = sum(n_depart[b] for b in valid_idx)
                mean_lift_b = total_dep > 0 ?
                    sum(lift_b_vec[b] * n_depart[b] for b in valid_idx) / total_dep : NaN
                flag_sticky = if !isnan(mean_lift_b)
                    mean_lift_b > 1.3 ? "  ← GLOBALLY STICKY (walk self-traps)" :
                    mean_lift_b > 1.05 ? "  ← mild global stickiness" :
                    mean_lift_b < 0.95 ? "  ← GLOBAL AVOIDANCE (anti-persistent)" :
                                         "  (traffic-weighted stickiness ≈ random)"
                else "  (insufficient data)" end
                @printf("      Traffic-weighted mean lift_b   : %.4f%s\n",
                        isnan(mean_lift_b) ? 0.0 : mean_lift_b, flag_sticky)
            end
        end
    end
    println()

    end  # if n_blog >= 32

    # ==========================================================================
    #  CIR-ACF — Post-emission conditional emission probability
    #
    #  Diagnostic motivation (per ChatGPT analysis of stride-variant results):
    #
    #    The joint picture of Fano factor, birthday α, persistence score, and
    #    phase-3 quality suggests the walk is NOT a homogeneous rare-event
    #    process but rather a renewal process with "quiet periods" punctuated by
    #    "productive episodes."  The key distinguishing observable is:
    #
    #      P(emit at t+Δ | emit at t)   as a function of Δ (step lag)
    #
    #    Under the Poisson null, this equals the unconditional emission rate λ
    #    for all Δ ≥ 1.  Positive post-emission correlation → walk enters
    #    a transiently productive region after each closure; the shape of the
    #    autocorrelation tail characterises whether that productivity is:
    #
    #      • short burst (high lift at Δ=1..10, decays fast)  → hit-only stride
    #      • long persistence (lift elevated over hundreds of steps)  → baseline
    #      • bimodal (burst + persistent tail)  → hybrid regime
    #
    #    Unifying prediction: if baseline has fewer, longer-lived productive
    #    pockets while hit-only has more, shorter-lived ones, then:
    #      baseline  → wide, flat ACF tail (decorrelation lag >> burst width)
    #      hit-only  → sharp spike at Δ≈1..5 then rapid decay to null
    #
    #    This directly explains persistence↓ + Fano↑ + α↑ + phase3-quality↓
    #    under hit-only stride as a single dynamical story.
    #
    #  Method:
    #    Sort the merged arrivals array.  For each emission at step t[i], binary-
    #    search for the first arrival > t[i] and count how many arrivals fall in
    #    (t[i], t[i]+Δ] for each Δ in a lag grid.  Accumulate per-lag hit counts
    #    and normalise.  Compare to Poisson baseline P_base(Δ) = 1−exp(−λΔ).
    #
    #    "lift(Δ) = P_cond(Δ) / P_base(Δ)" measures excess emission probability
    #    relative to memoryless baseline.  lift > 1 → positive autocorrelation;
    #    lift < 1 → post-emission refractory period / avoidance.
    #
    #    We also compute a lag-weighted AUC of (lift−1) to get a scalar "total
    #    excess productivity" that integrates both burst intensity and tail length.
    #
    #  Output:
    #    • Table of Δ, P_cond(Δ), P_base(Δ), lift(Δ) for the lag grid.
    #    • Burst width Δ_burst: smallest Δ where lift first drops below
    #      0.5*(lift_max + 1.0)  (half-max above null).
    #    • Tail half-life Δ_tail: smallest Δ where lift first drops below 1.10.
    #    • Total excess AUC ∫(lift−1)dΔ (trapezoid rule over the grid).
    #    • Interpretation banner comparing to Poisson / burst / persistent archetypes.
    # ==========================================================================
    let
        arrivals_cir = stat.lp1_conj_arrivals
        n_cir = length(arrivals_cir)

        @printf("\n  CIR-ACF — Post-emission conditional LP1-conj emission probability P(emit within Δ | emit at t):\n")
        @printf("  ─────────────────────────────────────────────────────────────────────────────────────────────\n")

        if n_cir < 8
            @printf("    (need ≥ 8 emissions; got %d — skipping CIR-ACF)\n", n_cir)
        else
            # Sort arrivals so binary search works.
            arr_sorted = sort(arrivals_cir)
            total_steps_cir = arr_sorted[end] - arr_sorted[1] + 1
            lambda_cir = (n_cir - 1) / max(1.0, Float64(total_steps_cir))  # emissions per step

            @printf("    Emissions (n)          : %d\n", n_cir)
            @printf("    Step span              : %d\n", total_steps_cir)
            @printf("    Mean emission rate λ   : %.6e  (emissions/step)\n", lambda_cir)
            @printf("    Mean inter-arrival gap : %.1f steps\n", 1.0 / max(lambda_cir, 1e-30))
            println()

            # Build lag grid: dense at short lags, then geometric out to ~span/4.
            # We want to capture both the burst regime (Δ ≈ 1..20) and the tail
            # (Δ up to hundreds or thousands of steps).  Cap at 80 grid points.
            max_lag_cir = min(total_steps_cir ÷ 4, 100_000)
            lag_grid_cir = Int[]
            for d in 1:min(30, max_lag_cir)
                push!(lag_grid_cir, d)
            end
            d = 35
            while d <= max_lag_cir && length(lag_grid_cir) < 80
                push!(lag_grid_cir, d)
                d = max(d + 1, round(Int, d * 1.35))
            end

            if isempty(lag_grid_cir)
                @printf("    (step span too small to build lag grid)\n")
            else
                n_lags_cir = length(lag_grid_cir)
                P_cond_cir  = zeros(Float64, n_lags_cir)

                # For each source emission i, compute the binary indicator:
                # hit_any[li] = #{i : at least one emission in (t[i], t[i]+lag_grid[li]]}.
                # Method: binary-search for the first arrival after t[i], then walk
                # the sorted array advancing j2 through the lag grid.
                # Cost: O(n_cir × mean_events_per_window).
                max_lag_val = lag_grid_cir[end]
                hit_any = zeros(Int, n_lags_cir)
                n_sources2 = 0
                @inbounds for i in 1:n_cir
                    t_src = arr_sorted[i]
                    t_src + max_lag_val > arr_sorted[end] && continue
                    n_sources2 += 1
                    lo_j2 = i + 1; hi_j2 = n_cir
                    j_start2 = n_cir + 1
                    while lo_j2 <= hi_j2
                        mid_j2 = (lo_j2 + hi_j2) >> 1
                        if arr_sorted[mid_j2] > t_src
                            j_start2 = mid_j2;  hi_j2 = mid_j2 - 1
                        else;  lo_j2 = mid_j2 + 1;  end
                    end
                    j2 = j_start2
                    @inbounds for li2 in 1:n_lags_cir
                        lag_val = lag_grid_cir[li2]
                        # Advance j2 to first arrival beyond this lag threshold.
                        while j2 <= n_cir && arr_sorted[j2] - t_src <= lag_val
                            j2 += 1
                        end
                        if j2 > j_start2
                            hit_any[li2] += 1
                        end
                    end
                end

                if n_sources2 == 0
                    @printf("    (no source events with right-span; step span too small for lag grid)\n")
                else
                    for li2 in 1:n_lags_cir
                        P_cond_cir[li2] = Float64(hit_any[li2]) / Float64(n_sources2)
                    end

                    # Poisson baseline: P_base(Δ) = 1 − exp(−λ·Δ).
                    # This is the probability of at least one arrival in a window of size Δ
                    # for a stationary Poisson process with rate λ.
                    P_base_cir = [1.0 - exp(-lambda_cir * Float64(lag_grid_cir[li]))
                                  for li in 1:n_lags_cir]

                    lift_cir = [P_base_cir[li] > 1e-12 ?
                                P_cond_cir[li] / P_base_cir[li] : NaN
                                for li in 1:n_lags_cir]

                    # Summary statistics.
                    valid_lift = [lift_cir[li] for li in 1:n_lags_cir if !isnan(lift_cir[li])]
                    lift_max   = isempty(valid_lift) ? 1.0 : maximum(valid_lift)
                    lift_final = isempty(valid_lift) ? 1.0 : valid_lift[end]

                    # Burst width: smallest Δ where lift first drops below half-max above null.
                    # half-max threshold = 1.0 + 0.5*(lift_max - 1.0)
                    lift_half_thresh = 1.0 + 0.5 * max(0.0, lift_max - 1.0)
                    delta_burst = -1
                    for li in 1:n_lags_cir
                        isnan(lift_cir[li]) && continue
                        if lift_cir[li] < lift_half_thresh
                            delta_burst = lag_grid_cir[li]; break
                        end
                    end

                    # Tail half-life: smallest Δ where lift first drops below 1.10.
                    delta_tail = -1
                    for li in 1:n_lags_cir
                        isnan(lift_cir[li]) && continue
                        if lift_cir[li] < 1.10
                            delta_tail = lag_grid_cir[li]; break
                        end
                    end

                    # Total excess AUC: trapezoid integral of (lift − 1) over the lag grid.
                    # Measures total excess productivity relative to Poisson null.
                    auc_excess = 0.0
                    for li in 2:n_lags_cir
                        if !isnan(lift_cir[li]) && !isnan(lift_cir[li-1])
                            dΔ    = Float64(lag_grid_cir[li] - lag_grid_cir[li-1])
                            avg_l = 0.5 * ((lift_cir[li] - 1.0) + (lift_cir[li-1] - 1.0))
                            auc_excess += avg_l * dΔ
                        end
                    end

                    @printf("    Summary statistics:\n")
                    @printf("      n_source_events (with right-span) : %d\n", n_sources2)
                    @printf("      lift_max (peak post-emission lift) : %.4f\n", lift_max)
                    @printf("      lift at Δ=%d (final lag)          : %.4f\n",
                            lag_grid_cir[end], lift_final)
                    if delta_burst > 0
                        @printf("      Δ_burst (lift < half-max)         : %d steps\n", delta_burst)
                    else
                        @printf("      Δ_burst                           : > %d steps (lift never drops to half-max)\n",
                                lag_grid_cir[end])
                    end
                    if delta_tail > 0
                        @printf("      Δ_tail (lift < 1.10)              : %d steps\n", delta_tail)
                    else
                        @printf("      Δ_tail                            : > %d steps (persistent above 1.10 throughout)\n",
                                lag_grid_cir[end])
                    end
                    @printf("      Total excess AUC ∫(lift−1)dΔ     : %.2f step-units\n", auc_excess)
                    println()

                    # Per-variant interpretation key:
                    # Archetypes:
                    #   Poisson    : lift_max ≈ 1, AUC ≈ 0
                    #   Burst      : lift_max >> 1, Δ_burst small (< 20), Δ_tail < 50
                    #   Persistent : lift_max moderate, Δ_tail large (>> 50), AUC large
                    #   Bimodal    : lift_max >> 1 AND Δ_tail large → burst + persistence
                    archetype = if lift_max < 1.15
                        "POISSON-LIKE  (no significant post-emission autocorrelation)"
                    elseif (delta_tail > 0 && delta_tail < 50) || (delta_tail < 0 && lift_max < 1.5)
                        @sprintf("BURST         (sharp spike, Δ_tail=%s; consistent with hit-triggered stride renewal effect)",
                                 delta_tail > 0 ? string(delta_tail)*" steps" : ">$(lag_grid_cir[end]) steps")
                    elseif delta_tail < 0 && lift_max >= 1.5
                        "PERSISTENT    (long positive tail throughout grid; walk mines productive regions repeatedly)"
                    elseif delta_tail > 0 && delta_tail >= 50 && lift_max >= 2.0
                        @sprintf("BURST+PERSIST (high peak AND slow decay; Δ_burst=%s Δ_tail=%d steps; richest structure)",
                                 delta_burst > 0 ? string(delta_burst)*" steps" : ">$(lag_grid_cir[end])", delta_tail)
                    else
                        @sprintf("MODERATE      (lift_max=%.2f, Δ_tail=%s; mild positive autocorrelation)",
                                 lift_max,
                                 delta_tail > 0 ? string(delta_tail)*" steps" : ">$(lag_grid_cir[end]) steps")
                    end
                    @printf("    Archetype classification  : %s\n", archetype)
                    println()

                    # Expected cross-variant comparison note:
                    @printf("    Cross-variant interpretation guide:\n")
                    @printf("      If baseline:  lift_max moderate, Δ_tail >> 100 → persistent pockets\n")
                    @printf("      If hit-only:  lift_max >> baseline, Δ_tail << baseline → burst/renewal\n")
                    @printf("      Persistent ACF explains: higher persistence score, lower Fano, lower birthday α,\n")
                    @printf("        better phase-3 quality (walk re-mines the same productive geometry)\n")
                    @printf("      Burst ACF explains:     lower persistence score, higher Fano, higher birthday α,\n")
                    @printf("        weaker phase-3 quality (transient pockets; less useful graph connectivity)\n")
                    println()

                    # Full table.
                    @printf("    %-8s  %-12s  %-12s  %-10s  %s\n",
                            "Δ (steps)", "P_cond(Δ)", "P_base(Δ)", "lift(Δ)", "interpretation")
                    @printf("    %s\n", "-"^72)
                    for li in 1:n_lags_cir
                        l = isnan(lift_cir[li]) ? NaN : lift_cir[li]
                        flag_cir = if isnan(l);               "(insufficient baseline)"
                                   elseif l > 5.0;            "← VERY STRONG burst (>5×)"
                                   elseif l > 2.0;            "← strong lift (>2×)"
                                   elseif l > 1.5;            "← moderate lift"
                                   elseif l > 1.10;           "← mild lift"
                                   elseif l > 0.90;           "(≈ null)"
                                   else;                       "← refractory / avoidance"
                                   end
                        @printf("    %-8d  %-12.6f  %-12.6f  %-10s  %s\n",
                                lag_grid_cir[li],
                                P_cond_cir[li],
                                P_base_cir[li],
                                isnan(l) ? "  NaN" : @sprintf("%.4f", l),
                                flag_cir)
                    end
                end
            end
        end
    end   # CIR-ACF let

end
