# =============================================================================
#  lp1_conj_deep_diag_d7_d11.jl
#
#  LP1-conj deep diagnostic sections D7 – D11.
#
#  D7  — Marginal utility of LP1-conj table entries
#  D8  — Closure-depth distribution
#  D9  — H(step opcode | recent LP1-conj)
#  D10 — Transition graph compression (spectral gap + SCC)
#  D11 — Branch-conditioned α₂ and step-opcode traffic analysis
#
#  Included by lp1_conj_deep_diag.jl; do not include directly.
# =============================================================================

function _report_d7_d11(phi_stat  ::PhiBiasStat,
                         deep_stat ::ConjDeepStat,
                         n_emit    ::Int;
                         conj_snap ::Union{Dict, AbstractVector, Nothing} = nothing)

    # ──────────────────────────────────────────────────────────────────────
    #  D7 — Marginal utility of LP1-conj table entries
    # ──────────────────────────────────────────────────────────────────────
    @printf("\n  D7 — Marginal utility of LP1-conj table entries\n")
    @printf("  ─────────────────────────────────────────────────────────────────\n")
    let
        is_first = deep_stat.is_first_closure
        n_first  = length(is_first)
        if n_first == 0
            @printf("    (no closure data recorded — check ConjDeepStat wiring)\n")
        else
            n_novel      = count(identity, is_first)
            n_redundant  = n_first - n_novel
            @printf("    Total closures recorded        : %d\n", n_first)
            @printf("    Novel closures (first for key) : %d  (%.1f%%)\n",
                    n_novel, 100.0 * n_novel / n_first)
            @printf("    Redundant closures             : %d  (%.1f%%)\n",
                    n_redundant, 100.0 * n_redundant / n_first)

            fracs = [0.10, 0.20, 0.30, 0.50, 0.70, 0.90, 1.0]
            @printf("    Cumulative solve-enabling closures vs emission fraction:\n")
            @printf("      %8s  %10s  %10s  %8s\n",
                    "emit%", "n_closures", "n_novel", "marginal_util")
            cumul_novel = 0
            prev_novel  = 0
            for frac in fracs
                idx  = clamp(round(Int, frac * n_first), 1, n_first)
                cumul_novel = count(identity, is_first[1:idx])
                marginal    = idx > 1 ?
                    (cumul_novel - prev_novel) / max(1, round(Int, (fracs[1])*n_first)) :
                    NaN
                @printf("      %8.1f%%  %10d  %10d  %8s\n",
                        100*frac, idx, cumul_novel,
                        isnan(marginal) ? "  n/a" : @sprintf("%.4f", cumul_novel / idx))
                prev_novel = cumul_novel
            end

            sat_frac = 1.0
            cum_prev  = 0
            for frac in [0.05, 0.10, 0.20, 0.30, 0.40, 0.50, 0.60, 0.70, 0.80, 0.90]
                idx  = clamp(round(Int, frac * n_first), 1, n_first)
                cum_now = count(identity, is_first[1:idx])
                marginal_rate = n_novel > 0 ? (cum_now - cum_prev) / n_novel : 0.0
                cum_prev = cum_now
                if marginal_rate < 0.05 && sat_frac == 1.0
                    sat_frac = frac
                end
            end
            if sat_frac < 1.0
                @printf("    Saturation point (≥95%% novel closures): ~%.0f%% of table\n",
                        100 * sat_frac)
                @printf("    → Table could be reduced by ~%.0f%% with <5%% closure penalty\n",
                        100 * (1.0 - sat_frac))
            else
                @printf("    No saturation detected: table is efficiently used\n")
            end
        end

        if conj_snap !== nothing
            snap_sz = conj_snap isa AbstractVector ?
                      sum(conj_total_entries(lsm) for lsm in conj_snap; init=0) :
                      length(conj_snap)
            @printf("    Conj snapshot size             : %d entries\n", snap_sz)
            @printf("    Closures / snapshot entry      : %.4f\n",
                    snap_sz > 0 ? length(deep_stat.is_first_closure) / snap_sz : 0.0)
        end
    end

    # ──────────────────────────────────────────────────────────────────────
    #  D8 — Closure-depth distribution
    # ──────────────────────────────────────────────────────────────────────
    @printf("\n  D8 — Closure-depth distribution\n")
    @printf("  ─────────────────────────────────────────────────────────────────\n")
    let
        depths = deep_stat.d8_depths
        nd = length(depths)

        if nd < 2
            @printf("    (need ≥ 2 closures with depth data; got %d — check miss-path wiring)\n", nd)
            @goto d8_done
        end

        d_min  = minimum(depths)
        d_max  = maximum(depths)
        d_mean = sum(depths) / nd
        d_var  = nd < 2 ? 0.0 : sum((x - d_mean)^2 for x in depths) / (nd - 1)
        d_std  = sqrt(d_var)
        d_cv   = d_mean > 0 ? d_std / d_mean : NaN
        d_sorted = sort(depths)
        p10 = d_sorted[max(1, round(Int, 0.10 * nd))]
        p50 = d_sorted[max(1, round(Int, 0.50 * nd))]
        p90 = d_sorted[max(1, round(Int, 0.90 * nd))]
        p99 = d_sorted[max(1, round(Int, 0.99 * nd))]

        @printf("    Closures with depth data       : %d\n", nd)
        @printf("    Depth min/p10/p50/p90/p99/max  : %d / %d / %d / %d / %d / %d\n",
                d_min, p10, p50, p90, p99, d_max)
        @printf("    Mean depth / CV                : %.1f / %.4f\n", d_mean, d_cv)
        if d_cv > 1.5
            @printf("    ↑ CV > 1.5: HIGHLY HEAVY-TAILED depth distribution\n")
            @printf("      → consistent with metastable basin hopping: most closures fast,\n")
            @printf("        rare closures survive extremely long.\n")
        elseif d_cv > 1.0
            @printf("    ↑ CV > 1.0: moderately heavy tail (over-dispersed)\n")
        else
            @printf("    ↑ CV ≤ 1.0: depth distribution near-geometric (memoryless)\n")
        end

        bins      = [0, 1, 5, 20, 50, 150, 400, typemax(Int)]
        bin_names = ["[0,1)", "[1,5)", "[5,20)", "[20,50)", "[50,150)", "[150,400)", "[400,∞)"]
        bin_cnts  = zeros(Int, length(bins) - 1)
        for d in depths
            for bi in 1:(length(bins)-1)
                if d >= bins[bi] && d < bins[bi+1]
                    bin_cnts[bi] += 1; break
                end
            end
        end
        @printf("    Closure-depth histogram:\n")
        @printf("      %12s  %7s  %7s\n", "depth range", "count", "frac%")
        for bi in 1:length(bin_cnts)
            @printf("      %12s  %7d  %7.2f%%\n",
                    bin_names[bi], bin_cnts[bi], 100.0 * bin_cnts[bi] / nd)
        end

        @printf("    Hazard h(band) = P(close in band | survived to band start):\n")
        @printf("      %12s  %7s  %7s  %7s\n", "band", "closed", "survived", "h(band)")
        surviving = nd
        for bi in 1:length(bin_cnts)
            closed_in_band = bin_cnts[bi]
            h = surviving > 0 ? closed_in_band / surviving : 0.0
            @printf("      %12s  %7d  %7d  %7.4f%s\n",
                    bin_names[bi], closed_in_band, surviving,
                    h, h > 0.5 ? "  ← dominant" : "")
            surviving -= closed_in_band
        end

        if nd >= 8
            μd  = d_mean
            cov_d = sum((depths[i] - μd) * (depths[i+1] - μd)
                        for i in 1:(nd-1)) / (nd - 1)
            var_d = nd > 1 ? sum((x - μd)^2 for x in depths) / nd : 1.0
            acf1_d = var_d > 0 ? cov_d / var_d : 0.0
            @printf("    Depth ACF(1)                   : %.4f  %s\n", acf1_d,
                    acf1_d > 0.15  ? "← POSITIVE: consecutive depths correlated (basin memory)" :
                    acf1_d < -0.15 ? "← NEGATIVE: depth alternates (repulsion between long closures)" :
                    "(≈ uncorrelated)")
        end

        band_of(d) = d < 20 ? 1 : d < 150 ? 2 : 3
        band_names = ["short(<20)", "med(20-150)", "long(≥150)"]
        trans_bd = zeros(Int, 3, 3)
        for i in 1:(nd-1)
            bf = band_of(depths[i])
            bt = band_of(depths[i+1])
            trans_bd[bf, bt] += 1
        end
        @printf("    Depth-band transition matrix (rows=from, cols=to):\n")
        @printf("      %12s  %12s  %12s  %12s\n", "from\\to", band_names[1], band_names[2], band_names[3])
        for r in 1:3
            row_sum = sum(trans_bd[r, :])
            if row_sum > 0
                @printf("      %12s  %12.3f  %12.3f  %12.3f\n",
                        band_names[r],
                        trans_bd[r,1]/row_sum, trans_bd[r,2]/row_sum, trans_bd[r,3]/row_sum)
            end
        end

        @printf("    Depth-conditioned key entropy H(bucket | depth band):\n")
        @printf("      %12s  %7s  %7s  %8s\n", "band", "n", "H(bits)", "H/H_max")
        close_bkt = deep_stat.d8_close_bkt
        for (bi, bname) in enumerate(band_names)
            band_bkts = Int[]
            for ci in 1:nd
                band_of(depths[ci]) == bi && push!(band_bkts, Int(close_bkt[ci]))
            end
            nb_band = length(band_bkts)
            nb_band < 2 && continue
            cnt_b = Dict{Int,Int}()
            for b in band_bkts; cnt_b[b] = get(cnt_b, b, 0) + 1; end
            H_band = -sum((c/nb_band)*log2(c/nb_band) for c in values(cnt_b))
            H_max  = log2(Float64(DEEP_DIAG_N_BUCKETS))
            @printf("      %12s  %7d  %7.4f  %8.4f\n", bname, nb_band, H_band, H_max > 0 ? H_band/H_max : 0.0)
        end

        @printf("    Depth-conditioned collision entropy α₂(bucket | depth band):\n")
        @printf("      %12s  %7s  %10s  %s\n", "band", "n", "α₂ (bits)", "interpretation")
        for (bi, bname) in enumerate(band_names)
            band_bkts = Int[]
            for ci in 1:nd
                band_of(depths[ci]) == bi && push!(band_bkts, Int(close_bkt[ci]))
            end
            nb_band = length(band_bkts)
            nb_band < 2 && continue
            cnt_b = Dict{Int,Int}()
            for b in band_bkts; cnt_b[b] = get(cnt_b, b, 0) + 1; end
            p2sum = sum((c/nb_band)^2 for c in values(cnt_b))
            a2_band = p2sum > 0 ? -log2(p2sum) : NaN
            interp = isnan(a2_band) ? "—" :
                     a2_band < 4.0  ? "← VERY LOW: tiny support (high concentration)" :
                     a2_band < 7.0  ? "← low-moderate" :
                     a2_band < 9.0  ? "← near-uniform in active set" :
                     "← near-uniform over full bucket space"
            @printf("      %12s  %7d  %10.4f  %s\n", bname, nb_band, a2_band, interp)
        end

        close_abkt = deep_stat.d8_close_abkt
        N_ABKT_COARSE = 8
        abkt_depths = [Int[] for _ in 1:N_ABKT_COARSE]
        if !isempty(close_abkt)
            max_abkt = maximum(Int.(close_abkt))
            for ci in 1:nd
                ab = Int(close_abkt[ci])
                coarse = clamp(1 + (ab * N_ABKT_COARSE) ÷ (max_abkt + 1), 1, N_ABKT_COARSE)
                push!(abkt_depths[coarse], depths[ci])
            end
            @printf("    Lyapunov proxy — depth std dev by a-bucket band (8 coarse bands):\n")
            @printf("      %8s  %7s  %9s  %9s\n", "a-band", "n", "mean_d", "std_d")
            for ab in 1:N_ABKT_COARSE
                v = abkt_depths[ab]
                length(v) < 2 && continue
                μ_ab = sum(v) / length(v)
                σ_ab = sqrt(sum((x - μ_ab)^2 for x in v) / (length(v)-1))
                @printf("      %8d  %7d  %9.1f  %9.1f\n", ab, length(v), μ_ab, σ_ab)
            end
        end

        @label d8_done
    end

    # ──────────────────────────────────────────────────────────────────────
    #  D9 — H(step opcode | recent LP1-conj)
    # ──────────────────────────────────────────────────────────────────────
    @printf("\n  D9 — H(step opcode | recent LP1-conj)\n")
    @printf("  ─────────────────────────────────────────────────────────────────\n")
    let
        n_op = length(deep_stat.opcode_log)
        if n_op < 20
            @printf("    (opcode log too short: %d steps — check record_conj_deep_opcode! wiring)\n", n_op)
        else
            opcodes   = deep_stat.opcode_log
            is_lp1c   = deep_stat.opcode_is_lp1c
            opcode_names = ["0-LP", "1LP-aff", "1LP-conj", "2LP-aff", "2LP-conj", "skip"]
            N_OPCODES = 6

            for (τ_win_label, τ_win) in (("τ*=128", 128), ("τ_long=512", 512))
                cnt_window   = zeros(Int, N_OPCODES)
                cnt_baseline = zeros(Int, N_OPCODES)
                last_lp1c    = -typemax(Int)
                for i in 1:n_op
                    is_lp1c[i] && (last_lp1c = i)
                    in_win = (i - last_lp1c) <= τ_win && last_lp1c > 0
                    opc = Int(opcodes[i]) + 1
                    1 <= opc <= N_OPCODES || continue
                    if in_win
                        cnt_window[opc] += 1
                    else
                        cnt_baseline[opc] += 1
                    end
                end

                n_win  = sum(cnt_window)
                n_base = sum(cnt_baseline)

                _ent(cnt) = begin
                    n = sum(cnt)
                    n == 0 && return 0.0
                    -sum((c / n) * log2(max(1e-300, c / n)) for c in cnt if c > 0)
                end

                H_win  = _ent(cnt_window)
                H_base = _ent(cnt_baseline)

                @printf("    Window %s  (n_win=%d  n_base=%d):\n", τ_win_label, n_win, n_base)
                @printf("      H(opcode | in_window)  : %.4f bits\n", H_win)
                @printf("      H(opcode | baseline)   : %.4f bits\n", H_base)
                Δ = H_base - H_win
                @printf("      ΔH = H_base − H_win    : %+.4f bits  %s\n", Δ,
                        Δ > 0.3  ? "← ENTROPY COLLAPSE: walk constrained post-emission" :
                        Δ > 0.1  ? "← moderate constraint post-emission" :
                        Δ < -0.1 ? "← entropy INCREASE post-emission (diversification)" :
                        "(≈ no change)")
                @printf("      %12s  %8s  %8s  %8s\n", "opcode", "P_win", "P_base", "lift")
                for k in 1:N_OPCODES
                    p_w = n_win  > 0 ? cnt_window[k]   / n_win  : 0.0
                    p_b = n_base > 0 ? cnt_baseline[k] / n_base : 0.0
                    lift = p_b > 1e-12 ? p_w / p_b : (p_w > 0 ? Inf : 1.0)
                    @printf("      %12s  %8.5f  %8.5f  %8.3f  %s\n",
                            opcode_names[k], p_w, p_b, lift,
                            lift > 2.0 ? "← OVER-REPRESENTED in window" :
                            lift < 0.5 ? "← SUPPRESSED in window" : "")
                end
                println()
            end
        end
    end

    # ──────────────────────────────────────────────────────────────────────
    #  D11 — Branch-conditioned α₂ and step-opcode traffic analysis
    # ──────────────────────────────────────────────────────────────────────
    @printf("\n  D11 — Branch-conditioned α₂ and step-opcode traffic analysis\n")
    @printf("  ─────────────────────────────────────────────────────────────────\n")
    let
        n_op = length(deep_stat.opcode_log)
        blog = phi_stat.lp1_conj_key_blog
        n_blog = length(blog)

        opcode_names = ["0-LP", "1LP-aff", "1LP-conj", "2LP-aff", "2LP-conj", "skip"]
        N_OPCODES = 6

        if n_op < 10
            @printf("    (opcode log too short: %d steps)\n", n_op)
        else
            opc_count = zeros(Int, N_OPCODES)
            opc_emit  = zeros(Int, N_OPCODES)
            for i in 1:n_op
                k = Int(deep_stat.opcode_log[i]) + 1
                1 <= k <= N_OPCODES && (opc_count[k] += 1)
                deep_stat.opcode_is_lp1c[i] && k == 3 && (opc_emit[3] += 1)
            end
            total_steps = sum(opc_count)
            total_emit  = sum(opc_emit)

            @printf("    Step-opcode traffic distribution (n=%d valid phi steps):\n", total_steps)
            @printf("      %12s  %8s  %8s  %8s\n", "opcode", "count", "share%", "emit_lift")
            for k in 1:N_OPCODES
                share = total_steps > 0 ? opc_count[k] / total_steps : 0.0
                emit_frac = total_emit > 0 ? opc_emit[k] / total_emit : 0.0
                lift = share > 1e-12 ? emit_frac / share : (emit_frac > 0 ? Inf : 0.0)
                @printf("      %12s  %8d  %8.3f%%  %8.3f  %s\n",
                        opcode_names[k], opc_count[k], 100.0 * share, lift,
                        k == 3 && lift > 0 ? "(by definition)" : "")
            end
            println()
        end

        if n_blog >= 8
            half = n_blog ÷ 2
            function _alpha2_blog(slice::AbstractVector{UInt16})
                n = length(slice)
                n == 0 && return NaN
                cnt = Dict{UInt16, Int}()
                for b in slice; cnt[b] = get(cnt, b, 0) + 1; end
                p2 = sum((c / n)^2 for c in values(cnt))
                p2 > 0 ? -log2(p2) : NaN
            end
            a2_first  = _alpha2_blog(blog[1:half])
            a2_second = _alpha2_blog(blog[half+1:end])
            a2_all    = _alpha2_blog(blog)
            Δa2 = a2_second - a2_first

            @printf("    LP1-conj key_blog α₂ stationarity (n=%d partials):\n", n_blog)
            @printf("      α₂ (full)        : %.4f bits\n", a2_all)
            @printf("      α₂ (first half)  : %.4f bits\n", a2_first)
            @printf("      α₂ (second half) : %.4f bits\n", a2_second)
            @printf("      Δα₂ (2nd − 1st)  : %+.4f bits  %s\n", Δa2,
                    abs(Δa2) > 1.0 ? "← NON-STATIONARY: key geometry changing over run" :
                    abs(Δa2) > 0.3 ? "← moderate drift" :
                    "(≈ stationary)")
            println()

            if n_blog >= 16
                q = n_blog ÷ 4
                @printf("    Per-quartile α₂:\n")
                @printf("      %6s  %8s  %8s\n", "qrt", "n", "α₂")
                for qi in 1:4
                    lo = (qi - 1) * q + 1
                    hi = qi == 4 ? n_blog : qi * q
                    a2q = _alpha2_blog(blog[lo:hi])
                    @printf("      %6d  %8d  %8.4f\n", qi, hi - lo + 1, a2q)
                end
            end
        else
            @printf("    (key_blog too short for α₂ stationarity: %d partials)\n", n_blog)
        end
    end
end
