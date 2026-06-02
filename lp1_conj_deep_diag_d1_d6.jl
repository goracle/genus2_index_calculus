# =============================================================================
#  lp1_conj_deep_diag_d1_d6.jl
#
#  LP1-conj deep diagnostic sections D1 – D6.
#
#  D1 — Recurrence fingerprinting
#  D2 — Conditional collision entropy H₂(X_t | X_{t-1})
#  D3 — Branch ancestry clustering
#  D4 — Burst persistence / Jacobian linearization proxy
#  D5 — Multiplicity collapse (Zipf / Gini / Hill)
#  D6 — Emission-conditioned return maps
#
#  Included by lp1_conj_deep_diag.jl; do not include directly.
#  All functions declared here receive (phi_stat, deep_stat, arrivals,
#  keys_u128, emit_bkt, n_emit) via the caller's local bindings.
# =============================================================================

function _report_d1_d6(phi_stat ::PhiBiasStat,
                        deep_stat::ConjDeepStat,
                        arrivals ::Vector{Int},
                        keys_u128::Vector{UInt128},
                        emit_bkt ::Vector{Int},
                        n_emit   ::Int)

    # ──────────────────────────────────────────────────────────────────────
    #  D1 — Recurrence fingerprinting
    # ──────────────────────────────────────────────────────────────────────
    @printf("\n  D1 — Recurrence fingerprinting\n")
    @printf("  ─────────────────────────────────────────────────────────────────\n")
    let
        # Map each key to its emission indices (in sorted order).
        key_to_indices = Dict{UInt128, Vector{Int}}()
        sizehint!(key_to_indices, min(n_emit, 4096))
        for (i, k) in enumerate(keys_u128)
            v = get!(key_to_indices, k, Int[])
            push!(v, i)
        end

        # Build recurrence-time histogram (in units of emissions, not steps).
        max_tau = min(200, n_emit ÷ 4)
        rec_hist = zeros(Int, max(1, max_tau))
        n_returns = 0
        for (_, idxs) in key_to_indices
            length(idxs) < 2 && continue
            for j in 2:length(idxs)
                τ = idxs[j] - idxs[j-1]
                if 1 <= τ <= max_tau
                    rec_hist[τ] += 1
                    n_returns += 1
                end
            end
        end

        @printf("    Distinct keys emitted          : %d  (%.1f%% of %d)\n",
                length(key_to_indices), 100.0 * length(key_to_indices) / n_emit, n_emit)
        @printf("    Keys with ≥2 emissions         : %d\n",
                count(v -> length(v) >= 2, values(key_to_indices)))
        @printf("    Total same-key recurrences     : %d\n", n_returns)

        if n_returns > 0
            rtimes = Int[]
            for (_, idxs) in key_to_indices
                for j in 2:length(idxs)
                    push!(rtimes, idxs[j] - idxs[j-1])
                end
            end
            μ_r   = sum(rtimes) / length(rtimes)
            var_r = length(rtimes) < 2 ? 0.0 :
                    sum((x - μ_r)^2 for x in rtimes) / (length(rtimes) - 1)
            cv_r  = μ_r > 0 ? sqrt(var_r) / μ_r : NaN
            @printf("    Recurrence-time (in emissions): mean=%.2f  CV=%.3f\n", μ_r, cv_r)
            if cv_r > 1.5
                @printf("      ↑ CV > 1.5: HIGHLY BURSTY recurrences (algebraic attractor suspected)\n")
            elseif cv_r > 1.0
                @printf("      ↑ CV > 1.0: moderately bursty recurrences\n")
            else
                @printf("      ↑ CV ≤ 1.0: recurrences roughly geometric (Poisson-like)\n")
            end

            if length(rtimes) >= 4
                n_r = length(rtimes)
                μ2  = μ_r
                cov = sum((rtimes[i] - μ2) * (rtimes[i+1] - μ2)
                          for i in 1:n_r-1) / (n_r - 1)
                var2 = sum((x - μ2)^2 for x in rtimes) / n_r
                acf1 = var2 > 0 ? cov / var2 : 0.0
                @printf("    Recurrence-time ACF(1)         : %.4f  %s\n", acf1,
                        acf1 > 0.2 ? "← POSITIVE: recurrence times cluster (burst epochs)" :
                        acf1 < -0.2 ? "← NEGATIVE: recurrences alternate short/long" :
                        "(≈ uncorrelated)")
            end
        end

        τ_wins = [1, 2, 5, 10, 20, 50]
        @printf("    Burst conditional prob P(same within τ | same previously):\n")
        @printf("      %5s  %8s  %8s  %8s\n", "τ", "P_obs", "P_null", "lift")
        n_per_key  = [length(v) for v in values(key_to_indices)]
        p_null_num = sum(c*(c-1) for c in n_per_key; init=0)
        p_null_den = n_emit * (n_emit - 1)
        P_null_sk  = p_null_den > 0 ? p_null_num / p_null_den : 0.0
        for τ_win in τ_wins
            τ_win >= max_tau && continue
            n_cond = n_returns == 0 ? 0 :
                     count(τ -> τ <= τ_win, [idxs[j] - idxs[j-1]
                                             for (_, idxs) in key_to_indices
                                             for j in 2:length(idxs)])
            p_obs  = n_returns > 0 ? n_cond / n_returns : 0.0
            p_null = min(1.0, τ_win * P_null_sk)
            lift   = p_null > 1e-12 ? p_obs / p_null : (p_obs > 0 ? Inf : 1.0)
            @printf("      %5d  %8.5f  %8.5f  %8.3f  %s\n", τ_win, p_obs, p_null, lift,
                    lift > 3.0 ? "← STRONG burst attractor" :
                    lift > 1.5 ? "← moderate burst attractor" :
                    "(≈ random)")
        end
    end

    # ──────────────────────────────────────────────────────────────────────
    #  D2 — Conditional collision entropy H₂(X_t | X_{t-1})
    # ──────────────────────────────────────────────────────────────────────
    @printf("\n  D2 — Conditional collision entropy H₂(X_t | X_{{t-1}})\n")
    @printf("  ─────────────────────────────────────────────────────────────────\n")
    let
        nb  = DEEP_DIAG_N_BUCKETS
        T_mat = deep_stat.n_trans

        row_totals = [Int(sum(T_mat[i, :])) for i in 1:nb]
        grand_total = sum(row_totals)

        if grand_total < 4
            @printf("    (insufficient transition data: %d transitions)\n", grand_total)
        else
            p_marg = [row_totals[i] / grand_total for i in 1:nb]
            H2_marginal = -log2(max(1e-300, sum(x^2 for x in p_marg)))

            H2_cond_sum = 0.0
            for i in 1:nb
                rt = row_totals[i]
                rt == 0 && continue
                if rt == 1
                    H2_cond_sum += p_marg[i] * 1.0
                else
                    row_sq = sum(Float64(T_mat[i, j])^2 for j in 1:nb)
                    H2_cond_sum += p_marg[i] * (row_sq / (Float64(rt)^2))
                end
            end
            H2_conditional = -log2(max(1e-300, H2_cond_sum))

            red = H2_marginal - H2_conditional
            rel_red = H2_marginal > 0 ? red / H2_marginal : 0.0

            @printf("    Transitions analyzed           : %d\n", grand_total)
            @printf("    Coarse buckets                 : %d  (%d bits)\n",
                    nb, DEEP_DIAG_BUCKET_BITS)
            @printf("    H₂(X)    marginal entropy      : %.4f bits\n", H2_marginal)
            @printf("    H₂(X|X₋₁) conditional entropy  : %.4f bits\n", H2_conditional)
            @printf("    Reduction (H₂ − H₂|cond)       : %.4f bits  (%.1f%%)\n",
                    red, 100 * rel_red)
            if rel_red > 0.20
                @printf("    ↑ >20%% reduction: STRONG dynamical state persistence\n")
                @printf("      → emission process retains predictive information across steps.\n")
            elseif rel_red > 0.05
                @printf("    ↑ 5-20%% reduction: moderate persistence (weak algebraic channel)\n")
            else
                @printf("    ↑ <5%% reduction: bursts are mostly independent repeats (no channel)\n")
            end

            if n_emit >= 2 * DEEP_DIAG_COND_ENT_LAG
                @printf("    Lag-k conditional collision entropy (from full emission sequence):\n")
                @printf("      %4s  %10s  %10s  %8s\n", "lag", "H₂(X|X₋ₖ)", "H₂(X)", "reduction%")
                for lag in 1:DEEP_DIAG_COND_ENT_LAG
                    pairs_by_from = Dict{Int,Vector{Int}}()
                    for t in (lag+1):n_emit
                        from_bkt = emit_bkt[t - lag]
                        v = get!(pairs_by_from, from_bkt, Int[])
                        push!(v, emit_bkt[t])
                    end
                    n_pairs = n_emit - lag
                    p_from  = Dict(k => length(v)/n_pairs for (k, v) in pairs_by_from)
                    cond_coll = 0.0
                    for (from_bkt, tos) in pairs_by_from
                        ntos = length(tos)
                        cnt = Dict{Int,Int}()
                        for b in tos; cnt[b] = get(cnt, b, 0) + 1; end
                        row_c2 = sum(c^2 for c in values(cnt)) / (ntos^2)
                        cond_coll += get(p_from, from_bkt, 0.0) * row_c2
                    end
                    H2_c = -log2(max(1e-300, cond_coll))
                    rr   = H2_marginal > 0 ? (H2_marginal - H2_c) / H2_marginal : 0.0
                    @printf("      %4d  %10.4f  %10.4f  %8.1f%%\n",
                            lag, H2_c, H2_marginal, 100 * rr)
                end
            end
        end
    end

    # ──────────────────────────────────────────────────────────────────────
    #  D3 — Branch ancestry clustering
    # ──────────────────────────────────────────────────────────────────────
    @printf("\n  D3 — Branch ancestry clustering\n")
    @printf("  ─────────────────────────────────────────────────────────────────\n")
    let
        n_anc = length(deep_stat.ancestry_log_a)
        if n_anc < 10
            @printf("    (ancestry log too short: %d entries)\n", n_anc)
        else
            sig_counts = Dict{UInt64, Int}()
            for i in 1:n_anc
                a_b = UInt64(deep_stat.ancestry_log_a[i])
                par = UInt64(deep_stat.ancestry_log_parity[i])
                kh  = UInt64(deep_stat.ancestry_log_keyhash[i])
                sig = ((a_b >> 2) & 0x3f) | (par << 6) | ((kh >> 22) << 8)
                sig_counts[sig] = get(sig_counts, sig, 0) + 1
            end

            top_k = 10
            sorted_sigs = sort(collect(sig_counts), by = x -> -x[2])
            total_anc   = sum(values(sig_counts))
            n_sig       = length(sig_counts)

            @printf("    Ancestry entries              : %d\n", n_anc)
            @printf("    Distinct ancestry signatures  : %d  (coarsened: 6 a-bits + 2 parity + 10 key-bits)\n", n_sig)

            cumulative = 0
            @printf("    Top-%d ancestry motifs by emission count:\n", top_k)
            @printf("      %5s  %8s  %8s  %8s\n", "rank", "count", "share%", "cumul%")
            for (rank, (sig, cnt)) in enumerate(sorted_sigs[1:min(top_k, end)])
                cumulative += cnt
                @printf("      %5d  %8d  %8.2f%%  %8.2f%%\n",
                        rank, cnt,
                        100.0 * cnt / total_anc,
                        100.0 * cumulative / total_anc)
            end

            top1_share  = sorted_sigs[1][2] / total_anc
            top10_share = sum(x[2] for x in sorted_sigs[1:min(10, end)]) / total_anc
            @printf("    Top-1  motif mass             : %.2f%%\n", 100 * top1_share)
            @printf("    Top-10 motif mass             : %.2f%%\n", 100 * top10_share)
            if top10_share > 0.5
                @printf("    ↑ >50%% in top-10 motifs: FEW TRANSITION FAMILIES drive most emissions\n")
                @printf("      → reconciles high support + low α₂ + weak geometric bias.\n")
            elseif top10_share > 0.25
                @printf("    ↑ 25-50%%: moderate ancestry concentration\n")
            else
                @printf("    ↑ <25%%: ancestry fairly spread — no dominant transition family\n")
            end
        end
    end

    # ──────────────────────────────────────────────────────────────────────
    #  D4 — Burst persistence / Jacobian linearization proxy
    # ──────────────────────────────────────────────────────────────────────
    @printf("\n  D4 — Burst persistence / Jacobian linearization proxy\n")
    @printf("  ─────────────────────────────────────────────────────────────────\n")
    let
        if n_emit < 4
            @printf("    (need ≥ 4 emissions; got %d)\n", n_emit)
        else
            arr_sorted = sort(arrivals)
            gaps = [arr_sorted[i] - arr_sorted[i-1] for i in 2:n_emit]
            μ_gap = sum(gaps) / length(gaps)
            λ_base = μ_gap > 0 ? 1.0 / μ_gap : 0.0

            τ_grid = [1, 2, 5, 10, 20, 50, 100, 200, 500]
            @printf("    Mean inter-arrival gap         : %.2f steps\n", μ_gap)
            @printf("    C(τ) = P(next hit within τ steps):\n")
            @printf("      %5s  %8s  %8s  %8s\n", "τ", "C_obs", "C_null(Poisson)", "lift")
            n_gaps = length(gaps)
            for τ in τ_grid
                c_obs  = count(<=(τ), gaps) / n_gaps
                c_null = 1.0 - exp(-λ_base * τ)
                lift   = c_null > 1e-6 ? c_obs / c_null : (c_obs > 0 ? Inf : 1.0)
                @printf("      %5d  %8.5f  %8.5f  %8.3f  %s\n", τ, c_obs, c_null, lift,
                        lift > 2.0 ? "← PERSISTENT algebraic channel" :
                        lift > 1.3 ? "← moderate persistence" :
                        lift < 0.7 ? "← CHAOTIC (burst destroys next hit)" :
                        "(≈ Poisson)")
            end

            persist_score = let
                τ_pts = [1, 2, 5, 10, 20, 50, 100]
                lifts  = Float64[]
                for τ in τ_pts
                    c_obs  = count(<=(τ), gaps) / n_gaps
                    c_null = 1.0 - exp(-λ_base * τ)
                    push!(lifts, c_null > 1e-6 ? c_obs / c_null : 1.0)
                end
                sum(lifts) / length(lifts)
            end
            @printf("    Persistence score (mean lift)  : %.4f  %s\n", persist_score,
                    persist_score > 1.5 ? "← GENUINE algebraic channels" :
                    persist_score > 1.1 ? "← mild persistence" :
                    persist_score < 0.8 ? "← CHAOTIC: bursts are coincidence artifacts" :
                    "(≈ Poisson / no structure)")
        end
    end

    # ──────────────────────────────────────────────────────────────────────
    #  D5 — Multiplicity collapse (Zipf / Gini / Hill)
    # ──────────────────────────────────────────────────────────────────────
    @printf("\n  D5 — Multiplicity collapse (Zipf / Gini / Hill)\n")
    @printf("  ─────────────────────────────────────────────────────────────────\n")
    let
        key_counts = Dict{UInt128, Int}()
        for k in keys_u128; key_counts[k] = get(key_counts, k, 0) + 1; end

        mult = sort(collect(values(key_counts)), rev=true)
        n_k  = length(mult)
        total_emits = sum(mult)

        @printf("    Distinct keys                  : %d\n", n_k)
        @printf("    Total emissions                : %d\n", total_emits)
        if n_k == 0 || total_emits == 0
            @printf("    (no data)\n")
        else
            @printf("    Max / median multiplicity      : %d / %.1f\n",
                    mult[1], mult[clamp(n_k ÷ 2, 1, n_k)])

            gini = _gini(collect(values(key_counts)))
            @printf("    Gini coefficient               : %.4f  %s\n", gini,
                    gini > 0.7 ? "← EXTREME concentration (tiny set dominates)" :
                    gini > 0.4 ? "← moderate concentration" :
                    "← fairly uniform")

            for frac in [0.001, 0.01, 0.05, 0.10]
                share = _top_share(collect(values(key_counts)), frac)
                k_count = max(1, round(Int, frac * n_k))
                @printf("    Top %.1f%% of keys (%d keys)      : %.2f%% of emissions\n",
                        100*frac, k_count, 100*share)
            end

            hill_k = min(50, n_k - 1)
            if hill_k >= 2
                if mult[1] == 1
                    @printf("    Hill exponent α̂ (k=%d)         : undefined (all multiplicities = 1, no tail structure)\n",
                            hill_k)
                else
                    α_hill = _hill_exponent(mult; k=hill_k)
                    @printf("    Hill exponent α̂ (k=%d)         : %.3f  %s\n",
                            hill_k, α_hill,
                            α_hill < 1.5 ? "← HEAVY TAIL (α<1.5: power-law multiplicity)" :
                            α_hill < 3.0 ? "← moderate tail" :
                            "← thin tail (quasi-geometric)")
                end
            end

            top_n = min(100, n_k)
            if top_n >= 5
                log_ranks  = [log(Float64(i)) for i in 1:top_n]
                log_counts = [log(Float64(mult[i])) for i in 1:top_n]
                μ_lr, μ_lc = sum(log_ranks)/top_n, sum(log_counts)/top_n
                cov_num = sum((log_ranks[i]-μ_lr)*(log_counts[i]-μ_lc) for i in 1:top_n)
                var_den = sum((log_ranks[i]-μ_lr)^2 for i in 1:top_n)
                zipf_slope = var_den > 0 ? cov_num / var_den : NaN
                @printf("    Zipf log-log slope (top-%d)     : %.4f  %s\n",
                        top_n, zipf_slope,
                        !isnan(zipf_slope) && zipf_slope < -0.8 ?
                            "← Zipf-like rank-frequency (algebraic structure)" :
                        !isnan(zipf_slope) && zipf_slope > -0.3 ?
                            "← flat rank-frequency (uniform keys)" :
                        "← intermediate")
            end
        end
    end

    # ──────────────────────────────────────────────────────────────────────
    #  D6 — Emission-conditioned return maps
    # ──────────────────────────────────────────────────────────────────────
    @printf("\n  D6 — Emission-conditioned return maps (emission-index space)\n")
    @printf("  ─────────────────────────────────────────────────────────────────\n")
    let
        n_emit < 4 && (@printf("    (need ≥ 4 emissions)\n"); @goto d6_done)

        trans_cnt = Dict{Tuple{Int,Int}, Int}()
        for i in 2:n_emit
            b_from = emit_bkt[i-1]
            b_to   = emit_bkt[i]
            k = (b_from, b_to)
            trans_cnt[k] = get(trans_cnt, k, 0) + 1
        end

        n_trans_total = n_emit - 1
        p_joint = Dict((k[1], k[2]) => v / n_trans_total for (k, v) in trans_cnt)
        p_from  = Dict{Int,Float64}()
        for ((b_f, _), p) in p_joint
            p_from[b_f] = get(p_from, b_f, 0.0) + p
        end

        marginal_cnt = Dict{Int,Int}()
        for b in emit_bkt; marginal_cnt[b] = get(marginal_cnt, b, 0) + 1; end
        H_marg = -sum((c/n_emit)*log2(c/n_emit) for c in values(marginal_cnt))

        H_joint  = -sum(p * log2(max(1e-300, p)) for p in values(p_joint))
        H_from   = -sum(p * log2(max(1e-300, p)) for p in values(p_from))
        H_cond_e = H_joint - H_from

        @printf("    Active (from,to) pairs         : %d\n", length(trans_cnt))
        @printf("    H(X_t) marginal emission entropy: %.4f bits\n", H_marg)
        @printf("    H(X_t|X_{{t-1}}) in emission space: %.4f bits\n", H_cond_e)
        @printf("    Effective automaton size        : 2^%.2f ≈ %.1f states\n",
                H_cond_e, 2.0^H_cond_e)

        n_self = sum(v for ((f,t), v) in trans_cnt if f == t; init=0)
        @printf("    Self-loop fraction              : %.4f  (%.1f%% of transitions)\n",
                n_self / n_trans_total, 100.0 * n_self / n_trans_total)

        active_buckets = sort(collect(keys(marginal_cnt)), by=b->-marginal_cnt[b])[1:min(100, end)]
        bkt_set = Set(active_buckets)
        parent = Dict{Int,Int}(b => b for b in active_buckets)
        function uf_find(x); while parent[x] != x; parent[x] = parent[parent[x]]; x = parent[x] end; x end
        function uf_union(x, y); rx, ry = uf_find(x), uf_find(y); rx != ry && (parent[rx] = ry); end
        for ((f, t), _) in trans_cnt
            (f in bkt_set && t in bkt_set) && uf_union(f, t)
        end
        root_sizes = Dict{Int,Int}()
        for b in active_buckets
            r = uf_find(b)
            root_sizes[r] = get(root_sizes, r, 0) + 1
        end
        scc_sizes = sort(collect(values(root_sizes)), rev=true)
        @printf("    Top active buckets analyzed     : %d\n", length(active_buckets))
        @printf("    Strongly-connected component sizes (top 5): %s\n",
                join(string.(scc_sizes[1:min(5,end)]), ", "))
        if length(scc_sizes) == 1
            @printf("    ↑ Single giant SCC: emission process is strongly connected\n")
        else
            n_singletons = count(==(1), scc_sizes)
            @printf("    ↑ %d SCCs (%d singletons): %s\n",
                    length(scc_sizes), n_singletons,
                    length(scc_sizes) <= 3 ? "few large components — structured automaton" :
                    "fragmented — emission lives on multiple disjoint fibers")
        end

        @label d6_done
    end
end
