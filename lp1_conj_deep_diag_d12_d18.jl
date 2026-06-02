# =============================================================================
#  lp1_conj_deep_diag_d12_d18.jl
#
#  LP1-conj deep diagnostic sections D12 – D18.
#
#  D12 — Alpha/anchor joint support diagnostic
#  D13 — Mumford coordinate support cardinality
#  D14 — Conditional entropy H(a | px_bucket)
#  D15 — Residual support ratio conditioned on px_bucket
#  D16 — Pre-burst state fingerprinting
#  D17 — LP1-conj lifetime multiplicity analysis
#  D18 — u1+px Vieta sum cardinality at close events
#
#  Included by lp1_conj_deep_diag.jl; do not include directly.
# =============================================================================

function _report_d12_d18(deep_stat::ConjDeepStat; p::Int = 0)

    # ──────────────────────────────────────────────────────────────────────
    #  D12 — Alpha/anchor joint support diagnostic
    # ──────────────────────────────────────────────────────────────────────
    @printf("\n  D12 — Alpha/anchor joint support diagnostic\n")
    @printf("  ─────────────────────────────────────────────────────────────────\n")
    let
        n_store = length(deep_stat.d12_store_alpha)
        n_close = length(deep_stat.d12_close_alpha)
        @printf("    D12 store events recorded      : %d\n", n_store)
        @printf("    D12 close events recorded      : %d\n", n_close)

        if n_store < 4
            @printf("    (too few store events for D12 — skipping)\n")
            @goto d12_done
        end

        n_abkt = clamp(isqrt(max(1, n_store)), 8, 64)
        n_pbkt = clamp(isqrt(max(1, n_store)), 8, 64)

        alpha_max = max(1, maximum(deep_stat.d12_store_alpha; init=1))
        px_max    = max(1, maximum(deep_stat.d12_store_px;    init=1))
        if n_close > 0
            alpha_max = max(alpha_max, maximum(deep_stat.d12_close_alpha; init=1))
            px_max    = max(px_max,    maximum(deep_stat.d12_close_px;    init=1))
        end

        function _abkt(a::Int)::Int
            clamp(1 + (a * n_abkt) ÷ (alpha_max + 1), 1, n_abkt)
        end
        function _pbkt(px_val::Int)::Int
            clamp(1 + (px_val * n_pbkt) ÷ (px_max + 1), 1, n_pbkt)
        end

        # ── 2-D histogram of store events ─────────────────────────────────
        hist2d_store = zeros(Int, n_abkt, n_pbkt)
        @inbounds for i in 1:n_store
            ab = _abkt(deep_stat.d12_store_alpha[i])
            pb = _pbkt(deep_stat.d12_store_px[i])
            hist2d_store[ab, pb] += 1
        end
        n_cells  = n_abkt * n_pbkt
        expected = Float64(n_store) / n_cells
        chi2_store = expected > 0 ?
            sum((Float64(hist2d_store[i,j]) - expected)^2 / expected
                for i in 1:n_abkt, j in 1:n_pbkt) : NaN
        dof_store = n_cells - 1

        @printf("    2-D histogram (alpha_bkt × px_bkt) of STORE events:\n")
        @printf("      grid: %d × %d  (α_range=[0,%d], px_range=[0,%d])\n",
                n_abkt, n_pbkt, alpha_max, px_max)
        @printf("      χ²/dof (vs uniform): %.3f  (dof=%d; uniform expected ≈ %.1f)\n",
                chi2_store / dof_store, dof_store, Float64(dof_store))
        if chi2_store / dof_store > 2.0
            @printf("      ↑ χ²/dof >> 1: CONCENTRATED — (alpha,px) space is not flat\n")
        elseif chi2_store / dof_store > 1.3
            @printf("      ↑ χ²/dof moderately elevated: mild concentration\n")
        else
            @printf("      (≈ uniform: no strong 2-D concentration detected)\n")
        end

        all_cells = vec([(hist2d_store[i,j], i, j) for i in 1:n_abkt, j in 1:n_pbkt])
        sort!(all_cells, rev=true)
        @printf("      Top-5 hottest (alpha_bkt, px_bkt, count):\n")
        for (cnt, ab, pb) in all_cells[1:min(5, end)]
            a_lo = (ab-1) * (alpha_max+1) ÷ n_abkt
            a_hi = ab     * (alpha_max+1) ÷ n_abkt - 1
            p_lo = (pb-1) * (px_max+1)    ÷ n_pbkt
            p_hi = pb     * (px_max+1)    ÷ n_pbkt - 1
            @printf("        α∈[%d,%d)  px∈[%d,%d)  count=%d  (expected=%.1f  lift=%.2f)\n",
                    a_lo, a_hi, p_lo, p_hi, cnt, expected, expected > 0 ? cnt/expected : 0.0)
        end

        # ── Mutual information I(alpha_bucket; px_bucket) for stores ──────
        marginal_a = [sum(hist2d_store[i, j] for j in 1:n_pbkt) for i in 1:n_abkt]
        marginal_p = [sum(hist2d_store[i, j] for i in 1:n_abkt) for j in 1:n_pbkt]
        MI = 0.0
        if n_store > 0
            for i in 1:n_abkt, j in 1:n_pbkt
                c = hist2d_store[i, j]
                c == 0 && continue
                pij = Float64(c) / n_store
                pi  = Float64(marginal_a[i]) / n_store
                pj  = Float64(marginal_p[j]) / n_store
                pi > 0 && pj > 0 && (MI += pij * log2(pij / (pi * pj)))
            end
        end
        H_a = -sum(x/n_store * log2(max(x/n_store, 1e-300)) for x in marginal_a if x > 0)
        H_p = -sum(x/n_store * log2(max(x/n_store, 1e-300)) for x in marginal_p if x > 0)
        norm_MI = (min(H_a, H_p) > 0) ? MI / min(H_a, H_p) : 0.0
        @printf("    Mutual information I(alpha_bkt; px_bkt) for stores:\n")
        @printf("      I = %.4f bits  H(alpha)=%.4f  H(px)=%.4f  NMI=%.4f\n",
                MI, H_a, H_p, norm_MI)
        if norm_MI > 0.1
            @printf("      ↑ NMI > 0.1: ALPHA AND ANCHOR ARE CORRELATED — alpha·G x-support is structured\n")
        elseif norm_MI > 0.02
            @printf("      ↑ NMI mildly elevated: weak alpha/anchor correlation\n")
        else
            @printf("      (≈ independent: alpha and anchor px are not correlated at store time)\n")
        end

        # ── Paired MI on matched store→close keys: px memory ──────────────
        if n_store >= 4 && n_close >= 4
            @printf("    Paired mutual information I(px_store_bkt; px_close_bkt) on matched keys:\n")

            store_key_to_px = Dict{UInt128, Int}()
            @inbounds for i in 1:n_store
                haskey(store_key_to_px, deep_stat.d12_store_key[i]) ||
                    (store_key_to_px[deep_stat.d12_store_key[i]] = deep_stat.d12_store_px[i])
            end
            close_key_to_px = Dict{UInt128, Int}()
            @inbounds for i in 1:n_close
                haskey(close_key_to_px, deep_stat.d12_close_key[i]) ||
                    (close_key_to_px[deep_stat.d12_close_key[i]] = deep_stat.d12_close_px[i])
            end

            paired_px_store = Int[]
            paired_px_close = Int[]
            @inbounds for (k, p_store) in store_key_to_px
                p_close = get(close_key_to_px, k, -1)
                p_close < 0 && continue
                push!(paired_px_store, p_store)
                push!(paired_px_close, p_close)
            end

            n_pair_px = length(paired_px_store)
            @printf("      paired keys                 : %d\n", n_pair_px)
            if n_pair_px >= 4
                px_store_max = max(1, maximum(paired_px_store; init=1))
                px_close_max = max(1, maximum(paired_px_close; init=1))
                px_pair_max  = max(px_store_max, px_close_max)
                n_pxb        = clamp(isqrt(max(1, n_pair_px)), 8, 64)

                function _ppb(px_val::Int)::Int
                    clamp(1 + (px_val * n_pxb) ÷ (px_pair_max + 1), 1, n_pxb)
                end

                hist2d_px = zeros(Int, n_pxb, n_pxb)
                @inbounds for i in 1:n_pair_px
                    hist2d_px[_ppb(paired_px_store[i]), _ppb(paired_px_close[i])] += 1
                end

                px_marg_s = [sum(hist2d_px[i, j] for j in 1:n_pxb) for i in 1:n_pxb]
                px_marg_c = [sum(hist2d_px[i, j] for i in 1:n_pxb) for j in 1:n_pxb]
                mi_px = 0.0
                @inbounds for i in 1:n_pxb, j in 1:n_pxb
                    c = hist2d_px[i, j]
                    c == 0 && continue
                    pij = Float64(c) / n_pair_px
                    pi  = Float64(px_marg_s[i]) / n_pair_px
                    pj  = Float64(px_marg_c[j]) / n_pair_px
                    pi > 0 && pj > 0 && (mi_px += pij * log2(pij / (pi * pj)))
                end
                h_s = -sum(x/n_pair_px * log2(max(x/n_pair_px, 1e-300)) for x in px_marg_s if x > 0)
                h_c = -sum(x/n_pair_px * log2(max(x/n_pair_px, 1e-300)) for x in px_marg_c if x > 0)
                nmi_px = (min(h_s, h_c) > 0) ? mi_px / min(h_s, h_c) : 0.0

                shift = max(1, n_pair_px ÷ 3)
                hist2d_shift = zeros(Int, n_pxb, n_pxb)
                @inbounds for i in 1:n_pair_px
                    j = 1 + mod(i - 1 + shift, n_pair_px)
                    hist2d_shift[_ppb(paired_px_store[i]), _ppb(paired_px_close[j])] += 1
                end
                px_marg_s2 = [sum(hist2d_shift[i, j] for j in 1:n_pxb) for i in 1:n_pxb]
                px_marg_c2 = [sum(hist2d_shift[i, j] for i in 1:n_pxb) for j in 1:n_pxb]
                mi_shift = 0.0
                @inbounds for i in 1:n_pxb, j in 1:n_pxb
                    c = hist2d_shift[i, j]
                    c == 0 && continue
                    pij = Float64(c) / n_pair_px
                    pi  = Float64(px_marg_s2[i]) / n_pair_px
                    pj  = Float64(px_marg_c2[j]) / n_pair_px
                    pi > 0 && pj > 0 && (mi_shift += pij * log2(pij / (pi * pj)))
                end
                excess_mi = mi_px - mi_shift

                @printf("      I = %.4f bits  H(store_px)=%.4f  H(close_px)=%.4f  NMI=%.4f\n",
                        mi_px, h_s, h_c, nmi_px)
                @printf("      shift-baseline I = %.4f bits  excess = %.4f bits\n",
                        mi_shift, excess_mi)
                if excess_mi > 0.05
                    @printf("      ↑ excess MI > 0.05 bits: anchor x carries real memory across store→close\n")
                elseif excess_mi > 0.01
                    @printf("      ↑ weak but visible x-memory across store→close\n")
                else
                    @printf("      (≈ no detectable x-memory beyond finite-sample bias)\n")
                end
            else
                @printf("      (too few matched store→close keys for px MI)\n")
            end
        end

        # ── Same analysis for close events ────────────────────────────────
        if n_close >= 4
            hist2d_close = zeros(Int, n_abkt, n_pbkt)
            @inbounds for i in 1:n_close
                ab = _abkt(deep_stat.d12_close_alpha[i])
                pb = _pbkt(deep_stat.d12_close_px[i])
                hist2d_close[ab, pb] += 1
            end
            expected_c = Float64(n_close) / n_cells
            chi2_close = expected_c > 0 ?
                sum((Float64(hist2d_close[i,j]) - expected_c)^2 / expected_c
                    for i in 1:n_abkt, j in 1:n_pbkt) : NaN
            @printf("    2-D histogram χ²/dof for CLOSE events: %.3f  (uniform expected ≈ %.1f)\n",
                    chi2_close / dof_store, Float64(dof_store))
            if chi2_close / dof_store > 2.0
                @printf("      ↑ CONCENTRATED at close time too — not just a store-side bias\n")
            end
        end

        # ── Paired delta-alpha distribution ───────────────────────────────
        if n_store >= 4 && n_close >= 4
            @printf("    Paired delta-alpha distribution:\n")
            store_key_to_alpha = Dict{UInt128, Int}()
            @inbounds for i in 1:n_store
                haskey(store_key_to_alpha, deep_stat.d12_store_key[i]) ||
                    (store_key_to_alpha[deep_stat.d12_store_key[i]] = deep_stat.d12_store_alpha[i])
            end
            delta_alphas = Int[]
            @inbounds for i in 1:n_close
                k = deep_stat.d12_close_key[i]
                s_alpha = get(store_key_to_alpha, k, -1)
                s_alpha < 0 && continue
                c_alpha = deep_stat.d12_close_alpha[i]
                raw_d = mod(c_alpha - s_alpha, alpha_max + 1)
                delta = min(raw_d, alpha_max + 1 - raw_d)
                push!(delta_alphas, delta)
            end
            n_paired = length(delta_alphas)
            @printf("      paired (store→close) events     : %d\n", n_paired)
            if n_paired >= 2
                mu_d    = sum(delta_alphas) / n_paired
                med_d   = sort(delta_alphas)[n_paired ÷ 2 + 1]
                frac_lo = count(d -> d < (alpha_max+1) ÷ 16, delta_alphas) / n_paired
                @printf("      delta-alpha: mean=%.1f  median=%d  frac<ell/16=%.3f\n",
                        mu_d, med_d, frac_lo)
                if frac_lo > 0.5
                    @printf("      ↑ >50%% of closes within ell/16 of store alpha: SMALL EFFECTIVE SUPPORT\n")
                    @printf("        → confirms hypothesis: alpha·G x-support is algebraically bounded\n")
                elseif frac_lo > 0.2
                    @printf("      ↑ >20%% within ell/16: mild alpha concentration at closure\n")
                else
                    @printf("      (delta-alpha spread broadly — alpha support appears large)\n")
                end
                bin_w  = max(1, (alpha_max ÷ 2) ÷ 8)
                bins   = zeros(Int, 9)
                for d in delta_alphas
                    b = clamp(1 + d ÷ bin_w, 1, 9)
                    bins[b] += 1
                end
                @printf("      delta-alpha histogram (bin_width≈%d, range [0,ell/2]):\n", bin_w)
                @printf("        %8s  %8s  %8s\n", "bin_lo", "count", "frac%")
                for b in 1:9
                    lo = (b-1)*bin_w
                    @printf("        %8d  %8d  %7.2f%%\n",
                            lo, bins[b], 100.0*bins[b]/max(1,n_paired))
                end
            else
                @printf("      (too few paired events: %d)\n", n_paired)
            end
        end

        # ── Per-px_bucket alpha entropy H(alpha | px=b) ───────────────────
        @printf("    Per-px_bucket alpha entropy H(alpha_bkt | px_bkt) for stores:\n")
        if n_store >= 4
            px_alpha_hist = [zeros(Int, n_abkt) for _ in 1:n_pbkt]
            @inbounds for i in 1:n_store
                ab = _abkt(deep_stat.d12_store_alpha[i])
                pb = _pbkt(deep_stat.d12_store_px[i])
                px_alpha_hist[pb][ab] += 1
            end
            H_alpha_given_px = Float64[]
            px_nonempty = Int[]
            for pb in 1:n_pbkt
                h = px_alpha_hist[pb]
                tot = sum(h)
                tot < 4 && continue
                ent = -sum(c/tot * log2(max(c/tot, 1e-300)) for c in h if c > 0)
                push!(H_alpha_given_px, ent)
                push!(px_nonempty, pb)
            end
            if !isempty(H_alpha_given_px)
                H_max   = log2(Float64(n_abkt))
                H_mean  = sum(H_alpha_given_px) / length(H_alpha_given_px)
                H_min_v, H_min_i = findmin(H_alpha_given_px)
                H_max_v, H_max_i = findmax(H_alpha_given_px)
                @printf("      H_max (uniform over %d alpha_bkts): %.4f bits\n", n_abkt, H_max)
                @printf("      mean H(alpha|px)                  : %.4f bits (%.1f%% of max)\n",
                        H_mean, 100.0*H_mean/max(1e-10, H_max))
                @printf("      min  H(alpha|px=b)                : %.4f bits  px_bkt=%d  ← most constrained\n",
                        H_min_v, px_nonempty[H_min_i] - 1)
                @printf("      max  H(alpha|px=b)                : %.4f bits  px_bkt=%d\n",
                        H_max_v, px_nonempty[H_max_i] - 1)
                if H_mean / H_max < 0.7
                    @printf("      ↑ mean H < 0.7×H_max: ANCHOR STRONGLY CONSTRAINS ALPHA\n")
                    @printf("        → non-split residuals occur only for narrow alpha ranges at each anchor\n")
                elseif H_mean / H_max < 0.9
                    @printf("      ↑ mild constraint: alpha somewhat restricted per anchor\n")
                else
                    @printf("      (alpha nearly uniform across anchors — no strong constraint)\n")
                end
                order = sortperm(H_alpha_given_px)
                @printf("      5 most-constrained px_buckets:\n")
                @printf("        %6s  %8s  %8s\n", "px_bkt", "H(bits)", "H/H_max")
                for idx in order[1:min(5, end)]
                    pb = px_nonempty[idx]
                    p_lo = (pb-1) * (px_max+1) ÷ n_pbkt
                    p_hi = pb     * (px_max+1) ÷ n_pbkt - 1
                    @printf("        px∈[%5d,%5d)  H=%.4f  H/H_max=%.4f\n",
                            p_lo, p_hi, H_alpha_given_px[idx], H_alpha_given_px[idx]/H_max)
                end
            else
                @printf("      (no px bucket had ≥4 store events)\n")
            end
        end

        @label d12_done
    end   # let D12

    # ──────────────────────────────────────────────────────────────────────
    #  D13 — Mumford coordinate support cardinality
    # ──────────────────────────────────────────────────────────────────────
    @printf("\n  D13 — Mumford coordinate support cardinality\n")
    @printf("  ─────────────────────────────────────────────────────────────────\n")
    let
        n_store = length(deep_stat.d12_store_key)
        @printf("    store events available : %d\n", n_store)

        if n_store < 4
            @printf("    (too few store events — skipping D13)\n")
        elseif p <= 1
            @printf("    (p not provided or ≤1 — cannot compute log_p; pass p= to print_conj_deep_report)\n")
        else
            log_p = log(Float64(p))

            mask32 = UInt128(0xffffffff)
            u0s = Vector{UInt32}(undef, n_store)
            u1s = Vector{UInt32}(undef, n_store)
            v0s = Vector{UInt32}(undef, n_store)
            v1s = Vector{UInt32}(undef, n_store)
            @inbounds for i in 1:n_store
                k = deep_stat.d12_store_key[i]
                u0s[i] = UInt32(k         & mask32)
                u1s[i] = UInt32((k >> 32) & mask32)
                v0s[i] = UInt32((k >> 64) & mask32)
                v1s[i] = UInt32((k >> 96) & mask32)
            end

            n_u0   = length(Set(u0s))
            n_u1   = length(Set(u1s))
            n_v0   = length(Set(v0s))
            n_v1   = length(Set(v1s))

            upairs = Set{UInt64}()
            sizehint!(upairs, n_store)
            @inbounds for i in 1:n_store
                push!(upairs, UInt64(u0s[i]) | (UInt64(u1s[i]) << 32))
            end
            n_upair = length(upairs)

            vpairs = Set{UInt64}()
            sizehint!(vpairs, n_store)
            @inbounds for i in 1:n_store
                push!(vpairs, UInt64(v0s[i]) | (UInt64(v1s[i]) << 32))
            end
            n_vpair = length(vpairs)

            n_full = length(Set(deep_stat.d12_store_key))

            function kappa(n::Int)::Float64
                n <= 1 ? 0.0 : log(Float64(n)) / log_p
            end

            @printf("    p = %d\n", p)
            @printf("\n    Support cardinalities and exponents κ = log_p(|S|):\n")
            @printf("      %-20s  %10s  %8s  %s\n", "set", "|S|", "κ", "interpretation")
            @printf("      %-20s  %10s  %8s  %s\n", "────────────────────",
                    "──────────", "────────", "──────────────────────────────────────")

            rows = [
                ("u0  (marginal)",    n_u0,   "u-poly const term"),
                ("u1  (marginal)",    n_u1,   "u-poly linear coeff"),
                ("v0  (marginal)",    n_v0,   "v-poly const term"),
                ("v1  (marginal)",    n_v1,   "v-poly linear coeff"),
                ("(u0,u1) pairs",     n_upair,"u-polynomial support"),
                ("(v0,v1) pairs",     n_vpair,"v-polynomial support"),
                ("full (u0,u1,v0,v1)",n_full,"distinct LP keys seen"),
            ]
            for (label, n, interp) in rows
                @printf("      %-22s  %10d  %8.4f  %s\n", label, n, kappa(n), interp)
            end

            kappa_full = kappa(n_full)
            @printf("\n    Complexity exponent summary:\n")
            @printf("      Naive LP1-conj table pressure  : p^1.00  (all of F_p × F_p × …)\n")
            @printf("      Observed LP-key support        : p^%.4f  (%d distinct keys from %d stores)\n",
                    kappa_full, n_full, n_store)
            @printf("      Observed u-poly support        : p^%.4f  (%d distinct u-polys)\n",
                    kappa(n_upair), n_upair)
            reduction = 1.0 - kappa_full
            if reduction > 0.3
                @printf("      ↑ STRONG reduction: effective LP key space is p^%.4f below naive\n",
                        reduction)
                @printf("        → collision probability scales as p^%.4f, not p^0\n",
                        kappa_full - 1.0)
                @printf("        → LP1-conj table saturates at ~p^%.4f entries, not p\n",
                        kappa_full)
            elseif reduction > 0.1
                @printf("      ↑ moderate reduction (%.2f exponent below naive)\n", reduction)
            else
                @printf("      (support close to naive — no strong algebraic confinement detected)\n")
            end

            if n_store >= 2 && n_full >= 1
                mean_hits = Float64(n_store) / n_full
                @printf("\n    Key multiplicity (re-hit rate):\n")
                @printf("      mean hits per distinct key : %.2f\n", mean_hits)
                @printf("      distinct / total stores    : %.4f  (1.0 = no repeats)\n",
                        Float64(n_full) / n_store)

                key_counts = Dict{UInt128, Int}()
                sizehint!(key_counts, n_full)
                @inbounds for k in deep_stat.d12_store_key
                    key_counts[k] = get(key_counts, k, 0) + 1
                end
                counts_sorted = sort(collect(values(key_counts)), rev=true)
                n_distinct = length(counts_sorted)
                total_hits  = sum(counts_sorted)

                k1pct  = max(1, n_distinct ÷ 100)
                k10pct = max(1, n_distinct ÷ 10)
                mass1  = sum(counts_sorted[1:k1pct])  / total_hits
                mass10 = sum(counts_sorted[1:k10pct]) / total_hits
                @printf("      top  1%% of keys hold %.1f%% of stores\n", 100.0*mass1)
                @printf("      top 10%% of keys hold %.1f%% of stores\n", 100.0*mass10)

                n_d = length(counts_sorted)
                gini = 0.0
                if n_d > 1
                    cs = cumsum(sort(counts_sorted))
                    gini = 1.0 - 2.0 * sum(cs) / (Float64(n_d) * total_hits) + 1.0/n_d
                end
                @printf("      Gini coefficient           : %.4f  (0=uniform, 1=monopoly)\n", gini)
                if gini > 0.7
                    @printf("      ↑ HIGH Gini: a tiny set of LP keys dominates stores\n")
                    @printf("        → effective support is smaller than |S| suggests\n")
                elseif gini > 0.4
                    @printf("      ↑ moderate Gini: noticeable concentration in key hits\n")
                end

                # ── Recurrence-trimmed support ────────────────────────────
                @printf("\n    Recurrence-trimmed support (tail cut by key multiplicity):\n")
                @printf("      %5s  %10s  %9s  %10s  %10s  %10s\n",
                        "r", "keys≥r", "store%", "κ_key", "κ_α", "κ_(α,px)")
                @printf("      %s\n", "─"^62)

                have_alpha = length(deep_stat.d12_store_alpha) == n_store
                have_px    = length(deep_stat.d12_store_px)    == n_store

                key_to_alpha    = Dict{UInt128, Set{Int}}()
                key_to_alpha_px = Dict{UInt128, Set{Tuple{Int,Int}}}()
                if have_alpha
                    sizehint!(key_to_alpha,    n_full)
                    sizehint!(key_to_alpha_px, n_full)
                    @inbounds for i in 1:n_store
                        k  = deep_stat.d12_store_key[i]
                        al = deep_stat.d12_store_alpha[i]
                        px = have_px ? deep_stat.d12_store_px[i] : 0
                        push!(get!(key_to_alpha,    k, Set{Int}()),              al)
                        push!(get!(key_to_alpha_px, k, Set{Tuple{Int,Int}}()), (al, px))
                    end
                end

                for r in (1, 2, 3, 5, 10)
                    keys_r = [k for (k, c) in key_counts if c >= r]
                    if isempty(keys_r)
                        @printf("      %5d  %10d  %9s  %10s  %10s  %10s\n",
                                r, 0, "-", "-", "-", "-")
                        continue
                    end
                    n_keys_r  = length(keys_r)
                    n_store_r = sum(key_counts[k] for k in keys_r; init=0)
                    store_pct = 100.0 * n_store_r / max(n_store, 1)
                    κ_key_str = @sprintf("%.4f", log(p, n_keys_r))

                    κ_α_str   = "-"
                    κ_apx_str = "-"
                    if have_alpha && !isempty(key_to_alpha)
                        all_alpha    = Set{Int}()
                        all_alpha_px = Set{Tuple{Int,Int}}()
                        for k in keys_r
                            if haskey(key_to_alpha, k)
                                union!(all_alpha,    key_to_alpha[k])
                                union!(all_alpha_px, key_to_alpha_px[k])
                            end
                        end
                        n_al  = length(all_alpha)
                        n_apx = length(all_alpha_px)
                        κ_α_str   = n_al  > 0 ? @sprintf("%.4f", log(p, n_al))  : "-"
                        κ_apx_str = n_apx > 0 ? @sprintf("%.4f", log(p, n_apx)) : "-"
                    end

                    @printf("      %5d  %10d  %9.2f  %10s  %10s  %10s\n",
                            r, n_keys_r, store_pct, κ_key_str, κ_α_str, κ_apx_str)
                end

                # ── p-adic valuation distributions ───────────────────────
                @printf("\n    p-adic valuation distributions (coords mod p, so v_p ∈ {0,1,…}):\n")
                @printf("      (v_p(x)=0 means x≢0 mod p; v_p(x)≥1 means p|x)\n")

                function vp_hist(xs::Vector{UInt32})
                    z = count(iszero, xs)
                    nz = length(xs) - z
                    return z, nz
                end

                for (name, xs) in (("u0", u0s), ("u1", u1s), ("v0", v0s), ("v1", v1s))
                    z, nz = vp_hist(xs)
                    frac0 = Float64(z) / n_store
                    @printf("      %s: p∤x (v_p=0): %d (%.1f%%)   p|x (v_p≥1): %d (%.1f%%)\n",
                            name, nz, 100.0*(1-frac0), z, 100.0*frac0)
                end
                n_all_zero = count(1:n_store) do i
                    u0s[i] == 0 && u1s[i] == 0 && v0s[i] == 0 && v1s[i] == 0
                end
                @printf("      all-zero (trivial key) events  : %d / %d\n", n_all_zero, n_store)
                if any(>(0.05), [count(iszero,xs)/n_store for xs in (u0s,u1s,v0s,v1s)])
                    @printf("      ↑ >5%% zero in some coordinate — possible subvariety confinement\n")
                    @printf("        (non-split residuals with p|coord live on a degree-drop locus)\n")
                end
            end
        end
    end   # let D13

    # ──────────────────────────────────────────────────────────────────────
    #  D14 — Conditional entropy H(a | px_bucket)
    # ──────────────────────────────────────────────────────────────────────
    @printf("\n  D14 — Conditional entropy H(a | px_bucket)\n")
    @printf("  ─────────────────────────────────────────────────────────────────\n")
    let
        n_store  = length(deep_stat.d12_store_key)
        have_a   = length(deep_stat.d14_store_a)  == n_store
        have_px  = length(deep_stat.d12_store_px) == n_store

        if n_store < 4 || !have_a || !have_px
            @printf("    (insufficient data: n_store=%d have_a=%s have_px=%s — skipping D14)\n",
                    n_store, have_a, have_px)
        elseif p <= 1
            @printf("    (p not provided — skipping D14)\n")
        else
            n_pbkt  = 32
            n_abkts = 64
            px_max  = p - 1
            _pbkt14(px) = clamp(1 + Int(px) * n_pbkt  ÷ max(px_max, 1), 1, n_pbkt)
            _abkt14(av) = av < 0 ? 1 : clamp(1 + av * n_abkts ÷ max(p, 1), 1, n_abkts)

            px_a_hist = [zeros(Int, n_abkts) for _ in 1:n_pbkt]
            n_valid = 0
            @inbounds for i in 1:n_store
                av = deep_stat.d14_store_a[i]
                av < 0 && continue
                pb = _pbkt14(deep_stat.d12_store_px[i])
                ab = _abkt14(av)
                px_a_hist[pb][ab] += 1
                n_valid += 1
            end

            @printf("    store events with valid a   : %d / %d\n", n_valid, n_store)

            if n_valid < 4
                @printf("    (too few valid a events — skipping entropy computation)\n")
            else
                H_max = log2(Float64(n_abkts))
                H_vals      = Float64[]
                px_nonempty = Int[]
                for pb in 1:n_pbkt
                    h = px_a_hist[pb]
                    tot = sum(h)
                    tot < 4 && continue
                    ent = -sum(c/tot * log2(max(c/tot, 1e-300)) for c in h if c > 0)
                    push!(H_vals, ent)
                    push!(px_nonempty, pb)
                end

                if isempty(H_vals)
                    @printf("    (no px bucket had >=4 valid events)\n")
                else
                    H_mean           = sum(H_vals) / length(H_vals)
                    H_min_v, H_min_i = findmin(H_vals)
                    H_max_v, H_max_i = findmax(H_vals)
                    ratio            = H_mean / max(1e-10, H_max)

                    @printf("    H_max (uniform over %d a-buckets) : %.4f bits\n", n_abkts, H_max)
                    @printf("    mean H(a | px)                    : %.4f bits  (%.1f%% of max)\n",
                            H_mean, 100.0 * ratio)
                    @printf("    min  H(a | px=b)                  : %.4f bits  px_bkt=%d  <- most constrained\n",
                            H_min_v, px_nonempty[H_min_i] - 1)
                    @printf("    max  H(a | px=b)                  : %.4f bits  px_bkt=%d\n",
                            H_max_v, px_nonempty[H_max_i] - 1)

                    if ratio < 0.7
                        @printf("    !! mean H < 0.7*H_max: ANCHOR CONSTRAINS phi\n")
                        @printf("       -> division by u(px) introduces bias; certain anchors collapse 'a'\n")
                    elseif ratio < 0.9
                        @printf("    ^ mild phi-restriction (H/H_max = %.3f)\n", ratio)
                    else
                        @printf("    (a nearly uniform across anchors — no direct phi-compression from px; %.3f)\n",
                                ratio)
                    end

                    order = sortperm(H_vals)
                    @printf("    5 most-constrained px_buckets:\n")
                    @printf("      %6s  %8s  %8s\n", "px_bkt", "H(bits)", "H/H_max")
                    for idx in order[1:min(5, lastindex(order))]
                        pb   = px_nonempty[idx]
                        p_lo = (pb-1) * (px_max+1) ÷ n_pbkt
                        p_hi = pb     * (px_max+1) ÷ n_pbkt - 1
                        @printf("      px~[%5d,%5d)  H=%.4f  H/H_max=%.4f\n",
                                p_lo, p_hi, H_vals[idx], H_vals[idx] / H_max)
                    end
                end
            end
        end
    end   # let D14

    # ──────────────────────────────────────────────────────────────────────
    #  D15 — Residual support ratio conditioned on px_bucket
    # ──────────────────────────────────────────────────────────────────────
    @printf("\n  D15 — Residual support ratio conditioned on px_bucket\n")
    @printf("  ─────────────────────────────────────────────────────────────────\n")
    let
        n_store = length(deep_stat.d12_store_key)
        have_px = length(deep_stat.d12_store_px) == n_store

        if n_store < 4 || !have_px
            @printf("    (insufficient data: n_store=%d have_px=%s — skipping D15)\n",
                    n_store, have_px)
        elseif p <= 1
            @printf("    (p not provided — skipping D15)\n")
        else
            n_pbkt  = 32
            px_max  = p - 1
            _pbkt15(px) = clamp(1 + Int(px) * n_pbkt ÷ max(px_max, 1), 1, n_pbkt)

            bkt_total    = zeros(Int, n_pbkt)
            bkt_distinct = [Set{UInt128}() for _ in 1:n_pbkt]
            @inbounds for i in 1:n_store
                pb = _pbkt15(deep_stat.d12_store_px[i])
                bkt_total[pb] += 1
                push!(bkt_distinct[pb], deep_stat.d12_store_key[i])
            end

            @printf("    %-24s  %8s  %8s  %8s  %s\n",
                    "px_bucket", "samples", "distinct", "ratio", "note")
            @printf("    %s\n", "-"^70)

            ratios_nonempty = Float64[]
            min_ratio = 1.0;  min_pb = 0
            max_ratio = 0.0;  max_pb = 0
            for pb in 1:n_pbkt
                tot = bkt_total[pb]
                tot < 4 && continue
                nd  = length(bkt_distinct[pb])
                r   = Float64(nd) / tot
                push!(ratios_nonempty, r)
                p_lo = (pb-1) * (px_max+1) ÷ n_pbkt
                p_hi = pb     * (px_max+1) ÷ n_pbkt - 1
                note = r < 0.5 ? "<- LOCAL COLLAPSE (strong)" :
                       r < 0.8 ? "<- mild collision clustering" :
                                 ""
                @printf("    px~[%5d,%5d)  %8d  %8d  %8.4f  %s\n",
                        p_lo, p_hi, tot, nd, r, note)
                if r < min_ratio; min_ratio = r; min_pb = pb; end
                if r > max_ratio; max_ratio = r; max_pb = pb; end
            end

            if !isempty(ratios_nonempty)
                global_distinct = length(Set(deep_stat.d12_store_key))
                mean_ratio = sum(ratios_nonempty) / length(ratios_nonempty)
                @printf("\n    Summary:\n")
                @printf("      global support ratio (all px) : %.4f  (%d distinct / %d stores)\n",
                        Float64(global_distinct) / n_store, global_distinct, n_store)
                @printf("      mean conditional ratio        : %.4f\n", mean_ratio)
                @printf("      min  conditional ratio        : %.4f  px_bkt=%d  <- most collapsed\n",
                        min_ratio, min_pb - 1)
                @printf("      max  conditional ratio        : %.4f  px_bkt=%d\n",
                        max_ratio, max_pb - 1)

                if min_ratio < 0.5
                    @printf("      !! STRONG local collapse at px_bkt=%d (ratio=%.4f)\n",
                            min_pb - 1, min_ratio)
                    @printf("         -> walks anchored there collide far below birthday bound\n")
                    @printf("         -> steer anchor selection toward this px bucket for faster closure\n")
                elseif min_ratio < 0.8
                    @printf("      ^ mild collapse in some buckets — worth investigating anchor bias\n")
                else
                    @printf("      (no bucket shows significant local collapse)\n")
                end

                @printf("\n    D14 x D15 cross-check:\n")
                @printf("      Pattern A (D14 drops AND D15 drops) -> anchor-dependent compression; walk is steerable\n")
                @printf("      Pattern B (D14 flat, D15 drops)     -> collapse arises in later steps (div/sqrt/splitting)\n")
                @printf("      Pattern C (both flat)               -> structure is temporal/trajectory, not static\n")
            else
                @printf("    (no px bucket had >=4 store events)\n")
            end
        end
    end   # let D15

    # ──────────────────────────────────────────────────────────────────────
    #  D16 — Pre-burst state fingerprinting
    # ──────────────────────────────────────────────────────────────────────
    @printf("\n  D16 — Pre-burst state fingerprinting (lag Δ ∈ [%d, %d])\n",
            D16_LAG_LO, D16_LAG_HI)
    @printf("  ─────────────────────────────────────────────────────────────────\n")
    let
        n_pb = deep_stat.d16_n_preburst
        n_bl = deep_stat.d16_n_baseline
        pb_hist = deep_stat.d16_preburst_hist
        bl_hist = deep_stat.d16_baseline_hist

        @printf("    Pre-burst samples : %d  (gate 1/%d, cap %d)\n",
                n_pb, D16_GATE_DENOM, D16_MAX_SAMPLES)
        @printf("    Baseline samples  : %d\n", n_bl)

        if n_pb < 20 || n_bl < 20
            @printf("    (insufficient samples — collect more emissions)\n")
        else
            all_keys = union(keys(pb_hist), keys(bl_hist))
            ratios = Dict{UInt32, Float64}()
            for k in all_keys
                pb_f = get(pb_hist, k, 0) / n_pb
                bl_f = get(bl_hist, k, 0) / n_bl
                bl_f > 0.0 && (ratios[k] = pb_f / bl_f)
            end

            sorted_keys = sort(collect(keys(ratios)), by=k -> -ratios[k])
            n_show = min(30, length(sorted_keys))
            @printf("    Top %d (step_mod, partition_id) buckets by pre-burst / baseline ratio:\n", n_show)
            @printf("    %-10s  %-12s  %10s  %10s  %10s  %s\n",
                    "step_mod", "partition_id", "pb_count", "bl_count", "ratio", "note")
            @printf("    %s\n", "-"^75)

            total_pb_top = 0
            n_spike = 0
            for i in 1:n_show
                k       = sorted_keys[i]
                sm      = (k >> 16) & 0xff
                pid     = k & 0xffff
                pb_c    = get(pb_hist, k, 0)
                bl_c    = get(bl_hist, k, 0)
                ratio_v = ratios[k]
                note    = ratio_v >= 5.0 ? "<- STRONG SPIKE" :
                          ratio_v >= 2.5 ? "<- moderate spike" :
                          ratio_v >= 1.5 ? "<- mild elevation" : ""
                @printf("    %-10d  %-12d  %10d  %10d  %10.3f  %s\n",
                        sm, pid, pb_c, bl_c, ratio_v, note)
                total_pb_top += pb_c
                ratio_v >= 2.5 && (n_spike += 1)
            end

            frac_top = Float64(total_pb_top) / max(1, n_pb)
            @printf("\n    Top-%d buckets hold %.1f%% of all pre-burst samples\n",
                    n_show, 100.0 * frac_top)
            @printf("    Buckets with ratio ≥ 2.5× : %d\n", n_spike)

            if n_spike == 0
                @printf("    -> Ratios near 1 everywhere: bursts are NOT from a specific walk regime\n")
                @printf("       (structure is emergent / global, not locally concentrated)\n")
            elseif n_spike <= 5
                @printf("    -> Few hot buckets: burst has a LOCAL cause in (step_mod, partition_id)\n")
                @printf("       Check whether spiking partition_ids correspond to small FB columns\n")
                @printf("       or periodic step_mod values → may indicate walk attractor or cycling\n")
            else
                @printf("    -> Many spiking buckets: broad concentration — may reflect periodic\n")
                @printf("       structure in step_mod or systematic anchor bias across partitions\n")
            end

            pb_part = Dict{Int,Int}()
            bl_part = Dict{Int,Int}()
            for (k, v) in pb_hist; pid = Int(k & 0xffff); pb_part[pid] = get(pb_part, pid, 0) + v; end
            for (k, v) in bl_hist; pid = Int(k & 0xffff); bl_part[pid] = get(bl_part, pid, 0) + v; end

            part_ratios = Dict{Int,Float64}()
            for pid in union(keys(pb_part), keys(bl_part))
                pf = get(pb_part, pid, 0) / n_pb
                bf = get(bl_part, pid, 0) / n_bl
                bf > 0.0 && (part_ratios[pid] = pf / bf)
            end
            top_parts = sort(collect(keys(part_ratios)), by=k -> -part_ratios[k])[1:min(10,length(part_ratios))]

            @printf("\n    Marginal over step_mod — top partition_ids by ratio:\n")
            @printf("    %-14s  %10s  %10s  %10s\n", "partition_id", "pb_count", "bl_count", "ratio")
            for pid in top_parts
                @printf("    %-14d  %10d  %10d  %10.3f\n",
                        pid,
                        get(pb_part, pid, 0), get(bl_part, pid, 0), part_ratios[pid])
            end

            pb_sm = Dict{Int,Int}()
            bl_sm = Dict{Int,Int}()
            for (k, v) in pb_hist; sm = Int((k >> 16) & 0xff); pb_sm[sm] = get(pb_sm, sm, 0) + v; end
            for (k, v) in bl_hist; sm = Int((k >> 16) & 0xff); bl_sm[sm] = get(bl_sm, sm, 0) + v; end

            sm_ratios = Dict{Int,Float64}()
            for sm in union(keys(pb_sm), keys(bl_sm))
                pf = get(pb_sm, sm, 0) / n_pb
                bf = get(bl_sm, sm, 0) / n_bl
                bf > 0.0 && (sm_ratios[sm] = pf / bf)
            end
            top_sms = sort(collect(keys(sm_ratios)), by=k -> -sm_ratios[k])[1:min(10,length(sm_ratios))]

            @printf("\n    Marginal over partition_id — top step_mod values by ratio:\n")
            @printf("    %-14s  %10s  %10s  %10s\n", "step_mod", "pb_count", "bl_count", "ratio")
            for sm in top_sms
                @printf("    %-14d  %10d  %10d  %10.3f\n",
                        sm,
                        get(pb_sm, sm, 0), get(bl_sm, sm, 0), sm_ratios[sm])
            end
        end
    end   # let D16

    # ──────────────────────────────────────────────────────────────────────
    #  D17 — LP1-conj lifetime multiplicity analysis
    # ──────────────────────────────────────────────────────────────────────
    @printf("\n  D17 — LP1-conj lifetime multiplicity analysis\n")
    @printf("  ─────────────────────────────────────────────────────────────────\n")
    let hits = deep_stat.d17_lifetime_hits
        n_tracked = length(hits)
        @printf("    Distinct keys tracked : %d  (cap %d)\n", n_tracked, D17_MAX_TRACKED_KEYS)
        if n_tracked == 0
            @printf("    (no lifetime hits recorded — check record_conj_deep_miss! wiring)\n")
        else
            counts_vec = collect(values(hits))
            sort!(counts_vec, rev=true)
            total_hits = sum(counts_vec)
            c_max  = counts_vec[1]
            c_mean = Float64(total_hits) / n_tracked
            c_var  = sum((Float64(c) - c_mean)^2 for c in counts_vec) / n_tracked
            c_cv   = sqrt(c_var) / max(1e-30, c_mean)

            @printf("    Total hits            : %d\n", total_hits)
            @printf("    c_max                 : %d\n", c_max)
            @printf("    c_mean                : %.3f\n", c_mean)
            @printf("    CV (σ/μ)              : %.3f\n", c_cv)
            @printf("    Gini                  : %.4f\n", _gini(counts_vec))
            @printf("    Hill α̂ (k=50)         : %.3f\n", _hill_exponent(counts_vec; k=50))
            for frac in (0.01, 0.05, 0.10)
                @printf("    Top-%.0f%% key mass     : %.1f%%\n",
                        100.0*frac, 100.0*_top_share(counts_vec, frac))
            end

            n_zipf = min(200, n_tracked)
            if n_zipf >= 10
                log_ranks  = [log(Float64(i)) for i in 1:n_zipf]
                log_counts = [log(Float64(max(1, counts_vec[i]))) for i in 1:n_zipf]
                lr_mean = sum(log_ranks)  / n_zipf
                lc_mean = sum(log_counts) / n_zipf
                cov = sum((log_ranks[i] - lr_mean) * (log_counts[i] - lc_mean) for i in 1:n_zipf)
                var = sum((log_ranks[i] - lr_mean)^2                            for i in 1:n_zipf)
                zipf_slope = var > 0 ? cov / var : NaN
                @printf("    Zipf log-log slope    : %.3f  (from top-%d keys; -1 = pure Zipf)\n",
                        zipf_slope, n_zipf)
            end

            # ── Top-50 keys with Mumford decode ───────────────────────────
            @printf("\n    Top-50 keys by lifetime hit count")
            p > 1 && @printf(" (p=%d for discriminant residue)", p)
            @printf(":\n")
            @printf("    %-8s  %-10s  %-10s  %-10s  %-10s  %5s  %8s  %8s  %s\n",
                    "rank", "u0", "u1", "v0", "v1", "hits",
                    "disc_u%p", "disc_v%p", "flags")
            @printf("    %s\n", "-"^92)

            mask32 = UInt128(0xffffffff)
            top_pairs = sort(collect(hits), by=kv->-kv[2])[1:min(50, n_tracked)]
            for (rank, (key, cnt)) in enumerate(top_pairs)
                u0 = Int(key         & mask32)
                u1 = Int((key >> 32) & mask32)
                v0 = Int((key >> 64) & mask32)
                v1 = Int((key >> 96) & mask32)
                flag_parts = String[]
                disc_u_str = "?"
                disc_v_str = "?"
                if p > 1
                    disc_u = mod(u1*u1 - 4*u0, p)
                    disc_v = mod(v1*v1 - 4*v0, p)
                    is_qr(d) = d == 0 || powermod(d, (p-1)÷2, p) == 1
                    disc_u_str = is_qr(disc_u) ? "QR" : "NR"
                    disc_v_str = is_qr(disc_v) ? "QR" : "NR"
                    disc_u == 0 && push!(flag_parts, "u-SPLIT!")
                    disc_v == 0 && push!(flag_parts, "v-SPLIT!")
                    is_qr(disc_u) && disc_u != 0 && push!(flag_parts, "u-split-gen")
                    is_qr(disc_v) && disc_v != 0 && push!(flag_parts, "v-SPLIT!")
                end
                @printf("    %-8d  %-10d  %-10d  %-10d  %-10d  %5d  %8s  %8s  %s\n",
                        rank, u0, u1, v0, v1, cnt,
                        disc_u_str, disc_v_str,
                        isempty(flag_parts) ? "" : join(flag_parts, " "))
            end

            # ── High-multiplicity model fit ────────────────────────────────
            c_thresh = max(2, c_max ÷ 10)
            hi_counts = filter(c -> c >= c_thresh, counts_vec)
            @printf("\n    High-multiplicity model (c ≥ %d): %d keys, %.1f%% of total hits\n",
                    c_thresh, length(hi_counts),
                    100.0 * sum(hi_counts) / max(1, total_hits))
            if length(hi_counts) >= 5
                log_sum = sum(log(Float64(c) / max(1.0, Float64(c_thresh)-1)) for c in hi_counts)
                alpha_pl = length(hi_counts) / max(1e-30, log_sum)
                @printf("    Power-law MLE α̂        : %.3f  (α<2 → infinite-variance; α<1 → divergent mean)\n",
                        alpha_pl)
            else
                @printf("    (fewer than 5 high-mult keys; model fit skipped)\n")
            end

            # ── Disc-u / disc-v summary over all tracked keys ─────────────
            if p > 1
                n_u_qr = 0; n_v_qr = 0; n_u_nr = 0; n_v_nr = 0
                is_qr_p(d) = d == 0 || powermod(d, (p-1)÷2, p) == 1
                for (key, _) in hits
                    u0 = Int(key         & mask32)
                    u1 = Int((key >> 32) & mask32)
                    v0 = Int((key >> 64) & mask32)
                    v1 = Int((key >> 96) & mask32)
                    is_qr_p(mod(u1*u1 - 4*u0, p)) ? (n_u_qr += 1) : (n_u_nr += 1)
                    is_qr_p(mod(v1*v1 - 4*v0, p)) ? (n_v_qr += 1) : (n_v_nr += 1)
                end
                n_tot = n_u_qr + n_u_nr
                @printf("\n    disc(u) over all %d tracked keys:\n", n_tot)
                @printf("      QR (split or zero) : %d  (%.1f%%)\n", n_u_qr, 100.0*n_u_qr/max(1,n_tot))
                @printf("      NR (non-split)     : %d  (%.1f%%)\n", n_u_nr, 100.0*n_u_nr/max(1,n_tot))
                @printf("    disc(v) over all %d tracked keys:\n", n_tot)
                @printf("      QR (split or zero) : %d  (%.1f%%)\n", n_v_qr, 100.0*n_v_qr/max(1,n_tot))
                @printf("      NR (non-split)     : %d  (%.1f%%)\n", n_v_nr, 100.0*n_v_nr/max(1,n_tot))
                @printf("\n    Interpretation:\n")
                frac_u_nr = n_u_nr / max(1, n_tot)
                frac_v_qr = n_v_qr / max(1, n_tot)
                if frac_u_nr > 0.80
                    @printf("      disc(u)=NR dominant (%.0f%%): u-poly irreducible → support points over F_p² \\ F_p\n",
                            100.0*frac_u_nr)
                    @printf("      This is consistent with LP1-conj design; NOT a decoding artifact.\n")
                end
                if frac_v_qr > 0.30
                    @printf("      disc(v)=QR elevated (%.0f%%): verify key packing matches canonical_lp1_conj_key.\n",
                            100.0*frac_v_qr)
                    @printf("      Expected packing: key = u0 | u1<<32 | v0<<64 | v1<<96 (each coord mod p).\n")
                    @printf("      If disc(v) remains >30%% QR after packing verification, the v-polynomial\n")
                    @printf("      of the stored residual may have rational roots — check sign normalization.\n")
                end
            end
        end
    end   # let D17

    # ──────────────────────────────────────────────────────────────────────
    #  D18 — u1+px Vieta sum cardinality at close events
    # ──────────────────────────────────────────────────────────────────────
    @printf("\n  D18 — u1+px Vieta sum cardinality at close events\n")
    @printf("  ─────────────────────────────────────────────────────────────────\n")
    let
        n_close = length(deep_stat.d12_close_key)
        n_store = length(deep_stat.d12_store_key)
        have_close_px = length(deep_stat.d12_close_px) == n_close
        have_store_px = length(deep_stat.d12_store_px) == n_store

        D18_MIN_CLOSE = max(50, round(Int, 3.0 * sqrt(Float64(p))))

        @printf("    close events available : %d  (need ≥%d for meaningful collision statistics)\n",
                n_close, D18_MIN_CLOSE)
        @printf("    store events available : %d\n", n_store)

        if n_close < D18_MIN_CLOSE
            @printf("    (too few close events to distinguish σ-concentration from uniform sampling — skipping D18)\n")
            @goto d18_done
        end
        if !have_close_px
            @printf("    (d12_close_px not parallel to d12_close_key — check wiring)\n")
            @goto d18_done
        end
        if p <= 1
            @printf("    (p not provided — pass p= to print_conj_deep_report)\n")
            @goto d18_done
        end

        mask32 = UInt128(0xffffffff)

        sigma_close = Vector{Int}(undef, n_close)
        @inbounds for i in 1:n_close
            c1_rs = Int((deep_stat.d12_close_key[i] >> 32) & mask32)
            sigma_close[i] = mod(p - c1_rs, p)
        end

        sigma_store = if have_store_px && n_store >= 2
            sv = Vector{Int}(undef, n_store)
            @inbounds for i in 1:n_store
                c1_rs = Int((deep_stat.d12_store_key[i] >> 32) & mask32)
                sv[i] = mod(p - c1_rs, p)
            end
            sv
        else
            Int[]
        end

        sigma_close_set = Set(sigma_close)
        n_sigma_close   = length(sigma_close_set)
        n_sigma_store   = isempty(sigma_store) ? 0 : length(Set(sigma_store))

        expected_close = p * (1.0 - exp(-Float64(n_close) / p))
        expected_store = n_sigma_store > 0 ? p * (1.0 - exp(-Float64(n_store) / p)) : 0.0

        compress_close = n_sigma_close / max(1.0, expected_close)
        compress_store = n_sigma_store > 0 ? n_sigma_store / max(1.0, expected_store) : NaN

        @printf("\n    Vieta sum σ = u1+px = −c1_rs (mod p):\n")
        @printf("      |{σ}| at close events : %d  (expected under uniform: %.1f)  ratio=%.4f\n",
                n_sigma_close, expected_close, compress_close)
        if !isempty(sigma_store)
            @printf("      |{σ}| at store events : %d  (expected under uniform: %.1f)  ratio=%.4f\n",
                    n_sigma_store, expected_store, compress_store)
        end

        shortfall = expected_close - n_sigma_close
        shortfall_sigma = shortfall / max(1.0, sqrt(expected_close))
        if compress_close < 0.5 && shortfall_sigma > 3.0
            @printf("\n      ↑ COMPRESSION DETECTED: close events concentrate on %.1f%% of expected σ-space\n",
                    100.0 * compress_close)
            @printf("        → LP1-conj collisions cluster on a thin set of Vieta sum hyperplanes\n")
            @printf("        → effective key space is lower-dimensional than p^2\n")
        elseif compress_close < 0.8 && shortfall_sigma > 3.0
            @printf("\n      ↑ mild compression (%.1f%% of expected σ-space, %.1fσ shortfall)\n",
                    100.0 * compress_close, shortfall_sigma)
        else
            @printf("      (σ-cardinality consistent with uniform sampling)\n")
        end

        function sigma_entropy(vals::Vector{Int})::Float64
            n = length(vals)
            n == 0 && return 0.0
            cnt = Dict{Int,Int}()
            for v in vals; cnt[v] = get(cnt, v, 0) + 1; end
            -sum((c/n) * log2(c/n) for c in values(cnt))
        end

        n_repeats = n_close - n_sigma_close
        if n_repeats > 0
            H_close = sigma_entropy(sigma_close)
            H_max   = log2(Float64(p))
            @printf("\n      H(σ | close) = %.4f bits  (H_max = %.4f bits)  ratio=%.4f\n",
                    H_close, H_max, H_close / H_max)
            if !isempty(sigma_store)
                H_store = sigma_entropy(sigma_store)
                H_close_null = log2(Float64(n_close))
                excess_drop = (H_store - H_close) - (H_store - H_close_null)
                @printf("      H(σ | store) = %.4f bits  ratio=%.4f\n", H_store, H_store / H_max)
                if excess_drop > 0.5
                    @printf("      ΔH excess (beyond sample-size null) = %+.4f bits ← ENTROPY DROP AT CLOSE\n",
                            excess_drop)
                else
                    @printf("      (entropy drop consistent with sample-size null — no excess concentration)\n")
                end
            end
        else
            @printf("\n      (no σ repeats at close — entropy comparison not meaningful at this sample size)\n")
        end

        sigma_close_cnt = Dict{Int,Int}()
        for v in sigma_close; sigma_close_cnt[v] = get(sigma_close_cnt, v, 0) + 1; end
        max_cnt = maximum(values(sigma_close_cnt))

        if max_cnt >= 2
            top_sigma = sort(collect(sigma_close_cnt), by=kv->-kv[2])[1:min(10, length(sigma_close_cnt))]
            uniform_rate = Float64(n_close) / p

            @printf("\n      Top-10 σ values at close (uniform_expected/slot = %.3f):\n", uniform_rate)
            @printf("      %-12s  %8s  %8s  %8s  %s\n", "σ", "count", "expected", "lift", "note")
            @printf("      %s\n", "-"^60)
            for (σ_val, cnt) in top_sigma
                lift = cnt / max(1e-10, uniform_rate)
                note = lift > 5.0 ? "← STRONG HOT PLANE" :
                       lift > 2.0 ? "← elevated" : ""
                @printf("      %-12d  %8d  %8.2f  %8.3f  %s\n",
                        σ_val, cnt, uniform_rate, lift, note)
            end

            sigma_to_keys = Dict{Int, Set{UInt128}}()
            @inbounds for i in 1:n_close
                σ_val = sigma_close[i]
                k = deep_stat.d12_close_key[i]
                s = get!(sigma_to_keys, σ_val, Set{UInt128}())
                push!(s, k)
            end

            @printf("\n      Key diversity on top-10 σ planes (distinct close keys per σ):\n")
            @printf("      %-12s  %8s  %10s  %8s  %s\n", "σ", "closes", "dist_keys", "fill", "note")
            @printf("      %s\n", "-"^65)
            for (σ_val, cnt) in top_sigma
                n_keys = length(get(sigma_to_keys, σ_val, Set{UInt128}()))
                fill   = n_keys / cnt
                note   = fill < 0.3 ? "← KEY REUSE: few keys dominate this plane" :
                         fill < 0.7 ? "← moderate reuse" : ""
                @printf("      %-12d  %8d  %10d  %8.3f  %s\n",
                        σ_val, cnt, n_keys, fill, note)
            end
        end

        if !isempty(sigma_store) && n_sigma_close >= 100
            sigma_store_set = Set(sigma_store)
            n_overlap       = length(intersect(sigma_close_set, sigma_store_set))
            frac_close_in_store = n_overlap / max(1, n_sigma_close)
            @printf("\n      σ-set overlap (close ∩ store) / |close σ-set|: %d / %d = %.4f\n",
                    n_overlap, n_sigma_close, frac_close_in_store)
            if frac_close_in_store < 0.5
                @printf("      ↑ LOW OVERLAP: many σ values only appear at close, not store\n")
                @printf("        → some collision partners were stored in a different epoch/anchor regime\n")
            end
        end

        D18_MIN_FOR_MOD = 500
        if n_close >= D18_MIN_FOR_MOD
            @printf("\n      σ mod small primes (periodicity / subgroup probe):\n")
            @printf("      %-6s  %-12s  %8s  %8s  %8s\n", "mod", "top residue", "freq", "uniform", "3σ_hi")
            for q in (2, 3, 5, 7, 11, 13, 17)
                res_cnt = Dict{Int,Int}()
                for v in sigma_close; r = mod(v, q); res_cnt[r] = get(res_cnt, r, 0) + 1; end
                top_r, top_c = sort(collect(res_cnt), by=kv->-kv[2])[1]
                freq  = top_c / n_close
                unif  = 1.0 / q
                hi3σ  = unif + 3.0 * sqrt(unif * (1.0 - unif) / n_close)
                flag  = freq > hi3σ ? " ← $(round(Int, freq/unif))× concentrated" : ""
                @printf("      %-6d  %-12d  %8.4f  %8.4f  %8.4f%s\n", q, top_r, freq, unif, hi3σ, flag)
            end
        end

        @label d18_done
    end   # let D18
end
