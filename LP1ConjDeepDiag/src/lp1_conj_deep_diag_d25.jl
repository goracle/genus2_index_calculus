# =============================================================================
#  lp1_conj_deep_diag_d25.jl — D25: Closure (α, px) Cell Lift Analysis
#
#  Repurposed from alternating-renewal burst model (which produced degenerate
#  singleton bursts) to a direct dig on the D12 anomaly:
#
#    D12 shows the *store* distribution is non-uniform in (α, px) space
#    (χ²/dof ≈ 122, hot cells with 4× lift).  D25 asks: do *closures*
#    concentrate in those same hot cells, or in different ones?
#
#    If closure lift ≈ store lift → birthday collisions are proportional to
#      density; the α₂ gap comes from marginal non-uniformity alone.
#    If closure lift >> store lift in specific cells → those cells have
#      anomalously high closure rate; walk geometry concentrates second visits
#      in a thin subspace, directly explaining α₂ ≈ 0.6 < α ≈ 1.15.
#
#  Also reports the Δα = (α_close − α_store) mod ell histogram to test for
#  step-table periodicity driving repeated visits at fixed α offsets.
#
#  Included by lp1_conj_deep_diag.jl; do not include directly.
# =============================================================================

function _report_d25(deep_stat::ConjDeepStat, store_al::Vector{Int}, store_px::Vector{Int},
                     ell::Int, p::Int)
    @printf("\n── D25: Closure (α,px) Cell Lift vs D12 Store Distribution ─────────\n")

    n_close = deep_stat.d25_n_closures
    @printf("  Total closures recorded : %d", n_close)
    n_close > D25_MAX_CLOSURES && @printf("  (cap=%d; %d uncounted)", D25_MAX_CLOSURES, n_close - D25_MAX_CLOSURES)
    @printf("\n")

    close_al = deep_stat.d25_close_al
    close_px = deep_stat.d25_close_px
    n_rec    = length(close_al)

    if n_rec < 4
        @printf("  (fewer than 4 closure records — skipping D25)\n")
        return
    end

    n_store = length(store_al)

    # ── Build store grid ─────────────────────────────────────────────────────
    store_grid = zeros(Int, D25_GRID_SIZE, D25_GRID_SIZE)
    for i in 1:n_store
        al = store_al[i]; px = store_px[i]
        (al < 0 || px < 0) && continue
        al_bkt = clamp((al * D25_GRID_SIZE) ÷ max(1, ell), 0, D25_GRID_SIZE - 1)
        px_bkt = clamp(px * D25_GRID_SIZE ÷ max(1, p),     0, D25_GRID_SIZE - 1)
        @inbounds store_grid[al_bkt + 1, px_bkt + 1] += 1
    end
    n_store_valid = sum(store_grid)

    # ── Build closure grid ───────────────────────────────────────────────────
    close_grid = zeros(Int, D25_GRID_SIZE, D25_GRID_SIZE)
    n_close_valid = 0
    for i in 1:n_rec
        al = close_al[i]; px = close_px[i]
        (al < 0 || px < 0) && continue
        @inbounds close_grid[al + 1, px + 1] += 1
        n_close_valid += 1
    end

    @printf("  Store events used       : %d  Close events used: %d\n",
            n_store_valid, n_close_valid)

    if n_store_valid == 0 || n_close_valid == 0
        @printf("  (insufficient valid data — check al_cur/px_anchor wiring)\n")
        return
    end

    # ── Per-cell lift: (close_frac) / (store_frac) ──────────────────────────
    # Expected closure rate per cell under null (closures proportional to stores):
    #   lift(c) = (close_grid[c] / n_close_valid) / (store_grid[c] / n_store_valid)
    # Cells with zero stores are skipped.
    lifts = Float64[]
    lift_cells = NTuple{3, Float64}[]   # (lift, al_bkt, px_bkt)
    for ai in 1:D25_GRID_SIZE, pi in 1:D25_GRID_SIZE
        sc = store_grid[ai, pi]
        sc == 0 && continue
        cc = close_grid[ai, pi]
        store_frac = sc / n_store_valid
        close_frac = cc / n_close_valid
        lift = close_frac / store_frac
        push!(lifts, lift)
        push!(lift_cells, (lift, Float64(ai - 1), Float64(pi - 1)))
    end

    n_active = length(lifts)
    @printf("  Active (α,px) cells     : %d / %d\n", n_active, D25_GRID_SIZE * D25_GRID_SIZE)

    sort!(lift_cells, by = x -> -x[1])
    sort!(lifts)

    # Summary statistics
    lift_mean   = sum(lifts) / n_active
    lift_median = lifts[cld(n_active, 2)]
    lift_p90    = lifts[max(1, round(Int, 0.90 * n_active))]
    lift_max    = lifts[end]
    @printf("  Cell lift (close/store) : mean=%.3f  median=%.3f  p90=%.3f  max=%.3f\n",
            lift_mean, lift_median, lift_p90, lift_max)

    # Fraction of cells with lift > 2×, > 5×, > 10×
    n2  = count(x -> x > 2.0,  lifts)
    n5  = count(x -> x > 5.0,  lifts)
    n10 = count(x -> x > 10.0, lifts)
    @printf("  Cells with lift >2×: %d  >5×: %d  >10×: %d\n", n2, n5, n10)

    # Top-10 hottest cells
    @printf("\n  Top-10 cells by closure lift:\n")
    @printf("    %-6s  %-6s  %8s  %8s  %8s\n",
            "al_bkt", "px_bkt", "lift", "n_close", "n_store")
    for i in 1:min(10, length(lift_cells))
        lft, ai, pi = lift_cells[i]
        ai_i = Int(ai); pi_i = Int(pi)
        cc = close_grid[ai_i + 1, pi_i + 1]
        sc = store_grid[ai_i + 1, pi_i + 1]
        @printf("    %-6d  %-6d  %8.3f  %8d  %8d\n", ai_i, pi_i, lft, cc, sc)
    end

    # ── χ² test: are closures distributed proportionally to stores? ─────────
    # H0: closure cell counts ~ Multinomial(n_close, store_frac).
    # χ² = Σ (observed - expected)² / expected, df = n_active - 1.
    chi2 = 0.0
    for ai in 1:D25_GRID_SIZE, pi in 1:D25_GRID_SIZE
        sc = store_grid[ai, pi]
        sc == 0 && continue
        expected = n_close_valid * sc / n_store_valid
        observed = Float64(close_grid[ai, pi])
        chi2 += (observed - expected)^2 / max(1e-9, expected)
    end
    df = n_active - 1
    chi2_dof = chi2 / max(1, df)
    @printf("\n  χ² test (closures vs store null):  χ²/dof=%.3f  (dof=%d)\n", chi2_dof, df)
    if chi2_dof > 3.0
        @printf("    ↑ CONCENTRATED — closures do NOT follow store distribution\n")
        @printf("      Excess closure concentration explains α₂ < α (smaller effective space)\n")
    elseif chi2_dof > 1.5
        @printf("    ↑ Mild concentration — moderate α₂ suppression expected\n")
    else
        @printf("    ↑ Consistent with proportional — α₂ gap arises from marginal non-uniformity\n")
    end

    # ── Δα histogram ─────────────────────────────────────────────────────────
    dal = deep_stat.d25_dal_hist
    n_dal = sum(dal)
    @printf("\n  Δα = (α_close − α_store) mod ell  [%d buckets, n=%d with valid al_store]\n",
            D25_DAL_BUCKETS, n_dal)

    if n_dal >= 4
        # χ² vs uniform
        expected_per_bin = n_dal / D25_DAL_BUCKETS
        chi2_dal = sum((Float64(c) - expected_per_bin)^2 / max(1e-9, expected_per_bin)
                       for c in dal)
        chi2_dal_dof = chi2_dal / (D25_DAL_BUCKETS - 1)
        @printf("    χ²/dof vs uniform: %.3f\n", chi2_dal_dof)

        # Top-5 Δα buckets
        top5 = sort(collect(enumerate(dal)), by = x -> -x[2])[1:min(5, end)]
        @printf("    Top-5 Δα buckets (bkt → fraction of ell):\n")
        for (bkt, cnt) in top5
            frac = (bkt - 1) / D25_DAL_BUCKETS
            lift_b = cnt / max(1.0, expected_per_bin)
            @printf("      bkt=%-3d  Δα≈%.4f·ell  count=%d  lift=%.2f\n",
                    bkt - 1, frac, cnt, lift_b)
        end

        if chi2_dal_dof > 3.0
            @printf("    ↑ NON-UNIFORM Δα — step-table periodicity: second visits\n")
            @printf("      cluster at specific α-offsets from the stored entry.\n")
        else
            @printf("    ↑ Δα consistent with uniform — no strong step-table periodicity.\n")
        end
    else
        @printf("    (al_store unavailable or too few records — check neg_al wiring)\n")
    end

    # ── Depth-conditioned closure lift ───────────────────────────────────────
    close_depth = deep_stat.d25_close_depth
    depth_counts = zeros(Int, 8)
    for d in close_depth
        d >= 0 && (depth_counts[d + 1] += 1)
    end
    @printf("\n  Closure depth bands (log2-coarsened to 8 levels):\n")
    @printf("    %-6s  %8s  %8s\n", "band", "n_close", "frac%")
    for b in 1:8
        n = depth_counts[b]
        n == 0 && continue
        @printf("    %-6d  %8d  %7.1f%%\n", b - 1, n, 100.0 * n / n_rec)
    end

    flush(stdout)
end
