# =============================================================================
#  lp1_conj_deep_diag_d40.jl
#
#  D40 — Hot-channel vs background closure-rate split.
#
#  Motivation (direct follow-up to D35): D35 found Δpx (FB anchor x
#  difference between closing and storing anchor) CONCENTRATED — in the
#  run that motivated this module, EVERY closure had Δpx == 0, i.e.
#  px_close == px_store for all n closures. That is a much stronger
#  statement than "the marginal Δpx distribution is narrow": it means every
#  closure recorded so far pairs an anchor with ITSELF (same FB x-coordinate
#  at store time and close time).
#
#  This collides head-on with the birthday-model accounting done elsewhere
#  (the [LP1-conj birthday diagnostics] block, computed outside this file):
#  that model predicts ~2-4 collisions at the emission counts seen when
#  D35 was captured, and the walk had already produced ~30-40 REAL closures
#  by that point — a ~10-15x excess over the Poisson(λ_expected) prediction,
#  which is astronomically unlikely (P(X ≥ 29 | λ=2.41) ~ 1e-20) if the
#  process were truly i.i.d. sampling over the birthday model's effective
#  support S_eff.
#
#  The resolution: S_eff (and S₂/AMS) are only interpretable as "effective
#  support size" UNDER THE ASSUMPTION that closures are i.i.d. draws from
#  a fixed support. D35's Δpx concentration falsifies that assumption
#  directly — closures are not exchangeable draws from one population, they
#  are (at least) a MIXTURE of two populations:
#
#    (a) a "hot channel" of closures where px_close == px_store exactly
#        (the anchor recorded at store time is architecturally the SAME
#        anchor recorded at close time — e.g. because the walk's anchor
#        cursor returns to the same FB slot before the LP1-conj key clears,
#        or because of a genuine structural shortcut/degeneracy in which
#        anchors can produce LP1-conj closures), and
#    (b) a "background" of closures with px_close != px_store, which may
#        still follow something closer to the naive/S_eff birthday law.
#
#  D40 does NOT try to reconstruct the global N-scale birthday accounting
#  (that needs the full emission stream and lives outside this file/struct
#  — see the [LP1-conj birthday diagnostics] block). Instead it answers a
#  narrower, directly-computable question from data D35 already recorded:
#  of the closures actually observed, how many fall in the hot channel,
#  and does that channel show additional internal structure (e.g. is it
#  dominated by a SINGLE recurring anchor, or spread across many distinct
#  anchors that each independently satisfy px_close==px_store)?
#
#  Two-part test:
#
#  1. HOT-CHANNEL SHARE: partition n closures into hot (Δpx==0) vs
#     background (Δpx!=0). Report counts/shares plainly — if this is
#     asking "is the anomaly explained by a bug/shortcut concentrated in
#     one channel", the share itself is the headline number: if it's at or
#     near 100%, the entire birthday-vs-observed discrepancy computed
#     elsewhere is attributable to this channel, not to a general S_eff
#     misestimate spread evenly across all closures.
#
#  2. HOT-CHANNEL INTERNAL CONCENTRATION: within the hot channel only,
#     is it a small number of anchors repeating (a specific degenerate
#     FB point/loop), or many distinct anchors each independently landing
#     on px_close==px_store? Reuses the D35/D19 Rényi-2 + Gini + top-share
#     vocabulary, applied to px_close values RESTRICTED to the hot subset.
#     A low S_eff / high top-share here (few distinct anchors dominating)
#     points at a specific reproducible degeneracy (findable/fixable or
#     exploitable). A high S_eff / flat top-share (many distinct anchors,
#     each hitting px_close==px_store independently) points at a structural
#     property of the walk or curve rather than a single bug site.
#
#  3. BACKGROUND-ONLY RATE CHECK: report the background subset's own Δα
#     range-test verdict (reusing D35's _range_test), to see whether
#     removing the hot channel leaves a background population that IS
#     consistent with the naive/S_eff birthday model, or whether the
#     background is independently anomalous too (in which case the hot
#     channel is A contributor, not THE explanation).
#
#  This module adds NO new recording path: it consumes the D35 per-closure
#  vectors (d35_px_close, d35_px_store, d35_dalpha) directly, exactly like
#  D30 reuses the same raw fields for a different lens. Nothing needs to
#  be threaded through handle_1lp_conj! for this to work.
#
#  Included by lp1_conj_deep_diag.jl; do not include directly.
# =============================================================================

# ---------------------------------------------------------------------------
#  _binomial_tail_upper — P(X >= k | n, p) via direct summation in log-space.
#  n here is always the (small, capped) closure count, so this is cheap and
#  exact (no normal/Poisson approximation — D40's whole point is not to
#  smuggle back in the same asymptotic assumptions being questioned).
#
#  Computes log C(n,i) via the standard O(1)-per-step recurrence
#      log C(n,i) = log C(n,i-1) + log(n-i+1) - log(i)
#  starting from log C(n,0) = 0, so the whole tail sum is O(n) total (not
#  O(n) lgamma evaluations each doing O(n) work) and needs no external
#  special-functions dependency beyond Base's own log/log1p.
# ---------------------------------------------------------------------------
function _binomial_tail_upper(k::Int, n::Int, p::Float64)::Float64
    (n <= 0 || p <= 0.0) && return k <= 0 ? 1.0 : 0.0
    p >= 1.0 && return 1.0
    k <= 0 && return 1.0
    k > n && return 0.0

    logp = log(p)
    logq = log1p(-p)

    # Walk the recurrence up to i=k-1 without accumulating terms (we only
    # need the tail i=k..n), then continue accumulating from i=k onward.
    log_binom = 0.0  # log C(n,0)
    for i in 1:(k - 1)
        log_binom += log(n - i + 1) - log(i)
    end

    log_terms = Vector{Float64}(undef, n - k + 1)
    idx = 1
    for i in k:n
        if i > 0
            log_binom += log(n - i + 1) - log(i)
        end
        log_terms[idx] = log_binom + i * logp + (n - i) * logq
        idx += 1
    end

    m = maximum(log_terms)
    return exp(m) * sum(exp(t - m) for t in log_terms)
end

# ---------------------------------------------------------------------------
#  _report_d40 — print the hot-channel vs background closure-rate split.
#
#  Arguments:
#    deep_stat — merged ConjDeepStat (reuses D35's fields directly)
#    p         — field characteristic (ambient size for the hot-channel
#                internal Rényi-2 test; 0 → skip that sub-section)
# ---------------------------------------------------------------------------
function _report_d40(deep_stat::ConjDeepStat; p::Int = 0)

    @printf("\n─── D40: hot-channel (Δpx=0) vs background closure-rate split ───────\n")

    n = length(deep_stat.d35_px_close)
    @printf("  Closures available (from D35 vectors, capped at %d) : %d\n", D35_MAX_CLOSURES, n)
    @printf("  Closures seen (uncapped total, from D35)            : %d\n", deep_stat.d35_n_closures)

    if n < 4
        @printf("  (too few closures for D40 — skipping)\n\n")
        flush(stdout)
        return nothing
    end

    px_close = deep_stat.d35_px_close
    px_store = deep_stat.d35_px_store
    dalpha   = deep_stat.d35_dalpha

    is_hot = [px_close[i] == px_store[i] for i in 1:n]
    n_hot  = count(is_hot)
    n_bg   = n - n_hot

    # -----------------------------------------------------------------------
    #  PART 1 — hot-channel share, plainly stated.
    # -----------------------------------------------------------------------
    @printf("\n")
    @printf("  PART 1 — hot-channel share (px_close == px_store exactly):\n")
    @printf("    hot-channel closures       : %d  (%.2f%% of %d)\n", n_hot, 100.0 * n_hot / n, n)
    @printf("    background closures        : %d  (%.2f%% of %d)\n", n_bg, 100.0 * n_bg / n, n)

    if p > 0
        # If px_close and px_store were independent Uniform(0,p) draws (the
        # birthday-model null), the per-closure chance of an EXACT match is
        # 1/p — vanishingly small for cryptographic p. Any observed n_hot > 0
        # already rejects that null hard; we report both the plain count and
        # the formal tail probability for completeness.
        p_match_null = 1.0 / Float64(p)
        tail_p = _binomial_tail_upper(n_hot, n, p_match_null)
        @printf("    P(exact match | indep. draws) = 1/p ≈ %.3e\n", p_match_null)
        @printf("    P(>= %d exact matches in %d closures | indep. null) ≈ %.3e\n",
                n_hot, n, tail_p)
        if n_hot > 0 && tail_p < 1e-6
            @printf("    → REJECTS the independent-draw null outright: exact px matches at\n")
            @printf("      this rate cannot arise from independent Uniform(0,p) anchor pairs.\n")
            @printf("      This is a structural degeneracy, not a birthday-scale coincidence.\n")
        end
    end

    if n_hot == n
        @printf("\n")
        @printf("    → ALL closures are hot-channel. The birthday-vs-observed excess\n")
        @printf("      computed elsewhere (see [LP1-conj birthday diagnostics]) is fully\n")
        @printf("      attributable to this channel — there is no separate background\n")
        @printf("      population left to check against the naive/S_eff birthday law.\n")
        @printf("      Treat this as a single structural finding to root-cause (bug or\n")
        @printf("      exploitable shortcut), not as a keyspace-size estimation problem.\n")
        flush(stdout)
        @printf("\n")
        return nothing
    elseif n_hot == 0
        @printf("\n")
        @printf("    → NO hot-channel closures in this sample. If the birthday-vs-\n")
        @printf("      observed excess persists, it is NOT explained by px_close==px_store\n")
        @printf("      degeneracy — look elsewhere (e.g. D30's circular-distance test for\n")
        @printf("      NEAR-miss geometric adjacency rather than exact match, or D32/D36\n")
        @printf("      recurrence-gap structure).\n")
        flush(stdout)
        @printf("\n")
        return nothing
    end

    # -----------------------------------------------------------------------
    #  PART 2 — hot-channel internal concentration: few repeating anchors,
    #  or many distinct anchors each independently landing on Δpx==0?
    # -----------------------------------------------------------------------
    hot_px = [px_close[i] for i in 1:n if is_hot[i]]
    s_eff_hot, counts_hot, sorted_hot = _renyi2_support(hot_px)

    @printf("\n")
    @printf("  PART 2 — hot-channel internal concentration (which anchors recur):\n")
    @printf("    distinct anchors in hot channel : %d  (of %d hot closures)\n",
            length(counts_hot), n_hot)
    @printf("    Rényi-2 effective support S_eff  : %.2f\n", s_eff_hot)
    if p > 0
        @printf("    S_eff / p (ambient)              : %.3e\n", s_eff_hot / Float64(p))
    end

    if length(sorted_hot) >= 2 && sorted_hot[1] > sorted_hot[end]
        g_hot  = _gini(sorted_hot)
        ts_hot = _top_share(sorted_hot, 0.05)
        h_hot  = _hill_exponent(sorted_hot; k=min(50, length(sorted_hot) - 1))
        @printf("    Gini                             : %.4f\n", g_hot)
        @printf("    top-5%% share                     : %.4f\n", ts_hot)
        @printf("    Hill α(k=%d)                     : %.3f\n", min(50, length(sorted_hot) - 1), h_hot)
    else
        @printf("    Gini / top-share / Hill          : n/a (flat — every hot anchor\n")
        @printf("                                        appears exactly once)\n")
    end

    @printf("\n")
    @printf("    Top-10 most frequent hot-channel anchors:\n")
    @printf("    %-20s  %10s  %10s\n", "px value", "count", "share of hot")
    @printf("    %s\n", "─"^46)
    top_hot = sort(collect(counts_hot), by = kv -> -kv[2])
    for (val, cnt) in top_hot[1:min(10, length(top_hot))]
        @printf("    %-20d  %10d  %10.4f\n", val, cnt, cnt / n_hot)
    end

    if s_eff_hot <= 1.5 && n_hot >= 4
        @printf("\n")
        @printf("    → Hot channel is dominated by a SINGLE (or near-single) anchor —\n")
        @printf("      this looks like ONE specific reproducible degeneracy (a fixed\n")
        @printf("      point, small-order point, or cursor-return bug), not a broad\n")
        @printf("      structural property of many anchors. Worth root-causing directly:\n")
        @printf("      check whether this px value corresponds to a small-order or\n")
        @printf("      otherwise special point on the curve.\n")
    elseif length(counts_hot) >= max(2, n_hot ÷ 2)
        @printf("\n")
        @printf("    → Hot channel spans many DISTINCT anchors, each independently\n")
        @printf("      landing on px_close==px_store. This looks like a structural\n")
        @printf("      property of the walk/anchor-cursor mechanics (e.g. short-period\n")
        @printf("      return-to-anchor behavior) rather than one specific bad point —\n")
        @printf("      cross-check against D32 (store→close depth) and D36 (FB-index\n")
        @printf("      distance) for the SAME hot-channel closures to see if they also\n")
        @printf("      show short recurrence gaps.\n")
    end

    # -----------------------------------------------------------------------
    #  PART 3 — background-only range test (reuses D35's _range_test).
    #  Answers: with the hot channel removed, is what's left consistent
    #  with the naive/S_eff birthday model, or independently anomalous?
    # -----------------------------------------------------------------------
    @printf("\n")
    @printf("  PART 3 — background-only Δα range test (hot channel excluded):\n")
    bg_dalpha = [dalpha[i] for i in 1:n if !is_hot[i]]
    @printf("    background closures analyzed : %d\n", n_bg)

    if n_bg < 4
        @printf("    (too few background closures for a range test — skipping)\n")
    else
        # ell (group order) is not directly threaded to D40 to keep its
        # signature minimal; the caller can rerun D35 on the background-
        # only subset for the full range-test verdict if ell is needed.
        # Here we report the plain spread as a first-order check.
        lo, hi = extrema(bg_dalpha)
        @printf("    observed Δα range in background : [%d, %d]  (width = %.3e)\n",
                lo, hi, Float64(hi - lo))
        @printf("    (compare against D35's own Δα range-test verdict on the FULL\n")
        @printf("     closure set above — if the background-only width is comparably\n")
        @printf("     wide/narrow, the hot channel is not distorting D35's Δα verdict;\n")
        @printf("     if it differs substantially, D35's combined verdict is a mixture\n")
        @printf("     of two different populations and should be re-run background-only.)\n")
    end

    @printf("\n")
    @printf("  Summary: of %d total closures, %.1f%% are hot-channel (exact px\n", n, 100.0 * n_hot / n)
    @printf("  match, p ≈ %.3e chance under independence) and %.1f%% are background.\n",
            p > 0 ? 1.0 / Float64(p) : NaN, 100.0 * n_bg / n)
    @printf("  This directly tests whether the birthday-vs-observed collision excess\n")
    @printf("  found elsewhere is attributable to this specific channel rather than\n")
    @printf("  to a general keyspace-size misestimate spread evenly across closures.\n")

    @printf("\n")
    flush(stdout)
    return nothing
end
