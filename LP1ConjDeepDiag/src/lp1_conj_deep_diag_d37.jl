# =============================================================================
#  lp1_conj_deep_diag_d37.jl  --  Report section D37.
#
#  D37 — LP1-conj closure-indexed spatial autocorrelation. Built to answer,
#  directly and without the D29 cursor artifact: is the α₂≈0.60 birthday
#  exponent's excess (vs the i.i.d. 0.5 baseline) coming from spatial (px)
#  structure in WHICH FB anchors keep closing against each other, or is it
#  purely an algebraic/key-level effect with no spatial component?
#
#  Why this exists alongside D29 rather than fixing D29 in place: D29
#  section 2 samples px at the single (P0 = cur_pt) site, once per valid
#  step, regardless of opcode. With LP2-affine disabled, NO code path ever
#  assigns cur_pt to anything but next_anchor()'s own deterministic
#  round-robin cursor (handle_1lp_affine!, handle_1lp_conj!, and
#  handle_2lp_conj! all return next_anchor_ref[]() unconditionally on every
#  internal path, including closures — see their source). So in this
#  configuration D29's px stream is 100% cursor, 0% walk-state, and its
#  "basin trapping" peak-ACF=1.0 result is entirely the cursor's own fixed
#  period, not a property of the walk.
#
#  D37 instead samples directly at the productive event itself: every
#  LP1-conj CLOSURE records px_close (= fb[i0][1], the closing FB anchor —
#  genuine walk state, never cursor-derived) and px_store (= fb[prev_col][1],
#  the FB anchor the close matched against). The sample is indexed by
#  CLOSURE ORDER, not raw step count: lag=k means "k closures apart," not
#  "k steps apart." This is the right axis for the question being asked —
#  whether consecutive (or near-consecutive) LP1-conj closures keep landing
#  on spatially nearby FB anchors — and trades step-time resolution for
#  freedom from the cursor artifact.
#
#  Cross-thread handling: closures from different threads are NOT
#  concatenated into one series (unlike D29/D35/D25's flat-vector merge).
#  Closures are comparatively rare, so splicing thread A's last closure
#  directly against thread B's first would create lag pairs with no real
#  temporal relationship, and at lags approaching D37_ACF_LAG_HI this
#  contamination would not be negligible (it is negligible for D29's
#  every-step sampling, where each thread contributes millions of points,
#  but not here). Instead, _report_d37 computes Pearson ACF independently
#  within EACH thread's own closure-ordered chain (deep_stat.d37_chains),
#  then pools the resulting per-thread z-scores at each lag via Stouffer's
#  method (sum of z / sqrt(n_chains)) — the standard way to combine
#  independent test statistics for the same null hypothesis without
#  pretending they're one sample.
# =============================================================================

# ---------------------------------------------------------------------------
#  _d37_lag_grid — dense lags 1..D37_ACF_LAG_HI, in CLOSURE count (not steps).
# ---------------------------------------------------------------------------
function _d37_lag_grid()::Vector{Int}
    return collect(D37_ACF_LAG_LO:D37_ACF_LAG_STRIDE:D37_ACF_LAG_HI)
end

# ---------------------------------------------------------------------------
#  _d37_chain_acf_z — Pearson ACF and z-score (vs i.i.d. null) for ONE
#  thread's closure-ordered series, at a given closure-lag. Returns
#  `nothing` if the chain is too short to test this lag (caller should skip
#  this chain/lag combination rather than padding with a fabricated value).
# ---------------------------------------------------------------------------
function _d37_chain_acf_z(x::Vector{Float64}, lag::Int)::Union{Float64, Nothing}
    n = length(x)
    lag <= 0 && return nothing
    lag >= n && return nothing
    n_eff = n - lag
    n_eff < 8 && return nothing   # too few pairs for a meaningful z (arbitrary small-sample floor)
    val = _d29_pearson_acf(x, lag)          # reuse D29's Pearson ACF helper — same math, different series
    z   = _d29_pearson_acf_z(val, n_eff)    # reuse D29's z-score helper
    return z
end

# ---------------------------------------------------------------------------
#  _d37_pool_z — Stouffer's method: combine independent z-scores into one
#  pooled z. Returns (pooled_z, n_chains_used). Chains contributing `nothing`
#  at this lag (too short) are excluded, not zero-filled.
# ---------------------------------------------------------------------------
function _d37_pool_z(zs::Vector{Float64})::Tuple{Float64, Int}
    isempty(zs) && return (0.0, 0)
    return (sum(zs) / sqrt(Float64(length(zs))), length(zs))
end

# ---------------------------------------------------------------------------
#  _d37_spatial_acf_report — runs the per-chain ACF + Stouffer-pool sweep
#  for one named series (px_close or px_store) across all chains, and
#  prints the summary. Returns the pooled z at the peak lag, or `nothing`
#  if no chain had enough closures to test anything.
# ---------------------------------------------------------------------------
function _d37_spatial_acf_report(chains::Vector{Vector{Float64}}, label::String)::Union{Float64, Nothing}
    lags = _d37_lag_grid()
    best_lag = -1
    best_abs_pooled_z = -1.0
    best_pooled_z = 0.0
    best_n_chains = 0
    n_sig = 0
    n_lags_tested = 0

    for lag in lags
        zs = Float64[]
        for chain in chains
            z = _d37_chain_acf_z(chain, lag)
            z !== nothing && push!(zs, z)
        end
        isempty(zs) && continue
        n_lags_tested += 1
        pooled_z, n_used = _d37_pool_z(zs)
        if abs(pooled_z) > best_abs_pooled_z
            best_abs_pooled_z = abs(pooled_z)
            best_pooled_z     = pooled_z
            best_lag          = lag
            best_n_chains     = n_used
        end
        abs(pooled_z) >= D29_Z_SIG && (n_sig += 1)
    end

    if n_lags_tested == 0
        @printf("      [%s] no chain had enough closures to test any lag — skipped\n", label)
        return nothing
    end

    @printf("      [%s] peak pooled |z|=%.2f at lag=%d closures  (pooled over %d/%d chains)%s\n",
            label, best_abs_pooled_z, best_lag, best_n_chains, length(chains),
            best_abs_pooled_z >= D29_Z_SIG ? "  ← SIGNIFICANT vs i.i.d. null" : "")
    @printf("      [%s] lags with pooled |z|>=%.1f out of %d tested: %d\n",
            label, D29_Z_SIG, n_lags_tested, n_sig)
    return best_pooled_z
end

# ---------------------------------------------------------------------------
#  _report_d37 — closure-indexed spatial ACF on px_close and px_store,
#  pooled across per-thread chains via Stouffer's method.
# ---------------------------------------------------------------------------
function _report_d37(deep_stat::ConjDeepStat; p::Int = 0, ell::Int = 0)
    @printf("\n  D37 — LP1-conj closure-indexed spatial ACF (cursor-artifact-free, see docstring)\n")
    @printf("  ─────────────────────────────────────────────────────────────────\n")

    n_chains = length(deep_stat.d37_chains)
    @printf("    Closures observed (uncapped, all threads) : %d\n", deep_stat.d37_n_closures)
    @printf("    Threads contributing a closure chain      : %d\n", n_chains)

    if n_chains == 0
        @printf("    (no LP1-conj closures recorded — nothing to test)\n\n")
        return nothing
    end

    chain_lens = [length(c.px_close) for c in deep_stat.d37_chains]
    sorted_lens = sort(chain_lens)
    @printf("    Per-chain closure counts: min=%d  median=%d  max=%d\n",
            sorted_lens[1], sorted_lens[cld(length(sorted_lens), 2)], sorted_lens[end])

    min_chain_for_test = D37_ACF_LAG_LO + 8   # mirrors the n_eff>=8 floor in _d37_chain_acf_z
    n_usable_chains = count(>=(min_chain_for_test), chain_lens)
    if n_usable_chains == 0
        @printf("    (no chain has enough closures (>= %d) to test even lag=%d — too few closures per thread for this diagnostic at current run length)\n\n",
                min_chain_for_test, D37_ACF_LAG_LO)
        return nothing
    end

    # ── px_close: spatial structure of the CLOSING anchor, in closure order ──
    @printf("\n    1. px_close spatial ACF (closing FB anchor, lags 1..%d closures)\n", D37_ACF_LAG_HI)
    @printf("    -----------------------------------------------------------------\n")
    close_chains = [Float64.(c.px_close) for c in deep_stat.d37_chains if length(c.px_close) >= min_chain_for_test]
    z_close = _d37_spatial_acf_report(close_chains, "px_close")

    # ── px_store: spatial structure of the STORED anchor each close matched against ──
    @printf("\n    2. px_store spatial ACF (stored FB anchor, lags 1..%d closures)\n", D37_ACF_LAG_HI)
    @printf("    -----------------------------------------------------------------\n")
    store_chains = [Float64.(c.px_store) for c in deep_stat.d37_chains if length(c.px_store) >= min_chain_for_test]
    z_store = _d37_spatial_acf_report(store_chains, "px_store")

    @printf("\n    Verdict:\n")
    sig_close = z_close !== nothing && abs(z_close) >= D29_Z_SIG
    sig_store = z_store !== nothing && abs(z_store) >= D29_Z_SIG
    if sig_close || sig_store
        @printf("      → Spatial structure detected in LP1-conj closures (cursor-artifact-free).\n")
        sig_close && @printf("        px_close shows significant closure-lag autocorrelation: which FB anchor\n        CLOSES tends to repeat at nearby closures.\n")
        sig_store && @printf("        px_store shows significant closure-lag autocorrelation: which FB anchor\n        gets MATCHED AGAINST tends to repeat at nearby closures.\n")
        @printf("      This is consistent with α₂'s excess (vs 0.5) having a genuine spatial\n")
        @printf("      component, not just a key/algebraic-level effect.\n")
    else
        @printf("      → No significant closure-lag spatial autocorrelation in either px_close or\n")
        @printf("        px_store. If the key-level autocorrelation driving α₂≈0.60 is real and not\n")
        @printf("        itself an artifact, this result points AWAY from spatial/basin structure as\n")
        @printf("        its source — look at the algebraic/key-construction side instead (e.g. how\n")
        @printf("        lp_key/CanonicalLP1Key values are derived, not where their FB anchors sit).\n")
    end

    @printf("\n")
    return nothing
end
