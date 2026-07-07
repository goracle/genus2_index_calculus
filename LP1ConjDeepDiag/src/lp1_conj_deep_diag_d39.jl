# =============================================================================
#  lp1_conj_deep_diag_d39.jl  --  report section D39: closure-indexed
#  sequential autocorrelation of α, P_fb, and the difference process Δα.
#
#  See the D39 constants-block docstring in lp1_conj_deep_diag_core.jl for
#  the full hypothesis writeup. Short version: the closure identity
#
#      atom(R) + atom(S)  ==  neg_al·G  -  atom(P_fb)                    (*)
#
#  means that if LP1-conj keys (which encode atom(R)+atom(S)) carry real
#  sequential autocorrelation, it must show up on the RHS too. This module
#  tests the RHS directly via two tractable proxies — the raw scalar
#  neg_al (standing in for neg_al·G, since G is a fixed generator for the
#  whole run) and px_anchor (= fb[i0][1], standing in for atom(P_fb)) —
#  plus the difference process combined_al (Δα), which is the *sequential*
#  complement to D35's *support-concentration* test on the same quantity.
#
#  Design mirrors D37 throughout:
#    - per-thread closure-ordered chains, NOT concatenated across threads
#      (closures are sparse; splicing would inject spurious lag pairs at
#      thread boundaries — see merge_conj_deep_stats D39 comment)
#    - ACF computed within each chain separately (sample Pearson
#      autocorrelation at each lag), then z-scores are pooled across
#      chains via an inverse-variance-weighted mean (each chain's ACF
#      estimate at lag L has approximate variance 1/(n_chain - L) under
#      the i.i.d. null, by the standard Bartlett large-sample formula)
#    - only chains with at least D39_MIN_CHAIN_LEN points contribute to a
#      given lag, exactly mirroring D37's "pooled over k/n chains" readout
# =============================================================================

const D39_MIN_CHAIN_LEN = 4   # need at least a few points before ACF at lag 1 is meaningful

# ---------------------------------------------------------------------------
#  _seq_acf_z(x, lag) -> (r, z, n_pairs)
#
#  Sample Pearson autocorrelation of vector x at the given lag, plus its
#  z-score against the i.i.d.-null standard error 1/sqrt(n - lag) (Bartlett,
#  first-lag large-sample approximation — same convention D29 already uses
#  for its circular-ACF z-scores in this codebase).
#
#  Returns (NaN, NaN, 0) if there are fewer than 2 valid pairs.
# ---------------------------------------------------------------------------
function _seq_acf_z(x::Vector{Int}, lag::Int)::Tuple{Float64,Float64,Int}
    n = length(x)
    n_pairs = n - lag
    n_pairs < 2 && return (NaN, NaN, 0)

    xf = Float64.(x)
    mu = sum(xf) / n
    denom = 0.0
    @inbounds for i in 1:n
        d = xf[i] - mu
        denom += d * d
    end
    denom == 0.0 && return (NaN, NaN, 0)   # degenerate (constant series)

    numer = 0.0
    @inbounds for i in 1:n_pairs
        numer += (xf[i] - mu) * (xf[i+lag] - mu)
    end
    r = numer / denom
    se = 1.0 / sqrt(Float64(n_pairs))
    z = r / se
    return (r, z, n_pairs)
end

# ---------------------------------------------------------------------------
#  _pooled_acf_over_chains(chains, field, lags; min_len) -> Vector{(lag, pooled_z, n_chains_used, max_abs_r)}
#
#  For each lag, computes per-chain (r, z) via _seq_acf_z on chains long
#  enough to support that lag, then pools the z-scores with inverse-
#  variance weighting (weight = n_pairs, since Var(z) ≈ 1 under the null
#  by construction — so this reduces to a pairs-weighted mean of z, the
#  natural pooling rule when each chain's z is already on a common scale).
# ---------------------------------------------------------------------------
function _pooled_acf_over_chains(chains::Vector{Vector{Int}}, lags::AbstractVector{Int};
                                  min_len::Int = D39_MIN_CHAIN_LEN)
    results = NamedTuple{(:lag,:pooled_z,:n_chains,:max_abs_r),Tuple{Int,Float64,Int,Float64}}[]
    for lag in lags
        wsum   = 0.0
        zsum   = 0.0
        nchain = 0
        max_abs_r = 0.0
        for ch in chains
            length(ch) < max(min_len, lag + 2) && continue
            r, z, n_pairs = _seq_acf_z(ch, lag)
            isnan(z) && continue
            w = Float64(n_pairs)
            wsum += w
            zsum += w * z
            nchain += 1
            max_abs_r = max(max_abs_r, abs(r))
        end
        pooled_z = nchain > 0 ? zsum / sqrt(wsum) : NaN
        # ^ pooling rule: Σ w_i z_i / sqrt(Σ w_i) is the standard inverse-
        #   variance-weighted combination when Var(z_i) ≈ 1/w_i under H0,
        #   so the combined statistic is again ~N(0,1) under H0.
        push!(results, (lag=lag, pooled_z=pooled_z, n_chains=nchain, max_abs_r=max_abs_r))
    end
    return results
end

# ---------------------------------------------------------------------------
#  _report_d39 — top-level report section.
# ---------------------------------------------------------------------------
function _report_d39(deep_stat::ConjDeepStat)
    chains = deep_stat.d39_chains
    n_total = deep_stat.d39_n_closures

    @printf("\n  D39 — Closure-indexed sequential autocorrelation (α, P_fb, Δα)\n")
    @printf("  ─────────────────────────────────────────────────────────────────\n")
    @printf("    Closures observed (uncapped, all threads) : %d\n", n_total)

    if isempty(chains)
        @printf("    (no chains recorded — skipping; D39 needs at least one closure\n")
        @printf("     to build a chain. Was record_d39_closure! wired into the\n")
        @printf("     handle_1lp_conj! close path?)\n")
        return nothing
    end

    chain_lens = [length(c.neg_al) for c in chains]
    sorted_lens = sort(chain_lens)
    median_len = sorted_lens[cld(length(sorted_lens), 2)]
    @printf("    Threads contributing a closure chain      : %d\n", length(chains))
    @printf("    Per-chain closure counts: min=%d  median=%d  max=%d\n",
            minimum(chain_lens), median_len, maximum(chain_lens))

    max_len = maximum(chain_lens)
    # Cap tested lags at both the configured ceiling and what the data can
    # actually support (no point testing lag 500 against chains of length 10).
    lag_hi = min(D39_ACF_LAG_HI, max(1, max_len - D39_MIN_CHAIN_LEN))
    lags = D39_ACF_LAG_LO:D39_ACF_LAG_STRIDE:lag_hi
    if isempty(lags)
        @printf("    (chains too short for any tested lag — skipping ACF tables)\n")
        return nothing
    end

    series_defs = (
        (label = "neg_al      (proxy for α·a)",   field = c -> c.neg_al),
        (label = "px_anchor   (proxy for P_fb)",  field = c -> c.px_anchor),
        (label = "combined_al (Δα, difference process)", field = c -> c.combined_al),
    )

    for sd in series_defs
        vecs = [sd.field(c) for c in chains]
        results = _pooled_acf_over_chains(vecs, lags)
        valid = filter(r -> !isnan(r.pooled_z), results)

        @printf("\n    %s\n", sd.label)
        @printf("    -----------------------------------------------------------------\n")
        if isempty(valid)
            @printf("      (no chain long enough to support any tested lag)\n")
            continue
        end

        best = valid[argmax(abs.(getfield.(valid, :pooled_z)))]
        @printf("      peak pooled |z|=%.2f at lag=%d closures  (pooled over %d/%d chains)\n",
                abs(best.pooled_z), best.lag, best.n_chains, length(chains))

        n_sig = count(r -> abs(r.pooled_z) >= 3.0, valid)
        @printf("      lags with pooled |z|>=3.0 out of %d tested: %d\n", length(valid), n_sig)

        if n_sig > 0
            sig_lags = [r.lag for r in valid if abs(r.pooled_z) >= 3.0]
            shown = sig_lags[1:min(10, length(sig_lags))]
            @printf("      significant lags (first %d): %s%s\n",
                    length(shown), join(shown, ", "),
                    length(sig_lags) > length(shown) ? ", ..." : "")
        end
    end

    # --- Verdict ---
    @printf("\n    Verdict:\n")
    al_vecs = [c.neg_al for c in chains]
    px_vecs = [c.px_anchor for c in chains]
    dal_vecs = [c.combined_al for c in chains]
    al_res  = filter(r -> !isnan(r.pooled_z), _pooled_acf_over_chains(al_vecs, lags))
    px_res  = filter(r -> !isnan(r.pooled_z), _pooled_acf_over_chains(px_vecs, lags))
    dal_res = filter(r -> !isnan(r.pooled_z), _pooled_acf_over_chains(dal_vecs, lags))

    al_sig  = any(r -> abs(r.pooled_z) >= 3.0, al_res)
    px_sig  = any(r -> abs(r.pooled_z) >= 3.0, px_res)
    dal_sig = any(r -> abs(r.pooled_z) >= 3.0, dal_res)

    if al_sig
        @printf("      → SIGNIFICANT sequential autocorrelation in neg_al (α). Under the\n")
        @printf("        fixed-generator argument (see constants-block docstring), this is\n")
        @printf("        real structure in the walk's α trajectory and is consistent with\n")
        @printf("        the closure-identity hypothesis: autocorrelation in atom(R)+atom(S)\n")
        @printf("        showing up on the α side of (*). Caveat: this does NOT by itself\n")
        @printf("        prove autocorrelation in the group element α·a — only in the\n")
        @printf("        scalar α — see docstring for why that gap cannot be closed without\n")
        @printf("        per-closure Jacobian scalar multiplication (out of scope here).\n")
    else
        @printf("      → No significant sequential autocorrelation detected in neg_al (α)\n")
        @printf("        at the tested lags/sample size. Does not rule out structure at\n")
        @printf("        lags beyond %d closures or below this n's detection power.\n", lag_hi)
    end

    if px_sig
        @printf("      → SIGNIFICANT sequential autocorrelation in px_anchor (P_fb).\n")
    else
        @printf("      → No significant sequential autocorrelation detected in px_anchor\n")
        @printf("        (P_fb) at the tested lags/sample size.\n")
    end

    if dal_sig
        @printf("      → SIGNIFICANT sequential autocorrelation in combined_al (Δα). This\n")
        @printf("        is the autocorrelation question D35 could not ask (D35 tests\n")
        @printf("        whether Δα's SUPPORT is narrow, not whether consecutive Δα values\n")
        @printf("        are correlated) — a positive result here is direct evidence for\n")
        @printf("        the autocorrelated-keys hypothesis driving α₂≈0.59–0.60.\n")
    else
        @printf("      → No significant sequential autocorrelation detected in combined_al\n")
        @printf("        (Δα) at the tested lags/sample size.\n")
    end

    if !al_sig && !px_sig && !dal_sig
        @printf("\n      Combined: none of the three closure-indexed proxies show\n")
        @printf("      significant sequential autocorrelation at n=%d closures / lags up\n", n_total)
        @printf("      to %d. Either the α₂ pinning's autocorrelation signature lives\n", lag_hi)
        @printf("      below this layer's detection power at current sample size, or it\n")
        @printf("      is not visible through these particular proxies — consider rerunning\n")
        @printf("      D39 once closure count has grown substantially (cf. D35's caveat),\n")
        @printf("      or revisit the key-construction-downstream-of-a hypothesis from D31.\n")
    end

    _report_d39b(chains)
    _report_d39c(deep_stat)

    return nothing
end

# =============================================================================
#  D39b — phase-locked closure diagnostic (addendum).
#
#  See the D39b constants-block docstring in lp1_conj_deep_diag_core.jl for
#  the full hypothesis writeup. Short version: D39's autocorrelation result
#  could be genuine algebraic/spatial structure, OR it could be an artifact
#  of closures preferentially landing on a repeating step-table slot (which
#  would inherit a fixed increment, manufacturing spurious sequential
#  structure). This section tests for that confound directly using the
#  newly-recorded d39_phase series (step-table slot `si` at each closure).
# =============================================================================

# ---------------------------------------------------------------------------
#  _discretize(x, n_bins) -> Vector{Int}  (1-based bin index)
#
#  Quantile-ish bucketing: equal-width bins over [min(x), max(x)]. Used to
#  discretize α/P/Δα (which are integers over a wide range) into a small
#  number of bins for the MI estimate — plain integer values would make
#  every value its own bin, giving a degenerate (maximal, meaningless) MI.
# ---------------------------------------------------------------------------
function _discretize(x::Vector{Int}, n_bins::Int)::Vector{Int}
    isempty(x) && return Int[]
    lo, hi = minimum(x), maximum(x)
    hi == lo && return ones(Int, length(x))
    width = (hi - lo) / n_bins
    return [clamp(1 + Int(floor((xi - lo) / width)), 1, n_bins) for xi in x]
end

# ---------------------------------------------------------------------------
#  _conditional_mi(joint_with, phase_t, phase_t1; n_bins, n_shuffle) ->
#      (mi_bits, null_mean_bits, null_std_bits, z)
#
#  Estimates I((α_t,P_t,Δα_t); phase_{t+1} | phase_t) via the standard
#  decomposition I(X;Y|Z) = H(Y|Z) - H(Y|X,Z), implemented as plug-in
#  (maximum-likelihood) entropy estimates over discretized joint counts —
#  consistent with how D29's mutual-information readout is described in
#  the existing log output (binned MI against a shuffle null).
#
#  joint_with : Vector{Int}, the discretized (α_t,P_t,Δα_t) JOINT label at
#               each consecutive-pair index (one combined label per pair;
#               see _report_d39b for how the three series are combined)
#  phase_t    : Vector{Int}, phase at closure t (the EARLIER of the pair)
#  phase_t1   : Vector{Int}, phase at closure t+1 (the LATER of the pair)
#
#  Null: phase_t1 is randomly shuffled n_shuffle times (breaking any real
#  t -> t+1 phase relationship while preserving each series' own marginal),
#  and the conditional MI is recomputed each time. z is the observed MI's
#  z-score against this null distribution.
# ---------------------------------------------------------------------------
function _conditional_mi(joint_with::Vector{Int}, phase_t::Vector{Int}, phase_t1::Vector{Int};
                          n_shuffle::Int = 200, rng = Random.Xoshiro())::NTuple{4,Float64}
    n = length(joint_with)
    (n != length(phase_t) || n != length(phase_t1)) &&
        throw(ArgumentError("_conditional_mi: length mismatch"))
    n < 8 && return (NaN, NaN, NaN, NaN)

    function cmi(jw::Vector{Int}, pt::Vector{Int}, pt1::Vector{Int})::Float64
        # H(Y|Z): Y=pt1, Z=pt
        n_ = length(jw)
        cz   = Dict{Int,Int}()
        cyz  = Dict{Tuple{Int,Int},Int}()
        cxz  = Dict{Tuple{Int,Int},Int}()
        cxyz = Dict{Tuple{Int,Int,Int},Int}()
        for i in 1:n_
            phz, y, x = pt[i], pt1[i], jw[i]
            cz[phz]        = get(cz, phz, 0) + 1
            cyz[(y,phz)]   = get(cyz, (y,phz), 0) + 1
            cxz[(x,phz)]   = get(cxz, (x,phz), 0) + 1
            cxyz[(x,y,phz)]= get(cxyz, (x,y,phz), 0) + 1
        end
        h_y_given_z = 0.0
        for ((y,phz), c) in cyz
            p_yz = c / n_
            p_z  = cz[phz] / n_
            h_y_given_z -= p_yz * log2(p_yz / p_z)
        end
        h_y_given_xz = 0.0
        for ((x,y,phz), c) in cxyz
            p_xyz = c / n_
            p_xz  = cxz[(x,phz)] / n_
            h_y_given_xz -= p_xyz * log2(p_xyz / p_xz)
        end
        return max(0.0, h_y_given_z - h_y_given_xz)
    end

    mi_obs = cmi(joint_with, phase_t, phase_t1)

    null_vals = Vector{Float64}(undef, n_shuffle)
    perm = collect(1:n)
    for k in 1:n_shuffle
        shuffle!(rng, perm)
        null_vals[k] = cmi(joint_with, phase_t, phase_t1[perm])
    end
    null_mean = sum(null_vals) / n_shuffle
    null_var  = sum((v - null_mean)^2 for v in null_vals) / max(1, n_shuffle - 1)
    null_std  = sqrt(null_var)
    z = null_std > 0 ? (mi_obs - null_mean) / null_std : NaN

    return (mi_obs, null_mean, null_std, z)
end

# ---------------------------------------------------------------------------
#  _phase_stratified_lag1_corr(combined_al, phase) ->
#      (r_same, n_same, r_diff, n_diff)
#
#  Splits consecutive closure pairs (t, t+1) within each chain into
#  "same phase" (phase[t] == phase[t+1]) vs "different phase", and computes
#  the lag-1 Pearson correlation of combined_al separately within each
#  stratum, pooling pairs across ALL chains (not per-chain — see D39b
#  constants-block docstring's sample-size caveat: same-phase pairs are
#  rare, expected ~n/N_STEPS total, so per-chain stratification would
#  leave most chains with zero same-phase pairs).
# ---------------------------------------------------------------------------
function _phase_stratified_lag1_corr(chains)
    same_x = Float64[]; same_y = Float64[]
    diff_x = Float64[]; diff_y = Float64[]
    for c in chains
        n = length(c.combined_al)
        n < 2 && continue
        for t in 1:(n-1)
            if c.phase[t] == c.phase[t+1]
                push!(same_x, Float64(c.combined_al[t]))
                push!(same_y, Float64(c.combined_al[t+1]))
            else
                push!(diff_x, Float64(c.combined_al[t]))
                push!(diff_y, Float64(c.combined_al[t+1]))
            end
        end
    end
    function pearson(x, y)
        n = length(x)
        n < 2 && return NaN
        mx, my = sum(x)/n, sum(y)/n
        sxy = sum((x[i]-mx)*(y[i]-my) for i in 1:n)
        sxx = sum((xi-mx)^2 for xi in x)
        syy = sum((yi-my)^2 for yi in y)
        (sxx == 0.0 || syy == 0.0) && return NaN
        return sxy / sqrt(sxx*syy)
    end
    return (pearson(same_x, same_y), length(same_x), pearson(diff_x, diff_y), length(diff_x))
end

# ---------------------------------------------------------------------------
#  _report_d39b — phase-locked closure diagnostic report section.
# ---------------------------------------------------------------------------
function _report_d39b(chains)
    @printf("\n  D39b — Phase-locked closure diagnostic (table-resonance check)\n")
    @printf("  ─────────────────────────────────────────────────────────────────\n")

    all_phases = Int[]
    for c in chains; append!(all_phases, c.phase); end
    if isempty(all_phases) || all(p -> p < 0, all_phases)
        @printf("    (no phase data recorded — step_phase was not passed at the\n")
        @printf("     handle_1lp_conj! call site; skipping D39b)\n")
        return nothing
    end
    n_steps_observed = maximum(all_phases)
    @printf("    Step-table size (inferred from max observed slot) : %d\n", n_steps_observed)

    # --- Build consecutive-pair joint label for the MI test ---
    # Combine (α_t,P_t,Δα_t) into one discretized joint label per pair via
    # a small mixed-radix code over per-series bins, pooling pairs across
    # all chains (same rationale as the phase-stratified corr test below).
    n_bins = 4
    joint_with = Int[]
    phase_t    = Int[]
    phase_t1   = Int[]
    for c in chains
        n = length(c.neg_al)
        n < 2 && continue
        al_b  = _discretize(c.neg_al,      n_bins)
        px_b  = _discretize(c.px_anchor,   n_bins)
        dal_b = _discretize(c.combined_al, n_bins)
        for t in 1:(n-1)
            (c.phase[t] < 0 || c.phase[t+1] < 0) && continue
            label = (al_b[t]-1) + n_bins*(px_b[t]-1) + n_bins*n_bins*(dal_b[t]-1) + 1
            push!(joint_with, label)
            push!(phase_t,  c.phase[t])
            push!(phase_t1, c.phase[t+1])
        end
    end

    n_pairs = length(joint_with)
    @printf("    Consecutive closure pairs available (pooled, all chains) : %d\n", n_pairs)

    if n_pairs < 8
        @printf("    (too few consecutive pairs for the conditional-MI test — skipping)\n")
    else
        mi_obs, null_mean, null_std, mi_z = _conditional_mi(joint_with, phase_t, phase_t1)
        @printf("\n    1. I((α_t,P_t,Δα_t); phase_t+1 | phase_t)\n")
        @printf("    -----------------------------------------------------------------\n")
        if isnan(mi_z)
            @printf("      (degenerate — could not estimate; too few pairs or zero variance)\n")
        else
            @printf("      observed conditional MI : %.5f bits\n", mi_obs)
            @printf("      shuffle-null mean ± std : %.5f ± %.5f bits  (n_shuffle=200)\n", null_mean, null_std)
            @printf("      z = (obs - null_mean) / null_std : %.2f\n", mi_z)
            if mi_z >= 3.0
                @printf("      → SIGNIFICANT: this closure's (α,P,Δα) carries information about\n")
                @printf("        the NEXT closure's table slot beyond what the current slot alone\n")
                @printf("        predicts. This is the opposite of pure resonance (resonance would\n")
                @printf("        predict phase_t alone explains phase_t+1; this says the WALK STATE\n")
                @printf("        does too) — consistent with the autocorrelation being more than a\n")
                @printf("        table artifact, though it does not on its own rule out resonance\n")
                @printf("        contributing part of the D39 signal.\n")
            else
                @printf("      → Not significant at this n: no detectable extra information beyond\n")
                @printf("        phase_t. Consistent with (but does not prove) D39's autocorrelation\n")
                @printf("        being explainable by phase_t alone — see test 2 below for a more\n")
                @printf("        direct check.\n")
            end
        end
    end

    # --- Test 2: phase-stratified lag-1 Δα correlation ---
    r_same, n_same, r_diff, n_diff = _phase_stratified_lag1_corr(chains)
    @printf("\n    2. corr(Δα_t, Δα_t+1), stratified by phase(t)==phase(t+1)\n")
    @printf("    -----------------------------------------------------------------\n")
    if isnan(r_same)
        @printf("      same-phase   pairs : n=%d   r=n/a (too few pairs)\n", n_same)
    else
        @printf("      same-phase   pairs : n=%d   r=%.4f\n", n_same, r_same)
    end
    if isnan(r_diff)
        @printf("      different-phase pairs : n=%d   r=n/a (too few pairs)\n", n_diff)
    else
        @printf("      different-phase pairs : n=%d   r=%.4f\n", n_diff, r_diff)
    end

    if n_same < 5
        @printf("      → same-phase stratum too sparse (n=%d) at current closure count to\n", n_same)
        @printf("        draw a conclusion — expected ~n_pairs/%d same-phase pairs by chance;\n", n_steps_observed)
        @printf("        rerun once closure count has grown substantially.\n")
    elseif !isnan(r_same) && !isnan(r_diff)
        if abs(r_same) > abs(r_diff) + 0.2   # crude practical-significance margin, not a formal test
            @printf("      → same-phase correlation notably exceeds different-phase correlation.\n")
            @printf("        Some of D39's Δα autocorrelation may be table-resonance — closures\n")
            @printf("        that happen to share a step-table slot inherit a shared fixed\n")
            @printf("        increment. Does not rule out a genuine component too; compare\n")
            @printf("        magnitudes once n_same has grown.\n")
        else
            @printf("      → same-phase and different-phase correlations are comparable. D39's\n")
            @printf("        Δα autocorrelation does NOT appear to be explained by step-table\n")
            @printf("        phase resonance — the original interpretation (real algebraic/\n")
            @printf("        spatial structure) survives this check.\n")
        end
    end

    return nothing
end

# =============================================================================
#  D39c — Cross-correlation analysis: closing the propagation chain
#
#  GPT's argument (from the pasted summary): if P_fb and α are each positively
#  autocorrelated, and if both are generated by the same slowly-varying closure
#  geometry, the cross-term Cov(α_t, P_{fb,t+k}) + Cov(P_{fb,t}, α_{t+k}) is
#  itself large and positive, so the residual
#
#      Z_t = α_t - P_{fb,t}   (scalar proxy for neg_al·G - atom(P_fb) = R+Rconj)
#
#  inherits persistence.  That statement only holds if the cross-terms are not
#  fine-tuned to cancel the individual auto-covariances.  This section measures
#  ALL six (auto + cross) terms so we can say definitively whether the
#  cross-terms reinforce or cancel, and whether Cov(Z_t,Z_{t+k}) > 0.
#
#  Concretely, for X = neg_al, Y = px_anchor, Z_res = X - Y (the key proxy):
#
#      Cov(Z_res,t, Z_res,t+k) =  Cov(X_t,X_{t+k})            [auto X]
#                               +  Cov(Y_t,Y_{t+k})            [auto Y]
#                               -  Cov(X_t,Y_{t+k})            [cross X→Y]
#                               -  Cov(Y_t,X_{t+k})            [cross Y→X]
#
#  All four terms are estimated here via pooled Pearson correlations, and the
#  implied sign/magnitude of Cov(Z_res,t, Z_res,t+k) is printed explicitly.
#
#  We also measure Cov(Z_res_t, Z_res_{t+k}) directly as a fifth check,
#  and CCF(combined_al_t, X_{t+k}) and CCF(combined_al_t, Y_{t+k}) to see
#  whether the difference process Δα tracks either constituent series.
# =============================================================================

# ---------------------------------------------------------------------------
#  _seq_ccf_z(x, y, lag) -> (r, z, n_pairs)
#
#  Sample Pearson cross-correlation of x with y at the given lag:
#      r(k) = Σ (x_t - μ_x)(y_{t+k} - μ_y) / (n * σ_x * σ_y)
#
#  x leads y by lag steps (positive lag = x is earlier).
#  SE under the i.i.d. null is 1/sqrt(n - lag), same Bartlett convention
#  as _seq_acf_z.  Returns (NaN, NaN, 0) on degenerate input.
# ---------------------------------------------------------------------------
function _seq_ccf_z(x::Vector{Int}, y::Vector{Int}, lag::Int)::Tuple{Float64,Float64,Int}
    length(x) != length(y) && throw(ArgumentError("_seq_ccf_z: x and y must have the same length"))
    n = length(x)
    n_pairs = n - lag
    n_pairs < 2 && return (NaN, NaN, 0)

    xf = Float64.(x)
    yf = Float64.(y)
    mu_x = sum(xf) / n
    mu_y = sum(yf) / n

    var_x = 0.0; var_y = 0.0
    @inbounds for i in 1:n
        var_x += (xf[i] - mu_x)^2
        var_y += (yf[i] - mu_y)^2
    end
    (var_x == 0.0 || var_y == 0.0) && return (NaN, NaN, 0)

    numer = 0.0
    @inbounds for i in 1:n_pairs
        numer += (xf[i] - mu_x) * (yf[i + lag] - mu_y)
    end
    # Normalise by sqrt(var_x * var_y) so result is in [-1,1].
    # (We use the full-series variances, not just the lagged-pair window,
    #  mirroring the Pearson convention used in _seq_acf_z.)
    r = numer / sqrt(var_x * var_y)
    se = 1.0 / sqrt(Float64(n_pairs))
    z = r / se
    return (r, z, n_pairs)
end

# ---------------------------------------------------------------------------
#  _pooled_ccf_over_chains(chains, field_x, field_y, lags; min_len)
#
#  Same pooling logic as _pooled_acf_over_chains, but calls _seq_ccf_z(x,y).
#  Returns the same NamedTuple vector shape as _pooled_acf_over_chains.
# ---------------------------------------------------------------------------
function _pooled_ccf_over_chains(chains, field_x, field_y, lags::AbstractVector{Int};
                                  min_len::Int = D39_MIN_CHAIN_LEN)
    results = NamedTuple{(:lag,:pooled_z,:n_chains,:max_abs_r),Tuple{Int,Float64,Int,Float64}}[]
    for lag in lags
        wsum   = 0.0
        zsum   = 0.0
        nchain = 0
        max_abs_r = 0.0
        for ch in chains
            xv = field_x(ch)
            yv = field_y(ch)
            length(xv) < max(min_len, lag + 2) && continue
            r, z, n_pairs = _seq_ccf_z(xv, yv, lag)
            isnan(z) && continue
            w = Float64(n_pairs)
            wsum += w
            zsum += w * z
            nchain += 1
            max_abs_r = max(max_abs_r, abs(r))
        end
        pooled_z = nchain > 0 ? zsum / sqrt(wsum) : NaN
        push!(results, (lag=lag, pooled_z=pooled_z, n_chains=nchain, max_abs_r=max_abs_r))
    end
    return results
end

# ---------------------------------------------------------------------------
#  _pool_acf_scalar(vecs, lags; min_len)  ->  pooled_z vector (one per lag)
#
#  Thin wrapper that extracts just the pooled_z column from
#  _pooled_acf_over_chains when the caller already has Vector{Vector{Int}}.
# ---------------------------------------------------------------------------
function _pool_acf_scalar(vecs::Vector{Vector{Int}}, lags::AbstractVector{Int};
                           min_len::Int = D39_MIN_CHAIN_LEN)::Vector{Float64}
    res = _pooled_acf_over_chains(vecs, lags; min_len=min_len)
    return [r.pooled_z for r in res]
end

# ---------------------------------------------------------------------------
#  _pool_ccf_scalar(vecs_x, vecs_y, lags; min_len)  ->  pooled_z vector
#
#  Same but for cross-correlation.  vecs_x and vecs_y are assumed to be
#  parallel (same chain index i → same closure sequence for both series).
# ---------------------------------------------------------------------------
function _pool_ccf_scalar(vecs_x::Vector{Vector{Int}}, vecs_y::Vector{Vector{Int}},
                           lags::AbstractVector{Int};
                           min_len::Int = D39_MIN_CHAIN_LEN)::Vector{Float64}
    n = length(vecs_x)
    length(vecs_y) != n && throw(ArgumentError("_pool_ccf_scalar: vecs_x/y length mismatch"))
    results = NamedTuple{(:lag,:pooled_z,:n_chains,:max_abs_r),Tuple{Int,Float64,Int,Float64}}[]
    for lag in lags
        wsum   = 0.0
        zsum   = 0.0
        nchain = 0
        max_abs_r = 0.0
        for i in 1:n
            xv = vecs_x[i]; yv = vecs_y[i]
            length(xv) < max(min_len, lag + 2) && continue
            r, z, n_pairs = _seq_ccf_z(xv, yv, lag)
            isnan(z) && continue
            w = Float64(n_pairs)
            wsum += w
            zsum += w * z
            nchain += 1
            max_abs_r = max(max_abs_r, abs(r))
        end
        pooled_z = nchain > 0 ? zsum / sqrt(wsum) : NaN
        push!(results, (lag=lag, pooled_z=pooled_z, n_chains=nchain, max_abs_r=max_abs_r))
    end
    return [r.pooled_z for r in results]
end

# ---------------------------------------------------------------------------
#  _summarise_acf_row(label, pooled_zs, lags) — one-line summary printer
# ---------------------------------------------------------------------------
function _summarise_acf_row(label::String, pooled_zs::Vector{Float64}, lags::AbstractVector{Int})
    valid = [(lags[i], pooled_zs[i]) for i in eachindex(lags) if !isnan(pooled_zs[i])]
    if isempty(valid)
        @printf("    %-36s  no valid lags\n", label)
        return
    end
    n_sig   = count(lz -> abs(lz[2]) >= 3.0, valid)
    best_i  = argmax(abs.(last.(valid)))
    best_l, best_z = valid[best_i]
    sign_ch = best_z >= 0 ? "+" : "-"
    @printf("    %-36s  peak z=%+6.2f at lag=%-4d  n_sig(|z|≥3)=%d/%d\n",
            label, best_z, best_l, n_sig, length(valid))
end

# ---------------------------------------------------------------------------
#  _report_d39c — cross-correlation + covariance-decomposition section.
# ---------------------------------------------------------------------------
function _report_d39c(deep_stat::ConjDeepStat)
    chains = deep_stat.d39_chains
    isempty(chains) && return nothing   # already reported in _report_d39

    @printf("\n  D39c — Cross-correlation / covariance-decomposition analysis\n")
    @printf("  ─────────────────────────────────────────────────────────────────\n")
    @printf("  Notation: X = neg_al (α proxy)   Y = px_anchor (P_fb proxy)\n")
    @printf("            Δ = combined_al (Δα)    Z_res = X - Y (key proxy)\n")
    @printf("  Testing GPT's chain: Cov(Z_res,t, Z_res,t+k)\n")
    @printf("                     = Cov(X,X)(k) + Cov(Y,Y)(k)\n")
    @printf("                     - Cov(X,Y)(k) - Cov(Y,X)(k)\n\n")

    max_len = maximum(length(c.neg_al) for c in chains)
    lag_hi  = min(D39_ACF_LAG_HI, max(1, max_len - D39_MIN_CHAIN_LEN))
    lags    = D39_ACF_LAG_LO:D39_ACF_LAG_STRIDE:lag_hi
    if isempty(lags)
        @printf("    (chains too short for any tested lag — skipping D39c)\n")
        return nothing
    end

    # Extract per-chain series vectors.
    al_vecs  = [c.neg_al      for c in chains]    # X
    px_vecs  = [c.px_anchor   for c in chains]    # Y
    dal_vecs = [c.combined_al for c in chains]    # Δ

    # Build Z_res = X - Y per chain.
    zres_vecs = Vector{Vector{Int}}(undef, length(chains))
    for (i, c) in enumerate(chains)
        n = length(c.neg_al)
        v = Vector{Int}(undef, n)
        @inbounds for t in 1:n
            v[t] = c.neg_al[t] - c.px_anchor[t]
        end
        zres_vecs[i] = v
    end

    # --- Compute all pooled ACF/CCF series ---
    zAA = _pool_acf_scalar(al_vecs,   lags)   # Cov(X,X)(k)  — auto X
    zBB = _pool_acf_scalar(px_vecs,   lags)   # Cov(Y,Y)(k)  — auto Y
    zDD = _pool_acf_scalar(dal_vecs,  lags)   # Cov(Δ,Δ)(k)  — auto Δ
    zZZ = _pool_acf_scalar(zres_vecs, lags)   # Cov(Z,Z)(k)  — auto Z_res (direct)

    zAB = _pool_ccf_scalar(al_vecs, px_vecs,  lags)   # CCF X→Y  (X leads Y)
    zBA = _pool_ccf_scalar(px_vecs, al_vecs,  lags)   # CCF Y→X  (Y leads X)
    zAD = _pool_ccf_scalar(al_vecs, dal_vecs, lags)   # CCF X→Δ
    zDA = _pool_ccf_scalar(dal_vecs, al_vecs, lags)   # CCF Δ→X
    zBD = _pool_ccf_scalar(px_vecs, dal_vecs, lags)   # CCF Y→Δ
    zDB = _pool_ccf_scalar(dal_vecs, px_vecs, lags)   # CCF Δ→Y

    # --- Summary table ---
    @printf("  Peak-z summary (pooled Pearson ACF/CCF over all chains):\n")
    @printf("    %-36s  peak-z and significance\n", "series")
    @printf("    %s\n", "─"^74)
    _summarise_acf_row("ACF(X,X)  [auto α]",          zAA, lags)
    _summarise_acf_row("ACF(Y,Y)  [auto P_fb]",        zBB, lags)
    _summarise_acf_row("ACF(Δ,Δ)  [auto Δα]",          zDD, lags)
    _summarise_acf_row("ACF(Z,Z)  [auto Z_res direct]", zZZ, lags)
    @printf("    %s\n", "─"^74)
    _summarise_acf_row("CCF(X→Y)  [α leads P_fb]",     zAB, lags)
    _summarise_acf_row("CCF(Y→X)  [P_fb leads α]",     zBA, lags)
    _summarise_acf_row("CCF(X→Δ)  [α leads Δα]",       zAD, lags)
    _summarise_acf_row("CCF(Δ→X)  [Δα leads α]",       zDA, lags)
    _summarise_acf_row("CCF(Y→Δ)  [P_fb leads Δα]",    zBD, lags)
    _summarise_acf_row("CCF(Δ→Y)  [Δα leads P_fb]",    zDB, lags)
    @printf("    %s\n", "─"^74)

    # --- Covariance decomposition at a few representative lags ---
    # We print lag 1, and the lag at which |zAA| is maximised (if different
    # from 1), and the lag at which |zZZ| is maximised.
    valid_AA = [(lags[i], zAA[i]) for i in eachindex(lags) if !isnan(zAA[i])]
    valid_ZZ = [(lags[i], zZZ[i]) for i in eachindex(lags) if !isnan(zZZ[i])]
    probe_lags = Int[1]
    if !isempty(valid_AA)
        l_peak_AA = valid_AA[argmax(abs.(last.(valid_AA)))][1]
        l_peak_AA != 1 && push!(probe_lags, l_peak_AA)
    end
    if !isempty(valid_ZZ)
        l_peak_ZZ = valid_ZZ[argmax(abs.(last.(valid_ZZ)))][1]
        l_peak_ZZ ∉ probe_lags && push!(probe_lags, l_peak_ZZ)
    end
    sort!(probe_lags)

    @printf("\n  Covariance-decomposition check at selected lags:\n")
    @printf("  (all quantities are pooled Pearson z-scores, i.i.d. null SE=1/sqrt(n))\n\n")
    @printf("  %5s  %7s  %7s  %7s  %7s  %7s  %7s\n",
            "lag", "z(X,X)", "z(Y,Y)", "z(X,Y)", "z(Y,X)", "implied", "direct")
    @printf("  %5s  %7s  %7s  %7s  %7s  %7s  %7s\n",
            "", "", "", "cross→", "cross←", "z(Z,Z)", "z(Z,Z)")
    @printf("  %s\n", "─"^58)

    lag_to_idx = Dict(lags[i] => i for i in eachindex(lags))
    for lag in probe_lags
        haskey(lag_to_idx, lag) || continue
        idx = lag_to_idx[lag]
        zAA_ = isnan(zAA[idx]) ? NaN : zAA[idx]
        zBB_ = isnan(zBB[idx]) ? NaN : zBB[idx]
        zAB_ = isnan(zAB[idx]) ? NaN : zAB[idx]
        zBA_ = isnan(zBA[idx]) ? NaN : zBA[idx]
        zZZ_ = isnan(zZZ[idx]) ? NaN : zZZ[idx]
        # "implied" is the signed sum of the four decomposition terms,
        # expressed as a z-score heuristic (not a formal test):
        # implied_z ≈ zAA + zBB - zAB - zBA  (uses z-score additivity
        # as a rough guide; not exact due to covariance between estimators)
        implied = (isnan(zAA_)||isnan(zBB_)||isnan(zAB_)||isnan(zBA_)) ?
                  NaN : zAA_ + zBB_ - zAB_ - zBA_
        @printf("  %5d  %+7.2f  %+7.2f  %+7.2f  %+7.2f  %+7.2f  %+7.2f\n",
                lag,
                isnan(zAA_) ? 0.0 : zAA_,
                isnan(zBB_) ? 0.0 : zBB_,
                isnan(zAB_) ? 0.0 : zAB_,
                isnan(zBA_) ? 0.0 : zBA_,
                isnan(implied) ? 0.0 : implied,
                isnan(zZZ_) ? 0.0 : zZZ_)
    end
    @printf("  (zeros printed for NaN entries)\n")

    # --- Verdict ---
    @printf("\n  D39c Verdict:\n")
    @printf("  ─────────────────────────────────────────────────────────────────\n")

    zZZ_sig = !isempty(valid_ZZ) && any(lz -> abs(lz[2]) >= 3.0, valid_ZZ)
    zAA_sig = !isempty(valid_AA) && any(lz -> abs(lz[2]) >= 3.0, valid_AA)
    zBB_sig = let v = [(lags[i],zBB[i]) for i in eachindex(lags) if !isnan(zBB[i])]
                  !isempty(v) && any(lz -> abs(lz[2]) >= 3.0, v) end
    zAB_peak = isempty(valid_AA) ? NaN : begin
        idxs = [lag_to_idx[lag] for lag in first.(valid_AA) if haskey(lag_to_idx,lag)]
        isempty(idxs) ? NaN : zAB[idxs[argmax(abs.(zAB[idxs]))]]
    end

    if zZZ_sig
        @printf("  → SIGNIFICANT autocorrelation in Z_res = α - P_fb (the key proxy).\n")
        @printf("    The LP1-conj key process itself carries sequential persistence.\n")
        if zAA_sig && zBB_sig
            @printf("    Both α and P_fb are individually autocorrelated (D39 result confirmed\n")
            @printf("    here too), so the cross-term signs determine whether they reinforce\n")
            @printf("    or partially cancel — see the decomposition table above.\n")
        end
    else
        @printf("  → No significant autocorrelation detected in Z_res at this sample size.\n")
        @printf("    Either the key-proxy autocorrelation lives below current detection power,\n")
        @printf("    or the cross-terms cancel the individual auto-covariances.\n")
        if zAA_sig || zBB_sig
            @printf("    Note: at least one of α / P_fb IS individually autocorrelated —\n")
            @printf("    the cancellation scenario (cross-terms dominate) cannot be ruled out;\n")
            @printf("    cross-correlation z-scores above confirm whether this is the case.\n")
        end
    end

    # Diagnose cross-term direction
    lag1_idx = get(lag_to_idx, 1, nothing)
    if lag1_idx !== nothing
        ab1 = zAB[lag1_idx]; ba1 = zBA[lag1_idx]
        aa1 = zAA[lag1_idx]; bb1 = zBB[lag1_idx]
        if !isnan(ab1) && !isnan(ba1)
            # Whether negative cross-terms amplify or cancel depends on the sign
            # of the auto-term sum. The decomposition is:
            #   implied_z(Z,Z) = zAA + zBB - zAB - zBA
            # Subtracting a negative cross-term adds a positive value. That
            # drives the sum *away from zero* only when (zAA+zBB) is itself
            # positive (persistent auto-structure). When (zAA+zBB) < 0 (both
            # sequences are anti-persistent / alternating), the positive
            # contribution from the subtracted negative cross-term pushes the
            # implied z *toward* zero — partial cancellation, not amplification.
            auto_sum = (isnan(aa1) ? 0.0 : aa1) + (isnan(bb1) ? 0.0 : bb1)
            auto_persistent = auto_sum > 0.0   # true → both series tend to persist
            if ab1 > 3.0 || ba1 > 3.0
                # Positive cross-terms: Cov(X,Y)+Cov(Y,X) > 0, subtracted → reduces implied z.
                if auto_persistent
                    @printf("  → Cross-terms are POSITIVE: α and P_fb move together at lag 1.\n")
                    @printf("    Subtracting positive cross-terms from a positive auto sum\n")
                    @printf("    partially cancels the persistence; Z_res persistence will be\n")
                    @printf("    WEAKER than the individual auto-covariances alone suggest.\n")
                else
                    @printf("  → Cross-terms are POSITIVE: α and P_fb move together at lag 1.\n")
                    @printf("    Auto-terms are anti-persistent (zAA+zBB=%.2f < 0); subtracting\n", auto_sum)
                    @printf("    positive cross-terms drives the implied z further negative,\n")
                    @printf("    AMPLIFYING the anti-persistence in Z_res.\n")
                end
            elseif ab1 < -3.0 || ba1 < -3.0
                # Negative cross-terms: Cov(X,Y)+Cov(Y,X) < 0, subtracted → adds positive value.
                if auto_persistent
                    @printf("  → Cross-terms are NEGATIVE: α and P_fb are anti-correlated at lag 1.\n")
                    @printf("    Auto-terms are persistent (zAA+zBB=%.2f > 0); subtracting\n", auto_sum)
                    @printf("    negative cross-terms adds a positive contribution, AMPLIFYING\n")
                    @printf("    the persistence. Z_res persistence will be STRONGER than\n")
                    @printf("    either constituent alone.\n")
                else
                    @printf("  → Cross-terms are NEGATIVE: α and P_fb are anti-correlated at lag 1.\n")
                    @printf("    Auto-terms are anti-persistent (zAA+zBB=%.2f < 0); subtracting\n", auto_sum)
                    @printf("    negative cross-terms adds a positive value that drives the implied\n")
                    @printf("    z toward zero — PARTIAL CANCELLATION, not amplification.\n")
                    @printf("    Z_res persistence will be WEAKER in magnitude than the\n")
                    @printf("    individual auto-covariances alone suggest.\n")
                end
            else
                @printf("  → Cross-terms not significant at lag 1 (z(X→Y)=%.2f, z(Y→X)=%.2f);\n",
                        ab1, ba1)
                @printf("    cannot confidently assess the cancellation vs. reinforcement regime.\n")
            end
        end
    end

    return nothing
end
