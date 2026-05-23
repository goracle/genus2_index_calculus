# =============================================================================
#  phi_bias_diag.jl  --  Diagnostic instrumentation for a-parameter bias.
#
#  Theory recap (see comments in trial3_phi.jl for derivation):
#
#    After normalising d=1, the φ construction collapses to one scalar
#
#      a = (v₁·pₓ + v₀ − pᵧ) / u(pₓ)
#
#    and the residual Mumford coefficients are low-degree polynomials in a:
#
#      c₁_RS = pₓ − u₁ − a²              (degree 2)
#      c₀_RS = −(pₓ−3u₁)a² − 2v₁a + K   (degree 2, K depends on D,pₓ)
#
#    Therefore the split discriminant Δ = c₁²−4c₀ is degree 4 in a.
#
#  Three structural biases to probe (original):
#
#  Surface 1 — 1-D image:  for fixed D, all residual (c₁,c₀) pairs lie on a
#    conic in 𝔽ₚ², not a dense 2-D cloud.  Measured by image-collision rate.
#
#  Surface 2 — discriminant bias:  split events are governed by Δ(a) (degree 4),
#    so splits are not uniformly distributed in a.  Measured by a χ² test on
#    a histogram of the a-value at each split step.
#
#  Surface 3 — a=0 slice:  when a=0 the residual is completely determined by D
#    and pᵧ dependence), so O(√p) distinct anchors all produce the same
#    (c₁,c₀).  Measured by comparing FB-smooth rate at a=0 vs overall.
#
#  Three sequential-structure diagnostics (new):
#
#  Seq 1 — Run-length distribution:  if split/non-split outcomes are i.i.d.
#    Bernoulli(1/2), run lengths follow Geometric(1/2).  We accumulate the
#    empirical run-length histogram and compute a KS statistic against the
#    Geometric(1/2) CDF.  Shorter-than-geometric runs → anti-correlation
#    (bouncing between regions); longer → positive correlation (clustering).
#
#  Seq 2 — LP1-conj temporal Fano factor:  if LP1-conj hits are Poisson in
#    walk-step time, the inter-arrival variance equals the mean (Fano = 1).
#    Fano >> 1 indicates the walk spends time in high-productivity Jacobian
#    regions — algebraic structure in the LP1-conj observable.
#
#  Seq 3 — Post-LP anchor correlation:  after a 1-LP event the next anchor
#    P0_{n+1} is the LP point itself (not a random FB element), creating a
#    potential correlation between the anchor and D_{n+1}.  We compare the
#    a-histogram on post-LP steps against the baseline histogram.  A KS
#    divergence here means the LP-derived anchors bias the a-distribution.
#
#  Four spectral diagnostics (computed post-hoc from lp1_conj_arrivals):
#
#  Spec 1 — Welch PSD:  bin arrivals into fixed windows → binary indicator →
#    Hann-windowed DFT per window, averaged (Welch estimate).  Compared to a
#    shuffled-gap null.  Low-frequency lift > 2× indicates long-range order.
#
#  Spec 2 — Windowed spectrogram:  divide arrivals into 4 chronological slices
#    and report per-slice density and gap CV.  Reveals regime switching and
#    intermittency invisible to global statistics.
#
#  Spec 3 — Shuffled spectral comparison:  built into Spec 1 above; every PSD
#    bin is shown alongside its shuffled-gap null.
#
#  Spec 4 — Allan factor variance scaling:  F(T) = Var(N_T)/E[N_T] over a
#    geometric progression of window sizes.  Poisson → F(T)≈1; clustered →
#    F(T) grows.  A log-log slope (Hurst proxy) summarises long-memory.
#
#  Five new signal diagnostics (computed post-hoc from lp1_conj_arrivals and
#  lp1_conj_a_hist; New 3 requires one extra field in PhiBiasStat):
#
#  New 1 — Density autocorrelation:  bin arrivals into coarse count series and
#    compute lag-1/2/3 ACF.  Positive ACF → persistent hot/cold epochs.
#
#  New 2 — Hot/cold window conditioning:  classify windows by hit density
#    (hot ≥ median, cold < median) and compute lift = E[N_{t+1}|hot] /
#    E[N_{t+1}|cold].  Lift >> 1 means bursts are temporally predictive.
#
#  New 3 — State-space a-region hotness:  compare LP1-conj emission histogram
#    per a-bucket against visit histogram (split_hist) to find dynamically hot
#    a-regions.  χ²/dof flags systematic dynamic bias.
#
#  New 4 — Multitaper PSD + spectral slope:  K=4 cosine tapers for reduced
#    variance at low frequencies; OLS log-log slope gives 1/fᵅ exponent α.
#    α > 1 → long-memory; α ≈ 0 → white noise.
#
#  New 5 — Gap-distribution characterisation (replaces unstable MMPP-2 MoM fit):
#    (a) burst-size distribution with KS test vs Geometric null,
#    (b) short/long gap fractions vs Poisson prediction (hot/cold persistence),
#    (c) KS test of rescaled gaps vs Exponential(1) with heavy-tail flag.
#
#  All accumulators are per-thread (no locking during the walk).
#  Call merge_phi_bias_stats to combine and print_phi_bias_report to display.
#
#  Overhead: one Int comparison (a==0), one histogram bucket write, and one
#  (c1,c0) hash-insert per valid phi step — negligible relative to the Jacobian
#  arithmetic that dominates phase2_worker.
# =============================================================================

# ---------------------------------------------------------------------------
#  PhiBiasStat — per-thread accumulator
# ---------------------------------------------------------------------------
mutable struct PhiBiasStat
    total          ::Int     # valid phi steps recorded
    a_zero         ::Int     # steps where a == 0
    a_zero_split   ::Int     # a==0 AND residual split over 𝔽ₚ
    a_zero_fb      ::Int     # a==0 AND both R,S in FB (0-LP or 1-LP)

    # Split histogram: a partitioned into nbuckets equal-width buckets over 𝔽ₚ.
    # Entry i counts split steps whose a fell in bucket i.
    # nbuckets = isqrt(p) gives O(√p) buckets — coarse enough to accumulate
    # signal in a typical run, fine enough to reveal non-uniform clustering.
    split_hist     ::Vector{Int}
    nonsplit_hist  ::Vector{Int}   # parallel histogram for non-split steps

    # Image-collision counter: incremented when two different a-values (within
    # the same D-keyed window) produce the same (c1_rs, c0_rs) pair.
    # We maintain only the *current* D's image set (a rolling window keyed on
    # the Mumford (u0,u1,v0,v1) quadruple) so memory stays bounded.
    image_collisions ::Int
    _img_key         ::NTuple{4,Int}        # Mumford key of the current D
    _img_seen        ::Set{NTuple{2,Int}}   # (c1,c0) pairs seen for _img_key

    # ---- Seq 1: run-length distribution ----------------------------------------
    # _run_is_split: whether the current in-progress run is of split steps.
    # _run_len:      length of the current in-progress run (not yet committed).
    # run_hist_split[k]     = number of completed split-runs of exactly length k.
    # run_hist_nonsplit[k]  = number of completed non-split runs of length k.
    # Capped at MAX_RUN_LEN; runs longer than that accumulate in bin MAX_RUN_LEN.
    _run_is_split    ::Bool
    _run_len         ::Int
    run_hist_split   ::Vector{Int}   # length MAX_RUN_LEN
    run_hist_nonsplit::Vector{Int}   # length MAX_RUN_LEN

    # ---- Seq 2: LP1-conj inter-arrival Fano factor + conditional intensity -----
    # raw-step index at each 1-LP-conj hit; used post-run to compute inter-arrival
    # gaps → variance/mean (Fano factor ≈ 1 ↔ Poisson; >> 1 ↔ clustering).
    lp1_conj_arrivals::Vector{Int}
    # Mumford key (CanonicalLP1Key = UInt128) at each emission, parallel to
    # lp1_conj_arrivals.  Used to detect whether temporally-close hits also share
    # algebraic structure (same key → same Jacobian neighbourhood).
    lp1_conj_keys    ::Vector{UInt128}

    # ---- Seq 3: post-LP anchor correlation -------------------------------------
    # Compare a-histograms conditioned on how the anchor P0 was chosen:
    #   post_lp_a_hist:  steps where P0 was the LP point from a prior LP event.
    #   baseline_a_hist: steps where P0 was drawn uniformly from the FB.
    # Same bucket layout as split_hist (isqrt(p) buckets over [0,p)).
    post_lp_a_hist      ::Vector{Int}
    baseline_a_hist     ::Vector{Int}
    _prev_anchor_was_lp ::Bool   # true iff the step just recorded used an LP-derived P0

    # ---- New 3: state-space a-region hotness ------------------------------------
    # lp1_conj_a_hist[bucket] = number of LP1-conj *emissions* whose triggering
    # phi step fell in bucket.  Compared to the overall split_hist to identify
    # dynamically hot a-regions: buckets where emissions are over-represented
    # relative to visit frequency.  Set by record_lp1_conj_hit! via bucket arg.
    lp1_conj_a_hist ::Vector{Int}
end

const MAX_RUN_LEN = 64   # run-length histogram cap (longer runs fold into bin 64)

function PhiBiasStat(p::Int)
    nbuckets = max(1, isqrt(p))
    PhiBiasStat(
        # Surface 1-3 fields
        0, 0, 0, 0,
        zeros(Int, nbuckets),
        zeros(Int, nbuckets),
        0,
        (-1, -1, -1, -1),
        Set{NTuple{2,Int}}(),
        # Seq 1: run-length
        true,                          # _run_is_split (arbitrary initial)
        0,                             # _run_len
        zeros(Int, MAX_RUN_LEN),       # run_hist_split
        zeros(Int, MAX_RUN_LEN),       # run_hist_nonsplit
        # Seq 2: LP1-conj arrivals + keys
        Int[],
        UInt128[],
        # Seq 3: post-LP anchor
        zeros(Int, nbuckets),          # post_lp_a_hist
        zeros(Int, nbuckets),          # baseline_a_hist
        false,                         # _prev_anchor_was_lp
        # New 3: a-region hotness
        zeros(Int, nbuckets),          # lp1_conj_a_hist
    )
end

# ---------------------------------------------------------------------------
#  record_phi_step! — called once per valid phi step in phase2_worker.
#
#  Arguments:
#    stat     — per-thread PhiBiasStat
#    a        — the scalar a from build_phi_mumford (already reduced mod p)
#    c1_rs    — first Mumford coeff of residual quadratic
#    c0_rs    — second Mumford coeff of residual quadratic
#    split    — true iff the residual split over 𝔽ₚ (rs_split)
#    r_in_fb  — true iff R is in the factor base (iR != 0), ignored when !split
#    s_in_fb  — true iff S is in the factor base (iS != 0), ignored when !split
#    d_key    — (u0,u1,v0,v1) Mumford representation of the current divisor D
#    p        — field characteristic (used for bucket index)
# ---------------------------------------------------------------------------
@inline function record_phi_step!(stat   ::PhiBiasStat,
                                   a      ::Int,
                                   c1_rs  ::Int,
                                   c0_rs  ::Int,
                                   split  ::Bool,
                                   r_in_fb::Bool,
                                   s_in_fb::Bool,
                                   d_key  ::NTuple{4,Int},
                                   p      ::Int)
    stat.total += 1

    # --- Bucket index for a (0-based bucket, 1-indexed in array) ---
    nbuckets = length(stat.split_hist)
    # a is already in [0, p-1].  Multiply-then-shift is branch-free.
    bucket = 1 + (a * nbuckets) ÷ p   # integer division, result in [1,nbuckets]
    bucket = clamp(bucket, 1, nbuckets)

    if split
        stat.split_hist[bucket] += 1
    else
        stat.nonsplit_hist[bucket] += 1
    end

    # --- a=0 slice ---
    if a == 0
        stat.a_zero += 1
        if split
            stat.a_zero_split += 1
            if r_in_fb && s_in_fb
                stat.a_zero_fb += 1
            end
        end
    end

    # --- Image-collision tracking (rolling per-D window) ---
    if d_key !== stat._img_key
        # Divisor changed: reset window.
        empty!(stat._img_seen)
        stat._img_key = d_key
    end
    img_pair = (c1_rs, c0_rs)
    if img_pair in stat._img_seen
        stat.image_collisions += 1
    else
        push!(stat._img_seen, img_pair)
    end

    # --- Seq 1: run-length tracking ---
    if stat._run_len == 0
        # First step ever: initialise run state.
        stat._run_is_split = split
        stat._run_len      = 1
    elseif split == stat._run_is_split
        stat._run_len += 1
    else
        # Run ended — commit it.
        k = clamp(stat._run_len, 1, MAX_RUN_LEN)
        if stat._run_is_split
            stat.run_hist_split[k] += 1
        else
            stat.run_hist_nonsplit[k] += 1
        end
        # Start new run.
        stat._run_is_split = split
        stat._run_len      = 1
    end

    # --- Seq 3: post-LP anchor histogram ---
    if stat._prev_anchor_was_lp
        stat.post_lp_a_hist[bucket] += 1
    else
        stat.baseline_a_hist[bucket] += 1
    end
    # _prev_anchor_was_lp is set externally by record_lp1_conj_anchor! /
    # record_random_anchor! — those are called by the walk loop after updating
    # cur_pt, not here, so the flag read above reflects the *previous* step's
    # anchor choice, which is what we want.

    return nothing
end

# ---------------------------------------------------------------------------
#  record_lp1_conj_hit! — called inside handle_1lp_conj! only when a relation
#  is actually emitted (i.e. a birthday match is closed).  raw_step is the
#  current s.raw_steps counter passed through from the worker.
#  lp_key is the CanonicalLP1Key (UInt128) of the emitted LP1-conj hit.
#  a_bucket is the 1-based bucket index of the triggering a-value (same
#  bucketing as split_hist); pass 0 if not available to skip hotness tracking.
# ---------------------------------------------------------------------------
@inline function record_lp1_conj_hit!(stat::PhiBiasStat, raw_step::Int,
                                       lp_key::UInt128 = zero(UInt128),
                                       a_bucket::Int   = 0)
    push!(stat.lp1_conj_arrivals, raw_step)
    push!(stat.lp1_conj_keys,     lp_key)
    if 1 <= a_bucket <= length(stat.lp1_conj_a_hist)
        stat.lp1_conj_a_hist[a_bucket] += 1
    end
    stat._prev_anchor_was_lp = true
    return nothing
end

# ---------------------------------------------------------------------------
#  record_random_anchor! — called when cur_pt is set to a random FB element
#  (i.e. NOT from an LP event).  Clears the post-LP flag.
# ---------------------------------------------------------------------------
@inline function record_random_anchor!(stat::PhiBiasStat)
    stat._prev_anchor_was_lp = false
    return nothing
end

# ---------------------------------------------------------------------------
#  merge_phi_bias_stats — reduce per-thread stats into one aggregate.
# ---------------------------------------------------------------------------
function merge_phi_bias_stats(stats::Vector{PhiBiasStat})::PhiBiasStat
    isempty(stats) && error("merge_phi_bias_stats: empty input")
    # Use first element as prototype for bucket count.
    p_dummy = length(stats[1].split_hist)^2   # approximate p (bucket count = √p)
    merged = PhiBiasStat(p_dummy)
    # Resize histograms to match (they should all be the same length).
    nb = length(stats[1].split_hist)
    resize!(merged.split_hist,       nb); fill!(merged.split_hist,       0)
    resize!(merged.nonsplit_hist,    nb); fill!(merged.nonsplit_hist,    0)
    resize!(merged.post_lp_a_hist,   nb); fill!(merged.post_lp_a_hist,  0)
    resize!(merged.baseline_a_hist,  nb); fill!(merged.baseline_a_hist, 0)
    resize!(merged.lp1_conj_a_hist,  nb); fill!(merged.lp1_conj_a_hist, 0)
    resize!(merged.run_hist_split,    MAX_RUN_LEN); fill!(merged.run_hist_split,    0)
    resize!(merged.run_hist_nonsplit, MAX_RUN_LEN); fill!(merged.run_hist_nonsplit, 0)

    for s in stats
        merged.total            += s.total
        merged.a_zero           += s.a_zero
        merged.a_zero_split     += s.a_zero_split
        merged.a_zero_fb        += s.a_zero_fb
        merged.image_collisions += s.image_collisions
        append!(merged.lp1_conj_arrivals, s.lp1_conj_arrivals)
        append!(merged.lp1_conj_keys,     s.lp1_conj_keys)
        for i in eachindex(merged.split_hist)
            merged.split_hist[i]       += s.split_hist[i]
            merged.nonsplit_hist[i]    += s.nonsplit_hist[i]
            merged.post_lp_a_hist[i]   += s.post_lp_a_hist[i]
            merged.baseline_a_hist[i]  += s.baseline_a_hist[i]
            merged.lp1_conj_a_hist[i]  += s.lp1_conj_a_hist[i]
        end
        for k in 1:MAX_RUN_LEN
            merged.run_hist_split[k]    += s.run_hist_split[k]
            merged.run_hist_nonsplit[k] += s.run_hist_nonsplit[k]
        end
    end
    return merged
end

# ---------------------------------------------------------------------------
#  print_phi_bias_report — human-readable summary with χ² test.
# ---------------------------------------------------------------------------
function print_phi_bias_report(stat::PhiBiasStat; p::Int = 0)
    total    = stat.total
    nb       = length(stat.split_hist)
    n_split  = sum(stat.split_hist)
    n_nonspl = sum(stat.nonsplit_hist)

    @printf("\n── φ a-parameter bias report ─────────────────────────────────────────\n")
    @printf("  valid phi steps recorded : %d\n", total)
    @printf("  split steps              : %d  (%.2f%% of recorded)\n",
            n_split, 100.0 * n_split / max(1, total))
    @printf("  non-split steps          : %d  (%.2f%%)\n",
            n_nonspl, 100.0 * n_nonspl / max(1, total))
    println()

    # --- Surface 3: a=0 slice ---
    @printf("  Surface 3 — a=0 slice:\n")
    @printf("    a=0 steps              : %d  (%.4f%% of recorded)\n",
            stat.a_zero, 100.0 * stat.a_zero / max(1, total))
    @printf("    a=0 split rate         : %.2f%%  (overall split: %.2f%%)\n",
            100.0 * stat.a_zero_split / max(1, stat.a_zero),
            100.0 * n_split / max(1, total))
    @printf("    a=0 FB-smooth rate     : %.2f%%  (of a=0 split steps)\n",
            100.0 * stat.a_zero_fb / max(1, stat.a_zero_split))
    println()

    # --- Surface 1: image collisions ---
    @printf("  Surface 1 — residual image collisions:\n")
    @printf("    (c₁,c₀) collisions     : %d  (%.4f%% of recorded)\n",
            stat.image_collisions, 100.0 * stat.image_collisions / max(1, total))
    @printf("    interpretation: if > 0, two distinct a-values from the same D\n")
    @printf("    produced identical residual Mumford pairs — algebraic thinness.\n")
    println()

    # --- Surface 2: discriminant bias (χ² on split histogram) ---
    @printf("  Surface 2 — discriminant bias (split histogram χ² test):\n")
    @printf("    histogram buckets      : %d  (each ~%s wide in 𝔽ₚ)\n",
            nb, p > 0 ? string(p ÷ nb) : "p/√p")
    if n_split > 0
        expected  = n_split / nb
        chi2_split = sum((x - expected)^2 / max(1.0, expected)
                         for x in stat.split_hist)
        dof = nb - 1
        @printf("    split χ²               : %.2f  (dof=%d; uniform expected ≈ %.1f)\n",
                chi2_split, dof, Float64(dof))
        # Rule of thumb: χ² / dof >> 1 indicates non-uniformity.
        ratio = chi2_split / max(1.0, Float64(dof))
        flag  = ratio > 2.0 ? " ← NON-UNIFORM" : " (consistent with uniform)"
        @printf("    χ²/dof                 : %.3f%s\n", ratio, flag)
    else
        @printf("    (no split steps recorded — χ² not computed)\n")
    end

    # Also χ² for non-split steps (should be uniform if Δ is random).
    if n_nonspl > 0
        expected2   = n_nonspl / nb
        chi2_nonspl = sum((x - expected2)^2 / max(1.0, expected2)
                          for x in stat.nonsplit_hist)
        dof2 = nb - 1
        @printf("    non-split χ²           : %.2f  (dof=%d)\n", chi2_nonspl, dof2)
    end

    # --- Top buckets (show the 5 most-populated split buckets) ---
    if n_split > 0 && nb >= 5
        indexed  = collect(enumerate(stat.split_hist))
        top5     = sort(indexed, by=x->-x[2])[1:min(5, end)]
        @printf("    top split buckets (bucket_idx, count):\n")
        for (bi, cnt) in top5
            frac = p > 0 ? @sprintf(" [a ∈ [%d,%d))", (bi-1)*p÷nb, bi*p÷nb) : ""
            @printf("      bucket %4d%s : %d  (%.2f%% of splits)\n",
                    bi, frac, cnt, 100.0*cnt/n_split)
        end
    end

    # --- Seq 1: Run-length distribution KS test ---
    @printf("  Seq 1 — Run-length distribution (KS vs Geometric(1/2)):\n")
    for (label, hist) in (("split", stat.run_hist_split), ("non-split", stat.run_hist_nonsplit))
        n_runs = sum(hist)
        if n_runs >= 10
            # Empirical CDF vs Geometric(1/2) CDF: P(L ≤ k) = 1 - (1/2)^k
            ks_stat = 0.0
            cumul   = 0.0
            for k in 1:MAX_RUN_LEN
                cumul     += hist[k] / n_runs
                geo_cdf    = 1.0 - 0.5^k
                ks_stat    = max(ks_stat, abs(cumul - geo_cdf))
            end
            mean_run = sum(k * hist[k] for k in 1:MAX_RUN_LEN) / n_runs
            # Geometric(1/2) has mean = 2.
            flag = ks_stat > 0.05 ? (mean_run > 2.0 ? " ← LONG RUNS (pos corr)" :
                                                        " ← SHORT RUNS (anti-corr)") :
                                    " (consistent with i.i.d.)"
            @printf("    %-9s runs: n=%d  mean_len=%.2f  KS=%.4f%s\n",
                    label, n_runs, mean_run, ks_stat, flag)
            # Show run-length histogram up to k=10
            @printf("      len:  %s\n", join([@sprintf("%4d", k) for k in 1:min(10,MAX_RUN_LEN)], " "))
            @printf("      cnt:  %s\n", join([@sprintf("%4d", hist[k]) for k in 1:min(10,MAX_RUN_LEN)], " "))
            if MAX_RUN_LEN > 10
                overflow = sum(hist[11:end])
                @printf("      cnt[11+]: %d\n", overflow)
            end
        else
            @printf("    %-9s runs: n=%d  (too few for KS test)\n", label, n_runs)
        end
    end
    println()

    # --- Seq 2: LP1-conj Fano factor + CIR + Spectral (Welch PSD, spectrogram,
    #           Allan factor) + key fingerprint ---
    @printf("  Seq 2 — LP1-conj temporal analysis:\n")
    arrivals = stat.lp1_conj_arrivals
    lp_keys  = stat.lp1_conj_keys
    if length(arrivals) >= 4
        # Sort by arrival time (merge across threads may be out of order).
        perm     = sortperm(arrivals)
        arrivals = arrivals[perm]
        lp_keys  = lp_keys[perm]

        gaps    = [arrivals[i] - arrivals[i-1] for i in 2:length(arrivals)]
        n_gaps  = length(gaps)
        mean_gap = sum(gaps) / n_gaps
        var_gap  = n_gaps > 1 ? sum((g - mean_gap)^2 for g in gaps) / (n_gaps - 1) :
                                 0.0
        fano    = var_gap / max(1.0, mean_gap)
        flag_fano = fano > 2.0 ? " ← CLUSTERING (algebraic structure)" :
                    fano < 0.5 ? " ← ANTI-CLUSTERING (over-dispersed)"  :
                                 " (consistent with Poisson)"
        @printf("    LP1-conj hits    : %d\n", length(arrivals))
        @printf("    inter-arrival μ  : %.1f steps\n", mean_gap)
        @printf("    inter-arrival σ² : %.1f\n", var_gap)
        @printf("    Fano factor      : %.3f%s\n", fano, flag_fano)

        # ---- Conditional Intensity Ratio (CIR) --------------------------------
        # Null realisations are independent — parallelise over them with
        # per-thread RNGs.  Observed counts are O(N log N) and fast; serial.
        @printf("    Conditional Intensity Ratios (CIR) vs shuffled-gap null:\n")
        @printf("      window  observed  null_mean  CIR    interpretation\n")
        n_hits   = length(arrivals)
        n_shuf   = 20
        # Pre-generate all n_shuf shuffled arrival arrays in parallel.
        # One RNG per iteration slot — avoids threadid() bounds issues when
        # Julia schedules tasks with IDs that exceed nthreads().
        cir_rngs     = [MersenneTwister(rand(UInt64)) for _ in 1:n_shuf]
        null_arrs    = [similar(arrivals) for _ in 1:n_shuf]
        Threads.@threads for si in 1:n_shuf
            sg     = copy(gaps)
            rng_c  = cir_rngs[si]
            for k in n_gaps:-1:2
                j2 = rand(rng_c, 1:k)
                sg[k], sg[j2] = sg[j2], sg[k]
            end
            na = null_arrs[si]
            na[1] = arrivals[1]
            for k in 2:n_hits
                na[k] = na[k-1] + sg[k-1]
            end
            sort!(na)
        end

        for W in (10, 50, 200, 500, 1000, 2000, 5000, 10000, 50000, 100000, 250000, 500000, 1000000)
            # Observed count: O(N log N), fast serial.
            obs_count = 0
            for i in 1:n_hits
                hi = searchsortedlast(arrivals, arrivals[i] + W)
                obs_count += max(0, hi - i)
            end

            # Null: reuse pre-shuffled arrays — just count pairs per array.
            null_counts = zeros(Int, n_shuf)
            Threads.@threads for si in 1:n_shuf
                na  = null_arrs[si]
                cnt = 0
                for i in 1:n_hits
                    hi = searchsortedlast(na, na[i] + W)
                    cnt += max(0, hi - i)
                end
                null_counts[si] = cnt
            end
            null_mean = sum(null_counts) / n_shuf
            cir       = obs_count / max(1.0, null_mean)
            flag_cir  = cir > 1.5 ? " ← HOT (basin exploitable)" :
                        cir < 0.7 ? " ← COLD (anti-clustered)"   :
                                    " (≈ random)"
            @printf("      W=%-5d  %8d  %9.1f  %5.3f  %s\n",
                    W, obs_count, null_mean, cir, flag_cir)
        end

        # ---- Spectral 1: Welch PSD of hit-indicator binary sequence -------------
        # Bin arrivals into fixed-width windows → binary indicator series → DFT.
        # Compare low-frequency vs high-frequency power to detect long-range
        # organisation invisible to short-lag CIR.
        #
        # Parallelism: real windows and each shuffled-null realisation are
        # independent.  We use @threads over both loops; each thread gets its
        # own MersenneTwister so there is no RNG contention.
        @printf("    Welch PSD (hit-indicator series):\n")
        if length(arrivals) >= 8
            total_span = arrivals[end] - arrivals[1] + 1
            # Use ~64 windows; each window covers total_span/64 steps.
            n_welch_win = max(4, min(64, length(arrivals) ÷ 8))
            win_len     = max(8, total_span ÷ n_welch_win)
            n_bins_half = win_len ÷ 2          # positive-frequency bins

            # Inner DFT helper — pure function, no captures, safe to call from
            # any thread.  O(n²) is fine: win_len is typically ≤512.
            function _psd_window(hit_indicator::Vector{Float64}, nb::Int)::Vector{Float64}
                n = length(hit_indicator)
                w  = [0.5 * (1.0 - cos(2π * (i-1) / max(1, n-1))) for i in 1:n]
                xw = hit_indicator .* w
                out = zeros(Float64, nb)
                for k in 1:nb
                    s     = zero(ComplexF64)
                    tw    = exp(-2π * im * (k-1) / n)
                    tw_pw = one(ComplexF64)
                    for j in 1:n
                        s    += xw[j] * tw_pw
                        tw_pw *= tw
                    end
                    out[k] = abs2(s)
                end
                return out
            end

            # --- Real PSD: parallel over Welch windows --------------------------
            # One result slot per window iteration — no threadid() indexing.
            psd_wins    = [zeros(Float64, n_bins_half) for _ in 1:n_welch_win]
            wins_valid  = zeros(Bool, n_welch_win)
            offset      = arrivals[1]

            Threads.@threads for wi in 0:(n_welch_win - 1)
                t_start = offset + wi * win_len
                ind     = zeros(Float64, win_len)
                for t in arrivals
                    idx = t - t_start + 1
                    if 1 <= idx <= win_len
                        ind[idx] = 1.0
                    end
                end
                if sum(ind) >= 1
                    psd_wins[wi + 1]  = _psd_window(ind, n_bins_half)
                    wins_valid[wi + 1] = true
                end
            end
            psd_sum     = reduce(.+, psd_wins[wins_valid])
            n_wins_used = sum(wins_valid)

            # --- Shuffled-null PSD: parallel over realisations ------------------
            # One RNG + result slot per realisation — no threadid() indexing.
            n_spec_shuf   = 20
            shuf_rngs     = [MersenneTwister(rand(UInt64)) for _ in 1:n_spec_shuf]
            psd_shuf_slots = [zeros(Float64, n_bins_half) for _ in 1:n_spec_shuf]
            shuf_valid    = zeros(Bool, n_spec_shuf)

            Threads.@threads for si in 1:n_spec_shuf
                rng       = shuf_rngs[si]
                shuf_g    = copy(gaps)
                for k in length(shuf_g):-1:2
                    j2 = rand(rng, 1:k)
                    shuf_g[k], shuf_g[j2] = shuf_g[j2], shuf_g[k]
                end
                null_arr2    = similar(arrivals)
                null_arr2[1] = arrivals[1]
                for k in 2:length(arrivals)
                    null_arr2[k] = null_arr2[k-1] + shuf_g[k-1]
                end
                sort!(null_arr2)
                win_sum  = zeros(Float64, n_bins_half)
                win_cnt  = 0
                for wi in 0:(n_welch_win - 1)
                    t_start = offset + wi * win_len
                    ind2    = zeros(Float64, win_len)
                    for t in null_arr2
                        idx = t - t_start + 1
                        if 1 <= idx <= win_len
                            ind2[idx] = 1.0
                        end
                    end
                    if sum(ind2) >= 1
                        win_sum .+= _psd_window(ind2, n_bins_half)
                        win_cnt  += 1
                    end
                end
                if win_cnt >= 1
                    psd_shuf_slots[si] = win_sum ./ win_cnt
                    shuf_valid[si]     = true
                end
            end
            psd_shuf_avg = any(shuf_valid) ?
                           reduce(.+, psd_shuf_slots[shuf_valid]) ./ max(1, sum(shuf_valid)) :
                           zeros(Float64, n_bins_half)

            if n_wins_used >= 2
                psd_avg = psd_sum ./ n_wins_used

                # Summarise: low-freq (lowest 10%) vs high-freq (top 50%) power ratio.
                n_lo = max(1, n_bins_half ÷ 10)
                n_hi = max(1, n_bins_half ÷ 2)
                power_lo  = sum(psd_avg[1:n_lo])
                power_hi  = sum(psd_avg[(n_bins_half - n_hi + 1):end])
                power_lo_s = sum(psd_shuf_avg[1:n_lo])
                power_hi_s = sum(psd_shuf_avg[(n_bins_half - n_hi + 1):end])

                lo_lift = power_lo / max(1e-30, power_lo_s)
                hi_lift = power_hi / max(1e-30, power_hi_s)

                flag_psd = lo_lift > 2.0 ? " ← LOW-FREQ EXCESS (long-range order)" :
                           lo_lift < 0.5 ? " ← LOW-FREQ DEFICIT" :
                                           " (≈ flat / random)"
                @printf("      windows used         : %d  (win_len=%d, bins=%d)\n",
                        n_wins_used, win_len, n_bins_half)
                @printf("      low-freq power lift  : %.3f%s\n", lo_lift, flag_psd)
                @printf("      high-freq power lift : %.3f\n", hi_lift)

                # Print the first 8 PSD bins (real / shuffled).
                n_show = min(8, n_bins_half)
                @printf("      bin (freq×win_len):  %s\n",
                        join([@sprintf("%6d", k) for k in 1:n_show], " "))
                @printf("      PSD real:            %s\n",
                        join([@sprintf("%6.1f", psd_avg[k]) for k in 1:n_show], " "))
                @printf("      PSD shuffled:        %s\n",
                        join([@sprintf("%6.1f", psd_shuf_avg[k]) for k in 1:n_show], " "))
                @printf("      ratio real/shuf:     %s\n",
                        join([@sprintf("%6.2f", psd_avg[k] / max(1e-30, psd_shuf_avg[k]))
                              for k in 1:n_show], " "))
            else
                @printf("      (too few windowed hits for Welch PSD)\n")
            end
        else
            @printf("      (need ≥8 hits for Welch PSD)\n")
        end
        println()

        # ---- Spectral 2: windowed spectrogram (rolling 4-slice) -----------------
        # Divide arrivals into 4 equal chronological slices; compute per-slice
        # mean gap and hit density.  Reveals regime switching / intermittency
        # that global PSD averages away.
        @printf("    Spectrogram (4-slice chronological):\n")
        if length(arrivals) >= 16
            n_slices  = 4
            slice_len = length(arrivals) ÷ n_slices
            @printf("      slice  hits   span_steps   density(hits/kstep)   mean_gap  cv_gap\n")
            for si in 1:n_slices
                i1 = (si - 1) * slice_len + 1
                i2 = si == n_slices ? length(arrivals) : si * slice_len
                sl_arr  = arrivals[i1:i2]
                sl_n    = length(sl_arr)
                sl_span = sl_arr[end] - sl_arr[1] + 1
                sl_density = 1000.0 * sl_n / max(1, sl_span)
                if sl_n >= 2
                    sl_gaps   = [sl_arr[j] - sl_arr[j-1] for j in 2:sl_n]
                    sl_mean   = sum(sl_gaps) / length(sl_gaps)
                    sl_var    = length(sl_gaps) > 1 ?
                                sum((g - sl_mean)^2 for g in sl_gaps) / (length(sl_gaps) - 1) :
                                0.0
                    sl_cv     = sqrt(sl_var) / max(1.0, sl_mean)
                    @printf("      %5d  %4d  %11d   %19.3f   %8.1f  %.3f\n",
                            si, sl_n, sl_span, sl_density, sl_mean, sl_cv)
                else
                    @printf("      %5d  %4d  %11d   (insufficient)\n", si, sl_n, sl_span)
                end
            end
            # Flag if density varies > 2× between any two slices.
            densities = Float64[]
            for si in 1:n_slices
                i1 = (si - 1) * slice_len + 1
                i2 = si == n_slices ? length(arrivals) : si * slice_len
                sl_arr = arrivals[i1:i2]
                sl_n   = length(sl_arr)
                sl_span = sl_arr[end] - sl_arr[1] + 1
                push!(densities, sl_n / max(1, sl_span))
            end
            d_max = maximum(densities); d_min = minimum(densities)
            ratio_sg = d_max / max(1e-30, d_min)
            flag_sg  = ratio_sg > 2.0 ? " ← REGIME SWITCHING (density varies ×$(round(ratio_sg, digits=1)))" :
                                         " (density stable across slices)"
            @printf("      max/min slice density  : %.2f×%s\n", ratio_sg, flag_sg)
        else
            @printf("      (need ≥16 hits for spectrogram)\n")
        end
        println()

        # ---- Spectral 4: Allan factor (variance scaling with window size) -------
        # F(T) = Var(N_T) / E[N_T] where N_T = hit count in window of T steps.
        # Poisson → F(T) ≈ 1 for all T.
        # Clustered (long-memory) → F(T) grows with T.
        # Compared against shuffled-gap null to isolate the signal.
        @printf("    Allan factor F(T) = Var(N_T)/E[N_T]:\n")
        if length(arrivals) >= 8
            total_span_af = arrivals[end] - arrivals[1] + 1
            # Choose window sizes as geometric progression from ~10 to total_span/4.
            min_T  = max(10, total_span_af ÷ 1000)
            max_T  = total_span_af ÷ 4
            af_windows = Int[]
            if min_T < max_T
                T = min_T
                while T <= max_T
                    push!(af_windows, T)
                    T = max(T + 1, round(Int, T * 2.5))
                end
            end
            if isempty(af_windows)
                push!(af_windows, max(10, total_span_af ÷ 8))
            end

            function allan_factor(arr::Vector{Int}, T::Int, span::Int)
                # Partition [arr[1], arr[1]+span) into windows of T steps.
                n_windows = max(1, span ÷ T)
                counts = zeros(Int, n_windows)
                t0 = arr[1]
                for a in arr
                    wi = min(n_windows, (a - t0) ÷ T + 1)
                    counts[wi] += 1
                end
                mn = sum(counts) / n_windows
                vr = n_windows > 1 ?
                     sum((c - mn)^2 for c in counts) / (n_windows - 1) : 0.0
                return vr / max(1e-30, mn), mn
            end

            # Shuffled null for Allan factor — one RNG per iteration slot.
            n_af_shuf    = 10
            af_rngs      = [MersenneTwister(rand(UInt64)) for _ in 1:n_af_shuf]
            null_arrs_af = [similar(arrivals) for _ in 1:n_af_shuf]
            Threads.@threads for si in 1:n_af_shuf
                sg    = copy(gaps)
                rng_a = af_rngs[si]
                for k in length(sg):-1:2
                    j2 = rand(rng_a, 1:k)
                    sg[k], sg[j2] = sg[j2], sg[k]
                end
                na = null_arrs_af[si]
                na[1] = arrivals[1]
                for k in 2:length(arrivals)
                    na[k] = na[k-1] + sg[k-1]
                end
                sort!(na)
            end

            @printf("      T_steps    F(T)_real   F(T)_null   lift   interpretation\n")
            # Parallel over window sizes: each T is independent.
            n_af_T       = length(af_windows)
            results_af   = Vector{NTuple{4,Float64}}(undef, n_af_T)  # (T, f_real, f_null, lift)
            Threads.@threads for ti in 1:n_af_T
                T      = af_windows[ti]
                f_real, _ = allan_factor(arrivals, T, total_span_af)
                f_null_sum = 0.0
                for si in 1:n_af_shuf
                    fn, _ = allan_factor(null_arrs_af[si], T, total_span_af)
                    f_null_sum += fn
                end
                f_null = f_null_sum / n_af_shuf
                lift   = f_real / max(1e-30, f_null)
                results_af[ti] = (Float64(T), f_real, f_null, lift)
            end
            for (T_f, f_real, f_null, lift_af) in results_af
                flag_af = lift_af > 2.0 ? " CLUSTERED" :
                          lift_af < 0.5 ? " ANTI-CLUST" :
                                          " ≈Poisson"
                @printf("      %9d  %11.3f  %10.3f  %6.2f  %s\n",
                        round(Int, T_f), f_real, f_null, lift_af, flag_af)
            end
            println()

            # Slope of log F(T) vs log T (Hurst-like exponent estimate).
            if length(af_windows) >= 3
                log_T = [log(Float64(T)) for T in af_windows]
                log_F = [log(max(1e-30, r[2])) for r in results_af]
                n_pts = length(log_T)
                mx = sum(log_T) / n_pts; my = sum(log_F) / n_pts
                slope_num = sum((log_T[i] - mx) * (log_F[i] - my) for i in 1:n_pts)
                slope_den = sum((log_T[i] - mx)^2 for i in 1:n_pts)
                hurst_slope = slope_den > 0.0 ? slope_num / slope_den : 0.0
                flag_hurst = hurst_slope > 0.3  ? " ← LONG-MEMORY (H>0.5 analog)" :
                             hurst_slope < -0.1 ? " ← ANTI-PERSISTENT" :
                                                   " (≈ Poisson, uncorrelated)"
                @printf("      Allan log-log slope (Hurst proxy): %.3f%s\n",
                        hurst_slope, flag_hurst)
            end
        else
            @printf("      (need ≥8 hits for Allan factor)\n")
        end
        println()

        # ════════════════════════════════════════════════════════════════════
        # New 1 — Autocorrelation of hit-density over coarse bins
        # ════════════════════════════════════════════════════════════════════
        # Bin arrivals into windows of sizes T ∈ {10⁴, 2·10⁴, …} and compute
        # normalised lag-k autocorrelations of the count series N_T[w].
        # Poisson → ACF ≈ 0 at all lags.  Positive ACF → persistent hot/cold
        # epochs; negative → alternating (anti-persistence).
        # Parallel over bin-size values; each is independent.
        @printf("    Density autocorrelation (ACF of coarse hit-count series):\n")
        if length(arrivals) >= 16
            total_span_acf = arrivals[end] - arrivals[1] + 1
            # Choose 4 bin sizes geometrically; need ≥20 bins each.
            acf_bin_sizes = Int[]
            T_try = max(100, total_span_acf ÷ 200)
            while T_try <= total_span_acf ÷ 20 && length(acf_bin_sizes) < 5
                push!(acf_bin_sizes, T_try)
                T_try = max(T_try + 1, round(Int, T_try * 2.0))
            end

            # Per bin-size result: (T, n_bins, acf_lag1, acf_lag2, acf_lag3, flag)
            acf_results = Vector{Any}(undef, length(acf_bin_sizes))
            Threads.@threads for ti in 1:length(acf_bin_sizes)
                T       = acf_bin_sizes[ti]
                n_bins  = total_span_acf ÷ T
                n_bins < 8 && (acf_results[ti] = (T, n_bins, NaN, NaN, NaN); continue)
                counts  = zeros(Float64, n_bins)
                t0      = arrivals[1]
                for a in arrivals
                    wi = min(n_bins, (a - t0) ÷ T + 1)
                    counts[wi] += 1.0
                end
                mn   = sum(counts) / n_bins
                var0 = sum((c - mn)^2 for c in counts) / n_bins
                if var0 < 1e-30
                    acf_results[ti] = (T, n_bins, 0.0, 0.0, 0.0)
                    continue
                end
                # ACF at lags 1, 2, 3.
                acf = ntuple(lag -> begin
                    cov = sum((counts[w] - mn) * (counts[w + lag] - mn)
                              for w in 1:(n_bins - lag)) / (n_bins - lag)
                    cov / var0
                end, 3)
                acf_results[ti] = (T, n_bins, acf[1], acf[2], acf[3])
            end

            @printf("      T_steps  n_bins   ACF(1)   ACF(2)   ACF(3)   interpretation\n")
            for r in acf_results
                T, nb_r = r[1], r[2]
                if isnan(r[3])
                    @printf("      %7d  %6d   (too few bins)\n", T, nb_r)
                    continue
                end
                a1, a2, a3 = r[3], r[4], r[5]
                flag_acf = abs(a1) > 0.15 ?
                           (a1 > 0 ? " ← PERSISTENT (hot/cold epochs)" :
                                     " ← ANTI-PERSISTENT (alternating)") :
                           " (≈ uncorrelated)"
                @printf("      %7d  %6d   %+6.3f   %+6.3f   %+6.3f  %s\n",
                        T, nb_r, a1, a2, a3, flag_acf)
            end
        else
            @printf("      (need ≥16 hits for ACF)\n")
        end
        println()

        # ════════════════════════════════════════════════════════════════════
        # New 2 — Hot/cold window conditioning
        # ════════════════════════════════════════════════════════════════════
        # Classify each fixed-width window as "hot" (hit density ≥ median) or
        # "cold" (< median).  Then compare the *next* window's closure rate
        # (hit count) conditioned on the current window's class.
        # Hot→hot persistence means the walk has memory: a burst now predicts
        # a burst soon.  Reported as lift = E[N_{t+1}|hot] / E[N_{t+1}|cold].
        @printf("    Hot/cold window conditioning (burst memory):\n")
        if length(arrivals) >= 20
            total_span_hc = arrivals[end] - arrivals[1] + 1
            T_hc          = max(100, total_span_hc ÷ 50)   # ~50 windows
            n_wins_hc     = total_span_hc ÷ T_hc
            if n_wins_hc >= 10
                counts_hc = zeros(Int, n_wins_hc)
                t0_hc     = arrivals[1]
                for a in arrivals
                    wi = min(n_wins_hc, (a - t0_hc) ÷ T_hc + 1)
                    counts_hc[wi] += 1
                end
                # Median threshold.
                sorted_c = sort(counts_hc)
                median_c = length(sorted_c) % 2 == 0 ?
                           (sorted_c[length(sorted_c)÷2] + sorted_c[length(sorted_c)÷2 + 1]) / 2.0 :
                           Float64(sorted_c[(length(sorted_c)+1)÷2])
                # For each window w, record next-window count conditioned on hot/cold.
                hot_next = Int[]; cold_next = Int[]
                for w in 1:(n_wins_hc - 1)
                    if counts_hc[w] >= median_c
                        push!(hot_next,  counts_hc[w + 1])
                    else
                        push!(cold_next, counts_hc[w + 1])
                    end
                end
                n_hot  = length(hot_next);  n_cold = length(cold_next)
                mu_hot  = n_hot  > 0 ? sum(hot_next)  / n_hot  : 0.0
                mu_cold = n_cold > 0 ? sum(cold_next) / n_cold : 0.0
                lift_hc = mu_hot / max(1e-9, mu_cold)
                flag_hc = lift_hc > 1.3 ? " ← MEMORY: hot predicts hot" :
                          lift_hc < 0.77 ? " ← ANTI-MEMORY: hot predicts cold" :
                                           " (no burst memory)"
                @printf("      window T       : %d steps (%d windows)\n", T_hc, n_wins_hc)
                @printf("      density median : %.2f hits/window\n", median_c)
                @printf("      hot windows    : %d  →  next mean = %.3f hits\n", n_hot, mu_hot)
                @printf("      cold windows   : %d  →  next mean = %.3f hits\n", n_cold, mu_cold)
                @printf("      lift hot/cold  : %.3f%s\n", lift_hc, flag_hc)

                # Also compute 2-step: hot window now → hot window in 2 steps.
                if n_wins_hc >= 12
                    hot2_next = Int[]; cold2_next = Int[]
                    for w in 1:(n_wins_hc - 2)
                        if counts_hc[w] >= median_c
                            push!(hot2_next,  counts_hc[w + 2])
                        else
                            push!(cold2_next, counts_hc[w + 2])
                        end
                    end
                    mu_hot2  = length(hot2_next)  > 0 ? sum(hot2_next)  / length(hot2_next)  : 0.0
                    mu_cold2 = length(cold2_next) > 0 ? sum(cold2_next) / length(cold2_next) : 0.0
                    lift2    = mu_hot2 / max(1e-9, mu_cold2)
                    @printf("      lag-2 lift     : %.3f  (memory decay %s)\n",
                            lift2, lift2 > 1.0 ? "persists" : "gone")
                end
            else
                @printf("      (need ≥10 windows; got %d with T=%d)\n", n_wins_hc, T_hc)
            end
        else
            @printf("      (need ≥20 hits)\n")
        end
        println()

        # ════════════════════════════════════════════════════════════════════
        # New 3 — State-space a-region hotness (dynamic bias)
        # ════════════════════════════════════════════════════════════════════
        # Compare lp1_conj_a_hist (emissions per a-bucket) against split_hist
        # (visits per a-bucket) to find dynamically hot a-regions.
        # lift[bucket] = (emissions/total_emissions) / (visits/total_visits).
        # lift >> 1 means that bucket produces LP1-conj hits at higher-than-
        # expected rate given how often it is visited — dynamic bias even when
        # the global a-distribution looks uniform.
        @printf("    State-space a-region hotness (dynamic vs static bias):\n")
        lc_hist   = stat.lp1_conj_a_hist
        vis_hist  = stat.split_hist   # visits = split steps (where LP can fire)
        n_lc_tot  = sum(lc_hist)
        n_vis_tot = sum(vis_hist)
        if n_lc_tot >= 10 && n_vis_tot >= 10
            # Per-bucket lift, clipped to avoid divide-by-zero.
            lifts = [
                (lc_hist[i] / max(1e-30, Float64(n_lc_tot))) /
                (vis_hist[i] / max(1e-30, Float64(n_vis_tot)))
                for i in eachindex(lc_hist)
            ]
            # Sort and report top-5 and bottom-5.
            order = sortperm(lifts, rev=true)
            @printf("      total LP1-conj emissions : %d  total split visits: %d\n",
                    n_lc_tot, n_vis_tot)
            @printf("      TOP-5 hot a-buckets (lift = emission_rate / visit_rate):\n")
            for rank in 1:min(5, length(order))
                bi = order[rank]
                frac_str = p > 0 ? @sprintf(" [a∈[%d,%d))", (bi-1)*p÷nb, bi*p÷nb) : ""
                @printf("        bucket %4d%s  lift=%.3f  emissions=%d  visits=%d\n",
                        bi, frac_str, lifts[bi], lc_hist[bi], vis_hist[bi])
            end
            @printf("      BOTTOM-5 cold a-buckets:\n")
            for rank in max(1,length(order)-4):length(order)
                bi = order[rank]
                frac_str = p > 0 ? @sprintf(" [a∈[%d,%d))", (bi-1)*p÷nb, bi*p÷nb) : ""
                @printf("        bucket %4d%s  lift=%.3f  emissions=%d  visits=%d\n",
                        bi, frac_str, lifts[bi], lc_hist[bi], vis_hist[bi])
            end
            # χ² test: are emissions distributed proportional to visits?
            expected_lc = [vis_hist[i] * Float64(n_lc_tot) / max(1.0, Float64(n_vis_tot))
                           for i in eachindex(vis_hist)]
            chi2_lc = sum((lc_hist[i] - expected_lc[i])^2 / max(1.0, expected_lc[i])
                          for i in eachindex(lc_hist))
            dof_lc  = length(lc_hist) - 1
            ratio_lc = chi2_lc / max(1.0, Float64(dof_lc))
            flag_lc  = ratio_lc > 2.0 ? " ← DYNAMIC BIAS (some a-regions systematically hotter)" :
                                          " (emissions proportional to visits)"
            @printf("      χ²/dof (emissions vs visits): %.3f%s\n", ratio_lc, flag_lc)
        else
            @printf("      (need ≥10 LP1-conj emissions; got %d)\n", n_lc_tot)
        end
        println()

        # ════════════════════════════════════════════════════════════════════
        # New 4 — Multitaper PSD + spectral slope (1/fᵅ test)
        # ════════════════════════════════════════════════════════════════════
        # Uses K=4 DPSS-like tapers (approximated by cosine tapers of orders
        # 1..K) for reduced variance at low frequencies.  Reports spectral
        # slope α from log-log OLS fit to avoid Welch bias at very low freqs.
        # All tapers computed in parallel (each is an independent DFT).
        @printf("    Multitaper PSD + spectral slope (1/fᵅ):\n")
        if length(arrivals) >= 16
            total_span_mt = arrivals[end] - arrivals[1] + 1
            n_mt_bins = min(512, max(32, length(arrivals) * 2))
            # Bin hits into n_mt_bins equal-width time buckets.
            mt_counts = zeros(Float64, n_mt_bins)
            t0_mt     = arrivals[1]
            bin_width = max(1, total_span_mt ÷ n_mt_bins)
            for a in arrivals
                bi = min(n_mt_bins, (a - t0_mt) ÷ bin_width + 1)
                mt_counts[bi] += 1.0
            end
            # Subtract mean.
            mt_mean    = sum(mt_counts) / n_mt_bins
            mt_centred = mt_counts .- mt_mean
            n_bins_half_mt = n_mt_bins ÷ 2

            # K cosine tapers: w_k[j] = sqrt(2/(N+1)) * sin(k*π*j/(N+1)), k=1..K
            K_tapers = 4
            mt_psd_slots = [zeros(Float64, n_bins_half_mt) for _ in 1:K_tapers]
            Threads.@threads for k in 1:K_tapers
                taper = [sqrt(2.0 / (n_mt_bins + 1)) *
                         sin(k * π * j / (n_mt_bins + 1))
                         for j in 1:n_mt_bins]
                xw    = mt_centred .* taper
                psd_k = zeros(Float64, n_bins_half_mt)
                for freq in 1:n_bins_half_mt
                    s     = zero(ComplexF64)
                    tw    = exp(-2π * im * (freq - 1) / n_mt_bins)
                    tw_pw = one(ComplexF64)
                    for j in 1:n_mt_bins
                        s    += xw[j] * tw_pw
                        tw_pw *= tw
                    end
                    psd_k[freq] = abs2(s)
                end
                mt_psd_slots[k] = psd_k
            end
            mt_psd = reduce(.+, mt_psd_slots) ./ K_tapers

            # Spectral slope: OLS log(PSD) ~ α·log(freq) over low 20% of freqs.
            n_fit = max(4, n_bins_half_mt ÷ 5)
            log_f = [log(Float64(k)) for k in 1:n_fit]
            log_p = [log(max(1e-30, mt_psd[k])) for k in 1:n_fit]
            mf = sum(log_f) / n_fit; mp = sum(log_p) / n_fit
            slope_num_mt = sum((log_f[i] - mf) * (log_p[i] - mp) for i in 1:n_fit)
            slope_den_mt = sum((log_f[i] - mf)^2 for i in 1:n_fit)
            alpha_mt     = slope_den_mt > 0 ? -slope_num_mt / slope_den_mt : 0.0
            # α > 0 means power decreases with freq → red/1/fᵅ noise.
            flag_alpha = alpha_mt > 1.5  ? " ← STRONG 1/fᵅ (α≈$(round(alpha_mt,digits=2)), long-memory)" :
                         alpha_mt > 0.5  ? " ← MILD 1/fᵅ (sub-Brownian memory)" :
                         alpha_mt < -0.3 ? " ← BLUE NOISE (anti-persistent)" :
                                           " (≈ white noise, α≈0)"
            @printf("      bins=%d  tapers=%d  fit_bins=%d\n", n_mt_bins, K_tapers, n_fit)
            @printf("      spectral slope α : %.3f%s\n", alpha_mt, flag_alpha)

            # Show first 8 multitaper PSD bins vs Welch (already computed above
            # if available — just show MT here standalone).
            n_show_mt = min(8, n_bins_half_mt)
            @printf("      freq bin:   %s\n",
                    join([@sprintf("%8d", k) for k in 1:n_show_mt], " "))
            @printf("      MT PSD:     %s\n",
                    join([@sprintf("%8.2f", mt_psd[k]) for k in 1:n_show_mt], " "))
        else
            @printf("      (need ≥16 hits for multitaper PSD)\n")
        end
        println()

        # ════════════════════════════════════════════════════════════════════
        # New 5 — Gap-distribution characterisation (replaces unstable MMPP fit)
        # ════════════════════════════════════════════════════════════════════
        # The symmetric MMPP-2 method-of-moments fit is numerically unstable
        # when the Fano factor is large: it produces negative transition rates
        # (q < 0) and epoch durations of ~10^30 steps — physically meaningless.
        # We replace it with three robust, interpretable diagnostics:
        #
        #   (a) Burst-size distribution: how many hits arrive in bursts of 1/2/3+?
        #       A burst is a run of hits with inter-arrival < burst_sep steps.
        #       Geometric burst sizes → Poisson; heavy tail → clustering.
        #
        #   (b) Hot-window persistence (gap-conditioned tail):
        #       Fraction of gaps that are "short" (< μ/2) vs "long" (> 2μ).
        #       For a Poisson process P(gap < μ/2) ≈ 1 - e^{-0.5} ≈ 0.39 and
        #       P(gap > 2μ) ≈ e^{-2} ≈ 0.135.  Excess short-gap fraction means
        #       bursts; excess long-gap fraction means cold epochs between bursts.
        #
        #   (c) Geometric vs heavy-tail gap test (KS vs Exponential):
        #       Rescale gaps by their mean → unit-mean Exponential(1) null.
        #       KS statistic > 0.1 flags a non-Poisson gap distribution.
        #       A right-skewed empirical CDF (excess large gaps) is the
        #       signature of a bursty / heavy-tailed process.
        @printf("    Gap distribution (burst / persistence / tail):\n")
        if length(arrivals) >= 10
            n_g      = length(gaps)
            mu_g     = mean_gap
            var_g    = var_gap

            # Lag-1 ACF of gaps (retain for summary line).
            rho1 = 0.0
            if n_g >= 4
                rho1_num = sum((gaps[i] - mu_g) * (gaps[i+1] - mu_g) for i in 1:(n_g-1))
                rho1_den = sum((g - mu_g)^2 for g in gaps)
                rho1     = rho1_den > 0.0 ? rho1_num / rho1_den : 0.0
            end
            @printf("      Observed gap stats: μ=%.1f  σ²=%.1f  Fano=%.3f  ρ₁=%+.4f\n",
                    mu_g, var_g, fano, rho1)

            # (a) Burst-size distribution.
            # Define burst separator as max(1, floor(μ/3)).
            burst_sep    = max(1, floor(Int, mu_g / 3.0))
            burst_sizes  = Int[]
            cur_burst    = 1
            for k in 1:(n_g)
                if k <= n_g && gaps[k] <= burst_sep
                    cur_burst += 1
                else
                    push!(burst_sizes, cur_burst)
                    cur_burst = 1
                end
            end
            push!(burst_sizes, cur_burst)  # last burst
            n_bursts = length(burst_sizes)
            cnt1 = count(==(1), burst_sizes)
            cnt2 = count(==(2), burst_sizes)
            cnt3p = count(>=(3), burst_sizes)
            mean_burst = n_bursts > 0 ? sum(burst_sizes) / n_bursts : 0.0
            max_burst  = n_bursts > 0 ? maximum(burst_sizes) : 0
            # Geometric(p) burst sizes: P(size=k) = (1-p)^{k-1}·p.
            # Mean = 1/p, so p = 1/mean_burst.
            p_geo = n_bursts > 0 && mean_burst > 1.0 ? 1.0 / mean_burst : 1.0
            # KS vs Geometric CDF for burst sizes.
            bsorted = sort(burst_sizes)
            ks_b = 0.0; cumul_b = 0.0
            for bs in bsorted
                cumul_b += 1.0 / n_bursts
                geo_cdf_b = 1.0 - (1.0 - p_geo)^bs
                ks_b = max(ks_b, abs(cumul_b - geo_cdf_b))
            end
            flag_burst = ks_b > 0.1 ? " ← NON-GEOMETRIC (heavy-tail bursts)" :
                                       " (consistent with geometric)"
            @printf("      (a) Burst-size distribution (sep=%.0f steps):\n", Float64(burst_sep))
            @printf("          n_bursts=%d  mean=%.2f  max=%d\n", n_bursts, mean_burst, max_burst)
            @printf("          size=1: %d (%.1f%%)  size=2: %d (%.1f%%)  size≥3: %d (%.1f%%)\n",
                    cnt1, 100.0*cnt1/max(1,n_bursts),
                    cnt2, 100.0*cnt2/max(1,n_bursts),
                    cnt3p, 100.0*cnt3p/max(1,n_bursts))
            @printf("          KS vs Geometric(1/mean)=%.4f%s\n", ks_b, flag_burst)

            # (b) Short/long gap fractions vs Poisson prediction.
            n_short = count(g -> g < mu_g / 2.0, gaps)
            n_long  = count(g -> g > 2.0 * mu_g, gaps)
            f_short = n_short / n_g
            f_long  = n_long  / n_g
            # Poisson(rate 1/μ) predictions:
            poisson_short = 1.0 - exp(-0.5)   # ≈ 0.394
            poisson_long  = exp(-2.0)          # ≈ 0.135
            flag_pers = if f_short > poisson_short * 1.3 || f_long > poisson_long * 1.5
                " ← HOT/COLD PERSISTENCE (excess short+long gaps)"
            elseif f_short < poisson_short * 0.7
                " ← ANTI-PERSISTENT (gaps more uniform than Poisson)"
            else
                " (consistent with Poisson persistence)"
            end
            @printf("      (b) Hot/cold persistence:\n")
            @printf("          short (< μ/2): %.1f%%  [Poisson expect %.1f%%]\n",
                    100.0*f_short, 100.0*poisson_short)
            @printf("          long  (> 2μ) : %.1f%%  [Poisson expect %.1f%%]%s\n",
                    100.0*f_long, 100.0*poisson_long, flag_pers)

            # (c) KS test of rescaled gaps vs Exponential(1).
            rescaled = sort(gaps ./ max(1.0, mu_g))
            ks_exp   = 0.0
            for (k, rg) in enumerate(rescaled)
                emp_cdf = k / n_g
                exp_cdf = 1.0 - exp(-rg)
                ks_exp  = max(ks_exp, abs(emp_cdf - exp_cdf))
            end
            # Right-skew: top 5% of gaps vs Exponential prediction.
            top5_thresh = -log(0.05)   # Exp(1) quantile at 95% ≈ 3.0
            n_top5 = count(g -> g / mu_g > top5_thresh, gaps)
            expected_top5 = round(Int, 0.05 * n_g)
            flag_tail = if n_top5 > 2 * expected_top5
                @sprintf(" ← HEAVY RIGHT TAIL (%d gaps > 3μ, expected %d)", n_top5, expected_top5)
            elseif ks_exp > 0.1
                " ← NON-EXPONENTIAL gap distribution"
            else
                " (consistent with Exponential / Poisson)"
            end
            @printf("      (c) Gap tail test (KS vs Exponential):\n")
            @printf("          KS=%.4f  gaps>3μ: %d (expected %d)%s\n",
                    ks_exp, n_top5, expected_top5, flag_tail)
        else
            @printf("      (need ≥10 hits for gap analysis)\n")
        end
        println()

        # ---- Key fingerprint: do close-in-time hits share algebraic keys? ------
        # For each hit i, look at hits within W_fp steps and count what fraction
        # share the same lp_key.  Compare to the global key collision rate
        # (expected under random key assignment).
        if !isempty(lp_keys) && length(lp_keys) == n_hits
            W_fp         = 2000         # fingerprint window — matches mid-range CIR lag
            fp_pairs     = 0           # pairs within window
            fp_same_key  = 0           # of those, pairs with matching key
            for i in 1:n_hits
                hi = searchsortedlast(arrivals, arrivals[i] + W_fp)
                for j in (i+1):hi
                    fp_pairs += 1
                    if lp_keys[j] == lp_keys[i]
                        fp_same_key += 1
                    end
                end
            end
            # Expected same-key rate under uniform random key assignment:
            # P(key_i == key_j) = Σ_k (count_k / N)² (birthday collision prob).
            key_counts   = Dict{UInt128,Int}()
            for k in lp_keys; key_counts[k] = get(key_counts, k, 0) + 1; end
            expected_frac = sum(Float64(v)^2 for v in values(key_counts)) /
                            Float64(n_hits)^2
            obs_frac      = fp_same_key / max(1, fp_pairs)
            key_lift      = obs_frac / max(1e-9, expected_frac)
            flag_key      = key_lift > 2.0 ? " ← FINGERPRINT: close hits share keys" :
                                              " (key sharing ≈ random)"
            @printf("    Key fingerprint (W=%d): %d pairs, %d same-key (%.2f%%), expected %.2f%%, lift=%.2f%s\n",
                    W_fp, fp_pairs, fp_same_key,
                    100.0 * obs_frac, 100.0 * expected_frac,
                    key_lift, flag_key)
        end
    else
        @printf("    LP1-conj hits    : %d  (need ≥4 for analysis)\n", length(arrivals))
    end
    println()

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

    @printf("──────────────────────────────────────────────────────────────────────\n")
    flush(stdout)
end
