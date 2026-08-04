#!/usr/bin/env julia
#
# scaling_sweep.jl
#
# Runs the threaded character sampler across a range of (N, B) pairs,
# tracking two diagnostics as N grows with B ~ N^0.4 held fixed to the
# advisory's scale:
#
#   1. ratio = (MC estimate of sum_{chi!=1}|S_F|^8) / (flat value B^8/N)
#      -- this is the empirical E(S,S)/flat-E(S,S) ratio. Advisory
#      section 7.5's worst-case bound allows this to grow like B^2
#      (i.e. diverge as N -> infinity along B ~ N^0.4). If it instead
#      stays roughly constant (or grows much slower) across the sweep,
#      that is direct empirical evidence AGAINST the pessimistic
#      worst case -- exactly the kind of signal item 8(c) asks for.
#
#   2. max |U(chi)| observed -- should stay near the semicircle bound
#      (~2) with no growing trend if the SU_2/Haar-like behavior
#      extrapolates; a max that creeps up with N is the lumpiness
#      signature.
#
# Both are printed per (N,B) so you can see whether the ratio is
# roughly flat (consistent with (H0)-like behavior) or growing
# (consistent with the B^2 worst case being closer to the truth).
#
# NOTE: this remains the SYNTHETIC cyclic-group stand-in, same caveat
# as character_sampler.jl -- see the HOOK section in that file and
# genus2_hook_template.jl in this directory for wiring in real
# J(F_p)/trial3 data instead.

using Random
using Printf

include("character_sampler.jl")

"""
    sweep(; Ns, m_per_point, m_scaling, m_floor, m_cap, seed)

Ns: vector of group orders to test (use primes for the exact-check
     compatibility if you extend this with the FFT cross-check).
B is set to round(N^0.4) at each point, matching the advisory's scale.

m_scaling controls how the sample count m scales across the sweep,
since a FIXED m samples a shrinking fraction of the (growing)
non-trivial character set as N grows -- this loses tail-detection
power exactly where it matters most (large N, closer to the real
cryptographic regime). Options:
  :fixed   -- m = m_per_point at every N (the old behavior; only use
              this for a quick smoke test, not for trusting the tail
              stats across the sweep)
  :sqrt_N  -- m = m_per_point * sqrt(N / Ns[1]), i.e. grows with the
              square root of N relative to the first point. Keeps
              runtime reasonable (total work is O(m*B) ~ O(N^0.9))
              while still sampling more of the character group as N
              grows.
  :linear_N -- m = m_per_point * (N / Ns[1]). Samples a constant
              FRACTION of the non-trivial character set across the
              sweep (strongest tail-detection guarantee) but total
              work is O(N^1.4) -- gets expensive fast; use m_cap to
              bound it.

m_floor / m_cap clamp the resulting m at each point (m_cap defaults
to N-1, the max possible; set a tighter m_cap to bound runtime under
:linear_N at large N).
"""
function sweep(; Ns::Vector{Int} = [10_007, 100_003, 1_000_003, 10_000_019],
                  m_per_point::Int = 20_000,
                  m_scaling::Symbol = :sqrt_N,
                  m_floor::Int = 2_000,
                  m_cap::Int = typemax(Int),
                  seed::Int = 1)
    N0 = Float64(first(Ns))
    println("N\tB\tm\tratio(MC/flat)\tmax|U|\tmean|U|\tfrac_over_bound\telapsed_s")
    results = NamedTuple[]
    for N in Ns
        B = round(Int, N^0.4)

        m_target = if m_scaling == :fixed
            m_per_point
        elseif m_scaling == :sqrt_N
            round(Int, m_per_point * sqrt(N / N0))
        elseif m_scaling == :linear_N
            round(Int, m_per_point * (N / N0))
        else
            error("unknown m_scaling = $m_scaling (use :fixed, :sqrt_N, or :linear_N)")
        end
        m = clamp(m_target, m_floor, min(m_cap, N - 1))

        rng = MersenneTwister(seed)
        G = AbelianGroup([N])
        F_int = greedy_sidon_subset(N, B, rng)
        defect = sidon_defect(F_int, N)
        if defect != 0
            @warn "N=$N: greedy Sidon construction has defect $defect (not perfectly Sidon)"
        end
        F = [[x] for x in F_int]

        t0 = time()
        result = run_character_sampler_threaded(G, F; m = m,
                                                   seed = seed, k_size = N,
                                                   report_every = typemax(Int))  # quiet per-point
        elapsed = time() - t0

        Bf = Float64(length(F_int))
        flat = (Bf^8) / N
        ratio = result.M8_running[end] / flat
        mags = abs.(result.U_vals)
        maxU = maximum(mags)
        meanU = sum(mags) / length(mags)
        frac_over = count(>(2.0), mags) / length(mags)

        @printf("%d\t%d\t%d\t%.4f\t%.4f\t%.4f\t%.6f\t%.2f\n",
                N, B, m, ratio, maxU, meanU, frac_over, elapsed)

        push!(results, (; N, B, m, ratio, maxU, meanU, frac_over, elapsed))
    end
    return results
end

"""
    fit_growth_exponent(results)

Fits ratio ~ C * N^gamma via ordinary least squares on
log(ratio) = log(C) + gamma*log(N), using the (N, ratio) pairs from
`sweep()`'s output.

Prints the fitted gamma alongside the two reference exponents that
bracket the open question in the advisory doc:
  - gamma ~ 0        : flat/(H0)-consistent regime (best case)
  - gamma ~ 1.2       : section 7.5's pessimistic worst-case bound,
                        ratio <= 2N^2/B^2 with B ~ N^0.4, i.e.
                        2*N^(2 - 0.8) = 2*N^1.2

Also reports the R^2 of the fit as a rough goodness-of-fit check --
a low R^2 means "ratio vs N is not well-described by a single power
law over this range" and the printed gamma should be read with that
caveat, not taken as a precise scaling exponent.

Needs at least 2 points; 3+ strongly recommended (2 points fit any
line exactly with R^2 = 1, which is not informative).
"""
function fit_growth_exponent(results::Vector{<:NamedTuple})
    @assert length(results) >= 2 "need at least 2 sweep points to fit a slope"
    if length(results) == 2
        @warn "only 2 points -- the fit below is exact by construction " *
              "(R^2 = 1 always) and does not by itself confirm a power-law " *
              "relationship; add more Ns to the sweep for a meaningful fit."
    end

    xs = [log(Float64(r.N)) for r in results]
    ys = [log(r.ratio) for r in results]
    n = length(xs)
    xbar, ybar = sum(xs) / n, sum(ys) / n
    sxx = sum((x - xbar)^2 for x in xs)
    sxy = sum((x - xbar) * (y - ybar) for (x, y) in zip(xs, ys))
    gamma = sxy / sxx
    logC = ybar - gamma * xbar

    yhat = [logC + gamma * x for x in xs]
    ss_res = sum((y - yh)^2 for (y, yh) in zip(ys, yhat))
    ss_tot = sum((y - ybar)^2 for y in ys)
    r2 = ss_tot > 0 ? 1 - ss_res / ss_tot : 1.0

    println("\n--- Growth-exponent fit: ratio ~ C * N^gamma ---")
    @printf("  fitted gamma        = %.4f\n", gamma)
    @printf("  fitted C            = %.4e\n", exp(logC))
    @printf("  R^2                 = %.4f\n", r2)
    println("  reference points:")
    println("    gamma ~ 0.0        : flat / (H0)-consistent (best case)")
    println("    gamma ~ 1.2        : section 7.5 pessimistic worst-case bound")
    if gamma < 0.3
        println("  -> closer to the flat regime.")
    elseif gamma > 1.0
        println("  -> close to or exceeding the pessimistic worst-case rate.")
    else
        println("  -> intermediate: growing, but slower than the worst-case bound.")
    end

    return (; gamma, C = exp(logC), r2)
end

"""
    local_growth_exponents(results)

Companion to fit_growth_exponent's single GLOBAL power-law fit --
answers "is the exponent stable across the tested N range, or is it
decreasing/increasing as N grows" (the global fit's R^2 cannot
distinguish these: a single power law can fit a limited N-range
excellently even when the true asymptotic exponent differs from the
locally-measured one, e.g. if there is a crossover at larger N/B not
yet reached, or if the fitted global gamma is simply not
representative of the trend).

For each CONSECUTIVE pair of points (r1, r2) in `results` (assumed
sorted by increasing N, as `sweep()` produces), computes the local
slope

    gamma_local = log(r2.ratio / r1.ratio) / log(r2.N / r1.N)

i.e. the exponent a power law would need between just those two
points. Prints the sequence of local gammas alongside the consecutive
N's they span, plus whether each is LOWER than the previous local
gamma (a decreasing sequence is what "washing out at large N/B" would
look like: if greedy's phase incoherence increasingly cancels as B
grows, the LOCAL exponent between later N-pairs should trend toward
0, not just the single global fit landing at some intermediate value
by construction).

CAVEAT: with only a few sweep points, each local gamma is a 2-point
slope (noisy, no R^2 to check) -- this is a coarser, higher-variance
signal than the global fit, appropriate for spotting a clear
monotonic trend across 3+ consecutive gaps, not for a precise
per-interval exponent. Needs at least 3 points (2 points give only
one gap, nothing to compare a trend against).
"""
function local_growth_exponents(results::Vector{<:NamedTuple})
    @assert length(results) >= 3 "need at least 3 sweep points to see a LOCAL trend " *
                                  "(2 points give only one gap, nothing to compare against)"

    sorted_results = sort(results; by = r -> r.N)
    local_gammas = Float64[]
    println("\n--- Local (consecutive-pair) growth exponents ---")
    println("N_from\tN_to\tgamma_local\tvs_previous")
    for i in 2:length(sorted_results)
        r1, r2 = sorted_results[i-1], sorted_results[i]
        g = log(r2.ratio / r1.ratio) / log(Float64(r2.N) / Float64(r1.N))
        push!(local_gammas, g)
        trend = if i == 2
            "(first gap)"
        elseif g < local_gammas[end-1]
            "lower"
        elseif g > local_gammas[end-1]
            "higher"
        else
            "same"
        end
        @printf("%d\t%d\t%.4f\t\t%s\n", r1.N, r2.N, g, trend)
    end

    n_lower = count(i -> local_gammas[i] < local_gammas[i-1], 2:length(local_gammas))
    n_gaps_compared = length(local_gammas) - 1
    println()
    if n_gaps_compared == 0
        println("only one gap available -- no trend to report (need 4+ points for a real trend read)")
    elseif n_lower == n_gaps_compared
        println("-> LOCAL gamma is monotonically DECREASING across every gap: consistent with " *
                "washing-out (phase incoherence increasingly cancelling as N/B grows). Still " *
                "only $(length(sorted_results)) points -- more N's would strengthen this.")
    elseif n_lower == 0
        println("-> LOCAL gamma is flat or increasing across every gap: NOT consistent with " *
                "washing-out at the N's tested here -- the global fit's gamma may be close to " *
                "the actual asymptotic rate rather than a transient.")
    else
        println("-> LOCAL gamma is not monotonic ($(n_lower)/$(n_gaps_compared) gaps lower than " *
                "the previous gap) -- no clean trend either way at this N range; could be noise " *
                "from only a few points, or a genuine non-power-law crossover.")
    end

    return (; local_gammas, Ns = [r.N for r in sorted_results])
end

"""
    sweep_multi_seed(; Ns, seeds, m_per_point, m_scaling, m_floor, m_cap)

Runs `sweep()` once per seed in `seeds` (same Ns and m-scaling options
throughout), fits gamma separately for each seed's results via
`fit_growth_exponent`, and reports the spread of fitted gamma across
seeds -- this is the direct answer to "is the single-seed R^2=0.9989
fit a real power law, or a lucky draw from one RNG stream?".

A tight spread (small std relative to the mean) across seeds is real
evidence the fitted gamma reflects the underlying relationship rather
than one seed's noise. A wide spread means the single-seed fit from
before should not be trusted at face value, however good that one
fit's R^2 looked.

Prints a per-seed summary line and the aggregate (mean, std, min, max)
of gamma across seeds. Returns (; per_seed_results, per_seed_gammas,
gamma_mean, gamma_std).

Cost: seeds x (cost of one sweep) -- runs each full sweep sequentially
per seed (the sweep itself is already using all available threads
internally via run_character_sampler_threaded, so seeds are not
further parallelized against each other here to avoid oversubscribing
threads).
"""
function sweep_multi_seed(; Ns::Vector{Int} = [10_007, 100_003, 1_000_003, 10_000_019],
                             seeds::Vector{Int} = collect(1:5),
                             m_per_point::Int = 20_000,
                             m_scaling::Symbol = :sqrt_N,
                             m_floor::Int = 2_000,
                             m_cap::Int = typemax(Int))
    @assert !isempty(seeds) "need at least 1 seed"

    per_seed_results = Vector{Vector{NamedTuple}}(undef, length(seeds))
    per_seed_gammas  = Vector{Float64}(undef, length(seeds))

    for (si, seed) in enumerate(seeds)
        println("\n=== seed $seed ($(si)/$(length(seeds))) ===")
        results = sweep(; Ns, m_per_point, m_scaling, m_floor, m_cap, seed)
        fit = fit_growth_exponent(results)
        # Companion LOCAL check (see local_growth_exponents docstring):
        # the single global fit above cannot distinguish "gamma really
        # is ~0.46 asymptotically" from "gamma is decreasing toward 0
        # as N/B grow but hasn't gotten there yet at these Ns" -- both
        # can produce a high-R^2 global fit over a limited N range.
        # Needs 3+ Ns; skip (not fail the whole sweep) if fewer.
        if length(results) >= 3
            local_growth_exponents(results)
        end
        per_seed_results[si] = results
        per_seed_gammas[si]  = fit.gamma
    end

    n = length(seeds)
    gamma_mean = sum(per_seed_gammas) / n
    gamma_std  = n > 1 ? sqrt(sum((g - gamma_mean)^2 for g in per_seed_gammas) / (n - 1)) : 0.0

    println("\n=== Multi-seed summary: gamma across $(n) seed(s) ===")
    println("seed\tgamma")
    for (seed, g) in zip(seeds, per_seed_gammas)
        @printf("%d\t%.4f\n", seed, g)
    end
    @printf("\nmean(gamma) = %.4f\n", gamma_mean)
    if n > 1
        @printf("std(gamma)  = %.4f\n", gamma_std)
        @printf("min/max     = %.4f / %.4f\n", minimum(per_seed_gammas), maximum(per_seed_gammas))
        rel_spread = gamma_std / abs(gamma_mean)
        if rel_spread < 0.15
            println("-> tight spread relative to the mean: the single-seed fit is likely reflecting", 
                    " a real relationship, not seed noise.")
        else
            println("-> wide spread relative to the mean: do not trust a single-seed gamma at face", 
                    " value -- consider more seeds and/or more Ns before drawing conclusions.")
        end
    else
        @warn "only 1 seed -- this reports a point estimate of gamma with no spread information; " *
              "pass seeds = collect(1:K) for K > 1 to actually check stability across seeds."
    end

    return (; per_seed_results, per_seed_gammas, gamma_mean, gamma_std)
end

if abspath(PROGRAM_FILE) == @__FILE__
    # Default: multi-seed sweep across 5 seeds to check whether the
    # fitted growth exponent gamma is stable (real signal) or seed-
    # dependent (noise dressed up as a tight single-seed R^2). Each
    # seed runs the same 4-point N sweep with B ~ N^0.4 and m growing
    # like sqrt(N) (see m_scaling docstring above). Increase
    # m_per_point for tighter per-point error bars; increase `seeds`
    # for a tighter estimate of gamma's spread (more seeds = more
    # confidence the mean gamma is real, at the cost of proportionally
    # more runtime since seeds run sequentially).
    sweep_multi_seed()
end
