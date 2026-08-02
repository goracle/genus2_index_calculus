# ---------------------------------------------------------------
# Strategy 7: pair-sum energy local search (exact O(B)-per-swap,
# targets M4, used as a cheap proxy for M8)
# ---------------------------------------------------------------
#
# HISTORY: this replaces an earlier version of Strategy 7 that scored
# swaps via a linearized gradient of sum_chi |S_chi|^8 restricted to a
# frozen set of "bad" Fourier modes (spectral_swap_search). That
# version was measured to make the FULL-spectrum ratio (as estimated
# by the character sampler) WORSE in 2 of 3 tested N's, and stall
# (zero accepted swaps) at the third -- a real negative result, not a
# noise artifact (see the run that prompted this rewrite), traced to
# two compounding problems: (1) optimizing a small frozen mode subset
# has no guarantee of transferring to the full spectrum -- a swap can
# cleanly improve the ~B modes being watched while making the other
# ~N-B modes worse, and the character sampler measures ALL of them;
# (2) the linearization itself assumes |chi(y)-chi(x)| is small
# relative to |S_chi|, which is not generally true when |S_chi| is
# itself only O(sqrt(B))-ish. Both issues were real, not
# implementation bugs -- the surrogate objective was the problem.
#
# EXTERNAL PROPOSAL (paraphrased, in response to that result): rather
# than optimizing Fourier coefficients via a linearized surrogate,
# work directly in physical space with the pair-sum multiplicity
# function r(t) = #{(a,b) in FxF : a+b = t mod N} (an ordered-pair
# count, i.e. the additive convolution 1_F * 1_F). A swap changes r at
# only O(B) points (the pair-sums involving the swapped element), so
# any energy functional of r that can be updated incrementally from
# those O(B) changed entries admits an EXACT, no-linearization,
# O(B)-per-swap local search -- "no surrogate, no frozen Omega, no
# linearization, no worrying about missing frequencies."
#
# CORRECTION TO THE PROPOSAL'S STATED IDENTITY (verified numerically,
# both symbolically and by direct computation on random test sets --
# see chat): the proposal describes the 8th moment as "literally the
# 4th moment of the pair-sum distribution", i.e. sum_t r(t)^4. That is
# NOT the correct identity. What IS exactly true (standard Parseval on
# Z/N, verified numerically to floating-point precision across many
# random F): sum_t r(t)^2 = (1/N) * sum_chi |S_chi|^4 -- this is
# exactly M4 (already tracked elsewhere in this file), not M8, and IS
# updatable in O(B) per swap (r changes at O(B) points, and
# sum(v^2)-style energies update purely from the changed entries with
# no cross-terms beyond those entries -- verified against brute-force
# recomputation across 200 random trials, see chat).
#
# The TRUE exact identity for M8 involves q = r (*) r (the
# AUTOCORRELATION of r, not r^4 pointwise): sum_chi |S_chi|^8 =
# N * sum_t q(t)^2 (also verified numerically to floating-point
# precision). But autocorrelation is a global operation -- changing
# r at O(B) points was checked to change q at very close to ALL N
# points (957 of 1009 in one concrete test), because convolution
# smears a local change across the whole transform. So the true
# M8-exact quantity does NOT admit an O(B)-per-swap update; it costs
# O(N) per swap to recompute q from scratch. That defeats the "cheap
# exact O(B^2) budget" premise of the proposal at the M8 level
# specifically.
#
# WHAT'S IMPLEMENTED HERE, GIVEN THAT: minimize sum_t r(t)^2 (= M4,
# exactly, not a proxy for M4 -- an exact equality) via genuine
# O(B)-per-swap incremental local search, used as an UNTESTED PROXY
# for improving M8 (there is no theorem here, and no claim that
# minimizing M4 necessarily improves M8 -- lower M4 is at best
# correlated with lower M8 in the way "less concentrated pairwise
# sums" is intuitively related to "less concentrated 4-fold sums", but
# this is exactly the kind of claim that needs to be MEASURED, not
# assumed, same discipline as every other strategy in this file).
# What this construction DOES buy over the discarded spectral version:
# a genuinely exact, cheap (O(B) per swap), no-approximation objective
# -- so if it fails to improve M8, that failure isn't attributable to
# a linearization error or a frozen-subset blind spot the way the
# previous version's failure was. It would be a cleaner negative (or
# positive) result either way.

"""
    pairsum_energy(F::Vector{Int}, N::Int) -> (r::Dict{Int,Int}, E::Int)

Builds the pair-sum multiplicity dict r(t) = #{(a,b) in FxF : a+b = t
mod N} (ordered pairs, so r(2a) counts the single (a,a) self-pair once
and r(a+b) for a != b counts both (a,b) and (b,a)) from scratch, and
returns it alongside E = sum_t r(t)^2 -- exactly N times M4/N, i.e.
exactly equal to sum_chi |S_chi|^4 / N (verified numerically; see
Strategy 7 header comment). Only nonzero entries are stored (a sparse
Dict, not a dense length-N array), since at most O(B^2) entries of r
are ever nonzero.

O(B^2) cost -- called once per swap-search call (to build the initial
r from the seed F), not once per step (steps update incrementally via
pairsum_remove!/pairsum_add! below).
"""
function pairsum_energy(F::Vector{Int}, N::Int)
    r = Dict{Int,Int}()
    for a in F, b in F
        t = mod(a + b, N)
        r[t] = get(r, t, 0) + 1
    end
    E = sum(v^2 for v in values(r))
    return (r, E)
end

"""
    pairsum_bump!(r, t, delta) -> ΔE

Adds `delta` to r[t] (removing the key if it hits exactly 0, to keep r
sparse), returning the resulting change in sum_t r(t)^2 caused by THIS
single bump (new^2 - old^2). This is the atomic operation both
pairsum_remove! and pairsum_add! are built from.
"""
function pairsum_bump!(r::Dict{Int,Int}, t::Int, delta::Int)
    old = get(r, t, 0)
    new = old + delta
    dE = new^2 - old^2
    if new == 0
        delete!(r, t)
    else
        r[t] = new
    end
    return dE
end

"""
    pairsum_remove!(r, x, F_current, N) -> ΔE

Removes ALL ordered-pair contributions of `x` from `r`, given
`F_current` (the current F, which must still CONTAIN x when this is
called -- call this BEFORE actually removing x from your F array).
For every other f in F_current (f != x), BOTH ordered pairs (x,f) and
(f,x) map to the same t = x+f mod N and are each removed separately
(they are two distinct entries in the ordered-pair count, even though
they share a t) -- getting this double-removal right (rather than
removing only one of the two) was verified against brute-force
recomputation across 200 random trials (see Strategy 7 header
comment); the single self-pair (x,x) is removed once, not twice.
Returns the total energy change (sum of every pairsum_bump! call's
contribution).
"""
function pairsum_remove!(r::Dict{Int,Int}, x::Int, F_current::Vector{Int}, N::Int)
    dE = 0
    for f in F_current
        if f == x
            dE += pairsum_bump!(r, mod(2x, N), -1)
        else
            dE += pairsum_bump!(r, mod(x + f, N), -1)
            dE += pairsum_bump!(r, mod(f + x, N), -1)
        end
    end
    return dE
end

"""
    pairsum_add!(r, y, F_after, N) -> ΔE

Adds ALL ordered-pair contributions of `y` to `r`, given `F_after`
(F with x already logically removed, and NOT yet containing y --
i.e. the "in-between" state after pairsum_remove! but before y is
appended to your F array). Mirrors pairsum_remove! exactly (same
double-count-for-f!=x, single-count-for-self-pair structure, just
adding instead of subtracting). Returns the total energy change.
"""
function pairsum_add!(r::Dict{Int,Int}, y::Int, F_after::Vector{Int}, N::Int)
    dE = 0
    for f in F_after
        dE += pairsum_bump!(r, mod(y + f, N), +1)
        dE += pairsum_bump!(r, mod(f + y, N), +1)
    end
    dE += pairsum_bump!(r, mod(2y, N), +1)
    return dE
end

"""
    pairsum_swap_search(F_int, N; pool_size, rng, method=:greedy,
                          max_steps=200, anneal_T0=1.0, anneal_cooling=0.98)

Local search over Sidon-preserving swaps of `F_int` (assumed already
Sidon on entry -- not checked at entry), scored by the EXACT change in
sum_t r(t)^2 (= M4, exactly -- see pairsum_energy) under each proposed
swap, maintained incrementally via pairsum_remove!/pairsum_add! rather
than recomputed from scratch each time -- genuinely O(B) per swap
evaluated, not O(B^2) and not a linearized approximation of anything.

Candidate pool: a fixed random Theta(B) set of elements not in F_int,
sampled once at the start (same convention as the discarded spectral
version, and same caveat: not refreshed mid-search).

method=:greedy -- scans every (x in F, y in pool) pair each step (an
O(B * pool_size) scan, each pair scored in O(B) via a TRIAL bump/undo
against a COPY of the current r -- see implementation note below on
why a copy is used rather than true in-place trial), takes the single
most-negative-dE Sidon-preserving swap, commits it (mutating the real
r), and repeats. Stops early if no improving Sidon-preserving swap is
found. method=:anneal -- draws one random (x,y) pair per step,
Metropolis-accepts based on the exact dE (same acceptance rule as the
discarded spectral version), and only commits/mutates r if the
resulting F is Sidon (a rejected proposal is a wasted step, same
accepted tradeoff as before -- see chat).

IMPLEMENTATION NOTE ON COST: scoring a single candidate swap exactly
costs O(B) (apply pairsum_remove!+pairsum_add! to a trial copy of r,
read off the total dE, discard the copy) -- copying a Dict of size
O(B^2) (worst case, though typically much sparser for a Sidon set) on
every one of the O(B*pool_size) candidate evaluations in a greedy step
means the ACTUAL per-step cost is more like O(B * pool_size * B) in
the worst case if r is dense, not the idealized O(B*pool_size). This
is addressed by NOT copying r at all: instead, each candidate is
scored by applying pairsum_remove!/pairsum_add! directly to the LIVE
r, reading off dE, and then UNDOING the exact same bumps (which is
exact and cheap since pairsum_bump! is its own exact inverse under
negated delta) if the candidate is not the one taken. This keeps each
candidate evaluation at genuine O(B) regardless of how large r's
current support is.

Returns (F_final::Vector{Int}, n_accepted::Int, n_tried::Int,
history::Vector{Int}) where history[i] is the EXACT (not sampled,
not linearized) sum_t r(t)^2 after step i.
"""
function pairsum_swap_search(F_int::Vector{Int}, N::Int;
                                pool_size::Int,
                                rng::AbstractRNG,
                                method::Symbol = :greedy,
                                max_steps::Int = 200,
                                anneal_T0::Float64 = 1.0,
                                anneal_cooling::Float64 = 0.98)
    @assert method in (:greedy, :anneal) "method must be :greedy or :anneal, got $method"

    F = copy(F_int)
    Fset = Set(F)
    r, E = pairsum_energy(F, N)

    pool_candidates = Int[]
    attempts = 0
    while length(pool_candidates) < pool_size && attempts < 20 * pool_size + N
        z = rand(rng, 0:(N-1))
        attempts += 1
        if !(z in Fset) && !(z in pool_candidates)
            push!(pool_candidates, z)
        end
    end
    if length(pool_candidates) < pool_size
        @warn "pairsum_swap_search: could only build a pool of $(length(pool_candidates)) " *
              "(wanted $pool_size) after exhausting the attempt budget -- proceeding with " *
              "the smaller pool rather than looping indefinitely"
    end

    n_accepted = 0
    n_tried = 0
    history = Int[]
    T = anneal_T0

    # Scores one candidate swap (x -> y) EXACTLY, in O(B), by applying
    # the bumps to the LIVE r, reading dE, then undoing them (exact
    # inverse: re-applying the same bump sequence with negated deltas
    # restores r to byte-for-byte the same state, since pairsum_bump!
    # is a pure function of (old value, delta) -> new value with no
    # hidden state). Does NOT mutate F -- only r, and only transiently.
    function score_swap(x::Int, y::Int)
        F_without_x = filter(!=(x), F)
        dE = pairsum_remove!(r, x, F, N)
        dE += pairsum_add!(r, y, F_without_x, N)
        # Undo: remove y's just-added contributions, re-add x's.
        pairsum_remove!(r, y, vcat(F_without_x, [y]), N)
        pairsum_add!(r, x, F_without_x, N)
        return dE
    end

    for step in 1:max_steps
        push!(history, E)

        if method == :greedy
            best_dE = 0
            best_swap = nothing
            for x in F
                for y in pool_candidates
                    n_tried += 1
                    dE = score_swap(x, y)
                    dE >= best_dE && continue
                    F_trial = copy(F)
                    idx = findfirst(==(x), F_trial)
                    F_trial[idx] = y
                    if sidon_defect(F_trial, N) == 0
                        best_dE = dE
                        best_swap = (x, y)
                    end
                end
            end
            if best_swap === nothing
                break
            end
            x, y = best_swap
            F_without_x = filter(!=(x), F)
            actual_dE = pairsum_remove!(r, x, F, N)
            actual_dE += pairsum_add!(r, y, F_without_x, N)
            @assert actual_dE == best_dE "pairsum energy bookkeeping mismatch: " *
                "committed dE=$actual_dE != scored dE=$best_dE -- indicates a bug " *
                "in score_swap's trial-and-undo symmetry, investigate before trusting " *
                "any result from this search"
            E += actual_dE
            idx = findfirst(==(x), F)
            F[idx] = y
            delete!(Fset, x)
            push!(Fset, y)
            filter!(!=(y), pool_candidates)
            push!(pool_candidates, x)
            n_accepted += 1

        else  # :anneal
            x = rand(rng, F)
            y = rand(rng, pool_candidates)
            n_tried += 1
            dE = score_swap(x, y)
            accept = if dE <= 0
                true
            else
                rand(rng) < exp(-dE / max(T, 1e-12))
            end
            if accept
                F_trial = copy(F)
                idx = findfirst(==(x), F_trial)
                F_trial[idx] = y
                if sidon_defect(F_trial, N) == 0
                    F_without_x = filter(!=(x), F)
                    actual_dE = pairsum_remove!(r, x, F, N)
                    actual_dE += pairsum_add!(r, y, F_without_x, N)
                    E += actual_dE
                    F[idx] = y
                    delete!(Fset, x)
                    push!(Fset, y)
                    filter!(!=(y), pool_candidates)
                    push!(pool_candidates, x)
                    n_accepted += 1
                end
            end
            T *= anneal_cooling
        end
    end

    return (F, n_accepted, n_tried, history)
end

# ---------------------------------------------------------------
# run_pairsum_swap_comparison: seeds via greedy_sidon_subset, refines
# via pairsum_swap_search, measures with the usual character sampler
# -- INCLUDING MULTIPLE INDEPENDENT SAMPLER SEEDS PER (N, before/after)
# SO THE BEFORE/AFTER COMPARISON HAS A VISIBLE NOISE FLOOR.
# ---------------------------------------------------------------
#
# WHY MULTIPLE SAMPLER SEEDS: the discarded spectral-swap version
# reported single-seed before/after ratios (e.g. 563 -> 599) with no
# indication of whether that gap was outside Monte Carlo noise --
# flagged directly as a gap by the external review. Fixed here by
# running run_character_sampler_threaded n_sampler_seeds times (with
# DIFFERENT seeds) for both the before-refinement and after-refinement
# F, and reporting mean +/- standard error for each, so a reader can
# see directly whether "after" is outside "before"'s noise band rather
# than having to trust a single point estimate.

"""
    run_pairsum_swap_comparison(; Ns, m_per_point, m_scaling, m_floor,
                                   m_cap, seed, method, pool_size_factor,
                                   max_steps, n_sampler_seeds)

Same overall shape as the discarded run_spectral_swap_comparison, but:
  - refines via pairsum_swap_search (exact M4 minimization) instead of
    the linearized spectral surrogate;
  - runs `n_sampler_seeds` INDEPENDENT character-sampler measurements
    (different seeds) for both the greedy seed (before) and the
    refined F (after), reporting mean and standard error of the ratio
    for each, so the before/after comparison carries a visible
    confidence interval instead of a single noisy point estimate.

Also reports the EXACT M4 energy (from pairsum_swap_search's history)
before and after refinement -- this is not sampled/noisy at all (it's
computed exactly), so it directly confirms whether the local search
achieved what it was actually optimizing (M4 should only ever
decrease or stay flat under :greedy; may fluctuate under :anneal),
independent of whether that translates into a lower M8 ratio.
"""
function run_pairsum_swap_comparison(; Ns::Vector{Int} = [10_007, 100_003, 1_000_003, 10_000_019],
                                        m_per_point::Int = 20_000,
                                        m_scaling::Symbol = :sqrt_N,
                                        m_floor::Int = 2_000,
                                        m_cap::Int = typemax(Int),
                                        seed::Int = 1,
                                        method::Symbol = :greedy,
                                        pool_size_factor::Float64 = 1.0,
                                        max_steps::Int = 200,
                                        n_sampler_seeds::Int = 5)
    N0 = Float64(first(Ns))
    results = NamedTuple[]

    println("\n=== Pair-sum energy local search (method=$method), seed=greedy_sidon_subset, " *
            "$n_sampler_seeds independent sampler seeds per point ===")
    println("N\tB\tm\tM4_before(exact)\tM4_after(exact)\t" *
            "ratio_before(mean±se)\tratio_after(mean±se)\tn_accepted\tn_tried\tdefect_after\telapsed_s")
    for N in Ns
        B = round(Int, N^0.4)
        build_rng = MersenneTwister(seed)
        F_seed = greedy_sidon_subset(N, B, build_rng)
        @assert length(F_seed) == B "greedy seed returned |F|=$(length(F_seed)), expected B=$B"
        @assert sidon_defect(F_seed, N) == 0 "greedy seed is not Sidon -- cannot proceed"

        _, M4_before_exact = pairsum_energy(F_seed, N)

        pool_sz = max(1, round(Int, pool_size_factor * B))

        t0 = time()
        F_final, n_accepted, n_tried, history = pairsum_swap_search(
            F_seed, N; pool_size = pool_sz, rng = build_rng, method = method, max_steps = max_steps)
        search_elapsed = time() - t0

        M4_after_exact = isempty(history) ? M4_before_exact : history[end]
        defect_after = sidon_defect(F_final, N)
        if defect_after != 0
            @warn "N=$N: refined F has nonzero sidon_defect=$defect_after -- " *
                  "this should be impossible (pairsum_swap_search only accepts " *
                  "Sidon-preserving swaps); investigate before trusting this row"
        end

        m_target = if m_scaling == :fixed
            m_per_point
        elseif m_scaling == :sqrt_N
            round(Int, m_per_point * sqrt(N / N0))
        elseif m_scaling == :linear_N
            round(Int, m_per_point * (N / N0))
        else
            error("unknown m_scaling = $m_scaling")
        end
        m = clamp(m_target, m_floor, min(m_cap, N - 1))

        Bf = Float64(B)
        flat = (Bf^8) / N

        F_before_wrapped = [[x] for x in F_seed]
        F_after_wrapped = [[x] for x in F_final]

        ratios_before = Float64[]
        ratios_after = Float64[]
        for s in 1:n_sampler_seeds
            sampler_seed = seed * 1_000_003 + s   # distinct, deterministic per (seed, s)
            res_b = run_character_sampler_threaded(G_for(N), F_before_wrapped; m = m,
                                                      seed = sampler_seed, k_size = N,
                                                      report_every = typemax(Int))
            push!(ratios_before, res_b.M8_running[end] / flat)
            res_a = run_character_sampler_threaded(G_for(N), F_after_wrapped; m = m,
                                                      seed = sampler_seed, k_size = N,
                                                      report_every = typemax(Int))
            push!(ratios_after, res_a.M8_running[end] / flat)
        end

        mean_before = mean(ratios_before)
        mean_after = mean(ratios_after)
        se_before = n_sampler_seeds > 1 ? std(ratios_before) / sqrt(n_sampler_seeds) : NaN
        se_after = n_sampler_seeds > 1 ? std(ratios_after) / sqrt(n_sampler_seeds) : NaN

        elapsed = time() - t0

        @printf("%d\t%d\t%d\t%d\t\t\t%d\t\t\t%.4f±%.4f\t%.4f±%.4f\t%d\t\t%d\t%d\t\t%.2f\n",
                N, B, m, M4_before_exact, M4_after_exact,
                mean_before, se_before, mean_after, se_after,
                n_accepted, n_tried, defect_after, elapsed)

        push!(results, (; N, B, m, M4_before_exact, M4_after_exact,
                           mean_before, se_before, mean_after, se_after,
                           ratios_before, ratios_after,
                           n_accepted, n_tried, defect_after, elapsed))
    end

    println("\n--- Significance check: is (after - before) outside a 2-standard-error band? ---")
    println("N\tmean_after - mean_before\tcombined_2se\toutside_2se_band?")
    for r in results
        diff = r.mean_after - r.mean_before
        combined_2se = 2 * sqrt(r.se_before^2 + r.se_after^2)
        outside = !isnan(combined_2se) && abs(diff) > combined_2se
        @printf("%d\t%.4f\t\t\t\t%.4f\t\t%s\n", r.N, diff, combined_2se,
                outside ? "YES (likely real)" : "no (within noise)")
    end
    if n_sampler_seeds < 3
        @warn "n_sampler_seeds=$n_sampler_seeds is too few for the standard-error " *
              "estimates above to be trustworthy themselves -- use at least 5-10 " *
              "for a meaningful noise-floor check, this default/call used fewer"
    end

    if length(results) >= 2
        println("\n--- Pair-sum-refined growth-exponent fit (AFTER refinement, mean ratio vs real N) ---")
        fit_rows = [(; N = r.N, B = r.B, m = r.m, ratio = r.mean_after,
                       maxU = 0.0, defect = r.defect_after, elapsed = r.elapsed)
                    for r in results]
        fit = fit_growth_exponent(fit_rows)
        println("\n--- For comparison, UNREFINED greedy-seed fit (BEFORE refinement, mean ratio) ---")
        fit_rows_before = [(; N = r.N, B = r.B, m = r.m, ratio = r.mean_before,
                              maxU = 0.0, defect = 0, elapsed = r.elapsed)
                           for r in results]
        fit_before = fit_growth_exponent(fit_rows_before)
        return (; results, fit, fit_before)
    end

    return (; results, fit = nothing, fit_before = nothing)
end

