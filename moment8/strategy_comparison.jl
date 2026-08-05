#!/usr/bin/env julia
#
# strategy_comparison.jl
#
# Compares candidate factor-base CONSTRUCTION STRATEGIES against a
# shared 8th-moment objective (the character-sampler ratio and its
# fitted N-scaling exponent), rather than treating F as fixed and
# unknown.
#
# WHY THIS EXISTS
# ----------------
# The advisory doc (section 7.6) proves that no O(B^2)-cost SELECTION
# RULE can *certify* good 8th-moment / U^3-level behavior from cheap
# pairwise-sum data alone -- that data only ever pins down the 4th
# moment (U^2 level). But it does NOT say every valid Sidon F has the
# SAME 8th moment: two different B-element Sidon subsets of the same
# Z/N can behave very differently at the 8th-moment level, and nothing
# stops you from constructing F to empirically test well, even without
# a certificate that it will. Character sampling (character_sampler.jl
# / character_sampler_threaded.jl) gives a cheap, honest empirical
# readout of where a *specific* candidate F sits on the flat-to-
# worst-case spectrum -- so it can be used as an objective function to
# COMPARE candidate construction strategies, even though it can't
# prove any one of them is good in general.
#
# All strategies here produce genuine Sidon subsets of the SAME group
# Z/N (matching your confirmed real-subgroup isomorphism), verified by
# the existing sidon_defect check before anything else runs. The
# comparison is apples-to-apples: same N, same B, same character
# samples (same seed) per (N, strategy) pair, so any difference in the
# ratio is attributable to the strategy, not to sampling noise.
#
# STRATEGIES INCLUDED
# --------------------
#   :greedy   -- the original baseline (random order, greedy rejection
#                for the Sidon property). No structure beyond Sidon-
#                ness itself; this is the "generic" reference point
#                from the earlier sweep (gamma ~ 0.46).
#
#   :quadratic_residues -- REMOVED (see note near its old location
#                below) -- an earlier version of this file claimed
#                squares mod prime N form a Sidon set. That is FALSE
#                (checked directly: badly non-Sidon), so the strategy
#                was pulled rather than left in with wrong results.
#
#   :greedy_low_energy -- a GREEDY-WITH-A-TIEBREAK variant: among
#                Sidon-valid candidates at each step, prefer the one
#                that adds the least to a running *approximate* 4-fold
#                energy proxy (cheap to compute incrementally), rather
#                than accepting candidates in random order. This is a
#                legitimate O(B^2)-ish selection heuristic in the
#                spirit of section 7.6's "relaxed budget" -- it cannot
#                be PROVEN to help at the 8th-moment level (per
#                Shkredov's dichotomy), but nothing stops you from
#                trying it and just measuring the result.
#
# Add more strategies by writing a function with signature
# (N::Int, target_size::Int, rng::AbstractRNG) -> Vector{Int} and
# registering it in STRATEGIES below.

using Random
using Printf
using Statistics
using Base.Threads: nthreads   # Threads.@spawn used fully-qualified in projected_greedy_sidon_subset's batch-scoring loop below

include("character_sampler.jl")
include("scaling_sweep.jl")   # for fit_growth_exponent, reused here per-strategy

# ---------------------------------------------------------------
# Strategy 1: greedy (baseline, already defined in
# character_sampler_threaded.jl as greedy_sidon_subset)
# ---------------------------------------------------------------

# ---------------------------------------------------------------
# Strategy 2 was originally "quadratic residues" (squares mod prime
# N as a classical algebraic Sidon set) -- REMOVED. That was a
# factual error: squares mod p are NOT an additively Sidon set (this
# was checked directly: for N=101, the multiplicity of a single
# difference value reaches 25 -- nowhere near Sidon). The genuine
# classical algebraic constructions (Singer difference sets, which
# need N = q^2+q+1 for a prime power q; certain Erdos-Turan
# constructions embedded in Z rather than Z/N) have real number-
# theoretic prerequisites that don't line up with an arbitrary prime
# sweep, so a correct version of "structured algebraic Sidon set" is
# left for a future pass rather than shipped half-right. If you want
# this comparison point, the Singer construction constrained to
# N = q^2+q+1 is the right thing to implement next, not a quick patch
# of the above.

# ---------------------------------------------------------------
# Strategy 3: greedy with a cheap low-energy tiebreak
# ---------------------------------------------------------------

"""
    greedy_low_energy_sidon_subset(N, target_size, rng; lookahead=6, max_restarts=20)

Greedy Sidon construction (same rejection rule as greedy_sidon_subset)
but, at each step, instead of taking the FIRST valid candidate from a
single random order, examines `lookahead` candidates and accepts
whichever one adds the fewest NEW pairwise sums that are "close to"
already-dense regions of the sum-set (a cheap incremental proxy for
avoiding sum-set clumping, computed from data already being tracked
for the Sidon check -- no extra O(B^2) cost beyond what greedy
already pays).

This is NOT a proven 8th-moment-improving construction -- per section
7.6, no O(B^2)-cost rule can be proven to control the 8th moment.
It's a legitimate, cheap thing to TRY and then measure, which is
exactly what this comparison script is for.

IMPORTANT (fixed after an earlier bug): this ALWAYS runs over the
full candidate range 0:(N-1), same as greedy_sidon_subset, rather
than a size-limited pool -- an earlier version capped the pool at
pool_factor*target_size and could silently return FEWER than
target_size elements once that bounded pool was exhausted (observed
directly: |F|=32 instead of 40, |F|=362 instead of 631, etc., which
badly corrupted the strategy comparison since the flat-value
normalizer B^8/N is highly sensitive to B). This version raises an
error instead of ever silently returning a short result, so a size
mismatch is caught immediately rather than producing a misleading
ratio.

RESTART LOGIC (added after observing a real exhaustion at N=10000019,
target_size=631: the single-pass greedy stalled at 603/631 elements
after scanning the full N candidates). This was diagnosed as a
search-order artifact, not a fundamental existence bound -- plain
greedy_sidon_subset (no lookahead/tiebreak) succeeded at the exact
same (N, target_size), so a Sidon set of that size does exist; the
low-energy tiebreak's density-minimizing bias can occasionally walk
itself into a corner where all remaining unused candidates collide
with the accumulated sum-set, before target_size is reached. Rather
than fail on the first stall, this version reshuffles the candidate
order and restarts from scratch (fresh `elems`/`sums_seen`/
`sum_density`) up to `max_restarts` times, and only raises if every
attempt fails -- at which point it really is more likely to reflect
a genuine capacity issue (or a lookahead value pathologically prone
to self-trapping) rather than one unlucky shuffle.

THREADING (added after observing a real multi-minute silent hang at
N=10000019: restarts are independent, each doing a full O(N) attempt,
and none of that was parallelized -- 20 sequential O(N)=10^7 scans
with zero progress output in between is indistinguishable from a
hang. Restarts are embarrassingly parallel (different shuffles,
disjoint local state), so this version follows the same pattern
already used in character_sampler.jl's run_character_sampler:
STATIC pre-split of the `max_restarts` attempts across
`Threads.nthreads()` tasks via `Threads.@spawn`, each task closing
over its own local RNG -- never indexing anything by `threadid()`,
since that is unsafe under Julia's >=1.9 dynamic scheduler (see
character_sampler.jl's comments for why). Attempts run in
`ceil(max_restarts/nthreads())` waves; within a wave all tasks race
and the first successful result found (by wave, then by task index
for determinism) is returned. A heartbeat prints every
`progress_every` seconds from a lightweight polling loop so a long
attempt shows up as visible progress rather than silence, and a
per-attempt candidate-scan counter (via `Threads.Atomic{Int}`, safe
to share/increment across tasks unlike threadid()-indexed arrays)
backs that heartbeat. Worst-case cost is still O(max_restarts * N)
total work, but wall-clock is divided by nthreads() (rounded up to
whole waves), and now a stall-in-progress is visible instead of
silent.
"""
function greedy_low_energy_sidon_subset(N::Int, target_size::Int, rng::AbstractRNG;
                                          lookahead::Int = 6, max_restarts::Int = 20,
                                          progress_every::Real = 5.0)

    # One independent attempt. Never touches shared state except its
    # own `scanned` counter (for the heartbeat) -- everything else
    # (elems, sums_seen, sum_density, candidates, rng_local) is local
    # to this call/task, so N attempts can run concurrently with no
    # locking needed.
    function one_attempt(rng_local::AbstractRNG, scanned::Threads.Atomic{Int})
        elems = Int[]
        sums_seen = Set{Int}()
        sum_density = Dict{Int,Int}()

        candidates = collect(0:(N-1))
        Random.shuffle!(rng_local, candidates)
        ci = 1

        while length(elems) < target_size && ci <= length(candidates)
            valid_batch = Tuple{Int,Vector{Int},Int}[]
            scan = ci
            while length(valid_batch) < lookahead && scan <= length(candidates)
                x = candidates[scan]
                ok = true
                new_sums = Int[]
                for y in elems
                    s = mod(x + y, N)
                    if s in sums_seen
                        ok = false
                        break
                    end
                    push!(new_sums, s)
                end
                if ok
                    s2 = mod(2x, N)
                    (s2 in sums_seen) && (ok = false)
                end
                if ok
                    push!(new_sums, mod(2x, N))
                    score = sum(get(sum_density, s, 0) for s in new_sums)
                    push!(valid_batch, (x, new_sums, score))
                end
                scan += 1
                Threads.atomic_add!(scanned, 1)
            end

            if isempty(valid_batch)
                ci = scan
                continue
            end

            best = argmin(t -> t[3], valid_batch)
            push!(elems, best[1])
            for s in best[2]
                union!(sums_seen, (s,))
                sum_density[s] = get(sum_density, s, 0) + 1
            end
            ci = scan
        end

        return elems
    end

    nt = Threads.nthreads()
    if nt == 1
        @warn "nthreads() == 1 -- Julia was not started with multiple threads. " *
              "Run with `julia -t auto` or `julia -t N` (N>1) to actually run " *
              "restart attempts concurrently; this script cannot create OS " *
              "threads Julia wasn't started with, so restarts will run one at " *
              "a time regardless of `max_restarts`."
    end

    n_waves = cld(max_restarts, nt)
    attempt_number = 0

    for wave in 1:n_waves
        wave_size = min(nt, max_restarts - attempt_number)

        # Fresh atomic scan counters per task this wave, for the heartbeat.
        scanned_counters = [Threads.Atomic{Int}(0) for _ in 1:wave_size]
        results = Vector{Union{Nothing,Vector{Int}}}(undef, wave_size)

        tasks = Vector{Task}(undef, wave_size)
        for w in 1:wave_size
            a = attempt_number + w
            # RNG local to this task/closure, seeded off the caller's
            # rng so runs are reproducible given the caller's seed --
            # never derived from threadid().
            rng_local = MersenneTwister(rand(rng, UInt) ⊻ (0x9E3779B9 * UInt(a)))
            sc = scanned_counters[w]
            tasks[w] = Threads.@spawn begin
                results[w] = one_attempt(rng_local, sc)
            end
        end

        # Lightweight heartbeat: poll the atomics rather than blocking
        # silently on `wait`, so a long wave shows visible progress.
        start_t = time()
        last_report = start_t
        while any(!istaskdone(t) for t in tasks)
            sleep(0.2)
            now_t = time()
            if now_t - last_report >= progress_every
                total_scanned = sum(c[] for c in scanned_counters)
                elapsed = round(now_t - start_t, digits=1)
                println("  ... greedy_low_energy restart wave $wave/$n_waves " *
                        "($wave_size attempt(s) in flight, N=$N, target_size=$target_size): " *
                        "$(total_scanned) total candidates scanned across the wave " *
                        "so far, $(elapsed)s elapsed")
                last_report = now_t
            end
        end
        foreach(wait, tasks)

        # Take the first successful attempt in this wave, by task index,
        # for determinism given a fixed seed and thread count.
        for w in 1:wave_size
            elems = results[w]
            if elems !== nothing && length(elems) >= target_size
                a = attempt_number + w
                if a > 1
                    @warn "greedy_low_energy_sidon_subset: needed $a attempt(s) " *
                          "(N=$N, target_size=$target_size) -- earlier attempt(s) stalled " *
                          "short of target_size before exhausting candidates; this is a " *
                          "known search-order artifact of the low-energy tiebreak, not an " *
                          "existence issue (see docstring)"
                end
                return elems
            end
        end

        attempt_number += wave_size
    end

    error("greedy_low_energy_sidon_subset: failed to reach target_size=$target_size " *
          "at N=$N after $max_restarts restarts (each exhausting all $N candidates). " *
          "Plain greedy_sidon_subset succeeding at the same (N, target_size) would " *
          "indicate this is still a search-order issue, not a genuine capacity limit -- " *
          "try a larger max_restarts or lookahead before concluding no such Sidon set " *
          "exists.")
end

# ---------------------------------------------------------------
# Strategy 3.5: greedy with an incremental sampled-R(t)-variance
# tiebreak (O(B^2)-budget version of new_invariants.jl's proposal 5)
# ---------------------------------------------------------------
#
# WHY THIS EXISTS / WHERE IT CAME FROM
# -------------------------------------
# new_invariants.jl's sampled_R_variance_score is a RETROACTIVE scorer
# only: its own docstring shows that tracking L=Theta(B^2) shifts live
# through a greedy run costs O(B^3) per swap (O(B) work per shift,
# times O(B^2) shifts), which blows the O(B^2) budget. The retroactive
# correlation check (run_retroactive_correlation_check, run against
# real greedy vs. embedded-Singer@0.2 data) showed this score DOES
# separate the known-good (greedy, gamma~0.46) construction from the
# known-bad one (Singer@0.2, gamma~1.57) in the right direction, so it
# is worth trying to recover an O(B^2)-compatible LIVE version rather
# than only ever using it after the fact.
#
# THE FIX: shrink L from Theta(B^2) to Theta(B) (a FIXED set of shifts
# drawn ONCE at the start of the run, not redrawn per swap -- fixing
# the shifts is also more principled for a tiebreak, since it scores
# every candidate at a given step against the SAME shift set, the same
# way compare_strategies fixes one character-sampler seed across
# strategies rather than re-seeding per comparison). With L=Theta(B),
# incremental cost per swap becomes O(B) [delta list size] * O(B)
# [tracked shifts] = O(B^2), inside budget. This is a real reduction
# in the ESTIMATE's precision (standard error ~ 1/sqrt(L), so
# Theta(B) samples of R(t) is nosier than the Theta(B^2)/L_cap=20000
# used in the retroactive check) -- offered as a legitimate O(B^2)
# heuristic to TRY and measure, per section 7.6, not as a claim that
# it recovers the retroactive score's precision.
#
# INCREMENTAL UPDATE (derived and numerically verified against a
# direct O(B^2) rebuild before writing this -- see chat derivation):
# on a swap (remove x, add x', from candidate set F to F' = F\{x} u {x'}),
# the sumset histogram r(u) = #{(a,b) in F^2 : a+b=u} changes only at
# points in a delta list Delta = {(u, d)} of size O(B): for y in F,
# y != x: (x+y, -1) and (y+x, -1) [cross terms, x removed]; (2x, -1)
# [diagonal, x removed]; for y in F' (new set), y != x': (x'+y, +1)
# and (y+x', +1) [cross terms, x' added]; (2x', +1) [diagonal, x'
# added]. Writing r_new = r_old + delta (delta as a sparse map, zero
# elsewhere), bilinear expansion of R(t) = sum_u r(u) r(u-t) gives
#     R_new(t) = R_old(t)
#                + sum_{(w,d) in Delta} r_old(w+t) * d      [term2]
#                + sum_{(u,d) in Delta} d * r_old(u-t)      [term3]
#                + sum_{(u,d) in Delta} d * delta(u-t)      [term4]
# each term summed ONLY over Delta's O(B) entries (not the full
# support), each requiring O(1) dict lookups per entry -- so updating
# ONE tracked R(t_i) costs O(B), and updating all L=Theta(B) tracked
# shifts costs O(B^2) per swap, matching the target budget. This was
# checked against a brute-force O(N) rebuild of r and a direct O(N)
# recomputation of R(t) for several (t, swap) pairs; an earlier hand-
# derived version of this formula (which iterated delta's support
# only for term2/3/4 but conflated the diagonal (x,x)/(x',x') weight
# with the cross terms) was WRONG (verified failing on t=5 and t=50
# in the test case), so the diagonal MUST be added with weight 1 (not
# 2) alongside the doubled cross terms, exactly as in the derivation
# above -- this matches greedy_low_energy_sidon_subset's existing
# 2x-diagonal handling elsewhere in this file, which is why this
# tiebreak follows the same convention rather than inventing a new one.
#
# WHAT THE TIEBREAK ACTUALLY SCORES: at each step, among `lookahead`
# Sidon-valid candidates, this picks the one whose ADDITION would
# produce the smallest resulting sample variance of R(t_i)-mu across
# the L fixed shifts (mu = B^4/N, the unconditional expectation from
# advisory-6 section 7.3) -- i.e. greedily prefers candidates that
# keep R(t) closer to flat (uniform), which is the direction
# associated with LOWER true 8th moment per the retroactive check.
# Like greedy_low_energy_sidon_subset, this is a heuristic TRY, not a
# proof: per section 7.6, no O(B^2) selection rule can be proven to
# control the 8th moment in general.
"""
    greedy_rvar_tiebreak_sidon_subset(N, target_size, rng; lookahead=6,
                                        L_factor=4, max_restarts=20,
                                        progress_every=5.0)

Greedy Sidon construction (same rejection rule as greedy_sidon_subset)
with a tiebreak that, among `lookahead` valid candidates at each step,
picks the one minimizing the resulting sample variance of R(t)-mu
across a FIXED set of L = L_factor * target_size shifts (drawn once,
before the greedy loop starts). R(t) = sum_u r(u) r(u-t) is tracked
incrementally via the O(B)-per-shift delta update derived and
verified in the comments above; total incremental cost is
O(L * B) = O(B^2) per swap given L = Theta(B), matching the O(B^2)
budget available to construct F.

This is an O(B^2)-budget attempt to recover, in a LIVE construction,
the direction of separation new_invariants.jl's retroactive
sampled_R_variance_score showed between known-good and known-bad
strategies -- see the block comment above for the full derivation and
why the naive Theta(B^2)-shift version (new_invariants.jl's
retroactive scorer) cannot be run live within budget.

Same restart-on-stall and threaded-restart structure as
greedy_low_energy_sidon_subset (restarts are independent, each a full
attempt over a fresh shuffle; static pre-split across
Threads.nthreads() via Threads.@spawn, no threadid()-indexed state).
"""
function greedy_rvar_tiebreak_sidon_subset(N::Int, target_size::Int, rng::AbstractRNG;
                                             lookahead::Int = 6, L_factor::Int = 4,
                                             max_restarts::Int = 20,
                                             progress_every::Real = 5.0)

    L = max(1, L_factor * target_size)
    mu = (Float64(target_size)^4) / Float64(N)

    # One independent attempt. Local state only (elems, sums_seen for
    # the Sidon check; r, shifts, Rvals for the rvar tiebreak) -- safe
    # to run concurrently across tasks, same pattern as
    # greedy_low_energy_sidon_subset's one_attempt.
    function one_attempt(rng_local::AbstractRNG, scanned::Threads.Atomic{Int})
        elems = Int[]
        sums_seen = Set{Int}()          # for the Sidon rejection check (pairwise sums)
        r = Dict{Int,Int}()             # sumset histogram r(u) = #{(a,b) in elems^2 : a+b=u}

        # Fixed shift set, drawn ONCE for this attempt (not per swap/step
        # -- see comment block above on why fixing shifts matters for a
        # tiebreak, distinct from new_invariants.jl's per-call resampling
        # in its purely retroactive, one-shot use).
        shifts = Int[]
        seen_t = Set{Int}()
        while length(shifts) < L
            t = rand(rng_local, 0:(N-1))
            if !(t in seen_t)
                push!(seen_t, t)
                push!(shifts, t)
            end
        end
        Rvals = zeros(Float64, L)   # R(t_i) for each tracked shift, maintained incrementally

        candidates = collect(0:(N-1))
        Random.shuffle!(rng_local, candidates)
        ci = 1

        # Applies a delta list (u => weight) to r in place, and returns
        # it so the caller can also use it to update Rvals incrementally
        # (avoids building the delta list twice).
        function delta_for_add(x::Int, current_elems::Vector{Int})
            d = Dict{Int,Int}()
            for y in current_elems
                y == x && continue
                u1 = mod(x + y, N)
                d[u1] = get(d, u1, 0) + 1
                u2 = mod(y + x, N)
                d[u2] = get(d, u2, 0) + 1
            end
            u0 = mod(2x, N)
            d[u0] = get(d, u0, 0) + 1   # diagonal (x,x), weight 1 -- NOT doubled
            return d
        end

        # Given r BEFORE the update and a delta list, returns the
        # increment to add to R(t) for a single shift t -- the
        # term2+term3+term4 formula verified above. O(|delta|) per shift.
        function delta_R(r_before::Dict{Int,Int}, delta::Dict{Int,Int}, t::Int)
            inc = 0.0
            @inbounds for (u, dval) in delta
                inc += get(r_before, mod(u - t, N), 0) * dval          # term3
                inc += get(r_before, mod(u + t, N), 0) * dval          # term2 (r_old(w+t)*d, w=u here)
                inc += dval * get(delta, mod(u - t, N), 0)             # term4
            end
            return inc
        end

        while length(elems) < target_size && ci <= length(candidates)
            valid_batch = Tuple{Int,Dict{Int,Int},Float64}[]  # (x, delta_for_x, resulting_var_estimate)
            scan = ci
            while length(valid_batch) < lookahead && scan <= length(candidates)
                x = candidates[scan]
                ok = true
                new_sums = Int[]
                for y in elems
                    s = mod(x + y, N)
                    if s in sums_seen
                        ok = false
                        break
                    end
                    push!(new_sums, s)
                end
                if ok
                    s2 = mod(2x, N)
                    (s2 in sums_seen) && (ok = false)
                end
                if ok
                    delta = delta_for_add(x, elems)
                    # Trial-evaluate resulting variance WITHOUT mutating
                    # shared state: compute the R(t)-increment for each
                    # tracked shift using r as it stands now (pre-add),
                    # sum (Rvals[i] + inc - mu)^2 as the candidate score.
                    var_trial = 0.0
                    for i in 1:L
                        inc = delta_R(r, delta, shifts[i])
                        diff = (Rvals[i] + inc) - mu
                        var_trial += diff * diff
                    end
                    var_trial /= L
                    push!(valid_batch, (x, delta, var_trial))
                end
                scan += 1
                Threads.atomic_add!(scanned, 1)
            end

            if isempty(valid_batch)
                ci = scan
                continue
            end

            best = argmin(t -> t[3], valid_batch)
            bx, bdelta = best[1], best[2]
            push!(elems, bx)
            for i in 1:L
                Rvals[i] += delta_R(r, bdelta, shifts[i])
            end
            for (u, dval) in bdelta
                r[u] = get(r, u, 0) + dval
            end
            for s in new_sums_for(bx, elems, N)
                union!(sums_seen, (s,))
            end
            ci = scan
        end

        return elems
    end

    # Helper: recompute the sums a candidate x contributes against the
    # CURRENT elems (post-add) for sums_seen bookkeeping -- mirrors
    # greedy_low_energy_sidon_subset's inline new_sums accumulation but
    # factored out since this function's main loop already builds a
    # delta dict for the rvar tiebreak and re-deriving sums_seen updates
    # from that dict (keyed by sums, weighted by count) is more error-
    # prone than a direct O(B) pass.
    function new_sums_for(x::Int, elems_after_add::Vector{Int}, N::Int)
        out = Int[]
        for y in elems_after_add
            y == x && push!(out, mod(2x, N))
            y != x && push!(out, mod(x + y, N))
        end
        return out
    end

    nt = Threads.nthreads()
    if nt == 1
        @warn "nthreads() == 1 -- Julia was not started with multiple threads. " *
              "Run with `julia -t auto` or `julia -t N` (N>1) to actually run " *
              "restart attempts concurrently."
    end

    n_waves = cld(max_restarts, nt)
    attempt_number = 0

    for wave in 1:n_waves
        wave_size = min(nt, max_restarts - attempt_number)

        scanned_counters = [Threads.Atomic{Int}(0) for _ in 1:wave_size]
        results = Vector{Union{Nothing,Vector{Int}}}(undef, wave_size)

        tasks = Vector{Task}(undef, wave_size)
        for w in 1:wave_size
            a = attempt_number + w
            rng_local = MersenneTwister(rand(rng, UInt) ⊻ (0x9E3779B9 * UInt(a)))
            sc = scanned_counters[w]
            tasks[w] = Threads.@spawn begin
                results[w] = one_attempt(rng_local, sc)
            end
        end

        start_t = time()
        last_report = start_t
        while any(!istaskdone(t) for t in tasks)
            sleep(0.2)
            now_t = time()
            if now_t - last_report >= progress_every
                total_scanned = sum(c[] for c in scanned_counters)
                elapsed = round(now_t - start_t, digits=1)
                println("  ... greedy_rvar_tiebreak restart wave $wave/$n_waves " *
                        "($wave_size attempt(s) in flight, N=$N, target_size=$target_size, L=$L): " *
                        "$(total_scanned) total candidates scanned across the wave " *
                        "so far, $(elapsed)s elapsed")
                last_report = now_t
            end
        end
        foreach(wait, tasks)

        for w in 1:wave_size
            elems = results[w]
            if elems !== nothing && length(elems) >= target_size
                a = attempt_number + w
                if a > 1
                    @warn "greedy_rvar_tiebreak_sidon_subset: needed $a attempt(s) " *
                          "(N=$N, target_size=$target_size) -- earlier attempt(s) stalled " *
                          "short of target_size, same known search-order-artifact class as " *
                          "greedy_low_energy_sidon_subset's restart logic."
                end
                return elems
            end
        end

        attempt_number += wave_size
    end

    error("greedy_rvar_tiebreak_sidon_subset: failed to reach target_size=$target_size " *
          "at N=$N after $max_restarts restarts. Try a larger max_restarts or lookahead " *
          "before concluding no such Sidon set exists (plain greedy_sidon_subset " *
          "succeeding at the same (N, target_size) would confirm this is a search-order " *
          "issue, not a capacity limit).")
end

# ---------------------------------------------------------------
# Strategy 4: Singer difference set (prime case)
# ---------------------------------------------------------------
#
# BACKGROUND
# ----------
# A Singer difference set is the classical (q^2+q+1, q+1, 1)-difference
# set coming from PG(2,q): the q+1 points of a line in the projective
# plane over F_q. Its defining property is that every NONZERO
# difference d in Z/(q^2+q+1) is represented EXACTLY ONCE as a
# difference of two elements of D. That's strictly stronger than
# Sidon (Sidon only forbids a difference/sum being repeated; here
# every nonzero difference occurs exactly once) -- it is the genuine
# algebraic construction flagged as "the right thing to implement
# next" in the removed quadratic-residues note above. It is
# asymptotically optimal (|D| = q+1 ~ sqrt(Nq)) and, unlike greedy,
# requires NO exhaustive search or rejection: construction is a fixed
# O(B^2) pass over finite-field arithmetic, spent once, with no
# candidates thrown away.
#
# CONSTRUCTION (prime q only; general prime powers would need a
# further field extension and are not implemented here)
# ----------------------------------------------------------------
# Build F_{q^3} = F_q[t]/(f(t)) for a random monic irreducible cubic f
# over F_q = Z/q (q prime). Find h, a generator of the unique
# order-Nq subgroup of F_{q^3}^* (Nq = q^2+q+1 = (q^3-1)/(q-1)).
# Compute the trace Tr: F_{q^3} -> F_q (F_q-linear) of every power of
# h. D = { i in 0:(Nq-1) : Tr(h^i) = 0 } is the trace-zero hyperplane
# read off in the discrete-log parametrization by h -- a classical
# Singer difference set.
#
# COST vs BUDGET
# ---------------
# - Irreducible cubic search: expected O(1) trials (~1/3 of monic
#   cubics over F_q are irreducible), each O(q) to check for a root --
#   ~O(q) = O(B) in practice.
# - Generator search for h: expected O(1) trials (a constant fraction
#   of elements generate the full order-Nq subgroup), each O(log q)
#   field multiplications for the order check -- negligible.
# - Power table h^0..h^(Nq-1) plus trace of each: O(Nq) field mults,
#   O(1) each (fixed-size arithmetic mod q). Since Nq = q^2+q+1 and
#   B = q+1, Nq = Theta(B^2) -- this step is EXACTLY O(B^2), matching
#   the stated budget, spent entirely on construction. Verifying via
#   the existing sidon_defect check is a further O(B^2) (same as
#   every other strategy pays), so total remains O(B^2).
#
# For reference: greedy's rejection-sampling scan touches candidates
# up to N times in the worst case, and at this sweep's B = N^0.4,
# N is much larger than B^2 (e.g. N=10^7, B=631, B^2~4*10^5), so
# greedy's O(N) scan is actually cheaper than O(B^2) HERE -- but that
# is an artifact of this specific exponent choice, not a general
# property: greedy's cost scales with N directly, Singer's with B^2
# regardless of how N and B relate, so Singer is the one that
# genuinely respects a B^2 budget stated independent of N.
#
# CAVEAT: Nq != N in general
# ----------------------------
# A Singer set is only defined natively for Nq = q^2+q+1 exactly, q
# prime. The sweep's N values (10007, 100003, ...) are NOT of this
# form, so there is no way to produce a genuine Singer Sidon set of a
# CHOSEN size B living in Z/N for arbitrary N -- forcing one would
# require re-embedding a Z/Nq structure into Z/N, which does NOT
# preserve the exact-difference-set property in general. Rather than
# fake this (the same mistake already made and reverted once with
# quadratic residues above), singer_sidon_subset(N, target_size, rng)
# picks the LARGEST prime q with q^2+q+1 <= N, constructs D natively
# in Z/Nq, and returns D as integer representatives in 0:(Nq-1) --
# valid residues mod N too (Nq <= N), and D remains Sidon when
# reinterpreted mod N (going from modulus Nq to a LARGER modulus N
# only removes wraparound; it cannot create new coincidences among
# sums/differences that were already distinct mod Nq). target_size is
# IGNORED (Singer returns whatever |D|=q+1 is for the largest valid q)
# -- this strategy CANNOT be run through the common compare_strategies
# path, which asserts length(F_int) == B. Use run_singer_comparison
# below instead, which reports Singer's own (q, Nq, B) honestly
# alongside the other strategies rather than silently forcing a
# mismatched B through the shared harness.

"""
    largest_prime_leq(n) -> Int

Largest prime p <= n, via trial division. n is at most a few thousand
here (q never needs to exceed roughly sqrt(N) for the largest N in
this sweep), so this is cheap and not a meaningful contributor to the
O(B^2) budget.
"""
function largest_prime_leq(n::Int)
    n < 2 && error("no prime <= $n")
    isprime_trial(x) = begin
        x < 2 && return false
        x < 4 && return true
        (x % 2 == 0) && return false
        i = 3
        while i * i <= x
            (x % i == 0) && return false
            i += 2
        end
        return true
    end
    p = n
    while !isprime_trial(p)
        p -= 1
    end
    return p
end

"""
    largest_singer_q(N) -> (q, Nq)

Largest PRIME q such that Nq = q^2+q+1 <= N. Returns (q, Nq).
"""
function largest_singer_q(N::Int)
    q_max = floor(Int, (-1 + sqrt(1.0 + 4.0 * (N - 1))) / 2)
    q_max = min(q_max, N)
    q_max < 2 && error("N=$N too small for any prime q with q^2+q+1<=N")
    q = largest_prime_leq(q_max)
    return (q, q^2 + q + 1)
end

"""
    gf_q_irreducible_cubic(q, rng) -> (c0, c1, c2)

Find a monic irreducible cubic x^3 + c2*x^2 + c1*x + c0 over F_q (q
prime, F_q = Z/q). A cubic is irreducible over F_q iff it has NO root
in F_q. Checked by brute-force root search, O(q) per candidate;
~1/3 of monic cubics over F_q are irreducible, so expected O(1)
candidates -- total expected cost O(q) = O(B).
"""
function gf_q_irreducible_cubic(q::Int, rng::AbstractRNG)
    has_root(c0, c1, c2) = any(mod(x^3 + c2*x^2 + c1*x + c0, q) == 0 for x in 0:(q-1))
    while true
        c0 = rand(rng, 0:(q-1))
        c1 = rand(rng, 0:(q-1))
        c2 = rand(rng, 0:(q-1))
        c0 == 0 && continue
        if !has_root(c0, c1, c2)
            return (c0, c1, c2)
        end
    end
end

"""
    prime_factors(n) -> Vector{Int}

Distinct prime factors of n via trial division. n = Nq here
(<= ~10^7 across this sweep), so cheap (O(sqrt(Nq)) = O(B)).
"""
function prime_factors(n::Int)
    fs = Int[]
    m = n
    d = 2
    while d * d <= m
        if m % d == 0
            push!(fs, d)
            while m % d == 0
                m ÷= d
            end
        end
        d += 1
    end
    m > 1 && push!(fs, m)
    return fs
end

"""
    singer_sidon_subset_native(q, rng) -> (D::Vector{Int}, Nq::Int)

Builds a genuine Singer difference set D subset Z/Nq (Nq = q^2+q+1,
|D| = q+1) for prime q, by explicit F_{q^3} arithmetic.

F_{q^3} elements are represented as coefficient triples (a0,a1,a2)
meaning a0 + a1*t + a2*t^2, with t^3 = -(c2 t^2 + c1 t + c0) mod q for
a random irreducible monic cubic found above. `mul` does the
length-3-by-length-3 polynomial product (degree <= 4) and reduces
using the relation for t^3 (t^4 = t*t^3, expanded symbolically).

Tr(v) = v + v^q + v^(q^2) is F_q-linear and lands in the scalar
coordinate after reduction.

GENERATOR NOTE (fixed after a real bug found during verification):
an earlier version of this function found h by projecting a random
nonzero v to v^(q-1) and treating <h> (order Nq) as a transversal for
F_q^* inside F_{q^3}^* -- i.e. assuming powers of h enumerate the Nq
projective points of PG(2,q) bijectively via exponent alone. THAT IS
ONLY VALID when gcd(Nq, q-1) = 1. It fails whenever q ≡ 1 (mod 3),
since then 3 | gcd(Nq, q-1) (checked directly: q=7 gives gcd=3,
q=13 gives gcd=3, q=97 gives gcd=3 -- verified numerically that the
naive construction gives |D| != q+1 and a non-perfect difference set
in exactly these cases, while q=2,3,5,11 happened to have
gcd(Nq,q-1)=1 and worked by coincidence). This matters directly for
your sweep: q=97 (for N=10007) hits this bug.

FIX: instead find a generator `g` of the FULL group F_{q^3}^*
(order q^3-1 = (q-1)*Nq, verified via Lagrange checks against all
prime factors of q^3-1, not just Nq's factors). The projective point
corresponding to field element g^a is determined by a mod Nq (since
F_q^* is the unique order-(q-1) subgroup <g^Nq>, and two powers of g
lie in the same F_q^*-coset iff their exponents agree mod Nq -- this
holds unconditionally, with no gcd caveat, because it follows directly
from |F_{q^3}^*| = Nq*(q-1) and cyclic group structure, not from any
subgroup-transversal argument). So D = { i in 0:(Nq-1) : Tr(g^i) = 0 },
using g^0..g^(Nq-1) directly (NOT g^(q-1) powers), is correct for
every prime q -- verified computationally for q in
{2,3,5,7,11,13,97}: |D|=q+1 and the difference multiset is perfectly
uniform (every nonzero difference exactly once) in all seven cases,
including the three that broke the transversal-subgroup approach.

Cost: O(Nq) = O(B^2) field multiplications for the power table
(each O(1)) -- the promised O(B^2) budget, spent entirely on
construction with nothing thrown away (contrast with greedy, which
spends O(B^2)-scale work rejecting most candidates it examines).
"""
function singer_sidon_subset_native(q::Int, rng::AbstractRNG)
    Nq = q^2 + q + 1
    Mfull = q^3 - 1
    c0, c1, c2 = gf_q_irreducible_cubic(q, rng)

    reduce3(a0, a1, a2) = (mod(a0, q), mod(a1, q), mod(a2, q))

    function mul(u, v)
        u0, u1, u2 = u
        v0, v1, v2 = v
        p0 = u0*v0
        p1 = u0*v1 + u1*v0
        p2 = u0*v2 + u1*v1 + u2*v0
        p3 = u1*v2 + u2*v1
        p4 = u2*v2
        t4_0 = c2*c0
        t4_1 = c2*c1 - c0
        t4_2 = c2^2 - c1
        r0 = p0 + p3*(-c0) + p4*t4_0
        r1 = p1 + p3*(-c1) + p4*t4_1
        r2 = p2 + p3*(-c2) + p4*t4_2
        return reduce3(r0, r1, r2)
    end

    function fpow(v, e)
        result = (1, 0, 0)
        base = v
        while e > 0
            if e & 1 == 1
                result = mul(result, base)
            end
            base = mul(base, base)
            e >>= 1
        end
        return result
    end

    function Tr(v)
        vq  = fpow(v, q)
        vq2 = fpow(v, q*q)
        a0, a1, a2 = v
        b0, b1, b2 = vq
        d0, d1, d2 = vq2
        return mod(a0 + b0 + d0, q)
    end

    # Find a generator g of the FULL multiplicative group F_{q^3}^*
    # (order Mfull = q^3-1), verified against ALL prime factors of
    # Mfull -- not just Nq's factors, which was the bug. Expected O(1)
    # trials (a constant fraction of nonzero elements generate the
    # full group), each O(log(Mfull)) field multiplications for the
    # order check -- negligible next to the O(Nq)=O(B^2) power table.
    Mfull_prime_factors = prime_factors(Mfull)

    g = nothing
    while g === nothing
        v = (rand(rng, 0:(q-1)), rand(rng, 0:(q-1)), rand(rng, 0:(q-1)))
        v == (0, 0, 0) && continue
        if fpow(v, Mfull) == (1, 0, 0) &&
           all(r -> fpow(v, Mfull ÷ r) != (1, 0, 0), Mfull_prime_factors)
            g = v
        end
    end

    # Power table g^0..g^(Nq-1) -- these Nq field elements represent
    # the Nq DISTINCT projective points of PG(2,q), indexed by exponent
    # mod Nq (see docstring: this indexing is unconditionally valid,
    # unlike the earlier <h> transversal approach).
    powers = Vector{NTuple{3,Int}}(undef, Nq)
    powers[1] = (1, 0, 0)
    for i in 2:Nq
        powers[i] = mul(powers[i-1], g)
    end

    D = Int[]
    for i in 0:(Nq-1)
        if Tr(powers[i+1]) == 0
            push!(D, i)
        end
    end

    return (D, Nq)
end

"""
    singer_sidon_subset(N, target_size, rng) -> Vector{Int}

Wrapper matching the (N, target_size, rng) -> Vector{Int} strategy
signature. See the CAVEAT above: target_size is IGNORED. Finds the
largest prime q with q^2+q+1 <= N, builds D natively in Z/Nq, and
returns D as integer representatives (valid mod N too, since Nq<=N).
Do not run this through compare_strategies' common path (it asserts
length(F_int)==B) -- use run_singer_comparison instead.
"""
function singer_sidon_subset(N::Int, target_size::Int, rng::AbstractRNG)
    q, Nq = largest_singer_q(N)
    D, Nq2 = singer_sidon_subset_native(q, rng)
    @assert Nq == Nq2
    return D
end

# ---------------------------------------------------------------
# run_singer_comparison: honest side-by-side, own (q, Nq, B) columns
# ---------------------------------------------------------------

"""
    run_singer_comparison(; Ns, m_per_point, m_scaling, m_floor, m_cap, seed)

Runs the Singer construction at the largest-prime-q point <= each N
in `Ns`, alongside the SAME character-sampler objective used in
compare_strategies, but WITHOUT forcing Singer's B to match the other
strategies' B = round(N^0.4). Prints Singer's own N (really Nq), B
(really q+1), and q, so nothing is silently overwritten or force-fit.

Not merged into compare_strategies' main loop because that function's
correctness depends on every strategy sharing the same (N, B) per
row (see its docstring/assert) -- Singer structurally cannot promise
an arbitrary chosen B for arbitrary N, so it gets its own honest
harness instead of corrupting that invariant.
"""
function run_singer_comparison(; Ns::Vector{Int} = [10_007, 100_003, 1_000_003, 10_000_019],
                                   m_per_point::Int = 20_000,
                                   m_scaling::Symbol = :sqrt_N,
                                   m_floor::Int = 2_000,
                                   m_cap::Int = typemax(Int),
                                   seed::Int = 1)
    N0 = Float64(first(Ns))
    results = NamedTuple[]

    println("N_target\tq\tNq\tB(=q+1)\tm\tratio(MC/flat)\tmax|U|\tsidon_defect\telapsed_s")
    for N in Ns
        q, Nq = largest_singer_q(N)
        rng = MersenneTwister(seed)
        D, _ = singer_sidon_subset_native(q, rng)
        B = length(D)
        @assert B == q + 1 "Singer set size mismatch: got $B, expected q+1=$(q+1)"

        defect = sidon_defect(D, Nq)
        if defect != 0
            @warn "N_target=$N (Nq=$Nq): Singer set has nonzero sidon_defect=$defect -- " *
                  "should be exactly 0 by construction; investigate field arithmetic " *
                  "or generator search before trusting this row"
        end

        m_target = if m_scaling == :fixed
            m_per_point
        elseif m_scaling == :sqrt_N
            round(Int, m_per_point * sqrt(Nq / N0))
        elseif m_scaling == :linear_N
            round(Int, m_per_point * (Nq / N0))
        else
            error("unknown m_scaling = $m_scaling")
        end
        m = clamp(m_target, m_floor, min(m_cap, Nq - 1))

        F = [[x] for x in D]
        t0 = time()
        result = run_character_sampler_threaded(G_for(Nq), F; m = m, seed = seed,
                                                   k_size = Nq, report_every = typemax(Int))
        elapsed = time() - t0

        Bf = Float64(B)
        flat = (Bf^8) / Nq
        ratio = result.M8_running[end] / flat
        maxU = maximum(abs.(result.U_vals))

        @printf("%d\t%d\t%d\t%d\t%d\t%.4f\t%.4f\t%d\t%.2f\n",
                N, q, Nq, B, m, ratio, maxU, defect, elapsed)

        push!(results, (; N_target = N, q, Nq, B, m, ratio, maxU, defect, elapsed))
    end

    if length(results) >= 2
        println("\n--- Singer growth-exponent fit ---")
        fit_rows = [(; N = r.Nq, B = r.B, m = r.m, ratio = r.ratio,
                       maxU = r.maxU, defect = r.defect, elapsed = r.elapsed)
                    for r in results]
        fit = fit_growth_exponent(fit_rows)
        if length(fit_rows) >= 3
            local_growth_exponents(fit_rows)
        end
        return (; results, fit)
    end

    return (; results, fit = nothing)
end

# ---------------------------------------------------------------
# run_singer_embedded_comparison: Singer D embedded in the REAL
# target group Z/N, measured against N (not Nq)
# ---------------------------------------------------------------
#
# WHY THIS EXISTS (separate from run_singer_comparison above)
# -------------------------------------------------------------
# run_singer_comparison's ratio numbers are computed with the group
# order fixed at Nq = q^2+q+1 -- Singer's OWN native modulus, which
# is Theta(B^2). That is not the same experiment as "how does this
# factor base behave inside our actual subgroup", because our actual
# subgroup has order N ~ p^2, while B is constrained externally to
# scale like B ~ p^(2/5) -- so N ~ p^2 ~ B^5, not B^2. Native Singer
# lives in a group roughly p^(6/5) SMALLER than our real N.
#
# Embedding D (integer representatives) into Z/N preserves Sidon-ness
# PROVIDED N >= 2*(Nq-1), not merely Nq <= N (an earlier version of
# this comment claimed Nq <= N was sufficient -- this was WRONG and
# caught empirically: at target_q_exponent=0.5, Nq ends up close to N,
# raw pairwise sums of D's representatives (which range up to
# 2*(Nq-1)) then wrap under mod N, creating collisions that did not
# exist mod Nq. The corrected condition N >= 2*(Nq-1) is enforced by
# an assert below; target_q_exponent values that violate it for a
# given N will now raise clearly instead of silently returning a
# corrupted, nonzero-sidon_defect row (as the 0.5 sweep point
# previously did). Within that valid range, embedding does preserve
# Sidon-ness for free -- same wraparound argument as
# singer_sidon_subset above, just with the right threshold.
# But the property that made native-Singer's ratio flat -- every
# nonzero difference in Z/Nq hit EXACTLY once -- is a statement
# about Z/Nq. Once embedded in Z/N with Nq << N, D's differences
# only populate a size-Nq subset of Z/N; from the ambient group's
# point of view that is now a highly CONCENTRATED, non-equidistributed
# difference pattern, not a flat one. Whether that concentration
# still beats greedy's 8th-moment excess at the same N is exactly
# the open empirical question this function answers -- the native
# ratio (0.94-0.998 in earlier runs) does NOT transfer and should
# not be quoted as evidence for embedded behavior.
#
# q IS CHOSEN TO HIT THE B ~ N^0.4 TARGET (not "largest q <= N"):
# since B = q+1 and the sweep's other strategies all target
# B = round(N^0.4), q is chosen so that q+1 ~ N^0.4, i.e.
# q ~ N^0.4 (equivalently, matching B ~ p^(2/5) when N ~ p^2, since
# then N^0.4 ~ (p^2)^0.4 = p^0.8 -- NOTE: this is the exponent
# implied by "B ~ p^(2/5) and N ~ p^2" only if you read B's target
# directly as p^0.4 = N^0.2, NOT N^0.4; see the target_q_exponent
# keyword below, which defaults to 0.2 to match B ~ p^(2/5) ~ N^0.2
# literally, and can be set to 0.4 to instead match this sweep's
# other strategies' B ~ N^0.4 convention for apples-to-apples
# comparison against greedy/greedy_low_energy in compare_strategies).
# The largest prime q with q <= target_q is used (Singer only
# implements prime q here).

"""
    run_singer_embedded_comparison(; Ns, target_q_exponent, m_per_point,
                                      m_scaling, m_floor, m_cap, seed)

For each N in `Ns`: pick prime q ~ N^target_q_exponent (largest prime
<= that target), build the native Singer difference set D in Z/Nq,
embed D's integer representatives into Z/N unchanged (valid since
Nq <= N), and run the SAME character-sampler 8th-moment measurement
used by compare_strategies / run_singer_comparison but with the group
and flat-normalizer fixed at the REAL target N -- not Nq. This is the
fair comparison against greedy/greedy_low_energy at matched (N, B).

`target_q_exponent` defaults to 0.2 so that B = q+1 ~ N^0.2, matching
"B ~ p^(2/5)" literally when N ~ p^2 (since then N^0.2 ~ p^0.4). Pass
0.4 instead to match this sweep's OTHER strategies' B ~ N^0.4
convention if you want a same-B, same-N comparison against greedy
specifically (note: at N ~ p^2 that would mean B ~ p^0.8, a
DIFFERENT B-vs-p scaling than "B ~ p^(2/5)" -- the two exponent
choices are not interchangeable, hence this being a keyword rather
than a hardcoded constant).

sidon_defect is checked against N (the real embedding target), not
Nq -- this re-verifies Sidon-ness actually survives the embedding
rather than assuming it (see docstring above: it should be exactly 0
by the wraparound argument, but this checks rather than asserts,
since a defect here would indicate a bug in the embedding, not an
expected outcome).
"""
function run_singer_embedded_comparison(; Ns::Vector{Int} = [10_007, 100_003, 1_000_003, 10_000_019],
                                            target_q_exponent::Float64 = 0.2,
                                            m_per_point::Int = 20_000,
                                            m_scaling::Symbol = :sqrt_N,
                                            m_floor::Int = 2_000,
                                            m_cap::Int = typemax(Int),
                                            seed::Int = 1)
    N0 = Float64(first(Ns))
    results = NamedTuple[]

    println("\n=== Singer difference set, EMBEDDED in real target N " *
            "(target_q_exponent=$target_q_exponent) ===")
    println("N\tq\tNq\tB(=q+1)\tm\tratio(MC/flat, vs N)\tmax|U|\tsidon_defect(mod N)\telapsed_s")
    for N in Ns
        q_target = max(2, floor(Int, N^target_q_exponent))
        q_target = min(q_target, N)  # guard tiny N
        q = largest_prime_leq(q_target)
        rng = MersenneTwister(seed)
        D, Nq = singer_sidon_subset_native(q, rng)
        B = length(D)
        @assert B == q + 1 "Singer set size mismatch: got $B, expected q+1=$(q+1)"
        # CORRECTED CONDITION (previously just Nq <= N, which is NOT
        # sufficient -- caught after target_q_exponent=0.5 silently
        # produced sidon_defect in the hundreds of thousands instead of
        # tripping this assert). D's integer representatives lie in
        # [0, Nq-1], so a raw pairwise sum x+y before any reduction can
        # be as large as 2*(Nq-1). Singer's exact-once guarantee is a
        # statement about mod(x+y, Nq); reducing mod N instead only
        # agrees with that guarantee if no sum wraps under mod N, i.e.
        # N >= 2*(Nq-1). Nq <= N alone is not enough once Nq gets close
        # to N (e.g. target_q_exponent near 0.5): sums up to ~2Nq can
        # then exceed N and wrap, creating NEW mod-N collisions between
        # sums that were distinct mod Nq -- exactly the failure mode
        # the old comment claimed was impossible.
        @assert N >= 2 * (Nq - 1) "Singer native modulus Nq=$Nq is too close to " *
                         "target N=$N for a valid embedding -- need N >= 2*(Nq-1) = " *
                         "$(2*(Nq-1)), not just N >= Nq, or pairwise sums of D's " *
                         "representatives can wrap mod N and create spurious " *
                         "collisions absent mod Nq (this is what silently corrupted " *
                         "target_q_exponent=0.5 previously: Nq was close enough to N " *
                         "that sidon_defect became nonzero instead of staying 0). " *
                         "Lower target_q_exponent for this N, or treat this exponent " *
                         "as out of range for the embedded comparison."

        # Re-check Sidon-ness against the REAL modulus N, not Nq --
        # should be 0 given the assert above holds, but verified rather
        # than assumed (a defect here now indicates an actual bug, not
        # a known-and-silently-tolerated near-boundary case).
        defect = sidon_defect(D, N)
        if defect != 0
            @warn "N=$N, q=$q (Nq=$Nq): embedded Singer set has nonzero " *
                  "sidon_defect=$defect when checked mod N despite N >= 2*(Nq-1) " *
                  "holding -- this should be impossible; investigate the embedding " *
                  "or sidon_defect logic before trusting this row"
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

        F = [[x] for x in D]
        t0 = time()
        # Group and k_size fixed at the REAL target N, matching how
        # greedy/greedy_low_energy are measured in compare_strategies --
        # this is the whole point of this function versus
        # run_singer_comparison above.
        result = run_character_sampler_threaded(G_for(N), F; m = m, seed = seed,
                                                   k_size = N, report_every = typemax(Int))
        elapsed = time() - t0

        Bf = Float64(B)
        flat = (Bf^8) / N          # flat normalizer vs the REAL N, not Nq
        ratio = result.M8_running[end] / flat
        maxU = maximum(abs.(result.U_vals))

        @printf("%d\t%d\t%d\t%d\t%d\t%.4f\t%.4f\t%d\t%.2f\n",
                N, q, Nq, B, m, ratio, maxU, defect, elapsed)

        push!(results, (; N, q, Nq, B, m, ratio, maxU, defect, elapsed))
    end

    if length(results) >= 2
        println("\n--- Embedded-Singer growth-exponent fit (vs real N) ---")
        fit_rows = [(; N = r.N, B = r.B, m = r.m, ratio = r.ratio,
                       maxU = r.maxU, defect = r.defect, elapsed = r.elapsed)
                    for r in results]
        fit = fit_growth_exponent(fit_rows)
        if length(fit_rows) >= 3
            local_growth_exponents(fit_rows)
        end
        return (; results, fit)
    end

    return (; results, fit = nothing)
end

# ---------------------------------------------------------------
# Strategy 5: "Singer paired" -- randomized partner-sum construction
# ---------------------------------------------------------------
#
# USER'S IDEA: rather than embedding raw Singer points D directly
# (Strategy 4, which showed extreme 8th-moment blowup once Nq << N --
# see run_singer_embedded_comparison), build F from SUMS of pairs of
# Singer points: F = { P + partner(P) : P in D }, where partner(P) is
# drawn randomly. Concretely here: partner is a random OTHER element
# of D itself, via a uniformly random permutation sigma of D's
# indices -- F[i] = D[i] + D[sigma(i)].
#
# WHY THIS MIGHT HELP (motivation, NOT a guarantee -- see below):
# embedded-Singer's problem was that its Nq-1 covered differences sit
# in a small contiguous-ish block near 0 (since D's raw representatives
# are all < Nq << N), giving those few residues huge relative
# hit-multiplicity versus the flat B^2/N average. Summing each Singer
# point with a second, independently-varying Singer point scatters the
# OUTPUT values themselves across a much wider range (up to ~2*(Nq-1),
# still << N in general, but more spread than D alone) -- the hope is
# this reduces the pathological clustering that embedding raw D
# produced, even though total sum-set SIZE is still bounded by O(B^2)
# regardless of construction (a pure counting fact, not fixable by any
# choice of B-element set -- see the chat discussion: no B-element set
# can cover more than O(B^2) of Z/N's residues).
#
# WHY THIS IS NOT A DERIVATION -- MUST BE MEASURED, NOT ASSUMED:
# a difference of two elements of F is
#     (D[i] + D[sigma(i)]) - (D[j] + D[sigma(j)])
#   = (D[i] - D[j]) + (D[sigma(i)] - D[sigma(j)])
# i.e. a SUM of two differences, each individually drawn from D's
# exact-once difference multiset (mod Nq). There is no general theorem
# that the sum of two exact-once quantities is itself well-behaved --
# depending on sigma, this could concentrate onto very few values just
# as easily as it could spread out. This is an experiment, not a
# proof, and is reported exactly as such: measured empirically via the
# same character-sampler 8th-moment ratio used throughout this file.
#
# |F| MAY BE SMALLER THAN |D|: unlike raw D (whose distinctness is
# guaranteed by construction) or independent random shifts, sums
# D[i]+D[sigma(i)] CAN collide for different i -- there is no a priori
# injectivity guarantee for this map. This function deduplicates and
# reports the ACTUAL |F| achieved rather than asserting a fixed size;
# a large gap between |F| and |D| would itself be informative (heavy
# collision = this construction is throwing away a lot of the budget).

"""
    singer_paired_sidon_subset(q, rng) -> (F::Vector{Int}, Nq::Int, n_collisions::Int)

Builds D natively via singer_sidon_subset_native(q, rng), then forms
F = unique({ D[i] + D[sigma(i)] mod Nq : i in eachindex(D) }) for a
uniformly random permutation sigma of eachindex(D) (sigma(i) == i is
allowed -- partner CAN be the point itself, giving F[i] = 2*D[i], not
excluded since there is no principled reason to exclude self-pairing
here). Returns F (deduplicated, so |F| <= |D| = q+1), Nq, and the
number of collisions removed (|D| - |F|) so collision rate is visible
rather than silently absorbed.

Sums are taken mod Nq (native Singer modulus) BEFORE any embedding
into a larger N -- embedding F into Z/N afterward is subject to the
SAME N >= 2*(|value range|-1) caveat as singer_sidon_subset's raw
embedding (see that function and run_singer_embedded_comparison's
corrected assert) -- callers embedding F into a real target N must
re-verify Sidon-ness there directly (via sidon_defect) rather than
assume it transfers, since summing two Singer points is a genuinely
different construction than embedding D alone, and no wraparound-only
argument has been established for it.
"""
function singer_paired_sidon_subset(q::Int, rng::AbstractRNG)
    D, Nq = singer_sidon_subset_native(q, rng)
    n = length(D)
    sigma = Random.shuffle(rng, collect(1:n))
    F_with_dupes = [mod(D[i] + D[sigma[i]], Nq) for i in 1:n]
    F = collect(Set(F_with_dupes))
    n_collisions = n - length(F)
    return (F, Nq, n_collisions)
end

# ---------------------------------------------------------------
# run_singer_paired_comparison: paired-Singer embedded in real N,
# same harness shape as run_singer_embedded_comparison for direct
# side-by-side comparison against raw embedded-Singer and greedy.
# ---------------------------------------------------------------

"""
    run_singer_paired_comparison(; Ns, target_q_exponent, m_per_point,
                                    m_scaling, m_floor, m_cap, seed)

Same structure as run_singer_embedded_comparison, but F is built via
singer_paired_sidon_subset (random-partner sums of Singer points)
instead of raw D. Re-verifies Sidon-ness of the embedded F against the
REAL target N via sidon_defect (NOT assumed -- see that function's
docstring: no wraparound-only argument is established for this
construction, unlike raw-D embedding). Also reports the collision
count from the pairing step (|D|-|F|) and the resulting B=|F|, which
can differ across N even at fixed target_q_exponent since collision
rate is a property of the random pairing, not deterministic.

Uses the SAME seed convention as the other comparison functions in
this file (fresh MersenneTwister(seed) per N) so results are
reproducible and comparable run-to-run.
"""
function run_singer_paired_comparison(; Ns::Vector{Int} = [10_007, 100_003, 1_000_003, 10_000_019],
                                          target_q_exponent::Float64 = 0.2,
                                          m_per_point::Int = 20_000,
                                          m_scaling::Symbol = :sqrt_N,
                                          m_floor::Int = 2_000,
                                          m_cap::Int = typemax(Int),
                                          seed::Int = 1)
    N0 = Float64(first(Ns))
    results = NamedTuple[]

    println("\n=== Singer PAIRED (random-partner sums), embedded in real target N " *
            "(target_q_exponent=$target_q_exponent) ===")
    println("N\tq\tNq\tB(=|F|)\tcollisions\tm\tratio(MC/flat, vs N)\tmax|U|\tsidon_defect(mod N)\telapsed_s")
    for N in Ns
        q_target = max(2, floor(Int, N^target_q_exponent))
        q_target = min(q_target, N)
        q = largest_prime_leq(q_target)
        rng = MersenneTwister(seed)
        F_int, Nq, n_collisions = singer_paired_sidon_subset(q, rng)
        B = length(F_int)

        if Nq > N
            @warn "N=$N, q=$q: Nq=$Nq exceeds N -- skipping this point " *
                  "(target_q_exponent=$target_q_exponent too large for this N)"
            continue
        end

        # Sidon-ness is NOT assumed here (see docstring) -- checked
        # directly against the real N. A nonzero defect is a real
        # possible outcome for this construction, not a bug signal.
        defect = sidon_defect(F_int, N)

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

        F = [[x] for x in F_int]
        t0 = time()
        result = run_character_sampler_threaded(G_for(N), F; m = m, seed = seed,
                                                   k_size = N, report_every = typemax(Int))
        elapsed = time() - t0

        Bf = Float64(B)
        flat = (Bf^8) / N
        ratio = result.M8_running[end] / flat
        maxU = maximum(abs.(result.U_vals))

        @printf("%d\t%d\t%d\t%d\t%d\t\t%d\t%.4f\t%.4f\t%d\t%.2f\n",
                N, q, Nq, B, n_collisions, m, ratio, maxU, defect, elapsed)

        push!(results, (; N, q, Nq, B, n_collisions, m, ratio, maxU, defect, elapsed))
    end

    if length(results) >= 2
        println("\n--- Singer-paired growth-exponent fit (vs real N) ---")
        fit_rows = [(; N = r.N, B = r.B, m = r.m, ratio = r.ratio,
                       maxU = r.maxU, defect = r.defect, elapsed = r.elapsed)
                    for r in results]
        fit = fit_growth_exponent(fit_rows)
        return (; results, fit)
    end

    return (; results, fit = nothing)
end
# NOT a candidate factor-base construction. This sweeps
# target_q_exponent upward across several values purely to trace how
# the embedded-Singer growth exponent gamma changes as B is allowed
# to scale closer to sqrt(N) -- confirming or refuting the structural
# prediction that Nq/N ~ N^(2*target_q_exponent - 1), so Nq/N only
# stops shrinking with N once target_q_exponent -> 0.5 (i.e. B ~
# sqrt(N)). The real problem constrains B ~ p^(2/5) ~ N^0.2 (with
# N ~ p^2), which is fixed and not a free parameter -- exponents
# above 0.2 in this sweep do NOT represent an allowed factor-base
# choice, they exist only to show WHERE on the exponent axis the
# mechanism would need to sit for embedding to stop being lossy, so
# you can see how far 0.2 is from that point and decide whether any
# variant of "scale q up" is salvageable given the real constraint.
"""
    run_singer_embedded_exponent_sweep(; Ns, exponents, kwargs...)

Runs run_singer_embedded_comparison once per exponent in `exponents`
(default spans the real constraint 0.2 up to 0.45, the practical
ceiling this sweep can probe -- 0.5 is deliberately EXCLUDED: at that
exponent Nq ~ q^2 ~ N by construction, so the embedding-validity
condition N >= 2*(Nq-1) can never hold for any N in this sweep's
range, meaning target_q_exponent=0.5 fails
run_singer_embedded_comparison's assert on EVERY call, not just
occasionally -- it was removed from the default rather than left in
to fail every run; pass it explicitly via `exponents` only if you
want to see that assert fire), prints each full block via the
existing per-exponent function, then prints a compact summary table
of (exponent, fitted gamma, fitted C, R^2) so the trend across
exponents is visible without re-reading every per-N row.

kwargs are forwarded to each run_singer_embedded_comparison call
(e.g. Ns, m_per_point, seed).
"""
function run_singer_embedded_exponent_sweep(; Ns::Vector{Int} = [10_007, 100_003, 1_000_003, 10_000_019],
                                                exponents::Vector{Float64} = [0.2, 0.3, 0.4, 0.45],
                                                kwargs...)
    println("\n############################################################")
    println("# EMBEDDED-SINGER EXPONENT SWEEP -- DIAGNOSTIC ONLY")
    println("# Real factor-base constraint is target_q_exponent=0.2")
    println("# (B ~ p^(2/5) ~ N^0.2 given N ~ p^2). Exponents above 0.2")
    println("# below are NOT valid factor-base choices -- they trace where")
    println("# the compression mechanism would need target_q_exponent to")
    println("# sit (~0.5, i.e. B ~ sqrt(N)) before embedding stops being")
    println("# lossy, so you can see how far the real constraint is from")
    println("# that point.")
    println("############################################################")

    summary = NamedTuple[]
    for exp in exponents
        run = run_singer_embedded_comparison(; Ns = Ns, target_q_exponent = exp, kwargs...)
        if run.fit !== nothing
            push!(summary, (; target_q_exponent = exp, run.fit.gamma, run.fit.C, run.fit.r2))
        else
            @warn "target_q_exponent=$exp: fewer than 2 successful points, skipped in summary"
        end
    end

    if !isempty(summary)
        println("\n=== Sweep summary: gamma vs. target_q_exponent ===")
        println("(predicted Nq/N ~ N^(2*exponent-1) -- gamma should trend toward",
                " 0 as exponent -> 0.5 if the compression-mechanism explanation is correct)")
        println("target_q_exponent\tfitted_gamma\tfitted_C\tR^2")
        for s in summary
            @printf("%.3f\t\t\t%.4f\t\t%.4e\t%.4f\n",
                    s.target_q_exponent, s.gamma, s.C, s.r2)
        end
        println("\nFor reference, the REAL constraint (target_q_exponent=0.2) is the",
                " first row above -- everything past it is diagnostic extrapolation,",
                " not an available choice given B ~ p^(2/5).")
    end

    return summary
end

# ---------------------------------------------------------------
# Exact-spectrum helpers (shared by phi_diagnostic.jl,
# norm_trace_pullback.jl, and Strategy 8 below)
# ---------------------------------------------------------------
#
# Defined here (the file everything else already includes) rather
# than in phi_diagnostic.jl, where the DFT+top-k logic originally
# lived, to avoid a circular include: phi_diagnostic.jl already does
# `include("strategy_comparison.jl")`, so putting these helpers there
# instead and having strategy_comparison.jl include phi_diagnostic.jl
# back would create a cycle. phi_diagnostic.jl's full_spectrum_diagnostic
# now calls these two functions instead of duplicating the DFT/sort
# logic inline (see that file's history -- it originally had this code
# inline, moved here unchanged when Strategy 8 needed to reuse it).

"""
    compute_full_spectrum(F::Vector{Int}, N::Int) -> S_hat::Vector{ComplexF64}

Direct O(N*|F|) DFT: S_hat(k) = sum_{x in F} exp(2*pi*i*k*x/N), for
every k in 0:(N-1) (returned 1-indexed: S_hat[k+1] is the value at
frequency k). EXACT, no Monte Carlo sampling -- this is what makes
"top top_frac fraction of characters" a real ranking rather than a
noisy one, and is only feasible because N is kept small enough for
O(N*|F|) to be cheap (a few thousand up to a few million -- see
full_spectrum_diagnostic's and Strategy 8's docstrings for the same
caveat; this does NOT scale to the 10^7-scale production sweep points
used elsewhere in this file, where only the character-sampler's Monte
Carlo estimate is affordable).
"""
function compute_full_spectrum(F::Vector{Int}, N::Int)
    S_hat = Vector{ComplexF64}(undef, N)
    for k in 0:(N-1)
        s = 0.0 + 0.0im
        @inbounds for x in F
            s += cis(2pi * k * x / N)
        end
        S_hat[k+1] = s
    end
    return S_hat
end

"""
    top_k_peaks(S_hat::Vector{ComplexF64}, N::Int; top_frac=0.01)
        -> (top_ks::Vector{Int}, top_mags8::Vector{Float64}, frac_of_M8::Float64)

Given a full spectrum S_hat (as returned by compute_full_spectrum,
1-indexed so S_hat[k+1] is frequency k), ranks the N-1 NON-TRIVIAL
frequencies (k=0, the trivial character, is excluded -- S_hat(0) = |F|
by construction, not part of the moment sum this project cares about)
by |S_hat(k)|^8 and returns the top `top_frac` fraction as
K_peak = top_ks (actual frequency values, not array indices), their
|S_hat(k)|^8 magnitudes, and the fraction of the total non-trivial
|S|^8 mass they account for.
"""
function top_k_peaks(S_hat::Vector{ComplexF64}, N::Int; top_frac::Float64 = 0.01)
    mags8 = [abs(S_hat[k+1])^8 for k in 1:(N-1)]
    total_M8 = sum(mags8)  # proportional to (N-1)*M8_hat/Gord_nontrivial scaling; relative use only here

    n_top = max(1, round(Int, top_frac * (N - 1)))
    order = sortperm(mags8; rev = true)
    top_ks = [k for k in 1:(N-1)][order[1:n_top]]  # 1-indexed k values (actual frequency, not array index)
    top_mags8 = mags8[order[1:n_top]]

    frac_of_M8 = sum(top_mags8) / total_M8
    return (top_ks, top_mags8, frac_of_M8)
end

# ---------------------------------------------------------------
# Strategy 6: Singer set with an incremental 8th-moment-style filter
# ---------------------------------------------------------------
#
# USER'S IDEA: unlike Strategy 5 above (which changes what F's
# elements ARE, by summing Singer-point pairs), this one keeps F as a
# genuine subset of D itself, taken in Singer order, but adds a SECOND
# rejection filter on top of the ordinary Sidon check as each new
# Singer element is considered:
#
#   1. Take D[1] unconditionally (first Singer element, no filter to
#      apply yet -- nothing accepted before it to pair against).
#   2. For each subsequent Singer element D[i] (i = 2, 3, ...., in
#      native Singer order, no shuffling):
#        a. Draw partner_i uniformly at random from the elements of F
#           ALREADY ACCEPTED so far (not from all of D, not from Z/N).
#        b. Compute diff_i = mod(D[i] - partner_i, N).
#        c. Reject D[i] if diff_i + diff_prev has been seen before,
#           for ANY previously accepted pair's diff_prev -- i.e.
#           maintain a running Set of all such SUMS-OF-TWO-DIFFERENCES
#           seen so far (call it quad_sums_seen), and reject D[i] if
#           diff_i + diff_prev (mod N) lands on a value already in
#           quad_sums_seen for some earlier accepted diff_prev.
#        d. ALSO still apply the ordinary Sidon check against F itself
#           (ordinary pairwise-sum collision, same rule as
#           greedy_sidon_subset) -- both filters must pass.
#        e. If D[i] fails either filter, skip it and move to D[i+1].
#           NO retry with a different partner, no replacement --
#           a rejected Singer element is simply never revisited, so
#           |F| can and generally will be SMALLER than |D|.
#
# WHY THIS IS A GENUINE 8TH-MOMENT-STYLE FILTER, NOT JUST A RELABELED
# 4TH-MOMENT ONE: a term contributing to the 8th moment / U^4-type sum
# looks like a QUADRUPLE of differences summing to something repeated
# -- schematically (a-b)+(c-d) colliding with another (a'-b')+(c'-d').
# diff_i + diff_prev is exactly a sum of two differences of F-pairs,
# so checking THAT value for collisions (rather than a single
# difference, which is all the ordinary Sidon check does) is screening
# against exactly the kind of 4-term additive coincidence that feeds
# the 8th moment. This is still an O(B)-per-step, O(B^2)-total
# incremental proxy -- same complexity class as greedy_low_energy's
# tiebreak above -- NOT an exhaustive 8th-moment computation (which
# would be the O(B^4)-or-worse thing the character sampler exists to
# estimate cheaply instead of computing exactly).
#
# WHY THIS IS NOT A DERIVATION -- MUST BE MEASURED, NOT ASSUMED: per
# section 7.6 (see file header), no O(B^2)-cost selection rule can be
# PROVEN to control the true 8th moment / U^3-level behavior; this is
# exactly that kind of rule, applied here to a Singer starting order
# instead of a random one. It might help, it might not, and the random
# partner draw means two runs with different seeds can accept a
# different SUBSET of D and reach a different final B. That is
# reported honestly (this strategy, like greedy_low_energy, cannot
# promise an exact target_size -- see the wrapper below) rather than
# assumed away.
#
# RELATIONSHIP TO EXISTING STRATEGIES: this reuses the Singer element
# ORDER as the candidate stream (Strategy 4's D, walked in native
# order rather than reshuffled) but reuses greedy_low_energy's
# incremental-rejection SHAPE (Strategy 3) applied to a new quantity
# (sum-of-two-differences rather than a density tiebreak). It is
# neither pure Singer nor pure greedy -- a genuinely new hybrid, hence
# its own strategy slot rather than a variant flag on either.

"""
    singer_quad_filtered_subset(q, rng; max_size=nothing) -> (F::Vector{Int}, Nq::Int, n_rejected::Int)

Builds the native Singer difference set D via
singer_sidon_subset_native(q, rng) (Nq = q^2+q+1, |D| = q+1), then
walks D IN ITS NATIVE ORDER (no shuffling -- the Singer order itself
is the point of interest here, unlike every rejection-based strategy
above which shuffles first) applying two filters to each candidate
D[i] (i >= 2; D[1] is always accepted):

  - Ordinary Sidon check against F (elements accepted so far): reject
    if mod(D[i] + f, Nq) has already appeared as a pairwise sum for
    any f in F, or if mod(2*D[i], Nq) has already appeared.
  - NEW 8th-moment-style filter: draw partner_i uniformly at random
    from F (already-accepted elements only -- requires F nonempty,
    guaranteed once D[1] is in), compute diff_i = mod(D[i] - partner_i,
    Nq), and reject if mod(diff_i + diff_prev, Nq) has been seen
    before for any diff_prev recorded from an earlier ACCEPTED
    element's own partner draw. Both filters must pass for D[i] to be
    accepted; failing either means D[i] is skipped and never
    reconsidered (no retry with a different partner).

All arithmetic mod Nq (the native Singer modulus) -- this function
does NOT embed into a larger N; callers wanting a specific target N
should embed F afterward and re-verify sidon_defect there directly,
same caveat as singer_paired_sidon_subset above (summing/differencing
Singer points is a different construction than embedding D alone, and
no wraparound-only argument is established for it).

`max_size`, if given, stops walking D early once length(F) reaches
it (D still has q+1-max_size elements left unexamined in that case).
Default `nothing` walks the full D.

Returns F (the accepted subset, in the order accepted -- a prefix-ish
subsequence of D's native order, NOT necessarily contiguous since
rejected elements are simply skipped), Nq, and n_rejected = the number
of D's elements that failed at least one filter (so the rejection
rate is visible rather than silently absorbed -- mirrors
n_collisions in singer_paired_sidon_subset).
"""
function singer_quad_filtered_subset(q::Int, rng::AbstractRNG; max_size::Union{Int,Nothing} = nothing)
    D, Nq = singer_sidon_subset_native(q, rng)

    F = Int[D[1]]
    sums_seen = Set{Int}()
    push!(sums_seen, mod(2 * D[1], Nq))

    # diffs_seen: every diff_i = mod(D[i]-partner_i, Nq) recorded from
    # a previously ACCEPTED element's own partner draw (one per
    # accepted element after the first).
    diffs_seen = Int[]
    # quad_sums_seen: the set of all mod(diff_i + diff_prev, Nq)
    # values already produced by earlier accepted elements, checked
    # against new candidates before they're accepted.
    quad_sums_seen = Set{Int}()

    n_rejected = 0

    for i in 2:length(D)
        max_size !== nothing && length(F) >= max_size && break
        x = D[i]

        # Ordinary Sidon check against F, same rule as
        # greedy_sidon_subset / greedy_low_energy_sidon_subset.
        sidon_ok = true
        new_sums = Int[]
        for y in F
            s = mod(x + y, Nq)
            if s in sums_seen
                sidon_ok = false
                break
            end
            push!(new_sums, s)
        end
        if sidon_ok
            s2 = mod(2x, Nq)
            (s2 in sums_seen) && (sidon_ok = false)
        end

        if !sidon_ok
            n_rejected += 1
            continue
        end

        # 8th-moment-style filter: random partner from F as already
        # accepted (F is guaranteed nonempty here, since D[1] seeded
        # it before this loop starts).
        partner = rand(rng, F)
        diff_i = mod(x - partner, Nq)

        quad_hit = false
        for dp in diffs_seen
            if mod(diff_i + dp, Nq) in quad_sums_seen
                quad_hit = true
                break
            end
        end

        if quad_hit
            n_rejected += 1
            continue
        end

        # Accept: commit both filters' bookkeeping together, only now
        # that both have passed.
        push!(F, x)
        union!(sums_seen, new_sums)
        push!(sums_seen, mod(2x, Nq))
        for dp in diffs_seen
            push!(quad_sums_seen, mod(diff_i + dp, Nq))
        end
        push!(diffs_seen, diff_i)
    end

    return (F, Nq, n_rejected)
end

# ---------------------------------------------------------------
# run_singer_quad_filtered_comparison: embedded in real N, same
# harness shape as run_singer_paired_comparison for direct comparison
# against raw embedded-Singer, paired-Singer, and greedy.
# ---------------------------------------------------------------

"""
    run_singer_quad_filtered_comparison(; Ns, target_q_exponent, m_per_point,
                                           m_scaling, m_floor, m_cap, seed)

Same structure as run_singer_paired_comparison, but F is built via
singer_quad_filtered_subset (native-order Singer walk with the
incremental 8th-moment-style sum-of-differences filter) instead of
raw D or paired-sums D. Re-verifies Sidon-ness of the embedded F
against the REAL target N via sidon_defect (not assumed). Also
reports n_rejected from the filtering step and the resulting B=|F|,
which can differ across N (and across seeds at fixed N) since both
the rejection rate and the random partner draws are stochastic.

Uses the SAME seed convention as the other comparison functions in
this file (fresh MersenneTwister(seed) per N).
"""
function run_singer_quad_filtered_comparison(; Ns::Vector{Int} = [10_007, 100_003, 1_000_003, 10_000_019],
                                                 target_q_exponent::Float64 = 0.2,
                                                 m_per_point::Int = 20_000,
                                                 m_scaling::Symbol = :sqrt_N,
                                                 m_floor::Int = 2_000,
                                                 m_cap::Int = typemax(Int),
                                                 seed::Int = 1)
    N0 = Float64(first(Ns))
    results = NamedTuple[]

    println("\n=== Singer QUAD-FILTERED (native order + 8th-moment-style filter), " *
            "embedded in real target N (target_q_exponent=$target_q_exponent) ===")
    println("N\tq\tNq\tB(=|F|)\trejected\tm\tratio(MC/flat, vs N)\tmax|U|\tsidon_defect(mod N)\telapsed_s")
    for N in Ns
        q_target = max(2, floor(Int, N^target_q_exponent))
        q_target = min(q_target, N)
        q = largest_prime_leq(q_target)
        rng = MersenneTwister(seed)
        F_int, Nq, n_rejected = singer_quad_filtered_subset(q, rng)
        B = length(F_int)

        if Nq > N
            @warn "N=$N, q=$q: Nq=$Nq exceeds N -- skipping this point " *
                  "(target_q_exponent=$target_q_exponent too large for this N)"
            continue
        end

        # Same wraparound caveat as singer_paired_sidon_subset /
        # run_singer_embedded_comparison: F's representatives live in
        # [0, Nq-1], so this only needs Nq <= N to embed without
        # relabeling (values themselves don't change), but Sidon-ness
        # of F under mod N is re-checked directly below rather than
        # assumed, since this filter's guarantee (no bugs in the
        # filter logic) is about mod Nq, not mod N.
        defect = sidon_defect(F_int, N)
        if defect != 0
            @warn "N=$N, q=$q (Nq=$Nq): quad-filtered Singer subset has nonzero " *
                  "sidon_defect=$defect when checked mod N -- unexpected, since the " *
                  "ordinary Sidon filter was enforced mod Nq and Nq<=N should not " *
                  "introduce new collisions; investigate before trusting this row"
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

        F = [[x] for x in F_int]
        t0 = time()
        result = run_character_sampler_threaded(G_for(N), F; m = m, seed = seed,
                                                   k_size = N, report_every = typemax(Int))
        elapsed = time() - t0

        Bf = Float64(B)
        flat = (Bf^8) / N
        ratio = result.M8_running[end] / flat
        maxU = maximum(abs.(result.U_vals))

        @printf("%d\t%d\t%d\t%d\t%d\t\t%d\t%.4f\t%.4f\t%d\t%.2f\n",
                N, q, Nq, B, n_rejected, m, ratio, maxU, defect, elapsed)

        push!(results, (; N, q, Nq, B, n_rejected, m, ratio, maxU, defect, elapsed))
    end

    if length(results) >= 2
        println("\n--- Singer-quad-filtered growth-exponent fit (vs real N) ---")
        fit_rows = [(; N = r.N, B = r.B, m = r.m, ratio = r.ratio,
                       maxU = r.maxU, defect = r.defect, elapsed = r.elapsed)
                    for r in results]
        fit = fit_growth_exponent(fit_rows)
        if length(fit_rows) >= 3
            local_growth_exponents(fit_rows)
        end
        return (; results, fit)
    end

    return (; results, fit = nothing)
end

# ---------------------------------------------------------------
# run_singer_quad_filtered_exponent_sweep: does the quad filter do
# anything once Nq is large enough for its collision space to have
# real crowding?
# ---------------------------------------------------------------
#
# WHY THIS EXISTS: at target_q_exponent=0.2 (the real constraint),
# Nq is tiny (e.g. 31, 57, 183, 553 across this sweep's Ns) and B is
# correspondingly tiny (B ~ N^0.2, so single digits to low twenties).
# The quad filter's collision check operates on a space of size Nq,
# and with only ~B quad-sums ever generated (one per accepted
# element), there is essentially no chance of a collision when Nq is
# already comparable to or larger than B -- the filter has nothing to
# bite on at this scale, which is exactly what the first
# run_singer_quad_filtered_comparison run showed (0-9 rejections out
# of a few dozen candidates, and a fitted gamma slightly WORSE than
# unfiltered embedded-Singer at the same exponent).
#
# This does NOT mean the filter idea is dead -- it means 0.2 is a
# regime where it structurally cannot be tested, since the collision
# space it checks is too roomy relative to how few elements exist to
# fill it. This sweep raises target_q_exponent (same values as
# run_singer_embedded_exponent_sweep: 0.2 up to 0.45) purely to see
# whether, once Nq and B both grow, quad-sum collisions start
# happening often enough for the filter to actually reject a
# meaningful fraction of candidates and produce a DIFFERENT gamma than
# the unfiltered embedded-Singer baseline at the same exponent.
#
# STILL DIAGNOSTIC, NOT A NEW FACTOR-BASE PROPOSAL, for the same
# reason run_singer_embedded_exponent_sweep is diagnostic: the real
# problem fixes target_q_exponent=0.2 given B ~ p^(2/5) ~ N^0.2 with
# N ~ p^2. Exponents above 0.2 here are not an available choice --
# they exist only to locate where (if anywhere) the filter mechanism
# starts to have teeth, so you can judge whether the mechanism is
# fundamentally toothless or just being tested in the wrong regime.

"""
    run_singer_quad_filtered_exponent_sweep(; Ns, exponents, kwargs...)

Runs run_singer_quad_filtered_comparison once per exponent in
`exponents` (same default range as run_singer_embedded_exponent_sweep:
0.2 up to 0.45), prints each full block via the existing per-exponent
function, then prints a compact summary table of (exponent, fitted
gamma, fitted C, R^2, and total rejections summed across all Ns at
that exponent) so you can see both the gamma trend AND whether the
filter's rejection rate actually grows with exponent (it should, if
"Nq too small relative to B" is really why it did nothing at 0.2).

kwargs are forwarded to each run_singer_quad_filtered_comparison call
(e.g. Ns, m_per_point, seed).
"""
function run_singer_quad_filtered_exponent_sweep(; Ns::Vector{Int} = [10_007, 100_003, 1_000_003, 10_000_019],
                                                     exponents::Vector{Float64} = [0.2, 0.3, 0.4, 0.45],
                                                     kwargs...)
    println("\n############################################################")
    println("# SINGER QUAD-FILTERED EXPONENT SWEEP -- DIAGNOSTIC ONLY")
    println("# Real factor-base constraint is target_q_exponent=0.2")
    println("# (B ~ p^(2/5) ~ N^0.2 given N ~ p^2). Exponents above 0.2")
    println("# below are NOT valid factor-base choices -- they exist only")
    println("# to check whether the quad filter starts rejecting a")
    println("# meaningful fraction of candidates once Nq/B grow, i.e.")
    println("# whether target_q_exponent=0.2 is just too small a regime")
    println("# for this filter to have any effect, rather than the filter")
    println("# being fundamentally inert.")
    println("############################################################")

    summary = NamedTuple[]
    for exp in exponents
        run = run_singer_quad_filtered_comparison(; Ns = Ns, target_q_exponent = exp, kwargs...)
        total_rejected = isempty(run.results) ? 0 : sum(r.n_rejected for r in run.results)
        total_candidates = isempty(run.results) ? 0 : sum(r.B + r.n_rejected for r in run.results)
        reject_frac = total_candidates > 0 ? total_rejected / total_candidates : 0.0
        if run.fit !== nothing
            push!(summary, (; target_q_exponent = exp, run.fit.gamma, run.fit.C, run.fit.r2,
                               total_rejected, total_candidates, reject_frac))
        else
            @warn "target_q_exponent=$exp: fewer than 2 successful points, skipped in summary"
        end
    end

    if !isempty(summary)
        println("\n=== Sweep summary: gamma AND rejection rate vs. target_q_exponent ===")
        println("(if the filter is only toothless at small Nq/B, reject_frac should",
                " rise with exponent -- if it stays near 0 throughout, the filter is",
                " not just under-tested at 0.2, it is not discriminating at any scale probed here)")
        println("target_q_exponent\tfitted_gamma\tfitted_C\tR^2\treject_frac\t(rejected/total)")
        for s in summary
            @printf("%.3f\t\t\t%.4f\t\t%.4e\t%.4f\t%.4f\t\t(%d/%d)\n",
                    s.target_q_exponent, s.gamma, s.C, s.r2, s.reject_frac,
                    s.total_rejected, s.total_candidates)
        end
        println("\nFor reference, the REAL constraint (target_q_exponent=0.2) is the",
                " first row above -- everything past it is diagnostic extrapolation,",
                " not an available choice given B ~ p^(2/5). Compare each row's gamma",
                " against the UNFILTERED embedded-Singer gamma at the same exponent",
                " (see run_singer_embedded_exponent_sweep's summary) to judge whether",
                " the filter is doing anything once it has room to.")
    end

    return summary
end

# ---------------------------------------------------------------
# Strategy 7 (v3): greedy construction scored by a fixed random
# character projection of the 8th moment
# ---------------------------------------------------------------
#
# HISTORY, v1 -> v2 -> v3:
#
# v1 (spectral_swap_search, discarded): scored Sidon-preserving swaps
# via a LINEARIZED gradient of sum_chi |S_chi|^8 restricted to a
# frozen set of "bad" Fourier modes. Made the full-spectrum ratio
# WORSE in 2 of 3 tested N's and stalled at the third -- traced to (1)
# a frozen mode subset with no transfer guarantee to the full
# spectrum, and (2) the linearization itself being invalid when
# |S_chi| ~ O(sqrt(B)).
#
# v2 (pairsum_swap_search, discarded): replaced the linearized
# surrogate with an EXACT O(B)-per-swap objective, sum_t r(t)^2 (the
# pair-sum energy, exactly equal to M4). Implementation was verified
# correct (score_swap matches brute-force recomputation to the last
# integer, r is restored byte-for-byte after every trial). The
# objective itself, however, turned out to be USELESS for this
# purpose: for a Sidon set of fixed size B, every pairwise sum is
# either a self-pair (contributing r=1, B of them) or a two-way
# collision of an ordered cross-pair (contributing r=2,
# C(B,2) of them) -- Sidon-ness alone forces this multiset of r
# VALUES for every Sidon set of size B, giving the closed form
#   sum_t r(t)^2 = B*1^2 + C(B,2)*2^2 = 2B^2 - B,
# a constant depending only on B, not on which B elements are chosen.
# So M4 has literally zero degrees of freedom across the entire
# Sidon-preserving search space -- n_accepted=0 at every N tested was
# not a bug, it was the only mathematically possible outcome of that
# search. (Verified both symbolically and by exhaustive candidate
# enumeration against brute-force pairsum_energy recomputation; see
# chat.) The lesson generalizes: any Sidon-preserving local-search
# objective needs to depend on WHERE the occupied sums/differences
# land, not just on their multiplicities, since Sidon-ness already
# pins the multiplicity multiset.
#
# v3 (THIS FILE): abandons "optimize after construction" (local
# search over swaps of a completed Sidon set) in favor of "spend the
# quadratic budget during construction" -- built sequentially, the
# same way greedy_sidon_subset is, except at each step the candidate
# is chosen not as the first Sidon-valid one but as the Sidon-valid
# one that minimizes a SAMPLED, EXACT (not linearized) 8th-moment
# score against a FIXED set of K random characters, sampled once at
# the very start and never adapted to the growing F (same fix as
# v1's frozen-mode problem, but for an unbiased random Omega instead
# of a frozen bad-mode Omega, so there's no "optimized for the modes
# I'm watching, ignored everywhere else" failure mode -- a uniformly
# random Omega is an unbiased estimator of the FULL M8 sum in
# expectation, at any point during construction).
#
# COMPLEXITY, STATED HONESTLY: with |Omega| = K held as a FIXED
# CONSTANT (not scaled with B), each of the B construction stages
# scores O(B) candidates (the shuffled-order Sidon-candidate stream,
# same as greedy_sidon_subset) at O(K) = O(1) per candidate (K fixed
# characters, updating each S_chi from the candidate's phase is O(1)
# per character), giving O(B^2 * K) = O(B^2) total with K folded into
# the constant. This is the HONEST version of the "O(B^2) budget"
# claim: it holds because K is fixed, not because scoring against
# Theta(B) characters is free -- scoring against Theta(B) characters
# at every one of the B stages would cost O(B^3), which was flagged
# and explicitly rejected in favor of fixed K (see chat).
#
# WHAT THIS IS NOT: this is still an untested proxy, same discipline
# as every other strategy in this file -- a K-character random
# projection is an unbiased ESTIMATE of the full M8 sum, not M8
# itself, and greedily minimizing an estimate at each of B
# sequential steps has no theorem attached guaranteeing the final
# F's TRUE (character-sampler-measured) M8 ratio improves over plain
# greedy_sidon_subset. That is exactly what
# run_projected_greedy_comparison measures, with the same
# multi-seed noise-floor discipline as the discarded v2 comparison.

"""
    sample_fixed_characters(N::Int, K::Int, rng::AbstractRNG) -> Vector{Int}

Draws K distinct nonzero residues mod N, uniformly at random, to serve
as the fixed character set Omega = {chi_k(x) = exp(2*pi*i*k*x/N) : k in
result}. Sampled ONCE per construction run and never refreshed --
deliberately unbiased and independent of the growing F, unlike v1's
frozen "worst modes" set (which was itself derived from F and hence
could miss modes that only became bad later in the search).
"""
function sample_fixed_characters(N::Int, K::Int, rng::AbstractRNG)
    K = min(K, N - 1)
    ks = Set{Int}()
    attempts = 0
    while length(ks) < K && attempts < 20 * K + N
        k = rand(rng, 1:(N-1))
        push!(ks, k)
        attempts += 1
    end
    if length(ks) < K
        @warn "sample_fixed_characters: could only draw $(length(ks)) distinct " *
              "characters (wanted $K) after exhausting the attempt budget -- " *
              "proceeding with the smaller set rather than looping indefinitely"
    end
    return collect(ks)
end

"""
    projected_m8_score(S_vec::Vector{ComplexF64}) -> Float64

Exact (not linearized) sum_{chi in Omega} |S_chi|^8 given the current
S_chi values for every chi in Omega. O(K) per call.
"""
function projected_m8_score(S_vec::Vector{ComplexF64})
    s = 0.0
    @inbounds for S in S_vec
        s += abs2(S)^4
    end
    return s
end

"""
    projected_greedy_sidon_subset(N, target_size, rng; K=200,
                                    n_probe_multiplier=4) -> (F, Omega, final_score)

Sequential Sidon-set construction (same skeleton as
greedy_sidon_subset: shuffle a candidate stream, keep Sidon-compatible
ones, stop at target_size) EXCEPT at each of the `target_size` stages,
instead of taking the first Sidon-compatible candidate encountered,
this scans the FULL remaining candidate pool for Sidon-compatible
candidates, scores up to `n_probe_multiplier * target_size` of them by
the EXACT projected M8 score (sum over the K fixed characters in Omega
of |S_chi + phase of candidate|^8), and takes the minimizer -- i.e. it
greedily minimizes a sampled, unbiased proxy for the full 8th moment
at construction time, rather than refining a completed Sidon set
afterward (see file header for why refinement of a completed Sidon
set is dead for the M4 proxy, and why construction avoids that
specific trap).

CANDIDATE-POOL BOOKKEEPING (fixed after an earlier draft of this
function got this wrong -- see chat): every stage scans the ENTIRE
remaining pool to identify which candidates are still Sidon-valid
(permanently dropping ones that collide with the current sums_seen,
since sums_seen only grows and a rejected candidate never becomes
valid again), but only SCORES (evaluates the projected M8 for) the
first `n_probe_multiplier * target_size` valid ones found each stage,
to bound per-stage cost. Valid candidates beyond that scoring cap are
kept in the pool for future stages rather than being silently
discarded. An earlier draft discarded unscored-but-valid candidates
at the end of every stage's scan, which caused the entire N-sized
candidate space to be exhausted after only ~target_size/n_probe_multiplier
stages instead of target_size stages -- confirmed by direct trace (see
chat) and fixed here.

NOTE ON MAXIMAL-BUT-NOT-MAXIMUM SIDON SETS: even with that bookkeeping
fixed, this function (like greedy_sidon_subset itself) is not
guaranteed to reach target_size -- greedy Sidon construction can paint
itself into a corner where the partial set is a MAXIMAL Sidon set
(no candidate anywhere in Z/N extends it) short of the requested size,
purely because of which elements got picked early on, independent of
implementation correctness. Verified directly (see chat): a stuck run
was checked by exhaustively testing every residue in Z/N as a
candidate extension of the partial F, not just the tracked candidate
pool, confirming zero valid extensions existed anywhere -- a genuine
dead end, not a pool-bookkeeping artifact. This is a known intrinsic
risk of ANY greedy Sidon construction (plain greedy_sidon_subset is
just as exposed to it, only less likely to hit it on any particular
seed since its candidate ORDER differs). Callers should treat
length(F) < target_size as a real possible outcome, not assume it
indicates a bug.

Omega (the K fixed characters) is sampled ONCE at the very start via
sample_fixed_characters and never changes during construction. S_chi
for every chi in Omega is maintained incrementally (O(K) update per
accepted element, not recomputed from scratch each stage) as running
complex sums.

COST: up to `target_size` stages, each scanning the remaining pool
(shrinking over time, same order of magnitude as greedy_sidon_subset's
per-stage scan) but scoring at most n_probe_multiplier*target_size
candidates at O(K) per candidate (K fixed, see file header) -- the
scoring cost is O(B^2 * K) = O(B^2) total with K folded into the
constant; the Sidon-validity scan itself is the same order of total
work greedy_sidon_subset already does.

THREADED: the per-stage batch-scoring step (the O(B^2*K) part) is
parallelized across Threads.nthreads() via Threads.@spawn -- each
candidate's trial score is independent (only reads S_vec/Omega, no
writes until the stage's winner is chosen), so it's an embarrassingly
parallel map, followed by a cheap serial reduction to find the
minimizer. The Sidon-validity scan (finding which pool candidates are
still valid) remains serial -- it mutates `sums_seen`-derived state
incrementally per candidate within a stage and is a smaller share of
total cost than scoring at realistic K. Requires Julia started with
multiple threads (`julia -t auto` or `-t N`, N>1) to actually run in
parallel; falls back to correct but single-core behavior otherwise
(see the nthreads()==1 warning below).

Returns (F::Vector{Int}, Omega::Vector{Int}, final_score::Float64)
where final_score is the EXACT projected M8 score (over Omega only,
not the full spectrum) of the returned F -- NOT sampled/noisy, since
Omega and every S_chi are tracked exactly throughout construction.
"""
function projected_greedy_sidon_subset(N::Int, target_size::Int, rng::AbstractRNG;
                                          K::Int = 200,
                                          n_probe_multiplier::Int = 4,
                                          pool_refill_factor::Int = 3)
    if Threads.nthreads() == 1
        @warn "nthreads() == 1 -- Julia was not started with multiple threads, so the " *
              "batch-scoring loop below will run on one core despite being threaded code " *
              "(this is what was reported hanging). Restart with `julia -t auto` (or " *
              "`-t N` for N>1) to actually use multiple threads."
    end
    Omega = sample_fixed_characters(N, K, rng)
    nK = length(Omega)
    S_vec = zeros(ComplexF64, nK)

    F = Int[]
    sums_seen = Set{Int}()

    max_probe_per_stage = max(1, n_probe_multiplier * target_size)
    # BOUNDED POOL (fixes an O(N*B) per-stage scan -- see chat: the
    # previous version rescanned the ENTIRE remaining N-sized tail
    # every stage to find Sidon-valid candidates, giving O(N*B) total
    # work, which is what hung at N=10_000_019. That rescan bought
    # nothing: candidates far back in the shuffle are exchangeable
    # with candidates near the front (the shuffle is uniform), so
    # there is no reason to keep an O(N)-sized queue alive when only
    # a probe-sized pool is ever scored. Fix: draw a bounded pool of
    # `pool_refill_factor * max_probe_per_stage` FRESH, not-yet-seen
    # residues at a time from a shuffled stream, refilling only when
    # the live pool is exhausted (i.e. amortized, not every stage).
    # This makes per-stage work O(pool size) = O(target_size), and
    # total work O(target_size^2) = O(B^2), matching the stated
    # budget, instead of O(N*B).
    pool_size_target = max(1, pool_refill_factor * max_probe_per_stage)
    stream = collect(0:(N-1))
    Random.shuffle!(rng, stream)
    stream_pos = 0  # index of the last element of `stream` already drawn
    pool = Int[]

    refill!() = begin
        need = pool_size_target - length(pool)
        take = min(need, length(stream) - stream_pos)
        if take > 0
            append!(pool, @view stream[(stream_pos+1):(stream_pos+take)])
            stream_pos += take
        end
    end
    refill!()

    while length(F) < target_size
        if isempty(pool)
            break  # exhausted the entire shuffled stream with zero remaining valid candidates
        end

        # Scan only the current (bounded) pool for Sidon-validity --
        # O(pool size * |F|) per stage instead of O(N * |F|).
        batch = Int[]
        batch_new_sums = Vector{Int}[]
        kept_pool = Int[]  # valid-but-unscored survivors, stay in the pool
        for x in pool
            ok = true
            new_sums = Int[]
            for y in F
                s = mod(x + y, N)
                if s in sums_seen
                    ok = false
                    break
                end
                push!(new_sums, s)
            end
            if ok
                s2 = mod(2x, N)
                if s2 in sums_seen
                    ok = false
                else
                    push!(new_sums, s2)
                end
            end
            if !ok
                continue  # permanently invalid (sums_seen only grows), drop from pool entirely
            end
            if length(batch) < max_probe_per_stage
                push!(batch, x)
                push!(batch_new_sums, new_sums)
            else
                push!(kept_pool, x)  # valid, just not scored this round
            end
        end
        pool = kept_pool

        if isempty(batch)
            refill!()
            if isempty(pool)
                break  # stream exhausted too, genuinely no valid candidates anywhere left to try
            end
            continue
        end

        # Score every candidate in the batch by the EXACT resulting
        # projected M8 (over the fixed Omega), choosing the minimizer.
        # No mutation of the real S_vec happens until the winner is
        # chosen, so this is a pure trial, same discipline as v2's
        # score_swap trial-without-committing pattern.
        #
        # THREADED (previously a single serial for-loop -- this is
        # the O(B^2*K) budget's actual cost, and it was all running on
        # one core; see chat, this was reported hanging at N=10^6+
        # scale). Each candidate's trial score only READS S_vec/Omega
        # (no writes until the winner is chosen after the loop), so
        # scoring the batch is embarrassingly parallel: split `batch`
        # into nthreads() STATIC, CONTIGUOUS chunks and @spawn one task
        # per chunk, each writing only to its own slice of preallocated
        # trial_scores/trial_phases arrays -- same discipline as
        # run_character_sampler_threaded in character_sampler.jl (never
        # index anything by threadid(), since that is unsafe under
        # Julia's >=1.9 dynamic scheduler; tie each task to its own
        # chunk/closure instead). No RNG is used in this loop, so
        # there's no analogous per-task-RNG concern here -- purely a
        # read-many/write-disjoint parallel map, followed by a cheap
        # serial O(batch size) reduction to find the minimizer.
        nb = length(batch)
        trial_scores = Vector{Float64}(undef, nb)
        trial_phases = Vector{Vector{ComplexF64}}(undef, nb)

        nt = Threads.nthreads()
        chunk_bounds = let
            bounds = Vector{UnitRange{Int}}(undef, nt)
            base, rem = divrem(nb, nt)
            lo = 1
            for t in 1:nt
                len = base + (t <= rem ? 1 : 0)
                bounds[t] = lo:(lo + len - 1)
                lo += len
            end
            bounds
        end

        tasks = Vector{Task}(undef, nt)
        for t in 1:nt
            range_t = chunk_bounds[t]
            tasks[t] = Threads.@spawn begin
                for i in range_t
                    x = batch[i]
                    trial_score = 0.0
                    phase_x = Vector{ComplexF64}(undef, nK)
                    @inbounds for kk in 1:nK
                        k = Omega[kk]
                        ph = cis(2pi * k * x / N)
                        phase_x[kk] = ph
                        trial_score += abs2(S_vec[kk] + ph)^4
                    end
                    trial_scores[i] = trial_score
                    trial_phases[i] = phase_x
                end
            end
        end
        foreach(wait, tasks)

        best_i = argmin(trial_scores)
        best_phase = trial_phases[best_i]

        x_chosen = batch[best_i]
        push!(F, x_chosen)
        union!(sums_seen, batch_new_sums[best_i])
        unused_batch = [batch[j] for j in eachindex(batch) if j != best_i]
        pool = vcat(unused_batch, pool)
        @inbounds for kk in 1:nK
            S_vec[kk] += best_phase[kk]
        end

        length(pool) < pool_size_target && refill!()
    end

    if length(F) < target_size
        @warn "projected_greedy_sidon_subset: only built |F|=$(length(F)) " *
              "(wanted target_size=$target_size) -- either the bounded pool never " *
              "contained enough simultaneously-valid candidates, or (rarely) the " *
              "partial Sidon set became genuinely maximal. Proceeding with the " *
              "smaller set. Try a larger pool_refill_factor if this triggers often."
    end

    final_score = projected_m8_score(S_vec)
    return (F, Omega, final_score)
end

# ---------------------------------------------------------------
# run_projected_greedy_comparison: builds via BOTH plain
# greedy_sidon_subset (baseline) and projected_greedy_sidon_subset
# (this file), measures both with the usual character sampler --
# INCLUDING MULTIPLE INDEPENDENT SAMPLER SEEDS PER (N, baseline/
# projected) SO THE COMPARISON HAS A VISIBLE NOISE FLOOR, same
# discipline as the discarded v2 comparison (see its header comment
# for why this matters: a single-seed before/after ratio has no way
# to distinguish a real effect from Monte Carlo noise).
# ---------------------------------------------------------------

"""
    run_projected_greedy_comparison(; Ns, m_per_point, m_scaling, m_floor,
                                       m_cap, seed, K, n_probe_multiplier,
                                       n_sampler_seeds)

For each N: builds F_baseline via greedy_sidon_subset and
F_projected via projected_greedy_sidon_subset (SAME underlying RNG
stream up to the point their candidate orders diverge -- both start
from `MersenneTwister(seed)`, so any difference in outcome is
attributable to the construction rule, not to different random
candidate orderings, to the extent the two constructions' RNG
consumption stays aligned; see caveat in the function body), then
runs `n_sampler_seeds` INDEPENDENT character-sampler measurements
(different seeds) for each, reporting mean and standard error of the
ratio for both so the comparison carries a visible confidence
interval instead of a single noisy point estimate.

Also reports the EXACT projected-M8 score (over Omega only, from
projected_greedy_sidon_subset's own bookkeeping) for the projected
construction -- not sampled/noisy, confirms the construction achieved
what it was actually optimizing, independent of whether that
transfers to the TRUE (full-spectrum, character-sampler-measured) M8
ratio.
"""
function run_projected_greedy_comparison(; Ns::Vector{Int} = [10_007, 100_003, 1_000_003, 10_000_019],
                                            m_per_point::Int = 20_000,
                                            m_scaling::Symbol = :sqrt_N,
                                            m_floor::Int = 2_000,
                                            m_cap::Int = typemax(Int),
                                            seed::Int = 1,
                                            K::Int = 200,
                                            n_probe_multiplier::Int = 4,
                                            n_sampler_seeds::Int = 5)
    N0 = Float64(first(Ns))
    results = NamedTuple[]

    println("\n=== Projected greedy construction (K=$K fixed random characters), " *
            "baseline=greedy_sidon_subset, $n_sampler_seeds independent sampler seeds per point ===")
    println("N\tB\tm\tprojM8_score(exact)\t" *
            "ratio_baseline(mean±se)\tratio_projected(mean±se)\tdefect_proj\telapsed_s")
    for N in Ns
        B = round(Int, N^0.4)

        # NOTE ON RNG ALIGNMENT: F_baseline is built from
        # MersenneTwister(seed). F_proj is built from a DIFFERENT,
        # offset seed (seed + 1_000_000*attempt, see retry loop below)
        # -- both to allow retries on a maximal-Sidon dead end and
        # because projected_greedy_sidon_subset draws Omega from its
        # rng before touching the candidate stream, so the two
        # constructions' candidate orders were never going to align
        # element-for-element anyway. "seed" here buys run-to-run
        # determinism/reproducibility, not a shared candidate
        # ordering between baseline and projected -- flagged directly
        # rather than implying a tighter match than actually holds.
        rng_baseline = MersenneTwister(seed)
        F_baseline = greedy_sidon_subset(N, B, rng_baseline)
        @assert length(F_baseline) == B "greedy baseline returned |F|=$(length(F_baseline)), expected B=$B"
        @assert sidon_defect(F_baseline, N) == 0 "greedy baseline is not Sidon -- cannot proceed"

        # projected_greedy_sidon_subset can legitimately land on a
        # MAXIMAL (but not maximum) Sidon set short of target_size B
        # -- an intrinsic risk of greedy Sidon construction, not a
        # bug (see that function's docstring for the direct
        # verification that this is a genuine dead end, not a
        # candidate-pool bookkeeping artifact). Retry with a fresh
        # seed derivative a bounded number of times before giving up,
        # rather than crashing the whole multi-N sweep on one unlucky
        # draw.
        F_proj = Int[]
        Omega = Int[]
        proj_score = NaN
        build_elapsed = 0.0
        max_retries = 5
        for attempt in 1:max_retries
            rng_proj = MersenneTwister(seed + 1_000_000 * attempt)
            t0 = time()
            F_proj, Omega, proj_score = projected_greedy_sidon_subset(
                N, B, rng_proj; K = K, n_probe_multiplier = n_probe_multiplier)
            build_elapsed = time() - t0
            length(F_proj) == B && break
            @warn "N=$N: projected greedy build attempt $attempt landed on a " *
                  "maximal Sidon set of size $(length(F_proj)) < B=$B -- retrying " *
                  "with a fresh RNG draw (attempt $(attempt+1)/$max_retries)"
        end
        @assert length(F_proj) == B "projected greedy failed to reach target_size=$B " *
            "after $max_retries retries (last attempt returned |F|=$(length(F_proj))) -- " *
            "this many consecutive maximal-Sidon dead ends is unusual, investigate " *
            "before trusting this N"
        defect_proj = sidon_defect(F_proj, N)
        if defect_proj != 0
            @warn "N=$N: projected-greedy F has nonzero sidon_defect=$defect_proj -- " *
                  "this should be impossible (projected_greedy_sidon_subset only ever " *
                  "accepts Sidon-preserving candidates); investigate before trusting this row"
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

        F_baseline_wrapped = [[x] for x in F_baseline]
        F_proj_wrapped = [[x] for x in F_proj]

        t_sample_start = time()
        ratios_baseline = Float64[]
        ratios_proj = Float64[]
        for s in 1:n_sampler_seeds
            sampler_seed = seed * 1_000_003 + s   # distinct, deterministic per (seed, s)
            res_b = run_character_sampler_threaded(G_for(N), F_baseline_wrapped; m = m,
                                                      seed = sampler_seed, k_size = N,
                                                      report_every = typemax(Int))
            push!(ratios_baseline, res_b.M8_running[end] / flat)
            res_p = run_character_sampler_threaded(G_for(N), F_proj_wrapped; m = m,
                                                      seed = sampler_seed, k_size = N,
                                                      report_every = typemax(Int))
            push!(ratios_proj, res_p.M8_running[end] / flat)
        end
        sample_elapsed = time() - t_sample_start

        mean_baseline = mean(ratios_baseline)
        mean_proj = mean(ratios_proj)
        se_baseline = n_sampler_seeds > 1 ? std(ratios_baseline) / sqrt(n_sampler_seeds) : NaN
        se_proj = n_sampler_seeds > 1 ? std(ratios_proj) / sqrt(n_sampler_seeds) : NaN

        elapsed = build_elapsed + sample_elapsed

        @printf("%d\t%d\t%d\t%.4e\t\t%.4f±%.4f\t\t%.4f±%.4f\t\t%d\t\t%.2f\n",
                N, B, m, proj_score,
                mean_baseline, se_baseline, mean_proj, se_proj,
                defect_proj, elapsed)

        push!(results, (; N, B, m, proj_score,
                           mean_baseline, se_baseline, mean_proj, se_proj,
                           ratios_baseline, ratios_proj,
                           defect_proj, elapsed))
    end

    println("\n--- Significance check: is (projected - baseline) outside a 2-standard-error band? ---")
    println("N\tmean_projected - mean_baseline\tcombined_2se\toutside_2se_band?")
    for r in results
        diff = r.mean_proj - r.mean_baseline
        combined_2se = 2 * sqrt(r.se_baseline^2 + r.se_proj^2)
        outside = !isnan(combined_2se) && abs(diff) > combined_2se
        @printf("%d\t%.4f\t\t\t\t\t%.4f\t\t%s\n", r.N, diff, combined_2se,
                outside ? "YES (likely real)" : "no (within noise)")
    end
    if n_sampler_seeds < 3
        @warn "n_sampler_seeds=$n_sampler_seeds is too few for the standard-error " *
              "estimates above to be trustworthy themselves -- use at least 5-10 " *
              "for a meaningful noise-floor check, this default/call used fewer"
    end

    if length(results) >= 2
        println("\n--- Projected-greedy growth-exponent fit (mean ratio vs real N) ---")
        fit_rows = [(; N = r.N, B = r.B, m = r.m, ratio = r.mean_proj,
                       maxU = 0.0, defect = r.defect_proj, elapsed = r.elapsed)
                    for r in results]
        fit = fit_growth_exponent(fit_rows)
        println("\n--- For comparison, plain greedy_sidon_subset fit (mean ratio) ---")
        fit_rows_baseline = [(; N = r.N, B = r.B, m = r.m, ratio = r.mean_baseline,
                                 maxU = 0.0, defect = 0, elapsed = r.elapsed)
                              for r in results]
        fit_baseline = fit_growth_exponent(fit_rows_baseline)
        return (; results, fit, fit_baseline)
    end

    return (; results, fit = nothing, fit_baseline = nothing)
end

# ---------------------------------------------------------------
# Strategy 8: Fourier-peak pruning of a completed Singer set
# ---------------------------------------------------------------
#
# RESULT (measured, this session -- see chat for full output): tested
# at target_q_exponent in {0.2, 0.4}, q in {5, 7, 251, 331}, this
# does NOT help. normalized_ratio (the per-element shape effect, with
# the trivial B-shrinkage divided out -- see peak_pruned_subset and
# run_singer_peak_pruned_comparison docstrings) came back CONSISTENTLY
# ABOVE 1 at all four tested points (1.38, 1.16, 1.06, 1.07 as q grows
# 5->7->251->331) -- i.e. the elements pruning REMOVES are, on a
# per-element basis, LESS peak-heavy than the elements it KEEPS behind:
# pruning makes the survivors' average worse, not better, the opposite
# of the intended effect. Two things about the trend are worth stating
# precisely: (1) the effect is consistently signed the wrong way, not
# noisy/mixed like the projected-greedy comparison above -- all four
# points agree; (2) normalized_ratio is APPROACHING 1 from above as q
# grows (1.38 -> 1.16 -> 1.06 -> 1.07), not diverging further from it
# or crossing below it -- consistent with the effect shrinking toward
# "no effect" at larger scale, not with a real signal that just needed
# more data to surface. Taken together this joins new_invariants.jl's
# five cheap-proxy results (section 10.2) and Strategy 7's v1 as
# another proxy that, once actually measured against the true
# character-sampler/exact-DFT M8, does not do what its construction
# suggested it should -- see peak_score's docstring below for the
# likely reason (it is a phase-collapsed heuristic, not a derived
# first-order M8 gradient, so there was never a proof it should point
# the right direction; this is exactly the kind of gap that measuring
# was supposed to catch, and did).
#
# USER'S IDEA (relayed from an external model, this session): rather
# than changing HOW D is built (Strategies 4-7 above all vary the
# construction), take the native Singer set D as-is and PRUNE it
# after the fact -- compute the exact top-top_frac Fourier peaks
# K_peak (via top_k_peaks, same ranking full_spectrum_diagnostic
# already uses diagnostically), score each x in D by its marginal
# contribution to that peak mass via the exact first-order derivative
# of sum_{k in K_peak} |S_hat(k)|^8 with respect to removing x,
#
#   grad(x) = sum_{k in K_peak} |S_hat(k)|^6 * cos(2*pi*k*x/N + arg(S_hat(k))),
#
# and drop the top `prune_frac` of D by grad(x) (highest grad(x) = x
# contributes most to shrinking M8_restricted if removed, so these are
# the ones pruned -- see peak_score's docstring for the sign
# convention and full derivation, and for the phase-collapsed
# predecessor of this score, which is superseded).
#
# WHY THIS IS A DIFFERENT KIND OF EXPERIMENT THAN 10.2's FIVE CHEAP
# PROXIES (see genus2-index-calculus-advisory-6.md section 10.2, and
# new_invariants.jl): those were all O(B^2)-BUDGET INCREMENTAL SCORES
# computed DURING construction, deliberately cheap because they had to
# run inside a B-stage greedy loop. This is different in kind, not
# degree: it operates on the EXACT full spectrum (an O(N*B) DFT, same
# cost class full_spectrum_diagnostic already pays), which is not
# something an O(B^2) in-loop proxy could ever see -- diff_set_energy
# and pairsum energy were dead on arrival PRECISELY because Sidon-ness
# pins their O(B^2) inputs to a constant (see Strategy 7's v2 history
# above); grad(x) has no such degeneracy, because it depends on WHERE
# elements land relative to the actual peak frequencies, which Sidon-
# ness does not constrain. The tradeoff is cost: this needs the exact
# spectrum, so (like full_spectrum_diagnostic and unlike every other
# strategy in this file) it does NOT scale to the 10^7-point production
# sweep -- it is restricted to the same small-N regime already used for
# the confinement/clustering diagnostics.
#
# HISTORY -- WHY grad(x) NOW USES arg(S_hat(k)), NOT JUST |S_hat(k)|^6:
# the original version of this score was |S_hat(k)|^6 * cos(2*pi*k*x/N),
# a "phase-collapsed" heuristic that treats S_hat(k) as if it were a
# positive real number -- correlating x's own phase with the peak's
# magnitude but ignoring where S_hat(k)'s OWN phase actually sits. A
# run_singer_peak_pruned_topfrac_comparison sweep at top_frac=0.01 vs
# top_frac=1.0 came back with IDENTICAL prunings at both settings (a
# null result on whether widening K_peak matters), which is consistent
# with that score being a weaker, coarser signal than the true
# gradient rather than evidence K_peak's width genuinely doesn't
# matter. peak_score now implements the exact first-order term (see
# its docstring for the derivation) -- the topfrac null result should
# be re-measured against this version before trusting it.
#
# STILL A LINEARIZATION: this is exact for a SINGLE removal with
# everything else in D held fixed; pruning prune_frac of D removes
# many elements at once, and cross terms between simultaneous removals
# are not captured. This is exactly why the comparison harness below
# (like every other strategy here) MEASURES the true,
# character-sampler-independent EXACT M8 before and after pruning
# rather than assuming grad(x) is a valid descent direction at
# anything beyond first order.

"""
    peak_score(x::Int, N::Int, S_hat::Vector{ComplexF64}, K_peak::Vector{Int}) -> Float64

grad(x) = -(1/8) * d(M8_restricted)/d[include x], i.e. the exact
first-order change in sum_{k in K_peak} |S_hat(k)|^8 from adding x to
F, PHASE-CORRECT version:

  grad(x) = sum_{k in K_peak} |S_hat(k)|^6 * cos(2*pi*k*x/N + arg(S_hat(k)))

Derivation: treating S_hat(k), conj(S_hat(k)) as independent,
d|S_hat(k)|^8/d S_hat(k) = 4|S_hat(k)|^6 * conj(S_hat(k)). Removing x
changes S_hat(k) by -exp(2*pi*i*k*x/N), so the real first-order change
in |S_hat(k)|^8 is -8*|S_hat(k)|^6 * Re[conj(S_hat(k)) *
exp(2*pi*i*k*x/N)] = -8*|S_hat(k)|^6 * |S_hat(k)| * cos(2*pi*k*x/N -
arg(S_hat(k))) ... written with +arg(S_hat(k)) above via
conj(S_hat(k)) = |S_hat(k)|*exp(-i*arg(S_hat(k))), so
Re[conj(S_hat(k))*exp(2pi*i*k*x/N)] = |S_hat(k)|*cos(2*pi*k*x/N -
arg(S_hat(k))); the sign convention here matches "high grad(x) =
x reinforces the existing peaks, i.e. removing x would shrink M8",
consistent with peak_pruned_subset pruning the HIGHEST-scoring x's.

PREVIOUS VERSION (superseded): |S_hat(k)|^6 * cos(2*pi*k*x/N), with
no arg(S_hat(k)) phase term -- equivalent to treating S_hat(k) as if
it were a positive real number. That version was flagged in this
file's history as a "phase-collapsed proxy," not a derivative, and a
run_singer_peak_pruned_topfrac_comparison sweep at top_frac=0.01 vs
top_frac=1.0 came back with IDENTICAL rankings (and hence identical
pruning) at both settings -- a null result on whether widening
K_peak changes anything. Since the phase-collapsed score is coarser
than the true gradient (it only sees |S_hat(k)|, not where x's own
phase sits relative to S_hat(k)'s phase), that null result was
plausibly an artifact of the weaker proxy, not evidence that
widening K_peak genuinely doesn't matter. This phase-corrected
version is the true first-order derivative (up to the O(B^2)
second-order cross terms from removing MULTIPLE elements
simultaneously, which no single-element linearization captures) and
supersedes the phase-collapsed one -- re-run the topfrac comparison
against this version before drawing conclusions from the earlier
null result.

O(|K_peak|) per call, same cost as before (one extra angle() call per
k). K_peak need not be a small "top fraction" -- passing every
nonzero frequency (K_peak = 1:(N-1), i.e. calling peak_pruned_subset
with top_frac=1.0) is a valid and meaningful use, answering "how does
x align with the FULL spectrum's mass" rather than just the loudest
1% -- see run_singer_peak_pruned_topfrac_comparison for a direct
comparison of the two.

STILL A LINEARIZATION, NOT A PROOF: this is the exact first-order
term for removing a SINGLE x holding everything else fixed. Pruning
prune_frac of D removes many elements at once, and cross terms
between simultaneously-removed elements are not captured by any
per-element score computed against the ORIGINAL (unpruned) S_hat --
same caveat this file applies to every other proxy; the comparison
harness measures the TRUE exact M8 before/after rather than trusting
this score's ranking is what a greedy one-at-a-time removal would
actually achieve.
"""
function peak_score(x::Int, N::Int, S_hat::Vector{ComplexF64}, K_peak::Vector{Int})
    s = 0.0
    @inbounds for k in K_peak
        Sk = S_hat[k+1]
        mag6 = abs(Sk)^6
        s += mag6 * cos(2pi * k * x / N + angle(Sk))
    end
    return s
end

"""
    peak_pruned_subset(D::Vector{Int}, N::Int; top_frac=0.01, prune_frac=0.05)
        -> (F_pruned::Vector{Int}, K_peak::Vector{Int}, scores::Vector{Float64})

Given a completed Sidon set D subset Z/N (typically a native or
embedded Singer set -- see run_singer_peak_pruned_comparison below for
the intended caller), computes the exact spectrum of D (via
compute_full_spectrum), identifies the top `top_frac` fraction of
non-trivial frequencies by |S_hat(k)|^8 (via top_k_peaks -- this is
K_peak, matching the ranking full_spectrum_diagnostic already reports
diagnostically), scores every x in D by peak_score(x, N, S_hat,
K_peak), and returns D with the top `prune_frac` fraction BY SCORE
removed (highest grad(x) = most "peak-building", per the user's
proposal -- these are dropped, not kept).

PRUNING A SIDON SET IS TRIVIALLY STILL SIDON (removing elements from a
Sidon set cannot create a new pairwise-sum collision), so no re-check
against sidon_defect is mathematically necessary for correctness here
-- unlike every OTHER strategy above, which constructs F by ADDING
elements and must therefore verify Sidon-ness was preserved. The
caller (run_singer_peak_pruned_comparison) verifies it anyway, not
because a defect is possible from pruning itself, but as a blanket
sanity check on D's own construction (same discipline as every other
comparison harness in this file, which never assumes a defect of 0
without checking).

Returns F_pruned (D minus the pruned elements, in D's original
relative order), K_peak (so callers can report how many frequencies
were used), scores (peak_score for every x in D, aligned with D's
order, not just the pruned ones -- lets a caller inspect the full
score distribution if wanted), and frac_of_M8 (the fraction of D's
total |S_hat|^8 mass that K_peak alone accounts for -- see NOTE
below on why this number, not just K_peak's raw size, is what
determines whether top_frac actually changes anything).

NOTE ON top_frac's REAL EFFECT: peak_score weights each frequency by
|S_hat(k)|^6, so if D's spectrum is peaky (a handful of frequencies
carry nearly all the mass -- frac_of_M8 near 1.0 already at small
top_frac), then K_peak's remaining 99% of frequencies at
top_frac=1.0 contribute negligibly to the ^6-weighted sum relative
to the already-included peak frequencies. In that regime,
top_frac=0.01 and top_frac=1.0 can produce near-IDENTICAL score
RANKINGS (and hence identical pruning, identical F_pruned) even
though the raw score magnitudes and wall-clock cost differ --
because sortperm only depends on relative order, not the totals.
This is NOT a bug in top_k_peaks or peak_score (both correctly use
whatever K_peak they're given); it means a head-to-head comparison
of top_frac values is only informative when frac_of_M8 at the
smaller top_frac is meaningfully less than 1.0. Always check
frac_of_M8 before concluding two top_frac settings "agree" or
"disagree" in sign -- agreement may just mean the top_frac=0.01
slice was already ~all the mass.
"""
function peak_pruned_subset(D::Vector{Int}, N::Int; top_frac::Float64 = 0.01, prune_frac::Float64 = 0.05)
    S_hat = compute_full_spectrum(D, N)
    K_peak, _, frac_of_M8 = top_k_peaks(S_hat, N; top_frac = top_frac)

    scores = [peak_score(x, N, S_hat, K_peak) for x in D]

    # SIGN/FIRST-ORDER-CORRECTNESS CHECK: peak_score is only useful if
    # its ranking actually predicts the real effect of removal. Rather
    # than re-deriving the gradient independently (e.g. via a symbolic
    # or sympy-style check external to this pipeline), verify it in
    # place, on data already in hand: pick the single highest-scoring
    # x* in D, recompute the spectrum of D with x* actually removed,
    # and confirm M8_restricted (summed over the SAME K_peak) really
    # did decrease -- this is exactly the claim peak_score's sign
    # convention makes ("highest grad(x) = x contributes most to
    # shrinking M8_restricted if removed"). This costs one extra
    # O(N*B) spectrum computation, same cost class the caller already
    # pays twice (before/after), so it is not a meaningfully more
    # expensive stage to add here.
    if !isempty(D)
        x_star = D[argmax(scores)]
        M8_restricted_before = sum(abs(S_hat[k+1])^8 for k in K_peak)
        D_minus_xstar = filter(!=(x_star), D)
        S_hat_minus = compute_full_spectrum(D_minus_xstar, N)
        M8_restricted_after_removal = sum(abs(S_hat_minus[k+1])^8 for k in K_peak)
        @assert M8_restricted_after_removal < M8_restricted_before (
            "peak_score sign check failed: removing the highest-scoring element " *
            "x*=$x_star did NOT decrease M8 restricted to K_peak " *
            "($M8_restricted_before -> $M8_restricted_after_removal) -- peak_score's " *
            "sign convention (or its derivation) is wrong, investigate before " *
            "trusting any pruning result from this call"
        )
    end

    # BUG FIX (found by running at small q -- see chat: q=5,7 both
    # silently pruned ZERO elements): round(Int, prune_frac*length(D))
    # rounds DOWN TO ZERO whenever prune_frac*|D| < 0.5, which happens
    # for essentially every small-q native Singer set (e.g. |D|=6 at
    # q=5, |D|=8 at q=7 -- 0.05*6=0.3, 0.05*8=0.4, both round to 0).
    # The function returned D unchanged with no warning in that case,
    # silently no-opting rather than pruning anything -- confirmed
    # directly by the q=5/q=7 runs both showing B_after == B_before.
    # Fixed to guarantee at least 1 element is pruned whenever
    # prune_frac > 0 and D is nonempty (matching top_k_peaks' own
    # max(1, round(...)) floor for the same reason), and to warn when
    # the requested fraction had to be rounded UP to reach that floor,
    # so a silent no-op like this one is now impossible to miss.
    n_prune = round(Int, prune_frac * length(D))
    if n_prune == 0 && prune_frac > 0 && !isempty(D)
        @warn "peak_pruned_subset: prune_frac=$prune_frac on |D|=$(length(D)) rounds " *
              "down to 0 elements pruned -- flooring to 1 instead of silently no-oping " *
              "(this is what happened, unflagged, at small q before this fix: B_after " *
              "came back equal to B_before with no indication pruning did nothing). " *
              "Use a larger q/N or a larger prune_frac if you want a genuinely " *
              "informative pruning fraction rather than this floor."
        n_prune = 1
    end
    # Rank D's INDICES by score descending, then drop the top n_prune --
    # sortperm on indices (not on D itself) keeps `scores` aligned with
    # D's original order for the returned tuple, and keeps the pruned
    # elements' identities (not just their scores) directly recoverable
    # if a caller wants to inspect which specific x's were dropped.
    order = sortperm(scores; rev = true)
    prune_idx = Set(order[1:n_prune])
    F_pruned = [D[i] for i in eachindex(D) if !(i in prune_idx)]

    return (F_pruned, K_peak, scores, frac_of_M8)
end

# ---------------------------------------------------------------
# Strategy 9: single-loudest-frequency PHASE-SPLIT exclusion
# ---------------------------------------------------------------
#
# USER'S IDEA (relayed in chat): rather than a magnitude-ranked score
# summed over many frequencies (Strategy 8's peak_pruned_subset,
# which came back a null result -- see that function's docstring and
# comment history), isolate the SINGLE loudest frequency k* and split
# D by PHASE alone at that one frequency: which elements of D are
# constructively reinforcing S_hat(k*) (phase-aligned with it) versus
# destructively interfering or neutral (not phase-aligned).
#
# WHY THIS IS A GENUINELY DIFFERENT OBJECT FROM peak_score, NOT A
# RELABELING: peak_score at any top_frac sums |S_hat(k)|^6-WEIGHTED
# contributions across many k's at once, so an element's score
# depends on its phase relationship to every frequency in K_peak
# simultaneously, weighted by how loud each one is. Restricting to a
# single k* removes the weighting and the aggregation entirely: every
# element of D contributes exactly the SAME magnitude (a unit vector
# exp(2*pi*i*k*x/N)) to S_hat(k*) -- only phase differs between
# elements at a single frequency, there is no magnitude ranking to
# collapse into ties the way the top_frac=0.01-vs-1.0 experiment did
# (see peak_pruned_subset's docstring on frac_of_M8 near 1.0 washing
# out the top_frac comparison -- that failure mode cannot occur here,
# since there is only one frequency and every element's contribution
# to it has identical magnitude by construction).
#
# THE SPLIT: rank D by phase alignment at k* -- alignment(x) =
# Re[conj(S_hat(k*)) * exp(2*pi*i*k*x/N)], which is large and positive
# for elements PUSHING S_hat(k*) further in the direction it already
# points -- and remove the top prune_frac fraction BY THIS RANKING
# (default 0.05, same convention as Strategy 8's peak_pruned_subset).
# F_aligned is the pruned elements, F_opposed = D minus F_aligned is
# the candidate pruned/remainder set to measure.
#
# BUG FIX (originally: unbounded +/-90-degree SIGN split, not a
# ranked/bounded prune): the first version put every x with
# alignment(x) > 0 into F_aligned and removed ALL of them. That
# criterion has no size control -- for a genuinely resonant D (phases
# at k* actually clustered, which is WHY k* is the loudest peak in the
# first place, not incidental), essentially every element has positive
# alignment, since that clustering IS the mechanism making the sum
# large instead of O(sqrt(B)). Confirmed directly with a synthetic
# clustered-phase D: 300/300 elements landed in F_aligned, leaving
# F_opposed EMPTY -- vs. a roughly even 162/138 split for phase-random
# D at the same B. An empty F_opposed then poisons every downstream
# consumer expecting B_after > 0 (M8 over an empty set,
# normalized_ratio dividing by B_after^8 = 0) -- this was the
# "over-prunes and deletes everything" bug. Ranking by alignment and
# removing a fixed prune_frac (with the same floor-at-1 protection as
# peak_pruned_subset, plus an explicit cap at |D|-1 so F_opposed can
# never be emptied) fixes this: |F_opposed| is now deterministic and
# bounded away from 0 for any prune_frac in (0,1), regardless of how
# tight the phase clustering is.
#
# THIS IS STILL A LINEARIZATION IN THE SAME SENSE AS peak_score:
# alignment(x) is a first-order criterion (does this element point
# roughly toward where S_hat(k*) already is, and by how much), not an
# exact optimal bipartition -- removing the top-ranked elements still
# changes S_hat(k*) by more than a first-order approximation strictly
# guarantees for a non-tiny prune_frac. This is exactly why the same
# measurement discipline applies: report the EXACT M8 of F_opposed via
# a fresh compute_full_spectrum, do not assume the split achieves what
# its construction suggests.
#
# COST: one extra full_spectrum computation for F_opposed, same cost
# class as every other before/after comparison in this file. Only
# extra parameter is prune_frac (default 0.05, matching Strategy 8) --
# k* is still just the single argmax, always well-defined for nonempty
# D.
"""
    phase_split_by_peak_freq(D::Vector{Int}, N::Int; prune_frac::Float64 = 0.05)
        -> (F_opposed::Vector{Int}, F_aligned::Vector{Int}, k_star::Int, S_hat::Vector{ComplexF64})

Computes the exact spectrum of D, finds k_star = argmax_k |S_hat(k)|^8
over the N-1 non-trivial frequencies (the single loudest frequency,
not a top-frac slice), ranks every x in D by its alignment score
Re[conj(S_hat(k_star)) * exp(2*pi*i*k_star*x/N)], and removes the
`prune_frac` fraction with the HIGHEST alignment (most responsible for
reinforcing S_hat(k_star)):

  - F_aligned: the pruned elements (top prune_frac by alignment score)
  - F_opposed: everything else (D minus F_aligned) -- the candidate
    pruned/remainder set, and what gets measured downstream

BUG FIX (was: unbounded sign split, no size control): the original
version put EVERY x with alignment > 0 into F_aligned and removed all
of them, on the theory that "positive alignment" cleanly separates
peak-reinforcing from peak-opposing elements. That criterion has no
floor or ceiling on how much of D it removes -- for a set whose
elements are genuinely NOT phase-random at k_star (i.e. exactly the
interesting/resonant case that made k_star the loudest peak in the
first place -- see norm_trace_pullback.jl's q=17 clustering finding),
essentially every element's phase sits within 90 degrees of the sum's
own direction, since that clustering is WHY the sum is large rather
than O(sqrt(B)). Confirmed directly: a synthetic D with phases at
k_star clustered around a common direction puts 100% of elements in
F_aligned and leaves F_opposed EMPTY (checked with 300/300 landing in
F_aligned in a Gaussian-clustered-phase simulation, vs. a roughly even
162/138 split for phase-uniform D at the same B). An empty F_opposed
then breaks every downstream consumer that assumes B_after > 0
(M8_after computed over an empty set, normalized_ratio dividing by
B_after^8 = 0) -- this is the over-pruning ("deletes everything") bug.

FIX: use alignment as a RANKING, not a sign test, and remove exactly
the top prune_frac fraction (same convention and same floor-at-1
behavior as peak_pruned_subset's prune_frac, including a warning when
prune_frac*|D| rounds down to 0). This guarantees 1 <= |F_aligned| <
|D| for any prune_frac in (0, 1) and nonempty D, regardless of how
tightly D's phases happen to cluster at k_star -- unlike the sign
split, which had no such guarantee and degenerated exactly in the
resonant case this strategy exists to study.

Returns F_opposed, F_aligned (sized deterministically by prune_frac,
not by D's phase distribution), k_star itself, and the full S_hat (so
a caller measuring M8_after does not need to recompute the BEFORE
spectrum from scratch).
"""
function phase_split_by_peak_freq(D::Vector{Int}, N::Int; prune_frac::Float64 = 0.05)
    @assert 0.0 < prune_frac < 1.0 "prune_frac must be in (0,1), got $prune_frac"
    S_hat = compute_full_spectrum(D, N)
    mags8 = [abs(S_hat[k+1])^8 for k in 1:(N-1)]
    k_star = argmax(mags8)  # 1-indexed into 1:(N-1), which IS the frequency value k itself

    Sk_star = S_hat[k_star+1]
    alignments = [real(conj(Sk_star) * cis(2pi * k_star * x / N)) for x in D]

    n_prune = round(Int, prune_frac * length(D))
    if n_prune == 0 && !isempty(D)
        @warn "phase_split_by_peak_freq: prune_frac=$prune_frac on |D|=$(length(D)) rounds " *
              "down to 0 elements pruned -- flooring to 1 instead of silently no-oping " *
              "(same fix as peak_pruned_subset's identical bug)"
        n_prune = 1
    end
    n_prune = min(n_prune, length(D) - 1)  # never prune everything -- F_opposed must stay nonempty

    order = sortperm(alignments; rev = true)   # highest alignment first
    aligned_idx = Set(order[1:n_prune])

    F_aligned = Int[]
    F_opposed = Int[]
    for (i, x) in enumerate(D)
        if i in aligned_idx
            push!(F_aligned, x)
        else
            push!(F_opposed, x)
        end
    end

    return (F_opposed, F_aligned, k_star, S_hat)
end

# ---------------------------------------------------------------
# run_singer_peak_pruned_comparison: measures the TRUE (exact-DFT)
# M8 of a native/embedded Singer set before and after peak pruning,
# at the same small-N scale full_spectrum_diagnostic already uses.
# ---------------------------------------------------------------

"""
    run_singer_peak_pruned_comparison(; Ns, target_q_exponent=0.2, top_frac=0.01,
                                          prune_frac=0.05, seed=1)

For each N in `Ns`: picks the largest prime q with q <= N^target_q_exponent
(same convention as run_singer_embedded_comparison -- q^2+q+1 = Nq is then
implied), builds the native Singer set D via singer_sidon_subset_native,
embeds it in Z/N by literal inclusion (asserting N >= 2*(Nq-1), same
embedding-validity guard as run_singer_embedded_comparison and
full_spectrum_diagnostic -- pruning does not relax this requirement,
since D must already be a genuine Sidon set mod N before pruning is
measured against it), re-verifies sidon_defect(D, N) == 0 (see
peak_pruned_subset's docstring for why this is a blanket sanity check
rather than something pruning itself could break), then computes:

  - the EXACT M8 of the unpruned embedded D (sum_{k=1}^{N-1}
    |S_hat(k)|^8, i.e. total_M8 from top_k_peaks' normalization
    undone -- recomputed directly here rather than reusing top_k_peaks'
    internal total_M8, since that function only returns the top-frac
    slice's fraction of the total, not the total itself)
  - peak_pruned_subset(D, N; top_frac, prune_frac) to get F_pruned
  - the EXACT M8 of F_pruned via a FRESH compute_full_spectrum +
    top_k_peaks call (NOT incrementally derived from D's spectrum --
    removing elements changes every S_hat(k), not just the ones at
    K_peak, so the pruned set's spectrum must be recomputed from
    scratch, not patched)

and reports both, plus the ratio, plus |F_pruned| (pruning can only
shrink B from D's q+1, by construction -- see peak_pruned_subset's
docstring on the round()-to-zero bug that was fixed there: at small q
this floors to 1 element pruned rather than the requested fraction).

DEFAULT target_q_exponent=0.2 MATCHES THE REAL FACTOR-BASE CONSTRAINT
(B ~ p^(2/5) ~ N^0.2, per the advisory doc) but gives a TINY q even at
large N (q=5 at N=10007, q=28 at N=2,000,000) -- confirmed directly:
at q=5,7 (this function's original default Ns), B_before=6,8 and
prune_frac=0.05 rounded down to 0 elements pruned before the fix
above, and even post-fix, pruning exactly 1 of 6-8 elements is not a
regime where a 1%-of-frequencies peak set or a 5%-of-elements prune
fraction means much statistically. Following phi_diagnostic.jl's own
convention (its smoke test uses target_q_exponent=0.4 specifically to
get q large enough for its clustering test to have statistical power)
-- raise target_q_exponent well above 0.2 here too if you want q (and
hence B_before, and hence a meaningful prune count) actually large.
This is a DIAGNOSTIC-ONLY exponent, same caveat as phi_diagnostic.jl's
0.4 run: it is not a proposal that the real factor base use a larger
q, only a way to get enough B for the pruning experiment itself to be
legible. The 0.2 default is kept as the function's default despite
this so the "real constraint" case is never silently skipped -- pass
a larger target_q_exponent explicitly to see the effect at a
statistically meaningful scale.

THIS DOES NOT SCALE to the 10^7-point production sweep -- same
restriction as full_spectrum_diagnostic (O(N*B) exact DFT, computed
TWICE per N here: once for D, once for F_pruned). Keep Ns/q small
enough for O(N*B) to stay cheap (per phi_diagnostic.jl's own docs,
N up to a few million with q up to the low hundreds is fine) or this
will be very slow.

Returns a Vector{NamedTuple} of per-N results (N, q, Nq, B_before,
B_after, M8_before, M8_after, ratio, normalized_ratio, elapsed_s),
printed as a table and also returned for further analysis.
"""
function run_singer_peak_pruned_comparison(; Ns::Vector{Int} = [10_007, 100_003],
                                               target_q_exponent::Float64 = 0.2,
                                               top_frac::Float64 = 0.01,
                                               prune_frac::Float64 = 0.05,
                                               seed::Int = 1)
    results = NamedTuple[]

    println("\n=== Singer set, Fourier-PEAK-PRUNED (target_q_exponent=$target_q_exponent, " *
            "top_frac=$top_frac, prune_frac=$prune_frac) ===")
    println("N\tq\tNq\tB_before\tB_after\tM8_before\tM8_after\tratio(after/before)\tnormalized_ratio\tfrac_of_M8_in_Kpeak\tsidon_defect_before\tsidon_defect_after\telapsed_s")
    for N in Ns
        t0 = time()
        rng = MersenneTwister(seed)
        q_target = max(2, floor(Int, N^target_q_exponent))
        q_target = min(q_target, N)  # guard tiny N, same as run_singer_embedded_comparison
        q = largest_prime_leq(q_target)
        D, Nq = singer_sidon_subset_native(q, rng)
        B_before = length(D)
        @assert N >= 2 * (Nq - 1) "Singer native modulus Nq=$Nq too close to N=$N for a " *
                         "valid embedding (need N >= 2*(Nq-1)) -- shrink q (lower " *
                         "target_q_exponent) or grow N; see run_singer_embedded_comparison " *
                         "for the full explanation of why this guard exists"

        defect_before = sidon_defect(D, N)
        if defect_before != 0
            @warn "N=$N, q=$q: unpruned embedded Singer set has nonzero " *
                  "sidon_defect=$defect_before -- pruning results below are " *
                  "untrustworthy at this N; investigate before trusting this row"
        end

        S_hat_before = compute_full_spectrum(D, N)
        mags8_before = [abs(S_hat_before[k+1])^8 for k in 1:(N-1)]
        M8_before = sum(mags8_before)

        F_pruned, K_peak, scores, frac_of_M8 = peak_pruned_subset(D, N; top_frac = top_frac, prune_frac = prune_frac)
        B_after = length(F_pruned)

        defect_after = sidon_defect(F_pruned, N)
        if defect_after != 0
            @warn "N=$N, q=$q: pruned set has nonzero sidon_defect=$defect_after -- " *
                  "this should be IMPOSSIBLE (pruning only removes elements from an " *
                  "already-Sidon set, which cannot create a new collision); investigate " *
                  "peak_pruned_subset before trusting this row"
        end

        S_hat_after = compute_full_spectrum(F_pruned, N)
        mags8_after = [abs(S_hat_after[k+1])^8 for k in 1:(N-1)]
        M8_after = sum(mags8_after)

        ratio = M8_after / M8_before
        # normalized_ratio isolates the SHAPE effect of pruning from the
        # trivial fact that removing elements shrinks M8 anyway (any
        # random B_after-sized subset would show ratio < 1 too). Dividing
        # each M8 by its own B^8 before comparing answers "are the
        # SURVIVING elements less peak-heavy per-element than the
        # original set", which is what the pruning rule is actually
        # trying to achieve -- see peak_score's docstring on why this
        # is a heuristic ranking, not a proven descent direction, so
        # this number (not the raw ratio above) is the one to look at
        # before drawing any conclusion.
        normalized_ratio = (M8_after / Float64(B_after)^8) / (M8_before / Float64(B_before)^8)
        elapsed = time() - t0

        @printf("%d\t%d\t%d\t%d\t\t%d\t%.6e\t%.6e\t%.4f\t\t\t%.4f\t\t\t%.6f\t\t\t%d\t\t\t%d\t\t\t%.2f\n",
                N, q, Nq, B_before, B_after, M8_before, M8_after, ratio, normalized_ratio,
                frac_of_M8, defect_before, defect_after, elapsed)

        push!(results, (; N, q, Nq, B_before, B_after, M8_before, M8_after, ratio,
                           normalized_ratio, frac_of_M8, defect_before, defect_after, elapsed))
    end

    println("\nnormalized_ratio = (M8_after/B_after^8) / (M8_before/B_before^8) -- isolates")
    println("the per-element SHAPE effect of pruning from the trivial fact that removing")
    println("elements shrinks M8 regardless of which ones are removed (any same-size random")
    println("subset would show raw ratio < 1 too). normalized_ratio < 1 means the surviving")
    println("elements are genuinely less peak-heavy per-element, not just fewer in number;")
    println("normalized_ratio >= 1 means pruning did nothing beyond the trivial B-shrinkage,")
    println("or made the survivors WORSE per-element despite dropping the highest scorers.")

    return results
end

# ---------------------------------------------------------------
# run_singer_phase_split_comparison: measures the TRUE (exact-DFT) M8
# of a native/embedded Singer set before and after excluding the
# elements PHASE-ALIGNED with the single loudest frequency k* (see
# phase_split_by_peak_freq's docstring for the full construction and
# why it is a different object from peak_pruned_subset's magnitude
# ranking, not a relabeling of it).
# ---------------------------------------------------------------

"""
    run_singer_phase_split_comparison(; Ns, target_q_exponent=0.2, prune_frac=0.05, seed=1)

For each N in `Ns`: builds the native Singer set D (same construction
as run_singer_peak_pruned_comparison, same embedding-validity guard),
calls phase_split_by_peak_freq(D, N; prune_frac) to get F_opposed (the
candidate pruned set: D minus the top prune_frac fraction of elements
by phase-alignment with D's single loudest frequency k*) and
F_aligned, then measures the EXACT M8 of both D and F_opposed via
fresh compute_full_spectrum calls (F_aligned is not separately
re-measured -- it is the complement, reported for its size only, same
as peak_pruned_subset's treatment of the pruned elements).

BUG FIX / BEHAVIOR CHANGE: this used to have no top_frac or prune_frac
parameter -- F_aligned was defined as EVERY x with positive alignment,
an unbounded sign split rather than a ranked, sized prune. That
degenerated to F_opposed = [] (pruning 100% of D) whenever D's phases
at k* were genuinely clustered -- exactly the resonant case this
strategy is meant to study; see phase_split_by_peak_freq's docstring
for the confirmed 300/300 all-aligned example. It now takes
prune_frac (default 0.05, matching Strategy 8's convention) and always
removes exactly that fraction (floored at 1 element, capped at |D|-1
so F_opposed can never be emptied), regardless of how tight the
clustering is -- reported directly as B_after and n_aligned so the
actual counts are visible.

Returns a Vector{NamedTuple} of per-N results (N, q, Nq, k_star,
B_before, B_after, n_aligned, M8_before, M8_after, ratio,
normalized_ratio, sidon_defect_before, sidon_defect_after, elapsed_s),
printed as a table and also returned for further analysis (e.g.
fit_growth_exponent / local_growth_exponents on the ratio column, same
as every other strategy in this file).
"""
function run_singer_phase_split_comparison(; Ns::Vector{Int} = [10_007, 100_003, 1_000_003, 10_000_019],
                                               target_q_exponent::Float64 = 0.2,
                                               prune_frac::Float64 = 0.05,
                                               seed::Int = 1)
    results = NamedTuple[]

    println("\n=== Singer set, PHASE-SPLIT at single loudest frequency k* " *
            "(target_q_exponent=$target_q_exponent) ===")
    println("N\tq\tNq\tk_star\tB_before\tB_after\tn_aligned\tM8_before\tM8_after\tratio(after/before)\tnormalized_ratio\tsidon_defect_before\tsidon_defect_after\telapsed_s")
    for N in Ns
        t0 = time()
        rng = MersenneTwister(seed)
        q_target = max(2, floor(Int, N^target_q_exponent))
        q_target = min(q_target, N)
        q = largest_prime_leq(q_target)
        D, Nq = singer_sidon_subset_native(q, rng)
        B_before = length(D)
        @assert N >= 2 * (Nq - 1) "Singer native modulus Nq=$Nq too close to N=$N for a " *
                         "valid embedding (need N >= 2*(Nq-1)) -- shrink q (lower " *
                         "target_q_exponent) or grow N; see run_singer_embedded_comparison " *
                         "for the full explanation of why this guard exists"

        defect_before = sidon_defect(D, N)
        if defect_before != 0
            @warn "N=$N, q=$q: unpruned embedded Singer set has nonzero " *
                  "sidon_defect=$defect_before -- phase-split results below are " *
                  "untrustworthy at this N; investigate before trusting this row"
        end

        S_hat_before = compute_full_spectrum(D, N)
        mags8_before = [abs(S_hat_before[k+1])^8 for k in 1:(N-1)]
        M8_before = sum(mags8_before)

        F_opposed, F_aligned, k_star, _ = phase_split_by_peak_freq(D, N; prune_frac = prune_frac)
        B_after = length(F_opposed)
        n_aligned = length(F_aligned)
        @assert B_after + n_aligned == B_before "internal mismatch: phase split did not " *
                                                 "partition D exactly -- this is a bug"

        defect_after = sidon_defect(F_opposed, N)
        if defect_after != 0
            @warn "N=$N, q=$q: phase-split remainder has nonzero sidon_defect=$defect_after " *
                  "-- this should be IMPOSSIBLE (excluding elements from an already-Sidon " *
                  "set cannot create a new collision); investigate phase_split_by_peak_freq " *
                  "before trusting this row"
        end

        S_hat_after = compute_full_spectrum(F_opposed, N)
        mags8_after = [abs(S_hat_after[k+1])^8 for k in 1:(N-1)]
        M8_after = sum(mags8_after)

        ratio = M8_after / M8_before
        normalized_ratio = (M8_after / Float64(B_after)^8) / (M8_before / Float64(B_before)^8)
        elapsed = time() - t0

        @printf("%d\t%d\t%d\t%d\t%d\t\t%d\t%d\t\t%.6e\t%.6e\t%.4f\t\t\t%.4f\t\t\t%d\t\t\t%d\t\t\t%.2f\n",
                N, q, Nq, k_star, B_before, B_after, n_aligned, M8_before, M8_after, ratio,
                normalized_ratio, defect_before, defect_after, elapsed)

        push!(results, (; N, q, Nq, k_star, B_before, B_after, n_aligned, M8_before, M8_after,
                           ratio, normalized_ratio, defect_before, defect_after, elapsed))
    end

    println("\nnormalized_ratio = (M8_after/B_after^8) / (M8_before/B_before^8), same convention")
    println("as run_singer_peak_pruned_comparison. normalized_ratio < 1 means F_opposed is")
    println("genuinely less peak-heavy per-element than D was, not just smaller.")
    println("n_aligned/B_before shows the ACTUAL split fraction produced by phase alone --")
    println("compare against Strategy 8's fixed prune_frac=0.05 to judge whether phase-split's")
    println("much larger typical exclusion fraction is doing more, or just removing more.")

    if length(results) >= 2
        println("\n--- Phase-split growth-exponent fit (mean ratio vs real N) ---")
        fit_rows = [(; N = r.N, B = r.B_after, m = 0, ratio = r.ratio,
                       maxU = 0.0, defect = r.defect_after, elapsed = r.elapsed)
                    for r in results]
        fit = fit_growth_exponent(fit_rows)
        if length(fit_rows) >= 3
            local_growth_exponents(fit_rows)
        end
        return (; results, fit)
    end

    return (; results, fit = nothing)
end

# ---------------------------------------------------------------
# run_singer_peak_pruned_topfrac_comparison: same D, same q/N, two
# top_frac settings (default: the original top_frac=0.01 vs. the FULL
# spectrum top_frac=1.0) -- answers the question "does scoring against
# every nonzero frequency, not just the top 1% by mass, change the
# sign of the effect".
# ---------------------------------------------------------------

"""
    run_singer_peak_pruned_topfrac_comparison(; Ns, target_q_exponent=0.2,
                                                  top_fracs=[0.01, 1.0],
                                                  prune_frac=0.05, seed=1)

Runs run_singer_peak_pruned_comparison once per value in `top_fracs`,
at the SAME (Ns, target_q_exponent, prune_frac, seed) each time -- so
D is IDENTICAL across all top_frac settings for a given N (D only
depends on q, which only depends on N/target_q_exponent/seed; see
run_singer_peak_pruned_comparison's rng seeding, reset fresh from
`seed` every N, independent of top_frac). Prints a
per-(N,top_frac) normalized_ratio comparison table at the end so the
sign/magnitude of the effect at top_frac=0.01 (peak_score's original
proposal: only the loudest 1% of frequencies inform the score) can be
read directly against top_frac=1.0 (every nonzero frequency
contributes to grad(x), i.e. the FULL spectrum -- this is the natural
follow-up: the current score is blind to frequencies just below the
top-1% cutoff, and pruning could easily be helping those loudest
peaks while making frequencies in the 1-10% band worse, which
top_frac=0.01 has no way to see or penalize).

COST NOTE: top_frac only changes the size of K_peak in the O(B*K)
scoring step (peak_score), NOT the O(N*B) exact-DFT step
(compute_full_spectrum), which dominates total cost and runs
regardless of top_frac. Going from top_frac=0.01 to top_frac=1.0
is at most a ~2x total slowdown at the q,N scale this function is
meant for (K_peak growing from 0.01*(N-1) to N-1, i.e. B*K terms
going from ~0.01*N*B to ~N*B, comparable to but not dominating the
DFT's own N*B cost) -- NOT the ~100x the K_peak size ratio alone
would suggest, because compute_full_spectrum's cost is independent
of top_frac and is what actually sets the wall-clock at this scale.
Still does NOT scale to the 10^7-point production sweep, same
restriction as run_singer_peak_pruned_comparison itself.

Returns a Dict{Float64, Vector{NamedTuple}} keyed by top_frac, same
per-N result shape as run_singer_peak_pruned_comparison.
"""
function run_singer_peak_pruned_topfrac_comparison(; Ns::Vector{Int} = [1_000_003, 2_000_003],
                                                        target_q_exponent::Float64 = 0.4,
                                                        top_fracs::Vector{Float64} = [0.01, 1.0],
                                                        prune_frac::Float64 = 0.05,
                                                        seed::Int = 1)
    all_results = Dict{Float64, Vector{NamedTuple}}()
    for tf in top_fracs
        println("\n########## top_frac = $tf ##########")
        all_results[tf] = run_singer_peak_pruned_comparison(; Ns = Ns,
                                                                target_q_exponent = target_q_exponent,
                                                                top_frac = tf,
                                                                prune_frac = prune_frac,
                                                                seed = seed)
    end

    println("\n=== top_frac head-to-head (same D per N, only K_peak's size differs) ===")
    header = String[]
    for tf in top_fracs
        push!(header, "normalized_ratio(top_frac=$tf)")
        push!(header, "frac_of_M8(top_frac=$tf)")
    end
    println("N\t" * join(header, "\t"))
    for (i, N) in enumerate(Ns)
        row_vals = String[]
        for tf in top_fracs
            r = all_results[tf][i]
            @assert r.N == N "internal mismatch: result order does not match Ns -- this is a bug"
            push!(row_vals, @sprintf("%.4f", r.normalized_ratio))
            push!(row_vals, @sprintf("%.6f", r.frac_of_M8))
        end
        println("$N\t" * join(row_vals, "\t\t\t"))
    end
    println("\nIf the full-spectrum (top_frac=1.0) column comes back with normalized_ratio")
    println("consistently < 1 while the top-1% column stays >= 1 (or vice versa), that")
    println("would mean the SIGN of the effect depends on which frequencies inform the")
    println("score -- i.e. peak_score's current top_frac=0.01 restriction is not just")
    println("underpowered but actively looking at the wrong slice of the spectrum. If")
    println("both columns agree in sign, CHECK frac_of_M8(top_frac=0.01) before")
    println("concluding the top-1% restriction wasn't the problem: if it's already near")
    println("1.0, the two settings never differed in which mass they saw, so agreement")
    println("is not informative either way -- see peak_pruned_subset's docstring.")

    return all_results
end

# ---------------------------------------------------------------
# Strategy registry
# ---------------------------------------------------------------

const STRATEGIES = Dict{Symbol, Function}(
    :greedy              => greedy_sidon_subset,
    :greedy_low_energy   => greedy_low_energy_sidon_subset,
    :singer              => singer_sidon_subset,
)

# ---------------------------------------------------------------
# Comparison harness
# ---------------------------------------------------------------

"Small helper: build the AbelianGroup for cyclic Z/N once per call site."
G_for(N::Int) = AbelianGroup([N])

"""
    compare_strategies(; Ns, strategies, m_per_point, m_scaling, m_floor, m_cap, seed)

Runs the character sampler against each strategy in `strategies`
(keys into STRATEGIES) across the same Ns / B / character-sample
budget, using the SAME seed for every strategy at a given N (so the
character samples themselves are identical across strategies -- only
F differs, isolating the strategy's effect).

Every strategy is required to return EXACTLY `target_size` = B
elements -- enforced by an explicit check after construction, not
just assumed. This matters because the comparison's flat-value
normalizer B^8/N depends sensitively on B; an earlier version of
greedy_low_energy_sidon_subset could silently return fewer elements
than requested, which corrupted the head-to-head ratio comparison
without any visible error. That bug is fixed at the construction
level (see that function's docstring) AND guarded here, so any future
strategy with a similar bug fails loudly instead of producing a
misleading ratio.

Prints a per-(N,strategy) row, then a growth-exponent fit PER
STRATEGY (across Ns), so you get both the head-to-head ratio at each
scale and each strategy's own gamma for direct comparison against the
baseline's gamma ~ 0.46 measured earlier.

Returns a Dict{Symbol, Vector{NamedTuple}} of per-strategy sweep
results (same shape as scaling_sweep.jl's `sweep()` output) plus a
Dict{Symbol, NamedTuple} of per-strategy fits, so downstream code
(e.g. a further multi-seed wrapper) can reuse them directly.
"""
function compare_strategies(; Ns::Vector{Int} = [10_007, 100_003, 1_000_003, 10_000_019],
                                strategies::Vector{Symbol} = [:greedy, :greedy_low_energy],
                                m_per_point::Int = 20_000,
                                m_scaling::Symbol = :sqrt_N,
                                m_floor::Int = 2_000,
                                m_cap::Int = typemax(Int),
                                seed::Int = 1)
    for s in strategies
        @assert haskey(STRATEGIES, s) "unknown strategy $s -- available: $(keys(STRATEGIES))"
    end

    N0 = Float64(first(Ns))
    all_results = Dict{Symbol, Vector{NamedTuple}}(s => NamedTuple[] for s in strategies)

    println("N\tB\tm\tstrategy\tratio(MC/flat)\tmax|U|\tsidon_defect\telapsed_s")
    for N in Ns
        B = round(Int, N^0.4)

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

        for strat in strategies
            # Known dead point, skipped BEFORE paying for it: greedy_low_energy
            # at N=10_000_019 (B=631) has failed identically on every observed
            # run -- 20 restart waves each exhausting all 10,000,019 candidates
            # (~190M total candidates scanned across 20 threads), taking ~86s
            # wall-clock, then erroring with "failed to reach target_size after
            # max_restarts". This is not an occasional flake to retry; it is a
            # reproducible failure at this specific (N, B, strategy) combination
            # under the current max_restarts=20/lookahead=6 defaults. Skipping
            # it here avoids re-paying the 86s every run for a result that is
            # already known. Remove this skip (or raise max_restarts/lookahead
            # in greedy_low_energy_sidon_subset's call site) if you want to
            # re-attempt it -- the underlying function itself is unchanged and
            # will still try normally if called directly.
            if strat == :greedy_low_energy && N == 10_000_019
                @warn "N=$N strategy=$strat: skipped -- known to fail after " *
                      "~86s of restart waves on every observed run at this " *
                      "(N,B); see comment at this skip if you want to re-enable it"
                continue
            end

            rng = MersenneTwister(seed)   # SAME seed per strategy at this N -> same
                                            # candidate ordering / character samples,
                                            # so differences isolate the strategy itself
            construct = STRATEGIES[strat]

            # Wrapped per (N, strat) point rather than left to propagate:
            # an unwrapped failure here aborts compare_strategies() entirely --
            # meaning every OTHER (N, strat) point after the failing one, even
            # ones that would have succeeded, never runs either. Catching
            # here means one bad point is skipped and reported, not paid
            # for in full then thrown away. (The known-dead point above is
            # skipped before this even triggers; this remains as a general
            # safety net for any OTHER construction failure.)
            F_int = try
                construct(N, B, rng)
            catch e
                @warn "N=$N strategy=$strat: construction failed, skipping this point" exception=(e, catch_backtrace())
                continue
            end

            @assert length(F_int) == B "strategy=$strat at N=$N returned |F|=$(length(F_int)) " *
                                        "but B=$B was requested -- this would corrupt the " *
                                        "flat-value normalizer B^8/N and invalidate the " *
                                        "comparison; fix the strategy to return exactly B " *
                                        "elements or raise clearly, not return a short result."
            defect = sidon_defect(F_int, N)
            if defect != 0
                @warn "N=$N strategy=$strat: Sidon defect $defect (not perfectly Sidon) -- " *
                      "comparison for this point is weaker than intended"
            end
            F = [[x] for x in F_int]

            # Fresh RNG for character sampling, seeded identically
            # across strategies at this N so the SAME set of sampled
            # characters is used for every strategy -- isolates F as
            # the only varying input.
            t0 = time()
            result = run_character_sampler_threaded(G_for(N), F; m = m, seed = seed,
                                                       k_size = N, report_every = typemax(Int))
            elapsed = time() - t0

            Bf = Float64(length(F_int))
            flat = (Bf^8) / N
            ratio = result.M8_running[end] / flat
            maxU = maximum(abs.(result.U_vals))

            @printf("%d\t%d\t%d\t%s\t%.4f\t%.4f\t%d\t%.2f\n",
                    N, B, m, strat, ratio, maxU, defect, elapsed)

            push!(all_results[strat], (; N, B, m, ratio, maxU, defect, elapsed))
        end
    end

    println("\n--- Per-strategy growth-exponent fits ---")
    fits = Dict{Symbol, NamedTuple}()
    for strat in strategies
        rs = all_results[strat]
        if length(rs) >= 2
            println("\n[$strat]")
            fits[strat] = fit_growth_exponent(rs)
            # Companion LOCAL check (see local_growth_exponents docstring
            # in scaling_sweep.jl): the single global fit above cannot
            # distinguish "gamma really is ~this value asymptotically"
            # from "gamma is trending toward/away from 0 as N/B grow but
            # this N-range hasn't shown it yet" -- both can produce a
            # high-R^2 global fit. Needs 3+ points; strategies skipped
            # at some N (e.g. greedy_low_energy at N=10000019, see its
            # skip comment above) may have fewer than `strategies`-wide
            # Ns and still clear this bar with 3.
            if length(rs) >= 3
                local_growth_exponents(rs)
            end
        else
            @warn "[$strat] fewer than 2 valid points -- skipping fit"
        end
    end

    if length(fits) >= 2
        println("\n--- Head-to-head gamma summary ---")
        println("strategy\tgamma\tR^2")
        for (strat, fit) in sort(collect(fits); by = kv -> kv[2].gamma)
            @printf("%s\t%.4f\t%.4f\n", strat, fit.gamma, fit.r2)
        end
        println("\nLower gamma = ratio grows more slowly with N = closer to the flat/(H0)",
                " regime = empirically better 8th-moment behavior for that strategy.")
    end

    return (; all_results, fits)
end

if abspath(PROGRAM_FILE) == @__FILE__
    # Strategy 9 runs FIRST, unthreaded, on its own (per chat: tired of
    # waiting through the older strategies to reach new results) --
    # every OTHER strategy below has already been run and its result
    # is recorded in this file's own comments, so there is no reason
    # to make Strategy 9 wait behind them anymore. Running it alone
    # (not inside the threaded block below) also means it gets the
    # full nthreads() budget to itself for its internal
    # compute_full_spectrum/character-sampler parallelism, rather than
    # competing with whatever else is spawned concurrently.
    try
        println("--- Strategy 9: phase-split at single loudest frequency, " *
                "target_q_exponent=0.2 (real constraint) ---")
        run_singer_phase_split_comparison(; target_q_exponent = 0.2)
    catch e
        @error "run_singer_phase_split_comparison() [0.2] failed" exception=(e, catch_backtrace())
    end
    try
        println("\n--- Strategy 9: phase-split at single loudest frequency, " *
                "target_q_exponent=0.4 (diagnostic only) ---")
        run_singer_phase_split_comparison(; Ns = [1_000_003, 2_000_003], target_q_exponent = 0.4)
    catch e
        @error "run_singer_phase_split_comparison() [0.4] failed" exception=(e, catch_backtrace())
    end

    # ---------------------------------------------------------------
    # Everything below is the PREVIOUSLY-RUN strategy sequence
    # (Strategies 1-8 plus sweeps), now launched CONCURRENTLY via
    # Threads.@spawn rather than run one-after-another -- per chat,
    # threading "the ending tests" so they finish sooner in wall-clock
    # while Strategy 9 above has already reported first.
    #
    # WHY BUFFERED OUTPUT, NOT DIRECT println/@printf FROM EACH TASK:
    # every strategy function below prints its own table via bare
    # println/@printf to the process-global stdout. If N tasks do that
    # concurrently, their lines interleave mid-table and the output
    # becomes unreadable (this is not a hypothetical -- Julia gives no
    # ordering or atomicity guarantee across tasks writing to the same
    # stream). Each task's output is instead captured into its own
    # IOBuffer via redirect_stdout, and flushed as one atomic block to
    # the real stdout when that task completes -- readable per-block,
    # same total content, just not interleaved.
    #
    # WHY THIS IS NOT A FREE N-WAY SPEEDUP: every strategy below
    # ALREADY uses Threads.nthreads() internally (character sampling
    # and, for the Singer constructions, the field-arithmetic power
    # table) -- see run_character_sampler_threaded and
    # singer_sidon_subset_native's own threading comments. Running M
    # strategies concurrently on top of that means up to M*nthreads()
    # tasks contending for the same physical cores; Julia's scheduler
    # will interleave them rather than deadlock, but wall-clock gains
    # depend entirely on how many cores are idle beyond what a single
    # strategy already saturates -- on a fully-loaded machine this can
    # show little improvement, or even regress slightly from
    # scheduling overhead, versus the old sequential order. It is
    # still very unlikely to be SLOWER than strictly sequential
    # (each task still only runs when a core is free), just not
    # guaranteed to scale linearly with the number of blocks below.
    #
    # WHY try/catch STAYS PER-TASK: same reasoning as the original
    # sequential version -- one strategy failing (e.g. a Sidon
    # construction exhausting its candidate pool) must not prevent the
    # others from completing and reporting.
    #
    # BUG FIX (crash): redirect_stdout()/redirect_stdout(f, wr) mutate
    # the single GLOBAL Base.stdout binding -- it is not thread-local
    # or task-local. The original code had every one of the 7 tasks
    # below call redirect_stdout() concurrently via Threads.@spawn,
    # each assuming it owned "the" stdout pipe for the duration of its
    # block. In reality all 7 were racing to swap the same global
    # binding: task B's redirect_stdout() call could silently replace
    # task A's redirect before A's close(wr)/read(rd), so A ended up
    # reading from (or writing into, then closing) a pipe it no longer
    # owned. Depending on interleaving this surfaces as reading a
    # closed/empty pipe, writing after close (IOError: stream is
    # closed), or a stuck read() that never sees EOF because the wrong
    # task closed the wrong writer -- all nondeterministic, which
    # matches "crashes" rather than "reliably crashes the same way".
    #
    # FIX: take out a lock around the ENTIRE
    # redirect/run/close/read sequence for each task, so only one task
    # ever holds "ownership" of the global stdout swap at a time. This
    # keeps the per-task IOBuffer-capture behavior and submission-order
    # printing the surrounding comments describe, while making the
    # swap itself safe. It serializes the redirect bookkeeping (cheap)
    # NOTE ON WHAT THIS COSTS: unlike a first attempt at this fix (lock
    # only around the redirect-in/redirect-out calls, released while
    # f() itself runs), THIS IS STILL NOT SAFE if the lock is released
    # between "point stdout at my pipe" and "read my pipe back" --
    # another task could grab the lock in that window, redirect stdout
    # to ITS OWN pipe, run its whole block, and redirect back, all
    # while task A's f() is still executing and still writing into
    # what is now the WRONG global stdout. So the lock below is held
    # for the ENTIRE redirect_stdout(wr) do f() end call, not just the
    # swap-in/swap-out bookkeeping. This DOES serialize the actual
    # strategy computation across these 7 tasks (only one runs at a
    # time from stdout's perspective) -- there is no way to keep
    # println/@printf-based output capture safe under concurrency
    # without serializing around the shared global stream; the
    # alternative (rewriting every strategy function to build a string
    # instead of printing) is a much larger change than this bug fix
    # warrants. Each strategy still gets its own thread from Julia's
    # scheduler and any INTERNAL Threads.@spawn parallelism (character
    # sampling, field-arithmetic power tables) is unaffected, since
    # those don't touch stdout -- only the top-level "run one strategy
    # end-to-end" serialization changes here, trading some of the
    # wall-clock overlap the original code intended for actually not
    # crashing.
    tasks = Task[]
    stdout_swap_lock = ReentrantLock()

    "Run `f` with stdout captured into a private IOBuffer, safely w.r.t. other concurrent callers of this function (see BUG FIX note above -- the whole call is serialized, not just the redirect bookkeeping)."
    function run_captured(f::Function)
        return lock(stdout_swap_lock) do
            rd, wr = redirect_stdout()
            try
                redirect_stdout(wr) do
                    f()
                end
            finally
                close(wr)
            end
            String(read(rd))
        end
    end

    push!(tasks, Threads.@spawn run_captured() do
        try
            compare_strategies()   # greedy vs greedy_low_energy, same (N,B) per row
        catch e
            @error "compare_strategies() failed -- see error below; continuing to Singer" exception=(e, catch_backtrace())
        end
    end)

    push!(tasks, Threads.@spawn run_captured() do
        println("\n=== Singer difference set (own N/B columns -- see docstring caveat) ===")
        try
            run_singer_comparison()
        catch e
            @error "run_singer_comparison() failed" exception=(e, catch_backtrace())
        end
    end)

    push!(tasks, Threads.@spawn run_captured() do
        try
            run_singer_embedded_exponent_sweep()
        catch e
            @error "run_singer_embedded_exponent_sweep() failed" exception=(e, catch_backtrace())
        end
    end)

    push!(tasks, Threads.@spawn run_captured() do
        try
            run_singer_paired_comparison()
        catch e
            @error "run_singer_paired_comparison() failed" exception=(e, catch_backtrace())
        end
    end)

    push!(tasks, Threads.@spawn run_captured() do
        try
            run_singer_quad_filtered_comparison()
        catch e
            @error "run_singer_quad_filtered_comparison() failed" exception=(e, catch_backtrace())
        end
    end)

    push!(tasks, Threads.@spawn run_captured() do
        try
            run_singer_quad_filtered_exponent_sweep()
        catch e
            @error "run_singer_quad_filtered_exponent_sweep() failed" exception=(e, catch_backtrace())
        end
    end)

    # run_projected_greedy_comparison() stays disabled (per chat,
    # slow + null result) -- not spawned here either.

    push!(tasks, Threads.@spawn run_captured() do
        try
            println("--- Run 1: real constraint, target_q_exponent=0.2 (expect tiny q -- see comment above) ---")
            run_singer_peak_pruned_comparison(; target_q_exponent = 0.2)
        catch e
            @error "run_singer_peak_pruned_comparison() [0.2] failed" exception=(e, catch_backtrace())
        end
        try
            println("\n--- Run 2: diagnostic-only higher exponent, target_q_exponent=0.4 (larger q, statistically legible prune count) ---")
            run_singer_peak_pruned_comparison(; Ns = [1_000_003, 2_000_003], target_q_exponent = 0.4)
        catch e
            @error "run_singer_peak_pruned_comparison() [0.4] failed" exception=(e, catch_backtrace())
        end
        try
            println("\n--- Run 3: top_frac=0.01 vs top_frac=1.0 (full spectrum) head-to-head, same D ---")
            run_singer_peak_pruned_topfrac_comparison(; Ns = [1_000_003, 2_000_003], target_q_exponent = 0.4)
        catch e
            @error "run_singer_peak_pruned_topfrac_comparison() failed" exception=(e, catch_backtrace())
        end
    end)

    # Collect and print each task's buffered output IN SUBMISSION
    # ORDER (not completion order) once ALL tasks are done -- fetch()
    # on a Task blocks until that task finishes and returns its value,
    # so this loop both waits for everything and preserves a stable,
    # rerun-to-rerun-comparable ordering that matches the original
    # sequential script, rather than whatever order tasks happened to
    # finish in (which varies run to run and would make diffing two
    # runs' output harder).
    for t in tasks
        print(fetch(t))
    end
end
