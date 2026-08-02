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
using Base.Threads: nthreads   # Threads.@spawn / Threads.Atomic / Threads.atomic_add! used fully-qualified below

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
    # Each block is wrapped independently so a failure in one strategy
    # (e.g. a Sidon-construction exhaustion) doesn't prevent the others
    # from running and reporting results -- previously a single error
    # anywhere in compare_strategies() aborted the whole script before
    # run_singer_comparison() ever executed.
    try
        compare_strategies()   # greedy vs greedy_low_energy, same (N,B) per row
    catch e
        @error "compare_strategies() failed -- see error below; continuing to Singer" exception=(e, catch_backtrace())
    end

    println("\n=== Singer difference set (own N/B columns -- see docstring caveat) ===")
    try
        run_singer_comparison()
    catch e
        @error "run_singer_comparison() failed" exception=(e, catch_backtrace())
    end

    # This is the fair, apples-to-apples comparison against
    # greedy/greedy_low_energy above: same target N per row, ratio
    # computed against that real N (not Singer's native Nq). See
    # run_singer_embedded_comparison's docstring for why this is a
    # separate function from run_singer_comparison rather than a
    # variant flag on it -- the native-Nq ratio and the embedded-vs-N
    # ratio are answering different questions and neither is a
    # substitute for the other.
    #
    # run_singer_embedded_exponent_sweep runs target_q_exponent=0.2
    # (the REAL constraint: B~p^(2/5)~N^0.2) plus several higher
    # exponents purely as a DIAGNOSTIC to trace whether/where gamma
    # trends back toward flat -- see that function's docstring. The
    # higher exponents are not proposals; only the 0.2 row reflects
    # an allowed factor-base choice.
    try
        run_singer_embedded_exponent_sweep()
    catch e
        @error "run_singer_embedded_exponent_sweep() failed" exception=(e, catch_backtrace())
    end

    # User's "randomized partner" idea: F = sums of Singer points with
    # a random partner drawn from the Singer set itself, rather than
    # raw D embedded directly. Run at the REAL constraint exponent
    # (0.2) for direct comparison against greedy/greedy_low_energy
    # above and raw embedded-Singer (target_q_exponent=0.2 block
    # earlier in this run) at the same N -- this is the point of
    # comparison that actually matters for the factor-base decision.
    try
        run_singer_paired_comparison()
    catch e
        @error "run_singer_paired_comparison() failed" exception=(e, catch_backtrace())
    end
end
