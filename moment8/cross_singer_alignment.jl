#!/usr/bin/env julia
#
# cross_singer_alignment.jl
#
# Tests the PREMISE behind "sum several Singer sets and let their
# phases at each other's peak frequencies cancel" (per chat) BEFORE
# building the expensive union experiment.
#
# THE IDEA BEING TESTED: if D_1 has a resonant peak at frequency k_1*
# (|S_hat_1(k_1*)| much larger than typical -- see phi_diagnostic.jl's
# and norm_trace_pullback.jl's q=17 finding), and D_2 is an
# INDEPENDENT Singer set (different random cubic / generator, and
# optionally a different q), then unioning D_1 and D_2 only helps
# cancel THAT peak if D_2's own contribution to frequency k_1*
# (S_hat_2(k_1*) -- not D_2's OWN peak frequency, D_1's) happens to
# point opposite to S_hat_1(k_1*). There is no a priori reason this
# should be true, coincidentally true, or systematically false across
# a family of Singer sets -- it has to be measured.
#
# WHAT THIS SCRIPT DOES: builds m independent Singer sets (each via a
# fresh call to singer_sidon_subset_native with its own seed -- and
# optionally different q's, see `q_variety` below), all embedded in
# the SAME Z/N by literal inclusion (same embedding as every other
# script in this project). For each set i, finds its own dominant
# frequency k_i* (largest |S_hat_i(k)|^8 over nonzero k). Then builds
# the full m x m cross-alignment matrix:
#
#   align[i,j] = Re[conj(S_hat_i(k_i*)) * S_hat_j(k_i*)]
#                / (|S_hat_i(k_i*)| * |S_hat_j(k_i*)|)
#
# i.e. the cosine of the phase difference between set i's OWN
# contribution to its own peak and set j's contribution to that SAME
# frequency, normalized to [-1, 1]. By construction align[i,i] = 1
# (a set is always perfectly self-aligned with its own peak -- this is
# not a null result, just the diagonal's definition). The interesting
# entries are align[i,j] for i != j:
#
#   - near -1: set j is ANTI-aligned with set i's peak -- unioning
#     would genuinely help cancel that specific peak, in the direction
#     the naive proposal hopes for.
#   - near 0: set j's phase at k_i* looks like an independent/random
#     draw -- unioning neither reliably helps nor hurts THAT peak
#     (consistent with "no special relationship", i.e. cancellation
#     would only happen by luck, not by any structural reason -- you
#     could equally get align near +1 on the next seed).
#   - near +1: set j is ALIGNED -- unioning would make that specific
#     peak WORSE, not better. If this happens systematically (not just
#     for one pair), it means the "family" of Singer sets resonates
#     together and union-based cancellation is not viable without
#     first understanding why (e.g. all constructions sharing some
#     invariant tied to q or the trace-zero condition itself).
#
# NULL COMPARISON: for calibration, the same statistic is computed for
# `n_null` pairs of independent UNIFORM-RANDOM phases (i.e. what
# align[i,j] would look like if D_j's phase at k_i* really were an
# independent random draw on the unit circle) -- this tells you the
# spread to expect under "genuinely no relationship" so a handful of
# off-diagonal entries landing near -1 or +1 by chance (small m --
# few pairs) isn't over-interpreted as a real effect.
#
# WHAT THIS DOES NOT DO: it does not build the union F = D_1 union ...
# union D_m or measure its actual M8 -- that is a separate, more
# expensive experiment (also needs a Sidon-compatibility check across
# sets, and the max(Nq_i) embedding-validity guard applied to the
# largest set). This script only checks whether the PREMISE the union
# experiment would rely on (systematic anti-alignment) is plausible at
# all, so that expensive experiment isn't built on an unverified
# assumption -- same "measure, don't assume" discipline as
# peak_pruned_subset's in-place sign check and phi_diagnostic.jl's
# confinement-vs-clustering split.

using Printf
using Statistics
using Random

include("strategy_comparison.jl")   # singer_sidon_subset_native, largest_prime_leq,
                                     # compute_full_spectrum, sidon_defect

"""
    build_singer_sets(N::Int, qs::Vector{Int}; base_seed::Int = 1)
        -> Vector{NamedTuple}

Builds one Singer set per entry in `qs` (qs can repeat the same q
multiple times -- each call still gets an INDEPENDENT random
irreducible cubic and generator, since singer_sidon_subset_native
draws fresh randomness every call; repeating q tests "does resonance
persist across independent constructions of the SAME abstract group",
while varying q additionally tests across different Nq's/group
orders), all embedded in the same Z/N by literal inclusion.

Each set gets its own seed (base_seed + index) so runs are
reproducible but sets are genuinely independent of each other.

Returns a Vector of NamedTuples (; q, Nq, D, B, seed, defect), one per
requested set, after asserting the SAME N >= 2*(Nq-1) embedding-
validity guard used everywhere else in this project (checked
per-set, since different q's give different Nq's) and verifying
sidon_defect(D, N) == 0 for each (a set with nonzero defect would make
the "own peak" interpretation of k_i* unreliable, same reasoning as
every other diagnostic in this project that checks this before
trusting downstream numbers).
"""
function build_singer_sets(N::Int, qs::Vector{Int}; base_seed::Int = 1)
    sets = NamedTuple[]
    for (i, q) in enumerate(qs)
        seed_i = base_seed + i
        rng = MersenneTwister(seed_i)
        D, Nq = singer_sidon_subset_native(q, rng)
        B = length(D)
        @assert N >= 2 * (Nq - 1) "set $i: Singer native modulus Nq=$Nq too close to N=$N " *
                         "for a valid embedding (need N >= 2*(Nq-1)) -- lower q or grow N"
        defect = sidon_defect(D, N)
        if defect != 0
            @warn "set $i (q=$q, seed=$seed_i): nonzero sidon_defect=$defect -- " *
                  "this set's own spectrum/peak-frequency numbers are untrustworthy"
        end
        push!(sets, (; q, Nq, D, B, seed = seed_i, defect))
    end
    return sets
end

"""
    dominant_frequency(S_hat::Vector{ComplexF64}, N::Int, Nq::Int;
                        confinement_guard_frac::Float64 = 0.15) -> Int

Returns argmax_k |S_hat(k)|^8 over the N-1 NON-TRIVIAL frequencies
k in 1:(N-1), EXCLUDING frequencies too close to a multiple of the
confinement period N/Nq.

BUG FIX (found by running this script): the original version was a
plain unrestricted argmax over 1:(N-1). Since D's integer
representatives are confined to the short interval [0, Nq-1] inside
the much larger Z/N (Nq=307 vs N=2,000,000 in the q=17 case), the
spectrum of ANY interval-confined set -- Singer or not, resonant or
not -- is heavily concentrated at LOW k purely from the interval's
geometry (this is exactly the "confinement" artifact
phi_diagnostic.jl's own confinement-scale test was built to separate
from genuine algebraic resonance; see that script's docstring). The
plain argmax found k=1 (or another tiny k) for every single set in
both test runs, regardless of q or which random cubic/generator built
it -- i.e. it was measuring "this set starts near 0", the same
artifact for every set, not anything Singer-specific. That is why
every off-diagonal cross-alignment entry came back +1.000: all five
sets' "own peaks" were actually the same confinement-driven low-k
mode, so of course they were perfectly aligned with each other there.
This was a bug in this diagnostic, not a real finding about Singer
sets -- see phi_diagnostic.jl's own confinement-vs-clustering split,
which this function was supposed to already be applying and wasn't.

FIX: mirror phi_diagnostic.jl's confinement test directly -- exclude
any k within `confinement_guard_frac` of the nearest multiple of
period = N/Nq (in units of the period, so 0.15 excludes k's landing
within 15% of a period-width band around each confinement multiple),
then take argmax over what remains. This still allows a genuinely
CONFINEMENT-DOMINATED set's peak to be reported (if literally nothing
survives the guard, see the @assert below -- that is itself
informative, meaning this set has essentially no non-confinement
structure to speak of) but stops the search from defaulting to the
confinement artifact when real structure exists elsewhere, which is
what happened here.
"""
function dominant_frequency(S_hat::Vector{ComplexF64}, N::Int, Nq::Int;
                             confinement_guard_frac::Float64 = 0.15)
    period = N / Nq
    mags8 = [abs(S_hat[k+1])^8 for k in 1:(N-1)]

    allowed = Int[]
    for k in 1:(N-1)
        dist_to_grid = abs(mod(k / period, 1.0) - round(mod(k / period, 1.0)))  # in units of the period
        if dist_to_grid >= confinement_guard_frac
            push!(allowed, k)
        end
    end

    @assert !isempty(allowed) "dominant_frequency: confinement_guard_frac=$confinement_guard_frac " *
             "excluded ALL nonzero frequencies for Nq=$Nq, N=$N -- period=N/Nq=$period is too " *
             "coarse relative to the guard fraction (this happens when Nq is a large fraction of " *
             "N); lower confinement_guard_frac or grow N/Nq's ratio"

    best_k = allowed[argmax(mags8[allowed])]
    return best_k
end

"""
    cross_alignment_matrix(sets::Vector{NamedTuple}, N::Int;
                            confinement_guard_frac::Float64 = 0.15)
        -> (align::Matrix{Float64}, k_stars::Vector{Int}, S_hats::Vector{Vector{ComplexF64}})

Computes the full spectrum of every set (compute_full_spectrum, one
O(N*B_i) DFT per set -- same cost class as phi_diagnostic.jl, so keep
N,B in the same "small enough for exact DFT" regime that script uses),
each set's own confinement-guarded dominant frequency k_i* (see
dominant_frequency's docstring -- uses EACH set's own Nq, since
different sets can have different q's/Nq's in the varied-q run), and
the m x m normalized cross-alignment matrix

    align[i,j] = Re[conj(S_hat_i(k_i*)) * S_hat_j(k_i*)]
                 / (|S_hat_i(k_i*)| * |S_hat_j(k_i*)|)

align[i,i] is always 1.0 by construction (a set's contribution to its
own peak is, trivially, perfectly aligned with itself) -- this is a
sanity-check identity, not a result to interpret; see docstring above
for how to read the off-diagonal entries.

If any set's S_hat_j(k_i*) is exactly 0 (a set contributing NOTHING
at another's peak frequency -- possible but not expected generically),
align[i,j] is reported as NaN rather than dividing by zero, and a
warning is issued naming the (i,j) pair.
"""
function cross_alignment_matrix(sets::Vector{NamedTuple}, N::Int;
                                 confinement_guard_frac::Float64 = 0.15)
    m = length(sets)
    S_hats = [compute_full_spectrum(s.D, N) for s in sets]
    k_stars = [dominant_frequency(S_hats[i], N, sets[i].Nq;
                                   confinement_guard_frac = confinement_guard_frac) for i in 1:m]

    align = Matrix{Float64}(undef, m, m)
    for i in 1:m
        ki = k_stars[i]
        Si_ki = S_hats[i][ki+1]
        mag_i = abs(Si_ki)
        for j in 1:m
            Sj_ki = S_hats[j][ki+1]
            mag_j = abs(Sj_ki)
            if mag_i == 0.0 || mag_j == 0.0
                @warn "cross_alignment_matrix: set $j contributes exactly 0 at set $i's " *
                      "peak frequency k_$i*=$ki -- reporting NaN for align[$i,$j]"
                align[i, j] = NaN
            else
                align[i, j] = real(conj(Si_ki) * Sj_ki) / (mag_i * mag_j)
            end
        end
    end
    return (align, k_stars, S_hats)
end

"""
    null_alignment_stats(n_null::Int, rng::AbstractRNG) -> (mean, std, samples)

Calibration baseline: align[i,j] values you'd see for n_null pairs of
INDEPENDENT UNIFORM-RANDOM phases on the unit circle -- i.e.
Re[conj(exp(i*theta_1)) * exp(i*theta_2)] = cos(theta_2 - theta_1) for
theta_1, theta_2 ~ Uniform(0, 2pi) independently. This is what the
off-diagonal align[i,j] entries SHOULD look like if D_j's phase at
D_i's peak frequency really is unrelated to D_i's own phase there --
mean 0, spread determined by the arcsine-type distribution of
cos(uniform), NOT by the number of characters/B in either set (this
is a single-phase-difference statistic, not a sum, so it does not
concentrate around 0 the way an M8-type aggregate would).
"""
function null_alignment_stats(n_null::Int, rng::AbstractRNG)
    theta1 = rand(rng, n_null) .* (2pi)
    theta2 = rand(rng, n_null) .* (2pi)
    samples = cos.(theta2 .- theta1)
    return (mean(samples), std(samples), samples)
end

"""
    run_cross_alignment_check(; N, qs, base_seed=1, n_null=100_000)

Full pipeline: build the requested Singer sets (build_singer_sets),
compute the cross-alignment matrix (cross_alignment_matrix), print it,
compute the null calibration (null_alignment_stats), and report
whether the off-diagonal entries look like genuine anti-alignment
(cancellation-friendly), genuine alignment (cancellation-hostile --
"family resonance"), or statistically indistinguishable from
independent random phases (cancellation is a coin flip, not a
structural effect) -- see module docstring for the three-way reading.

Uses a two-sided comparison against the null spread (not just sign):
an off-diagonal mean much more negative than the null's spread would
predict by chance is evidence FOR the naive cancellation proposal; a
mean much more positive is evidence AGAINST it (resonance, not
independence); a mean and spread consistent with the null means the
data available here can't distinguish the two, and either outcome on
a specific pair should be treated as a coincidence of that specific
pair, not a general property to build the union experiment on.
"""
function run_cross_alignment_check(; N::Int, qs::Vector{Int}, base_seed::Int = 1, n_null::Int = 100_000,
                                       confinement_guard_frac::Float64 = 0.15)
    m = length(qs)
    @assert m >= 2 "need at least 2 Singer sets to test cross-alignment"

    println("=== Cross-alignment check: $m independent Singer sets, N=$N " *
            "(confinement_guard_frac=$confinement_guard_frac) ===")
    println("qs = $qs (repeats are independent constructions of the same abstract group -- " *
            "different random cubic/generator each time)")

    sets = build_singer_sets(N, qs; base_seed = base_seed)
    for (i, s) in enumerate(sets)
        @printf("  set %d: q=%d Nq=%d B=%d seed=%d sidon_defect=%d\n",
                i, s.q, s.Nq, s.B, s.seed, s.defect)
    end

    align, k_stars, _ = cross_alignment_matrix(sets, N; confinement_guard_frac = confinement_guard_frac)

    println("\nOwn dominant frequencies k_i* (confinement-guarded -- see dominant_frequency's " *
            "docstring on why this excludes low-k confinement artifacts):")
    for (i, k) in enumerate(k_stars)
        @printf("  set %d: k_%d* = %d\n", i, i, k)
    end

    println("\nCross-alignment matrix (align[i,j] = cos of phase difference between set i's\n" *
            "own contribution to k_i* and set j's contribution to that SAME frequency;\n" *
            "diagonal is always 1.0 by construction, see docstring):")
    print("      ")
    for j in 1:m
        @printf("  set%-2d ", j)
    end
    println()
    for i in 1:m
        @printf("set%-2d ", i)
        for j in 1:m
            v = align[i, j]
            if isnan(v)
                print("   NaN  ")
            else
                @printf(" %+.3f ", v)
            end
        end
        println()
    end

    off_diag = Float64[]
    for i in 1:m, j in 1:m
        if i != j && !isnan(align[i, j])
            push!(off_diag, align[i, j])
        end
    end
    n_off = length(off_diag)
    mean_off = mean(off_diag)
    std_off = std(off_diag)

    rng_null = MersenneTwister(base_seed + 12345)
    mean_null, std_null, _ = null_alignment_stats(n_null, rng_null)

    @printf("\nOff-diagonal summary: mean=%.4f std=%.4f (n=%d pairs)\n", mean_off, std_off, n_off)
    @printf("Null (independent random phase) baseline: mean=%.4f std=%.4f (n=%d draws)\n",
            mean_null, std_null, n_null)

    # Two-sided z-like comparison: is the off-diagonal mean far from 0
    # relative to the SPREAD the null predicts for a sample of size
    # n_off (std_null / sqrt(n_off) is the null's standard error at
    # this sample size)? Small n_off (few sets -> few pairs) means
    # this has little power -- flagged explicitly, not silently
    # under-reported as a confident verdict.
    se_null = std_null / sqrt(max(n_off, 1))
    z = mean_off / se_null

    println("\n--- Verdict ---")
    if n_off < 6
        println("Only $n_off off-diagonal pairs -- too few for a statistically confident")
        println("verdict either way. Increase the number of Singer sets (qs) before trusting")
        println("the sign/magnitude of mean_off as a general property of this family.")
    elseif z < -2.0
        println("Off-diagonal mean is significantly NEGATIVE (z=$( round(z, digits=2) )):")
        println("cross-set phases at each other's peaks look systematically ANTI-aligned,")
        println("more than chance predicts. This SUPPORTS the naive cancellation proposal --")
        println("building the union experiment (with a Sidon-compatibility check across sets)")
        println("is worth doing next.")
    elseif z > 2.0
        println("Off-diagonal mean is significantly POSITIVE (z=$( round(z, digits=2) )):")
        println("cross-set phases at each other's peaks look systematically ALIGNED, more")
        println("than chance predicts -- this is 'family resonance': these Singer sets tend")
        println("to reinforce, not cancel, each other's peaks. Unioning would likely make M8")
        println("WORSE, not better. Worth understanding WHY before trying anyway (possibly")
        println("tied to the same underlying q or trace-zero condition shared across")
        println("constructions) rather than proceeding to the union experiment as-is.")
    else
        println("Off-diagonal mean is statistically indistinguishable from the independent-")
        println("random-phase null (z=$( round(z, digits=2) )). Cross-set phase relationships at")
        println("each other's peaks look like independent random draws -- no systematic")
        println("cancellation OR reinforcement to exploit. A union experiment could still get")
        println("lucky on any given seed, but there is no structural reason to expect it to")
        println("work reliably, and this is not a solid premise to build the (more expensive)")
        println("union experiment on without first finding a DIFFERENT reason to expect")
        println("cancellation (e.g. a deliberately chosen anti-aligned CONSTRUCTION, not a")
        println("randomly drawn independent one -- which is a different, harder proposal than")
        println("'independent Singer sets happen to cancel').")
    end

    return (; sets, align, k_stars, off_diag, mean_off, std_off, mean_null, std_null, z)
end

if abspath(PROGRAM_FILE) == @__FILE__
    # Real-constraint regime (target_q_exponent=0.2-ish q's) at a
    # moderate N so compute_full_spectrum (O(N*B) per set, times m
    # sets) stays cheap -- same N scale phi_diagnostic.jl's own runs
    # use.
    N = 2_000_000

    println("### Run A: repeated q (same abstract group Z/Nq, independent random ###")
    println("###         cubic/generator each time) -- tests whether resonance persists ###")
    println("###         across independent constructions of the SAME q. ###\n")
    q_repeat = largest_prime_leq(max(2, floor(Int, N^0.2)))
    run_cross_alignment_check(; N = N, qs = fill(q_repeat, 5), base_seed = 1)

    println("\n\n### Run B: varied q (different abstract groups / Nq's) -- tests whether ###")
    println("###         varying the group itself changes the picture. ###\n")
    # A handful of distinct primes near the target_q_exponent=0.2 scale
    # for N=2_000_000 (q_target ~ 18), picked as the largest prime <=
    # a few nearby targets so Nq varies across sets while all satisfy
    # the N >= 2*(Nq-1) embedding guard.
    q_targets = [12, 15, 18, 22, 26]
    qs_varied = [largest_prime_leq(t) for t in q_targets]
    run_cross_alignment_check(; N = N, qs = qs_varied, base_seed = 100)

    println("\n(Rerun with more sets / different base_seed / larger N before treating a")
    println("single run's verdict as conclusive -- this is a first pass, same caveat as")
    println("phi_diagnostic.jl's own smoke tests.)")
end
