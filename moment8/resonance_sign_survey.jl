#!/usr/bin/env julia
#
# resonance_sign_survey.jl
#
# FOLLOWS FROM: cross_singer_alignment.jl's shift_test found that
# translating one q=17 Singer set's D (mod Nq) before embedding does
# NOT flip the sign of restricted_align against a second, independent
# q=17 draw -- restricted_align stayed strongly positive (+0.51 to
# +0.84) across the FULL range of shifts t in [0, Nq). That rules out
# "the phase-lock is a simple translation artifact" and points at
# something translation-invariant: most plausibly the trace-zero
# condition's interaction with the norm map to F_q, which doesn't
# care where in [0,Nq) you start counting.
#
# If the sign of that phase-lock really is a fixed function of q
# (rather than of the particular random construction), then no amount
# of resampling OR shifting within a single q will ever find a
# cancelling pair -- but the SIGN might still differ from one q to
# another. This script tests exactly that: for each of several small
# primes q known to show real mod-Nq clustering (not confinement, per
# phi_diagnostic.jl's confinement-scale test), build TWO independent
# Singer sets of that q (fresh random cubic/generator each, same
# pattern as cross_singer_alignment.jl's Run A) and measure
# restricted_align between them on their shared residue grid.
#
# READING THE OUTPUT:
#   - If every tested q gives POSITIVE restricted_align (like q=17's
#     +0.66 to +0.78 from cross_singer_alignment.jl), that's consistent
#     with the sign being fixed across q (e.g. by some structural
#     reason the trace-zero/norm construction always produces
#     reinforcing, not cancelling, phase relationships) -- meaning
#     cross-q cancellation by SIMPLE selection of a different q is
#     also not going to work, and the search needs to go to a genuinely
#     different lever (multiplicative shifts, a different subset
#     construction entirely, or accepting that this q-family cannot
#     self-cancel and looking outside it).
#   - If some q's give NEGATIVE restricted_align, that's the first
#     positive signal for a real union strategy: mix Singer sets built
#     from a NEGATIVE-signed q with ones from a POSITIVE-signed q,
#     re-test with cross_singer_alignment.jl's full pipeline on that
#     specific pair.
#
# WHAT THIS DOES NOT DO: doesn't yet look for a CLOSED FORM for the
# sign (e.g. a quadratic-residue/Legendre-symbol-style dependence on q
# mod small numbers, or a Gauss-sum evaluation) -- that's the natural
# next step if a sign pattern shows up here, since a closed form would
# let you pick a cancelling q directly instead of surveying.

using Printf
using Statistics
using Random

include("strategy_comparison.jl")   # singer_sidon_subset_native, compute_full_spectrum,
                                     # top_k_peaks, sidon_defect

"""
    resonance_check(N::Int, q::Int; top_frac::Float64 = 0.01)
        -> (mean_dist_to_grid::Float64, mean_dist_null::Float64,
            n_distinct::Int, n_top::Int, is_resonant::Bool)

phi_diagnostic.jl's confinement-scale test, factored out for reuse:
builds ONE Singer set of this q, checks whether its top-mass
frequencies sit near confinement-grid multiples of N/Nq (the boring,
non-algebraic explanation) or not, AND whether they cluster onto a
small set of residues mod Nq. is_resonant = true only when BOTH the
confinement test comes back negative (mean_dist_to_grid NOT
meaningfully below the null) AND the clustering test comes back
positive (n_distinct well below n_top) -- q=17 satisfied both in
phi_diagnostic.jl's own run; q=331 satisfied neither. Only resonant
q's are worth including in the sign survey below -- a q that's merely
confinement-dominated has no real phase-lock to have a sign at all.
"""
function resonance_check(N::Int, q::Int; top_frac::Float64 = 0.01, seed::Int = 1)
    rng = MersenneTwister(seed)
    D, Nq = singer_sidon_subset_native(q, rng)
    @assert N >= 2 * (Nq - 1) "q=$q: Nq=$Nq too close to N=$N for a valid embedding"
    defect = sidon_defect(D, N)
    if defect != 0
        @warn "q=$q seed=$seed: nonzero sidon_defect=$defect -- resonance_check untrustworthy here"
    end

    S_hat = compute_full_spectrum(D, N)
    top_ks, _, _ = top_k_peaks(S_hat, N; top_frac = top_frac)
    n_top = length(top_ks)

    approx_period = N / Nq
    dist(k) = abs(mod(k / approx_period, 1.0) - round(mod(k / approx_period, 1.0)))
    mean_dist_to_grid = mean(dist(k) for k in top_ks)
    rng2 = MersenneTwister(seed + 999)
    null_ks = rand(rng2, 1:(N-1), n_top)
    mean_dist_null = mean(dist(k) for k in null_ks)

    residues = [mod(k, Nq) for k in top_ks]
    n_distinct = length(unique(residues))

    not_confinement = mean_dist_to_grid >= 0.5 * mean_dist_null
    clustered = n_distinct < 0.5 * n_top
    is_resonant = not_confinement && clustered

    return (; mean_dist_to_grid, mean_dist_null, n_distinct, n_top, Nq, defect, is_resonant)
end

"""
    same_q_restricted_align(N::Int, q::Int; top_frac::Float64 = 0.01,
                             seed_a::Int, seed_b::Int)
        -> (jaccard::Float64, restricted_align::Float64, n_shared::Int)

Builds TWO independent Singer sets of the SAME q (fresh random
cubic/generator each, via seed_a and seed_b), then computes the same
jaccard-overlap-of-residues and restricted-cross-alignment-on-the-
shared-grid statistics as cross_singer_alignment.jl's
residue_overlap_report -- reimplemented standalone here (not included
from cross_singer_alignment.jl) since that file's entry point runs
its own multi-run script on inclusion and this script wants a single
reusable per-q function, not a side effect of including it.
"""
function same_q_restricted_align(N::Int, q::Int; top_frac::Float64 = 0.01,
                                   seed_a::Int = 1, seed_b::Int = 2)
    rng_a = MersenneTwister(seed_a)
    D_a, Nq = singer_sidon_subset_native(q, rng_a)
    rng_b = MersenneTwister(seed_b)
    D_b, Nq_b = singer_sidon_subset_native(q, rng_b)
    @assert Nq == Nq_b "same q must give same Nq -- got $Nq vs $Nq_b"
    @assert N >= 2 * (Nq - 1) "q=$q: Nq=$Nq too close to N=$N for a valid embedding"

    defect_a = sidon_defect(D_a, N)
    defect_b = sidon_defect(D_b, N)
    if defect_a != 0 || defect_b != 0
        @warn "q=$q: nonzero sidon_defect (a=$defect_a, b=$defect_b) -- result untrustworthy"
    end

    S_hat_a = compute_full_spectrum(D_a, N)
    S_hat_b = compute_full_spectrum(D_b, N)
    top_ks_a, _, _ = top_k_peaks(S_hat_a, N; top_frac = top_frac)
    top_ks_b, _, _ = top_k_peaks(S_hat_b, N; top_frac = top_frac)

    res_a = Set(mod(k, Nq) for k in top_ks_a)
    res_b = Set(mod(k, Nq) for k in top_ks_b)
    shared = intersect(res_a, res_b)
    union_sz = length(union(res_a, res_b))
    jaccard = union_sz == 0 ? NaN : length(shared) / union_sz

    ks_a_shared = [k for k in top_ks_a if mod(k, Nq) in shared]
    ks_b_shared = [k for k in top_ks_b if mod(k, Nq) in shared]
    ks_shared = unique(vcat(ks_a_shared, ks_b_shared))

    if isempty(ks_shared)
        return (; jaccard, restricted_align = NaN, n_shared = 0)
    end

    num = 0.0
    denom_a = 0.0
    denom_b = 0.0
    @inbounds for k in ks_shared
        sa = S_hat_a[k+1]
        sb = S_hat_b[k+1]
        num += real(conj(sa) * sb)
        denom_a += abs2(sa)
        denom_b += abs2(sb)
    end
    denom = sqrt(denom_a * denom_b)
    restricted_align = denom == 0.0 ? NaN : num / denom

    return (; jaccard, restricted_align, n_shared = length(ks_shared))
end

"""
    run_sign_survey(; N::Int, qs::Vector{Int}, top_frac::Float64 = 0.01)

Full pipeline: for each q in `qs`, first checks resonance_check (skip
q's that are confinement-dominated, not genuinely resonant -- their
restricted_align sign wouldn't mean anything), then runs
same_q_restricted_align on two fresh independent draws of that q and
reports the sign. Prints a summary table at the end so the sign
pattern (if any) is easy to read off across the whole q sweep.
"""
function run_sign_survey(; N::Int, qs::Vector{Int}, top_frac::Float64 = 0.01)
    println("=== Resonance sign survey: N=$N, qs=$qs, top_frac=$top_frac ===\n")
    println("Step 1: resonance_check per q (skip confinement-dominated q's -- no real")
    println("phase-lock to have a sign, per phi_diagnostic.jl's confinement-scale test)\n")

    resonant_qs = Int[]
    for q in qs
        rc = resonance_check(N, q; top_frac = top_frac)
        pct_distinct = 100 * rc.n_distinct / rc.n_top
        @printf("  q=%-4d Nq=%-7d dist_to_grid=%.4f (null=%.4f)  %d/%d distinct residues (%.1f%%)  -> %s\n",
                q, rc.Nq, rc.mean_dist_to_grid, rc.mean_dist_null, rc.n_distinct, rc.n_top,
                pct_distinct, rc.is_resonant ? "RESONANT" : "confinement-dominated, SKIPPING")
        rc.is_resonant && push!(resonant_qs, q)
    end

    if isempty(resonant_qs)
        println("\nNo resonant q's found in this sweep -- nothing to test for sign. Try a")
        println("different spread of q's (see phi_diagnostic.jl's target_q_exponent comments")
        println("for why small q tends to be the resonant regime at this N).")
        return NamedTuple[]
    end

    println("\nStep 2: same-q restricted_align (two independent draws per q) for the")
    println("resonant q's only: $resonant_qs\n")
    @printf("  %6s  %10s  %10s  %17s  %10s\n", "q", "Nq", "jaccard", "restricted_align", "n_shared")

    results = NamedTuple[]
    for q in resonant_qs
        r = same_q_restricted_align(N, q; top_frac = top_frac)
        @printf("  %6d  %10d  %10.3f  %+17.3f  %10d\n",
                q, q^2 + q + 1, r.jaccard, r.restricted_align, r.n_shared)
        push!(results, (; q, r.jaccard, r.restricted_align, r.n_shared))
    end

    println("\n--- Sign summary ---")
    signs = [sign(r.restricted_align) for r in results if !isnan(r.restricted_align)]
    n_pos = count(==(1.0), signs)
    n_neg = count(==(-1.0), signs)
    n_tested = length(signs)
    @printf("  %d/%d resonant q's tested gave POSITIVE restricted_align, %d/%d NEGATIVE\n",
            n_pos, n_tested, n_neg, n_tested)
    if n_neg == 0
        println("  -> every tested q shows the SAME sign (positive/reinforcing). Consistent with")
        println("     the sign being a fixed property of this construction (trace-zero + norm-map")
        println("     structure), not something that varies q-to-q in this range. Cross-q")
        println("     cancellation by simple q selection does not look promising from this data --")
        println("     next step would be a genuinely different lever (multiplicative shift of D,")
        println("     or a closed-form check of WHY the sign is fixed) rather than a wider q sweep.")
    elseif n_pos == 0
        println("  -> every tested q shows the SAME sign (negative/cancelling). Surprising given")
        println("     q=17 (from cross_singer_alignment.jl) was positive -- re-check for a bug")
        println("     before trusting this.")
    else
        println("  -> MIXED signs across q's -- this is the actionable case. Pair a positive-sign")
        println("     q with a negative-sign q and re-run cross_singer_alignment.jl's full")
        println("     pipeline (or shift_test) on that specific pair to see whether their union")
        println("     actually reduces M8, rather than just reinforcing within one q-family.")
    end

    return results
end

if abspath(PROGRAM_FILE) == @__FILE__
    N = 2_000_000
    # Spread of small primes; Nq = q^2+q+1 stays well under n_top=20000
    # (top_frac=0.01 * (N-1)) for all of these, so the clustering-vs-
    # confinement test has room to distinguish real resonance from
    # coverage ceiling (see phi_diagnostic.jl's q=17 vs q=331 finding --
    # the test degrades once Nq approaches n_top).
    qs = [11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67]
    run_sign_survey(; N = N, qs = qs, top_frac = 0.01)

    println("\n(First pass -- rerun with more/different seeds per q before treating any")
    println("single q's sign as conclusive, same caveat as everywhere else in this project.)")
end
