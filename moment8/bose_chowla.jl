#!/usr/bin/env julia
#
# bose_chowla.jl
#
# FOLLOWS FROM: resonance_sign_survey.jl found that EVERY tested
# resonant q (11 through 67) gives the SAME sign (positive/reinforcing)
# for same-q restricted_align among Singer sets -- 15/15, with a
# visible monotonic trend, not scatter. Combined with
# cross_singer_alignment.jl's shift_test (translating D by t does not
# flip the sign either, across the FULL range of t), this points at
# the phase-lock being a structural consequence of the SPECIFIC
# algebraic mechanism Singer sets use (trace-zero condition over the
# degree-3 extension F_{q^3}, tied to the norm map), not something
# that varies by q or by which random draw/shift you pick within that
# mechanism.
#
# THIS SCRIPT tries a DIFFERENT Sidon-set construction with a
# DIFFERENT algebraic mechanism, per Bose (1942)/Bose-Chowla: instead
# of the degree-3 extension F_{q^3} and a trace-to-F_q condition
# (projective geometry), Bose's construction uses the degree-2
# extension F_{q^2} and a coset-membership condition (affine
# geometry):
#
#   Let theta be a generator (primitive element) of F_{q^2}^* (cyclic,
#   order q^2-1). Define
#     A(q,theta) = { a in Z_{q^2-1} : theta^a - theta  in  F_q }
#   (i.e. theta^a - theta has zero coefficient on the non-scalar basis
#   element once written in the (1, alpha) basis of F_{q^2} over F_q,
#   for alpha a root of the defining irreducible quadratic).
#   |A(q,theta)| = q, and A(q,theta) is Sidon in Z_{q^2-1} (Bose 1942;
#   see also Bose-Chowla's Bose_h generalization). This is a
#   genuinely different mechanism from Singer's trace-zero-over-a-
#   cubic condition -- worth testing because there's no a priori
#   reason its phase relationships should be governed by the same
#   norm/trace identity that locked the Singer family together.
#
# WHAT THIS SCRIPT DOES:
#   1. Implements bose_chowla_subset_native(q, rng) -> (A, Mq) mirroring
#      singer_sidon_subset_native's structure (random defining
#      polynomial + random generator each call, verified against ALL
#      prime factors of the full group order, same fix Singer's
#      construction needed -- see that function's GENERATOR NOTE).
#   2. Verifies sidon_defect(A, N) == 0 after embedding, same
#      discipline as every other strategy in this project.
#   3. Runs the SAME resonance_check + same-q restricted_align sign
#      test as resonance_sign_survey.jl, across a spread of q's, so
#      the Bose-Chowla sign pattern is directly comparable to the
#      Singer one already measured.
#
# WHAT THIS DOES NOT DO: doesn't yet test Bose-Chowla against Singer
# sets in cross_singer_alignment.jl's cross-family sense (does a
# Bose-Chowla set cancel a SINGER set's anomalous mass) -- that's the
# natural next step if this script finds Bose-Chowla's own sign
# pattern differs from Singer's, since a construction that resonates
# with itself but not with Singer sets would still be exactly what's
# needed for a cancelling union.

using Printf
using Statistics
using Random

include("strategy_comparison.jl")   # largest_prime_leq, prime_factors, compute_full_spectrum,
                                     # top_k_peaks, sidon_defect -- reused as-is

"""
    gf_q2_irreducible_quadratic(q::Int, rng::AbstractRNG) -> (d0, d1)

Finds a random monic irreducible quadratic x^2 + d1*x + d0 over F_q
(i.e. no root in F_q), mirroring gf_q_irreducible_cubic's
has_root-by-brute-force approach (cheap: O(q) per candidate, and a
constant fraction of monic quadratics over F_q are irreducible, so
O(1) expected candidates).
"""
function gf_q2_irreducible_quadratic(q::Int, rng::AbstractRNG)
    has_root(d0, d1) = any(mod(x^2 + d1*x + d0, q) == 0 for x in 0:(q-1))
    while true
        d0 = rand(rng, 0:(q-1))
        d1 = rand(rng, 0:(q-1))
        if !has_root(d0, d1)
            return (d0, d1)
        end
    end
end

"""
    bose_chowla_subset_native(q::Int, rng::AbstractRNG) -> (A::Vector{Int}, Mq::Int)

Builds a genuine Bose-Chowla Sidon set A subset Z/Mq (Mq = q^2-1,
|A| = q) for prime power q, by explicit F_{q^2} arithmetic.

F_{q^2} elements are represented as coefficient pairs (a0, a1) meaning
a0 + a1*alpha, with alpha^2 = -(d1*alpha + d0) mod q for a random
irreducible monic quadratic found above (mirrors singer_sidon_subset_
native's cubic-coefficient-triple representation one degree down).

`theta` is found as a generator of the FULL group F_{q^2}^* (order
q^2-1), verified against ALL prime factors of q^2-1 -- same discipline
as singer_sidon_subset_native's GENERATOR NOTE fix (that function
documents a real bug from an earlier, insufficiently-verified
generator search; this reuses the same all-prime-factors check from
the start rather than risk repeating it).

A(q,theta) = { a in 0:(Mq-1) : theta^a - theta has zero alpha-
coefficient }, i.e. theta^a and theta agree in their alpha-coordinate
-- equivalently theta^a - theta lands in the scalar (F_q) subfield.
Matches the definition in Bose's construction / the Bose-Chowla
survey literature exactly (A(q,theta) := {a : theta^a - theta in F_q}).

Cost: O(Mq) = O(q^2) field multiplications for the power table --
comparable in spirit to Singer's O(Nq)=O(B^2) budget (there B=q+1;
here |A|=q, Mq=q^2-1, so this is O(Mq) = O(|A|^2) too).
"""
function bose_chowla_subset_native(q::Int, rng::AbstractRNG)
    Mq = q^2 - 1
    d0, d1 = gf_q2_irreducible_quadratic(q, rng)

    reduce2(a0, a1) = (mod(a0, q), mod(a1, q))

    function mul(u, v)
        u0, u1 = u
        v0, v1 = v
        # (u0 + u1*alpha)(v0 + v1*alpha) = u0*v0 + (u0*v1+u1*v0)*alpha + u1*v1*alpha^2
        # alpha^2 = -(d1*alpha + d0)
        p0 = u0*v0
        p1 = u0*v1 + u1*v0
        p2 = u1*v1
        r0 = p0 + p2*(-d0)
        r1 = p1 + p2*(-d1)
        return reduce2(r0, r1)
    end

    function fpow(v, e)
        result = (1, 0)
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

    Mfull_prime_factors = prime_factors(Mq)

    theta = nothing
    while theta === nothing
        v = (rand(rng, 0:(q-1)), rand(rng, 0:(q-1)))
        v == (0, 0) && continue
        if fpow(v, Mq) == (1, 0) &&
           all(r -> fpow(v, Mq ÷ r) != (1, 0), Mfull_prime_factors)
            theta = v
        end
    end

    # theta itself, as a field element (0 + 1*alpha), needed for the
    # "theta^a - theta in F_q" membership test below.
    theta_elem = (0, 1)

    # Power table theta^0 .. theta^(Mq-1).
    powers = Vector{NTuple{2,Int}}(undef, Mq)
    powers[1] = (1, 0)
    for i in 2:Mq
        powers[i] = mul(powers[i-1], theta)
    end

    A = Int[]
    for a in 0:(Mq-1)
        p0, p1 = powers[a+1]
        # theta^a - theta = (p0 - 0) + (p1 - 1)*alpha ; membership in
        # F_q means the alpha-coefficient is 0, i.e. p1 == 1.
        if mod(p1 - theta_elem[2], q) == 0
            push!(A, a)
        end
    end

    return (A, Mq)
end

"""
    resonance_check_bc(N::Int, q::Int; top_frac::Float64 = 0.01, seed::Int = 1)

Same confinement-scale + clustering test as resonance_sign_survey.jl's
resonance_check, but for a Bose-Chowla set instead of a Singer set
(the mod-reduction is against Mq = q^2-1 here, not Nq = q^2+q+1).
"""
function resonance_check_bc(N::Int, q::Int; top_frac::Float64 = 0.01, seed::Int = 1)
    rng = MersenneTwister(seed)
    A, Mq = bose_chowla_subset_native(q, rng)
    @assert N >= 2 * (Mq - 1) "q=$q: Mq=$Mq too close to N=$N for a valid embedding"
    defect = sidon_defect(A, N)
    if defect != 0
        @warn "q=$q seed=$seed: nonzero sidon_defect=$defect -- resonance_check_bc untrustworthy here"
    end

    S_hat = compute_full_spectrum(A, N)
    top_ks, _, _ = top_k_peaks(S_hat, N; top_frac = top_frac)
    n_top = length(top_ks)

    approx_period = N / Mq
    dist(k) = abs(mod(k / approx_period, 1.0) - round(mod(k / approx_period, 1.0)))
    mean_dist_to_grid = mean(dist(k) for k in top_ks)
    rng2 = MersenneTwister(seed + 999)
    null_ks = rand(rng2, 1:(N-1), n_top)
    mean_dist_null = mean(dist(k) for k in null_ks)

    residues = [mod(k, Mq) for k in top_ks]
    n_distinct = length(unique(residues))

    not_confinement = mean_dist_to_grid >= 0.5 * mean_dist_null
    clustered = n_distinct < 0.5 * n_top
    is_resonant = not_confinement && clustered

    return (; mean_dist_to_grid, mean_dist_null, n_distinct, n_top, Mq, defect, is_resonant)
end

"""
    same_q_restricted_align_bc(N::Int, q::Int; top_frac::Float64 = 0.01,
                                seed_a::Int, seed_b::Int)

Same shared-grid restricted_align statistic as
resonance_sign_survey.jl's same_q_restricted_align, but for two
independent Bose-Chowla draws of the same q instead of two independent
Singer draws.
"""
function same_q_restricted_align_bc(N::Int, q::Int; top_frac::Float64 = 0.01,
                                      seed_a::Int = 1, seed_b::Int = 2)
    rng_a = MersenneTwister(seed_a)
    A_a, Mq = bose_chowla_subset_native(q, rng_a)
    rng_b = MersenneTwister(seed_b)
    A_b, Mq_b = bose_chowla_subset_native(q, rng_b)
    @assert Mq == Mq_b "same q must give same Mq -- got $Mq vs $Mq_b"
    @assert N >= 2 * (Mq - 1) "q=$q: Mq=$Mq too close to N=$N for a valid embedding"

    defect_a = sidon_defect(A_a, N)
    defect_b = sidon_defect(A_b, N)
    if defect_a != 0 || defect_b != 0
        @warn "q=$q: nonzero sidon_defect (a=$defect_a, b=$defect_b) -- result untrustworthy"
    end

    S_hat_a = compute_full_spectrum(A_a, N)
    S_hat_b = compute_full_spectrum(A_b, N)
    top_ks_a, _, _ = top_k_peaks(S_hat_a, N; top_frac = top_frac)
    top_ks_b, _, _ = top_k_peaks(S_hat_b, N; top_frac = top_frac)

    res_a = Set(mod(k, Mq) for k in top_ks_a)
    res_b = Set(mod(k, Mq) for k in top_ks_b)
    shared = intersect(res_a, res_b)
    union_sz = length(union(res_a, res_b))
    jaccard = union_sz == 0 ? NaN : length(shared) / union_sz

    ks_a_shared = [k for k in top_ks_a if mod(k, Mq) in shared]
    ks_b_shared = [k for k in top_ks_b if mod(k, Mq) in shared]
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
    run_bc_sign_survey(; N::Int, qs::Vector{Int}, top_frac::Float64 = 0.01)

Same two-step pipeline as resonance_sign_survey.jl's run_sign_survey
(resonance_check_bc to filter to genuinely resonant q's, then
same_q_restricted_align_bc for the sign), reported the same way so the
Bose-Chowla sign table is directly comparable line-for-line against
the Singer sign table already measured.
"""
function run_bc_sign_survey(; N::Int, qs::Vector{Int}, top_frac::Float64 = 0.01)
    println("=== Bose-Chowla resonance sign survey: N=$N, qs=$qs, top_frac=$top_frac ===\n")
    println("Step 1: resonance_check_bc per q\n")

    resonant_qs = Int[]
    for q in qs
        rc = resonance_check_bc(N, q; top_frac = top_frac)
        pct_distinct = 100 * rc.n_distinct / rc.n_top
        @printf("  q=%-4d Mq=%-7d dist_to_grid=%.4f (null=%.4f)  %d/%d distinct residues (%.1f%%)  -> %s\n",
                q, rc.Mq, rc.mean_dist_to_grid, rc.mean_dist_null, rc.n_distinct, rc.n_top,
                pct_distinct, rc.is_resonant ? "RESONANT" : "confinement-dominated, SKIPPING")
        rc.is_resonant && push!(resonant_qs, q)
    end

    if isempty(resonant_qs)
        println("\nNo resonant q's found in this sweep for Bose-Chowla -- nothing to test for sign.")
        return NamedTuple[]
    end

    println("\nStep 2: same-q restricted_align (two independent draws per q) for the")
    println("resonant q's only: $resonant_qs\n")
    @printf("  %6s  %10s  %10s  %17s  %10s\n", "q", "Mq", "jaccard", "restricted_align", "n_shared")

    results = NamedTuple[]
    for q in resonant_qs
        r = same_q_restricted_align_bc(N, q; top_frac = top_frac)
        @printf("  %6d  %10d  %10.3f  %+17.3f  %10d\n",
                q, q^2 - 1, r.jaccard, r.restricted_align, r.n_shared)
        push!(results, (; q, r.jaccard, r.restricted_align, r.n_shared))
    end

    println("\n--- Sign summary (Bose-Chowla) ---")
    signs = [sign(r.restricted_align) for r in results if !isnan(r.restricted_align)]
    n_pos = count(==(1.0), signs)
    n_neg = count(==(-1.0), signs)
    n_tested = length(signs)
    @printf("  %d/%d resonant q's tested gave POSITIVE restricted_align, %d/%d NEGATIVE\n",
            n_pos, n_tested, n_neg, n_tested)
    if n_neg == 0
        println("  -> same qualitative picture as Singer sets: fixed positive sign. The")
        println("     phase-lock is not specific to Singer's trace-zero mechanism -- it may be a")
        println("     more general feature of algebraic difference-set constructions, which")
        println("     would be an important (if discouraging) finding in its own right.")
    elseif n_pos == 0
        println("  -> every tested q gives NEGATIVE restricted_align for Bose-Chowla. Interesting")
        println("     on its own, but the real test is Bose-Chowla vs SINGER cross-alignment --")
        println("     a same-family negative sign doesn't by itself mean it cancels a Singer set.")
    else
        println("  -> MIXED signs -- worth pairing a positive-sign Bose-Chowla q with a")
        println("     negative-sign one, same as the Singer case.")
    end
    println("\n  Regardless of sign here, the NEXT real test is Bose-Chowla vs SINGER: does a")
    println("  Bose-Chowla set's anomalous mass align or decorrelate against a Singer set's,")
    println("  at whatever frequencies each is resonant on -- that cross-family comparison is")
    println("  what actually matters for a cancelling union, not either family's self-alignment")
    println("  alone. Not yet implemented here (Bose-Chowla and Singer sets live on different")
    println("  native moduli, Mq=q^2-1 vs Nq=q^2+q+1, so a direct residue-overlap comparison")
    println("  needs both embedded in the same N first, same as cross_singer_alignment.jl does")
    println("  for two different q's -- worth building as a follow-up if this survey looks")
    println("  promising.)")

    return results
end

if abspath(PROGRAM_FILE) == @__FILE__
    N = 2_000_000
    # Same spread of small primes as resonance_sign_survey.jl, for a
    # direct side-by-side comparison. Mq = q^2-1 grows at the same
    # rate as Singer's Nq = q^2+q+1 (both ~q^2), so the same top_frac/
    # N choice keeps n_top well above Mq across this whole range too.
    qs = [11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67]
    run_bc_sign_survey(; N = N, qs = qs, top_frac = 0.01)

    println("\n(First pass -- rerun with more/different seeds per q before treating any")
    println("single q's sign as conclusive, same caveat as everywhere else in this project.)")
end
