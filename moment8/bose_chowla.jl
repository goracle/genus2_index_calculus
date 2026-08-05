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
    bose_chowla_power_table(q::Int, rng::AbstractRNG) -> (powers, theta, Mq, q)

Shared setup for the whole Bose(q,theta,k) family at a fixed (q,theta):
finds a random irreducible quadratic defining F_{q^2}, finds a
generator theta of the FULL group F_{q^2}^* (order q^2-1, verified
against ALL prime factors -- same discipline as singer_sidon_subset_
native's GENERATOR NOTE fix), and builds the power table theta^0 ..
theta^(Mq-1).

This is the expensive O(Mq) = O(q^2) part. Factored out so a k-sweep
at fixed (q,theta) -- varying only which k in F_q\\{0} defines the
membership condition below -- does this work ONCE and reuses it across
every k, instead of redoing an O(Mq) power table per k.

Returns theta as (0,1)-basis coefficients (v0,v1) so callers have the
actual field element used, not an assumed (0,1) -- see
bose_chowla_subset_for_k's docstring for why that distinction matters.
"""
function bose_chowla_power_table(q::Int, rng::AbstractRNG)
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

    # Power table theta^0 .. theta^(Mq-1).
    powers = Vector{NTuple{2,Int}}(undef, Mq)
    powers[1] = (1, 0)
    for i in 2:Mq
        powers[i] = mul(powers[i-1], theta)
    end

    return (powers, theta, Mq, q)
end

"""
    bose_chowla_subset_for_k(powers, theta, Mq, q, k::Int) -> A::Vector{Int}

Extracts Bose(q,theta,k) = { a in 0:(Mq-1) : theta^a - k*theta in F_q }
from a power table already built by bose_chowla_power_table. This is
the cheap O(Mq) membership scan, reused across every k at fixed
(q,theta) -- k only enters here.

theta^a - k*theta = (p0 - k*theta[1]) + (p1 - k*theta[2])*alpha, where
(p0,p1) = powers[a+1] and (theta[1],theta[2]) is theta's OWN (v0,v1)
coefficient pair as actually found by bose_chowla_power_table (theta
is a general random field element there, NOT hardcoded to (0,1)=alpha
-- an earlier version of this file assumed theta_elem=(0,1)
unconditionally, which is only correct when the found generator
happens to literally equal alpha; using theta[2] here is the fix,
verified against the k=1 case in Python before shipping). Membership
in F_q means the alpha-coefficient is 0, i.e. p1 - k*theta[2] == 0.

k=0 is excluded by convention (matches the literature's k in
F_q\\{0}; k=0 would just test theta^a in F_q, a degenerate case with
different size/structure, not part of this family).
"""
function bose_chowla_subset_for_k(powers::Vector{NTuple{2,Int}}, theta::NTuple{2,Int},
                                    Mq::Int, q::Int, k::Int)
    @assert mod(k, q) != 0 "k must be nonzero mod q (k in F_q \\ {0})"
    theta_alpha_coeff = theta[2]
    kk = mod(k, q)

    A = Int[]
    for a in 0:(Mq-1)
        p0, p1 = powers[a+1]
        if mod(p1 - kk * theta_alpha_coeff, q) == 0
            push!(A, a)
        end
    end
    return A
end

"""
    bose_chowla_subset_native(q::Int, rng::AbstractRNG; k::Int = 1) -> (A::Vector{Int}, Mq::Int)

Builds a genuine Bose-Chowla Sidon set A subset Z/Mq (Mq = q^2-1,
|A| = q) for prime power q, by explicit F_{q^2} arithmetic --
Bose(q,theta,k) = { a : theta^a - k*theta in F_q } for the requested k
(k=1 by default, matching every call site elsewhere in this project
before the k-sweep existed).

Thin wrapper around bose_chowla_power_table + bose_chowla_subset_for_k
for callers that just want a single (q,k) pair and don't care about
reusing the power table across multiple k's -- kept so existing
call sites (resonance_check_bc, same_q_restricted_align_bc) work
unchanged. For an actual k-sweep at fixed (q,theta), call
bose_chowla_power_table once and bose_chowla_subset_for_k per k
instead, to avoid redoing the O(Mq) power table for every k.
"""
function bose_chowla_subset_native(q::Int, rng::AbstractRNG; k::Int = 1)
    powers, theta, Mq, _ = bose_chowla_power_table(q, rng)
    A = bose_chowla_subset_for_k(powers, theta, Mq, q, k)
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
    shared_grid_restricted_align(S_hat_a, S_hat_b, Mq::Int, N::Int; top_frac::Float64 = 0.01)
        -> (; jaccard, restricted_align, n_shared)

The shared-grid restricted_align core math, factored out of
same_q_restricted_align_bc so it can be reused unchanged for the k-
sweep case (two DIFFERENT k's at fixed q,theta) instead of duplicating
it. Takes two already-computed spectra and the common Mq they should
both be reduced mod -- everything downstream of "I have two spectra
and a modulus" is identical whether the two sets being compared came
from independent (q,theta) draws or from the same (q,theta) at two
different k's.
"""
function shared_grid_restricted_align(S_hat_a::Vector{ComplexF64}, S_hat_b::Vector{ComplexF64},
                                        Mq::Int, N::Int; top_frac::Float64 = 0.01)
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
    k_sweep_pair_align(N::Int, q::Int, k_a::Int, k_b::Int; top_frac::Float64 = 0.01,
                        seed::Int = 1)

THE k-SWEEP TEST: holds (q, theta) FIXED (single power table, single
seed) and compares Bose(q,theta,k_a) against Bose(q,theta,k_b) -- i.e.
only k varies, not the whole algebraic setup. This isolates k's effect
on the cross-alignment sign cleanly, unlike varying q (which changes
Mq, the field, everything at once) or independently redrawing theta
(which changes the generator too).

Builds the power table ONCE via bose_chowla_power_table and extracts
both k_a's and k_b's sets from it via bose_chowla_subset_for_k, per
the efficient design in that function's docstring -- a k-sweep across
many k's at fixed (q,theta) should call bose_chowla_power_table once
and reuse it, not redo the O(Mq) table per k (see
run_k_sweep below for the multi-k driver that does this properly).

Reuses shared_grid_restricted_align for the actual alignment
statistic, same as same_q_restricted_align_bc.
"""
function k_sweep_pair_align(N::Int, q::Int, k_a::Int, k_b::Int; top_frac::Float64 = 0.01,
                              seed::Int = 1)
    rng = MersenneTwister(seed)
    powers, theta, Mq, _ = bose_chowla_power_table(q, rng)
    @assert N >= 2 * (Mq - 1) "q=$q: Mq=$Mq too close to N=$N for a valid embedding"

    A_a = bose_chowla_subset_for_k(powers, theta, Mq, q, k_a)
    A_b = bose_chowla_subset_for_k(powers, theta, Mq, q, k_b)

    defect_a = sidon_defect(A_a, N)
    defect_b = sidon_defect(A_b, N)
    if defect_a != 0 || defect_b != 0
        @warn "q=$q k_a=$k_a k_b=$k_b: nonzero sidon_defect (a=$defect_a, b=$defect_b) -- result untrustworthy"
    end

    S_hat_a = compute_full_spectrum(A_a, N)
    S_hat_b = compute_full_spectrum(A_b, N)

    return shared_grid_restricted_align(S_hat_a, S_hat_b, Mq, N; top_frac = top_frac)
end

"""
    run_k_sweep(; N::Int, q::Int, ks::Vector{Int} = collect(1:(q-1)),
                  top_frac::Float64 = 0.01, seed::Int = 1, k_ref::Int = 1)

Driver for the k-sweep: fixes (q, theta) via a SINGLE
bose_chowla_power_table call (seeded by `seed`), then for every k in
`ks` compares Bose(q,theta,k) against the reference Bose(q,theta,k_ref)
(k_ref=1 by default, matching every prior call site's implicit
convention). Reports restricted_align per k so the sign pattern across
the whole k in F_q\\{0} sweep is visible at a glance -- the goal being
to find ANY k whose set anti-aligns (negative restricted_align)
against k_ref=1, unlike every q tried so far in run_bc_sign_survey.

This is deliberately NOT same-q-independent-draws (that's what
same_q_restricted_align_bc / run_bc_sign_survey already test, and
found always-positive) -- it isolates k as the single free variable at
fixed (q,theta), per the plan: q and independent redraws already
failed to flip the sign, k is the next (and, per Bose's own
construction, genuinely different-per-k) lever to try.

Prints a full sign summary at the end, same style as
run_bc_sign_survey, so a negative-sign k (if found) stands out clearly.
"""
function run_k_sweep(; N::Int, q::Int, ks::Vector{Int} = collect(1:(q-1)),
                        top_frac::Float64 = 0.01, seed::Int = 1, k_ref::Int = 1)
    println("=== Bose-Chowla k-sweep: N=$N, q=$q (Mq=$(q^2-1)), k_ref=$k_ref, ks=$ks, seed=$seed ===\n")
    println("Fixed (q,theta) via a single power-table build; only k varies below.\n")

    rng = MersenneTwister(seed)
    powers, theta, Mq, _ = bose_chowla_power_table(q, rng)
    @assert N >= 2 * (Mq - 1) "q=$q: Mq=$Mq too close to N=$N for a valid embedding"

    A_ref = bose_chowla_subset_for_k(powers, theta, Mq, q, k_ref)
    defect_ref = sidon_defect(A_ref, N)
    if defect_ref != 0
        @warn "q=$q k_ref=$k_ref: nonzero sidon_defect=$defect_ref -- reference set untrustworthy"
    end
    S_hat_ref = compute_full_spectrum(A_ref, N)

    @printf("  %6s  %10s  %10s  %17s  %10s\n", "k", "|A_k|", "jaccard", "restricted_align", "n_shared")

    results = NamedTuple[]
    for k in ks
        if mod(k, q) == mod(k_ref, q)
            continue   # skip comparing k_ref against itself
        end
        A_k = bose_chowla_subset_for_k(powers, theta, Mq, q, k)
        defect_k = sidon_defect(A_k, N)
        if defect_k != 0
            @warn "q=$q k=$k: nonzero sidon_defect=$defect_k -- this k's result untrustworthy"
        end
        S_hat_k = compute_full_spectrum(A_k, N)
        r = shared_grid_restricted_align(S_hat_ref, S_hat_k, Mq, N; top_frac = top_frac)
        @printf("  %6d  %10d  %10.3f  %+17.3f  %10d\n",
                k, length(A_k), r.jaccard, r.restricted_align, r.n_shared)
        push!(results, (; k, r.jaccard, r.restricted_align, r.n_shared))
    end

    println("\n--- Sign summary (k-sweep, vs k_ref=$k_ref) ---")
    signs = [sign(r.restricted_align) for r in results if !isnan(r.restricted_align)]
    n_pos = count(==(1.0), signs)
    n_neg = count(==(-1.0), signs)
    n_tested = length(signs)
    @printf("  %d/%d k's tested gave POSITIVE restricted_align (vs k_ref), %d/%d NEGATIVE\n",
            n_pos, n_tested, n_neg, n_tested)
    if n_neg == 0
        println("  -> still all-positive: varying k at fixed (q,theta) did NOT flip the sign")
        println("     for this q. Worth trying other q's before concluding k is a dead end --")
        println("     the sign might depend on q mod something (cf. quadratic Gauss sum sign")
        println("     depending on q mod 4) rather than being uniformly unfixable via k alone.")
    else
        neg_ks = [r.k for r in results if !isnan(r.restricted_align) && r.restricted_align < 0]
        println("  -> FOUND negative-sign k's: $neg_ks -- this is exactly the lever needed.")
        println("     Next: check whether Bose(q,theta,k) for a negative k here also anti-aligns")
        println("     against a SINGER set (the real target), not just against k_ref within its")
        println("     own Bose-Chowla family -- same-family anti-alignment doesn't guarantee")
        println("     cross-family anti-alignment against Singer.")
    end

    return results
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

    println("\n\n### k-sweep: fixed q, holding (q,theta) fixed and varying k across F_q\\{0} ###")
    println("###           to test the one lever not yet tried (q and independent redraws ###")
    println("###           both already gave all-positive sign, per the survey above and ###")
    println("###           cross_singer_alignment.jl's shift_test). ###\n")
    run_k_sweep(; N = N, q = 17, seed = 1, top_frac = 0.01)

    println("\n(Single q=17 pass -- if this comes back all-positive too, rerun run_k_sweep on")
    println("other resonant q's from the survey above (e.g. q=11, q=53) before concluding k")
    println("doesn't help; the sign may depend on q itself, not be uniformly fixed by any lever.)")
end
