#!/usr/bin/env julia

using Oscar

################################################################################
#
#  elim2.jl  --  Monster elimination: match u_RS/v_RS symbolic residuals
#                between two DIFFERENT K's (K=2 sample vs K=3 sample), each
#                with c=2 free symbolic anchors.
#
#  Unlike elim.jl (which hand-transcribes two already-printed rational
#  functions of a single variable t), this script never touches the printed
#  text report at all. It calls PhiSymbolic.symbolic_residual(...) directly
#  -- the same function that *produces* that printed report -- once per
#  sample, and then walks the returned residue-ring-tower elements to
#  re-express each coefficient as an element of one shared plain
#  multivariate polynomial ring
#
#      F[wa1,wa2,wb1,wb2,a1,a2,b1,b2]
#
#  building it up exactly the way _eval_tower_recursive does numerically,
#  except substituting ring generators instead of plugging in concrete
#  field values. That gives us honest Oscar polynomial objects, so the
#  final cross-multiplication / ideal / Groebner basis step is just
#  elim.jl's coeff_equal pattern, doubled up to 8 variables.
#
#  Unknowns:
#
#      sample 1 (K=2, c=2):   symbolic anchors (t1,w1) -> renamed (a1,wa1)
#                              symbolic anchors (t2,w2) -> renamed (a2,wa2)
#      sample 2 (K=3, c=2):   symbolic anchors (t1,w1) -> renamed (b1,wb1)
#                              symbolic anchors (t2,w2) -> renamed (b2,wb2)
#
#  We seek
#
#      u_RS^(K=2)(x; a1,a2)  ==  u_RS^(K=3)(x; b1,b2)     coefficient-wise
#      v_RS^(K=2)(x; a1,a2)  ==  v_RS^(K=3)(x; b1,b2)     coefficient-wise
#
################################################################################

################################################################################
# Locate and include the symbolic engine.
#
# Adjust PHI_GENERAL_SRC if your checkout lives somewhere else -- this
# assumes elim2.jl sits next to (or one level above) the phi_general/src
# directory that was unzipped from phi_general.zip.
################################################################################

const PHI_GENERAL_SRC = joinpath(ELIM2_ROOT_DIR, "phi_general", "src")

include(joinpath(PHI_GENERAL_SRC, "trial3_phi_symbolic_unified.jl"))
using .PhiSymbolic

################################################################################
# Curve / field constants -- same as elim.jl
################################################################################

const p = 2371157
const F_POLY_ASC = [2, 1, 0, 0, 0, 1]   # y^2 = x^5 + x + 2, ascending coeffs

F = GF(p)

################################################################################
# The two samples, taken verbatim from err.txt (lines 1220 and 1233 of the
# thread-2 symbolic report). Both have K-c=0, i.e. NO fixed anchors -- both
# printed symbolic anchors are free unknowns. This is exactly why we can
# call symbolic_residual with fixed_anchors = Tuple{Int,Int}[] and get the
# same rational-function-of-two-variables result that was being hand-copied
# out of the printed report before.
#
#   ### thread 2, sample 1: K=2, c=2,
#       fixed anchors = [], symbolic anchors = [(196, 793353), (1171057, 2268951)],
#       u0,u1=468873,956582  v0,v1=2168176,2288437 ###
#
#   ### thread 2, sample 2: K=3, c=2,
#       fixed anchors = [(196, 793353)], symbolic anchors = [(1664320, 277399), (691604, 1848341)],
#       u0,u1=2112189,375309  v0,v1=801778,2048138 ###
################################################################################

const K1, c1 = 2, 2
const fixed1 = Tuple{Int,Int}[]
const u0_1, u1_1, v0_1, v1_1 = 468873, 956582, 2168176, 2288437

const K2, c2 = 3, 2
const fixed2 = [(196, 793353)]
if length(fixed2) != K2 - c2
    error("elim2.jl: sample 2 (K=$K2, c=$c2) needs exactly $(K2-c2) fixed anchor(s), " *
          "got $(length(fixed2)).")
end
const u0_2, u1_2, v0_2, v1_2 = 2112189, 375309, 801778, 2048138

println("Calling PhiSymbolic.symbolic_residual for sample 1 (K=$K1, c=$c1)...")
res1 = PhiSymbolic.symbolic_residual(K1, c1, fixed1, u0_1, u1_1, v0_1, v1_1, F_POLY_ASC, p)

println("Calling PhiSymbolic.symbolic_residual for sample 2 (K=$K2, c=$c2)...")
res2 = PhiSymbolic.symbolic_residual(K2, c2, fixed2, u0_2, u1_2, v0_2, v1_2, F_POLY_ASC, p)

if isempty(res1.u_RS_coeffs) || isempty(res1.v_RS_coeffs)
    error("sample 1 (K=$K1): construction failed or degenerate -- no u_RS/v_RS to match")
end
if isempty(res2.u_RS_coeffs) || isempty(res2.v_RS_coeffs)
    error("sample 2 (K=$K2): construction failed or degenerate -- no u_RS/v_RS to match")
end

println("sample 1: deg(u_RS)=$(length(res1.u_RS_coeffs)-1)  deg(v_RS)=$(length(res1.v_RS_coeffs)-1)")
println("sample 2: deg(u_RS)=$(length(res2.u_RS_coeffs)-1)  deg(v_RS)=$(length(res2.v_RS_coeffs)-1)")

################################################################################
# Target ring: F[wa1,wa2,wb1,wb2,a2,a1,b2,b1]
#
# Plain ring construction, matching elim.jl's working pattern -- this
# Oscar/AbstractAlgebra version's polynomial_ring does not accept an
# `ordering` kwarg at all (confirmed: elim.jl never passes one, and
# passing one raises a MethodError on poly_ring internally). w's are
# declared before the a/b's, same convention as elim.jl's `w1,w2,t2,t1`,
# so that eliminate(..., [wa1,wa2,wb1,wb2]) leaves polynomials purely in
# a1,a2,b1,b2 regardless of monomial ordering.
#
# The block/product ordering idea (isolating the w's as a dominant block
# for a faster elimination-oriented Groebner computation) still applies,
# but gets passed directly to groebner_basis(...; ordering=...) below,
# at the point where this Oscar version actually supports it, rather
# than baked into the ring itself.
################################################################################

R, (wa1, wa2, wb1, wb2, a2, a1, b2, b1) = polynomial_ring(
    F,
    ["wa1", "wa2", "wb1", "wb2", "a2", "a1", "b2", "b1"]
)

# Block ordering built from R's own generators, for use at groebner_basis
# call sites further down (groebner_basis(I; ordering = block_ordering)).
block_ordering = degrevlex(gens(R)[1:4]) * degrevlex(gens(R)[5:8])

curve_a1 = wa1^2 - (a1^5 + a1 + 2)
curve_a2 = wa2^2 - (a2^5 + a2 + 2)
curve_b1 = wb1^2 - (b1^5 + b1 + 2)
curve_b2 = wb2^2 - (b2^5 + b2 + 2)

################################################################################
# Tower -> plain-ring substitution.
#
# symbolic_residual with c=2 builds K_final as:
#
#   R_t = rational_function_field(Fp, ["t1","t2"])
#   layer 1:  R_w1 = R_t[w1];  K1 = R_w1 / (w1^2 - f(t1))     (contains t1, w1)
#   layer 2:  R_w2 = K1[w2];   K2 = R_w2 / (w2^2 - f(t2))     (contains t1,w1,t2,w2)
#
# So an element of K_final is stored as `data(val)` = a degree-<=1
# polynomial in w2 over K1, i.e.
#
#   val = c0(t1,w1)  +  c1(t1,w1) * w2
#
# and recursing one level further, each of c0,c1 is itself a rational
# function of t1 with a possible single w1 term:
#
#   c_i(t1,w1) = d0(t1) + d1(t1) * w1
#
# where d0,d1 are honest elements of the rational function field R_t in
# (t1,t2) -- i.e. num(t1,t2)/den(t1,t2) as Oscar fraction-field elements.
#
# _tower_to_ring below walks this exact structure (mirroring
# _eval_tower_recursive in trial3_phi_symbolic_unified.jl) but instead of
# evaluating at concrete field values, it substitutes the ring generators
# (t_gens[i], w_gens[i]) and *builds an Oscar ring element*, accumulating
# everything over a common denominator so the final result is returned as
# a (numerator, denominator) pair of honest polynomials in R.
################################################################################

# Reduce a (num, den) pair by their gcd. This is the key fix motivated by
# diag_norm.jl: the raw denominators coming out of the tower (built from
# det(A) of the internal linear system) were confirmed to factor almost
# entirely into powers of things that are SUPPOSED to cancel --
# (u_poly(t_i))^k, (t_i - t_j)^k for two symbolic anchors, and
# (t_i - fixed_anchor)^k -- i.e. spurious multiplicity from Cramer's-rule
# denominators that symbolic_residual's own divexact steps already divide
# out algebraically, but which coeff_equal's raw cross-multiplication
# re-introduces and compounds if left unreduced. Reducing by gcd at each
# step keeps num/den in lowest terms throughout, instead of letting that
# multiplicity accumulate across two tower layers and then across the
# final cross-sample cross-multiplication (which is what produced the
# degree-128, ~7.46M-term Fu0/Fu1 originally).
function _reduce_frac(num, den)
    iszero(num) && return (num, one(den))
    g = gcd(num, den)
    if !isone(g)
        num = divexact(num, g)
        den = divexact(den, g)
    end
    return (num, den)
end

# Evaluate a rational_function_field element (a fraction of multivariate
# polys in t1,t2) into R, substituting t_gens for [t1,t2].
function _base_frac_to_ring(val, t_gens::Vector)
    num = numerator(val)
    den = denominator(val)
    # num, den live in the polynomial ring underlying the rational
    # function field; `t_gens` gives the images of that ring's generators
    # in our shared ring R (as elements of R, e.g. [a1,a2] or [b1,b2]).
    num_R = evaluate(num, t_gens)
    den_R = evaluate(den, t_gens)
    return _reduce_frac(num_R, den_R)
end

# level: how many w-layers remain to strip before we hit the base
# rational-function-field case. t_gens/w_gens are the *target* ring
# generators (length c each) that (t1,...,tc)/(w1,...,wc) get mapped to.
function _tower_to_ring(val, level::Int, t_gens::Vector, w_gens::Vector)
    if level == 0
        return _base_frac_to_ring(val, t_gens)
    end

    val_poly = data(val)              # degree <=1 poly in w_level over K_{level-1}
    c0 = coeff(val_poly, 0)
    c1 = coeff(val_poly, 1)

    n0, d0 = _tower_to_ring(c0, level - 1, t_gens, w_gens)
    n1, d1 = _tower_to_ring(c1, level - 1, t_gens, w_gens)

    wv = w_gens[level]

    # val = c0 + c1*w  =  n0/d0 + (n1/d1)*w  =  (n0*d1 + n1*d0*w) / (d0*d1)
    num = n0 * d1 + n1 * d0 * wv
    den = d0 * d1
    return _reduce_frac(num, den)
end

# Convenience wrapper: coefficients coming out of symbolic_residual for a
# c=2 sample are elements of the full K_final tower (level = c = 2).
tower_to_ring(val, t_gens::Vector, w_gens::Vector) = _tower_to_ring(val, 2, t_gens, w_gens)

################################################################################
# Map both samples' coefficient vectors into R -- in parallel across
# available threads (each coefficient's tower walk is independent, so this
# is embarrassingly parallel). Run with `julia -t N elim2.jl` to use N
# threads; check Threads.nthreads() below to confirm they're picked up.
################################################################################

println("Threads.nthreads() = ", Threads.nthreads())

t_gens_1 = [a1, a2]
w_gens_1 = [wa1, wa2]

t_gens_2 = [b1, b2]
w_gens_2 = [wb1, wb2]

# res.u_RS_coeffs[i] is the coefficient of x^(i-1) (ascending order),
# same convention print_symbolic_residual uses.

function map_coeffs_threaded(coeffs, t_gens, w_gens)
    n = length(coeffs)
    nums = Vector{Any}(undef, n)
    dens = Vector{Any}(undef, n)
    Threads.@threads for i in 1:n
        nums[i], dens[i] = tower_to_ring(coeffs[i], t_gens, w_gens)
    end
    return nums, dens
end

u1_num, u1_den = map_coeffs_threaded(res1.u_RS_coeffs, t_gens_1, w_gens_1)
v1_num, v1_den = map_coeffs_threaded(res1.v_RS_coeffs, t_gens_1, w_gens_1)
u2_num, u2_den = map_coeffs_threaded(res2.u_RS_coeffs, t_gens_2, w_gens_2)
v2_num, v2_den = map_coeffs_threaded(res2.v_RS_coeffs, t_gens_2, w_gens_2)

println()
println("Mapped both samples' u_RS/v_RS coefficients into the shared ring.")
println("u_RS^(K=$K1) has $(length(u1_num)) coefficient(s) (x^0..x^$(length(u1_num)-1))")
println("u_RS^(K=$K2) has $(length(u2_num)) coefficient(s) (x^0..x^$(length(u2_num)-1))")
println("v_RS^(K=$K1) has $(length(v1_num)) coefficient(s) (x^0..x^$(length(v1_num)-1))")
println("v_RS^(K=$K2) has $(length(v2_num)) coefficient(s) (x^0..x^$(length(v2_num)-1))")
println()

# Per-sample (un-cross-multiplied) size diagnostics. This is the premise
# the "decoupling via target variables" approach depends on: it's only a
# win if each SAMPLE's own num/den (5-variable, single-sample) is much
# smaller than the cross-multiplied Fu/Fv (8-variable, both samples'
# variables mixed via coeff_equal's num1*den2 - num2*den1). Printed here
# so that premise is checked against real numbers rather than assumed.
println("Per-sample (uncrossed) generator sizes -- checked BEFORE deciding ",
        "whether decoupling via target variables is worth it:")
for (label, nums, dens) in [
        ("u1", u1_num, u1_den), ("u2", u2_num, u2_den),
        ("v1", v1_num, v1_den), ("v2", v2_num, v2_den),
    ]
    for (i, (n, d)) in enumerate(zip(nums, dens))
        println("  $label num[$i]: degree=", total_degree(n), " terms=", length(terms(n)),
                "   $label den[$i]: degree=", total_degree(d), " terms=", length(terms(d)))
    end
end
println()

################################################################################
# Symmetry check: is u_RS/v_RS actually invariant under swapping the two
# symbolic anchors within a sample (a1<->a2, wa1<->wa2 for sample 1;
# b1<->b2, wb1<->wb2 for sample 2)?
#
# This is a factual question about symbolic_residual's construction, not
# something to assume. If it holds, reformulating the target ring in
# terms of elementary symmetric polynomials (s1=a1+a2, s2=a1*a2, and
# likewise for b) is a legitimate and potentially big structural win --
# the Groebner basis engine currently has no way to know the ideal is
# invariant under this swap and may be wasting significant work
# exploring symmetric-but-distinct branches. If it does NOT hold, that
# reformulation is invalid and shouldn't be attempted -- so check first.
################################################################################

function check_swap_symmetry(nums, dens, from_gens, to_gens, label)
    all_invariant = true
    for (i, (n, d)) in enumerate(zip(nums, dens))
        n_swapped = evaluate(n, from_gens, to_gens)
        d_swapped = evaluate(d, from_gens, to_gens)
        # Compare n_swapped/d_swapped to n/d as fractions: n*d_swapped == n_swapped*d
        # (avoids needing a common denominator or field-of-fractions machinery)
        lhs = n * d_swapped
        rhs = n_swapped * d
        invariant = iszero(lhs - rhs)
        println("  $label [$i]: invariant under swap = ", invariant)
        all_invariant &= invariant
    end
    return all_invariant
end

println("Checking a1<->a2 (and wa1<->wa2) symmetry of sample 1's u_RS/v_RS...")
u1_symmetric = check_swap_symmetry(u1_num, u1_den, [a1, a2, wa1, wa2], [a2, a1, wa2, wa1], "u1")
v1_symmetric = check_swap_symmetry(v1_num, v1_den, [a1, a2, wa1, wa2], [a2, a1, wa2, wa1], "v1")

println("Checking b1<->b2 (and wb1<->wb2) symmetry of sample 2's u_RS/v_RS...")
u2_symmetric = check_swap_symmetry(u2_num, u2_den, [b1, b2, wb1, wb2], [b2, b1, wb2, wb1], "u2")
v2_symmetric = check_swap_symmetry(v2_num, v2_den, [b1, b2, wb1, wb2], [b2, b1, wb2, wb1], "v2")

if u1_symmetric && v1_symmetric && u2_symmetric && v2_symmetric
    println()
    println("CONFIRMED: full a1<->a2/b1<->b2 swap symmetry holds. Reformulating in")
    println("terms of elementary symmetric polynomials (s1=a1+a2, s2=a1*a2, and")
    println("likewise for b) is mathematically valid here and worth pursuing --")
    println("see Gemini's symmetric-polynomial suggestion.")
else
    println()
    println("NOT fully symmetric under this swap (see per-coefficient results above).")
    println("Do NOT reformulate the target ring in terms of elementary symmetric")
    println("polynomials alone -- that reformulation assumes full invariance and")
    println("would silently discard real solutions/change the variety if the")
    println("system isn't actually symmetric this way.")
end
println()
if length(u1_num) != length(u2_num)
    error("u_RS degree mismatch between samples: $(length(u1_num)-1) vs $(length(u2_num)-1) -- " *
          "matching only makes sense if both u_RS have the same degree")
end
if length(v1_num) != length(v2_num)
    error("v_RS degree mismatch between samples: $(length(v1_num)-1) vs $(length(v2_num)-1) -- " *
          "matching only makes sense if both v_RS have the same degree")
end

# The top (leading) u_RS coefficient is always 1 on both sides -- symbolic_residual
# normalizes u_RS to monic before returning it (see "Normalize to monic" in
# trial3_phi_symbolic_unified.jl). Matching x^deg is therefore the trivial
# equation 1==1 and contributes nothing to the ideal; including it just wastes
# a coeff_equal cross-multiplication. Only match coefficients x^0 .. x^(deg-1).
const U_DEG_TOP = length(u1_num)   # index of the (trivial) leading coefficient
const N_U_MATCH = U_DEG_TOP - 1    # how many real u-coefficients to match

################################################################################
# Collect every denominator that tower_to_ring cleared, across both samples
# and both of u_RS/v_RS. These are EXACTLY the spurious-locus factors that
# coeff_equal's cross-multiplication (num1*den2 - num2*den1) reintroduces
# into Fu/Fv below -- not a guess like "a1-a2", but the literal
# denominators produced by this run's own tower arithmetic. Saturating Iu/
# Iuv by their product afterwards removes exactly this induced multiplicity
# without touching the real variety.
#
# Only nonconstant denominators matter (a constant denominator contributes
# nothing to saturate against), so filter those out to keep the saturation
# ideal itself small.
################################################################################

function _nonconstant_dens(dens)
    return [d for d in dens if total_degree(d) > 0]
end

const CLEARED_DENOMS = vcat(
    _nonconstant_dens(u1_den), _nonconstant_dens(u2_den),
    _nonconstant_dens(v1_den), _nonconstant_dens(v2_den),
)

println("Collected ", length(CLEARED_DENOMS), " nonconstant cleared denominator(s) ",
        "across both samples (for saturation).")
println()

################################################################################
# Equality equations -- same coeff_equal pattern as elim.jl, applied
# coefficient-by-coefficient.
################################################################################

function coeff_equal(num1, den1, num2, den2)
    return num1 * den2 - num2 * den1
end

Fu = Vector{Any}(undef, N_U_MATCH)
Threads.@threads for i in 1:N_U_MATCH
    Fu[i] = coeff_equal(u1_num[i], u1_den[i], u2_num[i], u2_den[i])
end

Fv = Vector{Any}(undef, length(v1_num))
Threads.@threads for i in 1:length(v1_num)
    Fv[i] = coeff_equal(v1_num[i], v1_den[i], v2_num[i], v2_den[i])
end

println("Built ", length(Fu), " u-matching equation(s) (x^0..x^$(N_U_MATCH-1); ",
        "trivial leading x^$(U_DEG_TOP-1) coefficient 1==1 skipped) and ",
        length(Fv), " v-matching equation(s).")
for (i, g) in enumerate(Fu)
    println("  Fu$(i-1): degree=", total_degree(g), "  terms=", length(terms(g)))
end
for (i, g) in enumerate(Fv)
    println("  Fv$(i-1): degree=", total_degree(g), "  terms=", length(terms(g)))
end
println()



################################################################################
# degree_check.jl
#
# Insert this block into elim2.jl immediately after Fu/Fv are built
# (i.e. right after the println() block that prints Fu/Fv degree/terms,
# around line 419, BEFORE the "ALTERNATIVE: decoupled construction"
# section). It uses variables already in scope at that point:
#   wa1, wa2, wb1, wb2   (ring generators)
#   u1_num, u1_den, u2_num, u2_den, v1_num, v1_den, v2_num, v2_den
#   Fu, Fv
#
# Purpose: compute EXACT degree-in-each-w for every relevant polynomial,
# with no assumptions. This settles whether:
#
#   (A) each sample's own (num,den) pair is degree <=1 in ITS OWN w's
#       (necessary precondition, claimed by _tower_to_ring's structure)
#   (B) that bound survives into Fu/Fv after cross-multiplication
#   (C) whether Fu/Fv, as actually stored in R (a FREE polynomial ring,
#       NOT reduced mod wa_i^2 - f(a_i)), already exceed degree 1 in any
#       w_i -- which is the concrete failure mode to check for, since
#       num = n0*d1 + n1*d0*w2 in the tower recursion can produce a w1^2
#       term from n0*d1's cross terms, and nothing in _tower_to_ring
#       reduces that back down using w1^2 = f(t1).
################################################################################
