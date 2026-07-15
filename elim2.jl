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

const PHI_GENERAL_SRC = joinpath(@__DIR__, "phi_general", "src")

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

println("===========================================================")
println("DEGREE-IN-W DIAGNOSTIC")
println("===========================================================")
println()

w_all = [wa1, wa2, wb1, wb2]
w_names = ["wa1", "wa2", "wb1", "wb2"]

function report_wdeg(label, g)
    degs = [degree(g, w) for w in w_all]
    println("  $label: total_degree=", total_degree(g),
            "  degree-in-(wa1,wa2,wb1,wb2)=", degs)
    return degs
end

println("--- Sample 1 per-coefficient num/den: degree in wa1, wa2 (should be <=1 each) ---")
for (i, (n, d)) in enumerate(zip(u1_num, u1_den))
    report_wdeg("u1_num[$i]", n)
    report_wdeg("u1_den[$i]", d)
end
for (i, (n, d)) in enumerate(zip(v1_num, v1_den))
    report_wdeg("v1_num[$i]", n)
    report_wdeg("v1_den[$i]", d)
end
println()

println("--- Sample 2 per-coefficient num/den: degree in wb1, wb2 (should be <=1 each) ---")
for (i, (n, d)) in enumerate(zip(u2_num, u2_den))
    report_wdeg("u2_num[$i]", n)
    report_wdeg("u2_den[$i]", d)
end
for (i, (n, d)) in enumerate(zip(v2_num, v2_den))
    report_wdeg("v2_num[$i]", n)
    report_wdeg("v2_den[$i]", d)
end
println()

println("--- Fu/Fv (post cross-multiplication): degree in each of wa1,wa2,wb1,wb2 ---")
all_ok = true
for (i, g) in enumerate(Fu)
    degs = report_wdeg("Fu$(i-1)", g)
    if any(d -> d > 1, degs)
        global all_ok = false
        println("    *** Fu$(i-1) EXCEEDS degree 1 in at least one w-variable ***")
    end
end
for (i, g) in enumerate(Fv)
    degs = report_wdeg("Fv$(i-1)", g)
    if any(d -> d > 1, degs)
        global all_ok = false
        println("    *** Fv$(i-1) EXCEEDS degree 1 in at least one w-variable ***")
    end
end
println()

if all_ok
    println("RESULT: every Fu/Fv generator is degree <=1 in EACH of wa1,wa2,wb1,wb2.")
    println("This is the exact precondition needed for iterated norm elimination")
    println("(each generator can be split as A + B*w_i with A,B free of w_i, and")
    println("the norm A^2 - B^2*f(t_i) eliminates w_i exactly, no reduction needed).")
else
    println("RESULT: at least one Fu/Fv generator exceeds degree 1 in some w-variable.")
    println("This means _tower_to_ring's recursion produced a w_i^2 (or higher) term")
    println("that was NEVER reduced using w_i^2 = f(t_i) before being stored as a")
    println("free-ring element. Norm elimination as originally proposed does NOT")
    println("apply directly to Fu/Fv as currently constructed -- the polynomials")
    println("must first be reduced modulo (wa1^2-f(a1), wa2^2-f(a2), wb1^2-f(b1),")
    println("wb2^2-f(b2)) to bring them back to degree <=1 in each w before a norm")
    println("step can be taken. See the reduction helper below.")
end
println()

################################################################################
# If degrees DO exceed 1: reduce each Fu/Fv generator modulo the four curve
# relations (w_i^2 - f(t_i)) to bring it back to affine-in-each-w form, then
# recheck degrees. This directly tests whether the higher-degree terms were
# "fake" (removable by the algebraic relation the ring doesn't know about)
# or genuinely irreducible content.
################################################################################

function reduce_mod_w_squares(g, w_list, f_list)
    # w_list[i]^2 -> f_list[i]  (f_list[i] is the univariate poly a_i^5+a_i+2
    # etc., already expressed in R). Repeatedly replace w_i^2 with f_list[i]
    # using exponent reduction on each variable independently: any monomial
    # w_i^k for k>=2 reduces via k -> k-2 replacing w_i^2 by f_list[i], i.e.
    # w_i^k = f_list[i]^(k div 2) * w_i^(k mod 2).
    R_local = parent(g)
    result = zero(R_local)
    for (mono, coeff_) in zip(monomials(g), coefficients(g))
        new_mono_coeff = coeff_
        new_mono = mono
        for (w, f) in zip(w_list, f_list)
            e = degree(new_mono, w)
            if e >= 2
                k = div(e, 2)
                r = e - 2*k
                # divide out w^e, multiply back w^r, multiply coeff by f^k
                new_mono = divexact(new_mono, w^e) * (r == 0 ? one(R_local) : w^r)
                new_mono_coeff = new_mono_coeff * f^k
            end
        end
        result += new_mono_coeff * new_mono
    end
    return result
end

if !all_ok
    println("--- Reducing Fu/Fv modulo (w_i^2 - f(t_i)) and rechecking degrees ---")
    f_list = [a1^5 + a1 + 2, a2^5 + a2 + 2, b1^5 + b1 + 2, b2^5 + b2 + 2]

    Fu_reduced_test = [reduce_mod_w_squares(g, w_all, f_list) for g in Fu]
    Fv_reduced_test = [reduce_mod_w_squares(g, w_all, f_list) for g in Fv]

    println("After reduction:")
    all_ok_after = true
    for (i, g) in enumerate(Fu_reduced_test)
        degs = report_wdeg("Fu$(i-1)_reduced", g)
        if any(d -> d > 1, degs); global all_ok_after = false; end
    end
    for (i, g) in enumerate(Fv_reduced_test)
        degs = report_wdeg("Fv$(i-1)_reduced", g)
        if any(d -> d > 1, degs); global all_ok_after = false; end
    end
    println()
    if all_ok_after
        println("RESULT: after reducing mod the curve relations, all generators ARE")
        println("degree <=1 in each w. Norm elimination applies to the REDUCED")
        println("generators (Fu_reduced_test / Fv_reduced_test), not the raw Fu/Fv.")
    else
        println("RESULT: even after reduction mod curve relations, some generator")
        println("still exceeds degree 1 in some w-variable. This means the excess")
        println("degree is NOT an artifact of unreduced w^2 terms -- it is genuine")
        println("polynomial content that norm elimination (a rank-2 construction)")
        println("cannot remove in one step. In that case, the obstruction is real:")
        println("iterated norms would need to be taken multiple times (norm of a")
        println("norm) or the degree pattern needs to be inspected term-by-term")
        println("to see whether SOME but not all w's are safely affine.")
    end
end

################################################################################
# ALTERNATIVE: decoupled construction via target variables.
#
# coeff_equal(num1,den1,num2,den2) = num1*den2 - num2*den1 forces BOTH
# samples' variables (a1,a2,wa1,wa2,b1,b2,wb1,wb2 -- 8 variables total)
# into a single generator, cross-multiplied together. That's the direct
# cause of the degree-32/48, tens-of-thousands-of-terms blowup: each
# cross-multiplied generator already mixes everything before
# groebner_basis/F4 gets a chance to work with anything smaller.
#
# Decoupling introduces one target variable per matched coefficient
# (U0,U1 for u_RS's x^0,x^1 coefficients; V0,V1 for v_RS's) and replaces
# each single 8-variable degree-32/48 equation with TWO equations, each
# touching only ONE sample's variables (5 variables: that sample's
# a/b-pair, its w-pair, and the shared target variable) at whatever
# degree that sample's own num/den carry individually (checked above in
# the per-sample size diagnostics -- confirm those are actually smaller
# before trusting this is a win, rather than assuming it).
#
# This does NOT change the underlying variety: U_i is just forced to
# equal both samples' i-th coefficient (in lowest terms), which is
# exactly what Fu/Fv's cross-multiplication was already asserting -- it
# only changes how that assertion is phrased algebraically, trading one
# dense 8-variable equation for two sparser 5-variable ones plus an
# extra variable to eliminate later (along with the w's).
#
# NOTE: unlike the "w-linearity/norm" idea some outside analysis
# suggested, this does not depend on any assumption about the degree of
# these polynomials in the w variables, so there's no risk of silently
# dropping terms -- it's a straightforward, always-valid algebraic
# substitution (introduce a variable, equate it to both sides).
################################################################################

R_dec, dec_gens = polynomial_ring(
    F,
    vcat(["wa1", "wa2", "wb1", "wb2", "a2", "a1", "b2", "b1"],
         ["U$i" for i in 0:(N_U_MATCH-1)],
         ["V$i" for i in 0:(length(v1_num)-1)])
)
wa1_d, wa2_d, wb1_d, wb2_d, a2_d, a1_d, b2_d, b1_d = dec_gens[1:8]
U_vars = dec_gens[9:(8+N_U_MATCH)]
V_vars = dec_gens[(9+N_U_MATCH):(8+N_U_MATCH+length(v1_num))]

curve_a1_d = wa1_d^2 - (a1_d^5 + a1_d + 2)
curve_a2_d = wa2_d^2 - (a2_d^5 + a2_d + 2)
curve_b1_d = wb1_d^2 - (b1_d^5 + b1_d + 2)
curve_b2_d = wb2_d^2 - (b2_d^5 + b2_d + 2)

# Re-map each sample's num/den (currently elements of R, built from
# t_gens_1=[a1,a2]/w_gens_1=[wa1,wa2] and t_gens_2=[b1,b2]/w_gens_2=
# [wb1,wb2]) into R_dec. Since R and R_dec share the same variable
# NAMES for wa1,wa2,wb1,wb2,a2,a1,b2,b1 (just with U0,U1,V0,V1 appended),
# this is a straightforward generator-for-generator substitution.
old_to_new = Dict(
    wa1 => wa1_d, wa2 => wa2_d, wb1 => wb1_d, wb2 => wb2_d,
    a2 => a2_d, a1 => a1_d, b2 => b2_d, b1 => b1_d,
)
remap(f) = evaluate(f, [old_to_new[g] for g in gens(R)])

u1_num_d = [remap(f) for f in u1_num]
u1_den_d = [remap(f) for f in u1_den]
u2_num_d = [remap(f) for f in u2_num]
u2_den_d = [remap(f) for f in u2_den]
v1_num_d = [remap(f) for f in v1_num]
v1_den_d = [remap(f) for f in v1_den]
v2_num_d = [remap(f) for f in v2_num]
v2_den_d = [remap(f) for f in v2_den]

# U_i * den == num, for each sample separately, for each matched
# coefficient i. (V_i likewise for v_RS.) This is what "num/den == U_i"
# means algebraically -- same content as coeff_equal, just not
# cross-multiplied against the other sample directly.
Fu_decoupled = Any[]
for (i, Uvar) in enumerate(U_vars)
    push!(Fu_decoupled, u1_num_d[i] - Uvar * u1_den_d[i])
    push!(Fu_decoupled, u2_num_d[i] - Uvar * u2_den_d[i])
end

Fv_decoupled = Any[]
for (i, Vvar) in enumerate(V_vars)
    push!(Fv_decoupled, v1_num_d[i] - Vvar * v1_den_d[i])
    push!(Fv_decoupled, v2_num_d[i] - Vvar * v2_den_d[i])
end

println("Decoupled construction (target variables U0,U1,V0,V1):")
for (i, g) in enumerate(Fu_decoupled)
    println("  Fu_decoupled[$i]: degree=", total_degree(g), "  terms=", length(terms(g)))
end
for (i, g) in enumerate(Fv_decoupled)
    println("  Fv_decoupled[$i]: degree=", total_degree(g), "  terms=", length(terms(g)))
end
println()

Iu_decoupled = ideal(R_dec, vcat(Fu_decoupled, [curve_a1_d, curve_a2_d, curve_b1_d, curve_b2_d]))
Iuv_decoupled = ideal(R_dec, vcat(Fu_decoupled, Fv_decoupled,
                                  [curve_a1_d, curve_a2_d, curve_b1_d, curve_b2_d]))

block_ordering_dec = degrevlex(dec_gens[1:4]) * degrevlex(dec_gens[5:end])





################################################################################
# norm_eliminate.jl
#
# Insert immediately after the DEGREE-IN-W DIAGNOSTIC block confirms
# all Fu/Fv are degree <=1 in each of wa1,wa2,wb1,wb2 (confirmed by your
# run). This replaces the entire Groebner-basis + eliminate() pipeline
# for Fu/Fv with four sequential exact norm (resultant) computations.
#
# split_linear(g, w) : g = P + Q*w  (P,Q free of w), EXACT, since g is
# degree <=1 in w by the diagnostic above -- no approximation, no
# reduction needed.
#
# norm_eliminate(g, w, f) : returns P^2 - Q^2*f, i.e. Res_w(g, w^2-f).
# This vanishes exactly when g vanishes AND w^2=f holds (either root),
# so V(norm_eliminate(g,w,f)) restricted to the curve w^2=f equals the
# projection of V(g, w^2-f) onto the w-free variables. Standard
# elimination-via-norm for a quadratic extension -- exact, not lossy,
# PROVIDED g is degree <=1 in w (confirmed above).
################################################################################

function split_linear(g, w)
    # g has degree <=1 in w (confirmed by diagnostic). Extract P (w^0
    # coefficient) and Q (w^1 coefficient) as elements not involving w.
    P = evaluate(g, [w], [zero(parent(g))])   # g with w set to 0 -> P
    Q = divexact(g - P, w)                    # (g - P)/w -> Q, exact since g-P is divisible by w
    return P, Q
end

function norm_eliminate(g, w, f)
    P, Q = split_linear(g, w)
    return P^2 - Q^2 * f
end

################################################################################
# layer_degree_check.jl
#
# Goal: measure polynomial size/degree AT EACH TOWER LAYER, before
# _tower_to_ring finishes flattening to the fully-reduced (num,den) pair.
# This tests GPT's specific claim: that taking the norm INSIDE the
# recursion (at level 1, before the final _base_frac_to_ring substitution
# into t1) gives smaller polynomials than taking it after full
# flattening (which is what norm_eliminate.jl did, and which exploded).
#
# Insert this in place of the existing tower_to_ring wrapper call, i.e.
# instrument _tower_to_ring itself to print degree/terms at each level,
# for one representative coefficient (res1.u_RS_coeffs[1]) rather than
# all of them, to keep this fast and readable.
################################################################################

# Instrumented copy of _tower_to_ring that prints size at each level
# instead of silently recursing. Uses the same logic as elim2.jl's
# _tower_to_ring (lines 209-227) verbatim, just with diagnostics added.
function _tower_to_ring_instrumented(val, level::Int, t_gens::Vector, w_gens::Vector, path::String="root")
    if level == 0
        n, d = _base_frac_to_ring(val, t_gens)
        println("  [level 0, $path] AFTER base_frac_to_ring (t-substitution): ",
                "num: degree=", total_degree(n), " terms=", length(terms(n)),
                "  den: degree=", total_degree(d), " terms=", length(terms(d)))
        return (n, d)
    end

    val_poly = data(val)
    c0 = coeff(val_poly, 0)
    c1 = coeff(val_poly, 1)

    n0, d0 = _tower_to_ring_instrumented(c0, level - 1, t_gens, w_gens, path * ".c0")
    n1, d1 = _tower_to_ring_instrumented(c1, level - 1, t_gens, w_gens, path * ".c1")

    wv = w_gens[level]
    num = n0 * d1 + n1 * d0 * wv
    den = d0 * d1
    num, den = _reduce_frac(num, den)

    println("  [level $level, $path] AFTER combining with w_gens[$level]: ",
            "num: degree=", total_degree(num), " terms=", length(terms(num)),
            "  den: degree=", total_degree(den), " terms=", length(terms(den)))

    return (num, den)
end

println("===========================================================")
println("PER-LAYER DEGREE TRACE (sample 1, u_RS_coeffs[1] only)")
println("===========================================================")
println()
n_test, d_test = _tower_to_ring_instrumented(res1.u_RS_coeffs[1], 2, t_gens_1, w_gens_1)
println()
println("Final (should match u1_num[1]/u1_den[1] from the main script): ",
        "num degree=", total_degree(n_test), " den degree=", total_degree(d_test))
println()

################################################################################
# Now test: take the norm at LEVEL 1 (i.e. eliminate wa2, the innermost/
# outermost w depending on convention -- here level=2 is outermost per
# the wrapper's level=c=2 call, level=1 is the c0/c1 split w.r.t. w_gens[1]
# = wa1) BEFORE doing the final t-substitution, vs. the current approach
# of flattening all the way to (num,den) in R and THEN norm-eliminating.
#
# Concretely: at level 1, val is c0(t1) + c1(t1)*w1, i.e. an element of
# K1 = R_t[w1]/(w1^2-f(t1)) -- but c0, c1 here are still elements of the
# RATIONAL FUNCTION FIELD R_t (fractions of polys in t1,t2), not yet
# substituted into the ring R. Taking the norm HERE means:
#
#   norm = c0^2 - c1^2 * f(t1)
#
# computed as a rational-function-field operation (numerator/denominator
# arithmetic in Fp(t1,t2)), THEN substituting t_gens at the very end --
# i.e. norm-then-substitute, instead of substitute-then-norm.
################################################################################

println("===========================================================")
println("Testing norm-BEFORE-substitution vs norm-AFTER-substitution")
println("===========================================================")
println()

# Get the level-1 c0, c1 split directly (one layer of recursion by hand,
# mirroring _tower_to_ring's own level==2 branch).
val2 = res1.u_RS_coeffs[1]
val2_poly = data(val2)
c0_at_lvl1 = coeff(val2_poly, 0)   # element of K1 (contains t1, w1)
c1_at_lvl1 = coeff(val2_poly, 1)   # element of K1 (contains t1, w1)

# c0_at_lvl1, c1_at_lvl1 are themselves elements of K1 = R_t[w1]/(w1^2-f(t1)),
# so split AGAIN to get down to R_t (rational function field) coefficients:
c0_poly = data(c0_at_lvl1)
c00 = coeff(c0_poly, 0)   # in R_t
c01 = coeff(c0_poly, 1)   # in R_t

c1_poly = data(c1_at_lvl1)
c10 = coeff(c1_poly, 0)   # in R_t
c11 = coeff(c1_poly, 1)   # in R_t

println("Level-1 rational-function-field pieces (before any ring substitution):")
for (label, v) in [("c00", c00), ("c01", c01), ("c10", c10), ("c11", c11)]
    num_deg = total_degree(numerator(v))
    den_deg = total_degree(denominator(v))
    println("  $label: numerator degree=$num_deg  denominator degree=$den_deg")
end
println()
println("(If these are small -- e.g. single-digit degree in t1,t2 -- then taking")
println("norms at THIS level, while everything is still a rational function of")
println("just t1,t2 with no w's substituted in yet, is much cheaper than doing")
println("it after _tower_to_ring has fully flattened to degree-16/24 polys in R.")
println("Compare these numbers to u1_num[1]'s degree=16 to see the ratio.)")

if false # dis too slow lmao, gets done with the first one but blows up
    println("===========================================================")
    println("NORM/RESULTANT ELIMINATION (no Groebner basis)")
    println("===========================================================")
    println()

    f_a1 = a1^5 + a1 + 2
    f_a2 = a2^5 + a2 + 2
    f_b1 = b1^5 + b1 + 2
    f_b2 = b2^5 + b2 + 2

    # Eliminate wa1, wa2, wb1, wb2 in sequence from each of Fu0, Fu1, Fv0, Fv1.
    # Order chosen to match elim2.jl's own elimination order (wb2, wb1, wa2, wa1)
    # for comparability, though for norm elimination the order is a free choice
    # (each step is an exact algebraic operation, not a search) and shouldn't
    # matter mathematically -- only for intermediate-expression-size bookkeeping.
    function eliminate_all_w(g)
        g = norm_eliminate(g, wb2, f_b2)
        println("    after eliminating wb2: total_degree=", total_degree(g), " terms=", length(terms(g)))
        g = norm_eliminate(g, wb1, f_b1)
        println("    after eliminating wb1: total_degree=", total_degree(g), " terms=", length(terms(g)))
        g = norm_eliminate(g, wa2, f_a2)
        println("    after eliminating wa2: total_degree=", total_degree(g), " terms=", length(terms(g)))
        g = norm_eliminate(g, wa1, f_a1)
        println("    after eliminating wa1: total_degree=", total_degree(g), " terms=", length(terms(g)))
        return g
    end

    println("--- Eliminating Fu0 ---")
    Ru0 = eliminate_all_w(Fu[1])
    println("--- Eliminating Fu1 ---")
    Ru1 = eliminate_all_w(Fu[2])
    println("--- Eliminating Fv0 ---")
    Rv0 = eliminate_all_w(Fv[1])
    println("--- Eliminating Fv1 ---")
    Rv1 = eliminate_all_w(Fv[2])

    println()
    println("Final relation polynomials in (a1,a2,b1,b2) only -- NO Groebner basis used:")
    for (label, g) in [("Ru0", Ru0), ("Ru1", Ru1), ("Rv0", Rv0), ("Rv1", Rv1)]
        println("  $label: total_degree=", total_degree(g), " terms=", length(terms(g)),
                "  vars=", vars(g))
    end
    println()

    # Sanity: confirm none of these are identically zero (that would mean
    # either a real algebraic degeneracy, or a bug in split_linear/norm_eliminate).
    for (label, g) in [("Ru0", Ru0), ("Ru1", Ru1), ("Rv0", Rv0), ("Rv1", Rv1)]
        if iszero(g)
            println("  *** WARNING: $label is IDENTICALLY ZERO after norm elimination ***")
        end
    end

    println()
    println("If nonzero, gcd(Ru0,Ru1,Rv0,Rv1) (in F[a1,a2,b1,b2]) is your candidate")
    println("relation-ideal generating set WITHOUT ever calling groebner_basis.")
    println("Compute pairwise gcds next -- cheap compared to everything above.")
end







#!/usr/bin/env julia
#
# norm_elim_diag.jl
#
# Answers the supervisor's direct question and nothing else:
#
#     sample polynomial (per-sample num/den, NOT cross-multiplied)
#       -> remove wa2 -> degree? terms?
#       -> remove wa1 -> degree? terms?
#
# This measures whether per-sample norm elimination is actually cheap,
# as opposed to assuming it from the "smaller base size" argument alone.
#
# It deliberately does NOT build Fu/Fv (the cross-multiplied 8-variable
# equations), does NOT call groebner_basis, and does NOT touch the
# decoupled U/V construction. It is a narrow, fast diagnostic meant to
# run BEFORE committing to the fiber-product pipeline, so the "cheap"
# claim in the last response is checked against real numbers instead of
# asserted.
#
# Usage:
#   julia -t auto norm_elim_diag.jl
#
# Requires trial3_phi_symbolic_unified.jl in the same directory (or edit
# PHI_GENERAL_SRC below to point at it).

using Oscar

################################################################################
# Load the symbolic engine -- same include pattern as elim2.jl, but this
# repo layout has trial3_phi_symbolic_unified.jl sitting next to this
# script rather than under phi_general/src, so we check both locations.
################################################################################

const HERE = @__DIR__
const CANDIDATE_PATHS = [
    joinpath(HERE, "trial3_phi_symbolic_unified.jl"),
    joinpath(HERE, "phi_general", "src", "trial3_phi_symbolic_unified.jl"),
]
const ENGINE_PATH = findfirst(isfile, CANDIDATE_PATHS) === nothing ?
    error("trial3_phi_symbolic_unified.jl not found in: $CANDIDATE_PATHS") :
    CANDIDATE_PATHS[findfirst(isfile, CANDIDATE_PATHS)]

include(ENGINE_PATH)
using .PhiSymbolic

################################################################################
# Same curve / sample data as elim2.jl (sample 1, K=2 c=2 -- the smaller of
# the two samples, and sufficient to answer the question: is per-sample
# norm elimination cheap?). Extend to sample 2 at the bottom if sample 1
# looks tractable.
################################################################################

const p = 2371157
const F_POLY_ASC = [2, 1, 0, 0, 0, 1]   # y^2 = x^5 + x + 2, ascending coeffs
F = GF(p)

const K1, c1 = 2, 2
const fixed1 = Tuple{Int,Int}[]
const u0_1, u1_1, v0_1, v1_1 = 468873, 956582, 2168176, 2288437

println("Calling PhiSymbolic.symbolic_residual for sample 1 (K=$K1, c=$c1)...")
res1 = PhiSymbolic.symbolic_residual(K1, c1, fixed1, u0_1, u1_1, v0_1, v1_1, F_POLY_ASC, p)

if isempty(res1.u_RS_coeffs) || isempty(res1.v_RS_coeffs)
    error("sample 1 (K=$K1): construction failed or degenerate -- no u_RS/v_RS to test")
end

println("sample 1: deg(u_RS)=$(length(res1.u_RS_coeffs)-1)  deg(v_RS)=$(length(res1.v_RS_coeffs)-1)")
println()

################################################################################
# Target ring: JUST this sample's variables. 5 variables (wa1,wa2,a1,a2)
# plus we'll add U/V target vars only where needed for elimination via
# ideal-based eliminate(); the norm-elimination path below doesn't need
# them at all -- it works directly on (numerator,denominator) pairs.
################################################################################

R, (wa1, wa2, a1, a2) = polynomial_ring(F, ["wa1", "wa2", "a1", "a2"])

curve_a1 = wa1^2 - (a1^5 + a1 + 2)
curve_a2 = wa2^2 - (a2^5 + a2 + 2)

################################################################################
# Tower -> ring flattening -- copied verbatim from elim2.jl's _tower_to_ring
# / _base_frac_to_ring / _reduce_frac, restricted to a single sample.
################################################################################

function _reduce_frac(num, den)
    iszero(num) && return (num, one(den))
    g = gcd(num, den)
    if !isone(g)
        num = divexact(num, g)
        den = divexact(den, g)
    end
    return (num, den)
end

function _base_frac_to_ring(val, t_gens::Vector)
    num = numerator(val)
    den = denominator(val)
    num_R = evaluate(num, t_gens)
    den_R = evaluate(den, t_gens)
    return _reduce_frac(num_R, den_R)
end

function _tower_to_ring(val, level::Int, t_gens::Vector, w_gens::Vector)
    if level == 0
        return _base_frac_to_ring(val, t_gens)
    end
    val_poly = data(val)
    c0 = coeff(val_poly, 0)
    c1 = coeff(val_poly, 1)
    n0, d0 = _tower_to_ring(c0, level - 1, t_gens, w_gens)
    n1, d1 = _tower_to_ring(c1, level - 1, t_gens, w_gens)
    wv = w_gens[level]
    num = n0 * d1 + n1 * d0 * wv
    den = d0 * d1
    return _reduce_frac(num, den)
end

tower_to_ring(val, t_gens::Vector, w_gens::Vector) = _tower_to_ring(val, 2, t_gens, w_gens)

t_gens_1 = [a1, a2]
w_gens_1 = [wa1, wa2]

function map_coeffs(coeffs, t_gens, w_gens)
    n = length(coeffs)
    nums = Vector{Any}(undef, n)
    dens = Vector{Any}(undef, n)
    for i in 1:n
        nums[i], dens[i] = tower_to_ring(coeffs[i], t_gens, w_gens)
    end
    return nums, dens
end

println("Flattening sample 1's u_RS, v_RS coefficients into F[wa1,wa2,a1,a2]...")
u1_num, u1_den = map_coeffs(res1.u_RS_coeffs, t_gens_1, w_gens_1)
v1_num, v1_den = map_coeffs(res1.v_RS_coeffs, t_gens_1, w_gens_1)
println("done.")
println()

# Drop the trivial monic leading coefficient of u_RS (== 1, contributes
# nothing), same convention as elim2.jl.
const N_U_MATCH = length(u1_num) - 1

println("Per-sample (uncrossed) sizes BEFORE any elimination:")
for (label, nums, dens, n_use) in [
        ("u1", u1_num, u1_den, N_U_MATCH),
        ("v1", v1_num, v1_den, length(v1_num)),
    ]
    for i in 1:n_use
        n, d = nums[i], dens[i]
        println("  $label num[$i]: degree=", total_degree(n), " terms=", length(terms(n)),
                "   $label den[$i]: degree=", total_degree(d), " terms=", length(terms(d)))
    end
end
println()

################################################################################
# THE ACTUAL QUESTION.
#
# For a single coefficient's (num, den) pair, form
#
#     g = num - U*den        (U a placeholder value, not yet a new ring var --
#                              we work with num,den directly via the norm map
#                              on num/den's dependence on w, exactly as
#                              elim2.jl's norm_eliminate.jl section does, but
#                              measured here in isolation, one coefficient at
#                              a time, one w at a time.)
#
# Concretely: num and den are each degree<=1 in wa2 (confirmed structurally
# by _tower_to_ring: level=2 introduces wa2 linearly, level=1 introduces wa1
# linearly, and nothing downstream re-squares them since R is a FREE
# polynomial ring, not reduced mod wa_i^2-f(a_i), until we explicitly
# substitute that relation via the norm map). We eliminate wa2 first via
#
#     num = Pn + Qn*wa2,   den = Pd + Qd*wa2
#
#     N(num) := Pn^2 - Qn^2 * f(a2)      (multiply num by its "conjugate")
#     N(den) := Pd^2 - Qd^2 * f(a2)
#
# But num/den = U really means num - U*den = 0, i.e. we need the norm of
# (num - U*den) as a combined object, OR equivalently we track num and den
# SEPARATELY through the wa2-elimination and recombine after. The cleanest
# exact approach, avoiding introducing U before we've even checked cost:
# eliminate wa2 from the PAIR (num,den) by rationalizing the fraction --
# multiply num/den by conj(den)/conj(den):
#
#     num/den = num*conj(den) / (den*conj(den)) = num*conj(den) / N(den)
#
# num*conj(den) is still linear in wa2 (linear * linear can be degree 2,
# but conj(den) = Pd - Qd*wa2, so num*conj(den) generally IS degree 2 in
# wa2 -- so this does NOT trivially collapse; we must actually take the
# norm of the whole numerator too). This is exactly the doubling step the
# supervisor is asking to see measured, not assumed. So:
#
#     new_num := N(num) = Pn^2 - Qn^2*f(a2)     [rationalizes num alone]
#     new_den := N(den) = Pd^2 - Qd^2*f(a2)
#
# is WRONG in general because num/den != N(num)/N(den) unless num,den share
# the same conjugation structure consistently -- the correct rationalization
# multiplies num/den by conj(den)/conj(den), giving
#
#     num*conj(den) / N(den)
#
# and num*conj(den) must then itself be split into its own P',Q' (linear in
# wa2 gone -- wait: num*conj(den) = (Pn+Qn*wa2)(Pd-Qd*wa2)
#            = Pn*Pd - Pn*Qd*wa2 + Qn*Pd*wa2 - Qn*Qd*wa2^2
#            = (Pn*Pd - Qn*Qd*f(a2))  +  (Qn*Pd - Pn*Qd)*wa2
#
# using wa2^2 = f(a2). This IS still linear in wa2 (the algebra works out
# because conjugation is a ring homomorphism on this quadratic extension),
# so num*conj(den) reduces to a new (P'',Q'') pair, still linear in wa2,
# same shape as before -- it has NOT eliminated wa2, only rationalized the
# denominator down to N(den) (wa2-free). To fully eliminate wa2 from the
# EQUATION num - U*den = 0, form:
#
#     h := num - U*den = (Pn - U*Pd) + (Qn - U*Qd)*wa2
#     N(h) = (Pn - U*Pd)^2 - (Qn - U*Qd)^2 * f(a2)
#
# This is the correct, single, exact norm elimination of wa2 from the
# matching equation itself (treating U as an extra indeterminate rather
# than trying to eliminate wa2 from num,den separately, which doesn't by
# itself remove wa2 from the equation num=U*den). We measure N(h)'s
# degree/terms, then repeat for wa1 on the result.
################################################################################

# f(a) = a^5 + a + 2, evaluated symbolically at whichever anchor variable
f_of(a) = a^5 + a + 2

# CORRECTNESS-CRITICAL FIX (found by sympy sanity check before running this
# on real data -- see sanity_check.py / sanity_check2.py alongside this
# file): h0 = num - U*den is linear in wa1 ALONE and linear in wa2 ALONE,
# but NOT jointly -- it has a genuine wa1*wa2 cross term, because num's
# wa2-coefficient itself contains a wa1 term (tower structure: the level-2
# recursion produces n1*d0*wa2 where d0 already carries wa1). Squaring the
# wa2-coefficient to take the norm over wa2 therefore produces a wa1^2
# term. In the FREE polynomial ring R (not reduced mod wa1^2-f(a1)), that
# wa1^2 does not automatically collapse -- it just sits there, so h1 is no
# longer linear in wa1, and the next norm step is on a degree-2-in-wa1
# polynomial instead of degree-1. Without reducing wa_i^2 -> f(a_i) after
# EVERY norm step, split_linear's degree<=1 assumption silently breaks
# (or, worse, in a language that doesn't assert on it, silently proceeds
# and computes the WRONG norm). This function reduces mod the curve
# relations at every step, exactly the way the tower's actual field
# arithmetic would, so the elimination is both exact and actually linear
# at the point split_linear is called.
function reduce_mod_curves(g, wa1, a1, wa2, a2)
    changed = true
    while changed
        changed = false
        # reduce even powers wa_i^(2k) -> f(a_i)^k, highest first
        for k in 6:-1:1
            d1 = degree(g, wa1)
            if d1 >= 2*k
                g = g - (coeff(g, [wa1], [2*k]) * wa1^(2*k)) +
                        (coeff(g, [wa1], [2*k]) * f_of(a1)^k)
                changed = true
            end
            d2 = degree(g, wa2)
            if d2 >= 2*k
                g = g - (coeff(g, [wa2], [2*k]) * wa2^(2*k)) +
                        (coeff(g, [wa2], [2*k]) * f_of(a2)^k)
                changed = true
            end
        end
    end
    return g
end

function split_linear(g, w)
    # g is degree <=1 in w AFTER reduce_mod_curves has been applied.
    # Return (P,Q) with g = P + Q*w, P,Q free of w. Exact -- no
    # approximation -- but only valid post-reduction; calling this on an
    # unreduced g is exactly the bug the sanity check caught.
    d = degree(g, w)
    @assert d <= 1 "expected degree <=1 in $w after curve reduction, got $d " *
                    "-- reduce_mod_curves did not fully linearize; check its loop bound (k up to 6) " *
                    "is high enough for this g's actual degree in $w"
    Q = coeff(g, [w], [1])
    P = g - Q * w
    return P, Q
end

function norm_eliminate_step(g, w, a_anchor, wa1, a1, wa2, a2)
    # Reduce mod curve relations FIRST (fixes the cross-term bug above),
    # then split linearly in w, take the norm, and reduce again (the
    # squaring step can reintroduce even powers of the OTHER w variable
    # too, via cross terms in P^2/Q^2).
    g = reduce_mod_curves(g, wa1, a1, wa2, a2)
    P, Q = split_linear(g, w)
    result = P^2 - Q^2 * f_of(a_anchor)
    return reduce_mod_curves(result, wa1, a1, wa2, a2)
end

function run_norm_elim_for_coeff(label, num, den, U_placeholder_name)
    println("=" ^ 70)
    println(label)
    println("=" ^ 70)

    # Build h = num - U*den in a ring with an extra U variable, so the
    # norm step is well-defined algebraically (see derivation above).
    Rh, (wa1h, wa2h, a1h, a2h, Uh) = polynomial_ring(
        F, ["wa1", "wa2", "a1", "a2", U_placeholder_name]
    )
    old_gens = gens(R)  # [wa1, wa2, a1, a2]
    new_gens = [wa1h, wa2h, a1h, a2h]
    remap(f) = evaluate(f, new_gens)

    num_h = remap(num)
    den_h = remap(den)
    h0 = num_h - Uh * den_h

    println("  h0 = num - U*den:  degree=", total_degree(h0), "  terms=", length(terms(h0)))

    # Step 1: eliminate wa2 (reduces mod both curve relations internally,
    # which is what fixes the wa1-cross-term bug found by the sympy check)
    h1 = norm_eliminate_step(h0, wa2h, a2h, wa1h, a1h, wa2h, a2h)
    println("  after eliminating wa2:  degree=", total_degree(h1), "  terms=", length(terms(h1)),
            "   (still contains wa1? ", (wa1h in vars(h1)), ")")

    # Step 2: eliminate wa1
    h2 = norm_eliminate_step(h1, wa1h, a1h, wa1h, a1h, wa2h, a2h)
    println("  after eliminating wa1:  degree=", total_degree(h2), "  terms=", length(terms(h2)),
            "   (still contains any w? ", any(v -> v in (wa1h, wa2h), vars(h2)), ")")

    println()
    return (h0=h0, h1=h1, h2=h2)
end

################################################################################
# Run it on every u_RS / v_RS coefficient of sample 1. This is the whole
# experiment -- no Groebner basis, no cross-sample anything.
################################################################################

results = Dict{String,Any}()

for i in 1:N_U_MATCH
    results["u1_$i"] = run_norm_elim_for_coeff("u1 coefficient x^$(i-1)  (norm-eliminate wa2 then wa1)",
                                                 u1_num[i], u1_den[i], "U")
end

for i in 1:length(v1_num)
    results["v1_$i"] = run_norm_elim_for_coeff("v1 coefficient x^$(i-1)  (norm-eliminate wa2 then wa1)",
                                                 v1_num[i], v1_den[i], "V")
end

################################################################################
# Summary table -- the numbers the supervisor actually asked for.
################################################################################

println()
println("#" ^ 70)
println("SUMMARY: per-sample, per-coefficient norm elimination cost")
println("#" ^ 70)
println()
println(rpad("coefficient", 14), rpad("h0 deg/terms", 18),
        rpad("after wa2", 18), rpad("after wa1", 18))
for (key, r) in sort(collect(results); by = first)
    d0, t0 = total_degree(r.h0), length(terms(r.h0))
    d1, t1 = total_degree(r.h1), length(terms(r.h1))
    d2, t2 = total_degree(r.h2), length(terms(r.h2))
    println(rpad(key, 14), rpad("$d0 / $t0", 18), rpad("$d1 / $t1", 18), rpad("$d2 / $t2", 18))
end
println()
println("Compare the 'after wa1' column to the cross-multiplied Fu/Fv sizes")
println("(degree 32/48, ~29,889 / ~150,241 terms) already measured. If these")
println("numbers stay in the hundreds/low-thousands, per-sample norm elimination")
println("is cheap as claimed. If they blow up comparably, the claim was wrong")
println("and the per-sample base-size advantage does not survive elimination --")
println("in which case the fiber-product win has to come entirely from the")
println("decoupled-U/V Groebner route (elim2.jl's Iu_decoupled/Iuv_decoupled),")
println("not from norm elimination, and that's the next thing to test.")













################################################################################
# EXPERIMENT: eliminate the w's (and, separately, w's+U's) from the
# DECOUPLED ideal, and report real numbers. This is the falsification
# test for the graph formulation: does post-elimination size for the
# decoupled route actually beat the cross-multiplied Fu/Fv numbers
# (degree 32/48, ~29,889 / ~150,241 terms), or does it converge to
# something comparable once the w's (and U/V's) are actually gone?
#
# Mechanism note: eliminate(I, vars) in Oscar computes a Groebner basis
# under a monomial ordering with `vars` forced dominant (an elimination
# ordering -- internally a block/lex-style order over `vars` composed
# with an order on the rest), then reads off the generators of
# I ∩ k[remaining vars]. This IS the block-elimination mechanism --
# block_ordering_dec above was for direct groebner_basis(...; ordering=)
# calls; eliminate() builds its own internal elimination ordering and
# does not consume block_ordering_dec. That's why the two are separate
# calls below rather than one feeding the other.
################################################################################

################################################################################
# INSTRUMENTATION PASS -- run before any elimination attempt.
#
# Goal: find out WHERE the Groebner computation goes pathological,
# rather than waiting on a single call that already hung. Three parts:
#
#   A) Static diagnostics on Fu_decoupled/curve generators (no Groebner
#      call at all -- these are cheap structural facts we should have
#      measured before ever calling eliminate()).
#   B) Incremental sub-ideal sweep: ideal(Fu_decoupled[1]), then
#      ideal(Fu_decoupled[1:2]), etc., each run through eliminate() with
#      a hard wall-clock timeout, so we can see which generator count
#      first goes pathological instead of learning only "the full system
#      hangs".
#   C) Incremental VARIABLE sweep: eliminate just wa1_d, then wa1_d+wa2_d,
#      etc., each with a hard timeout, to see whether a single sample's
#      pair of w's is already hard (intrinsic to one sample) or whether
#      it's specifically the SECOND sample's w's being added that causes
#      the blowup (cross-sample interaction).
#
# Both B and C use a hard timeout via a background Task + Timer, because
# there is no clean way to abort a running Singular/msolve C call from
# inside Julia -- the timeout can only tell you "still running after N
# seconds", not actually kill and reclaim the C-level computation. If a
# step times out, the printed elapsed time is the timeout value, not a
# true completion time, and the underlying Singular process may still be
# consuming CPU/RAM in the background for the rest of this Julia
# session. If that matters, run each timed step as its own external
# `timeout N julia -e '...'` subprocess instead (see note at the bottom
# of this block).
################################################################################

println()
println("===========================================================")
println("PART A: static diagnostics on Fu_decoupled + curve generators")
println("(no Groebner call -- pure structural facts)")
println("===========================================================")
println()

all_gens_for_diag = vcat(Fu_decoupled, [curve_a1_d, curve_a2_d, curve_b1_d, curve_b2_d])
diag_labels = vcat(["Fu_decoupled[$i]" for i in 1:length(Fu_decoupled)],
                    ["curve_a1_d", "curve_a2_d", "curve_b1_d", "curve_b2_d"])

println(rpad("generator", 18), rpad("degree", 8), rpad("terms", 8),
        rpad("#vars", 7), rpad("vars-used", 30), rpad("homogeneous?", 13))
for (label, g) in zip(diag_labels, all_gens_for_diag)
    vs = vars(g)
    is_hom = is_homogeneous(g)
    println(rpad(label, 18), rpad(total_degree(g), 8), rpad(length(terms(g)), 8),
            rpad(length(vs), 7), rpad(join(string.(vs), ","), 30), rpad(is_hom, 13))
end
println()

# Total-degree profile: how many terms at each total degree, per generator
# (crude Hilbert-function-style shape -- fully dense vs concentrated at
# top degree looks very different and is informative before Groebner).
println("Degree profile (term-count histogram by total degree) per generator:")
for (label, g) in zip(diag_labels, all_gens_for_diag)
    profile = Dict{Int,Int}()
    for t in terms(g)
        d = total_degree(t)
        profile[d] = get(profile, d, 0) + 1
    end
    println("  $label: ", sort(collect(profile); by = first))
end
println()

println("Number of generators (Fu_decoupled + curves) = ", length(all_gens_for_diag))
println("Ambient ring R_dec has ", ngens(R_dec), " variables: ", symbols(R_dec))
println()

################################################################################
# Timeout helper. Runs `f()` on a background Task and polls it; if it has
# not finished within `limit_secs`, returns (nothing, :timeout, elapsed)
# without being able to kill the underlying computation (see note above).
# If it finishes, returns (result, :ok, elapsed). If it throws, returns
# (nothing, :error, elapsed) and prints the exception.
#
# IMPORTANT CAVEAT, stated plainly rather than assumed away: Threads.@spawn
# only gives the MAIN thread a chance to keep polling while f() runs on a
# separate Julia thread. It does NOT guarantee f() itself is preemptible.
# eliminate()/groebner_basis() ultimately block on a Singular or msolve C
# library call; if that C call does not yield back to the Julia scheduler
# (Singular's classical engine, in particular, is known to run as an
# uninterruptible foreign call from Julia's point of view), then the
# background task genuinely will not finish, this function will correctly
# report :timeout, but nothing about the underlying Singular process will
# have been reclaimed -- consistent with the note below the helper about
# needing `timeout N julia ...` at the OS level for a true kill. What this
# DOES reliably give you, which the previous single blind eliminate() call
# did not: the wall-clock point at which you know a given step has NOT
# finished, without that call blocking every LATER instrumentation step
# in this file from ever running. That is the actual gain here -- prior
# runs stopped producing output entirely once the first eliminate() call
# hung; this version continues past a timed-out step to the next one.
################################################################################

function run_with_timeout(f, limit_secs; poll_secs=1.0)
    t_start = time()
    task = Threads.@spawn begin
        try
            (:ok, f())
        catch e
            (:error, e)
        end
    end
    while !istaskdone(task) && (time() - t_start) < limit_secs
        sleep(poll_secs)
    end
    elapsed = time() - t_start
    if !istaskdone(task)
        return (nothing, :timeout, elapsed)
    end
    status, val = fetch(task)
    if status == :error
        println("  -> error: ", val)
        return (nothing, :error, elapsed)
    end
    return (val, :ok, elapsed)
end

const SUBIDEAL_TIMEOUT_SECS = 300.0   # 5 min per step -- adjust as needed
const VARSWEEP_TIMEOUT_SECS = 300.0

################################################################################
# PART B: incremental sub-ideal sweep.
#
# Build ideal(Fu_decoupled[1]), ideal(Fu_decoupled[1:2]), ...,
# ideal(Fu_decoupled[1:end]) -- always WITH the four curve equations
# included (dropping those would change the variety, not just shrink the
# ideal for timing purposes) -- and eliminate all four w's from each,
# timing every step. Fu_decoupled has 4 generators (u1 x^0, u2 x^0,
# u1 x^1, u2 x^1 -- see the construction loop above), so this is a sweep
# over prefixes of length 1..4.
################################################################################

################################################################################
# PART B: incremental sub-ideal sweep.
#
# Build ideal(Fu_decoupled[1]), ideal(Fu_decoupled[1:2]), ...,
# ideal(Fu_decoupled[1:end]) -- always WITH the four curve equations
# included (dropping those would change the variety, not just shrink the
# ideal for timing purposes) -- and eliminate all four w's from each,
# timing every step. Fu_decoupled has 4 generators (u1 x^0, u2 x^0,
# u1 x^1, u2 x^1 -- see the construction loop above), so this is a sweep
# over prefixes of length 1..4.
#
# EVIDENCE FROM ACTUAL RUN: k=1 completed in 15s (degree 36, 1445
# terms). k=2 timed out at 300s, and the k=3 step that followed
# triggered a Singular segfault (omalloc bin-page crash inside
# redtailBbb) -- most likely because the k=2 background Task was still
# running when k=3 started a second concurrent Singular call against
# shared allocator state (see the detailed NOTE further below, next to
# Part G). A segfault kills the entire Julia process and is NOT
# catchable by run_with_timeout's try/catch, so if PART_B_FULL_SWEEP is
# left on, this loop can crash before Part G (which answers the same
# question safely via fiber-product decomposition) ever runs. Defaults
# to running ONLY k=1 (the one step already confirmed safe and fast);
# set PART_B_FULL_SWEEP = true only once Parts B/C/F's timeout mechanism
# has been moved to subprocess-based (`timeout N julia ...`) kills, or if
# you specifically want to reproduce the crash for further debugging.
################################################################################

const PART_B_FULL_SWEEP = false

println("===========================================================")
println("PART B: incremental sub-ideal sweep on Fu_decoupled")
println("(each step: eliminate [wa1_d,wa2_d,wb1_d,wb2_d], timeout=",
        SUBIDEAL_TIMEOUT_SECS, "s)")
if !PART_B_FULL_SWEEP
    println("PART_B_FULL_SWEEP=false: running only k=1 (confirmed safe/fast).")
    println("k=2 previously timed out and k=3 segfaulted Singular in this exact")
    println("construction -- see PART G below for the safe way to get the")
    println("k=2-equivalent answer via fiber-product decomposition.")
end
println("===========================================================")
println()

curve_gens_d = [curve_a1_d, curve_a2_d, curve_b1_d, curve_b2_d]

k_range = PART_B_FULL_SWEEP ? (1:length(Fu_decoupled)) : (1:1)

for k in k_range
    prefix = Fu_decoupled[1:k]
    Ik = ideal(R_dec, vcat(prefix, curve_gens_d))
    println("--- k=$k: ideal(Fu_decoupled[1:$k], curves)  [", length(prefix) + 4, " generators] ---")
    result, status, elapsed = run_with_timeout(SUBIDEAL_TIMEOUT_SECS) do
        eliminate(Ik, [wa1_d, wa2_d, wb1_d, wb2_d])
    end
    if status == :ok
        gk = gens(result)
        println("  status=OK  elapsed=", round(elapsed, digits=3), "s  ",
                "generators_out=", length(gk),
                "  degrees=", total_degree.(gk),
                "  terms=", length.(terms.(gk)))
    elseif status == :timeout
        println("  status=TIMEOUT after ", round(elapsed, digits=3), "s ",
                "(still running in background -- see note on run_with_timeout)")
    else
        println("  status=ERROR after ", round(elapsed, digits=3), "s")
    end
    println()
end

################################################################################
# PART C: incremental VARIABLE sweep.
#
# Eliminate just wa1_d, then wa1_d+wa2_d (sample 1's w's only), then
# wa1_d+wa2_d+wb1_d (adding sample 2's first w), then all four. This
# directly answers: is a single sample's pair of w's already hard
# (intrinsic to one sample's algebra), or does it only blow up once
# BOTH samples' w's are being eliminated jointly (cross-sample
# interaction)? Run against the FULL Fu_decoupled + curves ideal (not
# the sub-ideal sweep from Part B) so this isolates the variable-count
# effect specifically.
#
# RISK, based on actual evidence: this runs against Iu_decoupled, i.e.
# ALL FOUR Fu_decoupled generators together -- the same joint-sample
# shape whose 2-generator version (Part B's k=2) already timed out and
# whose 3-generator version (k=3) segfaulted Singular. The first two
# steps here (wa1_d alone; wa1_d+wa2_d) only involve sample-1 variables
# and curve_a1_d/curve_a2_d in terms of what's REACHABLE from those
# variables, but Iu_decoupled itself still contains all 4 generators as
# ideal members regardless of which variables you ask eliminate() to
# remove -- so even the "sample 1 only" steps are not guaranteed as safe
# as Part G's genuinely-isolated small-ring version. Steps 3 and 4
# explicitly add sample-2 variables and are the most likely to reproduce
# the hang/segfault. Same guard as Part B: default to the first step
# only (which involves the fewest target variables and is closest to
# the confirmed-fast Part B k=1 case), full sweep opt-in via
# PART_C_FULL_SWEEP.
################################################################################

const PART_C_FULL_SWEEP = false

println("===========================================================")
println("PART C: incremental VARIABLE sweep on full Iu_decoupled")
println("(timeout=", VARSWEEP_TIMEOUT_SECS, "s per step)")
if !PART_C_FULL_SWEEP
    println("PART_C_FULL_SWEEP=false: running only step 1 (wa1_d alone).")
    println("Steps 2-4 add more variables/cross-sample coupling and risk the")
    println("same timeout/segfault seen in Part B k=2/k=3 -- see PART G below")
    println("for the safe, decomposed way to get the cross-sample answer.")
end
println("===========================================================")
println()

var_prefixes = [
    ("wa1_d only",                     [wa1_d]),
    ("wa1_d, wa2_d (sample 1 only)",   [wa1_d, wa2_d]),
    ("wa1_d, wa2_d, wb1_d",            [wa1_d, wa2_d, wb1_d]),
    ("wa1_d, wa2_d, wb1_d, wb2_d (all)", [wa1_d, wa2_d, wb1_d, wb2_d]),
]

prefixes_to_run = PART_C_FULL_SWEEP ? var_prefixes : var_prefixes[1:1]

if false # this times out
for (label, vs) in prefixes_to_run
    println("--- eliminating: $label ---")
    result, status, elapsed = run_with_timeout(VARSWEEP_TIMEOUT_SECS) do
        eliminate(Iu_decoupled, vs)
    end
    if status == :ok
        gk = gens(result)
        println("  status=OK  elapsed=", round(elapsed, digits=3), "s  ",
                "generators_out=", length(gk),
                "  degrees=", total_degree.(gk),
                "  terms=", length.(terms.(gk)))
    elseif status == :timeout
        println("  status=TIMEOUT after ", round(elapsed, digits=3), "s ",
                "(still running in background -- see note on run_with_timeout)")
    else
        println("  status=ERROR after ", round(elapsed, digits=3), "s")
    end
    println()
end
end # this times out^
################################################################################
# PART D: cheap dimension/codimension diagnostics on the CURVE ideal only
# (4 generators, degree 5 each, 8 variables -- should be fast) plus, if
# it survives its own timeout, on the smallest Part-B sub-ideal (k=1).
# dim()/codim() on the FULL Iu_decoupled are deliberately NOT called
# here -- the file's own earlier NOTE (see the dim(Iu)/dim(Iuv) removal
# above) already established that dim() triggers an uncontrolled
# default-ordering Groebner computation internally via
# singular_groebner_generators, independent of any ordering used
# elsewhere in this file. Calling it on the full system would just be a
# second, differently-shaped way of reproducing the same hang, not a
# diagnostic of it.
################################################################################

println("===========================================================")
println("PART D: dim/codim diagnostics (curve ideal, and smallest sub-ideal)")
println("===========================================================")
println()

println("--- dim/codim of curve-only ideal (4 gens, degree 5 each) ---")
result, status, elapsed = run_with_timeout(SUBIDEAL_TIMEOUT_SECS) do
    Icurve = ideal(R_dec, curve_gens_d)
    (dim(Icurve), codim(Icurve))
end
if status == :ok
    println("  status=OK  elapsed=", round(elapsed, digits=3), "s  dim=", result[1], "  codim=", result[2])
else
    println("  status=$status after ", round(elapsed, digits=3), "s")
end
println()

println("--- dim/codim of smallest sub-ideal (Fu_decoupled[1] + curves) ---")
result, status, elapsed = run_with_timeout(SUBIDEAL_TIMEOUT_SECS) do
    I1 = ideal(R_dec, vcat([Fu_decoupled[1]], curve_gens_d))
    (dim(I1), codim(I1))
end
if status == :ok
    println("  status=OK  elapsed=", round(elapsed, digits=3), "s  dim=", result[1], "  codim=", result[2])
else
    println("  status=$status after ", round(elapsed, digits=3), "s  ",
            "(if this alone times out, dim()/codim() themselves are the ",
            "pathological call, not eliminate() -- see PART A/B/C results ",
            "above for where actual elimination first breaks)")
end
println()

################################################################################
# PART E: confirm the ordering eliminate() is actually constructing.
#
# Oscar's eliminate(I, vars) does not expose its internal ordering object
# for direct inspection (there is no `eliminate(...; ordering=)` kwarg,
# and no public accessor returns "the ordering eliminate() used" after
# the fact -- confirmed against the current Oscar documentation for
# MPolyIdeal elimination, not assumed). What IS documented and directly
# checkable is what ordering groebner_basis(...; ordering=...) uses when
# YOU pass one explicitly, which is a separate code path. So: print
# block_ordering_dec (the explicit ordering object already built above,
# used only by direct groebner_basis calls) so its actual structure is
# visible, and print this caveat instead of asserting what eliminate()
# does internally without a way to check it.
################################################################################

println("===========================================================")
println("PART E: ordering actually in use")
println("===========================================================")
println()
println("block_ordering_dec (explicit, only consumed by direct groebner_basis")
println("calls, NOT by eliminate()):")
println("  ", block_ordering_dec)
println()
println("eliminate(I, vars) builds its own internal elimination ordering")
println("(an elimination-ordering variant, block-with-vars-dominant in spirit)")
println("and does not expose that ordering object for inspection via any")
println("documented Oscar API as of this writing -- not claiming a specific")
println("internal implementation here since it isn't independently checkable")
println("from user code. If the exact internal ordering matters, the only")
println("verifiable route is calling groebner_basis(I; ordering=<explicit")
println("elimination ordering built by hand>, algorithm=:f4) directly instead")
println("of eliminate(), so the ordering used is the one YOU constructed and")
println("printed above, not an opaque internal choice.")
println()

################################################################################
# NOTE on running this as isolated subprocesses instead of in-process
# timeouts:
#
# run_with_timeout above cannot truly kill a hung Singular/msolve C call
# -- it just stops WAITING for it. For a real kill (freeing CPU/RAM so
# the next step's timing isn't contaminated by a still-running previous
# step), run each Part B/C step as its own OS process instead:
#
#   timeout 300 julia -t 20 -e '
#       include("elim2_single_step.jl");   # a trimmed script that builds
#                                            # just R_dec/Fu_decoupled/curves
#                                            # and does ONE eliminate() call
#       eliminate(Ik, [wa1_d, wa2_d, wb1_d, wb2_d])
#   '
#
# `timeout 300 ...` (the coreutils command, not Julia code) sends SIGTERM
# after 300s and actually reclaims the process. This is more setup (needs
# the shared construction code factored into an includable file) but is
# the only way to get a clean kill; the in-process version above is
# faster to run right now and sufficient for the first-pass "where does
# it explode" question this instrumentation pass is actually for.
################################################################################

################################################################################
# PART G: FIBER-PRODUCT DECOMPOSITION.
#
# Part B's k=1->k=2 transition (15s, OK -> hang -> segfault) is not
# generic Groebner slowness. Fu_decoupled[1] (sample 1, target U0) and
# Fu_decoupled[2] (sample 2, target U0) share ONLY the variable U0 --
# their w/a/b variables are completely disjoint. That means
# ideal(Fu_decoupled[1], Fu_decoupled[2], curves) is, scheme-
# theoretically, the fiber product of the two samples' varieties over
# the shared U0-coordinate: R_dec/I = (R_a/I_a) (x)_{k[U0]} (R_b/I_b).
#
# Elimination commutes with this structure because eliminating the wa's
# cannot touch any generator that only involves wb's and vice versa:
#
#   elim_{wa1,wa2,wb1,wb2}(Ia + Ib) = elim_{wa1,wa2}(Ia) + elim_{wb1,wb2}(Ib)
#
# as ideals in k[a1,a2,b1,b2,U0]. This is a direct consequence of
# I ∩ k[remaining vars] applied to a sum of ideals in disjoint-except-
# shared-U0 variable sets -- eliminating the wa's is a self-contained
# computation inside k[wa1,wa2,a1,a2,U0] and simply passing through the
# wb-only generators unchanged (they contain no wa's to eliminate), and
# symmetrically for wb. So instead of handing Singular one 6-generator
# ideal in the union of both variable sets (which is what triggered the
# hang/segfault in Part B's k=2 step), do TWO independent eliminations,
# each in its own small ring, and take the SUM of the results in the
# combined ring at the end -- Singular never sees the joint system.
#
# This is built here for the U0-pair (Fu_decoupled[1] vs [2]) and the
# U1-pair (Fu_decoupled[3] vs [4]) separately, matching how the
# construction loop above actually built Fu_decoupled (alternating
# sample-1/sample-2 per target variable U0, then U1).
################################################################################

println()
println("===========================================================")
println("PART G: fiber-product decomposition (eliminate each side ")
println("independently, then combine via shared U-variable)")
println("===========================================================")
println()

# Fu_decoupled was built as [u1_x^0(U0), u2_x^0(U0), u1_x^1(U1), u2_x^1(U1)]
# -- confirm that pairing explicitly rather than assuming it silently.
fiber_pairs = [
    ("U0", Fu_decoupled[1], Fu_decoupled[2], U_vars[1]),
    ("U1", Fu_decoupled[3], Fu_decoupled[4], U_vars[2]),
]

if false # this section segfaults
for (uname, ga, gb, Uvar) in fiber_pairs
    println("--- fiber pair over $uname ---")
    println("  side A vars: ", vars(ga), "   side B vars: ", vars(gb))
    shared = intersect(Set(vars(ga)), Set(vars(gb)))
    println("  shared variables: ", collect(shared),
            shared == Set([Uvar]) ? "  (confirmed: only $uname shared)" :
            "  *** WARNING: shared set is not just {$uname} -- fiber-product ***" *
            "  *** decomposition below is NOT valid for this pair, skipping ***")
    if shared != Set([Uvar])
        println()
        continue
    end

    # Build side A's SELF-CONTAINED ring: only the variables ga actually
    # uses (its own w's, its own a/b's, and Uvar), remapped into a small
    # fresh ring so Singular only ever sees this side's variables.
    a_vars_sorted = sort(vars(ga); by = string)  # deterministic order
    Ra, ra_gens = polynomial_ring(F, string.(a_vars_sorted))
    a_remap = Dict(zip(a_vars_sorted, ra_gens))
    remap_to_Ra(f) = evaluate(f, [get(a_remap, v, zero(Ra)) for v in a_vars_sorted])
    # NOTE: evaluate(f, images) requires images indexed the same way f's
    # OWN parent ring's generators are, not a_vars_sorted -- since ga
    # lives in R_dec, we must map over ALL of R_dec's generators, sending
    # the ones ga doesn't use to 0 (they don't appear in ga's monomials
    # so this is exact, not an approximation).
    full_remap_a = [v in a_vars_sorted ? a_remap[v] : zero(Ra) for v in gens(R_dec)]
    ga_small = evaluate(ga, full_remap_a)

    # curve equations relevant to side A: whichever of curve_a*_d/curve_b*_d
    # share variables with ga.
    curve_gens_d_local = [curve_a1_d, curve_a2_d, curve_b1_d, curve_b2_d]
    curves_a = [c for c in curve_gens_d_local if !isempty(intersect(Set(vars(c)), Set(a_vars_sorted)))]
    curves_a_small = [evaluate(c, full_remap_a) for c in curves_a]

    Ia_small = ideal(Ra, vcat([ga_small], curves_a_small))
    w_vars_a = [v for v in ra_gens if string(v) in ("wa1","wa2","wb1","wb2")]

    println("  side A: independent ring with ", ngens(Ra), " vars, eliminating ", w_vars_a)
    resultA, statusA, elapsedA = run_with_timeout(SUBIDEAL_TIMEOUT_SECS) do
        eliminate(Ia_small, w_vars_a)
    end
    if statusA == :ok
        gA = gens(resultA)
        println("    status=OK  elapsed=", round(elapsedA, digits=3), "s  ",
                "generators=", length(gA), "  degrees=", total_degree.(gA),
                "  terms=", length.(terms.(gA)))
    else
        println("    status=$statusA after ", round(elapsedA, digits=3), "s")
    end

    # Side B, same procedure.
    b_vars_sorted = sort(vars(gb); by = string)
    Rb, rb_gens = polynomial_ring(F, string.(b_vars_sorted))
    b_remap = Dict(zip(b_vars_sorted, rb_gens))
    full_remap_b = [v in b_vars_sorted ? b_remap[v] : zero(Rb) for v in gens(R_dec)]
    gb_small = evaluate(gb, full_remap_b)
    curves_b = [c for c in curve_gens_d_local if !isempty(intersect(Set(vars(c)), Set(b_vars_sorted)))]
    curves_b_small = [evaluate(c, full_remap_b) for c in curves_b]
    Ib_small = ideal(Rb, vcat([gb_small], curves_b_small))
    w_vars_b = [v for v in rb_gens if string(v) in ("wa1","wa2","wb1","wb2")]

    println("  side B: independent ring with ", ngens(Rb), " vars, eliminating ", w_vars_b)
    resultB, statusB, elapsedB = run_with_timeout(SUBIDEAL_TIMEOUT_SECS) do
        eliminate(Ib_small, w_vars_b)
    end
    if statusB == :ok
        gB = gens(resultB)
        println("    status=OK  elapsed=", round(elapsedB, digits=3), "s  ",
                "generators=", length(gB), "  degrees=", total_degree.(gB),
                "  terms=", length.(terms.(gB)))
    else
        println("    status=$statusB after ", round(elapsedB, digits=3), "s")
    end

    if statusA == :ok && statusB == :ok
        println("  BOTH sides eliminated independently -- combined result would be")
        println("  elim_A(Ia) + elim_B(Ib) in k[a1,a2,b1,b2,$uname], WITHOUT Singular")
        println("  ever seeing the joint 6+ generator system that hung/segfaulted")
        println("  in Part B. Total combined generator count = ",
                length(gens(resultA)) + length(gens(resultB)), ".")
        println("  (Not re-embedding into R_dec here -- these live in Ra/Rb, two")
        println("  DIFFERENT small rings, both sharing the variable name \"$uname\"")
        println("  but as distinct ring objects; embedding both into one common")
        println("  k[a1,a2,b1,b2,$uname] ring for actual downstream use is a")
        println("  mechanical remap, omitted here since the point of this pass is")
        println("  the elimination-cost comparison, not the final variety.)")
    end
    println()
end

end # end segfault section

################################################################################
# PART H: FULLY INDEPENDENT small-ring reconstruction (not a restriction
# of Part G).
#
# Part G took Fu_decoupled[1]/[2] (already elements of the 12-variable
# R_dec) and remapped/evaluated them into smaller rings -- a restriction,
# not an independent build. This part is stricter, per direct request:
# it builds u1_num[1]/u1_den[1] (sample 1's ORIGINAL numerator/
# denominator pair, still living in the ORIGINAL 8-variable ring R from
# much earlier in this file, never touched by the R_dec construction at
# all) into a brand-new 5-variable ring from scratch, with NO reference
# to R_dec, Iu_decoupled, or Fu_decoupled anywhere in this construction.
# If this succeeds quickly where Part C's single-variable elimination on
# the full Iu_decoupled did not, that's strong evidence the pathology is
# an artifact of the 12-variable ambient ring (or of something Oscar/
# Singular does when constructing/preparing an ideal in that ring -- see
# the dim() segfault discussion below) rather than being intrinsic to
# the elimination mathematics itself.
#
# NEW EVIDENCE motivating this part: in the actual run, eliminating just
# wa1_d ALONE from the full Iu_decoupled timed out (Part C), and then
# dim() on the CURVE-ONLY ideal (4 generators, degree 5 each -- about as
# simple as an ideal in this ring gets) segfaulted. A single-variable
# elimination hanging, and dim() crashing on a tiny ideal, are both hard
# to explain by "the elimination math is genuinely hard" -- eliminating
# ONE variable from a system where every generator is individually cheap
# should not be expensive if the joint structure is actually as
# decomposable as Part G's math argument says it is. This points at
# something about how Oscar/Singular is handling the 12-variable R_dec
# ring itself (ring/ideal object construction, internal GB caching
# triggered by dim()'s call path -- see PART D's comment on
# singular_groebner_generators -- or possibly a resource/threading issue
# specific to this Oscar/Singular build) rather than at the elimination
# problem. This part tests that directly by never constructing anything
# in R_dec at all.
################################################################################

println()
println("===========================================================")
println("PART H: fully independent small-ring reconstruction (no R_dec)")
println("===========================================================")
println()

println("Building sample 1's isolated ring: [wa1, wa2, a1, a2, U0], from")
println("u1_num[1]/u1_den[1] directly -- R_dec is not referenced anywhere below.")
println()

Rs1, (wa1_s, wa2_s, a1_s, a2_s, U0_s) = polynomial_ring(F, ["wa1", "wa2", "a1", "a2", "U0"])

# u1_num[1]/u1_den[1] live in R (gens: wa1,wa2,wb1,wb2,a2,a1,b2,b1 --
# established far above at R's construction). Map wa1->wa1_s, wa2->wa2_s,
# wb1->0, wb2->0 (sample 1's num/den are already confirmed, in the
# DEGREE-IN-W DIAGNOSTIC printed earlier in this run, to have degree 0
# in wb1,wb2 -- so sending those generators to 0 is exact, not lossy),
# a2->a2_s, a1->a1_s, b2->0, b1->0.
#r_gens_full = gens(R)  # [wa1, wa2, wb1, wb2, a2, a1, b2, b1]
#images_s1 = [wa1_s, wa2_s, zero(Rs1), zero(Rs1), a2_s, a1_s, zero(Rs1), zero(Rs1)]
images_s1 = [wa1_s, wa2_s, a1_s, a2_s]
u1_num1_s = evaluate(u1_num[1], images_s1)
u1_den1_s = evaluate(u1_den[1], images_s1)
h_s1 = u1_num1_s - U0_s * u1_den1_s

curve_a1_s = wa1_s^2 - (a1_s^5 + a1_s + 2)
curve_a2_s = wa2_s^2 - (a2_s^5 + a2_s + 2)

println("  h_s1 = u1_num[1] - U0*u1_den[1], rebuilt in Rs1: degree=",
        total_degree(h_s1), "  terms=", length(terms(h_s1)))
println("  (compare to Fu_decoupled[1]'s degree=17/terms=306 from PART A --")
println("  these should match exactly since it's the same polynomial,")
println("  independently reconstructed)")
println()

Is1 = ideal(Rs1, [h_s1, curve_a1_s, curve_a2_s])

println("Eliminating [wa1_s, wa2_s] from Is1 (5-variable ring, 3 generators)...")
resultS1, statusS1, elapsedS1 = run_with_timeout(SUBIDEAL_TIMEOUT_SECS) do
    eliminate(Is1, [wa1_s, wa2_s])
end
# Fix for Sample 1 block
if statusS1 == :ok
    gS1 = gens(resultS1)
    println("  status=OK  elapsed=", round(elapsedS1, digits=3), "s")
    println("  parent ring = ", base_ring(resultS1)) # <-- Changed parent to base_ring
    println("  number of generators = ", length(gS1))
    for (i, g) in enumerate(gS1)
        println("    gen $i: degree=", total_degree(g), "  terms=", length(terms(g)))
    end
else
    println("  status=$statusS1 after ", round(elapsedS1, digits=3), "s")
end
println()

println("Building sample 2's isolated ring: [wb1, wb2, b1, b2, U0], from")
println("u2_num[1]/u2_den[1] directly.")
println()

Rs2, (wb1_s, wb2_s, b1_s, b2_s, U0_s2) = polynomial_ring(F, ["wb1", "wb2", "b1", "b2", "U0"])

images_s2 = [zero(Rs2), zero(Rs2), wb1_s, wb2_s, b2_s, zero(Rs2), zero(Rs2), b1_s]
# NOTE: r_gens_full order is [wa1,wa2,wb1,wb2,a2,a1,b2,b1] -- images_s2
# must follow that SAME order, mapping wa1,wa2,a2,a1 -> 0 and
# wb1,wb2,b2,b1 -> their Rs2 generators. Written out explicitly (not
# via a generic Dict-based remap helper) specifically so this mapping is
# directly inspectable against r_gens_full's printed order rather than
# hidden behind indirection, given how easy an off-by-one here would be
# to get wrong silently.
u2_num1_s = evaluate(u2_num[1], images_s2)
u2_den1_s = evaluate(u2_den[1], images_s2)
h_s2 = u2_num1_s - U0_s2 * u2_den1_s

curve_b1_s = wb1_s^2 - (b1_s^5 + b1_s + 2)
curve_b2_s = wb2_s^2 - (b2_s^5 + b2_s + 2)

println("  h_s2 = u2_num[1] - U0*u2_den[1], rebuilt in Rs2: degree=",
        total_degree(h_s2), "  terms=", length(terms(h_s2)))
println()

Is2 = ideal(Rs2, [h_s2, curve_b1_s, curve_b2_s])

println("Eliminating [wb1_s, wb2_s] from Is2 (5-variable ring, 3 generators)...")
resultS2, statusS2, elapsedS2 = run_with_timeout(SUBIDEAL_TIMEOUT_SECS) do
    eliminate(Is2, [wb1_s, wb2_s])
end
# Fix for Sample 2 block
if statusS2 == :ok
    gS2 = gens(resultS2)
    println("  status=OK  elapsed=", round(elapsedS2, digits=3), "s")
    println("  parent ring = ", base_ring(resultS2)) # <-- Changed parent to base_ring
    println("  number of generators = ", length(gS2))
    for (i, g) in enumerate(gS2)
        println("    gen $i: degree=", total_degree(g), "  terms=", length(terms(g)))
    end
else
    println("  status=$statusS2 after ", round(elapsedS2, digits=3), "s")
end
println()

println("#" ^ 70)
println("PART H READOUT")
println("#" ^ 70)
println()
println("Sample 1 isolated elimination: ", statusS1,
        statusS1 == :ok ? " ($(round(elapsedS1,digits=3))s)" : "")
println("Sample 2 isolated elimination: ", statusS2,
        statusS2 == :ok ? " ($(round(elapsedS2,digits=3))s)" : "")
println()
if statusS1 == :ok && statusS2 == :ok
    println("BOTH isolated 5-variable eliminations succeeded where PART C's")
    println("single-variable (wa1_d alone) elimination on the full 12-variable")
    println("Iu_decoupled did not. This is direct evidence the pathology is NOT")
    println("intrinsic to the elimination mathematics -- a 5-variable, 3-generator")
    println("elimination is not hard -- but IS specific to how Oscar/Singular")
    println("handles the larger ambient ring/ideal object, independent of how")
    println("many variables are actually being eliminated from it.")
elseif statusS1 == :timeout || statusS2 == :timeout
    println("At least one isolated elimination ALSO timed out. This would mean")
    println("the pathology is not purely an ambient-ring artifact -- something")
    println("about eliminating wa1,wa2 (or wb1,wb2) from THIS SPECIFIC degree-17")
    println("generator is intrinsically expensive, contradicting Part B k=1's")
    println("15s/degree-36/1445-term result for the FOUR-variable elimination of")
    println("the same generator. If that happens, the discrepancy between this")
    println("result and Part B k=1 (same generator, same variables eliminated,")
    println("different ring) is itself the next thing to explain.")
end
println()
println("On the dim() segfault (PART D, curve-only ideal): this happened on a")
println("4-generator, degree-5 ideal -- about as simple as this ring gets. That")
println("a crash occurred there specifically inside krull_dim ->")
println("singular_groebner_generators -> groebner_assure -> Singular's std()")
println("(see the backtrace) suggests dim()'s particular code path may be doing")
println("something version-specific and fragile in THIS Oscar/Singular build,")
println("independent of ideal difficulty. If PART H's isolated eliminations")
println("above succeed cleanly, that further isolates the problem: eliminate()")
println("itself may be fine on appropriately small inputs, and dim() specifically")
println("(not eliminate()) may be the fragile call. This combination -- ")
println("eliminate() hanging on the full ring, dim() segfaulting on a trivial")
println("ideal -- is exactly the shape of evidence worth filing as an issue")
println("against Singular.jl/Oscar.jl (https://github.com/oscar-system/Oscar.jl/issues),")
println("including: Oscar/Julia/Singular.jl versions (Pkg.status() output),")
println("this file's construction of R_dec and Is1/Is2, and both crash")
println("backtraces already captured in this run's output.")
# redtailBbb/omalloc allocator (see the backtrace after the k=2 timeout)
# is consistent with the k=2 background Task from Part B's run_with_timeout
# NOT having been killed -- Threads.@spawn cannot preempt a blocking
# Singular C call (see the caveat on run_with_timeout above), so when
# Part B moved on to k=3, the k=2 elimination was very likely STILL
# running in another thread, and the k=3 call started a SECOND
# concurrent Singular computation against the same underlying Singular/
# omalloc global allocator state. Singular's memory manager is not
# documented as safe against two concurrent kStd_internal/bba calls
# sharing global allocator pages from independent Task-based threads --
# the omInsertBinPage/omAllocBinFromFullPage frames in the crash are
# exactly the allocator's bin-page bookkeeping, and a page-table race
# between two simultaneous Groebner computations is a plausible direct
# cause. This is itself an argument for running Part B/C/G's timed steps
# as separate OS PROCESSES (`timeout N julia ...`) rather than
# in-process Tasks in any follow-up: it would avoid both the "can't
# actually kill a hung step" limitation AND this apparent concurrent-
# Singular-call crash. Not fixed in this patch since it requires
# factoring the shared construction code into an includable file, which
# is a larger restructuring than a targeted patch; the fiber-product
# decomposition in Part G above sidesteps the problem for THIS specific
# ideal by never trying to run two eliminate() calls in the same process
# without waiting for the first, but a general fix for Parts B/C/F still
# needs the subprocess-based timeout.
################################################################################
println("===========================================================")
println("PART I: The Sandbox Factory (Automated Elimination)")
println("===========================================================")

################################################################################
# Forward declarations, hoisted from later in this file (the
# part_i_squarefree_diag.jl / correct_multiplicity blocks below), because
# this is a flat top-to-bottom script with no function-hoisting: the
# resultant + multiplicity-correction pipeline wired into
# process_sample_1_coeff/process_sample_2_coeff just below needs
# canonical_factor_key, factor_multiset, and correct_multiplicity to
# already be defined by the time those factories are called (including the
# "Factory Test" call immediately after process_sample_1_coeff's
# definition). The originals still appear later in the file, unchanged --
# Julia just lets the later `function` definitions redefine these methods
# again (identically), which is harmless.
################################################################################

"""
    canonical_factor_key(f) -> String

Return a hashable, order-independent, unit-scaled key for an irreducible
polynomial `f`, so two irreducible factors coming out of independent
`factor()` calls (potentially differing by a nonzero field-element unit,
and with no guaranteed enumeration order) compare equal iff they are
associates.

Normalization: divide by the coefficient of the lexicographically-first
monomial (in a fixed, deterministic term order), so the leading
coefficient of the normalized polynomial is always 1. This is well
defined for any irreducible over a field, independent of which unit
multiple factor() happened to emit.
"""
function canonical_factor_key(f)
    R = parent(f)
    F = base_ring(R)
    # Deterministic term order: sort exponent vectors lexicographically.
    exps = collect(AbstractAlgebra.exponent_vectors(f))
    cfs  = collect(coefficients(f))
    order = sortperm(exps)  # lexicographic on Vector{Int} is Julia's default
    lead_c = cfs[order[1]]
    inv_lead = inv(lead_c)
    # Build normalized (monic-by-convention) term list as a canonical string.
    io = IOBuffer()
    for idx in order
        c = cfs[idx] * inv_lead
        print(io, string(c), ":", string(exps[idx]), ";")
    end
    return String(take!(io))
end

"""
    factor_multiset(f) -> Dict{String,Int}

Factor `f` and return a map: canonical_factor_key(irreducible factor) => exponent.
Keys are unit/order independent so two factorizations of associate
polynomials produce identical dictionaries.
"""
function factor_multiset(f)
    fac = factor(f)
    d = Dict{String,Int}()
    for (p, e) in fac
        key = canonical_factor_key(p)
        d[key] = get(d, key, 0) + e
    end
    return d, fac
end

"""
    correct_multiplicity(Res1, Res2; label="")

Gröbner-free multiplicity correction. Factors `Res1` and `Res2` (this is
the only factorization work needed -- no Groebner basis), matches factors
via `canonical_factor_key`, and for every factor whose Res2-exponent
exceeds its Res1-exponent, divides Res2 down by the excess power.

Returns a NamedTuple:
  corrected          -- the corrected polynomial (Res2 with all detected
                         excess multiplicity divided out)
  applied_factors    -- Vector of (key, F, excess) actually divided out
  t_factor           -- time spent factoring Res1 and Res2
  t_correct          -- time spent dividing out excess multiplicity
  all_divisions_exact -- whether every candidate excess power divided
                         Res2 evenly (a self-consistency check: if this
                         is false, factor()'s own exponents were
                         inconsistent with exact division, and the
                         "corrected" result should not be trusted blindly)

This function never calls eliminate()/groebner_basis() -- it is safe to
run unconditionally in default (CHECK_GROEBNER=false) benchmark mode.
"""
function correct_multiplicity(Res1, Res2; label::AbstractString="")
    println("-"^70)
    println("MULTIPLICITY CORRECTION (Gröbner-free)", isempty(label) ? "" : "  [$label]")
    println("-"^70)

    t0 = time()
    set1, fac1 = factor_multiset(Res1)
    set2, fac2 = factor_multiset(Res2)
    t_factor = time() - t0
    println("  factor(Res1)+factor(Res2) elapsed = ", round(t_factor, digits=4), "s  -> ",
            length(set1), " / ", length(set2), " distinct factor(s)")

    poly_of_2 = Dict{String,Any}(canonical_factor_key(p) => p for (p, _e) in fac2)

    # Candidates: factors present in Res2 whose exponent exceeds their
    # exponent in Res1 (0 if absent from Res1 entirely -- a factor that
    # appears ONLY in Res2 with no Res1 presence is, by this criterion,
    # entirely an artifact of the second resultant step and is corrected
    # down to exponent 0, i.e. divided out completely).
    all_keys2 = collect(keys(set2))
    candidates = NamedTuple[]
    for k in all_keys2
        e1 = get(set1, k, 0)
        e2 = set2[k]
        if e2 > e1
            push!(candidates, (key = k, excess = e2 - e1, exp_Res1 = e1, exp_Res2 = e2))
        end
    end

    println("  candidate inflated factor(s) (exp(Res2) > exp(Res1)): ", length(candidates))
    for c in candidates
        rep = poly_of_2[c.key]
        println("    degree=", total_degree(rep), "  terms=", length(terms(rep)),
                "  exp(Res1)=", c.exp_Res1, "  exp(Res2)=", c.exp_Res2, "  excess=", c.excess)
    end

    t0 = time()
    corrected = Res2
    applied = NamedTuple[]
    all_exact = true
    for c in candidates
        Fp = poly_of_2[c.key]
        Fpow = Fp^c.excess
        divides_exactly = false
        q = nothing
        try
            qtmp, rem = divrem(corrected, Fpow)
            if iszero(rem)
                divides_exactly = true
                q = qtmp
            else
                ok, q2 = divides(corrected, Fpow)
                if ok
                    divides_exactly = true
                    q = q2
                end
            end
        catch e
            println("    ** division by F^", c.excess, " raised an error -- ", sprint(showerror, e), " **")
        end
        if divides_exactly
            corrected = q
            push!(applied, (key = c.key, excess = c.excess))
            println("  divided out excess exponent ", c.excess, " of one factor -> ",
                    "degree=", (iszero(corrected) ? -1 : total_degree(corrected)),
                    "  terms=", length(terms(corrected)))
        else
            all_exact = false
            println("  ** excess exponent ", c.excess, " did NOT divide evenly -- ",
                    "skipping this candidate, correction may be incomplete **")
        end
    end
    t_correct = time() - t0

    if isempty(candidates)
        println("  (no candidate inflated factors -- Res2 already matches Res1's ",
                "multiplicities on every shared factor; corrected == Res2 unchanged)")
    end

    println("  correction elapsed = ", round(t_correct, digits=4), "s")
    println("  final corrected result: degree=", (iszero(corrected) ? -1 : total_degree(corrected)),
            "  terms=", length(terms(corrected)))
    println("-"^70)

    return (
        corrected = corrected,
        applied_factors = applied,
        t_factor = t_factor,
        t_correct = t_correct,
        all_divisions_exact = all_exact,
    )
end

# This is our factory. It takes a raw tower coefficient, builds a 5-variable ring, and eliminates the w's.
#
# Groebner-free rewrite (wired to correct_multiplicity, per chat): this used
# to call eliminate(I_small, [w1, w2]) directly, which is the slow Groebner
# oracle. We now use the exact PATH B / correction recipe verified against
# Groebner in _run_bench: sequential resultants to eliminate w1 then w2,
# then correct_multiplicity(step1, step2) to divide out the excess
# (inflated) multiplicity that the two-step resultant chain introduces
# relative to the true (Groebner) elimination ideal generator. This was
# checked (CHECK_GROEBNER=true runs of _run_bench) to reproduce gA exactly,
# so it's safe to use as the production path -- and since it divides out
# spurious factors before this coefficient ever reaches PART F/Bezout, the
# polynomials feeding the Bezout matrix should also come out smaller.
function process_sample_1_coeff(raw_coeff, target_name)
    println("  Spinning up sandbox for: ", target_name)
    
    # 1. Build the 5-variable sandbox
    R_small, (w1, w2, a1, a2, T) = polynomial_ring(F, ["wa1", "wa2", "a1", "a2", target_name])
    
    # 2. Convert the raw tower fraction directly into our new sandbox
    t_gens = [a1, a2]
    w_gens = [w1, w2]
    num_s, den_s = tower_to_ring(raw_coeff, t_gens, w_gens)
    
    # 3. Build the graph equation: Target * denominator - numerator = 0
    h_s = T * den_s - num_s
    
    # 4. Add the curve equations to the sandbox
    curve1 = w1^2 - (a1^5 + a1 + 2)
    curve2 = w2^2 - (a2^5 + a2 + 2)
    
    # 5. Eliminate the w's via sequential resultants instead of eliminate():
    #    step1 = Res_{w1}(h_s, curve1)   -- eliminates w1
    #    step2 = Res_{w2}(step1, curve2) -- eliminates w2
    step1 = resultant(h_s, curve1, 1)
    step2 = resultant(step1, curve2, 2)

    # 6. Divide out excess (inflated) multiplicity picked up by the
    #    resultant chain, Groebner-free, verified equal to eliminate()'s
    #    output in _run_bench.
    corr = correct_multiplicity(step1, step2; label="$(target_name) (a-vars, sample1)")

    # Return the winning (corrected) polynomial
    return corr.corrected
end

# Let's test the factory on the very first coefficient!
test_result = process_sample_1_coeff(res1.u_RS_coeffs[1], "U0")
println("Factory Test Successful! Resulting polynomial has degree: ", total_degree(test_result))
println()


# ==============================================================================
# Factory for Sample 2 (Uses 'b' variables instead of 'a')
# ==============================================================================
# Groebner-free rewrite -- same reasoning as process_sample_1_coeff above,
# mirrored for the b-variable (sample 2) sandbox.
function process_sample_2_coeff(raw_coeff, target_name)
    println("  Spinning up sandbox (Sample 2) for: ", target_name)
    
    # 1. Build the 5-variable sandbox for Sample 2
    R_small, (w1, w2, b1, b2, T) = polynomial_ring(F, ["wb1", "wb2", "b1", "b2", target_name])
    
    # 2. Convert the raw tower fraction directly into our new sandbox
    t_gens = [b1, b2]
    w_gens = [w1, w2]
    num_s, den_s = tower_to_ring(raw_coeff, t_gens, w_gens)
    
    # 3. Build the graph equation
    h_s = T * den_s - num_s
    
    # 4. Add the curve equations (using b)
    curve1 = w1^2 - (b1^5 + b1 + 2)
    curve2 = w2^2 - (b2^5 + b2 + 2)
    
    # 5. Eliminate the w's via sequential resultants instead of eliminate():
    #    step1 = Res_{w1}(h_s, curve1)   -- eliminates w1
    #    step2 = Res_{w2}(step1, curve2) -- eliminates w2
    step1 = resultant(h_s, curve1, 1)
    step2 = resultant(step1, curve2, 2)

    # 6. Divide out excess (inflated) multiplicity picked up by the
    #    resultant chain, Groebner-free, verified equal to eliminate()'s
    #    output in _run_bench.
    corr = correct_multiplicity(step1, step2; label="$(target_name) (b-vars, sample2)")

    return corr.corrected
end

println("===========================================================")
println("PART J: The Assembly Line (Processing All Coefficients)")
println("===========================================================")

# ------------------------------------------------------------------------
# PARALLELIZED via separate OS processes, NOT Threads.@spawn.
#
# Part H already documented why: two eliminate()/Singular calls running
# concurrently *in the same process* raced on Singular's global omalloc
# allocator and crashed (omInsertBinPage/omAllocBinFromFullPage), because
# Threads.@spawn cannot preempt or truly isolate a blocking Singular C
# call. Each sandbox below is dispatched to its own `julia
# part_j_worker.jl` subprocess instead, so every eliminate() call gets
# its own address space / allocator state, and the crash mode Part H
# hit simply can't occur here. Results come back via Oscar's save/load
# through a persistent output file per job.
#
# All 8 jobs (4 targets x 2 samples) are independent -- none of the
# process_sample_*_coeff calls depend on each other -- but launching all
# 8 at once nearly OOM's (each Singular/Oscar subprocess is heavy), so
# they're run through a bounded worker pool instead, PART_J_MAX_WORKERS
# in flight at a time.
#
# Output files live in PART_J_OUTPUT_DIR (./tmp, next to this script),
# NOT the system /tmp -- and PERSIST across runs (no cleanup at the end)
# so that a re-run can skip any job whose output file already exists,
# rather than recomputing it.
# ------------------------------------------------------------------------

const PART_J_MAX_WORKERS = 4

num_u_coeffs = length(res1.u_RS_coeffs) - 1   # skip trivial leading "1"
num_v_coeffs = length(res1.v_RS_coeffs)

part_j_jobs = NamedTuple{(:sample, :target), Tuple{Int,String}}[]
for i in 1:num_u_coeffs
    push!(part_j_jobs, (sample = 1, target = "U$(i-1)"))
    push!(part_j_jobs, (sample = 2, target = "U$(i-1)"))
end
for i in 1:num_v_coeffs
    push!(part_j_jobs, (sample = 1, target = "V$(i-1)"))
    push!(part_j_jobs, (sample = 2, target = "V$(i-1)"))
end

const PART_J_OUTPUT_DIR = joinpath(@__DIR__, "tmp")
mkpath(PART_J_OUTPUT_DIR)
part_j_worker_path = joinpath(@__DIR__, "part_j_worker.jl")

# Attach each job's persistent output path up front, so the
# already-done check and the launch step agree on the filename.
part_j_jobs_full = map(part_j_jobs) do job
    outfile = joinpath(PART_J_OUTPUT_DIR, "sample$(job.sample)_$(job.target).oscar")
    (job = job, outfile = outfile)
end

part_j_todo = filter(jf -> !isfile(jf.outfile), part_j_jobs_full)
part_j_skipped = filter(jf -> isfile(jf.outfile), part_j_jobs_full)

if !isempty(part_j_skipped)
    println("  Skipping ", length(part_j_skipped), " job(s) with existing output file(s):")
    for jf in part_j_skipped
        println("    already have: ", jf.outfile)
    end
end
println("  Running ", length(part_j_todo), " of ", length(part_j_jobs_full),
        " sandboxes (up to ", PART_J_MAX_WORKERS, " concurrent worker(s))...")

# Bounded worker pool: keep at most PART_J_MAX_WORKERS subprocesses alive
# at once. Jobs are handed out in order; as each running slot's process
# exits it is checked for success/failure and the next queued job (if
# any) is launched in its place.
part_j_queue = collect(part_j_todo)
part_j_running = Vector{NamedTuple}()   # (job, outfile, proc)
part_j_next_idx = 1

function part_j_launch_next!()
    global part_j_next_idx
    part_j_next_idx > length(part_j_queue) && return nothing
    jf = part_j_queue[part_j_next_idx]
    part_j_next_idx += 1
    println("  Spinning up sandbox", jf.job.sample == 2 ? " (Sample 2)" : "", " for: ", jf.job.target)
    cmd = `julia $part_j_worker_path $(jf.job.sample) $(jf.job.target) $(jf.outfile)`
    proc = run(pipeline(cmd; stdout=stdout, stderr=stderr); wait=false)
    push!(part_j_running, (job = jf.job, outfile = jf.outfile, proc = proc))
    return nothing
end

for _ in 1:min(PART_J_MAX_WORKERS, length(part_j_queue))
    part_j_launch_next!()
end

while !isempty(part_j_running)
    # Poll for any finished process, harvest it, and backfill its slot.
    finished_idx = nothing
    while finished_idx === nothing
        for (idx, pr) in enumerate(part_j_running)
            if process_exited(pr.proc)
                finished_idx = idx
                break
            end
        end
        finished_idx === nothing && sleep(0.5)
    end
    pr = popat!(part_j_running, finished_idx)
    if !success(pr.proc)
        error("Part J worker failed for sample=$(pr.job.sample) target=$(pr.job.target) " *
              "(exit code $(pr.proc.exitcode)). See its output above for the Singular/Oscar backtrace.")
    end
    part_j_launch_next!()
end

println("  All Part J sandboxes finished. Loading results back in...")

# These arrays will hold our final, clean polynomials, same order as the
# original sequential loop: U0,U1,...,V0,V1,... interleaved sample1/sample2.
clean_sample_1 = Any[]
clean_sample_2 = Any[]

for jf in part_j_jobs_full
    if !isfile(jf.outfile)
        error("Part J: expected output file missing for sample=$(jf.job.sample) " *
              "target=$(jf.job.target): $(jf.outfile)")
    end
    # load() needs the *target* ring's context; each worker built its own
    # fresh 5-variable ring per job, so we just load whatever ring/element
    # Oscar serialized -- no shared parent required here since Part K
    # remaps everything into a common ring anyway via remap_to_final().
    result = load(jf.outfile)
    if jf.job.sample == 1
        push!(clean_sample_1, result)
    else
        push!(clean_sample_2, result)
    end
end

println("\nAssembly Line Finished!")
println("Sample 1 produced ", length(clean_sample_1), " clean polynomials.")
println("Sample 2 produced ", length(clean_sample_2), " clean polynomials.")





#!/usr/bin/env julia

################################################################################
#
#  part_i_squarefree_diag.jl
#
#  Diagnostic for part_i_eliminate_vs_resultant_bench.jl.
#
#  Question: given
#      gA = Groebner eliminate() generator      (PATH A)
#      gB = sequential resultant chain result    (PATH B)
#  is gA recoverable from gB by adjusting ONLY the exponents on gB's
#  irreducible factors -- i.e. do gA and gB factor into the SAME SET of
#  irreducibles (up to unit scalars), differing only in multiplicity?
#
#  This is strictly weaker than "gA == squarefree_part(gB)" (which is the
#  special case where every gA exponent is forced to 1), so we check both:
#
#    Q1 (multiplicity-adjustable): same irreducible factor SET, any exponents
#    Q2 (squarefree part):         same set, AND every gA exponent == 1
#
#  Usage: include this file right after a PATH A / PATH B bench block has
#  run, with gA and gB bound to the two eliminant polynomials, e.g.:
#
#      gA = eliminate(I, [w1, w2])[1]
#      gB = res_w2   # final resultant-chain output
#      include("part_i_squarefree_diag.jl")
#      squarefree_multiplicity_diagnostic(gA, gB; label="U0 (a-vars)")
#
################################################################################

using Oscar

"""
    canonical_factor_key(f) -> String

Return a hashable, order-independent, unit-scaled key for an irreducible
polynomial `f`, so two irreducible factors coming out of independent
`factor()` calls (potentially differing by a nonzero field-element unit,
and with no guaranteed enumeration order) compare equal iff they are
associates.

Normalization: divide by the coefficient of the lexicographically-first
monomial (in a fixed, deterministic term order), so the leading
coefficient of the normalized polynomial is always 1. This is well
defined for any irreducible over a field, independent of which unit
multiple factor() happened to emit.
"""
function canonical_factor_key(f)
    R = parent(f)
    F = base_ring(R)
    # Deterministic term order: sort exponent vectors lexicographically.
    exps = collect(AbstractAlgebra.exponent_vectors(f))
    cfs  = collect(coefficients(f))
    order = sortperm(exps)  # lexicographic on Vector{Int} is Julia's default
    lead_c = cfs[order[1]]
    inv_lead = inv(lead_c)
    # Build normalized (monic-by-convention) term list as a canonical string.
    io = IOBuffer()
    for idx in order
        c = cfs[idx] * inv_lead
        print(io, string(c), ":", string(exps[idx]), ";")
    end
    return String(take!(io))
end

"""
    factor_multiset(f) -> Dict{String,Int}

Factor `f` and return a map: canonical_factor_key(irreducible factor) => exponent.
Keys are unit/order independent so two factorizations of associate
polynomials produce identical dictionaries.
"""
function factor_multiset(f)
    fac = factor(f)
    d = Dict{String,Int}()
    for (p, e) in fac
        key = canonical_factor_key(p)
        d[key] = get(d, key, 0) + e
    end
    return d, fac
end

"""
    squarefree_multiplicity_diagnostic(gA, gB; label="")

Core diagnostic. Prints a full report and returns a NamedTuple with the
boolean verdicts so calling code can assert on them.
"""
function squarefree_multiplicity_diagnostic(gA, gB; label::AbstractString="")
    println("="^70)
    println("SQUAREFREE / MULTIPLICITY DIAGNOSTIC", isempty(label) ? "" : "  [$label]")
    println("="^70)

    t0 = time()
    setA, facA = factor_multiset(gA)
    setB, facB = factor_multiset(gB)
    t_elapsed = time() - t0

    keysA = Set(keys(setA))
    keysB = Set(keys(setB))

    only_in_A = setdiff(keysA, keysB)
    only_in_B = setdiff(keysB, keysA)
    shared    = intersect(keysA, keysB)

    same_support = isempty(only_in_A) && isempty(only_in_B)

    println("  factor() elapsed (both sides) = ", round(t_elapsed, digits=4), "s")
    println("  PATH A (Groebner eliminant): ", length(keysA), " distinct irreducible factor(s)")
    println("  PATH B (resultant chain)   : ", length(keysB), " distinct irreducible factor(s)")
    println()

    if !isempty(only_in_A)
        println("  ** factors present in A but NOT in B (", length(only_in_A), "): **")
        for k in only_in_A
            println("       exponent in A = ", setA[k])
        end
    end
    if !isempty(only_in_B)
        println("  ** factors present in B but NOT in A (", length(only_in_B), "): **")
        for k in only_in_B
            println("       exponent in B = ", setB[k])
        end
    end

    println()
    println("  --- shared irreducible factors: exponent comparison ---")
    println("  ", rpad("factor total_degree", 22), rpad("exp in A", 10), rpad("exp in B", 10), "ratio (B/A)")
    all_exponents_match_1_in_A = true
    ratios = Float64[]
    for k in sort(collect(shared); by = kk -> setA[kk])
        eA = setA[k]
        eB = setB[k]
        # recover degree for display by re-parsing one term isn't cheap;
        # instead just report exponents, which is what matters here.
        push!(ratios, eB / eA)
        if eA != 1
            all_exponents_match_1_in_A = false
        end
        println("  ", rpad("(see key)", 22), rpad(eA, 10), rpad(eB, 10), round(eB/eA, digits=3))
    end

    # Q1: multiplicity-adjustable recovery.
    # gA is recoverable from gB by adjusting ONLY exponents iff they share
    # exactly the same set of irreducible factors (no factor appears in
    # one and not the other), regardless of what those exponents are.
    q1_multiplicity_adjustable = same_support

    # Q2: strict squarefree-part relationship.
    # gA == squarefree_part(gB) iff (Q1 holds) AND every exponent in A is 1.
    q2_is_squarefree_part_of_B = same_support && all_exponents_match_1_in_A

    println()
    println("  --- verdicts ---")
    println("  Q1 (same irreducible-factor SET; multiplicities may differ freely): ",
            q1_multiplicity_adjustable ? "TRUE  -- gA IS recoverable from gB by re-exponentiating factors" :
                                          "FALSE -- gA has/lacks factors that gB lacks/has; no exponent adjustment can fix this")
    println("  Q2 (gA is exactly the squarefree part of gB, i.e. all A-exponents == 1): ",
            q2_is_squarefree_part_of_B ? "TRUE" : "FALSE")

    if q1_multiplicity_adjustable && !q2_is_squarefree_part_of_B
        println("  => gA is a *non-trivial reweighting* of gB's factors (not simply squarefree-part(gB)).")
        println("     Exponent map (A -> B): ", Dict(k => (setA[k], setB[k]) for k in shared))
    end

    println("="^70)

    return (
        same_support = same_support,
        q1_multiplicity_adjustable = q1_multiplicity_adjustable,
        q2_is_squarefree_part_of_B = q2_is_squarefree_part_of_B,
        exponents_A = setA,
        exponents_B = setB,
        only_in_A = only_in_A,
        only_in_B = only_in_B,
    )
end

################################################################################
# Convenience wrapper matching the bench script's own naming: call this
# right after PATH A / PATH B are both computed inside
# part_i_eliminate_vs_resultant_bench.jl (gA = eliminate() generator,
# gB = final chained resultant, e.g. Res_{w2}).
################################################################################

function run_diag_on_bench_result(bench_result; label::AbstractString="")
    # Adjust field names below if the bench script's return struct differs;
    # written against the (gA, gB) naming used in this file's docstring.
    return squarefree_multiplicity_diagnostic(bench_result.gA, bench_result.gB; label=label)
end

################################################################################
# STAGE TRACE: localize exactly where multiplicity inflation is introduced.
#
#   Res1 = resultant(h_s, curve1, w1)          -- eliminate w1 only
#   Res2 = resultant(Res1, curve2, w2)          -- eliminate w2, chained from Res1
#   gA   = Groebner eliminate() generator       -- eliminates both at once
#
# We factor all three, key every irreducible factor by canonical_factor_key
# (so "F1"/"F2" mean the same associate class across all three objects, not
# just whatever order factor() happens to emit), and print one row per
# factor showing its exponent at each stage. This answers, directly from
# data:
#   - is F2 present in Res1 already, and at what multiplicity?
#   - does the exponent change Res1 -> Res2 (inflation during 2nd resultant)?
#   - does it change Res2 -> Groebner (i.e. does Res2 already match Groebner,
#     meaning nothing is wrong after all)?
# No claim is made about WHY beyond what the numbers show.
################################################################################

"""
    factor_stage_trace(Res1, Res2, gA; label="")

Factor `Res1`, `Res2`, and `gA` (Groebner eliminant), key their irreducible
factors canonically, and print a table of exponent-per-stage for every
factor that appears in ANY of the three, plus explicit notes on:
  - whether each factor is present/absent at each stage
  - the exponent delta Res1->Res2 and Res2->gA per factor

Returns a NamedTuple with the raw per-stage Dict{key,exponent} maps and a
Vector of per-factor row NamedTuples, so downstream code can assert on
specific deltas instead of re-parsing printed output.
"""
function factor_stage_trace(Res1, Res2, gA; label::AbstractString="")
    println("="^70)
    println("FACTOR STAGE TRACE", isempty(label) ? "" : "  [$label]")
    println("  Res1 = resultant(h_s, curve1, w1)")
    println("  Res2 = resultant(Res1, curve2, w2)")
    println("  gA   = Groebner eliminate() generator")
    println("="^70)

    t0 = time()
    set1, fac1 = factor_multiset(Res1)
    t1 = time()
    set2, fac2 = factor_multiset(Res2)
    t2 = time()
    setA, facA = factor_multiset(gA)
    t3 = time()

    println("  factor(Res1) elapsed = ", round(t1 - t0, digits=4), "s  -> ", length(set1), " distinct factor(s)")
    println("  factor(Res2) elapsed = ", round(t2 - t1, digits=4), "s  -> ", length(set2), " distinct factor(s)")
    println("  factor(gA)   elapsed = ", round(t3 - t2, digits=4), "s  -> ", length(setA), " distinct factor(s)")
    println()

    all_keys = union(Set(keys(set1)), Set(keys(set2)), Set(keys(setA)))

    # Order factors for display by their (Res2 exponent, then gA exponent,
    # then Res1 exponent) descending, purely so the "big/interesting"
    # factors surface first. This is a display choice only; it carries no
    # mathematical meaning.
    ordered_keys = sort(collect(all_keys);
        by = k -> (get(set2, k, 0), get(setA, k, 0), get(set1, k, 0)),
        rev = true)

    # Assign short display labels F1, F2, F3, ... in this same order so the
    # printed table matches the "F1 / F2" language used in conversation.
    label_of = Dict(k => "F$(i)" for (i, k) in enumerate(ordered_keys))

    println("  ", rpad("factor", 8), rpad("Res1", 8), rpad("Res2", 8), rpad("Groebner", 10),
            rpad("Δ(1->2)", 10), "Δ(2->A)")
    rows = NamedTuple[]
    for k in ordered_keys
        e1 = get(set1, k, 0)
        e2 = get(set2, k, 0)
        eA = get(setA, k, 0)
        d12 = e2 - e1
        d2A = eA - e2
        flags = String[]
        e1 == 0 && push!(flags, "ABSENT in Res1")
        e2 == 0 && push!(flags, "ABSENT in Res2")
        eA == 0 && push!(flags, "ABSENT in Groebner")
        println("  ", rpad(label_of[k], 8), rpad(e1, 8), rpad(e2, 8), rpad(eA, 10),
                rpad(d12, 10), d2A, isempty(flags) ? "" : "   ** " * join(flags, ", ") * " **")
        push!(rows, (
            label = label_of[k],
            key = k,
            exp_Res1 = e1,
            exp_Res2 = e2,
            exp_Groebner = eA,
            delta_1_to_2 = d12,
            delta_2_to_A = d2A,
        ))
    end

    println()
    println("  --- localization ---")
    for r in rows
        if r.exp_Groebner == 0
            continue  # not part of the final answer; skip localization commentary
        end
        if r.delta_1_to_2 == 0 && r.delta_2_to_A == 0
            println("  ", r.label, ": exponent CONSTANT across all three stages (", r.exp_Res1, ") -- no inflation for this factor.")
        elseif r.delta_1_to_2 != 0 && r.delta_2_to_A == 0
            println("  ", r.label, ": inflation occurs ENTIRELY during the FIRST resultant (Res1) -- ",
                    "already at exponent ", r.exp_Res1, " by Res1, unchanged through Res2 and matches Groebner-vs-Res2 gap of 0.")
        elseif r.delta_1_to_2 == 0 && r.delta_2_to_A != 0
            verb = r.delta_2_to_A > 0 ? "inflation" : "deflation"
            println("  ", r.label, ": Res1 and Res2 AGREE (exponent ", r.exp_Res1,
                    ") -- all ", verb, " relative to Groebner is a Res2-vs-Groebner gap, not introduced by either resultant step relative to each other.")
        elseif sign(r.delta_1_to_2) == sign(r.delta_2_to_A) && r.delta_1_to_2 != 0
            # Same-sign deltas: the two steps genuinely compound rather than
            # cancel, so "accumulates" is the right word here.
            verb = r.delta_1_to_2 > 0 ? "inflation ACCUMULATES" : "deflation ACCUMULATES"
            println("  ", r.label, ": exponent CHANGES at both steps (Res1=", r.exp_Res1,
                    " -> Res2=", r.exp_Res2, " -> Groebner=", r.exp_Groebner,
                    ") -- ", verb, " across both resultant steps.")
        else
            # Opposite-sign deltas: the two steps move the exponent in
            # different directions. If they land back where they started
            # (net == 0) this is a round trip, not accumulation -- e.g.
            # inflated by the second resultant, then fully cancelled by
            # Groebner. Report the net change explicitly rather than
            # calling this "accumulation," which would be backwards.
            net = r.exp_Groebner - r.exp_Res1
            if net == 0
                println("  ", r.label, ": exponent CHANGES at both steps but NETS TO ZERO (Res1=", r.exp_Res1,
                        " -> Res2=", r.exp_Res2, " -> Groebner=", r.exp_Groebner,
                        ") -- Res2 inflates/deflates this factor and Groebner exactly cancels it back out; ",
                        "no net inflation relative to Res1, so Res1 alone already reflects the true multiplicity.")
            else
                dir = net > 0 ? "net INFLATION" : "net DEFLATION"
                println("  ", r.label, ": exponent CHANGES at both steps in OPPOSING directions (Res1=", r.exp_Res1,
                        " -> Res2=", r.exp_Res2, " -> Groebner=", r.exp_Groebner,
                        ") -- partial cancellation, with a ", dir, " of ", abs(net), " surviving overall.")
            end
        end
    end

    println("="^70)

    return (
        exponents_Res1 = set1,
        exponents_Res2 = set2,
        exponents_Groebner = setA,
        labels = label_of,
        rows = rows,
    )
end

################################################################################
# PART H2: INFLATION-VS-DIVISION DIAGNOSTIC (investigation only).
#
# Question: is the exponent inflation seen by factor_stage_trace (Res1 ->
# Res2 -> Groebner) universal across every benchmark target, or an
# accident of one degree-8 factor in one target? And when a factor
# inflates (exp(Res2) > exp(Groebner)), does DIVIDING Res2 by the excess
# power of that factor exactly reproduce the Groebner eliminant (up to
# ideal equality / a unit)?
#
# This does NOT change the elimination algorithm. It only factors the
# three already-computed objects (Res1, Res2, gA), matches factors
# exactly as factor_stage_trace already does, and -- for every factor
# whose exponent drops going from Res2 to Groebner -- performs an exact
# polynomial division and checks whether the quotient reproduces gA.
################################################################################

"""
    inflating_factor_division_diagnostic(Res1, Res2, gA; label="")

Automated per-benchmark diagnostic. Steps:

  1. Factor Res1, Res2, gA (timed).
  2. Match irreducible factors exactly via `canonical_factor_key`
     (same matching used by `factor_stage_trace`).
  3. Print one table row per matched factor: degree, term count, and
     exponent at each stage, plus deltas/ratio.
  4. Identify "inflating factors": exp(Res2) > exp(Groebner).
  5. For each inflating factor F, compute
         Q = Res2 / F^(exp(Res2) - exp(Groebner))
     via exact polynomial division, then check `ideal(Q) == ideal(gA)`
     and whether `Q == unit * gA` for some nonzero field-element unit.
  6. Print total timing of factor(Res2) + division + verification, for
     comparison against the Groebner elimination time already recorded
     by the caller.
  7. Print a concise per-target summary block.

Returns a NamedTuple with the raw per-factor rows and per-inflating-
factor verification results, so calling code can aggregate across all
eight benchmarks without re-parsing printed output.
"""
function inflating_factor_division_diagnostic(Res1, Res2, gA; label::AbstractString="")
    println("="^70)
    println("INFLATION-VS-DIVISION DIAGNOSTIC", isempty(label) ? "" : "  [$label]")
    println("  Res1 = resultant(h_s, curve1, w1)")
    println("  Res2 = resultant(Res1, curve2, w2)")
    println("  gA   = Groebner eliminate() generator")
    println("="^70)

    # ---- 1. Factor all three (timed individually; Res2's own timing is
    #         also reported separately below for the "replacement
    #         algorithm" cost comparison in step 6). ----
    t0 = time()
    set1, fac1 = factor_multiset(Res1)
    t1 = time()
    set2, fac2 = factor_multiset(Res2)
    t_factor_res2 = time() - t1
    t2 = time()
    setA, facA = factor_multiset(gA)
    t3 = time()

    println("  factor(Res1) elapsed = ", round(t1 - t0, digits=4), "s  -> ", length(set1), " distinct factor(s)")
    println("  factor(Res2) elapsed = ", round(t_factor_res2, digits=4), "s  -> ", length(set2), " distinct factor(s)")
    println("  factor(gA)   elapsed = ", round(t3 - t2, digits=4), "s  -> ", length(setA), " distinct factor(s)")
    println()

    # Build key -> actual polynomial object maps (needed for division,
    # unlike factor_stage_trace which only needs the exponent dicts).
    poly_of_1 = Dict{String,Any}(canonical_factor_key(p) => p for (p, _e) in fac1)
    poly_of_2 = Dict{String,Any}(canonical_factor_key(p) => p for (p, _e) in fac2)
    poly_of_A = Dict{String,Any}(canonical_factor_key(p) => p for (p, _e) in facA)

    # ---- 2. Match factors exactly as factor_stage_trace does. ----
    all_keys = union(Set(keys(set1)), Set(keys(set2)), Set(keys(setA)))
    ordered_keys = sort(collect(all_keys);
        by = k -> (get(set2, k, 0), get(setA, k, 0), get(set1, k, 0)),
        rev = true)
    label_of = Dict(k => "F$(i)" for (i, k) in enumerate(ordered_keys))

    # ---- 3. Print the requested table. ----
    println("  --- per-factor table ---")
    println("  ", rpad("factor", 6), rpad("degree", 8), rpad("terms", 8),
            rpad("exp(Res1)", 11), rpad("exp(Res2)", 11), rpad("exp(gA)", 9),
            rpad("d12", 6), rpad("d2A", 6), "ratio12")
    rows = NamedTuple[]
    for k in ordered_keys
        # Prefer the Res2 representative for degree/term-count display
        # (that's the object the division step will actually use); fall
        # back to Res1's or gA's representative if absent from Res2.
        rep = get(poly_of_2, k, get(poly_of_1, k, get(poly_of_A, k, nothing)))
        deg = rep === nothing ? -1 : total_degree(rep)
        nterms = rep === nothing ? -1 : length(terms(rep))

        e1 = get(set1, k, 0)
        e2 = get(set2, k, 0)
        eA = get(setA, k, 0)
        d12 = e2 - e1
        d2A = eA - e2
        ratio12 = e1 == 0 ? NaN : e2 / e1

        println("  ", rpad(label_of[k], 6), rpad(deg, 8), rpad(nterms, 8),
                rpad(e1, 11), rpad(e2, 11), rpad(eA, 9),
                rpad(d12, 6), rpad(d2A, 6),
                isnan(ratio12) ? "n/a" : round(ratio12, digits=3))

        push!(rows, (
            label = label_of[k],
            key = k,
            degree = deg,
            terms = nterms,
            exp_Res1 = e1,
            exp_Res2 = e2,
            exp_Groebner = eA,
            delta12 = d12,
            delta2G = d2A,
            ratio12 = ratio12,
        ))
    end
    println()

    # ---- 4. Identify inflating factors: exp(Res2) > exp(Groebner). ----
    inflating = filter(r -> r.exp_Res2 > r.exp_Groebner, rows)
    println("  --- inflating factors (exp(Res2) > exp(Groebner)): ", length(inflating), " found ---")
    for r in inflating
        println("    ", r.label, ": exp(Res2)=", r.exp_Res2, "  exp(Groebner)=", r.exp_Groebner,
                "  excess=", r.exp_Res2 - r.exp_Groebner)
    end
    println()

    # ---- 5. For each inflating factor: exact division + verification. ----
    verif_results = NamedTuple[]
    t_division_total = 0.0
    t_verification_total = 0.0

    R_gA = parent(gA)
    ideal_gA = nothing
    try
        ideal_gA = ideal(R_gA, [gA])
    catch e
        println("  ** could not build ideal(gA) for verification -- ", sprint(showerror, e), " **")
    end

    for r in inflating
        println("  --- dividing out inflating factor ", r.label, " (excess exponent ",
                r.exp_Res2 - r.exp_Groebner, ") ---")
        F = get(poly_of_2, r.key, nothing)
        if F === nothing
            println("    ** could not recover polynomial object for ", r.label, " from factor(Res2) -- skipping **")
            continue
        end

        excess = r.exp_Res2 - r.exp_Groebner
        t0d = time()
        Fpow = F^excess
        Q = nothing
        divides_exactly = false
        try
            q, rem = divrem(Res2, Fpow)
            if iszero(rem)
                divides_exactly = true
                Q = q
            else
                # Fall back to Oscar's divides() for a definitive exact
                # test in case divrem's remainder convention differs.
                ok, q2 = divides(Res2, Fpow)
                if ok
                    divides_exactly = true
                    Q = q2
                end
            end
        catch e
            println("    ** exact division raised an error -- ", sprint(showerror, e), " **")
        end
        t_div = time() - t0d
        t_division_total += t_div

        if !divides_exactly || Q === nothing
            println("    exact division Res2 / F^", excess, " did NOT divide evenly -- ",
                    "F^", excess, " is not actually a factor of Res2 at this exponent (inconsistent with factor()'s own exponent; reporting as-is).")
            push!(verif_results, (
                label = r.label, key = r.key, excess = excess,
                division_exact = false, ideal_match = false, unit_match = false, unit_ratio = nothing,
                t_division = t_div, t_verification = 0.0,
            ))
            println()
            continue
        end

        println("    division elapsed = ", round(t_div, digits=4), "s  -> Q: total_degree=",
                (iszero(Q) ? -1 : total_degree(Q)), "  terms=", length(terms(Q)))

        # ---- verify ideal(Q) == ideal(gA) ----
        t0v = time()
        ideal_match = false
        if ideal_gA !== nothing && parent(Q) === R_gA
            try
                ideal_match = (ideal(R_gA, [Q]) == ideal_gA)
            catch e
                println("    ** ideal(Q)==ideal(gA) check raised an error -- ", sprint(showerror, e), " **")
            end
        elseif parent(Q) !== R_gA
            println("    NOTE: parent(Q) != parent(gA) -- skipping ideal-equality check (reported as false).")
        end

        # ---- verify Q == unit * gA ----
        unit_match = false
        unit_ratio = nothing
        if parent(Q) === R_gA && !iszero(Q) && !iszero(gA) && length(terms(Q)) == length(terms(gA))
            lcQ = leading_coefficient(Q)
            lcA = leading_coefficient(gA)
            if !iszero(lcA)
                candidate_ratio = lcQ // lcA
                if Q == candidate_ratio * gA
                    unit_match = true
                    unit_ratio = candidate_ratio
                end
            end
        end
        t_verif = time() - t0v
        t_verification_total += t_verif

        if ideal_match
            println("    *** ideal(Q) == ideal(gA):  YES -- exact division reproduces the Groebner elimination ideal ***")
        else
            println("    ideal(Q) == ideal(gA):  NO")
        end
        if unit_match
            println("    *** Q == unit * gA:  YES  (unit = $unit_ratio) -- division reproduces gA up to a scalar ***")
        else
            println("    Q == unit * gA:  NO")
        end
        println("    verification elapsed = ", round(t_verif, digits=4), "s")

        push!(verif_results, (
            label = r.label, key = r.key, excess = excess,
            division_exact = true, ideal_match = ideal_match, unit_match = unit_match,
            unit_ratio = unit_ratio, t_division = t_div, t_verification = t_verif,
        ))
        println()
    end

    # ---- 6. Timing summary (factor(Res2) + division + verification). ----
    t_total_pipeline = t_factor_res2 + t_division_total + t_verification_total
    println("  --- timing: factor(Res2) + division + verification ---")
    println("    factor(Res2)  = ", round(t_factor_res2, digits=4), "s")
    println("    division      = ", round(t_division_total, digits=4), "s  (summed over ", length(inflating), " inflating factor(s))")
    println("    verification  = ", round(t_verification_total, digits=4), "s")
    println("    TOTAL         = ", round(t_total_pipeline, digits=4), "s")
    println("    (compare against the Groebner eliminate() time recorded separately by the caller " *
            "to see whether factor+divide is consistently cheaper -- a possible replacement for " *
            "Gröbner elimination after the resultant chain.)")
    println()

    # ---- 7. Concise summary block. ----
    any_reproduces = any(v -> v.division_exact && (v.ideal_match || v.unit_match), verif_results)
    println("  --- summary ---")
    println("  target ", label)
    println("  inflating factors: ", length(inflating))
    for (i, r) in enumerate(inflating)
        v = i <= length(verif_results) ? verif_results[i] : nothing
        println("    factor ", i, ":")
        println("      degree: ", r.degree)
        println("      Res1 exponent: ", r.exp_Res1)
        println("      Res2 exponent: ", r.exp_Res2)
        println("      Groebner exponent: ", r.exp_Groebner)
        println("      removed exponent: ", r.exp_Res2 - r.exp_Groebner)
        if v === nothing
            println("      division reproduces Groebner: NO (verification not run)")
        else
            reproduces = v.division_exact && (v.ideal_match || v.unit_match)
            println("      division reproduces Groebner: ", reproduces ? "YES" : "NO")
        end
    end
    if isempty(inflating)
        println("    (no inflating factors for this target -- exp(Res2) <= exp(Groebner) everywhere)")
    end
    println("="^70)

    return (
        rows = rows,
        inflating = inflating,
        verification = verif_results,
        t_factor_res2 = t_factor_res2,
        t_division_total = t_division_total,
        t_verification_total = t_verification_total,
        t_total_pipeline = t_total_pipeline,
        any_reproduces = any_reproduces,
    )
end

################################################################################
# PRODUCTION MULTIPLICITY-CORRECTION PIPELINE (Gröbner-free).
#
# Turns the diagnostic finding above (Res2 = Groebner-eliminant * F^excess,
# for some repeated factor F already visible after Res1) into an actual
# corrective step that does NOT need the Groebner eliminant to run at all.
#
# Self-consistency signal used instead of "compare against gA": a genuine
# spurious-multiplicity factor F is one that
#   (a) is already present in Res1 (it's an intrinsic factor of the
#       eliminant geometry, not an artifact manufactured by the second
#       resultant), AND
#   (b) has its exponent in Res2 grow relative to its exponent in Res1
#       specifically because Res2 = resultant(Res1, curve2, w2) resultants
#       Res1 against ANOTHER copy of the same branch locus -- i.e. gcd
#       structure between Res1 and curve2's discriminant/leading
#       coefficient predicts which factor(s) get re-counted.
#
# Concretely: for every irreducible factor F of Res2 whose exponent
# e2 = exp_Res2(F) exceeds e1 = exp_Res1(F) (its exponent already present
# after the FIRST resultant), the excess exponent (e2 - e1) is the
# candidate spurious multiplicity introduced purely by the second
# resultant step -- no Groebner computation needed to conjecture this,
# since it only compares Res1 and Res2 against each other.
#
# This mirrors the empirically-confirmed 3->9 case (excess = 9-3 = 6,
# which happened to reduce to the correct exponent-3 factor once divided
# down -- but nothing here hard-codes 3 or 9; it is read off e1/e2).
################################################################################

"""
    correct_multiplicity(Res1, Res2; label="")

Gröbner-free multiplicity correction. Factors `Res1` and `Res2` (this is
the only factorization work needed -- no Groebner basis), matches factors
via `canonical_factor_key`, and for every factor whose Res2-exponent
exceeds its Res1-exponent, divides Res2 down by the excess power.

Returns a NamedTuple:
  corrected          -- the corrected polynomial (Res2 with all detected
                         excess multiplicity divided out)
  applied_factors    -- Vector of (key, F, excess) actually divided out
  t_factor           -- time spent factoring Res1 and Res2
  t_correct          -- time spent dividing out excess multiplicity
  all_divisions_exact -- whether every candidate excess power divided
                         Res2 evenly (a self-consistency check: if this
                         is false, factor()'s own exponents were
                         inconsistent with exact division, and the
                         "corrected" result should not be trusted blindly)

This function never calls eliminate()/groebner_basis() -- it is safe to
run unconditionally in default (CHECK_GROEBNER=false) benchmark mode.
"""
function correct_multiplicity(Res1, Res2; label::AbstractString="")
    println("-"^70)
    println("MULTIPLICITY CORRECTION (Gröbner-free)", isempty(label) ? "" : "  [$label]")
    println("-"^70)

    t0 = time()
    set1, fac1 = factor_multiset(Res1)
    set2, fac2 = factor_multiset(Res2)
    t_factor = time() - t0
    println("  factor(Res1)+factor(Res2) elapsed = ", round(t_factor, digits=4), "s  -> ",
            length(set1), " / ", length(set2), " distinct factor(s)")

    poly_of_2 = Dict{String,Any}(canonical_factor_key(p) => p for (p, _e) in fac2)

    # Candidates: factors present in Res2 whose exponent exceeds their
    # exponent in Res1 (0 if absent from Res1 entirely -- a factor that
    # appears ONLY in Res2 with no Res1 presence is, by this criterion,
    # entirely an artifact of the second resultant step and is corrected
    # down to exponent 0, i.e. divided out completely).
    all_keys2 = collect(keys(set2))
    candidates = NamedTuple[]
    for k in all_keys2
        e1 = get(set1, k, 0)
        e2 = set2[k]
        if e2 > e1
            push!(candidates, (key = k, excess = e2 - e1, exp_Res1 = e1, exp_Res2 = e2))
        end
    end

    println("  candidate inflated factor(s) (exp(Res2) > exp(Res1)): ", length(candidates))
    for c in candidates
        rep = poly_of_2[c.key]
        println("    degree=", total_degree(rep), "  terms=", length(terms(rep)),
                "  exp(Res1)=", c.exp_Res1, "  exp(Res2)=", c.exp_Res2, "  excess=", c.excess)
    end

    t0 = time()
    corrected = Res2
    applied = NamedTuple[]
    all_exact = true
    for c in candidates
        Fp = poly_of_2[c.key]
        Fpow = Fp^c.excess
        divides_exactly = false
        q = nothing
        try
            qtmp, rem = divrem(corrected, Fpow)
            if iszero(rem)
                divides_exactly = true
                q = qtmp
            else
                ok, q2 = divides(corrected, Fpow)
                if ok
                    divides_exactly = true
                    q = q2
                end
            end
        catch e
            println("    ** division by F^", c.excess, " raised an error -- ", sprint(showerror, e), " **")
        end
        if divides_exactly
            corrected = q
            push!(applied, (key = c.key, excess = c.excess))
            println("  divided out excess exponent ", c.excess, " of one factor -> ",
                    "degree=", (iszero(corrected) ? -1 : total_degree(corrected)),
                    "  terms=", length(terms(corrected)))
        else
            all_exact = false
            println("  ** excess exponent ", c.excess, " did NOT divide evenly -- ",
                    "skipping this candidate, correction may be incomplete **")
        end
    end
    t_correct = time() - t0

    if isempty(candidates)
        println("  (no candidate inflated factors -- Res2 already matches Res1's ",
                "multiplicities on every shared factor; corrected == Res2 unchanged)")
    end

    println("  correction elapsed = ", round(t_correct, digits=4), "s")
    println("  final corrected result: degree=", (iszero(corrected) ? -1 : total_degree(corrected)),
            "  terms=", length(terms(corrected)))
    println("-"^70)

    return (
        corrected = corrected,
        applied_factors = applied,
        t_factor = t_factor,
        t_correct = t_correct,
        all_divisions_exact = all_exact,
    )
end

"""
    verify_correction(corrected, gA; check_groebner=CHECK_GROEBNER, label="")

Verify the corrected polynomial. Three tiers, cheapest first:
  1. If `check_groebner` is true and `gA` is available: exact polynomial
     equality against the Groebner eliminant, up to a unit, plus an ideal-
     equality fallback if the unit check fails. This is the authoritative
     check but requires the expensive Groebner computation to have run.
  2. If `check_groebner` is false (default): `gA` is not computed at all,
     so instead report factor/multiplicity self-consistency for
     `corrected` (squarefree-content sanity: does `corrected` still carry
     any UNCORRECTED repeated factor beyond what a generic eliminant of
     this shape should have? This is necessarily weaker evidence than
     exact Groebner comparison, and is reported as such.)

Returns a NamedTuple with the verification verdict and which tier ran.
"""
function verify_correction(corrected, gA; check_groebner::Bool=CHECK_GROEBNER, label::AbstractString="")
    if check_groebner && gA !== nothing
        t0 = time()
        ideal_match = false
        unit_match = false
        unit_ratio = nothing
        try
            if parent(corrected) === parent(gA)
                if !iszero(corrected) && !iszero(gA) && length(terms(corrected)) == length(terms(gA))
                    lcC = leading_coefficient(corrected)
                    lcA = leading_coefficient(gA)
                    if !iszero(lcA)
                        candidate_ratio = lcC // lcA
                        if corrected == candidate_ratio * gA
                            unit_match = true
                            unit_ratio = candidate_ratio
                        end
                    end
                end
                if !unit_match
                    ideal_match = (ideal(parent(gA), [corrected]) == ideal(parent(gA), [gA]))
                end
            end
        catch e
            println("  ** verify_correction: Groebner comparison raised an error -- ",
                    sprint(showerror, e), " **")
        end
        t_verify = time() - t0
        matches = unit_match || ideal_match
        println("  verify_correction [$label]: against Groebner -- unit_match=", unit_match,
                "  ideal_match=", ideal_match, "  (", round(t_verify, digits=4), "s)")
        return (matches = matches, tier = :groebner, unit_match = unit_match,
                ideal_match = ideal_match, unit_ratio = unit_ratio, t_verify = t_verify)
    else
        # Tier 2: factor/multiplicity self-consistency only, no Groebner.
        # A "clean" correction should be squarefree in every factor that
        # was corrected (excess divided down to exactly the Res1
        # multiplicity), and dividing again by any corrected factor
        # should fail (no further excess remaining).
        t0 = time()
        set_corrected, _ = factor_multiset(corrected)
        t_verify = time() - t0
        println("  verify_correction [$label]: Groebner check skipped (CHECK_GROEBNER=false) -- ",
                "reporting factor/multiplicity self-consistency only (", round(t_verify, digits=4), "s): ",
                length(set_corrected), " distinct factor(s) in corrected result.")
        return (matches = missing, tier = :self_consistency, unit_match = missing,
                ideal_match = missing, unit_ratio = nothing, t_verify = t_verify)
    end
end

################################################################################
# IDENTIFY THE INFLATING FACTOR (F_infl).
#
# We know (empirically, from factor_stage_trace) which canonical-key
# factor inflates in multiplicity. This section does NOT theorize about
# WHY -- it computes concrete candidate polynomials from the actual
# system (h_s, curve1, curve2, and the resultant chain's own
# intermediate objects) and GCDs each one against F_infl to see which
# candidates it divides, equals, or shares structure with.
#
# Candidates tested, all derived directly from your system:
#   1. disc_w(curve1), disc_w(curve2)      -- discriminant of each curve
#                                              equation in its own w-var
#   2. lc_w(h_s) in w1, in w2               -- leading coefficient of h_s
#                                              as a polynomial in each w
#   3. lc_w(curve1), lc_w(curve2)           -- leading coeff of each curve
#                                              eqn in its own w (should be
#                                              a unit/1 since monic, but
#                                              checked rather than assumed)
#   4. Jacobian determinant of (h_s, curve1, curve2) w.r.t. (w1, w2)
#      -- the 2x2 minor ∂(h_s,curve1)/∂(w1,w2) etc; branch/ramification
#         locus candidate
#   5. Res1 itself (as a whole, and its own leading coeff in w2 before
#      the second resultant consumes it)
#   6. gcd(F_infl, F_infl at Res1-stage vs Res2-stage) is not meaningful
#      (different ring), so instead we gcd F_infl against each candidate
#      IN F_infl's own ring, after mapping candidates into that ring.
#
# All comparisons are done via gcd() in a common ring: whichever ring
# F_infl's representative element lives in. Candidates computed in a
# smaller ring (e.g. only in a1,a2) are mapped in via the same
# coefficient-copy technique used elsewhere in elim2.jl
# (MPolyBuildCtx / push_term!), not via a ring homomorphism object,
# to avoid requiring the two rings to be related by an explicit map.
################################################################################

"""
    map_into_ring(f, target_ring, var_index_map)

Copy `f` term-by-term into `target_ring`, placing each generator of
`parent(f)` into the generator of `target_ring` given by
`var_index_map[i]` (1-indexed). Any generator of `parent(f)` not
present in `var_index_map` must not actually appear in `f` (checked).
Used to lift small candidate polynomials (e.g. a discriminant computed
in just [a1,a2]) into the larger ring F_infl's representative lives in.
"""
function map_into_ring(f, target_ring, var_index_map::Vector{Int})
    B = MPolyBuildCtx(target_ring)
    n_target = nvars(target_ring)
    for (c, exps) in zip(coefficients(f), AbstractAlgebra.exponent_vectors(f))
        new_exps = zeros(Int, n_target)
        for (i, e) in enumerate(exps)
            if e != 0
                new_exps[var_index_map[i]] = e
            end
        end
        push_term!(B, c, new_exps)
    end
    return finish(B)
end

"""
    identify_inflating_factor(F_infl_poly, candidates::Dict{String,<:Any}; label="")

`F_infl_poly` is the actual irreducible polynomial object (not just its
canonical key) for the factor you want identified -- pull this directly
out of a `factor(Res2)` or `factor(gA)` call's factor list (matched by
canonical_factor_key against the row you care about from
factor_stage_trace).

`candidates` maps a human-readable name to a polynomial ALREADY LIVING
IN (or already mapped into) F_infl_poly's ring -- use map_into_ring
above first if a candidate was computed in a different/smaller ring.

For each candidate, prints:
  - gcd(F_infl_poly, candidate) and its degree
  - whether F_infl_poly divides the candidate
  - whether the candidate divides F_infl_poly
  - whether they are equal up to unit scalar
"""
function identify_inflating_factor(F_infl_poly, candidates::Dict{String,<:Any}; label::AbstractString="")
    println("="^70)
    println("IDENTIFY INFLATING FACTOR", isempty(label) ? "" : "  [$label]")
    println("  F_infl: total_degree=", total_degree(F_infl_poly), "  terms=", length(terms(F_infl_poly)))
    println("="^70)

    R = parent(F_infl_poly)

    for (name, cand) in candidates
        if is_zero(cand)
            println("  [", rpad(name, 28), "]  candidate is the zero polynomial -- skipping")
            continue
        end
        if parent(cand) !== R
            println("  [", rpad(name, 28), "]  ** SKIPPED: candidate not in F_infl's ring; call map_into_ring first **")
            continue
        end

        g = gcd(F_infl_poly, cand)
        g_deg = is_zero(g) ? -1 : total_degree(g)
        # Multivariate polynomials over a field have no generic rem()/%
        # in this Oscar/AbstractAlgebra stack -- exact divisibility here
        # is tested via divides(), which returns (flag, quotient) and is
        # the correct primitive for FqMPolyRingElem.
        f_divides_cand, _ = divides(cand, F_infl_poly)          # F_infl | candidate
        cand_divides_f, _ = divides(F_infl_poly, cand)          # candidate | F_infl
        equal_up_to_unit = false
        if total_degree(cand) == total_degree(F_infl_poly) && f_divides_cand && cand_divides_f
            equal_up_to_unit = true
        end

        tag = equal_up_to_unit ? "  <<< EQUAL UP TO UNIT SCALAR" :
              f_divides_cand   ? "  <<< F_infl DIVIDES this candidate" :
              cand_divides_f   ? "  <<< candidate DIVIDES F_infl" :
              (g_deg > 0)      ? "  <<< nontrivial common factor (gcd degree $g_deg)" :
                                  ""

        println("  [", rpad(name, 28), "]  cand deg=", rpad(total_degree(cand), 6),
                "  gcd deg=", rpad(g_deg, 6), tag)
    end

    println("="^70)
end

################################################################################
# Convenience builders for the standard candidate set, given the raw
# system polynomials. Call these to build the Dict passed into
# identify_inflating_factor above. Each returns a polynomial in ITS OWN
# natural ring; you must map_into_ring(...) each one into F_infl's ring
# before use (the exact var_index_map depends on your ring's generator
# order, which only you know at the call site -- left explicit rather
# than guessed).
################################################################################

"""
    discriminant_of_curve(curve, w)

disc_w(curve) for curve = w^2 - c(t), i.e. a monic quadratic in w:
disc = b^2 - 4ac with a=1, b=0, c=-c(t)  =>  disc = 4*c(t).
Returned up to the classical sign/scale convention (4*c(t)); if you need
the textbook-exact discriminant sign, adjust by a unit -- units don't
affect any gcd/divisibility test above.
"""
function discriminant_of_curve(curve, w)
    # curve = w^2 - c(t)  =>  c(t) = w^2 - curve, extracted by
    # setting w -> 0 after negating: c(t) = -(curve with w^2 term removed... )
    # Simpler and robust: disc of a*w^2+b*w+c is b^2-4ac. Extract a,b,c as
    # coefficients of w^2, w^1, w^0 directly via coeff().
    a = coeff(curve, [w], [2])
    b = coeff(curve, [w], [1])
    c = coeff(curve, [w], [0])
    return b^2 - 4*a*c
end

"""
    leading_coeff_in(f, w)

Leading coefficient of `f` viewed as a univariate polynomial in `w`
(coefficient of the highest power of `w` appearing).
"""
function leading_coeff_in(f, w)
    d = degree(f, w)
    return coeff(f, [w], [d])
end

"""
    jacobian_2x2(f1, f2, v1, v2)

2x2 Jacobian determinant  |∂f1/∂v1  ∂f1/∂v2; ∂f2/∂v1  ∂f2/∂v2|
-- a standard branch-locus / ramification candidate for a system being
eliminated in exactly two variables (v1,v2).
"""
function jacobian_2x2(f1, f2, v1, v2)
    return derivative(f1, v1) * derivative(f2, v2) - derivative(f1, v2) * derivative(f2, v1)
end

println("identify_inflating_factor + helper builders (discriminant_of_curve, leading_coeff_in, ",
        "jacobian_2x2, map_into_ring) loaded. Actual call site is inside _run_bench, right after ",
        "factor_stage_trace, where curve1/curve2/step1/gA are in scope.")


#!/usr/bin/env julia
################################################################################
# part_i_eliminate_vs_resultant_bench.jl
#
# Controlled experiment: does eliminate(I_small, [w1,w2]) inside
# process_sample_1_coeff / process_sample_2_coeff (elim2.jl, Part I) cause
# the symbolic blow-up, or does it already exist before that call?
#
# HOW TO RUN
# -----------------------------------------------------------------------
# This does NOT modify elim2.jl. It is meant to be run in the SAME Julia
# session as elim2.jl, after res1 (and, for the sample-2 path, res2) exist
# -- i.e. after elim2.jl's setup block (through line ~106) has executed --
# but it never calls process_sample_1_coeff/process_sample_2_coeff itself,
# so it does not depend on Part I/J/K having run. Load it with:
#
#     julia> include("elim2.jl")   # let it run, or Ctrl-C after res1/res2
#                                    # exist if you don't want the rest of
#                                    # the script to execute yet
#     julia> include("part_i_eliminate_vs_resultant_bench.jl")
#     julia> bench_report_1 = run_bench_sample1("U0", res1.u_RS_coeffs[1])
#
# or, more simply, just include this file AFTER elim2.jl's full run --
# res1/res2/tower_to_ring will all still be in Main.
#
# WHAT IT DOES
# -----------------------------------------------------------------------
# For a chosen raw tower coefficient (e.g. res1.u_RS_coeffs[1]), builds
# the identical 5-variable sandbox process_sample_1_coeff builds, then
# runs TWO elimination paths side by side from the SAME h_s/curve1/curve2:
#
#   Path A (original):  eliminate(ideal(R_small,[h_s,curve1,curve2]),[w1,w2])
#   Path B (candidate):  step1 = resultant(h_s,   curve1, w1)
#                         step2 = resultant(step1, curve2, w2)
#
# Both paths are timed and measured (elapsed time, total_degree, term
# count, degree in every remaining variable) at every intermediate
# object, matching the requested log format:
#
#     h_s
#     Res_{w1}
#     Res_{w2}
#     Groebner eliminant
#
# Then it verifies equivalence: are Path A's output and Path B's output
# (a) identical, (b) equal up to a unit scalar, (c) generators of the
# same ideal (mutual ideal-membership check), and checks whether either
# one factors nontrivially.
#
# Nothing here alters process_sample_1_coeff/process_sample_2_coeff --
# both are left completely untouched in elim2.jl. This is read-only
# instrumentation bolted on next to them.
################################################################################

using Oscar

################################################################################
# CHECK_GROEBNER: master switch for the expensive Gröbner verification path.
#
# Default benchmark mode is resultant elimination -> factor analysis ->
# multiplicity correction -> (cheap) verification, with NO Gröbner basis
# computation at all. Gröbner's eliminate() is kept only as an opt-in
# debugging oracle: set CHECK_GROEBNER = true (or ENV["ELIM2_CHECK_GROEBNER"]
# = "true") to additionally run PATH A and compare the corrected resultant
# result against it exactly, the way the original diagnostic experiment did.
#
# This is a `const ... = get(ENV, ...)` read once at load time, matching the
# existing RUN_FULL_RESULTANT / ELIM2_PARTF_DIRECT_CROSSCHECK convention
# elsewhere in this file, so it can be toggled per-run without editing code:
#
#     ELIM2_CHECK_GROEBNER=true julia elim2.jl
################################################################################

const CHECK_GROEBNER = get(ENV, "ELIM2_CHECK_GROEBNER", "false") == "true"

println("CHECK_GROEBNER = ", CHECK_GROEBNER,
        CHECK_GROEBNER ? "  (Gröbner eliminate() WILL run, as a debugging oracle)" :
                          "  (Gröbner eliminate() will be SKIPPED -- default production/benchmark mode)")

# ------------------------------------------------------------------------
# Small measurement helper -- prints elapsed time, total_degree, term
# count, and per-variable degree for one polynomial object, tagged with
# a label matching the requested log format.
# ------------------------------------------------------------------------
function _measure(label::String, g, elapsed::Float64; vars_of_interest=nothing)
    R = parent(g)
    varnames = vars_of_interest === nothing ? symbols(R) : vars_of_interest
    degs_str = join(["deg($(vn))=$(degree(g, gen(R, i)))"
                      for (i, vn) in enumerate(symbols(R))], ", ")
    td = iszero(g) ? -1 : total_degree(g)
    nt = length(terms(g))
    println("    $label")
    println("      elapsed        = ", round(elapsed, digits=4), " s")
    println("      total_degree   = ", td)
    println("      terms          = ", nt)
    println("      per-var degree = ", degs_str)
    flush(stdout)
    return (label=label, elapsed=elapsed, total_degree=td, terms=nt)
end

# ------------------------------------------------------------------------
# Core A/B routine, parameterized so it works for both sample 1 (a1,a2)
# and sample 2 (b1,b2) variable naming, mirroring
# process_sample_1_coeff / process_sample_2_coeff exactly.
# ------------------------------------------------------------------------
function _run_bench(raw_coeff, target_name::String, t_names::Vector{String}, w_names::Vector{String})
    println("="^70)
    println("BENCH: target=$target_name  t_vars=$t_names  w_vars=$w_names")
    println("="^70)

    # Human-readable "which sample" tag used throughout this bench's
    # labels/diagnostics, derived from t_names rather than hardcoded, so
    # this same function correctly self-labels for both sample 1 (a-vars)
    # and sample 2 (b-vars) benchmarks.
    sample_tag = (t_names == ["a1", "a2"]) ? "a-vars" :
                 (t_names == ["b1", "b2"]) ? "b-vars" : join(t_names, ",")
    bench_label = "$target_name ($sample_tag)"

    # 1. Build the identical 5-variable sandbox process_sample_*_coeff builds.
    R_small, gens_small = polynomial_ring(F, vcat(w_names, t_names, [target_name]))
    w1, w2, t1, t2, T = gens_small

    t0 = time()
    t_gens = [t1, t2]
    w_gens = [w1, w2]
    num_s, den_s = tower_to_ring(raw_coeff, t_gens, w_gens)
    t_tower = time() - t0
    println("  [setup] tower_to_ring: elapsed=", round(t_tower, digits=4), "s  ",
            "num terms=", length(terms(num_s)), "  den terms=", length(terms(den_s)),
            "  num total_degree=", (iszero(num_s) ? -1 : total_degree(num_s)),
            "  den total_degree=", (iszero(den_s) ? -1 : total_degree(den_s)))
    flush(stdout)

    t0 = time()
    h_s = T * den_s - num_s
    t_hs = time() - t0

    curve1 = w1^2 - (t1^5 + t1 + 2)
    curve2 = w2^2 - (t2^5 + t2 + 2)

    println()
    println("  --- shared input ---")
    _measure("h_s", h_s, t_hs)
    _measure("curve1", curve1, 0.0)
    _measure("curve2", curve2, 0.0)
    println()

    results = Dict{String,Any}()

    # ----------------------------------------------------------------
    # PATH A (debugging oracle only): eliminate(I_small, [w1, w2])
    #
    # Gated behind CHECK_GROEBNER. Default benchmark mode never touches
    # this -- gA/gb_gens are left as `nothing`/empty and every downstream
    # comparison against Groebner is skipped or downgraded to a
    # self-consistency check (see verify_correction).
    # ----------------------------------------------------------------
    gA = nothing
    gb_gens = Any[]
    t_gb = 0.0
    if CHECK_GROEBNER
        println("  --- PATH A: eliminate(ideal(R_small,[h_s,curve1,curve2]), [w1,w2]) ---")
        I_small = ideal(R_small, [h_s, curve1, curve2])
        t0 = time()
        eliminated_ideal = eliminate(I_small, [w1, w2])
        t_gb = time() - t0
        gb_gens = gens(eliminated_ideal)
        println("    Groebner eliminate() returned ", length(gb_gens), " generator(s).")
        if length(gb_gens) == 0
            error("PATH A: eliminate() returned an EMPTY generator set -- elimination ideal " *
                  "is trivial or zero. Something upstream (h_s/curve1/curve2) is degenerate. " *
                  "Stopping rather than continuing blindly.")
        end
        gA = gb_gens[1]
        if length(gb_gens) > 1
            println("    NOTE: eliminate() returned >1 generator; using generator [1] for " *
                    "comparison, but this itself is worth flagging -- the eliminant may not " *
                    "be principal, unlike the resultant path's single output.")
            for (i, g) in enumerate(gb_gens)
                _measure("Groebner eliminant [gen $i]", g, (i == 1 ? t_gb : 0.0))
            end
        else
            _measure("Groebner eliminant", gA, t_gb)
        end
        println()
    else
        println("  --- PATH A: SKIPPED (CHECK_GROEBNER=false; Groebner eliminate() ",
                "is a debugging oracle only in default benchmark mode) ---")
        println()
    end
    results["A_gens"] = gb_gens
    results["A_time"] = t_gb
    # ----------------------------------------------------------------
    # PATH B (candidate): sequential univariate resultants
    #   step1 = Res_{w1}(h_s, curve1)   -- eliminates w1
    #   step2 = Res_{w2}(step1, curve2) -- eliminates w2
    # ----------------------------------------------------------------
    println("  --- PATH B: sequential resultant(h_s, curve1, w1) then resultant(_, curve2, w2) ---")

    # Eliminate w1 (first variable)
    t0 = time()
    step1 = resultant(h_s, curve1, 1)
    t_r1 = time() - t0
    _measure("Res_{w1}", step1, t_r1)

    # Eliminate w2 (second variable)
    t0 = time()
    step2 = resultant(step1, curve2, 2)
    t_r2 = time() - t0
    _measure("Res_{w2}", step2, t_r2)



    results["B_result"] = step2
    results["B_time"] = t_r1 + t_r2
    println()

    gB = step2

    # ----------------------------------------------------------------
    # NORMAL WORKFLOW (always runs, no Groebner needed):
    #   resultant elimination -> factor analysis -> multiplicity
    #   correction -> verification.
    # ----------------------------------------------------------------
    corr = correct_multiplicity(step1, step2; label=bench_label)
    verif = verify_correction(corr.corrected, gA; check_groebner=CHECK_GROEBNER, label=bench_label)

    results["h_s_terms"] = length(terms(h_s))
    results["h_s_degree"] = iszero(h_s) ? -1 : total_degree(h_s)
    results["gA"] = gA
    results["gB"] = gB
    results["corrected"] = corr.corrected
    results["t_resultant"] = t_r1 + t_r2
    results["t_factor"] = corr.t_factor
    results["t_correct"] = corr.t_correct
    results["t_groebner"] = t_gb
    results["correction_matches_groebner"] = verif.matches
    results["applied_factors"] = corr.applied_factors
    results["all_divisions_exact"] = corr.all_divisions_exact

    # ----------------------------------------------------------------
    # EQUIVALENCE CHECKS / DIAGNOSTIC-ONLY COMPARISONS AGAINST GROEBNER.
    #
    # Everything below this point requires gA (the Groebner eliminant)
    # and is therefore gated behind CHECK_GROEBNER -- it is retained
    # verbatim as the existing diagnostic/debugging-oracle comparison,
    # not part of the default production workflow above.
    # ----------------------------------------------------------------
    if CHECK_GROEBNER
        println("  --- equivalence checks: PATH A (Groebner) vs PATH B (resultant) ---")

        # A and B may live in R_small still (both were built from R_small's
        # h_s/curve1/curve2), so they should already share a parent. Confirm.
        if parent(gA) !== parent(gB)
            println("    NOTE: parent rings differ (", parent(gA), " vs ", parent(gB),
                    "); this itself is diagnostic -- eliminate() may return elements of a " *
                    "different (sub)ring object than resultant() does, even over the same " *
                    "variable set. Attempting a direct term-level comparison anyway only if " *
                    "generator sets match; otherwise this is reported as UNVERIFIED, not equal.")
        end

        same_parent = parent(gA) === parent(gB)

        # (a) identical?
        identical = same_parent && (gA == gB)
        println("    (a) identical (==)?              ", identical)

        # (b) equal up to a unit (nonzero scalar in F, since R_small's base
        #     ring is a field GF(p))?
        equal_up_to_unit = false
        unit_ratio = nothing
        if same_parent && !identical
            # Over a field-coefficient polynomial ring, "equal up to unit" means
            # gA == c*gB for some nonzero c in F. Compare via leading-term ratio,
            # then verify across ALL terms (not just leading), since a matching
            # leading-term ratio alone doesn't prove global proportionality.
            if !iszero(gA) && !iszero(gB) && length(terms(gA)) == length(terms(gB))
                lcA = leading_coefficient(gA)
                lcB = leading_coefficient(gB)
                if !iszero(lcB)
                    candidate_ratio = lcA // lcB
                    equal_up_to_unit = (gA == candidate_ratio * gB)
                    if equal_up_to_unit
                        unit_ratio = candidate_ratio
                    end
                end
            end
        end
        println("    (b) equal up to unit scalar?     ", equal_up_to_unit,
                unit_ratio === nothing ? "" : "  (ratio gA = $unit_ratio * gB)")

        # (c) same elimination ideal? Mutual ideal-membership check: gA in
        #     ideal(gB) and gB in ideal(gA) within the SAME ring. This is the
        #     correct test when they might differ by more than a unit (e.g. a
        #     genuinely different-but-associate generator, or A having several
        #     generators).
        same_ideal = false
        if same_parent
            try
                ideal_A = length(gb_gens) > 1 ? ideal(R_small, gb_gens) : ideal(R_small, [gA])
                ideal_B = ideal(R_small, [gB])
                same_ideal = (ideal_A == ideal_B)
            catch e
                println("    (c) ideal equality check raised an error -- reporting as UNVERIFIED: ", e)
            end
        end
        println("    (c) same elimination ideal (ideal(A) == ideal(B))?  ", same_ideal)

        # (d) does one factor while the other doesn't?
        println("    (d) factorization check:")
        for (nm, g) in (("PATH A gen[1]", gA), ("PATH B (gB)", gB))
            t0 = time()
            fac = factor(g)
            t_fac = time() - t0
            nfac = length(fac)
            println("        $nm: ", nfac, " irreducible factor(s)  (factor() elapsed=",
                    round(t_fac, digits=4), "s)")
            for (f, e) in fac
                println("            factor: total_degree=", total_degree(f),
                        "  terms=", length(terms(f)), "  exponent=", e)
            end
        end
        println()

        # ----------------------------------------------------------------
        # SIZE / COST COMPARISON
        # ----------------------------------------------------------------
        println("  --- size/cost comparison ---")
        println("    PATH A (Groebner eliminate): time=", round(t_gb, digits=4),
                "s  total_degree=", total_degree(gA), "  terms=", length(terms(gA)))
        println("    PATH B (resultant chain)   : time=", round(t_r1 + t_r2, digits=4),
                "s  total_degree=", total_degree(gB), "  terms=", length(terms(gB)))
        ratio_terms = length(terms(gA)) / max(1, length(terms(gB)))
        ratio_time  = t_gb / max(1e-9, (t_r1 + t_r2))
        println("    term-count ratio  (A/B) = ", round(ratio_terms, digits=2))
        println("    time ratio        (A/B) = ", round(ratio_time, digits=2))
        println()

        results["identical"] = identical
        results["equal_up_to_unit"] = equal_up_to_unit
        results["same_ideal"] = same_ideal
        squarefree_multiplicity_diagnostic(gA, gB; label=bench_label)
        trace = factor_stage_trace(step1, step2, gA; label=bench_label)

        # ------------------------------------------------------------------
        # PART H2: universal inflation-vs-division diagnostic.
        #
        # Investigates whether the exponent-inflation pattern seen at the
        # factor_stage_trace stage (Res1 -> Res2 -> Groebner) is universal
        # across all benchmark targets, and whether exact polynomial
        # division by the inflating factor's excess power recovers the
        # Groebner eliminant (up to ideal equality / unit). Purely
        # observational -- does not alter step1/step2/gA or any upstream
        # algorithm.
        # ------------------------------------------------------------------
        infl_report = inflating_factor_division_diagnostic(step1, step2, gA; label=bench_label)

        # ------------------------------------------------------------------
        # Pick out the inflating factor and actually run identify_inflating_factor
        # on it, rather than just printing a reminder of how to call it.
        #
        # "Inflating" here means the row with the largest |delta| relative to
        # Res1 that survives to the Groebner stage (exp_Groebner != 0) --
        # this is deliberately the same notion of "worst offender" that
        # factor_stage_trace's own localization commentary already reports
        # per-row, just reduced to a single pick so we have one concrete
        # F_infl_poly to hand to identify_inflating_factor.
        # ------------------------------------------------------------------
        surviving_rows = filter(r -> r.exp_Groebner != 0, trace.rows)
        if isempty(surviving_rows)
            println("  (no surviving factor with nonzero Groebner exponent -- skipping identify_inflating_factor)")
        else
            worst = argmax(r -> abs(r.delta_1_to_2) + abs(r.delta_2_to_A), surviving_rows)

            # facA is the Groebner-stage factor list (key => (poly, exponent)
            # info lives in `facA` from factor_multiset(gA) inside factor_stage_trace;
            # re-derive it here directly from gA so we have the actual polynomial
            # object, not just its canonical key string.
            facA_local = factor(gA)
            F_infl_poly = nothing
            for (f, _e) in facA_local
                if canonical_factor_key(f) == worst.key
                    F_infl_poly = f
                    break
                end
            end

            if F_infl_poly === nothing
                println("  (could not recover the polynomial object for factor ", worst.label,
                        " from factor(gA) -- skipping identify_inflating_factor)")
            else
                # Build the standard candidate set directly from the system
                # polynomials in scope here (h_s, curve1, curve2, step1), all
                # already living in R_small = parent(gA), so no map_into_ring
                # lift is needed for these.
                candidates = Dict{String,Any}(
                    "disc_w(curve1)"      => discriminant_of_curve(curve1, w1),
                    "disc_w(curve2)"      => discriminant_of_curve(curve2, w2),
                    "lc_w1(h_s)"          => leading_coeff_in(h_s, w1),
                    "lc_w2(h_s)"          => leading_coeff_in(h_s, w2),
                    "jacobian(h_s,curve1; t1,w1)" => jacobian_2x2(h_s, curve1, t1, w1),
                    "jacobian(h_s,curve2; t2,w2)" => jacobian_2x2(h_s, curve2, t2, w2),
                    "step1 (Res_w1)"      => step1,
                )
                identify_inflating_factor(F_infl_poly, candidates; label="$bench_label, factor $(worst.label)")
            end
        end

        results["infl_report"] = infl_report
    else
        results["identical"] = missing
        results["equal_up_to_unit"] = missing
        results["same_ideal"] = missing
        results["infl_report"] = nothing
    end

    return results
end

# ------------------------------------------------------------------------
# Public entry points mirroring process_sample_1_coeff / process_sample_2_coeff
# ------------------------------------------------------------------------
run_bench_sample1(target_name::String, raw_coeff) =
    _run_bench(raw_coeff, target_name, ["a1", "a2"], ["wa1", "wa2"])

run_bench_sample2(target_name::String, raw_coeff) =
    _run_bench(raw_coeff, target_name, ["b1", "b2"], ["wb1", "wb2"])

println("part_i_eliminate_vs_resultant_bench.jl loaded.")
println("Run e.g.:  run_bench_sample1(\"U0\", res1.u_RS_coeffs[1])")
println("      or:  run_bench_sample2(\"U0\", res2.u_RS_coeffs[1])")


# ------------------------------------------------------------------------
# AUTOMATED DRIVER: run all eight benchmark cases (U0, U1, V0, V1) x
# (sample 1 / sample 2) so the inflation-vs-division question is answered
# universally rather than by inspecting one target by hand.
#
#   U0 <- u_RS_coeffs[1] (x^0 coefficient of u_RS)
#   U1 <- u_RS_coeffs[2] (x^1 coefficient of u_RS)
#   V0 <- v_RS_coeffs[1] (x^0 coefficient of v_RS)
#   V1 <- v_RS_coeffs[2] (x^1 coefficient of v_RS)
#
# Each case is run through _run_bench (both PATH A/B, the existing
# squarefree/factor_stage_trace diagnostics, and the new
# inflating_factor_division_diagnostic). A single crashing case does not
# abort the sweep -- it is caught, reported, and the loop continues, so a
# hang/error on (say) V1 doesn't destroy the results already collected
# for U0/U1/V0.
# ------------------------------------------------------------------------

bench_cases = [
    ("U0", 1, res1.u_RS_coeffs[1], res2.u_RS_coeffs[1]),
    ("U1", 2, res1.u_RS_coeffs[2], res2.u_RS_coeffs[2]),
    ("V0", 1, res1.v_RS_coeffs[1], res2.v_RS_coeffs[1]),
    ("V1", 2, res1.v_RS_coeffs[2], res2.v_RS_coeffs[2]),
]

all_bench_results = Dict{String,Any}()

for (target_name, _idx, raw1, raw2) in bench_cases
    for (sample_num, run_fn, raw_coeff) in ((1, run_bench_sample1, raw1), (2, run_bench_sample2, raw2))
        case_key = "$(target_name)_sample$(sample_num)"
        println()
        println("#"^70)
        println("# RUNNING BENCH CASE: ", case_key)
        println("#"^70)
        try
            all_bench_results[case_key] = run_fn(target_name, raw_coeff)
        catch e
            println("  ** BENCH CASE ", case_key, " FAILED -- ", sprint(showerror, e), " **")
            println("  ** continuing with remaining benchmark cases **")
            all_bench_results[case_key] = Dict{String,Any}("error" => sprint(showerror, e))
        end
    end
end

# ------------------------------------------------------------------------
# CROSS-BENCHMARK SUMMARY: is inflation universal? Does division
# consistently reproduce the Groebner eliminant? Is factor+divide
# consistently cheaper than Groebner elimination?
# ------------------------------------------------------------------------
println()
println("="^70)
println("CROSS-BENCHMARK SUMMARY (all ", length(bench_cases) * 2, " cases)")
println("="^70)

n_with_inflation = 0
n_division_always_reproduces = 0
n_cases_run = 0

for (target_name, _idx, _r1, _r2) in bench_cases
    for sample_num in (1, 2)
        case_key = "$(target_name)_sample$(sample_num)"
        res = get(all_bench_results, case_key, nothing)
        if res === nothing || (res isa Dict && haskey(res, "error"))
            println("  ", case_key, ": ERROR -- ", res === nothing ? "no result" : res["error"])
            continue
        end
        global n_cases_run += 1
        infl = res["infl_report"]
        if infl === nothing
            println("  ", rpad(case_key, 14),
                    " inflating=n/a  division_reproduces_all=n/a",
                    " (infl_report unavailable -- CHECK_GROEBNER=false for this run)")
            continue
        end
        n_infl = length(infl.inflating)
        n_infl > 0 && (global n_with_inflation += 1)
        all_reproduce = n_infl > 0 && all(v -> v.division_exact && (v.ideal_match || v.unit_match), infl.verification)
        n_infl > 0 && all_reproduce && (global n_division_always_reproduces += 1)
        println("  ", rpad(case_key, 14),
                " inflating=", rpad(n_infl, 3),
                " division_reproduces_all=", rpad(n_infl == 0 ? "n/a" : (all_reproduce ? "YES" : "NO"), 5),
                " factor(Res2)+div+verif=", round(infl.t_total_pipeline, digits=3), "s",
                "  vs  Groebner=", round(get(res, "A_time", NaN), digits=3), "s")
    end
end

println()
println("  cases with at least one inflating factor: ", n_with_inflation, " / ", n_cases_run)
println("  cases where division reproduces Groebner for ALL inflating factors: ",
        n_division_always_reproduces, " / ", n_with_inflation, " (of the inflating cases)")
if n_with_inflation > 0 && n_division_always_reproduces == n_with_inflation
    println("  => VERDICT: inflation is universal across observed cases, and exact division ",
            "consistently reproduces the Groebner eliminant -- factor(Res2)+division may be ",
            "a viable replacement for Groebner elimination after the resultant chain, PENDING ",
            "a timing comparison per the table above.")
elseif n_with_inflation > 0
    println("  => VERDICT: inflation occurs in some cases, but division does NOT consistently ",
            "reproduce the Groebner eliminant -- NOT a safe universal replacement without further ",
            "investigation of the cases where it fails.")
else
    println("  => VERDICT: no inflating factors observed in any case (exp(Res2) <= exp(Groebner) ",
            "everywhere) -- the original degree-8 U0 finding may have been accidental/case-specific.")
end
println("="^70)







println()
println("===========================================================")
println("PART K: The Final Collision (Eliminating the Middlemen)")
println("===========================================================")

# 1. Build the shared, final universe (Notice: NO 'w' variables allowed!)
R_final, (a1_f, a2_f, b1_f, b2_f, U0_f, U1_f, V0_f, V1_f) = polynomial_ring(F, ["a1", "a2", "b1", "b2", "U0", "U1", "V0", "V1"])

final_equations = Any[]

println("  Mapping Sample 1 into the final universe...")


################################################################################
# PART K FIX: manual term-by-term remap, replacing the generic evaluate()
# call that dies on the very first invocation.
#
# Root-cause hypothesis (see chat): clean_sample_1[i] lives in R_small =
# F[wa1,wa2,a1,a2,Ti] (5 vars), already eliminated of wa1,wa2 by
# process_sample_1_coeff's own eliminate() call -- so as a polynomial it
# should contain NO wa1/wa2 monomials at all (every exponent on those two
# generators is 0). evaluate(f, images) across two UNRELATED polynomial
# ring objects (R_small -> R_final) is not a cheap "rename the
# generators" operation in general -- Oscar's generic evaluate()
# reconstructs the whole expression through ring-homomorphism arithmetic,
# which can be far more expensive than the term count of the input or
# output would suggest, especially across rings that were never declared
# to have any relationship to each other.
#
# Fix: read clean_sample_1[i] apart into (coefficient, exponent_vector)
# pairs directly (using coefficients()/exponent_vectors(), both
# documented O(1)-per-term iterators, no ring-homomorphism machinery
# involved), and push each term straight into an MPolyBuildCtx for
# R_final. This is linear in the number of terms of the input polynomial
# and never constructs anything in an intermediate/unrelated ring.
#
# gen_map: for each generator index of R_small (in R_small's own
# declared order), an Int index into R_final's generator list (1-based),
# or `0` if that generator must be zero in the image (i.e. the wa1/wa2
# slots -- which we can also just assert are always-zero-exponent as a
# cheap sanity check while we're at it, rather than silently trusting
# that eliminate() actually removed them).
################################################################################

function remap_to_final(f, final_gens::Vector, gen_map::Vector{Int})
    # Using MPolyBuildCtx + push_term! + finish, the documented,
    # empirically-linear-in-term-count pattern for rebuilding a polynomial
    # term-by-term into a different ring (see Oscar/AbstractAlgebra docs'
    # swap_vars example -- confirmed by their own benchmark to scale
    # linearly, e.g. 0.0001s to 0.004s for a 40x growth in term count).
    # This avoids the likely O(n^2)-ish behavior of accumulating via
    # repeated `result += coeff*monomial` polynomial addition, which
    # re-normalizes/re-sorts the whole accumulator on every term, and it
    # avoids evaluate()'s generic cross-ring homomorphism machinery
    # entirely -- we go straight from (coefficient, exponent_vector) pairs
    # to push_term! calls in the TARGET ring, with no ring-homomorphism
    # evaluation step at all.
    R_out = parent(final_gens[1])
    n_out = length(final_gens)
    B = MPolyBuildCtx(R_out)

    for (c, exps) in zip(coefficients(f), AbstractAlgebra.exponent_vectors(f))
        new_exps = zeros(Int, n_out)
        for (k, e) in enumerate(exps)
            e == 0 && continue
            tgt = gen_map[k]
            if tgt == 0
                # Sanity check: a generator mapped to "must be zero" (the
                # eliminated w-slots) has a nonzero exponent here --
                # eliminate() did NOT fully remove this variable. Fail
                # loudly rather than silently drop real content.
                error("remap_to_final: generator index $k (mapped to zero) " *
                      "has nonzero exponent $e in a term of the input " *
                      "polynomial -- eliminate() did NOT fully remove this " *
                      "variable, zeroing it here would silently drop real " *
                      "content. Inspect the input polynomial before proceeding.")
            end
            new_exps[tgt] += e
        end
        push_term!(B, c, new_exps)
    end

    return finish(B)
end

################################################################################
# Usage, replacing the dying block at elim2.jl lines 2141-2154:
#
#   R_small (per process_sample_1_coeff) has generator order:
#     [wa1, wa2, a1, a2, T]     <- T is whatever target name was passed
#
#   R_final has generator order:
#     [a1_f, a2_f, b1_f, b2_f, U0_f, U1_f, V0_f, V1_f]
#
# So for sample 1 targeting U0 (target index 1 in the loop below):
#   gen_map = [0, 0, 1, 2, 5]     (wa1->0, wa2->0, a1->a1_f(idx1), a2->a2_f(idx2), T->U0_f(idx5))
#
# and similarly for U1 (T->U1_f, idx6), V0 (T->V0_f, idx7), V1 (T->V1_f, idx8).
#
# For sample 2 (R_small has [wb1,wb2,b1,b2,T]):
#   gen_map = [0, 0, 3, 4, <target_idx>]   (b1->b1_f(idx3), b2->b2_f(idx4))
################################################################################

println("Remapping sample 1 into the final universe (manual term-by-term)...")

final_gens = [a1_f, a2_f, b1_f, b2_f, U0_f, U1_f, V0_f, V1_f]

# sample 1: a-variables map to final indices 1,2; target T maps to final index 5,6,7,8 resp.
sample1_target_final_idx = [5, 6, 7, 8]   # U0, U1, V0, V1
for (i, tgt_idx) in enumerate(sample1_target_final_idx)
    gen_map = [0, 0, 1, 2, tgt_idx]
    t0 = time()
    g = remap_to_final(clean_sample_1[i], final_gens, gen_map)
    println("  clean_sample_1[$i] remapped in ", round(time()-t0, digits=3),
            "s: degree=", total_degree(g), " terms=", length(terms(g)))
    push!(final_equations, g)
end

println("Remapping sample 2 into the final universe (manual term-by-term)...")

# sample 2: b-variables map to final indices 3,4; target T maps to final index 5,6,7,8 resp.
sample2_target_final_idx = [5, 6, 7, 8]   # U0, U1, V0, V1
for (i, tgt_idx) in enumerate(sample2_target_final_idx)
    gen_map = [0, 0, 3, 4, tgt_idx]
    t0 = time()
    g = remap_to_final(clean_sample_2[i], final_gens, gen_map)
    println("  clean_sample_2[$i] remapped in ", round(time()-t0, digits=3),
            "s: degree=", total_degree(g), " terms=", length(terms(g)))
    push!(final_equations, g)
end


################################################################################
# PART K, take 3: direct resultant instead of eliminate() on an ideal.
#
# Both earlier attempts (ideal-based eliminate() per target variable, and
# ideal-based eliminate() on all four at once) OOM'd with zero diagnostic
# output -- we don't even know what degree/term count killed the process.
# Root cause hypothesis (see chat): eliminate(ideal(g1,g2), [T]) computes a
# full Groebner basis of <g1,g2> under an elimination ordering, which is
# far more general (and far more expensive) machinery than this problem
# needs. final_equations[i] and final_equations[i+4] are individual
# polynomials, each degree <=1 in T_i (T_i was introduced as
# "T_i * den - num", degree 1 in T_i by construction). Eliminating a
# SINGLE variable that appears at most linearly in TWO polynomials is
# exactly what resultant() computes directly, in one shot, no GB:
#
#   Res_{T_i}(g1, g2) vanishes iff g1, g2 have a common root in T_i
#
# For two polynomials each degree <=1 in T_i, resultant is (worst case) a
# single Sylvester-matrix determinant, not a GB search. This also sidesteps
# eliminate()'s internal elimination-ordering choice (see PART E -- that
# ordering is opaque and not tunable through eliminate()).
#
# Instrumentation: print degree/terms of each final_equations[i] BEFORE
# calling resultant (neither OOM'd attempt above ever did this), and write
# each result to disk immediately after, so a crash on (say) V1 doesn't
# destroy the U0/U1/V0 results that already finished.
################################################################################

################################################################################
# PART K setup: pick the target, build the 5-variable fiber-product ring,
# and extract each side's coefficients as polynomials in T. This is the
# part of the old "take 4" code that's still needed -- only the
# Sylvester-matrix-building and Leibniz-summand-enumeration that used to
# follow it has been replaced below.
################################################################################

const name  = "U0"
const i1    = 1
const i2    = 5
const Tvar  = U0_f

g1 = final_equations[i1]
g2 = final_equations[i2]

d1T = degree(g1, Tvar)
d2T = degree(g2, Tvar)
println("  --- $name ---")
println("    g1 (sample 1 side): total_degree=", total_degree(g1),
        "  terms=", length(terms(g1)), "  degree-in-$name=", d1T)
println("    g2 (sample 2 side): total_degree=", total_degree(g2),
        "  terms=", length(terms(g2)), "  degree-in-$name=", d2T)

if d1T == 0 || d2T == 0
    error("$name does not actually appear in one side; resultant " *
          "would be degenerate. Inspect final_equations construction.")
end

println("    building the fiber-product ring/generators for $name...")
flush(stdout)

# Same 5-variable fiber-product ring as before: only (a1,a2,b1,b2,T) --
# g1 only involves (a1,a2,T), g2 only involves (b1,b2,T).
Rfp, (a1_fp, a2_fp, b1_fp, b2_fp, T_fp) =
    polynomial_ring(F, ["a1", "a2", "b1", "b2", string(name)])
rfp_gens = [a1_fp, a2_fp, b1_fp, b2_fp, T_fp]

i2_local = i2 - length(clean_sample_1)
g1_fp = remap_to_final(clean_sample_1[i1], rfp_gens,
                        [0, 0, 1, 2, 5])   # wa1,wa2->0; a1->1; a2->2; T->5
g2_fp = remap_to_final(clean_sample_2[i2_local], rfp_gens,
                        [0, 0, 3, 4, 5])   # wb1,wb2->0; b1->3; b2->4; T->5

println("      g1 remapped into 5-var fiber-product ring: degree=",
        total_degree(g1_fp), " terms=", length(terms(g1_fp)),
        "  degree-in-T=", degree(g1_fp, T_fp))
println("      g2 remapped into 5-var fiber-product ring: degree=",
        total_degree(g2_fp), " terms=", length(terms(g2_fp)),
        "  degree-in-T=", degree(g2_fp, T_fp))

# Extract [c0, c1, ..., c_maxdeg] (each T-free) such that
# g == sum_k c_k * T^k, using coefficients()/exponent_vectors() so it
# never touches ring-homomorphism machinery.
function poly_coeffs_in(g, T, maxdeg)
    Rg = parent(g)
    gensR = gens(Rg)
    Tidx = findfirst(==(T), gensR)
    coeff_polys = [MPolyBuildCtx(Rg) for _ in 0:maxdeg]
    for (c, exps) in zip(coefficients(g), AbstractAlgebra.exponent_vectors(g))
        k = exps[Tidx]
        new_exps = copy(exps)
        new_exps[Tidx] = 0
        push_term!(coeff_polys[k+1], c, new_exps)
    end
    return [finish(ctx) for ctx in coeff_polys]
end

syl_c1 = poly_coeffs_in(g1_fp, T_fp, d1T)   # syl_c1[k+1] is coeff of T^k in g1_fp, k=0..d1T
syl_c2 = poly_coeffs_in(g2_fp, T_fp, d2T)   # syl_c2[k+1] is coeff of T^k in g2_fp, k=0..d2T







################################################################################
# part_k_diagnostic.jl
#
# Standalone structural diagnostic for the U0 quartic-in-T resultant problem
# (elim2.jl Part K, "redesigned" subresultant-PRS version).
#
# WHY THIS SCRIPT EXISTS
# -----------------------------------------------------------------------
# GPT's diagnosis of the PRS slowness: degree-in-T is only 4 on each side,
# so a subresultant PRS is nominally O(d1T*d2T) = O(16) pseudo-division
# steps -- cheap. The observed cost instead comes from the *coefficient
# ring* arithmetic: each of those 4+1 coefficients (elements of
# F[a1,a2,b1,b2], or its fraction field) is itself a large polynomial
# (elim2.jl's own PART H readout: 1445-term, degree-36 objects appear at
# this stage), and every pseudo-division step does full multivariate
# multiply/divide on objects of that size. The PRS algorithm is right;
# the coefficients feeding it are the bottleneck.
#
# GPT's ranked ideas, and what this script checks for each:
#   1. Do the quartics factor (e.g. as two quadratics, or have a
#      rational root / GF(p)-rational factor)?          -> Section A, B
#   2. Are the coefficients themselves reducible / do they share
#      common factors that could be pulled out before the PRS runs?
#                                                          -> Section C
#   3. Is the quartic secretly quadratic-in-T^2, reciprocal, or
#      palindromic (structural symmetry that would collapse degree)?
#                                                          -> Section D
#   4. How much does substituting explicit anchor values (dropping to
#      GF(p) coefficients) shrink term counts -- i.e. is the "1445
#      terms" figure inherent to the math, or an artifact of carrying
#      a1,a2,b1,b2 symbolically this late?                -> Section E
#
# This script does NOT re-run or interfere with the resultant(g1_T, g2_T)
# call in elim2.jl Part K -- it is read-only with respect to g1_T/g2_T
# and only inspects syl_c1/syl_c2 (the per-power-of-T coefficient slices
# built by poly_coeffs_in, already sitting in memory once elim2.jl reaches
# the "computing resultant via subresultant PRS" print). Run this in the
# SAME Julia session/REPL as elim2.jl, either:
#   (a) after Part K finishes (to sanity-check the result), or
#   (b) in a second REPL that has independently re-run elim2.jl only as
#       far as the syl_c1/syl_c2 construction (before the resultant()
#       call), if you want answers *while* the original resultant is
#       still crunching in the first REPL.
#
# It assumes elim2.jl's Part K setup has already run and the following
# names exist in Main: F, Rfp, T_fp, g1_fp, g2_fp, d1T, d2T, syl_c1,
# syl_c2, Rcoef, Kcoef, a1_c, a2_c, b1_c, b2_c, coef_gens,
# drop_T_to_coef_ring, poly_coeffs_in.
################################################################################

using Oscar

println("="^70)
println("PART K DIAGNOSTIC: quartic-in-T structure probe")
println("="^70)

@assert isdefined(Main, :syl_c1) && isdefined(Main, :syl_c2) """
    syl_c1/syl_c2 not found in Main. Run elim2.jl at least through the
    'computing resultant via subresultant PRS' print (i.e. through the
    poly_coeffs_in(g1_fp,...)/poly_coeffs_in(g2_fp,...) calls) before
    loading this diagnostic.
    """

# ------------------------------------------------------------------------
# Section A: per-coefficient size report (term counts / degrees), so we
# can see exactly which T^k slice(s) are driving the PRS cost.
# ------------------------------------------------------------------------
println("\n--- Section A: coefficient-of-T^k size report ---")
println("side 1 (g1_fp, degree-in-T=", d1T, "):")
for (k, c) in enumerate(syl_c1)
    kk = k - 1
    println("  [a1,a2,b1,b2]-coeff of T^$kk : total_degree=", total_degree(c),
            "  terms=", length(terms(c)))
end
println("side 2 (g2_fp, degree-in-T=", d2T, "):")
for (k, c) in enumerate(syl_c2)
    kk = k - 1
    println("  [a1,a2,b1,b2]-coeff of T^$kk : total_degree=", total_degree(c),
            "  terms=", length(terms(c)))
end

# ------------------------------------------------------------------------
# Section B: does g1_fp / g2_fp factor over its own ring, treated as a
# univariate-in-T polynomial with those large coefficients? Cheapest
# possible test first: leading/trailing coefficient GCD (a necessary
# condition for a nontrivial factorization T^4+...  = (T^2+AT+B)(T^2+CT+D)
# is that no single irreducible factor of the coefficient ring divides
# every T^k-coefficient in a way that's inconsistent with such a split;
# full factorization of a degree-4 univariate poly over a fraction field
# is what we actually want, so try factor() directly and time-box it).
# ------------------------------------------------------------------------
println("\n--- Section B: factorization of g1_T / g2_T over Kcoef(T) ---")

function try_factor_with_timeout(label, g, limit_secs)
    # Reuse elim2.jl's own run_with_timeout (~line 1403) rather than a
    # hand-rolled @async wrapper. NOTE the same caveat elim2.jl documents
    # for that helper: it uses Threads.@spawn, so a genuinely hung/
    # non-yielding Singular call inside factor() won't actually be
    # killed -- run_with_timeout will correctly report :timeout at the
    # wall-clock deadline and let the REST of this diagnostic proceed,
    # but the abandoned factor() call keeps running in the background
    # (same tradeoff elim2.jl already accepted for its own PART B sweep,
    # and the same reason elim2.jl's comments say a true kill needs an
    # OS-level `timeout N julia ...` wrapper around the whole process).
    if isdefined(Main, :run_with_timeout)
        val, status, elapsed = Main.run_with_timeout(() -> factor(g), limit_secs)
        if status != :ok
            println("  $label: factor() did not complete (status=$status, ",
                    round(elapsed, digits=1), "s elapsed) -- skipping. ",
                    "Background task may still be running; a fresh REPL ",
                    "is the only way to fully reclaim it.")
            return nothing
        end
        fac = val
    else
        println("  $label: run_with_timeout not found in Main (load elim2.jl ",
                "first) -- running factor() with NO timeout. This may hang ",
                "for a long time if the polynomial is large; interrupt ",
                "(Ctrl-C) if needed.")
        fac = factor(g)
    end
    n = length(fac)
    println("  $label: ", n, " irreducible factor(s):")
    for (f, e) in fac
        Tgen = gens(parent(f))[end]
        println("    degree-in-T=", degree(f, Tgen),
                " (exponent ", e, "), total_degree=", total_degree(f),
                " terms=", length(terms(f)))
    end
    return fac
end

if isdefined(Main, :g1_T) && isdefined(Main, :g2_T)
    fac1 = try_factor_with_timeout("g1_T", Main.g1_T, 60.0)
    fac2 = try_factor_with_timeout("g2_T", Main.g2_T, 60.0)
else
    println("  g1_T/g2_T not yet built in this session (Part K hasn't ",
            "reached that line) -- skipping live factorization test. ",
            "Rebuilding just enough to test factor() on g1_fp/g2_fp as ",
            "plain multivariate polys instead (factor(), not resultant()):")
    fac1 = try_factor_with_timeout("g1_fp", Main.g1_fp, 60.0)
    fac2 = try_factor_with_timeout("g2_fp", Main.g2_fp, 60.0)
end

# ------------------------------------------------------------------------
# Section C: do the T^k coefficients across k=0..4 share a common
# multivariate factor? If gcd(syl_c1...) is nontrivial, it can be pulled
# out of g1_fp entirely before the PRS ever runs, shrinking every pseudo-
# division step proportionally. Same check for side 2.
# ------------------------------------------------------------------------
println("\n--- Section C: common-factor (GCD) check across T^k coefficients ---")

function gcd_report(label, coeffs)
    nz = filter(!iszero, coeffs)
    if length(nz) < 2
        println("  $label: fewer than 2 nonzero coefficients, nothing to GCD.")
        return
    end
    g = nz[1]
    for c in nz[2:end]
        g = gcd(g, c)
    end
    if is_unit(g)
        println("  $label: gcd across all T^k coefficients is a unit -- ",
                "no common factor to pull out.")
    else
        println("  $label: NONTRIVIAL common factor found! degree=",
                total_degree(g), " terms=", length(terms(g)),
                " -- pulling this out before building g*_T could shrink ",
                "every coefficient the PRS touches.")
    end
end

gcd_report("side 1 (syl_c1)", syl_c1)
gcd_report("side 2 (syl_c2)", syl_c2)

# ------------------------------------------------------------------------
# Section D: structural symmetry checks on g1_fp / g2_fp as polynomials
# in T -- is it quadratic-in-T^2 (only even powers present), palindromic/
# reciprocal (c_k == c_{d-k} up to a unit), or otherwise reducible in a
# way that would let us solve two quadratics instead of one quartic?
# ------------------------------------------------------------------------
println("\n--- Section D: symmetry checks (even-power-only / palindromic) ---")

function symmetry_report(label, coeffs, d)
    # coeffs[k+1] = coefficient of T^k, k = 0..d
    odd_nonzero = any(!iszero(coeffs[k+1]) for k in 1:2:d)
    println("  $label: only even powers of T present? ", !odd_nonzero,
            odd_nonzero ? "" : "  --> reduces to a QUADRATIC in T^2, " *
            "halving the effective degree for root-finding / factoring.")

    if d >= 1
        is_palindromic = true
        for k in 0:d
            ck = coeffs[k+1]
            cdk = coeffs[d-k+1]
            # palindromic up to scalar: c_k == lambda * c_{d-k} for fixed lambda
            if iszero(ck) != iszero(cdk)
                is_palindromic = false
                break
            end
        end
        println("  $label: leading/trailing coefficient zero-pattern is ",
                is_palindromic ? "consistent with" : "NOT consistent with",
                " a palindromic (reciprocal) polynomial.")
    end
end

symmetry_report("side 1 (syl_c1)", syl_c1, d1T)
symmetry_report("side 2 (syl_c2)", syl_c2, d2T)

# ------------------------------------------------------------------------
# Section E: numeric substitution test. Plug in a handful of random
# GF(p)-rational values for (a1,a2,b1,b2) (respecting the curve
# constraints if F is exposed as such -- here we just use random field
# elements, which is fine for a *size* diagnostic even if not every
# substitution lands on the actual curve) and see how much the term
# count of g1_fp/g2_fp collapses. This tells us whether "1445 terms" is
# inherent to the degree-36 geometry, or mostly bookkeeping overhead from
# carrying 4 symbolic anchor variables through the tower this late.
# ------------------------------------------------------------------------
println("\n--- Section E: random specialization size test ---")

function specialize_and_report(label, g, gens_to_kill)
    # Uses the same evaluate(f, full_image_list) pattern already used
    # throughout elim2.jl (e.g. `remap(f) = evaluate(f, [...])` at line
    # 645 / 1208). g1_fp/g2_fp are only 5-variable, so this full-ring
    # evaluate() is cheap and safe here -- it's the large final-universe
    # objects elsewhere in elim2.jl where evaluate() was the problem
    # (the ring-remapping bug already fixed upstream via
    # MPolyBuildCtx/push_term!/finish, i.e. remap_to_final).
    Rg = parent(g)
    all_gens = gens(Rg)
    images = Vector{Any}(undef, length(all_gens))
    for (i, v) in enumerate(all_gens)
        if v in gens_to_kill
            images[i] = rand(F)
        else
            images[i] = v   # leave T (and any other free generator) symbolic
        end
    end
    g_spec = evaluate(g, images)
    Tpos = findfirst(v -> !(v in gens_to_kill), all_gens)
    println("  $label: before terms=", length(terms(g)),
            "  after random (a*,b*) specialization terms=",
            length(terms(g_spec)), "  degree-in-T unchanged=",
            degree(g_spec, all_gens[Tpos]))
end

specialize_and_report("g1_fp", g1_fp, [a1_fp, a2_fp])
specialize_and_report("g2_fp", g2_fp, [b1_fp, b2_fp])

println("\n" * "="^70)
println("PART K DIAGNOSTIC COMPLETE")
println("="^70)
println("""
Reading the results:
  Section A tells you WHICH T^k coefficient(s) are large -- if it's
    lopsided (e.g. only the T^4/T^0 coefficients are big and T^1..T^3
    are small), that's a strong hint the quartic is close to a binomial
    T^4 + c and worth testing for radical/Kummer structure directly.
  Section B is the direct test of GPT idea #1 (does it factor).
  Section C is GPT idea #2/#3 combined (pull out common structure /
    keep coefficients factored) -- a nontrivial GCD here is the
    highest-leverage win if found, since it shrinks EVERY pseudo-
    division step in the PRS proportionally, for free.
  Section D is the quadratic-in-T^2 / palindromic test.
  Section E answers whether 1445 terms is inherent to the degree-36
    geometry or partly an artifact of carrying (a1,a2,b1,b2) symbolic.
""")






################################################################################
# PART K, REDESIGNED: resultant via a univariate-in-T ring over the
# multivariate coefficient ring F[a1,a2,b1,b2] (or its fraction field),
# instead of a hand-built Sylvester matrix + Leibniz summand enumeration.
#
# -----------------------------------------------------------------------
# WHY THE OLD APPROACH WAS DOOMED, INDEPENDENT OF PARALLELIZATION
# -----------------------------------------------------------------------
# The old "take 5" strategy enumerated permutations sigma of {1..n} and
# formed prod_i Syl[i, sigma[i]] one at a time, banking on the matrix's
# bandedness to skip permutations that are structurally zero. That part
# is correct and does cut 40320 down to a few hundred -- but it attacks
# the wrong axis of the blowup. The evidence is right there in the
# comments: the IDENTITY permutation alone (a single Leibniz summand)
# already produced a degree-256, 17.85-million-term polynomial before
# OOM-killing the process. Bandedness controls *how many* summands are
# nonzero; it says nothing about *how large* each individual summand's
# raw polynomial product is. Multiplying out entries drawn from a
# degree ~32-ish polynomial ring 8 times over, with no cancellation
# available until every one of the (few hundred) surviving summands has
# been formed and added together, is a textbook case of intermediate
# expression swell: the final resultant is typically MUCH smaller than
# any single term in its Leibniz expansion, because the sum cancels
# enormously. Leibniz expansion pays the full swell cost per term and
# only gets the benefit of cancellation at the very end -- if it ever
# gets there.
#
# The original resultant(g1_fp, g2_fp, T_fp) call (Part K, take 3) is
# what actually OOM'd first, and the fallback to hand-rolled Sylvester +
# Leibniz was a strict downgrade, not a fix: it replaced one bad
# algorithm with an even worse one. The real problem was almost
# certainly that g1_fp, g2_fp live in a *plain* 5-variable ring
# F[a1,a2,b1,b2,T], so resultant(...,T) has no structural reason to
# treat T specially -- generic dispatch on a flat multivariate ring can
# fall back to exactly the Sylvester-determinant-by-expansion strategy
# that blew up by hand above, just hidden one call deeper.
#
# -----------------------------------------------------------------------
# THE FIX: change the RING, not the algorithm-by-hand
# -----------------------------------------------------------------------
# g1_fp and g2_fp are each low degree in T (d1T = d2T = 4) with dense
# coefficients in (a1,a2,b1,b2). The right object to compute in is the
# univariate polynomial ring in T *over* the coefficient ring
# F[a1,a2,b1,b2] (equivalently, over its fraction field):
#
#     Rcoef, (a1,a2,b1,b2) = polynomial_ring(F, ["a1","a2","b1","b2"])
#     Rcoef_frac = fraction_field(Rcoef)          # exact division allowed
#     Rt, T = polynomial_ring(Rcoef_frac, "T")
#
# In this tower, resultant(g1_T, g2_T) for univariate polynomials over a
# field-like coefficient ring dispatches to the SUBRESULTANT PRS
# algorithm (Euclidean-style pseudo-remainder sequence, fraction-free /
# Bareiss-type at each step) rather than Leibniz determinant expansion.
# This is the standard replacement for Sylvester-determinant-by-cofactor
# or -by-Leibniz whenever the eliminated variable's degree is small on
# both sides -- exactly this case (degree 4 and 4).
#
# Why this specific algorithm matches this specific matrix:
#   * It is an O(d1T * d2T) sequence of pseudo-division steps (here,
#     4*4 = 16 "slots" worst case, actually far fewer since the PRS
#     degree-drops are usually much faster than unit steps) instead of
#     an O(n!) or even O(n^3) determinant computation on an 8x8 matrix
#     whose entries are already huge.
#   * Every intermediate pseudo-remainder in a subresultant PRS is
#     ITSELF a signed subdeterminant (minor) of the Sylvester matrix,
#     so subresultant theory gives a hard a priori bound on how large
#     each intermediate object can get -- bounded by the same Hadamard-
#     type bound that bounds the FINAL resultant, not by n! times the
#     size of the biggest raw entry. That is precisely "no intermediate
#     expression swell" in the precise technical sense.
#   * It stays exact / symbolic the whole way (fraction-free variants
#     never introduce anything outside the original coefficient ring's
#     fraction field), so priority 4 (exact symbolic arithmetic) holds
#     automatically -- there's no floating point or numerical resultant
#     involved anywhere.
#   * It needs no permutation search, no bandedness bookkeeping, no
#     "nonzero-compatible sigma" enumeration, and no per-summand
#     subprocess harness -- Part K's entire OOM-recovery/subprocess
#     survey machinery becomes unnecessary and can be deleted outright.
#
# Expected complexity: O(d1T * d2T) coefficient-ring pseudo-division
# steps = O(16) worst case here, each step operating on polynomials in
# F[a1,a2,b1,b2] whose size is controlled by the subresultant bound
# rather than growing combinatorially -- versus the old approach's
# O(few hundred surviving permutations) x O(8-factor products of
# degree-32-ish polynomials each), which is precisely what produced a
# single 17.85-million-term intermediate object.
################################################################################

println("  --- $name (redesigned: subresultant PRS, no Sylvester expansion) ---")

# ------------------------------------------------------------------------
# Step 1: coefficient ring F[a1,a2,b1,b2], and its fraction field so
# pseudo-division has exact inverses available. We reuse g1_fp/g2_fp's
# own coefficient extraction (poly_coeffs_in, already present above) to
# avoid re-deriving anything from clean_sample_1/2 -- syl_c1, syl_c2 are
# already exactly "coefficients of g1_fp, g2_fp as polynomials in T",
# living in the 4-variable ring Rfp restricted to (a1,a2,b1,b2). We just
# need to hand them to Oscar's univariate resultant instead of building
# a Sylvester matrix by hand.
# ------------------------------------------------------------------------

Rcoef, (a1_c, a2_c, b1_c, b2_c) = polynomial_ring(F, ["a1", "a2", "b1", "b2"])
Kcoef = fraction_field(Rcoef)

# syl_c1[k+1], syl_c2[k+1] (k = 0..d1T / 0..d2T) currently live in Rfp,
# the 5-variable ring that still nominally contains T_fp as a generator
# (even though these coefficient slices are T-free by construction). Map
# each one down into Rcoef via the same term-by-term MPolyBuildCtx
# technique already used by remap_to_final / poly_coeffs_in elsewhere in
# this file -- linear in term count, no ring-homomorphism machinery.
function drop_T_to_coef_ring(f, coef_gens::Vector)
    B = MPolyBuildCtx(parent(coef_gens[1]))
    for (c, exps) in zip(coefficients(f), AbstractAlgebra.exponent_vectors(f))
        # exps is [e_a1, e_a2, e_b1, e_b2, e_T]; e_T must be 0 here.
        push_term!(B, c, exps[1:4])
    end
    return finish(B)
end

coef_gens = [a1_c, a2_c, b1_c, b2_c]
c1_lifted = [Kcoef(drop_T_to_coef_ring(c, coef_gens)) for c in syl_c1]
c2_lifted = [Kcoef(drop_T_to_coef_ring(c, coef_gens)) for c in syl_c2]

# ------------------------------------------------------------------------
# Step 2: univariate ring in T over Kcoef = Frac(F[a1,a2,b1,b2]), then
# reassemble g1_T, g2_T from their already-extracted coefficient slices
# (syl_c1/syl_c2), and let Oscar's univariate resultant do subresultant
# PRS elimination -- this is the call that replaces the ENTIRE Sylvester-
# matrix-plus-Leibniz-survey apparatus below.
# ------------------------------------------------------------------------

Rt, T = polynomial_ring(Kcoef, string(name))

g1_T = sum(c1_lifted[k+1] * T^k for k in 0:d1T)
g2_T = sum(c2_lifted[k+1] * T^k for k in 0:d2T)

################################################################################
# BEZOUT MATRIX ENTRY DIAGNOSTIC (no determinant computed here)
#
# Question being asked, per Claire's request: before writing/running any
# Bareiss elimination, just BUILD the 4x4 Bezoutian of g1_T, g2_T (both
# degree 4 in T, coefficients in Rcoef = F[a1,a2,b1,b2]) and report
# degree / term count / sparsity for each of the 16 entries. This alone
# tells us whether Bezout construction is cheap (bottleneck genuinely
# was the PRS recursion) or whether it's already expensive (bottleneck
# just moved one step earlier, and Bezout buys nothing by itself).
#
# Construction (only valid for two EXACT degree-4 polynomials, which is
# confirmed here since d1T == d2T == 4):
#
#   g1(T) = sum_{i=0}^4 p_i T^i,   g2(T) = sum_{i=0}^4 q_i T^i
#   [p,q]_{m,n} := p_m*q_n - p_n*q_m   (antisymmetric bracket)
#
#   B00 = [p,q]_{0,1}
#   B01 = [p,q]_{0,2}
#   B02 = [p,q]_{0,3}
#   B03 = [p,q]_{0,4}
#   B11 = [p,q]_{0,3} + [p,q]_{1,2}
#   B12 = [p,q]_{0,4} + [p,q]_{1,3}
#   B13 = [p,q]_{1,4}
#   B22 = [p,q]_{1,4} + [p,q]_{2,3}
#   B23 = [p,q]_{2,4}
#   B33 = [p,q]_{3,4}
#   (B symmetric: Bji = Bij)
#
# c1_lifted / c2_lifted are already the T^0..T^4 coefficients (p_i, q_i)
# as elements of Kcoef = Frac(F[a1,a2,b1,b2]). We expect these
# denominators to be units (same assumption the resultant step below
# already relies on) -- checked explicitly per-entry rather than assumed.
################################################################################

if d1T == 4 && d2T == 4
    println("    --- Bezout matrix entry diagnostic ($name) ---")
    println("    (constructing B only -- NOT computing det(B) / resultant here)")
    flush(stdout)

    p_coef = c1_lifted   # p_coef[k+1] = p_k, k = 0..4
    q_coef = c2_lifted   # q_coef[k+1] = q_k, k = 0..4

    # bracket_num(m, n): numerator polynomial of p_m*q_n - p_n*q_m in
    # Rcoef, after checking both denominators are units. Kept as plain
    # Rcoef elements (not Kcoef fractions) so degree/terms/sparsity are
    # ordinary polynomial-ring queries, matching how res_num is reported
    # further down.
    function bracket_num(m::Int, n::Int)
        pm, qn = p_coef[m+1], q_coef[n+1]
        pn, qm = p_coef[n+1], q_coef[m+1]
        val = pm * qn - pn * qm   # Kcoef arithmetic
        den = denominator(val)
        if !is_unit(den)
            println("      WARNING: [p,q]_{$m,$n} has non-unit denominator " *
                    "(degree=", total_degree(den), ") -- coefficient lift " *
                    "may not be a clean polynomial here; reporting numerator only.")
        end
        return Rcoef(numerator(val))
    end

    # Bracket cache: only distinct (m,n), m<n, are ever needed; brackets
    # are antisymmetric so [p,q]_{n,m} = -[p,q]_{m,n} and have identical
    # degree/term-count/sparsity to their (m,n) counterpart -- computed
    # once per pair.
    bracket_cache = Dict{Tuple{Int,Int}, Any}()
    function bracket(m::Int, n::Int)
        key = m < n ? (m, n) : (n, m)
        if !haskey(bracket_cache, key)
            bracket_cache[key] = bracket_num(key[1], key[2])
        end
        return m < n ? bracket_cache[key] : -bracket_cache[key]
    end

    # Assemble the 10 distinct symmetric entries per the formula above.
    B = Dict{Tuple{Int,Int}, Any}()
    B[(0,0)] = bracket(0,1)
    B[(0,1)] = bracket(0,2)
    B[(0,2)] = bracket(0,3)
    B[(0,3)] = bracket(0,4)
    B[(1,1)] = bracket(0,3) + bracket(1,2)
    B[(1,2)] = bracket(0,4) + bracket(1,3)
    B[(1,3)] = bracket(1,4)
    B[(2,2)] = bracket(1,4) + bracket(2,3)
    B[(2,3)] = bracket(2,4)
    B[(3,3)] = bracket(3,4)
    # symmetric completions
    B[(1,0)] = B[(0,1)]
    B[(2,0)] = B[(0,2)]
    B[(3,0)] = B[(0,3)]
    B[(2,1)] = B[(1,2)]
    B[(3,1)] = B[(1,3)]
    B[(3,2)] = B[(2,3)]

    # Total possible monomials in 4 vars (a1,a2,b1,b2) up to an entry's
    # own total_degree, as a crude density denominator for a sparsity
    # ratio: terms / C(deg+4,4). This is a loose upper bound (actual
    # monomial count of THAT specific degree, not <= degree, would be
    # tighter/more standard, but this is enough to flag "dense vs
    # sparse" at a glance without extra machinery).
    nvars_coef = 4
    function sparsity_ratio(f)
        d = total_degree(f)
        t = length(terms(f))
        # C(d+nvars_coef, nvars_coef) = max monomials of total degree <= d
        max_mono = binomial(d + nvars_coef, nvars_coef)
        return max_mono == 0 ? NaN : t / max_mono
    end

    println("      entry   degree   terms      sparsity(terms/maxmono<=deg)")
    for i in 0:3, j in 0:3
        f = B[(i,j)]
        d = total_degree(f)
        t = length(terms(f))
        s = sparsity_ratio(f)
        println("      B[$i,$j]   ", d, "        ", t, "        ",
                round(s, sigdigits=4))
    end
    flush(stdout)

    total_terms = sum(length(terms(B[(i,j)])) for i in 0:3, j in 0:3)
    max_deg = maximum(total_degree(B[(i,j)]) for i in 0:3, j in 0:3)
    println("      --- summary: max entry degree=$max_deg, " *
            "total terms across all 16 entries=$total_terms ---")
    println("      Reading this: if entries look like degree~64 with ")
    println("      O(1000) terms each, Bezout construction is cheap and ")
    println("      Bareiss elimination is worth writing next. If entries ")
    println("      already look like degree~64 with O(100000+) terms, ")
    println("      the bottleneck has simply moved from the PRS recursion ")
    println("      into Bezout construction itself, and Bareiss won't help.")
    flush(stdout)
else
    println("    (skipping Bezout diagnostic: expected d1T==d2T==4, got ",
            d1T, ", ", d2T, ")")
end

################################################################################
# PARTS A-E: deep structural diagnostic pass, requested BEFORE any resultant
# (Sylvester or Bezout-determinant or PRS) is actually run to completion.
#
# Goal: figure out WHY the Bezout entries came back at ~83,521 terms /
# degree 64 each (~1.3M terms total across the 16 entries) -- is that
# swell inherent to the true resultant's algebraic complexity, or is it
# an artifact of (a) hidden factorable structure in g1/g2, (b) carrying
# redundant non-symmetric variables when a1<->a2, b1<->b2 symmetry is
# available, or (c) a bad representation choice. Nothing below computes
# det(B) or the full resultant -- this is pure structure inspection.
################################################################################
global all_a_sym = true
global all_b_sym = true

if d1T == 4 && d2T == 4
    println()
    println("=" ^ 70)
    println("PARTS A-E: deep diagnostic (no resultant computed) -- $name")
    println("=" ^ 70)
    flush(stdout)

    # ------------------------------------------------------------------
    # shared helper: try factor(), fall back gracefully if it errors or
    # times out conceptually (Oscar's factor() has no built-in timeout,
    # so we just wrap in try/catch -- if factor() itself hangs, that is
    # itself diagnostic information worth seeing separately, but we do
    # not want a factor() hang to mask the rest of this report).
    # ------------------------------------------------------------------
    function safe_factor_report(f; label::String="", indent::String="        ")
        d = total_degree(f)
        t = length(terms(f))
        println(indent, label, "degree=", d, "  terms=", t)
        if iszero(f)
            println(indent, "  (zero polynomial)")
            return
        end
        try
            t0f = time()
            fac = factor(f)
            elf = time() - t0f
            nfac = length(fac)
            println(indent, "  factor() in ", round(elf, digits=3), "s -> ",
                    nfac, " distinct irreducible factor(s):")
            for (fp, e) in fac
                println(indent, "    exponent=", e, "  degree=", total_degree(fp),
                        "  terms=", length(terms(fp)))
            end
        catch err
            println(indent, "  factor() FAILED/skipped: ", sprint(showerror, err))
        end
        flush(stdout)
    end

    # ------------------------------------------------------------------
    # PART A: coefficient-vector analysis of g1, g2 as polynomials in T
    # ------------------------------------------------------------------
    println()
    println("--- PART A: coefficient-vector analysis ---")
    flush(stdout)

    # p_coef, q_coef, bracket_num already defined above (Bezout block);
    # reuse p_coef[k+1]=p_k, q_coef[k+1]=q_k directly -- these are Kcoef
    # elements, take numerator (denominator already unit-checked at
    # construction time via bracket_num's pattern; check again here per
    # coefficient since these are used standalone, not just in brackets).
    function coef_as_poly(c)
        den = denominator(c)
        if !is_unit(den)
            println("      WARNING: coefficient has non-unit denominator (degree=",
                    total_degree(den), ") -- reporting numerator only.")
        end
        return Rcoef(numerator(c))
    end

    g1_coefs_poly = [coef_as_poly(p_coef[k+1]) for k in 0:4]  # index k+1 <-> T^k
    g2_coefs_poly = [coef_as_poly(q_coef[k+1]) for k in 0:4]

    for (gname, cs) in (("g1", g1_coefs_poly), ("g2", g2_coefs_poly))
        println("  $gname:")
        for k in 4:-1:0
            safe_factor_report(cs[k+1]; label="coeff of T^$k: ")
        end
    end

    # structural tests
    println("  structural tests:")
    for (gname, cs) in (("g1", g1_coefs_poly), ("g2", g2_coefs_poly))
        c4, c3, c2, c1, c0 = cs[5], cs[4], cs[3], cs[2], cs[1]
        println("    $gname: T^3 coeff zero? ", iszero(c3),
                "   T^1 coeff zero? ", iszero(c1))
        if iszero(c3) && iszero(c1)
            println("      -> $gname has NO odd-T terms: candidate form ",
                    "T^4 + a*T^2 + c (biquadratic in T) or T^4 + c if also c2==0.")
            if iszero(c2)
                println("      -> $gname coeff-of-T^2 ALSO zero: candidate pure form T^4 + c.")
            end
        end
        # palindromic test: c0 vs c4, c1 vs c3 (up to a possible overall
        # scalar/unit factor -- report the ratio's structure rather than
        # assuming it must be exactly 1)
        if !iszero(c0) && !iszero(c4)
            println("      $gname palindromic check: deg(c0)=", total_degree(c0),
                    " vs deg(c4)=", total_degree(c4),
                    "   deg(c1)=", total_degree(c1),
                    " vs deg(c3)=", total_degree(c3))
        end
        # common factor among "odd slot" coefficients c3, c1 (both should
        # be zero or share a factor if there's hidden even/odd splitting)
        if !iszero(c3) && !iszero(c1)
            g_odd = gcd(c3, c1)
            println("      $gname gcd(c3,c1): degree=", total_degree(g_odd),
                    "  terms=", length(terms(g_odd)),
                    (total_degree(g_odd) > 0 ? "  <-- NONTRIVIAL" : "  (trivial/unit)"))
        end
    end
    flush(stdout)

    # ------------------------------------------------------------------
    # PART B: GCD structure among T-coefficients of each quartic
    # ------------------------------------------------------------------
    println()
    println("--- PART B: GCD structure among T-coefficients ---")
    flush(stdout)

    function report_gcd_pair(cs, gname, i::Int, j::Int)
        ci, cj = cs[i+1], cs[j+1]
        if iszero(ci) || iszero(cj)
            println("    $gname gcd(c$i,c$j): one side is zero -- skipping gcd (undefined/trivial)")
            return
        end
        g = gcd(ci, cj)
        dg = total_degree(g)
        tg = length(terms(g))
        println("    $gname gcd(c$i,c$j): degree=", dg, "  terms=", tg,
                dg > 0 ? "  <-- NONTRIVIAL FACTOR" : "  (unit)")
        if dg > 0
            qi, ri = divrem(ci, g)
            qj, rj = divrem(cj, g)
            ok_i = iszero(ri); ok_j = iszero(rj)
            println("      c$i before=", length(terms(ci)), " terms; after /gcd=",
                    length(terms(qi)), " terms  (exact div? ", ok_i, ")")
            println("      c$j before=", length(terms(cj)), " terms; after /gcd=",
                    length(terms(qj)), " terms  (exact div? ", ok_j, ")")
        end
    end

    for (gname, cs) in (("g1", g1_coefs_poly), ("g2", g2_coefs_poly))
        report_gcd_pair(cs, gname, 4, 3)
        report_gcd_pair(cs, gname, 4, 2)
        report_gcd_pair(cs, gname, 4, 1)
        report_gcd_pair(cs, gname, 4, 0)

        nonzero_cs = [c for c in cs if !iszero(c)]
        if length(nonzero_cs) >= 2
            g_all = reduce(gcd, nonzero_cs)
            dg_all = total_degree(g_all)
            tg_all = length(terms(g_all))
            println("    $gname gcd(all nonzero coefficients): degree=", dg_all,
                    "  terms=", tg_all,
                    dg_all > 0 ? "  <-- NONTRIVIAL, content should be pulled out" : "  (unit, no common content)")
        else
            println("    $gname gcd(all coefficients): fewer than 2 nonzero coefficients, skipping")
        end
    end
    flush(stdout)

    # ------------------------------------------------------------------
    # PART C: symmetry reduction test (a1<->a2, b1<->b2 -> sa,pa,sb,pb)
    # ------------------------------------------------------------------
    println()
    println("--- PART C: symmetry reduction test ---")
    flush(stdout)

    # Build the swap automorphisms of Rcoef directly from its own
    # generators (a1_c,a2_c,b1_c,b2_c already in scope from Step 1
    # above) -- swap a1<->a2 only, and swap b1<->b2 only.
    swap_a = hom(Rcoef, Rcoef, [a2_c, a1_c, b1_c, b2_c])
    swap_b = hom(Rcoef, Rcoef, [a1_c, a2_c, b2_c, b1_c])

    function is_symmetric_under(f, phi)
        return iszero(f - phi(f))
    end

    all_coefs = vcat(
        [("g1", k, g1_coefs_poly[k+1]) for k in 0:4],
        [("g2", k, g2_coefs_poly[k+1]) for k in 0:4]
    )

    global all_a_sym = true
    global all_b_sym = true
    for (gname, k, f) in all_coefs
        if iszero(f)
            continue
        end
        global all_a_sym
        global all_b_sym
        sym_a = is_symmetric_under(f, swap_a)
        sym_b = is_symmetric_under(f, swap_b)
        all_a_sym &= sym_a
        all_b_sym &= sym_b
        println("    $gname coeff of T^$k: symmetric under a1<->a2? ", sym_a,
                "   symmetric under b1<->b2? ", sym_b)
    end
    flush(stdout)

    if all_a_sym && all_b_sym
        println("  CONFIRMED: every quartic coefficient is symmetric under both ",
                "a1<->a2 and b1<->b2.")
        println("  Attempting conversion into elementary symmetric basis ",
                "(sa=a1+a2, pa=a1*a2, sb=b1+b2, pb=b1*b2)...")
        flush(stdout)

        # Symmetric-basis ring
        Rsym, (sa, pa, sb, pb) = polynomial_ring(F, ["sa", "pa", "sb", "pb"])

        # Rewrite f(a1,a2,b1,b2), known symmetric in (a1,a2) and (b1,b2)
        # separately, in terms of (sa,pa,sb,pb) via Newton's identities /
        # direct substitution: express as a polynomial in a1 with
        # coefficients depending on a2 is not what we want -- instead
        # use the standard trick of representing symmetric functions of
        # (a1,a2) via a1=  (sa + d)/2, a2 = (sa-d)/2 is unnecessary; the
        # clean way in a CAS is: build the map by matching monomials.
        # Given full symmetry is already confirmed, every monomial
        # a1^i*a2^j*b1^k*b2^l appears paired with a1^j*a2^i*b1^l*b2^k
        # with equal coefficient (for i!=j or k!=l); we rewrite via
        # repeated elimination: a1^2 -> sa*a1 - pa (since a1,a2 are
        # roots of X^2 - sa*X + pa), reducing every monomial's a-degree
        # in a1,a2 down to at most degree 1 in each of a1,a2 individually
        # then expressing the surviving symmetric combination in sa,pa.
        # For a DIAGNOSTIC term-count measurement (not a full rewrite),
        # we instead use Oscar's msolve/symmetric-function machinery if
        # available, and fall back to a direct evaluate-and-interpolate
        # sanity count if not. Wrapped in try/catch since this is
        # explicitly a "measure savings, don't fully commit" step.
        function try_symmetric_rewrite(f)
            # Fallback strategy: since f is symmetric in (a1,a2) and
            # (b1,b2) separately, and total_degree/term-count are the
            # quantities we actually want, estimate the reduced term
            # count via the standard bound: a symmetric polynomial in
            # (a1,a2) of degree d has a symmetric-basis representation
            # with at most ~ (number of monomials sa^i pa^j with
            # 2j+i <= d_a) terms per "half" -- rather than guess, do the
            # actual rewrite using elimination substitution a1^2 ->
            # sa*a1 - pa repeatedly via divrem in a fresh ring where sa,
            # pa are already available as extra generators, then confirm
            # the a1-degree has dropped to <=1 and a2 no longer appears
            # (by construction) before reading off a monomial count in
            # (sa,pa,b-analog).
            try
                # Extended ring carrying both original and symmetric
                # generators simultaneously so we can do the elimination
                # substitution as ordinary polynomial arithmetic.
                Rext, (a1e,a2e,b1e,b2e,sae,pae,sbe,pbe) = polynomial_ring(
                    F, ["a1","a2","b1","b2","sa","pa","sb","pb"])
                incl = hom(Rcoef, Rext, [a1e,a2e,b1e,b2e])
                fe = incl(f)
                # Reduce a2-degree to 0 using a2 = sa - a1 (exact,
                # since a1+a2=sa), then reduce resulting a1-degree using
                # a1^2 = sae*a1e - pae (from a1,a2 roots of X^2-sa X+pa).
                # Substitute a2e -> (sae - a1e) directly via evaluate.
                fe2 = evaluate(fe, [a1e, sae - a1e, b1e, b2e, sae, pae, sbe, pbe])
                # Now repeatedly knock down a1e powers >=2 using
                # a1e^2 == sae*a1e - pae, via divrem against that
                # relation treated as a univariate reduction in a1e.
                Runiv, a1u = polynomial_ring(fraction_field(Rext), "a1u")
                # This nested-ring gymnastics is more machinery than a
                # pure diagnostic needs; instead do plain polynomial
                # division of fe2 (as element of Rext) by the relation
                # a1e^2 - sae*a1e + pae, using Oscar's built-in divrem
                # in the multivariate ring directly (works because the
                # relation is monic in a1e).
                relation_a = a1e^2 - sae*a1e + pae
                q, r = divrem(fe2, relation_a)
                fe3 = r   # r should now have a1e-degree <= 1
                # Same treatment for b1e/b2e -> sb,pb
                fe4 = evaluate(fe3, [a1e, a2e, b1e, sbe - b1e, sae, pae, sbe, pbe])
                relation_b = b1e^2 - sbe*b1e + pbe
                q2, r2 = divrem(fe4, relation_b)
                fe5 = r2
                # fe5 should now be expressible with a1e,b1e-degree <=1;
                # since f was confirmed FULLY symmetric (not just
                # individually in each pair), the surviving a1e,b1e
                # degree-1 terms must actually cancel to degree 0 -- if
                # they don't, symmetry detection or the reduction has a
                # bug, and we report that rather than silently trusting it.
                deg_a1_remaining = degree(fe5, a1e)
                deg_b1_remaining = degree(fe5, b1e)
                if deg_a1_remaining > 0 || deg_b1_remaining > 0
                    return (nothing, "residual a1/b1-degree after reduction " *
                            "(a1:$deg_a1_remaining, b1:$deg_b1_remaining) -- " *
                            "symmetric rewrite incomplete, reporting raw reduced form")
                end
                # Project down to Rsym by dropping a1e,a2e,b1e,b2e
                # (they should not appear at all at this point).
                Bctx = MPolyBuildCtx(Rsym)
                for (c, exps) in zip(coefficients(fe5), AbstractAlgebra.exponent_vectors(fe5))
                    # exps = [e_a1,e_a2,e_b1,e_b2,e_sa,e_pa,e_sb,e_pb]
                    if exps[1] != 0 || exps[2] != 0 || exps[3] != 0 || exps[4] != 0
                        return (nothing, "unexpected leftover a/b generator in reduced form")
                    end
                    push_term!(Bctx, c, exps[5:8])
                end
                fsym = finish(Bctx)
                return (fsym, nothing)
            catch err
                return (nothing, sprint(showerror, err))
            end
        end

        for (gname, k, f) in all_coefs
            if iszero(f)
                println("    $gname coeff of T^$k: zero, skipping symmetric rewrite")
                continue
            end
            before_terms = length(terms(f))
            before_deg = total_degree(f)
            fsym, err = try_symmetric_rewrite(f)
            if fsym === nothing
                println("    $gname coeff of T^$k: rewrite skipped/failed (", err, ")")
            else
                after_terms = length(terms(fsym))
                after_deg = total_degree(fsym)
                pct = before_terms == 0 ? 0.0 : 100.0 * (1 - after_terms/before_terms)
                println("    $gname coeff of T^$k: degree $before_deg -> $after_deg,  ",
                        "terms $before_terms -> $after_terms  ",
                        "(", round(pct, digits=1), "% reduction)")
            end
            flush(stdout)
        end
    else
        println("  NOT fully symmetric under both swaps for every coefficient -- ",
                "skipping symmetric-basis rewrite (would be unsound).")
    end
    flush(stdout)

    # ------------------------------------------------------------------
    # PART C.5: PARTIAL symmetrization diagnostic.
    #
    # Motivation: PART C above only acts when a coefficient is symmetric
    # under BOTH a1<->a2 AND b1<->b2 simultaneously. In practice g1 is
    # typically symmetric only in (b1,b2) and g2 only in (a1,a2) (see
    # the per-coefficient printout above) -- PART C correctly refuses to
    # touch these ("NOT fully symmetric... skipping"), but that leaves a
    # real, one-sided reduction on the table: a coefficient symmetric in
    # (b1,b2) alone can still be rewritten in (a1,a2,sb,pb), dropping b1,b2
    # individually without touching a1,a2. This block does exactly that
    # rewrite, per coefficient, for whichever single pair is symmetric,
    # and separately stress-tests the "combine g1 and g2 afterwards"
    # step, since g1 and g2 end up partially symmetrized in DIFFERENT
    # variable pairs and are not obviously combinable without further
    # work (see PART C.5 SECTION 3 below).
    #
    # IMPLEMENTATION NOTE (important, learned the hard way): the first
    # version of this diagnostic used `divrem(f, b1^2 - sb*b1 + pb)` in
    # the ambient multivariate ring to perform the b1-degree reduction.
    # That is WRONG in general: multivariate divrem reduces against the
    # divisor's leading term under the ring's *global* monomial order
    # (degrevlex here), not against "the b1^2 term specifically" -- and
    # since sb*b1 and b1^2 are the same total degree, degrevlex's
    # tie-break (on variable position) can pick sb*b1 as the leading
    # term instead of b1^2, so the "reduction" silently does nothing.
    # That bug produced a suspicious flat 0.0% reduction on every
    # coefficient, which is what exposed it.
    #
    # Fixed approach: extract f's coefficients EXPLICITLY as a
    # polynomial in the single variable being eliminated (via coeff(f,
    # [var], [d]) for each degree d present -- ordering-independent,
    # already used elsewhere in this file, e.g. leading_coeff_in), then
    # perform the b1^2 -> sb*b1 - pb (or a1^2 -> sa*a1 - pa) reduction
    # by explicit degree-by-degree substitution, which has no
    # dependence on any monomial order at all.
    # ------------------------------------------------------------------
    println()
    println("--- PART C.5: partial symmetrization diagnostic ---")
    flush(stdout)

    # Target rings for the two partial-rewrite directions.
    Rb_only, (a1b, a2b, sbb, pbb) = polynomial_ring(F, ["a1", "a2", "sb", "pb"])
    Ra_only, (saa, paa, b1a, b2a) = polynomial_ring(F, ["sa", "pa", "b1", "b2"])

    # Scratch ring: original vars plus both symmetric-pair substitutes,
    # used only as a common home for intermediate coefficient-polynomial
    # arithmetic (additions/multiplications of coefficient-of-b1^k
    # pieces, which themselves still depend on a1,a2 and, after
    # reduction, on sb,pb). No divrem against a 2-term relation is done
    # in this ring -- see note above.
    Rext_c5, (a1c5, a2c5, b1c5, b2c5, sac5, pac5, sbc5, pbc5) = polynomial_ring(
        F, ["a1", "a2", "b1", "b2", "sa", "pa", "sb", "pb"])
    incl_c5 = hom(Rcoef, Rext_c5, [a1c5, a2c5, b1c5, b2c5])

    # Ordering-independent reduction of a univariate-in-`var` polynomial
    # (given as a Dict degree => coefficient-polynomial, coefficients
    # living in Rext_c5) modulo relation var^2 = lin*var + const, i.e.
    # standard "reduce a degree-d polynomial in a quadratic-algebraic
    # element down to degree <=1" via repeated top-down substitution:
    # var^k = lin*var^(k-1) + const*var^(k-2) for k>=2, applied
    # degree-by-degree starting from the top so every step only ever
    # touches two adjacent coefficient slots.
    function reduce_quadratic!(coeffs_by_deg::Dict{Int,Any}, lin, const_term)
        maxd = maximum(keys(coeffs_by_deg))
        for d in maxd:-1:2
            c = get(coeffs_by_deg, d, nothing)
            if c === nothing || iszero(c)
                delete!(coeffs_by_deg, d)
                continue
            end
            delete!(coeffs_by_deg, d)
            # var^d = var^(d-2) * (lin*var + const)
            #       = lin*var^(d-1) + const*var^(d-2)
            coeffs_by_deg[d-1] = get(coeffs_by_deg, d-1, zero(c)) + lin*c
            coeffs_by_deg[d-2] = get(coeffs_by_deg, d-2, zero(c)) + const_term*c
        end
        return coeffs_by_deg   # now only keys 0 and/or 1 remain
    end

    # Rewrite f, KNOWN symmetric in (b1,b2) only, into (a1,a2,sb,pb):
    # substitute b2 -> sb - b1 (exact, since b1+b2=sb), extract the
    # resulting polynomial's coefficients in b1 explicitly via coeff(),
    # reduce those degree-by-degree via reduce_quadratic! using
    # b1^2 = sb*b1 - pb, and verify the degree-1-in-b1 slot vanishes
    # (as it must, since f depends on b1,b2 ONLY through symmetric
    # combinations -- this is the standard elementary-symmetric-
    # polynomial fact, and is checked rather than assumed).
    function symmetrize_b_only(f; debug::Bool=false)
        debug && println("      [DBG b_only] input f: terms=", length(terms(f)),
                          "  degree=", total_degree(f))
        # --- NEW DIAGNOSTIC: check raw f's dependence on b1_c/b2_c BEFORE
        # any ring games, using both element-form and index-form degree(),
        # so any divergence between the two call conventions is exposed
        # directly instead of silently producing a wrong (possibly always
        # 0) answer downstream.
        if debug
            println("      [DBG b_only] === RAW f DIAGNOSTIC (in Rcoef) ===")
            println("      [DBG b_only] degree(f, b1_c)              = ", degree(f, b1_c))
            println("      [DBG b_only] degree(f, b2_c)              = ", degree(f, b2_c))
            println("      [DBG b_only] var_index(b1_c)              = ", var_index(b1_c))
            println("      [DBG b_only] var_index(b2_c)              = ", var_index(b2_c))
            println("      [DBG b_only] degree(f, var_index(b1_c))   = ", degree(f, var_index(b1_c)))
            println("      [DBG b_only] vars(f) (generators actually appearing) = ", vars(f))
        end
        fe = incl_c5(f)
        debug && println("      [DBG b_only] after incl_c5: terms=", length(terms(fe)))
        if debug
            println("      [DBG b_only] === fe DIAGNOSTIC (in Rext_c5, pre-substitution) ===")
            println("      [DBG b_only] degree(fe, b1c5)             = ", degree(fe, b1c5))
            println("      [DBG b_only] degree(fe, b2c5)             = ", degree(fe, b2c5))
            println("      [DBG b_only] var_index(b1c5)              = ", var_index(b1c5))
            println("      [DBG b_only] var_index(b2c5)              = ", var_index(b2c5))
            println("      [DBG b_only] vars(fe) (generators appearing) = ", vars(fe))
        end
        fe2 = evaluate(fe, [a1c5, a2c5, b1c5, sbc5 - b1c5, sac5, pac5, sbc5, pbc5])
        debug && println("      [DBG b_only] after b2->sb-b1 substitution: terms=",
                          length(terms(fe2)), "  degree=", total_degree(fe2))
        d = degree(fe2, b1c5)
        debug && println("      [DBG b_only] degree(fe2, b1c5) [element-form] = ", d)
        if debug
            d_idx = degree(fe2, var_index(b1c5))
            println("      [DBG b_only] degree(fe2, var_index(b1c5)) [index-form] = ", d_idx,
                    d_idx != d ? "   <<<< MISMATCH between element-form and index-form degree()!" : "   (match)")
            println("      [DBG b_only] vars(fe2) (generators appearing after substitution) = ", vars(fe2))
            println("      [DBG b_only] degree(fe2, sbc5) [should be >0 if sb actually entered] = ", degree(fe2, sbc5))
            # Direct algebraic sanity check: fe2 should NOT equal fe if the
            # substitution actually did anything (unless f happens to be
            # independent of b2c5, which contradicts Section-1 classification).
            println("      [DBG b_only] fe2 == fe (substitution was a no-op)? ", fe2 == fe)
        end
        coeffs_by_deg = Dict{Int,Any}()
        # --- NEW: cross-check element-form coeff(f, [var_element], [exp])
        # against the documented index-form coeff(f, vars::Vector{Int},
        # exps::Vector{Int}) API for every degree 0:d, so a call-convention
        # bug is caught mechanically rather than assumed away.
        if debug
            b1_idx = var_index(b1c5)
            for k in 0:d
                ck_elem = coeff(fe2, [b1c5], [k])
                ck_idx  = coeff(fe2, [b1_idx], [k])
                same = ck_elem == ck_idx
                println("      [DBG b_only] k=$k: coeff(fe2,[b1c5],[k]) terms=",
                        length(terms(ck_elem)), "   coeff(fe2,[b1_idx=$b1_idx],[k]) terms=",
                        length(terms(ck_idx)),
                        same ? "   (match)" : "   <<<< MISMATCH between element-form and index-form coeff()!")
            end
        end
        for k in 0:d
            ck = coeff(fe2, [var_index(b1c5)], [k])
            if !iszero(ck)
                coeffs_by_deg[k] = ck
                debug && println("      [DBG b_only] coeff of b1^", k, ": terms=",
                                  length(terms(ck)))
            end
        end
        if isempty(coeffs_by_deg)
            coeffs_by_deg[0] = zero(fe2)
        end
        debug && println("      [DBG b_only] sum of per-degree term counts BEFORE reduce = ",
                          sum(length(terms(v)) for v in values(coeffs_by_deg)),
                          "  (compare to fe2's ", length(terms(fe2)), " -- should roughly match",
                          " if coeff() extraction is complete and non-overlapping)")
        reduce_quadratic!(coeffs_by_deg, sbc5, -pbc5)
        debug && println("      [DBG b_only] AFTER reduce_quadratic!: remaining keys=",
                          sort(collect(keys(coeffs_by_deg))),
                          "  term counts=", Dict(k=>length(terms(v)) for (k,v) in coeffs_by_deg))
        if haskey(coeffs_by_deg, 1) && !iszero(coeffs_by_deg[1])
            debug && println("      [DBG b_only] FAILED: nonzero b1^1 residual, terms=",
                              length(terms(coeffs_by_deg[1])))
            return (nothing, "residual b1-degree=1 term did not vanish after " *
                    "reduction -- f was not actually (b1,b2)-symmetric, or " *
                    "reduction bug")
        end
        r = get(coeffs_by_deg, 0, zero(fe2))
        debug && println("      [DBG b_only] r (post-reduction, pre-projection): terms=",
                          length(terms(r)), "  degree=", total_degree(r))
        Bctx = MPolyBuildCtx(Rb_only)
        n_pushed = 0
        for (c, exps) in zip(coefficients(r), AbstractAlgebra.exponent_vectors(r))
            # exps = [e_a1,e_a2,e_b1,e_b2,e_sa,e_pa,e_sb,e_pb]
            if exps[3] != 0 || exps[4] != 0
                debug && println("      [DBG b_only] FAILED at projection: leftover b1/b2 exps=", exps)
                return (nothing, "unexpected leftover b1/b2 exponent after reduction " *
                        "(exps=$exps) -- reduction did not fully eliminate b1,b2")
            end
            if exps[5] != 0 || exps[6] != 0
                debug && println("      [DBG b_only] FAILED at projection: leftover sa/pa exps=", exps)
                return (nothing, "unexpected sa/pa dependence in a b-only rewrite " *
                        "(exps=$exps) -- sa,pa should never appear here")
            end
            push_term!(Bctx, c, [exps[1], exps[2], exps[7], exps[8]])
            n_pushed += 1
        end
        fsym = finish(Bctx)
        debug && println("      [DBG b_only] pushed ", n_pushed, " terms into Bctx; ",
                          "finish(Bctx) reports terms=", length(terms(fsym)),
                          "  degree=", total_degree(fsym))
        return (fsym, nothing)   # lives in Rb_only: (a1,a2,sb,pb)
    end

    # Mirror image: f known symmetric in (a1,a2) only, rewritten into
    # (sa,pa,b1,b2), leaving b1,b2 untouched.
    function symmetrize_a_only(f; debug::Bool=false)
        debug && println("      [DBG a_only] input f: terms=", length(terms(f)),
                          "  degree=", total_degree(f))
        if debug
            println("      [DBG a_only] === RAW f DIAGNOSTIC (in Rcoef) ===")
            println("      [DBG a_only] degree(f, a1_c)              = ", degree(f, a1_c))
            println("      [DBG a_only] degree(f, a2_c)              = ", degree(f, a2_c))
            println("      [DBG a_only] var_index(a1_c)              = ", var_index(a1_c))
            println("      [DBG a_only] vars(f) (generators actually appearing) = ", vars(f))
        end
        fe = incl_c5(f)
        if debug
            println("      [DBG a_only] === fe DIAGNOSTIC (in Rext_c5, pre-substitution) ===")
            println("      [DBG a_only] degree(fe, a1c5)             = ", degree(fe, a1c5))
            println("      [DBG a_only] degree(fe, a2c5)             = ", degree(fe, a2c5))
            println("      [DBG a_only] vars(fe) (generators appearing) = ", vars(fe))
        end
        fe2 = evaluate(fe, [a1c5, sac5 - a1c5, b1c5, b2c5, sac5, pac5, sbc5, pbc5])
        debug && println("      [DBG a_only] after a2->sa-a1 substitution: terms=",
                          length(terms(fe2)), "  degree=", total_degree(fe2))
        d = degree(fe2, a1c5)
        debug && println("      [DBG a_only] degree(fe2, a1c5) [element-form] = ", d)
        if debug
            d_idx = degree(fe2, var_index(a1c5))
            println("      [DBG a_only] degree(fe2, var_index(a1c5)) [index-form] = ", d_idx,
                    d_idx != d ? "   <<<< MISMATCH between element-form and index-form degree()!" : "   (match)")
            println("      [DBG a_only] vars(fe2) (generators appearing after substitution) = ", vars(fe2))
            println("      [DBG a_only] degree(fe2, sac5) [should be >0 if sa actually entered] = ", degree(fe2, sac5))
            println("      [DBG a_only] fe2 == fe (substitution was a no-op)? ", fe2 == fe)
        end
        coeffs_by_deg = Dict{Int,Any}()
        if debug
            a1_idx = var_index(a1c5)
            for k in 0:d
                ck_elem = coeff(fe2, [a1c5], [k])
                ck_idx  = coeff(fe2, [a1_idx], [k])
                same = ck_elem == ck_idx
                println("      [DBG a_only] k=$k: coeff(fe2,[a1c5],[k]) terms=",
                        length(terms(ck_elem)), "   coeff(fe2,[a1_idx=$a1_idx],[k]) terms=",
                        length(terms(ck_idx)),
                        same ? "   (match)" : "   <<<< MISMATCH between element-form and index-form coeff()!")
            end
        end
        for k in 0:d
            ck = coeff(fe2, [var_index(a1c5)], [k])
            if !iszero(ck)
                coeffs_by_deg[k] = ck
                debug && println("      [DBG a_only] coeff of a1^", k, ": terms=",
                                  length(terms(ck)))
            end
        end
        if isempty(coeffs_by_deg)
            coeffs_by_deg[0] = zero(fe2)
        end
        debug && println("      [DBG a_only] sum of per-degree term counts BEFORE reduce = ",
                          sum(length(terms(v)) for v in values(coeffs_by_deg)))
        reduce_quadratic!(coeffs_by_deg, sac5, -pac5)
        debug && println("      [DBG a_only] AFTER reduce_quadratic!: remaining keys=",
                          sort(collect(keys(coeffs_by_deg))),
                          "  term counts=", Dict(k=>length(terms(v)) for (k,v) in coeffs_by_deg))
        if haskey(coeffs_by_deg, 1) && !iszero(coeffs_by_deg[1])
            debug && println("      [DBG a_only] FAILED: nonzero a1^1 residual, terms=",
                              length(terms(coeffs_by_deg[1])))
            return (nothing, "residual a1-degree=1 term did not vanish after " *
                    "reduction -- f was not actually (a1,a2)-symmetric, or " *
                    "reduction bug")
        end
        r = get(coeffs_by_deg, 0, zero(fe2))
        debug && println("      [DBG a_only] r (post-reduction, pre-projection): terms=",
                          length(terms(r)), "  degree=", total_degree(r))
        Bctx = MPolyBuildCtx(Ra_only)
        n_pushed = 0
        for (c, exps) in zip(coefficients(r), AbstractAlgebra.exponent_vectors(r))
            # exps = [e_a1,e_a2,e_b1,e_b2,e_sa,e_pa,e_sb,e_pb]
            if exps[1] != 0 || exps[2] != 0
                debug && println("      [DBG a_only] FAILED at projection: leftover a1/a2 exps=", exps)
                return (nothing, "unexpected leftover a1/a2 exponent after reduction " *
                        "(exps=$exps) -- reduction did not fully eliminate a1,a2")
            end
            if exps[7] != 0 || exps[8] != 0
                debug && println("      [DBG a_only] FAILED at projection: leftover sb/pb exps=", exps)
                return (nothing, "unexpected sb/pb dependence in an a-only rewrite " *
                        "(exps=$exps) -- sb,pb should never appear here")
            end
            push_term!(Bctx, c, [exps[5], exps[6], exps[3], exps[4]])
            n_pushed += 1
        end
        fsym = finish(Bctx)
        debug && println("      [DBG a_only] pushed ", n_pushed, " terms into Bctx; ",
                          "finish(Bctx) reports terms=", length(terms(fsym)),
                          "  degree=", total_degree(fsym))
        return (fsym, nothing)   # lives in Ra_only: (sa,pa,b1,b2)
    end

    println()
    println("  Section 1: per-coefficient single-pair symmetry classification")
    println("  (independent of PART C's all-coefficients-at-once verdict above)")
    flush(stdout)

    # classification[gname][k] in {:both, :a_only, :b_only, :neither, :zero,
    #                               :indep_of_both, :indep_of_a, :indep_of_b}
    #
    # IMPORTANT: is_symmetric_under(f, swap_a) is VACUOUSLY true whenever f
    # does not depend on a1,a2 at all (swapping variables that don't appear
    # is a no-op) -- and likewise for swap_b. Section 2's "symmetrize"
    # rewrite then has nothing real to reduce, which is exactly why it was
    # reporting a flat 0.0% reduction on every coefficient: g1's
    # coefficients are genuinely independent of b1,b2 (not merely
    # b-symmetric), and g2's are genuinely independent of a1,a2. So
    # dependence is checked explicitly via degree() BEFORE trusting the
    # swap-symmetry test, and the vacuous cases are given their own labels
    # so Section 2 can skip them (there is nothing to symmetrize) instead
    # of "succeeding" at a no-op.
    c5_class = Dict{Tuple{String,Int},Symbol}()
    for (gname, k, f) in all_coefs
        if iszero(f)
            c5_class[(gname,k)] = :zero
            println("    $gname coeff of T^$k: zero, skipping")
            continue
        end
        depends_on_a = degree(f, a1_c) > 0 || degree(f, a2_c) > 0
        depends_on_b = degree(f, b1_c) > 0 || degree(f, b2_c) > 0
        sym_a = is_symmetric_under(f, swap_a)
        sym_b = is_symmetric_under(f, swap_b)
        local cls
        if !depends_on_a && !depends_on_b
            cls = :indep_of_both   # constant in all four -- shouldn't happen given degree=32, but handle it
        elseif !depends_on_b
            cls = :indep_of_b      # vacuously b-symmetric; genuinely a1,a2-only, not reducible via b-swap
        elseif !depends_on_a
            cls = :indep_of_a      # vacuously a-symmetric; genuinely b1,b2-only, not reducible via a-swap
        elseif sym_a && sym_b
            cls = :both
        elseif sym_a
            cls = :a_only
        elseif sym_b
            cls = :b_only
        else
            cls = :neither
        end
        c5_class[(gname,k)] = cls
        println("    $gname coeff of T^$k: class=", cls,
                "  (a1<->a2? ", sym_a, ", b1<->b2? ", sym_b,
                ", depends_on_a=", depends_on_a, ", depends_on_b=", depends_on_b, ")")
    end
    flush(stdout)

    println()
    println("  Section 2: partial rewrite term/degree reduction, per coefficient")
    println("  (only attempted where Section 1 found GENUINE a1-only or b1-only")
    println("  symmetry -- i.e. the coefficient actually depends on both members")
    println("  of that pair, and is truly symmetric under swapping them. 'both'")
    println("  coefficients are handled by PART C above and skipped here to avoid")
    println("  double-reporting. 'neither' cannot be partially symmetrized at all.")
    println("  'indep_of_a'/'indep_of_b' are the VACUOUS case caught by the")
    println("  Section-1 fix: the coefficient simply does not depend on that pair")
    println("  at all, so is_symmetric_under() was trivially true and there is")
    println("  nothing to symmetrize -- reported honestly instead of run through")
    println("  the rewrite as a no-op, which is what previously produced the flat")
    println("  0.0% reduction on every coefficient.)")
    flush(stdout)

    c5_rewritten = Dict{Tuple{String,Int},Any}()   # stores (poly, which_pair)
    for (gname, k, f) in all_coefs
        cls = c5_class[(gname,k)]
        if cls == :zero
            continue
        elseif cls == :both
            println("    $gname coeff of T^$k: fully symmetric (both pairs) -- ",
                    "see PART C above, not repeated here")
            continue
        elseif cls == :neither
            println("    $gname coeff of T^$k: symmetric under NEITHER swap -- ",
                    "no partial symmetrization possible")
            continue
        elseif cls == :indep_of_both
            println("    $gname coeff of T^$k: independent of a1,a2,b1,b2 entirely -- ",
                    "already minimal, no symmetrization applicable")
            continue
        elseif cls == :indep_of_b
            println("    $gname coeff of T^$k: VACUOUS b-symmetry -- coefficient does ",
                    "not depend on b1,b2 at all (only a1,a2); swap-symmetry was trivially ",
                    "true and there is nothing to symmetrize. Already minimal in b.")
            continue
        elseif cls == :indep_of_a
            println("    $gname coeff of T^$k: VACUOUS a-symmetry -- coefficient does ",
                    "not depend on a1,a2 at all (only b1,b2); swap-symmetry was trivially ",
                    "true and there is nothing to symmetrize. Already minimal in a.")
            continue
        end
        # From here on, cls is genuinely :a_only or :b_only -- the
        # coefficient really depends on both members of that pair AND is
        # really symmetric under swapping them, so the rewrite has actual
        # work to do.

        before_terms = length(terms(f))
        before_deg = total_degree(f)

        # Full stage-by-stage trace on just the FIRST coefficient we hit
        # for each rewrite direction (b_only / a_only) -- enough to
        # diagnose where the pipeline diverges without flooding output
        # for all ten coefficients.
        global _c5_debug_done_b = @isdefined(_c5_debug_done_b) ? _c5_debug_done_b : false
        global _c5_debug_done_a = @isdefined(_c5_debug_done_a) ? _c5_debug_done_a : false

        if cls == :b_only
            do_dbg = !_c5_debug_done_b
            if do_dbg
                println("    [entering full debug trace for $gname coeff of T^$k, class=b_only]")
                global _c5_debug_done_b = true
            end
            fsym, err = symmetrize_b_only(f; debug=do_dbg)
            pairname = "b"
        else # :a_only
            do_dbg = !_c5_debug_done_a
            if do_dbg
                println("    [entering full debug trace for $gname coeff of T^$k, class=a_only]")
                global _c5_debug_done_a = true
            end
            fsym, err = symmetrize_a_only(f; debug=do_dbg)
            pairname = "a"
        end

        if fsym === nothing
            println("    $gname coeff of T^$k: rewrite FAILED (", err, ")")
        else
            after_terms = length(terms(fsym))
            after_deg = total_degree(fsym)
            pct = before_terms == 0 ? 0.0 : 100.0 * (1 - after_terms/before_terms)
            println("    $gname coeff of T^$k: symmetrized ($pairname-pair only)  ",
                    "degree $before_deg -> $after_deg,  terms $before_terms -> $after_terms  ",
                    "(", round(pct, digits=1), "% reduction)")
            c5_rewritten[(gname,k)] = (fsym, cls)
        end
        flush(stdout)
    end

    println()
    println("  Section 2 summary: aggregate term counts, symmetrized vs raw")
    let
        raw_total = 0
        sym_total = 0
        n_rewritten = 0
        for (gname, k, f) in all_coefs
            cls = c5_class[(gname,k)]
            if cls == :a_only || cls == :b_only
                haskey(c5_rewritten, (gname,k)) || continue
                raw_total += length(terms(f))
                sym_total += length(terms(c5_rewritten[(gname,k)][1]))
                n_rewritten += 1
            end
        end
        if n_rewritten > 0
            pct = 100.0 * (1 - sym_total/raw_total)
            println("    $n_rewritten coefficient(s) partially symmetrized: ",
                    "total terms $raw_total -> $sym_total  (", round(pct, digits=1), "% reduction)")
        else
            println("    no coefficients were eligible for partial symmetrization ",
                    "(all were :both, :neither, or :zero)")
        end
    end
    flush(stdout)

    println()
    println("  Section 3: cross-ring combination check")
    println("  (the actual hazard flagged for Task 2: g1 is typically rewritten")
    println("  in (a1,a2,sb,pb) and g2 in (sa,pa,b1,b2) -- these are DIFFERENT")
    println("  rings and cannot be combined [resultant/GCD/matching] directly.")
    println("  This section checks, computationally, whether that combination")
    println("  requires reintroducing the eliminated pair, i.e. whether the")
    println("  partial rewrite is a dead end for the downstream matching step")
    println("  as currently structured.)")
    flush(stdout)

    g1_b_only_present = any(c5_class[("g1",k)] == :b_only for k in 0:4 if haskey(c5_class,("g1",k)))
    g2_a_only_present = any(c5_class[("g2",k)] == :a_only for k in 0:4 if haskey(c5_class,("g2",k)))

    if g1_b_only_present && g2_a_only_present
        println("    g1 has (b1,b2)-symmetric coefficient(s); g2 has (a1,a2)-symmetric ",
                "coefficient(s) -- this is the expected asymmetric case from the log.")
        println("    g1's natural target ring after rewrite: (a1,a2,sb,pb)")
        println("    g2's natural target ring after rewrite: (sa,pa,b1,b2)")
        println("    Common ring containing BOTH without reintroducing any variable ",
                "individually: NONE -- (a1,a2,sb,pb) has a1,a2 unreduced while ",
                "(sa,pa,b1,b2) has b1,b2 unreduced, and neither is a subring of the other.")
        println("    Only combination routes available, in order of cost:")
        println("      (i)   map BOTH into the raw ring (a1,a2,b1,b2) -- discards all")
        println("            symmetrization savings before the combination step, i.e.")
        println("            the win from Section 2 does not survive into PART K's")
        println("            final collision step as currently structured.")
        println("      (ii)  desymmetrize the OTHER pair back out of each side via the")
        println("            quadratic formula (b1,b2 = (sb +/- sqrt(sb^2-4pb))/2, and")
        println("            symmetrically for a1,a2) before combining -- reintroduces")
        println("            a degree-2 field extension per desymmetrized pair, so this")
        println("            is not free either, and needs explicit sign-branch handling.")
        println("      (iii) fully symmetrize BOTH g1 and g2 in BOTH pairs -- only valid")
        println("            if g1 is ALSO (a1,a2)-symmetric and g2 ALSO (b1,b2)-symmetric,")
        println("            which PART C above already tests; per the log this is FALSE,")
        println("            so route (iii) is not available for this construction.")
        println("    VERDICT: partial symmetrization, as currently scoped, reduces the")
        println("    SIZE of g1 and g2 individually (Section 2 numbers above are real)")
        println("    but does NOT by itself simplify the PART K combination step -- that")
        println("    step still needs route (i) or (ii). This should be treated as an")
        println("    open sub-problem, not assumed solved by Section 2's reduction.")
    else
        g1_indep_b = any(get(c5_class, ("g1",k), nothing) == :indep_of_b for k in 0:4)
        g2_indep_a = any(get(c5_class, ("g2",k), nothing) == :indep_of_a for k in 0:4)
        if g1_indep_b && g2_indep_a
            println("    Did NOT find genuine b-only/a-only partial symmetry -- instead,")
            println("    Section 1 found g1's coefficients are entirely INDEPENDENT of")
            println("    b1,b2 (they only ever involved a1,a2 to begin with), and g2's")
            println("    coefficients are entirely INDEPENDENT of a1,a2 (only b1,b2).")
            println("    This is a stronger, better situation than partial symmetrization:")
            println("    g1 already lives in the smaller ring (a1,a2) and g2 already lives")
            println("    in (b1,b2) -- no rewrite, no quadratic-relation reduction, and no")
            println("    sqrt-desymmetrization is needed to get there, because they were")
            println("    never coupled to the other pair in the first place. The routes")
            println("    (i)/(ii)/(iii) discussion above does not apply to this case: the")
            println("    combination step should instead be analyzed directly as a")
            println("    resultant/Bezout construction between a genuinely-(a1,a2)-only")
            println("    polynomial and a genuinely-(b1,b2)-only polynomial, which may be")
            println("    a materially easier structure than the general 4-variable case")
            println("    assumed by PART D/E above -- worth re-deriving those diagnostics")
            println("    with this narrower variable dependence taken into account.")
        else
            println("    Did not find the previously-assumed g1:(b-only) / g2:(a-only) ",
                    "asymmetric pattern in this run's classification (see Section 1) -- ",
                    "re-check before relying on the analysis below.")
        end
    end
    flush(stdout)

    println()
    println("  Section 4: partially-symmetrized Bezout-entry-style size probe")
    println("  (compares the combined term count of g1[T^0]+g2[T^0] in raw form")
    println("  against their partially symmetrized intermediate form, so the")
    println("  effect of Section 2's reduction can be read off directly before")
    println("  any remapping-back-to-raw-ring cost from Section 3 is paid.)")
    flush(stdout)

    if haskey(c5_rewritten, ("g1",0)) && haskey(c5_rewritten, ("g2",0))
        f1sym, cls1 = c5_rewritten[("g1",0)]
        f2sym, cls2 = c5_rewritten[("g2",0)]
        raw_terms = length(terms(g1_coefs_poly[1])) + length(terms(g2_coefs_poly[1]))
        sym_terms = length(terms(f1sym)) + length(terms(f2sym))
        println("    g1[T^0] + g2[T^0] combined term count:")
        println("      raw (a1,a2,b1,b2) form:          ", raw_terms)
        println("      partially symmetrized form:      ", sym_terms,
                "  (", round(100.0*(1-sym_terms/raw_terms), digits=1), "% smaller)")
        println("    NOTE: this measures the SYMMETRIZED INTERMEDIATE size only --")
        println("    per Section 3, recombining these into one Bezout-style entry")
        println("    still requires mapping back to the raw ring (route (i)) or a")
        println("    sqrt-desymmetrization (route (ii)), so this number bounds the")
        println("    best case, not the as-implemented case, until Section 3's open")
        println("    sub-problem is resolved.")
    else
        println("    g1[T^0]/g2[T^0] not both eligible for partial symmetrization in ",
                "this run -- skipping Section 4 size probe (see Section 1 above).")
    end
    flush(stdout)

    println()
    println("PART C.5 COMPLETE")
    println("Answering (per Task 2 questions):")
    println("  - meaningful term-count reduction from partial symmetrization?")
    println("    -> see Section 2 summary (aggregate) and per-coefficient lines.")
    println("  - hidden pitfalls combining partially-symmetrized rings?")
    println("    -> see Section 3 (this is a real, currently-open blocker, not")
    println("       merely a theoretical concern -- routes (i)/(ii)/(iii) are the")
    println("       only options and none is free).")
    println("  - does it help the actual Bezout/PRS combination step, not just")
    println("    the standalone coefficient size?")
    println("    -> see Section 4 (currently: reduces intermediate size only;")
    println("       benefit at the combination step is NOT yet demonstrated).")
    flush(stdout)

    # ------------------------------------------------------------------
    # PART D: Bezout entry sparsity / factoring analysis
    # ------------------------------------------------------------------
    println()
    println("--- PART D: Bezout entry sparsity analysis ---")
    flush(stdout)

    function monomial_support_report(f; indent::String="        ")
        # variables actually appearing (nonzero exponent in at least one term)
        nv = nvars(parent(f))
        appears = falses(nv)
        for exps in AbstractAlgebra.exponent_vectors(f)
            for (idx, e) in enumerate(exps)
                if e != 0
                    appears[idx] = true
                end
            end
        end
        vnames = [string(g) for g in gens(parent(f))]
        present = [vnames[i] for i in 1:nv if appears[i]]
        println(indent, "variables appearing: ", present)
    end

    for i in 0:3, j in i:3   # symmetric, only report each distinct entry once
        f = B[(i,j)]
        println("  B[$i,$j]:")
        println("    total_degree=", total_degree(f), "  terms=", length(terms(f)))
        monomial_support_report(f)
        # common-factor check: gcd across the polynomial's own terms is
        # not directly a builtin op (terms don't individually gcd against
        # each other in the usual sense) -- what's meaningful here is
        # whether factor() finds this entry has a nontrivial factorization
        # (i.e. gcd of its irreducible factors' multiplicities > trivial),
        # which safe_factor_report already reports. Run it once per
        # entry as requested.
        safe_factor_report(f; label="", indent="    ")
        flush(stdout)
    end

    # ------------------------------------------------------------------
    # PART E: PRS growth prediction -- single pseudo-remainder step only
    # ------------------------------------------------------------------
    println()
    println("--- PART E: PRS growth prediction (ONE pseudo-remainder step only) ---")
    flush(stdout)

    try
        t0e = time()
        r_prem = pseudorem(g1_T, g2_T)
        el_e = time() - t0e
        println("  prem(g1_T, g2_T) computed in ", round(el_e, digits=3), "s")
        if iszero(r_prem)
            println("  r is IDENTICALLY ZERO (g2_T | g1_T over Kcoef) -- degenerate case, inspect inputs.")
        else
            deg_r = degree(r_prem)
            println("  degree in T of r: ", deg_r)
            max_terms = 0
            local max_deg = 0
            for k in 0:deg_r
                ck = coeff(r_prem, k)
                ck_num = coef_as_poly(ck)
                tk = length(terms(ck_num))
                dk = total_degree(ck_num)
                max_terms = max(max_terms, tk)
                max_deg = max(max_deg, dk)
                println("    coeff of T^$k in r: degree=", dk, "  terms=", tk)
            end
            println("  --- summary: max coeff term count=", max_terms,
                    "  max coeff total_degree=", max_deg, " ---")
            # gcd across r's coefficients, same content check as Part B
            r_coefs_nonzero = [coef_as_poly(coeff(r_prem, k)) for k in 0:deg_r
                                if !iszero(coeff(r_prem, k))]
            if length(r_coefs_nonzero) >= 2
                g_r = reduce(gcd, r_coefs_nonzero)
                println("  gcd(all coefficients of r): degree=", total_degree(g_r),
                        "  terms=", length(terms(g_r)),
                        total_degree(g_r) > 0 ? "  <-- NONTRIVIAL" : "  (unit)")
            end
        end
    catch err
        println("  prem() FAILED/skipped: ", sprint(showerror, err))
    end
    flush(stdout)

    println()
    println("=" ^ 70)
    println("PARTS A-E DIAGNOSTIC COMPLETE -- $name")
    println("Answering:")
    println("  1. Hidden factors in g1/g2?      -> see PART A/B factor() and gcd reports")
    println("  2. Redundant symmetric variables? -> see PART C term-count reduction %")
    println("  3. PRS cheaper than Bezout?       -> compare PART E single-step sizes")
    println("     against the PART D Bezout entry sizes above (~83k terms/entry)")
    println("  4. Representation change feasible? -> see PART C (symmetric basis) and")
    println("     PART B (content extraction) results together")
    println("=" ^ 70)
    flush(stdout)

    ############################################################################
    # PART F: exploit p_i in F[a1,a2] / q_j in F[b1,b2] separability.
    #
    # Section 1's fix established that g1's T-coefficients (p_0..p_4) are
    # PURELY (a1,a2)-polynomials and g2's T-coefficients (q_0..q_4) are
    # PURELY (b1,b2)-polynomials -- they were never coupled to the other
    # pair to begin with. PART D's Bezout entries came back at EXACTLY
    # 289*289 = 83521 terms, which is not incidental: since p_m and q_n
    # share no variables, p_m*q_n as a flattened polynomial has exactly
    # (#terms of p_m)*(#terms of q_n) terms with zero possible collisions
    # -- i.e. every Bezout entry [p,q]_{m,n} = p_m*q_n - p_n*q_m is really
    # a RANK-<=2 object (a difference of two outer products of coefficient
    # vectors), not a dense 4-variable polynomial. Flattening it into
    # Rcoef immediately (as bracket_num does) throws that structure away
    # and forces every downstream factor()/gcd()/prem() call to pay the
    # dense 4-variable cost.
    #
    # The fix: introduce an ABSTRACT 10-variable ring F[P0..P4,Q0..Q4]
    # (one symbol per T-coefficient of g1 and g2), build the SAME 4x4
    # Bezout matrix entirely in terms of these abstract symbols (a cheap,
    # low-degree computation -- each entry is degree 2 in the P's/Q's
    # jointly, det(B) is degree <=8 total), and substitute the real
    # (a1,a2)-polynomials for P_i / (b1,b2)-polynomials for Q_j only ONCE,
    # at the very end, via a single ring homomorphism evaluate() call.
    # This defers the expensive flattening to the last possible step
    # instead of paying it at every intermediate Bezout/PRS stage.
    ############################################################################
    println()
    println("--- PART F: abstract-variable (P,Q)-separated Bezout/resultant ---")
    println("  (exploits p_i in F[a1,a2] / q_j in F[b1,b2] confirmed by the")
    println("  Section-1 fix above; see PART D's exact 289*289=83521 entry")
    println("  term counts for the empirical signature that motivated this.)")
    flush(stdout)

    # Abstract ring: one symbol per T-coefficient of g1 (P0..P4) and g2
    # (Q0..Q4). Total degree stays tiny here (det(B) is degree <=8) no
    # matter how large the eventual a1,a2,b1,b2-substitutions are.
    Rpq, pq_gens = polynomial_ring(F, ["P0","P1","P2","P3","P4","Q0","Q1","Q2","Q3","Q4"])
    P0,P1,P2,P3,P4,Q0,Q1,Q2,Q3,Q4 = pq_gens
    Pvec = [P0,P1,P2,P3,P4]
    Qvec = [Q0,Q1,Q2,Q3,Q4]

    # Abstract bracket: [P,Q]_{m,n} := P_m*Q_n - P_n*Q_m, cheap (degree 2,
    # <=4 terms) since it's built from single symbols, not the actual
    # 289-term a/b-polynomials.
    abstract_bracket_cache = Dict{Tuple{Int,Int}, Any}()
    function abstract_bracket(m::Int, n::Int)
        key = m < n ? (m, n) : (n, m)
        if !haskey(abstract_bracket_cache, key)
            i, j = key
            abstract_bracket_cache[key] = Pvec[i+1]*Qvec[j+1] - Pvec[j+1]*Qvec[i+1]
        end
        return m < n ? abstract_bracket_cache[key] : -abstract_bracket_cache[key]
    end

    # Same 10 distinct symmetric entries as the concrete Bezout block
    # above, but now built from the cheap abstract brackets.
    Bpq = Dict{Tuple{Int,Int}, Any}()
    Bpq[(0,0)] = abstract_bracket(0,1)
    Bpq[(0,1)] = abstract_bracket(0,2)
    Bpq[(0,2)] = abstract_bracket(0,3)
    Bpq[(0,3)] = abstract_bracket(0,4)
    Bpq[(1,1)] = abstract_bracket(0,3) + abstract_bracket(1,2)
    Bpq[(1,2)] = abstract_bracket(0,4) + abstract_bracket(1,3)
    Bpq[(1,3)] = abstract_bracket(1,4)
    Bpq[(2,2)] = abstract_bracket(1,4) + abstract_bracket(2,3)
    Bpq[(2,3)] = abstract_bracket(2,4)
    Bpq[(3,3)] = abstract_bracket(3,4)
    Bpq[(1,0)] = Bpq[(0,1)]
    Bpq[(2,0)] = Bpq[(0,2)]
    Bpq[(3,0)] = Bpq[(0,3)]
    Bpq[(2,1)] = Bpq[(1,2)]
    Bpq[(3,1)] = Bpq[(1,3)]
    Bpq[(3,2)] = Bpq[(2,3)]

    println("  Abstract Bezout entries (in F[P0..P4,Q0..Q4], BEFORE substitution):")
    for i in 0:3, j in 0:3
        f = Bpq[(i,j)]
        println("    Bpq[$i,$j]: degree=", total_degree(f), "  terms=", length(terms(f)))
    end
    flush(stdout)

    # Assemble the abstract 4x4 matrix and compute its determinant --
    # this is the entire "resultant via Bezout" computation, but done
    # while every entry is still degree <=2 in 10 variables, so det()
    # only ever has to expand a determinant of small-degree polynomials,
    # never the 83521-term flattened entries.
    println("  Assembling abstract 4x4 matrix and computing det()...")
    flush(stdout)
    t0f = time()
    Bpq_mat = matrix(Rpq, [Bpq[(i,j)] for i in 0:3, j in 0:3])
    detB_abstract = det(Bpq_mat)
    el_f = time() - t0f
    println("  det(Bpq) computed in ", round(el_f, digits=3), "s: degree=",
            total_degree(detB_abstract), "  terms=", length(terms(detB_abstract)))
    flush(stdout)

    # Substitution homomorphism: P_i -> actual (a1,a2)-polynomial
    # g1_coefs_poly[i+1], Q_j -> actual (b1,b2)-polynomial
    # g2_coefs_poly[j+1]. This is the ONE place the real, large
    # coefficients ever enter the computation -- everything above this
    # line was cheap regardless of how large g1_coefs_poly/g2_coefs_poly
    # are, because it only ever manipulated the 10 abstract placeholders.
    # ------------------------------------------------------------------
    # Substitution strategy: DISK-BACKED, term-by-term.
    #
    # The single evaluate(detB_abstract, subst_vals) call OOM'd: even
    # though det(Bpq) is only 219 terms in the abstract (P,Q) symbols,
    # each term substitutes in as a product of up to 4 of the 289-term
    # p_i's (all living in the SAME 2-variable ring F[a1,a2], degree<=32
    # each) times up to 4 of the 289-term q_j's (same, in F[b1,b2]).
    # Because the p_i's share variables with each other, their product
    # doesn't blow up combinatorially the way cross-ring products do --
    # a product of 4 degree-32-in-2-variables polynomials is still only
    # a degree-<=128-in-2-variables polynomial, capped at C(128+2,2) =
    # 8385 monomials -- but the (a1,a2)-part times the (b1,b2)-part IS a
    # cross-ring product (disjoint variables, no collisions), so a single
    # substituted det() term can still have up to ~8385*8385 ~= 70
    # million monomials before any further collection. evaluate() was
    # trying to build and sum all 219 such terms simultaneously in one
    # in-memory polynomial, which is what actually exhausted RAM.
    # ------------------------------------------------------------------
    println("  Substituting real (a1,a2)/(b1,b2) coefficients into det(Bpq),",
            " term-by-term with disk-backed accumulation",
            " (single in-memory evaluate() OOM'd here previously)...")
    flush(stdout)

    subst_vals = vcat(
        g1_coefs_poly,   # P0..P4 -> p_0..p_4, already Rcoef elements (pure F[a1,a2])
        g2_coefs_poly,   # Q0..Q4 -> q_0..q_4, already Rcoef elements (pure F[b1,b2])
    )

    PARTF_SCRATCH_DIR = joinpath(@__DIR__, "part_f_scratch", name)
    mkpath(PARTF_SCRATCH_DIR)
    accum_file    = joinpath(PARTF_SCRATCH_DIR, "accum.oscar")
    accum_tmpfile = joinpath(PARTF_SCRATCH_DIR, "accum.oscar.tmp")
    progress_file = joinpath(PARTF_SCRATCH_DIR, "progress.txt")
    manifest_file = joinpath(PARTF_SCRATCH_DIR, "manifest.txt")

    detB_terms = collect(terms(detB_abstract))
    n_terms = length(detB_terms)
    println("  det(Bpq) has ", n_terms, " monomials to substitute; streaming each",
            " straight into a single running-sum file in ", PARTF_SCRATCH_DIR,
            " (no per-term files kept, so disk usage stays at ~2 polynomials'",
            " worth instead of growing with ", n_terms, ").")
    flush(stdout)

    # Streamed substitute-and-accumulate: for each monomial of
    # detB_abstract, substitute it (bounded RAM: worst case ~289^4
    # monomials before collection for a single term, same as before) and
    # immediately fold it into a running-sum polynomial that is
    # checkpointed to disk after every term. At no point do we keep more
    # than the current accumulator + the current term's substituted value
    # resident in RAM -- and on disk we keep at most the accumulator (one
    # file) plus a temp file that exists only for the duration of the
    # atomic rename below, instead of one file per term plus a full tree
    # of pairwise-merge files.
    #
    # Resumability: progress_file records how many of the n_terms
    # monomials (in the fixed order given by detB_terms) are already
    # folded into accum_file. On restart we load the existing accumulator
    # (if any) and skip exactly that many leading terms, rather than
    # re-substituting everything or tracking a directory full of files.
    t0terms = time()
    n_already_done = 0
    detB_concrete = zero(Rcoef)   # preallocated accumulator -- never replaced by
                                   # a fresh object after this; add! mutates it
                                   # in place every iteration instead of + allocating
                                   # a brand-new ~17.8M-term polynomial each time.
    if isfile(accum_file) && isfile(progress_file)
        n_already_done = parse(Int, strip(read(progress_file, String)))
        if n_already_done > 0
            println("  resuming: ", n_already_done, "/", n_terms,
                    " terms already folded into the accumulator from a",
                    " previous run.")
            loaded = load(accum_file)
            loaded_n_terms = length(loaded)
            println("  loaded checkpoint has ", loaded_n_terms, " terms;",
                    " attempting cheap coercion into Rcoef first...")
            flush(stdout)
            t0resume = time()

            # Try the cheap path first: Rcoef(loaded) is a single C-level
            # FLINT call and is FAST if the parent rings happen to be
            # compatible this time (this is not guaranteed to fail --
            # it's environment/version dependent, see comment below).
            # Only fall back to the slow, one-term-at-a-time Julia loop
            # (which was silently costing MINUTES for a multi-million-term
            # accumulator with zero progress output, and looked exactly
            # like a hang) if the fast coercion actually throws.
            local rebuilt
            try
                rebuilt = Rcoef(loaded)
                println("  cheap coercion succeeded in ",
                        round(time() - t0resume, digits=1), "s.")
            catch e
                println("  cheap coercion failed (", typeof(e), ") -- falling back",
                        " to term-by-term rebuild. This is the SLOW path: it makes",
                        " one push_term! call per term (", loaded_n_terms, " total",
                        " here), each a separate FFI call into FLINT with no",
                        " batching -- for a multi-million-term polynomial this can",
                        " legitimately take minutes with NO progress output,",
                        " which is exactly what looked like a hang before this",
                        " message was added. Printing progress every 500k terms",
                        " so it's visible instead of silent:")
                flush(stdout)
                # save()/load() does not guarantee returning a polynomial in
                # the IDENTICAL Rcoef parent object (even though it's the
                # same ring mathematically) -- Nemo's coercion, R(other_poly),
                # is stricter than that and can throw "Unable to coerce
                # polynomial". Sidestep coercion entirely: rebuild the
                # loaded polynomial term-by-term straight into Rcoef's own
                # generators, the same MPolyBuildCtx/push_term!/finish
                # pattern used by remap_to_final elsewhere in this file.
                # Generator order is identity here (both rings are Rcoef's
                # own [a1,a2,b1,b2] declared order), so no gen_map is needed.
                rebuild_ctx = MPolyBuildCtx(Rcoef)
                n_pushed = 0
                t0rebuild = time()
                for (c, exps) in zip(coefficients(loaded), AbstractAlgebra.exponent_vectors(loaded))
                    push_term!(rebuild_ctx, F(c), exps)
                    n_pushed += 1
                    if n_pushed % 500_000 == 0
                        println("    rebuilt ", n_pushed, "/", loaded_n_terms,
                                " terms (", round(time() - t0rebuild, digits=1), "s elapsed)")
                        flush(stdout)
                    end
                end
                rebuilt = finish(rebuild_ctx)
                println("  term-by-term rebuild complete: ", n_pushed, " terms in ",
                        round(time() - t0rebuild, digits=1), "s.")
            end
            flush(stdout)

            # Rebuild directly into detB_concrete's ring (Rcoef). This
            # runs once (not per-term), so there's no performance reason
            # to use add! here -- detB_concrete is still zero(Rcoef) at
            # this point, so plain assignment is exact and unambiguous.
            detB_concrete = rebuilt
            println("  resume rebuild total: ", round(time() - t0resume, digits=1), "s.")
        end
    end

    # Detect once, outside the hot loop, whether this Nemo/AbstractAlgebra
    # install actually supports in-place add! on Rcoef elements (some
    # versions/ring types silently fall back to allocating regardless, in
    # which case applicable() below will just be false and we use plain +
    # -- correctness never depends on this, only speed).
    #
    # Separately verify SELF-ALIASED add!(a, a, c) actually produces the
    # right numeric result, not just that the method exists -- some
    # AbstractAlgebra in-place implementations only support add!(a, b, c)
    # for a distinct from b/c, and silently misbehave (not error) if a
    # aliases one of its inputs. This is checked ONCE with tiny throwaway
    # values, never against the real 17.8M-term accumulator, so it's
    # cheap and safe to always run.
    HAVE_INPLACE_ADD = applicable(add!, detB_concrete, detB_concrete, detB_concrete)
    HAVE_SAFE_SELF_ALIAS_ADD = false
    if HAVE_INPLACE_ADD
        _probe = Rcoef(gens(Rcoef)[1])          # tiny throwaway: just "a1"
        _probe_expected = _probe + _probe        # == 2*a1, via plain +
        _probe_copy = deepcopy(_probe)
        add!(_probe_copy, _probe_copy, _probe)
        HAVE_SAFE_SELF_ALIAS_ADD = (_probe_copy == _probe_expected)
    end

    if HAVE_SAFE_SELF_ALIAS_ADD
        println("  in-place add! (self-aliased) verified correct for Rcoef",
                " elements -- accumulator will be mutated in place each",
                " term (no full reallocation).")
    elseif HAVE_INPLACE_ADD
        println("  add! exists but self-aliased add!(a,a,c) did NOT match",
                " plain + on a probe value -- NOT safe to use here.",
                " Falling back to + (correct, but each fold reallocates",
                " the full accumulator).")
    else
        println("  in-place add! NOT available for Rcoef elements on this",
                " Nemo/AbstractAlgebra version -- falling back to +",
                " (correct, but each fold reallocates the full accumulator).")
    end
    flush(stdout)

    # NOTE on GC instrumentation: Base.gc_num() was tried here first and
    # proved UNRELIABLE for this workload -- it reported NEGATIVE bytes
    # allocated in a live run (-0.52 GB, -0.35 GB), which happens because
    # FLINT/Nemo mpoly data lives in C-allocated memory that Julia's GC
    # does not track at all; gc_num() only sees the thin Julia-side
    # wrapper, not the actual multi-GB polynomial backing storage. Since
    # GC time was also negligible (0.3-1.2s) while ~40s/iteration stayed
    # unaccounted, GC is RULED OUT. Replaced with direct RSS (resident
    # set size) sampling from /proc/self/status, which reflects actual
    # process memory regardless of which allocator (Julia GC or FLINT's
    # own malloc) is responsible -- this will show whether the missing
    # time correlates with memory growth (consistent with FLINT
    # allocating/copying large buffers) or not (pointing elsewhere, e.g.
    # disk cache eviction pressure from the save() calls).
    function read_rss_mb()
        for line in eachline("/proc/self/status")
            if startswith(line, "VmRSS:")
                # format: "VmRSS:	 1234567 kB"
                parts = split(line)
                return parse(Int, parts[2]) / 1024.0   # kB -> MB
            end
        end
        return -1.0
    end

    max_term_size_seen = 0
    max_term_size_idx = 0
    for (i, t) in enumerate(detB_terms)
        if i <= n_already_done
            continue   # already folded into detB_concrete in a previous run
        end
        t0iter = time()
        rss_before = read_rss_mb()

        t0eval = time()
        # ------------------------------------------------------------
        # CHUNKED substitution (fixes the OOM from evaluate(t, subst_vals)).
        #
        # A single term t of detB_abstract is a monomial in P0..P4,Q0..Q4,
        # e.g. coeff * P_i1*P_i2 * Q_j1*Q_j2 (up to 4 P's and 4 Q's,
        # since det(Bpq) is degree <=8 total and each abstract_bracket
        # entry mixes P's and Q's). Substituting P_k -> p_k (a
        # ~289-term poly in F[a1,a2]) and Q_k -> q_k (a ~289-term poly
        # in F[b1,b2]) and calling evaluate() on the WHOLE monomial at
        # once forces Nemo to build the FULL cross product -- up to
        # ~8385*8385 ~= 70 million monomials -- as one single
        # intermediate polynomial before any collection/addition
        # happens. That intermediate is what exhausted RAM; it was
        # never kept, only the (smaller) sum, but building it even
        # transiently requires having all 70M terms live in memory
        # simultaneously.
        #
        # Fix: exploit exactly the disjoint-variable structure the
        # PART F comment above already identified. Split the term's
        # exponent vector into its P-part and Q-part, compute:
        #   a_side = product of the p_k's raised to their P-exponents
        #            (pure F[a1,a2] arithmetic, capped at ~8385 terms)
        #   b_side = product of the q_k's raised to their Q-exponents
        #            (pure F[b1,b2] arithmetic, capped at ~8385 terms)
        # separately -- each of these is cheap and bounded. Then fold
        # coeff * a_side * b_side into the accumulator NOT as one
        # multiply, but by walking a_side in small term-batches
        # (PARTF_CHUNK terms at a time), multiplying each batch by the
        # full b_side (a batch of <=PARTF_CHUNK terms times an
        # <=8385-term poly is at most PARTF_CHUNK*8385 monomials, not
        # 8385*8385), and add!-ing each partial product straight into
        # detB_concrete before moving to the next batch. At no point
        # do we hold more than one chunk's worth of the cross product
        # in memory -- the full a_side*b_side product is never
        # materialized as a single object.
        # ------------------------------------------------------------
        t_exps = first(AbstractAlgebra.exponent_vectors(t))
        t_coeff = first(coefficients(t))

        a_side = one(Rcoef)
        b_side = one(Rcoef)
        for k in 1:5
            ePk = t_exps[k]        # exponent of P_{k-1} in this monomial
            eQk = t_exps[5 + k]    # exponent of Q_{k-1} in this monomial
            if ePk > 0
                a_side = a_side * (g1_coefs_poly[k]^ePk)
            end
            if eQk > 0
                b_side = b_side * (g2_coefs_poly[k]^eQk)
            end
        end
        a_side = t_coeff * a_side   # fold the term's scalar coefficient into the (smaller) a-side

        this_size = length(terms(a_side)) * length(terms(b_side))   # worst-case bound, for reporting only
        if this_size > max_term_size_seen
            global max_term_size_seen = this_size
            global max_term_size_idx = i
        end

        # PARTF_CHUNK terms per batch, on BOTH sides. Previously only
        # a_side was chunked (PARTF_CHUNK terms) while b_side was kept
        # whole (up to ~8385 terms) and multiplied against each a-chunk
        # in full -- so each partial product could still be up to
        # PARTF_CHUNK*8385 (~1.7M) monomials before collection, and with
        # a_side/b_side each capable of reaching that ~8385-term bound
        # independently (not just in the worst case Claire's original
        # comment sized for), that was the actual OOM source, not just
        # the single-shot evaluate() this loop already replaced. Nesting
        # the chunking on both sides bounds every single cross-product
        # batch to at most PARTF_CHUNK*PARTF_CHUNK monomials, independent
        # of how large a_side/b_side get.
        PARTF_CHUNK = 200   # terms per batch per side; tune down further if RSS still climbs
        a_terms = collect(terms(a_side))
        b_terms = collect(terms(b_side))
        n_a_terms = length(a_terms)
        n_b_terms = length(b_terms)
        a_chunk_start = 1
        while a_chunk_start <= n_a_terms
            a_chunk_end = min(a_chunk_start + PARTF_CHUNK - 1, n_a_terms)
            a_chunk = sum(a_terms[a_chunk_start:a_chunk_end]; init=zero(Rcoef))
            b_chunk_start = 1
            while b_chunk_start <= n_b_terms
                b_chunk_end = min(b_chunk_start + PARTF_CHUNK - 1, n_b_terms)
                b_chunk = sum(b_terms[b_chunk_start:b_chunk_end]; init=zero(Rcoef))
                partial = a_chunk * b_chunk
                if HAVE_SAFE_SELF_ALIAS_ADD
                    add!(detB_concrete, detB_concrete, partial)
                else
                    global detB_concrete = detB_concrete + partial
                end
                partial = nothing
                b_chunk = nothing
                b_chunk_start = b_chunk_end + 1
            end
            a_chunk = nothing
            a_chunk_start = a_chunk_end + 1
        end
        a_side = nothing
        b_side = nothing
        a_terms = nothing   # drop references explicitly before the timed GC sweep below
        b_terms = nothing
        el_eval = time() - t0eval
        rss_after_eval = read_rss_mb()

        t0fold = time()
        # Folding now happens inside the chunk loop above (one add! per
        # chunk rather than one add! for the whole term), so this stage
        # is a no-op left in place only so the existing timing/RSS
        # instrumentation below still has a well-defined (zero-length)
        # "fold" phase to report -- the real fold cost is now counted
        # inside el_eval, which is the honest place for it to live given
        # it's now interleaved with the substitution.
        el_fold = time() - t0fold
        rss_after_fold = read_rss_mb()

        # Force one full collection here, now that this term's a_side/
        # b_side/a_terms/each chunk's partial product are all
        # unreachable (each chunk is already dropped inside the loop
        # above, but a_side/b_side/a_terms themselves are only freed
        # once the whole term is done). This turns what would otherwise
        # be unpredictable incremental GC pauses scattered through the
        # NEXT term's chunk loop into one accounted-for sweep here,
        # timed separately so it shows up explicitly instead of as
        # "unaccounted" wall-clock.
        t0gc = time()
        GC.gc(false)   # false = not full/aggressive; just reclaim what's already dead
        el_gc = time() - t0gc
        rss_after_gc = read_rss_mb()

        # Checkpoint: write to a temp file, then atomically rename over
        # the real accumulator file, then update the progress counter.
        # A crash mid-write leaves the OLD accum_file (and old
        # progress_file, still saying i-1) intact -- never a half-written
        # accumulator that progress_file claims is complete. Only one
        # accumulator's worth of data ever sits on disk at a time.
        #
        # NOTE: save() serializes the WHOLE accumulator (detB_concrete),
        # not just this term's contribution -- its cost and transient
        # memory overhead scale with the accumulator's CURRENT size, which
        # only grows as the loop progresses. Doing this every single term
        # (as originally written) means paying an ever-increasing cost 219
        # times over on an ever-larger polynomial, which was a second,
        # independent OOM source on top of the unchunked b_side fixed
        # above -- by the later terms (e.g. resuming at 72/219) the
        # accumulator itself may already be too large to serialize
        # cheaply. Checkpoint only every PARTF_CHECKPOINT_EVERY terms (and
        # always on the final term) instead; resumability is preserved
        # since progress_file/accum_file are only ever updated together
        # (same crash-safety guarantee, just less often), the only change
        # is that a crash between checkpoints re-does up to
        # PARTF_CHECKPOINT_EVERY terms of substitution work, which is
        # cheap relative to a save() of a multi-GB polynomial.
        #
        # Each sub-step timed separately -- in particular mv() is only a
        # fast atomic rename if accum_tmpfile and accum_file are on the
        # SAME filesystem; if PARTF_SCRATCH_DIR straddles a filesystem
        # boundary (e.g. tmp on one mount, scratch dir on another), Julia
        # silently falls back to a full copy+delete for mv(), which for a
        # large accumulator can take much longer than the save() itself
        # and would otherwise show up as unexplained missing time.
        PARTF_CHECKPOINT_EVERY = 5   # terms between checkpoints; lower if a crash near the end of a run is costing too much re-work, raise if save() itself is still RAM-heavy at this cadence
        do_checkpoint = (i % PARTF_CHECKPOINT_EVERY == 0) || (i == n_terms)

        local el_write, el_mv, el_prog, rss_after_save
        if do_checkpoint
            t0write = time()
            save(accum_tmpfile, detB_concrete)
            el_write = time() - t0write

            t0mv = time()
            mv(accum_tmpfile, accum_file; force=true)
            el_mv = time() - t0mv

            t0prog = time()
            open(progress_file, "w") do io
                print(io, i)
            end
            el_prog = time() - t0prog

            rss_after_save = read_rss_mb()
        else
            el_write = 0.0
            el_mv = 0.0
            el_prog = 0.0
            rss_after_save = rss_after_gc
        end

        el_save = el_write + el_mv + el_prog
        el_iter_measured = el_eval + el_fold + el_gc + el_save
        el_iter_actual = time() - t0iter
        el_unaccounted = el_iter_actual - el_iter_measured

        if el_eval > 2.0 || el_fold > 2.0 || el_gc > 2.0 || el_save > 2.0 || el_unaccounted > 2.0 || i <= 3
            println("      term ", i, " breakdown -- evaluate: ", round(el_eval, digits=1),
                    "s  fold(add!): ", round(el_fold, digits=1),
                    "s  gc(explicit): ", round(el_gc, digits=1),
                    "s  save(write): ", round(el_write, digits=1),
                    "s  mv(rename): ", round(el_mv, digits=1),
                    "s  progress-write: ", round(el_prog, digits=1),
                    "s  || measured total: ", round(el_iter_measured, digits=1),
                    "s  actual wall-clock: ", round(el_iter_actual, digits=1),
                    "s  UNACCOUNTED: ", round(el_unaccounted, digits=1), "s",
                    el_unaccounted > 2.0 ? "  <<<< still-unexplained gap" : "")
            println("        RSS (resident memory, MB) -- before iter: ", round(rss_before, digits=0),
                    "  after evaluate: ", round(rss_after_eval, digits=0),
                    " (Δ", round(rss_after_eval - rss_before, digits=0), ")",
                    "  after fold: ", round(rss_after_fold, digits=0),
                    " (Δ", round(rss_after_fold - rss_after_eval, digits=0), ")",
                    "  after gc: ", round(rss_after_gc, digits=0),
                    " (Δ", round(rss_after_gc - rss_after_fold, digits=0), ")",
                    "  after save: ", round(rss_after_save, digits=0),
                    " (Δ", round(rss_after_save - rss_after_gc, digits=0), ")")
            println("        (Note: Base.gc_num()-based instrumentation was tried",
                    " and abandoned -- it reported NEGATIVE bytes allocated for",
                    " this workload because FLINT/Nemo mpoly data lives in",
                    " C-allocated memory outside Julia's GC accounting. RSS",
                    " above reflects the OS's view of actual process memory",
                    " regardless of which allocator is responsible, and is the",
                    " ground truth for where the unaccounted time correlates",
                    " with memory growth.)")
            flush(stdout)
        end

        if i % 10 == 0 || i == n_terms
            println("    folded term ", i, "/", n_terms,
                    " (this term=", this_size, " terms, largest so far=term ",
                    max_term_size_idx, " w/ ", max_term_size_seen, " terms,",
                    " running total=", length(terms(detB_concrete)), " terms) -- ",
                    round(time() - t0terms, digits=1), "s elapsed")
            flush(stdout)
        end
    end
    el_sub = time() - t0terms
    println("  all ", n_terms, " terms substituted and accumulated (disk-backed,",
            " streamed, one checkpoint file) in ", round(el_sub, digits=1),
            "s this run.")
    flush(stdout)

    println("  substitution done (disk-backed, streamed): degree=",
            total_degree(detB_concrete), "  terms=", length(terms(detB_concrete)),
            "  (", round(el_sub, digits=1), "s total this run)")
    flush(stdout)

    # Record the manifest so a subsequent run (or a human) can tell at a
    # glance that this result came from the disk-backed path and where
    # the checkpoint file lives, without needing to re-derive it.
    open(manifest_file, "w") do io
        println(io, "PART F disk-backed substitution manifest for $name")
        println(io, "n_terms = $n_terms")
        println(io, "final result file = $accum_file")
        println(io, "final degree = ", total_degree(detB_concrete))
        println(io, "final terms  = ", length(terms(detB_concrete)))
    end

    # Cross-check against the concrete (already-flattened) Bezout matrix
    # built above: det(B) via the abstract route should agree exactly
    # with det() computed directly on the concrete B, since it's the
    # same matrix. HOWEVER: det(B_mat_concrete) is exactly the dense,
    # single-shot computation that OOM'd in the first place (it has to
    # internally build and sum the same huge products the disk-backed
    # path above was written to avoid) -- so it is NOT run by default.
    # Gate it behind an explicit opt-in, same pattern as
    # RUN_FULL_RESULTANT below, so re-confirming correctness on a
    # machine with enough RAM is a deliberate choice, not something that
    # silently reproduces the crash every run.
    RUN_PARTF_DIRECT_CROSSCHECK = get(ENV, "ELIM2_PARTF_DIRECT_CROSSCHECK", "false") == "true"
    if @isdefined(B) && RUN_PARTF_DIRECT_CROSSCHECK
        println("  Cross-checking against det() of the concrete (pre-flattened) B...")
        println("  (ELIM2_PARTF_DIRECT_CROSSCHECK=true -- this repeats the dense,",
                " single-shot computation the disk-backed path exists to avoid;",
                " only run this with enough RAM headroom.)")
        flush(stdout)
        t0chk = time()
        B_mat_concrete = matrix(Rcoef, [B[(i,j)] for i in 0:3, j in 0:3])
        detB_direct = det(B_mat_concrete)
        el_chk = time() - t0chk
        agrees = detB_concrete == detB_direct
        println("  det(B) computed directly in ", round(el_chk, digits=3), "s: degree=",
                total_degree(detB_direct), "  terms=", length(terms(detB_direct)))
        println("  AGREES with abstract-route result? ", agrees,
                agrees ? "" : "   <<<< MISMATCH -- reordering bug, do not trust PART F result")
        flush(stdout)
    elseif @isdefined(B)
        # Cheap partial correctness signal instead: re-derive a handful
        # of individual concrete Bezout entries (already computed as B[..]
        # above, at ~83521 terms each -- NOT re-flattening the whole
        # determinant) via the abstract-bracket substitution route, and
        # confirm they agree entry-by-entry. This is orders of magnitude
        # cheaper than det() on the full matrix (it's just re-checking
        # the entries, which were already built and paid for above),
        # while still directly testing whether evaluate() on a single
        # abstract bracket matches the concrete bracket_num() path.
        println("  Skipping full det(B) cross-check (set ",
                "ELIM2_PARTF_DIRECT_CROSSCHECK=true to enable -- expensive,",
                " dense, same computation that OOM'd before). Running a",
                " cheaper per-entry spot-check instead:")
        flush(stdout)
        n_mismatch = 0
        for (i, j) in [(0,0), (1,2), (2,3), (3,3)]
            abstract_entry_concrete = evaluate(Bpq[(i,j)], subst_vals)
            same = abstract_entry_concrete == B[(i,j)]
            global n_mismatch += !same
            println("    entry ($i,$j): abstract-route == concrete B[$i,$j]? ", same)
        end
        println("    spot-check: ", n_mismatch == 0 ? "all entries agree" :
                "$n_mismatch MISMATCH(es) -- investigate before trusting PART F result")
        flush(stdout)
    else
        println("  (concrete B not available for cross-check in this branch)")
    end

    println("  PART F summary: det(Bpq) computed as a degree<=8 polynomial in",
            " 10 abstract symbols, THEN substituted once, instead of building")
    println("  and manipulating dense ", nvars(Rcoef), "-variable ", 83521,
            "-term entries at every intermediate step.")
    flush(stdout)
    ############################################################################
    # END PART F
    ############################################################################
end

################################################################################
# RESULTANT COMPUTATION -- gated behind an explicit flag.
#
# Per the diagnostic-first request, the actual resultant(g1_T,g2_T) call
# (subresultant PRS over Kcoef, previously ran unconditionally and was
# the call that hung for ~an hour) is NOT run automatically anymore.
# Set RUN_FULL_RESULTANT = true below (or via ENV) once PARTS A-E above
# have been read and a decision has been made on which algorithm/
# representation to actually commit to.
################################################################################

const RUN_FULL_RESULTANT = get(ENV, "ELIM2_RUN_FULL_RESULTANT", "false") == "true"

if !RUN_FULL_RESULTANT
    println()
    println("Skipping full resultant(g1_T, g2_T) computation (RUN_FULL_RESULTANT=false).")
    println("Set ENV[\"ELIM2_RUN_FULL_RESULTANT\"] = \"true\" to run it after reviewing ",
            "the PARTS A-E diagnostic above.")
    flush(stdout)
    exit(0)
end

println("    computing resultant via subresultant PRS (degree-in-T = $d1T, $d2T)...")
flush(stdout)
t0 = time()
res_frac = resultant(g1_T, g2_T)
elapsed = time() - t0
println("    resultant computed in ", round(elapsed, digits=3), "s")

# res_frac lives in Kcoef = Frac(F[a1,a2,b1,b2]); the true resultant of
# two polynomials with polynomial (not just rational) coefficients is
# itself a polynomial (no cryptographically-relevant denominator can
# survive -- Sylvester-matrix entries were already polynomials, and the
# determinant of a polynomial matrix is a polynomial), so we expect
# denominator(res_frac) to be a unit. Confirm rather than assume: if
# it's not a unit, something upstream (e.g. an unintended common factor
# introduced during the coefficient lift) needs inspection, but the
# resultant computation itself is already done at this point regardless.
res_num = numerator(res_frac)
res_den = denominator(res_frac)

if !is_unit(res_den)
    println("    WARNING: resultant denominator is not a unit (degree=",
            total_degree(res_den), "); this should not happen for a "
            * "genuine polynomial-coefficient resultant -- inspect "
            * "coefficient lift for spurious common factors.")
end

result_poly = Rcoef(res_num) // Rcoef(res_den)   # keep as exact fraction; typically res_den is a unit and this collapses to a polynomial

println("    $name resultant: total_degree=", total_degree(res_num),
        "  terms=", length(terms(res_num)))

# Save straight into the same place the old per-summand harness would
# have written its final assembled term, so downstream code that reads
# "the U0 resultant" doesn't need to change.
const RESULTANT_FILE = joinpath(@__DIR__, "part_k_results", "$(name)_resultant.oscar")
mkpath(dirname(RESULTANT_FILE))
save(RESULTANT_FILE, res_num)
println("    saved resultant -> ", RESULTANT_FILE)

################################################################################
# Everything below this point in the old file -- next_permutation!,
# first_k_permutations, first_k_nonzero_permutations,
# count_nonzero_permutations, the PART_K_MAX_WORKERS subprocess pool,
# part_k_launch/part_k_harvest/part_k_summand_complete, and the entire
# "keep computing summands until one dies" driver loop -- is now
# unnecessary and should be deleted. None of that machinery is wrong,
# exactly -- it correctly identifies which Leibniz summands are nonzero
# and safely isolates OOM crashes -- it is just solving a problem
# (surviving Leibniz expansion of an 8x8 determinant with huge entries)
# that a proper resultant algorithm avoids needing to solve at all.
################################################################################
