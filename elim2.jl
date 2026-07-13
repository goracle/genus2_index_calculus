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

# This is our factory. It takes a raw tower coefficient, builds a 5-variable ring, and eliminates the w's.
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
    
    # 5. Eliminate the w's!
    I_small = ideal(R_small, [h_s, curve1, curve2])
    eliminated_ideal = eliminate(I_small, [w1, w2])
    
    # Return the winning polynomial
    return gens(eliminated_ideal)[1]
end

# Let's test the factory on the very first coefficient!
test_result = process_sample_1_coeff(res1.u_RS_coeffs[1], "U0")
println("Factory Test Successful! Resulting polynomial has degree: ", total_degree(test_result))
println()


# ==============================================================================
# Factory for Sample 2 (Uses 'b' variables instead of 'a')
# ==============================================================================
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
    
    # 5. Eliminate the w's!
    I_small = ideal(R_small, [h_s, curve1, curve2])
    eliminated_ideal = eliminate(I_small, [w1, w2])
    
    return gens(eliminated_ideal)[1]
end

println("===========================================================")
println("PART J: The Assembly Line (Processing All Coefficients)")
println("===========================================================")

# These arrays will hold our final, clean polynomials
clean_sample_1 = Any[]
clean_sample_2 = Any[]

# 1. Loop through the 'u' coefficients
# (We skip the very last one because it's just a trivial leading "1")
num_u_coeffs = length(res1.u_RS_coeffs) - 1

for i in 1:num_u_coeffs
    target = "U$(i-1)"
    push!(clean_sample_1, process_sample_1_coeff(res1.u_RS_coeffs[i], target))
    push!(clean_sample_2, process_sample_2_coeff(res2.u_RS_coeffs[i], target))
end

# 2. Loop through the 'v' coefficients
num_v_coeffs = length(res1.v_RS_coeffs)

for i in 1:num_v_coeffs
    target = "V$(i-1)"
    push!(clean_sample_1, process_sample_1_coeff(res1.v_RS_coeffs[i], target))
    push!(clean_sample_2, process_sample_2_coeff(res2.v_RS_coeffs[i], target))
end

println("\nAssembly Line Finished!")
println("Sample 1 produced ", length(clean_sample_1), " clean polynomials.")
println("Sample 2 produced ", length(clean_sample_2), " clean polynomials.")

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

const RESULTS_DIR = joinpath(@__DIR__, "part_k_results")
mkpath(RESULTS_DIR)

function save_poly(label::String, g)
    path = joinpath(RESULTS_DIR, "$label.txt")
    open(path, "w") do io
        println(io, "# $label  degree=", total_degree(g), "  terms=", length(terms(g)))
        println(io, g)
    end
    println("    wrote ", path)
end

# One target variable at a time: [name, sample1_eq_index, sample2_eq_index, T_gen]
const TARGETS = [
    ("U0", 1, 5, U0_f),
    ("U1", 2, 6, U1_f),
    ("V0", 3, 7, V0_f),
    ("V1", 4, 8, V1_f),
]

final_polys = Any[]

for (name, i1, i2, Tvar) in TARGETS
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
        println("    *** WARNING: $name does not actually appear in one side; ",
                "resultant would be degenerate. Skipping -- inspect final_equations ",
                "construction before proceeding. ***")
        continue
    end

    println("    computing $name via fiber-product elimination (small ring)...")
    flush(stdout)
    t0 = time()

    # FIBER-PRODUCT FIX (replaces both earlier attempts):
    #   1. eliminate(ideal(g1,g2), [T]) directly in the full 8-var R_final
    #      OOM'd with no diagnostics (see comment above) -- too many
    #      irrelevant variables (a2,b1,b2 etc. that g1 doesn't even use)
    #      dragging the Groebner computation's ambient ring along for
    #      the ride.
    #   2. resultant(g1, g2, U0) assumed g1,g2 were degree<=1 in U0
    #      (true of h_s = T*den-num at CONSTRUCTION time in Part I/J's
    #      process_sample_*_coeff) but that assumption doesn't survive
    #      eliminate(I_small, [w1,w2])'s own Groebner computation --
    #      w1,w2 satisfy degree-2 relations that couple back into T, so
    #      the RETURNED generator can be (and is: degree-in-U0=4) higher
    #      degree in T than the input h_s was. So resultant(g1,g2,U0) is
    #      an honest 8x8 Sylvester determinant, not a cheap 2x2 one --
    #      exactly the swell estimated in chat before this fix.
    #
    #   Fix: g1 only involves (a1,a2,T); g2 only involves (b1,b2,T) --
    #   confirmed by PART A's "vars-used" printout on the analogous
    #   Fu_decoupled generators. So build a genuinely small ring with
    #   ONLY those 5 variables (not all 8 of R_final) and eliminate T
    #   there via a Groebner ideal -- the exact same shape that
    #   succeeded in PART H (5-variable ring, eliminate 2 unknowns from
    #   a 3-generator ideal, ~1-8s). Here we eliminate 1 unknown (T)
    #   from a 2-generator ideal in a 5-variable ring, which is strictly
    #   smaller/easier than anything PART H already proved safe.
    Rfp, (a1_fp, a2_fp, b1_fp, b2_fp, T_fp) =
        polynomial_ring(F, ["a1", "a2", "b1", "b2", string(name)])

    # clean_sample_1[i1] lives in its OWN 5-variable ring [wa1,wa2,a1,a2,T]
    # (per process_sample_1_coeff's polynomial_ring call) -- eliminate()
    # does not shrink the generator list, it just zeroes out wa1,wa2's
    # degree in the returned polynomial (confirmed directly in PART H's
    # own printed "parent ring = ...5 variables..." after eliminating 2
    # of those 5). So the correct gen_map sends wa1,wa2 (indices 1,2) to
    # 0 -- remap_to_final's own assertion will fail loudly if that's
    # wrong, i.e. if wa1/wa2 turn out to have nonzero exponent somewhere,
    # rather than silently dropping real content -- and a1,a2,T to their
    # Rfp positions.
    #
    # BUG FIX: remap_to_final's n_out is length(final_gens) -- it needs
    # the TARGET ring's FULL generator list (all 5 of Rfp's gens, in
    # Rfp's own order [a1_fp,a2_fp,b1_fp,b2_fp,T_fp]), not just the 3
    # generators this particular source polynomial happens to use. Using
    # a 3-element final_gens made n_out=3 while T_fp's real position in
    # the 5-variable Rfp is index 5, producing a 3-long exponent vector
    # pushed into a 5-variable ring -- exactly the crash seen. gen_map
    # must likewise index into that same full 5-slot target list.
    rfp_gens = [a1_fp, a2_fp, b1_fp, b2_fp, T_fp]
    g1_fp = remap_to_final(clean_sample_1[i1], rfp_gens,
                            [0, 0, 1, 2, 5])   # wa1,wa2->0; a1->1; a2->2; T->5
    g2_fp = remap_to_final(clean_sample_2[i2], rfp_gens,
                            [0, 0, 3, 4, 5])   # wb1,wb2->0; b1->3; b2->4; T->5

    println("      g1 remapped into 5-var fiber-product ring: degree=",
            total_degree(g1_fp), " terms=", length(terms(g1_fp)))
    println("      g2 remapped into 5-var fiber-product ring: degree=",
            total_degree(g2_fp), " terms=", length(terms(g2_fp)))

    Ifp = ideal(Rfp, [g1_fp, g2_fp])

    local r, elapsed
    resultFP, statusFP, elapsedFP = run_with_timeout(SUBIDEAL_TIMEOUT_SECS) do
        eliminate(Ifp, [T_fp])
    end

    if statusFP != :ok
        error("fiber-product eliminate() for $name failed: status=$statusFP " *
              "after $(round(elapsedFP, digits=3))s. Inspect g1_fp/g2_fp above " *
              "(degree/terms) before re-running -- if these are much larger " *
              "than PART A's Fu_decoupled sizes (degree 17, 306 terms), the " *
              "swell happened upstream in process_sample_*_coeff's own " *
              "eliminate() call, not here.")
    end

    gFP = gens(resultFP)
    if length(gFP) == 0
        error("fiber-product eliminate() for $name returned ZERO generators " *
              "-- g1_fp, g2_fp share no common consequence after eliminating " *
              "$name, which likely means a construction bug (wrong variable " *
              "remap) rather than a genuine mathematical outcome. Inspect " *
              "gen_map values above before trusting this.")
    end
    r = gFP[1]
    elapsed = elapsedFP

    println("    done in ", round(elapsed, digits=3), "s: degree=", total_degree(r),
            "  terms=", length(terms(r)), "  vars=", vars(r))

    if iszero(r)
        println("    *** WARNING: fiber-product elimination result is IDENTICALLY ",
                "ZERO -- g1_fp,g2_fp share a common factor involving $name, or a ",
                "construction bug. Inspect before trusting downstream results. ***")
    end

    save_poly(name, r)
    push!(final_polys, r)
    println()
end

println("\nFinal un-coupled polynomials linking a and b:")
println("Found ", length(final_polys), " final equation(s) (", length(TARGETS) - length(final_polys),
        " skipped -- see warnings above if nonzero).")
for (i, p) in enumerate(final_polys)
    println("  Final Eq $i: degree=", total_degree(p), " terms=", length(terms(p)))
end
println("\nResults also written to ", RESULTS_DIR, "/ as each one finished.")
println()
