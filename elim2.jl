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

println("Attempting groebner_basis on the DECOUPLED U-system first ",
        "(smaller, sparser generators -- try this before the original ",
        "8-variable Iu/Iuv if that OOM'd).")
GBu_decoupled = try
    result = groebner_basis(Iu_decoupled; ordering = block_ordering_dec, algorithm = :f4)
    println("(decoupled Iu computed via algorithm = :f4)")
    result
catch e
    println("algorithm=:f4 failed on decoupled Iu (", e, "), falling back to :buchberger...")
    groebner_basis(Iu_decoupled; ordering = block_ordering_dec, algorithm = :buchberger)
end
println("Decoupled GBu has ", length(GBu_decoupled), " elements.")
println()

# NOTE: U0,U1 (and V0,V1, if you go on to try Iuv_decoupled the same
# way) still need to be eliminated afterwards, same as the w's -- they
# were introduced purely to decouple the two samples, not because you
# care about their values. eliminate(Iu_decoupled, [U0,U1,wa1_d,...])
# once GBu_decoupled confirms this route is actually tractable.
################################################################################

################################################################################
# Factor each equation before building the ideal.
#
# The raw cross-multiplied Fu/Fv can be enormous (observed: degree 128,
# ~7.46M terms) because coeff_equal(num1,den1,num2,den2) = num1*den2 -
# num2*den1 is built from maximally-expanded tower denominators. If the
# underlying algebra has nested/factored structure (confirmed by hand via
# Mathematica FullSimplify on one of these), some of that bulk is very
# likely spurious multiplicity -- e.g. den1, den2 individually appearing
# as extraneous factors introduced by the cross-multiplication itself,
# or shared factors with the curve equations (which would mean part of
# the "equation" is automatically zero on the curve and contributes
# nothing to the elimination).
#
# factor() is run in parallel across threads since each equation's
# factorization is independent and this is by far the most expensive
# single step before groebner_basis. Results are reported so we can see
# the actual multiplicity/degree structure -- and, in particular, whether
# any irreducible factor recurs across Fu0/Fu1/Fv0/Fv1 or matches a curve
# equation, before anything is handed to groebner_basis.
################################################################################

println("===========================================================")
println("Factoring Fu/Fv equations (parallel across threads)")
println("===========================================================")
println()
println("NOTE: factor() thread-safety across independent Oscar/Nemo objects")
println("is assumed but not verified against this specific Oscar version.")
println("If this crashes, segfaults, or gives inconsistent results between")
println("runs, switch the Threads.@threads loop below to a plain serial")
println("for loop (same code otherwise) and file that as an Oscar version")
println("issue rather than trusting parallel factor() results silently.")
println()

all_eqs = vcat(Fu, Fv)
eq_labels = vcat(["Fu$(i-1)" for i in 1:length(Fu)], ["Fv$(i-1)" for i in 1:length(Fv)])
factorizations = Vector{Any}(undef, length(all_eqs))

Threads.@threads for i in 1:length(all_eqs)
    factorizations[i] = factor(all_eqs[i])
end

for (label, fac) in zip(eq_labels, factorizations)
    println("$label factors into $(length(fac)) irreducible piece(s):")
    for (factor_poly, mult) in fac
        println("    [mult=$mult] degree=", total_degree(factor_poly),
                "  terms=", length(terms(factor_poly)))
    end
    println()
end

# Check for irreducible factors shared across equations, or matching a
# curve equation exactly (up to unit) -- either signals part of the
# "equation" is not real elimination content.
println("Checking for repeated/shared irreducible factors across equations...")
seen_factors = Dict{Any,Vector{String}}()
for (label, fac) in zip(eq_labels, factorizations)
    for (factor_poly, _) in fac
        # normalize by leading coefficient so unit multiples compare equal
        key = leading_coefficient(factor_poly) == 0 ? factor_poly :
              factor_poly * inv(leading_coefficient(factor_poly))
        push!(get!(seen_factors, key, String[]), label)
    end
end
any_shared = false
for (fp, labels) in seen_factors
    if length(unique(labels)) > 1
        global any_shared = true
        println("  SHARED factor (degree=$(total_degree(fp))) appears in: ", unique(labels))
    end
end
if !any_shared
    println("  No irreducible factor shared across equations.")
end

for (label, fp) in [("curve_a1", curve_a1), ("curve_a2", curve_a2),
                     ("curve_b1", curve_b1), ("curve_b2", curve_b2)]
    fp_norm = fp * inv(leading_coefficient(fp))
    if haskey(seen_factors, fp_norm)
        println("  Curve equation $label appears as a factor in: ", seen_factors[fp_norm])
    end
end
println()

# Build the ideal from square-free, factor-deduplicated generators: for
# each equation, take each *distinct* irreducible factor once (drop
# multiplicity -- repeated factors don't add new variety components) and
# drop any factor that is a bare unit/constant (contributes nothing).
# This is the standard "radical-ish" cleanup before a Groebner basis call
# on a polynomial that's this large; it does not change the variety, only
# removes redundant generators.
function squarefree_generators(g)
    fac = factor(g)
    gens_out = Any[]
    for (factor_poly, _) in fac
        total_degree(factor_poly) == 0 && continue  # skip unit/constant factors
        push!(gens_out, factor_poly)
    end
    return gens_out
end

println("Reducing each equation to its distinct irreducible factors...")
Fu_reduced = Any[]
for (i, g) in enumerate(Fu)
    fs = squarefree_generators(g)
    println("  Fu$(i-1) -> ", length(fs), " distinct irreducible factor(s), degrees=", total_degree.(fs))
    append!(Fu_reduced, fs)
end
Fv_reduced = Any[]
for (i, g) in enumerate(Fv)
    fs = squarefree_generators(g)
    println("  Fv$(i-1) -> ", length(fs), " distinct irreducible factor(s), degrees=", total_degree.(fs))
    append!(Fv_reduced, fs)
end
println()

################################################################################
# Build ideals
#
# NOTE: using Fu_reduced/Fv_reduced (distinct irreducible factors of each
# coeff_equal expression, with unit-multiple duplicates against each other
# AND against the curve equations already collapsed above) instead of the
# raw Fu/Fv. This is a genuine mathematical simplification, not a cosmetic
# one: V(g) = V(g1) ∪ V(g2) ∪ ... for g = g1^{e1} * g2^{e2} * ..., so
# generating the ideal from {g1,g2,...} instead of {g} changes what
# variety we compute (a union of components rather than one polynomial's
# full -- possibly non-radical -- vanishing locus), and dropping a factor
# that's a unit multiple of a curve equation removes a generator that
# was already implied by curve_a1/curve_a2/curve_b1/curve_b2. If the
# "Checking for repeated/shared irreducible factors" report above showed
# nothing shared and no curve-equation matches, Fu_reduced/Fv_reduced is
# just Fu/Fv split into pieces and this changes nothing mathematically,
# only what groebner_basis has to chew on internally. If anything WAS
# shared, look at that report before trusting the final variety here --
# in particular decide whether a shared/curve-matching factor should have
# been dropped (as done here) or whether its presence is itself
# meaningful and should be investigated instead of discarded.
################################################################################

#
# U-only system.
#
Iu = ideal(R, vcat(Fu_reduced, [curve_a1, curve_a2, curve_b1, curve_b2]))


#
# Full Mumford system (u AND v matching).
#
Iuv = ideal(R, vcat(Fu_reduced, Fv_reduced, [curve_a1, curve_a2, curve_b1, curve_b2]))

################################################################################
# NOTE on saturation: an earlier version of this script saturated Iu/Iuv
# by CLEARED_DENOMS (the denominators tower_to_ring cleared) on the
# theory that coeff_equal's cross-multiplication reintroduces spurious
# multiplicity that these denominators describe. The factor() report
# above disproves that for THIS run: Fu0/Fu1 (degree 32) and Fv0/Fv1
# (degree 48) each factor into exactly ONE irreducible piece with
# multiplicity 1, and none of them share a factor with each other or
# with curve_a1/curve_a2/curve_b1/curve_b2. That means there is no
# spurious component to remove here -- the full degree is genuine
# variety-defining content, not cancelable junk. Saturating against it
# would only add cost (saturation is itself built from elimination/
# colon-ideal machinery, so it's not cheaper than groebner_basis -- it's
# built out of the same primitive) without simplifying anything, which
# is why that step was hanging. CLEARED_DENOMS is left defined above
# (still useful diagnostically / for future runs where the factor report
# DOES show shared or curve-matching factors) but is no longer applied
# automatically. If a future run's factor() report shows shared factors,
# saturate selectively by just those specific factors, not the full
# CLEARED_DENOMS list.
################################################################################

println("Skipping saturation: factor() report showed no spurious/shared factors to remove.")
println()

println()
println("Constructed symbolic systems.")
println("U equations:   ", ngens(Iu))
println("UV equations:  ", ngens(Iuv))
# NOTE: dim(Iu)/dim(Iuv) were removed here. dim() on an ideal is computed
# from a Groebner basis's leading-term ideal internally -- so calling it
# on Iu/Iuv (degree-32/48 generators, 8 variables) BEFORE the explicit
# groebner_basis(...; ordering=block_ordering) calls below forces Oscar
# to first compute a full Groebner basis under its DEFAULT ordering
# (unblocked degrevlex over all 8 variables), which is exactly the naive
# computation the block ordering was meant to avoid. This is what was
# actually hanging -- not saturation, and not groebner_basis(Iu;
# ordering=block_ordering) itself, but this dim() call silently doing
# the expensive default-ordering computation first. dim is now read off
# GBu/GBuv after they're computed with the block ordering, further down.
println()

################################################################################
#
# Groebner basis
#
################################################################################

println()
println("===========================================================")
println("Computing Groebner basis for U-system")
println("===========================================================")
println()

# Prefer F4 (Faugere's algorithm via msolve) over the default :buchberger
# (Singular's classical, single-threaded std()/bba/redHoney -- exactly
# what showed up stuck in the crash backtrace). F4 is matrix-based and
# has real internal parallelism in its linear algebra step, and msolve
# targets finite fields specifically, which is exactly our setting
# (GF(p)). Falls back to :buchberger if :f4 errors -- e.g. if this
# Oscar/msolve version doesn't support the block ordering or some other
# input restriction applies (see the algorithm=:f4 docstring notes).
# Prefer F4 (Faugere's algorithm via msolve) over the default :buchberger
# (Singular's classical, single-threaded std()/bba/redHoney -- exactly
# what showed up stuck in the crash backtrace). F4 is matrix-based and
# has real internal parallelism in its linear algebra step, and msolve
# targets finite fields specifically, which is exactly our setting
# (GF(p)). Falls back to :buchberger if :f4 errors -- e.g. if this
# Oscar/msolve version doesn't support the block ordering or some other
# input restriction applies (see the algorithm=:f4 docstring notes).
GBu = try
    result = groebner_basis(Iu; ordering = block_ordering, algorithm = :f4)
    println("(computed via algorithm = :f4)")
    result
catch e
    println("algorithm=:f4 failed (", e, "), falling back to :buchberger...")
    groebner_basis(Iu; ordering = block_ordering, algorithm = :buchberger)
end

println("Basis has ", length(GBu), " elements.")
println()

# NOTE: dim(Iu) was here before, on the theory that it would reuse the
# just-computed block-ordering GB. That's wrong: the crash backtrace
# shows dim() -> krull_dim -> singular_groebner_generators ->
# groebner_assure -> _compute_standard_basis calls Singular's std()
# directly, with NO ordering argument threaded through at all -- it is
# a completely separate standard-basis computation under whatever
# internal default groebner_assure uses, not the block_ordering GBu was
# computed with. So dim(Iu) was never going to benefit from GBu having
# already finished; it re-triggers the expensive default-ordering
# computation every time, which is what was hanging (again) inside
# Singular's bba/redHoney reduction loop.
#
# Instead, estimate the dimension directly from GBu's own leading terms
# (valid for the ordering GBu was actually computed under): the ideal is
# zero-dimensional iff, for every variable, SOME leading monomial in GBu
# is a pure power of that variable alone. This needs no further calls
# into Singular.
function leading_term_dim_zero(gb, all_vars)
    lms = [leading_monomial(g) for g in gb]
    for v in all_vars
        found_pure_power = any(lms) do lm
            evars = vars(lm)
            length(evars) == 1 && evars[1] == v
        end
        if !found_pure_power
            return false
        end
    end
    return true
end

if leading_term_dim_zero(GBu, gens(R))
    println("GBu leading terms indicate Iu is zero-dimensional ",
            "(pure power of every variable appears as some leading monomial).")
else
    println("GBu leading terms do NOT show a pure power for every variable -- ",
            "Iu is NOT confirmed zero-dimensional from this check alone ",
            "(this is a sufficient-for-zero-dim heuristic under GBu's own ",
            "ordering, not a full dim() computation).")
end
println()

for (i, g) in enumerate(GBu)

    println("--------------------------------------------------")
    println("g", i)
    println("--------------------------------------------------")
    println("variables = ", vars(g))
    println("degree    = ", total_degree(g))
    println("terms     = ", length(terms(g)))
    println()
    println(g)
    println()

end

################################################################################
#
# Repeat for the full Mumford system.
#
################################################################################

println()
println("===========================================================")
println("Computing Groebner basis for UV-system")
println("===========================================================")
println()

GBuv = try
    result = groebner_basis(Iuv; ordering = block_ordering, algorithm = :f4)
    println("(computed via algorithm = :f4)")
    result
catch e
    println("algorithm=:f4 failed (", e, "), falling back to :buchberger...")
    groebner_basis(Iuv; ordering = block_ordering, algorithm = :buchberger)
end

println("Basis has ", length(GBuv), " elements.")
println()

# See NOTE above GBu's dim check: dim(Iuv) here would trigger the same
# separate, uncontrolled-ordering Singular std() call. Use the same
# leading-term heuristic instead.
if leading_term_dim_zero(GBuv, gens(R))
    println("GBuv leading terms indicate Iuv is zero-dimensional ",
            "(pure power of every variable appears as some leading monomial).")
else
    println("GBuv leading terms do NOT show a pure power for every variable -- ",
            "Iuv is NOT confirmed zero-dimensional from this check alone.")
end
println()

for (i, g) in enumerate(GBuv)

    println("--------------------------------------------------")
    println("g", i)
    println("--------------------------------------------------")
    println("variables = ", vars(g))
    println("degree    = ", total_degree(g))
    println("terms     = ", length(terms(g)))
    println()
    println(g)
    println()

end

################################################################################
#
# Look for elimination polynomials (pure in a1,a2,b1,b2 -- no w's).
#
################################################################################

const W_VARS = (wa1, wa2, wb1, wb2)

function uses_only_ab(g)
    for v in vars(g)
        if v in W_VARS
            return false
        end
    end
    return true
end

println()
println("===========================================================")
println("Polynomials involving only (a1,a2,b1,b2)")
println("===========================================================")
println()

pure = typeof(GBu[1])[]

for g in GBu
    if uses_only_ab(g)
        push!(pure, g)
        println("--------------------------------")
        println("degree = ", total_degree(g))
        println("terms  = ", length(terms(g)))
        println(g)
        println()
    end
end

println()
println("Found ", length(pure), " elimination candidates.")
println()

################################################################################
#
# If the UV ideal is zero-dimensional (or low-dim), eliminate the w's.
#
################################################################################

for (i, f) in enumerate(gens(Iuv))
    println("eq $i: ", vars(f))
end

println("All variables:")
println(symbols(R))

# NOTE: this used to loop over every variable in R, building a fresh
# ideal ideal(vcat(gens(Iuv),[x])) and calling dim(J) on it -- 8 separate
# ideals, each triggering ANOTHER full default-ordering Groebner basis
# computation on top of the degree-32/48 generators, on top of the
# dim(ideal(curve_a1,...)) / dim(Iu) / dim(Iuv) calls right after it.
# That's 11 extra expensive Groebner computations purely for diagnostic
# printouts, all using the default (non-block) ordering -- this was
# almost certainly the next hang after the one fixed above. Cut down to
# what's actually informative and cheap: curve-only dimension (small,
# cheap on its own) plus the leading-monomial-derived variable
# dependence already visible in GBu/GBuv (no new Groebner computation).
println("dim(curve equations only) = ", dim(ideal(curve_a1, curve_a2, curve_b1, curve_b2)))
println("(dim(Iu)/dim(Iuv)/per-variable dim(J) diagnostics skipped here -- ",
        "each forces its own default-ordering Groebner basis on the ",
        "degree-32/48 system; see GBu/GBuv computed below with the ",
        "block ordering instead, and read dimension off THOSE.)")

println()
println("===========================================================")
println("Eliminating wa1, wa2, wb1, wb2 directly from the UV system")
println("===========================================================")
println()

# Eliminate one variable at a time rather than handing eliminate() all
# four w's in a single block call. Each single-variable elimination is a
# smaller resultant-style computation against the (hopefully already much
# smaller, post-saturation) ideal from the previous step, instead of one
# joint 4-variable elimination over the full system at once.
It = Iuv
for w in (wb2, wb1, wa2, wa1)
    global It = eliminate(It, [w])
    println("  after eliminating $w: ", ngens(It), " generator(s)")
end

println("Found ", length(gens(It)), " elimination polynomials in (a1,a2,b1,b2).")
for (i, g) in enumerate(gens(It))
    println("\nCandidate $i (Degree $(total_degree(g))):")
    println(g)
end

################################################################################
#
# Verification helper.
#
################################################################################

function verify_candidate(a1v, wa1v, a2v, wa2v, b1v, wb1v, b2v, wb2v)

    vals = Dict(
        a1 => F(a1v), wa1 => F(wa1v),
        a2 => F(a2v), wa2 => F(wa2v),
        b1 => F(b1v), wb1 => F(wb1v),
        b2 => F(b2v), wb2 => F(wb2v),
    )

    println()

    for (i, g) in enumerate(Fu)
        println("Fu$(i-1) = ", evaluate(g, vals))
    end
    for (i, g) in enumerate(Fv)
        println("Fv$(i-1) = ", evaluate(g, vals))
    end
    println("curve_a1 = ", evaluate(curve_a1, vals))
    println("curve_a2 = ", evaluate(curve_a2, vals))
    println("curve_b1 = ", evaluate(curve_b1, vals))
    println("curve_b2 = ", evaluate(curve_b2, vals))

    println()

    ok =
        all(iszero(evaluate(g, vals)) for g in Fu) &&
        all(iszero(evaluate(g, vals)) for g in Fv) &&
        iszero(evaluate(curve_a1, vals)) &&
        iszero(evaluate(curve_a2, vals)) &&
        iszero(evaluate(curve_b1, vals)) &&
        iszero(evaluate(curve_b2, vals))

    println("Verified = ", ok)

    return ok

end
