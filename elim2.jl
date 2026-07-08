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
# Lex ordering matches elim.jl's convention: w's before t's, so that
# eliminate(..., [wa1,wa2,wb1,wb2]) leaves polynomials purely in a1,a2,b1,b2.
################################################################################

R, (wa1, wa2, wb1, wb2, a2, a1, b2, b1) = polynomial_ring(
    F,
    ["wa1", "wa2", "wb1", "wb2", "a2", "a1", "b2", "b1"]
)

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
    return (num_R, den_R)
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
    return (num, den)
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

println()
println("Constructed symbolic systems.")
println("U equations:   ", ngens(Iu))
println("UV equations:  ", ngens(Iuv))
println("dim(Iu)  = ", dim(Iu))
println("dim(Iuv) = ", dim(Iuv))
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

GBu = groebner_basis(Iu)

println("Basis has ", length(GBu), " elements.")
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

GBuv = groebner_basis(Iuv)

println("Basis has ", length(GBuv), " elements.")
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

for x in gens(R)
    J = ideal(vcat(gens(Iuv), [x]))
    println(x, " -> ", dim(J))
end

println(dim(ideal(curve_a1, curve_a2, curve_b1, curve_b2)))
println(dim(Iu))
println(dim(Iuv))

println()
println("===========================================================")
println("Eliminating wa1, wa2, wb1, wb2 directly from the UV system")
println("===========================================================")
println()

It = eliminate(Iuv, [wa1, wa2, wb1, wb2])

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
