#!/usr/bin/env julia

################################################################################
#
#  elim2_refactored.jl
#
#  Encapsulated version of elim2.jl.
#
#  ---------------------------------------------------------------------------
#  WHY THIS FILE LOOKS THE WAY IT DOES
#  ---------------------------------------------------------------------------
#  The original elim2.jl was not one script: it was (at least) five
#  originally-separate Julia scripts concatenated back-to-back over the
#  course of a research investigation, each with its own `#!/usr/bin/env
#  julia` header and its own `using Oscar`, plus a large trailing
#  block-comment epilogue. Nothing here reorders or merges that content --
#  every top-level statement from the original file has been kept, moved
#  into a function body, and called from the appropriate `run_*` entry
#  point below, in the same relative order it appeared in the original.
#  Dead branches (`if false ... end`) and the trailing `#= ... =#` comment
#  are preserved as-is (as unreachable code / as comments) rather than
#  deleted.
#
#  The five original units, and the submodule each now lives in:
#
#    1. elim2.jl proper (original lines 1-1090, plus its PART A-K
#       continuation at original lines ~5007-8396)      -> submodule Elim2Main
#    2. norm_elim_diag.jl (original lines 1091-2853)     -> submodule NormElimDiag
#    3. part_i_squarefree_diag.jl (original lines 2854-3964)
#                                                          -> submodule PartISquarefreeDiag
#    4. part_i_eliminate_vs_resultant_bench.jl (original lines 3965-~5006)
#                                                          -> submodule PartIBench
#
#  Each submodule exposes one or more `run_*` functions instead of running
#  at top-level on `include`. Shared per-script state (what used to be
#  bare global variables) is now carried in a struct returned by the
#  earlier stage and threaded into the later ones as an explicit argument
#  -- nothing relies on Julia global scope.
#
#  This top-level module is Pkg-friendly: including it (or `using` it as
#  a package) defines types and functions only. Nothing runs until you
#  call one of the `run_*` entry points, e.g.:
#
#      include("elim2_refactored.jl")
#      using .Elim2
#      session = Elim2.Elim2Main.run_main()
#
#  or, to reproduce the original file's end-to-end behavior (all five
#  units, in original order), call `Elim2.run_all()`.
#
################################################################################

module Elim2

using Oscar
using Serialization

################################################################################
# Shared engine include, common to every submodule below (each original
# script located trial3_phi_symbolic_unified.jl slightly differently --
# see each submodule's own `locate_engine()` for the exact original
# search path it used).
################################################################################

"""
    locate_engine_default()

Original elim2.jl's fixed assumption: the symbolic engine lives at
`<this file's dir>/phi_general/src/trial3_phi_symbolic_unified.jl`.
"""
function locate_engine_default()
    return joinpath(@__DIR__, "phi_general", "src", "trial3_phi_symbolic_unified.jl")
end

################################################################################
#
#  Submodule: Elim2Main
#
#  Encapsulation of original elim2.jl lines 1-1090 (samples -> ring ->
#  tower_to_ring -> Fu/Fv -> degree-in-w diagnostic -> decoupled U/V
#  construction -> norm_eliminate helpers -> per-layer degree trace ->
#  norm-before-vs-after-substitution experiment -> dead `if false` block).
#  The PART A-K continuation (original lines ~5007-8396) is appended to
#  this same submodule further down, since it is a direct continuation of
#  the state built here (same R_dec/Iu_decoupled/etc.).
#
################################################################################
module Elim2Main

using Oscar
using Serialization
using ..Elim2: locate_engine_default

################################################################################
# Struct: CurveConfig -- the curve/field constants, identical for both
# samples. Original top-level consts: p, F_POLY_ASC, F.
################################################################################
struct CurveConfig
    p::Int
    F_POLY_ASC::Vector{Int}
    F  # GF(p)
end

function default_curve_config()
    p = 2371157
    F_POLY_ASC = [2, 1, 0, 0, 0, 1]   # y^2 = x^5 + x + 2, ascending coeffs
    F = GF(p)
    return CurveConfig(p, F_POLY_ASC, F)
end

################################################################################
# Struct: SampleSpec -- one sample's (K, c, fixed anchors, u0/u1/v0/v1)
# input to PhiSymbolic.symbolic_residual. Original top-level consts:
# K1,c1,fixed1,u0_1,u1_1,v0_1,v1_1 (sample 1) and K2,c2,fixed2,u0_2,u1_2,
# v0_2,v1_2 (sample 2).
################################################################################
struct SampleSpec
    K::Int
    c::Int
    fixed::Vector{Tuple{Int,Int}}
    u0::Int
    u1::Int
    v0::Int
    v1::Int
end

function default_sample1()
    return SampleSpec(2, 2, Tuple{Int,Int}[], 468873, 956582, 2168176, 2288437)
end

function default_sample2()
    fixed2 = [(196, 793353)]
    spec = SampleSpec(3, 2, fixed2, 2112189, 375309, 801778, 2048138)
    if length(spec.fixed) != spec.K - spec.c
        error("elim2.jl: sample 2 (K=$(spec.K), c=$(spec.c)) needs exactly " *
              "$(spec.K - spec.c) fixed anchor(s), got $(length(spec.fixed)).")
    end
    return spec
end

"""
    call_symbolic_residual(PhiSymbolic, spec, cfg; label="sample")

Original lines 93-107 (per sample): calls PhiSymbolic.symbolic_residual,
then checks the result isn't degenerate, then prints its degrees.
"""
function call_symbolic_residual(PhiSymbolic, spec::SampleSpec, cfg::CurveConfig; label::String = "sample")
    println("Calling PhiSymbolic.symbolic_residual for $label (K=$(spec.K), c=$(spec.c))...")
    res = PhiSymbolic.symbolic_residual(spec.K, spec.c, spec.fixed, spec.u0, spec.u1,
                                         spec.v0, spec.v1, cfg.F_POLY_ASC, cfg.p)
    if isempty(res.u_RS_coeffs) || isempty(res.v_RS_coeffs)
        error("$label (K=$(spec.K)): construction failed or degenerate -- no u_RS/v_RS to match")
    end
    println("$label: deg(u_RS)=$(length(res.u_RS_coeffs)-1)  deg(v_RS)=$(length(res.v_RS_coeffs)-1)")
    return res
end

################################################################################
# Struct: TargetRing -- the shared plain multivariate ring
# F[wa1,wa2,wb1,wb2,a2,a1,b2,b1], its generators, the curve relations in
# it, and its block ordering. Original top-level: R, (wa1,wa2,wb1,wb2,
# a2,a1,b2,b1), block_ordering, curve_a1, curve_a2, curve_b1, curve_b2.
################################################################################
struct TargetRing
    R
    wa1; wa2; wb1; wb2; a2; a1; b2; b1
    block_ordering
    curve_a1; curve_a2; curve_b1; curve_b2
end

"""
    build_target_ring(cfg)

Original lines 127-139. Plain ring construction, matching elim.jl's
working pattern -- this Oscar/AbstractAlgebra version's polynomial_ring
does not accept an `ordering` kwarg at all. w's are declared before the
a/b's so that eliminate(..., [wa1,wa2,wb1,wb2]) leaves polynomials purely
in a1,a2,b1,b2 regardless of monomial ordering.
"""
function build_target_ring(cfg::CurveConfig)
    R, (wa1, wa2, wb1, wb2, a2, a1, b2, b1) = polynomial_ring(
        cfg.F,
        ["wa1", "wa2", "wb1", "wb2", "a2", "a1", "b2", "b1"]
    )

    # Block ordering built from R's own generators, for use at
    # groebner_basis call sites further down (groebner_basis(I; ordering
    # = block_ordering)).
    block_ordering = degrevlex(gens(R)[1:4]) * degrevlex(gens(R)[5:8])

    curve_a1 = wa1^2 - (a1^5 + a1 + 2)
    curve_a2 = wa2^2 - (a2^5 + a2 + 2)
    curve_b1 = wb1^2 - (b1^5 + b1 + 2)
    curve_b2 = wb2^2 - (b2^5 + b2 + 2)

    return TargetRing(R, wa1, wa2, wb1, wb2, a2, a1, b2, b1,
                       block_ordering, curve_a1, curve_a2, curve_b1, curve_b2)
end

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

function map_coeffs_threaded(coeffs, t_gens, w_gens)
    n = length(coeffs)
    nums = Vector{Any}(undef, n)
    dens = Vector{Any}(undef, n)
    Threads.@threads for i in 1:n
        nums[i], dens[i] = tower_to_ring(coeffs[i], t_gens, w_gens)
    end
    return nums, dens
end

# -----------------------------------------------------------------------------
# Mumford-identity check, post map_coeffs_threaded: v_RS(x)^2 ≡ f(x) (mod u_RS(x))
#
# u_num[i]/u_den[i] and v_num[i]/v_den[i] are the x^(i-1) coefficients of
# u_RS(x) and v_RS(x) respectively, each an independent element of R
# (num/den already reduced by tower_to_ring's own per-coefficient
# _reduce_frac call -- see the comment above _reduce_frac). This function
# re-forms u_RS(x) and v_RS(x) as polynomials in a fresh local variable X
# over Frac(R) and checks the Mumford identity holds identically as a
# rational function of the sample's own anchor variables (a1,a2 or b1,b2).
#
# symbolic_residual already guarantees this identity holds on the tower
# elements handed to map_coeffs_threaded (see the pre/post-reduction
# checks added in trial3_phi_symbolic_unified.jl). This check exists to
# answer a DIFFERENT question: does elim2.jl's own independent
# per-coefficient reduction in tower_to_ring/_reduce_frac (applied AFTER
# symbolic_residual returns, entirely separate from -- and unaware of --
# that upstream guarantee) preserve it? If this fails while the upstream
# checks passed, the break is localized to THIS reduction step, not the
# one inside symbolic_residual.
#
# Raises an ErrorException rather than returning a boolean: a failure
# here means u1_num/u1_den and v1_num/v1_den (or the sample-2 analogues)
# no longer describe a single self-consistent Mumford divisor, and
# feeding them into Fu_decoupled/Fv_decoupled/Iuv_decoupled downstream
# would silently produce an over-constrained ideal -- exactly the
# hypothesized cause of the U-only O(p^2) vs UV O(1) solution-count
# collapse. Better to fail loudly here, at the point consistency was
# lost, than to chase it through a Groebner basis computation later.
function _check_mumford_identity_ring(u_num::Vector, u_den::Vector,
                                       v_num::Vector, v_den::Vector,
                                       F_POLY_ASC::Vector{Int}, R,
                                       curve_gens::Vector;
                                       label::String = "")
    if isempty(u_num) || isempty(v_num)
        error("_check_mumford_identity_ring($label): empty u or v coefficient " *
              "vector -- nothing to check, caller should not have reached this point")
    end
    if length(u_num) != length(u_den) || length(v_num) != length(v_den)
        error("_check_mumford_identity_ring($label): mismatched num/den lengths " *
              "(len(u_num)=$(length(u_num)), len(u_den)=$(length(u_den)), " *
              "len(v_num)=$(length(v_num)), len(v_den)=$(length(v_den)))")
    end

    Rx, X = polynomial_ring(R, "X_mumford_check")

    # Build u_RS(X) and v_RS(X) as polynomials over Frac(R)-valued
    # coefficients, but clear denominators up front so everything stays
    # in Rx (u_num[i]/u_den[i] * common_den_u is a polynomial in R).
    den_u_common = reduce(*, u_den)
    den_v_common = reduce(*, v_den)

    u_poly = sum(
        Rx(u_num[i]) * Rx(divexact(den_u_common, u_den[i])) * X^(i-1)
        for i in 1:length(u_num)
    )
    v_poly = sum(
        Rx(v_num[i]) * Rx(divexact(den_v_common, v_den[i])) * X^(i-1)
        for i in 1:length(v_num)
    )

    f_poly = sum(Rx(F_POLY_ASC[i+1]) * X^i for i in 0:(length(F_POLY_ASC)-1))

    # u_poly's leading coefficient (in R, NOT a fraction field element)
    # generically has no reason to be a unit -- see note below (moved
    # verbatim from the original inline comment at this point in
    # elim2.jl, kept here since it explains why pseudorem() rather than
    # mod() is used just below).
    #
    # variables (a1,a2 or b1,b2), NOT a fraction field. is_unit(x) for x
    # in a multivariate polynomial ring over a field is only ever true for
    # nonzero CONSTANTS; u_lead is generically a nonconstant polynomial
    # (bidegree (16,16) in an actual run), so is_unit(u_lead) was
    # essentially guaranteed to be false regardless of whether anything
    # upstream was broken -- the guard fired on every run, not just broken
    # ones. That is_unit(den) idiom was borrowed from elsewhere in this
    # file (bracket_num, ~line 4954) without checking it fit this ring:
    # those call sites check is_unit(denominator(val)) for val in Kcoef =
    # Frac(F[a1,a2,b1,b2]) -- there the denominator is expected to cancel
    # down to 1 after arithmetic, so is_unit is a meaningful, often-true
    # test. Here u_lead lives directly in R, not Frac(R), and there's no
    # reason it should ever be constant.
    #
    # mod() needs an invertible leading coefficient in the modulus for a
    # well-defined quotient/remainder in general, so it was never the
    # right primitive for a modulus with non-unit leading coefficient over
    # a general commutative ring. pseudorem() is: pseudorem(f, g) computes
    # lc(g)^k * f reduced mod g for a suitable k (absorbing exactly the
    # obstruction that would otherwise require lc(g) to be a unit), and is
    # already used elsewhere in this file for the same reason (see
    # pseudorem(g1_T, g2_T) at the PRS growth-prediction step, and the
    # manual disk-sharded PRS loop further down). Since lc(u_poly) is
    # nonzero (u_poly is a nonzero polynomial of degree length(u_num)-1 by
    # construction) and R is an integral domain (a polynomial ring over a
    # finite field), multiplying lhs by a nonzero power of lc(u_poly)
    # cannot introduce or hide a nonzero residual: iszero is preserved
    # both ways, so pseudorem(lhs, u_poly) == 0 iff the underlying
    # (unscaled) identity holds -- exactly what mod(lhs, u_poly) would
    # have certified had its unit precondition actually held.

    # v_RS(X)^2 * den_v_common^2 - f(X) * den_v_common^2, further scaled by
    # den_u_common^2 so the whole check stays polynomial against the u_poly
    # modulus (= u_RS(X)*den_u_common) without ever dividing by den_u_common:
    # residual vanishes iff the true (unscaled) identity v_RS(X)^2 ≡ f(X)
    # (mod u_RS(X)) does too, since den_u_common and den_v_common are both
    # nonzero elements of the fraction field, hence nonzerodivisors.
    lhs = (v_poly^2 - f_poly * Rx(den_v_common)^2) * Rx(den_u_common)^2
    residual = pseudorem(lhs, u_poly)

    # CRITICAL: R (built at the top of this file as
    # F[wa1,wa2,wb1,wb2,a2,a1,b2,b1]) is the plain, FREE polynomial ring --
    # it does not itself impose the curve relations wa1^2 = a1^5+a1+2,
    # wa2^2 = a2^5+a2+2 (those live separately as curve_a1/curve_a2, used
    # elsewhere in this file only as ideal generators, e.g.
    # `ideal(R_dec, vcat(Fu_decoupled, [curve_a1_d, curve_a2_d, ...]))`).
    # The Mumford identity only needs to hold ON THE CURVE, i.e. modulo
    # <curve_gens>, not identically in the free ring R. residual is built
    # from tower elements whose w_i dependence is at most linear per the
    # tower structure (_tower_to_ring's `num = n0*d1 + n1*d0*wv` never
    # squares wv on its own), so any wa_i^2-or-higher term appearing here
    # only arose from the polynomial arithmetic in this check (v_poly^2,
    # u_poly^2 inside pseudorem's internal squaring of leading
    # coefficients) -- exactly the kind of term curve_gens is meant to
    # collapse back down. Testing iszero(residual) directly, without this
    # reduction, would reject correct (u,v) pairs whenever such a term
    # survives, which is what happened before this fix was added (see the
    # sample-1 residual with wa1,wa2 appearing up to degree 4).
    #
    # residual lives in Rx = R[X] (a Generic.Poly{FqMPolyRingElem}), NOT
    # directly in R -- normal_form(::MPolyRingElem, ::MPolyIdeal) only
    # accepts elements of R itself, so it cannot be called on residual as
    # a whole (confirmed by the MethodError: Oscar's normal_form methods
    # all require an FqMPolyRingElem/MPolyRingElem first argument, and
    # Generic.Poly{FqMPolyRingElem} is a different type -- a univariate
    # polynomial in X whose COEFFICIENTS are FqMPolyRingElem). Reduce each
    # X-coefficient of residual individually instead: a polynomial in X is
    # zero iff every one of its coefficients is zero, so residual is zero
    # on the curve iff every coefficient of residual, reduced mod
    # <curve_gens>, is zero.
    curve_ideal = ideal(R, curve_gens)
    residual_coeffs_on_curve = iszero(residual) ? FqMPolyRingElem[] :
        [normal_form(coeff(residual, i), curve_ideal) for i in 0:degree(residual)]

    if !all(iszero, residual_coeffs_on_curve)
        error("_check_mumford_identity_ring($label): v_RS(x)^2 - f(x) is NOT " *
              "identically 0 mod u_RS(x) after map_coeffs_threaded's " *
              "per-coefficient tower_to_ring/_reduce_frac reduction, even " *
              "after reducing modulo the curve relations ($curve_gens). " *
              "Mumford condition violated at this reduction step -- the " *
              "(u,v) coefficient pair no longer describes a single " *
              "self-consistent divisor. nonzero X-coefficients (on curve) = " *
              "$(filter(!iszero, residual_coeffs_on_curve))")
    end

    return nothing
end

################################################################################
# Struct: MappedSample -- one sample's u_RS/v_RS coefficients, each
# mapped into R as a (numerator, denominator) pair per x^i coefficient,
# plus the t/w generator vectors used to build them. Original top-level:
# t_gens_1/w_gens_1/u1_num/u1_den/v1_num/v1_den (sample 1) and the
# _2 analogues (sample 2).
################################################################################
struct MappedSample
    t_gens::Vector
    w_gens::Vector
    u_num::Vector
    u_den::Vector
    v_num::Vector
    v_den::Vector
end

"""
    map_sample(res, t_gens, w_gens, cfg, tring, curve_gens; label)

Original lines 243-247 (generator selection), 439-455 (map + Mumford
check) for one sample. `curve_gens` is that sample's own pair of curve
relations (e.g. `[curve_a1, curve_a2]`).
"""
function map_sample(res, t_gens::Vector, w_gens::Vector, cfg::CurveConfig,
                     tring::TargetRing, curve_gens::Vector; label::String = "")
    u_num, u_den = map_coeffs_threaded(res.u_RS_coeffs, t_gens, w_gens)
    v_num, v_den = map_coeffs_threaded(res.v_RS_coeffs, t_gens, w_gens)

    # Localize whether THIS file's own independent per-coefficient
    # reduction (as opposed to _reduce_tower_coeffs inside
    # symbolic_residual, checked separately in
    # trial3_phi_symbolic_unified.jl) is what breaks the Mumford
    # coupling. Checked per-sample, immediately after each sample's
    # coefficients are mapped into R, so a failure here points at exactly
    # which sample's reduction lost consistency.
    _check_mumford_identity_ring(u_num, u_den, v_num, v_den, cfg.F_POLY_ASC, tring.R,
                                  curve_gens; label = "$label, post map_coeffs_threaded")

    return MappedSample(t_gens, w_gens, u_num, u_den, v_num, v_den)
end

"""
    report_mapped_samples(s1, s2)

Original lines 457-482: prints coefficient counts and per-sample
(un-cross-multiplied) size diagnostics.
"""
function report_mapped_samples(s1::MappedSample, s2::MappedSample; K1, K2)
    println()
    println("Mapped both samples' u_RS/v_RS coefficients into the shared ring.")
    println("u_RS^(K=$K1) has $(length(s1.u_num)) coefficient(s) (x^0..x^$(length(s1.u_num)-1))")
    println("u_RS^(K=$K2) has $(length(s2.u_num)) coefficient(s) (x^0..x^$(length(s2.u_num)-1))")
    println("v_RS^(K=$K1) has $(length(s1.v_num)) coefficient(s) (x^0..x^$(length(s1.v_num)-1))")
    println("v_RS^(K=$K2) has $(length(s2.v_num)) coefficient(s) (x^0..x^$(length(s2.v_num)-1))")
    println()

    # Per-sample (un-cross-multiplied) size diagnostics. This is the
    # premise the "decoupling via target variables" approach depends on:
    # it's only a win if each SAMPLE's own num/den (5-variable,
    # single-sample) is much smaller than the cross-multiplied Fu/Fv
    # (8-variable, both samples' variables mixed via coeff_equal's
    # num1*den2 - num2*den1). Printed here so that premise is checked
    # against real numbers rather than assumed.
    println("Per-sample (uncrossed) generator sizes -- checked BEFORE deciding ",
            "whether decoupling via target variables is worth it:")
    for (label, nums, dens) in [
            ("u1", s1.u_num, s1.u_den), ("u2", s2.u_num, s2.u_den),
            ("v1", s1.v_num, s1.v_den), ("v2", s2.v_num, s2.v_den),
        ]
        for (i, (n, d)) in enumerate(zip(nums, dens))
            println("  $label num[$i]: degree=", total_degree(n), " terms=", length(terms(n)),
                    "   $label den[$i]: degree=", total_degree(d), " terms=", length(terms(d)))
        end
    end
    println()
end

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

"""
    run_symmetry_checks(s1, s2, tring)

Original lines 515-536: checks a1<->a2/b1<->b2 swap symmetry for both
samples' u_RS/v_RS and prints the resulting recommendation.
"""
function run_symmetry_checks(s1::MappedSample, s2::MappedSample, tring::TargetRing)
    println("Checking a1<->a2 (and wa1<->wa2) symmetry of sample 1's u_RS/v_RS...")
    u1_symmetric = check_swap_symmetry(s1.u_num, s1.u_den, [tring.a1, tring.a2, tring.wa1, tring.wa2],
                                        [tring.a2, tring.a1, tring.wa2, tring.wa1], "u1")
    v1_symmetric = check_swap_symmetry(s1.v_num, s1.v_den, [tring.a1, tring.a2, tring.wa1, tring.wa2],
                                        [tring.a2, tring.a1, tring.wa2, tring.wa1], "v1")

    println("Checking b1<->b2 (and wb1<->wb2) symmetry of sample 2's u_RS/v_RS...")
    u2_symmetric = check_swap_symmetry(s2.u_num, s2.u_den, [tring.b1, tring.b2, tring.wb1, tring.wb2],
                                        [tring.b2, tring.b1, tring.wb2, tring.wb1], "u2")
    v2_symmetric = check_swap_symmetry(s2.v_num, s2.v_den, [tring.b1, tring.b2, tring.wb1, tring.wb2],
                                        [tring.b2, tring.b1, tring.wb2, tring.wb1], "v2")

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

    return (u1_symmetric = u1_symmetric, v1_symmetric = v1_symmetric,
            u2_symmetric = u2_symmetric, v2_symmetric = v2_symmetric)
end

################################################################################
# Struct: MatchSpec -- how many u/v coefficients actually get matched
# (the top/leading u_RS coefficient is trivially 1==1 on both sides, so
# it's skipped), plus the cleared denominators collected across both
# samples for later saturation. Original top-level consts: U_DEG_TOP,
# N_U_MATCH, CLEARED_DENOMS.
################################################################################
struct MatchSpec
    U_DEG_TOP::Int
    N_U_MATCH::Int
    CLEARED_DENOMS::Vector
end

"""
    check_sample_degrees_match(s1, s2)

Original lines 538-545: u_RS/v_RS degree-match sanity checks between the
two samples (matching only makes sense if both have the same degree).
"""
function check_sample_degrees_match(s1::MappedSample, s2::MappedSample)
    if length(s1.u_num) != length(s2.u_num)
        error("u_RS degree mismatch between samples: $(length(s1.u_num)-1) vs $(length(s2.u_num)-1) -- " *
              "matching only makes sense if both u_RS have the same degree")
    end
    if length(s1.v_num) != length(s2.v_num)
        error("v_RS degree mismatch between samples: $(length(s1.v_num)-1) vs $(length(s2.v_num)-1) -- " *
              "matching only makes sense if both v_RS have the same degree")
    end
end

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
function _nonconstant_dens(dens)
    return [d for d in dens if total_degree(d) > 0]
end

"""
    build_match_spec(s1, s2)

Original lines 547-580 (post degree-match check). The top (leading)
u_RS coefficient is always 1 on both sides -- symbolic_residual
normalizes u_RS to monic before returning it -- so matching x^deg is
the trivial equation 1==1 and is skipped; only x^0..x^(deg-1) are
matched.
"""
function build_match_spec(s1::MappedSample, s2::MappedSample)
    U_DEG_TOP = length(s1.u_num)   # index of the (trivial) leading coefficient
    N_U_MATCH = U_DEG_TOP - 1      # how many real u-coefficients to match

    CLEARED_DENOMS = vcat(
        _nonconstant_dens(s1.u_den), _nonconstant_dens(s2.u_den),
        _nonconstant_dens(s1.v_den), _nonconstant_dens(s2.v_den),
    )

    println("Collected ", length(CLEARED_DENOMS), " nonconstant cleared denominator(s) ",
            "across both samples (for saturation).")
    println()

    return MatchSpec(U_DEG_TOP, N_U_MATCH, CLEARED_DENOMS)
end

################################################################################
# Equality equations -- same coeff_equal pattern as elim.jl, applied
# coefficient-by-coefficient.
################################################################################

function coeff_equal(num1, den1, num2, den2)
    return num1 * den2 - num2 * den1
end

################################################################################
# Struct: FuFv -- the u/v-matching cross-multiplied equations. Original
# top-level: Fu, Fv.
################################################################################
struct FuFv
    Fu::Vector{Any}
    Fv::Vector{Any}
end

"""
    build_fu_fv(s1, s2, mspec)

Original lines 591-610: builds Fu (x^0..x^(N_U_MATCH-1) matching
equations) and Fv (all v_RS coefficients' matching equations), in
parallel across threads, then prints their sizes.
"""
function build_fu_fv(s1::MappedSample, s2::MappedSample, mspec::MatchSpec)
    Fu = Vector{Any}(undef, mspec.N_U_MATCH)
    Threads.@threads for i in 1:mspec.N_U_MATCH
        Fu[i] = coeff_equal(s1.u_num[i], s1.u_den[i], s2.u_num[i], s2.u_den[i])
    end

    Fv = Vector{Any}(undef, length(s1.v_num))
    Threads.@threads for i in 1:length(s1.v_num)
        Fv[i] = coeff_equal(s1.v_num[i], s1.v_den[i], s2.v_num[i], s2.v_den[i])
    end

    println("Built ", length(Fu), " u-matching equation(s) (x^0..x^$(mspec.N_U_MATCH-1); ",
            "trivial leading x^$(mspec.U_DEG_TOP-1) coefficient 1==1 skipped) and ",
            length(Fv), " v-matching equation(s).")
    for (i, g) in enumerate(Fu)
        println("  Fu$(i-1): degree=", total_degree(g), "  terms=", length(terms(g)))
    end
    for (i, g) in enumerate(Fv)
        println("  Fv$(i-1): degree=", total_degree(g), "  terms=", length(terms(g)))
    end
    println()

    return FuFv(Fu, Fv)
end

################################################################################
# degree_check.jl
#
# Originally: "Insert this block into elim2.jl immediately after Fu/Fv
# are built ... Purpose: compute EXACT degree-in-each-w for every
# relevant polynomial, with no assumptions. This settles whether:
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

function report_wdeg(label, g, w_all)
    degs = [degree(g, w) for w in w_all]
    println("  $label: total_degree=", total_degree(g),
            "  degree-in-(wa1,wa2,wb1,wb2)=", degs)
    return degs
end

# If degrees DO exceed 1: reduce each Fu/Fv generator modulo the four curve
# relations (w_i^2 - f(t_i)) to bring it back to affine-in-each-w form, then
# recheck degrees. This directly tests whether the higher-degree terms were
# "fake" (removable by the algebraic relation the ring doesn't know about)
# or genuinely irreducible content.
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

"""
    run_degree_in_w_diagnostic(s1, s2, fufv, tring)

Original lines 639-777. Reports degree-in-each-w for every per-sample
num/den and for Fu/Fv; if any exceed degree 1 in some w, additionally
reduces Fu/Fv modulo the curve relations and rechecks. Returns a
NamedTuple with `all_ok` and (if computed) the reduced generators, so
callers can decide which generators to hand to norm elimination.
"""
function run_degree_in_w_diagnostic(s1::MappedSample, s2::MappedSample, fufv::FuFv, tring::TargetRing)
    println("===========================================================")
    println("DEGREE-IN-W DIAGNOSTIC")
    println("===========================================================")
    println()

    w_all = [tring.wa1, tring.wa2, tring.wb1, tring.wb2]
    w_names = ["wa1", "wa2", "wb1", "wb2"]

    println("--- Sample 1 per-coefficient num/den: degree in wa1, wa2 (should be <=1 each) ---")
    for (i, (n, d)) in enumerate(zip(s1.u_num, s1.u_den))
        report_wdeg("u1_num[$i]", n, w_all)
        report_wdeg("u1_den[$i]", d, w_all)
    end
    for (i, (n, d)) in enumerate(zip(s1.v_num, s1.v_den))
        report_wdeg("v1_num[$i]", n, w_all)
        report_wdeg("v1_den[$i]", d, w_all)
    end
    println()

    println("--- Sample 2 per-coefficient num/den: degree in wb1, wb2 (should be <=1 each) ---")
    for (i, (n, d)) in enumerate(zip(s2.u_num, s2.u_den))
        report_wdeg("u2_num[$i]", n, w_all)
        report_wdeg("u2_den[$i]", d, w_all)
    end
    for (i, (n, d)) in enumerate(zip(s2.v_num, s2.v_den))
        report_wdeg("v2_num[$i]", n, w_all)
        report_wdeg("v2_den[$i]", d, w_all)
    end
    println()

    println("--- Fu/Fv (post cross-multiplication): degree in each of wa1,wa2,wb1,wb2 ---")
    all_ok = true
    for (i, g) in enumerate(fufv.Fu)
        degs = report_wdeg("Fu$(i-1)", g, w_all)
        if any(d -> d > 1, degs)
            all_ok = false
            println("    *** Fu$(i-1) EXCEEDS degree 1 in at least one w-variable ***")
        end
    end
    for (i, g) in enumerate(fufv.Fv)
        degs = report_wdeg("Fv$(i-1)", g, w_all)
        if any(d -> d > 1, degs)
            all_ok = false
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

    Fu_reduced_test = nothing
    Fv_reduced_test = nothing
    if !all_ok
        println("--- Reducing Fu/Fv modulo (w_i^2 - f(t_i)) and rechecking degrees ---")
        f_list = [tring.a1^5 + tring.a1 + 2, tring.a2^5 + tring.a2 + 2,
                  tring.b1^5 + tring.b1 + 2, tring.b2^5 + tring.b2 + 2]

        Fu_reduced_test = [reduce_mod_w_squares(g, w_all, f_list) for g in fufv.Fu]
        Fv_reduced_test = [reduce_mod_w_squares(g, w_all, f_list) for g in fufv.Fv]

        println("After reduction:")
        all_ok_after = true
        for (i, g) in enumerate(Fu_reduced_test)
            degs = report_wdeg("Fu$(i-1)_reduced", g, w_all)
            if any(d -> d > 1, degs); all_ok_after = false; end
        end
        for (i, g) in enumerate(Fv_reduced_test)
            degs = report_wdeg("Fv$(i-1)_reduced", g, w_all)
            if any(d -> d > 1, degs); all_ok_after = false; end
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

    return (all_ok = all_ok, Fu_reduced_test = Fu_reduced_test, Fv_reduced_test = Fv_reduced_test)
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

################################################################################
# Struct: DecoupledSystem -- the U0,U1,V0,V1-target-variable ring and the
# decoupled equations/ideals built in it. Original top-level: R_dec,
# dec_gens, wa1_d/wa2_d/wb1_d/wb2_d/a2_d/a1_d/b2_d/b1_d, U_vars, V_vars,
# curve_a1_d/curve_a2_d/curve_b1_d/curve_b2_d, Fu_decoupled, Fv_decoupled,
# Iu_decoupled, Iuv_decoupled, block_ordering_dec.
################################################################################
struct DecoupledSystem
    R_dec
    wa1_d; wa2_d; wb1_d; wb2_d; a2_d; a1_d; b2_d; b1_d
    U_vars::Vector
    V_vars::Vector
    curve_a1_d; curve_a2_d; curve_b1_d; curve_b2_d
    Fu_decoupled::Vector{Any}
    Fv_decoupled::Vector{Any}
    Iu_decoupled
    Iuv_decoupled
    block_ordering_dec
end

"""
    build_decoupled_system(s1, s2, mspec, tring)

Original lines 812-878. Re-maps each sample's num/den (elements of R)
into a new ring R_dec that additionally carries target variables
U0,U1,...  and V0,V1,..., then builds `U_i * den == num` (and `V_i`
likewise) equations per sample -- this does not change the underlying
variety, just phrases the coefficient-matching without cross-multiplying
both samples' variables together directly.
"""
function build_decoupled_system(s1::MappedSample, s2::MappedSample, mspec::MatchSpec, tring::TargetRing)
    R_dec, dec_gens = polynomial_ring(
        base_ring(tring.R),
        vcat(["wa1", "wa2", "wb1", "wb2", "a2", "a1", "b2", "b1"],
             ["U$i" for i in 0:(mspec.N_U_MATCH-1)],
             ["V$i" for i in 0:(length(s1.v_num)-1)])
    )
    wa1_d, wa2_d, wb1_d, wb2_d, a2_d, a1_d, b2_d, b1_d = dec_gens[1:8]
    U_vars = dec_gens[9:(8+mspec.N_U_MATCH)]
    V_vars = dec_gens[(9+mspec.N_U_MATCH):(8+mspec.N_U_MATCH+length(s1.v_num))]

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
        tring.wa1 => wa1_d, tring.wa2 => wa2_d, tring.wb1 => wb1_d, tring.wb2 => wb2_d,
        tring.a2 => a2_d, tring.a1 => a1_d, tring.b2 => b2_d, tring.b1 => b1_d,
    )
    remap(f) = evaluate(f, [old_to_new[g] for g in gens(tring.R)])

    u1_num_d = [remap(f) for f in s1.u_num]
    u1_den_d = [remap(f) for f in s1.u_den]
    u2_num_d = [remap(f) for f in s2.u_num]
    u2_den_d = [remap(f) for f in s2.u_den]
    v1_num_d = [remap(f) for f in s1.v_num]
    v1_den_d = [remap(f) for f in s1.v_den]
    v2_num_d = [remap(f) for f in s2.v_num]
    v2_den_d = [remap(f) for f in s2.v_den]

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

    return DecoupledSystem(R_dec, wa1_d, wa2_d, wb1_d, wb2_d, a2_d, a1_d, b2_d, b1_d,
                            U_vars, V_vars, curve_a1_d, curve_a2_d, curve_b1_d, curve_b2_d,
                            Fu_decoupled, Fv_decoupled, Iu_decoupled, Iuv_decoupled,
                            block_ordering_dec)
end

################################################################################
# norm_eliminate.jl
#
# Originally: "Insert immediately after the DEGREE-IN-W DIAGNOSTIC block
# confirms all Fu/Fv are degree <=1 in each of wa1,wa2,wb1,wb2 (confirmed
# by your run). This replaces the entire Groebner-basis + eliminate()
# pipeline for Fu/Fv with four sequential exact norm (resultant)
# computations."
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
# _tower_to_ring verbatim, just with diagnostics added.
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

"""
    run_per_layer_degree_trace(res1, t_gens_1, w_gens_1, s1)

Original lines 962-970: runs the instrumented tower walk for
`res1.u_RS_coeffs[1]` only (one representative coefficient), printing
degree/term counts at each layer, then compares the final result to
`s1.u_num[1]/s1.u_den[1]`.
"""
function run_per_layer_degree_trace(res1, t_gens_1::Vector, w_gens_1::Vector, s1::MappedSample)
    println("===========================================================")
    println("PER-LAYER DEGREE TRACE (sample 1, u_RS_coeffs[1] only)")
    println("===========================================================")
    println()
    n_test, d_test = _tower_to_ring_instrumented(res1.u_RS_coeffs[1], 2, t_gens_1, w_gens_1)
    println()
    println("Final (should match u1_num[1]/u1_den[1] from the main script): ",
            "num degree=", total_degree(n_test), " den degree=", total_degree(d_test))
    println()
    return (n_test, d_test)
end

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

"""
    run_norm_before_vs_after_experiment(res1, fufv, tring)

Original lines 991-1090. Splits `res1.u_RS_coeffs[1]` down to its
level-1 rational-function-field pieces (c00,c01,c10,c11) and reports
their numerator/denominator degrees, to compare against the fully
flattened u1_num[1] degree. Then contains the ORIGINAL dead `if false`
block (kept verbatim, unreachable, exactly as in elim2.jl -- the author's
comment reads "dis too slow lmao, gets done with the first one but blows
up") which would have run norm elimination on Fu/Fv directly, with no
Groebner basis.
"""
function run_norm_before_vs_after_experiment(res1, fufv::FuFv, tring::TargetRing)
    println("===========================================================")
    println("Testing norm-BEFORE-substitution vs norm-AFTER-substitution")
    println("===========================================================")
    println()

    # Get the level-1 c0, c1 split directly (one layer of recursion by
    # hand, mirroring _tower_to_ring's own level==2 branch).
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

    # --------------------------------------------------------------------
    # ORIGINAL DEAD CODE (elim2.jl, `if false # dis too slow lmao, gets
    # done with the first one but blows up`). Preserved verbatim as an
    # unreachable branch -- not deleted, not run. wa1/wa2/wb1/wb2/a1/a2/
    # b1/b2 refer to `tring`'s generators; Fu/Fv refer to `fufv`.
    # --------------------------------------------------------------------
    wa1, wa2, wb1, wb2 = tring.wa1, tring.wa2, tring.wb1, tring.wb2
    a1, a2, b1, b2 = tring.a1, tring.a2, tring.b1, tring.b2
    Fu, Fv = fufv.Fu, fufv.Fv

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

    return (c00 = c00, c01 = c01, c10 = c10, c11 = c11)
end

end # module Elim2Main

################################################################################
#
#  Submodule: NormElimDiag
#
#  Encapsulation of original norm_elim_diag.jl (original elim2.jl lines
#  1091-2853): a standalone diagnostic script that answers "is per-sample
#  norm elimination of the w's actually cheap?" using ONLY sample 1 (K=2,
#  c=2), independently of Elim2Main's R/tring/decoupled-system state --
#  the original script re-declared its own small 4-variable ring, its own
#  copies of _reduce_frac/_base_frac_to_ring/_tower_to_ring/tower_to_ring/
#  map_coeffs, and even its own top-level `const p`/`F_POLY_ASC`/`F`,
#  entirely separate from elim2.jl proper's globals of the same name.
#  That duplication is preserved here: NormElimDiag has its own
#  CurveConfig-equivalent setup and its own tower-flattening helpers
#  (`_reduce_frac`, `_base_frac_to_ring`, `_tower_to_ring`, `tower_to_ring`,
#  `map_coeffs`) rather than reusing Elim2Main's, exactly as the original
#  two scripts never shared state.
#
#  This submodule also carries PART A-J of the original file (the
#  post-summary experimental continuation starting at original line
#  ~1478 "EXPERIMENT: eliminate the w's ... from the DECOUPLED ideal"),
#  which is NOT a continuation of the norm-elimination summary above it
#  but a second, independent experiment against Elim2Main's decoupled
#  system (Fu_decoupled/R_dec/etc, built in Elim2Main) -- so functions in
#  this later part take that state as explicit arguments
#  (`decoupled::Elim2Main.DecoupledSystem`) rather than rebuilding it.
#
#  PART J launches external `julia part_j_worker.jl` subprocesses; that
#  worker script was not part of the two uploaded files, so
#  `run_part_j!` below reproduces the launcher/poller exactly but will
#  fail at the `run(...)` call if `part_j_worker.jl` is not present next
#  to this file, same as the original would.
#
################################################################################
module NormElimDiag

using Oscar
using ..Elim2: locate_engine_default
using ..Elim2Main: DecoupledSystem

################################################################################
# Struct: DiagCurveConfig -- this script's own copy of the curve/field
# constants (identical values to Elim2Main.CurveConfig, but kept as an
# independent struct/constructor since the original file never shared
# this state with elim2.jl proper). Original top-level consts: p,
# F_POLY_ASC, F (this script's OWN copies, redeclared here).
################################################################################
struct DiagCurveConfig
    p::Int
    F_POLY_ASC::Vector{Int}
    F  # GF(p)
end

function default_diag_curve_config()
    p = 2371157
    F_POLY_ASC = [2, 1, 0, 0, 0, 1]   # y^2 = x^5 + x + 2, ascending coeffs
    F = GF(p)
    return DiagCurveConfig(p, F_POLY_ASC, F)
end

"""
    default_diag_sample1()

Original lines 1148-1150: sample 1's (K,c,fixed,u0,u1,v0,v1) tuple,
this script's own copy (identical values to Elim2Main.default_sample1()).
Returned as a plain NamedTuple rather than Elim2Main.SampleSpec, since
this script never imported that struct in the original.
"""
function default_diag_sample1()
    return (K = 2, c = 2, fixed = Tuple{Int,Int}[],
            u0 = 468873, u1 = 956582, v0 = 2168176, v1 = 2288437)
end

"""
    run_sample1_residual(PhiSymbolic, spec, cfg)

Original lines 1152-1160: calls PhiSymbolic.symbolic_residual for sample
1 only, checks it isn't degenerate, prints its degrees.
"""
function run_sample1_residual(PhiSymbolic, spec, cfg::DiagCurveConfig)
    println("Calling PhiSymbolic.symbolic_residual for sample 1 (K=$(spec.K), c=$(spec.c))...")
    res1 = PhiSymbolic.symbolic_residual(spec.K, spec.c, spec.fixed, spec.u0, spec.u1,
                                          spec.v0, spec.v1, cfg.F_POLY_ASC, cfg.p)
    if isempty(res1.u_RS_coeffs) || isempty(res1.v_RS_coeffs)
        error("sample 1 (K=$(spec.K)): construction failed or degenerate -- no u_RS/v_RS to test")
    end
    println("sample 1: deg(u_RS)=$(length(res1.u_RS_coeffs)-1)  deg(v_RS)=$(length(res1.v_RS_coeffs)-1)")
    println()
    return res1
end

################################################################################
# Struct: DiagRing -- this script's own single-sample target ring (JUST
# wa1,wa2,a1,a2 -- 4 variables, no b's, no U/V target vars at this
# stage). Original top-level: R, (wa1,wa2,a1,a2), curve_a1, curve_a2.
################################################################################
struct DiagRing
    R
    wa1; wa2; a1; a2
    curve_a1; curve_a2
end

"""
    build_diag_ring(cfg)

Original lines 1169-1172.
"""
function build_diag_ring(cfg::DiagCurveConfig)
    R, (wa1, wa2, a1, a2) = polynomial_ring(cfg.F, ["wa1", "wa2", "a1", "a2"])
    curve_a1 = wa1^2 - (a1^5 + a1 + 2)
    curve_a2 = wa2^2 - (a2^5 + a2 + 2)
    return DiagRing(R, wa1, wa2, a1, a2, curve_a1, curve_a2)
end

################################################################################
# Tower -> ring flattening, copied verbatim from elim2.jl's own
# _tower_to_ring / _base_frac_to_ring / _reduce_frac (original lines
# 1179-1225), restricted to a single sample and single-threaded (no
# Threads.@threads here, unlike Elim2Main.map_coeffs_threaded -- the
# original norm_elim_diag.jl used a plain sequential loop).
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

function map_coeffs(coeffs, t_gens, w_gens)
    n = length(coeffs)
    nums = Vector{Any}(undef, n)
    dens = Vector{Any}(undef, n)
    for i in 1:n
        nums[i], dens[i] = tower_to_ring(coeffs[i], t_gens, w_gens)
    end
    return nums, dens
end

################################################################################
# Struct: DiagMapped -- sample 1's u_RS/v_RS coefficients flattened into
# DiagRing.R, plus N_U_MATCH (the trivial leading u_RS coefficient
# dropped, same convention as Elim2Main). Original top-level: t_gens_1,
# w_gens_1, u1_num, u1_den, v1_num, v1_den, N_U_MATCH.
################################################################################
struct DiagMapped
    t_gens::Vector
    w_gens::Vector
    u_num::Vector
    u_den::Vector
    v_num::Vector
    v_den::Vector
    N_U_MATCH::Int
end

"""
    map_sample1(res1, dring)

Original lines 1214-1248: flattens sample 1's coefficients into
DiagRing.R and reports per-sample sizes before any elimination.
"""
function map_sample1(res1, dring::DiagRing)
    t_gens_1 = [dring.a1, dring.a2]
    w_gens_1 = [dring.wa1, dring.wa2]

    println("Flattening sample 1's u_RS, v_RS coefficients into F[wa1,wa2,a1,a2]...")
    u1_num, u1_den = map_coeffs(res1.u_RS_coeffs, t_gens_1, w_gens_1)
    v1_num, v1_den = map_coeffs(res1.v_RS_coeffs, t_gens_1, w_gens_1)
    println("done.")
    println()

    N_U_MATCH = length(u1_num) - 1

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

    return DiagMapped(t_gens_1, w_gens_1, u1_num, u1_den, v1_num, v1_den, N_U_MATCH)
end

################################################################################
# THE ACTUAL QUESTION (original lines 1250-1420): per-coefficient,
# per-sample norm elimination of wa2 then wa1 from the matching equation
# h = num - U*den. See the original file's extensive derivation comment
# (reproduced narratively above each function below) for why this must
# be done on num-U*den jointly rather than on num,den's norms
# separately, and why reduce_mod_curves must run before AND after every
# split_linear/norm step (the sympy-caught cross-term bug: squaring a
# wa2-linear coefficient that itself contains wa1 reintroduces wa1^2,
# which the free polynomial ring does not auto-reduce).
################################################################################

# f(a) = a^5 + a + 2, evaluated symbolically at whichever anchor variable
f_of(a) = a^5 + a + 2

"""
    reduce_mod_curves(g, wa1, a1, wa2, a2)

Original lines 1339-1360. Reduces `g` modulo wa1^2 -> f(a1), wa2^2 ->
f(a2) at every even power up to 12 (k from 6 down to 1), repeating until
a fixed point -- necessary before AND after every split_linear/norm step
so that step's degree-<=1-in-w precondition genuinely holds in the free
polynomial ring (which does not auto-reduce w_i^2).
"""
function reduce_mod_curves(g, wa1, a1, wa2, a2)
    changed = true
    while changed
        changed = false
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

"""
    split_linear(g, w)

Original lines 1362-1374. `g` must be degree <=1 in `w` AFTER
reduce_mod_curves has already been applied -- asserts this rather than
silently mis-splitting (this assert is what originally caught the
cross-term bug).
"""
function split_linear(g, w)
    d = degree(g, w)
    @assert d <= 1 "expected degree <=1 in $w after curve reduction, got $d " *
                    "-- reduce_mod_curves did not fully linearize; check its loop bound (k up to 6) " *
                    "is high enough for this g's actual degree in $w"
    Q = coeff(g, [w], [1])
    P = g - Q * w
    return P, Q
end

"""
    norm_eliminate_step(g, w, a_anchor, wa1, a1, wa2, a2)

Original lines 1376-1385. Reduces mod curves, splits linearly in `w`,
takes the norm P^2 - Q^2*f(a_anchor), then reduces mod curves again
(squaring can reintroduce even powers of the OTHER w).
"""
function norm_eliminate_step(g, w, a_anchor, wa1, a1, wa2, a2)
    g = reduce_mod_curves(g, wa1, a1, wa2, a2)
    P, Q = split_linear(g, w)
    result = P^2 - Q^2 * f_of(a_anchor)
    return reduce_mod_curves(result, wa1, a1, wa2, a2)
end

"""
    run_norm_elim_for_coeff(label, num, den, U_placeholder_name, dring)

Original lines 1387-1420. Builds h0 = num - U*den in a fresh 5-variable
ring (wa1,wa2,a1,a2,U_placeholder_name), norm-eliminates wa2 then wa1,
and reports degree/terms at each stage.
"""
function run_norm_elim_for_coeff(label, num, den, U_placeholder_name, dring::DiagRing)
    println("=" ^ 70)
    println(label)
    println("=" ^ 70)

    Rh, (wa1h, wa2h, a1h, a2h, Uh) = polynomial_ring(
        base_ring(dring.R), ["wa1", "wa2", "a1", "a2", U_placeholder_name]
    )
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

"""
    run_norm_elim_experiment(dmapped, dring)

Original lines 1427-1465: runs `run_norm_elim_for_coeff` on every u_RS
and v_RS coefficient of sample 1 (the whole norm-elimination experiment
-- no Groebner basis, no cross-sample anything), then prints the
supervisor-facing summary table.
"""
function run_norm_elim_experiment(dmapped::DiagMapped, dring::DiagRing)
    results = Dict{String,Any}()

    for i in 1:dmapped.N_U_MATCH
        results["u1_$i"] = run_norm_elim_for_coeff(
            "u1 coefficient x^$(i-1)  (norm-eliminate wa2 then wa1)",
            dmapped.u_num[i], dmapped.u_den[i], "U", dring)
    end

    for i in 1:length(dmapped.v_num)
        results["v1_$i"] = run_norm_elim_for_coeff(
            "v1 coefficient x^$(i-1)  (norm-eliminate wa2 then wa1)",
            dmapped.v_num[i], dmapped.v_den[i], "V", dring)
    end

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

    return results
end

################################################################################
# run_with_timeout -- shared timing helper for PARTS B/C/D/G/H/H'. See
# the original's extensive caveat (reproduced in the docstring): this
# cannot truly KILL a hung Singular/msolve C call, only stop WAITING for
# it; a genuinely reclaiming kill needs an OS-level `timeout N julia ...`
# subprocess instead (not done here, matching the original, which notes
# this as a known limitation rather than fixing it).
################################################################################

"""
    run_with_timeout(f, limit_secs; poll_secs=1.0)

Original lines 1594-1616. Runs `f` (a zero-arg closure) on a background
Task, polling every `poll_secs` up to `limit_secs`. Returns `(value,
:ok, elapsed)`, `(nothing, :error, elapsed)`, or `(nothing, :timeout,
elapsed)`. CAVEAT (original comment, preserved): if `f` blocks in a
Singular/msolve C call, this reports `:timeout` correctly but the
underlying computation is NOT reclaimed -- it keeps running in the
background for the rest of the Julia session. This is exactly what the
original file documents caused a Singular allocator segfault when Part
B's k=3 step started a second concurrent Singular call while k=2's
still-running background Task held allocator state (see
`run_part_b_subideal_sweep!`'s docstring). A true kill requires an
OS-level `timeout N julia -e '...'` subprocess instead, which Part J
(further below) actually does for its own (differently-shaped) reason.
"""
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
# PART A: static diagnostics on Fu_decoupled + curve generators (no
# Groebner call -- pure structural facts). Takes Elim2Main's
# DecoupledSystem as an explicit argument rather than reaching for
# module-level globals, since this is the point where norm_elim_diag.jl
# (a standalone script in the original) starts operating on state that,
# in the original flat file, was actually built earlier by elim2.jl
# proper (R_dec, Fu_decoupled, curve_*_d) -- i.e. this is the boundary
# where the two originally-separate scripts' state genuinely merges.
################################################################################

"""
    run_part_a_static_diagnostics(decoupled)

Original lines 1529-1566 (PART A). Reports degree/terms/#vars/
homogeneity and a total-degree term-count histogram for every
Fu_decoupled generator plus the four curve relations -- no Groebner
call.
"""
function run_part_a_static_diagnostics(decoupled::DecoupledSystem)
    println()
    println("===========================================================")
    println("PART A: static diagnostics on Fu_decoupled + curve generators")
    println("(no Groebner call -- pure structural facts)")
    println("===========================================================")
    println()

    curve_gens_d = [decoupled.curve_a1_d, decoupled.curve_a2_d,
                    decoupled.curve_b1_d, decoupled.curve_b2_d]
    all_gens_for_diag = vcat(decoupled.Fu_decoupled, curve_gens_d)
    diag_labels = vcat(["Fu_decoupled[$i]" for i in 1:length(decoupled.Fu_decoupled)],
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
    println("Ambient ring R_dec has ", ngens(decoupled.R_dec), " variables: ", symbols(decoupled.R_dec))
    println()

    return (all_gens_for_diag = all_gens_for_diag, diag_labels = diag_labels, curve_gens_d = curve_gens_d)
end

################################################################################
# PART B: incremental sub-ideal sweep.
################################################################################

"""
    run_part_b_subideal_sweep!(decoupled, curve_gens_d; full_sweep=false)

Original lines 1622-1699 (PART B). Builds `ideal(Fu_decoupled[1:k],
curves)` for k in 1..length(Fu_decoupled) (or just k=1 if
`full_sweep=false`) and eliminates the four w's from each, timing every
step against `SUBIDEAL_TIMEOUT_SECS`.

EVIDENCE FROM THE ORIGINAL RUN (preserved from the original comment,
since it is the reason `full_sweep` defaults to `false`): k=1 completed
in 15s (degree 36, 1445 terms). k=2 timed out at 300s, and the k=3 step
that followed triggered a Singular segfault (omalloc bin-page crash
inside redtailBbb) -- most likely because the k=2 background Task from
`run_with_timeout` was still running when k=3 started a second
concurrent Singular call against shared allocator state. A segfault
kills the entire Julia process and is not catchable by
`run_with_timeout`'s try/catch, so leaving `full_sweep=true` risks
crashing before PART G (which answers the same cross-sample question
safely via fiber-product decomposition) ever runs.
"""
function run_part_b_subideal_sweep!(decoupled::DecoupledSystem, curve_gens_d::Vector; full_sweep::Bool=false)
    println("===========================================================")
    println("PART B: incremental sub-ideal sweep on Fu_decoupled")
    println("(each step: eliminate [wa1_d,wa2_d,wb1_d,wb2_d], timeout=",
            SUBIDEAL_TIMEOUT_SECS, "s)")
    if !full_sweep
        println("full_sweep=false: running only k=1 (confirmed safe/fast).")
        println("k=2 previously timed out and k=3 segfaulted Singular in this exact")
        println("construction -- see PART G below for the safe way to get the")
        println("k=2-equivalent answer via fiber-product decomposition.")
    end
    println("===========================================================")
    println()

    R_dec = decoupled.R_dec
    Fu_decoupled = decoupled.Fu_decoupled
    wa1_d, wa2_d, wb1_d, wb2_d = decoupled.wa1_d, decoupled.wa2_d, decoupled.wb1_d, decoupled.wb2_d

    k_range = full_sweep ? (1:length(Fu_decoupled)) : (1:1)

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
end

################################################################################
# PART C: incremental VARIABLE sweep. NOTE: the original wraps this
# entire loop in `if false # this times out ... end` -- i.e. it is dead
# code in the original file, never executed. Preserved as such: this
# function exists but `run_all_diagnostics` below does not call it,
# exactly mirroring the original's disabled state.
################################################################################

"""
    run_part_c_variable_sweep(decoupled; full_sweep=false)

Original lines 1744-1772 (PART C), inside the original's `if false #
this times out ... end` dead branch -- NOT called by `run_all_diagnostics`,
kept only as a defined-but-unreachable function so the original code is
not lost. Would eliminate wa1_d alone, then +wa2_d, then +wb1_d, then all
four, from the FULL `Iu_decoupled`, each against `VARSWEEP_TIMEOUT_SECS`.
"""
function run_part_c_variable_sweep(decoupled::DecoupledSystem; full_sweep::Bool=false)
    println("===========================================================")
    println("PART C: incremental VARIABLE sweep on full Iu_decoupled")
    println("(timeout=", VARSWEEP_TIMEOUT_SECS, "s per step)")
    if !full_sweep
        println("full_sweep=false: running only step 1 (wa1_d alone).")
        println("Steps 2-4 add more variables/cross-sample coupling and risk the")
        println("same timeout/segfault seen in Part B k=2/k=3 -- see PART G below")
        println("for the safe, decomposed way to get the cross-sample answer.")
    end
    println("===========================================================")
    println()

    wa1_d, wa2_d, wb1_d, wb2_d = decoupled.wa1_d, decoupled.wa2_d, decoupled.wb1_d, decoupled.wb2_d
    var_prefixes = [
        ("wa1_d only",                     [wa1_d]),
        ("wa1_d, wa2_d (sample 1 only)",   [wa1_d, wa2_d]),
        ("wa1_d, wa2_d, wb1_d",            [wa1_d, wa2_d, wb1_d]),
        ("wa1_d, wa2_d, wb1_d, wb2_d (all)", [wa1_d, wa2_d, wb1_d, wb2_d]),
    ]
    prefixes_to_run = full_sweep ? var_prefixes : var_prefixes[1:1]

    for (label, vs) in prefixes_to_run
        println("--- eliminating: $label ---")
        result, status, elapsed = run_with_timeout(VARSWEEP_TIMEOUT_SECS) do
            eliminate(decoupled.Iu_decoupled, vs)
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
end

################################################################################
# PART D: cheap dimension/codimension diagnostics on the curve-only ideal
# and the smallest Part-B sub-ideal.
################################################################################

"""
    run_part_d_dim_codim(decoupled, curve_gens_d)

Original lines 1788-1818 (PART D). dim()/codim() on the full
Iu_decoupled are deliberately NOT called (see the module docstring's
note on `singular_groebner_generators` triggering an uncontrolled
default-ordering Groebner computation internally) -- only on the
4-generator curve-only ideal and on `Fu_decoupled[1]` + curves.
"""
function run_part_d_dim_codim(decoupled::DecoupledSystem, curve_gens_d::Vector)
    println("===========================================================")
    println("PART D: dim/codim diagnostics (curve ideal, and smallest sub-ideal)")
    println("===========================================================")
    println()

    R_dec = decoupled.R_dec

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
        I1 = ideal(R_dec, vcat([decoupled.Fu_decoupled[1]], curve_gens_d))
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
end

################################################################################
# PART E: confirm the ordering eliminate() is actually constructing.
################################################################################

"""
    run_part_e_ordering_note(decoupled)

Original lines 1836-1854 (PART E). Prints `block_ordering_dec` (only
consumed by direct `groebner_basis(...; ordering=)` calls) and a caveat
that `eliminate(I, vars)` does not expose its own internal ordering
object for inspection via any documented Oscar API.
"""
function run_part_e_ordering_note(decoupled::DecoupledSystem)
    println("===========================================================")
    println("PART E: ordering actually in use")
    println("===========================================================")
    println()
    println("block_ordering_dec (explicit, only consumed by direct groebner_basis")
    println("calls, NOT by eliminate()):")
    println("  ", decoupled.block_ordering_dec)
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
end

################################################################################
# PART G: FIBER-PRODUCT DECOMPOSITION. NOTE: the original wraps its
# per-pair loop body in `if false # this section segfaults ... end` --
# dead code in the original, preserved as such: `run_part_g_fiber_product`
# is defined but not called by `run_all_diagnostics`.
################################################################################

"""
    run_part_g_fiber_product(decoupled)

Original lines 1880-2018 (PART G), inside the original's `if false #
this section segfaults ... end` dead branch -- NOT called by
`run_all_diagnostics`. Would eliminate each of the two fiber-product
pairs (Fu_decoupled[1] vs [2] over U0; [3] vs [4] over U1)
INDEPENDENTLY in their own small remapped rings, then report the
combined generator count -- exploiting that
`elim_{wa,wb}(Ia + Ib) = elim_wa(Ia) + elim_wb(Ib)` when Ia, Ib share
only the target U-variable, so Singular never needs to see the full
joint system.
"""
function run_part_g_fiber_product(decoupled::DecoupledSystem)
    println()
    println("===========================================================")
    println("PART G: fiber-product decomposition (eliminate each side ")
    println("independently, then combine via shared U-variable)")
    println("===========================================================")
    println()

    Fu_decoupled = decoupled.Fu_decoupled
    U_vars = decoupled.U_vars
    curve_gens_d_local = [decoupled.curve_a1_d, decoupled.curve_a2_d,
                           decoupled.curve_b1_d, decoupled.curve_b2_d]
    R_dec = decoupled.R_dec
    F = base_ring(R_dec)

    fiber_pairs = [
        ("U0", Fu_decoupled[1], Fu_decoupled[2], U_vars[1]),
        ("U1", Fu_decoupled[3], Fu_decoupled[4], U_vars[2]),
    ]

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

        # Side A: self-contained ring with only the variables ga uses.
        a_vars_sorted = sort(vars(ga); by = string)
        Ra, ra_gens = polynomial_ring(F, string.(a_vars_sorted))
        a_remap = Dict(zip(a_vars_sorted, ra_gens))
        full_remap_a = [v in a_vars_sorted ? a_remap[v] : zero(Ra) for v in gens(R_dec)]
        ga_small = evaluate(ga, full_remap_a)

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
end

################################################################################
# PART H: FULLY INDEPENDENT small-ring reconstruction (not a restriction
# of Part G) -- U0 only. Builds sample 1's and sample 2's u_num[1]/u_den[1]
# into brand-new 5-variable rings from scratch, with NO reference to
# R_dec/Iu_decoupled/Fu_decoupled.
################################################################################

"""
    run_part_h_isolated_u0(dmapped, s2::Elim2Main.MappedSample)

Original lines 2057-2224 (PART H). `dmapped` is this submodule's own
sample-1 mapping (from `map_sample1`, giving `u1_num[1]/u1_den[1]` in
DiagRing's 4-variable ring). `s2` is Elim2Main's sample-2 MappedSample
(giving `u2_num[1]/u2_den[1]` in Elim2Main's original 8-variable ring
`[wa1,wa2,wb1,wb2,a2,a1,b2,b1]`) -- the original hardcodes that 8-slot
gens order when zeroing out sample 1's variables for sample 2's remap,
reproduced verbatim below rather than via a generic Dict-based helper,
matching the original's own comment about wanting this directly
inspectable.
"""
function run_part_h_isolated_u0(dmapped::DiagMapped, s2)
    println()
    println("===========================================================")
    println("PART H: fully independent small-ring reconstruction (no R_dec)")
    println("===========================================================")
    println()

    println("Building sample 1's isolated ring: [wa1, wa2, a1, a2, U0], from")
    println("u1_num[1]/u1_den[1] directly -- R_dec is not referenced anywhere below.")
    println()

    F = base_ring(parent(dmapped.u_num[1]))
    Rs1, (wa1_s, wa2_s, a1_s, a2_s, U0_s) = polynomial_ring(F, ["wa1", "wa2", "a1", "a2", "U0"])

    images_s1 = [wa1_s, wa2_s, a1_s, a2_s]
    u1_num1_s = evaluate(dmapped.u_num[1], images_s1)
    u1_den1_s = evaluate(dmapped.u_den[1], images_s1)
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
    if statusS1 == :ok
        gS1 = gens(resultS1)
        println("  status=OK  elapsed=", round(elapsedS1, digits=3), "s")
        println("  parent ring = ", base_ring(resultS1))
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

    # r_gens_full order is [wa1,wa2,wb1,wb2,a2,a1,b2,b1] -- images_s2
    # follows that SAME order: wa1,wa2,a2,a1 -> 0; wb1,wb2,b2,b1 -> their
    # Rs2 generators. Written out explicitly rather than via a generic
    # Dict-based remap helper, matching the original's own stated reason
    # (directly inspectable against r_gens_full's printed order).
    images_s2 = [zero(Rs2), zero(Rs2), wb1_s, wb2_s, b2_s, zero(Rs2), zero(Rs2), b1_s]
    u2_num1_s = evaluate(s2.u_num[1], images_s2)
    u2_den1_s = evaluate(s2.u_den[1], images_s2)
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
    if statusS2 == :ok
        gS2 = gens(resultS2)
        println("  status=OK  elapsed=", round(elapsedS2, digits=3), "s")
        println("  parent ring = ", base_ring(resultS2))
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
    # See the original file's extended note (reproduced in
    # run_with_timeout's docstring) on the redtailBbb/omalloc allocator
    # crash being consistent with two concurrent Singular calls sharing
    # global allocator state across independent Task-based threads.

    return (statusS1 = statusS1, statusS2 = statusS2)
end

################################################################################
# PART H': same isolated-small-ring test as PART H, but for V0/V1 instead
# of just U0. Gated off by default (PART_H_PRIME_ENABLED, ENV var
# ELIM2_RUN_PART_H_PRIME) since the original documents it as an
# already-validated, expensive re-check rather than something worth
# rerunning on every invocation.
################################################################################

const PART_H_PRIME_ENABLED = get(ENV, "ELIM2_RUN_PART_H_PRIME", "false") == "true"

# Expected values, read directly off the original run's own PART A
# printout (degree=25/terms=698 pre-elimination sizes for v1/v2 num[*]
# and Fv_decoupled). If a re-run disagrees with these, that disagreement
# is exactly the bug this section exists to catch -- not assumed.
const PART_H_PRIME_EXPECTED = Dict(
    ("V0", 1) => (h_degree = 25, h_terms = 698),
    ("V0", 2) => (h_degree = 25, h_terms = 698),
    ("V1", 1) => (h_degree = 25, h_terms = 698),
    ("V1", 2) => (h_degree = 25, h_terms = 698),
)

"""
    part_h_prime_build_and_eliminate(target_name, sample_num, num_coeff, den_coeff, t_names, w_names)

Original lines 2282-2391 (the `part_h_prime_build_and_eliminate` helper
inside PART H'). NOTE the original's own bisect comment, preserved
verbatim in spirit: sample 1's v/u_num live in the REBUILT 4-variable
ring (DiagRing.R in this refactor, via `dmapped`), while sample 2's stay
in the ORIGINAL 8-variable ring (Elim2Main's `tring.R`, via `s2`) --
callers must pass `num_coeff`/`den_coeff` from the matching source, and
the length-mismatch `@assert` below exists specifically because that
asymmetry is a real, recurring failure mode in the original file, not a
hypothetical one.
"""
function part_h_prime_build_and_eliminate(target_name::String, sample_num::Int,
                                            num_coeff, den_coeff,
                                            t_names::Vector{String}, w_names::Vector{String})
    println("Building $(target_name) sample $(sample_num)'s isolated ring: ",
            "[$(w_names[1]), $(w_names[2]), $(t_names[1]), $(t_names[2]), $(target_name)], from")
    println("v$(sample_num)_num/v$(sample_num)_den directly -- R_dec is not referenced.")
    println()

    F = base_ring(parent(num_coeff))
    Rloc, gensloc = polynomial_ring(F, [w_names[1], w_names[2], t_names[1], t_names[2], target_name])
    w1_l, w2_l, t1_l, t2_l, T_l = gensloc

    # Sample 1's num_coeff lives in the 4-variable ring [wa1,wa2,a1,a2];
    # sample 2's lives in the original 8-variable ring
    # [wa1,wa2,wb1,wb2,a2,a1,b2,b1]. images_local must match whichever
    # ring num_coeff actually came from -- see the @assert just below,
    # which is the original's own bisect checkpoint for exactly this.
    images_local = sample_num == 1 ?
        [w1_l, w2_l, t1_l, t2_l] :
        [zero(Rloc), zero(Rloc), w1_l, w2_l, zero(Rloc), zero(Rloc), t2_l, t1_l]
    @assert length(images_local) == nvars(parent(num_coeff)) (
        "PART H' bisect: images_local has $(length(images_local)) entries but " *
        "num_coeff for $(target_name) sample $(sample_num) lives in a ring with " *
        "$(nvars(parent(num_coeff))) variables -- sample 1's v/u_num live in the " *
        "rebuilt 4-variable R, sample 2's stay in the original 8-variable R; " *
        "check which one num_coeff actually came from before editing the mapping."
    )
    num_l = evaluate(num_coeff, images_local)
    den_l = evaluate(den_coeff, images_local)
    h_l = num_l - T_l * den_l

    println("  h = $(target_name)_num - $(target_name)*$(target_name)_den, rebuilt: degree=",
            total_degree(h_l), "  terms=", length(terms(h_l)))

    expected = get(PART_H_PRIME_EXPECTED, (target_name, sample_num), nothing)
    if expected !== nothing
        @assert total_degree(h_l) == expected.h_degree (
            "PART H' bisect: $(target_name) sample $(sample_num) pre-elimination h " *
            "has degree=$(total_degree(h_l)), expected $(expected.h_degree) from " *
            "this run's own PART A printout -- mismatch is BEFORE elimination, so " *
            "the bug is in the mapping/construction above, not in eliminate()."
        )
        @assert length(terms(h_l)) == expected.h_terms (
            "PART H' bisect: $(target_name) sample $(sample_num) pre-elimination h " *
            "has terms=$(length(terms(h_l))), expected $(expected.h_terms) -- " *
            "mismatch is BEFORE elimination; check the images_local mapping first."
        )
        println("  [assert OK] h matches this run's own PART A degree/terms for $(target_name).")
    else
        println("  [no expected value recorded for ($(target_name), sample $(sample_num)) -- skipping assert]")
    end
    println()

    curve1_l = w1_l^2 - (t1_l^5 + t1_l + 2)
    curve2_l = w2_l^2 - (t2_l^5 + t2_l + 2)

    Iloc = ideal(Rloc, [h_l, curve1_l, curve2_l])

    println("Eliminating [$(w_names[1]), $(w_names[2])] from I$(target_name)_$(sample_num) ",
            "(5-variable ring, 3 generators)...")
    resultLoc, statusLoc, elapsedLoc = run_with_timeout(SUBIDEAL_TIMEOUT_SECS) do
        eliminate(Iloc, [w1_l, w2_l])
    end

    if statusLoc == :ok
        gLoc = gens(resultLoc)
        println("  status=OK  elapsed=", round(elapsedLoc, digits=3), "s")
        println("  parent ring = ", base_ring(resultLoc))
        println("  number of generators = ", length(gLoc))
        for (i, g) in enumerate(gLoc)
            println("    gen $i: degree=", total_degree(g), "  terms=", length(terms(g)))
        end
        @assert length(gLoc) >= 1 (
            "PART H' bisect: $(target_name) sample $(sample_num) elimination " *
            "returned status=:ok but zero generators -- this is NOT the same " *
            "success PART H reported for U0 and should not be treated as such."
        )
    else
        println("  status=$statusLoc after ", round(elapsedLoc, digits=3), "s")
    end
    println()

    return (result = resultLoc, status = statusLoc, elapsed = elapsedLoc)
end

"""
    run_part_h_prime_isolated_v0v1(s1::Elim2Main.MappedSample, s2::Elim2Main.MappedSample)

Original lines 2256-2438 (PART H'). Gated by `PART_H_PRIME_ENABLED`
(`ENV["ELIM2_RUN_PART_H_PRIME"]="true"` to enable) exactly as in the
original -- calling this while the gate is off prints the original's
skip message and returns `nothing`. `s1`/`s2` are Elim2Main's
MappedSample for each sample (v1_num/v1_den, v2_num/v2_den).
"""
function run_part_h_prime_isolated_v0v1(s1, s2)
    if !PART_H_PRIME_ENABLED
        println()
        println("[PART H' skipped -- PART_H_PRIME_ENABLED=false. Set ENV[\"ELIM2_RUN_PART_H_PRIME\"]=\"true\" ",
                "to re-run the isolated small-ring V0/V1 elimination check.]")
        println()
        return nothing
    end

    println()
    println("===========================================================")
    println("PART H': isolated small-ring reconstruction, extended to V0/V1")
    println("(same construction as PART H, which only covered U0)")
    println("===========================================================")
    println()

    part_h_prime_results = Dict{Tuple{String,Int}, Any}()

    part_h_prime_results[("V0", 1)] = part_h_prime_build_and_eliminate(
        "V0", 1, s1.v_num[1], s1.v_den[1], ["a1", "a2"], ["wa1", "wa2"])
    part_h_prime_results[("V0", 2)] = part_h_prime_build_and_eliminate(
        "V0", 2, s2.v_num[1], s2.v_den[1], ["b1", "b2"], ["wb1", "wb2"])
    part_h_prime_results[("V1", 1)] = part_h_prime_build_and_eliminate(
        "V1", 1, s1.v_num[2], s1.v_den[2], ["a1", "a2"], ["wa1", "wa2"])
    part_h_prime_results[("V1", 2)] = part_h_prime_build_and_eliminate(
        "V1", 2, s2.v_num[2], s2.v_den[2], ["b1", "b2"], ["wb1", "wb2"])

    println("#" ^ 70)
    println("PART H' READOUT")
    println("#" ^ 70)
    println()
    for key in [("V0", 1), ("V0", 2), ("V1", 1), ("V1", 2)]
        r = part_h_prime_results[key]
        println("$(key[1]) sample $(key[2]) isolated elimination: ", r.status,
                r.status == :ok ? " ($(round(r.elapsed,digits=3))s)" : "")
    end
    println()

    all_v_ok = all(r.status == :ok for r in values(part_h_prime_results))
    if all_v_ok
        println("ALL FOUR V0/V1 isolated 5-variable eliminations succeeded, matching")
        println("PART H's U0 result. This closes the gap PART H left open: the")
        println("small-ring-reconstruction claim ('the pathology is an artifact of")
        println("the 12-variable ambient ring, not the elimination math') now holds")
        println("for every one of the 8 bench targets (U0,U1,V0,V1 x sample1,sample2),")
        println("not just U0. The 12-variable Iu_decoupled/Iuv_decoupled object should")
        println("not be needed again except as a cross-check artifact -- the per-")
        println("sample isolated-ring + multiplicity-correction pipeline (this section")
        println("+ correct_multiplicity below) is now evidenced as the full route.")
    else
        println("** At least one V0/V1 isolated elimination did NOT succeed -- this")
        println("BREAKS the generalization from PART H's U0-only result. Do not")
        println("assume the small-ring route works for V just because it worked for")
        println("U; the degree-25 V generators (vs degree-17 for U) may behave")
        println("differently. See per-case status above before proceeding. **")
    end
    println()

    return part_h_prime_results
end

################################################################################
# PART I: The Sandbox Factory (Automated Elimination) -- Groebner-free
# per-coefficient production pipeline via sequential resultants +
# correct_multiplicity, replacing the eliminate()/Groebner route entirely.
#
# canonical_factor_key/factor_multiset are defined here (matching the
# original's own "Forward declarations, hoisted..." comment: the
# original file is a flat top-to-bottom script with no function
# hoisting, so it redefines these -- identically -- a second time later,
# near part_i_squarefree_diag.jl's own definitions). Since this refactor
# uses functions (not top-level flat execution), only ONE definition of
# each is needed; PartISquarefreeDiag (the next submodule down) reuses
# these via `using ..NormElimDiag: canonical_factor_key, factor_multiset`
# rather than redefining them, so the "harmless redefinition" the
# original relied on is replaced here by ordinary code reuse.
################################################################################

"""
    canonical_factor_key(f) -> String

Original lines 2459-2490. Returns a hashable, order-independent,
unit-scaled key for an irreducible polynomial `f`, so two irreducible
factors coming out of independent `factor()` calls (potentially
differing by a nonzero field-element unit, and with no guaranteed
enumeration order) compare equal iff they are associates.

Normalization: divide by the coefficient of the lexicographically-first
monomial (in a fixed, deterministic term order), so the leading
coefficient of the normalized polynomial is always 1.
"""
function canonical_factor_key(f)
    R = parent(f)
    F = base_ring(R)
    exps = collect(AbstractAlgebra.exponent_vectors(f))
    cfs  = collect(coefficients(f))
    order = sortperm(exps)
    lead_c = cfs[order[1]]
    inv_lead = inv(lead_c)
    io = IOBuffer()
    for idx in order
        c = cfs[idx] * inv_lead
        print(io, string(c), ":", string(exps[idx]), ";")
    end
    return String(take!(io))
end

"""
    factor_multiset(f) -> (Dict{String,Int}, factorization)

Original lines 2492-2507. Factors `f` and returns a map:
canonical_factor_key(irreducible factor) => exponent, plus the raw
factorization object.
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
    correct_multiplicity_legacy(Res2)

SUPERSEDED -- original lines 2514-2621. Not called anywhere in this
file (both `process_sample_1_coeff` and `process_sample_2_coeff` call
the general 2-argument `correct_multiplicity(Res1, Res2; label="")`
defined in PartISquarefreeDiag instead). Kept only because the original
kept it (Julia dispatches it and the 2-arg version as separate methods
of the same name; not deleted since that wasn't asked for in the
original either). Renamed from `correct_multiplicity` to
`correct_multiplicity_legacy` here since this refactor's module system
does not auto-merge same-named functions across submodules the way flat
top-level `function` redefinition did in the original -- giving it a
distinct name preserves both definitions instead of one silently
shadowing the other. Hardcodes the correction exponent from the target
variable's name (U->4, V->6) and errors out if there's more than one
degree-8 factor, instead of handling every inflated factor a
Res1-vs-Res2 comparison finds -- do not wire this back in.
"""
function correct_multiplicity_legacy(Res2)
    R = parent(Res2)
    ring_vars = gens(R)
    if isempty(ring_vars)
        error("The resultant parent ring has no generators.")
    end

    target_var = ring_vars[end]
    target_str = string(target_var)

    coord_char = uppercase(target_str[1])
    if coord_char == 'U'
        exponent = 4
    elseif coord_char == 'V'
        exponent = 6
    else
        error("Could not determine coordinate ('U' or 'V') from target variable: $target_str")
    end

    local factors
    try
        factors = factor(Res2)
    catch e
        error("Failed to factor the second resultant Res2: ", e)
    end

    get_poly_degree(p) = begin
        try
            return total_degree(p)
        catch
            try
                return degree(p)
            catch
                error("Unable to determine degree of factor: $p")
            end
        end
    end

    f_infl = nothing
    f_infl_mult = 0

    for (fac, mult) in factors
        if get_poly_degree(fac) == 8
            if f_infl !== nothing
                error("Ambiguity detected: Found multiple distinct degree-8 factors in Res2:\n" *
                      "  1) $f_infl\n" *
                      "  2) $fac\n" *
                      "Cannot deterministically isolate the true inflation factor.")
            end
            f_infl = fac
            f_infl_mult = mult
        end
    end

    if f_infl === nothing
        fac_list = [(fac, mult) for (fac, mult) in factors]
        error("Mathematical assumption violated: Could not find the expected degree-8 " *
              "inflation factor in the factorization of Res2.\n" *
              "Factors found: $fac_list")
    end

    if f_infl_mult < exponent
        error("The identified degree-8 inflation factor ($f_infl) has multiplicity $f_infl_mult " *
              "in Res2, which is less than the required exponent of $exponent for coordinate '$coord_char'.")
    end

    divisor = f_infl^exponent
    success, corrected_poly = divides(Res2, divisor)

    if !success
        error("Exact division failed: Non-zero remainder when dividing Res2 by F_infl^$exponent.")
    end

    return (corrected = corrected_poly, inflation_factor = f_infl, exponent = exponent)
end

"""
    process_sample_1_coeff(raw_coeff, target_name, dring, correct_multiplicity_fn)

Original lines 2638-2670 (Factory for Sample 1, uses 'a' variables).
Groebner-free rewrite: builds the 5-variable sandbox
[wa1,wa2,a1,a2,target_name], flattens `raw_coeff` via `tower_to_ring`,
forms `h = T*den - num`, then eliminates w1 then w2 via SEQUENTIAL
RESULTANTS (`resultant(h, curve1, w1)` then `resultant(step1, curve2,
w2)`) rather than `eliminate()`'s Groebner-basis route, and divides out
the excess multiplicity the resultant chain introduces via
`correct_multiplicity_fn` (the caller passes PartISquarefreeDiag's
2-argument `correct_multiplicity`, matching what the original wired
this to). This route was checked (CHECK_GROEBNER=true runs of
`_run_bench`, in PartIBench below) to reproduce the Groebner-based
`eliminate()` generator exactly.
"""
function process_sample_1_coeff(raw_coeff, target_name, dring::DiagRing, correct_multiplicity_fn)
    println("  Spinning up sandbox for: ", target_name)

    R_small, (w1, w2, a1, a2, T) = polynomial_ring(base_ring(dring.R), ["wa1", "wa2", "a1", "a2", target_name])

    t_gens = [a1, a2]
    w_gens = [w1, w2]
    num_s, den_s = tower_to_ring(raw_coeff, t_gens, w_gens)

    h_s = T * den_s - num_s

    curve1 = w1^2 - (a1^5 + a1 + 2)
    curve2 = w2^2 - (a2^5 + a2 + 2)

    step1 = resultant(h_s, curve1, w1)
    step2 = resultant(step1, curve2, w2)

    corr = correct_multiplicity_fn(step1, step2)

    return corr.corrected
end

"""
    process_sample_2_coeff(raw_coeff, target_name, dring, correct_multiplicity_fn)

Original lines 2678-2709 (Factory for Sample 2, uses 'b' variables
instead of 'a'). Mirrors `process_sample_1_coeff` exactly, just with
`wb1,wb2,b1,b2` in place of `wa1,wa2,a1,a2`.
"""
function process_sample_2_coeff(raw_coeff, target_name, dring::DiagRing, correct_multiplicity_fn)
    println("  Spinning up sandbox (Sample 2) for: ", target_name)

    R_small, (w1, w2, b1, b2, T) = polynomial_ring(base_ring(dring.R), ["wb1", "wb2", "b1", "b2", target_name])

    t_gens = [b1, b2]
    w_gens = [w1, w2]
    num_s, den_s = tower_to_ring(raw_coeff, t_gens, w_gens)

    h_s = T * den_s - num_s

    curve1 = w1^2 - (b1^5 + b1 + 2)
    curve2 = w2^2 - (b2^5 + b2 + 2)

    step1 = resultant(h_s, curve1, w1)
    step2 = resultant(step1, curve2, w2)

    corr = correct_multiplicity_fn(step1, step2)

    return corr.corrected
end

################################################################################
# PART J: The Assembly Line -- dispatches process_sample_{1,2}_coeff's
# work to separate OS-process workers (`julia part_j_worker.jl`), NOT
# Threads.@spawn, because PART H already demonstrated that two
# eliminate()/Singular calls sharing one process's global omalloc
# allocator state can crash. Each job is its own subprocess with its own
# address space.
#
# `part_j_worker.jl` itself is an EXTERNAL file, not one of the two
# uploaded to this refactor -- it was not part of elim2.jl or
# elim2_refactored.jl's own content, only referenced by path. This
# function reproduces the launcher/poller exactly, but `run_part_j!`
# will fail at the `run(cmd; wait=false)` call if that worker script
# is not present next to this file, same as the original would.
################################################################################

const PART_J_MAX_WORKERS = 4

"""
    run_part_j!(res1, output_dir=joinpath(@__DIR__, "tmp"), worker_path=joinpath(@__DIR__, "part_j_worker.jl"))

Original lines 2711-2848 (PART J). Builds the list of (sample,target)
jobs from `res1`'s u_RS/v_RS coefficient counts (skipping u_RS's trivial
leading "1"), skips any job whose output file already exists (persistent
across runs, no cleanup), then runs the remaining jobs through a bounded
worker pool of at most `PART_J_MAX_WORKERS` concurrent `julia
part_j_worker.jl <sample> <target> <outfile>` subprocesses, launching
the next queued job into any freed slot as each process exits. Raises an
error immediately if any worker subprocess exits with a nonzero code.
Returns `(clean_sample_1, clean_sample_2)`, the loaded results in the
same U0,U1,...,V0,V1,... order as the original's sequential loop.
"""
function run_part_j!(res1;
                      output_dir::String = joinpath(@__DIR__, "tmp"),
                      worker_path::String = joinpath(@__DIR__, "part_j_worker.jl"))
    println("===========================================================")
    println("PART J: The Assembly Line (Processing All Coefficients)")
    println("===========================================================")

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

    mkpath(output_dir)

    part_j_jobs_full = map(part_j_jobs) do job
        outfile = joinpath(output_dir, "sample$(job.sample)_$(job.target).oscar")
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

    part_j_queue = collect(part_j_todo)
    part_j_running = Vector{NamedTuple}()
    part_j_next_idx = Ref(1)

    function part_j_launch_next!()
        part_j_next_idx[] > length(part_j_queue) && return nothing
        jf = part_j_queue[part_j_next_idx[]]
        part_j_next_idx[] += 1
        println("  Spinning up sandbox", jf.job.sample == 2 ? " (Sample 2)" : "", " for: ", jf.job.target)
        cmd = `julia $worker_path $(jf.job.sample) $(jf.job.target) $(jf.outfile)`
        proc = run(pipeline(cmd; stdout=stdout, stderr=stderr); wait=false)
        push!(part_j_running, (job = jf.job, outfile = jf.outfile, proc = proc))
        return nothing
    end

    for _ in 1:min(PART_J_MAX_WORKERS, length(part_j_queue))
        part_j_launch_next!()
    end

    while !isempty(part_j_running)
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

    clean_sample_1 = Any[]
    clean_sample_2 = Any[]

    for jf in part_j_jobs_full
        if !isfile(jf.outfile)
            error("Part J: expected output file missing for sample=$(jf.job.sample) " *
                  "target=$(jf.job.target): $(jf.outfile)")
        end
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

    return (clean_sample_1 = clean_sample_1, clean_sample_2 = clean_sample_2)
end

"""
    run_norm_elim_diag(PhiSymbolic; full_sweep_b=false, full_sweep_c=false)

Top-level entry point reproducing norm_elim_diag.jl's own original
end-to-end behavior in original top-to-bottom order (PARTS C/G are
defined above but were dead code in the original -- `if false` blocks --
and are NOT called here either, matching the original exactly). Runs
sample-1-only setup (`run_sample1_residual`/`build_diag_ring`/
`map_sample1`) and the norm-elimination experiment
(`run_norm_elim_experiment`); does NOT run PARTS A/B/D/E/G/H/H'/I/J,
since those original lines operate on Elim2Main's DecoupledSystem state
(built later, from BOTH samples) rather than this standalone sample-1
diagnostic -- call those separately via `run_part_a_static_diagnostics`,
etc., once a `DecoupledSystem` is available (see `Elim2.run_all`).
"""
function run_norm_elim_diag(PhiSymbolic; full_sweep_b::Bool=false, full_sweep_c::Bool=false)
    cfg = default_diag_curve_config()
    spec = default_diag_sample1()
    res1 = run_sample1_residual(PhiSymbolic, spec, cfg)
    dring = build_diag_ring(cfg)
    dmapped = map_sample1(res1, dring)
    results = run_norm_elim_experiment(dmapped, dring)
    return (res1 = res1, cfg = cfg, dring = dring, dmapped = dmapped, results = results)
end

end # module NormElimDiag

PLACEHOLDER_FOR_PARTISQUAREFREEDIAG

end # module Elim2
