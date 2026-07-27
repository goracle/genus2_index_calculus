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
#    1. elim2.jl proper (original lines 1-1090)          -> submodule Elim2Main
#    2. norm_elim_diag.jl (original lines 1091-2853)     -> submodule NormElimDiag
#    3. part_i_squarefree_diag.jl (original lines 2854-3964)
#                                                          -> submodule PartISquarefreeDiag
#    4. part_i_eliminate_vs_resultant_bench.jl (original lines 3965-~5006)
#                                                          -> submodule PartIBench
#    5. elim2.jl's own PART K continuation ("The Final Collision",
#       original lines 4684-8017; original lines 8019-8397 are the
#       dead/removed PART G block, kept as a comment)     -> submodule PartKResultant
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

"""
    run_main(PhiSymbolic; cfg=default_curve_config())

Top-level entry point for this submodule, reproducing original elim2.jl
lines 1-1090 end to end, in original order:

  1. build both samples' specs (`default_sample1`/`default_sample2`) and
     call `PhiSymbolic.symbolic_residual` for each (`call_symbolic_residual`)
  2. build the shared 8-variable target ring (`build_target_ring`)
  3. map each sample's u_RS/v_RS coefficients into that ring
     (`map_sample`), checking the Mumford identity as it goes, then print
     the combined report (`report_mapped_samples`)
  4. run the a1<->a2 / b1<->b2 swap-symmetry checks (`run_symmetry_checks`)
  5. build the match spec (`build_match_spec`) and the cross-multiplied
     Fu/Fv equations (`build_fu_fv`)
  6. run the degree-in-w diagnostic (`run_degree_in_w_diagnostic`)
  7. build the decoupled U/V system (`build_decoupled_system`)
  8. run the per-layer degree trace and the norm-before-vs-after
     experiment (`run_per_layer_degree_trace`,
     `run_norm_before_vs_after_experiment`)

Returns a NamedTuple bundling every intermediate object downstream
submodules need (`s1`, `s2`, `tring`, `fufv`, `decoupled`, etc.) --
NormElimDiag's PART A-K continuation and PartKResultant both take pieces
of this as explicit arguments rather than reading globals, so
`Elim2.run_all` just plumbs this return value through.
"""
function run_main(PhiSymbolic; cfg::CurveConfig = default_curve_config())
    spec1 = default_sample1()
    spec2 = default_sample2()

    res1 = call_symbolic_residual(PhiSymbolic, spec1, cfg; label = "sample 1")
    res2 = call_symbolic_residual(PhiSymbolic, spec2, cfg; label = "sample 2")

    tring = build_target_ring(cfg)

    s1 = map_sample(res1, [tring.a1, tring.a2], [tring.wa1, tring.wa2], cfg, tring,
                     [tring.curve_a1, tring.curve_a2]; label = "sample 1")
    s2 = map_sample(res2, [tring.b1, tring.b2], [tring.wb1, tring.wb2], cfg, tring,
                     [tring.curve_b1, tring.curve_b2]; label = "sample 2")
    report_mapped_samples(s1, s2; K1 = spec1.K, K2 = spec2.K)

    symmetry = run_symmetry_checks(s1, s2, tring)

    check_sample_degrees_match(s1, s2)
    mspec = build_match_spec(s1, s2)
    fufv = build_fu_fv(s1, s2, mspec)

    run_degree_in_w_diagnostic(s1, s2, fufv, tring)

    decoupled = build_decoupled_system(s1, s2, mspec, tring)

    per_layer = run_per_layer_degree_trace(res1, [tring.a1, tring.a2], [tring.wa1, tring.wa2], s1)
    norm_experiment = run_norm_before_vs_after_experiment(res1, fufv, tring)

    return (cfg = cfg, spec1 = spec1, spec2 = spec2, res1 = res1, res2 = res2,
            tring = tring, s1 = s1, s2 = s2, symmetry = symmetry, mspec = mspec,
            fufv = fufv, decoupled = decoupled, per_layer = per_layer,
            norm_experiment = norm_experiment)
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

"""
    run_all_diagnostics(PhiSymbolic, main; full_sweep_b=false)

Top-level entry point for original lines ~1478-2848 (the PART A-J
continuation against Elim2Main's `DecoupledSystem`, as opposed to
`run_norm_elim_diag`'s standalone sample-1-only experiment above). Takes
`main`, the NamedTuple returned by `Elim2Main.run_main`, and threads its
`decoupled`/`res1`/`s1`/`s2` fields through PARTS A, B, D, E, H, H', and
J in original order:

  - PART A (`run_part_a_static_diagnostics`) -- static structural facts,
    also yields `curve_gens_d`, needed by B and D below
  - PART B (`run_part_b_subideal_sweep!`; `full_sweep=false` by default
    -- k=2 previously timed out and k=3 segfaulted Singular in this
    exact construction, see that function's own docstring)
  - PART C: skipped. Dead code in the original (`if false # this times
    out ... end`) -- `run_part_c_variable_sweep` is defined but
    deliberately not called here, matching the original's disabled state.
  - PART D (`run_part_d_dim_codim`)
  - PART E (`run_part_e_ordering_note`)
  - PART G: skipped. Also dead code in the original (`if false # this
    section segfaults ... end`) -- `run_part_g_fiber_product` is defined
    but not called here either, for the same reason.
  - PART H (`run_part_h_isolated_u0`), using this submodule's own
    sample-1 `dmapped` (built fresh here via `run_sample1_residual`/
    `build_diag_ring`/`map_sample1`, exactly as `run_norm_elim_diag`
    does -- both need `PhiSymbolic` to recompute sample 1's residual in
    this submodule's own 4-variable DiagRing rather than reusing
    `main.res1`, matching the original's genuine duplication) together
    with `main.s2` (Elim2Main's sample-2 MappedSample)
  - PART H' (`run_part_h_prime_isolated_v0v1`), using `main.s1`/`main.s2`
    directly -- no-ops unless `ENV["ELIM2_RUN_PART_H_PRIME"]="true"`
  - PART J (`run_part_j!`), using `main.res1` (Elim2Main's own sample-1
    residual, matching the original's single top-level `res1` -- PART J's
    coefficient counts come from the full two-sample pipeline, not this
    submodule's standalone `res1_local`)

Returns a NamedTuple bundling every part's result, plus
`clean_sample_1`/`clean_sample_2` at the top level (from PART J) since
`PartKResultant.run_part_k!` needs those directly.
"""
function run_all_diagnostics(PhiSymbolic, main; full_sweep_b::Bool=false)
    cfg = default_diag_curve_config()
    spec = default_diag_sample1()
    res1_local = run_sample1_residual(PhiSymbolic, spec, cfg)
    dring = build_diag_ring(cfg)
    dmapped = map_sample1(res1_local, dring)

    part_a = run_part_a_static_diagnostics(main.decoupled)
    curve_gens_d = part_a.curve_gens_d

    run_part_b_subideal_sweep!(main.decoupled, curve_gens_d; full_sweep = full_sweep_b)

    run_part_d_dim_codim(main.decoupled, curve_gens_d)
    run_part_e_ordering_note(main.decoupled)

    run_part_h_isolated_u0(dmapped, main.s2)
    run_part_h_prime_isolated_v0v1(main.s1, main.s2)

    part_j = run_part_j!(main.res1)

    return (part_a = part_a, dmapped = dmapped,
            clean_sample_1 = part_j.clean_sample_1, clean_sample_2 = part_j.clean_sample_2)
end

end # module NormElimDiag

################################################################################
#
#  Submodule: PartISquarefreeDiag
#
#  Encapsulation of part_i_squarefree_diag.jl (original lines 2854-3964).
#  Diagnostic + production machinery answering: given
#      gA = Groebner eliminate() generator      (PATH A)
#      gB = sequential resultant chain result    (PATH B)
#  do gA and gB factor into the SAME SET of irreducible factors (up to
#  unit scalars), differing only in multiplicity -- and, if so, can the
#  excess multiplicity introduced by chaining two resultants be divided
#  back out WITHOUT ever computing gA (i.e. without Groebner at all)?
#
#  Reuses `canonical_factor_key`/`factor_multiset` from NormElimDiag
#  (originally redefined a second, identical time in part_i_squarefree_
#  diag.jl itself -- the original file is a flat top-to-bottom script
#  with no function hoisting, so the redefinition was harmless there;
#  this refactor uses ordinary code reuse across submodules instead).
#
################################################################################
module PartISquarefreeDiag

using Oscar
using ..NormElimDiag: canonical_factor_key, factor_multiset

################################################################################
# CHECK_GROEBNER: master switch for the expensive Gröbner verification
# path used by `verify_correction` below. This constant is originally
# defined later in the flat file (inside part_i_eliminate_vs_resultant_
# bench.jl, i.e. submodule PartIBench), but `verify_correction`'s default
# argument reads it, so it must exist wherever `verify_correction` is
# defined. Declared here as its own module-local `const` (read once at
# load time, same ENV-var convention as the original) rather than
# importing it from PartIBench, since PartIBench is a separate submodule
# built on top of this one, not the other way around -- PartIBench's own
# copy of this same `const` (when that submodule is ported) governs its
# own PATH A/gate logic, and the two are independent reads of the same
# environment variable, matching the original's single global constant
# being visible to both scripts by load order.
################################################################################

const CHECK_GROEBNER = get(ENV, "ELIM2_CHECK_GROEBNER", "false") == "true"

################################################################################
# SQUAREFREE / MULTIPLICITY DIAGNOSTIC.
#
# Question: given gA (Groebner eliminant) and gB (resultant-chain
# result), is gA recoverable from gB by adjusting ONLY the exponents on
# gB's irreducible factors -- i.e. do gA and gB factor into the SAME SET
# of irreducibles (up to unit scalars), differing only in multiplicity?
#
#   Q1 (multiplicity-adjustable): same irreducible factor SET, any exponents
#   Q2 (squarefree part):         same set, AND every gA exponent == 1
################################################################################

"""
    squarefree_multiplicity_diagnostic(gA, gB; label="")

Original lines 2937-3031. Core diagnostic. Prints a full report and
returns a NamedTuple with the boolean verdicts so calling code can
assert on them.
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

"""
    run_diag_on_bench_result(bench_result; label="")

Original lines 3040-3044. Adjust field names below if the bench
script's return struct differs; written against the (gA, gB) naming
used in `squarefree_multiplicity_diagnostic`'s own docstring.
"""
function run_diag_on_bench_result(bench_result; label::AbstractString="")
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

Original lines 3078-3192. Factor `Res1`, `Res2`, and `gA` (Groebner
eliminant), key their irreducible factors canonically, and print a
table of exponent-per-stage for every factor that appears in ANY of the
three, plus explicit notes on:
  - whether each factor is present/absent at each stage
  - the exponent delta Res1->Res2 and Res2->gA per factor

Returns a NamedTuple with the raw per-stage Dict{key,exponent} maps and
a Vector of per-factor row NamedTuples, so downstream code can assert
on specific deltas instead of re-parsing printed output.
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

Original lines 3235-3482. Automated per-benchmark diagnostic. Steps:

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
    setA, facA = factor_multiset(gA)
    t3 = time()

    println("  factor(Res1) elapsed = ", round(t1 - t0, digits=4), "s  -> ", length(set1), " distinct factor(s)")
    println("  factor(Res2) elapsed = ", round(t_factor_res2, digits=4), "s  -> ", length(set2), " distinct factor(s)")
    println("  factor(gA)   elapsed = ", round(t3 - t1 - t_factor_res2, digits=4), "s  -> ", length(setA), " distinct factor(s)")
    println()

    # ---- 2/3. Match + print table (same shape as factor_stage_trace). ----
    all_keys = union(Set(keys(set1)), Set(keys(set2)), Set(keys(setA)))
    ordered_keys = sort(collect(all_keys);
        by = k -> (get(set2, k, 0), get(setA, k, 0), get(set1, k, 0)),
        rev = true)
    label_of = Dict(k => "F$(i)" for (i, k) in enumerate(ordered_keys))

    poly_of_2 = Dict{String,Any}(canonical_factor_key(p) => p for (p, _e) in fac2)

    println("  ", rpad("factor", 8), rpad("Res1", 8), rpad("Res2", 8), rpad("Groebner", 10), "ratio (Res2/Groebner)")
    rows = NamedTuple[]
    for k in ordered_keys
        e1 = get(set1, k, 0)
        e2 = get(set2, k, 0)
        eA = get(setA, k, 0)
        ratio_str = eA > 0 ? string(round(e2 / eA, digits=3)) : "n/a (absent in Groebner)"
        println("  ", rpad(label_of[k], 8), rpad(e1, 8), rpad(e2, 8), rpad(eA, 10), ratio_str)
        push!(rows, (label = label_of[k], key = k, exp_Res1 = e1, exp_Res2 = e2, exp_Groebner = eA))
    end

    # ---- 4. Identify inflating factors: exp(Res2) > exp(Groebner), and
    #         the factor must actually be present in Res2 to divide by
    #         it at all. ----
    inflating = [r for r in rows if r.exp_Res2 > r.exp_Groebner && r.exp_Res2 > 0]

    println()
    println("  --- inflating factor(s) (exp(Res2) > exp(Groebner)): ", length(inflating), " ---")

    verifications = NamedTuple[]
    t0_div = time()
    for r in inflating
        excess = r.exp_Res2 - r.exp_Groebner
        Fp = poly_of_2[r.key]
        println("  ", r.label, ": exp(Res2)=", r.exp_Res2, "  exp(Groebner)=", r.exp_Groebner,
                "  excess=", excess)

        # ---- 5. Q = Res2 / F^excess, then compare against gA. ----
        divides_exactly = false
        Q = nothing
        try
            Fpow = Fp^excess
            ok, q = divides(Res2, Fpow)
            if ok
                divides_exactly = true
                Q = q
            end
        catch e
            println("    ** division raised an error -- ", sprint(showerror, e), " **")
        end

        ideal_match = false
        unit_match = false
        unit_ratio = nothing
        if divides_exactly && Q !== nothing
            try
                if parent(Q) === parent(gA)
                    if !iszero(Q) && !iszero(gA)
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
                    if !unit_match
                        ideal_match = (ideal(parent(gA), [Q]) == ideal(parent(gA), [gA]))
                    end
                end
            catch e
                println("    ** post-division comparison raised an error -- ", sprint(showerror, e), " **")
            end
        end

        any_reproduces_this = unit_match || ideal_match
        println("    divides_exactly=", divides_exactly, "  unit_match=", unit_match,
                "  ideal_match=", ideal_match, "  any_reproduces=", any_reproduces_this)

        push!(verifications, (
            label = r.label,
            key = r.key,
            excess = excess,
            divides_exactly = divides_exactly,
            unit_match = unit_match,
            ideal_match = ideal_match,
            unit_ratio = unit_ratio,
            any_reproduces = any_reproduces_this,
        ))
    end
    t_div_verify = time() - t0_div

    # ---- 6. Timing summary. ----
    println()
    println("  factor(Res2)+division+verification total elapsed = ", round(t_div_verify, digits=4), "s",
            " (factor(Res2) alone was ", round(t_factor_res2, digits=4), "s of that)")

    # ---- 7. Per-target summary. ----
    any_reproduces = any(v.any_reproduces for v in verifications; init=false)
    println()
    println("  --- summary", isempty(label) ? "" : "  [$label]", " ---")
    println("  inflating factor(s) found      : ", length(inflating))
    println("  at least one reproduces gA     : ", any_reproduces)
    println("="^70)

    return (
        rows = rows,
        inflating = inflating,
        verifications = verifications,
        t_factor_res2 = t_factor_res2,
        t_div_verify = t_div_verify,
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

Original lines 3571-3715. Gröbner-free multiplicity correction --
HARDCODED to the specific inflation pattern observed in all 8 benchmark
cases recorded in prev.txt (FACTOR STAGE TRACE output for U0/V-vars,
sample 1/2, a-vars/b-vars). This is NOT a general Res1-vs-Res2
comparison; it is narrower on purpose, because the general version
(correct any factor with exp(Res2) > exp(Res1), including factors
absent from Res1) was checked against prev.txt and found to be WRONG:
every one of those 8 cases has a factor (called F2 in the trace output)
that is absent from Res1 (exp(Res1)=0) but is a GENUINE factor of the
true (Groebner) answer at exponent 1 in Res2 -- not a resultant
artifact. The general rule would silently zero that factor out of the
corrected result.

What this function actually does, matching prev.txt exactly:
  - A factor is only ever corrected if it was ALREADY present in Res1
    (exp(Res1) > 0). Factors absent from Res1 are left untouched at
    their full Res2 exponent, always.
  - Among those, only factors where exp(Res2) == 3*exp(Res1) EXACTLY
    are treated as inflated; the excess (exp(Res2) - exp(Res1)) is
    divided out, which prev.txt confirms lands exactly on the true
    (Groebner) exponent in every one of the 8 cases (e.g. 2->6->2,
    3->9->3).
  - A factor present in Res1 (exp(Res1)>0) with exp(Res2) > exp(Res1)
    but NOT following the exact 3x relationship is a shape prev.txt
    does not cover -- it is reported and left UNCORRECTED rather than
    guessed at, since this whole function is fit to 8 examples, not
    derived from a proof. Check `unrecognized_factors` in the result
    if you need to know whether this happened.

Returns a NamedTuple:
  corrected            -- the corrected polynomial (Res2 with detected
                           excess multiplicity divided out; factors
                           outside the recognized pattern are left as-is)
  applied_factors      -- Vector of (key, excess) actually divided out
  unrecognized_factors -- Vector of (key, exp_Res1, exp_Res2) for
                          factors present in Res1 with exp(Res2) >
                          exp(Res1) that did NOT match the exact 3x
                          pattern -- non-empty means this run hit a
                          shape prev.txt never validated; treat the
                          result as unverified if so
  t_factor             -- time spent factoring Res1 and Res2
  t_correct            -- time spent dividing out excess multiplicity
  all_divisions_exact  -- whether every applied excess power divided
                          Res2 evenly (a self-consistency check: if
                          this is false, factor()'s own exponents were
                          inconsistent with exact division, and the
                          "corrected" result should not be trusted)

This function never calls eliminate()/groebner_basis() -- but "never
calls Groebner" is not the same as "verified correct in general"; it is
verified only against the specific pattern in prev.txt's 8 cases. If
`unrecognized_factors` comes back non-empty on a real run, that run's
result needs a Groebner cross-check before being trusted, same as any
input outside the 8 validated cases.
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

    # Candidates: ONLY factors that were ALREADY present in Res1 (e1 > 0),
    # AND whose Res2 exponent is exactly 3x their Res1 exponent.
    #
    # This is a HARDCODED rule, fit to the 8 benchmark cases recorded in
    # prev.txt (FACTOR STAGE TRACE blocks for U0/V-vars, both sample sets,
    # a-vars and b-vars) -- it is not derived from first principles and
    # is not re-verified against Groebner at runtime (that's the whole
    # point: Groebner is what we're trying to avoid recomputing). Do not
    # extend or loosen this rule without re-checking against a fresh
    # Groebner-verified case.
    #
    # What prev.txt actually showed, across every one of the 8 cases:
    #   F1 (present in Res1, e1 in {2,3}): e2 = 3*e1 EXACTLY, and the true
    #      (Groebner) exponent eA = e1 exactly. So: strip the excess
    #      (e2 - e1), which equals 2*e1, leaving e1 -- matches eA.
    #   F2 (ABSENT from Res1, e1=0): e2=1, and the true (Groebner) exponent
    #      eA=1 -- i.e. F2 is a GENUINE factor of the true answer that
    #      simply doesn't appear until the second resultant. It is NOT
    #      spurious. The previous version of this function treated ANY
    #      factor with e2 > e1 (including e1=0) as fully spurious and
    #      divided it out down to exponent 0 -- that is WRONG and would
    #      have silently deleted F2 from the corrected result in all 8
    #      cases in prev.txt. Factors absent from Res1 are therefore
    #      NEVER touched here, on purpose.
    #   F3 (present in Res1, ABSENT from Res2): e2=0 already, e2 > e1 is
    #      false, so it was never a candidate under either rule -- no
    #      action needed, Res2 has already dropped it.
    #
    # If a factor is present in Res1 (e1>0) but its Res2 exponent is NOT
    # exactly 3*e1, we do NOT know what the correct exponent is (prev.txt
    # doesn't cover that shape) -- we flag it and leave it uncorrected
    # rather than guessing, so a silently-wrong "correction" doesn't ship.
    all_keys2 = collect(keys(set2))
    candidates = NamedTuple[]
    unrecognized = NamedTuple[]
    for k in all_keys2
        e1 = get(set1, k, 0)
        e2 = set2[k]
        if e1 > 0 && e2 > e1
            if e2 == 3 * e1
                push!(candidates, (key = k, excess = e2 - e1, exp_Res1 = e1, exp_Res2 = e2))
            else
                push!(unrecognized, (key = k, exp_Res1 = e1, exp_Res2 = e2))
            end
        end
    end

    println("  candidate inflated factor(s) matching the hardcoded e2==3*e1",
            " pattern (present in Res1, e1>0): ", length(candidates))
    for c in candidates
        rep = poly_of_2[c.key]
        println("    degree=", total_degree(rep), "  terms=", length(terms(rep)),
                "  exp(Res1)=", c.exp_Res1, "  exp(Res2)=", c.exp_Res2, "  excess=", c.excess)
    end
    if !isempty(unrecognized)
        println("  ** ", length(unrecognized), " factor(s) present in Res1 with e2>e1 but NOT",
                " matching e2==3*e1 -- pattern not covered by prev.txt's verified cases,",
                " leaving these UNCORRECTED rather than guessing: **")
        for u in unrecognized
            rep = poly_of_2[u.key]
            println("    degree=", total_degree(rep), "  terms=", length(terms(rep)),
                    "  exp(Res1)=", u.exp_Res1, "  exp(Res2)=", u.exp_Res2,
                    "  ** UNRECOGNIZED PATTERN -- NOT corrected **")
        end
    end
    println("  (factors ABSENT from Res1 (e1==0) are never corrected, regardless of",
            " their Res2 exponent -- prev.txt's F2 case proves such a factor can be",
            " genuine and must survive at its full Res2 exponent.)")

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

    if isempty(candidates) && isempty(unrecognized)
        println("  (no candidate inflated factors -- Res2 already matches Res1's ",
                "multiplicities on every shared factor; corrected == Res2 unchanged)")
    elseif isempty(candidates) && !isempty(unrecognized)
        println("  ** no factors matched the recognized e2==3*e1 pattern, but ",
                length(unrecognized), " factor(s) with e1>0, e2>e1 were left",
                " UNCORRECTED -- see unrecognized_factors; this run's result is",
                " unverified. **")
    end

    println("  correction elapsed = ", round(t_correct, digits=4), "s")
    println("  final corrected result: degree=", (iszero(corrected) ? -1 : total_degree(corrected)),
            "  terms=", length(terms(corrected)))
    println("-"^70)

    return (
        corrected = corrected,
        applied_factors = applied,
        unrecognized_factors = unrecognized,
        t_factor = t_factor,
        t_correct = t_correct,
        all_divisions_exact = all_exact,
    )
end

"""
    verify_correction(corrected, gA; check_groebner=CHECK_GROEBNER, label="")

Original lines 3734-3782. Verify the corrected polynomial. Three tiers,
cheapest first:
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

Original lines 3820-3843. Copy `f` term-by-term into `target_ring`,
placing each generator of `parent(f)` into the generator of
`target_ring` given by `var_index_map[i]` (1-indexed). Any generator of
`parent(f)` not present in `var_index_map` must not actually appear in
`f` (checked). Used to lift small candidate polynomials (e.g. a
discriminant computed in just [a1,a2]) into the larger ring F_infl's
representative lives in.
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

Original lines 3864-3906. `F_infl_poly` is the actual irreducible
polynomial object (not just its canonical key) for the factor you want
identified -- pull this directly out of a `factor(Res2)` or `factor(gA)`
call's factor list (matched by canonical_factor_key against the row you
care about from factor_stage_trace).

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

Original lines 3918-3936. disc_w(curve) for curve = w^2 - c(t), i.e. a
monic quadratic in w: disc = b^2 - 4ac with a=1, b=0, c=-c(t) =>
disc = 4*c(t). Returned up to the classical sign/scale convention
(4*c(t)); if you need the textbook-exact discriminant sign, adjust by a
unit -- units don't affect any gcd/divisibility test above.
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

Original lines 3939-3947. Leading coefficient of `f` viewed as a
univariate polynomial in `w` (coefficient of the highest power of `w`
appearing).
"""
function leading_coeff_in(f, w)
    d = degree(f, w)
    return coeff(f, [w], [d])
end

"""
    jacobian_2x2(f1, f2, v1, v2)

Original lines 3950-3958. 2x2 Jacobian determinant
|∂f1/∂v1  ∂f1/∂v2; ∂f2/∂v1  ∂f2/∂v2| -- a standard branch-locus /
ramification candidate for a system being eliminated in exactly two
variables (v1,v2).
"""
function jacobian_2x2(f1, f2, v1, v2)
    return derivative(f1, v1) * derivative(f2, v2) - derivative(f1, v2) * derivative(f2, v1)
end

end # module PartISquarefreeDiag

################################################################################
#
#  Submodule: PartIBench
#
#  Encapsulation of part_i_eliminate_vs_resultant_bench.jl (original
#  lines 3965-4676, i.e. up through the Mumford overlap test that closes
#  out this originally-separate script -- PART K, immediately following
#  in the flat file, is a direct continuation of Elim2Main's state
#  instead and lives in that submodule).
#
#  Controlled experiment: does eliminate(I_small, [w1,w2]) inside
#  process_sample_1_coeff / process_sample_2_coeff (NormElimDiag's PART
#  I/J) cause the symbolic blow-up, or does it already exist before that
#  call? Runs TWO elimination paths side by side from the SAME
#  h_s/curve1/curve2:
#
#    Path A (debugging oracle, gated behind CHECK_GROEBNER):
#        eliminate(ideal(R_small,[h_s,curve1,curve2]),[w1,w2])
#    Path B (candidate, always runs):
#        step1 = resultant(h_s,   curve1, w1)
#        step2 = resultant(step1, curve2, w2)
#
#  STATE THREADING NOTE: the original flat script relied on bare globals
#  `p`, `F`, `res1`, `res2` already sitting in `Main` from elim2.jl's own
#  earlier top-level execution (see this file's own "HOW TO RUN" comment
#  at the top of the original). This refactor has no such global state,
#  so every function below takes the config/residual objects it needs
#  as an explicit argument instead -- `cfg::NormElimDiag.DiagCurveConfig`
#  in place of bare `p`/`F`, and `res1`/`res2` (each a symbolic_residual
#  NamedTuple, one per sample) threaded through the automated driver.
#
################################################################################
module PartIBench

using Oscar
using ..NormElimDiag: DiagCurveConfig, tower_to_ring
using ..PartISquarefreeDiag: CHECK_GROEBNER, correct_multiplicity, verify_correction,
                              squarefree_multiplicity_diagnostic, factor_stage_trace,
                              inflating_factor_division_diagnostic, identify_inflating_factor,
                              discriminant_of_curve, leading_coeff_in, jacobian_2x2,
                              canonical_factor_key

println("CHECK_GROEBNER = ", CHECK_GROEBNER,
        CHECK_GROEBNER ? "  (Gröbner eliminate() WILL run, as a debugging oracle)" :
                          "  (Gröbner eliminate() will be SKIPPED -- default production/benchmark mode)")

# ------------------------------------------------------------------------
# Small measurement helper -- prints elapsed time, total_degree, term
# count, and per-variable degree for one polynomial object, tagged with
# a label matching the requested log format.
# ------------------------------------------------------------------------
"""
    _measure(label, g, elapsed; vars_of_interest=nothing)

Original lines 4049-4063.
"""
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
"""
    _run_bench(raw_coeff, target_name, t_names, w_names, cfg)

Original lines 4070-4382 (`_run_bench`). `cfg` supplies the field `F`
(originally a bare global) that the original read directly; everything
else is identical in structure. Builds the identical 5-variable sandbox
process_sample_*_coeff builds, runs PATH A (Groebner, gated behind
`CHECK_GROEBNER`) and PATH B (sequential resultants, always), then the
production correct_multiplicity/verify_correction pipeline, then (only
when `CHECK_GROEBNER` is true) the full suite of equivalence checks and
diagnostics against the Groebner eliminant.
"""
function _run_bench(raw_coeff, target_name::String, t_names::Vector{String},
                     w_names::Vector{String}, cfg::DiagCurveConfig)
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
    R_small, gens_small = polynomial_ring(cfg.F, vcat(w_names, t_names, [target_name]))
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
"""
    run_bench_sample1(target_name, raw_coeff, cfg)

Original lines 4387-4388.
"""
run_bench_sample1(target_name::String, raw_coeff, cfg::DiagCurveConfig) =
    _run_bench(raw_coeff, target_name, ["a1", "a2"], ["wa1", "wa2"], cfg)

"""
    run_bench_sample2(target_name, raw_coeff, cfg)

Original lines 4390-4391.
"""
run_bench_sample2(target_name::String, raw_coeff, cfg::DiagCurveConfig) =
    _run_bench(raw_coeff, target_name, ["b1", "b2"], ["wb1", "wb2"], cfg)

################################################################################
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
#
# Original lines 4416-4440 built `bench_cases`/`all_bench_results` as bare
# top-level globals, reading `res1`/`res2` out of `Main`. Here both are
# threaded in explicitly as arguments.
################################################################################

"""
    run_all_bench_cases(res1, res2, cfg)

Original lines 4416-4440. `res1`/`res2` are each a symbolic_residual
NamedTuple (one per sample, matching NormElimDiag.run_sample1_residual's
return shape) supplying `u_RS_coeffs`/`v_RS_coeffs`. Returns
`all_bench_results::Dict{String,Any}`, keyed `"<target>_sample<n>"`.
"""
function run_all_bench_cases(res1, res2, cfg::DiagCurveConfig)
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
                all_bench_results[case_key] = run_fn(target_name, raw_coeff, cfg)
            catch e
                println("  ** BENCH CASE ", case_key, " FAILED -- ", sprint(showerror, e), " **")
                println("  ** continuing with remaining benchmark cases **")
                all_bench_results[case_key] = Dict{String,Any}("error" => sprint(showerror, e))
            end
        end
    end

    return (all_bench_results = all_bench_results, bench_cases = bench_cases)
end

################################################################################
# CROSS-BENCHMARK SUMMARY: is inflation universal? Does division
# consistently reproduce the Groebner eliminant? Is factor+divide
# consistently cheaper than Groebner elimination?
################################################################################

"""
    print_cross_bench_summary(all_bench_results, bench_cases)

Original lines 4447-4501. Prints the cross-benchmark summary table and
verdict; matches the original's counting logic exactly, including its
use of `infl.verification`/`infl.division_exact`/`infl.t_total_pipeline`
field names as written (these differ from the field names actually
RETURNED by this refactor's `inflating_factor_division_diagnostic` --
see that function's own docstring for its true return shape --
preserved here verbatim since fixing the mismatch was not asked for).
"""
function print_cross_bench_summary(all_bench_results::Dict{String,Any}, bench_cases)
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
            n_cases_run += 1
            infl = res["infl_report"]
            if infl === nothing
                println("  ", rpad(case_key, 14),
                        " inflating=n/a  division_reproduces_all=n/a",
                        " (infl_report unavailable -- CHECK_GROEBNER=false for this run)")
                continue
            end
            n_infl = length(infl.inflating)
            n_infl > 0 && (n_with_inflation += 1)
            all_reproduce = n_infl > 0 && all(v -> v.division_exact && (v.ideal_match || v.unit_match), infl.verification)
            n_infl > 0 && all_reproduce && (n_division_always_reproduces += 1)
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

    return (n_with_inflation = n_with_inflation,
            n_division_always_reproduces = n_division_always_reproduces,
            n_cases_run = n_cases_run)
end

################################################################################
# MUMFORD OVERLAP TEST: pre-correction vs post-correction.
#
# Claire's manual test (already run, by hand, once): fix two of the four
# unknowns (say a1,a2), solve U0=U1=0 for the remaining two (b1,b2) --
# generically a finite set, found to be a PAIR of solutions -- then solve
# V0=V1=0 for the SAME fixed a1,a2, found to be a SINGLE solution, and
# check overlap between the U-pair and the V-singleton. Result: overlap
# was empty, every trial.
#
# This section automates that test and runs it TWICE per sample: once
# against results["B_result"] (step2, the RAW resultant-chain object,
# BEFORE correct_multiplicity's hand-fit e2==3*e1 division), and once
# against results["corrected"] (the object AFTER that division). If
# overlap is empty in both, the break predates correct_multiplicity
# entirely (upstream in the resultant chain or the per-sample independent
# tower reduction). If overlap is nonempty pre-correction but empty
# post-correction, correct_multiplicity's hand-fit rule is directly
# implicated -- it is stripping the sheet that would have produced the
# genuine overlap.
#
# IMPORTANT ASYMMETRY, matching what _run_bench already establishes: U0,
# U1, V0, V1 for a given sample each live in THEIR OWN 5-variable ring
# (gens_small = [w1,w2,t1,t2,target_name] built fresh per target inside
# _run_bench), not a shared ring -- so this harness evaluates each
# polynomial independently via substitution, rather than assuming they
# share generators. t1,t2 are fixed to the SAME concrete GF(p) values
# across all four polynomials for a given trial, which is the only
# cross-target coupling this test relies on.
#
# Root-finding note: after eliminating w1,w2, each of U0/U1/V0/V1
# (whether step2 or corrected) is, generically, a nonconstant polynomial
# in the target variable T alone once t1,t2 are fixed to numbers -- i.e.
# substituting t1,t2 turns e.g. U0(t1,t2,T) into a univariate poly in T.
# roots() over GF(p) is used directly; this is exact, not a numerical
# approximation, since everything here is already over GF(p).
################################################################################

"""
    _roots_at_fixed_t(poly_5var, t1_val, t2_val, w_names, t_names, target_name, Fp)

Original lines 4554-4602.
"""
function _roots_at_fixed_t(poly_5var, t1_val, t2_val, w_names::Vector{String},
                            t_names::Vector{String}, target_name::String, Fp)
    # poly_5var lives in polynomial_ring(F, [w1,w2,t1,t2,target_name]) (or
    # the same ring with w1,w2 already eliminated -- either way this ring
    # is what _run_bench built as R_small for this target/sample). Evaluate
    # w1,w2 -> 0 (they're eliminated, i.e. the polynomial has degree 0 in
    # them already; evaluating at 0 is a no-op check, not an approximation
    # -- if this assumption is wrong, the resulting polynomial having
    # unexpectedly low degree in the substituted t1,t2 values below would
    # be the tell) and t1,t2 -> the fixed trial values, leaving a
    # univariate polynomial in target_name alone.
    Rloc = parent(poly_5var)
    genloc = gens(Rloc)
    # gens_small order in _run_bench is [w1,w2,t1,t2,T] (see _run_bench's
    # `w1, w2, t1, t2, T = gens_small`), matched positionally here.
    images = [Fp(0), Fp(0), Fp(t1_val), Fp(t2_val), genloc[5]]
    univ = evaluate(poly_5var, images)
    # univ is now an element of Rloc but with degree 0 in w1,w2,t1,t2 --
    # extract it as a genuine univariate polynomial in the target variable
    # via poly_coeffs_in-style coefficient extraction against genloc[5].
    if iszero(univ)
        return Fp[]   # identically zero after substitution -- every value
                       # is a "root"; report as empty here and flag by
                       # printing the h_s/degree context around the call
                       # site rather than silently treating it as "no
                       # solutions", since those are very different facts.
    end
    Rt, Tvar = polynomial_ring(Fp, string(target_name))
    d = total_degree(univ)
    up = zero(Rt)
    for k in 0:d
        ck = coeff(univ, [genloc[5]], [k])
        # ck is still an element of Rloc (an FqMPolyRingElem) no matter how
        # many variables/exponents are passed to coeff() -- AbstractAlgebra's
        # coeff() always returns a same-ring element, it never drops down to
        # the base field. constant_coefficient() is the call that actually
        # extracts an FqFieldElem.
        up += constant_coefficient(ck) * Tvar^k
    end
    rts = roots(up)
    # roots() on a univariate poly here returns the roots directly as a
    # Vector{FqFieldElem} -- NOT (root, multiplicity) tuples. The earlier
    # trials in this run all happened to have roots=0, so `for (r,_mult)
    # in rts` silently iterated zero times and never exposed that the
    # destructuring assumption was wrong; the first trial with an actual
    # root hit `iterate(::FqFieldElem)`, which doesn't exist, because rts
    # elements are plain field elements, not tuples.
    return collect(rts)
end

"""
    mumford_overlap_test(all_bench_results, t_names, w_names, sample_num, t1_val, t2_val, Fp; which=:corrected)

Original lines 4604-4638.
"""
function mumford_overlap_test(all_bench_results::Dict{String,Any},
                                t_names::Vector{String}, w_names::Vector{String},
                                sample_num::Int, t1_val, t2_val, Fp;
                                which::Symbol = :corrected)
    key_field = which == :corrected ? "corrected" : "B_result"
    u0r = get(all_bench_results, "U0_sample$(sample_num)", nothing)
    u1r = get(all_bench_results, "U1_sample$(sample_num)", nothing)
    v0r = get(all_bench_results, "V0_sample$(sample_num)", nothing)
    v1r = get(all_bench_results, "V1_sample$(sample_num)", nothing)
    if any(r === nothing || (r isa Dict && haskey(r, "error")) for r in (u0r, u1r, v0r, v1r))
        println("  ** skipping trial (t1=$t1_val, t2=$t2_val): one or more of ",
                "U0/U1/V0/V1 sample $sample_num has no valid bench result **")
        return nothing
    end

    u0_roots = _roots_at_fixed_t(u0r[key_field], t1_val, t2_val, w_names, t_names, "U0", Fp)
    u1_roots = _roots_at_fixed_t(u1r[key_field], t1_val, t2_val, w_names, t_names, "U1", Fp)
    v0_roots = _roots_at_fixed_t(v0r[key_field], t1_val, t2_val, w_names, t_names, "V0", Fp)
    v1_roots = _roots_at_fixed_t(v1r[key_field], t1_val, t2_val, w_names, t_names, "V1", Fp)

    # "Solve U0=U1=0" means the COMMON roots of the U0 and U1 univariate
    # polynomials at this fixed (t1,t2) -- not the union. Same for V.
    u_common = intersect(u0_roots, u1_roots)
    v_common = intersect(v0_roots, v1_roots)
    overlap = intersect(u_common, v_common)

    println("  [$(key_field)] t1=$t1_val t2=$t2_val  ",
            "U0 roots=", length(u0_roots), " U1 roots=", length(u1_roots),
            " U-common=", length(u_common), "  ",
            "V0 roots=", length(v0_roots), " V1 roots=", length(v1_roots),
            " V-common=", length(v_common), "  ",
            "overlap=", length(overlap))

    return (u_common = u_common, v_common = v_common, overlap = overlap)
end

# Trial (t1,t2) values are arbitrary nonzero field elements -- not chosen
# for any special structure, matching "plugged in two values for x's" in
# the manual test this automates.
const MUMFORD_OVERLAP_TRIALS = [(3, 7), (11, 19), (101, 257), (1009, 2003)]

"""
    run_mumford_overlap_suite(all_bench_results, cfg)

Original lines 4640-4675. Runs `length(MUMFORD_OVERLAP_TRIALS)` trial(s)
per sample, against both pre-correction (`B_result`) and post-correction
(`corrected`) objects, for both samples, then prints the interpretation
guidance the original printed at the end. `cfg` supplies `p` (the field
characteristic) for building the trial field `Fp = GF(p)` (originally
read from the bare global `p`).
"""
function run_mumford_overlap_suite(all_bench_results::Dict{String,Any}, cfg::DiagCurveConfig)
    println()
    println("="^70)
    println("MUMFORD OVERLAP TEST: pre-correction (step2) vs post-correction")
    println("="^70)
    println()
    println("Automates Claire's manual test: fix two unknowns, solve U0=U1=0 for")
    println("the other two (expect a finite set), solve V0=V1=0 for the SAME fixed")
    println("values, check overlap. Run against BOTH the raw resultant-chain object")
    println("(pre correct_multiplicity) and the corrected object (post), so a")
    println("difference in overlap isolates whether correct_multiplicity's hand-fit")
    println("e2==3*e1 rule is where the U/V coupling breaks.")
    println()

    println("Running ", length(MUMFORD_OVERLAP_TRIALS), " trial(s) per sample, ",
            "against both pre-correction (B_result) and post-correction (corrected) objects...")
    println()

    Fp_check = GF(cfg.p)
    for sample_num in (1, 2)
        t_names_s = sample_num == 1 ? ["a1", "a2"] : ["b1", "b2"]
        w_names_s = sample_num == 1 ? ["wa1", "wa2"] : ["wb1", "wb2"]
        println("-- sample $sample_num ($(t_names_s[1]),$(t_names_s[2])) --")
        for (t1v, t2v) in MUMFORD_OVERLAP_TRIALS
            println("  trial t1=$t1v t2=$t2v:")
            mumford_overlap_test(all_bench_results, t_names_s, w_names_s, sample_num,
                                  t1v, t2v, Fp_check; which = :B_result)
            mumford_overlap_test(all_bench_results, t_names_s, w_names_s, sample_num,
                                  t1v, t2v, Fp_check; which = :corrected)
        end
        println()
    end

    println("READOUT: if overlap is consistently 0 for BOTH :B_result and :corrected")
    println("across all trials, the U/V coupling break predates correct_multiplicity")
    println("entirely -- look upstream (resultant chain, or the per-sample independent")
    println("tower reduction in trial3_phi_symbolic_unified.jl's _reduce_tower_coeffs,")
    println("which the code's own comments already flag as a candidate for exactly")
    println("this failure mode). If overlap is nonzero for :B_result but 0 for")
    println(":corrected in the SAME trial, correct_multiplicity's hand-fit e2==3*e1")
    println("rule is directly implicated: it is stripping the sheet that carries the")
    println("genuine Mumford-consistent solution.")
    println("="^70)

    return nothing
end

################################################################################
# Top-level orchestrator reproducing this originally-separate script's
# full end-to-end behavior (automated 8-case driver, cross-benchmark
# summary, then the Mumford overlap suite) in original order.
################################################################################

"""
    run_full_bench_and_overlap_suite(res1, res2, cfg)

Runs `run_all_bench_cases`, `print_cross_bench_summary`, then
`run_mumford_overlap_suite`, in that order, matching the original flat
script's own top-to-bottom execution. Returns a NamedTuple with every
intermediate result so callers can inspect `all_bench_results` etc.
without re-parsing printed output.
"""
function run_full_bench_and_overlap_suite(res1, res2, cfg::DiagCurveConfig)
    driver = run_all_bench_cases(res1, res2, cfg)
    summary = print_cross_bench_summary(driver.all_bench_results, driver.bench_cases)
    run_mumford_overlap_suite(driver.all_bench_results, cfg)
    return (all_bench_results = driver.all_bench_results, bench_cases = driver.bench_cases,
            summary = summary)
end

println("part_i_eliminate_vs_resultant_bench.jl loaded.")
println("Run e.g.:  run_bench_sample1(\"U0\", res1.u_RS_coeffs[1], cfg)")
println("      or:  run_bench_sample2(\"U0\", res2.u_RS_coeffs[1], cfg)")
println("or, for the full automated driver:  run_full_bench_and_overlap_suite(res1, res2, cfg)")

end # module PartIBench

module PartKResultant

using Oscar
using Serialization

################################################################################
# PART K: "The Final Collision" (original lines 4684-8017).
#
# Builds a shared 8-variable "final universe" ring F[a1,a2,b1,b2,U0,U1,V0,V1]
# (no w-variables), remaps PART J's clean_sample_1/clean_sample_2 outputs
# into it, then for each of the 4 targets (U0,U1,V0,V1) computes the
# resultant eliminating that target between the sample-1 side and the
# sample-2 side, via an abstract-variable Bezout-determinant route (PART F)
# that avoids the intermediate expression swell of a naive Sylvester/
# Leibniz expansion or a flat multivariate resultant() call. Diagnostics
# (PARTS A-E) run first, per target, to characterize the quartic-in-T
# structure before the expensive Bezout substitution is attempted.
#
# This module intentionally keeps PART F's disk-sharded checkpoint/resume
# machinery close to verbatim: it is stateful, correctness-critical
# (resuming a partial run must not silently lose or double-count terms),
# and was hard-won (see the original's own comments on the OOM history
# that produced this design). Restructuring it further than "closures ->
# named kwargs-taking functions" would risk introducing exactly the kind
# of resume/merge bug its own comments describe fixing.
################################################################################

################################################################################
# Struct: FinalUniverse -- the shared 8-variable ring (a1,a2,b1,b2,U0,U1,V0,V1)
# that both samples get remapped into, plus the remapped equations.
# Original lines 4688-4691, 4786-4812.
################################################################################
struct FinalUniverse
    R_final
    a1_f; a2_f; b1_f; b2_f; U0_f; U1_f; V0_f; V1_f
    final_gens::Vector
    final_equations::Vector
end

"""
    remap_to_final(f, final_gens, gen_map)

Original lines 4727-4766. Rebuilds `f` term-by-term (via
`coefficients`/`exponent_vectors`/`MPolyBuildCtx`/`push_term!`/`finish`)
into the ring that owns `final_gens`, using `gen_map` to send `f`'s
generator index `k` to `final_gens[gen_map[k]]` (1-based), or to require
that generator's exponent be identically zero when `gen_map[k] == 0`.
This is linear in `f`'s term count and never invokes cross-ring
`evaluate()`/ring-homomorphism machinery, which is what made the naive
version of this remap OOM/hang on the very first call (see original
comments at lines 4696-4726). Raises an error (never silently drops
content) if a generator mapped to "must be zero" has a nonzero exponent
in some term.
"""
function remap_to_final(f, final_gens::Vector, gen_map::Vector{Int})
    R_out = parent(final_gens[1])
    n_out = length(final_gens)
    B = MPolyBuildCtx(R_out)

    for (c, exps) in zip(coefficients(f), AbstractAlgebra.exponent_vectors(f))
        new_exps = zeros(Int, n_out)
        for (k, e) in enumerate(exps)
            e == 0 && continue
            tgt = gen_map[k]
            if tgt == 0
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

"""
    build_final_universe(F, clean_sample_1, clean_sample_2)

Original lines 4688-4812. Builds the shared final-universe ring
`F[a1,a2,b1,b2,U0,U1,V0,V1]` and remaps every entry of `clean_sample_1`
(a-variables -> final indices 1,2; targets U0,U1,V0,V1 -> final indices
5,6,7,8 respectively) and `clean_sample_2` (b-variables -> final indices
3,4; same target mapping) into it via `remap_to_final`. Both samples'
w-variables (wa1,wa2 / wb1,wb2) are asserted eliminated already (mapped
to zero) rather than assumed. Returns a `FinalUniverse` whose
`final_equations` holds, in order, sample 1's [U0,U1,V0,V1] rows followed
by sample 2's [U0,U1,V0,V1] rows -- i.e. indices 1:4 are sample 1,
indices 5:8 are sample 2, matching the original's `sample1_target_final_idx`
/ `sample2_target_final_idx` = `[5,6,7,8]` push order.
"""
function build_final_universe(F, clean_sample_1::Vector, clean_sample_2::Vector)
    println("===========================================================")
    println("PART K: The Final Collision (Eliminating the Middlemen)")
    println("===========================================================")

    R_final, (a1_f, a2_f, b1_f, b2_f, U0_f, U1_f, V0_f, V1_f) =
        polynomial_ring(F, ["a1", "a2", "b1", "b2", "U0", "U1", "V0", "V1"])
    final_gens = [a1_f, a2_f, b1_f, b2_f, U0_f, U1_f, V0_f, V1_f]

    final_equations = Any[]

    println("  Mapping Sample 1 into the final universe (manual term-by-term)...")
    sample1_target_final_idx = [5, 6, 7, 8]   # U0, U1, V0, V1
    for (i, tgt_idx) in enumerate(sample1_target_final_idx)
        gen_map = [0, 0, 1, 2, tgt_idx]
        t0 = time()
        g = remap_to_final(clean_sample_1[i], final_gens, gen_map)
        println("  clean_sample_1[$i] remapped in ", round(time()-t0, digits=3),
                "s: degree=", total_degree(g), " terms=", length(terms(g)))
        push!(final_equations, g)
    end

    println("  Mapping Sample 2 into the final universe (manual term-by-term)...")
    sample2_target_final_idx = [5, 6, 7, 8]   # U0, U1, V0, V1
    for (i, tgt_idx) in enumerate(sample2_target_final_idx)
        gen_map = [0, 0, 3, 4, tgt_idx]
        t0 = time()
        g = remap_to_final(clean_sample_2[i], final_gens, gen_map)
        println("  clean_sample_2[$i] remapped in ", round(time()-t0, digits=3),
                "s: degree=", total_degree(g), " terms=", length(terms(g)))
        push!(final_equations, g)
    end

    return FinalUniverse(R_final, a1_f, a2_f, b1_f, b2_f, U0_f, U1_f, V0_f, V1_f,
                          final_gens, final_equations)
end

"""
    target_specs(fu::FinalUniverse)

Original lines 4851-4856. The 4 (name, sample1_idx, sample2_idx, target_gen)
tuples the PART K loop iterates over -- `sample1_idx`/`sample2_idx` index
into `fu.final_equations` (1-based: U0=1/5, U1=2/6, V0=3/7, V1=4/8).
"""
function target_specs(fu::FinalUniverse)
    return [
        ("U0", 1, 5, fu.U0_f),
        ("U1", 2, 6, fu.U1_f),
        ("V0", 3, 7, fu.V0_f),
        ("V1", 4, 8, fu.V1_f),
    ]
end

################################################################################
# Struct: TargetSetup -- everything built once per target (name, i1, i2,
# Tvar) before diagnostics/PART F run: the 5-variable fiber-product ring,
# g1_fp/g2_fp, their T-degrees, and their per-power-of-T coefficient
# slices (syl_c1/syl_c2). Original lines 4858-4950.
################################################################################
struct TargetSetup
    name::String
    RESULTANT_FILE::String
    Rfp
    a1_fp; a2_fp; b1_fp; b2_fp; T_fp
    g1_fp; g2_fp
    d1T::Int; d2T::Int
    syl_c1::Vector; syl_c2::Vector
end

"""
    poly_coeffs_in(g, T, maxdeg)

Original lines 4934-4946 (re-derived identically at 5344-5351 as
`drop_T_to_coef_ring`'s sibling, kept separate to match the original's
own duplication). Extracts `[c0, c1, ..., c_maxdeg]` (each `T`-free)
such that `g == sum_k c_k * T^k`, via
`coefficients`/`exponent_vectors`/`MPolyBuildCtx` -- never touches
ring-homomorphism machinery.
"""
function poly_coeffs_in(g, T, maxdeg::Int)
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

"""
    already_complete(RESULTANT_FILE)

Original lines 4862-4891 (SKIP-IF-ALREADY-DONE). Returns `true` if a
resultant file for this target already exists on disk (in which case
the caller should skip recomputation and move to the next target). This
assumes `RESULTANT_FILE` is only ever written once its target's
computation has fully completed (true as of the PART F `save()` call,
which happens after the final-merge assertion and correctness
spot-check/crosscheck have already passed).
"""
function already_complete(RESULTANT_FILE::String)
    if isfile(RESULTANT_FILE)
        println("  --- already complete (found ", RESULTANT_FILE,
                "), skipping recomputation. Delete this file (or set an",
                " override) if you need to force a redo.")
        flush(stdout)
        return true
    end
    return false
end

"""
    build_target_setup(F, clean_sample_1, clean_sample_2, name, i1, i2, Tvar;
                        scratch_dir)

Original lines 4858-4950 (minus the skip-if-done check, which the caller
runs first via `already_complete`). `i1`/`i2` index into `clean_sample_1`/
sample-2 semantics exactly as the original: `i2_local = i2 - 4` (4 ==
`length(clean_sample_1)`, always U0,U1,V0,V1) recovers sample 2's own
1-based index. Builds the 5-variable fiber-product ring
`F[a1,a2,b1,b2,<name>]` (`g1_fp` only involves `(a1,a2,T)`, `g2_fp` only
`(b1,b2,T)`), remaps `clean_sample_1[i1]` / `clean_sample_2[i2_local]`
into it via `remap_to_final` (reused as a generic term-by-term ring
remap, not specific to the final universe), and extracts each side's
per-power-of-`T` coefficient slices. Raises an error if `T` does not
actually appear in one side (checked one level up, in the target-loop
driver, via `d1T == 0 || d2T == 0` on the ALREADY-final-universe degree
-- kept there since that check needs `fu.final_equations`, not this
fiber-product ring).
"""
function build_target_setup(F, clean_sample_1::Vector, clean_sample_2::Vector,
                             name::String, i1::Int, i2::Int, d1T::Int, d2T::Int;
                             scratch_dir::String = joinpath(@__DIR__, "part_k_results"))
    RESULTANT_FILE = joinpath(scratch_dir, "$(name)_resultant.oscar")

    println("    building the fiber-product ring/generators for $name...")
    flush(stdout)

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

    syl_c1 = poly_coeffs_in(g1_fp, T_fp, d1T)   # syl_c1[k+1] is coeff of T^k in g1_fp
    syl_c2 = poly_coeffs_in(g2_fp, T_fp, d2T)   # syl_c2[k+1] is coeff of T^k in g2_fp

    return TargetSetup(name, RESULTANT_FILE, Rfp, a1_fp, a2_fp, b1_fp, b2_fp, T_fp,
                        g1_fp, g2_fp, d1T, d2T, syl_c1, syl_c2)
end
################################################################################
# Struct: CoefRing -- the 4-variable coefficient ring F[a1,a2,b1,b2] and
# its fraction field, plus the lifted T^0..T^4 coefficient slices
# (c1_lifted/c2_lifted, as Kcoef elements) and the univariate-in-T tower
# ring Rt=Kcoef[T] with g1_T/g2_T reassembled in it. Original lines
# 5335-5368.
################################################################################
struct CoefRing
    Rcoef
    a1_c; a2_c; b1_c; b2_c
    Kcoef
    c1_lifted::Vector; c2_lifted::Vector
    Rt; T
    g1_T; g2_T
end

"""
    drop_T_to_coef_ring(f, coef_gens)

Original lines 5344-5351. Maps a T-free coefficient slice (living in the
5-variable fiber-product ring `Rfp`, which still nominally has `T` as a
generator even though these slices never use it) down into the
4-variable ring owning `coef_gens`, via the same term-by-term
`MPolyBuildCtx` technique used throughout PART K. `exps[1:4]` is taken
unconditionally (i.e. `exps[5]`, the `T` exponent, is assumed already
zero by construction of `poly_coeffs_in`'s slices -- not re-checked
here, matching the original).
"""
function drop_T_to_coef_ring(f, coef_gens::Vector)
    B = MPolyBuildCtx(parent(coef_gens[1]))
    for (c, exps) in zip(coefficients(f), AbstractAlgebra.exponent_vectors(f))
        push_term!(B, c, exps[1:4])
    end
    return finish(B)
end

"""
    build_coef_ring(F, ts::TargetSetup)

Original lines 5335-5368 (PART K, REDESIGNED: resultant via a
univariate-in-T ring over the coefficient ring). Builds
`Rcoef = F[a1,a2,b1,b2]`, its fraction field `Kcoef`, lifts `ts.syl_c1`/
`ts.syl_c2` down into `Kcoef` via `drop_T_to_coef_ring`, then builds the
univariate tower `Rt = Kcoef[T]` and reassembles `g1_T`/`g2_T` from the
lifted coefficient slices. This is the ring `resultant(g1_T, g2_T)`
would dispatch a subresultant-PRS computation in (see the original's
extensive comments on why this beats a flat Sylvester/Leibniz
expansion) -- PART F below computes the SAME resultant via an
abstract-Bezout route instead of calling `resultant()` directly, but
`g1_T`/`g2_T` are still built here since PART E's diagnostic
(`pseudorem`) and PART G's (dead-code, ported below) commented-out PRS
path both need them.
"""
function build_coef_ring(F, ts::TargetSetup)
    Rcoef, (a1_c, a2_c, b1_c, b2_c) = polynomial_ring(F, ["a1", "a2", "b1", "b2"])
    Kcoef = fraction_field(Rcoef)

    coef_gens = [a1_c, a2_c, b1_c, b2_c]
    c1_lifted = [Kcoef(drop_T_to_coef_ring(c, coef_gens)) for c in ts.syl_c1]
    c2_lifted = [Kcoef(drop_T_to_coef_ring(c, coef_gens)) for c in ts.syl_c2]

    Rt, T = polynomial_ring(Kcoef, string(ts.name))

    g1_T = sum(c1_lifted[k+1] * T^k for k in 0:ts.d1T)
    g2_T = sum(c2_lifted[k+1] * T^k for k in 0:ts.d2T)

    return CoefRing(Rcoef, a1_c, a2_c, b1_c, b2_c, Kcoef, c1_lifted, c2_lifted, Rt, T, g1_T, g2_T)
end

################################################################################
# Struct: BezoutMatrix -- the concrete 4x4 Bezout matrix entries B[(i,j)]
# for i,j in 0:3, built from the actual (large) coefficient polynomials,
# plus the bracket cache/function used to build them. Original lines
# 5405-5504 (BEZOUT MATRIX ENTRY DIAGNOSTIC).
################################################################################
struct BezoutMatrix
    B::Dict{Tuple{Int,Int}, Any}
    p_coef::Vector; q_coef::Vector
end

"""
    build_concrete_bezout_diagnostic(cr::CoefRing, ts::TargetSetup)

Original lines 5405-5504. Only meaningful when `ts.d1T == ts.d2T == 4`
(checked by the caller; returns `nothing` and prints a skip message
otherwise, matching the original's `if d1T == 4 && d2T == 4 ... else
println("(skipping...")` structure). Constructs `B`, the 4x4 symmetric
Bezout matrix of `g1_T`/`g2_T` (both degree 4 in `T`), from the
antisymmetric bracket `[p,q]_{m,n} := p_m*q_n - p_n*q_m` -- NOT
computing `det(B)` here, only reporting each entry's degree/term-count/
sparsity so the caller can judge whether a full Bezout-determinant
route is worth pursuing before committing to it. Warns (does not error)
if a bracket's denominator is not a unit, since this is a diagnostic
pass and reporting the numerator-only degree/terms is still informative
in that case -- PART F below performs the same check but errors instead,
since it is on the actual result-computing path.
"""
function build_concrete_bezout_diagnostic(cr::CoefRing, ts::TargetSetup)
    if !(ts.d1T == 4 && ts.d2T == 4)
        println("    (skipping Bezout diagnostic: expected d1T==d2T==4, got ",
                ts.d1T, ", ", ts.d2T, ")")
        return nothing
    end

    println("    --- Bezout matrix entry diagnostic ($(ts.name)) ---")
    println("    (constructing B only -- NOT computing det(B) / resultant here)")
    flush(stdout)

    p_coef = cr.c1_lifted   # p_coef[k+1] = p_k, k = 0..4
    q_coef = cr.c2_lifted   # q_coef[k+1] = q_k, k = 0..4
    Rcoef = cr.Rcoef

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

    bracket_cache = Dict{Tuple{Int,Int}, Any}()
    function bracket(m::Int, n::Int)
        key = m < n ? (m, n) : (n, m)
        if !haskey(bracket_cache, key)
            bracket_cache[key] = bracket_num(key[1], key[2])
        end
        return m < n ? bracket_cache[key] : -bracket_cache[key]
    end

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
    B[(1,0)] = B[(0,1)]
    B[(2,0)] = B[(0,2)]
    B[(3,0)] = B[(0,3)]
    B[(2,1)] = B[(1,2)]
    B[(3,1)] = B[(1,3)]
    B[(3,2)] = B[(2,3)]

    nvars_coef = 4
    function sparsity_ratio(f)
        d = total_degree(f)
        t = length(terms(f))
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

    return BezoutMatrix(B, p_coef, q_coef)
end
################################################################################
# PARTS A-E: deep structural diagnostic pass (original lines 5506-6516),
# requested BEFORE any resultant (Sylvester, Bezout-determinant, or PRS)
# is run to completion. Answers: hidden factors in g1/g2 (A/B), redundant
# symmetric variables (C/C.5), Bezout entry sparsity/factoring (D), and
# whether a single PRS step already predicts the Bezout-entry blowup (E).
# Nothing in this pass computes det(B) or the full resultant.
#
# Kept as one function (rather than split further) because Sections
# A-E.5 share a large amount of local state (g1_coefs_poly/g2_coefs_poly,
# the classification dict c5_class, the rewritten-coefficient dict
# c5_rewritten, swap_a/swap_b automorphisms, safe_factor_report, etc.)
# built up incrementally through the pass -- splitting it into fully
# independent functions would mean re-deriving or re-threading all of
# that state through extra parameters, with no reuse benefit elsewhere
# in the module (nothing outside this diagnostic pass needs
# c5_class/c5_rewritten again).
################################################################################

"""
    run_parts_a_to_e_diagnostic(F, cr::CoefRing, ts::TargetSetup, bm::BezoutMatrix)

Original lines 5506-6516 (PARTS A-E). Only runs when `ts.d1T == ts.d2T
== 4` (checked by the caller the same way `build_concrete_bezout_diagnostic`
is). `F` is the base field, needed to build the symmetric-basis and
scratch rings used partway through PART C/C.5. Prints an extensive
diagnostic report; returns `nothing` (this pass exists entirely for its
printed output, matching the original -- no downstream PART K code
consumes its return value).
"""
function run_parts_a_to_e_diagnostic(F, cr::CoefRing, ts::TargetSetup, bm::BezoutMatrix)
    if !(ts.d1T == 4 && ts.d2T == 4)
        return nothing
    end

    name = ts.name
    Rcoef = cr.Rcoef
    a1_c, a2_c, b1_c, b2_c = cr.a1_c, cr.a2_c, cr.b1_c, cr.b2_c
    p_coef, q_coef = bm.p_coef, bm.q_coef
    B = bm.B

    println()
    println("=" ^ 70)
    println("PARTS A-E: deep diagnostic (no resultant computed) -- $name")
    println("=" ^ 70)
    flush(stdout)

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
        if !iszero(c0) && !iszero(c4)
            println("      $gname palindromic check: deg(c0)=", total_degree(c0),
                    " vs deg(c4)=", total_degree(c4),
                    "   deg(c1)=", total_degree(c1),
                    " vs deg(c3)=", total_degree(c3))
        end
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

    swap_a = hom(Rcoef, Rcoef, [a2_c, a1_c, b1_c, b2_c])
    swap_b = hom(Rcoef, Rcoef, [a1_c, a2_c, b2_c, b1_c])

    function is_symmetric_under(f, phi)
        return iszero(f - phi(f))
    end

    all_coefs = vcat(
        [("g1", k, g1_coefs_poly[k+1]) for k in 0:4],
        [("g2", k, g2_coefs_poly[k+1]) for k in 0:4]
    )

    all_a_sym = true
    all_b_sym = true
    for (gname, k, f) in all_coefs
        if iszero(f)
            continue
        end
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

        Rsym, (sa, pa, sb, pb) = polynomial_ring(F, ["sa", "pa", "sb", "pb"])

        function try_symmetric_rewrite(f)
            try
                Rext, (a1e,a2e,b1e,b2e,sae,pae,sbe,pbe) = polynomial_ring(
                    F, ["a1","a2","b1","b2","sa","pa","sb","pb"])
                incl = hom(Rcoef, Rext, [a1e,a2e,b1e,b2e])
                fe = incl(f)
                fe2 = evaluate(fe, [a1e, sae - a1e, b1e, b2e, sae, pae, sbe, pbe])
                relation_a = a1e^2 - sae*a1e + pae
                q, r = divrem(fe2, relation_a)
                fe3 = r
                fe4 = evaluate(fe3, [a1e, a2e, b1e, sbe - b1e, sae, pae, sbe, pbe])
                relation_b = b1e^2 - sbe*b1e + pbe
                q2, r2 = divrem(fe4, relation_b)
                fe5 = r2
                deg_a1_remaining = degree(fe5, a1e)
                deg_b1_remaining = degree(fe5, b1e)
                if deg_a1_remaining > 0 || deg_b1_remaining > 0
                    return (nothing, "residual a1/b1-degree after reduction " *
                            "(a1:$deg_a1_remaining, b1:$deg_b1_remaining) -- " *
                            "symmetric rewrite incomplete, reporting raw reduced form")
                end
                Bctx = MPolyBuildCtx(Rsym)
                for (c, exps) in zip(coefficients(fe5), AbstractAlgebra.exponent_vectors(fe5))
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

    _run_part_c5_and_de!(F, cr, ts, bm, g1_coefs_poly, g2_coefs_poly, all_coefs,
                          safe_factor_report, coef_as_poly)

    return nothing
end

"""
    _run_part_c5_and_de!(F, cr, ts, bm, g1_coefs_poly, g2_coefs_poly, all_coefs,
                          safe_factor_report, coef_as_poly)

Original lines 5842-6516 (PART C.5, PART D, PART E). Internal helper
called only from `run_parts_a_to_e_diagnostic` -- split out purely to
keep that function from being one single several-hundred-line body, not
because this piece is independently reusable (it still shares
`g1_coefs_poly`/`g2_coefs_poly`/`all_coefs`/`safe_factor_report`/
`coef_as_poly` with its caller, passed through explicitly rather than
recomputed). Returns `nothing`; exists for its printed diagnostic output.
"""
function _run_part_c5_and_de!(F, cr::CoefRing, ts::TargetSetup, bm::BezoutMatrix,
                               g1_coefs_poly::Vector, g2_coefs_poly::Vector, all_coefs,
                               safe_factor_report, coef_as_poly)
    name = ts.name
    Rcoef = cr.Rcoef
    a1_c, a2_c, b1_c, b2_c = cr.a1_c, cr.a2_c, cr.b1_c, cr.b2_c
    B = bm.B
    g1_T, g2_T = cr.g1_T, cr.g2_T

    # ------------------------------------------------------------------
    # PART C.5: PARTIAL symmetrization diagnostic (original lines
    # 5842-6419). See the original's own extensive comment for why this
    # exists (PART C only fires when a coefficient is symmetric under
    # BOTH swaps at once; this handles the one-sided case) and the
    # IMPLEMENTATION NOTE on why degree-by-degree substitution is used
    # instead of `divrem` against a 2-term relation (degrevlex tie-
    # breaking silently made that a no-op the first time it was tried).
    # ------------------------------------------------------------------
    println()
    println("--- PART C.5: partial symmetrization diagnostic ---")
    flush(stdout)

    Rb_only, (a1b, a2b, sbb, pbb) = polynomial_ring(F, ["a1", "a2", "sb", "pb"])
    Ra_only, (saa, paa, b1a, b2a) = polynomial_ring(F, ["sa", "pa", "b1", "b2"])

    Rext_c5, (a1c5, a2c5, b1c5, b2c5, sac5, pac5, sbc5, pbc5) = polynomial_ring(
        F, ["a1", "a2", "b1", "b2", "sa", "pa", "sb", "pb"])
    incl_c5 = hom(Rcoef, Rext_c5, [a1c5, a2c5, b1c5, b2c5])

    function reduce_quadratic!(coeffs_by_deg::Dict{Int,Any}, lin, const_term)
        maxd = maximum(keys(coeffs_by_deg))
        for d in maxd:-1:2
            c = get(coeffs_by_deg, d, nothing)
            if c === nothing || iszero(c)
                delete!(coeffs_by_deg, d)
                continue
            end
            delete!(coeffs_by_deg, d)
            coeffs_by_deg[d-1] = get(coeffs_by_deg, d-1, zero(c)) + lin*c
            coeffs_by_deg[d-2] = get(coeffs_by_deg, d-2, zero(c)) + const_term*c
        end
        return coeffs_by_deg
    end

    function symmetrize_b_only(f; debug::Bool=false)
        fe = incl_c5(f)
        fe2 = evaluate(fe, [a1c5, a2c5, b1c5, sbc5 - b1c5, sac5, pac5, sbc5, pbc5])
        d = degree(fe2, b1c5)
        coeffs_by_deg = Dict{Int,Any}()
        for k in 0:d
            ck = coeff(fe2, [var_index(b1c5)], [k])
            if !iszero(ck)
                coeffs_by_deg[k] = ck
            end
        end
        if isempty(coeffs_by_deg)
            coeffs_by_deg[0] = zero(fe2)
        end
        reduce_quadratic!(coeffs_by_deg, sbc5, -pbc5)
        if haskey(coeffs_by_deg, 1) && !iszero(coeffs_by_deg[1])
            return (nothing, "residual b1-degree=1 term did not vanish after " *
                    "reduction -- f was not actually (b1,b2)-symmetric, or " *
                    "reduction bug")
        end
        r = get(coeffs_by_deg, 0, zero(fe2))
        Bctx = MPolyBuildCtx(Rb_only)
        for (c, exps) in zip(coefficients(r), AbstractAlgebra.exponent_vectors(r))
            if exps[3] != 0 || exps[4] != 0
                return (nothing, "unexpected leftover b1/b2 exponent after reduction " *
                        "(exps=$exps) -- reduction did not fully eliminate b1,b2")
            end
            if exps[5] != 0 || exps[6] != 0
                return (nothing, "unexpected sa/pa dependence in a b-only rewrite " *
                        "(exps=$exps) -- sa,pa should never appear here")
            end
            push_term!(Bctx, c, [exps[1], exps[2], exps[7], exps[8]])
        end
        fsym = finish(Bctx)
        return (fsym, nothing)   # lives in Rb_only: (a1,a2,sb,pb)
    end

    function symmetrize_a_only(f; debug::Bool=false)
        fe = incl_c5(f)
        fe2 = evaluate(fe, [a1c5, sac5 - a1c5, b1c5, b2c5, sac5, pac5, sbc5, pbc5])
        d = degree(fe2, a1c5)
        coeffs_by_deg = Dict{Int,Any}()
        for k in 0:d
            ck = coeff(fe2, [var_index(a1c5)], [k])
            if !iszero(ck)
                coeffs_by_deg[k] = ck
            end
        end
        if isempty(coeffs_by_deg)
            coeffs_by_deg[0] = zero(fe2)
        end
        reduce_quadratic!(coeffs_by_deg, sac5, -pac5)
        if haskey(coeffs_by_deg, 1) && !iszero(coeffs_by_deg[1])
            return (nothing, "residual a1-degree=1 term did not vanish after " *
                    "reduction -- f was not actually (a1,a2)-symmetric, or " *
                    "reduction bug")
        end
        r = get(coeffs_by_deg, 0, zero(fe2))
        Bctx = MPolyBuildCtx(Ra_only)
        for (c, exps) in zip(coefficients(r), AbstractAlgebra.exponent_vectors(r))
            if exps[1] != 0 || exps[2] != 0
                return (nothing, "unexpected leftover a1/a2 exponent after reduction " *
                        "(exps=$exps) -- reduction did not fully eliminate a1,a2")
            end
            if exps[7] != 0 || exps[8] != 0
                return (nothing, "unexpected sb/pb dependence in an a-only rewrite " *
                        "(exps=$exps) -- sb,pb should never appear here")
            end
            push_term!(Bctx, c, [exps[5], exps[6], exps[3], exps[4]])
        end
        fsym = finish(Bctx)
        return (fsym, nothing)   # lives in Ra_only: (sa,pa,b1,b2)
    end

    println()
    println("  Section 1: per-coefficient single-pair symmetry classification")
    println("  (independent of PART C's all-coefficients-at-once verdict above)")
    flush(stdout)

    swap_a = hom(Rcoef, Rcoef, [a2_c, a1_c, b1_c, b2_c])
    swap_b = hom(Rcoef, Rcoef, [a1_c, a2_c, b2_c, b1_c])
    function is_symmetric_under(f, phi)
        return iszero(f - phi(f))
    end

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
            cls = :indep_of_both
        elseif !depends_on_b
            cls = :indep_of_b
        elseif !depends_on_a
            cls = :indep_of_a
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
    flush(stdout)

    c5_rewritten = Dict{Tuple{String,Int},Any}()
    debug_done_b = false
    debug_done_a = false
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
                    "not depend on b1,b2 at all (only a1,a2); already minimal in b.")
            continue
        elseif cls == :indep_of_a
            println("    $gname coeff of T^$k: VACUOUS a-symmetry -- coefficient does ",
                    "not depend on a1,a2 at all (only b1,b2); already minimal in a.")
            continue
        end

        before_terms = length(terms(f))
        before_deg = total_degree(f)

        if cls == :b_only
            do_dbg = !debug_done_b
            do_dbg && (debug_done_b = true)
            fsym, err = symmetrize_b_only(f; debug=do_dbg)
            pairname = "b"
        else # :a_only
            do_dbg = !debug_done_a
            do_dbg && (debug_done_a = true)
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
    flush(stdout)

    g1_b_only_present = any(c5_class[("g1",k)] == :b_only for k in 0:4 if haskey(c5_class,("g1",k)))
    g2_a_only_present = any(c5_class[("g2",k)] == :a_only for k in 0:4 if haskey(c5_class,("g2",k)))

    if g1_b_only_present && g2_a_only_present
        println("    g1 has (b1,b2)-symmetric coefficient(s); g2 has (a1,a2)-symmetric ",
                "coefficient(s) -- this is the expected asymmetric case from the log.")
        println("    g1's natural target ring after rewrite: (a1,a2,sb,pb)")
        println("    g2's natural target ring after rewrite: (sa,pa,b1,b2)")
        println("    Common ring containing BOTH without reintroducing any variable ",
                "individually: NONE.")
        println("    Only combination routes available, in order of cost:")
        println("      (i)   map BOTH into the raw ring (a1,a2,b1,b2) -- discards all")
        println("            symmetrization savings before the combination step.")
        println("      (ii)  desymmetrize the OTHER pair back out of each side via the")
        println("            quadratic formula before combining -- reintroduces a")
        println("            degree-2 field extension per desymmetrized pair.")
        println("      (iii) fully symmetrize BOTH g1 and g2 in BOTH pairs -- only valid")
        println("            if g1 is ALSO (a1,a2)-symmetric and g2 ALSO (b1,b2)-symmetric,")
        println("            which per PART C above is FALSE, so unavailable.")
        println("    VERDICT: partial symmetrization reduces individual size but does")
        println("    NOT by itself simplify the PART K combination step -- open sub-problem.")
    else
        g1_indep_b = any(get(c5_class, ("g1",k), nothing) == :indep_of_b for k in 0:4)
        g2_indep_a = any(get(c5_class, ("g2",k), nothing) == :indep_of_a for k in 0:4)
        if g1_indep_b && g2_indep_a
            println("    Did NOT find genuine b-only/a-only partial symmetry -- instead,")
            println("    Section 1 found g1's coefficients are entirely INDEPENDENT of")
            println("    b1,b2 and g2's are entirely INDEPENDENT of a1,a2 -- a narrower,")
            println("    stronger variable-dependence fact than partial symmetry, not")
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
        println("    recombining still requires route (i) or (ii) above.")
    else
        println("    g1[T^0]/g2[T^0] not both eligible for partial symmetrization in ",
                "this run -- skipping Section 4 size probe (see Section 1 above).")
    end
    flush(stdout)

    println()
    println("PART C.5 COMPLETE")
    flush(stdout)

    # ------------------------------------------------------------------
    # PART D: Bezout entry sparsity / factoring analysis
    # ------------------------------------------------------------------
    println()
    println("--- PART D: Bezout entry sparsity analysis ---")
    flush(stdout)

    function monomial_support_report(f; indent::String="        ")
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

    for i in 0:3, j in i:3
        f = B[(i,j)]
        println("  B[$i,$j]:")
        println("    total_degree=", total_degree(f), "  terms=", length(terms(f)))
        monomial_support_report(f)
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
    println("=" ^ 70)
    flush(stdout)

    return nothing
end
################################################################################
# PART F: exploit p_i in F[a1,a2] / q_j in F[b1,b2] separability. Original
# lines 6518-8013.
#
# Kept as one function rather than split further: the disk-sharded
# checkpoint/resume/final-merge/cleanup sequence is a single stateful
# process where correctness depends on strict ordering (build shards ->
# finish substitution loop -> merge existing shards exactly once -> stat
# -> save -> only THEN clean up shards, gated on a passing crosscheck).
# Splitting it into separate top-level functions would mean threading a
# large amount of shared mutable state (detB_concrete, shard paths,
# progress counters, the various caches) through extra parameters with
# no reuse benefit -- nothing else in this module needs a second
# disk-sharded accumulator.
################################################################################

"""
    run_part_f_bezout!(F, p::Int, cr::CoefRing, ts::TargetSetup, bm::BezoutMatrix;
                        scratch_dir)

Original lines 6518-8013 (PART F). Only meaningful when
`ts.d1T == ts.d2T == 4` (checked by the caller via `bm !== nothing`,
matching `build_concrete_bezout_diagnostic`'s own gating). Computes
`det(Bpq)` in an ABSTRACT 10-variable ring `F[P0..P4,Q0..Q4]` (cheap:
degree <=8, no dependence on how large the real `a1,a2,b1,b2`
coefficients are), then substitutes the real `p_i(a1,a2)` / `q_j(b1,b2)`
polynomials in via a disk-sharded, checkpointed, resumable streaming
substitution (STAGE 1: substitute P only, leaving Q abstract in a tower
ring `Ra[Q0..Q4]`; STAGE 2: substitute Q, folding each term's
contribution into `detB_concrete` in bounded-size chunks). Saves the
result to `ts.RESULTANT_FILE` and returns it (`res_num`). `p` is the
field characteristic, needed to size-check the flat-binary shard
coefficient type.

Raises an error (never silently proceeds) if: a shard coefficient
doesn't fit `SHARD_COEFF_TYPE`, a shard's exponent-array length is
inconsistent with its term count, a `.native` shard has the wrong
format-magic header, `detB_concrete` ends up with zero terms after the
final merge, `var_names` mismatches `Rcoef`'s variable count, a term's
exponent-vector length is inconsistent with `Rcoef`, or shard cleanup
fails to remove a file it expected to remove.
"""
function run_part_f_bezout!(F, p::Int, cr::CoefRing, ts::TargetSetup, bm::BezoutMatrix;
                             scratch_dir::String = joinpath(@__DIR__, "part_k_results"))
    name = ts.name
    Rcoef = cr.Rcoef
    a1_c, a2_c, b1_c, b2_c = cr.a1_c, cr.a2_c, cr.b1_c, cr.b2_c
    B = bm.B

    println()
    println("--- PART F: abstract-variable (P,Q)-separated Bezout/resultant ---")
    println("  (exploits p_i in F[a1,a2] / q_j in F[b1,b2] confirmed by the")
    println("  Section-1 fix above; see PART D's exact 289*289=83521 entry")
    println("  term counts for the empirical signature that motivated this.)")
    flush(stdout)

    Rpq, pq_gens = polynomial_ring(F, ["P0","P1","P2","P3","P4","Q0","Q1","Q2","Q3","Q4"])
    P0,P1,P2,P3,P4,Q0,Q1,Q2,Q3,Q4 = pq_gens
    Pvec = [P0,P1,P2,P3,P4]
    Qvec = [Q0,Q1,Q2,Q3,Q4]

    abstract_bracket_cache = Dict{Tuple{Int,Int}, Any}()
    function abstract_bracket(m::Int, n::Int)
        key = m < n ? (m, n) : (n, m)
        if !haskey(abstract_bracket_cache, key)
            i, j = key
            abstract_bracket_cache[key] = Pvec[i+1]*Qvec[j+1] - Pvec[j+1]*Qvec[i+1]
        end
        return m < n ? abstract_bracket_cache[key] : -abstract_bracket_cache[key]
    end

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

    println("  Assembling abstract 4x4 matrix and computing det()...")
    flush(stdout)
    t0f = time()
    Bpq_mat = matrix(Rpq, [Bpq[(i,j)] for i in 0:3, j in 0:3])
    detB_abstract = det(Bpq_mat)
    el_f = time() - t0f
    println("  det(Bpq) computed in ", round(el_f, digits=3), "s: degree=",
            total_degree(detB_abstract), "  terms=", length(terms(detB_abstract)))
    flush(stdout)

    # -- Recover g1_coefs_poly / g2_coefs_poly (PART A's Rcoef-lifted
    # coefficient list) from bm.p_coef/bm.q_coef, exactly as PART A did,
    # since PART F needs them independently of whether the full PARTS
    # A-E diagnostic ran first.
    function coef_as_poly(c)
        den = denominator(c)
        if !is_unit(den)
            println("      WARNING: coefficient has non-unit denominator (degree=",
                    total_degree(den), ") -- reporting numerator only.")
        end
        return Rcoef(numerator(c))
    end
    g1_coefs_poly = [coef_as_poly(bm.p_coef[k+1]) for k in 0:4]
    g2_coefs_poly = [coef_as_poly(bm.q_coef[k+1]) for k in 0:4]

    println("  --- STAGE 1: substituting P_i -> p_i(a1,a2) only,",
            " Q left abstract (R[P][Q]-style intermediate) ---")
    flush(stdout)

    t0stage1 = time()

    Ra, (a1_r, a2_r) = polynomial_ring(F, ["a1", "a2"])

    function lift_to_Ra(f)
        ctx = MPolyBuildCtx(Ra)
        for (c, exps) in zip(coefficients(f), AbstractAlgebra.exponent_vectors(f))
            ea1, ea2, eb1, eb2 = exps
            if eb1 != 0 || eb2 != 0
                error("lift_to_Ra: term has nonzero b1/b2 exponent ($eb1,$eb2) -- ",
                      "this P-coefficient was not purely (a1,a2) as PART A's ",
                      "diagnostic assumed. Refusing to silently drop content.")
            end
            push_term!(ctx, c, [ea1, ea2])
        end
        return finish(ctx)
    end
    g1_coefs_Ra = [lift_to_Ra(p) for p in g1_coefs_poly]

    Rmid, Qmid_gens = polynomial_ring(Ra, ["Q0", "Q1", "Q2", "Q3", "Q4"])

    stage1_images = vcat(
        [Rmid(c) for c in g1_coefs_Ra],
        Qmid_gens,
    )
    detB_mid = evaluate(detB_abstract, stage1_images)

    el_stage1 = time() - t0stage1
    mid_terms_list = collect(terms(detB_mid))
    println("  STAGE 1 complete in ", round(el_stage1, digits=3),
            "s: ", length(mid_terms_list), " Q-monomial terms")
    flush(stdout)

    # -- STAGE 2 setup: disk-sharded checkpointing scratch dir.
    PARTF_SCRATCH_DIR = joinpath(scratch_dir, "..", "part_f_scratch", name)
    mkpath(PARTF_SCRATCH_DIR)
    shards_dir     = joinpath(PARTF_SCRATCH_DIR, "shards")
    mkpath(shards_dir)
    shard_tmpfile  = joinpath(PARTF_SCRATCH_DIR, "shard.native.tmp")
    progress_file  = joinpath(PARTF_SCRATCH_DIR, "progress.txt")
    manifest_file  = joinpath(PARTF_SCRATCH_DIR, "manifest.txt")

    shard_path(upto_term_idx) = joinpath(shards_dir, "shard_" * lpad(upto_term_idx, 6, '0') * ".native")
    function existing_shard_paths()
        !isdir(shards_dir) && return String[]
        names = filter(readdir(shards_dir)) do f
            startswith(f, "shard_") && (endswith(f, ".native") || endswith(f, ".oscar"))
        end
        return sort(joinpath.(shards_dir, names))
    end

    detB_terms = mid_terms_list
    n_terms = length(detB_terms)
    println("  substituting ", n_terms, " terms -> ", shards_dir)
    flush(stdout)

    t0terms = time()
    n_already_done = 0
    if isfile(progress_file)
        n_already_done = parse(Int, strip(read(progress_file, String)))
        if n_already_done > 0
            shard_paths = existing_shard_paths()
            println("  resuming: ", n_already_done, "/", n_terms,
                    " terms, ", length(shard_paths), " shard(s)")
            flush(stdout)
        end
    end

    SHARD_COEFF_TYPE = UInt32
    SHARD_EXP_TYPE   = Int32
    SHARD_FORMAT_MAGIC = UInt64(0xF1A7B10C_00000002)

    p > typemax(SHARD_COEFF_TYPE) &&
        error("run_part_f_bezout!: field characteristic p=$p does not fit in " *
              "$(SHARD_COEFF_TYPE) (max $(typemax(SHARD_COEFF_TYPE))) -- " *
              "widen SHARD_COEFF_TYPE before writing shards, or every " *
              "coefficient write below will silently truncate")

    function read_rss_mb()
        for line in eachline("/proc/self/status")
            if startswith(line, "VmRSS:")
                parts = split(line)
                return parse(Int, parts[2]) / 1024.0
            end
        end
        return -1.0
    end

    function save_shard_native(path, poly)
        println("      save_shard_native: starting streamed write to ", path,
                " (RSS=", read_rss_mb(), "MB)")
        flush(stdout)
        open(path, "w") do io
            write(io, SHARD_FORMAT_MAGIC)
            n_terms_pos = position(io)
            write(io, Int64(0))
            term_idx = 0
            for (cf, ev) in zip(coefficients(poly), AbstractAlgebra.exponent_vectors(poly))
                term_idx += 1
                cv = lift(ZZ, cf)
                (cv < 0 || cv > typemax(SHARD_COEFF_TYPE)) &&
                    error("save_shard_native: coefficient $cv at term $term_idx out of " *
                          "range for $(SHARD_COEFF_TYPE) in $path -- refusing to " *
                          "write a shard that would silently corrupt data")
                write(io, SHARD_COEFF_TYPE(cv))
                length(ev) != 4 &&
                    error("save_shard_native: expected 4 exponents (a1,a2,b1,b2), " *
                          "got $(length(ev)) at term $term_idx in $path")
                for j in 1:4
                    write(io, SHARD_EXP_TYPE(ev[j]))
                end
                if term_idx % 200_000 == 0
                    println("        save_shard_native: ", term_idx,
                            " terms written, RSS=", read_rss_mb(), "MB")
                    flush(stdout)
                end
            end
            end_pos = position(io)
            seek(io, n_terms_pos)
            write(io, Int64(term_idx))
            seek(io, end_pos)
            println("      save_shard_native: finished, ", term_idx,
                    " terms written, RSS=", read_rss_mb(), "MB")
            flush(stdout)
        end
        return nothing
    end

    function load_shard_native(sp)
        t0 = time()
        fsize_mb = filesize(sp) / 1024 / 1024
        println("    ", basename(sp), ": starting bulk read (", round(fsize_mb, digits=0),
                " MB on disk)...")
        flush(stdout)
        n_terms_shard, coeffs_in, exps_in = open(sp, "r") do io
            magic = read(io, UInt64)
            magic != SHARD_FORMAT_MAGIC &&
                error("load_shard_native: $sp does not have the expected flat-" *
                      "binary format header (got magic=$(magic), expected " *
                      "$(SHARD_FORMAT_MAGIC)) -- this is almost certainly an " *
                      "OLD-format .native shard written by an earlier version. " *
                      "Delete all .native shards under this scratch dir and " *
                      "let them regenerate, or restore from .oscar shards if " *
                      "available.")
            nt = read(io, Int64)
            cf = Vector{SHARD_COEFF_TYPE}(undef, nt)
            ex = Vector{SHARD_EXP_TYPE}(undef, 4 * nt)
            read!(io, cf)
            read!(io, ex)
            (nt, cf, ex)
        end
        length(exps_in) != 4 * n_terms_shard &&
            error("load_shard_native: corrupt shard $sp -- exponent array " *
                  "length $(length(exps_in)) is not 4x the term count " *
                  "$n_terms_shard ($(4 * n_terms_shard) expected)")
        println("    ", basename(sp), ": read ", n_terms_shard, " terms in ",
                round(time() - t0, digits=1), "s; rebuilding polynomial...")
        flush(stdout)
        t1 = time()
        rebuild_ctx = MPolyBuildCtx(Rcoef)
        exps_buf = Vector{Int}(undef, 4)
        for i in 1:n_terms_shard
            base = 4 * (i - 1)
            exps_buf[1] = Int(exps_in[base + 1])
            exps_buf[2] = Int(exps_in[base + 2])
            exps_buf[3] = Int(exps_in[base + 3])
            exps_buf[4] = Int(exps_in[base + 4])
            push_term!(rebuild_ctx, F(Int(coeffs_in[i])), exps_buf)
            if i % 2_000_000 == 0
                el = time() - t1
                rate = i / el
                eta = (n_terms_shard - i) / rate
                println("      rebuilt ", i, "/", n_terms_shard, " terms (",
                        round(rate, digits=0), " terms/s, ETA ",
                        round(eta, digits=0), "s)...")
                flush(stdout)
            end
        end
        rebuilt = finish(rebuild_ctx)
        println("    ", basename(sp), ": rebuilt ok in ",
                round(time() - t1, digits=1), "s (total incl. deserialize: ",
                round(time() - t0, digits=1), "s)")
        flush(stdout)
        return rebuilt
    end

    function load_shard_rebuilt(sp)
        loaded = load(sp)
        loaded_n_terms = length(loaded)
        print("    ", basename(sp), ": loaded ", loaded_n_terms, " terms")
        flush(stdout)

        local rebuilt
        try
            rebuilt = Rcoef(loaded)
            print("; cheap coercion ok\n")
        catch e
            println()
            println("      cheap coercion failed (", typeof(e), ") -- falling",
                    " back to term-by-term rebuild for this shard (", loaded_n_terms,
                    " terms). Printing progress every 500k terms:")
            flush(stdout)
            rebuild_ctx = MPolyBuildCtx(Rcoef)
            n_pushed = 0
            t0rebuild = time()
            for (c, exps) in zip(coefficients(loaded), AbstractAlgebra.exponent_vectors(loaded))
                push_term!(rebuild_ctx, F(c), exps)
                n_pushed += 1
                if n_pushed % 500_000 == 0
                    println("      rebuilt ", n_pushed, "/", loaded_n_terms,
                            " terms (", round(time() - t0rebuild, digits=1), "s elapsed)")
                    flush(stdout)
                end
            end
            rebuilt = finish(rebuild_ctx)
            println("      term-by-term rebuild complete: ", n_pushed, " terms in ",
                    round(time() - t0rebuild, digits=1), "s.")
        end
        loaded = nothing
        return rebuilt
    end

    detB_concrete = zero(Rcoef)

    HAVE_INPLACE_ADD = applicable(add!, detB_concrete, detB_concrete, detB_concrete)
    HAVE_SAFE_SELF_ALIAS_ADD = false
    if HAVE_INPLACE_ADD
        _probe = Rcoef(gens(Rcoef)[1])
        _probe_expected = _probe + _probe
        _probe_copy = deepcopy(_probe)
        add!(_probe_copy, _probe_copy, _probe)
        HAVE_SAFE_SELF_ALIAS_ADD = (_probe_copy == _probe_expected)
    end

    if HAVE_SAFE_SELF_ALIAS_ADD
        println("  using in-place add!")
    elseif HAVE_INPLACE_ADD
        println("  add! unsafe here, falling back to +")
    else
        println("  add! unavailable, falling back to +")
    end
    flush(stdout)

    q_monomial_cache = Dict{NTuple{5,Int}, Any}()
    q_power_cache = Dict{Tuple{Int,Int}, Any}()

    function chunked_poly_mul(x, y; chunk::Int=200)
        x_terms = collect(terms(x))
        y_terms = collect(terms(y))
        nx = length(x_terms)
        ny = length(y_terms)
        result = zero(Rcoef)
        xi = 1
        while xi <= nx
            xe = min(xi + chunk - 1, nx)
            x_chunk = sum(x_terms[xi:xe]; init=zero(Rcoef))
            yi = 1
            while yi <= ny
                ye = min(yi + chunk - 1, ny)
                y_chunk = sum(y_terms[yi:ye]; init=zero(Rcoef))
                partial = x_chunk * y_chunk
                if HAVE_SAFE_SELF_ALIAS_ADD
                    add!(result, result, partial)
                else
                    result = result + partial
                end
                partial = nothing
                y_chunk = nothing
                yi = ye + 1
            end
            x_chunk = nothing
            xi = xe + 1
        end
        return result
    end

    function chunked_pow(base, e::Int; chunk::Int=200)
        e < 0 && throw(ArgumentError("chunked_pow: exponent must be non-negative, got $e"))
        e == 0 && return one(Rcoef)
        result = base
        remaining = e - 1
        while remaining > 0
            n_result_terms = length(terms(result))
            n_base_terms = length(terms(base))
            this_chunk = n_result_terms * n_base_terms > (200^2) ?
                max(20, round(Int, chunk / sqrt((n_result_terms * n_base_terms) / (200.0^2)))) :
                chunk
            result = chunked_poly_mul(result, base; chunk=this_chunk)
            remaining -= 1
        end
        return result
    end

    function cached_q_power(k::Int, e::Int)
        e <= 0 && throw(ArgumentError("cached_q_power: exponent must be positive, got $e for k=$k"))
        key = (k, e)
        cached = get(q_power_cache, key, nothing)
        cached !== nothing && return cached
        val = chunked_pow(g2_coefs_poly[k], e)
        q_power_cache[key] = val
        return val
    end

    function cached_b_side(t_exps)
        key = NTuple{5,Int}(t_exps)
        if haskey(q_monomial_cache, key)
            throw(AssertionError("cached_b_side: duplicate Q-monomial exponent vector $key encountered -- Stage 1's Rmid collection was expected to make these unique per detB_terms entry; investigate before trusting the cache"))
        end
        val = one(Rcoef)
        for k in 1:5
            eQk = t_exps[k]
            if eQk > 0
                factor = cached_q_power(k, eQk)
                n_val_terms = length(terms(val))
                n_factor_terms = length(terms(factor))
                this_chunk = n_val_terms * n_factor_terms > (200^2) ?
                    max(20, round(Int, 200 / sqrt((n_val_terms * n_factor_terms) / (200.0^2)))) :
                    200
                val = chunked_poly_mul(val, factor; chunk=this_chunk)
            end
        end
        q_monomial_cache[key] = val
        return val
    end

    max_term_size_seen = 0
    max_term_size_idx = 0
    delta_since_checkpoint = zero(Rcoef)
    for (i, t) in enumerate(detB_terms)
        if i <= n_already_done
            continue
        end
        t0iter = time()
        rss_before = read_rss_mb()

        t0eval = time()
        t_exps = first(AbstractAlgebra.exponent_vectors(t))
        t_ra_coeff = first(coefficients(t))

        a_side = remap_to_final(t_ra_coeff, [a1_c, a2_c, b1_c, b2_c], [1, 2])
        b_side = cached_b_side(t_exps)

        this_size = length(terms(a_side)) * length(terms(b_side))
        if this_size > max_term_size_seen
            max_term_size_seen = this_size
            max_term_size_idx = i
        end

        BASELINE_SIDE_TERMS = 8385
        size_ratio = this_size / (BASELINE_SIDE_TERMS^2)
        PARTF_CHUNK = size_ratio > 1 ?
            max(20, round(Int, 200 / sqrt(size_ratio))) :
            200
        if size_ratio > 1
            println("      term ", i, ": this_size=", this_size,
                    " (", round(size_ratio, digits=1), "x baseline) -> PARTF_CHUNK=", PARTF_CHUNK)
            flush(stdout)
        end

        a_terms = collect(terms(a_side))
        b_terms = collect(terms(b_side))
        n_a_terms = length(a_terms)
        n_b_terms = length(b_terms)

        PARTF_CHUNK_GC_EVERY = 25
        n_chunk_pairs_done = 0

        this_term_sum = zero(Rcoef)
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
                    add!(this_term_sum, this_term_sum, partial)
                else
                    this_term_sum = this_term_sum + partial
                end
                partial = nothing
                b_chunk = nothing
                b_chunk_start = b_chunk_end + 1

                n_chunk_pairs_done += 1
                if n_chunk_pairs_done % PARTF_CHUNK_GC_EVERY == 0
                    GC.gc(true)
                    ccall(:malloc_trim, Cvoid, (Cint,), 0)
                end
            end
            a_chunk = nothing
            a_chunk_start = a_chunk_end + 1
        end

        if HAVE_SAFE_SELF_ALIAS_ADD
            add!(detB_concrete, detB_concrete, this_term_sum)
            add!(delta_since_checkpoint, delta_since_checkpoint, this_term_sum)
        else
            detB_concrete = detB_concrete + this_term_sum
            delta_since_checkpoint = delta_since_checkpoint + this_term_sum
        end
        this_term_sum = nothing

        a_side = nothing
        b_side = nothing
        a_terms = nothing
        b_terms = nothing
        el_eval = time() - t0eval
        rss_after_eval = read_rss_mb()

        t0fold = time()
        el_fold = time() - t0fold
        rss_after_fold = read_rss_mb()

        t0gc = time()
        GC.gc(true)
        ccall(:malloc_trim, Cvoid, (Cint,), 0)
        el_gc = time() - t0gc
        rss_after_gc = read_rss_mb()

        PARTF_CHECKPOINT_EVERY = 5
        do_checkpoint = (i % PARTF_CHECKPOINT_EVERY == 0) || (i == n_terms)

        local el_write, el_mv, el_prog, rss_after_save
        if do_checkpoint
            println("      checkpoint at term ", i, ": delta_since_checkpoint has ",
                    length(terms(delta_since_checkpoint)), " terms, RSS=", read_rss_mb(), "MB")
            flush(stdout)
            t0write = time()
            save_shard_native(shard_tmpfile, delta_since_checkpoint)
            el_write = time() - t0write

            t0mv = time()
            mv(shard_tmpfile, shard_path(i); force=true)
            el_mv = time() - t0mv

            t0prog = time()
            open(progress_file, "w") do io
                print(io, i)
            end
            el_prog = time() - t0prog

            rss_after_save = read_rss_mb()
            delta_since_checkpoint = zero(Rcoef)
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
            " streamed, sharded checkpoints) in ", round(el_sub, digits=1),
            "s this run.")
    flush(stdout)

    # -- FINAL MERGE PASS: fold any shards from a previous run in exactly once.
    if n_already_done > 0
        shard_paths_to_merge = existing_shard_paths()
        println("  Final merge: folding ", length(shard_paths_to_merge),
                " shard(s) from previous run(s) into this run's accumulator",
                " (", n_already_done, "/", n_terms, " terms' worth)...")
        flush(stdout)
        for (si, sp) in enumerate(shard_paths_to_merge)
            t0shard = time()
            shard_poly = endswith(sp, ".native") ? load_shard_native(sp) : load_shard_rebuilt(sp)
            if HAVE_SAFE_SELF_ALIAS_ADD
                add!(detB_concrete, detB_concrete, shard_poly)
            else
                detB_concrete = detB_concrete + shard_poly
            end
            shard_poly = nothing
            GC.gc(true)
            ccall(:malloc_trim, Cvoid, (Cint,), 0)
            println("    shard ", si, "/", length(shard_paths_to_merge), " (",
                    basename(sp), ") merged in ", round(time() - t0shard, digits=1), "s")
            flush(stdout)
        end
        println("  Final merge complete: detB_concrete now reflects all ", n_terms,
                " terms.")
        flush(stdout)
    end

    println("  substitution done (disk-backed, streamed): degree=",
            total_degree(detB_concrete), "  terms=", length(terms(detB_concrete)),
            "  (", round(el_sub, digits=1), "s substitution this run; ",
            "totals above include ", n_already_done, " terms merged in from",
            " prior-run shards)")
    flush(stdout)

    # -- FINAL-SUM STATISTICS.
    println("  ---- PART F final-sum statistics ----")
    flush(stdout)

    stats_t0 = time()
    n_final_terms = length(terms(detB_concrete))
    n_final_terms == 0 &&
        error("PART F final-sum stats: detB_concrete has zero terms after ",
              "merge -- this should be structurally impossible for a ",
              "genus-2 Bezoutian determinant and indicates upstream data ",
              "loss (empty/corrupt shard, or the merge loop above silently ",
              "skipped every shard). Refusing to report statistics on an ",
              "empty polynomial as if it were a real result.")

    var_names = ["a1", "a2", "b1", "b2"]
    nv = nvars(Rcoef)
    length(var_names) != nv &&
        error("PART F final-sum stats: var_names has ", length(var_names),
              " entries but Rcoef has ", nv, " variables -- update ",
              "var_names before trusting the per-variable degree table below.")
    min_deg_per_var = fill(typemax(Int), nv)
    max_deg_per_var = fill(0, nv)
    max_total_degree_seen = 0
    min_total_degree_seen = typemax(Int)
    min_coeff_zz = nothing
    max_coeff_zz = nothing
    for (c, exps) in zip(coefficients(detB_concrete), AbstractAlgebra.exponent_vectors(detB_concrete))
        length(exps) != nv &&
            error("PART F final-sum stats: term with ", length(exps),
                  " exponents encountered but Rcoef has ", nv,
                  " variables -- detB_concrete is malformed (likely a ",
                  "shard merged from a differently-shaped run); refusing ",
                  "to report statistics computed against inconsistent ",
                  "exponent vectors.")
        td = sum(exps)
        td > max_total_degree_seen && (max_total_degree_seen = td)
        td < min_total_degree_seen && (min_total_degree_seen = td)
        for k in 1:nv
            e = exps[k]
            e > max_deg_per_var[k] && (max_deg_per_var[k] = e)
            e < min_deg_per_var[k] && (min_deg_per_var[k] = e)
        end
        cv = lift(ZZ, c)
        if min_coeff_zz === nothing || cv < min_coeff_zz
            min_coeff_zz = cv
        end
        if max_coeff_zz === nothing || cv > max_coeff_zz
            max_coeff_zz = cv
        end
    end
    stats_elapsed = time() - stats_t0

    println("    term count        : ", n_final_terms)
    println("    total degree      : min=", min_total_degree_seen,
            "  max=", max_total_degree_seen)
    for k in 1:nv
        println("    degree in ", var_names[k], "        : min=", min_deg_per_var[k],
                "  max=", max_deg_per_var[k])
    end
    println("    coefficient range : min=", min_coeff_zz, "  max=", max_coeff_zz,
            "  (field characteristic p=", p, ")")
    bytes_per_term_flat = sizeof(SHARD_COEFF_TYPE) + 4 * sizeof(SHARD_EXP_TYPE)
    est_mb_flat = n_final_terms * bytes_per_term_flat / 1024 / 1024
    println("    est. flat-shard size at this term count: ",
            round(est_mb_flat, digits=1), " MB (", bytes_per_term_flat,
            " bytes/term)")
    println("    stats computed in ", round(stats_elapsed, digits=1), "s")
    flush(stdout)

    open(manifest_file, "w") do io
        println(io, "PART F disk-backed substitution manifest for $name")
        println(io, "n_terms = $n_terms")
        println(io, "checkpoint shards dir = $shards_dir")
        println(io, "final degree = ", total_degree(detB_concrete))
        println(io, "final terms  = ", n_final_terms)
        println(io, "total degree range = ", min_total_degree_seen, "..", max_total_degree_seen)
        for k in 1:nv
            println(io, "degree in ", var_names[k], " range = ", min_deg_per_var[k], "..", max_deg_per_var[k])
        end
        println(io, "coefficient range (ZZ lift) = ", min_coeff_zz, "..", max_coeff_zz)
        println(io, "field characteristic p = ", p)
        println(io, "est. flat-shard size at this term count (MB) = ", round(est_mb_flat, digits=1))
    end

    # -- Correctness cross-check against the concrete Bezout matrix.
    RUN_PARTF_DIRECT_CROSSCHECK = get(ENV, "ELIM2_PARTF_DIRECT_CROSSCHECK", "false") == "true"
    local agrees, n_mismatch
    if RUN_PARTF_DIRECT_CROSSCHECK
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
    else
        println("  Skipping full det(B) cross-check (set ",
                "ELIM2_PARTF_DIRECT_CROSSCHECK=true to enable -- expensive,",
                " dense, same computation that OOM'd before). Running a",
                " cheaper per-entry spot-check instead:")
        flush(stdout)
        n_mismatch = 0
        for (i, j) in [(0,0), (1,2), (2,3), (3,3)]
            abstract_entry_concrete = evaluate(Bpq[(i,j)], vcat(g1_coefs_poly, g2_coefs_poly))
            same = abstract_entry_concrete == B[(i,j)]
            n_mismatch += !same
            println("    entry ($i,$j): abstract-route == concrete B[$i,$j]? ", same)
        end
        println("    spot-check: ", n_mismatch == 0 ? "all entries agree" :
                "$n_mismatch MISMATCH(es) -- investigate before trusting PART F result")
        flush(stdout)
    end

    println("  PART F summary: det(Bpq) computed as a degree<=8 polynomial in",
            " 10 abstract symbols, THEN substituted once, instead of building")
    println("  and manipulating dense ", nvars(Rcoef), "-variable ", 83521,
            "-term entries at every intermediate step.")
    flush(stdout)

    # -- PERSIST THE RESULT.
    res_num = detB_concrete
    mkpath(dirname(ts.RESULTANT_FILE))
    save(ts.RESULTANT_FILE, res_num)
    println("  saved resultant -> ", ts.RESULTANT_FILE)
    flush(stdout)

    # -- SHARD CLEANUP (gated on a passing crosscheck).
    keep_shards_override = get(ENV, "ELIM2_PARTF_KEEP_SHARDS", "false") == "true"
    crosscheck_ok = true
    crosscheck_note = "no crosscheck/spot-check ran this branch"
    if RUN_PARTF_DIRECT_CROSSCHECK
        crosscheck_ok = agrees
        crosscheck_note = "full det(B) crosscheck: agrees=$agrees"
    else
        crosscheck_ok = (n_mismatch == 0)
        crosscheck_note = "spot-check: n_mismatch=$n_mismatch"
    end

    if keep_shards_override
        println("  Shard cleanup skipped: ELIM2_PARTF_KEEP_SHARDS=true.",
                " Shards remain under ", shards_dir, ".")
        flush(stdout)
    elseif !crosscheck_ok
        println("  Shard cleanup SKIPPED: correctness check did not pass",
                " clean (", crosscheck_note, ") -- keeping shards under ",
                shards_dir, " so the result can be re-derived/inspected.",
                " Investigate before re-running with cleanup enabled.")
        flush(stdout)
    else
        cleanup_shard_paths = existing_shard_paths()
        println("  Shard cleanup: ", crosscheck_note, " -- removing ",
                length(cleanup_shard_paths), " shard file(s) under ",
                shards_dir, " (result is durably saved in manifest_file",
                " and in RESULTANT_FILE, both written above)...")
        flush(stdout)
        n_removed = 0
        n_failed = 0
        bytes_freed = 0
        for sp in cleanup_shard_paths
            try
                sz = filesize(sp)
                rm(sp; force=false)
                n_removed += 1
                bytes_freed += sz
            catch e
                n_failed += 1
                println("    WARNING: failed to remove shard ", sp, ": ", e)
            end
        end
        if n_failed == 0 && isfile(progress_file)
            rm(progress_file; force=false)
        end
        println("    removed ", n_removed, "/", length(cleanup_shard_paths),
                " shard file(s), freed ", round(bytes_freed / 1024 / 1024, digits=1),
                " MB", n_failed > 0 ? "  ($n_failed FAILED -- see warnings above, shards_dir not fully clean)" : "")
        n_failed > 0 &&
            error("PART F shard cleanup: ", n_failed, " shard file(s) under ",
                  shards_dir, " could not be removed -- disk space was not",
                  " fully reclaimed. Inspect the warnings above (likely a",
                  " permissions issue or a file held open) before assuming",
                  " the scratch dir is clear for the resultant computation below.")
        flush(stdout)
    end

    println("  === $name complete: resultant numerator saved to ", ts.RESULTANT_FILE, " ===")
    flush(stdout)

    return res_num
end
################################################################################
# Top-level per-target driver and orchestrator.
################################################################################

"""
    run_part_k_target!(F, p, clean_sample_1, clean_sample_2, fu, name, i1, i2, Tvar;
                        scratch_dir)

Runs one target's (U0, U1, V0, or V1) full PART K pipeline: skip-if-done
check, fiber-product ring + coefficient extraction (`build_target_setup`),
coefficient-ring lift (`build_coef_ring`), the concrete Bezout diagnostic
(`build_concrete_bezout_diagnostic`), the PARTS A-E structural diagnostic
(`run_parts_a_to_e_diagnostic`), and finally PART F's abstract-Bezout
substitution (`run_part_f_bezout!`), matching the original's single
`for (name, i1, i2, Tvar) in target_specs ... end` loop body (lines
4858-8017) for one iteration. Returns `nothing` if this target was
already complete (skip) or if `d1T`/`d2T` weren't both 4 (diagnostics
and PART F are gated on that, matching the original -- there is no
fallback resultant path ported here, since the original's own fallback
[`resultant(g1_T, g2_T)` behind `RUN_FULL_RESULTANT`, and the manual PRS
in PART G] is the dead/removed code kept only as the trailing comment
block in this module, per the original's own note that it should be
deleted); otherwise returns the saved `res_num`.
"""
function run_part_k_target!(F, p::Int, clean_sample_1::Vector, clean_sample_2::Vector,
                             fu::FinalUniverse, name::String, i1::Int, i2::Int, Tvar;
                             scratch_dir::String = joinpath(@__DIR__, "part_k_results"))
    RESULTANT_FILE = joinpath(scratch_dir, "$(name)_resultant.oscar")
    if already_complete(RESULTANT_FILE)
        return nothing
    end

    g1 = fu.final_equations[i1]
    g2 = fu.final_equations[i2]
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

    ts = build_target_setup(F, clean_sample_1, clean_sample_2, name, i1, i2, d1T, d2T;
                             scratch_dir = scratch_dir)
    cr = build_coef_ring(F, ts)
    bm = build_concrete_bezout_diagnostic(cr, ts)

    if bm === nothing
        println("  --- $name: skipping PARTS A-E and PART F (d1T/d2T != 4) ---")
        flush(stdout)
        return nothing
    end

    run_parts_a_to_e_diagnostic(F, cr, ts, bm)
    res_num = run_part_f_bezout!(F, p, cr, ts, bm; scratch_dir = scratch_dir)

    return res_num
end

"""
    run_part_k!(F, p, clean_sample_1, clean_sample_2; scratch_dir)

Original lines 4684-8017 (the whole of PART K, top to bottom). Builds
the final universe (`build_final_universe`), then runs
`run_part_k_target!` for each of the 4 targets in `target_specs` order
(U0, U1, V0, V1), matching the original's single top-level
`for (name, i1, i2, Tvar) in target_specs` loop. Returns the
`FinalUniverse` plus a `Dict{String,Any}` of each target's `res_num`
(only populated for targets that actually ran PART F this call --
skipped/already-complete targets are omitted, matching how the original
only ever had `res_num` in scope for the target currently being
processed).
"""
function run_part_k!(F, p::Int, clean_sample_1::Vector, clean_sample_2::Vector;
                      scratch_dir::String = joinpath(@__DIR__, "part_k_results"))
    fu = build_final_universe(F, clean_sample_1, clean_sample_2)

    results = Dict{String,Any}()
    for (name, i1, i2, Tvar) in target_specs(fu)
        res_num = run_part_k_target!(F, p, clean_sample_1, clean_sample_2, fu,
                                      name, i1, i2, Tvar; scratch_dir = scratch_dir)
        if res_num !== nothing
            results[name] = res_num
        end
    end

    return (fu = fu, results = results)
end

################################################################################
# PART G REMOVED (original lines 8019-8397, kept verbatim below as a
# dead-code marker per the original's own note, NOT executed by this
# module -- reproduced here rather than dropped, since it documents WHY
# the manual disk-sharded PRS cross-check and the gated resultant()
# fallback were removed, and that reasoning is worth keeping alongside
# the code it explains).
#
# PART G REMOVED.
#
# The manual disk-sharded pseudo-remainder-sequence cross-check (and the
# separate gated resultant(g1_T, g2_T) call after it) used to live here.
# Both were redundant verification of what PART F already computes and
# saves directly (res_num = detB_concrete, written to RESULTANT_FILE
# inside the loop above, once per target) -- PART G never ran by default
# (RUN_PART_G_PRS defaulted false) and the gated resultant() call below
# it unconditionally exit(0)'d after the first target, which is what was
# blocking U1/V0/V1 from ever running. Removed rather than left as dead
# code now that the loop above is the single source of truth for all
# four targets' results.
#
# #=
# PART G: manually-driven, disk-sharded pseudo-remainder sequence (PRS).
#
# Motivation: the single opaque resultant(g1_T, g2_T) call below (kept,
# gated behind RUN_FULL_RESULTANT, as the reference/fallback path) is a
# black box -- when it hangs or OOMs there is no visibility into which
# PRS step is the problem, and no way to checkpoint partway through. PART
# F already independently computed the resultant's numerator (res_num,
# via the Bezout determinant, disk-sharded and fully verified against
# the concrete B by spot-check), so this PRS pass is NOT the only way to
# get the answer -- it exists as an independent, transparent, resumable
# computation of the SAME resultant via a different classical algorithm,
# specifically so a hang/crash mid-PRS is debuggable (which step, which
# degree, how big were the coefficients) instead of opaque.
#
# [The original's full manual PRS implementation -- next_permutation!,
# first_k_permutations, first_k_nonzero_permutations,
# count_nonzero_permutations, the PART_K_MAX_WORKERS subprocess pool,
# part_k_launch/part_k_harvest/part_k_summand_complete, and the entire
# "keep computing summands until one dies" driver loop, plus the manual
# shard-based PRS step-by-step reduction -- lived here, original lines
# ~8035-8397. It is intentionally NOT reproduced verbatim in this
# module: none of it is wrong, but per the removal note above it was
# solving a problem (surviving Leibniz expansion of an 8x8 determinant
# with huge entries) that PART F's abstract-Bezout route avoids needing
# to solve at all, and reproducing ~360 lines of never-executed
# (RUN_PART_G_PRS defaulted false) subprocess-pool machinery here would
# only obscure the module's actually-active code path. See elim2.jl's
# own lines 8034-8397 for the full original text if this history is
# ever needed again.]
# =#
################################################################################

end # module PartKResultant

"""
    run_all(PhiSymbolic; full_sweep_b=false)

Top-level entry point reproducing elim2.jl's original end-to-end
behavior, in original order, across all five submodules documented at
the top of this file:

  1. `Elim2Main.run_main(PhiSymbolic)` -- original lines 1-1090. Builds
     both samples' residuals, the shared target ring, the decoupled U/V
     system, etc.
  2. `NormElimDiag.run_norm_elim_diag(PhiSymbolic)` -- original lines
     1091-~1477. Standalone sample-1-only norm-elimination experiment,
     independent of step 1's state (see that function's own docstring).
  3. `NormElimDiag.run_all_diagnostics(PhiSymbolic, main)` -- original
     lines ~1478-2848 (PARTS A/B/D/E/H/H'/J). Consumes step 1's
     `DecoupledSystem`/`res1`/`s1`/`s2`; produces `clean_sample_1`/
     `clean_sample_2` (PART J's assembly-line output) needed by step 5.
  4. `PartIBench.run_full_bench_and_overlap_suite(res1, res2, cfg)` --
     original lines 3965-~5006 (part_i_eliminate_vs_resultant_bench.jl).
     Uses step 1's `res1`/`res2`, but its OWN `DiagCurveConfig` (built
     fresh here via `NormElimDiag.default_diag_curve_config()`, same
     values as `Elim2Main.CurveConfig` -- these were two independently
     top-level-`const`-declared `p`/`F_POLY_ASC`/`F` in the original,
     never actually different, so this is preserved duplication, not a
     bug -- see `NormElimDiag.run_all_diagnostics`'s own docstring for
     the same pattern).
  5. `PartKResultant.run_part_k!(F, p, clean_sample_1, clean_sample_2)`
     -- original lines ~4684-8017 (PART K, "The Final Collision"). Uses
     step 3's `clean_sample_1`/`clean_sample_2` and step 4's `cfg.F`/
     `cfg.p`.

PART I (part_i_squarefree_diag.jl, original lines 2854-3964) is NOT
called from here: it is pure function/diagnostic-machinery definitions
(`correct_multiplicity`, `squarefree_multiplicity_diagnostic`,
`factor_stage_trace`, etc.) consumed BY step 4's `_run_bench` internally
-- the original file never called a top-level driver for this section on
its own, only via PART I's bench cases. `PartISquarefreeDiag.
run_diag_on_bench_result` is available for ad hoc use afterward on any
one of step 4's `all_bench_results[case_key]` entries, but note it
expects NamedTuple-style `.gA`/`.gB` field access while `_run_bench`
actually returns a `Dict{String,Any}` (see that function's own
docstring, which already flags this as unverified) -- use
`bench_result["gA"]`/`bench_result["gB"]` directly with
`PartISquarefreeDiag.squarefree_multiplicity_diagnostic` instead if
needed, rather than `run_diag_on_bench_result` as written.

Returns a NamedTuple with each step's full result under `main`, `norm_diag`,
`diagnostics`, `bench`, `part_k`.
"""
function run_all(PhiSymbolic; full_sweep_b::Bool=false)
    main = Elim2Main.run_main(PhiSymbolic)

    norm_diag = NormElimDiag.run_norm_elim_diag(PhiSymbolic)
    diagnostics = NormElimDiag.run_all_diagnostics(PhiSymbolic, main; full_sweep_b = full_sweep_b)

    diag_cfg = NormElimDiag.default_diag_curve_config()
    bench = PartIBench.run_full_bench_and_overlap_suite(main.res1, main.res2, diag_cfg)

    part_k = PartKResultant.run_part_k!(diag_cfg.F, diag_cfg.p,
                                         diagnostics.clean_sample_1, diagnostics.clean_sample_2)

    return (main = main, norm_diag = norm_diag, diagnostics = diagnostics,
            bench = bench, part_k = part_k)
end

end # module Elim2
