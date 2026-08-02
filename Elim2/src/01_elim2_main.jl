################################################################################
#
#  01_elim2_main.jl -- part of the Elim2 package (src/Elim2.jl includes
#  this file). See src/Elim2.jl for the package-level overview and the
#  full include order of all submodule files.
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
using ..SampleSpecs: SampleSpec, default_sample1, default_sample2
using ..ExceptionalLocusGuard: guard_sample_spec

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
# SampleSpec / default_sample1 / default_sample2 now live in
# 00_sample_specs.jl (module SampleSpecs), imported above, so this is the
# ONE place K, c, fixed anchors, and u0/u1/v0/v1 are defined for both
# samples -- part_j_worker.jl reads the exact same values by `include`-ing
# that file directly (see its own header for why it can't just `using
# Elim2`). Original top-level consts these replace: K1,c1,fixed1,u0_1,
# u1_1,v0_1,v1_1 (sample 1) and K2,c2,fixed2,u0_2,u1_2,v0_2,v1_2 (sample 2).
################################################################################

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

################################################################################
# Mumford-identity check on the DECOUPLED system: v_RS(X)^2 ≡ f(X) (mod
# u_RS(X)), where u_RS/v_RS are re-formed from the U_i/V_i TARGET
# VARIABLES themselves (constrained by Fu_decoupled/Fv_decoupled to equal
# num_d[i]/den_d[i]), evaluated modulo Iuv_decoupled (Fu_decoupled +
# Fv_decoupled + curve relations).
#
# This exists to close the gap left after _check_mumford_identity_ring
# (map_sample, checked on u_num/u_den/v_num/v_den BEFORE the U/V
# decoupling): nothing previously re-verified the identity survives
# build_decoupled_system's OWN construction step (re-mapping each
# sample's num/den pairs from R into R_dec, ahead of Fu_decoupled/
# Fv_decoupled being built on top of them). If independent
# per-coefficient reduction upstream already decoupled u and v's shared
# dependence on a sample's anchor variables (the leading hypothesis
# flagged in trial3_phi_symbolic_unified.jl's post-reduction check
# docstring for the V-equation O(p^2)->O(1) solution-count collapse),
# that decoupling would surface here.
#
# IMPORTANT (revised from the first version of this check): this does
# NOT reduce modulo Fu_decoupled/Fv_decoupled. U_i/V_i are DEFINED by
# those equations to equal num_d[i]/den_d[i] on the curve -- so instead
# of re-deriving that equality via a Groebner basis over an ideal
# containing Fu_decoupled+Fv_decoupled (10 generators, degree up to 25,
# in the 16-variable R_dec -- this OOM'd a 20-thread machine, confirmed
# by the process dying immediately after this function was entered,
# right after the Fv_decoupled term-count printout, with no further
# output), we substitute num_d[i]/den_d[i] directly (clearing
# denominators, exactly as _check_mumford_identity_ring does) and reduce
# only against curve_gens (2 generators, degree 5 -- the same small
# ideal _check_mumford_identity_ring already uses cheaply). This checks
# exactly the same mathematical fact -- Fu_decoupled/Fv_decoupled are
# LINEAR in U_i/V_i (U_i's only appearance is `num_d[i] - U_i*den_d[i]`),
# so "U_i satisfies Fu_decoupled" and "U_i == num_d[i]/den_d[i] on the
# curve" are the same statement; there is no need to pay for a Groebner
# basis to confirm a substitution that is already exact by construction.
#
# Raises an ErrorException (matching _check_mumford_identity_ring's own
# convention) rather than returning a boolean, for the same reason: a
# failure here means the re-mapped num/den pairs (and hence
# Fu_decoupled/Fv_decoupled built from them) no longer describe a
# Mumford-consistent divisor for this sample.
function _check_mumford_identity_decoupled(u_num_d::Vector, u_den_d::Vector,
                                            v_num_d::Vector, v_den_d::Vector,
                                            F_POLY_ASC::Vector{Int}, R_dec,
                                            curve_gens::Vector;
                                            label::String = "")
    if isempty(u_num_d) || isempty(v_num_d)
        error("_check_mumford_identity_decoupled($label): empty u_num_d or v_num_d " *
              "-- nothing to check, caller should not have reached this point")
    end
    if length(u_num_d) != length(u_den_d) || length(v_num_d) != length(v_den_d)
        error("_check_mumford_identity_decoupled($label): mismatched num/den lengths " *
              "(len(u_num_d)=$(length(u_num_d)), len(u_den_d)=$(length(u_den_d)), " *
              "len(v_num_d)=$(length(v_num_d)), len(v_den_d)=$(length(v_den_d)))")
    end

    Rx, X = polynomial_ring(R_dec, "X_mumford_check_decoupled")

    # Same denominator-clearing construction as _check_mumford_identity_ring,
    # just against the re-mapped (R_dec) num/den pairs instead of R's.
    den_u_common = reduce(*, u_den_d)
    den_v_common = reduce(*, v_den_d)

    u_poly = sum(
        Rx(u_num_d[i]) * Rx(divexact(den_u_common, u_den_d[i])) * X^(i-1)
        for i in 1:length(u_num_d)
    )
    v_poly = sum(
        Rx(v_num_d[i]) * Rx(divexact(den_v_common, v_den_d[i])) * X^(i-1)
        for i in 1:length(v_num_d)
    )
    f_poly = sum(Rx(F_POLY_ASC[i+1]) * X^i for i in 0:(length(F_POLY_ASC)-1))

    # As in _check_mumford_identity_ring: u_poly's leading coefficient is
    # not (generically) a unit, so pseudorem (not mod) is the correct
    # primitive here.
    lhs = (v_poly^2 - f_poly * Rx(den_v_common)^2) * Rx(den_u_common)^2
    residual = pseudorem(lhs, u_poly)

    # The identity only needs to hold ON THE CURVE (modulo curve_gens),
    # not identically in the free ring R_dec -- same small ideal
    # _check_mumford_identity_ring already reduces against, deliberately
    # NOT widened with Fu_decoupled/Fv_decoupled (see docstring above).
    curve_ideal = ideal(R_dec, curve_gens)
    residual_coeffs_on_curve = iszero(residual) ? [] :
        [normal_form(coeff(residual, i), curve_ideal) for i in 0:degree(residual)]

    if !all(iszero, residual_coeffs_on_curve)
        error("_check_mumford_identity_decoupled($label): v_RS(X)^2 - f(X) is NOT " *
              "identically 0 mod u_RS(X) for the re-mapped (R_dec) num/den pairs, " *
              "even after reducing modulo the curve relations ($curve_gens). " *
              "Mumford condition violated by build_decoupled_system's re-mapping " *
              "step -- the re-mapped (u,v) pair no longer describes a " *
              "self-consistent divisor for this sample, so Fu_decoupled/" *
              "Fv_decoupled built from it would not either. nonzero X-coefficients " *
              "(on curve) = $(filter(!iszero, residual_coeffs_on_curve))")
    end

    return nothing
end

"""
    build_decoupled_system(s1, s2, mspec, tring, cfg)

Original lines 812-878. Re-maps each sample's num/den (elements of R)
into a new ring R_dec that additionally carries target variables
U0,U1,...  and V0,V1,..., then builds `U_i * den == num` (and `V_i`
likewise) equations per sample -- this does not change the underlying
variety, just phrases the coefficient-matching without cross-multiplying
both samples' variables together directly.

`cfg` (added alongside the new `_check_mumford_identity_decoupled` calls
below) supplies `F_POLY_ASC` -- not otherwise available from `tring` --
for the post-decoupling Mumford identity check on Fv_decoupled.
"""
function build_decoupled_system(s1::MappedSample, s2::MappedSample, mspec::MatchSpec,
                                 tring::TargetRing, cfg::CurveConfig)
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

    # Closes the gap between map_sample's _check_mumford_identity_ring
    # (checked on u_num/u_den/v_num/v_den BEFORE decoupling, in R) and
    # this function's own re-mapping of those pairs into R_dec: verify
    # the Mumford identity still holds on the re-mapped pairs, cheaply
    # (against curve_gens only -- see _check_mumford_identity_decoupled's
    # docstring for why this is run BEFORE Fu_decoupled/Fv_decoupled are
    # even built, rather than reducing against them). Sample 1 uses
    # curve_a1_d/curve_a2_d; sample 2 uses curve_b1_d/curve_b2_d.
    _check_mumford_identity_decoupled(u1_num_d, u1_den_d, v1_num_d, v1_den_d,
                                       cfg.F_POLY_ASC, R_dec,
                                       [curve_a1_d, curve_a2_d]; label = "sample 1, decoupled")
    _check_mumford_identity_decoupled(u2_num_d, u2_den_d, v2_num_d, v2_den_d,
                                       cfg.F_POLY_ASC, R_dec,
                                       [curve_b1_d, curve_b2_d]; label = "sample 2, decoupled")

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

    # Section 6.2 precondition: reject either spec before any tower/HC.jl
    # work is attempted if its divisor class D lies in the exceptional
    # locus (D ~ K_C, or the D=2P tangency) where sigma: C^(2) -> J fails
    # to be injective -- the one place the generic-finiteness argument
    # does not apply. Cheap (two mod-p operations per spec); raises with a
    # specific message telling you to regenerate rather than solve and
    # trust the generic argument where it doesn't hold.
    guard_sample_spec(spec1, cfg.p; label = "sample 1")
    guard_sample_spec(spec2, cfg.p; label = "sample 2")

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

    decoupled = build_decoupled_system(s1, s2, mspec, tring, cfg)

    per_layer = run_per_layer_degree_trace(res1, [tring.a1, tring.a2], [tring.wa1, tring.wa2], s1)
    norm_experiment = run_norm_before_vs_after_experiment(res1, fufv, tring)

    return (cfg = cfg, spec1 = spec1, spec2 = spec2, res1 = res1, res2 = res2,
            tring = tring, s1 = s1, s2 = s2, symmetry = symmetry, mspec = mspec,
            fufv = fufv, decoupled = decoupled, per_layer = per_layer,
            norm_experiment = norm_experiment)
end

end # module Elim2Main
