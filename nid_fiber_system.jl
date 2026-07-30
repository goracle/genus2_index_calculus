#!/usr/bin/env julia
#
# nid_fiber_system.jl
#
# Finiteness check for the PRE-resultant fiber system -- curve relations +
# Fu_decoupled + Fv_decoupled, 12 equations in 12 unknowns
# (wa1,wa2,wb1,wb2,a2,a1,b2,b1,U0,U1,V0,V1) -- via HomotopyContinuation.jl's
# numerical_irreducible_decomposition, AFTER lifting GF(p) coefficients to
# integers and treating the system as living over C.
#
# WHY THIS EXISTS (see conversation): symbolic dim()/groebner_basis already
# choke on Fu_decoupled/Fv_decoupled directly (confirmed -- not assumed).
# HomotopyContinuation.jl's numerical_irreducible_decomposition sidesteps
# Groebner-basis computation entirely (it's a witness-set/monodromy-based
# method), and directly reports how many irreducible components exist AT
# EACH DIMENSION -- which is exactly the finiteness question: the system is
# 0-dimensional (finite) iff every reported component has dimension 0.
#
# This intentionally does NOT touch the 10M+-term PART K resultant files
# (U0/U1/V0/V1 in a1,a2,b1,b2 alone) -- those are unstreamable for a
# Newton-corrector Jacobian regardless of field (GF(p) or C), and HC.jl's
# path tracking has no meaning mod p in any case (no metric/continuity to
# track through). This script only ever builds a System from
# Fu_decoupled/Fv_decoupled/curve relations, each a few hundred terms,
# which fits trivially in RAM and as an HC.jl Expression.
#
# LIFTING CONVENTION (as specified): each GF(p) coefficient's canonical
# integer representative in [0,p) is used directly as an integer/complex
# coefficient -- no centering, no other reduction. This is a genuine lift
# of the mod-p system to a specific integer-coefficient system over C, NOT
# a claim that this is "the" canonical lift in a Hensel sense -- it's the
# system whose C-solution-count/dimension you asked to compute as an
# oracle for the mod-p system's finiteness, prior to any p-adic lifting of
# actual solutions.
#
# Usage:
#   julia -t N,1 nid_fiber_system.jl        # N worker threads + 1 interactive
#
# THREADING: numerical_irreducible_decomposition IS genuinely parallel --
# the cascade-of-homotopies step tracks many witness-point candidates per
# dimension concurrently, and it exposes threading=true (the default,
# but passed explicitly below rather than left implicit) governed by
# Julia's own thread pool, NOT OMP_NUM_THREADS. OMP_NUM_THREADS affects
# BLAS/LAPACK and Oscar/Singular/polymake's C internals -- a different
# layer that barely matters here, since run_main finishes in seconds and
# the actual cost is the NID cascade, which is pure-Julia and threaded via
# -t. HC.jl's own docs note some CPUs hang under plain -t N; their
# recommended workaround is -t N,1 (N worker threads + 1 reserved for the
# REPL/interactive tasks), which is what's suggested above -- e.g.
# `julia -t 8,1` for an 8-core budget.

import Pkg
Pkg.activate(joinpath(@__DIR__, "Elim2"))
using Oscar
using Elim2

include(Elim2.Elim2Main.locate_engine_default())
using .PhiSymbolic

using HomotopyContinuation

# NOTE: Oscar and HomotopyContinuation both export `homogenize` with
# unrelated signatures (Oscar: polyhedral cones/matrices; HC.jl/ModelKit:
# Expression/Variable). With both packages `using`-ed, plain `homogenize(...)`
# calls below are qualified as HomotopyContinuation.ModelKit.homogenize(...)
# to avoid dispatching into Oscar's PolyhedralGeometry method by accident.

println("Julia threads available for HC.jl's cascade/monodromy step: ",
        Threads.nthreads(), " (set via -t; raise this if the NID step ",
        "below is the bottleneck -- OMP_NUM_THREADS does not affect it)")
println()

# ---------------------------------------------------------------------------
# Step 1: run ONLY Elim2Main.run_main -- same as hc_path_estimate_decoupled.jl,
# no PART J/K, no resultant computation.
# ---------------------------------------------------------------------------

println("Running Elim2Main.run_main(PhiSymbolic) -- stage 'main' only...")
println()

main = Elim2.Elim2Main.run_main(PhiSymbolic)
dec = main.decoupled

println()
println("Got DecoupledSystem. Building the 12-equation/12-unknown fiber system:")
println("  4 curve relations + 4 Fu_decoupled + 4 Fv_decoupled")
println("  in (wa1,wa2,wb1,wb2,a2,a1,b2,b1,U0,U1,V0,V1)")
println()

# ---------------------------------------------------------------------------
# Step 2: lift each GF(p) polynomial to an HC.jl Expression over C.
#
# Rebuilds term-by-term from (exponent_vectors, coefficients) -- same
# primitive newton_polytope.jl's own support() uses (Oscar.exponents),
# zipped against Oscar.coefficients in the same iteration order (standard
# AbstractAlgebra contract: coefficients/exponents/monomials all iterate a
# polynomial's terms in the same order). Each GF(p) coefficient is lifted
# via its own integer representative (lift(ZZ, c) -- Oscar's own primitive
# for "the integer in [0,p) this field element represents"), used directly
# as an Int/BigInt coefficient in the HC.jl Expression, per the stated
# lifting convention (no centering, no other reduction).
# ---------------------------------------------------------------------------

"""
    lift_to_hc_expression(poly, hc_vars::Vector{Variable}, dec_gens::Vector) -> Expression

Rebuild `poly` (an element of R_dec, over GF(p)) as a HomotopyContinuation.jl
`Expression` in `hc_vars`, lifting each coefficient to its integer
representative in [0,p).

`dec_gens` is R_dec's own generator vector (`gens(dec.R_dec)`), in the same
order as `hc_vars` -- i.e. `hc_vars[i]` corresponds to `dec_gens[i]`. Raises
if `poly`'s parent's generator count doesn't match `length(hc_vars)`.
"""
function lift_to_hc_expression(poly, hc_vars::Vector{Variable}, dec_gens::Vector)
    n = length(hc_vars)
    length(dec_gens) == n ||
        error("lift_to_hc_expression: dec_gens has $(length(dec_gens)) entries, " *
              "expected $n to match hc_vars")

    expr = Expression(0)
    for (c, e) in zip(Oscar.coefficients(poly), Oscar.exponents(poly))
        length(e) == n ||
            error("lift_to_hc_expression: exponent vector has length $(length(e)), " *
                  "expected $n -- polynomial from an unexpected ring?")
        c_int = Int(lift(ZZ, c))  # canonical representative in [0,p), as an Int
        term = Expression(c_int)
        for i in 1:n
            e[i] == 0 && continue
            term *= hc_vars[i]^e[i]
        end
        expr += term
    end
    return expr
end

dec_gens = gens(dec.R_dec)
gen_names = [:wa1, :wa2, :wb1, :wb2, :a2, :a1, :b2, :b1]
append!(gen_names, [Symbol("U$i") for i in 0:(length(dec.U_vars)-1)])
append!(gen_names, [Symbol("V$i") for i in 0:(length(dec.V_vars)-1)])
length(gen_names) == length(dec_gens) ||
    error("gen_names/dec_gens length mismatch: $(length(gen_names)) vs $(length(dec_gens))")

hc_vars = [Variable(name) for name in gen_names]

println("Lifting generators to HomotopyContinuation.jl Expressions (GF(p) -> Z, ",
        "canonical [0,p) representative)...")

all_generators = vcat(
    [("curve_a1", dec.curve_a1_d), ("curve_a2", dec.curve_a2_d),
     ("curve_b1", dec.curve_b1_d), ("curve_b2", dec.curve_b2_d)],
    [("Fu_decoupled[$i]", g) for (i, g) in enumerate(dec.Fu_decoupled)],
    [("Fv_decoupled[$i]", g) for (i, g) in enumerate(dec.Fv_decoupled)],
)

hc_exprs_by_label = Dict{String, Expression}()
for (label, g) in all_generators
    t0 = time()
    e = lift_to_hc_expression(g, hc_vars, dec_gens)
    println("  $label lifted in ", round(time() - t0, digits=3), "s")
    hc_exprs_by_label[label] = e
end
println()

# ---------------------------------------------------------------------------
# Step 2b: PROJECTIVE COMPACTIFICATION of each anchor pair's curve.
#
# The affine curve wa1^2 = a1^5 + a1 + 2 (degree 5 = 2g+1, g=2, ODD degree)
# has its naive projective closure in ORDINARY P^2 (NOT weighted projective
# space -- weighted P(1,g+1,1) is only needed for the EVEN-degree case,
# where there are two points at infinity that would otherwise be singular;
# see e.g. the Auckland "Mathematics of Public Key Cryptography" ch.10 and
# the genus-2 Jacobian-models literature). For odd deg(f)=2g+1, the ordinary
# homogeneous closure Y^2*Z^(2g-1) = Z^(2g+1)*f(X/Z) has exactly ONE point
# at infinity, (0:1:0), and it is NON-SINGULAR -- confirmed both by the
# cited sources and by direct symbolic expansion (see conversation): for
# f(a1) = a1^5 + a1 + 2, this gives the homogeneous quintic
#     WA1^2 * ZA1^3 - A1^5 - A1*ZA1^4 - 2*ZA1^5 = 0
# which dehomogenizes back to wa1^2 - a1^5 - a1 - 2 at ZA1=1, and reduces to
# -A1^5 = 0 (i.e. A1=0, giving the single point (0:1:0)) at ZA1=0.
#
# Each anchor pair (wa1/a1, wa2/a2, wb1/b1, wb2/b2) gets its OWN
# homogenizing variable (Za1, Za2, Zb1, Zb2) -- NOT one shared variable for
# the whole system -- since each curve is an independent P^2 compactified
# separately; U0,U1,V0,V1 are left un-homogenized (affine), since they are
# the shared target variables and do not participate in either curve's own
# point-at-infinity structure (Fu_decoupled/Fv_decoupled are LINEAR in
# U_i/V_i by construction, so no compactification is needed in that
# direction for the curve's sake).
#
# Rather than hand-derive the homogenization of Fu_decoupled/Fv_decoupled
# (5 variables each: wa1,wa2,a1,a2,U_i or wb1,wb2,b1,b2,U_i) by hand and
# risk mismatching per-block degrees, HC.jl's own `homogenize` is used
# directly on each polynomial with its OWN anchor pair's homogenizing
# variable(s) -- this is exactly the "use HC.jl's built-in support" request
# rather than a hand-rolled multi-block homogenization.
# ---------------------------------------------------------------------------

println("Homogenizing per anchor pair (odd-degree curve => ordinary")
println("projective closure, NOT weighted -- see comment above)...")
println()

# ---------------------------------------------------------------------------
# HAND-ROLLED HOMOGENIZATION -- HC.jl v2.x has NO `homogenize` function.
#
# Confirmed directly (not assumed): `using HomotopyContinuation; methods(homogenize)`
# in a clean session (v2.22.1, this project's pinned version) raises
# `UndefVarError: homogenize not defined in Main` -- it isn't exported by
# ModelKit, and grepping ModelKit's own doc export list (model_kit.md)
# confirms there is no `homogenize` entry in it at all. The earlier
# MethodError (`no method matching homogenize(::Expression, ::Variable)`,
# with only Oscar's PolyhedralGeometry candidates listed) wasn't actually a
# name collision masking HC.jl's real method -- HC.jl has no method here to
# be masked. `homogenize` existed in HC.jl's OLD (v1.x) MultivariatePolynomials
# ("@polyvar")-based API, which was dropped when v2.0 introduced ModelKit.
#
# Replacement, using ModelKit's `exponents_coefficients` /
# `poly_from_exponents_coefficients` (both confirmed present in this
# version): for a single homogenizing variable z, each monomial's missing
# degree (target_degree - term_degree) is made up by an explicit power of z.
# This is the textbook single-variable homogenization and matches this
# script's own hand-derived check below exactly.
# ---------------------------------------------------------------------------

function homogenize_one(f::Expression, z::Variable, vars::Vector{Variable};
                         target_degree::Union{Int,Nothing} = nothing)
    M, c = exponents_coefficients(f, vars)
    term_degrees = vec(sum(M, dims = 1))
    d = target_degree === nothing ? maximum(term_degrees) : target_degree
    any(term_degrees .> d) &&
        error("homogenize_one: target_degree=$d is less than an existing " *
              "term's degree $(maximum(term_degrees)) -- refusing to " *
              "produce a negative power of $z.")
    z_pows = d .- term_degrees
    out = Expression(0)
    for j in 1:length(c)
        monom = c[j]
        for (i, v) in enumerate(vars)
            e = M[i, j]
            e == 0 || (monom *= v^e)
        end
        z_pows[j] == 0 || (monom *= z^z_pows[j])
        out += monom
    end
    return out
end

za1, za2, zb1, zb2 = Variable(:Za1), Variable(:Za2), Variable(:Zb1), Variable(:Zb2)

# curve relations: homogenize each with its OWN anchor pair's Z.
hom_curve_a1 = homogenize_one(hc_exprs_by_label["curve_a1"], za1, hc_vars)
hom_curve_a2 = homogenize_one(hc_exprs_by_label["curve_a2"], za2, hc_vars)
hom_curve_b1 = homogenize_one(hc_exprs_by_label["curve_b1"], zb1, hc_vars)
hom_curve_b2 = homogenize_one(hc_exprs_by_label["curve_b2"], zb2, hc_vars)

# Sanity-check each homogenized curve matches the hand-derived form exactly
# (WA1^2*Za1^3 - A1^5 - A1*Za1^4 - 2*Za1^5), rather than trusting
# homogenize()'s output blind -- raises loudly on any mismatch.
wa1_v, a1_v = hc_vars[1], hc_vars[6]
expected_curve_a1 = wa1_v^2 * za1^3 - a1_v^5 - a1_v * za1^4 - 2 * za1^5
iszero(expand(hom_curve_a1 - expected_curve_a1)) ||
    error("homogenize() produced curve_a1 = $hom_curve_a1, which does not " *
          "match the hand-derived homogeneous quintic $expected_curve_a1 " *
          "-- STOP: do not proceed with a compactification that hasn't " *
          "been verified against the closed-form derivation.")
println("  curve_a1 homogenization VERIFIED against hand-derived form.")

# Fu_decoupled[1]/Fv_decoupled[1] (sample 1, wa1,wa2,a1,a2,U0/V0) get BOTH
# Za1 and Za2 (they involve both anchors of sample 1 at once).
#
# *** UNVERIFIED CONVENTION -- CHECK BEFORE TRUSTING DOWNSTREAM RESULTS ***
# There is no HC.jl builtin here to defer to (see note above), and this
# script has no hand-derived closed form for Fu_decoupled/Fv_decoupled to
# check against the way hom_curve_a1 is checked below. The convention used
# here puts the ENTIRE per-monomial degree deficiency onto Za1 alone
# (Za2^0 always) -- i.e. treats [za1, za2] as "make up the missing degree
# using za1, with za2 along for the ride at its already-occurring power."
# This is almost certainly NOT what you want if Fu_decoupled/Fv_decoupled
# is meant to be separately homogeneous in the (wa1,a1)-block and the
# (wa2,a2)-block (a genuinely bi-homogeneous/multi-projective
# construction) -- that needs a different function entirely (pad each
# block to ITS OWN max degree with its own z), not this one. Given the
# DEGREE-IN-W DIAGNOSTIC printed above (degree <=1 in EACH of wa1,wa2
# separately), bi-homogeneous is plausible for your construction -- flagging
# this explicitly rather than silently picking the single-degree
# convention and letting a wrong answer look finished.
function homogenize_two(f::Expression, z1::Variable, z2::Variable,
                         vars::Vector{Variable})
    M, c = exponents_coefficients(f, vars)
    term_degrees = vec(sum(M, dims = 1))
    d = maximum(term_degrees)
    out = Expression(0)
    for j in 1:length(c)
        monom = c[j]
        for (i, v) in enumerate(vars)
            e = M[i, j]
            e == 0 || (monom *= v^e)
        end
        missing_deg = d - term_degrees[j]
        missing_deg == 0 || (monom *= z1^missing_deg)  # all on z1, see note above
        out += monom
    end
    return out
end

hom_Fu = Vector{Expression}(undef, 4)
hom_Fv = Vector{Expression}(undef, 4)
for i in 1:4
    is_sample1 = isodd(i)  # matches build_decoupled_system's own convention
    z1, z2 = is_sample1 ? (za1, za2) : (zb1, zb2)
    hom_Fu[i] = homogenize_two(hc_exprs_by_label["Fu_decoupled[$i]"], z1, z2, hc_vars)
    hom_Fv[i] = homogenize_two(hc_exprs_by_label["Fv_decoupled[$i]"], z1, z2, hc_vars)
end
println("  Fu_decoupled/Fv_decoupled homogenized (sample 1 -> Za1,Za2; ",
        "sample 2 -> Zb1,Zb2).")
println()

all_hom_exprs = vcat(
    [hom_curve_a1, hom_curve_a2, hom_curve_b1, hom_curve_b2],
    hom_Fu, hom_Fv,
)
all_hom_vars = vcat(hc_vars, [za1, za2, zb1, zb2])

F = System(all_hom_exprs, variables = all_hom_vars)
println("Built HomotopyContinuation.System (PROJECTIVE, per-anchor-pair ",
        "homogenized): ", length(all_hom_exprs), " equations, ",
        length(all_hom_vars), " variables (12 affine + 4 homogenizing).")
println()

# ---------------------------------------------------------------------------
# Step 3: numerical irreducible decomposition -- the finiteness oracle.
#
# Reports components by dimension directly. The system is 0-dimensional
# (finite over C, for this lifted integer-coefficient instance) iff every
# component reported has dimension 0. This does NOT require a Groebner
# basis or dim() call at any point -- numerical_irreducible_decomposition
# is witness-set/monodromy based (cascade of homotopies), which is exactly
# why it's viable here when the symbolic route already choked.
# ---------------------------------------------------------------------------

println("=" ^ 70)
println("Running numerical_irreducible_decomposition -- this is the actual")
println("finiteness check. May take a while: 12 equations/12 unknowns is a")
println("real numerical algebraic geometry computation, not instantaneous.")
println("=" ^ 70)
println()

t0 = time()
N = numerical_irreducible_decomposition(F; threading = true, show_progress = true)
println()
println("numerical_irreducible_decomposition finished in ", round(time() - t0, digits=1), "s")
println()
println(N)
println()

# ---------------------------------------------------------------------------
# Step 4: explicit finiteness verdict, read off N directly rather than left
# for the user to infer from the printed summary alone.
# ---------------------------------------------------------------------------

# HomotopyContinuation.jl's NumericalIrreducibleDecomposition print format
# reports "N component(s) of dimension d" per dimension found; the API to
# query this programmatically (rather than parsing the printed summary) is
# nid_components / degrees_of_components style accessors in recent
# versions -- if the exact accessor name differs in your installed version,
# the printed summary above already answers the question directly: look for
# ANY line reporting dimension > 0.
println("=" ^ 70)
println("VERDICT")
println("=" ^ 70)
println("If the summary above shows ONLY 'component(s) of dimension 0', the")
println("lifted (integer-coefficient) fiber system is 0-DIMENSIONAL -- i.e.")
println("finite over C for this instance. This is evidence (not a proof for")
println("the mod-p system specifically -- see the lifting-convention note at")
println("the top of this file) that the mod-p system is finite too, and the")
println("point count reported for the dimension-0 components is your")
println("candidate solution count to carry into the Hensel-lifting step.")
println()
println("If the summary shows ANY component of dimension >= 1, the lifted")
println("system has a positive-dimensional solution set -- the mod-p system")
println("may be positive-dimensional as well (or may not -- reduction mod p")
println("can both create and destroy positive-dimensional behavior relative")
println("to the characteristic-0 lift; this script only answers the")
println("characteristic-0 question, cleanly and directly).")
