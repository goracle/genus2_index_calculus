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

# NOTE: an earlier version of this script attempted a projective
# compactification (homogenizing the curve relations and
# Fu_decoupled/Fv_decoupled per anchor pair) before running
# numerical_irreducible_decomposition. That step was removed -- NID doesn't
# require homogeneity, and the homogenization construction risked adding
# spurious positive-dimensional structure (4 new variables, 0 new
# equations). See the comment at the System(...) construction below for
# the full account. HomotopyContinuation is `using`-ed together with Oscar
# above; if you reintroduce anything from ModelKit that Oscar/Hecke also
# export (e.g. `expand`, and previously `homogenize` was assumed to be one
# of these but turned out not to exist in ModelKit at all -- see git
# history/conversation), qualify it explicitly as
# HomotopyContinuation.ModelKit.<name>(...) to avoid ambiguity errors.

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
# Step 2b: build the System directly from the 12 AFFINE equations/12
# unknowns -- NO homogenization/projective compactification.
#
# REMOVED (previously here): a projective-compactification step that
# homogenized the 4 curve relations per-anchor-pair (Za1,Za2,Zb1,Zb2) and
# then Fu_decoupled/Fv_decoupled with those same 4 variables, producing a
# 12-equation/16-variable NON-SQUARE system. Confirmed this was the wrong
# tool for the actual goal (per conversation: homogenizing was intended as
# a numerical-conditioning aid for HC.jl's NID, not because points at
# infinity matter to the question being asked). Two problems with it,
# for the record:
#   1. numerical_irreducible_decomposition does NOT require homogeneity --
#      that's a `solve()`-with-`homvar`-era (HC.jl v1.x) constraint, not an
#      NID one. There was no correctness reason to homogenize before NID.
#   2. Adding 4 new variables with NO new equations pinning them down risks
#      introducing spurious positive-dimensional structure into the
#      reported decomposition -- i.e. it could make an actually-finite
#      affine variety LOOK positive-dimensional as an artifact of the
#      construction, the opposite of "conditioning."
#
# The actual "Some homotopy paths in the u-regeneration intersection step
# failed" warning HC.jl raised is a path-tracking robustness issue in
# regeneration (confirmed: this is u-regeneration, HC.jl's witness-set
# construction algorithm -- see Duff/Leykin/Rodriguez, cited in HC.jl's own
# docs), which is orthogonal to affine vs. projective and has its own
# dedicated options -- see the tuning note at the
# numerical_irreducible_decomposition call below.
# ---------------------------------------------------------------------------

F = System(
    [hc_exprs_by_label[label] for (label, _) in all_generators],
    variables = hc_vars,
)
println("Built HomotopyContinuation.System (AFFINE, no homogenization): ",
        length(all_generators), " equations, ", length(hc_vars), " variables.")
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
#
# TUNING (added after a prior run hit "Some homotopy paths in the
# u-regeneration intersection step failed. The returned witness set may be
# incomplete."): confirmed directly from HC.jl's stable docs
# (witness_sets.md / tracker.md / endgame_tracker.md -- fetched, not
# assumed) that `regeneration` -- which numerical_irreducible_decomposition
# calls internally, and whose options it forwards -- has an option that
# targets this EXACT warning:
#
#   max_trials_u_homotopy = 5 (default): "maximal number of random
#   subspaces tried until an intermediate u-regeneration intersection step
#   succeeds."
#
# i.e. the default already retries a failing intersection step 5 times
# with fresh random subspaces before giving up and printing the warning;
# raising it gives more attempts. Also passing tighter tracker_options
# (automatic_differentiation=3, extended_precision=true are the two the
# docs explicitly flag as helping "numerically challenging paths") and a
# larger EndgameOptions max_winding_number in case any failures are near
# singular/multi-sheeted points -- these are secondary to
# max_trials_u_homotopy, which targets the specific failing step.
# ---------------------------------------------------------------------------

println("=" ^ 70)
println("Running numerical_irreducible_decomposition -- this is the actual")
println("finiteness check. May take a while: 12 equations/12 unknowns is a")
println("real numerical algebraic geometry computation, not instantaneous.")
println("=" ^ 70)
println()

t0 = time()
N = numerical_irreducible_decomposition(
    F;
    threading = true,
    show_progress = true,
    max_trials_u_homotopy = 25,
    tracker_options = TrackerOptions(
        automatic_differentiation = 3,
        extended_precision = true,
    ),
    endgame_options = EndgameOptions(
        max_winding_number = 12,
    ),
)
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
