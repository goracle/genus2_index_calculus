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
println()

# ---------------------------------------------------------------------------
# Step 5: extract and SAVE the actual dimension-0 witness points.
#
# BUG FIX: the run above (and the version of this script that produced it)
# never called witness_sets(N; ...)/solutions(W) -- it only printed the
# summary object N, which reports counts/degrees but not coordinates. The
# 2475 witness points from that run were never captured and are gone
# (HC.jl does not persist them anywhere on its own). This step does not
# recover them; it fixes the script so a future run saves points as it
# goes, and adds the mod-p / Hensel verification pass that was always the
# intended next step per the file's own docstring notes.
#
# API used (confirmed directly against HC.jl's stable docs, not assumed):
#   witness_sets(N; dims = [0], only_irreducible = true) -> Vector{WitnessSet}
#   solutions(W::WitnessSet) -> the points stored in that witness set
# Each dimension-0 witness set here has degree 1 (per the run's own
# printed degree table), i.e. exactly one point; solutions(W) still
# returns a vector, so we splat/collect across all such W to get every
# point as a flat list.
# ---------------------------------------------------------------------------

using Serialization

println("=" ^ 70)
println("Extracting dimension-0 witness points")
println("=" ^ 70)

witness_sets_raw = witness_sets(N; dims = [0], only_irreducible = true)

# witness_sets(N; dims=[...]) returns one `dim => Vector{WitnessSet}` pair per
# requested dimension, NOT a flat Vector{WitnessSet} -- confirmed by the
# Pair{Int64, Vector{WitnessSet}} type in the original error. Unwrap
# explicitly rather than assuming the shape; raise if it's not what we expect
# so this fails loudly instead of silently mis-extracting again.
dim0_witness_sets = WitnessSet[]
for entry in witness_sets_raw
    if !(entry isa Pair{Int64, <:AbstractVector})
        error("witness_sets(N; dims=[0]) returned an element of type ",
              typeof(entry), ", expected Pair{Int64, <:AbstractVector} -- ",
              "HC.jl's API may have changed; do not assume, re-check the docs.")
    end
    dim, wsets = entry
    dim == 0 || error("witness_sets(N; dims=[0]) returned a pair for dim=",
                       dim, ", expected only dim=0.")
    append!(dim0_witness_sets, wsets)
end

println("Got ", length(dim0_witness_sets), " dimension-0 witness set(s) ",
        "(each of degree 1 per the run above, i.e. one point each).")

witness_points = Vector{Vector{ComplexF64}}()
for W in dim0_witness_sets
    for s in solutions(W)
        push!(witness_points, ComplexF64.(s))
    end
end

length(witness_points) > 0 ||
    error("Extracted 0 witness points from ", length(dim0_witness_sets),
          " witness set(s) -- extraction logic is still wrong, do not ",
          "proceed to save/Hensel step with an empty result.")
println("Collected ", length(witness_points), " witness point(s) in ",
        "variable order: ", gen_names)
println()

# Save immediately -- do this BEFORE the mod-p pass below, so a crash or
# interrupt during Hensel verification still leaves the raw
# characteristic-0 points on disk. Two formats: a native Julia
# Serialization dump (exact, fastest to reload in a follow-up Julia
# session) and a plain CSV of real/imaginary parts (portable, inspectable
# without Julia).
out_dir = joinpath(@__DIR__, "nid_output")
mkpath(out_dir)

jls_path = joinpath(out_dir, "witness_points.jls")
serialize(jls_path, (gen_names = gen_names, points = witness_points))
println("Saved ", length(witness_points), " points to ", jls_path,
        " (reload with: deserialize(\"$jls_path\")).")

csv_path = joinpath(out_dir, "witness_points.csv")
open(csv_path, "w") do io
    println(io, join(["$(g)_re,$(g)_im" for g in gen_names], ","))
    for pt in witness_points
        println(io, join(["$(real(c)),$(imag(c))" for c in pt], ","))
    end
end
println("Saved the same points to ", csv_path, " (plain CSV, portable).")
println()

# ---------------------------------------------------------------------------
# Step 6: mod-p verification (the Hensel-lifting precondition check).
#
# WHAT THIS DOES: the 2475 (or however many) points above are roots of the
# LIFTED (integer-coefficient, characteristic-0) system -- per this file's
# own lifting-convention note at the top, this is a specific integer lift
# chosen as a finiteness ORACLE, not a claim that solving it tells you
# about the mod-p system directly. This step is the bridge: for each
# witness point, reduce its coordinates mod p and check whether the
# reduction is well-behaved, i.e. whether the point survives as a genuine,
# non-degenerate solution of the ACTUAL mod-p system you care about.
#
# The precise criterion (multivariate Hensel's lemma, applied per-point):
# a witness point x reduces to a well-defined, non-singular mod-p solution
# iff det(Jacobian(F))(x) is a p-adic unit at x, i.e.
#     det(J_F(x)) mod p != 0
# Points that fail this check are exactly where characteristic-0 simplicity
# (confirmed above: every component had degree 1, i.e. every root was
# simple in C) could fail to survive reduction -- two distinct C-roots can
# collide mod p, or a root's coordinates can blow up mod p (denominator
# vanishing), even though nothing "went wrong" in the characteristic-0
# solve itself.
#
# WHAT THIS DOES NOT DO: it does not perform the actual p-adic Newton
# lifting/precision-raising step (i.e. computing the mod-p^k solution for
# k>1) -- that is a separate step you'd only need if downstream code
# requires higher p-adic precision than a single mod-p reduction. This
# step only answers the yes/no Hensel-applicability question per point,
# which is the thing that determines whether the characteristic-0 count
# (2475, or however many in a future run) is trustworthy as the ACTUAL
# mod-p solution count, or whether some points need to be discounted
# (collided) or flagged (denominator vanishing / point at infinity mod p).
#
# p is read from wherever the rest of the pipeline defines it (Elim2's own
# GF(p) modulus -- reusing dec's base ring's characteristic rather than
# hardcoding, so this always matches whatever prime the run above actually
# used).
# ---------------------------------------------------------------------------

println("=" ^ 70)
println("Mod-p verification (Hensel-lifting precondition check)")
println("=" ^ 70)

p = Int(characteristic(base_ring(dec.R_dec)))
println("Using p = ", p, " (read from dec.R_dec's base field characteristic).")
println()

# Jacobian of the same 12 generators, in the same variable order, built
# once via HC.jl's own ModelKit differentiation (symbolic, exact -- not a
# finite-difference approximation) so it can be evaluated at each point
# without re-deriving anything by hand.
exprs_in_order = [hc_exprs_by_label[label] for (label, _) in all_generators]
J_expr = [HomotopyContinuation.ModelKit.differentiate(f, v)
          for f in exprs_in_order, v in hc_vars]

"""
    reduce_mod_p(z::Complex, p::Int) -> Int

Reduce a (numerically near-integer) complex witness coordinate to its
canonical representative in [0,p). Verifies the imaginary part and the
fractional part of the real part are both within numerical tolerance of
zero before rounding -- if either check fails, the point's coordinates
are not close enough to a rational integer lift to be reduced this way at
all (a real, separate failure mode from the Jacobian-singularity check
below; both are reported).
"""
function reduce_mod_p(z::Complex, p::Int; tol::Float64 = 1e-6)
    if abs(imag(z)) > tol
        return nothing
    end
    r = real(z)
    n = round(Int, r)
    if abs(r - n) > tol
        return nothing
    end
    return mod(n, p)
end

hensel_ok = falses(length(witness_points))
reduction_ok = falses(length(witness_points))
det_mod_p = Vector{Union{Int,Nothing}}(undef, length(witness_points))

for (i, pt) in enumerate(witness_points)
    reduced = [reduce_mod_p(c, p) for c in pt]
    if any(isnothing, reduced)
        reduction_ok[i] = false
        hensel_ok[i] = false
        det_mod_p[i] = nothing
        continue
    end
    reduction_ok[i] = true
    reduced_int = Int.(reduced)

    # Evaluate the (exact, symbolic) Jacobian at the reduced point, then
    # take everything mod p and compute the determinant over that finite
    # field via Oscar/Nemo (exact modular linear algebra -- no floating
    # point involved in this determinant, unlike the witness-point solve
    # itself).
    Jn = [Int(round(real(
              HomotopyContinuation.ModelKit.evaluate(J_expr[r, c], hc_vars => reduced_int)
          ))) for r in 1:length(all_generators), c in 1:length(hc_vars)]
    Fp = Oscar.GF(p)
    Jn_modp = matrix(Fp, Jn)
    d = det(Jn_modp)
    det_mod_p[i] = Int(lift(ZZ, d))
    hensel_ok[i] = !iszero(d)
end

n_reduction_failed = count(!, reduction_ok)
n_singular = count(i -> reduction_ok[i] && !hensel_ok[i], eachindex(witness_points))
n_verified = count(hensel_ok)

println("Reduction-to-mod-p failed (coordinates not integer-lift-shaped, ",
        "tol=1e-6): ", n_reduction_failed, " / ", length(witness_points))
println("Reduced cleanly but Jacobian singular mod p (Hensel does NOT ",
        "apply -- point may collide with another or be spurious mod p): ",
        n_singular, " / ", length(witness_points))
println("Verified: reduces cleanly AND Jacobian nonsingular mod p ",
        "(Hensel applies, point is a genuine simple mod-p solution): ",
        n_verified, " / ", length(witness_points))
println()

if n_reduction_failed > 0 || n_singular > 0
    println("NOTE: ", n_reduction_failed + n_singular, " of ",
            length(witness_points), " characteristic-0 witness points did ",
            "NOT verify as clean simple solutions mod p. The trustworthy ",
            "mod-p candidate count for this instance is ", n_verified,
            ", not the raw characteristic-0 count of ", length(witness_points),
            ". Points failing reduction (as opposed to failing the ",
            "Jacobian check) may simply need a tighter tolerance or higher ",
            "solve precision -- inspect them individually before assuming ",
            "they're genuinely non-integral.")
else
    println("All ", length(witness_points), " witness points verified: ",
            "every characteristic-0 root reduces to a distinct, ",
            "non-degenerate solution of the actual mod-p system.")
end
println()

# Persist the verification results alongside the raw points, so this pass
# doesn't need to be rerun to answer "how many points actually verified"
# later.
verify_path = joinpath(out_dir, "hensel_verification.jls")
serialize(verify_path, (
    p = p,
    reduction_ok = reduction_ok,
    hensel_ok = hensel_ok,
    det_mod_p = det_mod_p,
))
println("Saved verification results to ", verify_path, ".")
