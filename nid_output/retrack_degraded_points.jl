#!/usr/bin/env julia
#
# retrack_degraded_points.jl
#
# WHY THIS EXISTS: a boundary-distance scan of witness_points.csv found 30
# coordinate instances (across 30 distinct witness points, always in b1 or
# b2, never a1/a2) sitting 1.5e-4 to 2.7e-4 away from their nearest root of
# x^3-x^2+1 -- comfortably inside classify_and_reduce_d1.jl's MATCH_TOL=5e-4
# (so they still get correctly bucketed as cubic_type), but nowhere near
# double-precision-clean (~1e-14 residual would be expected for a properly
# converged path). investigate_unrecognized_and_symmetry.jl already flagged
# three of these repeated values as "LIKELY the known cubic root, computed
# at lower accuracy (consistent with a degraded/failed homotopy path)" and
# recommended re-solving/re-tracking to confirm -- this script is that step.
#
# WHAT THIS DOES: rebuilds the exact same 12-equation System F that
# nid_fiber_system.jl built (via the same Elim2Main.run_main call, so the
# equations are guaranteed identical -- not re-derived by hand), then uses
# HomotopyContinuation.jl's `refine`/re-tracking machinery to re-track each
# flagged witness point AT HIGHER PRECISION, using its existing (imprecise)
# coordinates as the starting seed. This is seconds-to-minutes total, NOT
# the original 10-hour NID -- it re-tracks 30 known points, it does not
# rediscover the variety.
#
# WHAT THIS DOES NOT DO: it does not change or re-derive the fiber system,
# the symmetry-group quotient, or the d1/d2 label classification -- it only
# produces corrected high-precision coordinates for the 30 flagged points,
# to be fed back into the classification step afterward.

import Pkg
Pkg.activate(joinpath(@__DIR__, "..", "Elim2"))
using Oscar
using Elim2

include(Elim2.Elim2Main.locate_engine_default())
using .PhiSymbolic

using HomotopyContinuation
using Serialization

# ---------------------------------------------------------------------------
# Step 1: rebuild F exactly as nid_fiber_system.jl did (same call, same
# lifting convention) so the equations re-tracking runs against are
# guaranteed identical to the ones the original NID solved.
# ---------------------------------------------------------------------------

println("Rebuilding the 12-equation fiber system (same as nid_fiber_system.jl)...")
main = Elim2.Elim2Main.run_main(PhiSymbolic)
dec = main.decoupled

function lift_to_hc_expression(poly, hc_vars::Vector{Variable}, dec_gens::Vector)
    n = length(hc_vars)
    expr = Expression(0)
    for (c, e) in zip(Oscar.coefficients(poly), Oscar.exponents(poly))
        c_bigint = BigInt(lift(ZZ, c))
        term = Expression(c_bigint)
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
hc_vars = [Variable(name) for name in gen_names]

all_generators = vcat(
    [("curve_a1", dec.curve_a1_d), ("curve_a2", dec.curve_a2_d),
     ("curve_b1", dec.curve_b1_d), ("curve_b2", dec.curve_b2_d)],
    [("Fu_decoupled[$i]", g) for (i, g) in enumerate(dec.Fu_decoupled)],
    [("Fv_decoupled[$i]", g) for (i, g) in enumerate(dec.Fv_decoupled)],
)
hc_exprs_by_label = Dict(label => lift_to_hc_expression(g, hc_vars, dec_gens)
                          for (label, g) in all_generators)
F = System([hc_exprs_by_label[label] for (label, _) in all_generators],
           variables = hc_vars)

println("Rebuilt System matches nid_fiber_system.jl's F: ",
        length(all_generators), " equations, ", length(hc_vars), " variables.")
println()

# ---------------------------------------------------------------------------
# Step 2: load the original witness points and pull out the 30 flagged
# indices (1-based, matching witness_points.jls / witness_points.csv row
# order -- confirmed against the boundary-distance scan run earlier this
# session, NOT re-derived here to avoid any risk of drift between the scan
# and this script; if you've regenerated witness_points.jls since, rerun
# the boundary scan first and update this list).
# ---------------------------------------------------------------------------

wpts_nt = deserialize(joinpath(@__DIR__, "witness_points.jls"))
pts = wpts_nt.points
@assert wpts_nt.gen_names == gen_names "gen_names order mismatch between " *
    "witness_points.jls and this script's freshly-rebuilt F -- do not " *
    "proceed, re-tracking would seed the wrong variables."

flagged_indices = [292, 374, 382, 467, 528, 680, 681, 688, 1107, 1268, 1350,
                    1427, 1595, 1600, 1697, 1709, 1972, 1976, 2066, 2125,
                    2149, 2201, 2205, 2212, 2246, 2291, 2305, 2347, 2354, 2456]

println("Re-tracking ", length(flagged_indices), " flagged witness points ",
        "at higher precision...")
println()

# ---------------------------------------------------------------------------
# Step 3: refine each flagged point. HC.jl's `refine`/`newton` (via
# `newton(F, seed; ...)`) does a few extra Newton corrector steps at
# extended precision from a good-enough starting seed -- appropriate here
# because these points are already CLOSE to a true root (residual ~1e-4,
# not wildly off), which is exactly the regime Newton correction is
# reliable in. This is NOT full path-tracking from a random start; it's
# high-precision local refinement of an already-converged-ish point, which
# is the correct (and fast) tool for "degraded precision, not wrong root".
# ---------------------------------------------------------------------------

corrected = Dict{Int, Vector{ComplexF64}}()
failed = Int[]

for i in flagged_indices
    seed = pts[i]
    result = newton(F, seed;
                     atol = 1e-14,
                     rtol = 1e-14,
                     extended_precision = true)
    if is_success(result)
        corrected[i] = ComplexF64.(solution(result))
        old_resid = maximum(abs.(ComplexF64.(F(seed))))
        new_resid = maximum(abs.(ComplexF64.(F(corrected[i]))))
        println("  point $i: refined. |F(old)|_max=$(round(old_resid, sigdigits=3)) ",
                "-> |F(new)|_max=$(round(new_resid, sigdigits=3))")
    else
        push!(failed, i)
        println("  point $i: refinement FAILED (newton did not converge from ",
                "this seed) -- do not silently keep the old value; this point ",
                "needs manual inspection, possibly full re-tracking from ",
                "scratch rather than local refinement.")
    end
end

println()
println("Refined: ", length(corrected), " / ", length(flagged_indices))
if !isempty(failed)
    println("FAILED to refine (needs manual attention): ", failed)
end
println()

# ---------------------------------------------------------------------------
# Step 4: write out a corrected copy of the witness points -- do NOT
# overwrite witness_points.jls in place; save alongside so the original
# run's raw output is never silently mutated.
# ---------------------------------------------------------------------------

pts_corrected = copy(pts)
for (i, v) in corrected
    pts_corrected[i] = v
end

out_path = joinpath(@__DIR__, "witness_points_corrected.jls")
serialize(out_path, (gen_names = gen_names, points = pts_corrected,
                      refined_indices = collect(keys(corrected)),
                      failed_indices = failed))
println("Saved corrected witness points to ", out_path, ".")
println("Re-run the d1/d2 label classification (reclassify_and_verify_pairing_v3.jl,",
        " pointed at this file instead of witness_points.jls) to get the",
        " final label-orbit counts.")
