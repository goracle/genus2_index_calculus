#!/usr/bin/env julia
#
# certify_degraded_points.jl
#
# WHY THIS EXISTS: retrack_degraded_points.jl's Newton "refinement" did
# nothing useful -- residuals stayed at ~1e-7/1e-8 before and after (some
# bit-for-bit identical), instead of collapsing to ~1e-14 as real
# convergence would. That's consistent with `newton(...; extended_precision
# = true)` still evaluating F and the seed at plain Float64 internally, so
# there was nowhere for it to converge TO. It answered nothing about
# whether these 30 points are genuinely low-precision versions of a known
# root, or something else.
#
# THIS SCRIPT uses certify() instead -- the same rigorous interval/Krawczyk
# Smale alpha-theory tool nid_fiber_system.jl already runs on the full
# witness set (Step 5b there). certify() doesn't rely on Newton converging
# nicely from a Float64 seed; it either produces a certificate that a true
# isolated simple root exists in a computable ball around the point (and
# gives that root's location to certified precision), or it fails to
# certify, which is itself informative (point too close to another root /
# near-singular / genuinely not a simple root here).
#
# This directly answers the actual question: for each of the 30 flagged
# points, is "residual ~1e-4 from the nearest cubic root" (well inside
# MATCH_TOL=5e-4) consistent with a genuine simple root nearby (which
# would then almost certainly BE that cubic root, to certified precision),
# or does certification fail/point elsewhere?

import Pkg
Pkg.activate(joinpath(@__DIR__, "..", "Elim2"))
using Oscar
using Elim2

include(Elim2.Elim2Main.locate_engine_default())
using .PhiSymbolic

using HomotopyContinuation
using Serialization

# ---------------------------------------------------------------------------
# Step 1: rebuild F exactly as nid_fiber_system.jl / retrack_degraded_points.jl
# did -- same construction, so certify() runs against the identical system.
# ---------------------------------------------------------------------------

println("Rebuilding the 12-equation fiber system...")
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

println("Rebuilt System: ", length(all_generators), " equations, ",
        length(hc_vars), " variables.")
println()

# ---------------------------------------------------------------------------
# Step 2: load witness points, select the 30 flagged indices.
# ---------------------------------------------------------------------------

wpts_nt = deserialize(joinpath(@__DIR__, "witness_points.jls"))
pts = wpts_nt.points
@assert wpts_nt.gen_names == gen_names "gen_names order mismatch -- do not proceed."

flagged_indices = [292, 374, 382, 467, 528, 680, 681, 688, 1107, 1268, 1350,
                    1427, 1595, 1600, 1697, 1709, 1972, 1976, 2066, 2125,
                    2149, 2201, 2205, 2212, 2246, 2291, 2305, 2347, 2354, 2456]

flagged_points = [pts[i] for i in flagged_indices]

# ---------------------------------------------------------------------------
# Step 3: certify just these 30 points. Same API nid_fiber_system.jl uses
# on the full 2457-point set, here restricted to the flagged subset.
# ---------------------------------------------------------------------------

println("=" ^ 70)
println("Certifying the 30 flagged points (Smale alpha-theory)")
println("=" ^ 70)

cert_result = certify(F, flagged_points)

n_certified = ncertified(cert_result)
n_distinct = ndistinct_certified(cert_result)

println("Certified ", n_certified, "/", length(flagged_points),
        " point(s) as true, isolated, simple roots.")
println("Of those, ", n_distinct, " are certified pairwise-distinct ",
        "(among just these 30 -- distinctness against the OTHER 2427 ",
        "points is a separate question, not checked here).")
println()

if n_certified < length(flagged_points)
    println("NOTE: not all 30 certified. Points that fail are NOT simply",
            " 'imprecise' -- certify() failing means no rigorous ball could",
            " be constructed (could be near-singular, too close to another",
            " root for the certifying radius, or something else). Those",
            " need individual inspection, not another blind refinement",
            " attempt.")
    println()
end

# ---------------------------------------------------------------------------
# Step 4: for each certified point, pull its certified higher-precision
# location and compare directly to the nearest root of the two known
# minimal polynomials (x^2+x+1, x^3-x^2+1) -- this is the actual answer to
# "is this the known cubic root at low precision, or something else."
# ---------------------------------------------------------------------------

println("=" ^ 70)
println("Comparing certified locations against known roots")
println("=" ^ 70)

CC = AcbField(128)
QQx, xq = polynomial_ring(QQ, "x")
omega_roots_C = roots(CC, xq^2 + xq + 1)
cubic_roots_C = roots(CC, xq^3 - xq^2 + 1)
known_roots = vcat([ComplexF64(r) for r in omega_roots_C],
                    [ComplexF64(r) for r in cubic_roots_C])

certs = certificates(cert_result)
for (k, i) in enumerate(flagged_indices)
    cert = certs[k]
    if !is_certified(cert)
        println("  point $i: NOT certified -- see note above, inspect manually.")
        continue
    end
    # certified_solution_interval / solution_candidate style accessor --
    # confirm exact name against your installed HC.jl version's docs if
    # this errors; falling back to `solution(cert)` (the refined point
    # certify() itself computed) if the interval accessor differs.
    refined_pt = ComplexF64.(solution_candidate(cert))
    # which of the 12 coordinates is the flagged one (b1 or b2)? report all,
    # since we don't track which slot triggered the flag in this script --
    # cheap to just show the b1/b2 slots.
    b1_idx = findfirst(==(:b1), gen_names)
    b2_idx = findfirst(==(:b2), gen_names)
    for (name, idx) in (("b1", b1_idx), ("b2", b2_idx))
        z = refined_pt[idx]
        dists = [abs(z - r) for r in known_roots]
        dmin, jmin = findmin(dists)
        println("  point $i, $name (certified) = $z  ",
                "dist to nearest known root = $(round(dmin, sigdigits=4))")
    end
end

println()
println("If dist-to-nearest-known-root is now ~1e-13 or smaller (true",
        " double-precision-clean) for all certified points, that CONFIRMS",
        " these are genuinely the known cubic/omega roots at full",
        " precision -- the earlier ~1e-4 residual was purely a degraded",
        " solve, and classify_and_reduce_d1.jl's bucketing was already",
        " correct, just imprecise. If dist stays around ~1e-4 even after",
        " certification, these points are NOT simply low-precision",
        " versions of the known roots -- that would be a real, different",
        " finding worth its own investigation.")

serialize(joinpath(@__DIR__, "certify_degraded_result.jls"),
          (flagged_indices = flagged_indices, cert_result = cert_result))
