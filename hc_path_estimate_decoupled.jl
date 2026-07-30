#!/usr/bin/env julia
#
# hc_path_estimate_decoupled.jl
#
# BKK path-count estimate computed at Elim2Main.run_main's OWN output --
# Fu_decoupled / Fv_decoupled -- instead of at PART K's final U0=U1=V0=V1=0
# resultant system.
#
# WHY THIS IS A DIFFERENT (AND MUCH SMALLER) NUMBER
# --------------------------------------------------
# U0,U1,V0,V1 in the final system are themselves resultants (of g1,g2 over
# the fiber-product variable T, each g1/g2 already a resultant eliminating
# wa1,wa2,a1,a2 or wb1,wb2,b1,b2 from Fu_decoupled/Fv_decoupled). Counting
# HC paths on the FINAL system asks the homotopy to re-discover structure
# that TWO rounds of resultant elimination already collapsed into raw
# degree -- that's the "coupled system gives a hopeless path count".
#
# Fu_decoupled/Fv_decoupled are the actual defining equations, one round of
# substitution earlier:
#   sample 1 block: curve_a1, curve_a2, Fu_decoupled[1], Fu_decoupled[3],
#                    Fv_decoupled[1], Fv_decoupled[3]
#                    in variables (wa1,wa2,a1,a2,U0,U1,V0,V1)
#   sample 2 block: curve_b1, curve_b2, Fu_decoupled[2], Fu_decoupled[4],
#                    Fv_decoupled[2], Fv_decoupled[4]
#                    in variables (wb1,wb2,b1,b2,U0,U1,V0,V1)
# The two blocks are independent EXCEPT for sharing U0,U1,V0,V1 -- a fiber
# product, not a fully mixed 12-variable system. This script computes BKK
# bounds for each block treated as its own polynomial system (6 equations,
# 6 unknowns: wa1,wa2,a1,a2,U_i,V_i restricted to whichever U/V pair you
# ask for -- see below), directly from the live Oscar polynomials, with NO
# PART J/K/resultant computation needed at all.
#
# This only runs Elim2Main.run_main (the cheap, first pipeline stage --
# seconds, per your own err2.txt log) -- NOT run_all, NOT PART K.
#
# Usage:
#   julia hc_path_estimate_decoupled.jl
#
# What it reports:
#   1. Per-generator Newton polytope stats (dimension, vertex count) for
#      each of the 4 Fu_decoupled / 4 Fv_decoupled generators, plus the 4
#      curve relations -- so you can SEE the sparsity/dimension before
#      trusting any mixed-volume number built from them.
#   2. BKK bound (n-dim mixed volume via inclusion-exclusion, exact, from
#      newton_polytope.jl -- no new convex geometry code) for sample 1's
#      6-equation/6-unknown block and sample 2's block separately.
#   3. The total (sum, since the two blocks are solved as independent
#      homotopies coupled only through the 4 shared target variables --
#      NOT a product) as the actual candidate path-count bound for the
#      pipeline BEFORE PART K's resultant stage.
#
# IMPORTANT CAVEAT (stated, not hidden): BKK bounds the number of solutions
# in the ALGEBRAIC TORUS (nonzero coordinates) of a GENERIC system with the
# given supports. It is an upper bound on the number of HC paths needed for
# a polyhedral/toric start system, not a guarantee that this specific
# (non-generic, curve-constrained) system attains it -- some paths may
# diverge or correspond to solutions at infinity / on a coordinate
# hyperplane that get discarded. Treat this as "how many paths do I need to
# BUDGET for", not "how many actual solutions exist".

include(joinpath(@__DIR__, "newton_polytope.jl"))

using Combinatorics: combinations

# ---------------------------------------------------------------------------
# inclusion_exclusion_mixed_volume, copied from hc_path_estimate.jl (that
# file ends in an unconditional main() call driven by ARGS/--box, so it
# can't just be include()'d as a library -- this is the one function of
# its needed here, kept byte-identical to the original).
# ---------------------------------------------------------------------------

"""
    inclusion_exclusion_mixed_volume(polys::Vector{NewtonPolytope}) -> Rational

Exact mixed volume MV(P_1,...,P_n) of n polytopes in R^n via
    MV(P_1,...,P_n) = (1/n!) * sum_{S subseteq {1..n}, S nonempty}
                           (-1)^(n-|S|) * Vol(sum_{i in S} P_i)
Requires n! Minkowski sums to evaluate (2^n - 1 subset sums, each reusing
minkowski_sum/normalized_volume_of already in newton_polytope.jl). Raises if
any polytope's ambient dimension doesn't match n = length(polys).
"""
function inclusion_exclusion_mixed_volume(polys::Vector{NewtonPolytope})
    n = length(polys)
    n >= 1 || error("inclusion_exclusion_mixed_volume: need at least 1 polytope")
    for (i, P) in enumerate(polys)
        ambient_dimension(P) == n ||
            error("inclusion_exclusion_mixed_volume: polytope $i has " *
                  "ambient_dim=$(ambient_dimension(P)), expected $n to match " *
                  "the number of polytopes (mixed volume of n polytopes is " *
                  "only defined in R^n)")
    end

    total = 0 // 1
    idxs = collect(1:n)
    for k in 1:n
        for S in combinations(idxs, k)
            summed = polys[S[1]]
            for j in S[2:end]
                summed = minkowski_sum(summed, polys[j])
            end
            vol_S = normalized_volume_of(summed)
            sign = (-1)^(n - k)
            total += sign * vol_S
        end
    end
    mv = total // factorial(n)
    mv >= 0 ||
        error("inclusion_exclusion_mixed_volume: computed negative mixed " *
              "volume ($mv) -- check normalized_volume_of's scaling " *
              "convention before trusting this result")
    return mv
end

import Pkg
Pkg.activate(joinpath(@__DIR__, "Elim2"))
using Oscar
using Elim2

include(Elim2.Elim2Main.locate_engine_default())
using .PhiSymbolic

# ---------------------------------------------------------------------------
# Step 1: run ONLY Elim2Main.run_main -- this is where Fu_decoupled /
# Fv_decoupled already exist, long before PART J/K would ever be reached.
# ---------------------------------------------------------------------------

println("Running Elim2Main.run_main(PhiSymbolic) -- stage 'main' only, to get")
println("Fu_decoupled/Fv_decoupled without paying for PART J/K at all...")
println()

main = Elim2.Elim2Main.run_main(PhiSymbolic)
dec = main.decoupled

println()
println("Got DecoupledSystem. Fu_decoupled has ", length(dec.Fu_decoupled),
        " generators, Fv_decoupled has ", length(dec.Fv_decoupled), ".")
println("(Index convention from build_decoupled_system: for each U_i/V_i, ",
        "odd index = sample 1's equation, even index = sample 2's equation.)")
println()

# ---------------------------------------------------------------------------
# Step 2: per-generator Newton polytope report (curve relations + all
# Fu_decoupled/Fv_decoupled generators), so the block structure and sparsity
# are seen directly rather than assumed.
# ---------------------------------------------------------------------------

function report_polytope(label::String, poly)
    # prefilter=true: these generators' Newton polytopes are box/simplex-
    # shaped (U_i/V_i enter linearly, curve relations are degree-5 in one
    # var), so only a handful of extreme-direction candidates out of
    # hundreds of raw support points can ever be real vertices. Running
    # exact convex_hull on the full support here is wasted work at best and
    # the same hang/OOM risk newton_polytope.jl already warns about at
    # worst -- skip straight to the filtered candidate set.
    P = newton_polytope(support(poly), nvars(parent(poly)); prefilter=true)
    d = polytope_dimension(P)
    nv = length(vertices_of(P))
    println("  $label: ambient_dim=", P.ambient_dim, "  n_terms=", length(P.support),
            "  polytope_dim=", d, "  n_vertices=", nv)
    return P
end

println("=" ^ 70)
println("Per-generator Newton polytope report")
println("=" ^ 70)

println("--- Curve relations ---")
P_curve_a1 = report_polytope("curve_a1", dec.curve_a1_d)
P_curve_a2 = report_polytope("curve_a2", dec.curve_a2_d)
P_curve_b1 = report_polytope("curve_b1", dec.curve_b1_d)
P_curve_b2 = report_polytope("curve_b2", dec.curve_b2_d)

println("--- Fu_decoupled (U0 sample1, U0 sample2, U1 sample1, U1 sample2) ---")
P_Fu = [report_polytope("Fu_decoupled[$i]", g) for (i, g) in enumerate(dec.Fu_decoupled)]

println("--- Fv_decoupled (V0 sample1, V0 sample2, V1 sample1, V1 sample2) ---")
P_Fv = [report_polytope("Fv_decoupled[$i]", g) for (i, g) in enumerate(dec.Fv_decoupled)]
println()

# ---------------------------------------------------------------------------
# Step 3: confirm the fiber-product block structure directly (which
# variables actually appear in each generator), rather than assuming it --
# same spirit as run_active_vars.jl, but on the live polynomials.
# ---------------------------------------------------------------------------

println("=" ^ 70)
println("Active-variable check (confirms the fiber-product block structure)")
println("=" ^ 70)
dec_gens = gens(dec.R_dec)
gen_names = ["wa1", "wa2", "wb1", "wb2", "a2", "a1", "b2", "b1"]
n_target = length(dec.U_vars) + length(dec.V_vars)
append!(gen_names, ["U$i" for i in 0:(length(dec.U_vars)-1)])
append!(gen_names, ["V$i" for i in 0:(length(dec.V_vars)-1)])

function active_vars_report(label, poly)
    active = [i for i in 1:length(dec_gens) if degree(poly, dec_gens[i]) > 0]
    println("  $label: ", [gen_names[i] for i in active])
end

for (i, g) in enumerate(dec.Fu_decoupled)
    active_vars_report("Fu_decoupled[$i]", g)
end
for (i, g) in enumerate(dec.Fv_decoupled)
    active_vars_report("Fv_decoupled[$i]", g)
end
println()
println("Expected if the fiber-product structure holds: odd indices show only")
println("wa1,wa2,a1,a2,U*/V* (sample 1's own variables + shared targets); even")
println("indices show only wb1,wb2,b1,b2,U*/V* (sample 2's + shared targets).")
println("Confirm this by eye above before trusting the per-sample BKK split below.")
println()

# ---------------------------------------------------------------------------
# Step 4: per-sample block BKK bound.
#
# Sample 1's block (6 equations, 6 unknowns wa1,wa2,a1,a2,U_i,V_i restricted
# to ONE (U_i,V_i) pair at a time -- e.g. U0,V0 -- since U1/V1 are a SEPARATE
# copy of the same shared-target coupling, not additional unknowns in the
# SAME system): curve_a1, curve_a2, Fu_decoupled[2i-1], Fv_decoupled[2i-1].
# That's actually only 4 equations in 5 unknowns (wa1,wa2,a1,a2,U_i) if V_i
# is excluded, or 4 equations in 6 unknowns (wa1,wa2,a1,a2,U_i,V_i) if both
# U_i and V_i are targets tracked together for this sample -- in BOTH cases
# the system is UNDERDETERMINED as stated (fewer equations than unknowns)
# because U_i/V_i are only pinned down once sample 2's mirror equations are
# ALSO included. So the honest BKK-computable object is one sample's block
# PLUS the shared target variables PLUS the curve relations, all as ONE
# system in variables (wa1,wa2,a1,a2,wb1,wb2,b1,b2,U_i,V_i) -- 10 variables,
# 8 equations (4 curves + 2 Fu + 2 Fv, one U/V pair at a time) -- still far
# short of a square system, since U_i,V_i are the only variables genuinely
# fixed by BOTH samples together, while a1,a2,b1,b2,wa*,wb* are each only
# constrained by their OWN sample's curve relation plus ONE linear-in-U_i
# (resp. V_i) equation -- i.e. per anchor there are 2 unknowns (t,w) and 2
# equations (curve + Fu-or-Fv), so each anchor pair is ALREADY square on its
# own once U_i/V_i are fixed. This is exactly the point: solve the fiber
# BKK per anchor pair (2 equations, 2 unknowns: (a1,wa1) against curve_a1 +
# Fu_decoupled[1]; separately (a2,wa2) against curve_a2 -- but note
# Fu_decoupled[1] involves BOTH a1 AND a2 together, not one anchor alone --
# see the printed active-variable list above for the real coupling before
# assuming per-anchor decoupling holds).
#
# Given the active-variable report already shows Fu_decoupled[1] touching
# wa1,wa2,a1,a2 simultaneously (not one anchor at a time), the honest
# smallest SQUARE system per sample is:
#   {curve_a1, curve_a2, Fu_decoupled[2i-1], Fv_decoupled[2i-1]}
#   in {wa1, wa2, a1, a2} -- treating U_i, V_i as FIXED PARAMETERS (which is
#   exactly the role they play once the shared-target equations from BOTH
#   samples are solved together for U_i, V_i first, or symbolically, via
#   resultant elimination as PART K already does). This 4-equation/
#   4-unknown parametrized-by-(U_i,V_i) system is the natural per-sample
#   BKK object -- its mixed volume, doubled (both samples, same shape by
#   symmetry) and multiplied by the number of (U_i,V_i) combinations
#   actually of interest, is the path-count budget for solving each
#   sample's fiber BEFORE elimination, i.e. exactly what PART K's resultant
#   computation is a (much more expensive, degree-inflating) alternative
#   to computing this way.
# ---------------------------------------------------------------------------

println("=" ^ 70)
println("BKK bound: sample 1's fiber system {curve_a1, curve_a2,")
println("Fu_decoupled[1], Fv_decoupled[1]} in (wa1,wa2,a1,a2), U0/V0 held as")
println("parameters -- the natural square system PART K's resultant route")
println("is eliminating (U0,V0) FROM, not the final U0=U1=V0=V1=0 system.")
println("=" ^ 70)

sample1_system = [
    ("curve_a1", dec.curve_a1_d),
    ("curve_a2", dec.curve_a2_d),
    ("Fu_decoupled[1] (U0)", dec.Fu_decoupled[1]),
    ("Fv_decoupled[1] (V0)", dec.Fv_decoupled[1]),
]

# Restrict each polynomial's support to the (wa1,wa2,a1,a2) subspace for the
# mixed-volume computation: U0/V0 appear LINEARLY (Fu_decoupled/Fv_decoupled
# are U_i*den - num, i.e. degree 1 in U_i/V_i by construction -- see
# build_decoupled_system's own docstring), so treating them as parameters
# rather than unknowns for this system is exact, not an approximation: the
# Newton polytope in the 4 anchor/w variables alone, ignoring the (fixed)
# U0/V0 direction entirely, is what BKK against a parametrized coefficient
# field asks for.
function restrict_support_to_vars(poly, var_idxs::Vector{Int})
    supp_full = support(poly)
    return unique([[e[i] for i in var_idxs] for e in supp_full])
end

wa1_i, wa2_i, a2_i, a1_i = 1, 2, 5, 6   # indices into dec_gens per gen_names above
anchor_idxs = [wa1_i, wa2_i, a1_i, a2_i]

polys_sample1 = NewtonPolytope[]
for (label, g) in sample1_system
    supp_restricted = restrict_support_to_vars(g, anchor_idxs)
    P = newton_polytope(supp_restricted, 4; prefilter=true)
    println("  $label restricted to (wa1,wa2,a1,a2): n_terms(restricted)=",
            length(supp_restricted), "  polytope_dim=", polytope_dimension(P))
    push!(polys_sample1, P)
end

mv_sample1 = inclusion_exclusion_mixed_volume(polys_sample1)
println()
println("  Mixed volume (BKK path bound), sample 1's 4-equation/4-unknown")
println("  fiber system: ", mv_sample1)
println()

println("=" ^ 70)
println("BKK bound: sample 2's mirror fiber system {curve_b1, curve_b2,")
println("Fu_decoupled[2], Fv_decoupled[2]} in (wb1,wb2,b1,b2)")
println("=" ^ 70)

sample2_system = [
    ("curve_b1", dec.curve_b1_d),
    ("curve_b2", dec.curve_b2_d),
    ("Fu_decoupled[2] (U0)", dec.Fu_decoupled[2]),
    ("Fv_decoupled[2] (V0)", dec.Fv_decoupled[2]),
]

wb1_i, wb2_i, b2_i, b1_i = 3, 4, 7, 8
anchor_idxs_2 = [wb1_i, wb2_i, b1_i, b2_i]

polys_sample2 = NewtonPolytope[]
for (label, g) in sample2_system
    supp_restricted = restrict_support_to_vars(g, anchor_idxs_2)
    P = newton_polytope(supp_restricted, 4; prefilter=true)
    println("  $label restricted to (wb1,wb2,b1,b2): n_terms(restricted)=",
            length(supp_restricted), "  polytope_dim=", polytope_dimension(P))
    push!(polys_sample2, P)
end

mv_sample2 = inclusion_exclusion_mixed_volume(polys_sample2)
println()
println("  Mixed volume (BKK path bound), sample 2's 4-equation/4-unknown")
println("  fiber system: ", mv_sample2)
println()

println("=" ^ 70)
println("SUMMARY")
println("=" ^ 70)
println("  Sample 1 fiber BKK bound (per (U0,V0) parameter point): ", mv_sample1)
println("  Sample 2 fiber BKK bound (per (U0,V0) parameter point): ", mv_sample2)
println("  These are SOLVED INDEPENDENTLY per sample (each is its own 4x4")
println("  toric system), so the per-parameter-point path budget is the SUM,")
println("  not the product: ", mv_sample1 + mv_sample2)
println()
println("  Compare this to PART K's final U0=U1=V0=V1=0 system, whose")
println("  coefficients are ALREADY degree ~48-96 resultants (see err2.txt --")
println("  V1's g1/g2 are degree 52, degree-4-in-T, with 3125-term T-coefficients")
println("  each degree 48) -- i.e. two compounded resultant eliminations happened")
println("  between this fiber system and that one. This number is the honest")
println("  earlier-point path count; run this BEFORE deciding whether PART K's")
println("  resultant route (or a direct HC run on the fiber system above,")
println("  swept over however many (U0,V0)/(U1,V1) parameter values are")
println("  actually needed) is the better route to the DLP solve.")
