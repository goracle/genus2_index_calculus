#!/usr/bin/env julia
#
# run_active_vars.jl
#
# Per-equation driver: reports which variables actually appear (nonzero
# exponent somewhere in the support) for a SINGLE .native support file.
# Doesn't need the other 3 equations -- run this on each one as it finishes.
#
# This is the fact-check for the block-decomposition question: whether
# {U_alpha, V_alpha} only ever involve {x1,x2} and {U_alphaprime,
# V_alphaprime} only ever involve {x3,x4}. That determines which mixed-
# volume formula (and which path-count estimate) actually applies -- see
# hc_path_estimate.jl.
#
# Usage:
#   julia run_active_vars.jl <path-to-.native-file> [box]
#
#   box: pass the literal string "box" as the 2nd argument to also run
#   detect_box_structure and report the per-variable degree bounds (min/max
#   exponent per active variable) -- useful for confirming the stated
#   degree-64 / degree-96 box assumption against real data, not just
#   assumed. Only meaningful once the file's ambient_dim/active-var set is
#   already sane; runs after the active-variable report either way.
#
# Example (run once per equation as each finishes, no waiting required):
#   julia run_active_vars.jl U_alpha.native box
#   julia run_active_vars.jl V_alpha.native box
#   julia run_active_vars.jl U_alphaprime.native box
#   julia run_active_vars.jl V_alphaprime.native box   # once it's done

include(joinpath(@__DIR__, "newton_polytope.jl"))

"""
    active_variables(supp::Vector{Vector{Int}}, ambient_dim::Int) -> Vector{Int}

1-indexed list of variables with a nonzero exponent in at least one term of
the support. Pure bookkeeping over the exponent vectors already loaded --
no convex-hull/Polymake call involved, so this is cheap even for tens of
millions of terms.
"""
function active_variables(supp::Vector{Vector{Int}}, ambient_dim::Int)
    active = falses(ambient_dim)
    for e in supp
        length(e) == ambient_dim ||
            error("active_variables: exponent vector has length $(length(e)), " *
                  "expected ambient_dim=$ambient_dim -- corrupt support data?")
        @inbounds for i in 1:ambient_dim
            e[i] != 0 && (active[i] = true)
        end
    end
    return [i for i in 1:ambient_dim if active[i]]
end

"""
    per_variable_degree_bounds(supp, ambient_dim, active) -> Dict{Int,Tuple{Int,Int}}

For each active variable, the (min, max) exponent seen across the support.
For a full axis-aligned box this should come back (0, degree) for every
active variable. Deviation from that is worth noticing before trusting the
box-degree assumption used elsewhere.
"""
function per_variable_degree_bounds(supp::Vector{Vector{Int}}, ambient_dim::Int,
                                     active::Vector{Int})
    bounds = Dict{Int, Tuple{Int,Int}}(i => (typemax(Int), typemin(Int)) for i in active)
    for e in supp
        for i in active
            (lo, hi) = bounds[i]
            bounds[i] = (min(lo, e[i]), max(hi, e[i]))
        end
    end
    return bounds
end

function main()
    length(ARGS) >= 1 ||
        error("run_active_vars.jl: expected at least 1 argument (path to a " *
              ".native support file), got $(length(ARGS)) -- usage: " *
              "julia run_active_vars.jl <path> [box]")

    path = ARGS[1]
    isfile(path) ||
        error("run_active_vars.jl: no such file: $path")
    run_box = length(ARGS) >= 2 && ARGS[2] == "box"

    println("=" ^ 70)
    println(path)
    println("=" ^ 70)

    t0 = time()
    (supp, ambient_dim) = load_native_support(path)
    println("  loaded in ", round(time() - t0, digits=1), "s")

    active = active_variables(supp, ambient_dim)
    println()
    println("ambient_dim   = ", ambient_dim)
    println("n_terms       = ", length(supp))
    println("active vars   = ", active, "  (1-indexed; these are the only ",
            "variables this equation actually depends on)")

    if length(active) < ambient_dim
        inactive = [i for i in 1:ambient_dim if !(i in active)]
        println("inactive vars = ", inactive,
                "  -- equation is identically constant in these")
    end

    bounds = per_variable_degree_bounds(supp, ambient_dim, active)
    println()
    println("per-variable degree range (min exponent, max exponent):")
    for i in active
        (lo, hi) = bounds[i]
        println("  x$i : ($lo, $hi)")
    end

    if run_box
        println()
        println("-" ^ 70)
        println("Box structure check (detect_box_structure)")
        println("-" ^ 70)
        # prefilter=true is not optional at this scale -- exact convex hull
        # on tens of millions of points hangs/OOMs polymake, per
        # newton_polytope.jl's own warning. We already have per_variable_
        # degree_bounds above (cheap, exact, no hull needed) confirming this
        # is box-shaped in the min/max sense; prefilter's heuristic hull is
        # only being asked to double check vertex/facet structure, not
        # discover the degree bounds from scratch.
        A = NewtonAnalyzer(supp, ambient_dim; prefilter=true)
        try
            verdict = detect_box_structure(A)
            println(verdict)
        catch e
            println("  detect_box_structure failed/raised: ", e)
        end
    end

    println()
    println("Next: run this on the other equations as they finish, then ",
            "compare 'active vars' across all 4 -- if {U_alpha,V_alpha} both ",
            "show [1,2] and {U_alphaprime,V_alphaprime} both show [3,4] ",
            "(or whichever two-and-two split), the block decomposition is ",
            "confirmed and hc_path_estimate.jl's Scenario A applies.")
end

main()
