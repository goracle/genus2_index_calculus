#!/usr/bin/env julia
#
# run_newton_native.jl
#
# Driver for newton_polytope.jl that reads support directly from a flat
# native binary file (produced once by convert_to_native.jl), never calling
# Oscar.load on the original .oscar/.mrdi polynomial file. Use this for
# polynomials too large to round-trip through Oscar's JSON serialization.
#
# Usage:
#   julia run_newton_native.jl <path-to-.native-file> [max_k] [prefilter] [missing]
#
#   prefilter: pass the literal string "prefilter" as the 3rd argument to
#   enable prefilter_extreme_candidates before calling convex_hull. Needed
#   when the support has tens of millions of points, since polymake's exact
#   hull algorithm is not designed for that scale directly. See the caveats
#   in prefilter_extreme_candidates's docstring in newton_polytope.jl before
#   trusting results from a prefiltered run -- it is a fast heuristic, not a
#   certified-complete vertex enumeration.
#
#   missing: pass the literal string "missing" as the 4th argument to also
#   run missing_lattice_points and print every lattice point in the box that
#   is absent from the support. Only valid if detect_box_structure confirms
#   an exact axis-aligned box -- raises otherwise.
#
# Typical two-step workflow:
#   julia convert_to_native.jl part_k_results/V1_resultant.oscar \
#                               part_k_results/V1_resultant.native
#   julia run_newton_native.jl part_k_results/V1_resultant.native 6 prefilter missing
#
# Note: this driver does NOT need `using Oscar` for loading the polynomial
# (load_native_support is pure Julia I/O), but newton_polytope.jl still
# needs Oscar loaded for the polytope/convex-hull machinery, so it's brought
# in transitively via the include below.

include(joinpath(@__DIR__, "newton_polytope.jl"))

function main()
    length(ARGS) >= 1 ||
        error("run_newton_native.jl: expected at least 1 argument (path to a " *
              "native binary support file produced by convert_to_native.jl), " *
              "got $(length(ARGS)) -- usage: julia run_newton_native.jl " *
              "<path-to-.native-file> [max_k] [prefilter] [missing]")

    path = ARGS[1]
    isfile(path) ||
        error("run_newton_native.jl: no such file: $path")

    max_k = length(ARGS) >= 2 ? parse(Int, ARGS[2]) : 6
    use_prefilter = length(ARGS) >= 3 && ARGS[3] == "prefilter"
    show_missing = length(ARGS) >= 4 && ARGS[4] == "missing"

    println("Building Newton polytope from native support file: ", path)
    use_prefilter && println("  (prefilter_extreme_candidates ENABLED -- see docstring caveats)")
    t0 = time()
    A = NewtonAnalyzer(path; prefilter=use_prefilter)
    println("  built in ", round(time() - t0, digits=1), "s")
    println()

    summary(A; max_k=max_k)

    if show_missing
        println()
        println("=" ^ 70)
        println("Missing lattice points")
        println("=" ^ 70)
        print_missing_lattice_points(A)
    end
end

main()
