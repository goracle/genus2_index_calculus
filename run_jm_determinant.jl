#!/usr/bin/env julia
#
# run_jm_determinant.jl
#
# Driver connecting jm_determinant_analysis.jl to a REAL Newton polytope,
# rather than the synthetic self_check() example baked into that file.
#
# jm_determinant_analysis.jl itself does no file I/O -- it is a pure
# combinatorics library over an explicit BoxShape struct, checked against a
# hand-built synthetic example. This script is the missing piece: it loads
# an actual polynomial's support the same way run_newton_native.jl does,
# runs detect_box_structure/missing_lattice_points on it, and feeds the
# result into analyze().
#
# Usage:
#   julia run_jm_determinant.jl <path-to-.native-file> [m_report] [prefilter]
#
#   m_report: the m value used for the exact-vs-closed-form log-det
#   cross-check in analyze() (Section 4). Default 6, same default as
#   analyze()'s own keyword default.
#
#   prefilter: pass the literal string "prefilter" as the 3rd argument to
#   enable prefilter_extreme_candidates before convex_hull, exactly as
#   run_newton_native.jl does. REQUIRED in practice for supports of tens of
#   millions of points -- polymake's exact hull algorithm is not designed
#   for that scale and will OOM/hang rather than merely being slow (see
#   prefilter_extreme_candidates's docstring in newton_polytope.jl for the
#   exactness caveats of this fast path before trusting box-structure
#   results from a prefiltered run).
#
# Typical two-step workflow (same native-file convention as run_newton.jl):
#   julia convert_to_native.jl part_k_results/V1_resultant.oscar \
#                               part_k_results/V1_resultant.native
#   julia run_jm_determinant.jl part_k_results/V1_resultant.native 6 prefilter
#
# This requires Oscar (via newton_polytope.jl's polytope/convex-hull
# machinery) to build the polytope from the support and to run
# detect_box_structure -- unlike jm_determinant_analysis.jl on its own,
# which has no Oscar dependency and only needs Oscar when driven this way.
#
# If detect_box_structure reports the polytope is NOT an exact box, this
# raises rather than guessing at a fallback shape -- jm_determinant_analysis
# .jl's entire construction (Section 1-3) assumes an axis-aligned box
# support, and a non-box polytope needs the parallelotope/manual follow-up
# noted in detect_box_structure's own docstring before this analysis
# applies at all.

include(joinpath(@__DIR__, "newton_polytope.jl"))
include(joinpath(@__DIR__, "jm_determinant_analysis.jl"))

function main()
    length(ARGS) >= 1 ||
        error("run_jm_determinant.jl: expected at least 1 argument (path to " *
              "a native binary support file produced by convert_to_native.jl), " *
              "got $(length(ARGS)) -- usage: julia run_jm_determinant.jl " *
              "<path-to-.native-file> [m_report] [prefilter]")

    path = ARGS[1]
    isfile(path) ||
        error("run_jm_determinant.jl: no such file: $path")

    m_report = length(ARGS) >= 2 ? parse(Int, ARGS[2]) : 6
    use_prefilter = length(ARGS) >= 3 && ARGS[3] == "prefilter"

    println("Building Newton polytope from native support file: ", path)
    use_prefilter && println("  (prefilter_extreme_candidates ENABLED -- see docstring caveats)")
    t0 = time()
    A = NewtonAnalyzer(path; prefilter=use_prefilter)
    println("  built in ", round(time() - t0, digits=1), "s")
    println()

    println("Checking box structure (detect_box_structure)...")
    verdict = detect_box_structure(A)
    verdict.is_box ||
        error("run_jm_determinant.jl: Newton polytope from $path is NOT an " *
              "exact axis-aligned box (detect_box_structure reported: " *
              "$(verdict.reason)) -- jm_determinant_analysis.jl's shift-" *
              "polynomial construction assumes a box support (see its " *
              "Section 1-3); this file's own docstring suggests the " *
              "parallelotope/manual follow-up as the next step, not a " *
              "silent fallback here")
    println("  confirmed: exact box, origin=", verdict.origin,
            ", side_lengths=", verdict.side_lengths)
    println()

    println("Enumerating missing lattice points (missing_lattice_points)...")
    t1 = time()
    miss = missing_lattice_points(A)
    println("  found ", length(miss), " missing point(s) in ",
            round(time() - t1, digits=1), "s")
    println()

    shape = BoxShape(verdict.origin, verdict.side_lengths, miss)

    analyze(shape; m_report=m_report)
end

main()
