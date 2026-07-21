#!/usr/bin/env julia
#
# run_degV.jl
#
# Driver to inspect the `.native` file format used by convert_to_native.jl /
# NewtonAnalyzer, and run the Jochemsz-May box/determinant analysis
# (jm_determinant_analysis.jl's `analyze`) on the resulting BoxShape.
#
# Usage:
#   julia run_degV.jl <path1.native> [path2.native ...] [--m N] [--prefilter]
#
# Notes:
# - This mirrors the native-file workflow used by run_jm_determinant.jl,
#   so it can be run on the same inputs, but accepts multiple files in one
#   invocation and prints a combined summary before running `analyze` on
#   each.
# - NewtonAnalyzer / the `.native` format only ever carries a polynomial's
#   *support* (its exponent vectors, i.e. a NewtonPolytope) -- never
#   coefficients or a base ring. There is no polynomial to recover from a
#   `.native` file, so there is no "generic affine slice degree" to compute
#   here; jm_determinant_analysis.jl's `analyze` (dimension formula,
#   deletion-invariance certificate, deletion density, exact-vs-closed-form
#   log-det cross-check, and success-threshold beta*) is the analysis this
#   data actually supports, and is what this script now runs.
# - All failure modes raise descriptive exceptions; there are no silent
#   fallbacks.
#

include(joinpath(@__DIR__, "newton_polytope.jl"))
include(joinpath(@__DIR__, "jm_determinant_analysis.jl"))

struct ParsedNative
    path::String
    analyzer::Any
    box_verdict::Any
    shape::BoxShape
    missing::Vector{Vector{Int}}
end

function parse_args(argv::Vector{String})
    isempty(argv) && error("run_degV.jl: expected at least one .native file")
    paths = String[]
    m_report = 6
    prefilter = true # don't change it to false you... ai

    i = 1
    while i <= length(argv)
        arg = argv[i]
        if arg == "--m"
            i += 1
            i <= length(argv) || error("run_degV.jl: --m requires an integer argument")
            m_report = parse(Int, argv[i])
        elseif arg == "--prefilter"
            prefilter = true
        elseif startswith(arg, "-")
            error("run_degV.jl: unrecognized flag '$arg'")
        else
            push!(paths, arg)
        end
        i += 1
    end

    isempty(paths) && error("run_degV.jl: no .native files provided")
    return paths, m_report, prefilter
end

function inspect_native(path::String; prefilter::Bool=false)
    isfile(path) || error("run_degV.jl: no such file: $path")
    println("Loading native file: ", path)
    prefilter && println("  (prefilter_extreme_candidates enabled)")
    t0 = time()
    A = NewtonAnalyzer(path; prefilter=prefilter)
    println("  built NewtonAnalyzer in ", round(time() - t0, digits=3), " s")
    println()

    println("Checking box structure...")
    verdict = detect_box_structure(A)
    verdict.is_box ||
        error("run_degV.jl: Newton polytope from $path is NOT an exact " *
              "axis-aligned box (detect_box_structure reported: " *
              "$(verdict.reason)) -- jm_determinant_analysis.jl's shift-" *
              "polynomial construction assumes a box support; see " *
              "detect_box_structure's docstring for the parallelotope/" *
              "manual follow-up, not a silent fallback here")
    println("  exact box confirmed")
    println("  origin       = ", verdict.origin)
    println("  side_lengths = ", verdict.side_lengths)
    println()

    println("Enumerating missing lattice points...")
    t1 = time()
    miss = missing_lattice_points(A)
    println("  missing count = ", length(miss))
    println("  computed in ", round(time() - t1, digits=3), " s")
    println()

    shape = BoxShape(verdict.origin, verdict.side_lengths, miss)
    return ParsedNative(path, A, verdict, shape, miss)
end

function main()
    paths, m_report, prefilter = parse_args(copy(ARGS))

    parsed = ParsedNative[]
    for path in paths
        push!(parsed, inspect_native(path; prefilter=prefilter))
    end

    println("=" ^ 72)
    println("Native-format summary")
    println("=" ^ 72)
    for p in parsed
        println("File: ", p.path)
        println("  box side lengths: ", p.shape.d)
        println("  missing monomials: ", length(p.missing))
        println("  deletion density: ", round(deletion_density(p.shape), sigdigits=4))
    end
    println()

    for p in parsed
        println("=" ^ 72)
        println("Jochemsz-May analysis: ", p.path)
        println("=" ^ 72)
        analyze(p.shape; m_report=m_report)
        println()
    end
end

if abspath(PROGRAM_FILE) == @__FILE__
    main()
end
