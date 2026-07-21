#!/usr/bin/env julia
#
# run_degV.jl
#
# Driver to inspect the `.native` file format used by convert_to_native.jl /
# NewtonAnalyzer, and (when the underlying generators can be recovered)
# estimate the degree of a codimension-2 variety by a generic affine slice.
#
# Usage:
#   julia run_degV.jl <path1.native> [path2.native ...] [--seed N] [--trials N] [--prefilter]
#
# Notes:
# - This script intentionally mirrors the native-file workflow used by
#   run_jm_determinant.jl, so it can be run on the same inputs.
# - It first introspects the parsed native objects to help understand the
#   file format.
# - If the parsed object exposes polynomial generators, it forms the ideal,
#   adds two generic affine linear forms, and computes the degree of the
#   resulting zero-dimensional slice.
# - All failure modes raise descriptive exceptions; there are no silent
#   fallbacks.
#

include(joinpath(@__DIR__, "newton_polytope.jl"))
include(joinpath(@__DIR__, "jm_determinant_analysis.jl"))

using Random

# Oscar is needed for the degree computation once the generators are recovered.
# Keep the import explicit so the file still teaches the native format even if
# the inspection path is all the user needs.
using Oscar

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
    seed = 0
    trials = 1
    prefilter = false

    i = 1
    while i <= length(argv)
        arg = argv[i]
        if arg == "--seed"
            i += 1 <= length(argv) || error("run_degV.jl: --seed requires an integer argument")
            seed = parse(Int, argv[i])
        elseif arg == "--trials"
            i += 1 <= length(argv) || error("run_degV.jl: --trials requires an integer argument")
            trials = parse(Int, argv[i])
            trials >= 1 || error("run_degV.jl: --trials must be >= 1")
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
    return paths, seed, trials, prefilter
end

function inspect_native(path::String; prefilter::Bool=false)
    isfile(path) || error("run_degV.jl: no such file: $path")
    println("Loading native file: ", path)
    prefilter && println("  (prefilter_extreme_candidates enabled)")
    t0 = time()
    A = NewtonAnalyzer(path; prefilter=prefilter)
    println("  built NewtonAnalyzer in ", round(time() - t0, digits=3), " s")
    println("  analyzer type: ", typeof(A))
    println("  analyzer propertynames: ", propertynames(A, true))
    println()

    println("Checking box structure...")
    verdict = detect_box_structure(A)
    verdict.is_box || error("run_degV.jl: expected an exact box, got: $(verdict.reason)")
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

function try_recover_generators(A)
    # Heuristic introspection helper: the native reader may expose the
    # underlying generators under one of several common names.
    candidates = (
        :polys, :poly, :polynomial, :polynomials,
        :gens, :generators, :equations, :fs, :f, :terms
    )
    props = Set(propertynames(A, true))
    for sym in candidates
        if sym in props
            obj = getproperty(A, sym)
            if obj isa AbstractVector || obj isa Tuple
                return collect(obj), sym
            elseif obj !== nothing
                return [obj], sym
            end
        end
    end
    return nothing, nothing
end

function assert_same_ring(polys::Vector)
    isempty(polys) && error("assert_same_ring: no polynomials recovered")
    R = parent(polys[1])
    for (i, f) in enumerate(polys)
        parent(f) == R || error("assert_same_ring: polynomial $i lives in a different ring")
    end
    return R
end

function make_affine_linear_form(R, seed::Int, trial::Int, tag::Int)
    xs = gens(R)
    n = length(xs)
    n >= 2 || error("make_affine_linear_form: need at least two variables, got $n")
    K = base_ring(R)

    # Deterministic pseudo-random coefficients. The actual values are not
    # important; they just need to be generic enough for a slice.
    coeffs = Vector{Any}(undef, n)
    for j in 1:n
        raw = abs(hash((seed, trial, tag, j)))
        coeffs[j] = K(mod(raw, 1009) + 1)
    end
    shift = K(mod(abs(hash((seed, trial, tag, :shift))), 1009) + 1)

    L = zero(xs[1])
    for j in 1:n
        L += coeffs[j] * xs[j]
    end
    return L + shift
end

function recover_degree_from_generators(polys::Vector; seed::Int=0, trials::Int=1)
    isempty(polys) && error("recover_degree_from_generators: empty polynomial list")
    R = assert_same_ring(polys)
    n = ngens(R)
    n >= 2 || error("recover_degree_from_generators: ring has only $n variable(s)")
    if n < 4
        error("recover_degree_from_generators: degree-slice method expects the original positive-dimensional system in at least 4 variables; got $n")
    end

    degrees = BigInt[]
    for trial in 1:trials
        l1 = make_affine_linear_form(R, seed, trial, 1)
        l2 = make_affine_linear_form(R, seed, trial, 2)
        J = ideal(R, vcat(polys, [l1, l2]))
        d = dim(J)
        d == 0 || error("recover_degree_from_generators: slice ideal is not zero-dimensional (dim=$d); the chosen slice is not generic enough")
        degJ = degree(J)
        push!(degrees, BigInt(degJ))
        println("  trial $trial: degree(slice) = ", degJ)
    end

    firstdeg = first(degrees)
    all(d -> d == firstdeg, degrees) ||
        error("recover_degree_from_generators: inconsistent degrees across trials: $degrees")
    return firstdeg
end

function main()
    paths, seed, trials, prefilter = parse_args(copy(ARGS))
    prefilter = true

    #prefilter = true
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

    polys = Any[]
    recovered_from = Dict{String,Symbol}()

    for p in parsed
        gens, sym = try_recover_generators(p.analyzer)
        if gens === nothing
            println("Could not recover generators from ", p.path)
            println("  available properties: ", propertynames(p.analyzer, true))
            continue
        end
        println("Recovered $(length(gens)) generator(s) from ", p.path, " via field :$(sym)", sym)
        append!(polys, gens)
        recovered_from[p.path] = sym
    end

    isempty(polys) && error("run_degV.jl: no generators could be recovered from the native object(s); this is enough to inspect the file format, but not enough to compute a slice degree")

    println()
    println("=" ^ 72)
    println("Generic slice degree computation")
    println("=" ^ 72)
    println("seed   = ", seed)
    println("trials = ", trials)
    deg = recover_degree_from_generators(polys; seed=seed, trials=trials)
    println()
    println("Recovered degree from generic codimension-2 slice = ", deg)
    println("If this is the intended variety, this is the degree you want.")
end

if abspath(PROGRAM_FILE) == @__FILE__
    main()
end
