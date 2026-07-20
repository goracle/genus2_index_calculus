#!/usr/bin/env julia
#
# inspect_schema.jl
#
# ONE-TIME diagnostic: does NOT load the polynomial through Oscar. Instead
# reads the first N bytes of the .mrdi/.oscar JSON file as raw text and
# prints them, so we can see the actual key structure Oscar used for this
# specific polynomial/ring/version -- rather than guessing the schema from
# docs and risking a silently-wrong parse on a multi-GB file.
#
# Usage: julia inspect_schema.jl <path> [n_bytes]

function main()
    length(ARGS) >= 1 ||
        error("inspect_schema.jl: usage: julia inspect_schema.jl <path> [n_bytes]")
    path = ARGS[1]
    isfile(path) ||
        error("inspect_schema.jl: no such file: $path")
    n_bytes = length(ARGS) >= 2 ? parse(Int, ARGS[2]) : 20_000

    fsize = filesize(path)
    println("file size: ", round(fsize / 1024 / 1024, digits=1), " MB")
    println()

    open(path, "r") do io
        buf = Vector{UInt8}(undef, min(n_bytes, fsize))
        readbytes!(io, buf)
        println("=== first ", length(buf), " bytes ===")
        print(String(buf))
        println()
        println("=== end of head ===")
    end

    # Also grab the tail -- top-level JSON keys are sometimes only
    # resolvable once you've seen the closing structure, and for an object
    # this large the "data" section is likely almost the entire file with
    # "_ns"/"refs" either very early or very late.
    open(path, "r") do io
        tail_n = min(n_bytes, fsize)
        seek(io, max(0, fsize - tail_n))
        buf = Vector{UInt8}(undef, tail_n)
        readbytes!(io, buf)
        println("=== last ", length(buf), " bytes ===")
        print(String(buf))
        println()
        println("=== end of tail ===")
    end
end

main()
