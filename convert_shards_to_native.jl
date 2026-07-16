#!/usr/bin/env julia
#
# convert_shards_to_native.jl  (v2 -- direct text parse, no Oscar.load())
#
# Diagnosis (confirmed on shard_000005.oscar): the file itself is only
# 561M / 17.85M terms (~33 bytes/term on disk -- cheap). Oscar.load()
# OOMs anyway, even with 11G free, because it (1) parses the whole file
# into a generic JSON tree (a Vector{Any}/Dict/String allocation per
# term, easily 200-500+ bytes/term of Julia object overhead alone), then
# (2) reconstructs an MPolyRingElem from that tree with FLINT-backed
# bignum coefficients. Both steps hold the ENTIRE shard in memory in a
# heavier representation than the final answer needs. That 10-20x
# blowup on a 561M file is exactly enough to exceed 11G free.
#
# This script skips both steps. The .oscar format (confirmed by direct
# inspection) is flat and self-describing:
#   {"_ns":...,"_type":...,"data":[[["e1","e2","e3","e4"],"coeff"], ...],
#    "_refs":{...ring/field metadata...}}
# `data` is a single JSON array of (exponent-vector, coefficient-string)
# pairs with NO further nesting. We scan the raw text directly with a
# regex over that flat structure -- no JSON tree, no Oscar object model
# -- and push terms straight into an MPolyBuildCtx one at a time,
# streaming so peak memory is O(1) terms resident at once for the parse
# itself (plus whatever the destination polynomial needs, which is the
# actual unavoidable floor).
#
# USAGE:
#   julia convert_shards_to_native.jl <name>
# e.g.
#   julia convert_shards_to_native.jl U0

using Oscar
using Serialization

if length(ARGS) != 1
    error("usage: julia convert_shards_to_native.jl <name>  (e.g. U0) -- " *
          "got $(length(ARGS)) argument(s): $(ARGS)")
end
name = ARGS[1]

# Must match elim2.jl's F/Rcoef construction exactly -- confirmed against
# shard_000005.oscar's _refs block: symbols ["a1","a2","b1","b2"],
# field characteristic "2371157".
const p = 2371157
F = GF(p)
Rcoef, (a1_c, a2_c, b1_c, b2_c) = polynomial_ring(F, ["a1", "a2", "b1", "b2"])

scratch_dir = joinpath(@__DIR__, "part_f_scratch", name)
shards_dir  = joinpath(scratch_dir, "shards")
isdir(shards_dir) || error("convert_shards_to_native: no such directory $shards_dir -- " *
                            "check <name> matches elim2.jl's PARTF_SCRATCH_DIR")

oscar_shards = sort(filter(f -> startswith(f, "shard_") && endswith(f, ".oscar"),
                            readdir(shards_dir)))
if isempty(oscar_shards)
    println("No .oscar shards found under $shards_dir -- nothing to convert.")
    exit(0)
end

println("Converting ", length(oscar_shards), " .oscar shard(s) to .native under ", shards_dir,
        " via direct text parse (bypassing Oscar.load())...")
flush(stdout)

# Matches one term: [["e1","e2","e3","e4"],"coeff"]
# Captures the 4 exponent strings and the coefficient string separately.
const TERM_RE = r"\[\[\"(\d+)\",\"(\d+)\",\"(\d+)\",\"(\d+)\"\],\"(\d+)\"\]"

function parse_shard_streaming(path)
    # read() the raw bytes once -- this IS necessary (can't regex-scan
    # a file we haven't read), but a String/byte buffer of the file's
    # own size is a completely different cost than a JSON object tree
    # 10-20x larger. This is the floor, not the blowup.
    content = read(path, String)

    rebuild_ctx = MPolyBuildCtx(Rcoef)
    n_terms = 0
    for m in eachmatch(TERM_RE, content)
        exps = [parse(Int, m.captures[1]), parse(Int, m.captures[2]),
                parse(Int, m.captures[3]), parse(Int, m.captures[4])]
        coeff_val = parse(BigInt, m.captures[5])
        push_term!(rebuild_ctx, F(coeff_val), exps)
        n_terms += 1
        if n_terms % 2_000_000 == 0
            println("      parsed ", n_terms, " terms so far...")
            flush(stdout)
        end
    end
    content = nothing   # drop the raw text before finish() builds the poly
    n_terms == 0 &&
        error("parse_shard_streaming: matched 0 terms in $path -- regex mismatch " *
              "against actual file format, refusing to write an empty/wrong shard")
    rebuilt = finish(rebuild_ctx)
    return rebuilt, n_terms
end

for (si, fname) in enumerate(oscar_shards)
    src_path = joinpath(shards_dir, fname)
    dst_path = joinpath(shards_dir, replace(fname, ".oscar" => ".native"))

    if isfile(dst_path)
        println("  [", si, "/", length(oscar_shards), "] ", fname,
                " -> already converted (", basename(dst_path), " exists), skipping.")
        flush(stdout)
        continue
    end

    println("  [", si, "/", length(oscar_shards), "] ", fname, ": parsing...")
    flush(stdout)
    t0 = time()
    poly, n_terms_parsed = parse_shard_streaming(src_path)

    coeffs_out = collect(coefficients(poly))
    exps_out   = collect(AbstractAlgebra.exponent_vectors(poly))
    poly = nothing
    length(coeffs_out) != length(exps_out) &&
        error("convert_shards_to_native: coeffs/exps length mismatch " *
              "($(length(coeffs_out)) vs $(length(exps_out))) for $src_path -- " *
              "refusing to write a shard that can't be reconstructed")

    tmp_path = dst_path * ".tmp"
    open(tmp_path, "w") do io
        serialize(io, (coeffs_out, exps_out))
    end
    mv(tmp_path, dst_path; force=true)
    n_terms_final = length(coeffs_out)
    coeffs_out = nothing
    exps_out = nothing
    GC.gc(false)

    println("  [", si, "/", length(oscar_shards), "] ", fname, ": ", n_terms_parsed,
            " raw terms parsed -> ", n_terms_final, " terms after collection -> ",
            basename(dst_path), " in ", round(time() - t0, digits=1), "s")
    flush(stdout)
end

println("Done. Re-run elim2.jl -- it will find .native shards and use load_shard_native() exclusively.")
