#!/usr/bin/env julia
################################################################################
#  part_k_add_two_summands.jl  --  load two already-computed Leibniz summand
#  terms (from part_k_summand_worker.jl's ".stats.term.oscar" output) and add
#  them together, no simplification beyond whatever Oscar's polynomial
#  addition already does (ordinary like-term collection -- no factoring, no
#  GCD, no cancellation search).
#
#  Why this exists: computing all 608 nonzero-compatible summands for U0 and
#  storing them all as separate ~large .term.oscar files was the original
#  plan, but that doesn't fit on disk. This script lets you build up the
#  partial sum two terms at a time instead, so you only ever need the
#  summand(s) you're currently adding plus the running total on disk at
#  once -- not all 608 simultaneously.
#
#  Usage:
#      julia part_k_add_two_summands.jl <term_file_1> <term_file_2> <output_file>
#
#  Defaults to U0_summand_1.stats.term.oscar + U0_summand_2.stats.term.oscar
#  in part_k_results/ if no arguments are given, since that's the first pair
#  you'd naturally reach for (both already confirmed "ok" in the summand
#  survey log).
################################################################################

using Oscar

const PART_K_RESULTS_DIR = joinpath(@__DIR__, "part_k_results")

term_file_1 = length(ARGS) >= 1 ? ARGS[1] :
    joinpath(PART_K_RESULTS_DIR, "U0_summand_1.stats.term.oscar")
term_file_2 = length(ARGS) >= 2 ? ARGS[2] :
    joinpath(PART_K_RESULTS_DIR, "U0_summand_2.stats.term.oscar")
output_file = length(ARGS) >= 3 ? ARGS[3] :
    joinpath(PART_K_RESULTS_DIR, "U0_summands_1plus2.oscar")

for f in (term_file_1, term_file_2)
    isfile(f) || error("term file not found: $f")
end

println("loading ", term_file_1, " ...")
t0 = time()
p1 = load(term_file_1)
println("  loaded in ", round(time() - t0, digits=3), "s: ",
        "degree=", total_degree(p1), " terms=", length(terms(p1)))

println("loading ", term_file_2, " ...")
t0 = time()
p2 = load(term_file_2)
println("  loaded in ", round(time() - t0, digits=3), "s: ",
        "degree=", total_degree(p2), " terms=", length(terms(p2)))

parent(p1) === parent(p2) || error("p1 and p2 live in different rings -- can't add directly")

println("adding p1 + p2 (plain polynomial addition, no factoring/GCD/cancellation search) ...")
t0 = time()
psum = p1 + p2
elapsed = time() - t0
deg = total_degree(psum)
nterms = length(terms(psum))
println("  done in ", round(elapsed, digits=3), "s: degree=$deg terms=$nterms")

println("saving -> ", output_file)
save(output_file, psum)
println("saved.")

stats_file = output_file * ".stats"
open(stats_file, "w") do io
    println(io, "$deg,$nterms")
end
println("stats written -> ", stats_file)
