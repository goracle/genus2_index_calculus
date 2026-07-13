#!/usr/bin/env julia
################################################################################
#  part_k_gcd_check.jl  --  compute gcd(p1, p2) for two Leibniz summand term
#  files, as a real (not monomial-only) polynomial GCD check.
#
#  WARNING: multivariate GCD on degree-256 / ~17.8M-term polynomials can be
#  slow -- there is no guarantee this finishes quickly, or at all, in
#  reasonable time/memory. This script writes stats and prints progress
#  markers around the load and the gcd() call specifically so that if it
#  needs to be Ctrl-C'd, you know which phase it died in and roughly how
#  long the load alone took vs how long gcd() had been running.
#
#  It does NOT save the resulting gcd polynomial automatically if it turns
#  out to be trivial (a constant / 1) -- in that case there's nothing to
#  save and the answer is "no shared factor between these two summands."
#  If it's nontrivial, it IS saved, since that would be a genuinely useful
#  structural finding.
#
#  Usage:
#      julia part_k_gcd_check.jl <term_file_1> <term_file_2> [<output_file>]
################################################################################

using Oscar

const PART_K_RESULTS_DIR = joinpath(@__DIR__, "part_k_results")

term_file_1 = length(ARGS) >= 1 ? ARGS[1] :
    joinpath(PART_K_RESULTS_DIR, "U0_summand_1.stats.term.oscar")
term_file_2 = length(ARGS) >= 2 ? ARGS[2] :
    joinpath(PART_K_RESULTS_DIR, "U0_summand_2.stats.term.oscar")
output_file = length(ARGS) >= 3 ? ARGS[3] :
    joinpath(PART_K_RESULTS_DIR, "U0_summand_1_2_gcd.oscar")

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

parent(p1) === parent(p2) || error("p1 and p2 live in different rings -- can't gcd directly")

println()
println("computing gcd(p1, p2) -- this is a real multivariate GCD, NOT the ",
        "cheap monomial check. No progress output is possible mid-computation ",
        "(Oscar doesn't expose incremental progress for this), so the next ",
        "line you see is either the result or nothing for a long while. ",
        "If you need to abort, Ctrl-C is safe -- nothing has been written yet.")
flush(stdout)
t0 = time()
g = gcd(p1, p2)
elapsed = time() - t0
deg_g = total_degree(g)
nterms_g = length(terms(g))
println("gcd() finished in ", round(elapsed, digits=3), "s: degree=$deg_g terms=$nterms_g")

if nterms_g <= 1 && deg_g <= 0
    println("gcd is a unit/constant -- p1 and p2 share NO nontrivial common factor. Nothing to save.")
else
    println("NONTRIVIAL common factor found. Saving -> ", output_file)
    save(output_file, g)
    stats_file = output_file * ".stats"
    open(stats_file, "w") do io
        println(io, "$deg_g,$nterms_g")
    end
    println("stats written -> ", stats_file)
end
