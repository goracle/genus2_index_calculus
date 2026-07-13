#!/usr/bin/env julia
################################################################################
#  part_k_cofactors.jl  --  given p1, p2, and g = gcd(p1, p2) already found
#  (see part_k_gcd_check.jl), compute the cofactors p1/g and p2/g. These are
#  what's actually "new" / non-shared between the two summands -- if g is a
#  common factor of degree 192 out of a total degree 256, the cofactors are
#  only degree 64, which is a much smaller object to keep working with.
#
#  Also sanity-checks that g divides both p1 and p2 exactly (no remainder)
#  before trusting the cofactors, since Oscar's gcd() should guarantee that
#  but it costs little to double check for a computation this expensive.
#
#  Usage:
#      julia part_k_cofactors.jl <term_file_1> <term_file_2> <gcd_file> [<out_prefix>]
################################################################################

using Oscar

const PART_K_RESULTS_DIR = joinpath(@__DIR__, "part_k_results")

term_file_1 = length(ARGS) >= 1 ? ARGS[1] :
    joinpath(PART_K_RESULTS_DIR, "U0_summand_1.stats.term.oscar")
term_file_2 = length(ARGS) >= 2 ? ARGS[2] :
    joinpath(PART_K_RESULTS_DIR, "U0_summand_2.stats.term.oscar")
gcd_file = length(ARGS) >= 3 ? ARGS[3] :
    joinpath(PART_K_RESULTS_DIR, "U0_summand_1_2_gcd.oscar")
out_prefix = length(ARGS) >= 4 ? ARGS[4] :
    joinpath(PART_K_RESULTS_DIR, "U0_summand")

for f in (term_file_1, term_file_2, gcd_file)
    isfile(f) || error("file not found: $f")
end

println("loading p1 <- ", term_file_1, " ...")
t0 = time()
p1 = load(term_file_1)
println("  loaded in ", round(time() - t0, digits=3), "s: degree=", total_degree(p1),
        " terms=", length(terms(p1)))

println("loading p2 <- ", term_file_2, " ...")
t0 = time()
p2 = load(term_file_2)
println("  loaded in ", round(time() - t0, digits=3), "s: degree=", total_degree(p2),
        " terms=", length(terms(p2)))

println("loading g <- ", gcd_file, " ...")
t0 = time()
g = load(gcd_file)
println("  loaded in ", round(time() - t0, digits=3), "s: degree=", total_degree(g),
        " terms=", length(terms(g)))

parent(p1) === parent(p2) === parent(g) || error("p1, p2, g are not all in the same ring")

println()
println("dividing p1 / g ...")
t0 = time()
q1, r1 = divrem(p1, g)
elapsed = time() - t0
if !iszero(r1)
    error("g does NOT divide p1 exactly (nonzero remainder) -- something is wrong, aborting before saving anything")
end
println("  p1/g exact, done in ", round(elapsed, digits=3), "s: ",
        "degree=", total_degree(q1), " terms=", length(terms(q1)))

println("dividing p2 / g ...")
t0 = time()
q2, r2 = divrem(p2, g)
elapsed = time() - t0
if !iszero(r2)
    error("g does NOT divide p2 exactly (nonzero remainder) -- something is wrong, aborting before saving anything")
end
println("  p2/g exact, done in ", round(elapsed, digits=3), "s: ",
        "degree=", total_degree(q2), " terms=", length(terms(q2)))

q1_file = out_prefix * "_1_cofactor.oscar"
q2_file = out_prefix * "_2_cofactor.oscar"
println()
println("saving cofactor 1 -> ", q1_file)
save(q1_file, q1)
println("saving cofactor 2 -> ", q2_file)
save(q2_file, q2)

open(out_prefix * "_cofactors.stats", "w") do io
    println(io, "cofactor1_degree,cofactor1_terms,cofactor2_degree,cofactor2_terms")
    println(io, "$(total_degree(q1)),$(length(terms(q1))),$(total_degree(q2)),$(length(terms(q2)))")
end
println("stats written -> ", out_prefix * "_cofactors.stats")

println()
println("summary:")
println("  p1: degree=", total_degree(p1), " terms=", length(terms(p1)))
println("  p2: degree=", total_degree(p2), " terms=", length(terms(p2)))
println("  g : degree=", total_degree(g),  " terms=", length(terms(g)))
println("  q1 = p1/g: degree=", total_degree(q1), " terms=", length(terms(q1)))
println("  q2 = p2/g: degree=", total_degree(q2), " terms=", length(terms(q2)))
