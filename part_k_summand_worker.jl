#!/usr/bin/env julia
################################################################################
#  part_k_summand_worker.jl  --  compute ONE Leibniz summand of
#  det(Sylvester matrix), in its own OS process.
#
#  Why a subprocess: the whole point of "keep computing summands and see
#  where it dies" is to find a memory ceiling. Doing that in-process risks
#  (a) one bad summand OOM-killing the entire exploration, losing every
#  earlier result along with it, and (b) memory from earlier "successful"
#  summands lingering (GC pressure, fragmentation) and contaminating later
#  measurements. One process per summand means each measurement starts
#  from a clean slate and a crash only takes down that one data point.
#
#  Usage:
#      julia part_k_summand_worker.jl <matrix_file> <sigma> <stats_file>
#
#  <sigma> is a permutation of 1..n written as "3-1-4-2-..." (1-indexed,
#  hyphen-separated). <matrix_file> is an Oscar-saved n x n Matrix of
#  polynomials (from elim2.jl's Part K, take 5). Writes a single CSV-ish
#  line "degree,terms" to <stats_file> IMMEDIATELY after the product is
#  fully computed and its size measured -- i.e. before doing anything
#  more expensive (like stringifying/writing the full polynomial) -- so
#  that even if this process is later killed, the stats file still
#  captures the size that was reached.
################################################################################

using Oscar

if length(ARGS) != 3
    error("usage: julia part_k_summand_worker.jl <matrix_file> <sigma> <stats_file>")
end

matrix_file = ARGS[1]
sigma_str = ARGS[2]
stats_file = ARGS[3]

sigma = parse.(Int, split(sigma_str, "-"))

println("[summand worker] loading Sylvester matrix from ", matrix_file, " ...")
Syl = load(matrix_file)
n = size(Syl, 1)
length(sigma) == n || error("sigma length $(length(sigma)) does not match matrix size $n")

# Parity of sigma (needed for the correct signed summand, even though the
# survey itself only cares about size/timing, not the running total).
function permutation_sign(p::Vector{Int})
    n = length(p)
    visited = falses(n)
    sign = 1
    for i in 1:n
        if !visited[i]
            j = i
            clen = 0
            while !visited[j]
                visited[j] = true
                j = p[j]
                clen += 1
            end
            if iseven(clen)
                sign = -sign
            end
        end
    end
    return sign
end

sign_sigma = permutation_sign(sigma)

println("[summand worker] sigma=", sigma, " sign=", sign_sigma, "  computing product...")
t0 = time()

Rfp = parent(Syl[1, 1])

# Cheap pre-check: if ANY factor Syl[i, sigma[i]] is the structural zero
# entry of the (possibly sparse/banded) matrix, the whole product is the
# zero polynomial identically -- no need to multiply anything out to
# discover that. This matters because the driver in elim2.jl is expected
# to only hand this worker sigma's that are already nonzero-compatible,
# but this worker can also be invoked standalone (see usage comment above)
# with an arbitrary sigma, so it should not silently burn CPU/time
# multiplying degree-huge polynomials by zero just to rediscover degree=-1.
zero_factor_row = findfirst(i -> iszero(Syl[i, sigma[i]]), 1:n)
if zero_factor_row !== nothing
    println("[summand worker] Syl[$zero_factor_row, $(sigma[zero_factor_row])] is structurally zero ",
            "-- product is the zero polynomial, skipping multiplication.")
    term = zero(Rfp)
else
    term = one(Rfp)
    for i in 1:n
        global term *= Syl[i, sigma[i]]
    end
    if sign_sigma == -1
        term = -term
    end
end

elapsed = time() - t0
deg = total_degree(term)
nterms = length(terms(term))

println("[summand worker] product done in $(round(elapsed, digits=3))s: degree=$deg terms=$nterms")

# Write stats FIRST, before anything else that might be expensive enough
# to OOM (e.g. serializing the full polynomial). This is the line that
# the driver in elim2.jl reads back, and the one that survives even if
# this process dies right after.
open(stats_file, "w") do io
    println(io, "$deg,$nterms")
end
println("[summand worker] stats written -> ", stats_file)

# Optionally also save the full term -- comment out if this is what's
# killing individual workers; the stats above already capture the size
# that matters for finding the ceiling.
save(stats_file * ".term.oscar", term)
println("[summand worker] full term saved -> ", stats_file, ".term.oscar")
