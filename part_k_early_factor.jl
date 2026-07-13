#!/usr/bin/env julia
################################################################################
#  part_k_early_factor.jl  --  divide out the common factor between two
#  Leibniz summands EARLY, at the level of individual Sylvester matrix
#  entries, instead of dividing the two fully-expanded 17.8M-term products
#  (which is what made divrem() hang -- see part_k_cofactors.jl).
#
#  Key idea: summand pi_idx corresponds to a permutation sigma. The summand
#  is the product  prod_i Syl[i, sigma[i]]  over rows i = 1..n. If two
#  summands sigma_1 and sigma_2 agree on some row i (sigma_1[i] ==
#  sigma_2[i]), then BOTH products contain the identical factor
#  Syl[i, sigma_1[i]] at that row. That factor is a common divisor of the
#  two summands "for free" -- no GCD algorithm needed, just comparing the
#  two permutation arrays -- and it can be left OUT of both partial
#  products while everything else is still small, degree ~24-52 per
#  factor rather than degree 256 for the fully multiplied-out summand.
#
#  This script:
#    1. Loads the two sigma's from the summand_survey.csv log (written by
#       elim2.jl's Part K driver).
#    2. Finds the shared rows (where sigma_1[i] == sigma_2[i]).
#    3. Builds q1 = product over ONLY the rows where they differ, for
#       sigma_1; likewise q2 for sigma_2. These are the "cofactors" you'd
#       have gotten from dividing the full products by their common
#       factor -- but computed directly, without ever forming the huge
#       degree-256 products or doing multivariate polynomial division.
#    4. Reports degree/term counts for q1, q2, and (for reference) the
#       shared-row product g_shared = prod over rows where they agree.
#
#  Caveat: this only captures the common factor coming from ROW AGREEMENT
#  between sigma_1 and sigma_2. It's possible (though we have no evidence
#  either way yet) that gcd(p1, p2) picks up additional shared structure
#  beyond just the shared-row factors -- e.g. if two DIFFERENT Sylvester
#  entries happen to share a polynomial factor even on rows where sigma_1
#  and sigma_2 disagree. This script won't find that kind of factor; it
#  only finds the "obviously free" row-agreement kind. If the degree of
#  g_shared here doesn't match the degree=192 found by gcd(p1,p2) earlier,
#  that's the signal that there's more shared structure than just row
#  agreement, and we'd need another approach for the rest.
#
#  Usage:
#      julia part_k_early_factor.jl <matrix_file> <summand_log_csv> <pi_idx_1> <pi_idx_2>
################################################################################

using Oscar

const PART_K_RESULTS_DIR = joinpath(@__DIR__, "part_k_results")

matrix_file = length(ARGS) >= 1 ? ARGS[1] :
    error("usage: julia part_k_early_factor.jl <matrix_file> <summand_log_csv> <pi_idx_1> <pi_idx_2>")
summand_log_csv = length(ARGS) >= 2 ? ARGS[2] :
    error("need summand_survey.csv path as 2nd arg")
pi_idx_1 = length(ARGS) >= 3 ? parse(Int, ARGS[3]) : 1
pi_idx_2 = length(ARGS) >= 4 ? parse(Int, ARGS[4]) : 2

isfile(matrix_file) || error("matrix file not found: $matrix_file")
isfile(summand_log_csv) || error("summand log not found: $summand_log_csv")

# ---- pull sigma_1, sigma_2 out of the CSV log ----
function find_sigma(csv_path, pi_idx)
    for line in eachline(csv_path)
        startswith(line, "perm_index") && continue  # header
        fields = split(line, ",")
        length(fields) < 2 && continue
        if tryparse(Int, fields[1]) == pi_idx
            sigma_str = fields[2]
            return parse.(Int, split(sigma_str, "-"))
        end
    end
    error("pi_idx $pi_idx not found in $csv_path")
end

sigma_1 = find_sigma(summand_log_csv, pi_idx_1)
sigma_2 = find_sigma(summand_log_csv, pi_idx_2)
println("sigma_$pi_idx_1 = ", sigma_1)
println("sigma_$pi_idx_2 = ", sigma_2)

length(sigma_1) == length(sigma_2) || error("sigma length mismatch")
n = length(sigma_1)

shared_rows = [i for i in 1:n if sigma_1[i] == sigma_2[i]]
diff_rows   = [i for i in 1:n if sigma_1[i] != sigma_2[i]]

println()
println("n = $n rows total")
println("shared rows (sigma_1[i] == sigma_2[i]): ", length(shared_rows), " -> ", shared_rows)
println("differing rows: ", length(diff_rows), " -> ", diff_rows)

if isempty(shared_rows)
    println()
    println("No shared rows at all between these two permutations -- there is no ",
            "row-agreement-based common factor to exploit here. (The gcd(p1,p2) ",
            "found earlier, if any, would have to come from some other kind of ",
            "shared structure between different Sylvester entries, not simple ",
            "row agreement.)")
    exit(0)
end

println()
println("loading Sylvester matrix <- ", matrix_file, " ...")
t0 = time()
Syl = load(matrix_file)
println("  loaded in ", round(time() - t0, digits=3), "s")

matsize = size(Syl, 1)
matsize == n || error("matrix size $matsize does not match sigma length $n")

Rfp = parent(Syl[1, 1])

function partial_product(sigma, rows)
    p = one(Rfp)
    for i in rows
        p *= Syl[i, sigma[i]]
    end
    return p
end

println()
println("computing g_shared = product over shared rows (same for both sigma_1, sigma_2) ...")
t0 = time()
g_shared = partial_product(sigma_1, shared_rows)
println("  done in ", round(time() - t0, digits=3), "s: degree=", total_degree(g_shared),
        " terms=", length(terms(g_shared)))

println()
println("computing q1 = product over differing rows only, using sigma_1 ...")
t0 = time()
q1 = partial_product(sigma_1, diff_rows)
println("  done in ", round(time() - t0, digits=3), "s: degree=", total_degree(q1),
        " terms=", length(terms(q1)))

println()
println("computing q2 = product over differing rows only, using sigma_2 ...")
t0 = time()
q2 = partial_product(sigma_2, diff_rows)
println("  done in ", round(time() - t0, digits=3), "s: degree=", total_degree(q2),
        " terms=", length(terms(q2)))

println()
println("sanity check: degree(q1) + degree(g_shared) should equal degree(p1) = 256, ",
        "same for q2. (Not verified against the actual saved p1/p2 here -- those ",
        "are the slow-to-load 17.8M-term files -- but this is what the row-count ",
        "split implies.)")
println("  degree(g_shared) = ", total_degree(g_shared))
println("  degree(q1)       = ", total_degree(q1), "   (expect 256 - degree(g_shared))")
println("  degree(q2)       = ", total_degree(q2), "   (expect 256 - degree(g_shared))")

out_prefix = joinpath(PART_K_RESULTS_DIR, "U0_summand_$(pi_idx_1)_$(pi_idx_2)_early")
println()
println("saving g_shared -> ", out_prefix, "_gshared.oscar")
save(out_prefix * "_gshared.oscar", g_shared)
println("saving q1 -> ", out_prefix, "_q1.oscar")
save(out_prefix * "_q1.oscar", q1)
println("saving q2 -> ", out_prefix, "_q2.oscar")
save(out_prefix * "_q2.oscar", q2)

open(out_prefix * ".stats", "w") do io
    println(io, "gshared_degree,gshared_terms,q1_degree,q1_terms,q2_degree,q2_terms")
    println(io, "$(total_degree(g_shared)),$(length(terms(g_shared))),",
                "$(total_degree(q1)),$(length(terms(q1))),",
                "$(total_degree(q2)),$(length(terms(q2)))")
end
println("stats -> ", out_prefix, ".stats")
