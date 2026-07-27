
################################################################################
# RESULTANT COMPUTATION -- gated behind an explicit flag.
#
# Per the diagnostic-first request, the actual resultant(g1_T,g2_T) call
# (subresultant PRS over Kcoef, previously ran unconditionally and was
# the call that hung for ~an hour) is NOT run automatically anymore.
# Set RUN_FULL_RESULTANT = true below (or via ENV) once PARTS A-E above
# have been read and a decision has been made on which algorithm/
# representation to actually commit to.
################################################################################

const RUN_FULL_RESULTANT = get(ENV, "ELIM2_RUN_FULL_RESULTANT", "false") == "true"

if !RUN_FULL_RESULTANT
    println()
    println("Skipping full resultant(g1_T, g2_T) computation (RUN_FULL_RESULTANT=false).")
    println("Set ENV[\"ELIM2_RUN_FULL_RESULTANT\"] = \"true\" to run it after reviewing ",
            "the PARTS A-E diagnostic above.")
    flush(stdout)
    exit(0)
end

println("    computing resultant via subresultant PRS (degree-in-T = $d1T, $d2T)...")
flush(stdout)
t0 = time()
res_frac = resultant(g1_T, g2_T)
elapsed = time() - t0
println("    resultant computed in ", round(elapsed, digits=3), "s")

# res_frac lives in Kcoef = Frac(F[a1,a2,b1,b2]); the true resultant of
# two polynomials with polynomial (not just rational) coefficients is
# itself a polynomial (no cryptographically-relevant denominator can
# survive -- Sylvester-matrix entries were already polynomials, and the
# determinant of a polynomial matrix is a polynomial), so we expect
# denominator(res_frac) to be a unit. Confirm rather than assume: if
# it's not a unit, something upstream (e.g. an unintended common factor
# introduced during the coefficient lift) needs inspection, but the
# resultant computation itself is already done at this point regardless.
res_num = numerator(res_frac)
res_den = denominator(res_frac)

if !is_unit(res_den)
    println("    WARNING: resultant denominator is not a unit (degree=",
            total_degree(res_den), "); this should not happen for a "
            * "genuine polynomial-coefficient resultant -- inspect "
            * "coefficient lift for spurious common factors.")
end

result_poly = Rcoef(res_num) // Rcoef(res_den)   # keep as exact fraction; typically res_den is a unit and this collapses to a polynomial

println("    $name resultant: total_degree=", total_degree(res_num),
        "  terms=", length(terms(res_num)))

# Save straight into the same place the old per-summand harness would
# have written its final assembled term, so downstream code that reads
# "the U0 resultant" doesn't need to change.
const RESULTANT_FILE = joinpath(ELIM2_ROOT_DIR, "part_k_results", "$(name)_resultant.oscar")
mkpath(dirname(RESULTANT_FILE))
save(RESULTANT_FILE, res_num)
println("    saved resultant -> ", RESULTANT_FILE)

################################################################################
# Everything below this point in the old file -- next_permutation!,
# first_k_permutations, first_k_nonzero_permutations,
# count_nonzero_permutations, the PART_K_MAX_WORKERS subprocess pool,
# part_k_launch/part_k_harvest/part_k_summand_complete, and the entire
# "keep computing summands until one dies" driver loop -- is now
# unnecessary and should be deleted. None of that machinery is wrong,
# exactly -- it correctly identifies which Leibniz summands are nonzero
# and safely isolates OOM crashes -- it is just solving a problem
# (surviving Leibniz expansion of an 8x8 determinant with huge entries)
# that a proper resultant algorithm avoids needing to solve at all.
################################################################################
