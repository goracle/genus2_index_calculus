println("PART D: dim/codim diagnostics (curve ideal, and smallest sub-ideal)")
println("===========================================================")
println()

println("--- dim/codim of curve-only ideal (4 gens, degree 5 each) ---")
result, status, elapsed = run_with_timeout(SUBIDEAL_TIMEOUT_SECS) do
    Icurve = ideal(R_dec, curve_gens_d)
    (dim(Icurve), codim(Icurve))
end
if status == :ok
    println("  status=OK  elapsed=", round(elapsed, digits=3), "s  dim=", result[1], "  codim=", result[2])
else
    println("  status=$status after ", round(elapsed, digits=3), "s")
end
println()

println("--- dim/codim of smallest sub-ideal (Fu_decoupled[1] + curves) ---")
result, status, elapsed = run_with_timeout(SUBIDEAL_TIMEOUT_SECS) do
    I1 = ideal(R_dec, vcat([Fu_decoupled[1]], curve_gens_d))
    (dim(I1), codim(I1))
end
if status == :ok
    println("  status=OK  elapsed=", round(elapsed, digits=3), "s  dim=", result[1], "  codim=", result[2])
else
    println("  status=$status after ", round(elapsed, digits=3), "s  ",
            "(if this alone times out, dim()/codim() themselves are the ",
            "pathological call, not eliminate() -- see PART A/B/C results ",
            "above for where actual elimination first breaks)")
end
println()

################################################################################
# PART E: confirm the ordering eliminate() is actually constructing.
#
# Oscar's eliminate(I, vars) does not expose its internal ordering object
# for direct inspection (there is no `eliminate(...; ordering=)` kwarg,
# and no public accessor returns "the ordering eliminate() used" after
# the fact -- confirmed against the current Oscar documentation for
# MPolyIdeal elimination, not assumed). What IS documented and directly
# checkable is what ordering groebner_basis(...; ordering=...) uses when
# YOU pass one explicitly, which is a separate code path. So: print
# block_ordering_dec (the explicit ordering object already built above,
# used only by direct groebner_basis calls) so its actual structure is
# visible, and print this caveat instead of asserting what eliminate()
# does internally without a way to check it.
################################################################################

println("===========================================================")
