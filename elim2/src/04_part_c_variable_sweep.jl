println("PART C: incremental VARIABLE sweep on full Iu_decoupled")
println("(timeout=", VARSWEEP_TIMEOUT_SECS, "s per step)")
if !PART_C_FULL_SWEEP
    println("PART_C_FULL_SWEEP=false: running only step 1 (wa1_d alone).")
    println("Steps 2-4 add more variables/cross-sample coupling and risk the")
    println("same timeout/segfault seen in Part B k=2/k=3 -- see PART G below")
    println("for the safe, decomposed way to get the cross-sample answer.")
end
println("===========================================================")
println()

var_prefixes = [
    ("wa1_d only",                     [wa1_d]),
    ("wa1_d, wa2_d (sample 1 only)",   [wa1_d, wa2_d]),
    ("wa1_d, wa2_d, wb1_d",            [wa1_d, wa2_d, wb1_d]),
    ("wa1_d, wa2_d, wb1_d, wb2_d (all)", [wa1_d, wa2_d, wb1_d, wb2_d]),
]

prefixes_to_run = PART_C_FULL_SWEEP ? var_prefixes : var_prefixes[1:1]

if false # this times out
for (label, vs) in prefixes_to_run
    println("--- eliminating: $label ---")
    result, status, elapsed = run_with_timeout(VARSWEEP_TIMEOUT_SECS) do
        eliminate(Iu_decoupled, vs)
    end
    if status == :ok
        gk = gens(result)
        println("  status=OK  elapsed=", round(elapsed, digits=3), "s  ",
                "generators_out=", length(gk),
                "  degrees=", total_degree.(gk),
                "  terms=", length.(terms.(gk)))
    elseif status == :timeout
        println("  status=TIMEOUT after ", round(elapsed, digits=3), "s ",
                "(still running in background -- see note on run_with_timeout)")
    else
        println("  status=ERROR after ", round(elapsed, digits=3), "s")
    end
    println()
end
end # this times out^
################################################################################
# PART D: cheap dimension/codimension diagnostics on the CURVE ideal only
# (4 generators, degree 5 each, 8 variables -- should be fast) plus, if
# it survives its own timeout, on the smallest Part-B sub-ideal (k=1).
# dim()/codim() on the FULL Iu_decoupled are deliberately NOT called
# here -- the file's own earlier NOTE (see the dim(Iu)/dim(Iuv) removal
# above) already established that dim() triggers an uncontrolled
# default-ordering Groebner computation internally via
# singular_groebner_generators, independent of any ordering used
# elsewhere in this file. Calling it on the full system would just be a
# second, differently-shaped way of reproducing the same hang, not a
# diagnostic of it.
################################################################################

println("===========================================================")
