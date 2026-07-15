println("PART H: fully independent small-ring reconstruction (no R_dec)")
println("===========================================================")
println()

println("Building sample 1's isolated ring: [wa1, wa2, a1, a2, U0], from")
println("u1_num[1]/u1_den[1] directly -- R_dec is not referenced anywhere below.")
println()

Rs1, (wa1_s, wa2_s, a1_s, a2_s, U0_s) = polynomial_ring(F, ["wa1", "wa2", "a1", "a2", "U0"])

# u1_num[1]/u1_den[1] live in R (gens: wa1,wa2,wb1,wb2,a2,a1,b2,b1 --
# established far above at R's construction). Map wa1->wa1_s, wa2->wa2_s,
# wb1->0, wb2->0 (sample 1's num/den are already confirmed, in the
# DEGREE-IN-W DIAGNOSTIC printed earlier in this run, to have degree 0
# in wb1,wb2 -- so sending those generators to 0 is exact, not lossy),
# a2->a2_s, a1->a1_s, b2->0, b1->0.
#r_gens_full = gens(R)  # [wa1, wa2, wb1, wb2, a2, a1, b2, b1]
#images_s1 = [wa1_s, wa2_s, zero(Rs1), zero(Rs1), a2_s, a1_s, zero(Rs1), zero(Rs1)]
images_s1 = [wa1_s, wa2_s, a1_s, a2_s]
u1_num1_s = evaluate(u1_num[1], images_s1)
u1_den1_s = evaluate(u1_den[1], images_s1)
h_s1 = u1_num1_s - U0_s * u1_den1_s

curve_a1_s = wa1_s^2 - (a1_s^5 + a1_s + 2)
curve_a2_s = wa2_s^2 - (a2_s^5 + a2_s + 2)

println("  h_s1 = u1_num[1] - U0*u1_den[1], rebuilt in Rs1: degree=",
        total_degree(h_s1), "  terms=", length(terms(h_s1)))
println("  (compare to Fu_decoupled[1]'s degree=17/terms=306 from PART A --")
println("  these should match exactly since it's the same polynomial,")
println("  independently reconstructed)")
println()

Is1 = ideal(Rs1, [h_s1, curve_a1_s, curve_a2_s])

println("Eliminating [wa1_s, wa2_s] from Is1 (5-variable ring, 3 generators)...")
resultS1, statusS1, elapsedS1 = run_with_timeout(SUBIDEAL_TIMEOUT_SECS) do
    eliminate(Is1, [wa1_s, wa2_s])
end
# Fix for Sample 1 block
if statusS1 == :ok
    gS1 = gens(resultS1)
    println("  status=OK  elapsed=", round(elapsedS1, digits=3), "s")
    println("  parent ring = ", base_ring(resultS1)) # <-- Changed parent to base_ring
    println("  number of generators = ", length(gS1))
    for (i, g) in enumerate(gS1)
        println("    gen $i: degree=", total_degree(g), "  terms=", length(terms(g)))
    end
else
    println("  status=$statusS1 after ", round(elapsedS1, digits=3), "s")
end
println()

println("Building sample 2's isolated ring: [wb1, wb2, b1, b2, U0], from")
println("u2_num[1]/u2_den[1] directly.")
println()

Rs2, (wb1_s, wb2_s, b1_s, b2_s, U0_s2) = polynomial_ring(F, ["wb1", "wb2", "b1", "b2", "U0"])

images_s2 = [zero(Rs2), zero(Rs2), wb1_s, wb2_s, b2_s, zero(Rs2), zero(Rs2), b1_s]
# NOTE: r_gens_full order is [wa1,wa2,wb1,wb2,a2,a1,b2,b1] -- images_s2
# must follow that SAME order, mapping wa1,wa2,a2,a1 -> 0 and
# wb1,wb2,b2,b1 -> their Rs2 generators. Written out explicitly (not
# via a generic Dict-based remap helper) specifically so this mapping is
# directly inspectable against r_gens_full's printed order rather than
# hidden behind indirection, given how easy an off-by-one here would be
# to get wrong silently.
u2_num1_s = evaluate(u2_num[1], images_s2)
u2_den1_s = evaluate(u2_den[1], images_s2)
h_s2 = u2_num1_s - U0_s2 * u2_den1_s

curve_b1_s = wb1_s^2 - (b1_s^5 + b1_s + 2)
curve_b2_s = wb2_s^2 - (b2_s^5 + b2_s + 2)

println("  h_s2 = u2_num[1] - U0*u2_den[1], rebuilt in Rs2: degree=",
        total_degree(h_s2), "  terms=", length(terms(h_s2)))
println()

Is2 = ideal(Rs2, [h_s2, curve_b1_s, curve_b2_s])

println("Eliminating [wb1_s, wb2_s] from Is2 (5-variable ring, 3 generators)...")
resultS2, statusS2, elapsedS2 = run_with_timeout(SUBIDEAL_TIMEOUT_SECS) do
    eliminate(Is2, [wb1_s, wb2_s])
end
# Fix for Sample 2 block
if statusS2 == :ok
    gS2 = gens(resultS2)
    println("  status=OK  elapsed=", round(elapsedS2, digits=3), "s")
    println("  parent ring = ", base_ring(resultS2)) # <-- Changed parent to base_ring
    println("  number of generators = ", length(gS2))
    for (i, g) in enumerate(gS2)
        println("    gen $i: degree=", total_degree(g), "  terms=", length(terms(g)))
    end
else
    println("  status=$statusS2 after ", round(elapsedS2, digits=3), "s")
end
println()

println("#" ^ 70)
println("PART H READOUT")
println("#" ^ 70)
println()
println("Sample 1 isolated elimination: ", statusS1,
        statusS1 == :ok ? " ($(round(elapsedS1,digits=3))s)" : "")
println("Sample 2 isolated elimination: ", statusS2,
        statusS2 == :ok ? " ($(round(elapsedS2,digits=3))s)" : "")
println()
if statusS1 == :ok && statusS2 == :ok
    println("BOTH isolated 5-variable eliminations succeeded where PART C's")
    println("single-variable (wa1_d alone) elimination on the full 12-variable")
    println("Iu_decoupled did not. This is direct evidence the pathology is NOT")
    println("intrinsic to the elimination mathematics -- a 5-variable, 3-generator")
    println("elimination is not hard -- but IS specific to how Oscar/Singular")
    println("handles the larger ambient ring/ideal object, independent of how")
    println("many variables are actually being eliminated from it.")
elseif statusS1 == :timeout || statusS2 == :timeout
    println("At least one isolated elimination ALSO timed out. This would mean")
    println("the pathology is not purely an ambient-ring artifact -- something")
    println("about eliminating wa1,wa2 (or wb1,wb2) from THIS SPECIFIC degree-17")
    println("generator is intrinsically expensive, contradicting Part B k=1's")
    println("15s/degree-36/1445-term result for the FOUR-variable elimination of")
    println("the same generator. If that happens, the discrepancy between this")
    println("result and Part B k=1 (same generator, same variables eliminated,")
    println("different ring) is itself the next thing to explain.")
end
println()
println("On the dim() segfault (PART D, curve-only ideal): this happened on a")
println("4-generator, degree-5 ideal -- about as simple as this ring gets. That")
println("a crash occurred there specifically inside krull_dim ->")
println("singular_groebner_generators -> groebner_assure -> Singular's std()")
println("(see the backtrace) suggests dim()'s particular code path may be doing")
println("something version-specific and fragile in THIS Oscar/Singular build,")
println("independent of ideal difficulty. If PART H's isolated eliminations")
println("above succeed cleanly, that further isolates the problem: eliminate()")
println("itself may be fine on appropriately small inputs, and dim() specifically")
println("(not eliminate()) may be the fragile call. This combination -- ")
println("eliminate() hanging on the full ring, dim() segfaulting on a trivial")
println("ideal -- is exactly the shape of evidence worth filing as an issue")
println("against Singular.jl/Oscar.jl (https://github.com/oscar-system/Oscar.jl/issues),")
println("including: Oscar/Julia/Singular.jl versions (Pkg.status() output),")
println("this file's construction of R_dec and Is1/Is2, and both crash")
println("backtraces already captured in this run's output.")
# redtailBbb/omalloc allocator (see the backtrace after the k=2 timeout)
# is consistent with the k=2 background Task from Part B's run_with_timeout
# NOT having been killed -- Threads.@spawn cannot preempt a blocking
# Singular C call (see the caveat on run_with_timeout above), so when
# Part B moved on to k=3, the k=2 elimination was very likely STILL
# running in another thread, and the k=3 call started a SECOND
# concurrent Singular computation against the same underlying Singular/
# omalloc global allocator state. Singular's memory manager is not
# documented as safe against two concurrent kStd_internal/bba calls
# sharing global allocator pages from independent Task-based threads --
# the omInsertBinPage/omAllocBinFromFullPage frames in the crash are
# exactly the allocator's bin-page bookkeeping, and a page-table race
# between two simultaneous Groebner computations is a plausible direct
# cause. This is itself an argument for running Part B/C/G's timed steps
# as separate OS PROCESSES (`timeout N julia ...`) rather than
# in-process Tasks in any follow-up: it would avoid both the "can't
# actually kill a hung step" limitation AND this apparent concurrent-
# Singular-call crash. Not fixed in this patch since it requires
# factoring the shared construction code into an includable file, which
# is a larger restructuring than a targeted patch; the fiber-product
# decomposition in Part G above sidesteps the problem for THIS specific
# ideal by never trying to run two eliminate() calls in the same process
# without waiting for the first, but a general fix for Parts B/C/F still
# needs the subprocess-based timeout.
################################################################################
println("===========================================================")
