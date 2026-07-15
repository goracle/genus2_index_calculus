println("PART B: incremental sub-ideal sweep on Fu_decoupled")
println("(each step: eliminate [wa1_d,wa2_d,wb1_d,wb2_d], timeout=",
        SUBIDEAL_TIMEOUT_SECS, "s)")
if !PART_B_FULL_SWEEP
    println("PART_B_FULL_SWEEP=false: running only k=1 (confirmed safe/fast).")
    println("k=2 previously timed out and k=3 segfaulted Singular in this exact")
    println("construction -- see PART G below for the safe way to get the")
    println("k=2-equivalent answer via fiber-product decomposition.")
end
println("===========================================================")
println()

curve_gens_d = [curve_a1_d, curve_a2_d, curve_b1_d, curve_b2_d]

k_range = PART_B_FULL_SWEEP ? (1:length(Fu_decoupled)) : (1:1)

for k in k_range
    prefix = Fu_decoupled[1:k]
    Ik = ideal(R_dec, vcat(prefix, curve_gens_d))
    println("--- k=$k: ideal(Fu_decoupled[1:$k], curves)  [", length(prefix) + 4, " generators] ---")
    result, status, elapsed = run_with_timeout(SUBIDEAL_TIMEOUT_SECS) do
        eliminate(Ik, [wa1_d, wa2_d, wb1_d, wb2_d])
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

################################################################################
# PART C: incremental VARIABLE sweep.
#
# Eliminate just wa1_d, then wa1_d+wa2_d (sample 1's w's only), then
# wa1_d+wa2_d+wb1_d (adding sample 2's first w), then all four. This
# directly answers: is a single sample's pair of w's already hard
# (intrinsic to one sample's algebra), or does it only blow up once
# BOTH samples' w's are being eliminated jointly (cross-sample
# interaction)? Run against the FULL Fu_decoupled + curves ideal (not
# the sub-ideal sweep from Part B) so this isolates the variable-count
# effect specifically.
#
# RISK, based on actual evidence: this runs against Iu_decoupled, i.e.
# ALL FOUR Fu_decoupled generators together -- the same joint-sample
# shape whose 2-generator version (Part B's k=2) already timed out and
# whose 3-generator version (k=3) segfaulted Singular. The first two
# steps here (wa1_d alone; wa1_d+wa2_d) only involve sample-1 variables
# and curve_a1_d/curve_a2_d in terms of what's REACHABLE from those
# variables, but Iu_decoupled itself still contains all 4 generators as
# ideal members regardless of which variables you ask eliminate() to
# remove -- so even the "sample 1 only" steps are not guaranteed as safe
# as Part G's genuinely-isolated small-ring version. Steps 3 and 4
# explicitly add sample-2 variables and are the most likely to reproduce
# the hang/segfault. Same guard as Part B: default to the first step
# only (which involves the fewest target variables and is closest to
# the confirmed-fast Part B k=1 case), full sweep opt-in via
# PART_C_FULL_SWEEP.
################################################################################

const PART_C_FULL_SWEEP = false

println("===========================================================")
