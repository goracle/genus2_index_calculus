println("PART A: static diagnostics on Fu_decoupled + curve generators")
println("(no Groebner call -- pure structural facts)")
println("===========================================================")
println()

all_gens_for_diag = vcat(Fu_decoupled, [curve_a1_d, curve_a2_d, curve_b1_d, curve_b2_d])
diag_labels = vcat(["Fu_decoupled[$i]" for i in 1:length(Fu_decoupled)],
                    ["curve_a1_d", "curve_a2_d", "curve_b1_d", "curve_b2_d"])

println(rpad("generator", 18), rpad("degree", 8), rpad("terms", 8),
        rpad("#vars", 7), rpad("vars-used", 30), rpad("homogeneous?", 13))
for (label, g) in zip(diag_labels, all_gens_for_diag)
    vs = vars(g)
    is_hom = is_homogeneous(g)
    println(rpad(label, 18), rpad(total_degree(g), 8), rpad(length(terms(g)), 8),
            rpad(length(vs), 7), rpad(join(string.(vs), ","), 30), rpad(is_hom, 13))
end
println()

# Total-degree profile: how many terms at each total degree, per generator
# (crude Hilbert-function-style shape -- fully dense vs concentrated at
# top degree looks very different and is informative before Groebner).
println("Degree profile (term-count histogram by total degree) per generator:")
for (label, g) in zip(diag_labels, all_gens_for_diag)
    profile = Dict{Int,Int}()
    for t in terms(g)
        d = total_degree(t)
        profile[d] = get(profile, d, 0) + 1
    end
    println("  $label: ", sort(collect(profile); by = first))
end
println()

println("Number of generators (Fu_decoupled + curves) = ", length(all_gens_for_diag))
println("Ambient ring R_dec has ", ngens(R_dec), " variables: ", symbols(R_dec))
println()

################################################################################
# Timeout helper. Runs `f()` on a background Task and polls it; if it has
# not finished within `limit_secs`, returns (nothing, :timeout, elapsed)
# without being able to kill the underlying computation (see note above).
# If it finishes, returns (result, :ok, elapsed). If it throws, returns
# (nothing, :error, elapsed) and prints the exception.
#
# IMPORTANT CAVEAT, stated plainly rather than assumed away: Threads.@spawn
# only gives the MAIN thread a chance to keep polling while f() runs on a
# separate Julia thread. It does NOT guarantee f() itself is preemptible.
# eliminate()/groebner_basis() ultimately block on a Singular or msolve C
# library call; if that C call does not yield back to the Julia scheduler
# (Singular's classical engine, in particular, is known to run as an
# uninterruptible foreign call from Julia's point of view), then the
# background task genuinely will not finish, this function will correctly
# report :timeout, but nothing about the underlying Singular process will
# have been reclaimed -- consistent with the note below the helper about
# needing `timeout N julia ...` at the OS level for a true kill. What this
# DOES reliably give you, which the previous single blind eliminate() call
# did not: the wall-clock point at which you know a given step has NOT
# finished, without that call blocking every LATER instrumentation step
# in this file from ever running. That is the actual gain here -- prior
# runs stopped producing output entirely once the first eliminate() call
# hung; this version continues past a timed-out step to the next one.
################################################################################

function run_with_timeout(f, limit_secs; poll_secs=1.0)
    t_start = time()
    task = Threads.@spawn begin
        try
            (:ok, f())
        catch e
            (:error, e)
        end
    end
    while !istaskdone(task) && (time() - t_start) < limit_secs
        sleep(poll_secs)
    end
    elapsed = time() - t_start
    if !istaskdone(task)
        return (nothing, :timeout, elapsed)
    end
    status, val = fetch(task)
    if status == :error
        println("  -> error: ", val)
        return (nothing, :error, elapsed)
    end
    return (val, :ok, elapsed)
end

const SUBIDEAL_TIMEOUT_SECS = 300.0   # 5 min per step -- adjust as needed
const VARSWEEP_TIMEOUT_SECS = 300.0

################################################################################
# PART B: incremental sub-ideal sweep.
#
# Build ideal(Fu_decoupled[1]), ideal(Fu_decoupled[1:2]), ...,
# ideal(Fu_decoupled[1:end]) -- always WITH the four curve equations
# included (dropping those would change the variety, not just shrink the
# ideal for timing purposes) -- and eliminate all four w's from each,
# timing every step. Fu_decoupled has 4 generators (u1 x^0, u2 x^0,
# u1 x^1, u2 x^1 -- see the construction loop above), so this is a sweep
# over prefixes of length 1..4.
################################################################################

################################################################################
# PART B: incremental sub-ideal sweep.
#
# Build ideal(Fu_decoupled[1]), ideal(Fu_decoupled[1:2]), ...,
# ideal(Fu_decoupled[1:end]) -- always WITH the four curve equations
# included (dropping those would change the variety, not just shrink the
# ideal for timing purposes) -- and eliminate all four w's from each,
# timing every step. Fu_decoupled has 4 generators (u1 x^0, u2 x^0,
# u1 x^1, u2 x^1 -- see the construction loop above), so this is a sweep
# over prefixes of length 1..4.
#
# EVIDENCE FROM ACTUAL RUN: k=1 completed in 15s (degree 36, 1445
# terms). k=2 timed out at 300s, and the k=3 step that followed
# triggered a Singular segfault (omalloc bin-page crash inside
# redtailBbb) -- most likely because the k=2 background Task was still
# running when k=3 started a second concurrent Singular call against
# shared allocator state (see the detailed NOTE further below, next to
# Part G). A segfault kills the entire Julia process and is NOT
# catchable by run_with_timeout's try/catch, so if PART_B_FULL_SWEEP is
# left on, this loop can crash before Part G (which answers the same
# question safely via fiber-product decomposition) ever runs. Defaults
# to running ONLY k=1 (the one step already confirmed safe and fast);
# set PART_B_FULL_SWEEP = true only once Parts B/C/F's timeout mechanism
# has been moved to subprocess-based (`timeout N julia ...`) kills, or if
# you specifically want to reproduce the crash for further debugging.
################################################################################

const PART_B_FULL_SWEEP = false

println("===========================================================")
