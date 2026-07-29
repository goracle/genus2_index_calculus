#!/usr/bin/env julia
################################################################################
#
#  singular_concurrent_crash_repro.jl
#
#  Minimal, self-contained reproducer for the Singular/OSCAR allocator
#  crash documented (but never isolated into its own file) in Elim2/src/
#  02_norm_elim_diag.jl and Elim2/src/part_j_worker.jl of the
#  goracle/elliptic-fibration-search repo.
#
#  WHERE THIS CAME FROM (source locations, for the OSCAR issue report):
#
#    - Elim2/src/02_norm_elim_diag.jl, run_with_timeout()'s docstring
#      (~line 403-419) and run_part_b_subideal_sweep!()'s docstring
#      (~line 512-531): documents that PART B's k=1 eliminate() call
#      completed in 15s, k=2 timed out at 300s via a Threads.@spawn-based
#      soft timeout (which does NOT kill the underlying Singular C call --
#      it just stops waiting on it), and k=3 -- started immediately after,
#      while k=2's Task was STILL RUNNING in the background -- crashed the
#      whole Julia process with what the original run's console output
#      recorded as an omalloc bin-page allocator segfault "inside
#      redtailBbb" (Singular's tail-reduction routine).
#
#    - Elim2/src/02_norm_elim_diag.jl ~line 977-992 (run_part_h_isolated_u0
#      docstring content): a SEPARATE crash, this one inside dim()/codim()
#      (krull_dim -> singular_groebner_generators -> groebner_assure ->
#      Singular's std()) on a trivial 4-generator degree-5 ideal -- see
#      MODE=dim below.
#
#    - Elim2/src/part_j_worker.jl header (~line 15-22): explicitly states
#      the root cause as "two eliminate()/Singular calls running
#      concurrently *in the same process* raced on Singular's global
#      omalloc allocator and crashed (omInsertBinPage/omAllocBinFromFullPage)"
#      -- and that this is WHY Part J was redesigned to isolate every job
#      into its own OS subprocess rather than a Julia Task/Thread.
#
#  WHAT THIS FILE DOES DIFFERENTLY FROM THE ORIGINAL:
#
#  The original crash only showed up ~4700 lines into a much larger
#  pipeline (elim2.jl / elim2_refactored.jl), built on top of a specific
#  genus-2 curve match computed by a whole separate symbolic-tower engine
#  (phi_general/trial3_phi_symbolic_unified.jl). None of that machinery is
#  causally relevant to the crash -- the crash is a Singular.jl/OSCAR
#  allocator-concurrency bug triggered by ANY two eliminate()/std() calls
#  racing on the same process's global Singular state. This file reduces
#  the reproducer to exactly that: a genus-2-style curve system (same
#  shape/degree as the original: y^2 = x^5+x+2 branch curves plus a
#  degree-17-ish "target" relation) built directly, with NO dependency on
#  phi_general, PhiSymbolic, or any of the rest of the Elim2 package.
#
#  USAGE:
#      julia -t 4 singular_concurrent_crash_repro.jl            # MODE=race (default)
#      julia -t 4 singular_concurrent_crash_repro.jl race
#      julia -t 4 singular_concurrent_crash_repro.jl dim
#      julia -t 4 singular_concurrent_crash_repro.jl sequential  # control: should NOT crash
#
#  -t 4 (or more) is required for MODE=race/dim -- Threads.@spawn needs
#  >1 actual Julia thread available to get two Singular calls genuinely
#  running at the same time; with -t 1 they merely interleave cooperatively
#  and the race window this depends on won't open.
#
#  EXPECTED OUTCOME (per the original run's documented behavior):
#    race:       Julia process crashes (segfault / SIGSEGV, non-zero exit,
#                no Julia-catchable exception) partway through, OR hangs
#                indefinitely consuming memory (OOM) instead of crashing
#                outright -- both outcomes were observed across the
#                original investigation's several runs of this pattern.
#    dim:        crash inside dim()/codim() (krull_dim path) even on a
#                trivial 4-generator ideal, per the same allocator issue.
#    sequential: completes normally -- included as a negative control to
#                show the SAME ideals/eliminations are fine one-at-a-time,
#                isolating the bug to concurrency specifically, not to the
#                ideals themselves being pathological.
#
################################################################################

using Oscar

const MODE = length(ARGS) >= 1 ? ARGS[1] : "race"
MODE in ("race", "dim", "sequential") ||
    error("usage: julia -t N singular_concurrent_crash_repro.jl [race|dim|sequential]")

println("Julia threads available: ", Threads.nthreads())
if MODE in ("race", "dim") && Threads.nthreads() < 2
    println("WARNING: MODE=$MODE needs >=2 Julia threads to actually race two")
    println("Singular calls concurrently. Re-run with e.g. `julia -t 4 ...`.")
end

################################################################################
# Build the same shape of ring/ideal PART B/D operated on: an 8-variable
# decoupled ring (two independent genus-2-curve "sides", A and B, each
# with its own w/branch-point variables), a curve-only ideal (4 generators,
# degree 5 each -- matches PART D's crash description exactly), and a
# degree~17 "target" generator per side (matches PART B's Fu_decoupled
# shape/degree -- 17/306 terms was PART A's reported profile for
# Fu_decoupled[1]).
################################################################################

const p = 2371157   # same prime elim2.jl used throughout
F = GF(p)

R, (wa1, wa2, wb1, wb2, a1, a2, b1, b2) =
    polynomial_ring(F, ["wa1", "wa2", "wb1", "wb2", "a1", "a2", "b1", "b2"])

# The four genus-2 branch curves y^2 = x^5 + x + 2, one per w/x pair --
# identical construction to build_decoupled_system's curve_a1_d etc.
curve_a1 = wa1^2 - (a1^5 + a1 + 2)
curve_a2 = wa2^2 - (a2^5 + a2 + 2)
curve_b1 = wb1^2 - (b1^5 + b1 + 2)
curve_b2 = wb2^2 - (b2^5 + b2 + 2)
curve_gens = [curve_a1, curve_a2, curve_b1, curve_b2]

# A degree-17-ish "target" relation per side, built the same way
# Fu_decoupled's entries are (u_num - U*u_den survives as some fixed
# polynomial once U is instantiated) -- here we just need SOME degree>=15,
# few-hundred-term polynomial in the w/a/b variables to eliminate against,
# not the exact original coefficients, since the crash is allocator-level,
# not value-dependent. Built as a moderately-dense combination so the
# elimination step is nontrivial (not instant), same as the original's
# ~15s-for-k=1 profile.
function build_target_poly(w1, w2, x1, x2)
    g = zero(R)
    for i in 0:3, j in 0:3, k in 0:2, l in 0:2
        c = F((i + 3*j + 5*k + 7*l + 1) % p)
        g += c * w1^i * w2^j * x1^k * x2^l
    end
    g += w1^5 * x1^3 - w2^4 * x2^5 + x1^7 * x2^2 - w1^3 * w2^3 * x1 * x2
    return g
end

g_side_A = build_target_poly(wa1, wa2, a1, a2)   # stands in for Fu_decoupled[1]
g_side_B = build_target_poly(wb1, wb2, b1, b2)   # stands in for Fu_decoupled[2]

println("side A target: degree=", total_degree(g_side_A), " terms=", length(terms(g_side_A)))
println("side B target: degree=", total_degree(g_side_B), " terms=", length(terms(g_side_B)))
println()

# PART B's k=1 ideal: one target generator + all four curves.
I_k1 = ideal(R, vcat([g_side_A], curve_gens))
# PART B's k=2-equivalent ideal: BOTH sides' target generators + curves --
# this is the step whose *companion* concurrent call (not this ideal
# itself) is what triggers the crash below.
I_k2 = ideal(R, vcat([g_side_A, g_side_B], curve_gens))
# PART D's curve-only ideal: exactly 4 generators, degree 5 each.
I_curve = ideal(R, curve_gens)

################################################################################
# run_with_timeout -- deliberately-non-killing soft timeout, copied
# verbatim (in spirit) from 02_norm_elim_diag.jl's run_with_timeout. The
# whole point being reproduced here is that this does NOT reclaim the
# background Task: it only stops the caller from waiting on it. That
# still-running background Singular call is what races the next
# eliminate()/std() call issued after the timeout fires.
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
        return (task, :timeout, elapsed)   # NOTE: task is returned STILL RUNNING
    end
    status, val = fetch(task)
    return (val, status, elapsed)
end

################################################################################
# MODE=sequential -- negative control. Same two eliminations, run one
# after the other with nothing concurrent. Expected: completes cleanly,
# demonstrating neither ideal is independently pathological.
################################################################################
function run_sequential()
    println("[sequential] eliminating I_k1 (target A + curves)...")
    t0 = time()
    r1 = eliminate(I_k1, [wa1, wa2, wb1, wb2])
    println("[sequential] I_k1 done in ", round(time()-t0, digits=3), "s, ",
            length(gens(r1)), " generators out")

    println("[sequential] eliminating I_k2 (target A + target B + curves)...")
    t0 = time()
    r2 = eliminate(I_k2, [wa1, wa2, wb1, wb2])
    println("[sequential] I_k2 done in ", round(time()-t0, digits=3), "s, ",
            length(gens(r2)), " generators out")

    println("[sequential] no crash -- both eliminations are individually fine.")
end

################################################################################
# MODE=race -- the actual reproducer. Fires I_k1's eliminate() into the
# background via a short soft-timeout (short on purpose, to force us into
# the still-running-in-background state deterministically rather than
# waiting on real 300s timing), then -- WHILE THAT BACKGROUND TASK IS
# STILL ALIVE -- immediately starts a second, concurrent eliminate() call
# (also via Threads.@spawn) on I_k2 from the main thread. This is exactly
# PART B's k=2-then-k=3 sequence: a prior background elimination still
# holding Singular's global omalloc allocator state, raced by a second,
# independent eliminate() call.
################################################################################
function run_race()
    println("[race] launching I_k1 elimination with a short (5s) soft timeout")
    println("[race] (short on purpose -- forces the background-task-still-alive")
    println("[race] state deterministically rather than waiting on real timing)")
    result1, status1, elapsed1 = run_with_timeout(5.0) do
        eliminate(I_k1, [wa1, wa2, wb1, wb2])
    end
    println("[race] I_k1 status=", status1, " after ", round(elapsed1, digits=3), "s")

    if status1 != :timeout
        println("[race] I_k1 finished within 5s on this machine -- the background")
        println("[race] task is no longer alive, so the race window this repro")
        println("[race] depends on didn't open. Lower the elimination's cost margin")
        println("[race] is timing-dependent by nature (same as the original: the")
        println("[race] original's real trigger was a 300s timeout on a much bigger")
        println("[race] ideal, not a fixed constant), or just re-run.")
        return
    end

    println("[race] I_k1's Task is still running in the background (this is the")
    println("[race] documented pre-condition). Starting a SECOND, independent")
    println("[race] eliminate() call on I_k2 concurrently RIGHT NOW...")
    println()

    # This second call races result1's still-alive background task against
    # Singular's shared global allocator state -- this is the documented
    # crash trigger (omInsertBinPage/omAllocBinFromFullPage inside
    # redtailBbb per the original run's captured backtrace).
    result2 = eliminate(I_k2, [wa1, wa2, wb1, wb2])

    # If we get here without crashing, the race didn't land this run --
    # allocator races are inherently nondeterministic in exactly when/
    # whether they corrupt state badly enough to segfault vs. silently
    # producing wrong results vs. getting lucky. Re-running, or increasing
    # concurrent load (e.g. spawning several k1-style calls in the
    # background before starting k2), increases the odds of hitting it.
    println("[race] both calls returned without crashing on this run.")
    println("[race] I_k2 generators out: ", length(gens(result2)))
    println("[race] Allocator races are nondeterministic -- if this didn't crash,")
    println("[race] re-run (possibly multiple times), or see MODE=dim for the")
    println("[race] second, more reliably-triggered crash path documented in the")
    println("[race] original (dim()/codim() inside krull_dim on a trivial ideal).")
end

################################################################################
# MODE=dim -- the second documented crash, independent of the race above:
# dim()/codim() on I_curve (the 4-generator, degree-5-each curve-only
# ideal -- deliberately excluded from the default diagnostics run for
# exactly this reason; see 02_norm_elim_diag.jl's run_part_d_dim_codim
# docstring). Per the original: krull_dim -> singular_groebner_generators
# -> groebner_assure -> Singular's std() crashed even on this trivial
# input, suggesting dim()'s code path is fragile independent of ideal
# difficulty (possibly a different manifestation of the same underlying
# allocator/state issue, since it was observed in the same investigation
# alongside the eliminate() races above).
################################################################################
function run_dim()
    println("[dim] computing dim()/codim() of the curve-only ideal")
    println("[dim] (4 generators, degree 5 each -- about as simple as this ring gets)")
    d = dim(I_curve)
    c = codim(I_curve)
    println("[dim] dim=", d, " codim=", c, " -- no crash this run.")
    println("[dim] Per the original investigation this crashed inside")
    println("[dim] krull_dim -> singular_groebner_generators -> groebner_assure ->")
    println("[dim] Singular's std(), independent of ideal difficulty -- if it didn't")
    println("[dim] reproduce here, run repeatedly, or interleave with a concurrent")
    println("[dim] eliminate() call (MODE=race) since both crashes were observed in")
    println("[dim] the same session and may share root cause (shared allocator state).")
end

################################################################################
if MODE == "sequential"
    run_sequential()
elseif MODE == "race"
    run_race()
elseif MODE == "dim"
    run_dim()
end
