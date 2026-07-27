println("PART J: The Assembly Line (Processing All Coefficients)")
println("===========================================================")

# ------------------------------------------------------------------------
# PARALLELIZED via separate OS processes, NOT Threads.@spawn.
#
# Part H already documented why: two eliminate()/Singular calls running
# concurrently *in the same process* raced on Singular's global omalloc
# allocator and crashed (omInsertBinPage/omAllocBinFromFullPage), because
# Threads.@spawn cannot preempt or truly isolate a blocking Singular C
# call. Each sandbox below is dispatched to its own `julia
# part_j_worker.jl` subprocess instead, so every eliminate() call gets
# its own address space / allocator state, and the crash mode Part H
# hit simply can't occur here. Results come back via Oscar's save/load
# through a persistent output file per job.
#
# All 8 jobs (4 targets x 2 samples) are independent -- none of the
# process_sample_*_coeff calls depend on each other -- but launching all
# 8 at once nearly OOM's (each Singular/Oscar subprocess is heavy), so
# they're run through a bounded worker pool instead, PART_J_MAX_WORKERS
# in flight at a time.
#
# Output files live in PART_J_OUTPUT_DIR (./tmp, next to this script),
# NOT the system /tmp -- and PERSIST across runs (no cleanup at the end)
# so that a re-run can skip any job whose output file already exists,
# rather than recomputing it.
# ------------------------------------------------------------------------

const PART_J_MAX_WORKERS = 4

num_u_coeffs = length(res1.u_RS_coeffs) - 1   # skip trivial leading "1"
num_v_coeffs = length(res1.v_RS_coeffs)

part_j_jobs = NamedTuple{(:sample, :target), Tuple{Int,String}}[]
for i in 1:num_u_coeffs
    push!(part_j_jobs, (sample = 1, target = "U$(i-1)"))
    push!(part_j_jobs, (sample = 2, target = "U$(i-1)"))
end
for i in 1:num_v_coeffs
    push!(part_j_jobs, (sample = 1, target = "V$(i-1)"))
    push!(part_j_jobs, (sample = 2, target = "V$(i-1)"))
end

const PART_J_OUTPUT_DIR = joinpath(ELIM2_ROOT_DIR, "tmp")
mkpath(PART_J_OUTPUT_DIR)
part_j_worker_path = joinpath(ELIM2_ROOT_DIR, "part_j_worker.jl")

# Attach each job's persistent output path up front, so the
# already-done check and the launch step agree on the filename.
part_j_jobs_full = map(part_j_jobs) do job
    outfile = joinpath(PART_J_OUTPUT_DIR, "sample$(job.sample)_$(job.target).oscar")
    (job = job, outfile = outfile)
end

part_j_todo = filter(jf -> !isfile(jf.outfile), part_j_jobs_full)
part_j_skipped = filter(jf -> isfile(jf.outfile), part_j_jobs_full)

if !isempty(part_j_skipped)
    println("  Skipping ", length(part_j_skipped), " job(s) with existing output file(s):")
    for jf in part_j_skipped
        println("    already have: ", jf.outfile)
    end
end
println("  Running ", length(part_j_todo), " of ", length(part_j_jobs_full),
        " sandboxes (up to ", PART_J_MAX_WORKERS, " concurrent worker(s))...")

# Bounded worker pool: keep at most PART_J_MAX_WORKERS subprocesses alive
# at once. Jobs are handed out in order; as each running slot's process
# exits it is checked for success/failure and the next queued job (if
# any) is launched in its place.
part_j_queue = collect(part_j_todo)
part_j_running = Vector{NamedTuple}()   # (job, outfile, proc)
part_j_next_idx = 1

function part_j_launch_next!()
    global part_j_next_idx
    part_j_next_idx > length(part_j_queue) && return nothing
    jf = part_j_queue[part_j_next_idx]
    part_j_next_idx += 1
    println("  Spinning up sandbox", jf.job.sample == 2 ? " (Sample 2)" : "", " for: ", jf.job.target)
    cmd = `julia $part_j_worker_path $(jf.job.sample) $(jf.job.target) $(jf.outfile)`
    proc = run(pipeline(cmd; stdout=stdout, stderr=stderr); wait=false)
    push!(part_j_running, (job = jf.job, outfile = jf.outfile, proc = proc))
    return nothing
end

for _ in 1:min(PART_J_MAX_WORKERS, length(part_j_queue))
    part_j_launch_next!()
end

while !isempty(part_j_running)
    # Poll for any finished process, harvest it, and backfill its slot.
    finished_idx = nothing
    while finished_idx === nothing
        for (idx, pr) in enumerate(part_j_running)
            if process_exited(pr.proc)
                finished_idx = idx
                break
            end
        end
        finished_idx === nothing && sleep(0.5)
    end
    pr = popat!(part_j_running, finished_idx)
    if !success(pr.proc)
        error("Part J worker failed for sample=$(pr.job.sample) target=$(pr.job.target) " *
              "(exit code $(pr.proc.exitcode)). See its output above for the Singular/Oscar backtrace.")
    end
    part_j_launch_next!()
end

println("  All Part J sandboxes finished. Loading results back in...")

# These arrays will hold our final, clean polynomials, same order as the
# original sequential loop: U0,U1,...,V0,V1,... interleaved sample1/sample2.
clean_sample_1 = Any[]
clean_sample_2 = Any[]

for jf in part_j_jobs_full
    if !isfile(jf.outfile)
        error("Part J: expected output file missing for sample=$(jf.job.sample) " *
              "target=$(jf.job.target): $(jf.outfile)")
    end
    # load() needs the *target* ring's context; each worker built its own
    # fresh 5-variable ring per job, so we just load whatever ring/element
    # Oscar serialized -- no shared parent required here since Part K
    # remaps everything into a common ring anyway via remap_to_final().
    result = load(jf.outfile)
    if jf.job.sample == 1
        push!(clean_sample_1, result)
    else
        push!(clean_sample_2, result)
    end
end

println("\nAssembly Line Finished!")
println("Sample 1 produced ", length(clean_sample_1), " clean polynomials.")
println("Sample 2 produced ", length(clean_sample_2), " clean polynomials.")





#!/usr/bin/env julia

################################################################################
#
#  part_i_squarefree_diag.jl
#
#  Diagnostic for part_i_eliminate_vs_resultant_bench.jl.
#
#  Question: given
#      gA = Groebner eliminate() generator      (PATH A)
#      gB = sequential resultant chain result    (PATH B)
#  is gA recoverable from gB by adjusting ONLY the exponents on gB's
#  irreducible factors -- i.e. do gA and gB factor into the SAME SET of
#  irreducibles (up to unit scalars), differing only in multiplicity?
#
#  This is strictly weaker than "gA == squarefree_part(gB)" (which is the
#  special case where every gA exponent is forced to 1), so we check both:
#
#    Q1 (multiplicity-adjustable): same irreducible factor SET, any exponents
#    Q2 (squarefree part):         same set, AND every gA exponent == 1
#
#  Usage: include this file right after a PATH A / PATH B bench block has
#  run, with gA and gB bound to the two eliminant polynomials, e.g.:
#
#      gA = eliminate(I, [w1, w2])[1]
#      gB = res_w2   # final resultant-chain output
#      include("part_i_squarefree_diag.jl")
#      squarefree_multiplicity_diagnostic(gA, gB; label="U0 (a-vars)")
#
################################################################################

using Oscar

# canonical_factor_key(f) and factor_multiset(f) are already defined in
# 09_part_i_sandbox_factory.jl (included before this file, same module
# scope) -- both copies here were byte-identical, so they've been
# removed rather than redefined. See that file's docstrings for their
# documentation.

"""
    squarefree_multiplicity_diagnostic(gA, gB; label="")

Core diagnostic. Prints a full report and returns a NamedTuple with the
boolean verdicts so calling code can assert on them.
"""
function squarefree_multiplicity_diagnostic(gA, gB; label::AbstractString="")
    println("="^70)
    println("SQUAREFREE / MULTIPLICITY DIAGNOSTIC", isempty(label) ? "" : "  [$label]")
    println("="^70)

    t0 = time()
    setA, facA = factor_multiset(gA)
    setB, facB = factor_multiset(gB)
    t_elapsed = time() - t0

    keysA = Set(keys(setA))
    keysB = Set(keys(setB))

    only_in_A = setdiff(keysA, keysB)
    only_in_B = setdiff(keysB, keysA)
    shared    = intersect(keysA, keysB)

    same_support = isempty(only_in_A) && isempty(only_in_B)

    println("  factor() elapsed (both sides) = ", round(t_elapsed, digits=4), "s")
    println("  PATH A (Groebner eliminant): ", length(keysA), " distinct irreducible factor(s)")
    println("  PATH B (resultant chain)   : ", length(keysB), " distinct irreducible factor(s)")
    println()

    if !isempty(only_in_A)
        println("  ** factors present in A but NOT in B (", length(only_in_A), "): **")
        for k in only_in_A
            println("       exponent in A = ", setA[k])
        end
    end
    if !isempty(only_in_B)
        println("  ** factors present in B but NOT in A (", length(only_in_B), "): **")
        for k in only_in_B
            println("       exponent in B = ", setB[k])
        end
    end

    println()
    println("  --- shared irreducible factors: exponent comparison ---")
    println("  ", rpad("factor total_degree", 22), rpad("exp in A", 10), rpad("exp in B", 10), "ratio (B/A)")
    all_exponents_match_1_in_A = true
    ratios = Float64[]
    for k in sort(collect(shared); by = kk -> setA[kk])
        eA = setA[k]
        eB = setB[k]
        # recover degree for display by re-parsing one term isn't cheap;
        # instead just report exponents, which is what matters here.
        push!(ratios, eB / eA)
        if eA != 1
            all_exponents_match_1_in_A = false
        end
        println("  ", rpad("(see key)", 22), rpad(eA, 10), rpad(eB, 10), round(eB/eA, digits=3))
    end

    # Q1: multiplicity-adjustable recovery.
    # gA is recoverable from gB by adjusting ONLY exponents iff they share
    # exactly the same set of irreducible factors (no factor appears in
    # one and not the other), regardless of what those exponents are.
    q1_multiplicity_adjustable = same_support

    # Q2: strict squarefree-part relationship.
    # gA == squarefree_part(gB) iff (Q1 holds) AND every exponent in A is 1.
    q2_is_squarefree_part_of_B = same_support && all_exponents_match_1_in_A

    println()
    println("  --- verdicts ---")
    println("  Q1 (same irreducible-factor SET; multiplicities may differ freely): ",
            q1_multiplicity_adjustable ? "TRUE  -- gA IS recoverable from gB by re-exponentiating factors" :
                                          "FALSE -- gA has/lacks factors that gB lacks/has; no exponent adjustment can fix this")
    println("  Q2 (gA is exactly the squarefree part of gB, i.e. all A-exponents == 1): ",
            q2_is_squarefree_part_of_B ? "TRUE" : "FALSE")

    if q1_multiplicity_adjustable && !q2_is_squarefree_part_of_B
        println("  => gA is a *non-trivial reweighting* of gB's factors (not simply squarefree-part(gB)).")
        println("     Exponent map (A -> B): ", Dict(k => (setA[k], setB[k]) for k in shared))
    end

    println("="^70)

    return (
        same_support = same_support,
        q1_multiplicity_adjustable = q1_multiplicity_adjustable,
        q2_is_squarefree_part_of_B = q2_is_squarefree_part_of_B,
        exponents_A = setA,
        exponents_B = setB,
        only_in_A = only_in_A,
        only_in_B = only_in_B,
    )
end

################################################################################
# Convenience wrapper matching the bench script's own naming: call this
# right after PATH A / PATH B are both computed inside
# part_i_eliminate_vs_resultant_bench.jl (gA = eliminate() generator,
# gB = final chained resultant, e.g. Res_{w2}).
################################################################################

function run_diag_on_bench_result(bench_result; label::AbstractString="")
    # Adjust field names below if the bench script's return struct differs;
    # written against the (gA, gB) naming used in this file's docstring.
    return squarefree_multiplicity_diagnostic(bench_result.gA, bench_result.gB; label=label)
end

################################################################################
# STAGE TRACE: localize exactly where multiplicity inflation is introduced.
#
#   Res1 = resultant(h_s, curve1, w1)          -- eliminate w1 only
#   Res2 = resultant(Res1, curve2, w2)          -- eliminate w2, chained from Res1
#   gA   = Groebner eliminate() generator       -- eliminates both at once
#
# We factor all three, key every irreducible factor by canonical_factor_key
# (so "F1"/"F2" mean the same associate class across all three objects, not
# just whatever order factor() happens to emit), and print one row per
# factor showing its exponent at each stage. This answers, directly from
# data:
#   - is F2 present in Res1 already, and at what multiplicity?
#   - does the exponent change Res1 -> Res2 (inflation during 2nd resultant)?
#   - does it change Res2 -> Groebner (i.e. does Res2 already match Groebner,
#     meaning nothing is wrong after all)?
# No claim is made about WHY beyond what the numbers show.
################################################################################

"""
    factor_stage_trace(Res1, Res2, gA; label="")

Factor `Res1`, `Res2`, and `gA` (Groebner eliminant), key their irreducible
factors canonically, and print a table of exponent-per-stage for every
factor that appears in ANY of the three, plus explicit notes on:
  - whether each factor is present/absent at each stage
  - the exponent delta Res1->Res2 and Res2->gA per factor

Returns a NamedTuple with the raw per-stage Dict{key,exponent} maps and a
Vector of per-factor row NamedTuples, so downstream code can assert on
specific deltas instead of re-parsing printed output.
"""
function factor_stage_trace(Res1, Res2, gA; label::AbstractString="")
    println("="^70)
    println("FACTOR STAGE TRACE", isempty(label) ? "" : "  [$label]")
    println("  Res1 = resultant(h_s, curve1, w1)")
    println("  Res2 = resultant(Res1, curve2, w2)")
    println("  gA   = Groebner eliminate() generator")
    println("="^70)

    t0 = time()
    set1, fac1 = factor_multiset(Res1)
    t1 = time()
    set2, fac2 = factor_multiset(Res2)
    t2 = time()
    setA, facA = factor_multiset(gA)
    t3 = time()

    println("  factor(Res1) elapsed = ", round(t1 - t0, digits=4), "s  -> ", length(set1), " distinct factor(s)")
    println("  factor(Res2) elapsed = ", round(t2 - t1, digits=4), "s  -> ", length(set2), " distinct factor(s)")
    println("  factor(gA)   elapsed = ", round(t3 - t2, digits=4), "s  -> ", length(setA), " distinct factor(s)")
    println()

    all_keys = union(Set(keys(set1)), Set(keys(set2)), Set(keys(setA)))

    # Order factors for display by their (Res2 exponent, then gA exponent,
    # then Res1 exponent) descending, purely so the "big/interesting"
    # factors surface first. This is a display choice only; it carries no
    # mathematical meaning.
    ordered_keys = sort(collect(all_keys);
        by = k -> (get(set2, k, 0), get(setA, k, 0), get(set1, k, 0)),
        rev = true)

    # Assign short display labels F1, F2, F3, ... in this same order so the
    # printed table matches the "F1 / F2" language used in conversation.
    label_of = Dict(k => "F$(i)" for (i, k) in enumerate(ordered_keys))

    println("  ", rpad("factor", 8), rpad("Res1", 8), rpad("Res2", 8), rpad("Groebner", 10),
            rpad("Δ(1->2)", 10), "Δ(2->A)")
    rows = NamedTuple[]
    for k in ordered_keys
        e1 = get(set1, k, 0)
        e2 = get(set2, k, 0)
        eA = get(setA, k, 0)
        d12 = e2 - e1
        d2A = eA - e2
        flags = String[]
        e1 == 0 && push!(flags, "ABSENT in Res1")
        e2 == 0 && push!(flags, "ABSENT in Res2")
        eA == 0 && push!(flags, "ABSENT in Groebner")
        println("  ", rpad(label_of[k], 8), rpad(e1, 8), rpad(e2, 8), rpad(eA, 10),
                rpad(d12, 10), d2A, isempty(flags) ? "" : "   ** " * join(flags, ", ") * " **")
        push!(rows, (
            label = label_of[k],
            key = k,
            exp_Res1 = e1,
            exp_Res2 = e2,
            exp_Groebner = eA,
            delta_1_to_2 = d12,
            delta_2_to_A = d2A,
        ))
    end

    println()
    println("  --- localization ---")
    for r in rows
        if r.exp_Groebner == 0
            continue  # not part of the final answer; skip localization commentary
        end
        if r.delta_1_to_2 == 0 && r.delta_2_to_A == 0
            println("  ", r.label, ": exponent CONSTANT across all three stages (", r.exp_Res1, ") -- no inflation for this factor.")
        elseif r.delta_1_to_2 != 0 && r.delta_2_to_A == 0
            println("  ", r.label, ": inflation occurs ENTIRELY during the FIRST resultant (Res1) -- ",
                    "already at exponent ", r.exp_Res1, " by Res1, unchanged through Res2 and matches Groebner-vs-Res2 gap of 0.")
        elseif r.delta_1_to_2 == 0 && r.delta_2_to_A != 0
            verb = r.delta_2_to_A > 0 ? "inflation" : "deflation"
            println("  ", r.label, ": Res1 and Res2 AGREE (exponent ", r.exp_Res1,
                    ") -- all ", verb, " relative to Groebner is a Res2-vs-Groebner gap, not introduced by either resultant step relative to each other.")
        elseif sign(r.delta_1_to_2) == sign(r.delta_2_to_A) && r.delta_1_to_2 != 0
            # Same-sign deltas: the two steps genuinely compound rather than
            # cancel, so "accumulates" is the right word here.
            verb = r.delta_1_to_2 > 0 ? "inflation ACCUMULATES" : "deflation ACCUMULATES"
            println("  ", r.label, ": exponent CHANGES at both steps (Res1=", r.exp_Res1,
                    " -> Res2=", r.exp_Res2, " -> Groebner=", r.exp_Groebner,
                    ") -- ", verb, " across both resultant steps.")
        else
            # Opposite-sign deltas: the two steps move the exponent in
            # different directions. If they land back where they started
            # (net == 0) this is a round trip, not accumulation -- e.g.
            # inflated by the second resultant, then fully cancelled by
            # Groebner. Report the net change explicitly rather than
            # calling this "accumulation," which would be backwards.
            net = r.exp_Groebner - r.exp_Res1
            if net == 0
                println("  ", r.label, ": exponent CHANGES at both steps but NETS TO ZERO (Res1=", r.exp_Res1,
                        " -> Res2=", r.exp_Res2, " -> Groebner=", r.exp_Groebner,
                        ") -- Res2 inflates/deflates this factor and Groebner exactly cancels it back out; ",
                        "no net inflation relative to Res1, so Res1 alone already reflects the true multiplicity.")
            else
                dir = net > 0 ? "net INFLATION" : "net DEFLATION"
                println("  ", r.label, ": exponent CHANGES at both steps in OPPOSING directions (Res1=", r.exp_Res1,
                        " -> Res2=", r.exp_Res2, " -> Groebner=", r.exp_Groebner,
                        ") -- partial cancellation, with a ", dir, " of ", abs(net), " surviving overall.")
            end
        end
    end

    println("="^70)

    return (
        exponents_Res1 = set1,
        exponents_Res2 = set2,
        exponents_Groebner = setA,
        labels = label_of,
        rows = rows,
    )
end

################################################################################
# PART H2: INFLATION-VS-DIVISION DIAGNOSTIC (investigation only).
#
# Question: is the exponent inflation seen by factor_stage_trace (Res1 ->
# Res2 -> Groebner) universal across every benchmark target, or an
# accident of one degree-8 factor in one target? And when a factor
# inflates (exp(Res2) > exp(Groebner)), does DIVIDING Res2 by the excess
# power of that factor exactly reproduce the Groebner eliminant (up to
# ideal equality / a unit)?
#
# This does NOT change the elimination algorithm. It only factors the
# three already-computed objects (Res1, Res2, gA), matches factors
# exactly as factor_stage_trace already does, and -- for every factor
# whose exponent drops going from Res2 to Groebner -- performs an exact
# polynomial division and checks whether the quotient reproduces gA.
################################################################################

"""
    inflating_factor_division_diagnostic(Res1, Res2, gA; label="")

Automated per-benchmark diagnostic. Steps:

  1. Factor Res1, Res2, gA (timed).
  2. Match irreducible factors exactly via `canonical_factor_key`
     (same matching used by `factor_stage_trace`).
  3. Print one table row per matched factor: degree, term count, and
     exponent at each stage, plus deltas/ratio.
  4. Identify "inflating factors": exp(Res2) > exp(Groebner).
  5. For each inflating factor F, compute
         Q = Res2 / F^(exp(Res2) - exp(Groebner))
     via exact polynomial division, then check `ideal(Q) == ideal(gA)`
     and whether `Q == unit * gA` for some nonzero field-element unit.
  6. Print total timing of factor(Res2) + division + verification, for
     comparison against the Groebner elimination time already recorded
     by the caller.
  7. Print a concise per-target summary block.

Returns a NamedTuple with the raw per-factor rows and per-inflating-
factor verification results, so calling code can aggregate across all
eight benchmarks without re-parsing printed output.
"""
function inflating_factor_division_diagnostic(Res1, Res2, gA; label::AbstractString="")
    println("="^70)
    println("INFLATION-VS-DIVISION DIAGNOSTIC", isempty(label) ? "" : "  [$label]")
    println("  Res1 = resultant(h_s, curve1, w1)")
    println("  Res2 = resultant(Res1, curve2, w2)")
    println("  gA   = Groebner eliminate() generator")
    println("="^70)

    # ---- 1. Factor all three (timed individually; Res2's own timing is
    #         also reported separately below for the "replacement
    #         algorithm" cost comparison in step 6). ----
    t0 = time()
    set1, fac1 = factor_multiset(Res1)
    t1 = time()
    set2, fac2 = factor_multiset(Res2)
    t_factor_res2 = time() - t1
    t2 = time()
    setA, facA = factor_multiset(gA)
    t3 = time()

    println("  factor(Res1) elapsed = ", round(t1 - t0, digits=4), "s  -> ", length(set1), " distinct factor(s)")
    println("  factor(Res2) elapsed = ", round(t_factor_res2, digits=4), "s  -> ", length(set2), " distinct factor(s)")
    println("  factor(gA)   elapsed = ", round(t3 - t2, digits=4), "s  -> ", length(setA), " distinct factor(s)")
    println()

    # Build key -> actual polynomial object maps (needed for division,
    # unlike factor_stage_trace which only needs the exponent dicts).
    poly_of_1 = Dict{String,Any}(canonical_factor_key(p) => p for (p, _e) in fac1)
    poly_of_2 = Dict{String,Any}(canonical_factor_key(p) => p for (p, _e) in fac2)
    poly_of_A = Dict{String,Any}(canonical_factor_key(p) => p for (p, _e) in facA)

    # ---- 2. Match factors exactly as factor_stage_trace does. ----
    all_keys = union(Set(keys(set1)), Set(keys(set2)), Set(keys(setA)))
    ordered_keys = sort(collect(all_keys);
        by = k -> (get(set2, k, 0), get(setA, k, 0), get(set1, k, 0)),
        rev = true)
    label_of = Dict(k => "F$(i)" for (i, k) in enumerate(ordered_keys))

    # ---- 3. Print the requested table. ----
    println("  --- per-factor table ---")
    println("  ", rpad("factor", 6), rpad("degree", 8), rpad("terms", 8),
            rpad("exp(Res1)", 11), rpad("exp(Res2)", 11), rpad("exp(gA)", 9),
            rpad("d12", 6), rpad("d2A", 6), "ratio12")
    rows = NamedTuple[]
    for k in ordered_keys
        # Prefer the Res2 representative for degree/term-count display
        # (that's the object the division step will actually use); fall
        # back to Res1's or gA's representative if absent from Res2.
        rep = get(poly_of_2, k, get(poly_of_1, k, get(poly_of_A, k, nothing)))
        deg = rep === nothing ? -1 : total_degree(rep)
        nterms = rep === nothing ? -1 : length(terms(rep))

        e1 = get(set1, k, 0)
        e2 = get(set2, k, 0)
        eA = get(setA, k, 0)
        d12 = e2 - e1
        d2A = eA - e2
        ratio12 = e1 == 0 ? NaN : e2 / e1

        println("  ", rpad(label_of[k], 6), rpad(deg, 8), rpad(nterms, 8),
                rpad(e1, 11), rpad(e2, 11), rpad(eA, 9),
                rpad(d12, 6), rpad(d2A, 6),
                isnan(ratio12) ? "n/a" : round(ratio12, digits=3))

        push!(rows, (
            label = label_of[k],
            key = k,
            degree = deg,
            terms = nterms,
            exp_Res1 = e1,
            exp_Res2 = e2,
            exp_Groebner = eA,
            delta12 = d12,
            delta2G = d2A,
            ratio12 = ratio12,
        ))
    end
    println()

    # ---- 4. Identify inflating factors: exp(Res2) > exp(Groebner). ----
    inflating = filter(r -> r.exp_Res2 > r.exp_Groebner, rows)
    println("  --- inflating factors (exp(Res2) > exp(Groebner)): ", length(inflating), " found ---")
    for r in inflating
        println("    ", r.label, ": exp(Res2)=", r.exp_Res2, "  exp(Groebner)=", r.exp_Groebner,
                "  excess=", r.exp_Res2 - r.exp_Groebner)
    end
    println()

    # ---- 5. For each inflating factor: exact division + verification. ----
    verif_results = NamedTuple[]
    t_division_total = 0.0
    t_verification_total = 0.0

    R_gA = parent(gA)
    ideal_gA = nothing
    try
        ideal_gA = ideal(R_gA, [gA])
    catch e
        println("  ** could not build ideal(gA) for verification -- ", sprint(showerror, e), " **")
    end

    for r in inflating
        println("  --- dividing out inflating factor ", r.label, " (excess exponent ",
                r.exp_Res2 - r.exp_Groebner, ") ---")
        F = get(poly_of_2, r.key, nothing)
        if F === nothing
            println("    ** could not recover polynomial object for ", r.label, " from factor(Res2) -- skipping **")
            continue
        end

        excess = r.exp_Res2 - r.exp_Groebner
        t0d = time()
        Fpow = F^excess
        Q = nothing
        divides_exactly = false
        try
            q, rem = divrem(Res2, Fpow)
            if iszero(rem)
                divides_exactly = true
                Q = q
            else
                # Fall back to Oscar's divides() for a definitive exact
                # test in case divrem's remainder convention differs.
                ok, q2 = divides(Res2, Fpow)
                if ok
                    divides_exactly = true
                    Q = q2
                end
            end
        catch e
            println("    ** exact division raised an error -- ", sprint(showerror, e), " **")
        end
        t_div = time() - t0d
        t_division_total += t_div

        if !divides_exactly || Q === nothing
            println("    exact division Res2 / F^", excess, " did NOT divide evenly -- ",
                    "F^", excess, " is not actually a factor of Res2 at this exponent (inconsistent with factor()'s own exponent; reporting as-is).")
            push!(verif_results, (
                label = r.label, key = r.key, excess = excess,
                division_exact = false, ideal_match = false, unit_match = false, unit_ratio = nothing,
                t_division = t_div, t_verification = 0.0,
            ))
            println()
            continue
        end

        println("    division elapsed = ", round(t_div, digits=4), "s  -> Q: total_degree=",
                (iszero(Q) ? -1 : total_degree(Q)), "  terms=", length(terms(Q)))

        # ---- verify ideal(Q) == ideal(gA) ----
        t0v = time()
        ideal_match = false
        if ideal_gA !== nothing && parent(Q) === R_gA
            try
                ideal_match = (ideal(R_gA, [Q]) == ideal_gA)
            catch e
                println("    ** ideal(Q)==ideal(gA) check raised an error -- ", sprint(showerror, e), " **")
            end
        elseif parent(Q) !== R_gA
            println("    NOTE: parent(Q) != parent(gA) -- skipping ideal-equality check (reported as false).")
        end

        # ---- verify Q == unit * gA ----
        unit_match = false
        unit_ratio = nothing
        if parent(Q) === R_gA && !iszero(Q) && !iszero(gA) && length(terms(Q)) == length(terms(gA))
            lcQ = leading_coefficient(Q)
            lcA = leading_coefficient(gA)
            if !iszero(lcA)
                candidate_ratio = lcQ // lcA
                if Q == candidate_ratio * gA
                    unit_match = true
                    unit_ratio = candidate_ratio
                end
            end
        end
        t_verif = time() - t0v
        t_verification_total += t_verif

        if ideal_match
            println("    *** ideal(Q) == ideal(gA):  YES -- exact division reproduces the Groebner elimination ideal ***")
        else
            println("    ideal(Q) == ideal(gA):  NO")
        end
        if unit_match
            println("    *** Q == unit * gA:  YES  (unit = $unit_ratio) -- division reproduces gA up to a scalar ***")
        else
            println("    Q == unit * gA:  NO")
        end
        println("    verification elapsed = ", round(t_verif, digits=4), "s")

        push!(verif_results, (
            label = r.label, key = r.key, excess = excess,
            division_exact = true, ideal_match = ideal_match, unit_match = unit_match,
            unit_ratio = unit_ratio, t_division = t_div, t_verification = t_verif,
        ))
        println()
    end

    # ---- 6. Timing summary (factor(Res2) + division + verification). ----
    t_total_pipeline = t_factor_res2 + t_division_total + t_verification_total
    println("  --- timing: factor(Res2) + division + verification ---")
    println("    factor(Res2)  = ", round(t_factor_res2, digits=4), "s")
    println("    division      = ", round(t_division_total, digits=4), "s  (summed over ", length(inflating), " inflating factor(s))")
    println("    verification  = ", round(t_verification_total, digits=4), "s")
    println("    TOTAL         = ", round(t_total_pipeline, digits=4), "s")
    println("    (compare against the Groebner eliminate() time recorded separately by the caller " *
            "to see whether factor+divide is consistently cheaper -- a possible replacement for " *
            "Gröbner elimination after the resultant chain.)")
    println()

    # ---- 7. Concise summary block. ----
    any_reproduces = any(v -> v.division_exact && (v.ideal_match || v.unit_match), verif_results)
    println("  --- summary ---")
    println("  target ", label)
    println("  inflating factors: ", length(inflating))
    for (i, r) in enumerate(inflating)
        v = i <= length(verif_results) ? verif_results[i] : nothing
        println("    factor ", i, ":")
        println("      degree: ", r.degree)
        println("      Res1 exponent: ", r.exp_Res1)
        println("      Res2 exponent: ", r.exp_Res2)
        println("      Groebner exponent: ", r.exp_Groebner)
        println("      removed exponent: ", r.exp_Res2 - r.exp_Groebner)
        if v === nothing
            println("      division reproduces Groebner: NO (verification not run)")
        else
            reproduces = v.division_exact && (v.ideal_match || v.unit_match)
            println("      division reproduces Groebner: ", reproduces ? "YES" : "NO")
        end
    end
    if isempty(inflating)
        println("    (no inflating factors for this target -- exp(Res2) <= exp(Groebner) everywhere)")
    end
    println("="^70)

    return (
        rows = rows,
        inflating = inflating,
        verification = verif_results,
        t_factor_res2 = t_factor_res2,
        t_division_total = t_division_total,
        t_verification_total = t_verification_total,
        t_total_pipeline = t_total_pipeline,
        any_reproduces = any_reproduces,
    )
end

################################################################################
# PRODUCTION MULTIPLICITY-CORRECTION PIPELINE (Gröbner-free).
#
# Turns the diagnostic finding above (Res2 = Groebner-eliminant * F^excess,
# for some repeated factor F already visible after Res1) into an actual
# corrective step that does NOT need the Groebner eliminant to run at all.
#
# Self-consistency signal used instead of "compare against gA": a genuine
# spurious-multiplicity factor F is one that
#   (a) is already present in Res1 (it's an intrinsic factor of the
#       eliminant geometry, not an artifact manufactured by the second
#       resultant), AND
#   (b) has its exponent in Res2 grow relative to its exponent in Res1
#       specifically because Res2 = resultant(Res1, curve2, w2) resultants
#       Res1 against ANOTHER copy of the same branch locus -- i.e. gcd
#       structure between Res1 and curve2's discriminant/leading
#       coefficient predicts which factor(s) get re-counted.
#
# Concretely: for every irreducible factor F of Res2 whose exponent
# e2 = exp_Res2(F) exceeds e1 = exp_Res1(F) (its exponent already present
# after the FIRST resultant), the excess exponent (e2 - e1) is the
# candidate spurious multiplicity introduced purely by the second
# resultant step -- no Groebner computation needed to conjecture this,
# since it only compares Res1 and Res2 against each other.
#
# This mirrors the empirically-confirmed 3->9 case (excess = 9-3 = 6,
# which happened to reduce to the correct exponent-3 factor once divided
# down -- but nothing here hard-codes 3 or 9; it is read off e1/e2).
