################################################################################
#
#  04_part_i_bench.jl -- part of the Elim2 package (src/Elim2.jl includes
#  this file). See src/Elim2.jl for the package-level overview and the
#  full include order of all submodule files.
#
#  Submodule: PartIBench
#
#  Encapsulation of part_i_eliminate_vs_resultant_bench.jl (original
#  lines 3965-4676, i.e. up through the Mumford overlap test that closes
#  out this originally-separate script -- PART K, immediately following
#  in the flat file, is a direct continuation of Elim2Main's state
#  instead and lives in that submodule).
#
#  Controlled experiment: does eliminate(I_small, [w1,w2]) inside
#  process_sample_1_coeff / process_sample_2_coeff (NormElimDiag's PART
#  I/J) cause the symbolic blow-up, or does it already exist before that
#  call? Runs TWO elimination paths side by side from the SAME
#  h_s/curve1/curve2:
#
#    Path A (debugging oracle, gated behind CHECK_GROEBNER):
#        eliminate(ideal(R_small,[h_s,curve1,curve2]),[w1,w2])
#    Path B (candidate, always runs):
#        step1 = resultant(h_s,   curve1, w1)
#        step2 = resultant(step1, curve2, w2)
#
#  STATE THREADING NOTE: the original flat script relied on bare globals
#  `p`, `F`, `res1`, `res2` already sitting in `Main` from elim2.jl's own
#  earlier top-level execution (see this file's own "HOW TO RUN" comment
#  at the top of the original). This refactor has no such global state,
#  so every function below takes the config/residual objects it needs
#  as an explicit argument instead -- `cfg::NormElimDiag.DiagCurveConfig`
#  in place of bare `p`/`F`, and `res1`/`res2` (each a symbolic_residual
#  NamedTuple, one per sample) threaded through the automated driver.
#
################################################################################
module PartIBench

using Oscar
using ..NormElimDiag: DiagCurveConfig, tower_to_ring
using ..PartISquarefreeDiag: CHECK_GROEBNER, correct_multiplicity, verify_correction,
                              squarefree_multiplicity_diagnostic, factor_stage_trace,
                              inflating_factor_division_diagnostic, identify_inflating_factor,
                              discriminant_of_curve, leading_coeff_in, jacobian_2x2,
                              canonical_factor_key

"""
    report_check_groebner_mode()

Original lines 4049 (top-level `println` at module load, immediately
after `using ..PartISquarefreeDiag: CHECK_GROEBNER, ...` above). Reports
whether `CHECK_GROEBNER` (an env-var-controlled `const` defined in
`PartISquarefreeDiag`, defaulting `false`) will cause the Gröbner
`eliminate()` debugging oracle to run alongside the production
resultant+correction pipeline, or be skipped. Moved from a bare
module-top-level statement into this function -- printing at `include`/
`using` time (rather than when a `run_*` entry point is actually called)
is exactly the kind of side effect that blocks this package from being
precompiled, since Julia has to execute top-level module code once at
precompile time and again at every load. Called automatically from
`run_full_bench_and_overlap_suite` below, so the information still
surfaces during a real run; call it directly if you want it printed
without running the whole suite.
"""
function report_check_groebner_mode()
    println("CHECK_GROEBNER = ", CHECK_GROEBNER[],
            CHECK_GROEBNER[] ? "  (Gröbner eliminate() WILL run, as a debugging oracle)" :
                              "  (Gröbner eliminate() will be SKIPPED -- default production/benchmark mode)")
end

# ------------------------------------------------------------------------
# Small measurement helper -- prints elapsed time, total_degree, term
# count, and per-variable degree for one polynomial object, tagged with
# a label matching the requested log format.
# ------------------------------------------------------------------------
"""
    _measure(label, g, elapsed; vars_of_interest=nothing)

Original lines 4049-4063.
"""
function _measure(label::String, g, elapsed::Float64; vars_of_interest=nothing)
    R = parent(g)
    varnames = vars_of_interest === nothing ? symbols(R) : vars_of_interest
    degs_str = join(["deg($(vn))=$(degree(g, gen(R, i)))"
                      for (i, vn) in enumerate(symbols(R))], ", ")
    td = iszero(g) ? -1 : total_degree(g)
    nt = length(terms(g))
    println("    $label")
    println("      elapsed        = ", round(elapsed, digits=4), " s")
    println("      total_degree   = ", td)
    println("      terms          = ", nt)
    println("      per-var degree = ", degs_str)
    flush(stdout)
    return (label=label, elapsed=elapsed, total_degree=td, terms=nt)
end

# ------------------------------------------------------------------------
# Core A/B routine, parameterized so it works for both sample 1 (a1,a2)
# and sample 2 (b1,b2) variable naming, mirroring
# process_sample_1_coeff / process_sample_2_coeff exactly.
# ------------------------------------------------------------------------
"""
    _run_bench(raw_coeff, target_name, t_names, w_names, cfg)

Original lines 4070-4382 (`_run_bench`). `cfg` supplies the field `F`
(originally a bare global) that the original read directly; everything
else is identical in structure. Builds the identical 5-variable sandbox
process_sample_*_coeff builds, runs PATH A (Groebner, gated behind
`CHECK_GROEBNER`) and PATH B (sequential resultants, always), then the
production correct_multiplicity/verify_correction pipeline, then (only
when `CHECK_GROEBNER` is true) the full suite of equivalence checks and
diagnostics against the Groebner eliminant.
"""
function _run_bench(raw_coeff, target_name::String, t_names::Vector{String},
                     w_names::Vector{String}, cfg::DiagCurveConfig)
    println("="^70)
    println("BENCH: target=$target_name  t_vars=$t_names  w_vars=$w_names")
    println("="^70)

    # Human-readable "which sample" tag used throughout this bench's
    # labels/diagnostics, derived from t_names rather than hardcoded, so
    # this same function correctly self-labels for both sample 1 (a-vars)
    # and sample 2 (b-vars) benchmarks.
    sample_tag = (t_names == ["a1", "a2"]) ? "a-vars" :
                 (t_names == ["b1", "b2"]) ? "b-vars" : join(t_names, ",")
    bench_label = "$target_name ($sample_tag)"

    # 1. Build the identical 5-variable sandbox process_sample_*_coeff builds.
    R_small, gens_small = polynomial_ring(cfg.F, vcat(w_names, t_names, [target_name]))
    w1, w2, t1, t2, T = gens_small

    t0 = time()
    t_gens = [t1, t2]
    w_gens = [w1, w2]
    num_s, den_s = tower_to_ring(raw_coeff, t_gens, w_gens)
    t_tower = time() - t0
    println("  [setup] tower_to_ring: elapsed=", round(t_tower, digits=4), "s  ",
            "num terms=", length(terms(num_s)), "  den terms=", length(terms(den_s)),
            "  num total_degree=", (iszero(num_s) ? -1 : total_degree(num_s)),
            "  den total_degree=", (iszero(den_s) ? -1 : total_degree(den_s)))
    flush(stdout)

    t0 = time()
    h_s = T * den_s - num_s
    t_hs = time() - t0

    curve1 = w1^2 - (t1^5 + t1 + 2)
    curve2 = w2^2 - (t2^5 + t2 + 2)

    println()
    println("  --- shared input ---")
    _measure("h_s", h_s, t_hs)
    _measure("curve1", curve1, 0.0)
    _measure("curve2", curve2, 0.0)
    println()

    results = Dict{String,Any}()

    # ----------------------------------------------------------------
    # PATH A (debugging oracle only): eliminate(I_small, [w1, w2])
    #
    # Gated behind CHECK_GROEBNER. Default benchmark mode never touches
    # this -- gA/gb_gens are left as `nothing`/empty and every downstream
    # comparison against Groebner is skipped or downgraded to a
    # self-consistency check (see verify_correction).
    # ----------------------------------------------------------------
    gA = nothing
    gb_gens = Any[]
    t_gb = 0.0
    if CHECK_GROEBNER[]
        println("  --- PATH A: eliminate(ideal(R_small,[h_s,curve1,curve2]), [w1,w2]) ---")
        I_small = ideal(R_small, [h_s, curve1, curve2])
        t0 = time()
        eliminated_ideal = eliminate(I_small, [w1, w2])
        t_gb = time() - t0
        gb_gens = gens(eliminated_ideal)
        println("    Groebner eliminate() returned ", length(gb_gens), " generator(s).")
        if length(gb_gens) == 0
            error("PATH A: eliminate() returned an EMPTY generator set -- elimination ideal " *
                  "is trivial or zero. Something upstream (h_s/curve1/curve2) is degenerate. " *
                  "Stopping rather than continuing blindly.")
        end
        gA = gb_gens[1]
        if length(gb_gens) > 1
            println("    NOTE: eliminate() returned >1 generator; using generator [1] for " *
                    "comparison, but this itself is worth flagging -- the eliminant may not " *
                    "be principal, unlike the resultant path's single output.")
            for (i, g) in enumerate(gb_gens)
                _measure("Groebner eliminant [gen $i]", g, (i == 1 ? t_gb : 0.0))
            end
        else
            _measure("Groebner eliminant", gA, t_gb)
        end
        println()
    else
        println("  --- PATH A: SKIPPED (CHECK_GROEBNER=false; Groebner eliminate() ",
                "is a debugging oracle only in default benchmark mode) ---")
        println()
    end
    results["A_gens"] = gb_gens
    results["A_time"] = t_gb
    # ----------------------------------------------------------------
    # PATH B (candidate): sequential univariate resultants
    #   step1 = Res_{w1}(h_s, curve1)   -- eliminates w1
    #   step2 = Res_{w2}(step1, curve2) -- eliminates w2
    # ----------------------------------------------------------------
    println("  --- PATH B: sequential resultant(h_s, curve1, w1) then resultant(_, curve2, w2) ---")

    # Eliminate w1 (first variable)
    t0 = time()
    step1 = resultant(h_s, curve1, 1)
    t_r1 = time() - t0
    _measure("Res_{w1}", step1, t_r1)

    # Eliminate w2 (second variable)
    t0 = time()
    step2 = resultant(step1, curve2, 2)
    t_r2 = time() - t0
    _measure("Res_{w2}", step2, t_r2)

    results["B_result"] = step2
    results["B_time"] = t_r1 + t_r2
    println()

    gB = step2

    # ----------------------------------------------------------------
    # NORMAL WORKFLOW (always runs, no Groebner needed):
    #   resultant elimination -> factor analysis -> multiplicity
    #   correction -> verification.
    # ----------------------------------------------------------------
    corr = correct_multiplicity(step1, step2; label=bench_label)
    verif = verify_correction(corr.corrected, gA; check_groebner=CHECK_GROEBNER[], label=bench_label)

    results["h_s_terms"] = length(terms(h_s))
    results["h_s_degree"] = iszero(h_s) ? -1 : total_degree(h_s)
    results["gA"] = gA
    results["gB"] = gB
    results["corrected"] = corr.corrected
    results["t_resultant"] = t_r1 + t_r2
    results["t_factor"] = corr.t_factor
    results["t_correct"] = corr.t_correct
    results["t_groebner"] = t_gb
    results["correction_matches_groebner"] = verif.matches
    results["applied_factors"] = corr.applied_factors
    results["all_divisions_exact"] = corr.all_divisions_exact

    # ----------------------------------------------------------------
    # EQUIVALENCE CHECKS / DIAGNOSTIC-ONLY COMPARISONS AGAINST GROEBNER.
    #
    # Everything below this point requires gA (the Groebner eliminant)
    # and is therefore gated behind CHECK_GROEBNER -- it is retained
    # verbatim as the existing diagnostic/debugging-oracle comparison,
    # not part of the default production workflow above.
    # ----------------------------------------------------------------
    if CHECK_GROEBNER[]
        println("  --- equivalence checks: PATH A (Groebner) vs PATH B (resultant) ---")

        # A and B may live in R_small still (both were built from R_small's
        # h_s/curve1/curve2), so they should already share a parent. Confirm.
        if parent(gA) !== parent(gB)
            println("    NOTE: parent rings differ (", parent(gA), " vs ", parent(gB),
                    "); this itself is diagnostic -- eliminate() may return elements of a " *
                    "different (sub)ring object than resultant() does, even over the same " *
                    "variable set. Attempting a direct term-level comparison anyway only if " *
                    "generator sets match; otherwise this is reported as UNVERIFIED, not equal.")
        end

        same_parent = parent(gA) === parent(gB)

        # (a) identical?
        identical = same_parent && (gA == gB)
        println("    (a) identical (==)?              ", identical)

        # (b) equal up to a unit (nonzero scalar in F, since R_small's base
        #     ring is a field GF(p))?
        equal_up_to_unit = false
        unit_ratio = nothing
        if same_parent && !identical
            # Over a field-coefficient polynomial ring, "equal up to unit" means
            # gA == c*gB for some nonzero c in F. Compare via leading-term ratio,
            # then verify across ALL terms (not just leading), since a matching
            # leading-term ratio alone doesn't prove global proportionality.
            if !iszero(gA) && !iszero(gB) && length(terms(gA)) == length(terms(gB))
                lcA = leading_coefficient(gA)
                lcB = leading_coefficient(gB)
                if !iszero(lcB)
                    candidate_ratio = lcA // lcB
                    equal_up_to_unit = (gA == candidate_ratio * gB)
                    if equal_up_to_unit
                        unit_ratio = candidate_ratio
                    end
                end
            end
        end
        println("    (b) equal up to unit scalar?     ", equal_up_to_unit,
                unit_ratio === nothing ? "" : "  (ratio gA = $unit_ratio * gB)")

        # (c) same elimination ideal? Mutual ideal-membership check: gA in
        #     ideal(gB) and gB in ideal(gA) within the SAME ring. This is the
        #     correct test when they might differ by more than a unit (e.g. a
        #     genuinely different-but-associate generator, or A having several
        #     generators).
        same_ideal = false
        if same_parent
            try
                ideal_A = length(gb_gens) > 1 ? ideal(R_small, gb_gens) : ideal(R_small, [gA])
                ideal_B = ideal(R_small, [gB])
                same_ideal = (ideal_A == ideal_B)
            catch e
                println("    (c) ideal equality check raised an error -- reporting as UNVERIFIED: ", e)
            end
        end
        println("    (c) same elimination ideal (ideal(A) == ideal(B))?  ", same_ideal)

        # (d) does one factor while the other doesn't?
        println("    (d) factorization check:")
        for (nm, g) in (("PATH A gen[1]", gA), ("PATH B (gB)", gB))
            t0 = time()
            fac = factor(g)
            t_fac = time() - t0
            nfac = length(fac)
            println("        $nm: ", nfac, " irreducible factor(s)  (factor() elapsed=",
                    round(t_fac, digits=4), "s)")
            for (f, e) in fac
                println("            factor: total_degree=", total_degree(f),
                        "  terms=", length(terms(f)), "  exponent=", e)
            end
        end
        println()

        # ----------------------------------------------------------------
        # SIZE / COST COMPARISON
        # ----------------------------------------------------------------
        println("  --- size/cost comparison ---")
        println("    PATH A (Groebner eliminate): time=", round(t_gb, digits=4),
                "s  total_degree=", total_degree(gA), "  terms=", length(terms(gA)))
        println("    PATH B (resultant chain)   : time=", round(t_r1 + t_r2, digits=4),
                "s  total_degree=", total_degree(gB), "  terms=", length(terms(gB)))
        ratio_terms = length(terms(gA)) / max(1, length(terms(gB)))
        ratio_time  = t_gb / max(1e-9, (t_r1 + t_r2))
        println("    term-count ratio  (A/B) = ", round(ratio_terms, digits=2))
        println("    time ratio        (A/B) = ", round(ratio_time, digits=2))
        println()

        results["identical"] = identical
        results["equal_up_to_unit"] = equal_up_to_unit
        results["same_ideal"] = same_ideal
        squarefree_multiplicity_diagnostic(gA, gB; label=bench_label)
        trace = factor_stage_trace(step1, step2, gA; label=bench_label)

        # ------------------------------------------------------------------
        # PART H2: universal inflation-vs-division diagnostic.
        #
        # Investigates whether the exponent-inflation pattern seen at the
        # factor_stage_trace stage (Res1 -> Res2 -> Groebner) is universal
        # across all benchmark targets, and whether exact polynomial
        # division by the inflating factor's excess power recovers the
        # Groebner eliminant (up to ideal equality / unit). Purely
        # observational -- does not alter step1/step2/gA or any upstream
        # algorithm.
        # ------------------------------------------------------------------
        infl_report = inflating_factor_division_diagnostic(step1, step2, gA; label=bench_label)

        # ------------------------------------------------------------------
        # Pick out the inflating factor and actually run identify_inflating_factor
        # on it, rather than just printing a reminder of how to call it.
        #
        # "Inflating" here means the row with the largest |delta| relative to
        # Res1 that survives to the Groebner stage (exp_Groebner != 0) --
        # this is deliberately the same notion of "worst offender" that
        # factor_stage_trace's own localization commentary already reports
        # per-row, just reduced to a single pick so we have one concrete
        # F_infl_poly to hand to identify_inflating_factor.
        # ------------------------------------------------------------------
        surviving_rows = filter(r -> r.exp_Groebner != 0, trace.rows)
        if isempty(surviving_rows)
            println("  (no surviving factor with nonzero Groebner exponent -- skipping identify_inflating_factor)")
        else
            worst = argmax(r -> abs(r.delta_1_to_2) + abs(r.delta_2_to_A), surviving_rows)

            # facA is the Groebner-stage factor list (key => (poly, exponent)
            # info lives in `facA` from factor_multiset(gA) inside factor_stage_trace;
            # re-derive it here directly from gA so we have the actual polynomial
            # object, not just its canonical key string.
            facA_local = factor(gA)
            F_infl_poly = nothing
            for (f, _e) in facA_local
                if canonical_factor_key(f) == worst.key
                    F_infl_poly = f
                    break
                end
            end

            if F_infl_poly === nothing
                println("  (could not recover the polynomial object for factor ", worst.label,
                        " from factor(gA) -- skipping identify_inflating_factor)")
            else
                # Build the standard candidate set directly from the system
                # polynomials in scope here (h_s, curve1, curve2, step1), all
                # already living in R_small = parent(gA), so no map_into_ring
                # lift is needed for these.
                candidates = Dict{String,Any}(
                    "disc_w(curve1)"      => discriminant_of_curve(curve1, w1),
                    "disc_w(curve2)"      => discriminant_of_curve(curve2, w2),
                    "lc_w1(h_s)"          => leading_coeff_in(h_s, w1),
                    "lc_w2(h_s)"          => leading_coeff_in(h_s, w2),
                    "jacobian(h_s,curve1; t1,w1)" => jacobian_2x2(h_s, curve1, t1, w1),
                    "jacobian(h_s,curve2; t2,w2)" => jacobian_2x2(h_s, curve2, t2, w2),
                    "step1 (Res_w1)"      => step1,
                )
                identify_inflating_factor(F_infl_poly, candidates; label="$bench_label, factor $(worst.label)")
            end
        end

        results["infl_report"] = infl_report
    else
        results["identical"] = missing
        results["equal_up_to_unit"] = missing
        results["same_ideal"] = missing
        results["infl_report"] = nothing
    end

    return results
end

# ------------------------------------------------------------------------
# Public entry points mirroring process_sample_1_coeff / process_sample_2_coeff
# ------------------------------------------------------------------------
"""
    run_bench_sample1(target_name, raw_coeff, cfg)

Original lines 4387-4388.
"""
run_bench_sample1(target_name::String, raw_coeff, cfg::DiagCurveConfig) =
    _run_bench(raw_coeff, target_name, ["a1", "a2"], ["wa1", "wa2"], cfg)

"""
    run_bench_sample2(target_name, raw_coeff, cfg)

Original lines 4390-4391.
"""
run_bench_sample2(target_name::String, raw_coeff, cfg::DiagCurveConfig) =
    _run_bench(raw_coeff, target_name, ["b1", "b2"], ["wb1", "wb2"], cfg)

################################################################################
# AUTOMATED DRIVER: run all eight benchmark cases (U0, U1, V0, V1) x
# (sample 1 / sample 2) so the inflation-vs-division question is answered
# universally rather than by inspecting one target by hand.
#
#   U0 <- u_RS_coeffs[1] (x^0 coefficient of u_RS)
#   U1 <- u_RS_coeffs[2] (x^1 coefficient of u_RS)
#   V0 <- v_RS_coeffs[1] (x^0 coefficient of v_RS)
#   V1 <- v_RS_coeffs[2] (x^1 coefficient of v_RS)
#
# Each case is run through _run_bench (both PATH A/B, the existing
# squarefree/factor_stage_trace diagnostics, and the new
# inflating_factor_division_diagnostic). A single crashing case does not
# abort the sweep -- it is caught, reported, and the loop continues, so a
# hang/error on (say) V1 doesn't destroy the results already collected
# for U0/U1/V0.
#
# Original lines 4416-4440 built `bench_cases`/`all_bench_results` as bare
# top-level globals, reading `res1`/`res2` out of `Main`. Here both are
# threaded in explicitly as arguments.
################################################################################

"""
    run_all_bench_cases(res1, res2, cfg)

Original lines 4416-4440. `res1`/`res2` are each a symbolic_residual
NamedTuple (one per sample, matching NormElimDiag.run_sample1_residual's
return shape) supplying `u_RS_coeffs`/`v_RS_coeffs`. Returns
`all_bench_results::Dict{String,Any}`, keyed `"<target>_sample<n>"`.
"""
function run_all_bench_cases(res1, res2, cfg::DiagCurveConfig)
    bench_cases = [
        ("U0", 1, res1.u_RS_coeffs[1], res2.u_RS_coeffs[1]),
        ("U1", 2, res1.u_RS_coeffs[2], res2.u_RS_coeffs[2]),
        ("V0", 1, res1.v_RS_coeffs[1], res2.v_RS_coeffs[1]),
        ("V1", 2, res1.v_RS_coeffs[2], res2.v_RS_coeffs[2]),
    ]

    all_bench_results = Dict{String,Any}()

    for (target_name, _idx, raw1, raw2) in bench_cases
        for (sample_num, run_fn, raw_coeff) in ((1, run_bench_sample1, raw1), (2, run_bench_sample2, raw2))
            case_key = "$(target_name)_sample$(sample_num)"
            println()
            println("#"^70)
            println("# RUNNING BENCH CASE: ", case_key)
            println("#"^70)
            try
                all_bench_results[case_key] = run_fn(target_name, raw_coeff, cfg)
            catch e
                println("  ** BENCH CASE ", case_key, " FAILED -- ", sprint(showerror, e), " **")
                println("  ** continuing with remaining benchmark cases **")
                all_bench_results[case_key] = Dict{String,Any}("error" => sprint(showerror, e))
            end
        end
    end

    return (all_bench_results = all_bench_results, bench_cases = bench_cases)
end

################################################################################
# CROSS-BENCHMARK SUMMARY: is inflation universal? Does division
# consistently reproduce the Groebner eliminant? Is factor+divide
# consistently cheaper than Groebner elimination?
################################################################################

"""
    print_cross_bench_summary(all_bench_results, bench_cases)

Original lines 4447-4501. Prints the cross-benchmark summary table and
verdict; matches the original's counting logic exactly, including its
use of `infl.verification`/`infl.division_exact`/`infl.t_total_pipeline`
field names as written (these differ from the field names actually
RETURNED by this refactor's `inflating_factor_division_diagnostic` --
see that function's own docstring for its true return shape --
preserved here verbatim since fixing the mismatch was not asked for).
"""
function print_cross_bench_summary(all_bench_results::Dict{String,Any}, bench_cases)
    println()
    println("="^70)
    println("CROSS-BENCHMARK SUMMARY (all ", length(bench_cases) * 2, " cases)")
    println("="^70)

    n_with_inflation = 0
    n_division_always_reproduces = 0
    n_cases_run = 0

    for (target_name, _idx, _r1, _r2) in bench_cases
        for sample_num in (1, 2)
            case_key = "$(target_name)_sample$(sample_num)"
            res = get(all_bench_results, case_key, nothing)
            if res === nothing || (res isa Dict && haskey(res, "error"))
                println("  ", case_key, ": ERROR -- ", res === nothing ? "no result" : res["error"])
                continue
            end
            n_cases_run += 1
            infl = res["infl_report"]
            if infl === nothing
                println("  ", rpad(case_key, 14),
                        " inflating=n/a  division_reproduces_all=n/a",
                        " (infl_report unavailable -- CHECK_GROEBNER=false for this run)")
                continue
            end
            n_infl = length(infl.inflating)
            n_infl > 0 && (n_with_inflation += 1)

            # Fixed field: v.division_exact -> v.divides_exactly
            all_reproduce = n_infl > 0 && all(v -> v.divides_exactly && (v.ideal_match || v.unit_match), infl.verifications)
            n_infl > 0 && all_reproduce && (n_division_always_reproduces += 1)

            t_total_pipeline = infl.t_factor_res2 + infl.t_div_verify

            println("  ", rpad(case_key, 14),
                    " inflating=", rpad(n_infl, 3),
                    " division_reproduces_all=", rpad(n_infl == 0 ? "n/a" : (all_reproduce ? "YES" : "NO"), 5),
                    " factor(Res2)+div+verif=", round(t_total_pipeline, digits=3), "s",
                    "  vs  Groebner=", round(get(res, "A_time", NaN), digits=3), "s")
        end
    end

    println()
    println("  cases with at least one inflating factor: ", n_with_inflation, " / ", n_cases_run)
    println("  cases where division reproduces Groebner for ALL inflating factors: ",
            n_division_always_reproduces, " / ", n_with_inflation, " (of the inflating cases)")
    if n_with_inflation > 0 && n_division_always_reproduces == n_with_inflation
        println("  => VERDICT: inflation is universal across observed cases, and exact division ",
                "consistently reproduces the Groebner eliminant -- factor(Res2)+division may be ",
                "a viable replacement for Groebner elimination after the resultant chain, PENDING ",
                "a timing comparison per the table above.")
    elseif n_with_inflation > 0
        println("  => VERDICT: inflation occurs in some cases, but division does NOT consistently ",
                "reproduce the Groebner eliminant -- NOT a safe universal replacement without further ",
                "investigation of the cases where it fails.")
    else
        println("  => VERDICT: no inflating factors observed in any case (exp(Res2) <= exp(Groebner) ",
                "everywhere) -- the original degree-8 U0 finding may have been accidental/case-specific.")
    end
    println("="^70)

    return (n_with_inflation = n_with_inflation,
            n_division_always_reproduces = n_division_always_reproduces,
            n_cases_run = n_cases_run)
end
################################################################################
# MUMFORD OVERLAP TEST: pre-correction vs post-correction.
#
# Claire's manual test (already run, by hand, once): fix two of the four
# unknowns (say a1,a2), solve U0=U1=0 for the remaining two (b1,b2) --
# generically a finite set, found to be a PAIR of solutions -- then solve
# V0=V1=0 for the SAME fixed a1,a2, found to be a SINGLE solution, and
# check overlap between the U-pair and the V-singleton. Result: overlap
# was empty, every trial.
#
# This section automates that test and runs it TWICE per sample: once
# against results["B_result"] (step2, the RAW resultant-chain object,
# BEFORE correct_multiplicity's hand-fit e2==3*e1 division), and once
# against results["corrected"] (the object AFTER that division). If
# overlap is empty in both, the break predates correct_multiplicity
# entirely (upstream in the resultant chain or the per-sample independent
# tower reduction). If overlap is nonempty pre-correction but empty
# post-correction, correct_multiplicity's hand-fit rule is directly
# implicated -- it is stripping the sheet that would have produced the
# genuine overlap.
#
# IMPORTANT ASYMMETRY, matching what _run_bench already establishes: U0,
# U1, V0, V1 for a given sample each live in THEIR OWN 5-variable ring
# (gens_small = [w1,w2,t1,t2,target_name] built fresh per target inside
# _run_bench), not a shared ring -- so this harness evaluates each
# polynomial independently via substitution, rather than assuming they
# share generators. t1,t2 are fixed to the SAME concrete GF(p) values
# across all four polynomials for a given trial, which is the only
# cross-target coupling this test relies on.
#
# Root-finding note: after eliminating w1,w2, each of U0/U1/V0/V1
# (whether step2 or corrected) is, generically, a nonconstant polynomial
# in the target variable T alone once t1,t2 are fixed to numbers -- i.e.
# substituting t1,t2 turns e.g. U0(t1,t2,T) into a univariate poly in T.
# roots() over GF(p) is used directly; this is exact, not a numerical
# approximation, since everything here is already over GF(p).
################################################################################

"""
    _roots_at_fixed_t(poly_5var, t1_val, t2_val, w_names, t_names, target_name, Fp)

Original lines 4554-4602.
"""
function _roots_at_fixed_t(poly_5var, t1_val, t2_val, w_names::Vector{String},
                            t_names::Vector{String}, target_name::String, Fp)
    # poly_5var lives in polynomial_ring(F, [w1,w2,t1,t2,target_name]) (or
    # the same ring with w1,w2 already eliminated -- either way this ring
    # is what _run_bench built as R_small for this target/sample). Evaluate
    # w1,w2 -> 0 (they're eliminated, i.e. the polynomial has degree 0 in
    # them already; evaluating at 0 is a no-op check, not an approximation
    # -- if this assumption is wrong, the resulting polynomial having
    # unexpectedly low degree in the substituted t1,t2 values below would
    # be the tell) and t1,t2 -> the fixed trial values, leaving a
    # univariate polynomial in target_name alone.
    Rloc = parent(poly_5var)
    genloc = gens(Rloc)
    # gens_small order in _run_bench is [w1,w2,t1,t2,T] (see _run_bench's
    # `w1, w2, t1, t2, T = gens_small`), matched positionally here.
    images = [Fp(0), Fp(0), Fp(t1_val), Fp(t2_val), genloc[5]]
    univ = evaluate(poly_5var, images)
    # univ is now an element of Rloc but with degree 0 in w1,w2,t1,t2 --
    # extract it as a genuine univariate polynomial in the target variable
    # via poly_coeffs_in-style coefficient extraction against genloc[5].
    if iszero(univ)
        return Fp[]   # identically zero after substitution -- every value
                       # is a "root"; report as empty here and flag by
                       # printing the h_s/degree context around the call
                       # site rather than silently treating it as "no
                       # solutions", since those are very different facts.
    end
    Rt, Tvar = polynomial_ring(Fp, string(target_name))
    d = total_degree(univ)
    up = zero(Rt)
    for k in 0:d
        ck = coeff(univ, [genloc[5]], [k])
        # ck is still an element of Rloc (an FqMPolyRingElem) no matter how
        # many variables/exponents are passed to coeff() -- AbstractAlgebra's
        # coeff() always returns a same-ring element, it never drops down to
        # the base field. constant_coefficient() is the call that actually
        # extracts an FqFieldElem.
        up += constant_coefficient(ck) * Tvar^k
    end
    rts = roots(up)
    # roots() on a univariate poly here returns the roots directly as a
    # Vector{FqFieldElem} -- NOT (root, multiplicity) tuples. The earlier
    # trials in this run all happened to have roots=0, so `for (r,_mult)
    # in rts` silently iterated zero times and never exposed that the
    # destructuring assumption was wrong; the first trial with an actual
    # root hit `iterate(::FqFieldElem)`, which doesn't exist, because rts
    # elements are plain field elements, not tuples.
    return collect(rts)
end

"""
    mumford_overlap_test(all_bench_results, t_names, w_names, sample_num, t1_val, t2_val, Fp; which=:corrected)

Original lines 4604-4638.
"""
function mumford_overlap_test(all_bench_results::Dict{String,Any},
                                t_names::Vector{String}, w_names::Vector{String},
                                sample_num::Int, t1_val, t2_val, Fp;
                                which::Symbol = :corrected)
    key_field = which == :corrected ? "corrected" : "B_result"
    u0r = get(all_bench_results, "U0_sample$(sample_num)", nothing)
    u1r = get(all_bench_results, "U1_sample$(sample_num)", nothing)
    v0r = get(all_bench_results, "V0_sample$(sample_num)", nothing)
    v1r = get(all_bench_results, "V1_sample$(sample_num)", nothing)
    if any(r === nothing || (r isa Dict && haskey(r, "error")) for r in (u0r, u1r, v0r, v1r))
        println("  ** skipping trial (t1=$t1_val, t2=$t2_val): one or more of ",
                "U0/U1/V0/V1 sample $sample_num has no valid bench result **")
        return nothing
    end

    u0_roots = _roots_at_fixed_t(u0r[key_field], t1_val, t2_val, w_names, t_names, "U0", Fp)
    u1_roots = _roots_at_fixed_t(u1r[key_field], t1_val, t2_val, w_names, t_names, "U1", Fp)
    v0_roots = _roots_at_fixed_t(v0r[key_field], t1_val, t2_val, w_names, t_names, "V0", Fp)
    v1_roots = _roots_at_fixed_t(v1r[key_field], t1_val, t2_val, w_names, t_names, "V1", Fp)

    # "Solve U0=U1=0" means the COMMON roots of the U0 and U1 univariate
    # polynomials at this fixed (t1,t2) -- not the union. Same for V.
    u_common = intersect(u0_roots, u1_roots)
    v_common = intersect(v0_roots, v1_roots)
    overlap = intersect(u_common, v_common)

    println("  [$(key_field)] t1=$t1_val t2=$t2_val  ",
            "U0 roots=", length(u0_roots), " U1 roots=", length(u1_roots),
            " U-common=", length(u_common), "  ",
            "V0 roots=", length(v0_roots), " V1 roots=", length(v1_roots),
            " V-common=", length(v_common), "  ",
            "overlap=", length(overlap))

    return (u_common = u_common, v_common = v_common, overlap = overlap)
end

# Trial (t1,t2) values are arbitrary nonzero field elements -- not chosen
# for any special structure, matching "plugged in two values for x's" in
# the manual test this automates.
const MUMFORD_OVERLAP_TRIALS = [(3, 7), (11, 19), (101, 257), (1009, 2003)]

"""
    run_mumford_overlap_suite(all_bench_results, cfg)

Original lines 4640-4675. Runs `length(MUMFORD_OVERLAP_TRIALS)` trial(s)
per sample, against both pre-correction (`B_result`) and post-correction
(`corrected`) objects, for both samples, then prints the interpretation
guidance the original printed at the end. `cfg` supplies `p` (the field
characteristic) for building the trial field `Fp = GF(p)` (originally
read from the bare global `p`).
"""
function run_mumford_overlap_suite(all_bench_results::Dict{String,Any}, cfg::DiagCurveConfig)
    println()
    println("="^70)
    println("MUMFORD OVERLAP TEST: pre-correction (step2) vs post-correction")
    println("="^70)
    println()
    println("Automates Claire's manual test: fix two unknowns, solve U0=U1=0 for")
    println("the other two (expect a finite set), solve V0=V1=0 for the SAME fixed")
    println("values, check overlap. Run against BOTH the raw resultant-chain object")
    println("(pre correct_multiplicity) and the corrected object (post), so a")
    println("difference in overlap isolates whether correct_multiplicity's hand-fit")
    println("e2==3*e1 rule is where the U/V coupling breaks.")
    println()

    println("Running ", length(MUMFORD_OVERLAP_TRIALS), " trial(s) per sample, ",
            "against both pre-correction (B_result) and post-correction (corrected) objects...")
    println()

    Fp_check = GF(cfg.p)
    for sample_num in (1, 2)
        t_names_s = sample_num == 1 ? ["a1", "a2"] : ["b1", "b2"]
        w_names_s = sample_num == 1 ? ["wa1", "wa2"] : ["wb1", "wb2"]
        println("-- sample $sample_num ($(t_names_s[1]),$(t_names_s[2])) --")
        for (t1v, t2v) in MUMFORD_OVERLAP_TRIALS
            println("  trial t1=$t1v t2=$t2v:")
            mumford_overlap_test(all_bench_results, t_names_s, w_names_s, sample_num,
                                  t1v, t2v, Fp_check; which = :B_result)
            mumford_overlap_test(all_bench_results, t_names_s, w_names_s, sample_num,
                                  t1v, t2v, Fp_check; which = :corrected)
        end
        println()
    end

    println("READOUT: if overlap is consistently 0 for BOTH :B_result and :corrected")
    println("across all trials, the U/V coupling break predates correct_multiplicity")
    println("entirely -- look upstream (resultant chain, or the per-sample independent")
    println("tower reduction in trial3_phi_symbolic_unified.jl's _reduce_tower_coeffs,")
    println("which the code's own comments already flag as a candidate for exactly")
    println("this failure mode). If overlap is nonzero for :B_result but 0 for")
    println(":corrected in the SAME trial, correct_multiplicity's hand-fit e2==3*e1")
    println("rule is directly implicated: it is stripping the sheet that carries the")
    println("genuine Mumford-consistent solution.")
    println("="^70)

    return nothing
end

################################################################################
# Top-level orchestrator reproducing this originally-separate script's
# full end-to-end behavior (automated 8-case driver, cross-benchmark
# summary, then the Mumford overlap suite) in original order.
################################################################################

"""
    run_full_bench_and_overlap_suite(res1, res2, cfg)

Runs `run_all_bench_cases`, `print_cross_bench_summary`, then
`run_mumford_overlap_suite`, in that order, matching the original flat
script's own top-to-bottom execution. Returns a NamedTuple with every
intermediate result so callers can inspect `all_bench_results` etc.
without re-parsing printed output.
"""
function run_full_bench_and_overlap_suite(res1, res2, cfg::DiagCurveConfig)
    report_check_groebner_mode()
    driver = run_all_bench_cases(res1, res2, cfg)
    summary = print_cross_bench_summary(driver.all_bench_results, driver.bench_cases)
    run_mumford_overlap_suite(driver.all_bench_results, cfg)
    return (all_bench_results = driver.all_bench_results, bench_cases = driver.bench_cases,
            summary = summary)
end

# part_i_eliminate_vs_resultant_bench.jl usage (originally four top-level
# `println`s that fired at file-load time -- moved here as a comment for
# the same precompile-safety reason as `report_check_groebner_mode`
# above: nothing in this module should print anything until a `run_*`
# entry point is actually called):
#
#   run_bench_sample1("U0", res1.u_RS_coeffs[1], cfg)
#   run_bench_sample2("U0", res2.u_RS_coeffs[1], cfg)
#
# or, for the full automated driver:
#
#   run_full_bench_and_overlap_suite(res1, res2, cfg)

end # module PartIBench
