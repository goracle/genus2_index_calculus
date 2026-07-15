# ------------------------------------------------------------------------
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
# ------------------------------------------------------------------------

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
            all_bench_results[case_key] = run_fn(target_name, raw_coeff)
        catch e
            println("  ** BENCH CASE ", case_key, " FAILED -- ", sprint(showerror, e), " **")
            println("  ** continuing with remaining benchmark cases **")
            all_bench_results[case_key] = Dict{String,Any}("error" => sprint(showerror, e))
        end
    end
end

# ------------------------------------------------------------------------
# CROSS-BENCHMARK SUMMARY: is inflation universal? Does division
# consistently reproduce the Groebner eliminant? Is factor+divide
# consistently cheaper than Groebner elimination?
# ------------------------------------------------------------------------
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
        global n_cases_run += 1
        infl = res["infl_report"]
        if infl === nothing
            println("  ", rpad(case_key, 14),
                    " inflating=n/a  division_reproduces_all=n/a",
                    " (infl_report unavailable -- CHECK_GROEBNER=false for this run)")
            continue
        end
        n_infl = length(infl.inflating)
        n_infl > 0 && (global n_with_inflation += 1)
        all_reproduce = n_infl > 0 && all(v -> v.division_exact && (v.ideal_match || v.unit_match), infl.verification)
        n_infl > 0 && all_reproduce && (global n_division_always_reproduces += 1)
        println("  ", rpad(case_key, 14),
                " inflating=", rpad(n_infl, 3),
                " division_reproduces_all=", rpad(n_infl == 0 ? "n/a" : (all_reproduce ? "YES" : "NO"), 5),
                " factor(Res2)+div+verif=", round(infl.t_total_pipeline, digits=3), "s",
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







println()
println("===========================================================")
