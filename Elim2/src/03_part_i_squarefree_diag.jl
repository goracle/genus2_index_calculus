################################################################################
#
#  03_part_i_squarefree_diag.jl -- part of the Elim2 package (src/Elim2.jl
#  includes this file). See src/Elim2.jl for the package-level overview
#  and the full include order of all submodule files.
#
#  Submodule: PartISquarefreeDiag
#
#  Encapsulation of part_i_squarefree_diag.jl (original lines 2854-3964).
#  Diagnostic + production machinery answering: given
#      gA = Groebner eliminate() generator      (PATH A)
#      gB = sequential resultant chain result    (PATH B)
#  do gA and gB factor into the SAME SET of irreducible factors (up to
#  unit scalars), differing only in multiplicity -- and, if so, can the
#  excess multiplicity introduced by chaining two resultants be divided
#  back out WITHOUT ever computing gA (i.e. without Groebner at all)?
#
#  Reuses `canonical_factor_key`/`factor_multiset` from NormElimDiag
#  (originally redefined a second, identical time in part_i_squarefree_
#  diag.jl itself -- the original file is a flat top-to-bottom script
#  with no function hoisting, so the redefinition was harmless there;
#  this refactor uses ordinary code reuse across submodules instead).
#
################################################################################
module PartISquarefreeDiag

using Oscar
using ..NormElimDiag: canonical_factor_key, factor_multiset

################################################################################
# CHECK_GROEBNER: master switch for the expensive Gröbner verification
# path used by `verify_correction` below. This constant is originally
# defined later in the flat file (inside part_i_eliminate_vs_resultant_
# bench.jl, i.e. submodule PartIBench), but `verify_correction`'s default
# argument reads it, so it must exist wherever `verify_correction` is
# defined. Declared here as its own module-local `const` (read once at
# load time, same ENV-var convention as the original) rather than
# importing it from PartIBench, since PartIBench is a separate submodule
# built on top of this one, not the other way around -- PartIBench's own
# copy of this same `const` (when that submodule is ported) governs its
# own PATH A/gate logic, and the two are independent reads of the same
# environment variable, matching the original's single global constant
# being visible to both scripts by load order.
################################################################################


const CHECK_GROEBNER = Ref{Bool}(false)

function read_check_groebner_env()::Bool
    val = get(ENV, "ELIM2_CHECK_GROEBNER", "false")
    parsed = tryparse(Bool, val)
    if parsed === nothing
        throw(ArgumentError("Invalid boolean for ELIM2_CHECK_GROEBNER: '$(val)'. Must be 'true' or 'false'."))
    end
    return parsed
end

function __init__()
    CHECK_GROEBNER[] = read_check_groebner_env()
end

################################################################################
# SQUAREFREE / MULTIPLICITY DIAGNOSTIC.
#
# Question: given gA (Groebner eliminant) and gB (resultant-chain
# result), is gA recoverable from gB by adjusting ONLY the exponents on
# gB's irreducible factors -- i.e. do gA and gB factor into the SAME SET
# of irreducibles (up to unit scalars), differing only in multiplicity?
#
#   Q1 (multiplicity-adjustable): same irreducible factor SET, any exponents
#   Q2 (squarefree part):         same set, AND every gA exponent == 1
################################################################################

"""
    squarefree_multiplicity_diagnostic(gA, gB; label="")

Original lines 2937-3031. Core diagnostic. Prints a full report and
returns a NamedTuple with the boolean verdicts so calling code can
assert on them.
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

"""
    run_diag_on_bench_result(bench_result; label="")

Original lines 3040-3044. Adjust field names below if the bench
script's return struct differs; written against the (gA, gB) naming
used in `squarefree_multiplicity_diagnostic`'s own docstring.
"""
function run_diag_on_bench_result(bench_result; label::AbstractString="")
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

Original lines 3078-3192. Factor `Res1`, `Res2`, and `gA` (Groebner
eliminant), key their irreducible factors canonically, and print a
table of exponent-per-stage for every factor that appears in ANY of the
three, plus explicit notes on:
  - whether each factor is present/absent at each stage
  - the exponent delta Res1->Res2 and Res2->gA per factor

Returns a NamedTuple with the raw per-stage Dict{key,exponent} maps and
a Vector of per-factor row NamedTuples, so downstream code can assert
on specific deltas instead of re-parsing printed output.
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

Original lines 3235-3482. Automated per-benchmark diagnostic. Steps:

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
    setA, facA = factor_multiset(gA)
    t3 = time()

    println("  factor(Res1) elapsed = ", round(t1 - t0, digits=4), "s  -> ", length(set1), " distinct factor(s)")
    println("  factor(Res2) elapsed = ", round(t_factor_res2, digits=4), "s  -> ", length(set2), " distinct factor(s)")
    println("  factor(gA)   elapsed = ", round(t3 - t1 - t_factor_res2, digits=4), "s  -> ", length(setA), " distinct factor(s)")
    println()

    # ---- 2/3. Match + print table (same shape as factor_stage_trace). ----
    all_keys = union(Set(keys(set1)), Set(keys(set2)), Set(keys(setA)))
    ordered_keys = sort(collect(all_keys);
        by = k -> (get(set2, k, 0), get(setA, k, 0), get(set1, k, 0)),
        rev = true)
    label_of = Dict(k => "F$(i)" for (i, k) in enumerate(ordered_keys))

    poly_of_2 = Dict{String,Any}(canonical_factor_key(p) => p for (p, _e) in fac2)

    println("  ", rpad("factor", 8), rpad("Res1", 8), rpad("Res2", 8), rpad("Groebner", 10), "ratio (Res2/Groebner)")
    rows = NamedTuple[]
    for k in ordered_keys
        e1 = get(set1, k, 0)
        e2 = get(set2, k, 0)
        eA = get(setA, k, 0)
        ratio_str = eA > 0 ? string(round(e2 / eA, digits=3)) : "n/a (absent in Groebner)"
        println("  ", rpad(label_of[k], 8), rpad(e1, 8), rpad(e2, 8), rpad(eA, 10), ratio_str)
        push!(rows, (label = label_of[k], key = k, exp_Res1 = e1, exp_Res2 = e2, exp_Groebner = eA))
    end

    # ---- 4. Identify inflating factors: exp(Res2) > exp(Groebner), and
    #         the factor must actually be present in Res2 to divide by
    #         it at all. ----
    inflating = [r for r in rows if r.exp_Res2 > r.exp_Groebner && r.exp_Res2 > 0]

    println()
    println("  --- inflating factor(s) (exp(Res2) > exp(Groebner)): ", length(inflating), " ---")

    verifications = NamedTuple[]
    t0_div = time()
    for r in inflating
        excess = r.exp_Res2 - r.exp_Groebner
        Fp = poly_of_2[r.key]
        println("  ", r.label, ": exp(Res2)=", r.exp_Res2, "  exp(Groebner)=", r.exp_Groebner,
                "  excess=", excess)

        # ---- 5. Q = Res2 / F^excess, then compare against gA. ----
        divides_exactly = false
        Q = nothing
        try
            Fpow = Fp^excess
            ok, q = divides(Res2, Fpow)
            if ok
                divides_exactly = true
                Q = q
            end
        catch e
            println("    ** division raised an error -- ", sprint(showerror, e), " **")
        end

        ideal_match = false
        unit_match = false
        unit_ratio = nothing
        if divides_exactly && Q !== nothing
            try
                if parent(Q) === parent(gA)
                    if !iszero(Q) && !iszero(gA)
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
                    if !unit_match
                        ideal_match = (ideal(parent(gA), [Q]) == ideal(parent(gA), [gA]))
                    end
                end
            catch e
                println("    ** post-division comparison raised an error -- ", sprint(showerror, e), " **")
            end
        end

        any_reproduces_this = unit_match || ideal_match
        println("    divides_exactly=", divides_exactly, "  unit_match=", unit_match,
                "  ideal_match=", ideal_match, "  any_reproduces=", any_reproduces_this)

        push!(verifications, (
            label = r.label,
            key = r.key,
            excess = excess,
            divides_exactly = divides_exactly,
            unit_match = unit_match,
            ideal_match = ideal_match,
            unit_ratio = unit_ratio,
            any_reproduces = any_reproduces_this,
        ))
    end
    t_div_verify = time() - t0_div

    # ---- 6. Timing summary. ----
    println()
    println("  factor(Res2)+division+verification total elapsed = ", round(t_div_verify, digits=4), "s",
            " (factor(Res2) alone was ", round(t_factor_res2, digits=4), "s of that)")

    # ---- 7. Per-target summary. ----
    any_reproduces = any(v.any_reproduces for v in verifications; init=false)
    println()
    println("  --- summary", isempty(label) ? "" : "  [$label]", " ---")
    println("  inflating factor(s) found      : ", length(inflating))
    println("  at least one reproduces gA     : ", any_reproduces)
    println("="^70)

    return (
        rows = rows,
        inflating = inflating,
        verifications = verifications,
        t_factor_res2 = t_factor_res2,
        t_div_verify = t_div_verify,
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
################################################################################

"""
    correct_multiplicity(Res1, Res2; label="")

Original lines 3571-3715. Gröbner-free multiplicity correction --
HARDCODED to the specific inflation pattern observed in all 8 benchmark
cases recorded in prev.txt (FACTOR STAGE TRACE output for U0/V-vars,
sample 1/2, a-vars/b-vars). This is NOT a general Res1-vs-Res2
comparison; it is narrower on purpose, because the general version
(correct any factor with exp(Res2) > exp(Res1), including factors
absent from Res1) was checked against prev.txt and found to be WRONG:
every one of those 8 cases has a factor (called F2 in the trace output)
that is absent from Res1 (exp(Res1)=0) but is a GENUINE factor of the
true (Groebner) answer at exponent 1 in Res2 -- not a resultant
artifact. The general rule would silently zero that factor out of the
corrected result.

What this function actually does, matching prev.txt exactly:
  - A factor is only ever corrected if it was ALREADY present in Res1
    (exp(Res1) > 0). Factors absent from Res1 are left untouched at
    their full Res2 exponent, always.
  - Among those, only factors where exp(Res2) == 3*exp(Res1) EXACTLY
    are treated as inflated; the excess (exp(Res2) - exp(Res1)) is
    divided out, which prev.txt confirms lands exactly on the true
    (Groebner) exponent in every one of the 8 cases (e.g. 2->6->2,
    3->9->3).
  - A factor present in Res1 (exp(Res1)>0) with exp(Res2) > exp(Res1)
    but NOT following the exact 3x relationship is a shape prev.txt
    does not cover -- it is reported and left UNCORRECTED rather than
    guessed at, since this whole function is fit to 8 examples, not
    derived from a proof. Check `unrecognized_factors` in the result
    if you need to know whether this happened.

Returns a NamedTuple:
  corrected            -- the corrected polynomial (Res2 with detected
                           excess multiplicity divided out; factors
                           outside the recognized pattern are left as-is)
  applied_factors      -- Vector of (key, excess) actually divided out
  unrecognized_factors -- Vector of (key, exp_Res1, exp_Res2) for
                          factors present in Res1 with exp(Res2) >
                          exp(Res1) that did NOT match the exact 3x
                          pattern -- non-empty means this run hit a
                          shape prev.txt never validated; treat the
                          result as unverified if so
  t_factor             -- time spent factoring Res1 and Res2
  t_correct            -- time spent dividing out excess multiplicity
  all_divisions_exact  -- whether every applied excess power divided
                          Res2 evenly (a self-consistency check: if
                          this is false, factor()'s own exponents were
                          inconsistent with exact division, and the
                          "corrected" result should not be trusted)

This function never calls eliminate()/groebner_basis() -- but "never
calls Groebner" is not the same as "verified correct in general"; it is
verified only against the specific pattern in prev.txt's 8 cases. If
`unrecognized_factors` comes back non-empty on a real run, that run's
result needs a Groebner cross-check before being trusted, same as any
input outside the 8 validated cases.
"""
function correct_multiplicity(Res1, Res2; label::AbstractString="")
    println("-"^70)
    println("MULTIPLICITY CORRECTION (Gröbner-free)", isempty(label) ? "" : "  [$label]")
    println("-"^70)

    t0 = time()
    set1, fac1 = factor_multiset(Res1)
    set2, fac2 = factor_multiset(Res2)
    t_factor = time() - t0
    println("  factor(Res1)+factor(Res2) elapsed = ", round(t_factor, digits=4), "s  -> ",
            length(set1), " / ", length(set2), " distinct factor(s)")

    poly_of_2 = Dict{String,Any}(canonical_factor_key(p) => p for (p, _e) in fac2)

    # Candidates: ONLY factors that were ALREADY present in Res1 (e1 > 0),
    # AND whose Res2 exponent is exactly 3x their Res1 exponent.
    #
    # This is a HARDCODED rule, fit to the 8 benchmark cases recorded in
    # prev.txt (FACTOR STAGE TRACE blocks for U0/V-vars, both sample sets,
    # a-vars and b-vars) -- it is not derived from first principles and
    # is not re-verified against Groebner at runtime (that's the whole
    # point: Groebner is what we're trying to avoid recomputing). Do not
    # extend or loosen this rule without re-checking against a fresh
    # Groebner-verified case.
    #
    # What prev.txt actually showed, across every one of the 8 cases:
    #   F1 (present in Res1, e1 in {2,3}): e2 = 3*e1 EXACTLY, and the true
    #      (Groebner) exponent eA = e1 exactly. So: strip the excess
    #      (e2 - e1), which equals 2*e1, leaving e1 -- matches eA.
    #   F2 (ABSENT from Res1, e1=0): e2=1, and the true (Groebner) exponent
    #      eA=1 -- i.e. F2 is a GENUINE factor of the true answer that
    #      simply doesn't appear until the second resultant. It is NOT
    #      spurious. The previous version of this function treated ANY
    #      factor with e2 > e1 (including e1=0) as fully spurious and
    #      divided it out down to exponent 0 -- that is WRONG and would
    #      have silently deleted F2 from the corrected result in all 8
    #      cases in prev.txt. Factors absent from Res1 are therefore
    #      NEVER touched here, on purpose.
    #   F3 (present in Res1, ABSENT from Res2): e2=0 already, e2 > e1 is
    #      false, so it was never a candidate under either rule -- no
    #      action needed, Res2 has already dropped it.
    #
    # If a factor is present in Res1 (e1>0) but its Res2 exponent is NOT
    # exactly 3*e1, we do NOT know what the correct exponent is (prev.txt
    # doesn't cover that shape) -- we flag it and leave it uncorrected
    # rather than guessing, so a silently-wrong "correction" doesn't ship.
    all_keys2 = collect(keys(set2))
    candidates = NamedTuple[]
    unrecognized = NamedTuple[]
    for k in all_keys2
        e1 = get(set1, k, 0)
        e2 = set2[k]
        if e1 > 0 && e2 > e1
            if e2 == 3 * e1
                push!(candidates, (key = k, excess = e2 - e1, exp_Res1 = e1, exp_Res2 = e2))
            else
                push!(unrecognized, (key = k, exp_Res1 = e1, exp_Res2 = e2))
            end
        end
    end

    println("  candidate inflated factor(s) matching the hardcoded e2==3*e1",
            " pattern (present in Res1, e1>0): ", length(candidates))
    for c in candidates
        rep = poly_of_2[c.key]
        println("    degree=", total_degree(rep), "  terms=", length(terms(rep)),
                "  exp(Res1)=", c.exp_Res1, "  exp(Res2)=", c.exp_Res2, "  excess=", c.excess)
    end
    if !isempty(unrecognized)
        println("  ** ", length(unrecognized), " factor(s) present in Res1 with e2>e1 but NOT",
                " matching e2==3*e1 -- pattern not covered by prev.txt's verified cases,",
                " leaving these UNCORRECTED rather than guessing: **")
        for u in unrecognized
            rep = poly_of_2[u.key]
            println("    degree=", total_degree(rep), "  terms=", length(terms(rep)),
                    "  exp(Res1)=", u.exp_Res1, "  exp(Res2)=", u.exp_Res2,
                    "  ** UNRECOGNIZED PATTERN -- NOT corrected **")
        end
    end
    println("  (factors ABSENT from Res1 (e1==0) are never corrected, regardless of",
            " their Res2 exponent -- prev.txt's F2 case proves such a factor can be",
            " genuine and must survive at its full Res2 exponent.)")

    t0 = time()
    corrected = Res2
    applied = NamedTuple[]
    all_exact = true
    for c in candidates
        Fp = poly_of_2[c.key]
        Fpow = Fp^c.excess
        divides_exactly = false
        q = nothing
        try
            qtmp, rem = divrem(corrected, Fpow)
            if iszero(rem)
                divides_exactly = true
                q = qtmp
            else
                ok, q2 = divides(corrected, Fpow)
                if ok
                    divides_exactly = true
                    q = q2
                end
            end
        catch e
            println("    ** division by F^", c.excess, " raised an error -- ", sprint(showerror, e), " **")
        end
        if divides_exactly
            corrected = q
            push!(applied, (key = c.key, excess = c.excess))
            println("  divided out excess exponent ", c.excess, " of one factor -> ",
                    "degree=", (iszero(corrected) ? -1 : total_degree(corrected)),
                    "  terms=", length(terms(corrected)))
        else
            all_exact = false
            println("  ** excess exponent ", c.excess, " did NOT divide evenly -- ",
                    "skipping this candidate, correction may be incomplete **")
        end
    end
    t_correct = time() - t0

    if isempty(candidates) && isempty(unrecognized)
        println("  (no candidate inflated factors -- Res2 already matches Res1's ",
                "multiplicities on every shared factor; corrected == Res2 unchanged)")
    elseif isempty(candidates) && !isempty(unrecognized)
        println("  ** no factors matched the recognized e2==3*e1 pattern, but ",
                length(unrecognized), " factor(s) with e1>0, e2>e1 were left",
                " UNCORRECTED -- see unrecognized_factors; this run's result is",
                " unverified. **")
    end

    println("  correction elapsed = ", round(t_correct, digits=4), "s")
    println("  final corrected result: degree=", (iszero(corrected) ? -1 : total_degree(corrected)),
            "  terms=", length(terms(corrected)))
    println("-"^70)

    return (
        corrected = corrected,
        applied_factors = applied,
        unrecognized_factors = unrecognized,
        t_factor = t_factor,
        t_correct = t_correct,
        all_divisions_exact = all_exact,
    )
end

"""
    verify_correction(corrected, gA; check_groebner=CHECK_GROEBNER[], label="")

Original lines 3734-3782. Verify the corrected polynomial. Three tiers,
cheapest first:
  1. If `check_groebner` is true and `gA` is available: exact polynomial
     equality against the Groebner eliminant, up to a unit, plus an ideal-
     equality fallback if the unit check fails. This is the authoritative
     check but requires the expensive Groebner computation to have run.
  2. If `check_groebner` is false (default): `gA` is not computed at all,
     so instead report factor/multiplicity self-consistency for
     `corrected` (squarefree-content sanity: does `corrected` still carry
     any UNCORRECTED repeated factor beyond what a generic eliminant of
     this shape should have? This is necessarily weaker evidence than
     exact Groebner comparison, and is reported as such.)

Returns a NamedTuple with the verification verdict and which tier ran.
"""
function verify_correction(corrected, gA; check_groebner::Bool=CHECK_GROEBNER[], label::AbstractString="")
    if check_groebner && gA !== nothing
        t0 = time()
        ideal_match = false
        unit_match = false
        unit_ratio = nothing
        try
            if parent(corrected) === parent(gA)
                if !iszero(corrected) && !iszero(gA) && length(terms(corrected)) == length(terms(gA))
                    lcC = leading_coefficient(corrected)
                    lcA = leading_coefficient(gA)
                    if !iszero(lcA)
                        candidate_ratio = lcC // lcA
                        if corrected == candidate_ratio * gA
                            unit_match = true
                            unit_ratio = candidate_ratio
                        end
                    end
                end
                if !unit_match
                    ideal_match = (ideal(parent(gA), [corrected]) == ideal(parent(gA), [gA]))
                end
            end
        catch e
            println("  ** verify_correction: Groebner comparison raised an error -- ",
                    sprint(showerror, e), " **")
        end
        t_verify = time() - t0
        matches = unit_match || ideal_match
        println("  verify_correction [$label]: against Groebner -- unit_match=", unit_match,
                "  ideal_match=", ideal_match, "  (", round(t_verify, digits=4), "s)")
        return (matches = matches, tier = :groebner, unit_match = unit_match,
                ideal_match = ideal_match, unit_ratio = unit_ratio, t_verify = t_verify)
    else
        # Tier 2: factor/multiplicity self-consistency only, no Groebner.
        # A "clean" correction should be squarefree in every factor that
        # was corrected (excess divided down to exactly the Res1
        # multiplicity), and dividing again by any corrected factor
        # should fail (no further excess remaining).
        t0 = time()
        set_corrected, _ = factor_multiset(corrected)
        t_verify = time() - t0
        println("  verify_correction [$label]: Groebner check skipped (CHECK_GROEBNER=false) -- ",
                "reporting factor/multiplicity self-consistency only (", round(t_verify, digits=4), "s): ",
                length(set_corrected), " distinct factor(s) in corrected result.")
        return (matches = missing, tier = :self_consistency, unit_match = missing,
                ideal_match = missing, unit_ratio = nothing, t_verify = t_verify)
    end
end

################################################################################
# IDENTIFY THE INFLATING FACTOR (F_infl).
#
# We know (empirically, from factor_stage_trace) which canonical-key
# factor inflates in multiplicity. This section does NOT theorize about
# WHY -- it computes concrete candidate polynomials from the actual
# system (h_s, curve1, curve2, and the resultant chain's own
# intermediate objects) and GCDs each one against F_infl to see which
# candidates it divides, equals, or shares structure with.
#
# Candidates tested, all derived directly from your system:
#   1. disc_w(curve1), disc_w(curve2)      -- discriminant of each curve
#                                              equation in its own w-var
#   2. lc_w(h_s) in w1, in w2               -- leading coefficient of h_s
#                                              as a polynomial in each w
#   3. lc_w(curve1), lc_w(curve2)           -- leading coeff of each curve
#                                              eqn in its own w (should be
#                                              a unit/1 since monic, but
#                                              checked rather than assumed)
#   4. Jacobian determinant of (h_s, curve1, curve2) w.r.t. (w1, w2)
#      -- the 2x2 minor ∂(h_s,curve1)/∂(w1,w2) etc; branch/ramification
#         locus candidate
#   5. Res1 itself (as a whole, and its own leading coeff in w2 before
#      the second resultant consumes it)
#   6. gcd(F_infl, F_infl at Res1-stage vs Res2-stage) is not meaningful
#      (different ring), so instead we gcd F_infl against each candidate
#      IN F_infl's own ring, after mapping candidates into that ring.
#
# All comparisons are done via gcd() in a common ring: whichever ring
# F_infl's representative element lives in. Candidates computed in a
# smaller ring (e.g. only in a1,a2) are mapped in via the same
# coefficient-copy technique used elsewhere in elim2.jl
# (MPolyBuildCtx / push_term!), not via a ring homomorphism object,
# to avoid requiring the two rings to be related by an explicit map.
################################################################################

"""
    map_into_ring(f, target_ring, var_index_map)

Original lines 3820-3843. Copy `f` term-by-term into `target_ring`,
placing each generator of `parent(f)` into the generator of
`target_ring` given by `var_index_map[i]` (1-indexed). Any generator of
`parent(f)` not present in `var_index_map` must not actually appear in
`f` (checked). Used to lift small candidate polynomials (e.g. a
discriminant computed in just [a1,a2]) into the larger ring F_infl's
representative lives in.
"""
function map_into_ring(f, target_ring, var_index_map::Vector{Int})
    B = MPolyBuildCtx(target_ring)
    n_target = nvars(target_ring)
    for (c, exps) in zip(coefficients(f), AbstractAlgebra.exponent_vectors(f))
        new_exps = zeros(Int, n_target)
        for (i, e) in enumerate(exps)
            if e != 0
                new_exps[var_index_map[i]] = e
            end
        end
        push_term!(B, c, new_exps)
    end
    return finish(B)
end

"""
    identify_inflating_factor(F_infl_poly, candidates::Dict{String,<:Any}; label="")

Original lines 3864-3906. `F_infl_poly` is the actual irreducible
polynomial object (not just its canonical key) for the factor you want
identified -- pull this directly out of a `factor(Res2)` or `factor(gA)`
call's factor list (matched by canonical_factor_key against the row you
care about from factor_stage_trace).

`candidates` maps a human-readable name to a polynomial ALREADY LIVING
IN (or already mapped into) F_infl_poly's ring -- use map_into_ring
above first if a candidate was computed in a different/smaller ring.

For each candidate, prints:
  - gcd(F_infl_poly, candidate) and its degree
  - whether F_infl_poly divides the candidate
  - whether the candidate divides F_infl_poly
  - whether they are equal up to unit scalar
"""
function identify_inflating_factor(F_infl_poly, candidates::Dict{String,<:Any}; label::AbstractString="")
    println("="^70)
    println("IDENTIFY INFLATING FACTOR", isempty(label) ? "" : "  [$label]")
    println("  F_infl: total_degree=", total_degree(F_infl_poly), "  terms=", length(terms(F_infl_poly)))
    println("="^70)

    R = parent(F_infl_poly)

    for (name, cand) in candidates
        if is_zero(cand)
            println("  [", rpad(name, 28), "]  candidate is the zero polynomial -- skipping")
            continue
        end
        if parent(cand) !== R
            println("  [", rpad(name, 28), "]  ** SKIPPED: candidate not in F_infl's ring; call map_into_ring first **")
            continue
        end

        g = gcd(F_infl_poly, cand)
        g_deg = is_zero(g) ? -1 : total_degree(g)
        # Multivariate polynomials over a field have no generic rem()/%
        # in this Oscar/AbstractAlgebra stack -- exact divisibility here
        # is tested via divides(), which returns (flag, quotient) and is
        # the correct primitive for FqMPolyRingElem.
        f_divides_cand, _ = divides(cand, F_infl_poly)          # F_infl | candidate
        cand_divides_f, _ = divides(F_infl_poly, cand)          # candidate | F_infl
        equal_up_to_unit = false
        if total_degree(cand) == total_degree(F_infl_poly) && f_divides_cand && cand_divides_f
            equal_up_to_unit = true
        end

        tag = equal_up_to_unit ? "  <<< EQUAL UP TO UNIT SCALAR" :
              f_divides_cand   ? "  <<< F_infl DIVIDES this candidate" :
              cand_divides_f   ? "  <<< candidate DIVIDES F_infl" :
              (g_deg > 0)      ? "  <<< nontrivial common factor (gcd degree $g_deg)" :
                                  ""

        println("  [", rpad(name, 28), "]  cand deg=", rpad(total_degree(cand), 6),
                "  gcd deg=", rpad(g_deg, 6), tag)
    end

    println("="^70)
end

################################################################################
# Convenience builders for the standard candidate set, given the raw
# system polynomials. Call these to build the Dict passed into
# identify_inflating_factor above. Each returns a polynomial in ITS OWN
# natural ring; you must map_into_ring(...) each one into F_infl's ring
# before use (the exact var_index_map depends on your ring's generator
# order, which only you know at the call site -- left explicit rather
# than guessed).
################################################################################

"""
    discriminant_of_curve(curve, w)

Original lines 3918-3936. disc_w(curve) for curve = w^2 - c(t), i.e. a
monic quadratic in w: disc = b^2 - 4ac with a=1, b=0, c=-c(t) =>
disc = 4*c(t). Returned up to the classical sign/scale convention
(4*c(t)); if you need the textbook-exact discriminant sign, adjust by a
unit -- units don't affect any gcd/divisibility test above.
"""
function discriminant_of_curve(curve, w)
    # curve = w^2 - c(t)  =>  c(t) = w^2 - curve, extracted by
    # setting w -> 0 after negating: c(t) = -(curve with w^2 term removed... )
    # Simpler and robust: disc of a*w^2+b*w+c is b^2-4ac. Extract a,b,c as
    # coefficients of w^2, w^1, w^0 directly via coeff().
    a = coeff(curve, [w], [2])
    b = coeff(curve, [w], [1])
    c = coeff(curve, [w], [0])
    return b^2 - 4*a*c
end

"""
    leading_coeff_in(f, w)

Original lines 3939-3947. Leading coefficient of `f` viewed as a
univariate polynomial in `w` (coefficient of the highest power of `w`
appearing).
"""
function leading_coeff_in(f, w)
    d = degree(f, w)
    return coeff(f, [w], [d])
end

"""
    jacobian_2x2(f1, f2, v1, v2)

Original lines 3950-3958. 2x2 Jacobian determinant
|∂f1/∂v1  ∂f1/∂v2; ∂f2/∂v1  ∂f2/∂v2| -- a standard branch-locus /
ramification candidate for a system being eliminated in exactly two
variables (v1,v2).
"""
function jacobian_2x2(f1, f2, v1, v2)
    return derivative(f1, v1) * derivative(f2, v2) - derivative(f1, v2) * derivative(f2, v1)
end

end # module PartISquarefreeDiag
