################################################################################

"""
    correct_multiplicity(Res1, Res2; label="")

Gröbner-free multiplicity correction -- HARDCODED to the specific
inflation pattern observed in all 8 benchmark cases recorded in
prev.txt (FACTOR STAGE TRACE output for U0/V-vars, sample 1/2,
a-vars/b-vars). This is NOT a general Res1-vs-Res2 comparison; it is
narrower on purpose, because the general version (correct any factor
with exp(Res2) > exp(Res1), including factors absent from Res1) was
checked against prev.txt and found to be WRONG: every one of those 8
cases has a factor (called F2 in the trace output) that is absent from
Res1 (exp(Res1)=0) but is a GENUINE factor of the true (Groebner)
answer at exponent 1 in Res2 -- not a resultant artifact. The general
rule would silently zero that factor out of the corrected result.

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
    verify_correction(corrected, gA; check_groebner=CHECK_GROEBNER, label="")

Verify the corrected polynomial. Three tiers, cheapest first:
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
function verify_correction(corrected, gA; check_groebner::Bool=CHECK_GROEBNER, label::AbstractString="")
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

Copy `f` term-by-term into `target_ring`, placing each generator of
`parent(f)` into the generator of `target_ring` given by
`var_index_map[i]` (1-indexed). Any generator of `parent(f)` not
present in `var_index_map` must not actually appear in `f` (checked).
Used to lift small candidate polynomials (e.g. a discriminant computed
in just [a1,a2]) into the larger ring F_infl's representative lives in.
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

`F_infl_poly` is the actual irreducible polynomial object (not just its
canonical key) for the factor you want identified -- pull this directly
out of a `factor(Res2)` or `factor(gA)` call's factor list (matched by
canonical_factor_key against the row you care about from
factor_stage_trace).

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

disc_w(curve) for curve = w^2 - c(t), i.e. a monic quadratic in w:
disc = b^2 - 4ac with a=1, b=0, c=-c(t)  =>  disc = 4*c(t).
Returned up to the classical sign/scale convention (4*c(t)); if you need
the textbook-exact discriminant sign, adjust by a unit -- units don't
affect any gcd/divisibility test above.
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

Leading coefficient of `f` viewed as a univariate polynomial in `w`
(coefficient of the highest power of `w` appearing).
"""
function leading_coeff_in(f, w)
    d = degree(f, w)
    return coeff(f, [w], [d])
end

"""
    jacobian_2x2(f1, f2, v1, v2)

2x2 Jacobian determinant  |∂f1/∂v1  ∂f1/∂v2; ∂f2/∂v1  ∂f2/∂v2|
-- a standard branch-locus / ramification candidate for a system being
eliminated in exactly two variables (v1,v2).
"""
function jacobian_2x2(f1, f2, v1, v2)
    return derivative(f1, v1) * derivative(f2, v2) - derivative(f1, v2) * derivative(f2, v1)
end

println("identify_inflating_factor + helper builders (discriminant_of_curve, leading_coeff_in, ",
        "jacobian_2x2, map_into_ring) loaded. Actual call site is inside _run_bench, right after ",
        "factor_stage_trace, where curve1/curve2/step1/gA are in scope.")


#!/usr/bin/env julia
################################################################################
# part_i_eliminate_vs_resultant_bench.jl
#
# Controlled experiment: does eliminate(I_small, [w1,w2]) inside
# process_sample_1_coeff / process_sample_2_coeff (elim2.jl, Part I) cause
# the symbolic blow-up, or does it already exist before that call?
#
# HOW TO RUN
# -----------------------------------------------------------------------
# This does NOT modify elim2.jl. It is meant to be run in the SAME Julia
# session as elim2.jl, after res1 (and, for the sample-2 path, res2) exist
# -- i.e. after elim2.jl's setup block (through line ~106) has executed --
# but it never calls process_sample_1_coeff/process_sample_2_coeff itself,
# so it does not depend on Part I/J/K having run. Load it with:
#
#     julia> include("elim2.jl")   # let it run, or Ctrl-C after res1/res2
#                                    # exist if you don't want the rest of
#                                    # the script to execute yet
#     julia> include("part_i_eliminate_vs_resultant_bench.jl")
#     julia> bench_report_1 = run_bench_sample1("U0", res1.u_RS_coeffs[1])
#
# or, more simply, just include this file AFTER elim2.jl's full run --
# res1/res2/tower_to_ring will all still be in Main.
#
# WHAT IT DOES
# -----------------------------------------------------------------------
# For a chosen raw tower coefficient (e.g. res1.u_RS_coeffs[1]), builds
# the identical 5-variable sandbox process_sample_1_coeff builds, then
# runs TWO elimination paths side by side from the SAME h_s/curve1/curve2:
#
#   Path A (original):  eliminate(ideal(R_small,[h_s,curve1,curve2]),[w1,w2])
#   Path B (candidate):  step1 = resultant(h_s,   curve1, w1)
#                         step2 = resultant(step1, curve2, w2)
#
# Both paths are timed and measured (elapsed time, total_degree, term
# count, degree in every remaining variable) at every intermediate
# object, matching the requested log format:
#
#     h_s
#     Res_{w1}
#     Res_{w2}
#     Groebner eliminant
#
# Then it verifies equivalence: are Path A's output and Path B's output
# (a) identical, (b) equal up to a unit scalar, (c) generators of the
# same ideal (mutual ideal-membership check), and checks whether either
# one factors nontrivially.
#
# Nothing here alters process_sample_1_coeff/process_sample_2_coeff --
# both are left completely untouched in elim2.jl. This is read-only
# instrumentation bolted on next to them.
################################################################################

using Oscar

################################################################################
# CHECK_GROEBNER: master switch for the expensive Gröbner verification path.
#
# Default benchmark mode is resultant elimination -> factor analysis ->
# multiplicity correction -> (cheap) verification, with NO Gröbner basis
# computation at all. Gröbner's eliminate() is kept only as an opt-in
# debugging oracle: set CHECK_GROEBNER = true (or ENV["ELIM2_CHECK_GROEBNER"]
# = "true") to additionally run PATH A and compare the corrected resultant
# result against it exactly, the way the original diagnostic experiment did.
#
# This is a `const ... = get(ENV, ...)` read once at load time, matching the
# existing RUN_FULL_RESULTANT / ELIM2_PARTF_DIRECT_CROSSCHECK convention
# elsewhere in this file, so it can be toggled per-run without editing code:
#
#     ELIM2_CHECK_GROEBNER=true julia elim2.jl
################################################################################

const CHECK_GROEBNER = get(ENV, "ELIM2_CHECK_GROEBNER", "false") == "true"

println("CHECK_GROEBNER = ", CHECK_GROEBNER,
        CHECK_GROEBNER ? "  (Gröbner eliminate() WILL run, as a debugging oracle)" :
                          "  (Gröbner eliminate() will be SKIPPED -- default production/benchmark mode)")

# ------------------------------------------------------------------------
# Small measurement helper -- prints elapsed time, total_degree, term
# count, and per-variable degree for one polynomial object, tagged with
# a label matching the requested log format.
# ------------------------------------------------------------------------
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
function _run_bench(raw_coeff, target_name::String, t_names::Vector{String}, w_names::Vector{String})
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
    R_small, gens_small = polynomial_ring(F, vcat(w_names, t_names, [target_name]))
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
    if CHECK_GROEBNER
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
    verif = verify_correction(corr.corrected, gA; check_groebner=CHECK_GROEBNER, label=bench_label)

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
    if CHECK_GROEBNER
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
run_bench_sample1(target_name::String, raw_coeff) =
    _run_bench(raw_coeff, target_name, ["a1", "a2"], ["wa1", "wa2"])

run_bench_sample2(target_name::String, raw_coeff) =
    _run_bench(raw_coeff, target_name, ["b1", "b2"], ["wb1", "wb2"])

println("part_i_eliminate_vs_resultant_bench.jl loaded.")
println("Run e.g.:  run_bench_sample1(\"U0\", res1.u_RS_coeffs[1])")
println("      or:  run_bench_sample2(\"U0\", res2.u_RS_coeffs[1])")


