#!/usr/bin/env julia
#
# norm_elim_diag.jl
#
# Answers the supervisor's direct question and nothing else:
#
#     sample polynomial (per-sample num/den, NOT cross-multiplied)
#       -> remove wa2 -> degree? terms?
#       -> remove wa1 -> degree? terms?
#
# This measures whether per-sample norm elimination is actually cheap,
# as opposed to assuming it from the "smaller base size" argument alone.
#
# It deliberately does NOT build Fu/Fv (the cross-multiplied 8-variable
# equations), does NOT call groebner_basis, and does NOT touch the
# decoupled U/V construction. It is a narrow, fast diagnostic meant to
# run BEFORE committing to the fiber-product pipeline, so the "cheap"
# claim in the last response is checked against real numbers instead of
# asserted.
#
# Usage:
#   julia -t auto norm_elim_diag.jl
#
# Requires trial3_phi_symbolic_unified.jl in the same directory (or edit
# PHI_GENERAL_SRC below to point at it).

using Oscar

################################################################################
# Load the symbolic engine -- same include pattern as elim2.jl, but this
# repo layout has trial3_phi_symbolic_unified.jl sitting next to this
# script rather than under phi_general/src, so we check both locations.
################################################################################

const HERE = ELIM2_ROOT_DIR
const CANDIDATE_PATHS = [
    joinpath(HERE, "trial3_phi_symbolic_unified.jl"),
    joinpath(HERE, "phi_general", "src", "trial3_phi_symbolic_unified.jl"),
]
const ENGINE_PATH = findfirst(isfile, CANDIDATE_PATHS) === nothing ?
    error("trial3_phi_symbolic_unified.jl not found in: $CANDIDATE_PATHS") :
    CANDIDATE_PATHS[findfirst(isfile, CANDIDATE_PATHS)]

include(ENGINE_PATH)
using .PhiSymbolic

################################################################################
# Same curve / sample data as elim2.jl (sample 1, K=2 c=2 -- the smaller of
# the two samples, and sufficient to answer the question: is per-sample
# norm elimination cheap?). Extend to sample 2 at the bottom if sample 1
# looks tractable.
################################################################################

const p = 2371157
const F_POLY_ASC = [2, 1, 0, 0, 0, 1]   # y^2 = x^5 + x + 2, ascending coeffs
F = GF(p)

const K1, c1 = 2, 2
const fixed1 = Tuple{Int,Int}[]
const u0_1, u1_1, v0_1, v1_1 = 468873, 956582, 2168176, 2288437

println("Calling PhiSymbolic.symbolic_residual for sample 1 (K=$K1, c=$c1)...")
res1 = PhiSymbolic.symbolic_residual(K1, c1, fixed1, u0_1, u1_1, v0_1, v1_1, F_POLY_ASC, p)

if isempty(res1.u_RS_coeffs) || isempty(res1.v_RS_coeffs)
    error("sample 1 (K=$K1): construction failed or degenerate -- no u_RS/v_RS to test")
end

println("sample 1: deg(u_RS)=$(length(res1.u_RS_coeffs)-1)  deg(v_RS)=$(length(res1.v_RS_coeffs)-1)")
println()

################################################################################
# Target ring: JUST this sample's variables. 5 variables (wa1,wa2,a1,a2)
# plus we'll add U/V target vars only where needed for elimination via
# ideal-based eliminate(); the norm-elimination path below doesn't need
# them at all -- it works directly on (numerator,denominator) pairs.
################################################################################

R, (wa1, wa2, a1, a2) = polynomial_ring(F, ["wa1", "wa2", "a1", "a2"])

curve_a1 = wa1^2 - (a1^5 + a1 + 2)
curve_a2 = wa2^2 - (a2^5 + a2 + 2)

################################################################################
# Tower -> ring flattening -- uses tower_to_ring / _base_frac_to_ring /
# _reduce_frac as already defined in 01a_header_and_ring_map.jl (same
# module scope, included before this file). Not redefined here: the
# earlier copy was byte-identical and Julia's precompiler rejects
# redefining a method during module precompilation.
################################################################################

t_gens_1 = [a1, a2]
w_gens_1 = [wa1, wa2]

function map_coeffs(coeffs, t_gens, w_gens)
    n = length(coeffs)
    nums = Vector{Any}(undef, n)
    dens = Vector{Any}(undef, n)
    for i in 1:n
        nums[i], dens[i] = tower_to_ring(coeffs[i], t_gens, w_gens)
    end
    return nums, dens
end

println("Flattening sample 1's u_RS, v_RS coefficients into F[wa1,wa2,a1,a2]...")
u1_num, u1_den = map_coeffs(res1.u_RS_coeffs, t_gens_1, w_gens_1)
v1_num, v1_den = map_coeffs(res1.v_RS_coeffs, t_gens_1, w_gens_1)
println("done.")
println()

# Drop the trivial monic leading coefficient of u_RS (== 1, contributes
# nothing), same convention as elim2.jl.
const N_U_MATCH = length(u1_num) - 1

println("Per-sample (uncrossed) sizes BEFORE any elimination:")
for (label, nums, dens, n_use) in [
        ("u1", u1_num, u1_den, N_U_MATCH),
        ("v1", v1_num, v1_den, length(v1_num)),
    ]
    for i in 1:n_use
        n, d = nums[i], dens[i]
        println("  $label num[$i]: degree=", total_degree(n), " terms=", length(terms(n)),
                "   $label den[$i]: degree=", total_degree(d), " terms=", length(terms(d)))
    end
end
println()

################################################################################
# THE ACTUAL QUESTION.
#
# For a single coefficient's (num, den) pair, form
#
#     g = num - U*den        (U a placeholder value, not yet a new ring var --
#                              we work with num,den directly via the norm map
#                              on num/den's dependence on w, exactly as
#                              elim2.jl's norm_eliminate.jl section does, but
#                              measured here in isolation, one coefficient at
#                              a time, one w at a time.)
#
# Concretely: num and den are each degree<=1 in wa2 (confirmed structurally
# by _tower_to_ring: level=2 introduces wa2 linearly, level=1 introduces wa1
# linearly, and nothing downstream re-squares them since R is a FREE
# polynomial ring, not reduced mod wa_i^2-f(a_i), until we explicitly
# substitute that relation via the norm map). We eliminate wa2 first via
#
#     num = Pn + Qn*wa2,   den = Pd + Qd*wa2
#
#     N(num) := Pn^2 - Qn^2 * f(a2)      (multiply num by its "conjugate")
#     N(den) := Pd^2 - Qd^2 * f(a2)
#
# But num/den = U really means num - U*den = 0, i.e. we need the norm of
# (num - U*den) as a combined object, OR equivalently we track num and den
# SEPARATELY through the wa2-elimination and recombine after. The cleanest
# exact approach, avoiding introducing U before we've even checked cost:
# eliminate wa2 from the PAIR (num,den) by rationalizing the fraction --
# multiply num/den by conj(den)/conj(den):
#
#     num/den = num*conj(den) / (den*conj(den)) = num*conj(den) / N(den)
#
# num*conj(den) is still linear in wa2 (linear * linear can be degree 2,
# but conj(den) = Pd - Qd*wa2, so num*conj(den) generally IS degree 2 in
# wa2 -- so this does NOT trivially collapse; we must actually take the
# norm of the whole numerator too). This is exactly the doubling step the
# supervisor is asking to see measured, not assumed. So:
#
#     new_num := N(num) = Pn^2 - Qn^2*f(a2)     [rationalizes num alone]
#     new_den := N(den) = Pd^2 - Qd^2*f(a2)
#
# is WRONG in general because num/den != N(num)/N(den) unless num,den share
# the same conjugation structure consistently -- the correct rationalization
# multiplies num/den by conj(den)/conj(den), giving
#
#     num*conj(den) / N(den)
#
# and num*conj(den) must then itself be split into its own P',Q' (linear in
# wa2 gone -- wait: num*conj(den) = (Pn+Qn*wa2)(Pd-Qd*wa2)
#            = Pn*Pd - Pn*Qd*wa2 + Qn*Pd*wa2 - Qn*Qd*wa2^2
#            = (Pn*Pd - Qn*Qd*f(a2))  +  (Qn*Pd - Pn*Qd)*wa2
#
# using wa2^2 = f(a2). This IS still linear in wa2 (the algebra works out
# because conjugation is a ring homomorphism on this quadratic extension),
# so num*conj(den) reduces to a new (P'',Q'') pair, still linear in wa2,
# same shape as before -- it has NOT eliminated wa2, only rationalized the
# denominator down to N(den) (wa2-free). To fully eliminate wa2 from the
# EQUATION num - U*den = 0, form:
#
#     h := num - U*den = (Pn - U*Pd) + (Qn - U*Qd)*wa2
#     N(h) = (Pn - U*Pd)^2 - (Qn - U*Qd)^2 * f(a2)
#
# This is the correct, single, exact norm elimination of wa2 from the
# matching equation itself (treating U as an extra indeterminate rather
# than trying to eliminate wa2 from num,den separately, which doesn't by
# itself remove wa2 from the equation num=U*den). We measure N(h)'s
# degree/terms, then repeat for wa1 on the result.
################################################################################

# f(a) = a^5 + a + 2, evaluated symbolically at whichever anchor variable
f_of(a) = a^5 + a + 2

# CORRECTNESS-CRITICAL FIX (found by sympy sanity check before running this
# on real data -- see sanity_check.py / sanity_check2.py alongside this
# file): h0 = num - U*den is linear in wa1 ALONE and linear in wa2 ALONE,
# but NOT jointly -- it has a genuine wa1*wa2 cross term, because num's
# wa2-coefficient itself contains a wa1 term (tower structure: the level-2
# recursion produces n1*d0*wa2 where d0 already carries wa1). Squaring the
# wa2-coefficient to take the norm over wa2 therefore produces a wa1^2
# term. In the FREE polynomial ring R (not reduced mod wa1^2-f(a1)), that
# wa1^2 does not automatically collapse -- it just sits there, so h1 is no
# longer linear in wa1, and the next norm step is on a degree-2-in-wa1
# polynomial instead of degree-1. Without reducing wa_i^2 -> f(a_i) after
# EVERY norm step, split_linear's degree<=1 assumption silently breaks
# (or, worse, in a language that doesn't assert on it, silently proceeds
# and computes the WRONG norm). This function reduces mod the curve
# relations at every step, exactly the way the tower's actual field
# arithmetic would, so the elimination is both exact and actually linear
# at the point split_linear is called.
function reduce_mod_curves(g, wa1, a1, wa2, a2)
    changed = true
    while changed
        changed = false
        # reduce even powers wa_i^(2k) -> f(a_i)^k, highest first
        for k in 6:-1:1
            d1 = degree(g, wa1)
            if d1 >= 2*k
                g = g - (coeff(g, [wa1], [2*k]) * wa1^(2*k)) +
                        (coeff(g, [wa1], [2*k]) * f_of(a1)^k)
                changed = true
            end
            d2 = degree(g, wa2)
            if d2 >= 2*k
                g = g - (coeff(g, [wa2], [2*k]) * wa2^(2*k)) +
                        (coeff(g, [wa2], [2*k]) * f_of(a2)^k)
                changed = true
            end
        end
    end
    return g
end

function split_linear_reduced(g, w)
    # g is degree <=1 in w AFTER reduce_mod_curves has been applied.
    # Return (P,Q) with g = P + Q*w, P,Q free of w. Exact -- no
    # approximation -- but only valid post-reduction; calling this on an
    # unreduced g is exactly the bug the sanity check caught.
    #
    # NOTE: named split_linear_reduced (not split_linear) because it is
    # NOT interchangeable with 01b_wdegree_diagnostic.jl's split_linear --
    # that version assumes g is already degree <=1 in w with no reduction
    # step required, so it uses evaluate/divexact instead of coeff-based
    # extraction. Reusing the same name caused a method-overwrite error
    # during module precompilation.
    d = degree(g, w)
    @assert d <= 1 "expected degree <=1 in $w after curve reduction, got $d " *
                    "-- reduce_mod_curves did not fully linearize; check its loop bound (k up to 6) " *
                    "is high enough for this g's actual degree in $w"
    Q = coeff(g, [w], [1])
    P = g - Q * w
    return P, Q
end

function norm_eliminate_step(g, w, a_anchor, wa1, a1, wa2, a2)
    # Reduce mod curve relations FIRST (fixes the cross-term bug above),
    # then split linearly in w, take the norm, and reduce again (the
    # squaring step can reintroduce even powers of the OTHER w variable
    # too, via cross terms in P^2/Q^2).
    g = reduce_mod_curves(g, wa1, a1, wa2, a2)
    P, Q = split_linear_reduced(g, w)
    result = P^2 - Q^2 * f_of(a_anchor)
    return reduce_mod_curves(result, wa1, a1, wa2, a2)
end

function run_norm_elim_for_coeff(label, num, den, U_placeholder_name)
    println("=" ^ 70)
    println(label)
    println("=" ^ 70)

    # Build h = num - U*den in a ring with an extra U variable, so the
    # norm step is well-defined algebraically (see derivation above).
    Rh, (wa1h, wa2h, a1h, a2h, Uh) = polynomial_ring(
        F, ["wa1", "wa2", "a1", "a2", U_placeholder_name]
    )
    old_gens = gens(R)  # [wa1, wa2, a1, a2]
    new_gens = [wa1h, wa2h, a1h, a2h]
    remap(f) = evaluate(f, new_gens)

    num_h = remap(num)
    den_h = remap(den)
    h0 = num_h - Uh * den_h

    println("  h0 = num - U*den:  degree=", total_degree(h0), "  terms=", length(terms(h0)))

    # Step 1: eliminate wa2 (reduces mod both curve relations internally,
    # which is what fixes the wa1-cross-term bug found by the sympy check)
    h1 = norm_eliminate_step(h0, wa2h, a2h, wa1h, a1h, wa2h, a2h)
    println("  after eliminating wa2:  degree=", total_degree(h1), "  terms=", length(terms(h1)),
            "   (still contains wa1? ", (wa1h in vars(h1)), ")")

    # Step 2: eliminate wa1
    h2 = norm_eliminate_step(h1, wa1h, a1h, wa1h, a1h, wa2h, a2h)
    println("  after eliminating wa1:  degree=", total_degree(h2), "  terms=", length(terms(h2)),
            "   (still contains any w? ", any(v -> v in (wa1h, wa2h), vars(h2)), ")")

    println()
    return (h0=h0, h1=h1, h2=h2)
end

################################################################################
# Run it on every u_RS / v_RS coefficient of sample 1. This is the whole
# experiment -- no Groebner basis, no cross-sample anything.
################################################################################

results = Dict{String,Any}()

for i in 1:N_U_MATCH
    results["u1_$i"] = run_norm_elim_for_coeff("u1 coefficient x^$(i-1)  (norm-eliminate wa2 then wa1)",
                                                 u1_num[i], u1_den[i], "U")
end

for i in 1:length(v1_num)
    results["v1_$i"] = run_norm_elim_for_coeff("v1 coefficient x^$(i-1)  (norm-eliminate wa2 then wa1)",
                                                 v1_num[i], v1_den[i], "V")
end

################################################################################
# Summary table -- the numbers the supervisor actually asked for.
################################################################################

println()
println("#" ^ 70)
println("SUMMARY: per-sample, per-coefficient norm elimination cost")
println("#" ^ 70)
println()
println(rpad("coefficient", 14), rpad("h0 deg/terms", 18),
        rpad("after wa2", 18), rpad("after wa1", 18))
for (key, r) in sort(collect(results); by = first)
    d0, t0 = total_degree(r.h0), length(terms(r.h0))
    d1, t1 = total_degree(r.h1), length(terms(r.h1))
    d2, t2 = total_degree(r.h2), length(terms(r.h2))
    println(rpad(key, 14), rpad("$d0 / $t0", 18), rpad("$d1 / $t1", 18), rpad("$d2 / $t2", 18))
end
println()
println("Compare the 'after wa1' column to the cross-multiplied Fu/Fv sizes")
println("(degree 32/48, ~29,889 / ~150,241 terms) already measured. If these")
println("numbers stay in the hundreds/low-thousands, per-sample norm elimination")
println("is cheap as claimed. If they blow up comparably, the claim was wrong")
println("and the per-sample base-size advantage does not survive elimination --")
println("in which case the fiber-product win has to come entirely from the")
println("decoupled-U/V Groebner route (elim2.jl's Iu_decoupled/Iuv_decoupled),")
println("not from norm elimination, and that's the next thing to test.")













################################################################################
# EXPERIMENT: eliminate the w's (and, separately, w's+U's) from the
# DECOUPLED ideal, and report real numbers. This is the falsification
# test for the graph formulation: does post-elimination size for the
# decoupled route actually beat the cross-multiplied Fu/Fv numbers
# (degree 32/48, ~29,889 / ~150,241 terms), or does it converge to
# something comparable once the w's (and U/V's) are actually gone?
#
# Mechanism note: eliminate(I, vars) in Oscar computes a Groebner basis
# under a monomial ordering with `vars` forced dominant (an elimination
# ordering -- internally a block/lex-style order over `vars` composed
# with an order on the rest), then reads off the generators of
# I ∩ k[remaining vars]. This IS the block-elimination mechanism --
# block_ordering_dec above was for direct groebner_basis(...; ordering=)
# calls; eliminate() builds its own internal elimination ordering and
# does not consume block_ordering_dec. That's why the two are separate
# calls below rather than one feeding the other.
################################################################################

################################################################################
# INSTRUMENTATION PASS -- run before any elimination attempt.
#
# Goal: find out WHERE the Groebner computation goes pathological,
# rather than waiting on a single call that already hung. Three parts:
#
#   A) Static diagnostics on Fu_decoupled/curve generators (no Groebner
#      call at all -- these are cheap structural facts we should have
#      measured before ever calling eliminate()).
#   B) Incremental sub-ideal sweep: ideal(Fu_decoupled[1]), then
#      ideal(Fu_decoupled[1:2]), etc., each run through eliminate() with
#      a hard wall-clock timeout, so we can see which generator count
#      first goes pathological instead of learning only "the full system
#      hangs".
#   C) Incremental VARIABLE sweep: eliminate just wa1_d, then wa1_d+wa2_d,
#      etc., each with a hard timeout, to see whether a single sample's
#      pair of w's is already hard (intrinsic to one sample) or whether
#      it's specifically the SECOND sample's w's being added that causes
#      the blowup (cross-sample interaction).
#
# Both B and C use a hard timeout via a background Task + Timer, because
# there is no clean way to abort a running Singular/msolve C call from
# inside Julia -- the timeout can only tell you "still running after N
# seconds", not actually kill and reclaim the C-level computation. If a
# step times out, the printed elapsed time is the timeout value, not a
# true completion time, and the underlying Singular process may still be
# consuming CPU/RAM in the background for the rest of this Julia
# session. If that matters, run each timed step as its own external
# `timeout N julia -e '...'` subprocess instead (see note at the bottom
# of this block).
################################################################################

println()
println("===========================================================")
