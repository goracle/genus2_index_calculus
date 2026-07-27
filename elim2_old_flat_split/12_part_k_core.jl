println("PART K: The Final Collision (Eliminating the Middlemen)")
println("===========================================================")

# 1. Build the shared, final universe (Notice: NO 'w' variables allowed!)
R_final, (a1_f, a2_f, b1_f, b2_f, U0_f, U1_f, V0_f, V1_f) = polynomial_ring(F, ["a1", "a2", "b1", "b2", "U0", "U1", "V0", "V1"])

final_equations = Any[]

println("  Mapping Sample 1 into the final universe...")


################################################################################
# PART K FIX: manual term-by-term remap, replacing the generic evaluate()
# call that dies on the very first invocation.
#
# Root-cause hypothesis (see chat): clean_sample_1[i] lives in R_small =
# F[wa1,wa2,a1,a2,Ti] (5 vars), already eliminated of wa1,wa2 by
# process_sample_1_coeff's own eliminate() call -- so as a polynomial it
# should contain NO wa1/wa2 monomials at all (every exponent on those two
# generators is 0). evaluate(f, images) across two UNRELATED polynomial
# ring objects (R_small -> R_final) is not a cheap "rename the
# generators" operation in general -- Oscar's generic evaluate()
# reconstructs the whole expression through ring-homomorphism arithmetic,
# which can be far more expensive than the term count of the input or
# output would suggest, especially across rings that were never declared
# to have any relationship to each other.
#
# Fix: read clean_sample_1[i] apart into (coefficient, exponent_vector)
# pairs directly (using coefficients()/exponent_vectors(), both
# documented O(1)-per-term iterators, no ring-homomorphism machinery
# involved), and push each term straight into an MPolyBuildCtx for
# R_final. This is linear in the number of terms of the input polynomial
# and never constructs anything in an intermediate/unrelated ring.
#
# gen_map: for each generator index of R_small (in R_small's own
# declared order), an Int index into R_final's generator list (1-based),
# or `0` if that generator must be zero in the image (i.e. the wa1/wa2
# slots -- which we can also just assert are always-zero-exponent as a
# cheap sanity check while we're at it, rather than silently trusting
# that eliminate() actually removed them).
################################################################################

function remap_to_final(f, final_gens::Vector, gen_map::Vector{Int})
    # Using MPolyBuildCtx + push_term! + finish, the documented,
    # empirically-linear-in-term-count pattern for rebuilding a polynomial
    # term-by-term into a different ring (see Oscar/AbstractAlgebra docs'
    # swap_vars example -- confirmed by their own benchmark to scale
    # linearly, e.g. 0.0001s to 0.004s for a 40x growth in term count).
    # This avoids the likely O(n^2)-ish behavior of accumulating via
    # repeated `result += coeff*monomial` polynomial addition, which
    # re-normalizes/re-sorts the whole accumulator on every term, and it
    # avoids evaluate()'s generic cross-ring homomorphism machinery
    # entirely -- we go straight from (coefficient, exponent_vector) pairs
    # to push_term! calls in the TARGET ring, with no ring-homomorphism
    # evaluation step at all.
    R_out = parent(final_gens[1])
    n_out = length(final_gens)
    B = MPolyBuildCtx(R_out)

    for (c, exps) in zip(coefficients(f), AbstractAlgebra.exponent_vectors(f))
        new_exps = zeros(Int, n_out)
        for (k, e) in enumerate(exps)
            e == 0 && continue
            tgt = gen_map[k]
            if tgt == 0
                # Sanity check: a generator mapped to "must be zero" (the
                # eliminated w-slots) has a nonzero exponent here --
                # eliminate() did NOT fully remove this variable. Fail
                # loudly rather than silently drop real content.
                error("remap_to_final: generator index $k (mapped to zero) " *
                      "has nonzero exponent $e in a term of the input " *
                      "polynomial -- eliminate() did NOT fully remove this " *
                      "variable, zeroing it here would silently drop real " *
                      "content. Inspect the input polynomial before proceeding.")
            end
            new_exps[tgt] += e
        end
        push_term!(B, c, new_exps)
    end

    return finish(B)
end

################################################################################
# Usage, replacing the dying block at elim2.jl lines 2141-2154:
#
#   R_small (per process_sample_1_coeff) has generator order:
#     [wa1, wa2, a1, a2, T]     <- T is whatever target name was passed
#
#   R_final has generator order:
#     [a1_f, a2_f, b1_f, b2_f, U0_f, U1_f, V0_f, V1_f]
#
# So for sample 1 targeting U0 (target index 1 in the loop below):
#   gen_map = [0, 0, 1, 2, 5]     (wa1->0, wa2->0, a1->a1_f(idx1), a2->a2_f(idx2), T->U0_f(idx5))
#
# and similarly for U1 (T->U1_f, idx6), V0 (T->V0_f, idx7), V1 (T->V1_f, idx8).
#
# For sample 2 (R_small has [wb1,wb2,b1,b2,T]):
#   gen_map = [0, 0, 3, 4, <target_idx>]   (b1->b1_f(idx3), b2->b2_f(idx4))
################################################################################

println("Remapping sample 1 into the final universe (manual term-by-term)...")

final_gens = [a1_f, a2_f, b1_f, b2_f, U0_f, U1_f, V0_f, V1_f]

# sample 1: a-variables map to final indices 1,2; target T maps to final index 5,6,7,8 resp.
sample1_target_final_idx = [5, 6, 7, 8]   # U0, U1, V0, V1
for (i, tgt_idx) in enumerate(sample1_target_final_idx)
    gen_map = [0, 0, 1, 2, tgt_idx]
    t0 = time()
    g = remap_to_final(clean_sample_1[i], final_gens, gen_map)
    println("  clean_sample_1[$i] remapped in ", round(time()-t0, digits=3),
            "s: degree=", total_degree(g), " terms=", length(terms(g)))
    push!(final_equations, g)
end

println("Remapping sample 2 into the final universe (manual term-by-term)...")

# sample 2: b-variables map to final indices 3,4; target T maps to final index 5,6,7,8 resp.
sample2_target_final_idx = [5, 6, 7, 8]   # U0, U1, V0, V1
for (i, tgt_idx) in enumerate(sample2_target_final_idx)
    gen_map = [0, 0, 3, 4, tgt_idx]
    t0 = time()
    g = remap_to_final(clean_sample_2[i], final_gens, gen_map)
    println("  clean_sample_2[$i] remapped in ", round(time()-t0, digits=3),
            "s: degree=", total_degree(g), " terms=", length(terms(g)))
    push!(final_equations, g)
end


################################################################################
# PART K, take 3: direct resultant instead of eliminate() on an ideal.
#
# Both earlier attempts (ideal-based eliminate() per target variable, and
# ideal-based eliminate() on all four at once) OOM'd with zero diagnostic
# output -- we don't even know what degree/term count killed the process.
# Root cause hypothesis (see chat): eliminate(ideal(g1,g2), [T]) computes a
# full Groebner basis of <g1,g2> under an elimination ordering, which is
# far more general (and far more expensive) machinery than this problem
# needs. final_equations[i] and final_equations[i+4] are individual
# polynomials, each degree <=1 in T_i (T_i was introduced as
# "T_i * den - num", degree 1 in T_i by construction). Eliminating a
# SINGLE variable that appears at most linearly in TWO polynomials is
# exactly what resultant() computes directly, in one shot, no GB:
#
#   Res_{T_i}(g1, g2) vanishes iff g1, g2 have a common root in T_i
#
# For two polynomials each degree <=1 in T_i, resultant is (worst case) a
# single Sylvester-matrix determinant, not a GB search. This also sidesteps
# eliminate()'s internal elimination-ordering choice (see PART E -- that
# ordering is opaque and not tunable through eliminate()).
#
# Instrumentation: print degree/terms of each final_equations[i] BEFORE
# calling resultant (neither OOM'd attempt above ever did this), and write
# each result to disk immediately after, so a crash on (say) V1 doesn't
# destroy the U0/U1/V0 results that already finished.
################################################################################

################################################################################
# PART K setup: pick the target, build the 5-variable fiber-product ring,
# and extract each side's coefficients as polynomials in T. This is the
# part of the old "take 4" code that's still needed -- only the
# Sylvester-matrix-building and Leibniz-summand-enumeration that used to
# follow it has been replaced below.
################################################################################

const name  = "U0"
const i1    = 1
const i2    = 5
const Tvar  = U0_f

g1 = final_equations[i1]
g2 = final_equations[i2]

d1T = degree(g1, Tvar)
d2T = degree(g2, Tvar)
println("  --- $name ---")
println("    g1 (sample 1 side): total_degree=", total_degree(g1),
        "  terms=", length(terms(g1)), "  degree-in-$name=", d1T)
println("    g2 (sample 2 side): total_degree=", total_degree(g2),
        "  terms=", length(terms(g2)), "  degree-in-$name=", d2T)

if d1T == 0 || d2T == 0
    error("$name does not actually appear in one side; resultant " *
          "would be degenerate. Inspect final_equations construction.")
end

println("    building the fiber-product ring/generators for $name...")
flush(stdout)

# Same 5-variable fiber-product ring as before: only (a1,a2,b1,b2,T) --
# g1 only involves (a1,a2,T), g2 only involves (b1,b2,T).
Rfp, (a1_fp, a2_fp, b1_fp, b2_fp, T_fp) =
    polynomial_ring(F, ["a1", "a2", "b1", "b2", string(name)])
rfp_gens = [a1_fp, a2_fp, b1_fp, b2_fp, T_fp]

i2_local = i2 - length(clean_sample_1)
g1_fp = remap_to_final(clean_sample_1[i1], rfp_gens,
                        [0, 0, 1, 2, 5])   # wa1,wa2->0; a1->1; a2->2; T->5
g2_fp = remap_to_final(clean_sample_2[i2_local], rfp_gens,
                        [0, 0, 3, 4, 5])   # wb1,wb2->0; b1->3; b2->4; T->5

println("      g1 remapped into 5-var fiber-product ring: degree=",
        total_degree(g1_fp), " terms=", length(terms(g1_fp)),
        "  degree-in-T=", degree(g1_fp, T_fp))
println("      g2 remapped into 5-var fiber-product ring: degree=",
        total_degree(g2_fp), " terms=", length(terms(g2_fp)),
        "  degree-in-T=", degree(g2_fp, T_fp))

# Extract [c0, c1, ..., c_maxdeg] (each T-free) such that
# g == sum_k c_k * T^k, using coefficients()/exponent_vectors() so it
# never touches ring-homomorphism machinery.
function poly_coeffs_in(g, T, maxdeg)
    Rg = parent(g)
    gensR = gens(Rg)
    Tidx = findfirst(==(T), gensR)
    coeff_polys = [MPolyBuildCtx(Rg) for _ in 0:maxdeg]
    for (c, exps) in zip(coefficients(g), AbstractAlgebra.exponent_vectors(g))
        k = exps[Tidx]
        new_exps = copy(exps)
        new_exps[Tidx] = 0
        push_term!(coeff_polys[k+1], c, new_exps)
    end
    return [finish(ctx) for ctx in coeff_polys]
end

syl_c1 = poly_coeffs_in(g1_fp, T_fp, d1T)   # syl_c1[k+1] is coeff of T^k in g1_fp, k=0..d1T
syl_c2 = poly_coeffs_in(g2_fp, T_fp, d2T)   # syl_c2[k+1] is coeff of T^k in g2_fp, k=0..d2T







################################################################################
# part_k_diagnostic.jl
#
# Standalone structural diagnostic for the U0 quartic-in-T resultant problem
# (elim2.jl Part K, "redesigned" subresultant-PRS version).
#
# WHY THIS SCRIPT EXISTS
# -----------------------------------------------------------------------
# GPT's diagnosis of the PRS slowness: degree-in-T is only 4 on each side,
# so a subresultant PRS is nominally O(d1T*d2T) = O(16) pseudo-division
# steps -- cheap. The observed cost instead comes from the *coefficient
# ring* arithmetic: each of those 4+1 coefficients (elements of
# F[a1,a2,b1,b2], or its fraction field) is itself a large polynomial
# (elim2.jl's own PART H readout: 1445-term, degree-36 objects appear at
# this stage), and every pseudo-division step does full multivariate
# multiply/divide on objects of that size. The PRS algorithm is right;
# the coefficients feeding it are the bottleneck.
#
# GPT's ranked ideas, and what this script checks for each:
#   1. Do the quartics factor (e.g. as two quadratics, or have a
#      rational root / GF(p)-rational factor)?          -> Section A, B
#   2. Are the coefficients themselves reducible / do they share
#      common factors that could be pulled out before the PRS runs?
#                                                          -> Section C
#   3. Is the quartic secretly quadratic-in-T^2, reciprocal, or
#      palindromic (structural symmetry that would collapse degree)?
#                                                          -> Section D
#   4. How much does substituting explicit anchor values (dropping to
#      GF(p) coefficients) shrink term counts -- i.e. is the "1445
#      terms" figure inherent to the math, or an artifact of carrying
#      a1,a2,b1,b2 symbolically this late?                -> Section E
#
# This script does NOT re-run or interfere with the resultant(g1_T, g2_T)
# call in elim2.jl Part K -- it is read-only with respect to g1_T/g2_T
# and only inspects syl_c1/syl_c2 (the per-power-of-T coefficient slices
# built by poly_coeffs_in, already sitting in memory once elim2.jl reaches
# the "computing resultant via subresultant PRS" print). Run this in the
# SAME Julia session/REPL as elim2.jl, either:
#   (a) after Part K finishes (to sanity-check the result), or
#   (b) in a second REPL that has independently re-run elim2.jl only as
#       far as the syl_c1/syl_c2 construction (before the resultant()
#       call), if you want answers *while* the original resultant is
#       still crunching in the first REPL.
#
# It assumes elim2.jl's Part K setup has already run and the following
# names exist in Main: F, Rfp, T_fp, g1_fp, g2_fp, d1T, d2T, syl_c1,
# syl_c2, Rcoef, Kcoef, a1_c, a2_c, b1_c, b2_c, coef_gens,
# drop_T_to_coef_ring, poly_coeffs_in.
################################################################################

using Oscar

println("="^70)
