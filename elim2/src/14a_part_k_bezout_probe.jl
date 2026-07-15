println("PART K DIAGNOSTIC COMPLETE")
println("="^70)
println("""
Reading the results:
  Section A tells you WHICH T^k coefficient(s) are large -- if it's
    lopsided (e.g. only the T^4/T^0 coefficients are big and T^1..T^3
    are small), that's a strong hint the quartic is close to a binomial
    T^4 + c and worth testing for radical/Kummer structure directly.
  Section B is the direct test of GPT idea #1 (does it factor).
  Section C is GPT idea #2/#3 combined (pull out common structure /
    keep coefficients factored) -- a nontrivial GCD here is the
    highest-leverage win if found, since it shrinks EVERY pseudo-
    division step in the PRS proportionally, for free.
  Section D is the quadratic-in-T^2 / palindromic test.
  Section E answers whether 1445 terms is inherent to the degree-36
    geometry or partly an artifact of carrying (a1,a2,b1,b2) symbolic.
""")






################################################################################
# PART K, REDESIGNED: resultant via a univariate-in-T ring over the
# multivariate coefficient ring F[a1,a2,b1,b2] (or its fraction field),
# instead of a hand-built Sylvester matrix + Leibniz summand enumeration.
#
# -----------------------------------------------------------------------
# WHY THE OLD APPROACH WAS DOOMED, INDEPENDENT OF PARALLELIZATION
# -----------------------------------------------------------------------
# The old "take 5" strategy enumerated permutations sigma of {1..n} and
# formed prod_i Syl[i, sigma[i]] one at a time, banking on the matrix's
# bandedness to skip permutations that are structurally zero. That part
# is correct and does cut 40320 down to a few hundred -- but it attacks
# the wrong axis of the blowup. The evidence is right there in the
# comments: the IDENTITY permutation alone (a single Leibniz summand)
# already produced a degree-256, 17.85-million-term polynomial before
# OOM-killing the process. Bandedness controls *how many* summands are
# nonzero; it says nothing about *how large* each individual summand's
# raw polynomial product is. Multiplying out entries drawn from a
# degree ~32-ish polynomial ring 8 times over, with no cancellation
# available until every one of the (few hundred) surviving summands has
# been formed and added together, is a textbook case of intermediate
# expression swell: the final resultant is typically MUCH smaller than
# any single term in its Leibniz expansion, because the sum cancels
# enormously. Leibniz expansion pays the full swell cost per term and
# only gets the benefit of cancellation at the very end -- if it ever
# gets there.
#
# The original resultant(g1_fp, g2_fp, T_fp) call (Part K, take 3) is
# what actually OOM'd first, and the fallback to hand-rolled Sylvester +
# Leibniz was a strict downgrade, not a fix: it replaced one bad
# algorithm with an even worse one. The real problem was almost
# certainly that g1_fp, g2_fp live in a *plain* 5-variable ring
# F[a1,a2,b1,b2,T], so resultant(...,T) has no structural reason to
# treat T specially -- generic dispatch on a flat multivariate ring can
# fall back to exactly the Sylvester-determinant-by-expansion strategy
# that blew up by hand above, just hidden one call deeper.
#
# -----------------------------------------------------------------------
# THE FIX: change the RING, not the algorithm-by-hand
# -----------------------------------------------------------------------
# g1_fp and g2_fp are each low degree in T (d1T = d2T = 4) with dense
# coefficients in (a1,a2,b1,b2). The right object to compute in is the
# univariate polynomial ring in T *over* the coefficient ring
# F[a1,a2,b1,b2] (equivalently, over its fraction field):
#
#     Rcoef, (a1,a2,b1,b2) = polynomial_ring(F, ["a1","a2","b1","b2"])
#     Rcoef_frac = fraction_field(Rcoef)          # exact division allowed
#     Rt, T = polynomial_ring(Rcoef_frac, "T")
#
# In this tower, resultant(g1_T, g2_T) for univariate polynomials over a
# field-like coefficient ring dispatches to the SUBRESULTANT PRS
# algorithm (Euclidean-style pseudo-remainder sequence, fraction-free /
# Bareiss-type at each step) rather than Leibniz determinant expansion.
# This is the standard replacement for Sylvester-determinant-by-cofactor
# or -by-Leibniz whenever the eliminated variable's degree is small on
# both sides -- exactly this case (degree 4 and 4).
#
# Why this specific algorithm matches this specific matrix:
#   * It is an O(d1T * d2T) sequence of pseudo-division steps (here,
#     4*4 = 16 "slots" worst case, actually far fewer since the PRS
#     degree-drops are usually much faster than unit steps) instead of
#     an O(n!) or even O(n^3) determinant computation on an 8x8 matrix
#     whose entries are already huge.
#   * Every intermediate pseudo-remainder in a subresultant PRS is
#     ITSELF a signed subdeterminant (minor) of the Sylvester matrix,
#     so subresultant theory gives a hard a priori bound on how large
#     each intermediate object can get -- bounded by the same Hadamard-
#     type bound that bounds the FINAL resultant, not by n! times the
#     size of the biggest raw entry. That is precisely "no intermediate
#     expression swell" in the precise technical sense.
#   * It stays exact / symbolic the whole way (fraction-free variants
#     never introduce anything outside the original coefficient ring's
#     fraction field), so priority 4 (exact symbolic arithmetic) holds
#     automatically -- there's no floating point or numerical resultant
#     involved anywhere.
#   * It needs no permutation search, no bandedness bookkeeping, no
#     "nonzero-compatible sigma" enumeration, and no per-summand
#     subprocess harness -- Part K's entire OOM-recovery/subprocess
#     survey machinery becomes unnecessary and can be deleted outright.
#
# Expected complexity: O(d1T * d2T) coefficient-ring pseudo-division
# steps = O(16) worst case here, each step operating on polynomials in
# F[a1,a2,b1,b2] whose size is controlled by the subresultant bound
# rather than growing combinatorially -- versus the old approach's
# O(few hundred surviving permutations) x O(8-factor products of
# degree-32-ish polynomials each), which is precisely what produced a
# single 17.85-million-term intermediate object.
################################################################################

println("  --- $name (redesigned: subresultant PRS, no Sylvester expansion) ---")

# ------------------------------------------------------------------------
# Step 1: coefficient ring F[a1,a2,b1,b2], and its fraction field so
# pseudo-division has exact inverses available. We reuse g1_fp/g2_fp's
# own coefficient extraction (poly_coeffs_in, already present above) to
# avoid re-deriving anything from clean_sample_1/2 -- syl_c1, syl_c2 are
# already exactly "coefficients of g1_fp, g2_fp as polynomials in T",
# living in the 4-variable ring Rfp restricted to (a1,a2,b1,b2). We just
# need to hand them to Oscar's univariate resultant instead of building
# a Sylvester matrix by hand.
# ------------------------------------------------------------------------

Rcoef, (a1_c, a2_c, b1_c, b2_c) = polynomial_ring(F, ["a1", "a2", "b1", "b2"])
Kcoef = fraction_field(Rcoef)

# syl_c1[k+1], syl_c2[k+1] (k = 0..d1T / 0..d2T) currently live in Rfp,
# the 5-variable ring that still nominally contains T_fp as a generator
# (even though these coefficient slices are T-free by construction). Map
# each one down into Rcoef via the same term-by-term MPolyBuildCtx
# technique already used by remap_to_final / poly_coeffs_in elsewhere in
# this file -- linear in term count, no ring-homomorphism machinery.
function drop_T_to_coef_ring(f, coef_gens::Vector)
    B = MPolyBuildCtx(parent(coef_gens[1]))
    for (c, exps) in zip(coefficients(f), AbstractAlgebra.exponent_vectors(f))
        # exps is [e_a1, e_a2, e_b1, e_b2, e_T]; e_T must be 0 here.
        push_term!(B, c, exps[1:4])
    end
    return finish(B)
end

coef_gens = [a1_c, a2_c, b1_c, b2_c]
c1_lifted = [Kcoef(drop_T_to_coef_ring(c, coef_gens)) for c in syl_c1]
c2_lifted = [Kcoef(drop_T_to_coef_ring(c, coef_gens)) for c in syl_c2]

# ------------------------------------------------------------------------
# Step 2: univariate ring in T over Kcoef = Frac(F[a1,a2,b1,b2]), then
# reassemble g1_T, g2_T from their already-extracted coefficient slices
# (syl_c1/syl_c2), and let Oscar's univariate resultant do subresultant
# PRS elimination -- this is the call that replaces the ENTIRE Sylvester-
# matrix-plus-Leibniz-survey apparatus below.
# ------------------------------------------------------------------------

Rt, T = polynomial_ring(Kcoef, string(name))

g1_T = sum(c1_lifted[k+1] * T^k for k in 0:d1T)
g2_T = sum(c2_lifted[k+1] * T^k for k in 0:d2T)

################################################################################
# BEZOUT MATRIX ENTRY DIAGNOSTIC (no determinant computed here)
#
# Question being asked, per Claire's request: before writing/running any
# Bareiss elimination, just BUILD the 4x4 Bezoutian of g1_T, g2_T (both
# degree 4 in T, coefficients in Rcoef = F[a1,a2,b1,b2]) and report
# degree / term count / sparsity for each of the 16 entries. This alone
# tells us whether Bezout construction is cheap (bottleneck genuinely
# was the PRS recursion) or whether it's already expensive (bottleneck
# just moved one step earlier, and Bezout buys nothing by itself).
#
# Construction (only valid for two EXACT degree-4 polynomials, which is
# confirmed here since d1T == d2T == 4):
#
#   g1(T) = sum_{i=0}^4 p_i T^i,   g2(T) = sum_{i=0}^4 q_i T^i
#   [p,q]_{m,n} := p_m*q_n - p_n*q_m   (antisymmetric bracket)
#
#   B00 = [p,q]_{0,1}
#   B01 = [p,q]_{0,2}
#   B02 = [p,q]_{0,3}
#   B03 = [p,q]_{0,4}
#   B11 = [p,q]_{0,3} + [p,q]_{1,2}
#   B12 = [p,q]_{0,4} + [p,q]_{1,3}
#   B13 = [p,q]_{1,4}
#   B22 = [p,q]_{1,4} + [p,q]_{2,3}
#   B23 = [p,q]_{2,4}
#   B33 = [p,q]_{3,4}
#   (B symmetric: Bji = Bij)
#
# c1_lifted / c2_lifted are already the T^0..T^4 coefficients (p_i, q_i)
# as elements of Kcoef = Frac(F[a1,a2,b1,b2]). We expect these
# denominators to be units (same assumption the resultant step below
# already relies on) -- checked explicitly per-entry rather than assumed.
################################################################################

if d1T == 4 && d2T == 4
    println("    --- Bezout matrix entry diagnostic ($name) ---")
    println("    (constructing B only -- NOT computing det(B) / resultant here)")
    flush(stdout)

    p_coef = c1_lifted   # p_coef[k+1] = p_k, k = 0..4
    q_coef = c2_lifted   # q_coef[k+1] = q_k, k = 0..4

    # bracket_num(m, n): numerator polynomial of p_m*q_n - p_n*q_m in
    # Rcoef, after checking both denominators are units. Kept as plain
    # Rcoef elements (not Kcoef fractions) so degree/terms/sparsity are
    # ordinary polynomial-ring queries, matching how res_num is reported
    # further down.
    function bracket_num(m::Int, n::Int)
        pm, qn = p_coef[m+1], q_coef[n+1]
        pn, qm = p_coef[n+1], q_coef[m+1]
        val = pm * qn - pn * qm   # Kcoef arithmetic
        den = denominator(val)
        if !is_unit(den)
            println("      WARNING: [p,q]_{$m,$n} has non-unit denominator " *
                    "(degree=", total_degree(den), ") -- coefficient lift " *
                    "may not be a clean polynomial here; reporting numerator only.")
        end
        return Rcoef(numerator(val))
    end

    # Bracket cache: only distinct (m,n), m<n, are ever needed; brackets
    # are antisymmetric so [p,q]_{n,m} = -[p,q]_{m,n} and have identical
    # degree/term-count/sparsity to their (m,n) counterpart -- computed
    # once per pair.
    bracket_cache = Dict{Tuple{Int,Int}, Any}()
    function bracket(m::Int, n::Int)
        key = m < n ? (m, n) : (n, m)
        if !haskey(bracket_cache, key)
            bracket_cache[key] = bracket_num(key[1], key[2])
        end
        return m < n ? bracket_cache[key] : -bracket_cache[key]
    end

    # Assemble the 10 distinct symmetric entries per the formula above.
    B = Dict{Tuple{Int,Int}, Any}()
    B[(0,0)] = bracket(0,1)
    B[(0,1)] = bracket(0,2)
    B[(0,2)] = bracket(0,3)
    B[(0,3)] = bracket(0,4)
    B[(1,1)] = bracket(0,3) + bracket(1,2)
    B[(1,2)] = bracket(0,4) + bracket(1,3)
    B[(1,3)] = bracket(1,4)
    B[(2,2)] = bracket(1,4) + bracket(2,3)
    B[(2,3)] = bracket(2,4)
    B[(3,3)] = bracket(3,4)
    # symmetric completions
    B[(1,0)] = B[(0,1)]
    B[(2,0)] = B[(0,2)]
    B[(3,0)] = B[(0,3)]
    B[(2,1)] = B[(1,2)]
    B[(3,1)] = B[(1,3)]
    B[(3,2)] = B[(2,3)]

    # Total possible monomials in 4 vars (a1,a2,b1,b2) up to an entry's
    # own total_degree, as a crude density denominator for a sparsity
    # ratio: terms / C(deg+4,4). This is a loose upper bound (actual
    # monomial count of THAT specific degree, not <= degree, would be
    # tighter/more standard, but this is enough to flag "dense vs
    # sparse" at a glance without extra machinery).
    nvars_coef = 4
    function sparsity_ratio(f)
        d = total_degree(f)
        t = length(terms(f))
        # C(d+nvars_coef, nvars_coef) = max monomials of total degree <= d
        max_mono = binomial(d + nvars_coef, nvars_coef)
        return max_mono == 0 ? NaN : t / max_mono
    end

    println("      entry   degree   terms      sparsity(terms/maxmono<=deg)")
    for i in 0:3, j in 0:3
        f = B[(i,j)]
        d = total_degree(f)
        t = length(terms(f))
        s = sparsity_ratio(f)
        println("      B[$i,$j]   ", d, "        ", t, "        ",
                round(s, sigdigits=4))
    end
    flush(stdout)

    total_terms = sum(length(terms(B[(i,j)])) for i in 0:3, j in 0:3)
    max_deg = maximum(total_degree(B[(i,j)]) for i in 0:3, j in 0:3)
    println("      --- summary: max entry degree=$max_deg, " *
            "total terms across all 16 entries=$total_terms ---")
    println("      Reading this: if entries look like degree~64 with ")
    println("      O(1000) terms each, Bezout construction is cheap and ")
    println("      Bareiss elimination is worth writing next. If entries ")
    println("      already look like degree~64 with O(100000+) terms, ")
    println("      the bottleneck has simply moved from the PRS recursion ")
    println("      into Bezout construction itself, and Bareiss won't help.")
    flush(stdout)
else
    println("    (skipping Bezout diagnostic: expected d1T==d2T==4, got ",
            d1T, ", ", d2T, ")")
end

################################################################################
# PARTS A-E: deep structural diagnostic pass, requested BEFORE any resultant
# (Sylvester or Bezout-determinant or PRS) is actually run to completion.
#
# Goal: figure out WHY the Bezout entries came back at ~83,521 terms /
# degree 64 each (~1.3M terms total across the 16 entries) -- is that
# swell inherent to the true resultant's algebraic complexity, or is it
# an artifact of (a) hidden factorable structure in g1/g2, (b) carrying
# redundant non-symmetric variables when a1<->a2, b1<->b2 symmetry is
# available, or (c) a bad representation choice. Nothing below computes
# det(B) or the full resultant -- this is pure structure inspection.
################################################################################
global all_a_sym = true
