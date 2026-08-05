#!/usr/bin/env julia
#
# norm_trace_pullback.jl
#
# Follow-on to phi_diagnostic.jl. That script found, at the REAL
# constraint (target_q_exponent=0.2, q=17, Nq=307), that the top 1% of
# characters by |S_hat(k)|^8 mass collapse onto only 307 distinct
# residues mod Nq out of 20000 samples (1.5% distinct) -- i.e. NOT
# confinement (the k's are not preferentially near multiples of N/Nq),
# but real clustering mod Nq. At the higher, diagnostic-only exponent
# (q=331) the same test showed 91.7% distinct -- no clustering, pure
# spectral leakage.
#
# This script chases the q=17-style clustering signal down two levels:
#
#   STAGE 1 (residue inspection, cheap): take the anomalous k's mod Nq,
#     look at the *set* of distinct residues r. Do they look like a
#     subgroup / coset of Z/Nq (structured under multiplication), or
#     just "fewer than n_top but still scattered" (which would be a
#     weaker, less interesting form of clustering)? This is a sanity
#     gate before paying for Stage 2.
#
#   STAGE 2 (norm/trace/projective-line pullback, the real test): for
#     each distinct anomalous residue r in 0:(Nq-1), look up the field
#     element g^r in F_{q^3} (same generator/power-table construction
#     as singer_sidon_subset_native), and test whether these elements
#     correlate with:
#       (a) TRACE forms: s -> Tr(alpha * g^r) for alpha ranging over
#           F_{q^3} (or a sampled subset when q^3 is large) -- looking
#           for alpha such that Tr(alpha * g^r) is constant (e.g. 0)
#           across the anomalous r's, which would mean the anomalous
#           frequencies pick out a trace-zero HYPERPLANE.
#       (b) NORM: whether Norm(g^r) = g^r * (g^r)^q * (g^r)^(q^2)
#           (which lands in F_q, i.e. reduces mod q after the
#           F_{q^3}->F_q trace/norm reduction) takes a small number of
#           distinct values across the anomalous r's, vs. the same
#           statistic for a uniform-random sample of residues (a norm
#           analog of the mod-Nq clustering test already run in
#           phi_diagnostic.jl, but one level deeper -- on the FIELD
#           element, not the exponent).
#
# Both stages reuse the exact field construction from
# singer_sidon_subset_native (strategy_comparison.jl) -- same
# generator-finding logic (verified against ALL prime factors of
# q^3-1, not just Nq's, per that function's docstring on the
# transversal-subgroup bug) -- but expose the power table and Tr/Norm
# functions directly, since singer_sidon_subset_native keeps them as
# internal closures and only returns D and Nq.
#
# REVISION NOTE: the first version of Stage 2 compared DISTINCT-VALUE
# COUNTS (how many different Norm(g^r) / Tr(alpha*g^r) values appear).
# That saturates immediately: Norm and Tr both land in F_q, which has
# only q elements, while the anomalous-residue samples here run into
# the hundreds (q=17 case) to tens of thousands (q=331 case) -- so
# "distinct count" hits ~q for both the anomalous data AND a uniform
# random null, and cannot tell them apart once every value is already
# hit at least once. The actual first run showed exactly this: 16/16
# distinct Norm values and 17/17 distinct Tr values, anomalous vs.
# null, at q=17 -- a codomain-size ceiling artifact, not evidence of
# no signal. Stage 2 now uses a chi-squared statistic comparing the
# FULL empirical distribution over F_q to uniform (see
# chi_squared_uniform below), which has power even when every bin in
# the small codomain is already populated.
#
# NOTE: does NOT check Julia syntax by execution in this environment;
# written to match the conventions and helper functions already
# verified working in strategy_comparison.jl (gf_q_irreducible_cubic,
# prime_factors, largest_prime_leq).

using Printf
using Statistics
using Random

include("strategy_comparison.jl")
include("phi_diagnostic.jl")

"""
    build_gf_q3_field(q, rng) -> (mul, fpow, Tr, Norm, powers, g, Nq)

Rebuilds the F_{q^3} field arithmetic and the g^0..g^(Nq-1) power
table exactly as singer_sidon_subset_native does internally, but
returns the arithmetic functions and the power table directly instead
of only the derived Singer set D. This is the piece
singer_sidon_subset_native does not expose and that Stage 2 below
needs (to evaluate Tr(alpha * g^r) and Norm(g^r) for arbitrary r,
not just to build D).

Field elements are triples (a0,a1,a2) meaning a0 + a1*t + a2*t^2 in
F_q[t]/(t^3 + c2*t^2 + c1*t + c0), matching
singer_sidon_subset_native's representation and reduction rule
exactly (t^3 = -(c2 t^2 + c1 t + c0) mod q).
"""
function build_gf_q3_field(q::Int, rng::AbstractRNG)
    Nq = q^2 + q + 1
    Mfull = q^3 - 1
    c0, c1, c2 = gf_q_irreducible_cubic(q, rng)

    reduce3(a0, a1, a2) = (mod(a0, q), mod(a1, q), mod(a2, q))

    function mul(u, v)
        u0, u1, u2 = u
        v0, v1, v2 = v
        p0 = u0*v0
        p1 = u0*v1 + u1*v0
        p2 = u0*v2 + u1*v1 + u2*v0
        p3 = u1*v2 + u2*v1
        p4 = u2*v2
        t4_0 = c2*c0
        t4_1 = c2*c1 - c0
        t4_2 = c2^2 - c1
        r0 = p0 + p3*(-c0) + p4*t4_0
        r1 = p1 + p3*(-c1) + p4*t4_1
        r2 = p2 + p3*(-c2) + p4*t4_2
        return reduce3(r0, r1, r2)
    end

    function add(u, v)
        u0, u1, u2 = u
        v0, v1, v2 = v
        return reduce3(u0 + v0, u1 + v1, u2 + v2)
    end

    function fpow(v, e)
        result = (1, 0, 0)
        base = v
        while e > 0
            if e & 1 == 1
                result = mul(result, base)
            end
            base = mul(base, base)
            e >>= 1
        end
        return result
    end

    function Tr(v)
        vq  = fpow(v, q)
        vq2 = fpow(v, q*q)
        a0, a1, a2 = v
        b0, b1, b2 = vq
        d0, d1, d2 = vq2
        return mod(a0 + b0 + d0, q)
    end

    # Norm(v) = v * v^q * v^(q^2), which lands in F_q (fixed field of
    # Frobenius); by construction this always reduces to a scalar, so
    # we assert the non-scalar coordinates vanish as a correctness
    # check and return just the F_q value.
    function Norm(v)
        vq  = fpow(v, q)
        vq2 = fpow(v, q*q)
        n1 = mul(v, vq)
        n2 = mul(n1, vq2)
        @assert n2[2] == 0 && n2[3] == 0 "Norm did not reduce to F_q -- field construction bug"
        return n2[1]
    end

    Mfull_prime_factors = prime_factors(Mfull)
    g = nothing
    while g === nothing
        v = (rand(rng, 0:(q-1)), rand(rng, 0:(q-1)), rand(rng, 0:(q-1)))
        v == (0, 0, 0) && continue
        if fpow(v, Mfull) == (1, 0, 0) &&
           all(r -> fpow(v, Mfull ÷ r) != (1, 0, 0), Mfull_prime_factors)
            g = v
        end
    end

    powers = Vector{NTuple{3,Int}}(undef, Nq)
    powers[1] = (1, 0, 0)
    for i in 2:Nq
        powers[i] = mul(powers[i-1], g)
    end

    return (; mul, add, fpow, Tr, Norm, powers, g, Nq, q)
end

"""
    stage1_residue_inspection(top_ks, Nq) -> distinct_residues::Vector{Int}

Cheap first look at the anomalous residues mod Nq: report the count,
whether 0 is among them (relevant since D itself is {i : Tr(g^i)=0}),
and whether the set is closed (or nearly closed) under addition mod
Nq -- a subgroup/coset would show strong closure; unstructured
clustering would not.
"""
function stage1_residue_inspection(top_ks::Vector{Int}, Nq::Int)
    residues = sort(unique(mod.(top_ks, Nq)))
    n = length(residues)
    rset = Set(residues)

    # Closure-under-addition check: for a random sample of pairs
    # (r1,r2) from the residue set, what fraction of r1+r2 (mod Nq)
    # also lands in the set? For a genuine subgroup/coset this is
    # high; for a random subset of size n out of Nq it's ~ n/Nq.
    rng = MersenneTwister(12345)
    n_trials = min(2000, n * n)
    hits = 0
    for _ in 1:n_trials
        r1 = residues[rand(rng, 1:n)]
        r2 = residues[rand(rng, 1:n)]
        (mod(r1 + r2, Nq) in rset) && (hits += 1)
    end
    closure_frac = hits / n_trials
    baseline_frac = n / Nq

    @printf("\n--- Stage 1: residue inspection ---\n")
    @printf("  %d distinct residues mod Nq=%d (%.2f%% of Nq)\n", n, Nq, 100 * n / Nq)
    @printf("  closure under addition mod Nq: %.4f  (baseline for a random size-%d subset: %.4f)\n",
            closure_frac, n, baseline_frac)
    if closure_frac > 3 * baseline_frac
        println("  -> residue set is much more closed under addition than chance predicts:")
        println("     consistent with a coset/subgroup-like structure. Proceed to Stage 2.")
    else
        println("  -> no strong additive closure signature. Clustering may still be genuine")
        println("     algebraic resonance (subgroup structure isn't the only kind), so Stage 2")
        println("     is still worth running, but temper expectations accordingly.")
    end

    return residues
end

"""
    chi_squared_uniform(values, codomain_size) -> (chi2, dof)

Pearson chi-squared statistic testing whether `values` (each assumed
in 0:(codomain_size-1)) is drawn uniformly from that codomain. This is
the right tool where distinct-value counts SATURATE (codomain much
smaller than sample count, so "count distinct values" hits its ceiling
and can't distinguish uniform from non-uniform) -- e.g. Norm values
live in F_q (q elements) and Tr(alpha*x) values live in F_q too, while
the anomalous-residue sample sizes here (hundreds to tens of
thousands) are always >> q. Chi-squared instead compares the FULL
empirical distribution over the (small) codomain to uniform, so it
has power even when every bin is hit many times over.

Returns the statistic and degrees of freedom (codomain_size - 1);
under the null (uniform draws), chi2 is approximately
chi-squared-distributed with that many dof, so chi2 >> dof (e.g.
chi2 / dof >> 1, or chi2 well above the ~95th percentile for that dof)
is the signal to look for -- not a raw pass/fail, since dof and the
appropriate threshold both depend on q.
"""
function chi_squared_uniform(values::Vector{Int}, codomain_size::Int)
    counts = zeros(Int, codomain_size)
    for v in values
        counts[v+1] += 1
    end
    n = length(values)
    expected = n / codomain_size
    chi2 = sum((c - expected)^2 / expected for c in counts)
    dof = codomain_size - 1
    return (chi2, dof)
end

"""
    stage2_norm_trace_pullback(residues, field; n_alpha_samples=200, seed=1)

For the distinct anomalous residues (from Stage 1), pull back to field
elements g^r and test:

  (a) NORM clustering: compares the empirical distribution of
      Norm(g^r) over F_q (q possible values) against uniform, via
      chi-squared, for the anomalous residues vs. a uniform-random
      null sample of the same count. NOTE: an earlier version of this
      function compared DISTINCT-VALUE COUNTS instead -- that
      saturates immediately here because Norm's image has only q-1
      elements while samples run into the hundreds/thousands, so
      "distinct count" hits ~q-1 for both anomalous and null data and
      cannot distinguish them (this is exactly what the first run of
      this script showed: 16/16 distinct at q=17, 330/330 at q=331 --
      an artifact of codomain size, not evidence of no signal).
      Chi-squared instead measures whether the anomalous data
      OVER-WEIGHTS some norm values relative to uniform, which
      distinct-count cannot see once every value is already hit.

  (b) TRACE-FORM correlation: same fix, one level up. For a sample of
      alpha in F_{q^3} (all of them if q^3 is small enough, else a
      random sample), compute the chi-squared statistic of
      Tr(alpha*g^r)'s distribution over F_q (NOT distinct-count, same
      saturation problem as (a)) for the anomalous residues, and
      compare the BEST (highest) chi2 achieved over alpha against the
      best achieved on a null sample over the SAME alpha set (guards
      against a multiple-testing artifact: trying many alphas raises
      the expected max chi2 even under the null, so the comparison
      must be best-vs-best, not best-vs-nominal-threshold).

Both are proportional-cost relative to phi_diagnostic.jl's own
O(N*B) DFT step, so safe to run at the same N,q the diagnostic used.
"""
function stage2_norm_trace_pullback(residues::Vector{Int}, field; n_alpha_samples::Int = 200, seed::Int = 1)
    q  = field.q
    Nq = field.Nq
    powers = field.powers
    Tr = field.Tr
    Norm = field.Norm
    mul = field.mul

    n = length(residues)
    elems = [powers[r+1] for r in residues]  # g^r for each anomalous r

    # --- (a) Norm clustering (distributional, not distinct-count) ---
    norms = [Norm(e) for e in elems]
    chi2_norm, dof_norm = chi_squared_uniform(norms, q)

    rng = MersenneTwister(seed + 42)
    null_residues = rand(rng, 0:(Nq-1), n)
    null_norms = [Norm(powers[r+1]) for r in null_residues]
    chi2_norm_null, _ = chi_squared_uniform(null_norms, q)

    n_distinct_norms = length(unique(norms))
    n_distinct_null_norms = length(unique(null_norms))

    @printf("\n--- Stage 2a: Norm(g^r) clustering ---\n")
    @printf("  anomalous residues: %d distinct Norm values out of %d samples (%.1f%% distinct), values in F_%d\n",
            n_distinct_norms, n, 100 * n_distinct_norms / n, q)
    @printf("  null (uniform-random residues): %d distinct Norm values out of %d samples (%.1f%% distinct)\n",
            n_distinct_null_norms, n, 100 * n_distinct_null_norms / n)
    @printf("  chi-squared vs. uniform over F_%d (dof=%d): anomalous=%.1f  null=%.1f  ratio=%.2f\n",
            q, dof_norm, chi2_norm, chi2_norm_null, chi2_norm / max(chi2_norm_null, 1e-9))
    if chi2_norm > 3 * max(chi2_norm_null, dof_norm)
        println("  -> anomalous elements' norm distribution deviates from uniform far more than")
        println("     the null and more than dof alone would predict by chance:")
        println("     the anomalous set correlates with the NORM MAP -- a genuine algebraic")
        println("     signature (over-weighting some norm-fiber(s)).")
    else
        println("  -> norm distribution is not meaningfully more non-uniform than the null.")
        println("     No norm-fiber signature detected.")
    end

    # --- (b) Trace-form correlation ---
    # Sample alpha in F_{q^3} (all q^3 of them if small; else random
    # sample). For each alpha, check whether Tr(alpha * g^r) is
    # constant across the n anomalous elements -- report the alpha(s)
    # achieving the best (most constant) score, i.e. lowest number of
    # distinct Tr values, and compare against the null (same alpha
    # applied to a uniform-random residue sample of the same size).
    all_alpha = q^3 <= 20_000
    alphas = if all_alpha
        [(a0, a1, a2) for a0 in 0:(q-1) for a1 in 0:(q-1) for a2 in 0:(q-1)][2:end]  # skip (0,0,0)
    else
        rng2 = MersenneTwister(seed + 7)
        [(rand(rng2, 0:(q-1)), rand(rng2, 0:(q-1)), rand(rng2, 0:(q-1))) for _ in 1:n_alpha_samples]
    end

    # Best-chi2-over-alpha for the anomalous set (distributional, not
    # distinct-count -- see docstring for why distinct-count saturates
    # here too: Tr is F_q-valued, same small-codomain problem as Norm).
    best_alpha = nothing
    best_chi2 = -Inf
    best_n_distinct = n + 1
    for alpha in alphas
        alpha == (0, 0, 0) && continue
        tr_vals = [Tr(mul(alpha, e)) for e in elems]
        chi2, _ = chi_squared_uniform(tr_vals, q)
        if chi2 > best_chi2
            best_chi2 = chi2
            best_alpha = alpha
            best_n_distinct = length(unique(tr_vals))
        end
    end

    # Null comparison: best achievable chi2 over the SAME alpha set,
    # applied to a uniform-random residue sample -- tests whether "some
    # alpha makes it look non-uniform" is just a multiple-testing
    # artifact of trying many alphas (more alphas tried -> higher max
    # chi2 expected even under the null, so best-vs-best is the right
    # comparison, not best-vs-a-fixed-threshold).
    null_elems = [powers[r+1] for r in null_residues]
    best_chi2_null = -Inf
    best_n_distinct_null = n + 1
    for alpha in alphas
        alpha == (0, 0, 0) && continue
        tr_vals = [Tr(mul(alpha, e)) for e in null_elems]
        chi2, _ = chi_squared_uniform(tr_vals, q)
        if chi2 > best_chi2_null
            best_chi2_null = chi2
            best_n_distinct_null = length(unique(tr_vals))
        end
    end
    dof = q - 1

    @printf("\n--- Stage 2b: trace-form correlation (%d alpha's tested, %s) ---\n",
            length(alphas), all_alpha ? "exhaustive over F_q^3" : "random sample")
    @printf("  best alpha: Tr(alpha * g^r) takes %d distinct values out of %d anomalous elements\n",
            best_n_distinct, n)
    @printf("  same best-of-%d-alphas statistic on a uniform-random residue sample: %d distinct values\n",
            length(alphas), best_n_distinct_null)
    @printf("  chi-squared vs. uniform over F_%d (dof=%d): anomalous best=%.1f  null best=%.1f  ratio=%.2f\n",
            q, dof, best_chi2, best_chi2_null, best_chi2 / max(best_chi2_null, 1e-9))
    if best_chi2 > 3 * max(best_chi2_null, dof)
        println("  -> found an alpha under which the anomalous elements' trace distribution")
        println("     deviates from uniform far more than the multiple-testing null predicts:")
        println("     the anomalous set correlates with a TRACE FORM (affine hyperplane in")
        println("     PG(2,F_q) pulled back through g) -- evidence for genuine algebraic")
        println("     resonance, not an artifact of trying many alphas.")
    else
        println("  -> best-alpha deviation is not meaningfully better than the multiple-testing")
        println("     null at the same number of trials. No clear trace-form signature.")
    end

    return (; n, norms, n_distinct_norms, n_distinct_null_norms,
              chi2_norm, chi2_norm_null,
              best_alpha, best_chi2, best_chi2_null,
              best_n_distinct, best_n_distinct_null)
end

"""
    run_pullback(N, q; seed=1, top_frac=0.01, n_alpha_samples=200)

Full pipeline: rebuild D and its full spectrum diagnostic exactly as
phi_diagnostic.jl does (so top_ks matches what that script reported),
then run Stage 1 (residue inspection) and Stage 2 (norm/trace
pullback) on the same anomalous k's.

IMPORTANT: uses the SAME seed for singer_sidon_subset_native (via
full_spectrum_diagnostic) and for build_gf_q3_field, but these are
two INDEPENDENT constructions (independent random irreducible cubic,
independent generator search) -- they will in general produce
different field representations. What is invariant across both is
the EXPONENT structure (which i in 0:(Nq-1) have Tr(g^i)=0, i.e. the
Singer set D, and the abstract cyclic structure of exponents mod Nq)
-- NOT the specific field-element labels. Since Stage 1/2 operate on
residues r = k mod Nq (exponents, not field-representation-dependent
labels) and then map r -> g^r using field's OWN power table, this is
self-consistent: we are asking "do the anomalous EXPONENTS correlate
with algebraic structure of THIS run's field", which is the right
question (the Singer construction is unique up to the choice of
generator and cubic, and Tr/Norm-based correlation tests are
invariant to that choice up to a relabeling automorphism -- if there
is a genuine alpha or norm-fiber signature, it will show up under any
valid field realization, just possibly a different alpha).
"""
function run_pullback(N::Int, q::Int; seed::Int = 1, top_frac::Float64 = 0.01, n_alpha_samples::Int = 200)
    diag = full_spectrum_diagnostic(N, q; seed = seed, top_frac = top_frac)

    field = build_gf_q3_field(q, MersenneTwister(seed))
    @assert field.Nq == diag.Nq "Nq mismatch between diagnostic and field rebuild -- q inconsistent"

    residues = stage1_residue_inspection(diag.top_ks, diag.Nq)
    stage2 = stage2_norm_trace_pullback(residues, field; n_alpha_samples = n_alpha_samples, seed = seed)

    return (; diag, residues, stage2)
end

if abspath(PROGRAM_FILE) == @__FILE__
    println("=== Pullback test at the REAL constraint (target_q_exponent=0.2) ===")
    N1 = 2_000_000
    q1 = largest_prime_leq(max(2, floor(Int, N1^0.2)))
    run_pullback(N1, q1; seed = 1, top_frac = 0.01)

    println("\n=== Pullback test at diagnostic-only higher exponent (0.4), as a negative control ===")
    println("(phi_diagnostic.jl found NO mod-Nq clustering here -- Stage 1/2 should agree by finding nothing)")
    N2 = 2_000_000
    q2 = largest_prime_leq(max(2, floor(Int, N2^0.4)))
    run_pullback(N2, q2; seed = 1, top_frac = 0.01)
end
