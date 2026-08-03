#!/usr/bin/env julia
#
# new_invariants.jl
#
# Four candidate O(B^2)-preprocessing diagnostics/constructions,
# proposed as genuinely different directions from the five already
# tried and documented in strategy_comparison.jl (embedded Singer,
# quad-filtered Singer, frozen bad Fourier modes, pair-sum energy,
# random projection).
#
# CAVEAT ON "SECTION 7.6" / "SHKREDOV'S DICHOTOMY": several comments
# in strategy_comparison.jl assert, as settled fact, that no O(B^2)
# selection rule can be PROVEN to control the 8th moment. That claim
# comes from an "advisory doc" not present in this environment and is
# NOT independently verified here -- everything below is offered as
# an empirically-testable proxy/construction, not as a claimed proof
# of anything. Falsification experiments are the point.
#
# ORDER OF OPERATIONS (matches the priority given: proposals 1 and 4
# first, since they are RETROACTIVE -- pure post-hoc measurement on
# Sidon sets you already have and have already measured the true 8th
# moment for, no new construction needed):
#
#   1. gauss_character_score  -- multiplicative-character correlation
#      (proposal 1). O(B) per character, retroactive.
#   4. diff_set_energy         -- 2nd-order (difference-of-differences)
#      additive energy (proposal 4). O(B^2), retroactive.
#   3. structured_projection_score -- randomized-Hadamard-row sketch
#      of the 8th moment (proposal 3), a drop-in replacement for the
#      existing iid-uniform K=200 random-projection experiment.
#      O(B*K), retroactive (scores an already-built F; the point is
#      comparing sketch quality, not a new greedy construction).
#   2. discrepancy_score        -- L^2 discrepancy against arithmetic
#      progressions at dyadic scales (proposal 2). O(B log B),
#      retroactive.
#
# Each is retroactive by design for this pass: apply them to F's you
# already built (greedy, greedy_low_energy, embedded Singer, quad-
# filtered Singer) and already have true 8th-moment ratios for from
# strategy_comparison.jl's own output, and check correlation BEFORE
# writing any new greedy-with-this-tiebreak construction. This is the
# falsification step described for each proposal; see
# run_retroactive_correlation_check() at the bottom, which is the
# actual point of this file for this pass -- it does not build any
# new F, only scores F's the comparison script already produced.

using Random
using Printf
using Statistics

include("character_sampler.jl")        # AbelianGroup, S_F, greedy_sidon_subset, sidon_defect
include("scaling_sweep.jl")            # fit_growth_exponent
include("strategy_comparison.jl")      # greedy_low_energy_sidon_subset, singer_sidon_subset, etc.

# =================================================================
# Proposal 1: Gauss-sum / multiplicative-character correlation
# =================================================================

"""
    multiplicative_orders(p::Int, max_order::Int=6) -> Vector{Int}

Returns the orders d in 2:max_order that actually divide p-1, i.e.
the orders for which a genuine order-d multiplicative character of
F_p^* exists. Only cyclic-group N=p (prime) usage is assumed
elsewhere in this file, matching the rest of the codebase's cyclic
Z/N convention.
"""
function multiplicative_orders(p::Int, max_order::Int = 6)
    return [d for d in 2:max_order if (p - 1) % d == 0]
end

"""
    discrete_log_table(p::Int) -> (g, index_table)

Finds a generator g of F_p^* and returns index_table::Dict{Int,Int}
mapping x -> ind_g(x), x's discrete log base g, for every x in
1:(p-1). Any order-d multiplicative character value is then
chi_d(x) = exp(2*pi*i*(ind_g(x) mod d)/d) -- computed directly from
this ONE shared table, so gauss_character_score never needs to
rebuild a table per order.

PRIMITIVE-ROOT SEARCH: g is a primitive root of F_p^* (order p-1) iff
g^((p-1)/q) != 1 mod p for EVERY prime q dividing p-1. This requires
factoring p-1 once (O(sqrt(p)) via trial division, reusing
prime_factors from strategy_comparison.jl) and then
O(log((p-1)/q)) modular-exponentiation checks per candidate via
fast exponentiation by repeated squaring -- O(log p) per candidate,
expected O(1) candidates tried (a constant fraction of F_p^* are
primitive roots), so the search itself is negligible next to the
O(p) table-build pass below.

COST: O(p) to build the table (one pass of repeated multiplication by
g). This is fine when p is itself the O(B^2)-scale Nq used by the
Singer constructions, but for the plain greedy/greedy_low_energy
sweep's real N (which is NOT O(B^2) -- N ~ B^(5/2) at the stated
B ~ p^(2/5) scaling), building a full table is NOT within an O(B^2)
budget. This function is therefore retroactive/diagnostic-only here.
An eventual live O(B)-per-query construction would need a genuine
discrete-log ORACLE (e.g. baby-step giant-step, O(sqrt(p)) one-time
setup then O(log p) per query) rather than a full O(p) table, since
only B values are ever needed, not all p-1 -- not implemented here
since this pass is retroactive-only by design.
"""
function discrete_log_table(p::Int)
    pm1_factors = unique(prime_factors(p - 1))

    fast_pow_mod(base::Int, exp::Int, m::Int) = begin
        result = 1
        b = mod(base, m)
        e = exp
        while e > 0
            if e & 1 == 1
                result = mod(result * b, m)
            end
            b = mod(b * b, m)
            e >>= 1
        end
        return result
    end

    is_primitive_root(cand::Int) = all(q -> fast_pow_mod(cand, (p - 1) ÷ q, p) != 1, pm1_factors)

    g = 0
    for candidate in 2:(p-1)
        if is_primitive_root(candidate)
            g = candidate
            break
        end
    end
    @assert g != 0 "failed to find a primitive root mod $p (unexpected for prime p)"

    index_table = Dict{Int, Int}()
    sizehint!(index_table, p - 1)
    val = 1
    for i in 0:(p-2)
        index_table[val] = i
        val = mod(val * g, p)
    end
    return g, index_table
end

"""
    gauss_character_score(F::Vector{Int}, p::Int; max_order::Int=6) -> Dict{Int,Float64}

PROPOSAL 1 (retroactive scorer). For each multiplicative order d that
divides p-1 (up to max_order), computes

    T_d = |sum_{x in F, x != 0} chi_d(x)|^2

where chi_d is an order-d multiplicative character of F_p^*. Returns
a Dict d => T_d.

WHY THIS SHOULD CORRELATE WITH THE 8TH MOMENT: Gauss-sum theory links
additive and multiplicative characters -- a set F that is accidentally
biased toward (or away from) a multiplicative subgroup of small index
will have that bias reflected across MANY additive frequencies at
once (via the classical Gauss-sum identity relating additive
character sums restricted to multiplicative cosets back to sums over
all of F_p), which is a fundamentally different obstruction from
pairwise Sidon defect. Large T_d for some small d is evidence of
exactly the kind of "hidden structure invisible to 4th-moment data"
the frozen-mode and pair-sum-energy attempts were implicitly hoping
to catch.

COST: O(B) per order d once the shared discrete-log index table is
available; that table itself is O(p) to build (once total, reused
across every order -- see discrete_log_table), which is why this is
offered here as RETROACTIVE (evaluated on N's small enough that
O(p)=O(N) is tractable to just compute directly for a diagnostic
check) rather than as a live O(B^2)-budget construction step. See
discrete_log_table's docstring for what a genuine O(B)-per-query live
version would need (a discrete-log oracle, e.g. baby-step giant-step,
rather than a full table).

NOTE: x=0 is skipped (no multiplicative character of 0); if 0 in F
that element is simply excluded from every T_d, which is fine for a
diagnostic score.
"""
function gauss_character_score(F::Vector{Int}, p::Int; max_order::Int = 6)
    orders = multiplicative_orders(p, max_order)
    if isempty(orders)
        @warn "gauss_character_score: no multiplicative order in 2:$max_order divides p-1=$(p-1) -- returning empty"
        return Dict{Int,Float64}()
    end
    F_nonzero = [mod(x, p) for x in F if mod(x, p) != 0]

    # Build the O(p) discrete-log index table ONCE (not once per
    # order) -- chi_d(x) = exp(2*pi*i*(ind_g(x) mod d)/d) only needs
    # ind_g(x), the discrete log base a shared primitive root g, so
    # every requested order can reuse the same index table instead of
    # each paying its own O(p) primitive-root search + table build.
    g, index_table = discrete_log_table(p)

    scores = Dict{Int,Float64}()
    for d in orders
        s = 0.0 + 0.0im
        for x in F_nonzero
            idx = index_table[x]
            s += cis(2pi * (idx % d) / d)
        end
        scores[d] = abs2(s)
    end
    return scores
end

# =================================================================
# Proposal 4: second-order (difference-of-differences) additive
# energy of the difference set
# =================================================================

"""
    diff_set_energy(F::Vector{Int}, N::Int) -> Float64

PROPOSAL 4 (retroactive scorer). Builds the difference multiset
D = {a - b mod N : a,b in F, a != b} (|D| = B(B-1) elements, O(B^2)
to build) and computes

    E = sum_t r_D(t)^2

the additive (collision) energy of D ITSELF, where r_D(t) = #{(u,v)
in D x D : u - v = t}... equivalently and more simply computed here
as sum over t of (multiplicity of t in D)^2, i.e. the same
representation-function-squared idea as the discarded pair-sum
energy proposal, but applied ONE LEVEL UP: to the difference set,
not to F.

WHY THIS IS NOT THE DISCARDED PROPOSAL: sum_t r_2(t)^2 for r_2 the
representation function of F+F is constant across Sidon sets of fixed
size (every nonzero sum/difference occurs 0 or 1 times, by
definition of Sidon) -- that quantity has zero degrees of freedom and
was correctly discarded. diff_set_energy does NOT have this problem:
Sidonness only forces elements of D itself to arise from distinct
pairs in a controlled way (each nonzero difference value is hit by at
most... actually by exactly the Sidon property D can still have
repeated VALUES across different pairs only in the trivial +/-
symmetric-pair sense) -- but the multiplicity structure of D as a
multiset, i.e. how often a given difference-of-differences t = d1-d2
recurs, is NOT fixed by first-order Sidonness. This is the natural
next term in the moment hierarchy: sum_chi |S_F|^8 is the (expensive)
additive energy of the 4-fold sumset F+F+F+F; diff_set_energy is a
CHEAP O(B^2) proxy one level below that, built from D=F-F rather than
F+F+F+F, capturing whether F has second-order additive structure
beyond what Sidonness already guarantees.

COST: exactly O(B^2) -- D has B(B-1) elements by construction, and a
single histogram pass over D (using a Dict as a sparse counter, since
N can be far larger than B^2) is O(B^2) time and space.

FALSIFICATION: apply this to sets you have already measured the true
8th moment for (e.g. greedy vs quad-filtered-Singer at matched N,B) --
if this score does not track the same ordering the measured ratios
showed (even weakly, as the quad filter's rejection fraction did),
the invariant isn't picking up anything useful and should be dropped
before building any greedy-with-this-tiebreak construction.
"""
function diff_set_energy(F::Vector{Int}, N::Int)
    B = length(F)
    counts = Dict{Int,Int}()
    sizehint!(counts, B * (B - 1))
    @inbounds for i in eachindex(F), j in eachindex(F)
        i == j && continue
        t = mod(F[i] - F[j], N)
        counts[t] = get(counts, t, 0) + 1
    end
    E = 0.0
    for v in values(counts)
        E += Float64(v) * Float64(v)
    end
    return E
end

"""
    diff_set_energy_normalized(F::Vector{Int}, N::Int) -> Float64

diff_set_energy divided by B(B-1), the total mass of D -- gives a
per-element-pair average multiplicity-squared, more comparable across
different B than the raw sum. Since |D|=B(B-1) exactly for ANY set
(Sidon or not) with no repeated elements, this normalization is safe
and doesn't reintroduce a B-dependent artifact.
"""
function diff_set_energy_normalized(F::Vector{Int}, N::Int)
    B = length(F)
    B <= 1 && return 0.0
    return diff_set_energy(F, N) / (B * (B - 1))
end

# =================================================================
# Proposal 3: structured (randomized-Hadamard-row) projection score
# =================================================================

"""
    hadamard_frequencies(N::Int, K::Int, rng::AbstractRNG) -> Vector{Int}

Drop-in structured replacement for sample_fixed_characters's iid
uniform draw. Rather than K iid uniform frequencies in 1:(N-1) (the
existing, already-tried-and-weak approach from strategy_comparison.jl
Strategy 7), draws K frequencies as a RANDOM ARITHMETIC PROGRESSION
plus random offset: pick a random odd step s coprime to N (so
multiplication by s is a bijection on Z/N, preserving uniformity of
coverage) and a random start k0, then take {k0 + i*s mod N : i in
0:(K-1)}. This is the cheap cyclic-group stand-in for a randomized
Hadamard/subsampled-Fourier row selection (true Hadamard structure
needs a power-of-2 ambient dimension; Z/N here is the group already
in use throughout this codebase, so a random-AP frequency SET is the
natural analogue: it is far from a single frequency or a fully
unstructured iid sample, has provably flat coverage of residue
classes, and is the standard "structured randomness" trick used when
a true Hadamard basis isn't available).

WHY THIS SHOULD BEAT PLAIN IID (per proposal 3): structured sampling
schemes with flat coherence give norm-preservation (compressed-
sensing / Johnson-Lindenstrauss-flavored) guarantees that pure iid
sampling lacks -- iid draws can, with non-trivial probability, land a
disproportionate share of the K frequencies in a narrow band, which
is exactly the kind of variance that would explain the N~10^4/noisy
behavior already observed for the iid K=200 experiment. An AP-
structured Omega spreads coverage deterministically once k0/s are
fixed, removing that source of variance.

HONESTY CAVEAT: a random AP of frequencies in Z/N is offered here as
the natural cyclic-group ANALOGUE of a randomized Hadamard row
selection, not as a rigorously equivalent construction -- true
RIP/JL-type norm-preservation theorems are typically proven for
specific structured ensembles (subsampled Fourier/Hadamard matrices
with random sign flips, specific incoherence conditions) and this has
NOT been checked to satisfy those exact hypotheses. Treat the claim
above as a plausible mechanism motivating the experiment, not a
proven guarantee -- the falsification experiment below is what
actually decides whether it helps.

COST: O(K), same as the existing iid sampler.
"""
function hadamard_frequencies(N::Int, K::Int, rng::AbstractRNG)
    K = min(K, N - 1)
    s = 0
    while true
        cand = rand(rng, 1:(N-1))
        if gcd(cand, N) == 1
            s = cand
            break
        end
    end
    k0 = rand(rng, 1:(N-1))
    freqs = Vector{Int}(undef, K)
    k = k0
    for i in 1:K
        freqs[i] = k
        k = mod(k + s, N)
        k == 0 && (k = mod(k + s, N))  # skip the trivial character if landed on exactly
    end
    return unique(freqs)
end

"""
    structured_projection_score(F::Vector{Int}, N::Int, Omega::Vector{Int}) -> Float64

Exact sum_{chi in Omega} |S_chi(F)|^8 for a given (structured or not)
frequency set Omega, evaluated directly (no incremental bookkeeping
needed for a post-hoc/retroactive score on an already-built F).
O(B*K).
"""
function structured_projection_score(F::Vector{Int}, N::Int, Omega::Vector{Int})
    s = 0.0
    for k in Omega
        Sk = 0.0 + 0.0im
        for x in F
            Sk += cis(2pi * k * x / N)
        end
        s += abs2(Sk)^4
    end
    return s
end

# =================================================================
# Proposal 2: L^2 discrepancy against arithmetic progressions
# =================================================================

"""
    discrepancy_score(F::Vector{Int}, N::Int, B::Int; n_scales::Int=0,
                        progs_per_scale::Int=0, rng=Random.default_rng()) -> Float64

PROPOSAL 2 (retroactive scorer). Samples arithmetic progressions in
Z/N at O(log B) dyadic length scales (default: progs_per_scale ~ B,
n_scales ~ ceil(log2(B))) and computes the L^2 discrepancy

    D^2 = sum_{scale} sum_{sampled AP} (|F cap AP| - len(AP)*B/N)^2

WHY THIS SHOULD CORRELATE WITH THE 8TH MOMENT: Erdos-Turan-type
inequalities bound exponential-sum magnitudes (i.e. |S_chi|, the
quantity whose 8th moment is the actual objective) in terms of
discrepancy against progressions. Unlike a fixed/frozen character
set (which failed because it targets specific frequencies rather
than the mechanism that keeps ALL frequencies controlled together),
discrepancy against progressions at many scales is inherently a
multiscale, whole-spectrum-adjacent quantity.

COST: this implementation walks each sampled progression directly
(O(len) per progression, not a binning trick), so per-scale cost is
progs_per_scale * len(scale). With the defaults (progs_per_scale ~ B,
len(scale) ~ B/2^(scale-1)), total cost is B * sum_scale B/2^(scale-1)
~ 2*B^2 -- i.e. O(B^2), DOMINATED BY THE LARGEST SCALE (scale=1,
len~B), not O(B log B) as a binning-based version could achieve.
Still exactly within the stated O(B^2) budget, just not asymptotically
cheaper than the other proposals here -- a genuine O(B log B)
implementation would bin F's elements by residue class mod each
sampled step once per scale (O(B) per scale) rather than walking
progressions one at a time; left as a future optimization since B^2
is already within budget.

FALSIFICATION: same as the others -- compute retroactively on sets
already measured for the true 8th moment; if D^2 doesn't separate
strategies in the same direction the measured ratios do, drop it.
"""
function discrepancy_score(F::Vector{Int}, N::Int, B::Int;
                             n_scales::Int = 0,
                             progs_per_scale::Int = 0,
                             rng::AbstractRNG = Random.default_rng())
    n_scales = n_scales > 0 ? n_scales : max(1, ceil(Int, log2(max(B, 2))))
    progs_per_scale = progs_per_scale > 0 ? progs_per_scale : B

    Fset = Set(mod.(F, N))
    density = B / N
    D2 = 0.0

    for scale in 1:n_scales
        len = clamp(round(Int, B / (2.0^(scale - 1))), 1, N)
        for _ in 1:progs_per_scale
            step = rand(rng, 1:(N-1))
            start = rand(rng, 0:(N-1))
            cnt = 0
            x = start
            for _ in 1:len
                (x in Fset) && (cnt += 1)
                x = mod(x + step, N)
            end
            expected = len * density
            D2 += (cnt - expected)^2
        end
    end
    return D2
end

# =================================================================
# Retroactive correlation check -- the actual deliverable for this
# pass. Builds F via the strategies ALREADY KNOWN to differ in true
# 8th moment (greedy vs embedded-Singer at target_q_exponent=0.2,
# per the transcript: embedded-Singer's gamma~1.57 is dramatically
# WORSE than greedy's gamma~0.46 at the real B~N^0.2 constraint), and
# checks whether each proposal's cheap score separates them in the
# same direction -- BEFORE any new construction is built.
# =================================================================

"""
    run_retroactive_correlation_check(; Ns, seed)

For each N, builds F via :greedy (known good, low gamma) and via
embedded Singer at the REAL target_q_exponent=0.2 (known bad, high
gamma, per the already-observed transcript), then reports proposals
1, 3, and 4's scores side by side for both. (Proposal 2, discrepancy,
uses different N/B pairing machinery below in a separate loop since
it needs its own B.)

This does NOT re-run the character sampler -- the true 8th-moment
ordering between these two strategies is already established (greedy
gamma ~0.46 vs embedded-Singer-at-0.2 gamma ~1.57, from the provided
transcript); the question here is purely whether the cheap proxies
point the same direction.
"""
function run_retroactive_correlation_check(; Ns::Vector{Int} = [10_007, 100_003, 1_000_003, 10_000_019],
                                               seed::Int = 1)
    println("Retroactive check: does each cheap proxy separate greedy (KNOWN LOW gamma~0.46,",
            " good) from embedded-Singer@0.2 (KNOWN HIGH gamma~1.57, bad) in the same direction",
            " the true 8th moment does? Lower proxy score should track lower gamma if the proxy",
            " is any good.\n")

    println("N\tstrategy\tB\tgauss_T2\tgauss_T3\tdiffE_norm\tdiscrepancy_D2")

    for N in Ns
        B = round(Int, N^0.4)

        # --- greedy ---
        rng = MersenneTwister(seed)
        F_greedy = greedy_sidon_subset(N, B, rng)
        report_row(N, "greedy", F_greedy, N)

        # --- embedded Singer at target_q_exponent=0.2 ---
        # Mirrors run_singer_embedded_comparison's own q computation
        # exactly (q_target = floor(N^0.2), q = largest_prime_leq(q_target)),
        # so this is the SAME construction already measured in the
        # transcript (gamma~1.57 at this exponent), not a re-derived
        # approximation of it.
        q_target = max(2, floor(Int, N^0.2))
        q = largest_prime_leq(q_target)
        rng2 = MersenneTwister(seed)
        D_native, Nq = try
            singer_sidon_subset_native(q, rng2)
        catch e
            @warn "N=$N: embedded Singer construction failed at q=$q, skipping" exception=e
            continue
        end
        F_singer = D_native  # already valid residues mod N (Nq <= N by construction)
        report_row(N, "embedded_singer@0.2", F_singer, N)
    end
end

"Helper for run_retroactive_correlation_check: computes and prints all retroactive scores for one (N, F) pair."
function report_row(N::Int, label::String, F::Vector{Int}, p_for_gauss::Int)
    B = length(F)
    # gauss_character_score needs a PRIME modulus for the multiplicative-
    # character machinery (F_p^*); N in this sweep is already prime
    # (matches character_sampler.jl's convention of using prime N
    # throughout), so p_for_gauss = N directly.
    gauss_scores = try
        gauss_character_score(F, p_for_gauss; max_order = 6)
    catch e
        @warn "gauss_character_score failed for $label at N=$N" exception=e
        Dict{Int,Float64}()
    end
    t2 = get(gauss_scores, 2, NaN)
    t3 = get(gauss_scores, 3, NaN)

    diffE = diff_set_energy_normalized(F, N)

    rng_disc = MersenneTwister(1)
    D2 = discrepancy_score(F, N, B; rng = rng_disc)

    @printf("%d\t%s\t%d\t%.4e\t%.4e\t%.4e\t%.4e\n", N, label, B, t2, t3, diffE, D2)
end

# =================================================================
# Proposal 3's own falsification check: this is a SKETCH-QUALITY
# question, not a strategy-separation question -- for a single fixed
# F, does the structured (AP) Omega track the TRUE full-spectrum M8
# ratio more tightly than an iid Omega of the same size K? Answered
# by comparing both sketches' scores, normalized, against the true
# ratio already measured by run_projected_greedy_comparison in
# strategy_comparison.jl for the SAME (N, greedy F) -- reusing that
# already-known baseline ratio rather than re-running the character
# sampler here.
# =================================================================

"""
    run_structured_vs_iid_sketch_check(; Ns, K, seed)

For each N, builds F via plain greedy_sidon_subset (same construction
used throughout strategy_comparison.jl's baseline), then computes
BOTH an iid-uniform Omega score (via sample_fixed_characters, the
existing K=200 approach from Strategy 7) and a structured AP-Omega
score (via hadamard_frequencies, proposal 3) on the SAME F, reporting
both raw scores side by side.

This does not by itself prove which sketch is tighter -- that needs
comparing each sketch's score, normalized, against several
independent true-M8 measurements (from the character sampler) across
multiple F's of the same (N,B) and checking which sketch's score has
lower VARIANCE relative to the true value across those draws. That
full variance-reduction check is the actual falsification experiment
described in the original proposal and is left as a follow-up run
(it needs many repeated character-sampler calls per point, which is
a materially larger compute budget than this pass); what's provided
here is the mechanical comparison (both scores, same F, side by side)
needed to set that follow-up up.
"""
function run_structured_vs_iid_sketch_check(; Ns::Vector{Int} = [10_007, 100_003, 1_000_003, 10_000_019],
                                                K::Int = 200,
                                                seed::Int = 1)
    println("\nProposal 3 mechanical check: iid vs structured (AP) Omega score, same F, same K.")
    println("N\tB\tK_iid\tiid_score\tK_struct\tstructured_score\tratio(struct/iid)")

    for N in Ns
        B = round(Int, N^0.4)
        rng = MersenneTwister(seed)
        F = greedy_sidon_subset(N, B, rng)

        rng_iid = MersenneTwister(seed + 1)
        Omega_iid = sample_fixed_characters(N, K, rng_iid)
        score_iid = structured_projection_score(F, N, Omega_iid)

        rng_struct = MersenneTwister(seed + 1)
        Omega_struct = hadamard_frequencies(N, K, rng_struct)
        score_struct = structured_projection_score(F, N, Omega_struct)

        ratio = score_iid == 0 ? NaN : score_struct / score_iid
        @printf("%d\t%d\t%d\t%.4e\t%d\t%.4e\t%.4f\n",
                N, B, length(Omega_iid), score_iid, length(Omega_struct), score_struct, ratio)
    end
end

if abspath(PROGRAM_FILE) == @__FILE__
    run_retroactive_correlation_check()
    run_structured_vs_iid_sketch_check()
end
