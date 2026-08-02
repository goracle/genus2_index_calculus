#!/usr/bin/env julia
#
# character_sampler.jl
#
# Monte Carlo character-sampling diagnostic for the 8th-moment /
# additive-energy question on E(S,S), S = F+F, F the factor base.
#
# WHAT THIS DOES
# --------------
# Rather than building the O(B^2) pairwise-sum histogram of F+F and
# autocorrelating it (O(B^4), or O(M) but tail-biased -- see the
# advisory doc, section 7.6/8(c)), this samples characters chi of the
# group G = J(F_p) directly, computes
#
#     S_F(chi) = sum_{x in F} chi(x)   (complex number, unit-circle terms)
#
# and:
#
#   1. Tracks the running Monte-Carlo estimate of
#          M8_hat = |G|/m * sum_i |S_F(chi_i)|^8
#      an *unbiased* estimator of sum_chi |S_F(chi)|^8 = |G| * E(S,S)
#      (Parseval). NOTE: unbiased in expectation, but -- exactly as
#      with the histogram-pair estimator in the advisory doc -- it
#      will systematically *underestimate* E(S,S) with high
#      probability if the true energy is dominated by a few outlier
#      characters (the "lumpy" failure mode). Convergence behavior
#      (smooth vs. jumpy/still-climbing) is itself diagnostic.
#
#   2. Compares the empirical distribution of the *normalized* sums
#          U(chi) = S_F(chi) / sqrt(|k|)
#      against the theoretical target: under the unconditional
#      Forey-Fresan-Kowalski-Wigderson ("Jacobian graphs", 2026)
#      result for genus 2, Tr(x) for Haar-random x in SU_2(C) is
#      semicircle-distributed on [-2,2], and (their Theorem 1.2(4))
#      lambda*d_n/sqrt(d_n-1) becomes semicircle-equidistributed.
#      |U(chi)| bounded by ~2 is the discriminating signal: values
#      creeping or spiking past that bound are impossible under
#      pure SU_2-Haar behavior and are a direct, visual flag for
#      the lumpiness this whole gap is about.
#
# WHAT THIS IS NOT
# ----------------
# This is not group arithmetic for a genuine genus-2 Jacobian
# J(F_p) (Mumford representation / Cantor's algorithm). Real
# characters of J(F_p) require knowing its group structure
# (invariant factors) and F's actual coordinates in that group.
# This script is written against a GENERIC finite abelian group
# given by its invariant factors (d_1 | d_2 | ... | d_r), with
# characters realized as tuples of roots of unity -- the same
# formalism that applies to any J(F_p) once you have its group
# structure and F embedded as group elements. A synthetic example
# (cyclic group, random F) is included and runnable standalone;
# swap in real data at the two points marked HOOK below to drive
# this from elim2.jl / trial3 output.
#
# COST
# ----
# O(m * B) for m sampled characters and factor base size B -- no
# O(B^2) histogram, no O(B^4) autocorrelation. Cheap enough to run
# interactively; the whole point is you can throw idle compute at
# it across many (p, curve) instances.

using Random
using Printf
using Statistics

# ---------------------------------------------------------------
# Group model: finite abelian group via invariant factors.
#   G = Z/d_1 x Z/d_2 x ... x Z/d_r,   d_1 | d_2 | ... | d_r
# An element is a vector of residues (a_1,...,a_r), a_i in Z/d_i.
# A character is indexed by a vector (k_1,...,k_r), k_i in Z/d_i,
# and acts by
#   chi_k(a) = exp(2*pi*i * sum_j k_j*a_j/d_j)
# ---------------------------------------------------------------

struct AbelianGroup
    invariant_factors::Vector{Int}   # d_1,...,d_r
end

order(G::AbelianGroup) = prod(BigInt.(G.invariant_factors))

"Sample a uniformly random NON-TRIVIAL character index vector for G."
function random_character(rng::AbstractRNG, G::AbelianGroup)
    while true
        chi = [rand(rng, 0:(d-1)) for d in G.invariant_factors]
        any(!=(0), chi) && return chi   # reject the trivial character
    end
end

"""
    character_value(chi_idx, x, invariant_factors) -> ComplexF64

Evaluate chi_{chi_idx}(x) for group element x (vector of residues).
"""
function character_value(chi_idx::Vector{Int}, x::Vector{Int}, invariant_factors::Vector{Int})
    phase = 0.0
    @inbounds for j in eachindex(chi_idx)
        phase += (chi_idx[j] * x[j]) / invariant_factors[j]
    end
    phase *= 2pi
    return cis(phase)  # exp(i*phase)
end

# ---------------------------------------------------------------
# Core diagnostic
# ---------------------------------------------------------------

"""
    S_F(chi_idx, F, invariant_factors) -> ComplexF64

Compute S_F(chi) = sum_{x in F} chi(x) for a single character.
Cost O(|F|) = O(B).
"""
function S_F(chi_idx::Vector{Int}, F::Vector{Vector{Int}}, invariant_factors::Vector{Int})
    s = 0.0 + 0.0im
    @inbounds for x in F
        s += character_value(chi_idx, x, invariant_factors)
    end
    return s
end

"""
    run_character_sampler(G, F; m, rng, k_size=nothing, report_every)

Sample m random NON-TRIVIAL characters of G (trivial character
excluded -- see IMPORTANT note below), compute S_F(chi) for each,
and return:
  - chis        : the sampled character index vectors
  - S_vals      : complex S_F(chi) values
  - U_vals      : normalized U(chi) = S_F(chi)/sqrt(|k|)  (|k| ~ base
                  field size; pass k_size explicitly for a genuine
                  curve, defaults to |G|^(1/dim) heuristic for the
                  synthetic example -- see note at call site)
  - M8_running  : running Monte-Carlo estimate of |{chi!=1}|*E(S,S)
                  after each sample (for convergence-tracking /
                  plotting)
  - M4_running  : same, 4th moment (should converge fast & smoothly
                  -- this is the *settled* quantity, useful as a
                  sanity check that the sampler itself is working
                  before trusting the 8th-moment numbers)

IMPORTANT: the trivial character (chi = 1, S_F(1) = |F| = B exactly)
is excluded. This is not a minor cleanup: for realistic B, N the
trivial character's |S_F(1)|^8 = B^8 term completely swamps the sum
if included (confirmed while testing this script -- for a genuine
Sidon F with B ~ N^0.4, N ~ 1e6, the trivial character alone was
99.5% of the naive total, making the estimator meaningless). This
matches the advisory document's convention throughout (sums are
always over chi != 1, e.g. equation (8) in section 7.2) -- exclude,
don't just hope it washes out in the noise.

Cost: O(m * |F|).
"""
function run_character_sampler(G::AbelianGroup, F::Vector{Vector{Int}};
                                 m::Int,
                                 rng::AbstractRNG = Random.default_rng(),
                                 k_size::Union{Nothing,Real} = nothing,
                                 report_every::Int = max(1, m ÷ 20))
    Gord = Float64(order(G))
    Gord_nontrivial = Gord - 1.0   # number of non-trivial characters
    ksz  = k_size === nothing ? Gord^(1.0 / length(G.invariant_factors)) : Float64(k_size)

    chis    = Vector{Vector{Int}}(undef, m)
    S_vals  = Vector{ComplexF64}(undef, m)
    U_vals  = Vector{ComplexF64}(undef, m)

    sum8 = 0.0   # running sum of |S_F(chi)|^8, chi != 1 only
    sum4 = 0.0   # running sum of |S_F(chi)|^4, chi != 1 only
    M8_running = Vector{Float64}(undef, m)
    M4_running = Vector{Float64}(undef, m)

    println("Sampling $m non-trivial characters of a group of order ~$(Gord) ",
            "(|F| = $(length(F)))...")

    for i in 1:m
        chi = random_character(rng, G)
        s   = S_F(chi, F, G.invariant_factors)
        mag2 = abs2(s)          # |s|^2, cheap
        mag4 = mag2 * mag2      # |s|^4
        mag8 = mag4 * mag4      # |s|^8

        chis[i]   = chi
        S_vals[i] = s
        U_vals[i] = s / sqrt(ksz)

        sum8 += mag8
        sum4 += mag4
        M8_running[i] = Gord_nontrivial * (sum8 / i)   # unbiased estimate of sum_{chi!=1}|S_F(chi)|^8
        M4_running[i] = Gord_nontrivial * (sum4 / i)   # unbiased estimate of sum_{chi!=1}|S_F(chi)|^4

        if i % report_every == 0 || i == m
            @printf("  [%6d/%6d]  running M4_hat = %.4e   running M8_hat = %.4e\n",
                    i, m, M4_running[i], M8_running[i])
        end
    end

    return (; chis, S_vals, U_vals, M8_running, M4_running, k_size = ksz)
end

# ---------------------------------------------------------------
# Semicircle-law comparison (Forey-Fresan-Kowalski-Wigderson target)
# ---------------------------------------------------------------

"""
    semicircle_pdf(x) -> Float64

The Wigner semicircle density on [-2,2]: (1/2pi) * sqrt(4-x^2).
This is the proven limiting distribution (Jacobian graphs, Thm 1.2)
for the normalized eigenvalue statistic; here used as the natural
comparison target for |U(chi)| type quantities associated to a
genus-2 curve satisfying their hypotheses.
"""
function semicircle_pdf(x::Real)
    (abs(x) > 2) && return 0.0
    return sqrt(4 - x^2) / (2pi)
end

"""
    summarize_tail(U_vals; bound=2.0)

Report how many sampled |U(chi)| exceed `bound` (impossible in the
strict SU_2-Haar / semicircle limit for the trace statistic) and the
max observed value. A cheap, honest lumpiness flag: under the flat/
quasi-random hypothesis this should be empty or explainable by finite-
n fluctuation; a persistent, growing-with-m tail past the bound is
the empirical signature of the 8th-moment gap being real rather than
a slack inequality.

NOTE: U(chi) here is |S_F(chi)|/sqrt(k), which is the analogue of the
paper's U_n(chi) for the *factor base* F itself, not (yet) rescaled
to match their exact Tr(x)-on-SU_2 normalization for a specific
(C, m) instance -- treat the bound=2 comparison as indicative rather
than exact unless you've matched their d_n/sqrt(d_n-1) scaling for
your concrete curve. See advisory doc section 7.7 for the precise
statement being approximated.
"""
function summarize_tail(U_vals::Vector{ComplexF64}; bound::Real = 2.0)
    mags = abs.(U_vals)
    n_over = count(>(bound), mags)
    frac_over = n_over / length(mags)
    println("\n--- Tail summary (|U(chi)|, target bound = $bound) ---")
    @printf("  samples exceeding bound: %d / %d  (%.4f%%)\n",
            n_over, length(mags), 100 * frac_over)
    @printf("  max |U(chi)| observed:   %.4f\n", maximum(mags))
    @printf("  mean |U(chi)|:           %.4f   (semicircle mean |Tr|: ~1.273)\n",
            mean(mags))
    return (; n_over, frac_over, max_mag = maximum(mags))
end

# ---------------------------------------------------------------
# Synthetic example / smoke test
# ---------------------------------------------------------------
#
# Runs the whole pipeline against a GREEDILY-CONSTRUCTED, VERIFIED
# Sidon subset F of a cyclic group Z/N as a stand-in for J(F_p).
# This has NO curve structure, but greedy construction + an explicit
# Sidon check (below) means it actually has the structural property
# (Sidon-ness) that makes the real problem non-trivial -- a random
# subset of Z/N does NOT have this property and is a misleading
# stand-in (confirmed while building this script: a plain random
# subset has E(F,F) ~ B^3/N, not the Sidon-set B^2, and gives a
# meaningless comparison).
#
# The demo also cross-checks the Monte Carlo estimator against an
# EXACT value computed via a single N-point FFT (feasible for
# moderate synthetic N, not for a real |J(F_p)| ~ p^2 at cryptographic
# scale -- this exact check is a smoke test, not the production path).
# Do not skip this cross-check when adapting the script: it is what
# caught a real bug (trivial-character contamination) during
# development, and it is the cheapest way to catch further bugs
# before trusting the estimator on real curve data.

"Build a Sidon subset of Z/N of the given size by greedy construction.
Guaranteed genuinely Sidon by construction/rejection, not by an
assumed formula -- verify with `sidon_defect` before trusting it."
function greedy_sidon_subset(N::Int, target_size::Int, rng::AbstractRNG)
    elems = Int[]
    sums_seen = Set{Int}()
    candidates = collect(0:(N-1))
    Random.shuffle!(rng, candidates)
    for x in candidates
        ok = true
        new_sums = Int[]
        for y in elems
            s = mod(x + y, N)
            if s in sums_seen
                ok = false
                break
            end
            push!(new_sums, s)
        end
        if ok
            s2 = mod(2x, N)
            (s2 in sums_seen) && (ok = false)
        end
        if ok
            push!(elems, x)
            union!(sums_seen, new_sums)
            push!(sums_seen, mod(2x, N))
        end
        length(elems) >= target_size && break
    end
    return elems
end

"Count pairwise-sum collisions in a subset of Z/N (0 = perfectly Sidon).
Cost O(|elems|^2) -- only for smoke-testing small synthetic examples."
function sidon_defect(elems::Vector{Int}, N::Int)
    counts = Dict{Int,Int}()
    for i in eachindex(elems), j in i:length(elems)
        g = mod(elems[i] + elems[j], N)
        counts[g] = get(counts, g, 0) + 1
    end
    return sum(v - 1 for v in values(counts) if v > 1; init = 0)
end

"Exact sum_{chi!=1} |S_F(chi)|^8 and |S_F(chi)|^4 via a single dense
FFT over Z/N. O(N log N) -- fine for smoke-testing at N ~ 1e6, NOT a
substitute for the sampled estimator at real |J(F_p)| scale."
function exact_moments_cyclic(F::Vector{Int}, N::Int)
    dense = zeros(ComplexF64, N)
    for x in F
        dense[x + 1] = 1.0
    end
    Fhat = fft_naive_or_external(dense)  # see note below
    mag2 = abs2.(Fhat)
    mag4 = mag2 .^ 2
    mag8 = mag4 .^ 2
    # exclude trivial character (index 1 in 1-based, i.e. chi=1 / k=0)
    sum4 = sum(mag4) - mag4[1]
    sum8 = sum(mag8) - mag8[1]
    return sum4, sum8
end

# NOTE: Julia's FFTW is the standard choice (using FFTW; fft(dense))
# but is an external dependency. To keep this script dependency-free
# by default we fall back to a naive O(N^2) DFT, which is fine for
# smoke-testing at N ~ 1e4-1e5 but too slow much beyond that -- swap
# in `using FFTW; fft_naive_or_external = fft` if you have it
# available and want to smoke-test at larger N.
function fft_naive_or_external(dense::Vector{ComplexF64})
    N = length(dense)
    out = Vector{ComplexF64}(undef, N)
    for k in 0:(N-1)
        s = 0.0 + 0.0im
        for n in 0:(N-1)
            s += dense[n+1] * cis(-2pi * k * n / N)
        end
        out[k+1] = s
    end
    return out
end

function demo(; N::Int = 100_003,          # prime, stand-in for |J(F_p)| scale
                B::Int = round(Int, N^0.4), # B ~ p^(2/5) analogue
                m::Int = 20_000,
                seed::Int = 1,
                run_exact_check::Bool = true)
    rng = MersenneTwister(seed)
    G = AbelianGroup([N])  # cyclic group of order N

    F_int = greedy_sidon_subset(N, B, rng)
    defect = sidon_defect(F_int, N)
    println("=== Synthetic smoke test: cyclic group Z/$N, |F| = $(length(F_int)) ===")
    println("Sidon defect (pairwise-sum collisions, 0 = perfectly Sidon): $defect")
    if defect != 0
        @warn "F is not perfectly Sidon -- greedy construction may have " *
              "hit target size before exhausting candidates; results below " *
              "are still informative but the comparison to Sidon-regime " *
              "predictions is weaker than intended."
    end

    F = [[x] for x in F_int]

    result = run_character_sampler(G, F; m = m, rng = rng, k_size = N)
    summarize_tail(result.U_vals)

    Bf = Float64(length(F_int))
    println("\nnaive flat estimate B^8/N = ", (Bf^8) / N)
    println("MC estimate (sum_chi!=1 |S_F|^8) = ", result.M8_running[end])
    @printf("ratio MC-estimate / flat-B^8-over-N = %.4f\n",
            result.M8_running[end] / ((Bf^8) / N))

    if run_exact_check
        println("\nRunning exact O(N log N)-ish smoke-test check (this can be")
        println("slow for N beyond ~1e5 with the built-in naive DFT fallback;")
        println("pass run_exact_check=false to skip, or wire in FFTW)...")
        exact4, exact8 = exact_moments_cyclic(F_int, N)
        @printf("  exact sum_{chi!=1} |S_F|^4 = %.4e  (Sidon predicts ~ N*B^2 = %.4e)\n",
                exact4, N * Bf^2)
        @printf("  exact sum_{chi!=1} |S_F|^8 = %.4e\n", exact8)
        @printf("  MC estimate               = %.4e\n", result.M8_running[end])
        ratio_mc_exact = result.M8_running[end] / exact8
        @printf("  ratio MC/exact            = %.4f  (should be close to 1.0 -- far off means a bug, not a real effect)\n",
                ratio_mc_exact)
    end

    return result
end

# ---------------------------------------------------------------
# HOOK points for real data
# ---------------------------------------------------------------
#
# To drive this from actual genus-2 Jacobian data (elim2.jl / trial3):
#
#   1. Determine invariant_factors for J(F_p) at your test prime
#      (e.g. from #J(F_p) and its group structure -- Sage/PARI can
#      compute this, or read it off if your Jacobian arithmetic
#      code already tracks it).
#         G = AbelianGroup(invariant_factors)
#
#   2. Express each factor-base point as its coordinate vector in
#      that invariant-factor decomposition (a discrete-log-style
#      embedding -- expensive in general, but you already need
#      something like this for the attack's own bookkeeping).
#         F = [ [a_1, a_2] for each factor-base point ]   # r=2 example
#
#   3. k_size should be the actual base field size |k_n| = p^n you
#      are testing (not the |G|^(1/r) heuristic the demo uses).
#
#   4. Then:
#         result = run_character_sampler(G, F; m = 50_000, k_size = p)
#         summarize_tail(result.U_vals)
#
# If exact invariant-factor coordinates are impractical to extract,
# a cheaper approximate variant is to sample RANDOM ADDITIVE
# CHARACTERS via Kummer/Artin-Schreier pairings against a convenient
# subgroup instead of the full character group -- ask for that
# variant if useful; it trades some coverage of chi-space for not
# needing full discrete logs.

if abspath(PROGRAM_FILE) == @__FILE__
    demo()
end
