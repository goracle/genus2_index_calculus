#!/usr/bin/env julia
#
# phi_diagnostic.jl
#
# Diagnoses WHY embedded-Singer's 8th moment blows up (gamma ~ 1.3-1.65
# in strategy_comparison.jl's embedded-Singer sweep) despite the
# embedding provably preserving sidon_defect == 0 (verified directly in
# run_singer_embedded_comparison -- see that function's comments: the
# embedding phi is literal inclusion of D's integer representatives
# into Z/N, which is injective and difference-preserving whenever
# N >= 2*(Nq-1)).
#
# Since M4 / Sidon-ness is provably clean here, a blown-up M8 must come
# from 4-FOLD additive structure (d1+d2-d3-d4) that pairwise Sidon-ness
# does not control -- NOT from phi failing to be a homomorphism (it
# demonstrably is one, on D, given the N>=2*(Nq-1) guard).
#
# This script:
#   1. Computes the FULL Fourier spectrum of the indicator of embedded
#      D (all N characters, via a direct DFT -- feasible only because
#      we deliberately use a SMALL N here, not the 10^7-scale sweep
#      points; see run_singer_embedded_comparison for that regime).
#   2. Isolates the top ~1% of characters by |S_F(chi)|^8 contribution.
#   3. Reports where those characters' frequencies sit relative to:
#        (a) the confinement scale Nq (does frequency k relate simply
#            to N/Nq, i.e. "this character is just resolving the fact
#            that D lives in an interval of size Nq << N"?)
#        (b) a coarse proxy for subfield-norm/trace structure: since
#            D is only available natively as exponents i in [0,Nq-1]
#            with Tr(g^i)=0 (see singer_sidon_subset_native), we pull
#            the anomalous frequencies back to the exponent domain
#            (k mod Nq, since D subset [0,Nq-1] subset Z, the relevant
#            reduction for comparing to Nq-periodic structure is k mod
#            Nq) and check for clustering there.
#
# INTERPRETATION GUIDE (per the chat discussion this implements):
#   - If anomalous k values are uniformly/pseudorandomly scattered mod
#     Nq -> NOT algebraic alignment; consistent with the SIMPLER
#     explanation that D's image is confined to an interval of size Nq
#     inside Z/N, and ANY high-enough-frequency character sees that
#     confinement (a generic fact about interval-supported sets, not
#     something specific to Singer's algebraic origin).
#   - If anomalous k values cluster tightly mod Nq (far fewer distinct
#     residues than a uniform draw would produce) -> suggests genuine
#     algebraic resonance with the Singer/PG(2,F_q) structure, worth
#     chasing the norm/trace/line correlation further.
#
# NOTE ON SCOPE: this does NOT implement the full norm-map/projective-
# line correlation test from the chat (that requires re-deriving each
# anomalous exponent's field element via the g^i power table and
# testing Tr/N_{F_q^3/F_q} correlation directly) -- it implements the
# cheaper, decisive FIRST filter: confinement vs. non-confinement. If
# this shows confinement (expected, given the reasoning above), the
# heavier norm/trace test is not needed to explain the effect; if it
# shows genuine clustering beyond what confinement alone predicts,
# THAT is the signal to go implement the full pullback-to-PG(2,F_q)
# correlation test.

using Printf
using Statistics

include("strategy_comparison.jl")   # also provides compute_full_spectrum, top_k_peaks
                                     # (the exact-DFT + peak-ranking helpers used below --
                                     # moved there, not duplicated here, so the peak-pruning
                                     # experiment in strategy_comparison.jl can reuse them
                                     # without strategy_comparison.jl needing to include
                                     # THIS file back, which would be circular)

"""
    full_spectrum_diagnostic(N, q; seed=1, top_frac=0.01)

Builds the native Singer set D (order Nq = q^2+q+1), embeds it in Z/N
by literal inclusion (matching run_singer_embedded_comparison exactly),
computes the FULL N-point DFT of D's indicator function directly (not
via character_sampler's Monte Carlo estimate -- this is EXACT, no
sampling noise, which is only feasible because N is kept small here),
and reports:

  - the top `top_frac` fraction of nonzero-frequency k by |S_hat(k)|^8
  - each such k's reduction mod Nq (the confinement-scale test)
  - the effective number of distinct k mod Nq values among the
    anomalous set vs. what a uniform random draw of the same COUNT
    would produce (a simple clustering-vs-uniform check)

Requires N small enough for an O(N^2) direct DFT (N up to a few
thousand is fine; this is a diagnostic, not the production sweep).
"""
function full_spectrum_diagnostic(N::Int, q::Int; seed::Int = 1, top_frac::Float64 = 0.01)
    @assert N >= 2 "N too small"
    rng = MersenneTwister(seed)
    D, Nq = singer_sidon_subset_native(q, rng)
    B = length(D)
    @assert N >= 2 * (Nq - 1) "embedding invalid at this N,q (need N >= 2*(Nq-1)); " *
                              "shrink q or grow N -- see run_singer_embedded_comparison"

    defect = sidon_defect(D, N)
    @printf("N=%d  q=%d  Nq=%d  B=%d  sidon_defect(mod N)=%d\n", N, q, Nq, B, defect)
    defect != 0 && @warn "nonzero defect -- embedding invalid at this (N,q), diagnostic results untrustworthy"

    # Direct O(N*B) DFT: S_hat(k) = sum_{x in D} exp(2*pi*i*k*x/N), for
    # every nonzero k in 0:(N-1). This is EXACT (no Monte Carlo), which
    # is the point -- character_sampler's threaded sampler only
    # estimates a running mean over a RANDOM subset of characters; here
    # we want every character's exact value so "top 1%" is a real
    # ranking, not a noisy one.
    S_hat = compute_full_spectrum(D, N)

    top_ks, top_mags8, frac_of_M8 = top_k_peaks(S_hat, N; top_frac = top_frac)
    n_top = length(top_ks)

    @printf("Top %.2f%% of characters (%d of %d nonzero freqs) account for %.4f%% of total |S|^8 mass\n",
            100 * top_frac, n_top, N - 1, 100 * frac_of_M8)

    # --- Confinement-scale test: reduce anomalous k mod Nq ---
    # WHY THIS TEST: D's image (via phi = literal inclusion) is confined
    # to the interval [0, Nq-1] inside Z/N. A character chi_k restricted
    # to functions supported on that interval behaves, to first order,
    # like a character of PERIOD roughly N/gcd(k,N) folded against an
    # interval of width Nq -- the standard signature is that |S_hat(k)|
    # is large whenever k is a multiple of (or close to a multiple of)
    # N/Nq, PURELY from the interval geometry, with no reference to
    # Singer's internal algebraic structure. So: check whether the
    # anomalous k's cluster near multiples of N/Nq (confinement -- the
    # "boring", non-algebraic explanation) as opposed to being spread
    # uniformly mod Nq (which would leave confinement as a live
    # explanation without being confirmed) or clustering at some OTHER
    # residue set mod Nq unrelated to N/Nq (which would point toward
    # genuine algebraic resonance with the Singer set's structure and
    # motivate the heavier norm/trace pullback test).
    approx_period = N / Nq
    dists_to_grid = [abs(mod(k / approx_period, 1.0) - round(mod(k / approx_period, 1.0)))
                     for k in top_ks]
    mean_dist_to_grid = mean(dists_to_grid)
    # Null comparison: same statistic for a UNIFORM random sample of
    # the same size, to know what "no confinement signature" looks like.
    rng2 = MersenneTwister(seed + 999)
    null_ks = rand(rng2, 1:(N-1), n_top)
    null_dists = [abs(mod(k / approx_period, 1.0) - round(mod(k / approx_period, 1.0)))
                  for k in null_ks]
    mean_dist_null = mean(null_dists)

    @printf("\n--- Confinement-scale test (period ~ N/Nq = %.3f) ---\n", approx_period)
    @printf("  mean distance-to-nearest-grid-point, anomalous k's: %.4f  (0=exactly on grid, 0.25=uniform-random expectation)\n",
            mean_dist_to_grid)
    @printf("  same statistic for a uniform-random k sample:      %.4f  (null baseline)\n", mean_dist_null)
    if mean_dist_to_grid < 0.5 * mean_dist_null
        println("  -> anomalous frequencies sit much closer to multiples of N/Nq than chance:")
        println("     CONSISTENT WITH CONFINEMENT (interval-support artifact), not necessarily")
        println("     algebraic resonance with the Singer/PG(2,F_q) structure specifically.")
    else
        println("  -> anomalous frequencies are NOT preferentially near multiples of N/Nq.")
        println("     Confinement alone does not explain the anomaly -- worth pursuing the")
        println("     norm/trace/projective-line pullback test next.")
    end

    # --- Clustering mod Nq: are the anomalous k's spread out or bunched? ---
    # WHY: if phi were "seeing" specific algebraic substructure (norm
    # map, trace form, a handful of projective lines), we'd expect the
    # anomalous k mod Nq values to land on a SMALL, repeated set of
    # residues (far fewer distinct values than n_top). If they're
    # essentially all distinct (close to n_top distinct residues out of
    # n_top samples), that's consistent with pseudorandom/confinement
    # behavior rather than a small number of "resonant" algebraic modes.
    top_k_mod_Nq = [mod(k, Nq) for k in top_ks]
    n_distinct = length(unique(top_k_mod_Nq))
    @printf("\n--- Clustering mod Nq test ---\n")
    @printf("  anomalous k's mod Nq: %d distinct residues out of %d samples (%.1f%% distinct)\n",
            n_distinct, n_top, 100 * n_distinct / n_top)
    if n_distinct < 0.5 * n_top
        println("  -> substantial repetition: anomalous characters cluster onto a SMALL set of")
        println("     residues mod Nq. This is the signature to chase with the full norm/trace/")
        println("     projective-line pullback test -- possible genuine algebraic resonance.")
    else
        println("  -> anomalous k's mod Nq are close to all-distinct: no strong clustering onto")
        println("     a small algebraic subset. Consistent with pure spatial confinement/spectral")
        println("     leakage from the interval-support geometry, not algebraic alignment.")
    end

    return (; N, q, Nq, B, defect, D, S_hat, top_ks, top_mags8, frac_of_M8,
              mean_dist_to_grid, mean_dist_null, n_distinct, n_top)
end

if abspath(PROGRAM_FILE) == @__FILE__
    # NOTE ON DEFAULTS: at the REAL constraint (target_q_exponent=0.2),
    # q stays small even out to N=20_000_000 (q~28, Nq~813) -- this is
    # inherent to the 0.2 exponent, not a limitation of this script.
    # Cost here is O(N*B), so N can be pushed much larger than the
    # threaded sampler's sweep points while staying cheap. Two example
    # runs below: one at the REAL exponent (0.2) at a large N, and one
    # at a diagnostic-only higher exponent (0.4, matching the regime
    # where strategy_comparison.jl's own sweep shows the sharpest
    # blowup, gamma up to ~1.65) where q is large enough to give the
    # mod-Nq clustering test real statistical power (more distinct
    # residues to distinguish clustering from uniform).

    println("=== Run 1: real constraint, target_q_exponent=0.2 ===")
    N1 = 2_000_000
    q1 = largest_prime_leq(max(2, floor(Int, N1^0.2)))
    full_spectrum_diagnostic(N1, q1; seed = 1, top_frac = 0.01)

    println("\n=== Run 2: diagnostic-only higher exponent, target_q_exponent=0.4 ===")
    N2 = 2_000_000
    q2 = largest_prime_leq(max(2, floor(Int, N2^0.4)))
    full_spectrum_diagnostic(N2, q2; seed = 1, top_frac = 0.01)

    println("\n(Increase N and/or try several seeds before treating a single run's")
    println("confinement-vs-clustering verdict as conclusive -- this is a first pass.)")
end
