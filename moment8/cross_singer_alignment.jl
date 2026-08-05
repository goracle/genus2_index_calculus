#!/usr/bin/env julia
#
# cross_singer_alignment.jl
#
# Tests the PREMISE behind "sum several Singer sets and let their
# phases at each other's peak frequencies cancel" (per chat) BEFORE
# building the expensive union experiment.
#
# ============================================================
# REVISION 2 (this version): the previous two versions both tried to
# find a single canonical "own peak frequency" k_i* per set via
# argmax and compare cross-set phases AT THAT ONE FREQUENCY. Both were
# wrong, for the same underlying reason:
#
#   V1 (plain argmax over 1:(N-1)): found k_i*=1 (or another tiny k)
#   for EVERY set regardless of q or seed. D's integer representatives
#   are confined to the short interval [0, Nq-1] inside the much
#   larger Z/N (e.g. Nq=307 vs N=2,000,000) -- ANY interval-confined
#   set, Singer or not, has |S_hat(k)| heavily concentrated at LOW k
#   purely from interval geometry (the "confinement" artifact
#   phi_diagnostic.jl was built to separate from real resonance). V1
#   measured "this set starts near 0" for every set, hence the
#   spurious +1.000 cross-alignment across the board.
#
#   V2 (argmax with a hard exclusion band around confinement
#   multiples of N/Nq): ran, and EVERY reported k_i* landed at
#   dist_to_grid == confinement_guard_frac exactly (verified
#   numerically: 10/10 across both test runs sat at 0.1500-0.1501,
#   the exact boundary of the excluded band). This is because the
#   confinement envelope decays SMOOTHLY and MONOTONICALLY moving away
#   from a confinement multiple (verified directly: |S_hat(k)|^8 for a
#   plain random Nq-confined subset decreases gradually over the whole
#   range checked, no sharp falloff) -- so a hard exclusion band just
#   relocates the argmax to the band's own edge, which is STILL
#   dominated by the confinement envelope, not by anything
#   Singer-specific. No choice of confinement_guard_frac fixes this;
#   the whole "exclude a band, argmax the rest" strategy is the wrong
#   shape of fix.
#
# WHAT THIS VERSION DOES INSTEAD: stops trying to identify one
# canonical peak frequency via argmax at all. Reuses the machinery
# norm_trace_pullback.jl already validated (against a REAL finding --
# q=17 showed genuine mod-Nq clustering, q=331 did not, per that
# script's header):
#
#   1. top_k_peaks(S_hat, N; top_frac) -- the TOP-MASS FREQUENCY SLICE
#      (confinement-dominated frequencies INCLUDED, not excluded --
#      same as phi_diagnostic.jl; no attempt to hand-pick "the real
#      peak" out of the raw ranking).
#   2. Reduce those frequencies mod Nq and check how many DISTINCT
#      residues appear (phi_diagnostic.jl's confinement-vs-clustering
#      test): if the top-mass k's are spread over close to n_top
#      distinct residues, that slice is confinement/spectral-leakage
#      dominated -- there is no real algebraic resonance for a cross-
#      alignment question to be interesting about. If they collapse
#      onto far fewer residues, THAT is the actual resonance
#      (verified real for q=17 in prior work), and it's meaningful to
#      ask whether other sets reinforce or cancel it.
#   3. Cross-alignment, redefined as a MANY-FREQUENCY aggregate
#      statistic over the whole top-mass slice (not a single k*, which
#      is fragile to exactly which single frequency happens to win a
#      argmax): for set i's top-mass slice top_ks_i, compute
#
#        cross_energy(i,j) = sum_{k in top_ks_i} Re[conj(S_hat_i(k)) * S_hat_j(k)]
#
#      This is the real part of the (unnormalized) inner product
#      between set i's contribution and set j's contribution, summed
#      over exactly the frequencies that make up set i's anomalous
#      mass. If set j's presence would SHRINK set i's mass at those
#      frequencies (anti-aligned, cancellation-friendly),
#      cross_energy(i,j) is negative; if it would GROW it (aligned,
#      resonance), positive. Summing over the whole slice instead of
#      picking one k averages out single-frequency flukes, which a
#      lone argmax cannot do.
#
# NULL COMPARISON: same idea as before, but now calibrated for the
# SUMMED statistic (not a single cosine) -- built directly from
# shuffled/independent phase draws at the SAME frequencies, so the
# null correctly reflects the number of terms summed (n_top) rather
# than reusing the single-pair arcsine-cosine baseline from the
# previous version, which does not apply to a sum of many terms.
#
# WHAT THIS STILL DOES NOT DO: build the actual union and measure its
# exact M8. That remains a separate, more expensive experiment (needs
# a Sidon-compatibility check across sets, careful embedding-validity
# handling for the largest Nq, and the usual before/after normalized-
# ratio discipline). This script only checks whether cross-set
# cancellation is even structurally plausible at the frequencies that
# matter, using machinery already trusted in this codebase, so that
# expensive experiment isn't built on an unverified (and, as shown
# twice now, easy-to-get-wrong) peak-alignment premise.

using Printf
using Statistics
using Random

include("strategy_comparison.jl")   # singer_sidon_subset_native, largest_prime_leq,
                                     # compute_full_spectrum, top_k_peaks, sidon_defect

"""
    build_singer_sets(N::Int, qs::Vector{Int}; base_seed::Int = 1)
        -> Vector{NamedTuple}

Builds one Singer set per entry in `qs` (qs can repeat the same q
multiple times -- each call still gets an INDEPENDENT random
irreducible cubic and generator, since singer_sidon_subset_native
draws fresh randomness every call; repeating q tests "does resonance
persist across independent constructions of the SAME abstract group",
while varying q additionally tests across different Nq's/group
orders), all embedded in the same Z/N by literal inclusion.

Each set gets its own seed (base_seed + index) so runs are
reproducible but sets are genuinely independent of each other.

Returns a Vector of NamedTuples (; q, Nq, D, B, seed, defect), one per
requested set, after asserting the SAME N >= 2*(Nq-1) embedding-
validity guard used everywhere else in this project (checked
per-set, since different q's give different Nq's) and verifying
sidon_defect(D, N) == 0 for each.
"""
function build_singer_sets(N::Int, qs::Vector{Int}; base_seed::Int = 1)
    sets = NamedTuple[]
    for (i, q) in enumerate(qs)
        seed_i = base_seed + i
        rng = MersenneTwister(seed_i)
        D, Nq = singer_sidon_subset_native(q, rng)
        B = length(D)
        @assert N >= 2 * (Nq - 1) "set $i: Singer native modulus Nq=$Nq too close to N=$N " *
                         "for a valid embedding (need N >= 2*(Nq-1)) -- lower q or grow N"
        defect = sidon_defect(D, N)
        if defect != 0
            @warn "set $i (q=$q, seed=$seed_i): nonzero sidon_defect=$defect -- " *
                  "this set's own spectrum/mass-slice numbers are untrustworthy"
        end
        push!(sets, (; q, Nq, D, B, seed = seed_i, defect))
    end
    return sets
end

"""
    mass_slice_clustering(top_ks::Vector{Int}, Nq::Int) -> (n_distinct::Int, n_top::Int, residues::Vector{Int})

phi_diagnostic.jl's confinement-vs-clustering test, factored out for
reuse here: reduces `top_ks` mod Nq and counts distinct residues.
n_distinct close to n_top means the slice is confinement/spectral-
leakage dominated (no real algebraic resonance); n_distinct much less
than n_top means genuine clustering (the q=17-style signal).
"""
function mass_slice_clustering(top_ks::Vector{Int}, Nq::Int)
    residues = [mod(k, Nq) for k in top_ks]
    n_distinct = length(unique(residues))
    return (n_distinct, length(top_ks), residues)
end

"""
    cross_energy_matrix(sets::Vector{NamedTuple}, N::Int; top_frac::Float64 = 0.01)
        -> (cross_energy::Matrix{Float64}, top_ks_per_set::Vector{Vector{Int}},
            frac_of_M8_per_set::Vector{Float64}, clustering_per_set::Vector{Tuple{Int,Int}},
            S_hats::Vector{Vector{ComplexF64}})

Computes the full spectrum of every set (compute_full_spectrum) and
each set's top-mass frequency slice (top_k_peaks, same top_frac
convention as every other strategy in this project). Then builds the
m x m matrix

    cross_energy[i,j] = sum_{k in top_ks_i} Re[conj(S_hat_i(k)) * S_hat_j(k)]

-- the real part of the inner product between set i and set j,
restricted to EXACTLY the frequencies carrying set i's anomalous mass
(not a single k*, not set j's own slice). cross_energy[i,i] is always
positive (it's sum_k |S_hat_i(k)|^2 over that slice, a sum of
nonnegative terms) -- this is a sanity-check identity, not itself the
quantity of interest; see docstring above for how to read the
off-diagonal entries and mass_slice_clustering for whether set i's
slice is worth asking this question about in the first place.

Also returns each set's clustering statistic (n_distinct, n_top) from
mass_slice_clustering, since only sets with real clustering (not pure
confinement) are meaningful subjects for the cross-alignment question
-- see module docstring.
"""
function cross_energy_matrix(sets::Vector{NamedTuple}, N::Int; top_frac::Float64 = 0.01)
    m = length(sets)
    S_hats = [compute_full_spectrum(s.D, N) for s in sets]
    top_ks_per_set = Vector{Vector{Int}}(undef, m)
    frac_of_M8_per_set = Vector{Float64}(undef, m)
    clustering_per_set = Vector{Tuple{Int,Int}}(undef, m)
    residues_per_set = Vector{Vector{Int}}(undef, m)   # NEW: kept, not discarded -- see
                                                         # residue_overlap_report below, which
                                                         # needs the actual residue SETS (not
                                                         # just counts) to tell "same grid" apart
                                                         # from "locked phase on that grid".

    for i in 1:m
        top_ks, _, frac_of_M8 = top_k_peaks(S_hats[i], N; top_frac = top_frac)
        top_ks_per_set[i] = top_ks
        frac_of_M8_per_set[i] = frac_of_M8
        n_distinct, n_top, residues = mass_slice_clustering(top_ks, sets[i].Nq)
        clustering_per_set[i] = (n_distinct, n_top)
        residues_per_set[i] = residues
    end

    cross_energy = Matrix{Float64}(undef, m, m)
    for i in 1:m
        for j in 1:m
            s = 0.0
            @inbounds for k in top_ks_per_set[i]
                s += real(conj(S_hats[i][k+1]) * S_hats[j][k+1])
            end
            cross_energy[i, j] = s
        end
    end

    return (cross_energy, top_ks_per_set, frac_of_M8_per_set, clustering_per_set, S_hats, residues_per_set)
end

"""
    residue_overlap_report(sets, top_ks_per_set, residues_per_set, S_hats, N)

Separates two hypotheses that both produce "high cross-alignment" but
have very different implications for whether an opposite-signed /
cancelling union is findable:

  H1 (grid-only): same-Nq sets collapse onto the SAME small set of
     residues mod Nq (a property of Nq/the confinement geometry, not
     of the particular random cubic/generator draw), and cross-
     alignment is high simply because sets are compared at a shared
     handful of frequencies -- any two things supported on the same
     small frequency set will tend to show nonzero correlation just
     from concentration, independent of whether there's any deeper
     "resonance" locking their phases together.

  H2 (phase-lock): even restricting to residues that are ACTUALLY
     shared across independent draws, the phase relationship there is
     still strongly non-null -- i.e. it's not just "same grid" but
     "same grid AND correlated/locked phase on it", which would be a
     stronger and more surprising claim (something like a Gauss-sum
     identity fixing the phase up to a q-dependent constant,
     independent of the random cubic).

This function checks, for each pair of same-Nq sets (i,j):
  1. residue-set overlap: |residues_i ∩ residues_j| / |residues_i ∪ residues_j|
     (Jaccard). Near 1.0 -> H1 confirmed at the grid level (same grid
     every draw). Well below 1.0 -> grids differ across draws, so any
     observed alignment is NOT explained by a fixed shared grid, and
     H2-style phase-locking (or something else) is doing more work.
  2. restricted cross-alignment: recompute normalized cross-alignment
     using ONLY the frequencies in the shared grid (residues_i ∩
     residues_j, lifted back to actual top_ks -- since within one
     residue class mod Nq there can be multiple k's in the top-mass
     slice, e.g. k and k+Nq both anomalous, this uses every top_ks_i
     entry whose residue is in the intersection). If this stays high
     even after conditioning on "same grid", that's H2: phase is
     locked on the shared grid, not just co-located.

Does NOT attempt this for cross-Nq pairs (e.g. q=17 vs q=331): mod-Nq
residues live in different groups (Z/307 vs Z/109893) so "shared
residue" isn't even meaningful there without a common modulus; the
q=17-vs-q=331 block already showed ~0 alignment in the raw matrix, so
there's nothing to decompose for that block anyway.
"""
function residue_overlap_report(sets, top_ks_per_set, residues_per_set, S_hats, N)
    m = length(sets)
    println("\n--- Residue-overlap / phase-lock decomposition (same-Nq pairs only) ---")
    println("(H1: same grid every draw, alignment is just shared-frequency concentration.")
    println(" H2: even on the shared grid only, phase stays locked -- a stronger claim.)")
    any_pair = false
    for i in 1:m, j in (i+1):m
        sets[i].Nq != sets[j].Nq && continue   # only same-Nq pairs are comparable this way
        any_pair = true

        res_i = Set(residues_per_set[i])
        res_j = Set(residues_per_set[j])
        shared = intersect(res_i, res_j)
        union_sz = length(union(res_i, res_j))
        jaccard = union_sz == 0 ? NaN : length(shared) / union_sz

        # Restrict to top_ks_i whose residue mod Nq is in the shared set,
        # and separately top_ks_j whose residue is in the shared set --
        # then compute normalized alignment using ONLY those frequencies,
        # symmetrized over both index sets since they need not be
        # identical even when residues overlap (different k's, same
        # residue class, e.g. k and k+Nq).
        Nq = sets[i].Nq
        ks_i_shared = [k for k in top_ks_per_set[i] if mod(k, Nq) in shared]
        ks_j_shared = [k for k in top_ks_per_set[j] if mod(k, Nq) in shared]
        ks_shared = unique(vcat(ks_i_shared, ks_j_shared))

        if isempty(ks_shared)
            @printf("  set %d vs set %d (Nq=%d): jaccard=%.3f, no shared-grid frequencies to test phase-lock on\n",
                    i, j, Nq, jaccard)
            continue
        end

        num = 0.0
        denom_i = 0.0
        denom_j = 0.0
        @inbounds for k in ks_shared
            si = S_hats[i][k+1]
            sj = S_hats[j][k+1]
            num += real(conj(si) * sj)
            denom_i += abs2(si)
            denom_j += abs2(sj)
        end
        denom = sqrt(denom_i * denom_j)
        restricted_align = denom == 0.0 ? NaN : num / denom

        @printf("  set %d vs set %d (Nq=%d): jaccard=%.3f (%d shared / %d union residues), n_freqs_on_shared_grid=%d, restricted_align=%+.3f\n",
                i, j, Nq, jaccard, length(shared), union_sz, length(ks_shared), restricted_align)
    end
    if !any_pair
        println("  (no same-Nq pairs in this run -- nothing to decompose)")
    end
end

"""
    normalized_cross_alignment(cross_energy::Matrix{Float64}) -> Matrix{Float64}

Normalizes cross_energy[i,j] by sqrt(cross_energy[i,i] * cross_energy[j,j])
so entries live in roughly [-1,1] (like a correlation coefficient),
making magnitudes comparable ACROSS different (i,j) pairs and across
sets with very different B / slice sizes -- raw cross_energy scales
with both sets' magnitudes and the slice length, so is not comparable
as-is across pairs.
"""
function normalized_cross_alignment(cross_energy::Matrix{Float64})
    m = size(cross_energy, 1)
    norm = Matrix{Float64}(undef, m, m)
    for i in 1:m, j in 1:m
        denom = sqrt(max(cross_energy[i, i], 0.0) * max(cross_energy[j, j], 0.0))
        norm[i, j] = denom == 0.0 ? NaN : cross_energy[i, j] / denom
    end
    return norm
end

"""
    null_cross_alignment_stats(n_top::Int, n_trials::Int, rng::AbstractRNG) -> (mean, std)

Calibration baseline for the SUMMED statistic: for a slice of size
n_top, simulate cross_energy(i,j)-style sums where set j's phase at
each of the n_top frequencies is an INDEPENDENT uniform random draw
(i.e. genuinely unrelated to set i), normalized the same way as
normalized_cross_alignment, repeated n_trials times. This is what the
normalized statistic looks like under "no relationship between sets i
and j at these frequencies" -- NOT the same as the single-pair cosine
null from the previous version (that does not apply to a sum of
n_top>1 terms, which concentrates toward 0 as n_top grows, unlike a
single cosine).
"""
function null_cross_alignment_stats(n_top::Int, n_trials::Int, rng::AbstractRNG)
    vals = Vector{Float64}(undef, n_trials)
    for t in 1:n_trials
        # set i's own magnitudes at its n_top frequencies: arbitrary
        # positive weights are fine here since normalization divides
        # them out -- use unit magnitude for simplicity (only the
        # PHASE relationship is what null_cross_alignment_stats tests).
        phases_i = rand(rng, n_top) .* (2pi)
        phases_j = rand(rng, n_top) .* (2pi)
        num = sum(cos.(phases_j .- phases_i))
        # denom: sqrt(sum|Si|^2 * sum|Sj|^2) with unit magnitudes = n_top
        vals[t] = num / n_top
    end
    return (mean(vals), std(vals))
end

"""
    run_cross_alignment_check(; N, qs, base_seed=1, top_frac=0.01, n_null_trials=20_000)

Full pipeline: build sets, compute the cross-energy matrix and its
normalized form, report each set's mass-slice clustering (is there
even real resonance to ask this question about), print the normalized
cross-alignment matrix, calibrate against the appropriate summed-
statistic null, and give a verdict per the same three-way reading as
before (anti-aligned / aligned / indistinguishable-from-null) but now
computed correctly over the actual anomalous-mass frequency slice
instead of a single fragile argmax.
"""
function run_cross_alignment_check(; N::Int, qs::Vector{Int}, base_seed::Int = 1,
                                       top_frac::Float64 = 0.01, n_null_trials::Int = 20_000)
    m = length(qs)
    @assert m >= 2 "need at least 2 Singer sets to test cross-alignment"

    println("=== Cross-alignment check (v2, mass-slice based): $m independent Singer " *
            "sets, N=$N, top_frac=$top_frac ===")
    println("qs = $qs (repeats are independent constructions of the same abstract group -- " *
            "different random cubic/generator each time)")

    sets = build_singer_sets(N, qs; base_seed = base_seed)
    for (i, s) in enumerate(sets)
        @printf("  set %d: q=%d Nq=%d B=%d seed=%d sidon_defect=%d\n",
                i, s.q, s.Nq, s.B, s.seed, s.defect)
    end

    cross_energy, top_ks_per_set, frac_of_M8_per_set, clustering_per_set, S_hats, residues_per_set =
        cross_energy_matrix(sets, N; top_frac = top_frac)

    println("\nPer-set mass-slice clustering (phi_diagnostic.jl-style confinement-vs-resonance test):")
    any_resonant = false
    for i in 1:m
        n_distinct, n_top = clustering_per_set[i]
        pct_distinct = 100 * n_distinct / n_top
        resonant = n_distinct < 0.5 * n_top
        any_resonant |= resonant
        @printf("  set %d: top_frac=%.3f slice has %d freqs, frac_of_M8=%.4f, %d/%d distinct residues mod Nq (%.1f%%) -> %s\n",
                i, top_frac, n_top, frac_of_M8_per_set[i], n_distinct, n_top, pct_distinct,
                resonant ? "CLUSTERED (real resonance candidate)" : "scattered (confinement-dominated)")
    end
    if !any_resonant
        println("\n  NOTE: no set here shows real mod-Nq clustering at this q/N -- the cross-")
        println("  alignment numbers below describe confinement-slice interactions only, not")
        println("  genuine algebraic resonance (see q=17 vs q=331 in norm_trace_pullback.jl for")
        println("  what a real clustering signal looks like; try q's/N in that regime if you")
        println("  want a resonant case to test cross-alignment against).")
    end

    residue_overlap_report(sets, top_ks_per_set, residues_per_set, S_hats, N)

    norm_align = normalized_cross_alignment(cross_energy)

    println("\nNormalized cross-alignment matrix (row i = set i's own top-mass slice;\n" *
            "entry [i,j] = how aligned set j's contribution is with set i's, AVERAGED over\n" *
            "set i's whole anomalous-mass slice, not a single frequency; diagonal = 1.0 by\n" *
            "construction):")
    print("      ")
    for j in 1:m
        @printf("  set%-2d ", j)
    end
    println()
    for i in 1:m
        @printf("set%-2d ", i)
        for j in 1:m
            v = norm_align[i, j]
            if isnan(v)
                print("   NaN  ")
            else
                @printf(" %+.3f ", v)
            end
        end
        println()
    end

    off_diag = Float64[]
    off_diag_n_top = Int[]   # slice size backing each off-diagonal entry, for null calibration
    for i in 1:m, j in 1:m
        if i != j && !isnan(norm_align[i, j])
            push!(off_diag, norm_align[i, j])
            push!(off_diag_n_top, clustering_per_set[i][2])
        end
    end
    n_off = length(off_diag)
    mean_off = mean(off_diag)
    std_off = std(off_diag)

    # Null calibration: use the MEDIAN slice size among the off-
    # diagonal entries actually being compared (slice sizes are
    # usually close to the same top_frac*(N-1) value across sets here,
    # but not guaranteed identical if Nq's differ) as a representative
    # n_top for the null simulation.
    rng_null = MersenneTwister(base_seed + 12345)
    median_n_top = Int(round(median(off_diag_n_top)))
    mean_null, std_null = null_cross_alignment_stats(median_n_top, n_null_trials, rng_null)

    @printf("\nOff-diagonal summary: mean=%.4f std=%.4f (n=%d pairs)\n", mean_off, std_off, n_off)
    @printf("Null (independent-phase, same slice size n_top=%d) baseline: mean=%.4f std=%.4f (n=%d trials)\n",
            median_n_top, mean_null, std_null, n_null_trials)

    se_null = std_null / sqrt(max(n_off, 1))
    z = (mean_off - mean_null) / se_null

    println("\n--- Verdict ---")
    if n_off < 6
        println("Only $n_off off-diagonal pairs -- too few for a statistically confident")
        println("verdict either way. Increase the number of Singer sets (qs) before trusting")
        println("the sign/magnitude of mean_off as a general property of this family.")
    elseif z < -2.0
        println("Off-diagonal mean is significantly BELOW the independent-phase null " *
                "(z=$( round(z, digits=2) )):")
        println("cross-set contributions at each set's own anomalous-mass frequencies look")
        println("systematically ANTI-aligned, more than chance predicts. This SUPPORTS the")
        println("naive cancellation proposal -- building the union experiment (with a Sidon-")
        println("compatibility check across sets) is worth doing next.")
    elseif z > 2.0
        println("Off-diagonal mean is significantly ABOVE the independent-phase null " *
                "(z=$( round(z, digits=2) )):")
        println("cross-set contributions look systematically ALIGNED -- 'family resonance':")
        println("these Singer sets tend to reinforce, not cancel, each other's anomalous mass.")
        println("Unioning would likely make M8 WORSE, not better, at least for the specific")
        println("frequencies driving each set's own excess mass.")
    else
        println("Off-diagonal mean is statistically indistinguishable from the independent-")
        println("phase null (z=$( round(z, digits=2) )). Cross-set phase relationships at each")
        println("set's own anomalous-mass frequencies look like independent random draws -- no")
        println("systematic cancellation OR reinforcement to exploit here. A union experiment")
        println("could still get lucky on a given seed, but there is no structural reason to")
        println("expect it to work reliably from this data.")
    end
    if !any_resonant
        println("\n(Also see the clustering note above: with no genuinely resonant set in this")
        println("run, the verdict above describes confinement-slice behavior, not the algebraic")
        println("resonance case the original proposal was really about.)")
    end

    return (; sets, cross_energy, norm_align, top_ks_per_set, frac_of_M8_per_set,
              clustering_per_set, off_diag, mean_off, std_off, mean_null, std_null, z)
end

if abspath(PROGRAM_FILE) == @__FILE__
    # Use the SAME (N, q) regime norm_trace_pullback.jl already found a
    # real clustering signal in (q=17, target_q_exponent=0.2-ish),
    # rather than an arbitrary spread of q's -- this run is specifically
    # designed to have at least one genuinely resonant set to test
    # cross-alignment against, unlike picking q's blind.
    N = 2_000_000

    println("### Run A: repeated q=17 (same abstract group Z/307, independent random ###")
    println("###         cubic/generator each time) -- q=17 is the KNOWN-clustering case ###")
    println("###         from norm_trace_pullback.jl; tests whether that resonance persists ###")
    println("###         across independent constructions of the SAME q, and whether other ###")
    println("###         draws of the same q help or hurt each other. ###\n")
    run_cross_alignment_check(; N = N, qs = fill(17, 5), base_seed = 1)

    println("\n\n### Run B: varied q including q=17 and q=331 (norm_trace_pullback.jl's ###")
    println("###         non-clustering NEGATIVE CONTROL) -- tests whether a genuinely ###")
    println("###         resonant set (q=17) is helped or hurt by non-resonant neighbors. ###\n")
    run_cross_alignment_check(; N = N, qs = [17, 17, 331, 331, 17], base_seed = 100)

    println("\n(Rerun with more sets / different base_seed / larger top_frac before treating a")
    println("single run's verdict as conclusive -- this is a first pass, same caveat as")
    println("phi_diagnostic.jl's own smoke tests.)")
end
