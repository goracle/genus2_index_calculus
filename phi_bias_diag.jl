# =============================================================================
#  phi_bias_diag.jl  --  Diagnostic instrumentation for a-parameter bias.
#
#  Theory recap (see comments in trial3_phi.jl for derivation):
#
#    In a genus-2 Jacobian walk the φ-construction yields a Mumford pair
#    whose a-coefficient (degree-2 leading term of the U-polynomial) encodes
#    the residual x-coordinate after the Vieta step.  Uniformity of a over 𝔽ₚ
#    is a necessary condition for the walk to behave as an unbiased random walk
#    over the Jacobian factor-base.  Any concentration of a near 0, near p/2,
#    or in any narrow sub-interval would:
#      (a) reduce the effective factor-base size, and
#      (b) break the independence assumption used in the complexity analysis.
#
#  The diagnostics are grouped into "surfaces" (static cross-sections of the
#  a-distribution) and "sequences" (time-ordered properties of the a-stream).
#
#  Surface 1 — Image collision rate:  counts steps where two distinct a-values
#    from the same discriminant D produce identical residual (c₁,c₀) pairs.
#    Non-zero → algebraically thin fibre; reduces effective entropy.
#
#  Surface 2 — Discriminant bias:  χ² test on the histogram of a mod p over
#    sqrt(p) uniform buckets.  χ²/dof >> 1 → non-uniform marginal.
#
#  Surface 3 — a=0 slice:  fraction of steps with a=0; a=0 steps are
#    algebraically degenerate (U has a double root at 0).
#
#  Seq 1 — Run-length distribution:  consecutive runs of split / non-split
#    steps.  KS test vs Geometric(1/2); long runs → positive autocorrelation.
#
#  Seq 2 — LP1-conj temporal analysis:  Fano factor, conditional intensity
#    ratio (CIR), Welch PSD, spectrogram, Allan factor, New 1-5 diagnostics,
#    and key fingerprint for LP1-conj arrival stream.
#
#  Seq 3 — Post-LP anchor correlation:  after a 1-LP event the next anchor
#    a-histogram vs the unconditional baseline.  KS divergence > 0.05 →
#    emission biases the subsequent anchor location.
#
#  α₂-1 through α₂-12 — Rényi-2 collision entropy scaling:  time-resolved
#    α₂(T), intra/inter-regime split, regime-conditioned α₂, collision
#    autocorrelation, burst size spectrum, ρ(T) ratio, key geometry
#    stationarity, fluctuation curvature, measure-preserving test, entropy
#    decomposition, effective independence / motifs, and per-bucket identity
#    autocorrelation.
#
#  New 1 — Density autocorrelation.
#  New 2 — Hot/cold window conditioning.
#  New 3 — State-space a-region hotness (requires lp1_conj_a_hist field).
#  New 4 — Multitaper PSD + spectral slope.
#  New 5 — Gap-distribution characterisation.
#
# =============================================================================

#include("phi_bias_types.jl")
include("phi_bias_record.jl")
include("phi_bias_merge.jl")
include("phi_bias_report_surfaces.jl")
include("phi_bias_report_seq2.jl")
include("phi_bias_report_seq3_alpha2.jl")

# ---------------------------------------------------------------------------
#  print_phi_bias_report — human-readable summary with χ² test.
# ---------------------------------------------------------------------------
function print_phi_bias_report(stat::PhiBiasStat; p::Int = 0)
    _report_header_and_surfaces!(stat; p = p)
    _report_seq2!(stat; p = p)
    _report_seq3_alpha2!(stat)

    @printf("──────────────────────────────────────────────────────────────────────\n")
    flush(stdout)
end
