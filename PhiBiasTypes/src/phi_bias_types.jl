# =============================================================================
#  phi_bias_types.jl  --  PhiBiasStat struct, constants, and constructor.
#
#  Part of the phi_bias_diag diagnostic suite.  See phi_bias_diag.jl for the
#  full theory recap and diagnostic inventory.
# =============================================================================

# ---------------------------------------------------------------------------
#  PhiBiasStat — per-thread accumulator
# ---------------------------------------------------------------------------
mutable struct PhiBiasStat
    total          ::Int     # valid phi steps recorded
    a_zero         ::Int     # steps where a == 0
    a_zero_split   ::Int     # a==0 AND residual split over 𝔽ₚ
    a_zero_fb      ::Int     # a==0 AND both R,S in FB (0-LP or 1-LP)

    # Split histogram: a partitioned into nbuckets equal-width buckets over 𝔽ₚ.
    # Entry i counts split steps whose a fell in bucket i.
    # nbuckets = isqrt(p) gives O(√p) buckets — coarse enough to accumulate
    # signal in a typical run, fine enough to reveal non-uniform clustering.
    split_hist     ::Vector{Int}
    nonsplit_hist  ::Vector{Int}   # parallel histogram for non-split steps

    # Image-collision counter: incremented when two different a-values (within
    # the same D-keyed window) produce the same (c1_rs, c0_rs) pair.
    # We maintain only the *current* D's image set (a rolling window keyed on
    # the Mumford (u0,u1,v0,v1) quadruple) so memory stays bounded.
    image_collisions ::Int
    _img_key         ::NTuple{4,Int}        # Mumford key of the current D
    _img_seen        ::Set{NTuple{2,Int}}   # (c1,c0) pairs seen for _img_key

    # ---- Seq 1: run-length distribution ----------------------------------------
    # _run_is_split: whether the current in-progress run is of split steps.
    # _run_len:      length of the current in-progress run (not yet committed).
    # run_hist_split[k]     = number of completed split-runs of exactly length k.
    # run_hist_nonsplit[k]  = number of completed non-split runs of length k.
    # Capped at MAX_RUN_LEN; runs longer than that accumulate in bin MAX_RUN_LEN.
    _run_is_split    ::Bool
    _run_len         ::Int
    run_hist_split   ::Vector{Int}   # length MAX_RUN_LEN
    run_hist_nonsplit::Vector{Int}   # length MAX_RUN_LEN

    # ---- Seq 2: LP1-conj inter-arrival Fano factor + conditional intensity -----
    # raw-step index at each 1-LP-conj hit; used post-run to compute inter-arrival
    # gaps → variance/mean (Fano factor ≈ 1 ↔ Poisson; >> 1 ↔ clustering).
    lp1_conj_arrivals::Vector{Int}
    # Mumford key (CanonicalLP1Key = UInt128) at each emission, parallel to
    # lp1_conj_arrivals.  Used to detect whether temporally-close hits also share
    # algebraic structure (same key → same Jacobian neighbourhood).
    lp1_conj_keys    ::Vector{UInt128}

    # ---- Seq 3: post-LP anchor correlation -------------------------------------
    # Compare a-histograms conditioned on how the anchor P0 was chosen:
    #   post_lp_a_hist:  steps where P0 was the LP point from a prior LP event.
    #   baseline_a_hist: steps where P0 was drawn uniformly from the FB.
    # Same bucket layout as split_hist (isqrt(p) buckets over [0,p)).
    post_lp_a_hist      ::Vector{Int}
    baseline_a_hist     ::Vector{Int}
    _prev_anchor_was_lp ::Bool   # true iff the step just recorded used an LP-derived P0

    # ---- New 3: state-space a-region hotness ------------------------------------
    # lp1_conj_a_hist[bucket] = number of LP1-conj *emissions* whose triggering
    # phi step fell in bucket.  Compared to the overall split_hist to identify
    # dynamically hot a-regions: buckets where emissions are over-represented
    # relative to visit frequency.  Set by record_lp1_conj_hit! via bucket arg.
    lp1_conj_a_hist    ::Vector{Int}
    # lp1_conj_bucket_log: per-event a-bucket at each LP1-conj emission, in
    # chronological order parallel to lp1_conj_arrivals.  Used as the timeseries
    # for α₂ scaling diagnostics so that all α₂ sections focus on the LP1-conj
    # key space rather than the full walk step distribution.
    lp1_conj_bucket_log::Vector{Int}

    # ════════════════════════════════════════════════════════════════════════
    # α₂ scaling diagnostics (α₂-1 through α₂-11)
    # ════════════════════════════════════════════════════════════════════════
    # lp1_conj_key_blog: top-RENYI_BITS bucket index of every LP1-conj partial
    # (both stored and closed), in chronological order per thread.  Populated
    # by record_lp1_conj_partial! on every call to handle_1lp_conj!, so this
    # is the full partial stream — not just the ~O(100s) of emission closures.
    # UInt16 per entry = 2 bytes; 3.7M partials × 2 B = ~7 MB total.
    # Bucket index = top 14 bits of _lsm_fp(key), matching the LSM's Rényi buckets.
    lp1_conj_key_blog ::Vector{UInt16}

    # NOTE: step_bucket_log (Int/step), split_step_log (Bool/step), and
    # event_hash_log (UInt64/step) were removed — they grew to O(valid phi steps),
    # ~10 bytes × 125M steps = ~1.25 GB, causing OOM.  The α₂ diagnostics they
    # served are entirely superseded by lp1_conj_key_blog (the LP1-conj partial
    # stream), which is O(LP1-conj partials) ≪ O(walk steps).
    # The provenance check is replaced by a single running scalar _event_hash_state.
    _event_hash_state::UInt64
end

const MAX_RUN_LEN = 64   # run-length histogram cap (longer runs fold into bin 64)

# Per-thread vector caps for diagnostic accumulation.
# lp1_conj_key_blog is the high-volume path (every partial, not just closures);
# 5M UInt16 entries ≈ 10 MB/thread, ample for all α₂ spectral diagnostics.
# arrivals/keys/bucket_log are O(closures only) so 2M entries is a generous ceiling.
const MAX_LP1_CONJ_BLOG     = 5_000_000   # lp1_conj_key_blog cap (UInt16, 10 MB/thread)
const MAX_LP1_CONJ_ARRIVALS = 2_000_000   # lp1_conj_arrivals / keys / bucket_log cap

function PhiBiasStat(p::Int)
    nbuckets = max(1, isqrt(p))
    PhiBiasStat(
        # Surface 1-3 fields
        0, 0, 0, 0,
        zeros(Int, nbuckets),
        zeros(Int, nbuckets),
        0,
        (-1, -1, -1, -1),
        Set{NTuple{2,Int}}(),
        # Seq 1: run-length
        true,                          # _run_is_split (arbitrary initial)
        0,                             # _run_len
        zeros(Int, MAX_RUN_LEN),       # run_hist_split
        zeros(Int, MAX_RUN_LEN),       # run_hist_nonsplit
        # Seq 2: LP1-conj arrivals + keys
        Int[],
        UInt128[],
        # Seq 3: post-LP anchor
        zeros(Int, nbuckets),          # post_lp_a_hist
        zeros(Int, nbuckets),          # baseline_a_hist
        false,                         # _prev_anchor_was_lp
        # New 3: a-region hotness
        zeros(Int, nbuckets),          # lp1_conj_a_hist
        Int[],                         # lp1_conj_bucket_log
        # α₂ scaling diagnostics
        UInt16[],                      # lp1_conj_key_blog
        UInt64(0x9e3779b97f4a7c15),    # _event_hash_state
    )
end
