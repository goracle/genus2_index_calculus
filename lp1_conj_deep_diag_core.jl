# =============================================================================
#  lp1_conj_deep_diag_core.jl
#
#  Shared infrastructure for LP1-conj deep diagnostics:
#    • Global constants
#    • ConjDeepStat struct + constructor
#    • merge_conj_deep_stats
#    • Hot-path recording functions:
#        record_conj_deep_miss!
#        record_conj_deep_step!
#        record_conj_deep_opcode!
#        record_d16_emission!
#    • Math helpers: _gini, _hill_exponent, _top_share, _deep_fp64, _deep_bucket
#
#  Included by lp1_conj_deep_diag.jl; do not include directly.
# =============================================================================

# ---------------------------------------------------------------------------
#  Constants
# ---------------------------------------------------------------------------
const DEEP_DIAG_BUCKET_BITS      = 10          # 2^10 = 1024 coarse buckets
const DEEP_DIAG_N_BUCKETS        = 1 << DEEP_DIAG_BUCKET_BITS
const DEEP_DIAG_MAX_ANCESTRY     = 500_000
const DEEP_DIAG_MAX_OPCODE_LOG   = 2_000_000
const D12_MAX_EVENTS             = 500_000
const D7_MAX_CLOSURES            = 500_000
const D8_MAX_DEPTHS              = 500_000
const D8_MAX_SHADOW              = 500_000
const D17_MAX_TRACKED_KEYS       = 200_000
const D19_MAX_PAIRS              = 500_000   # cap on pair co-occurrence dict entries

# D20 — Pre-emission opcode sequence fingerprint.
# We keep a ring buffer of the last D20_WINDOW opcodes and snapshot it at
# every emission.  D20_MAX_SNAPSHOTS caps memory.
const D20_WINDOW        = 256        # opcodes to look back
const D20_RING_SIZE     = D20_WINDOW + 4
const D20_MAX_SNAPSHOTS = 2_000      # per-thread cap on full snapshots
const D20_HIST_WINDOW   = 16         # short window for opcode-N-before-emission histogram
const D20_BASELINE_CAP  = 200_000    # baseline opcode samples (reservoir)

# D21 — Refractory / eligible-state return time.
# After each emission we record how many steps until the *next* 1LP_CONJ opcode
# is seen (whether or not it becomes a close).  Measures refractory length.
const D21_MAX_GAPS      = 5_000      # per-thread cap on return-time samples

# D22 — Entry-event burst geometry.
# A "cold entry" is the first emission after a gap ≥ COLD_GAP_THRESH steps.
# We record a compact fingerprint of the triggering key so we can ask what
# makes the walk enter a productive micro-configuration.
# Also tracks full burst-run sizes (consecutive emissions each within BURST_SEP steps).
const D22_COLD_GAP_FRAC = 2          # denominator: gap ≥ mean/2 = cold entry
const D22_MAX_ENTRIES   = 10_000     # per-thread cap on cold-entry records
const D22_BURST_SEP     = 50_000     # steps separating bursts for burst-size counting
const D22_MAX_BURSTS    = 5_000      # per-thread cap on burst-size records

# D23 — Kill-renewal cascade probe (observational, walk-unmodified).
# After each emission we count how many additional emissions occur within the
# next K steps.  This is the "cascade depth" without requiring any stride
# suppression — it tells us whether bursts are 1-hit or multi-hit.
# We record (gap_to_prev, cascade_count_in_next_K) pairs.
const D23_CASCADE_WINDOW = 5_000     # steps after emission to watch for cascade hits
const D23_MAX_RECORDS    = 5_000     # per-thread cap

# D24 — Cross-thread burst alignment (coarse wall-clock / step-count buckets).
# Each thread logs the walk-step index of every emission into a shared atomic
# counter array bucketed to D24_BUCKET_STEPS resolution.  After the walk, the
# main thread checks how many buckets contain ≥ 2 thread contributions — that
# is the "same-window co-occurrence" rate.  High rate → global structure.
# This is purely a post-walk analysis; recording is a single atomic increment.
const D24_BUCKET_STEPS  = 200_000    # step-count resolution per bucket
const D24_MAX_BUCKETS   = 2_000      # cap on distinct buckets tracked per thread

# D28 — LP-aff anchor state at lag-k before LP1-conj emission.
# Parallel to the D20 opcode ring: at every 1LP-aff step we record the
# (px, py, al) of the affine LP point into a ring buffer of the same size
# and indexing as d20_opcode_ring.  At emission time we snapshot lags
# 1..D20_HIST_WINDOW from this ring alongside the opcode snapshot, giving
# per-lag px/al distributions conditioned on "emission happened k steps later".
# Non-1LP-aff steps write a sentinel (-1, -1, -1) into the ring so the lag
# index is always aligned with the D20 opcode ring.
# Baseline: reservoir of (px, al) from ALL 1LP-aff steps (not just those
# preceding emissions), sampled at 1/32 rate to keep memory bounded.
const D28_BASELINE_CAP  = 50_000    # per-thread cap on baseline aff-step records

# D32 — LP1-conj key recurrence-gap concentration (revised framing).
#
# The original D32 ("u-polynomial return map", u^(t+1) = u^(t) under varying
# anchor) doesn't directly apply to this codebase: the walk's own Jacobian
# divisor D_cur (driven by jac_add steps) is not fed back from the φ
# residual RS_mumford, so there is no single feedback map to test for fixed
# points in that sense.
#
# What IS directly testable — and what the CIR-ACF burst result (peak lift
# 15.18× at Δ=3 steps, decaying to baseline by Δ≈30-60 steps) actually
# motivates — is whether the LP1-conj STORE→CLOSE recurrence gap itself
# (depth = close_step - store_step, already computed for D8) is
# concentrated at short lags beyond what a memoryless process would
# predict at the same mean. CIR-ACF showed emissions cluster in time;
# D32 asks the complementary question: when a key DOES recur, how far back
# does it typically reach? A geometric/memoryless walk would predict
# P(depth <= k) = 1 - (1-q)^k for the empirical mean; if the real
# distribution puts excess mass at depth <= ~30 relative to that null, the
# walk has short-range key recurrence consistent with the φ map briefly
# re-visiting the same residual Mumford key — i.e. literal short cycles in
# practice, even without exact fixed points in u-space.
#
# d32_depth_log_hist : log2-bucketed histogram of (close_step - store_step)
#                      over ALL closures (not just the short-lag regime),
#                      so the report can show the full shape. Bucket b
#                      covers depth in [2^b, 2^(b+1)-1]; bucket 0 covers
#                      depth in [0,1]. D32_LOG_BUCKETS buckets total, with
#                      an overflow bucket for depth >= 2^(D32_LOG_BUCKETS-1).
# d32_short_lag_hist : LINEAR per-step histogram of depth for depth in
#                      [1, D32_SHORT_LAG_MAX], i.e. fine-grained resolution
#                      exactly in the CIR-ACF burst window. This is the
#                      direct test instrument; the log-hist above is context.
# d32_n_closures     : total closures counted (= sum of both histograms'
#                      contributing events; short_lag_hist only gets the
#                      depth <= D32_SHORT_LAG_MAX subset).
# d32_depth_sum      : running sum of depth over all closures, for the mean
#                      (needed to fit the geometric null in the report).
const D32_LOG_BUCKETS     = 32              # covers depth up to 2^31 (walk steps fit in Int)
const D32_SHORT_LAG_MAX   = 128             # linear resolution out to 128 steps (covers the burst window)

# D33 — φ a-coefficient residue bias (small-prime modular structure).
#
# The φ a-coefficient a = (v1·px + v0 - py) / u(px) is the single scalar
# that fully determines the next Mumford key u_RS.  If the walk's collision
# concentration (α₂ = 0.59 vs naive 1.0) originates in the algebraic
# structure of the curve rather than temporal clustering, it should be visible
# as a non-uniform distribution of 'a' modulo small primes — residue bias
# that a 64-bucket histogram (D14) is too coarse to detect.
#
# We accumulate exact remainder histograms for every prime in D33_PRIMES on
# all 1LP-conj STORE events where a_val >= 0.  The test statistic is χ²/dof
# vs the uniform distribution over {0, …, q-1} for each prime q.  A value
# >> 1 for any prime directly implicates that prime in the attractor geometry.
#
# We also accumulate the joint (a mod 3, a mod 5) 15-cell table to detect
# correlated residue structure that marginal tests would miss.  By CRT,
# (a mod 3, a mod 5) determines a mod 15 — so this is equivalent to an
# a mod 15 test but displayed as a cross-table for readability.
#
# All histograms are plain Int arrays; no reservoir needed — one increment
# per store event, O(1) hot-path cost.  Capped at D33_MAX_STORES to avoid
# wrapping issues (in practice 10M >> walk size).
const D33_PRIMES     = (2, 3, 5, 7, 11, 13)   # small primes to test
const D33_N_PRIMES   = 6
const D33_MAX_STORES = 10_000_000              # cap on a_val increments (overflow guard)

# D34 — x-bucket smoothing-probability diagnostic.
#
# Hypothesis (GPT): FB x-hotspots have elevated smoothing probability, which
# "drains" residuals from those regions before they can become LP1-conj keys,
# thereby flattening the LP1-conj distribution and keeping closure geometry
# near-proportional despite the high ρ=0.98 anchor–FB-x correlation in D12.
#
# Test: for each walk step we bucket the current anchor point's x-coordinate
# into D34_X_BUCKETS equal-width bins over [0, p), then increment one of three
# outcome counters:
#   n_steps[bkt]  — total steps with this anchor x-bucket (denominator)
#   n_0lp[bkt]    — 0-LP (full relation, i0∧iR∧iS all in FB) with this bucket
#   n_store[bkt]  — 1LP-conj genuine STORE with this bucket
#
# Post-walk we compute per-bucket rates:
#   r_full[bkt]  = n_0lp[bkt]  / n_steps[bkt]   ≈ Pr(full relation | x-bucket)
#   r_store[bkt] = n_store[bkt] / n_steps[bkt]   ≈ Pr(LP1-conj store | x-bucket)
#
# If hot x-buckets (high n_0lp) also have low n_store — i.e.
# corr(r_full, r_store) < 0 — that confirms the draining hypothesis.
# If corr > 0, biased FB x feeds forward into closure concentration.
# If corr ≈ 0, the LP1-conj map T strongly mixes x.
#
# We also compute per-bucket relative lift:
#   lift_store[bkt] = r_store[bkt] / mean(r_store)
# so the report can show which x-bands over- or under-produce LP1-conj residuals.
#
# Recording cost: one Int increment per walk step (D34_X_BUCKETS is small so
# the bucket index fits in L1), plus one increment in one of three outcome
# arrays. No allocation on the hot path.
const D34_X_BUCKETS = 128     # coarse x-axis partition; wide enough to show shape


# For each LP1-conj key k we track:
#   W(k)      = max(store_step) - min(store_step) across all STORE events
#   N_pair(k) = number of distinct i0 anchor indices seen at CLOSE time
#               (approximated via a UInt64 bitmask over i0 % 64; saturates at 64)
# Post-walk we compute corr(log W(k), log N_pair(k)) across all keys that
# closed at least once and had W(k) > 0.
# GPT hypothesis: this correlation should be strongly negative if collision
# concentration lives in trajectory-time rather than coordinate-space.
const D26_MAX_TRACKED_KEYS = 200_000   # cap on distinct keys tracked

# D25 — Closure (α,px) cell lift analysis.
# For each closure we record the closing visit's (al_bkt, px_bkt) in the same
# 64×64 grid used by D12.  Post-walk we compare the closure cell distribution
# against the D12 store histogram to find cells with anomalous closure lift.
# Also records Δal = al_close - al_store (mod ell, bucketed) to test for
# step-table periodicity driving repeated visits at fixed α offsets.
# Cap: well above expected closure counts; 10_000 is generous.
const D25_MAX_CLOSURES   = 10_000    # per-thread cap on closure records
const D25_GRID_BITS      = 6         # 2^6 = 64 buckets per axis (matches D12)
const D25_GRID_SIZE      = 1 << D25_GRID_BITS   # 64
const D25_DAL_BUCKETS    = 128       # Δal histogram buckets (mod ell)

# D16 — Pre-burst state fingerprinting ring-buffer constants.
const D16_LAG_LO      = 10
const D16_LAG_HI      = 40
const D16_RING_SIZE   = D16_LAG_HI + 4
const D16_GATE_DENOM  = 64
const D16_MAX_SAMPLES = 50_000

# ---------------------------------------------------------------------------
#  Opcode symbols used by record_conj_deep_opcode! and the D9/D11 diagnostics.
# ---------------------------------------------------------------------------
const OPCODE_0LP      = 0x00
const OPCODE_1LP_AFF  = 0x01
const OPCODE_1LP_CONJ = 0x02
const OPCODE_2LP_AFF  = 0x03
const OPCODE_2LP_CONJ = 0x04
const OPCODE_SKIP     = 0x05

# ---------------------------------------------------------------------------
#  ConjDeepStat — per-thread accumulator
# ---------------------------------------------------------------------------
mutable struct ConjDeepStat
    # D3 — branch ancestry log (capped at DEEP_DIAG_MAX_ANCESTRY).
    ancestry_log_a      ::Vector{UInt16}
    ancestry_log_parity ::Vector{UInt8}
    ancestry_log_keyhash::Vector{UInt32}

    # D7 — per-emission first-closure flag.
    is_first_closure::Vector{Bool}
    n_emissions     ::Int

    # D8 — closure-depth distribution.
    d8_shadow       ::Dict{UInt128, Int}   # lp_key → store raw_step
    d8_depths       ::Vector{Int}
    d8_close_bkt    ::Vector{UInt16}
    d8_close_abkt   ::Vector{UInt16}
    d8_prev_depth   ::Int

    # D12 — Alpha/anchor joint support.
    #
    # d12_store_* hold a reservoir sample (Algorithm R) of STORE events, not a
    # prefix.  d12_n_stores_seen is the total number of store events observed
    # by this thread (including ones that were never inserted into the
    # reservoir) — it is what makes each slot's inclusion probability
    # D12_MAX_EVENTS / d12_n_stores_seen uniform across the whole stream
    # rather than biased toward the first D12_MAX_EVENTS events.  Without this
    # counter, any downstream consumer that joins d12_store_key against a
    # later/uncapped key set (e.g. D27's CLOSE/SINGLETON partition) silently
    # excludes everything stored after the prefix window.
    d12_store_alpha ::Vector{Int}
    d12_store_px    ::Vector{Int}
    d12_store_key   ::Vector{UInt128}
    d12_n_stores_seen ::Int
    d12_close_alpha ::Vector{Int}
    d12_close_px    ::Vector{Int}
    d12_close_key   ::Vector{UInt128}

    # D14 — φ-coefficient 'a' at each store event (sentinel -1 if unavailable).
    d14_store_a     ::Vector{Int}

    # D16 — Pre-burst state fingerprinting ring buffer + histograms.
    d16_ring_step_mod   ::Vector{UInt8}
    d16_ring_partition  ::Vector{UInt16}
    d16_ring_bkt        ::Vector{UInt16}
    d16_emission_count  ::Int
    d16_preburst_hist   ::Dict{UInt32, Int}
    d16_baseline_hist   ::Dict{UInt32, Int}
    d16_n_preburst      ::Int
    d16_n_baseline      ::Int

    # D9 — step-opcode log.
    opcode_log      ::Vector{UInt8}
    opcode_is_lp1c  ::Vector{Bool}

    # D17 — per-key lifetime multiplicity counter.
    d17_lifetime_hits ::Dict{UInt128, Int}
    # D17 metadata: (px, py, a) of the anchor point P0 and φ-coefficient a
    # at the *first* store event for each key.  Keyed identically to
    # d17_lifetime_hits; populated only when px >= 0.  Used to annotate the
    # top-50 table with the walk state that first introduced the key.
    d17_key_meta      ::Dict{UInt128, NTuple{3,Int}}

    # D19 — Factor-base element productivity (closure participation counts).
    # d19_fb_close_counts    : fb_index → total closures touching this element
    #                          (i0 side + prev_col side combined).
    # d19_fb_i0_counts       : fb_index → closures where element appeared as i0.
    # d19_fb_prev_counts     : fb_index → closures where element appeared as prev_col.
    # d19_fb_pair_counts     : (lo,hi) sorted pair → co-occurrence count.
    # d19_anchor_sample_rels : fb_index → up to 5 sample relations as
    #                          (i0, prev_col, combined_al, combined_be) tuples,
    #                          stored for both the i0 and prev_col sides so any
    #                          top anchor will have examples regardless of role.
    d19_fb_close_counts    ::Dict{Int, Int}
    d19_fb_i0_counts       ::Dict{Int, Int}
    d19_fb_prev_counts     ::Dict{Int, Int}
    d19_fb_pair_counts     ::Dict{NTuple{2,Int}, Int}
    d19_anchor_sample_rels ::Dict{Int, Vector{NTuple{4,Int}}}

    # D20 — Pre-emission opcode sequence fingerprint.
    # Ring buffer of recent opcodes (hot path); snapshots at emission time.
    d20_opcode_ring            ::Vector{UInt8}    # circular buffer, length D20_RING_SIZE
    d20_ring_head              ::Int              # next-write index (1-based, mod D20_RING_SIZE)
    d20_ring_filled            ::Int              # how many valid entries (up to D20_RING_SIZE)
    d20_pre_snapshots          ::Vector{UInt8}    # n_snapshots × D20_HIST_WINDOW, row-major
    d20_n_snapshots            ::Int
    d20_baseline_opcode_counts ::Matrix{UInt32}   # D20_HIST_WINDOW × 6 (opcode type)
    d20_n_baseline             ::Int

    # D21 — Refractory gap: steps from emission until next 1LP_CONJ opcode.
    d21_steps_since_emit  ::Int             # -1 = not in refractory tracking
    d21_return_gaps       ::Vector{Int}     # collected return-time samples
    d21_n_emitted         ::Int             # total emissions seen by this thread

    # D22 — Entry-event burst geometry.
    # For each cold-entry emission (gap ≥ mean/2 from prev emission), we record:
    #   (key_bucket, a_bucket, burst_size) where burst_size = # of emissions
    #   occurring within D22_BURST_SEP steps of this one (including itself).
    # Because burst_size can only be finalised after the burst ends, we track
    # the current open burst separately and close it when the gap exceeds
    # D22_BURST_SEP.
    d22_cold_entries      ::Vector{NTuple{3,Int}}  # (key_bkt, a_bkt, burst_size) — finalised
    d22_burst_sizes       ::Vector{Int}            # all finalised burst sizes
    d22_cur_burst_size    ::Int                    # open burst accumulator
    d22_prev_emit_step    ::Int                    # walk-step of last emission (-1 = none)
    d22_last_gap          ::Int                    # gap before the current open burst's trigger
    d22_cur_burst_keybkt  ::Int                    # key_bucket of burst-opening emission
    d22_cur_burst_abkt    ::Int                    # a_bucket  of burst-opening emission
    d22_mean_gap_est      ::Float64                # running mean inter-arrival (EWMA, τ=100)

    # D23 — Kill-renewal cascade probe.
    # After each emission we open a D23_CASCADE_WINDOW-step watch window and
    # count further emissions within it.  We record the pair
    #   (steps_since_prev_emit, cascade_count)
    # where steps_since_prev_emit is the gap preceding this emission (so we can
    # condition on cold vs warm entries) and cascade_count is the number of
    # *additional* emissions within the next D23_CASCADE_WINDOW steps.
    d23_records           ::Vector{NTuple{2,Int}}  # (gap_to_prev, cascade_in_window)
    d23_watch_steps_left  ::Int                    # steps remaining in current watch window
    d23_cascade_count     ::Int                    # accumulator for current window
    d23_pending_gap       ::Int                    # gap recorded at window open (to be stored)

    # D24 — Cross-thread burst alignment.
    # Each thread records the coarse step-bucket index of every emission.
    # After the walk, the main thread overlaps all per-thread bucket sets.
    d24_emission_buckets  ::Dict{Int, Int}         # bucket_idx → count (this thread)
    d24_total_walk_steps  ::Int                    # total walk steps taken by this thread

    # D25 — Closure (α, px) cell lift vs D12 store distribution.
    #
    # For each closure we record (al_bkt, px_bkt, depth_bkt, dal_bkt) where:
    #   al_bkt   = alpha_cur bucketed to [0, D25_GRID_SIZE)  (same grid as D12)
    #   px_bkt   = px        bucketed to [0, D25_GRID_SIZE)  (same grid as D12)
    #   depth_bkt= log2(closure depth) coarsened to 8 bands
    #   dal_bkt  = (al_close - al_store) mod ell, bucketed to D25_DAL_BUCKETS
    #              (-1 if al_store unavailable, i.e. amortized mode neg_al not passed)
    #
    # Post-walk: compare d25_close_grid[al_bkt, px_bkt] / n_closures
    #            against   d12_store histogram cell / n_stores
    # to get per-cell closure lift.  A cell with 4× store occupancy but 10×
    # closure rate → closures concentrate there beyond what store density predicts.
    #
    # Δal histogram: d25_dal_hist[dal_bkt] counts closures at that α-offset.
    # Non-uniform → step-table periodicity; specific offsets dominate birthday hits.
    #
    # Cap: D25_MAX_CLOSURES (generous; expected count is O(100s)).
    d25_close_al    ::Vector{Int}             # al_bkt per closure (capped)
    d25_close_px    ::Vector{Int}             # px_bkt per closure (capped)
    d25_close_depth ::Vector{Int}             # log2-depth band per closure
    d25_dal_hist    ::Vector{Int}             # Δal histogram, length D25_DAL_BUCKETS
    d25_n_closures  ::Int                     # total closures seen (uncapped counter)

    # D26 — Temporal-width vs pair-concentration anticorrelation.
    # d26_step_range : lp_key → (min_store_step, max_store_step)
    #   Updated at every STORE.  W(k) = max - min.
    # d26_partner_mask : lp_key → UInt64 bitmask, bit (i0 % 64) set on each CLOSE.
    #   count_ones(mask) ≈ distinct partner count N_pair(k), exact up to 64.
    # d26_close_count : lp_key → number of closures (for filtering keys with ≥1 close)
    d26_step_range    ::Dict{UInt128, NTuple{2,Int}}  # (min_step, max_step)
    d26_partner_mask  ::Dict{UInt128, UInt64}         # bloom over i0 % 64
    d26_close_count   ::Dict{UInt128, Int}            # closures per key

    # D28 — LP-aff anchor (px, py, al) ring buffer + emission snapshots.
    #
    # d28_aff_ring  : circular buffer, same indexing as d20_opcode_ring.
    #   Each slot holds (px, py, al) when the corresponding opcode was 1LP_AFF,
    #   or (-1, -1, -1) as a sentinel for all other opcode types.
    #   Written by record_d28_aff_step! on every valid phi step.
    #
    # d28_pre_snapshots : per-emission snapshot of lags 1..D20_HIST_WINDOW from
    #   d28_aff_ring, stored row-major (D20_HIST_WINDOW NTuple{3,Int} per emission).
    #   Filled in record_d20_emission! alongside the opcode snapshot so the two
    #   arrays are always aligned: snapshot[i] corresponds to lag i before emission.
    #
    # d28_baseline_px / d28_baseline_al : reservoir sample of px and al values
    #   from ALL 1LP-aff steps (regardless of whether an emission follows),
    #   sampled at 1/32 rate.  Used as the null distribution in the D28 report.
    d28_aff_ring         ::Vector{NTuple{3,Int}}    # length D20_RING_SIZE; sentinel (-1,-1,-1)
    d28_pre_snapshots    ::Vector{NTuple{3,Int}}    # n_snapshots × D20_HIST_WINDOW, row-major
    d28_n_snapshots      ::Int                      # mirrors d20_n_snapshots
    d28_baseline_px      ::Vector{Int}              # reservoir of px at all 1LP-aff steps
    d28_baseline_al      ::Vector{Int}              # reservoir of al at all 1LP-aff steps
    d28_n_baseline       ::Int                      # total 1LP-aff steps seen (for reservoir)

    # D32 — LP1-conj key recurrence-gap concentration (short-lag focus).
    #
    # See constants block above for the revised framing and rationale.
    d32_depth_log_hist ::Vector{Int}   # length D32_LOG_BUCKETS, log2-bucketed depth histogram
    d32_short_lag_hist ::Vector{Int}   # length D32_SHORT_LAG_MAX, depth=1..D32_SHORT_LAG_MAX (1-based: index k = depth k)
    d32_n_closures     ::Int           # total closures contributing to d32_depth_log_hist
    d32_depth_sum      ::Int           # running sum of depth, for empirical mean

    # D33 — φ a-coefficient residue histograms (small-prime modular structure).
    #
    # d33_hist_flat  : concatenated histograms [mod-2 | mod-3 | mod-5 | mod-7 | mod-11 | mod-13]
    #                  lengths 2+3+5+7+11+13 = 41 cells total; offsets are [1,3,6,11,18,29].
    # d33_joint_3_5  : 15-cell joint table for (a mod 3, a mod 5).
    #                  Index: (a mod 3)*5 + (a mod 5) + 1  (1-based, row-major)
    # d33_n_stores   : total store events with a_val >= 0 counted (capped at D33_MAX_STORES).
    d33_hist_flat   ::Vector{Int}    # length 41: 2+3+5+7+11+13
    d33_joint_3_5   ::Vector{Int}    # length 15: (a mod 3) × (a mod 5)
    d33_n_stores    ::Int            # total store events with a_val >= 0 seen

    # D34 — x-bucket smoothing-probability diagnostic (draining hypothesis).
    #
    # Three fixed-size arrays of length D34_X_BUCKETS, indexed by
    # bkt = clamp(px * D34_X_BUCKETS ÷ p, 0, D34_X_BUCKETS-1) (0-based, +1 for Julia).
    #
    # d34_n_steps[bkt]  : total walk steps whose anchor fell in this x-bucket
    # d34_n_0lp[bkt]    : 0-LP (full relation) events in this x-bucket
    # d34_n_store[bkt]  : 1LP-conj genuine STORE events in this x-bucket
    #
    # All three are incremented on the hot path via record_d34_step!.
    # The "p" used for bucketing is passed at record time (not stored in stat);
    # callers must pass the same p they use for the report.  If p is unknown
    # (px=-1), the call is a no-op.
    d34_n_steps ::Vector{Int}    # length D34_X_BUCKETS
    d34_n_0lp   ::Vector{Int}    # length D34_X_BUCKETS
    d34_n_store ::Vector{Int}    # length D34_X_BUCKETS
end

function ConjDeepStat()
    ConjDeepStat(
        UInt16[], UInt8[], UInt32[],
        Bool[],
        0,
        Dict{UInt128,Int}(),
        Int[], UInt16[], UInt16[],
        -1,
        Int[], Int[], UInt128[],   # d12 store
        0,                          # d12_n_stores_seen
        Int[], Int[], UInt128[],   # d12 close
        Int[],                     # d14 store_a
        # D16
        zeros(UInt8,  D16_RING_SIZE),
        zeros(UInt16, D16_RING_SIZE),
        zeros(UInt16, D16_RING_SIZE),
        0,
        Dict{UInt32,Int}(),
        Dict{UInt32,Int}(),
        0,
        0,
        UInt8[], Bool[],
        Dict{UInt128,Int}(),           # d17_lifetime_hits
        Dict{UInt128,NTuple{3,Int}}(), # d17_key_meta
        # D19
        Dict{Int,Int}(),               # d19_fb_close_counts
        Dict{Int,Int}(),               # d19_fb_i0_counts
        Dict{Int,Int}(),               # d19_fb_prev_counts
        Dict{NTuple{2,Int},Int}(),     # d19_fb_pair_counts
        Dict{Int,Vector{NTuple{4,Int}}}(), # d19_anchor_sample_rels
        # D20
        zeros(UInt8, D20_RING_SIZE),       # d20_opcode_ring
        1,                                  # d20_ring_head
        0,                                  # d20_ring_filled
        UInt8[],                            # d20_pre_snapshots
        0,                                  # d20_n_snapshots
        zeros(UInt32, D20_HIST_WINDOW, 6), # d20_baseline_opcode_counts
        0,                                  # d20_n_baseline
        # D21
        -1,                                 # d21_steps_since_emit
        Int[],                              # d21_return_gaps
        0,                                  # d21_n_emitted
        # D22
        NTuple{3,Int}[],                    # d22_cold_entries
        Int[],                              # d22_burst_sizes
        0,                                  # d22_cur_burst_size
        -1,                                 # d22_prev_emit_step
        -1,                                 # d22_last_gap
        -1,                                 # d22_cur_burst_keybkt
        -1,                                 # d22_cur_burst_abkt
        0.0,                                # d22_mean_gap_est
        # D23
        NTuple{2,Int}[],                    # d23_records
        -1,                                 # d23_watch_steps_left
        0,                                  # d23_cascade_count
        -1,                                 # d23_pending_gap
        # D24
        Dict{Int,Int}(),                    # d24_emission_buckets
        0,                                  # d24_total_walk_steps
        # D25
        Int[],                              # d25_close_al
        Int[],                              # d25_close_px
        Int[],                              # d25_close_depth
        zeros(Int, D25_DAL_BUCKETS),        # d25_dal_hist
        0,                                  # d25_n_closures
        # D26
        Dict{UInt128, NTuple{2,Int}}(),     # d26_step_range
        Dict{UInt128, UInt64}(),            # d26_partner_mask
        Dict{UInt128, Int}(),               # d26_close_count
        # D28
        fill((-1,-1,-1), D20_RING_SIZE),    # d28_aff_ring
        NTuple{3,Int}[],                    # d28_pre_snapshots
        0,                                  # d28_n_snapshots
        Int[],                              # d28_baseline_px
        Int[],                              # d28_baseline_al
        0,                                  # d28_n_baseline
        # D32 — LP1-conj key recurrence-gap concentration
        zeros(Int, D32_LOG_BUCKETS),        # d32_depth_log_hist
        zeros(Int, D32_SHORT_LAG_MAX),      # d32_short_lag_hist
        0,                                  # d32_n_closures
        0,                                  # d32_depth_sum
        # D33 — φ a-coefficient residue histograms
        zeros(Int, 41),                     # d33_hist_flat (2+3+5+7+11+13 cells)
        zeros(Int, 15),                     # d33_joint_3_5
        0,                                  # d33_n_stores
        # D34 — x-bucket smoothing-probability diagnostic
        zeros(Int, D34_X_BUCKETS),          # d34_n_steps
        zeros(Int, D34_X_BUCKETS),          # d34_n_0lp
        zeros(Int, D34_X_BUCKETS),          # d34_n_store
    )
end

# ---------------------------------------------------------------------------
#  merge_conj_deep_stats — reduce per-thread structs into one.
# ---------------------------------------------------------------------------
function merge_conj_deep_stats(stats::Vector{ConjDeepStat})::ConjDeepStat
    isempty(stats) && error("merge_conj_deep_stats: empty input")
    merged = ConjDeepStat()
    for s in stats
        append!(merged.ancestry_log_a,       s.ancestry_log_a)
        append!(merged.ancestry_log_parity,  s.ancestry_log_parity)
        append!(merged.ancestry_log_keyhash, s.ancestry_log_keyhash)

        let n_rem = D7_MAX_CLOSURES - length(merged.is_first_closure)
            n_rem > 0 && append!(merged.is_first_closure,
                                 s.is_first_closure[1:min(n_rem, length(s.is_first_closure))])
        end
        merged.n_emissions += s.n_emissions

        # D8: merge depth/bucket vectors; shadow table is not merged.
        let n_rem = D8_MAX_DEPTHS - length(merged.d8_depths)
            if n_rem > 0
                n_take = min(n_rem, length(s.d8_depths))
                append!(merged.d8_depths,     s.d8_depths[1:n_take])
                append!(merged.d8_close_bkt,  s.d8_close_bkt[1:n_take])
                append!(merged.d8_close_abkt, s.d8_close_abkt[1:n_take])
            end
        end

        # D9: merge opcode log.
        let n_rem = DEEP_DIAG_MAX_OPCODE_LOG - length(merged.opcode_log)
            if n_rem > 0
                n_take = min(n_rem, length(s.opcode_log))
                append!(merged.opcode_log,     s.opcode_log[1:n_take])
                append!(merged.opcode_is_lp1c, s.opcode_is_lp1c[1:n_take])
            end
        end

        # D12 close event log is not capped — record everything. (The store
        # event reservoir is merged separately below, after this loop, via
        # _merge_d12_store_reservoirs! — that merge needs every thread's
        # d12_n_stores_seen available up front to allocate cap slots
        # correctly across threads, so it can't be folded into this
        # one-thread-at-a-time loop; see that function's docstring.)
        append!(merged.d12_close_alpha, s.d12_close_alpha)
        append!(merged.d12_close_px,    s.d12_close_px)
        append!(merged.d12_close_key,   s.d12_close_key)

        # D16: merge histograms; ring buffer is per-thread ephemeral.
        for (k, v) in s.d16_preburst_hist
            merged.d16_preburst_hist[k] = get(merged.d16_preburst_hist, k, 0) + v
        end
        for (k, v) in s.d16_baseline_hist
            merged.d16_baseline_hist[k] = get(merged.d16_baseline_hist, k, 0) + v
        end
        merged.d16_n_preburst += s.d16_n_preburst
        merged.d16_n_baseline += s.d16_n_baseline

        # D17: merge per-key lifetime hit counters.
        for (k, v) in s.d17_lifetime_hits
            if haskey(merged.d17_lifetime_hits, k)
                merged.d17_lifetime_hits[k] += v
            elseif length(merged.d17_lifetime_hits) < D17_MAX_TRACKED_KEYS
                merged.d17_lifetime_hits[k] = v
            end
        end
        # D17 metadata: keep first-seen (px, py, a) per key; no cap needed
        # since d17_key_meta is a subset of d17_lifetime_hits keys.
        for (k, meta) in s.d17_key_meta
            haskey(merged.d17_key_meta, k) || (merged.d17_key_meta[k] = meta)
        end

        # D19: merge per-FB-element closure counts.
        for (k, v) in s.d19_fb_close_counts
            merged.d19_fb_close_counts[k] = get(merged.d19_fb_close_counts, k, 0) + v
        end
        for (k, v) in s.d19_fb_i0_counts
            merged.d19_fb_i0_counts[k] = get(merged.d19_fb_i0_counts, k, 0) + v
        end
        for (k, v) in s.d19_fb_prev_counts
            merged.d19_fb_prev_counts[k] = get(merged.d19_fb_prev_counts, k, 0) + v
        end
        for (k, v) in s.d19_fb_pair_counts
            if haskey(merged.d19_fb_pair_counts, k)
                merged.d19_fb_pair_counts[k] += v
            elseif length(merged.d19_fb_pair_counts) < D19_MAX_PAIRS
                merged.d19_fb_pair_counts[k] = v
            end
        end
        # D19 sample relations: keep up to 5 per anchor across threads.
        for (k, rels) in s.d19_anchor_sample_rels
            dst = get!(merged.d19_anchor_sample_rels, k, NTuple{4,Int}[])
            for r in rels
                length(dst) >= 5 && break
                push!(dst, r)
            end
        end

        # D20: merge pre-emission snapshots and baseline counts.
        n_rem = (D20_MAX_SNAPSHOTS - merged.d20_n_snapshots) * D20_HIST_WINDOW
        if n_rem > 0 && length(s.d20_pre_snapshots) > 0
            n_take = min(n_rem, length(s.d20_pre_snapshots))
            # round down to whole windows
            n_take = (n_take ÷ D20_HIST_WINDOW) * D20_HIST_WINDOW
            append!(merged.d20_pre_snapshots, s.d20_pre_snapshots[1:n_take])
            merged.d20_n_snapshots += n_take ÷ D20_HIST_WINDOW
        end
        merged.d20_baseline_opcode_counts .+= s.d20_baseline_opcode_counts
        merged.d20_n_baseline += s.d20_n_baseline

        # D21: merge return-gap samples.
        let n_rem21 = D21_MAX_GAPS - length(merged.d21_return_gaps)
            if n_rem21 > 0
                n_take = min(n_rem21, length(s.d21_return_gaps))
                append!(merged.d21_return_gaps, s.d21_return_gaps[1:n_take])
            end
        end
        merged.d21_n_emitted += s.d21_n_emitted

        # D22: merge cold-entry records and burst-size vectors.
        let n_rem22 = D22_MAX_ENTRIES - length(merged.d22_cold_entries)
            if n_rem22 > 0
                n_take = min(n_rem22, length(s.d22_cold_entries))
                append!(merged.d22_cold_entries, s.d22_cold_entries[1:n_take])
            end
        end
        let n_rem22b = D22_MAX_BURSTS - length(merged.d22_burst_sizes)
            if n_rem22b > 0
                n_take = min(n_rem22b, length(s.d22_burst_sizes))
                append!(merged.d22_burst_sizes, s.d22_burst_sizes[1:n_take])
            end
        end

        # D23: merge cascade probe records.
        let n_rem23 = D23_MAX_RECORDS - length(merged.d23_records)
            if n_rem23 > 0
                n_take = min(n_rem23, length(s.d23_records))
                append!(merged.d23_records, s.d23_records[1:n_take])
            end
        end

        # D24: merge per-bucket emission counts and step totals.
        for (bkt, cnt) in s.d24_emission_buckets
            if haskey(merged.d24_emission_buckets, bkt)
                merged.d24_emission_buckets[bkt] += cnt
            elseif length(merged.d24_emission_buckets) < D24_MAX_BUCKETS
                merged.d24_emission_buckets[bkt] = cnt
            end
        end
        merged.d24_total_walk_steps += s.d24_total_walk_steps

        # D25: merge closure coordinate logs and Δal histogram.
        let n_rem25 = D25_MAX_CLOSURES - length(merged.d25_close_al)
            if n_rem25 > 0
                n_take = min(n_rem25, length(s.d25_close_al))
                append!(merged.d25_close_al,    s.d25_close_al[1:n_take])
                append!(merged.d25_close_px,    s.d25_close_px[1:n_take])
                append!(merged.d25_close_depth, s.d25_close_depth[1:n_take])
            end
        end
        merged.d25_dal_hist   .+= s.d25_dal_hist
        merged.d25_n_closures  += s.d25_n_closures

        # D26: merge (store_step,close_step) pairs. Each key is written at most
        # once (one closure per key); min/max is a harmless no-op safety net
        # in the (should-not-happen) case of duplicate closures.
        for (k, (lo, hi)) in s.d26_step_range
            if haskey(merged.d26_step_range, k)
                mlo, mhi = merged.d26_step_range[k]
                merged.d26_step_range[k] = (min(mlo, lo), max(mhi, hi))
            elseif length(merged.d26_step_range) < D26_MAX_TRACKED_KEYS
                merged.d26_step_range[k] = (lo, hi)
            end
        end
        for (k, mask) in s.d26_partner_mask
            merged.d26_partner_mask[k] = get(merged.d26_partner_mask, k, UInt64(0)) | mask
        end
        for (k, cnt) in s.d26_close_count
            merged.d26_close_count[k] = get(merged.d26_close_count, k, 0) + cnt
        end

        # D28: merge emission snapshots and baseline reservoir.
        n_rem28 = (D20_MAX_SNAPSHOTS - merged.d28_n_snapshots) * D20_HIST_WINDOW
        if n_rem28 > 0 && length(s.d28_pre_snapshots) > 0
            n_take = min(n_rem28, length(s.d28_pre_snapshots))
            n_take = (n_take ÷ D20_HIST_WINDOW) * D20_HIST_WINDOW
            append!(merged.d28_pre_snapshots, s.d28_pre_snapshots[1:n_take])
            merged.d28_n_snapshots += n_take ÷ D20_HIST_WINDOW
        end
        # Baseline: simple cap-and-append; exact reservoir merge not needed
        # since we only care about marginal px/al distributions.
        let n_rem28b = D28_BASELINE_CAP - length(merged.d28_baseline_px)
            if n_rem28b > 0
                n_take = min(n_rem28b, length(s.d28_baseline_px))
                append!(merged.d28_baseline_px, s.d28_baseline_px[1:n_take])
                append!(merged.d28_baseline_al, s.d28_baseline_al[1:n_take])
            end
        end
        merged.d28_n_baseline += s.d28_n_baseline

        # D32: merge recurrence-gap histograms — simple element-wise addition.
        # Both histograms are fixed-size arrays; no cap needed.
        merged.d32_depth_log_hist .+= s.d32_depth_log_hist
        merged.d32_short_lag_hist .+= s.d32_short_lag_hist
        merged.d32_n_closures     += s.d32_n_closures
        merged.d32_depth_sum      += s.d32_depth_sum

        # D33: merge residue histograms — simple element-wise addition.
        # Histograms are fixed-size arrays (41 and 15 cells); no cap needed.
        merged.d33_hist_flat .+= s.d33_hist_flat
        merged.d33_joint_3_5 .+= s.d33_joint_3_5
        merged.d33_n_stores  += s.d33_n_stores

        # D34: merge x-bucket step/outcome counts — simple element-wise addition.
        # All three are fixed-size arrays (D34_X_BUCKETS cells); no cap needed.
        merged.d34_n_steps .+= s.d34_n_steps
        merged.d34_n_0lp   .+= s.d34_n_0lp
        merged.d34_n_store .+= s.d34_n_store
    end

    # D12 store-event reservoir: merged separately (needs every thread's
    # true stream length up front; see _merge_d12_store_reservoirs!).
    _merge_d12_store_reservoirs!(merged, stats)

    return merged
end

# ---------------------------------------------------------------------------
#  _merge_d12_store_reservoirs! — combine per-thread D12 reservoir samples
#  into merged.d12_store_* (and the lockstep d14_store_a) as an exact,
#  unbiased reservoir sample of size ≤ D12_MAX_EVENTS drawn uniformly from
#  the union of every thread's true store stream.
#
#  Why this can't just be "append everything, then truncate" or "fold items
#  in one at a time treating each as +1 to a running n_seen": both of those
#  bias the result toward whichever thread happens to be processed first, or
#  toward threads with smaller streams (verified empirically — folding
#  thread B's already-4%-subsampled items into a running counter as if each
#  was a single fresh draw inflates small threads' apparent weight, because
#  it ignores how much each item was already pre-thinned by that thread's
#  own reservoir).
#
#  The exact approach (two-stage uniform sampling):
#    1. If you draw a uniform sample of size `cap` from a population
#       partitioned into groups of size n_1, n_2, ..., the number of draws
#       k_s landing in group s follows a multivariate hypergeometric
#       distribution with population sizes (n_1, n_2, ...).
#    2. Each thread's reservoir is *already* a uniform sample of size m_s
#       from its own n_s true events. A uniform random subsample of size
#       k_s ≤ m_s taken from that reservoir is therefore a uniform sample of
#       size k_s from the original n_s events (subsampling a uniform sample
#       stays uniform — standard fact).
#  So: draw the per-thread allocation (k_1, k_2, ...) via sequential
#  hypergeometric draws against the running total, then uniformly subsample
#  k_s items (without replacement) from each thread's reservoir. This was
#  verified by Monte Carlo simulation to converge exactly to the target
#  uniform inclusion probability D12_MAX_EVENTS / total_n_seen for every
#  original event regardless of which thread it came from or thread size
#  skew.
# ---------------------------------------------------------------------------
function _merge_d12_store_reservoirs!(merged::ConjDeepStat, stats::Vector{ConjDeepStat})
    total_n = sum(s.d12_n_stores_seen for s in stats)
    merged.d12_n_stores_seen = total_n
    total_n == 0 && return nothing

    cap = D12_MAX_EVENTS
    remaining_cap   = min(cap, total_n)
    remaining_total = total_n

    for (idx, s) in enumerate(stats)
        n_s = s.d12_n_stores_seen
        m_s = length(s.d12_store_alpha)   # this thread's reservoir size, ≤ min(n_s, cap)

        is_last = (idx == length(stats))
        k_s = if is_last
            remaining_cap   # last group must absorb whatever allocation remains
        elseif n_s == 0
            0
        else
            _draw_hypergeometric(remaining_total, n_s, remaining_cap)
        end
        k_s = min(k_s, m_s)   # can't take more than the thread actually retained

        if k_s > 0
            idxs = m_s == k_s ? collect(1:m_s) : _sample_without_replacement(m_s, k_s)
            for i in idxs
                push!(merged.d12_store_alpha, s.d12_store_alpha[i])
                push!(merged.d12_store_px,    s.d12_store_px[i])
                push!(merged.d12_store_key,   s.d12_store_key[i])
                push!(merged.d14_store_a,     s.d14_store_a[i])
            end
        end

        remaining_cap   -= k_s
        remaining_total -= n_s
    end
    return nothing
end

# ---------------------------------------------------------------------------
#  _draw_hypergeometric(N, K, n) — exact draw from Hypergeometric(N, K, n):
#  the number of "marked" items (population size K, out of total N) obtained
#  when drawing n items without replacement from the population of N.
#  Implemented as a direct sequential urn simulation (exact, not an
#  approximation) — cheap and only ever called O(n_threads) times per merge,
#  never in the hot path.
# ---------------------------------------------------------------------------
function _draw_hypergeometric(N::Int, K::Int, n::Int)::Int
    successes  = 0
    remaining_N = N
    remaining_K = K
    for _ in 1:n
        remaining_N <= 0 && break
        if rand(1:remaining_N) <= remaining_K
            successes += 1
            remaining_K -= 1
        end
        remaining_N -= 1
    end
    return successes
end

# ---------------------------------------------------------------------------
#  _sample_without_replacement(m, k) — k distinct uniformly random indices
#  from 1:m, via partial Fisher–Yates. Exact uniform sampling.
# ---------------------------------------------------------------------------
function _sample_without_replacement(m::Int, k::Int)::Vector{Int}
    pool = collect(1:m)
    @inbounds for i in 1:k
        j = rand(i:m)
        pool[i], pool[j] = pool[j], pool[i]
    end
    return pool[1:k]
end

# ---------------------------------------------------------------------------
#  record_d33_store! — called on every 1LP-conj STORE where a_val >= 0.
#
#  Increments the residue histogram for each prime in D33_PRIMES and the
#  joint (a mod 3, a mod 5) cross-table.  Hot-path cost: 6 mod + 6 array
#  increments + 2 more for joint = 8 additions total, no allocation.
#
#  d33_hist_flat layout (offsets are 1-based):
#    prime 2  → cells [1 .. 2]
#    prime 3  → cells [3 .. 5]
#    prime 5  → cells [6 .. 10]
#    prime 7  → cells [11 .. 17]
#    prime 11 → cells [18 .. 28]
#    prime 13 → cells [29 .. 41]
# ---------------------------------------------------------------------------
const D33_HIST_OFFSETS = (1, 3, 6, 11, 18, 29)   # 1-based start of each prime's block

@inline function record_d33_store!(stat ::ConjDeepStat, a_val::Int)
    stat.d33_n_stores >= D33_MAX_STORES && return nothing
    stat.d33_n_stores += 1

    # Residue histograms for each prime.
    # We unroll manually (D33_PRIMES is a compile-time tuple) for inlining.
    r2  = a_val % 2;  @inbounds stat.d33_hist_flat[D33_HIST_OFFSETS[1] + r2]  += 1
    r3  = a_val % 3;  @inbounds stat.d33_hist_flat[D33_HIST_OFFSETS[2] + r3]  += 1
    r5  = a_val % 5;  @inbounds stat.d33_hist_flat[D33_HIST_OFFSETS[3] + r5]  += 1
    r7  = a_val % 7;  @inbounds stat.d33_hist_flat[D33_HIST_OFFSETS[4] + r7]  += 1
    r11 = a_val % 11; @inbounds stat.d33_hist_flat[D33_HIST_OFFSETS[5] + r11] += 1
    r13 = a_val % 13; @inbounds stat.d33_hist_flat[D33_HIST_OFFSETS[6] + r13] += 1

    # Joint (a mod 3, a mod 5) cross-table.
    @inbounds stat.d33_joint_3_5[r3 * 5 + r5 + 1] += 1

    return nothing
end

# ---------------------------------------------------------------------------
#  record_conj_deep_miss! — call at every STORE (miss path in handle_1lp_conj!).
# ---------------------------------------------------------------------------
@inline function record_conj_deep_miss!(stat     ::ConjDeepStat,
                                         lp_key   ::UInt128,
                                         raw_step ::Int,
                                         alpha_cur::Int = -1,
                                         px       ::Int = -1,
                                         a_val    ::Int = -1,
                                         py       ::Int = -1)
    if !haskey(stat.d8_shadow, lp_key) && length(stat.d8_shadow) < D8_MAX_SHADOW
        stat.d8_shadow[lp_key] = raw_step
    end

    # D17: lifetime hit counter + first-seen anchor metadata.
    if haskey(stat.d17_lifetime_hits, lp_key)
        stat.d17_lifetime_hits[lp_key] += 1
    elseif length(stat.d17_lifetime_hits) < D17_MAX_TRACKED_KEYS
        stat.d17_lifetime_hits[lp_key] = 1
        # Record (px, py, a) on the very first store for this key.
        px >= 0 && (stat.d17_key_meta[lp_key] = (px, py, a_val))
    end

    # D12/D14: record (alpha, px, a) at store time via reservoir sampling
    # (Algorithm R).  This must NOT be a prefix cap: D27's CLOSE/SINGLETON
    # partition tests d12_store_key membership against an uncapped close-key
    # set, so if the reservoir only ever kept the first D12_MAX_EVENTS stores,
    # any key first stored later in the walk could never be classified as
    # CLOSE even if it closed — biasing the lift statistic toward whatever a
    # ~500k-store prefix happens to contain. Algorithm R gives every store
    # event, anywhere in the (arbitrarily long) stream, equal probability
    # D12_MAX_EVENTS / d12_n_stores_seen of occupying a reservoir slot.
    if alpha_cur >= 0
        stat.d12_n_stores_seen += 1
        n_seen = stat.d12_n_stores_seen
        if n_seen <= D12_MAX_EVENTS
            # Reservoir not yet full: unconditional insert.
            push!(stat.d12_store_alpha, alpha_cur)
            push!(stat.d12_store_px,    px)
            push!(stat.d12_store_key,   lp_key)
            push!(stat.d14_store_a,     a_val)
        else
            # Reservoir full: replace a uniformly random existing slot with
            # probability D12_MAX_EVENTS / n_seen (standard Algorithm R).
            j = rand(1:n_seen)
            if j <= D12_MAX_EVENTS
                @inbounds stat.d12_store_alpha[j] = alpha_cur
                @inbounds stat.d12_store_px[j]    = px
                @inbounds stat.d12_store_key[j]   = lp_key
                @inbounds stat.d14_store_a[j]     = a_val
            end
        end
    end

    # D26: step_range is populated at CLOSE time (record_conj_deep_step!),
    # where both store_step and close_step are available together.

    # D33: φ a-coefficient residue histograms. Runs over the FULL store
    # stream (not reservoir-sampled) since this is an O(1) increment-only
    # accumulator and we want maximum statistical power on the residue
    # tables — unlike D12/D14, there's no per-event storage cost to cap.
    a_val >= 0 && record_d33_store!(stat, a_val)

    return nothing
end

# ---------------------------------------------------------------------------
#  record_conj_deep_step! — call at every CLOSE (emission) in handle_1lp_conj!.
# ---------------------------------------------------------------------------
@inline function record_conj_deep_step!(stat     ::ConjDeepStat,
                                         lp_key   ::UInt128,
                                         a_bucket ::Int,
                                         raw_step ::Int,
                                         is_first ::Bool,
                                         alpha_cur::Int = -1,
                                         px       ::Int = -1,
                                         store_step::Int = -1,
                                         i0       ::Int = -1)
    stat.n_emissions += 1

    h64 = _deep_fp64(lp_key)
    bkt = Int(h64 >> (64 - DEEP_DIAG_BUCKET_BITS))   # 0-based ∈ [0, 1023]

    # D3 ancestry log.
    if length(stat.ancestry_log_a) < DEEP_DIAG_MAX_ANCESTRY
        push!(stat.ancestry_log_a,       UInt16(clamp(a_bucket, 0, 65535)))
        push!(stat.ancestry_log_parity,  UInt8(raw_step & 0x3))
        push!(stat.ancestry_log_keyhash, UInt32(h64 & 0xffffffff))
    end

    # D7 closure flag.
    length(stat.is_first_closure) < D7_MAX_CLOSURES && push!(stat.is_first_closure, is_first)

    # D8 closure depth — store_step supplied directly by caller from LSM value
    # (avoids the cross-thread d8_shadow miss: the storing thread embeds its
    # raw_step into the LSM value at insert time via the OFF_STEP padding field).
    if store_step >= 0
        depth = raw_step - store_step
        if depth >= 0 && length(stat.d8_depths) < D8_MAX_DEPTHS
            push!(stat.d8_depths,     depth)
            push!(stat.d8_close_bkt,  UInt16(bkt))
            push!(stat.d8_close_abkt, UInt16(clamp(a_bucket, 0, 65535)))
        end

        # D32: recurrence-gap concentration. Unlike D8_MAX_DEPTHS (capped,
        # prefix sample), this is an O(1) increment-only accumulator over
        # ALL closures, so it never saturates and stays unbiased over
        # arbitrarily long walks — important since the question is about
        # the tail/short-lag SHAPE of the distribution, which a truncated
        # prefix sample could distort if depth and closure order correlate.
        if depth >= 0
            stat.d32_n_closures += 1
            stat.d32_depth_sum  += depth
            # Bucket 0 covers depth in [0,1]; bucket b (b>=1) covers depth
            # in [2^b, 2^(b+1)-1], i.e. bit-length(depth) - 1 for depth >= 2.
            log_bkt = depth <= 1 ? 0 : min(D32_LOG_BUCKETS - 1, (64 - leading_zeros(depth)) - 1)
            @inbounds stat.d32_depth_log_hist[log_bkt + 1] += 1
            if 1 <= depth <= D32_SHORT_LAG_MAX
                @inbounds stat.d32_short_lag_hist[depth] += 1
            end
        end
    end

    # D12 close event — no cap; close events are rare enough to record all of them.
    if alpha_cur >= 0
        push!(stat.d12_close_alpha, alpha_cur)
        push!(stat.d12_close_px,    px)
        push!(stat.d12_close_key,   lp_key)
    end

    # D26: record (store_step, close_step) = (X1, X2) pair for this key.
    # Both timestamps come from this single call: store_step was embedded in
    # the LSM value at insert time; raw_step is this thread's current step
    # (the close time). No cross-thread merge needed for this pair.
    if i0 >= 0 && store_step >= 0 && length(stat.d26_step_range) < D26_MAX_TRACKED_KEYS
        stat.d26_step_range[lp_key] = (store_step, raw_step)
    end

    # D26: update partner bloom mask and close count.
    if i0 >= 0
        bit = UInt64(1) << (i0 % 64)
        stat.d26_partner_mask[lp_key] = get(stat.d26_partner_mask, lp_key, UInt64(0)) | bit
        stat.d26_close_count[lp_key]  = get(stat.d26_close_count,  lp_key, 0) + 1
    end

    return nothing
end

# ---------------------------------------------------------------------------
#  record_conj_deep_opcode! — call from the main walk loop on every valid phi step.
# ---------------------------------------------------------------------------
@inline function record_conj_deep_opcode!(stat       ::ConjDeepStat,
                                           opcode     ::UInt8,
                                           is_emission::Bool)
    length(stat.opcode_log) >= DEEP_DIAG_MAX_OPCODE_LOG && return nothing
    push!(stat.opcode_log,     opcode)
    push!(stat.opcode_is_lp1c, is_emission)
    return nothing
end

# ---------------------------------------------------------------------------
#  record_d16_emission! — call on every LP1-conj emission (close event) for D16.
# ---------------------------------------------------------------------------
@inline function record_d16_emission!(stat        ::ConjDeepStat,
                                       lp_key      ::UInt128,
                                       raw_step    ::Int,
                                       partition_id::Int)
    ec   = stat.d16_emission_count
    ring = ec % D16_RING_SIZE + 1

    h64  = UInt64(lp_key & 0xffffffffffffffff) * UInt64(0x9e3779b97f4a7c15) ⊻
           UInt64(lp_key >> 64)              * UInt64(0x6c62272e07bb0142)
    h64  ⊻= h64 >> 32; h64 *= UInt64(0x45d9f3b37197344d); h64 ⊻= h64 >> 32
    cur_bkt = UInt16(h64 >> (64 - DEEP_DIAG_BUCKET_BITS))

    step_mod_cur = UInt8(raw_step & 0xff)
    part_cur     = UInt16(clamp(partition_id, 0, 65535))

    # Baseline sampling: 1/D16_GATE_DENOM.
    if (rand(UInt8) & UInt8(D16_GATE_DENOM - 1)) == UInt8(0)
        bkey = UInt32(step_mod_cur) << 16 | UInt32(part_cur)
        stat.d16_baseline_hist[bkey] = get(stat.d16_baseline_hist, bkey, 0) + 1
        stat.d16_n_baseline += 1
    end

    # Pre-burst detection: scan ring for lag-Δ matches.
    if ec >= D16_LAG_LO && stat.d16_n_preburst < D16_MAX_SAMPLES
        if (rand(UInt8) & UInt8(D16_GATE_DENOM - 1)) == UInt8(0)
            @inbounds for lag in D16_LAG_LO:D16_LAG_HI
                past_slot = ((ec - lag) % D16_RING_SIZE) + 1
                if stat.d16_ring_bkt[past_slot] == cur_bkt
                    sm_past   = stat.d16_ring_step_mod[past_slot]
                    part_past = stat.d16_ring_partition[past_slot]
                    bkey      = UInt32(sm_past) << 16 | UInt32(part_past)
                    stat.d16_preburst_hist[bkey] = get(stat.d16_preburst_hist, bkey, 0) + 1
                    stat.d16_n_preburst += 1
                    stat.d16_n_preburst >= D16_MAX_SAMPLES && break
                end
            end
        end
    end

    @inbounds begin
        stat.d16_ring_step_mod[ring]  = step_mod_cur
        stat.d16_ring_partition[ring] = part_cur
        stat.d16_ring_bkt[ring]       = cur_bkt
    end
    stat.d16_emission_count = ec + 1
    return nothing
end

# ---------------------------------------------------------------------------
#  record_d19_closure! — call from handle_1lp_conj! at every CLOSE,
#  passing the current anchor index (i0), the stored anchor (prev_col),
#  and the relation scalars (combined_al, combined_be).
# ---------------------------------------------------------------------------
@inline function record_d19_closure!(stat       ::ConjDeepStat,
                                      i0         ::Int,
                                      prev_col   ::Int,
                                      combined_al::Int,
                                      combined_be::Int)
    # Per-element totals.
    stat.d19_fb_close_counts[i0]       = get(stat.d19_fb_close_counts, i0, 0) + 1
    stat.d19_fb_close_counts[prev_col] = get(stat.d19_fb_close_counts, prev_col, 0) + 1

    # Directional split.
    stat.d19_fb_i0_counts[i0]          = get(stat.d19_fb_i0_counts, i0, 0) + 1
    stat.d19_fb_prev_counts[prev_col]  = get(stat.d19_fb_prev_counts, prev_col, 0) + 1

    # Pair co-occurrence (canonical order: lo ≤ hi).
    if i0 != prev_col && length(stat.d19_fb_pair_counts) < D19_MAX_PAIRS
        pkey = i0 < prev_col ? (i0, prev_col) : (prev_col, i0)
        stat.d19_fb_pair_counts[pkey] = get(stat.d19_fb_pair_counts, pkey, 0) + 1
    end

    # Sample relations: store up to 5 *distinct* (i0,prev_col) pairs per anchor
    # on both sides so whichever element ends up in the top-5 will have varied
    # examples to display.  Dedup is by (i0,prev_col) pair — scalars are
    # identical for repeated closures of the same pair anyway.
    rel = (i0, prev_col, combined_al, combined_be)
    for anchor in (i0, prev_col)
        dst = get!(stat.d19_anchor_sample_rels, anchor, NTuple{4,Int}[])
        if length(dst) < 5
            already = false
            for r in dst
                if r[1] == i0 && r[2] == prev_col
                    already = true
                    break
                end
            end
            already || push!(dst, rel)
        end
    end

    return nothing
end

# ---------------------------------------------------------------------------
#  record_d20_step! — call on EVERY valid phi step (hot path, inline).
#  Updates the opcode ring buffer and (1/baseline_rate) baseline reservoir.
#  Also advances the D21 refractory counter.
#  Also writes a (-1,-1,-1) sentinel into the D28 aff ring for non-aff steps.
#
#  opcode should be one of OPCODE_0LP .. OPCODE_SKIP.
#  baseline_gate: sample baseline when (rand(UInt16) & 0x1f) == 0  (1/32 rate).
# ---------------------------------------------------------------------------
@inline function record_d20_step!(stat  ::ConjDeepStat,
                                   opcode::UInt8)
    # ── Ring buffer update ────────────────────────────────────────────────
    head = stat.d20_ring_head
    @inbounds stat.d20_opcode_ring[head] = opcode
    @inbounds stat.d28_aff_ring[head]    = (-1, -1, -1)   # D28 sentinel
    head = head == D20_RING_SIZE ? 1 : head + 1
    stat.d20_ring_head = head
    filled = stat.d20_ring_filled
    stat.d20_ring_filled = filled < D20_RING_SIZE ? filled + 1 : D20_RING_SIZE

    # ── Baseline reservoir (sparse: 1/32 of all steps) ───────────────────
    if stat.d20_n_baseline < D20_BASELINE_CAP && (rand(UInt8) & 0x1f) == 0x00
        # Record opcode-at-position[-k] for k=1..D20_HIST_WINDOW as a tally.
        # We use position 0 = "most recent step before now" = ring[head-1].
        ring = stat.d20_opcode_ring
        cur_filled = stat.d20_ring_filled
        cur_head   = stat.d20_ring_head - 1  # last-written slot (0→D20_RING_SIZE)
        cur_head   = cur_head == 0 ? D20_RING_SIZE : cur_head
        n_avail    = min(cur_filled, D20_HIST_WINDOW)
        for k in 1:n_avail
            slot = cur_head - k + 1
            slot = slot <= 0 ? slot + D20_RING_SIZE : slot
            oc   = Int(ring[slot]) + 1   # 1-based opcode index (1..6)
            @inbounds stat.d20_baseline_opcode_counts[k, oc] += UInt32(1)
        end
        stat.d20_n_baseline += 1
    end

    # ── D21 refractory tracker ────────────────────────────────────────────
    if stat.d21_steps_since_emit >= 0
        stat.d21_steps_since_emit += 1
        # First time we see a 1LP_CONJ opcode after an emission: record return gap.
        if opcode == OPCODE_1LP_CONJ
            if length(stat.d21_return_gaps) < D21_MAX_GAPS
                push!(stat.d21_return_gaps, stat.d21_steps_since_emit)
            end
            stat.d21_steps_since_emit = -1   # stop tracking until next emission
        end
    end

    return nothing
end

# ---------------------------------------------------------------------------
#  record_d28_aff_step! — call in place of record_d20_step! at 1LP-aff sites.
#  Writes the affine LP point (px, py) and current alpha into the D28 ring
#  at the same head position as the opcode ring, then delegates the rest of
#  the D20/D21 bookkeeping to record_d20_step!.
#  Also samples (px, al) into the D28 baseline reservoir at 1/32 rate.
# ---------------------------------------------------------------------------
@inline function record_d28_aff_step!(stat  ::ConjDeepStat,
                                       opcode::UInt8,
                                       px    ::Int,
                                       py    ::Int,
                                       al    ::Int)
    # Write the aff payload *before* record_d20_step! advances the head.
    head = stat.d20_ring_head
    @inbounds stat.d28_aff_ring[head] = (px, py, al)

    # D28 baseline reservoir: sample at 1/32 rate.
    stat.d28_n_baseline += 1
    if length(stat.d28_baseline_px) < D28_BASELINE_CAP && (rand(UInt8) & 0x1f) == 0x00
        push!(stat.d28_baseline_px, px)
        push!(stat.d28_baseline_al, al)
    end

    # Delegate opcode ring + D20 baseline + D21 tracking.
    # record_d20_step! will overwrite d28_aff_ring[head] with sentinel (-1,-1,-1),
    # so we must write our payload first and then prevent the overwrite.
    # We do this inline: copy the D20 logic but skip the sentinel write.
    @inbounds stat.d20_opcode_ring[head] = opcode
    # (d28_aff_ring[head] already set above — do not overwrite with sentinel)
    local new_head = head == D20_RING_SIZE ? 1 : head + 1
    stat.d20_ring_head = new_head
    local filled = stat.d20_ring_filled
    stat.d20_ring_filled = filled < D20_RING_SIZE ? filled + 1 : D20_RING_SIZE

    # D20 baseline opcode tally (1/32 rate, same gate as record_d20_step!).
    if stat.d20_n_baseline < D20_BASELINE_CAP && (rand(UInt8) & 0x1f) == 0x00
        ring = stat.d20_opcode_ring
        cur_filled = stat.d20_ring_filled
        cur_head2  = stat.d20_ring_head - 1
        cur_head2  = cur_head2 == 0 ? D20_RING_SIZE : cur_head2
        n_avail    = min(cur_filled, D20_HIST_WINDOW)
        for k in 1:n_avail
            slot = cur_head2 - k + 1
            slot = slot <= 0 ? slot + D20_RING_SIZE : slot
            oc   = Int(ring[slot]) + 1
            @inbounds stat.d20_baseline_opcode_counts[k, oc] += UInt32(1)
        end
        stat.d20_n_baseline += 1
    end

    # D21 refractory tracker.
    if stat.d21_steps_since_emit >= 0
        stat.d21_steps_since_emit += 1
        if opcode == OPCODE_1LP_CONJ
            if length(stat.d21_return_gaps) < D21_MAX_GAPS
                push!(stat.d21_return_gaps, stat.d21_steps_since_emit)
            end
            stat.d21_steps_since_emit = -1
        end
    end

    return nothing
end

# ---------------------------------------------------------------------------
#  record_d20_emission! — call at every LP1-conj CLOSE (emission).
#  Snapshots the last D20_HIST_WINDOW opcodes from the opcode ring buffer,
#  snapshots the last D20_HIST_WINDOW (px,py,al) tuples from the D28 aff ring,
#  and resets the D21 refractory counter.
#  The two snapshot arrays (d20_pre_snapshots and d28_pre_snapshots) are always
#  kept aligned: element k of each corresponds to lag k before this emission.
# ---------------------------------------------------------------------------
@inline function record_d20_emission!(stat::ConjDeepStat)
    # ── D20 + D28 snapshots ───────────────────────────────────────────────
    if stat.d20_n_snapshots < D20_MAX_SNAPSHOTS
        ring      = stat.d20_opcode_ring
        aff_ring  = stat.d28_aff_ring
        cur_head  = stat.d20_ring_head - 1
        cur_head  = cur_head == 0 ? D20_RING_SIZE : cur_head
        n_avail   = min(stat.d20_ring_filled, D20_HIST_WINDOW)
        for k in 1:D20_HIST_WINDOW
            if k <= n_avail
                slot = cur_head - k + 1
                slot = slot <= 0 ? slot + D20_RING_SIZE : slot
                push!(stat.d20_pre_snapshots, stat.d20_opcode_ring[slot])
                push!(stat.d28_pre_snapshots, stat.d28_aff_ring[slot])
            else
                push!(stat.d20_pre_snapshots, 0xff)        # sentinel: no data
                push!(stat.d28_pre_snapshots, (-1, -1, -1))  # sentinel: no data
            end
        end
        stat.d20_n_snapshots += 1
        stat.d28_n_snapshots  = stat.d20_n_snapshots   # always equal
    end

    # ── D21 reset ────────────────────────────────────────────────────────
    stat.d21_steps_since_emit = 0
    stat.d21_n_emitted       += 1

    return nothing
end

# ---------------------------------------------------------------------------
#  record_d22_d23_d24_emission! — call at every LP1-conj CLOSE (emission).
#
#  raw_step   : absolute walk-step counter for this thread.
#  key_bkt    : 0-based coarse bucket of the LP key (from _deep_bucket).
#  a_bkt      : 0-based bucket of the φ a-coefficient (clamp(a, 0, 65535)).
#
#  D22 logic (entry-event burst geometry):
#    Maintains an open burst window (consecutive emissions each ≤ D22_BURST_SEP
#    apart).  When a burst ends we push its size to d22_burst_sizes and, if the
#    burst was opened by a "cold entry" (gap ≥ mean_gap/2), we also push a
#    cold-entry fingerprint (key_bkt, a_bkt, burst_size) to d22_cold_entries.
#    The EWMA mean_gap_est is updated on every emission.
#
#  D23 logic (kill-renewal cascade probe, walk-unmodified):
#    Each emission opens a D23_CASCADE_WINDOW-step watch.  Subsequent emissions
#    inside the window increment d23_cascade_count.  When the window closes
#    (either by a new emission or by step expiry in record_d22_d23_d24_step!)
#    we store (gap_to_prev, cascade_count) in d23_records.  This measures burst
#    multiplicity without modifying the walk.
#
#  D24 logic (cross-thread burst alignment):
#    Increments a coarse step-bucket counter so that, after the walk, the main
#    thread can check for same-bucket co-occurrence across threads.
# ---------------------------------------------------------------------------
@inline function record_d22_d23_d24_emission!(stat    ::ConjDeepStat,
                                               raw_step::Int,
                                               key_bkt ::Int,
                                               a_bkt   ::Int)
    prev = stat.d22_prev_emit_step
    gap  = prev >= 0 ? raw_step - prev : -1

    # ── D22: burst tracking ───────────────────────────────────────────────
    # Update EWMA of inter-arrival gap.
    if gap > 0
        if stat.d22_mean_gap_est <= 0.0
            stat.d22_mean_gap_est = Float64(gap)
        else
            stat.d22_mean_gap_est = 0.99 * stat.d22_mean_gap_est + 0.01 * Float64(gap)
        end
    end

    new_burst = (prev < 0) || (gap > D22_BURST_SEP)

    if new_burst
        # Close previous burst (if any).
        if stat.d22_cur_burst_size > 0 && length(stat.d22_burst_sizes) < D22_MAX_BURSTS
            push!(stat.d22_burst_sizes, stat.d22_cur_burst_size)
            est     = stat.d22_mean_gap_est
            is_cold = (stat.d22_last_gap < 0) ||
                      (est <= 0.0) ||
                      (stat.d22_last_gap >= est / D22_COLD_GAP_FRAC)
            if is_cold && length(stat.d22_cold_entries) < D22_MAX_ENTRIES
                push!(stat.d22_cold_entries,
                      (stat.d22_cur_burst_keybkt,
                       stat.d22_cur_burst_abkt,
                       stat.d22_cur_burst_size))
            end
        end
        # Open new burst.
        stat.d22_cur_burst_size   = 1
        stat.d22_cur_burst_keybkt = key_bkt
        stat.d22_cur_burst_abkt   = a_bkt
        stat.d22_last_gap         = gap
    else
        stat.d22_cur_burst_size += 1
    end

    stat.d22_prev_emit_step = raw_step

    # ── D23: cascade window management ───────────────────────────────────
    # If we are inside an open watch window, count this emission as cascade.
    if stat.d23_watch_steps_left > 0
        stat.d23_cascade_count += 1
    end
    # Finalise any open window that we are now closing.
    if stat.d23_pending_gap >= 0 && stat.d23_watch_steps_left >= 0
        if length(stat.d23_records) < D23_MAX_RECORDS
            push!(stat.d23_records, (stat.d23_pending_gap, stat.d23_cascade_count))
        end
    end
    # Open fresh watch window for this emission.
    stat.d23_watch_steps_left = D23_CASCADE_WINDOW
    stat.d23_cascade_count    = 0
    stat.d23_pending_gap      = gap   # -1 if this is the very first emission

    # ── D24: step-bucket tally ────────────────────────────────────────────
    bkt = raw_step ÷ D24_BUCKET_STEPS
    if length(stat.d24_emission_buckets) < D24_MAX_BUCKETS || haskey(stat.d24_emission_buckets, bkt)
        stat.d24_emission_buckets[bkt] = get(stat.d24_emission_buckets, bkt, 0) + 1
    end

    return nothing
end

# ---------------------------------------------------------------------------
#  record_d22_d23_d24_step! — call on EVERY valid phi step.
#  Advances the D23 cascade window countdown, D24 step counter, and D25
#  background step counter (steps outside any active burst).
# ---------------------------------------------------------------------------
@inline function record_d22_d23_d24_step!(stat::ConjDeepStat)
    stat.d24_total_walk_steps += 1
    if stat.d23_watch_steps_left > 0
        stat.d23_watch_steps_left -= 1
        if stat.d23_watch_steps_left == 0
            # Window expired naturally — finalise record.
            if stat.d23_pending_gap >= 0 && length(stat.d23_records) < D23_MAX_RECORDS
                push!(stat.d23_records, (stat.d23_pending_gap, stat.d23_cascade_count))
            end
            stat.d23_watch_steps_left = -1
            stat.d23_cascade_count    = 0
            stat.d23_pending_gap      = -1
        end
    end
    return nothing
end

# ---------------------------------------------------------------------------
#  flush_d22_open_burst! — call once after the walk loop completes (per thread)
#  to finalise any burst that was still open when the walk ended.
# ---------------------------------------------------------------------------
@inline function flush_d22_open_burst!(stat::ConjDeepStat)
    stat.d22_cur_burst_size == 0 && return nothing
    length(stat.d22_burst_sizes) >= D22_MAX_BURSTS && return nothing
    push!(stat.d22_burst_sizes, stat.d22_cur_burst_size)
    est     = stat.d22_mean_gap_est
    is_cold = (stat.d22_last_gap < 0) ||
              (est <= 0.0) ||
              (stat.d22_last_gap >= est / D22_COLD_GAP_FRAC)
    if is_cold && length(stat.d22_cold_entries) < D22_MAX_ENTRIES
        push!(stat.d22_cold_entries,
              (stat.d22_cur_burst_keybkt,
               stat.d22_cur_burst_abkt,
               stat.d22_cur_burst_size))
    end
    return nothing
end

# ---------------------------------------------------------------------------
#  record_d25_closure! — call from record_conj_deep_step! on every closure.
#
#  al_close  : alpha_cur at close time  (-1 if unavailable)
#  px_close  : px_anchor at close time  (-1 if unavailable)
#  al_store  : neg_al from the stored LSM value  (-1 if unavailable)
#  depth     : raw_step - store_step  (-1 if unavailable)
#  ell       : group order (for Δal mod ell bucketing)
# ---------------------------------------------------------------------------
@inline function record_d25_closure!(stat     ::ConjDeepStat,
                                      al_close ::Int,
                                      px_close ::Int,
                                      al_store ::Int,
                                      depth    ::Int,
                                      ell      ::Int)
    stat.d25_n_closures += 1
    length(stat.d25_close_al) >= D25_MAX_CLOSURES && return nothing

    # (α, px) cell — bucket to [0, D25_GRID_SIZE) on [0, ell) and [0, p).
    # Use -1 as sentinel when data unavailable; report skips those.
    al_bkt = al_close >= 0 ? (al_close * D25_GRID_SIZE) ÷ max(1, ell) : -1
    px_bkt = px_close >= 0 ? min(px_close * D25_GRID_SIZE ÷ 2_500_000, D25_GRID_SIZE - 1) : -1

    # Depth band: coarsen log2(depth) to 8 levels.
    depth_bkt = if depth <= 0
        -1
    else
        min(7, floor(Int, log2(Float64(depth)) * 8.0 / 23.0))  # 23 ≈ log2(p^1.5)
    end

    # Δal = (al_close - al_store) mod ell, bucketed.
    dal_bkt = if al_close >= 0 && al_store >= 0 && ell > 0
        dal = mod(al_close - al_store, ell)
        (dal * D25_DAL_BUCKETS) ÷ ell
    else
        -1
    end

    push!(stat.d25_close_al,    al_bkt)
    push!(stat.d25_close_px,    px_bkt)
    push!(stat.d25_close_depth, depth_bkt)

    if dal_bkt >= 0
        @inbounds stat.d25_dal_hist[dal_bkt + 1] += 1
    end
    return nothing
end

# ---------------------------------------------------------------------------
# ---------------------------------------------------------------------------
#  record_d34_step! — call from the main walk loop on every valid phi step.
#
#  Arguments:
#    stat    — per-thread ConjDeepStat
#    px      — x-coordinate of current anchor point P0  (-1 if unavailable)
#    p       — field characteristic (for bucketing; must be > 0)
#    outcome — one of D34_OUTCOME_OTHER (0), D34_OUTCOME_0LP (1),
#              D34_OUTCOME_STORE (2).  Pass D34_OUTCOME_STORE only on genuine
#              new-key STORE events (not same-partial hits or closes).
#
#  Hot-path cost: one clamp + one division + three array increments; no alloc.
# ---------------------------------------------------------------------------
const D34_OUTCOME_OTHER = 0
const D34_OUTCOME_0LP   = 1
const D34_OUTCOME_STORE = 2

@inline function record_d34_step!(stat   ::ConjDeepStat,
                                   px     ::Int,
                                   p      ::Int,
                                   outcome::Int)
    (px < 0 || p <= 0) && return nothing
    bkt = clamp(px * D34_X_BUCKETS ÷ p, 0, D34_X_BUCKETS - 1) + 1  # 1-based
    @inbounds stat.d34_n_steps[bkt] += 1
    if outcome == D34_OUTCOME_0LP
        @inbounds stat.d34_n_0lp[bkt]   += 1
    elseif outcome == D34_OUTCOME_STORE
        @inbounds stat.d34_n_store[bkt] += 1
    end
    return nothing
end

@inline function _deep_fp64(key::UInt128)::UInt64
    lo = UInt64(key & 0xffffffffffffffff)
    hi = UInt64(key >> 64)
    h  = lo * UInt64(0x9e3779b97f4a7c15) ⊻ hi * UInt64(0x6c62272e07bb0142)
    h  ⊻= h >> 32; h *= UInt64(0x45d9f3b37197344d); h ⊻= h >> 32
    h
end

@inline function _deep_bucket(key::UInt128)::Int
    Int(_deep_fp64(key) >> (64 - DEEP_DIAG_BUCKET_BITS))
end

# ---------------------------------------------------------------------------
#  Math helpers shared across diagnostic sections
# ---------------------------------------------------------------------------

"""Gini coefficient of a count vector (0 = uniform, 1 = winner-takes-all)."""
function _gini(counts::Vector{Int})::Float64
    n = length(counts)
    n == 0 && return NaN
    s = sum(counts)
    s == 0 && return NaN
    sorted = sort(counts)
    num = 0.0
    for (i, x) in enumerate(sorted)
        num += (2*i - n - 1) * x
    end
    return num / (n * s)
end

"""
Hill tail exponent from top-k order statistics.
Uses log-ratio estimator: α̂ = 1/H̄ where H̄ = mean log(x_i / x_k) for i < k.
"""
function _hill_exponent(sorted_desc::Vector{Int}; k::Int = 50)::Float64
    n = length(sorted_desc)
    k = min(k, n - 1)
    k < 2 && return NaN
    xk = Float64(max(1, sorted_desc[k + 1]))
    s  = 0.0
    for i in 1:k
        s += log(max(1.0, Float64(sorted_desc[i])) / xk)
    end
    return k / max(1e-30, s)
end

"""Fraction of total mass in the top `frac × n` items (sorted descending)."""
function _top_share(counts::Vector{Int}, frac::Float64)::Float64
    isempty(counts) && return 0.0
    total = sum(counts)
    total == 0 && return 0.0
    sorted = sort(counts, rev=true)
    # `frac` may exceed 1 (e.g. callers asking for "top 5" out of fewer than
    # 5 tracked items), so clamp k into [1, length(sorted)] to avoid a
    # BoundsError on the sorted[1:k] slice below.
    k_raw = round(Int, frac * length(sorted))
    k = clamp(k_raw, 1, length(sorted))
    sum(sorted[1:k]) / total
end

"""
Chao1 non-parametric cardinality estimator for latent population size.
Predicts total unique states (support capacity) based on rare event frequencies.
  f1: number of singletons (keys seen exactly once)
  f2: number of doubletons (keys seen exactly twice)
  s_obs: total distinct keys discovered so far
"""
function _chao1_estimate(f1::Int, f2::Int, s_obs::Int)::Float64
    s_obs == 0 && return 0.0
    
    if f2 > 0
        # Classic Chao1 formula
        return Float64(s_obs) + (Float64(f1)^2 / (2.0 * Float64(f2)))
    else
        # Bias-corrected variant to gracefully guard against zero doubletons
        return Float64(s_obs) + (Float64(f1) * Float64(f1 - 1)) / 2.0
    end
end
