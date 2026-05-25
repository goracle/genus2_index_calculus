# =============================================================================
#  phi_bias_diag.jl  --  Diagnostic instrumentation for a-parameter bias.
#
#  Theory recap (see comments in trial3_phi.jl for derivation):
#
#    After normalising d=1, the φ construction collapses to one scalar
#
#      a = (v₁·pₓ + v₀ − pᵧ) / u(pₓ)
#
#    and the residual Mumford coefficients are low-degree polynomials in a:
#
#      c₁_RS = pₓ − u₁ − a²              (degree 2)
#      c₀_RS = −(pₓ−3u₁)a² − 2v₁a + K   (degree 2, K depends on D,pₓ)
#
#    Therefore the split discriminant Δ = c₁²−4c₀ is degree 4 in a.
#
#  Three structural biases to probe (original):
#
#  Surface 1 — 1-D image:  for fixed D, all residual (c₁,c₀) pairs lie on a
#    conic in 𝔽ₚ², not a dense 2-D cloud.  Measured by image-collision rate.
#
#  Surface 2 — discriminant bias:  split events are governed by Δ(a) (degree 4),
#    so splits are not uniformly distributed in a.  Measured by a χ² test on
#    a histogram of the a-value at each split step.
#
#  Surface 3 — a=0 slice:  when a=0 the residual is completely determined by D
#    and pᵧ dependence), so O(√p) distinct anchors all produce the same
#    (c₁,c₀).  Measured by comparing FB-smooth rate at a=0 vs overall.
#
#  Three sequential-structure diagnostics (new):
#
#  Seq 1 — Run-length distribution:  if split/non-split outcomes are i.i.d.
#    Bernoulli(1/2), run lengths follow Geometric(1/2).  We accumulate the
#    empirical run-length histogram and compute a KS statistic against the
#    Geometric(1/2) CDF.  Shorter-than-geometric runs → anti-correlation
#    (bouncing between regions); longer → positive correlation (clustering).
#
#  Seq 2 — LP1-conj temporal Fano factor:  if LP1-conj hits are Poisson in
#    walk-step time, the inter-arrival variance equals the mean (Fano = 1).
#    Fano >> 1 indicates the walk spends time in high-productivity Jacobian
#    regions — algebraic structure in the LP1-conj observable.
#
#  Seq 3 — Post-LP anchor correlation:  after a 1-LP event the next anchor
#    P0_{n+1} is the LP point itself (not a random FB element), creating a
#    potential correlation between the anchor and D_{n+1}.  We compare the
#    a-histogram on post-LP steps against the baseline histogram.  A KS
#    divergence here means the LP-derived anchors bias the a-distribution.
#
#  Four spectral diagnostics (computed post-hoc from lp1_conj_arrivals):
#
#  Spec 1 — Welch PSD:  bin arrivals into fixed windows → binary indicator →
#    Hann-windowed DFT per window, averaged (Welch estimate).  Compared to a
#    shuffled-gap null.  Low-frequency lift > 2× indicates long-range order.
#
#  Spec 2 — Windowed spectrogram:  divide arrivals into 4 chronological slices
#    and report per-slice density and gap CV.  Reveals regime switching and
#    intermittency invisible to global statistics.
#
#  Spec 3 — Shuffled spectral comparison:  built into Spec 1 above; every PSD
#    bin is shown alongside its shuffled-gap null.
#
#  Spec 4 — Allan factor variance scaling:  F(T) = Var(N_T)/E[N_T] over a
#    geometric progression of window sizes.  Poisson → F(T)≈1; clustered →
#    F(T) grows.  A log-log slope (Hurst proxy) summarises long-memory.
#
#  Five new signal diagnostics (computed post-hoc from lp1_conj_arrivals and
#  lp1_conj_a_hist; New 3 requires one extra field in PhiBiasStat):
#
#  New 1 — Density autocorrelation:  bin arrivals into coarse count series and
#    compute lag-1/2/3 ACF.  Positive ACF → persistent hot/cold epochs.
#
#  New 2 — Hot/cold window conditioning:  classify windows by hit density
#    (hot ≥ median, cold < median) and compute lift = E[N_{t+1}|hot] /
#    E[N_{t+1}|cold].  Lift >> 1 means bursts are temporally predictive.
#
#  New 3 — State-space a-region hotness:  compare LP1-conj emission histogram
#    per a-bucket against visit histogram (split_hist) to find dynamically hot
#    a-regions.  χ²/dof flags systematic dynamic bias.
#
#  New 4 — Multitaper PSD + spectral slope:  K=4 cosine tapers for reduced
#    variance at low frequencies; OLS log-log slope gives 1/fᵅ exponent α.
#    α > 1 → long-memory; α ≈ 0 → white noise.
#
#  New 5 — Gap-distribution characterisation (replaces unstable MMPP-2 MoM fit):
#    (a) burst-size distribution with KS test vs Geometric null,
#    (b) short/long gap fractions vs Poisson prediction (hot/cold persistence),
#    (c) KS test of rescaled gaps vs Exponential(1) with heavy-tail flag.
#
#  Seven α₂ scaling diagnostics (computed post-hoc from lp1_conj_bucket_log
#  and lp1_conj_arrivals; all diagnostics focus on the LP1-conj key space,
#  consistent with the birthday block.  slog is implicitly all-true since
#  every LP1-conj emission is a split step; α₂-7 and α₂-9 therefore use
#  alternative splits — first/second-half and inter-block KL respectively):
#
#  α₂-1 — Time-resolved α₂(T):  dyadic windows T, 2T, 4T … covering the full
#    run.  Tracks α₂(T) and dα₂/d(logT).  Convergence → single exponent;
#    two plateaus → burst/mixing crossover (Case B); indefinite drift → Case C.
#
#  α₂-2 — Intra vs inter-regime collision split:  classify each step as hot or
#    cold based on LP1-conj hit density in a surrounding window.  Split S₂ into
#    S₂^intra (both steps in same class) and S₂^inter (different class).
#    Dominated by intra at short T, inter at long T → proven two-timescale system.
#
#  α₂-3 — Regime-conditioned α₂:  α₂|hot and α₂|cold computed separately.
#    Δα₂ = α₂^hot − α₂^cold ≠ 0 → α₂ is NOT an invariant of the walk kernel.
#
#  α₂-4 — Collision autocorrelation C(τ):  for each bucket i, E[cᵢ(t)·cᵢ(t+τ)].
#    Exponential decay → classical mixing; power-law → α₂ ill-defined globally.
#    Hurst exponent from log-log slope.
#
#  α₂-5 — Collision burst size spectrum:  per-bucket run lengths of consecutive
#    hits; distribution P(L).  Geometric baseline vs power-law tail test.
#    Power-law → α₂ dominated by rare-event geometry.
#
#  α₂-6 — ρ(T) = S_occ(T)/S₂(T):  ratio of occupancy entropy to collision
#    entropy over dyadic windows.  ρ ≈ const → consistent scaling dimension;
#    ρ growing → decoupled geometry.
#
#  α₂-7 — LP1-conj key geometry stationarity:  α₂ on first half vs second half
#    of the emission sequence.  Δα₂ ≠ 0 → non-stationary key geometry over run.
#
#  All accumulators are per-thread (no locking during the walk).
#  Call merge_phi_bias_stats to combine and print_phi_bias_report to display.
#
#  Overhead: one Int comparison (a==0), one histogram bucket write, and one
#  (c1,c0) hash-insert per valid phi step — negligible relative to the Jacobian
#  arithmetic that dominates phase2_worker.
# =============================================================================

using FFTW   # required for rfft / plan_rfft in Welch and multitaper sections

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

    # step_bucket_log: bucket index (1-based) of every valid phi step, in
    # chronological order.  Position in the vector is the step ordinal.
    # Used post-hoc for all seven α₂ diagnostics.  One Int per step.
    step_bucket_log ::Vector{Int}
    # split_step_log: true iff the corresponding step in step_bucket_log was a
    # split step (residual quadratic split over 𝔽ₚ).  Parallel to step_bucket_log.
    # Used for α₂-7 (φ-conditioned α₂).
    split_step_log  ::Vector{Bool}
    # event_hash_log: thread-local provenance hash chain over the recorded step
    # stream.  A repeated hash is a strong hint that the walk is revisiting the
    # same structural motif rather than merely the same scalar summary.
    event_hash_log  ::Vector{UInt64}
    _event_hash_state::UInt64
end

const MAX_RUN_LEN = 64   # run-length histogram cap (longer runs fold into bin 64)

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
        Int[],                         # step_bucket_log
        Bool[],                        # split_step_log
        UInt64[],                      # event_hash_log
        UInt64(0x9e3779b97f4a7c15),    # _event_hash_state
    )
end

# ---------------------------------------------------------------------------
#  record_phi_step! — called once per valid phi step in phase2_worker.
#
#  Arguments:
#    stat     — per-thread PhiBiasStat
#    a        — the scalar a from build_phi_mumford (already reduced mod p)
#    c1_rs    — first Mumford coeff of residual quadratic
#    c0_rs    — second Mumford coeff of residual quadratic
#    split    — true iff the residual split over 𝔽ₚ (rs_split)
#    r_in_fb  — true iff R is in the factor base (iR != 0), ignored when !split
#    s_in_fb  — true iff S is in the factor base (iS != 0), ignored when !split
#    d_key    — (u0,u1,v0,v1) Mumford representation of the current divisor D
#    p        — field characteristic (used for bucket index)
# ---------------------------------------------------------------------------
@inline function record_phi_step!(stat   ::PhiBiasStat,
                                   a      ::Int,
                                   c1_rs  ::Int,
                                   c0_rs  ::Int,
                                   split  ::Bool,
                                   r_in_fb::Bool,
                                   s_in_fb::Bool,
                                   d_key  ::NTuple{4,Int},
                                   p      ::Int)
    stat.total += 1

    # --- Bucket index for a (0-based bucket, 1-indexed in array) ---
    nbuckets = length(stat.split_hist)
    # a is already in [0, p-1].  Multiply-then-shift is branch-free.
    bucket = 1 + (a * nbuckets) ÷ p   # integer division, result in [1,nbuckets]
    bucket = clamp(bucket, 1, nbuckets)

    if split
        stat.split_hist[bucket] += 1
    else
        stat.nonsplit_hist[bucket] += 1
    end

    # --- a=0 slice ---
    if a == 0
        stat.a_zero += 1
        if split
            stat.a_zero_split += 1
            if r_in_fb && s_in_fb
                stat.a_zero_fb += 1
            end
        end
    end

    # --- Image-collision tracking (rolling per-D window) ---
    if d_key !== stat._img_key
        # Divisor changed: reset window.
        empty!(stat._img_seen)
        stat._img_key = d_key
    end
    img_pair = (c1_rs, c0_rs)
    if img_pair in stat._img_seen
        stat.image_collisions += 1
    else
        push!(stat._img_seen, img_pair)
    end

    # --- Seq 1: run-length tracking ---
    if stat._run_len == 0
        # First step ever: initialise run state.
        stat._run_is_split = split
        stat._run_len      = 1
    elseif split == stat._run_is_split
        stat._run_len += 1
    else
        # Run ended — commit it.
        k = clamp(stat._run_len, 1, MAX_RUN_LEN)
        if stat._run_is_split
            stat.run_hist_split[k] += 1
        else
            stat.run_hist_nonsplit[k] += 1
        end
        # Start new run.
        stat._run_is_split = split
        stat._run_len      = 1
    end

    # --- Seq 3: post-LP anchor histogram ---
    if stat._prev_anchor_was_lp
        stat.post_lp_a_hist[bucket] += 1
    else
        stat.baseline_a_hist[bucket] += 1
    end
    # _prev_anchor_was_lp is set externally by record_lp1_conj_anchor! /
    # record_random_anchor! — those are called by the walk loop after updating
    # cur_pt, not here, so the flag read above reflects the *previous* step's
    # anchor choice, which is what we want.

    # --- α₂ timeseries logging ---
    push!(stat.step_bucket_log, bucket)
    push!(stat.split_step_log,  split)

    # --- provenance hash chain (thread-local) ---
    stat._event_hash_state = _mix_event_hash(stat._event_hash_state, bucket, split, a, c1_rs, c0_rs, stat.total)
    push!(stat.event_hash_log, stat._event_hash_state)

    return nothing
end

# ---------------------------------------------------------------------------
#  record_lp1_conj_partial! — called inside handle_1lp_conj! on EVERY partial
#  (both stored and closed), to build the full LP1-conj key stream for α₂ scaling.
#  Uses the same fingerprint hash as the LSM (_lsm_fp) so the bucket indices are
#  consistent with lsm_bday_report's Rényi estimator.
#  RENYI_BITS = 14 → 16384 buckets; UInt16 bucket index is stored per partial.
# ---------------------------------------------------------------------------
const _PHI_RENYI_BITS  = 14
const _PHI_RENYI_SHIFT = 64 - _PHI_RENYI_BITS

@inline function _phi_fp(key::UInt128)::UInt64
    lo = UInt64(key & 0xffffffffffffffff)
    hi = UInt64(key >> 64)
    h  = lo * UInt64(0x9e3779b97f4a7c15) +
         hi * UInt64(0x6c62272e07bb0142)
    h  = h ⊻ (h >> 32)
    h  = h * UInt64(0x45d9f3b37197344d)
    h  = h ⊻ (h >> 32)
    h
end

@inline function record_lp1_conj_partial!(stat::PhiBiasStat, lp_key::UInt128)
    bkt = UInt16(_phi_fp(lp_key) >> _PHI_RENYI_SHIFT)
    push!(stat.lp1_conj_key_blog, bkt)
    return nothing
end

# ---------------------------------------------------------------------------
#  record_lp1_conj_hit! — called inside handle_1lp_conj! only when a relation
#  is actually emitted (i.e. a birthday match is closed).  raw_step is the
#  current s.raw_steps counter passed through from the worker.
#  lp_key is the CanonicalLP1Key (UInt128) of the emitted LP1-conj hit.
#  a_bucket is the 1-based bucket index of the triggering a-value (same
#  bucketing as split_hist); pass 0 if not available to skip hotness tracking.
# ---------------------------------------------------------------------------
@inline function record_lp1_conj_hit!(stat::PhiBiasStat, raw_step::Int,
                                       lp_key::UInt128 = zero(UInt128),
                                       a_bucket::Int   = 0)
    push!(stat.lp1_conj_arrivals, raw_step)
    push!(stat.lp1_conj_keys,     lp_key)
    if 1 <= a_bucket <= length(stat.lp1_conj_a_hist)
        stat.lp1_conj_a_hist[a_bucket] += 1
    end
    push!(stat.lp1_conj_bucket_log, a_bucket > 0 ? a_bucket : 1)
    stat._prev_anchor_was_lp = true
    return nothing
end

# ---------------------------------------------------------------------------
#  record_random_anchor! — called when cur_pt is set to a random FB element
#  (i.e. NOT from an LP event).  Clears the post-LP flag.
# ---------------------------------------------------------------------------
@inline function record_random_anchor!(stat::PhiBiasStat)
    stat._prev_anchor_was_lp = false
    return nothing
end

# ---------------------------------------------------------------------------
#  hash / moment helpers for post-hoc diagnostics
# ---------------------------------------------------------------------------
@inline function _rotl64(x::UInt64, r::Int)::UInt64
    rr = r & 63
    return (x << rr) | (x >> ((64 - rr) & 63))
end

@inline function _mix_u64(x::UInt64)::UInt64
    # SplitMix64 finalizer.
    x ⊻= x >> 30
    x *= UInt64(0xbf58476d1ce4e5b9)
    x ⊻= x >> 27
    x *= UInt64(0x94d049bb133111eb)
    x ⊻= x >> 31
    return x
end

@inline function _mix_event_hash(prev::UInt64, bucket::Int, split::Bool,
                                 a::Int, c1::Int, c0::Int, step::Int)::UInt64
    h = prev ⊻ UInt64(0x9e3779b97f4a7c15)
    h ⊻= _mix_u64(UInt64(bucket) + (split ? UInt64(0x1111111111111111) : UInt64(0x2222222222222222)))
    h ⊻= _mix_u64(UInt64(abs(a)) + UInt64(0x9e3779b97f4a7c15))
    h ⊻= _mix_u64(UInt64(abs(c1)) ⊻ _rotl64(UInt64(abs(c0)), 17))
    h ⊻= _mix_u64(UInt64(step) * UInt64(0x5851f42d4c957f2d))
    return _mix_u64(h)
end

function _moment4(xs::AbstractVector{<:Real})
    n = length(xs)
    n == 0 && return (NaN, NaN, NaN, NaN)
    μ = sum(float(x) for x in xs) / n
    if n == 1
        return (μ, 0.0, 0.0, 0.0)
    end
    diffs = [float(x) - μ for x in xs]
    m2 = sum(d*d for d in diffs) / n
    if m2 < 1e-30
        return (μ, 0.0, 0.0, 0.0)
    end
    m3 = sum(d^3 for d in diffs) / n
    m4 = sum(d^4 for d in diffs) / n
    σ = sqrt(m2)
    skew = m3 / (σ^3)
    kurt = m4 / (σ^4) - 3.0
    return (μ, m2, skew, kurt)
end

function _kl_divergence_counts(p::Vector{Int}, q::Vector{Int}; pseudo::Float64 = 0.5)
    @assert length(p) == length(q)
    sp = sum(p) + pseudo * length(p)
    sq = sum(q) + pseudo * length(q)
    kl = 0.0
    for i in eachindex(p)
        pi = (p[i] + pseudo) / sp
        qi = (q[i] + pseudo) / sq
        kl += pi * log2(pi / max(1e-300, qi))
    end
    return kl
end

function _top_share(hist::Vector{Int}, frac::Float64)
    n = sum(hist)
    n == 0 && return 0.0
    k = max(1, ceil(Int, frac * length(hist)))
    vals = sort(hist, rev=true)
    return sum(vals[1:min(k, length(vals))]) / n
end

# ---------------------------------------------------------------------------
#  merge_phi_bias_stats — reduce per-thread stats into one aggregate.
# ---------------------------------------------------------------------------
function merge_phi_bias_stats(stats::Vector{PhiBiasStat})::PhiBiasStat
    isempty(stats) && error("merge_phi_bias_stats: empty input")
    # Use first element as prototype for bucket count.
    p_dummy = length(stats[1].split_hist)^2   # approximate p (bucket count = √p)
    merged = PhiBiasStat(p_dummy)
    # Resize histograms to match (they should all be the same length).
    nb = length(stats[1].split_hist)
    resize!(merged.split_hist,       nb); fill!(merged.split_hist,       0)
    resize!(merged.nonsplit_hist,    nb); fill!(merged.nonsplit_hist,    0)
    resize!(merged.post_lp_a_hist,   nb); fill!(merged.post_lp_a_hist,  0)
    resize!(merged.baseline_a_hist,  nb); fill!(merged.baseline_a_hist, 0)
    resize!(merged.lp1_conj_a_hist,  nb); fill!(merged.lp1_conj_a_hist, 0)
    resize!(merged.run_hist_split,    MAX_RUN_LEN); fill!(merged.run_hist_split,    0)
    resize!(merged.run_hist_nonsplit, MAX_RUN_LEN); fill!(merged.run_hist_nonsplit, 0)

    for s in stats
        merged.total            += s.total
        merged.a_zero           += s.a_zero
        merged.a_zero_split     += s.a_zero_split
        merged.a_zero_fb        += s.a_zero_fb
        merged.image_collisions += s.image_collisions
        append!(merged.lp1_conj_arrivals, s.lp1_conj_arrivals)
        append!(merged.lp1_conj_keys,     s.lp1_conj_keys)
        for i in eachindex(merged.split_hist)
            merged.split_hist[i]       += s.split_hist[i]
            merged.nonsplit_hist[i]    += s.nonsplit_hist[i]
            merged.post_lp_a_hist[i]   += s.post_lp_a_hist[i]
            merged.baseline_a_hist[i]  += s.baseline_a_hist[i]
            merged.lp1_conj_a_hist[i]  += s.lp1_conj_a_hist[i]
        end
        for k in 1:MAX_RUN_LEN
            merged.run_hist_split[k]    += s.run_hist_split[k]
            merged.run_hist_nonsplit[k] += s.run_hist_nonsplit[k]
        end
        # α₂ timeseries: concatenate across threads (order within each thread
        # is already chronological; cross-thread interleaving is unordered but
        # sufficient for all dyadic-window α₂ computations).
        append!(merged.step_bucket_log, s.step_bucket_log)
        append!(merged.split_step_log,  s.split_step_log)
        append!(merged.event_hash_log,  s.event_hash_log)
        append!(merged.lp1_conj_bucket_log, s.lp1_conj_bucket_log)
        append!(merged.lp1_conj_key_blog,    s.lp1_conj_key_blog)
    end
    return merged
end

# ---------------------------------------------------------------------------
#  print_phi_bias_report — human-readable summary with χ² test.
# ---------------------------------------------------------------------------
function print_phi_bias_report(stat::PhiBiasStat; p::Int = 0)
    total    = stat.total
    nb       = length(stat.split_hist)
    n_split  = sum(stat.split_hist)
    n_nonspl = sum(stat.nonsplit_hist)

    @printf("\n── φ a-parameter bias report ─────────────────────────────────────────\n")
    @printf("  valid phi steps recorded : %d\n", total)
    @printf("  split steps              : %d  (%.2f%% of recorded)\n",
            n_split, 100.0 * n_split / max(1, total))
    @printf("  non-split steps          : %d  (%.2f%%)\n",
            n_nonspl, 100.0 * n_nonspl / max(1, total))
    println()

    # --- Surface 3: a=0 slice ---
    @printf("  Surface 3 — a=0 slice:\n")
    @printf("    a=0 steps              : %d  (%.4f%% of recorded)\n",
            stat.a_zero, 100.0 * stat.a_zero / max(1, total))
    @printf("    a=0 split rate         : %.2f%%  (overall split: %.2f%%)\n",
            100.0 * stat.a_zero_split / max(1, stat.a_zero),
            100.0 * n_split / max(1, total))
    @printf("    a=0 FB-smooth rate     : %.2f%%  (of a=0 split steps)\n",
            100.0 * stat.a_zero_fb / max(1, stat.a_zero_split))
    println()

    # --- Surface 1: image collisions ---
    @printf("  Surface 1 — residual image collisions:\n")
    @printf("    (c₁,c₀) collisions     : %d  (%.4f%% of recorded)\n",
            stat.image_collisions, 100.0 * stat.image_collisions / max(1, total))
    @printf("    interpretation: if > 0, two distinct a-values from the same D\n")
    @printf("    produced identical residual Mumford pairs — algebraic thinness.\n")
    println()

    # --- Surface 2: discriminant bias (χ² on split histogram) ---
    @printf("  Surface 2 — discriminant bias (split histogram χ² test):\n")
    @printf("    histogram buckets      : %d  (each ~%s wide in 𝔽ₚ)\n",
            nb, p > 0 ? string(p ÷ nb) : "p/√p")
    if n_split > 0
        expected  = n_split / nb
        chi2_split = sum((x - expected)^2 / max(1.0, expected)
                         for x in stat.split_hist)
        dof = nb - 1
        @printf("    split χ²               : %.2f  (dof=%d; uniform expected ≈ %.1f)\n",
                chi2_split, dof, Float64(dof))
        # Rule of thumb: χ² / dof >> 1 indicates non-uniformity.
        ratio = chi2_split / max(1.0, Float64(dof))
        flag  = ratio > 2.0 ? " ← NON-UNIFORM" : " (consistent with uniform)"
        @printf("    χ²/dof                 : %.3f%s\n", ratio, flag)
    else
        @printf("    (no split steps recorded — χ² not computed)\n")
    end

    # Also χ² for non-split steps (should be uniform if Δ is random).
    if n_nonspl > 0
        expected2   = n_nonspl / nb
        chi2_nonspl = sum((x - expected2)^2 / max(1.0, expected2)
                          for x in stat.nonsplit_hist)
        dof2 = nb - 1
        @printf("    non-split χ²           : %.2f  (dof=%d)\n", chi2_nonspl, dof2)
    end

    # --- Top buckets (show the 5 most-populated split buckets) ---
    if n_split > 0 && nb >= 5
        indexed  = collect(enumerate(stat.split_hist))
        top5     = sort(indexed, by=x->-x[2])[1:min(5, end)]
        @printf("    top split buckets (bucket_idx, count):\n")
        for (bi, cnt) in top5
            frac = p > 0 ? @sprintf(" [a ∈ [%d,%d))", (bi-1)*p÷nb, bi*p÷nb) : ""
            @printf("      bucket %4d%s : %d  (%.2f%% of splits)\n",
                    bi, frac, cnt, 100.0*cnt/n_split)
        end
    end

    # --- Seq 1: Run-length distribution KS test ---
    @printf("  Seq 1 — Run-length distribution (KS vs Geometric(1/2)):\n")
    for (label, hist) in (("split", stat.run_hist_split), ("non-split", stat.run_hist_nonsplit))
        n_runs = sum(hist)
        if n_runs >= 10
            # Empirical CDF vs Geometric(1/2) CDF: P(L ≤ k) = 1 - (1/2)^k
            ks_stat = 0.0
            cumul   = 0.0
            for k in 1:MAX_RUN_LEN
                cumul     += hist[k] / n_runs
                geo_cdf    = 1.0 - 0.5^k
                ks_stat    = max(ks_stat, abs(cumul - geo_cdf))
            end
            mean_run = sum(k * hist[k] for k in 1:MAX_RUN_LEN) / n_runs
            # Geometric(1/2) has mean = 2.
            flag = ks_stat > 0.05 ? (mean_run > 2.0 ? " ← LONG RUNS (pos corr)" :
                                                        " ← SHORT RUNS (anti-corr)") :
                                    " (consistent with i.i.d.)"
            @printf("    %-9s runs: n=%d  mean_len=%.2f  KS=%.4f%s\n",
                    label, n_runs, mean_run, ks_stat, flag)
            # Show run-length histogram up to k=10
            @printf("      len:  %s\n", join([@sprintf("%4d", k) for k in 1:min(10,MAX_RUN_LEN)], " "))
            @printf("      cnt:  %s\n", join([@sprintf("%4d", hist[k]) for k in 1:min(10,MAX_RUN_LEN)], " "))
            if MAX_RUN_LEN > 10
                overflow = sum(hist[11:end])
                @printf("      cnt[11+]: %d\n", overflow)
            end
        else
            @printf("    %-9s runs: n=%d  (too few for KS test)\n", label, n_runs)
        end
    end
    println()

    # --- Seq 2: LP1-conj Fano factor + CIR + Spectral (Welch PSD, spectrogram,
    #           Allan factor) + key fingerprint ---
    @printf("  Seq 2 — LP1-conj temporal analysis:\n")
    arrivals = stat.lp1_conj_arrivals
    lp_keys  = stat.lp1_conj_keys
    if length(arrivals) >= 4
        # Sort by arrival time (merge across threads may be out of order).
        perm     = sortperm(arrivals)
        arrivals = arrivals[perm]
        lp_keys  = lp_keys[perm]

        gaps    = [arrivals[i] - arrivals[i-1] for i in 2:length(arrivals)]
        n_gaps  = length(gaps)
        mean_gap = sum(gaps) / n_gaps
        var_gap  = n_gaps > 1 ? sum((g - mean_gap)^2 for g in gaps) / (n_gaps - 1) :
                                 0.0
        fano    = var_gap / max(1.0, mean_gap)
        flag_fano = fano > 2.0 ? " ← CLUSTERING (algebraic structure)" :
                    fano < 0.5 ? " ← ANTI-CLUSTERING (over-dispersed)"  :
                                 " (consistent with Poisson)"
        @printf("    LP1-conj hits    : %d\n", length(arrivals))
        @printf("    inter-arrival μ  : %.1f steps\n", mean_gap)
        @printf("    inter-arrival σ² : %.1f\n", var_gap)
        @printf("    Fano factor      : %.3f%s\n", fano, flag_fano)

        # ---- Conditional Intensity Ratio (CIR) --------------------------------
        # Null realisations are independent — parallelise over them with
        # per-thread RNGs.  Observed counts are O(N log N) and fast; serial.
        @printf("    Conditional Intensity Ratios (CIR) vs shuffled-gap null:\n")
        @printf("      window  observed  null_mean  CIR    interpretation\n")
        n_hits   = length(arrivals)
        n_shuf   = 20
        # Pre-generate all n_shuf shuffled arrival arrays in parallel.
        # One RNG per iteration slot — avoids threadid() bounds issues when
        # Julia schedules tasks with IDs that exceed nthreads().
        cir_rngs     = [MersenneTwister(rand(UInt64)) for _ in 1:n_shuf]
        null_arrs    = [similar(arrivals) for _ in 1:n_shuf]
        Threads.@threads for si in 1:n_shuf
            sg     = copy(gaps)
            rng_c  = cir_rngs[si]
            for k in n_gaps:-1:2
                j2 = rand(rng_c, 1:k)
                sg[k], sg[j2] = sg[j2], sg[k]
            end
            na = null_arrs[si]
            na[1] = arrivals[1]
            for k in 2:n_hits
                na[k] = na[k-1] + sg[k-1]
            end
            sort!(na)
        end

        for W in (10, 50, 200, 500, 1000, 2000, 5000, 10000, 50000, 100000, 250000, 500000, 1000000)
            # Observed count: O(N log N), fast serial.
            obs_count = 0
            for i in 1:n_hits
                hi = searchsortedlast(arrivals, arrivals[i] + W)
                obs_count += max(0, hi - i)
            end

            # Null: reuse pre-shuffled arrays — just count pairs per array.
            null_counts = zeros(Int, n_shuf)
            Threads.@threads for si in 1:n_shuf
                na  = null_arrs[si]
                cnt = 0
                for i in 1:n_hits
                    hi = searchsortedlast(na, na[i] + W)
                    cnt += max(0, hi - i)
                end
                null_counts[si] = cnt
            end
            null_mean = sum(null_counts) / n_shuf
            cir       = obs_count / max(1.0, null_mean)
            flag_cir  = cir > 1.5 ? " ← HOT (basin exploitable)" :
                        cir < 0.7 ? " ← COLD (anti-clustered)"   :
                                    " (≈ random)"
            @printf("      W=%-5d  %8d  %9.1f  %5.3f  %s\n",
                    W, obs_count, null_mean, cir, flag_cir)
        end

        # ---- Spectral 1: Welch PSD of hit-indicator binary sequence -------------
        @printf("    Welch PSD (hit-indicator series):\n")
        if length(arrivals) >= 8
            total_span = arrivals[end] - arrivals[1] + 1
            n_welch_win = max(4, min(64, length(arrivals) ÷ 8))

            # FIX: Cap the FFT window size to a power of 2 (max 4096 bins).
            # Binning the raw steps prevents massive prime-sized FFT allocations
            # that cause O(N^2) memory explosions and OOMs.
            W_span      = max(8, total_span ÷ n_welch_win)
            win_len     = min(4096, nextpow(2, W_span))
            n_bins_half = win_len ÷ 2 + 1

            hann_w   = [0.5 * (1.0 - cos(2π * (i-1) / max(1, win_len-1))) for i in 1:win_len]

            # FIX: Remove the shared fft_plan. FFTW plans aren't always safe for 
            # concurrent execution on different arrays. Direct rfft is fast and lock-free.
            function _psd_window_fft(ind_buf::Vector{Float64},
                                     tmp_buf::Vector{Float64})::Vector{Float64}
                length(ind_buf) == length(tmp_buf) || throw(ArgumentError("Buffer size mismatch in Welch PSD window"))
                @inbounds @simd for i in eachindex(tmp_buf)
                    tmp_buf[i] = ind_buf[i] * hann_w[i]
                end
                return abs2.(rfft(tmp_buf))
            end

            n_wins_used = 0
            # --- Real PSD: parallel over Welch windows --------------------------
            psd_wins    = [zeros(Float64, n_bins_half) for _ in 1:n_welch_win]
            wins_valid  = zeros(Bool, n_welch_win)
            offset      = arrivals[1]
            Threads.@threads for wi in 0:(n_welch_win - 1)
                t_start  = offset + wi * W_span
                t_end    = t_start + W_span - 1
                ind      = zeros(Float64, win_len)
                tmp      = zeros(Float64, win_len)

                lo = searchsortedfirst(arrivals, t_start)
                hi = searchsortedlast(arrivals,  t_end)
                for k in lo:hi
                    idx = arrivals[k] - t_start
                    b_idx = clamp(floor(Int, idx * win_len / W_span) + 1, 1, win_len)
                    ind[b_idx] += 1.0
                end
                if (hi >= lo)
                    psd_wins[wi + 1]   = _psd_window_fft(ind, tmp)
                    wins_valid[wi + 1] = true
                end
            end
            # Explicitly count valid windows after the thread loop
            n_wins_used = count(wins_valid)
            psd_sum = zeros(Float64, n_bins_half)

            if n_wins_used > 0
                for wi in 1:n_welch_win
                    if wins_valid[wi]
                        psd_sum .+= psd_wins[wi]
                    end
                end
                psd_sum ./= n_wins_used
            end
            
            # Now, psd_sum is guaranteed to exist in this scope for the report
            @printf("    Welch PSD done (%d windows). Peak power: %.4e\n", 
                    n_wins_used, maximum(psd_sum))
            # --- Shuffled-null PSD: parallel over realisations ------------------
            n_spec_shuf    = 20
            shuf_rngs      = [MersenneTwister(rand(UInt64)) for _ in 1:n_spec_shuf]
            psd_shuf_slots = [zeros(Float64, n_bins_half) for _ in 1:n_spec_shuf]
            shuf_valid     = zeros(Bool, n_spec_shuf)

            Threads.@threads for si in 1:n_spec_shuf
                rng = shuf_rngs[si]
                shuf_g = copy(gaps)
                for k in length(shuf_g):-1:2
                    j2 = rand(rng, 1:k)
                    shuf_g[k], shuf_g[j2] = shuf_g[j2], shuf_g[k]
                end
                null_arr2 = similar(arrivals)
                null_arr2[1] = arrivals[1]
                for k in 2:length(arrivals)
                    null_arr2[k] = null_arr2[k-1] + shuf_g[k-1]
                end
                sort!(null_arr2)

                win_sum  = zeros(Float64, n_bins_half)
                win_cnt  = 0
                ind2 = zeros(Float64, win_len)
                tmp2 = zeros(Float64, win_len)

                for wi in 0:(n_welch_win - 1)
                    t_start = offset + wi * W_span
                    t_end   = t_start + W_span - 1
                    fill!(ind2, 0.0)

                    lo2 = searchsortedfirst(null_arr2, t_start)
                    hi2 = searchsortedlast(null_arr2,  t_end)
                    for k in lo2:hi2
                        idx = null_arr2[k] - t_start
                        b_idx = clamp(floor(Int, idx * win_len / W_span) + 1, 1, win_len)
                        ind2[b_idx] += 1.0
                    end
                    if hi2 >= lo2
                        win_sum .+= _psd_window_fft(ind2, tmp2)
                        win_cnt  += 1
                    end
                end
                if win_cnt >= 1
                    psd_shuf_slots[si] = win_sum ./ win_cnt
                    shuf_valid[si]     = true
                end
            end


            psd_shuf_avg = any(shuf_valid) ?
                           reduce(.+, psd_shuf_slots[shuf_valid]) ./ max(1, sum(shuf_valid)) :
                           zeros(Float64, n_bins_half)
            # n_bins_half is rfft output length (win_len÷2+1); downstream
            # indexing into psd_avg / psd_shuf_avg is safe because both arrays
            # have this length.

            if n_wins_used >= 2
                psd_avg = psd_sum ./ n_wins_used

                # n_bins_half = rfft length = win_len÷2+1 (DC bin + positive freqs).
                # Bin 1 = DC; bins 2..n_bins_half are positive freqs.
                # low-freq = bottom 10% of positive freqs; high-freq = top 50%.
                n_pos  = n_bins_half - 1          # positive-frequency bins
                n_lo   = max(1, n_pos ÷ 10)
                n_hi   = max(1, n_pos ÷ 2)
                # Skip DC (bin 1) in the power sums.
                power_lo  = sum(psd_avg[2:1+n_lo])
                power_hi  = sum(psd_avg[(n_bins_half - n_hi + 1):end])
                power_lo_s = sum(psd_shuf_avg[2:1+n_lo])
                power_hi_s = sum(psd_shuf_avg[(n_bins_half - n_hi + 1):end])

                lo_lift = power_lo / max(1e-30, power_lo_s)
                hi_lift = power_hi / max(1e-30, power_hi_s)

                flag_psd = lo_lift > 2.0 ? " ← LOW-FREQ EXCESS (long-range order)" :
                           lo_lift < 0.5 ? " ← LOW-FREQ DEFICIT" :
                                           " (≈ flat / random)"
                @printf("      windows used         : %d  (win_len=%d, bins=%d)\n",
                        n_wins_used, win_len, n_bins_half)
                @printf("      low-freq power lift  : %.3f%s\n", lo_lift, flag_psd)
                @printf("      high-freq power lift : %.3f\n", hi_lift)

                # Print bins 2..n_show+1 (positive-frequency, skipping DC at bin 1).
                n_show = min(8, n_bins_half - 1)
                @printf("      bin (freq×win_len):  %s\n",
                        join([@sprintf("%6d", k) for k in 1:n_show], " "))
                @printf("      PSD real:            %s\n",
                        join([@sprintf("%6.1f", psd_avg[k+1]) for k in 1:n_show], " "))
                @printf("      PSD shuffled:        %s\n",
                        join([@sprintf("%6.1f", psd_shuf_avg[k+1]) for k in 1:n_show], " "))
                @printf("      ratio real/shuf:     %s\n",
                        join([@sprintf("%6.2f", psd_avg[k+1] / max(1e-30, psd_shuf_avg[k+1]))
                              for k in 1:n_show], " "))
            else
                @printf("      (too few windowed hits for Welch PSD)\n")
            end
        else
            @printf("      (need ≥8 hits for Welch PSD)\n")
        end
        println()

        # ---- Spectral 2: windowed spectrogram (rolling 4-slice) -----------------
        # Divide arrivals into 4 equal chronological slices; compute per-slice
        # mean gap and hit density.  Reveals regime switching / intermittency
        # that global PSD averages away.
        @printf("    Spectrogram (4-slice chronological):\n")
        if length(arrivals) >= 16
            n_slices  = 4
            slice_len = length(arrivals) ÷ n_slices
            @printf("      slice  hits   span_steps   density(hits/kstep)   mean_gap  cv_gap\n")
            for si in 1:n_slices
                i1 = (si - 1) * slice_len + 1
                i2 = si == n_slices ? length(arrivals) : si * slice_len
                sl_arr  = arrivals[i1:i2]
                sl_n    = length(sl_arr)
                sl_span = sl_arr[end] - sl_arr[1] + 1
                sl_density = 1000.0 * sl_n / max(1, sl_span)
                if sl_n >= 2
                    sl_gaps   = [sl_arr[j] - sl_arr[j-1] for j in 2:sl_n]
                    sl_mean   = sum(sl_gaps) / length(sl_gaps)
                    sl_var    = length(sl_gaps) > 1 ?
                                sum((g - sl_mean)^2 for g in sl_gaps) / (length(sl_gaps) - 1) :
                                0.0
                    sl_cv     = sqrt(sl_var) / max(1.0, sl_mean)
                    @printf("      %5d  %4d  %11d   %19.3f   %8.1f  %.3f\n",
                            si, sl_n, sl_span, sl_density, sl_mean, sl_cv)
                else
                    @printf("      %5d  %4d  %11d   (insufficient)\n", si, sl_n, sl_span)
                end
            end
            # Flag if density varies > 2× between any two slices.
            densities = Float64[]
            for si in 1:n_slices
                i1 = (si - 1) * slice_len + 1
                i2 = si == n_slices ? length(arrivals) : si * slice_len
                sl_arr = arrivals[i1:i2]
                sl_n   = length(sl_arr)
                sl_span = sl_arr[end] - sl_arr[1] + 1
                push!(densities, sl_n / max(1, sl_span))
            end
            d_max = maximum(densities); d_min = minimum(densities)
            ratio_sg = d_max / max(1e-30, d_min)
            flag_sg  = ratio_sg > 2.0 ? " ← REGIME SWITCHING (density varies ×$(round(ratio_sg, digits=1)))" :
                                         " (density stable across slices)"
            @printf("      max/min slice density  : %.2f×%s\n", ratio_sg, flag_sg)
        else
            @printf("      (need ≥16 hits for spectrogram)\n")
        end
        println()

        # ---- Spectral 4: Allan factor (variance scaling with window size) -------
        # F(T) = Var(N_T) / E[N_T] where N_T = hit count in window of T steps.
        # Poisson → F(T) ≈ 1 for all T.
        # Clustered (long-memory) → F(T) grows with T.
        # Compared against shuffled-gap null to isolate the signal.
        @printf("    Allan factor F(T) = Var(N_T)/E[N_T]:\n")
        if length(arrivals) >= 8
            total_span_af = arrivals[end] - arrivals[1] + 1
            # Choose window sizes as geometric progression from ~10 to total_span/4.
            min_T  = max(10, total_span_af ÷ 1000)
            max_T  = total_span_af ÷ 4
            af_windows = Int[]
            if min_T < max_T
                T = min_T
                while T <= max_T
                    push!(af_windows, T)
                    T = max(T + 1, round(Int, T * 2.5))
                end
            end
            if isempty(af_windows)
                push!(af_windows, max(10, total_span_af ÷ 8))
            end

            function allan_factor(arr::Vector{Int}, T::Int, span::Int)
                # Partition [arr[1], arr[1]+span) into windows of T steps.
                n_windows = max(1, span ÷ T)
                counts = zeros(Int, n_windows)
                t0 = arr[1]
                for a in arr
                    wi = min(n_windows, (a - t0) ÷ T + 1)
                    counts[wi] += 1
                end
                mn = sum(counts) / n_windows
                vr = n_windows > 1 ?
                     sum((c - mn)^2 for c in counts) / (n_windows - 1) : 0.0
                return vr / max(1e-30, mn), mn
            end

            # Shuffled null for Allan factor — one RNG per iteration slot.
            n_af_shuf    = 10
            af_rngs      = [MersenneTwister(rand(UInt64)) for _ in 1:n_af_shuf]
            null_arrs_af = [similar(arrivals) for _ in 1:n_af_shuf]
            Threads.@threads for si in 1:n_af_shuf
                sg    = copy(gaps)
                rng_a = af_rngs[si]
                for k in length(sg):-1:2
                    j2 = rand(rng_a, 1:k)
                    sg[k], sg[j2] = sg[j2], sg[k]
                end
                na = null_arrs_af[si]
                na[1] = arrivals[1]
                for k in 2:length(arrivals)
                    na[k] = na[k-1] + sg[k-1]
                end
                sort!(na)
            end

            @printf("      T_steps    F(T)_real   F(T)_null   lift   interpretation\n")
            # Parallel over window sizes: each T is independent.
            n_af_T       = length(af_windows)
            results_af   = Vector{NTuple{4,Float64}}(undef, n_af_T)  # (T, f_real, f_null, lift)
            Threads.@threads for ti in 1:n_af_T
                T      = af_windows[ti]
                f_real, _ = allan_factor(arrivals, T, total_span_af)
                f_null_sum = 0.0
                for si in 1:n_af_shuf
                    fn, _ = allan_factor(null_arrs_af[si], T, total_span_af)
                    f_null_sum += fn
                end
                f_null = f_null_sum / n_af_shuf
                lift   = f_real / max(1e-30, f_null)
                results_af[ti] = (Float64(T), f_real, f_null, lift)
            end
            for (T_f, f_real, f_null, lift_af) in results_af
                flag_af = lift_af > 2.0 ? " CLUSTERED" :
                          lift_af < 0.5 ? " ANTI-CLUST" :
                                          " ≈Poisson"
                @printf("      %9d  %11.3f  %10.3f  %6.2f  %s\n",
                        round(Int, T_f), f_real, f_null, lift_af, flag_af)
            end
            println()

            # Slope of log F(T) vs log T (Hurst-like exponent estimate).
            if length(af_windows) >= 3
                log_T = [log(Float64(T)) for T in af_windows]
                log_F = [log(max(1e-30, r[2])) for r in results_af]
                n_pts = length(log_T)
                mx = sum(log_T) / n_pts; my = sum(log_F) / n_pts
                slope_num = sum((log_T[i] - mx) * (log_F[i] - my) for i in 1:n_pts)
                slope_den = sum((log_T[i] - mx)^2 for i in 1:n_pts)
                hurst_slope = slope_den > 0.0 ? slope_num / slope_den : 0.0
                flag_hurst = hurst_slope > 0.3  ? " ← LONG-MEMORY (H>0.5 analog)" :
                             hurst_slope < -0.1 ? " ← ANTI-PERSISTENT" :
                                                   " (≈ Poisson, uncorrelated)"
                @printf("      Allan log-log slope (Hurst proxy): %.3f%s\n",
                        hurst_slope, flag_hurst)
            end
        else
            @printf("      (need ≥8 hits for Allan factor)\n")
        end
        println()

        # ════════════════════════════════════════════════════════════════════
        # New 1 — Autocorrelation of hit-density over coarse bins
        # ════════════════════════════════════════════════════════════════════
        # Bin arrivals into windows of sizes T ∈ {10⁴, 2·10⁴, …} and compute
        # normalised lag-k autocorrelations of the count series N_T[w].
        # Poisson → ACF ≈ 0 at all lags.  Positive ACF → persistent hot/cold
        # epochs; negative → alternating (anti-persistence).
        # Parallel over bin-size values; each is independent.
        @printf("    Density autocorrelation (ACF of coarse hit-count series):\n")
        if length(arrivals) >= 16
            total_span_acf = arrivals[end] - arrivals[1] + 1
            # Choose 4 bin sizes geometrically; need ≥20 bins each.
            acf_bin_sizes = Int[]
            T_try = max(100, total_span_acf ÷ 200)
            while T_try <= total_span_acf ÷ 20 && length(acf_bin_sizes) < 5
                push!(acf_bin_sizes, T_try)
                T_try = max(T_try + 1, round(Int, T_try * 2.0))
            end

            # Per bin-size result: (T, n_bins, acf_lag1, acf_lag2, acf_lag3, flag)
            acf_results = Vector{Any}(undef, length(acf_bin_sizes))
            Threads.@threads for ti in 1:length(acf_bin_sizes)
                T       = acf_bin_sizes[ti]
                n_bins  = total_span_acf ÷ T
                n_bins < 8 && (acf_results[ti] = (T, n_bins, NaN, NaN, NaN); continue)
                counts  = zeros(Float64, n_bins)
                t0      = arrivals[1]
                for a in arrivals
                    wi = min(n_bins, (a - t0) ÷ T + 1)
                    counts[wi] += 1.0
                end
                mn   = sum(counts) / n_bins
                var0 = sum((c - mn)^2 for c in counts) / n_bins
                if var0 < 1e-30
                    acf_results[ti] = (T, n_bins, 0.0, 0.0, 0.0)
                    continue
                end
                # ACF at lags 1, 2, 3.
                acf = ntuple(lag -> begin
                    cov = sum((counts[w] - mn) * (counts[w + lag] - mn)
                              for w in 1:(n_bins - lag)) / (n_bins - lag)
                    cov / var0
                end, 3)
                acf_results[ti] = (T, n_bins, acf[1], acf[2], acf[3])
            end

            @printf("      T_steps  n_bins   ACF(1)   ACF(2)   ACF(3)   interpretation\n")
            for r in acf_results
                T, nb_r = r[1], r[2]
                if isnan(r[3])
                    @printf("      %7d  %6d   (too few bins)\n", T, nb_r)
                    continue
                end
                a1, a2, a3 = r[3], r[4], r[5]
                flag_acf = abs(a1) > 0.15 ?
                           (a1 > 0 ? " ← PERSISTENT (hot/cold epochs)" :
                                     " ← ANTI-PERSISTENT (alternating)") :
                           " (≈ uncorrelated)"
                @printf("      %7d  %6d   %+6.3f   %+6.3f   %+6.3f  %s\n",
                        T, nb_r, a1, a2, a3, flag_acf)
            end
        else
            @printf("      (need ≥16 hits for ACF)\n")
        end
        println()

        # ════════════════════════════════════════════════════════════════════
        # New 2 — Hot/cold window conditioning
        # ════════════════════════════════════════════════════════════════════
        # Classify each fixed-width window as "hot" (hit density ≥ median) or
        # "cold" (< median).  Then compare the *next* window's closure rate
        # (hit count) conditioned on the current window's class.
        # Hot→hot persistence means the walk has memory: a burst now predicts
        # a burst soon.  Reported as lift = E[N_{t+1}|hot] / E[N_{t+1}|cold].
        @printf("    Hot/cold window conditioning (burst memory):\n")
        if length(arrivals) >= 20
            total_span_hc = arrivals[end] - arrivals[1] + 1
            T_hc          = max(100, total_span_hc ÷ 50)   # ~50 windows
            n_wins_hc     = total_span_hc ÷ T_hc
            if n_wins_hc >= 10
                counts_hc = zeros(Int, n_wins_hc)
                t0_hc     = arrivals[1]
                for a in arrivals
                    wi = min(n_wins_hc, (a - t0_hc) ÷ T_hc + 1)
                    counts_hc[wi] += 1
                end
                # Median threshold.
                sorted_c = sort(counts_hc)
                median_c = length(sorted_c) % 2 == 0 ?
                           (sorted_c[length(sorted_c)÷2] + sorted_c[length(sorted_c)÷2 + 1]) / 2.0 :
                           Float64(sorted_c[(length(sorted_c)+1)÷2])
                # For each window w, record next-window count conditioned on hot/cold.
                hot_next = Int[]; cold_next = Int[]
                for w in 1:(n_wins_hc - 1)
                    if counts_hc[w] >= median_c
                        push!(hot_next,  counts_hc[w + 1])
                    else
                        push!(cold_next, counts_hc[w + 1])
                    end
                end
                n_hot  = length(hot_next);  n_cold = length(cold_next)
                mu_hot  = n_hot  > 0 ? sum(hot_next)  / n_hot  : 0.0
                mu_cold = n_cold > 0 ? sum(cold_next) / n_cold : 0.0
                lift_hc = mu_hot / max(1e-9, mu_cold)
                flag_hc = lift_hc > 1.3 ? " ← MEMORY: hot predicts hot" :
                          lift_hc < 0.77 ? " ← ANTI-MEMORY: hot predicts cold" :
                                           " (no burst memory)"
                @printf("      window T       : %d steps (%d windows)\n", T_hc, n_wins_hc)
                @printf("      density median : %.2f hits/window\n", median_c)
                @printf("      hot windows    : %d  →  next mean = %.3f hits\n", n_hot, mu_hot)
                @printf("      cold windows   : %d  →  next mean = %.3f hits\n", n_cold, mu_cold)
                @printf("      lift hot/cold  : %.3f%s\n", lift_hc, flag_hc)

                # Also compute 2-step: hot window now → hot window in 2 steps.
                if n_wins_hc >= 12
                    hot2_next = Int[]; cold2_next = Int[]
                    for w in 1:(n_wins_hc - 2)
                        if counts_hc[w] >= median_c
                            push!(hot2_next,  counts_hc[w + 2])
                        else
                            push!(cold2_next, counts_hc[w + 2])
                        end
                    end
                    mu_hot2  = length(hot2_next)  > 0 ? sum(hot2_next)  / length(hot2_next)  : 0.0
                    mu_cold2 = length(cold2_next) > 0 ? sum(cold2_next) / length(cold2_next) : 0.0
                    lift2    = mu_hot2 / max(1e-9, mu_cold2)
                    @printf("      lag-2 lift     : %.3f  (memory decay %s)\n",
                            lift2, lift2 > 1.0 ? "persists" : "gone")
                end
            else
                @printf("      (need ≥10 windows; got %d with T=%d)\n", n_wins_hc, T_hc)
            end
        else
            @printf("      (need ≥20 hits)\n")
        end
        println()

        # ════════════════════════════════════════════════════════════════════
        # New 3 — State-space a-region hotness (dynamic bias)
        # ════════════════════════════════════════════════════════════════════
        # Compare lp1_conj_a_hist (emissions per a-bucket) against split_hist
        # (visits per a-bucket) to find dynamically hot a-regions.
        # lift[bucket] = (emissions/total_emissions) / (visits/total_visits).
        # lift >> 1 means that bucket produces LP1-conj hits at higher-than-
        # expected rate given how often it is visited — dynamic bias even when
        # the global a-distribution looks uniform.
        @printf("    State-space a-region hotness (dynamic vs static bias):\n")
        lc_hist   = stat.lp1_conj_a_hist
        vis_hist  = stat.split_hist   # visits = split steps (where LP can fire)
        n_lc_tot  = sum(lc_hist)
        n_vis_tot = sum(vis_hist)
        if n_lc_tot >= 10 && n_vis_tot >= 10
            # Per-bucket lift, clipped to avoid divide-by-zero.
            lifts = [
                (lc_hist[i] / max(1e-30, Float64(n_lc_tot))) /
                (vis_hist[i] / max(1e-30, Float64(n_vis_tot)))
                for i in eachindex(lc_hist)
            ]
            # Sort and report top-5 and bottom-5.
            order = sortperm(lifts, rev=true)
            @printf("      total LP1-conj emissions : %d  total split visits: %d\n",
                    n_lc_tot, n_vis_tot)
            @printf("      TOP-5 hot a-buckets (lift = emission_rate / visit_rate):\n")
            for rank in 1:min(5, length(order))
                bi = order[rank]
                frac_str = p > 0 ? @sprintf(" [a∈[%d,%d))", (bi-1)*p÷nb, bi*p÷nb) : ""
                @printf("        bucket %4d%s  lift=%.3f  emissions=%d  visits=%d\n",
                        bi, frac_str, lifts[bi], lc_hist[bi], vis_hist[bi])
            end
            @printf("      BOTTOM-5 cold a-buckets:\n")
            for rank in max(1,length(order)-4):length(order)
                bi = order[rank]
                frac_str = p > 0 ? @sprintf(" [a∈[%d,%d))", (bi-1)*p÷nb, bi*p÷nb) : ""
                @printf("        bucket %4d%s  lift=%.3f  emissions=%d  visits=%d\n",
                        bi, frac_str, lifts[bi], lc_hist[bi], vis_hist[bi])
            end
            # χ² test: are emissions distributed proportional to visits?
            expected_lc = [vis_hist[i] * Float64(n_lc_tot) / max(1.0, Float64(n_vis_tot))
                           for i in eachindex(vis_hist)]
            chi2_lc = sum((lc_hist[i] - expected_lc[i])^2 / max(1.0, expected_lc[i])
                          for i in eachindex(lc_hist))
            dof_lc  = length(lc_hist) - 1
            ratio_lc = chi2_lc / max(1.0, Float64(dof_lc))
            flag_lc  = ratio_lc > 2.0 ? " ← DYNAMIC BIAS (some a-regions systematically hotter)" :
                                          " (emissions proportional to visits)"
            @printf("      χ²/dof (emissions vs visits): %.3f%s\n", ratio_lc, flag_lc)
        else
            @printf("      (need ≥10 LP1-conj emissions; got %d)\n", n_lc_tot)
        end
        println()

        # ════════════════════════════════════════════════════════════════════
        # New 4 — Multitaper PSD + spectral slope (1/fᵅ test)
        # ════════════════════════════════════════════════════════════════════
        # Uses K=4 DPSS-like tapers (approximated by cosine tapers of orders
        # 1..K) for reduced variance at low frequencies.  Reports spectral
        # slope α from log-log OLS fit to avoid Welch bias at very low freqs.
        # All tapers computed in parallel (each is an independent DFT).
        @printf("    Multitaper PSD + spectral slope (1/fᵅ):\n")
        if length(arrivals) >= 16
            total_span_mt = arrivals[end] - arrivals[1] + 1
            n_mt_bins = min(512, max(32, length(arrivals) * 2))
            # Bin hits into n_mt_bins equal-width time buckets.
            mt_counts = zeros(Float64, n_mt_bins)
            t0_mt     = arrivals[1]
            bin_width = max(1, total_span_mt ÷ n_mt_bins)
            for a in arrivals
                bi = min(n_mt_bins, (a - t0_mt) ÷ bin_width + 1)
                mt_counts[bi] += 1.0
            end
            # Subtract mean.
            mt_mean    = sum(mt_counts) / n_mt_bins
            mt_centred = mt_counts .- mt_mean
            n_bins_half_mt = n_mt_bins ÷ 2

            # K cosine tapers: w_k[j] = sqrt(2/(N+1)) * sin(k*π*j/(N+1)), k=1..K
            K_tapers = 4
            # Precompute FFTW plan for this signal length — shared across taper threads.
            _mt_tmp  = zeros(Float64, n_mt_bins)
            mt_plan  = plan_rfft(_mt_tmp)
            n_bins_half_mt = n_mt_bins ÷ 2 + 1   # rfft output length
            mt_psd_slots = [zeros(Float64, n_bins_half_mt) for _ in 1:K_tapers]
            Threads.@threads for k in 1:K_tapers
                taper = [sqrt(2.0 / (n_mt_bins + 1)) *
                         sin(k * π * j / (n_mt_bins + 1))
                         for j in 1:n_mt_bins]
                xw    = mt_centred .* taper
                # rfft: O(n log n) instead of O(n²)
                F     = mt_plan * xw
                mt_psd_slots[k] = abs2.(F)
            end
            mt_psd = reduce(.+, mt_psd_slots) ./ K_tapers

            # Spectral slope: OLS log(PSD) ~ α·log(freq) over low 20% of freqs.
            n_fit = max(4, n_bins_half_mt ÷ 5)
            log_f = [log(Float64(k)) for k in 1:n_fit]
            log_p = [log(max(1e-30, mt_psd[k])) for k in 1:n_fit]
            mf = sum(log_f) / n_fit; mp = sum(log_p) / n_fit
            slope_num_mt = sum((log_f[i] - mf) * (log_p[i] - mp) for i in 1:n_fit)
            slope_den_mt = sum((log_f[i] - mf)^2 for i in 1:n_fit)
            alpha_mt     = slope_den_mt > 0 ? -slope_num_mt / slope_den_mt : 0.0
            # α > 0 means power decreases with freq → red/1/fᵅ noise.
            flag_alpha = alpha_mt > 1.5  ? " ← STRONG 1/fᵅ (α≈$(round(alpha_mt,digits=2)), long-memory)" :
                         alpha_mt > 0.5  ? " ← MILD 1/fᵅ (sub-Brownian memory)" :
                         alpha_mt < -0.3 ? " ← BLUE NOISE (anti-persistent)" :
                                           " (≈ white noise, α≈0)"
            @printf("      bins=%d  tapers=%d  fit_bins=%d\n", n_mt_bins, K_tapers, n_fit)
            @printf("      spectral slope α : %.3f%s\n", alpha_mt, flag_alpha)

            # Show first 8 multitaper PSD bins vs Welch (already computed above
            # if available — just show MT here standalone).
            n_show_mt = min(8, n_bins_half_mt)
            @printf("      freq bin:   %s\n",
                    join([@sprintf("%8d", k) for k in 1:n_show_mt], " "))
            @printf("      MT PSD:     %s\n",
                    join([@sprintf("%8.2f", mt_psd[k]) for k in 1:n_show_mt], " "))
        else
            @printf("      (need ≥16 hits for multitaper PSD)\n")
        end
        println()

        # ════════════════════════════════════════════════════════════════════
        # New 5 — Gap-distribution characterisation (replaces unstable MMPP fit)
        # ════════════════════════════════════════════════════════════════════
        # The symmetric MMPP-2 method-of-moments fit is numerically unstable
        # when the Fano factor is large: it produces negative transition rates
        # (q < 0) and epoch durations of ~10^30 steps — physically meaningless.
        # We replace it with three robust, interpretable diagnostics:
        #
        #   (a) Burst-size distribution: how many hits arrive in bursts of 1/2/3+?
        #       A burst is a run of hits with inter-arrival < burst_sep steps.
        #       Geometric burst sizes → Poisson; heavy tail → clustering.
        #
        #   (b) Hot-window persistence (gap-conditioned tail):
        #       Fraction of gaps that are "short" (< μ/2) vs "long" (> 2μ).
        #       For a Poisson process P(gap < μ/2) ≈ 1 - e^{-0.5} ≈ 0.39 and
        #       P(gap > 2μ) ≈ e^{-2} ≈ 0.135.  Excess short-gap fraction means
        #       bursts; excess long-gap fraction means cold epochs between bursts.
        #
        #   (c) Geometric vs heavy-tail gap test (KS vs Exponential):
        #       Rescale gaps by their mean → unit-mean Exponential(1) null.
        #       KS statistic > 0.1 flags a non-Poisson gap distribution.
        #       A right-skewed empirical CDF (excess large gaps) is the
        #       signature of a bursty / heavy-tailed process.
        @printf("    Gap distribution (burst / persistence / tail):\n")
        if length(arrivals) >= 10
            n_g      = length(gaps)
            mu_g     = mean_gap
            var_g    = var_gap

            # Lag-1 ACF of gaps (retain for summary line).
            rho1 = 0.0
            if n_g >= 4
                rho1_num = sum((gaps[i] - mu_g) * (gaps[i+1] - mu_g) for i in 1:(n_g-1))
                rho1_den = sum((g - mu_g)^2 for g in gaps)
                rho1     = rho1_den > 0.0 ? rho1_num / rho1_den : 0.0
            end
            @printf("      Observed gap stats: μ=%.1f  σ²=%.1f  Fano=%.3f  ρ₁=%+.4f\n",
                    mu_g, var_g, fano, rho1)

            # (a) Burst-size distribution.
            # Define burst separator as max(1, floor(μ/3)).
            burst_sep    = max(1, floor(Int, mu_g / 3.0))
            burst_sizes  = Int[]
            cur_burst    = 1
            for k in 1:(n_g)
                if k <= n_g && gaps[k] <= burst_sep
                    cur_burst += 1
                else
                    push!(burst_sizes, cur_burst)
                    cur_burst = 1
                end
            end
            push!(burst_sizes, cur_burst)  # last burst
            n_bursts = length(burst_sizes)
            cnt1 = count(==(1), burst_sizes)
            cnt2 = count(==(2), burst_sizes)
            cnt3p = count(>=(3), burst_sizes)
            mean_burst = n_bursts > 0 ? sum(burst_sizes) / n_bursts : 0.0
            max_burst  = n_bursts > 0 ? maximum(burst_sizes) : 0
            # Geometric(p) burst sizes: P(size=k) = (1-p)^{k-1}·p.
            # Mean = 1/p, so p = 1/mean_burst.
            p_geo = n_bursts > 0 && mean_burst > 1.0 ? 1.0 / mean_burst : 1.0
            # KS vs Geometric CDF for burst sizes.
            bsorted = sort(burst_sizes)
            ks_b = 0.0; cumul_b = 0.0
            for bs in bsorted
                cumul_b += 1.0 / n_bursts
                geo_cdf_b = 1.0 - (1.0 - p_geo)^bs
                ks_b = max(ks_b, abs(cumul_b - geo_cdf_b))
            end
            flag_burst = ks_b > 0.1 ? " ← NON-GEOMETRIC (heavy-tail bursts)" :
                                       " (consistent with geometric)"
            @printf("      (a) Burst-size distribution (sep=%.0f steps):\n", Float64(burst_sep))
            @printf("          n_bursts=%d  mean=%.2f  max=%d\n", n_bursts, mean_burst, max_burst)
            @printf("          size=1: %d (%.1f%%)  size=2: %d (%.1f%%)  size≥3: %d (%.1f%%)\n",
                    cnt1, 100.0*cnt1/max(1,n_bursts),
                    cnt2, 100.0*cnt2/max(1,n_bursts),
                    cnt3p, 100.0*cnt3p/max(1,n_bursts))
            @printf("          KS vs Geometric(1/mean)=%.4f%s\n", ks_b, flag_burst)

            # (b) Short/long gap fractions vs Poisson prediction.
            n_short = count(g -> g < mu_g / 2.0, gaps)
            n_long  = count(g -> g > 2.0 * mu_g, gaps)
            f_short = n_short / n_g
            f_long  = n_long  / n_g
            # Poisson(rate 1/μ) predictions:
            poisson_short = 1.0 - exp(-0.5)   # ≈ 0.394
            poisson_long  = exp(-2.0)          # ≈ 0.135
            flag_pers = if f_short > poisson_short * 1.3 || f_long > poisson_long * 1.5
                " ← HOT/COLD PERSISTENCE (excess short+long gaps)"
            elseif f_short < poisson_short * 0.7
                " ← ANTI-PERSISTENT (gaps more uniform than Poisson)"
            else
                " (consistent with Poisson persistence)"
            end
            @printf("      (b) Hot/cold persistence:\n")
            @printf("          short (< μ/2): %.1f%%  [Poisson expect %.1f%%]\n",
                    100.0*f_short, 100.0*poisson_short)
            @printf("          long  (> 2μ) : %.1f%%  [Poisson expect %.1f%%]%s\n",
                    100.0*f_long, 100.0*poisson_long, flag_pers)

            # (c) KS test of rescaled gaps vs Exponential(1).
            rescaled = sort(gaps ./ max(1.0, mu_g))
            ks_exp   = 0.0
            for (k, rg) in enumerate(rescaled)
                emp_cdf = k / n_g
                exp_cdf = 1.0 - exp(-rg)
                ks_exp  = max(ks_exp, abs(emp_cdf - exp_cdf))
            end
            # Right-skew: top 5% of gaps vs Exponential prediction.
            top5_thresh = -log(0.05)   # Exp(1) quantile at 95% ≈ 3.0
            n_top5 = count(g -> g / mu_g > top5_thresh, gaps)
            expected_top5 = round(Int, 0.05 * n_g)
            flag_tail = if n_top5 > 2 * expected_top5
                @sprintf(" ← HEAVY RIGHT TAIL (%d gaps > 3μ, expected %d)", n_top5, expected_top5)
            elseif ks_exp > 0.1
                " ← NON-EXPONENTIAL gap distribution"
            else
                " (consistent with Exponential / Poisson)"
            end
            @printf("      (c) Gap tail test (KS vs Exponential):\n")
            @printf("          KS=%.4f  gaps>3μ: %d (expected %d)%s\n",
                    ks_exp, n_top5, expected_top5, flag_tail)
        else
            @printf("      (need ≥10 hits for gap analysis)\n")
        end
        println()

        # ════════════════════════════════════════════════════════════════════
        # New 6 — Hazard function: P(hit | time since last hit = τ)
        # ════════════════════════════════════════════════════════════════════
        # For a Poisson process the hazard is flat (memoryless).
        # If there is a sticky metastable basin, the hazard should be ELEVATED
        # shortly after a hit and decay to baseline on the decorrelation timescale.
        # We estimate h(τ) = (hits with gap ≤ τ+Δτ) / (gaps in (τ, τ+Δτ])
        # over a geometric grid of τ values.
        # Key question: does excess hazard survive beyond ~mean_gap?
        #   If yes  → genuine metastable basin (sticky attractor).
        #   If no   → burst is just correlated arrival times (slow drift).
        @printf("    Hazard function h(τ) vs Poisson baseline:\n")
        if n_gaps >= 20
            sorted_gaps_haz = sort(gaps)
            # Build geometric grid up to ≈5×mean_gap
            τ_max = round(Int, 5.0 * mean_gap)
            τ_grid = Int[]
            τ = max(1, round(Int, mean_gap / 16.0))
            while τ <= τ_max
                push!(τ_grid, τ)
                τ = max(τ+1, round(Int, τ * 1.7))
            end
            poisson_baseline_haz = 1.0 / max(1.0, mean_gap)
            @printf("      (Poisson baseline rate λ=1/μ = %.5f)\n", poisson_baseline_haz)
            @printf("      tau_steps    h(tau)    Poisson_h   lift_h   interp\n")
            prev_τ = 0
            decor_τ = -1
            for τ in τ_grid
                Δτ = τ - prev_τ
                n_in_band = searchsortedlast(sorted_gaps_haz, τ) -
                            searchsortedlast(sorted_gaps_haz, prev_τ)
                h_obs  = n_in_band / max(1, n_gaps * Δτ)
                h_poi  = poisson_baseline_haz
                lift_h = h_obs / max(1e-30, h_poi)
                flag_h = lift_h > 2.0 ? " HOT" :
                         lift_h > 1.3 ? " warm" :
                         lift_h < 0.7 ? " cold" : ""
                @printf("      %8d  %8.5f  %10.5f  %6.3f  %s\n",
                        τ, h_obs, h_poi, lift_h, flag_h)
                if decor_τ < 0 && lift_h < 1.3 && τ > round(Int, mean_gap/4.0)
                    decor_τ = τ
                end
                prev_τ = τ
            end
            if decor_τ > 0
                @printf("      -> decorr tau* ~= %d steps  (lift first < 1.3)\n", decor_τ)
                @printf("         decay ratio tau*/mu = %.2f  (>1 -> basin persists past mean inter-arrival)\n",
                        decor_τ / max(1.0, mean_gap))
            else
                @printf("      -> hazard elevated through tau_max=%d (strong stickiness)\n", τ_max)
            end
        else
            @printf("      (need >=20 gaps for hazard estimate)\n")
        end
        println()
        # New 7 — CIR decorrelation length (extract from existing CIR table)
        # ════════════════════════════════════════════════════════════════════
        # We already computed CIR(W) for a grid of W values above, but we don't
        # store the results in a variable for later use.  Here we re-derive the
        # decorrelation scale directly from the gap series using a fast estimator:
        #   R(lag) = ACF of the binary hit-indicator series at the raw-step level.
        # We bin at window_size = max(10, mean_gap/4) and find the first lag
        # where the ACF of the *gap* series drops below 1/e.
        @printf("    CIR decorrelation length from gap ACF:\n")
        if n_gaps >= 20
            max_lag_g = min(20, n_gaps ÷ 2)
            gap_acf   = zeros(Float64, max_lag_g)
            var_g_loc = n_gaps > 1 ?
                sum((g - mean_gap)^2 for g in gaps) / (n_gaps - 1) : 0.0
            if var_g_loc > 0.0
                for lag in 1:max_lag_g
                    cov = sum((gaps[i] - mean_gap) * (gaps[i+lag] - mean_gap)
                              for i in 1:(n_gaps - lag)) / (n_gaps - lag)
                    gap_acf[lag] = cov / var_g_loc
                end
                inv_e = exp(-1.0)
                decor_lag = findfirst(r -> r < inv_e, gap_acf)
                acf_str = join([@sprintf("%+.3f", gap_acf[k]) for k in 1:min(8, max_lag_g)], "  ")
                @printf("      gap ACF lags 1..%d: %s\n", min(8, max_lag_g), acf_str)
                if decor_lag !== nothing
                    @printf("      decorr lag: %d gaps  (ACF first < 1/e=%.3f)\n",
                            decor_lag, inv_e)
                    @printf("      in step-units: ~= %d steps\n",
                            round(Int, decor_lag * mean_gap))
                else
                    @printf("      ACF does not decay below 1/e within %d lags -- very long memory\n",
                            max_lag_g)
                end
            else
                @printf("      (gap variance zero -- degenerate walk)\n")
            end
        else
            @printf("      (need >=20 gaps for gap ACF)\n")
        end
        println()
        # For each hit i, look at hits within W_fp steps and count what fraction
        # share the same lp_key.  Compare to the global key collision rate
        # (expected under random key assignment).
        if !isempty(lp_keys) && length(lp_keys) == n_hits
            W_fp         = 2000         # fingerprint window — matches mid-range CIR lag
            fp_pairs     = 0           # pairs within window
            fp_same_key  = 0           # of those, pairs with matching key
            for i in 1:n_hits
                hi = searchsortedlast(arrivals, arrivals[i] + W_fp)
                for j in (i+1):hi
                    fp_pairs += 1
                    if lp_keys[j] == lp_keys[i]
                        fp_same_key += 1
                    end
                end
            end
            # Expected same-key rate under uniform random key assignment:
            # P(key_i == key_j) = Σ_k (count_k / N)² (birthday collision prob).
            key_counts   = Dict{UInt128,Int}()
            for k in lp_keys; key_counts[k] = get(key_counts, k, 0) + 1; end
            expected_frac = sum(Float64(v)^2 for v in values(key_counts)) /
                            Float64(n_hits)^2
            obs_frac      = fp_same_key / max(1, fp_pairs)
            key_lift      = obs_frac / max(1e-9, expected_frac)
            flag_key      = key_lift > 2.0 ? " ← FINGERPRINT: close hits share keys" :
                                              " (key sharing ≈ random)"
            @printf("    Key fingerprint (W=%d): %d pairs, %d same-key (%.2f%%), expected %.2f%%, lift=%.2f%s\n",
                    W_fp, fp_pairs, fp_same_key,
                    100.0 * obs_frac, 100.0 * expected_frac,
                    key_lift, flag_key)
        end
    else
        @printf("    LP1-conj hits    : %d  (need ≥4 for analysis)\n", length(arrivals))
    end
    println()

    # --- Seq 3: post-LP anchor bias (KS on a-histograms) ---
    @printf("  Seq 3 — Post-LP anchor a-histogram divergence:\n")
    n_post = sum(stat.post_lp_a_hist)
    n_base = sum(stat.baseline_a_hist)
    @printf("    post-LP steps    : %d\n", n_post)
    @printf("    baseline steps   : %d\n", n_base)
    if n_post >= 20 && n_base >= 20
        # KS statistic between the two normalised histograms.
        ks3 = 0.0
        cum_post = 0.0; cum_base = 0.0
        for i in eachindex(stat.post_lp_a_hist)
            cum_post += stat.post_lp_a_hist[i] / n_post
            cum_base += stat.baseline_a_hist[i] / n_base
            ks3 = max(ks3, abs(cum_post - cum_base))
        end
        flag3 = ks3 > 0.05 ? " ← DIVERGES (LP anchors bias a-dist)" :
                              " (consistent with uniform)"
        @printf("    KS(post vs base) : %.4f%s\n", ks3, flag3)
    else
        @printf("    (insufficient data for KS test)\n")
    end
    println()

    # ════════════════════════════════════════════════════════════════════════
    # α₂ SCALING DIAGNOSTICS  (α₂-1 through α₂-7)
    # ════════════════════════════════════════════════════════════════════════
    # All seven diagnostics run from lp1_conj_bucket_log (sorted by arrival time),
    # focusing exclusively on the LP1-conj key space.  The birthday block already
    # measures the same object via key collision statistics.
    #
    # Helper: compute Rényi-2 (collision) entropy and occupancy entropy from a
    # bucket count vector.  Returns (S2, S_occ, n_steps).
    #   S2    = -log2( Σ (cᵢ/n)² )   — collision entropy
    #   S_occ = -log2( #occupied / nb ) when uniform, or Shannon of occupancy
    #           We use the simpler effective-support: log2(#buckets_hit)
    # Both are in bits.  nb = number of buckets.
    function _bucket_entropies(counts::Vector{Int}, nb::Int)
        n = sum(counts)
        n == 0 && return (NaN, NaN, 0)
        p2sum = sum((counts[i] / n)^2 for i in 1:nb)
        S2    = p2sum > 0.0 ? -log2(p2sum) : NaN
        n_occ = count(>(0), counts)
        S_occ = n_occ > 0 ? log2(Float64(n_occ)) : 0.0
        return (S2, S_occ, n)
    end

    # ── α₂ sections: operate on the full LP1-conj partial key stream ────────────
    # blog = lp1_conj_key_blog: one UInt16 fp-bucket index per LP1-conj partial
    # (both stored and closed), populated by record_lp1_conj_partial! on every
    # call to handle_1lp_conj!.  nb = 2^±14 = 16384 fp-buckets, matching the
    # LSM’s Rényi granularity.  This is the quantity whose scaling exponent
    # α₂ governs the complexity of genus-2 IC via LP1-conj.
    blog   = stat.lp1_conj_key_blog   # Vector{UInt16}, 0-based bucket indices
    nb_a2  = 1 << _PHI_RENYI_BITS     # 16384 fp-buckets for α₂ diagnostics
    n_blog = length(blog)

    if n_blog < 32
        @printf("  α₂ scaling diagnostics (LP1-conj): need ≥32 LP1-conj emissions; got %d\n", n_blog)
    else

    # ── α₂-1: Time-resolved α₂(T) over dyadic windows ───────────────────────
    @printf("  α₂-1 — Time-resolved α₂(T) of LP1-conj a-bucket sequence:\n")
    @printf("    window_T   n_events   α₂(T)   S_occ(T)   ρ(T)=S_occ/S₂   dα₂/dlogT\n")
    # Build dyadic window sizes: T₀, 2T₀, 4T₀, … up to n_blog
    T0_a2 = max(16, n_blog ÷ 64)
    dyadic_windows = Int[]
    Tw = T0_a2
    while Tw <= n_blog
        push!(dyadic_windows, Tw)
        Tw *= 2
    end
    # For each window size, compute α₂(T) by sliding the window across the log
    # with stride = T (non-overlapping), averaging S₂ across windows.
    prev_a2  = NaN
    prev_logT = NaN
    da2_vals  = Float64[]
    a2_vals   = Float64[]
    logT_vals = Float64[]
    for T in dyadic_windows
        n_wins_a2 = n_blog ÷ T
        n_wins_a2 < 1 && continue
        s2_acc = 0.0; socc_acc = 0.0; n_valid = 0
        counts_T = zeros(Int, nb_a2)
        for wi in 0:(n_wins_a2 - 1)
            fill!(counts_T, 0)
            for k in (wi*T + 1):((wi+1)*T)
                counts_T[Int(blog[k]) + 1] += 1
            end
            (s2, socc, _) = _bucket_entropies(counts_T, nb_a2)
            if !isnan(s2)
                s2_acc += s2; socc_acc += socc; n_valid += 1
            end
        end
        n_valid == 0 && continue
        a2_T   = s2_acc   / n_valid
        socc_T = socc_acc / n_valid
        rho_T  = a2_T > 0.0 ? socc_T / a2_T : NaN
        logT   = log2(Float64(T))
        da2_dlogT = (!isnan(prev_a2) && !isnan(prev_logT) && logT > prev_logT) ?
                    (a2_T - prev_a2) / (logT - prev_logT) : NaN
        da_str  = isnan(da2_dlogT) ? "       —" : @sprintf("%+8.4f", da2_dlogT)
        rho_str = isnan(rho_T)     ? "        —" : @sprintf("%9.4f", rho_T)
        @printf("    %9d  %8d   %7.4f  %9.4f  %s  %s\n",
                T, n_wins_a2 * T, a2_T, socc_T, rho_str, da_str)
        push!(a2_vals, a2_T)
        push!(logT_vals, logT)
        push!(da2_vals, isnan(da2_dlogT) ? 0.0 : da2_dlogT)
        prev_a2 = a2_T; prev_logT = logT
    end
    # Classify the flow
    if length(da2_vals) >= 3
        da2_late = da2_vals[end]
        da2_early = da2_vals[2]
        a2_flag = if abs(da2_late) < 0.02
            "  → α₂ CONVERGED (single exponent, Case A)"
        elseif da2_early > 0.05 && abs(da2_late) < 0.05
            "  → α₂ CROSSOVER (two plateaus, Case B — burst then mixing)"
        elseif da2_late > 0.05
            "  → α₂ DRIFTING UPWARD (no fixed exponent, Case C)"
        else
            "  → α₂ trend inconclusive"
        end
        @printf("    %s\n", a2_flag)
    end
    println()

    # ── α₂-2: Intra vs inter-regime collision split ───────────────────────────
    @printf("  α₂-2 — Intra vs inter-regime collision split:\n")
    # Classify each LP1-conj emission as hot/cold by a sliding window over
    # lp1_conj_arrivals.  blog[i] is the a-bucket of the i-th emission in
    # chronological order; hot_mask[i] = true iff the surrounding arrival
    # density in the walk-step dimension exceeds the global median.
    # Simple density vector over fixed windows of n_blog ÷ 50 emissions.
    let
        T_rc   = max(8, n_blog ÷ 50)
        n_rc   = n_blog ÷ T_rc
        if n_rc >= 4
            # Count LP1-conj hits per window using lp1_conj_arrivals.
            # Map raw_steps to step-ordinal windows via the fraction
            # raw_step / total_span_approx * n_blog.
            arrivals_lc = stat.lp1_conj_arrivals
            total_span_lc = isempty(arrivals_lc) ? 0 :
                            arrivals_lc[end] - arrivals_lc[1] + 1
            lc_window_counts = zeros(Int, n_rc)
            if !isempty(arrivals_lc) && total_span_lc > 0
                for a in arrivals_lc
                    wi = clamp(round(Int, (a - arrivals_lc[1]) / total_span_lc * n_rc) + 1, 1, n_rc)
                    lc_window_counts[wi] += 1
                end
            else
                # No LP1-conj arrivals — use raw step density as proxy
                # (every window has equal density → all cold; diagnostics still run)
                fill!(lc_window_counts, 0)
            end
            sorted_lc = sort(lc_window_counts)
            median_lc = length(sorted_lc) % 2 == 0 ?
                (sorted_lc[length(sorted_lc)÷2] + sorted_lc[length(sorted_lc)÷2+1]) / 2.0 :
                Float64(sorted_lc[(length(sorted_lc)+1)÷2])
            # hot_mask[i] = true iff step i belongs to a hot window
            hot_mask = [lc_window_counts[clamp((i-1)÷T_rc + 1, 1, n_rc)] >= median_lc
                        for i in 1:n_blog]

            # Compute S₂ for four subsets of step pairs:
            # intra-hot, intra-cold, inter (hot-cold or cold-hot)
            counts_hot  = zeros(Int, nb_a2)
            counts_cold = zeros(Int, nb_a2)
            for i in 1:n_blog
                if hot_mask[i]
                    counts_hot[Int(blog[i]) + 1]  += 1
                else
                    counts_cold[Int(blog[i]) + 1] += 1
                end
            end
            n_hot_steps  = sum(counts_hot)
            n_cold_steps = sum(counts_cold)

            # Intra-collision entropy: S₂ computed within each regime
            (s2_hot,  socc_hot,  _) = _bucket_entropies(counts_hot,  nb_a2)
            (s2_cold, socc_cold, _) = _bucket_entropies(counts_cold, nb_a2)

            # Inter-collision entropy: use mixing formula
            # S₂^inter ≈ -log2( Σᵢ (n_hot[i]/n_hot) * (n_cold[i]/n_cold) )
            if n_hot_steps > 0 && n_cold_steps > 0
                cross = sum((counts_hot[i] / n_hot_steps) * (counts_cold[i] / n_cold_steps)
                            for i in 1:nb_a2)
                s2_inter = cross > 0.0 ? -log2(cross) : NaN
            else
                s2_inter = NaN
            end

            # Overall S₂ from combined counts (for reference)
            counts_all = counts_hot .+ counts_cold
            (s2_all, _, _) = _bucket_entropies(counts_all, nb_a2)

            @printf("    Regime split: T_window=%d, n_windows=%d, median_density=%.2f hits/window\n",
                    T_rc, n_rc, median_lc)
            @printf("    hot steps:  %d  α₂^hot  = %.4f  S_occ^hot  = %.4f\n",
                    n_hot_steps, s2_hot, socc_hot)
            @printf("    cold steps: %d  α₂^cold = %.4f  S_occ^cold = %.4f\n",
                    n_cold_steps, s2_cold, socc_cold)
            @printf("    inter-regime α₂: %.4f\n", isnan(s2_inter) ? -1.0 : s2_inter)
            @printf("    overall α₂:      %.4f\n", s2_all)
            if !isnan(s2_hot) && !isnan(s2_cold)
                delta_a2 = s2_hot - s2_cold
                flag_rc  = abs(delta_a2) > 0.05 ?
                    @sprintf("  ← Δα₂=%.4f, α₂ NOT invariant of walk kernel", delta_a2) :
                    "  (α₂ consistent across regimes)"
                @printf("    Δα₂ = α₂^hot − α₂^cold = %+.4f%s\n", delta_a2, flag_rc)
            end
        else
            @printf("    (need ≥4 regime windows; n_blog=%d too short)\n", n_blog)
        end
    end
    println()

    # ── α₂-3: Regime-conditioned α₂ (standalone summary) ─────────────────────
    # Already reported as part of α₂-2 above (Δα₂).  Print brief cross-ref.
    @printf("  α₂-3 — Regime-conditioned α₂: see Δα₂ in α₂-2 above.\n")
    println()

    # ── α₂-4: Collision autocorrelation C(τ) ─────────────────────────────────
    @printf("  α₂-4 — Collision autocorrelation C(τ) = E[cᵢ(t)·cᵢ(t+τ)]:\n")
    # Compute the autocorrelation of the squared-occupancy series:
    # at each time t, define x(t) = c_{blog[t]}(t) / n_T, i.e. the fractional
    # count of the occupied bucket in a sliding window.  For tractability we
    # use a coarse version: bin steps into windows of T_acf steps, compute the
    # vector of bucket counts, take the dot-product (collision count) of
    # adjacent windows, and compute its ACF.
    let
        T_acf   = max(8, n_blog ÷ 100)
        n_wins_acf = n_blog ÷ T_acf
        if n_wins_acf >= 16
            # Collision count per window: Σᵢ cᵢ² (unnormalised)
            coll_series = zeros(Float64, n_wins_acf)
            counts_w    = zeros(Int, nb_a2)
            for wi in 0:(n_wins_acf - 1)
                fill!(counts_w, 0)
                for k in (wi*T_acf + 1):((wi+1)*T_acf)
                    counts_w[Int(blog[k]) + 1] += 1
                end
                coll_series[wi+1] = Float64(sum(x^2 for x in counts_w))
            end
            mn_c  = sum(coll_series) / n_wins_acf
            var_c = n_wins_acf > 1 ?
                sum((x - mn_c)^2 for x in coll_series) / (n_wins_acf - 1) : 0.0
            max_lag_c4 = min(20, n_wins_acf ÷ 2)
            c_acf = zeros(Float64, max_lag_c4)
            if var_c > 0.0
                for lag in 1:max_lag_c4
                    cov = sum((coll_series[t] - mn_c) * (coll_series[t+lag] - mn_c)
                              for t in 1:(n_wins_acf - lag)) / (n_wins_acf - lag)
                    c_acf[lag] = cov / var_c
                end
            end
            acf_str = join([@sprintf("%+.3f", c_acf[k]) for k in 1:min(8, max_lag_c4)], "  ")
            @printf("    T_window=%d steps, %d windows\n", T_acf, n_wins_acf)
            @printf("    C(τ) lags 1..%d: %s\n", min(8, max_lag_c4), acf_str)
            # Classify decay
            inv_e_c = exp(-1.0)
            decor_c = findfirst(r -> abs(r) < inv_e_c, c_acf)
            if decor_c !== nothing
                @printf("    Decorr lag: %d windows ≈ %d steps\n",
                        decor_c, decor_c * T_acf)
            else
                @printf("    ACF does not decay below 1/e within %d lags — long-memory C(τ)\n",
                        max_lag_c4)
            end
            # Hurst proxy from log-log slope of |C(τ)|
            if max_lag_c4 >= 4
                lags_fit = [log(Float64(k)) for k in 1:max_lag_c4 if abs(c_acf[k]) > 1e-6]
                acf_fit  = [log(abs(c_acf[k])) for k in 1:max_lag_c4 if abs(c_acf[k]) > 1e-6]
                if length(lags_fit) >= 4
                    mlag = sum(lags_fit)/length(lags_fit); macf = sum(acf_fit)/length(acf_fit)
                    num_h = sum((lags_fit[i]-mlag)*(acf_fit[i]-macf) for i in eachindex(lags_fit))
                    den_h = sum((lags_fit[i]-mlag)^2 for i in eachindex(lags_fit))
                    slope_c4 = den_h > 0 ? num_h / den_h : 0.0
                    flag_c4  = slope_c4 > -0.5 ? "  ← POWER-LAW decay (α₂ ill-defined globally)" :
                               slope_c4 > -1.5 ? "  (intermediate decay)" :
                                                  "  (fast / exponential decay)"
                    @printf("    log|C(τ)| vs log τ slope: %.3f%s\n", slope_c4, flag_c4)
                end
            end
        else
            @printf("    (need ≥16 coarse windows; n_blog=%d with T=%d gives %d)\n",
                    n_blog, T_acf, n_wins_acf)
        end
    end
    println()

    # ── α₂-5: Collision burst size spectrum ──────────────────────────────────
    @printf("  α₂-5 — Per-bucket collision burst size spectrum:\n")
    # For each bucket b: find all maximal runs of consecutive steps where
    # blog[t] == b.  Collect the run-length distribution across all buckets.
    let
        burst_lengths = Int[]
        cur_b   = blog[1]
        cur_len = 1
        for t in 2:n_blog
            if blog[t] == cur_b
                cur_len += 1
            else
                cur_len > 1 && push!(burst_lengths, cur_len)
                cur_b   = blog[t]
                cur_len = 1
            end
        end
        cur_len > 1 && push!(burst_lengths, cur_len)

        if length(burst_lengths) >= 10
            n_bl    = length(burst_lengths)
            mean_bl = sum(burst_lengths) / n_bl
            max_bl  = maximum(burst_lengths)
            cnt1_bl = count(==(1), burst_lengths)   # handled above as cur_len==1 skip
            cnt2_bl = count(==(2), burst_lengths)
            cnt3p_bl = count(>=(3), burst_lengths)
            # KS vs Geometric(1/mean)
            p_geo_bl = mean_bl > 1.0 ? 1.0 / mean_bl : 1.0
            bsorted_bl = sort(burst_lengths)
            ks_bl = 0.0; cumul_bl = 0.0
            for bs in bsorted_bl
                cumul_bl += 1.0 / n_bl
                geo_cdf_bl = 1.0 - (1.0 - p_geo_bl)^bs
                ks_bl = max(ks_bl, abs(cumul_bl - geo_cdf_bl))
            end
            flag_bl = ks_bl > 0.1 ? "  ← POWER-LAW BURST (α₂ dominated by rare-event geometry)" :
                                     "  (consistent with geometric burst sizes)"
            @printf("    %d multi-step bursts detected (steps that re-hit same bucket)\n", n_bl)
            @printf("    mean_len=%.2f  max_len=%d\n", mean_bl, max_bl)
            @printf("    len=2: %d (%.1f%%)  len=3+: %d (%.1f%%)\n",
                    cnt2_bl, 100.0*cnt2_bl/n_bl, cnt3p_bl, 100.0*cnt3p_bl/n_bl)
            @printf("    KS vs Geometric(1/mean)=%.4f%s\n", ks_bl, flag_bl)
            # Log-log tail slope for power-law fit
            max_len_fit = min(max_bl, 30)
            len_counts  = [count(==(k), burst_lengths) for k in 2:max_len_fit]
            nonzero_idx = [k for k in eachindex(len_counts) if len_counts[k] > 0]
            if length(nonzero_idx) >= 4
                log_k   = [log(Float64(k+1)) for k in nonzero_idx]
                log_cnt = [log(Float64(len_counts[k])) for k in nonzero_idx]
                mk = sum(log_k)/length(log_k); mc = sum(log_cnt)/length(log_cnt)
                num_pl = sum((log_k[i]-mk)*(log_cnt[i]-mc) for i in eachindex(log_k))
                den_pl = sum((log_k[i]-mk)^2 for i in eachindex(log_k))
                slope_pl = den_pl > 0 ? num_pl / den_pl : 0.0
                flag_pl = slope_pl < -1.5 ? "  (steeper than geometric — sub-Poisson)" :
                          slope_pl > -0.5 ? "  ← SHALLOW SLOPE (power-law tail)" :
                                            "  (moderate slope)"
                @printf("    log-log tail slope: %.3f%s\n", slope_pl, flag_pl)
            end
        else
            @printf("    (fewer than 10 multi-step bursts detected; walk well-mixing at bucket level)\n")
        end
    end
    println()

    # ── α₂-6: ρ(T) = S_occ(T)/S₂(T) over dyadic windows ────────────────────
    @printf("  α₂-6 — ρ(T) = S_occ(T)/S₂(T) (effective-support vs collision-space ratio):\n")
    @printf("    window_T   α₂(T)   S_occ(T)   ρ(T)   dρ/dlogT   interpretation\n")
    prev_rho   = NaN
    prev_logT6 = NaN
    rho_vals   = Float64[]
    for T in dyadic_windows
        n_wins_r = n_blog ÷ T
        n_wins_r < 1 && continue
        s2_acc6 = 0.0; socc_acc6 = 0.0; n_v6 = 0
        counts_T6 = zeros(Int, nb_a2)
        for wi in 0:(n_wins_r - 1)
            fill!(counts_T6, 0)
            for k in (wi*T + 1):((wi+1)*T)
                counts_T6[Int(blog[k]) + 1] += 1
            end
            (s2, socc, _) = _bucket_entropies(counts_T6, nb_a2)
            if !isnan(s2)
                s2_acc6 += s2; socc_acc6 += socc; n_v6 += 1
            end
        end
        n_v6 == 0 && continue
        a2_T6   = s2_acc6   / n_v6
        socc_T6 = socc_acc6 / n_v6
        rho_T6  = a2_T6 > 0.0 ? socc_T6 / a2_T6 : NaN
        logT6   = log2(Float64(T))
        drho = (!isnan(prev_rho) && !isnan(prev_logT6) && logT6 > prev_logT6) ?
               (rho_T6 - prev_rho) / (logT6 - prev_logT6) : NaN
        drho_str = isnan(drho)  ? "        —" : @sprintf("%+9.4f", drho)
        rho_str6 = isnan(rho_T6) ? "     —" : @sprintf("%6.4f", rho_T6)
        interp = if isnan(rho_T6)
            "—"
        elseif !isnan(drho) && drho > 0.05
            "ρ GROWING → decoupled geometry"
        elseif !isnan(drho) && drho < -0.05
            "ρ SHRINKING → collapsing state space"
        else
            "ρ stable"
        end
        @printf("    %9d  %7.4f  %9.4f  %s  %s  %s\n",
                T, a2_T6, socc_T6, rho_str6, drho_str, interp)
        push!(rho_vals, isnan(rho_T6) ? 0.0 : rho_T6)
        prev_rho = rho_T6; prev_logT6 = logT6
    end
    if length(rho_vals) >= 3
        rho_range = maximum(rho_vals) - minimum(rho_vals)
        flag_rho  = rho_range < 0.05 ?
            "  → ρ CONSTANT: consistent scaling dimension" :
            @sprintf("  → ρ VARIES (range=%.4f): geometry and collision space decouple", rho_range)
        @printf("    %s\n", flag_rho)
    end
    println()

    # ── α₂-7: LP1-conj key collision geometry ────────────────────────────────
    # Since blog is now the LP1-conj a-bucket sequence, all events are split steps.
    # Instead of split/non-split (vacuous), compare α₂ on the first vs second half
    # of the emission sequence to detect non-stationarity in key geometry.
    @printf("  α₂-7 — LP1-conj collision geometry: first-half vs second-half α₂:\n")
    if n_blog >= 8
        mid = n_blog ÷ 2
        counts_h1 = zeros(Int, nb_a2); counts_h2 = zeros(Int, nb_a2)
        for i in 1:mid;        counts_h1[Int(blog[i]) + 1] += 1; end
        for i in (mid+1):n_blog; counts_h2[Int(blog[i]) + 1] += 1; end
        (s2_h1, socc_h1, n_h1) = _bucket_entropies(counts_h1, nb_a2)
        (s2_h2, socc_h2, n_h2) = _bucket_entropies(counts_h2, nb_a2)
        @printf("    first  half: %d events  α₂=%s  S_occ=%s\n",
                n_h1, isnan(s2_h1) ? "—" : @sprintf("%.4f", s2_h1),
                      isnan(socc_h1) ? "—" : @sprintf("%.4f", socc_h1))
        @printf("    second half: %d events  α₂=%s  S_occ=%s\n",
                n_h2, isnan(s2_h2) ? "—" : @sprintf("%.4f", s2_h2),
                      isnan(socc_h2) ? "—" : @sprintf("%.4f", socc_h2))
        if !isnan(s2_h1) && !isnan(s2_h2)
            delta_a2_halves = s2_h2 - s2_h1
            flag_halves = abs(delta_a2_halves) > 0.1 ?
                @sprintf("  ← NON-STATIONARY key geometry (Δα₂=%+.4f)", delta_a2_halves) :
                "  (key geometry stationary across run)"
            @printf("    Δα₂ = second − first = %+.4f%s\n", delta_a2_halves, flag_halves)
        end
    else
        @printf("    (need ≥8 LP1-conj emissions)\n")
    end
    println()

    # ── α₂-8: fluctuation curvature + per-window dispersion ───────────────────
    @printf("  α₂-8 — fluctuation curvature and dispersion across dyadic windows:\n")
    if length(a2_vals) >= 3
        d2_vals = [a2_vals[i+1] - 2a2_vals[i] + a2_vals[i-1] for i in 2:(length(a2_vals)-1)]
        max_abs_d2 = maximum(abs.(d2_vals))
        mean_abs_d2 = sum(abs.(x) for x in d2_vals) / length(d2_vals)
        @printf("    max |Δ²α₂| over logT   : %.6f\n", max_abs_d2)
        @printf("    mean |Δ²α₂| over logT  : %.6f\n", mean_abs_d2)
        flag_d2 = max_abs_d2 < 0.03 ? "  (curvature essentially flat)" :
                  max_abs_d2 < 0.10 ? "  (small residual curvature)" :
                                     "  ← curvature drift / hidden crossover"
        @printf("    curvature verdict      :%s\n", flag_d2)
    else
        @printf("    (need ≥3 dyadic windows for curvature)\n")
    end

    # Per-window dispersion of the α₂ estimator itself.
    @printf("  α₂ dispersion by window size:\n")
    for T in dyadic_windows
        n_wins_a2 = n_blog ÷ T
        n_wins_a2 < 2 && continue
        window_a2 = Float64[]
        counts_T = zeros(Int, nb_a2)
        for wi in 0:(n_wins_a2 - 1)
            fill!(counts_T, 0)
            for k in (wi*T + 1):((wi+1)*T)
                counts_T[Int(blog[k]) + 1] += 1
            end
            (s2w, _, _) = _bucket_entropies(counts_T, nb_a2)
            !isnan(s2w) && push!(window_a2, s2w)
        end
        if length(window_a2) >= 2
            μw, varw, skeww, kurtw = _moment4(window_a2)
            @printf("    T=%-8d  μ=%.4f  σ²=%.6f  skew=%+.3f  kurt=%+.3f\n",
                    T, μw, varw, skeww, kurtw)
        end
    end
    println()

    # ── α₂-9: measure-preserving / KL drift and perturbation susceptibility ───
    @printf("  α₂-9 — measure-preserving test and perturbation susceptibility:\n")
    if length(dyadic_windows) >= 2
        for T in dyadic_windows[1:min(4, length(dyadic_windows))]
            n_wins_a2 = n_blog ÷ T
            n_wins_a2 < 2 && continue
            kls = Float64[]
            prev_counts = zeros(Int, nb_a2)
            for wi in 0:(n_wins_a2 - 1)
                counts_T = zeros(Int, nb_a2)
                for k in (wi*T + 1):((wi+1)*T)
                    counts_T[Int(blog[k]) + 1] += 1
                end
                if wi > 0
                    push!(kls, _kl_divergence_counts(prev_counts, counts_T))
                end
                prev_counts .= counts_T
            end
            if !isempty(kls)
                @printf("    T=%-8d  mean KL(prev||curr)=%.5f  max KL=%.5f\n",
                        T, sum(kls)/length(kls), maximum(kls))
            end
        end
    end
    # Susceptibility proxy: KL drift between consecutive coarse blocks.
    # (slog is all-true for LP1-conj emissions, so split/non-split partition
    # is degenerate; instead measure inter-block KL divergence as a proxy for
    # stationarity — large KL → the a-bucket distribution is drifting.)
    if length(blog) >= 64
        block_T = max(8, n_blog ÷ 32)
        n_blocks = n_blog ÷ block_T
        if n_blocks >= 4
            kl_drift_vals = Float64[]
            prev_cnts = zeros(Int, nb_a2)
            for bi in 0:(n_blocks - 1)
                lo = bi * block_T + 1
                hi = min((bi + 1) * block_T, n_blog)
                cur_cnts = zeros(Int, nb_a2)
                for j in lo:hi
                    cur_cnts[Int(blog[j]) + 1] += 1
                end
                if bi > 0 && sum(prev_cnts) > 0 && sum(cur_cnts) > 0
                    push!(kl_drift_vals, _kl_divergence_counts(prev_cnts, cur_cnts))
                end
                prev_cnts .= cur_cnts
            end
            if !isempty(kl_drift_vals)
                mean_kl = sum(kl_drift_vals) / length(kl_drift_vals)
                max_kl  = maximum(kl_drift_vals)
                flag_kl = mean_kl > 0.5 ? "  ← HIGH DRIFT (a-dist non-stationary)" :
                          mean_kl > 0.1 ? "  (moderate drift)" :
                                          "  (a-dist stable across blocks)"
                @printf("    KL drift proxy (block_T=%d): mean=%.5f  max=%.5f%s\n",
                        block_T, mean_kl, max_kl, flag_kl)
            else
                @printf("    KL drift proxy        : insufficient block data\n")
            end
        end
    end
    println()

    # ── α₂-10: collision entropy decomposition and hot-bucket concentration ──
    # Operates on the full LP1-conj partial key stream (blog / lp1_conj_key_blog),
    # exactly as α₂-1 through α₂-9.  Accumulate bucket counts from the entire
    # blog vector and compute S₂ (Rényi-2 entropy) and concentration metrics.
    @printf("  α₂-10 — collision entropy decomposition / entropy whales (LP1-conj keys):\n")
    if n_blog >= 1
        counts_a10 = zeros(Int, nb_a2)
        for b in blog
            counts_a10[Int(b) + 1] += 1
        end
        (s2_all, socc_all, n_all) = _bucket_entropies(counts_a10, nb_a2)
        if n_all > 0
            top1  = _top_share(counts_a10, 0.01)
            top5  = _top_share(counts_a10, 0.05)
            top10 = _top_share(counts_a10, 0.10)
            @printf("    n_partials             : %d  (nb_fp_buckets=%d)\n", n_all, nb_a2)
            @printf("    α₂(lp1_conj keys)      : %.5f\n", s2_all)
            @printf("    top 1%% / 5%% / 10%% share : %.3f  %.3f  %.3f\n", top1, top5, top10)
            @printf("    occupancy entropy      : %.5f\n", socc_all)
            if top1 > 0.25
                @printf("    verdict                 :  ← entropy dominated by rare hot buckets\n")
            else
                @printf("    verdict                 :  (no extreme entropy whales)\n")
            end
        end
    else
        @printf("    (no LP1-conj partials recorded)\n")
    end
    println()

    # ── α₂-11: effective independence, motifs, and provenance hash ───────────
    @printf("  α₂-11 — effective independence, motifs, and provenance hash:\n")
    if length(arrivals) >= 8
        # Reuse the same coarse-window count model as the ACF section.
        total_span_eff = arrivals[end] - arrivals[1] + 1
        T_eff = max(100, total_span_eff ÷ 200)
        n_bins_eff = max(8, total_span_eff ÷ T_eff)
        counts_eff = zeros(Float64, n_bins_eff)
        t0_eff = arrivals[1]
        for a in arrivals
            wi = min(n_bins_eff, (a - t0_eff) ÷ T_eff + 1)
            counts_eff[wi] += 1.0
        end
        mn_eff = sum(counts_eff) / n_bins_eff
        var_eff = sum((c - mn_eff)^2 for c in counts_eff) / max(1, n_bins_eff - 1)
        if var_eff > 1e-30
            ρsum = 0.0
            max_lag = min(10, n_bins_eff - 1)
            for lag in 1:max_lag
                cov = sum((counts_eff[w] - mn_eff) * (counts_eff[w + lag] - mn_eff)
                          for w in 1:(n_bins_eff - lag)) / (n_bins_eff - lag)
                ρ = cov / var_eff
                ρsum += max(0.0, ρ)
            end
            neff = n_bins_eff / max(1e-9, 1.0 + 2.0 * ρsum)
            @printf("    N_eff (coarse windows) : %.2f of %d windows\n", neff, n_bins_eff)
        end
    end

    if length(blog) >= 4
        # a-bucket 4-gram motifs: detect repeated local patterns in the LP1-conj
        # a-bucket sequence.  Under i.i.d. uniform over nb buckets, every 4-gram
        # has probability 1/nb³; excess repetitions flag structural correlation.
        motif_counts_b = Dict{NTuple{4,Int},Int}()
        for i in 1:(length(blog)-3)
            mot = (blog[i], blog[i+1], blog[i+2], blog[i+3])
            motif_counts_b[mot] = get(motif_counts_b, mot, 0) + 1
        end
        if !isempty(motif_counts_b)
            top_motif_b = first(sort(collect(motif_counts_b), by = x -> -last(x)))
            n_4grams    = length(blog) - 3
            # Expected count for most-probable 4-gram under empirical marginal:
            # use product of empirical bucket frequencies as independence baseline.
            bkt_freq = zeros(Float64, nb_a2)
            for b in blog; bkt_freq[Int(b)+1] += 1.0; end
            bkt_freq ./= max(1.0, length(blog))
            p_indep = prod(bkt_freq[Int(b)+1] for b in top_motif_b[1])
            expected_b = p_indep * max(1, n_4grams)
            lift_b = top_motif_b[2] / max(1e-9, expected_b)
            flag_b = lift_b > 3.0 ? "  ← REPEATED STRUCTURAL MOTIF" :
                     lift_b > 1.5 ? "  (mild motif excess)" :
                                    "  (consistent with independence)"
            @printf("    top a-bucket 4-gram    : (%d,%d,%d,%d)  count=%d  expected≈%.2f  lift=%.2f%s\n",
                    top_motif_b[1]..., top_motif_b[2], expected_b, lift_b, flag_b)
        end
    end

    if !isempty(stat.event_hash_log)
        hset = length(unique(stat.event_hash_log))
        repeats = length(stat.event_hash_log) - hset
        final_digest = reduce(⊻, stat.event_hash_log; init=UInt64(0))
        @printf("    provenance hash states : %d  unique=%d  repeats=%d\n",
                length(stat.event_hash_log), hset, repeats)
        @printf("    provenance digest      : 0x%016x\n", final_digest)
        if repeats > 0
            @printf("    verdict                : repeated structural motifs detected\n")
        end
    end
    println()

    end  # if n_blog >= 32

    @printf("──────────────────────────────────────────────────────────────────────\n")
    flush(stdout)
end
