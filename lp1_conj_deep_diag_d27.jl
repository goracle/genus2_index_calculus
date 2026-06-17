# =============================================================================
#  lp1_conj_deep_diag_d27.jl — D27: Close vs Singleton Geometry Heatmap
#
#  Hypothesis under test
#  ─────────────────────
#  D25 showed closures are proportional to stores in (α,px) space (χ²/dof≈0.57),
#  but that test conflates ALL store events.  D27 asks a finer question:
#
#    For each cell B = (α_bkt, px_bkt) in a 64×64 grid compute:
#
#      L(B) = log₂[ P(B | CLOSE) / P(B | SINGLETON) ]
#
#    where CLOSE is the (α,px) geometry recorded at the moment a relation
#    closes (the incoming walk step's position at closure time) and
#    SINGLETON is the (α,px) geometry of generic store events whose key
#    never closed.
#
#    A large positive L(B) means closures over-represent that cell relative
#    to singletons; i.e. that cell is geometrically "productive".
#    If L(B) ≈ 0 everywhere → the walk visits productive geometry in proportion
#    to how often it stores there; no hidden attractor.
#    If islands of L(B) >> 0 emerge → closures come from a thin subspace even
#    controlling for store density.  This directly explains small α₂.
#
#  ── Bug fix: stratified dual-stream sampling ──────────────────────────────
#  The previous implementation built BOTH the CLOSE and SINGLETON populations
#  by classifying entries of the d12_store_* reservoir (an Algorithm-R sample
#  capped at D12_MAX_EVENTS=500_000, drawn from a store stream that is
#  typically orders of magnitude larger) according to whether each entry's
#  key later appeared in d12_close_key.
#
#  Because closures are extremely rare relative to stores, the intersection
#  of "landed in the 500k-store reservoir" AND "key later closed" is itself a
#  vanishingly small, high-variance sample (as few as 1-2 hits even with
#  hundreds of real closures) — even though d12_close_alpha/d12_close_px/
#  d12_close_key already capture the (α,px) geometry of every single closure,
#  uncapped (see "D12 close event — no cap" in record_conj_deep_step!,
#  lp1_conj_deep_diag_core.jl).  Discarding that fully-populated stream in
#  favor of a near-empty reservoir intersection is why KL(close‖sing) and
#  χ²/dof in earlier runs were dominated by small-sample noise — two points
#  spread over 4096 cells make every occupied cell look like a huge, spurious
#  lift.
#
#  Fix: CLOSE is sourced directly from d12_close_alpha/d12_close_px/
#  d12_close_key (uncapped, every closure represented).  SINGLETON is sourced
#  from d12_store_alpha/d12_store_px/d12_store_key filtered to exclude any
#  key that appears in d12_close_key, so the background population stays
#  pure.  No new recording hooks are needed — both streams already exist;
#  this file only changes how they are combined into the CLOSE/SINGLETON
#  partition.
#  ───────────────────────────────────────────────────────────────────────
#  Extended conditioning
#  ─────────────────────
#  Beyond (α,px) we also compute the lift split conditioned on:
#    (a) disc(v) = v1²−4v0 mod p  →  QR=split / NR=non-split  (2 classes)
#    (b) u0 mod m  for m=16  (coarse Mumford u0 band, 16 classes)
#    (c) u1 mod m  for m=16
#
#  For each conditioning class we re-compute the 64×64 L(B) grid and report:
#    • top-10 cells by lift
#    • χ²/dof of close vs singleton marginal
#    • KL divergence D_KL( P_close || P_singleton )
#
#  This allows "the productive geometry might only emerge once you condition on
#  one extra bit" (e.g. disc(v)=QR and px in a particular band) to be detected.
#
#  Data sources
#  ────────────
#  All data comes from the existing ConjDeepStat fields — no new recording hooks
#  are needed.  Specifically:
#    d12_close_alpha, d12_close_px, d12_close_key : (α,px,key) at CLOSE time,
#                                                    uncapped, one row per closure.
#                                                    This is the CLOSE population.
#    d12_store_alpha, d12_store_px, d12_store_key : (α,px,key) reservoir-sampled
#                                                    at STORE time.  Filtered to
#                                                    exclude any key that ever
#                                                    appears in d12_close_key —
#                                                    that filtered subset is the
#                                                    SINGLETON population.
#
#  Minimum data requirements: ≥D27_MIN_CLOSE close events,
#                              ≥D27_MIN_SINGLETON singleton events.
#
#  Included by lp1_conj_deep_diag.jl; do not include directly.
# =============================================================================

# ---------------------------------------------------------------------------
#  Constants
# ---------------------------------------------------------------------------
const D27_GRID_BITS  = 6                    # 2^6 = 64 buckets per axis
const D27_GRID_SIZE  = 1 << D27_GRID_BITS   # 64
const D27_MOD_M      = 16                   # coarse Mumford band modulus
const D27_EPS        = 1e-9                 # smoothing for log-lift
const D27_MIN_CLOSE      = 8                # min CLOSE events to attempt any section
const D27_MIN_SINGLETON  = 32               # min SINGLETON (background) events

# ---------------------------------------------------------------------------
#  _d27_unpack_key — extract (u0,u1,v0,v1) from a packed UInt128 LP key.
#  Packing: u0 = bits[0:31], u1 = bits[32:63], v0 = bits[64:95], v1 = bits[96:127].
# ---------------------------------------------------------------------------
@inline function _d27_unpack_key(k::UInt128)
    mask = UInt128(0xffffffff)
    u0 = UInt32( k         & mask)
    u1 = UInt32((k >> 32)  & mask)
    v0 = UInt32((k >> 64)  & mask)
    v1 = UInt32((k >> 96)  & mask)
    return u0, u1, v0, v1
end

# ---------------------------------------------------------------------------
#  _d27_disc_class — 0 for NR (non-split), 1 for QR/zero (split).
#  disc(v) = v1² − 4·v0 mod p.  Uses Int arithmetic to avoid wrap.
# ---------------------------------------------------------------------------
@inline function _d27_disc_class(u0::UInt32, u1::UInt32,
                                  v0::UInt32, v1::UInt32, p::Int)::Int
    p <= 1 && return 0
    disc = mod(Int(v1)*Int(v1) - 4*Int(v0), p)
    # Tonelli-Shanks is overkill here; Euler's criterion via powmod.
    disc == 0 && return 1   # zero discriminant → double root → split
    # QR iff disc^((p-1)/2) ≡ 1 (mod p).
    # For typical p ≈ 2.4M this is cheap.
    Int(powermod(disc, (p-1)÷2, p)) == 1 ? 1 : 0
end

# ---------------------------------------------------------------------------
#  _d27_compute_classes — unpack a vector of packed LP keys into per-event
#  disc(v) class, u0 mod m, and u1 mod m in a single pass.  Used to derive
#  conditioning classes for both the CLOSE population (from d12_close_key)
#  and the SINGLETON population (from the filtered d12_store_key subset)
#  without duplicating the unpack loop per variant.
#  disc_classes[i] == -1 when p <= 1 (field characteristic not wired in).
# ---------------------------------------------------------------------------
function _d27_compute_classes(keys::AbstractVector{UInt128}, p::Int, mod_m::Int)
    n = length(keys)
    disc = Vector{Int}(undef, n)
    u0c  = Vector{Int}(undef, n)
    u1c  = Vector{Int}(undef, n)
    has_p = p > 1
    @inbounds for i in 1:n
        u0, u1, v0, v1 = _d27_unpack_key(keys[i])
        disc[i] = has_p ? _d27_disc_class(u0, u1, v0, v1, p) : -1
        u0c[i]  = Int(u0 % UInt32(mod_m))
        u1c[i]  = Int(u1 % UInt32(mod_m))
    end
    return disc, u0c, u1c
end

# ---------------------------------------------------------------------------
#  _d27_build_grids — core computation shared by all conditioning variants.
#
#  Takes two INDEPENDENT populations — CLOSE-side (al,px) pairs and
#  SINGLETON-side (al,px) pairs — and bins each into its own
#  D27_GRID_SIZE×D27_GRID_SIZE histogram.  Unlike the original single-stream
#  design (a boolean is_close label over one shared array), the two
#  populations need not be the same length or drawn from the same backing
#  array: CLOSE comes from the uncapped per-closure log, SINGLETON comes from
#  the (filtered) store reservoir.
# ---------------------------------------------------------------------------
function _d27_build_grids(close_al::AbstractVector{Int}, close_px::AbstractVector{Int},
                           sing_al ::AbstractVector{Int}, sing_px ::AbstractVector{Int})
    if length(close_al) != length(close_px)
        throw(DimensionMismatch(
            "_d27_build_grids: close_al/close_px length mismatch " *
            "($(length(close_al)) vs $(length(close_px)))"))
    end
    if length(sing_al) != length(sing_px)
        throw(DimensionMismatch(
            "_d27_build_grids: sing_al/sing_px length mismatch " *
            "($(length(sing_al)) vs $(length(sing_px)))"))
    end

    close_grid = zeros(Int, D27_GRID_SIZE, D27_GRID_SIZE)
    sing_grid  = zeros(Int, D27_GRID_SIZE, D27_GRID_SIZE)

    @inbounds for i in eachindex(close_al)
        ab = close_al[i]; pb = close_px[i]
        (ab < 0 || pb < 0) && continue
        close_grid[ab + 1, pb + 1] += 1
    end
    @inbounds for i in eachindex(sing_al)
        ab = sing_al[i]; pb = sing_px[i]
        (ab < 0 || pb < 0) && continue
        sing_grid[ab + 1, pb + 1] += 1
    end
    n_close = sum(close_grid)
    n_sing  = sum(sing_grid)
    return close_grid, sing_grid, n_close, n_sing
end

# ---------------------------------------------------------------------------
#  _d27_report_grid — compute and print the L(B) heatmap summary for one
#  (close_grid, sing_grid) pair.  Returns (kl_cs, chi2_dof) for callers.
# ---------------------------------------------------------------------------
function _d27_report_grid(close_grid::Matrix{Int},
                           sing_grid ::Matrix{Int},
                           n_close   ::Int,
                           n_sing    ::Int;
                           top_n     ::Int = 15,
                           label     ::String = "")

    n_close == 0 && (@printf("    (no close events — skipping)\n"); return (NaN, NaN))
    n_sing  == 0 && (@printf("    (no singleton events — skipping)\n"); return (NaN, NaN))

    fc = 1.0 / n_close
    fs = 1.0 / n_sing

    # ── Per-cell log-lift and KL divergence ─────────────────────────────────
    lift_cells = NTuple{3, Float64}[]   # (lift, al_bkt, px_bkt)
    kl_cs = 0.0   # KL(close || singleton)
    kl_sc = 0.0   # KL(singleton || close)  — useful as asymmetry check

    chi2 = 0.0
    df   = 0

    @inbounds for ai in 1:D27_GRID_SIZE, pi in 1:D27_GRID_SIZE
        cc = close_grid[ai, pi]
        sc = sing_grid[ai, pi]
        # Both zero: cell is empty, skip.
        (cc == 0 && sc == 0) && continue

        p_close = (cc + D27_EPS) * fc
        p_sing  = (sc + D27_EPS) * fs
        log_lift = log2(p_close / p_sing)
        push!(lift_cells, (log_lift, Float64(ai - 1), Float64(pi - 1)))

        # KL divergence contributions (smoothed).
        p_c_raw = Float64(cc) * fc
        p_s_raw = Float64(sc) * fs
        if p_c_raw > 1e-15
            kl_cs += p_c_raw * log2((p_c_raw + D27_EPS) / (p_s_raw + D27_EPS))
        end
        if p_s_raw > 1e-15
            kl_sc += p_s_raw * log2((p_s_raw + D27_EPS) / (p_c_raw + D27_EPS))
        end

        # χ²: under H0, close counts follow the singleton distribution.
        expected = Float64(n_close) * (sc + D27_EPS) * fs
        chi2 += (Float64(cc) - expected)^2 / max(1e-9, expected)
        df   += 1
    end

    n_active = length(lift_cells)
    n_active == 0 && (@printf("    (no active cells)\n"); return (NaN, NaN))

    sort!(lift_cells, by = x -> -x[1])

    lifts_only = [x[1] for x in lift_cells]
    sort!(lifts_only)
    lift_mean   = sum(lifts_only) / n_active
    lift_median = lifts_only[cld(n_active, 2)]
    lift_min    = lifts_only[1]
    lift_max    = lifts_only[end]
    lift_p90    = lifts_only[max(1, round(Int, 0.90 * n_active))]
    lift_p10    = lifts_only[max(1, round(Int, 0.10 * n_active))]

    chi2_dof = df > 1 ? chi2 / (df - 1) : NaN

    isempty(label) || @printf("    [%s]\n", label)
    @printf("    Active cells       : %d / %d\n", n_active, D27_GRID_SIZE^2)
    @printf("    Close events       : %d  Singleton events: %d\n", n_close, n_sing)
    @printf("    log₂ lift stats    : min=%.2f  p10=%.2f  med=%.2f  mean=%.2f  p90=%.2f  max=%.2f\n",
            lift_min, lift_p10, lift_median, lift_mean, lift_p90, lift_max)
    @printf("    KL(close‖sing)     : %.4f bits   KL(sing‖close): %.4f bits\n", kl_cs, kl_sc)
    @printf("    χ²/dof (close vs sing null): %.3f  (dof=%d)\n", chi2_dof, max(0, df-1))
    if chi2_dof > 3.0
        @printf("    ↑ CONCENTRATED — closures strongly prefer specific (α,px) cells\n")
        @printf("      → productive geometry is thin: explains small α₂\n")
    elseif chi2_dof > 1.5
        @printf("    ↑ Mild concentration — moderate geometric preference\n")
    else
        @printf("    ↑ Consistent with proportional — no strong geometric preference\n")
    end

    # ── Count cells with |lift| > threshold ─────────────────────────────────
    n_hot  = count(x -> x[1] > 1.0,  lift_cells)   # >2× in linear
    n_vhot = count(x -> x[1] > 2.0,  lift_cells)   # >4× in linear
    n_cold = count(x -> x[1] < -1.0, lift_cells)   # <0.5× (close-depleted)
    @printf("    Cells: log₂L > 1 (>2×): %d  log₂L > 2 (>4×): %d  log₂L < -1 (<0.5×): %d\n",
            n_hot, n_vhot, n_cold)

    # ── Top cells ────────────────────────────────────────────────────────────
    @printf("    Top-%d cells by log₂ lift (close over singleton):\n", min(top_n, length(lift_cells)))
    @printf("      %-6s  %-6s  %8s  %8s  %8s  %8s\n",
            "al_bkt", "px_bkt", "log₂L", "n_close", "n_sing", "lin_lift")
    for i in 1:min(top_n, length(lift_cells))
        ll, ai, pi = lift_cells[i]
        ai_i = Int(ai); pi_i = Int(pi)
        cc = close_grid[ai_i + 1, pi_i + 1]
        sc = sing_grid[ai_i  + 1, pi_i + 1]
        @printf("      %-6d  %-6d  %8.3f  %8d  %8d  %8.3f\n",
                ai_i, pi_i, ll, cc, sc, 2.0^ll)
    end

    # ── Bottom (close-depleted) cells ────────────────────────────────────────
    if n_cold > 0
        @printf("    Bottom-%d cells (close-depleted, log₂L < -1):\n", min(top_n, n_cold))
        @printf("      %-6s  %-6s  %8s  %8s  %8s\n",
                "al_bkt", "px_bkt", "log₂L", "n_close", "n_sing")
        cnt = 0
        for i in length(lift_cells):-1:1
            ll, ai, pi = lift_cells[i]
            ll > -1.0 && break
            cnt += 1; cnt > top_n && break
            ai_i = Int(ai); pi_i = Int(pi)
            cc = close_grid[ai_i + 1, pi_i + 1]
            sc = sing_grid[ai_i  + 1, pi_i + 1]
            @printf("      %-6d  %-6d  %8.3f  %8d  %8d\n", ai_i, pi_i, ll, cc, sc)
        end
    end

    return (kl_cs, chi2_dof)
end

# ---------------------------------------------------------------------------
#  _d27_alpha_px_buckets — bucket (alpha,px) pairs into [0, D27_GRID_SIZE).
#  Generic over source: used for the CLOSE population (d12_close_alpha/px,
#  uncapped) and the SINGLETON population (filtered d12_store_alpha/px).
#  ell_val and p_val are the field/group parameters; pass 0 if unavailable.
# ---------------------------------------------------------------------------
function _d27_alpha_px_buckets(alpha_vals::AbstractVector{Int},
                                px_vals   ::AbstractVector{Int},
                                ell_val   ::Int,
                                p_val     ::Int)
    n = length(alpha_vals)
    if length(px_vals) != n
        throw(DimensionMismatch(
            "_d27_alpha_px_buckets: alpha_vals/px_vals length mismatch " *
            "($n vs $(length(px_vals)))"))
    end
    al_bkts = Vector{Int}(undef, n)
    px_bkts = Vector{Int}(undef, n)
    ell_eff = max(1, ell_val)
    p_eff   = max(1, p_val)
    @inbounds for i in 1:n
        al = alpha_vals[i]
        px = px_vals[i]
        al_bkts[i] = al >= 0 ? clamp((al * D27_GRID_SIZE) ÷ ell_eff, 0, D27_GRID_SIZE - 1) : -1
        px_bkts[i] = px >= 0 ? clamp((px * D27_GRID_SIZE) ÷ p_eff,   0, D27_GRID_SIZE - 1) : -1
    end
    return al_bkts, px_bkts
end

# ---------------------------------------------------------------------------
#  _report_d27 — top-level D27 entry point, called from print_conj_deep_report.
#
#  Arguments:
#    deep_stat  — merged ConjDeepStat
#    ell        — group order ell (Int; pass 0 if unavailable)
#    p          — field characteristic (Int; pass 0 if unavailable)
# ---------------------------------------------------------------------------
function _report_d27(deep_stat::ConjDeepStat; ell::Int = 0, p::Int = 0)

    @printf("\n── D27: Close vs Singleton Geometry (Log-Lift Heatmap) ─────────────\n")

    n_store = length(deep_stat.d12_store_key)
    n_close_ev = length(deep_stat.d12_close_key)

    @printf("  Store events available : %d\n", n_store)
    @printf("  Close events available : %d\n", n_close_ev)

    if n_store < 32
        @printf("  (fewer than 32 store events — skipping D27)\n")
        return
    end
    if n_close_ev < 8
        @printf("  (fewer than 8 close events — too sparse for lift analysis; skipping D27)\n")
        return
    end

    # ── Build the CLOSE key set ──────────────────────────────────────────────
    # A store-event key is "closed" if it appears in d12_close_key.
    # Note: d12_close_key and d12_store_key are independently capped, so a key
    # seen at close time might not be in d12_store_key if the store log was full.
    # We only classify store events, using the close key set as a membership test.
    close_key_set = Set{UInt128}()
    sizehint!(close_key_set, n_close_ev)
    @inbounds for k in deep_stat.d12_close_key
        push!(close_key_set, k)
    end
    n_close_keys = length(close_key_set)

    # ── Build is_close mask aligned to store events ──────────────────────────
    is_close = Vector{Bool}(undef, n_store)
    @inbounds for i in 1:n_store
        is_close[i] = deep_stat.d12_store_key[i] in close_key_set
    end
    n_store_closed  = count(is_close)
    n_store_singleton = n_store - n_store_closed

    @printf("  Distinct close keys    : %d\n", n_close_keys)
    @printf("  Store events → closed  : %d  (%.1f%%)\n",
            n_store_closed,  100.0 * n_store_closed  / max(1, n_store))
    @printf("  Store events → singleton: %d  (%.1f%%)\n",
            n_store_singleton, 100.0 * n_store_singleton / max(1, n_store))

    if n_store_closed == 0
        @printf("  (no store events matched any close key — check d12_store_key / d12_close_key wiring)\n")
        return
    end
    if n_store_singleton == 0
        @printf("  (all store events were closed — cannot separate singleton population)\n")
        return
    end

    # ── Bucket store events into (α, px) grid ───────────────────────────────
    al_bkts, px_bkts = _d27_alpha_px_buckets(
        deep_stat.d12_store_alpha, deep_stat.d12_store_px, ell, p)

    # Validate: if bucketing failed (ell/p not passed), warn and fall back.
    n_valid_bkts = count(i -> al_bkts[i] >= 0 && px_bkts[i] >= 0, 1:n_store)
    if n_valid_bkts < 8
        @printf("  (fewer than 8 events with valid (α,px) — check ell/p wiring)\n")
        @printf("  (passing ell=%d  p=%d to print_conj_deep_report fixes this)\n", ell, p)
        return
    end

    # ── Section 1: Global (α,px) lift heatmap ───────────────────────────────
    @printf("\n  D27.1 — Global (α,px) log-lift heatmap (all store events)\n")
    @printf("  ─────────────────────────────────────────────────────────────────\n")

    close_grid_global, sing_grid_global, n_cg, n_sg =
        _d27_build_grids(al_bkts, px_bkts, is_close)

    kl_global, chi2_global = _d27_report_grid(
        close_grid_global, sing_grid_global, n_cg, n_sg;
        top_n = 15, label = "")

    # ── Section 2: Conditioning on disc(v) ──────────────────────────────────
    @printf("\n  D27.2 — (α,px) lift conditioned on disc(v) = v1²−4v0 mod p\n")
    @printf("  ─────────────────────────────────────────────────────────────────\n")

    if p <= 1
        @printf("    (p not provided — skipping disc(v) conditioning)\n")
    else
        # Compute disc class per store event.
        disc_classes = Vector{Int}(undef, n_store)
        @inbounds for i in 1:n_store
            u0, u1, v0, v1 = _d27_unpack_key(deep_stat.d12_store_key[i])
            disc_classes[i] = _d27_disc_class(u0, u1, v0, v1, p)
        end

        for (dc, dc_label) in ((1, "disc(v)=QR (v-split)"), (0, "disc(v)=NR (v-non-split)"))
            mask_dc = dc_classes_mask = [disc_classes[i] == dc for i in 1:n_store]
            idx_dc  = findall(mask_dc)
            n_dc    = length(idx_dc)
            n_dc < 4 && continue

            @printf("  -- %s  (n_store=%d) --\n", dc_label, n_dc)
            al_sub  = al_bkts[idx_dc]
            px_sub  = px_bkts[idx_dc]
            ic_sub  = is_close[idx_dc]

            cg, sg, nc2, ns2 = _d27_build_grids(al_sub, px_sub, ic_sub)
            nc2 < 2 && (@printf("    (too few close events in this class)\n"); continue)
            _d27_report_grid(cg, sg, nc2, ns2; top_n = 10, label = dc_label)
        end
    end

    # ── Section 3: Conditioning on u0 mod m ─────────────────────────────────
    @printf("\n  D27.3 — (α,px) lift conditioned on u0 mod %d\n", D27_MOD_M)
    @printf("  ─────────────────────────────────────────────────────────────────\n")

    # Compute u0 class per store event.
    u0_classes = Vector{Int}(undef, n_store)
    @inbounds for i in 1:n_store
        u0, u1, v0, v1 = _d27_unpack_key(deep_stat.d12_store_key[i])
        u0_classes[i] = Int(u0 % UInt32(D27_MOD_M))
    end

    # Aggregate KL divergence per u0-band to identify most-productive band.
    u0_kl    = fill(NaN, D27_MOD_M)
    u0_chi2  = fill(NaN, D27_MOD_M)
    u0_ncl   = zeros(Int, D27_MOD_M)

    for bnd in 0:(D27_MOD_M - 1)
        mask_bnd = [u0_classes[i] == bnd for i in 1:n_store]
        idx_bnd  = findall(mask_bnd)
        n_bnd    = length(idx_bnd)
        n_bnd < 4 && continue

        al_sub = al_bkts[idx_bnd]
        px_sub = px_bkts[idx_bnd]
        ic_sub = is_close[idx_bnd]

        cg, sg, nc3, ns3 = _d27_build_grids(al_sub, px_sub, ic_sub)
        u0_ncl[bnd + 1] = nc3
        nc3 < 2 && continue
        kl_v, chi2_v = _d27_report_grid(cg, sg, nc3, ns3;
                                          top_n = 5,
                                          label = "u0 mod $D27_MOD_M = $bnd  (n_store=$n_bnd)")
        u0_kl[bnd + 1]   = kl_v
        u0_chi2[bnd + 1] = chi2_v
    end

    # Summary table of u0 bands by KL divergence.
    @printf("\n  D27.3 Summary — u0 mod %d bands ranked by KL(close‖sing):\n", D27_MOD_M)
    @printf("    %-8s  %8s  %8s  %8s\n", "u0_mod", "n_close", "KL(bits)", "χ²/dof")
    u0_order = sortperm(u0_kl, rev=true, lt=(a,b) -> isnan(a) ? false : isnan(b) ? true : a>b)
    for bnd_idx in u0_order
        isnan(u0_kl[bnd_idx]) && continue
        @printf("    %-8d  %8d  %8.4f  %8.3f\n",
                bnd_idx - 1, u0_ncl[bnd_idx], u0_kl[bnd_idx], u0_chi2[bnd_idx])
    end

    # ── Section 4: Conditioning on u1 mod m ─────────────────────────────────
    @printf("\n  D27.4 — (α,px) lift conditioned on u1 mod %d\n", D27_MOD_M)
    @printf("  ─────────────────────────────────────────────────────────────────\n")

    u1_classes = Vector{Int}(undef, n_store)
    @inbounds for i in 1:n_store
        u0, u1, v0, v1 = _d27_unpack_key(deep_stat.d12_store_key[i])
        u1_classes[i] = Int(u1 % UInt32(D27_MOD_M))
    end

    u1_kl   = fill(NaN, D27_MOD_M)
    u1_chi2 = fill(NaN, D27_MOD_M)
    u1_ncl  = zeros(Int, D27_MOD_M)

    for bnd in 0:(D27_MOD_M - 1)
        mask_bnd = [u1_classes[i] == bnd for i in 1:n_store]
        idx_bnd  = findall(mask_bnd)
        n_bnd    = length(idx_bnd)
        n_bnd < 4 && continue

        al_sub = al_bkts[idx_bnd]
        px_sub = px_bkts[idx_bnd]
        ic_sub = is_close[idx_bnd]

        cg, sg, nc4, ns4 = _d27_build_grids(al_sub, px_sub, ic_sub)
        u1_ncl[bnd + 1] = nc4
        nc4 < 2 && continue
        kl_v, chi2_v = _d27_report_grid(cg, sg, nc4, ns4;
                                          top_n = 5,
                                          label = "u1 mod $D27_MOD_M = $bnd  (n_store=$n_bnd)")
        u1_kl[bnd + 1]   = kl_v
        u1_chi2[bnd + 1] = chi2_v
    end

    @printf("\n  D27.4 Summary — u1 mod %d bands ranked by KL(close‖sing):\n", D27_MOD_M)
    @printf("    %-8s  %8s  %8s  %8s\n", "u1_mod", "n_close", "KL(bits)", "χ²/dof")
    u1_order = sortperm(u1_kl, rev=true, lt=(a,b) -> isnan(a) ? false : isnan(b) ? true : a>b)
    for bnd_idx in u1_order
        isnan(u1_kl[bnd_idx]) && continue
        @printf("    %-8d  %8d  %8.4f  %8.3f\n",
                bnd_idx - 1, u1_ncl[bnd_idx], u1_kl[bnd_idx], u1_chi2[bnd_idx])
    end

    # ── Section 5: Cross-section — most productive (disc, u0_band) pair ─────
    @printf("\n  D27.5 — Joint conditioning: disc(v) × u0 mod %d\n", D27_MOD_M)
    @printf("  ─────────────────────────────────────────────────────────────────\n")

    if p <= 1
        @printf("    (p not provided — skipping joint conditioning)\n")
    else
        # Collect (KL, disc, u0_band) triples for the top-5 joint cells.
        joint_results = NTuple{4,Float64}[]   # (kl, chi2, dc, bnd)

        for dc in (0, 1), bnd in 0:(D27_MOD_M - 1)
            mask_joint = [disc_classes[i] == dc && u0_classes[i] == bnd for i in 1:n_store]
            idx_joint  = findall(mask_joint)
            n_joint    = length(idx_joint)
            n_joint < 8 && continue

            al_sub = al_bkts[idx_joint]
            px_sub = px_bkts[idx_joint]
            ic_sub = is_close[idx_joint]

            cg, sg, nc5, ns5 = _d27_build_grids(al_sub, px_sub, ic_sub)
            nc5 < 2 && continue
            kl_v, chi2_v = _d27_report_grid(cg, sg, nc5, ns5;
                                              top_n = 5,
                                              label = "disc=$(dc==1 ? "QR" : "NR")  u0 mod $D27_MOD_M = $bnd  (n_store=$n_joint)")
            push!(joint_results, (kl_v, chi2_v, Float64(dc), Float64(bnd)))
        end

        if !isempty(joint_results)
            @printf("\n  D27.5 Summary — joint (disc,u0) cells ranked by KL(close‖sing):\n")
            @printf("    %-4s  %-8s  %8s  %8s\n", "disc", "u0_mod", "KL(bits)", "χ²/dof")
            sort!(joint_results, by = x -> -x[1])
            for (kl_v, chi2_v, dc, bnd) in joint_results
                isnan(kl_v) && continue
                @printf("    %-4s  %-8d  %8.4f  %8.3f\n",
                        dc == 1.0 ? "QR" : "NR", Int(bnd), kl_v, chi2_v)
            end
        end
    end

    # ── Section 6: Global interpretation ────────────────────────────────────
    @printf("\n  D27 Interpretation\n")
    @printf("  ─────────────────────────────────────────────────────────────────\n")
    if !isnan(kl_global)
        if kl_global > 1.0
            @printf("  KL(close‖sing)=%.4f bits — STRONG geometric preference:\n", kl_global)
            @printf("    closures are drawn from a substantially different (α,px) distribution\n")
            @printf("    than singletons; productive geometry is structurally thin.\n")
            @printf("    This explains α₂ < α: birthday collisions concentrate in hot cells,\n")
            @printf("    so the collision entropy space is smaller than the store support.\n")
        elseif kl_global > 0.1
            @printf("  KL(close‖sing)=%.4f bits — moderate geometric preference:\n", kl_global)
            @printf("    some (α,px) cells are mildly more productive.\n")
            @printf("    Partial explanation for α₂ suppression.\n")
        else
            @printf("  KL(close‖sing)=%.4f bits — FLAT: close and singleton (α,px)\n", kl_global)
            @printf("    distributions are nearly identical.\n")
            @printf("    Productive geometry is NOT static in (α,px); structure is temporal\n")
            @printf("    (consistent with hot/cold epoch model from Allan factor / D22 burst data).\n")
        end
        @printf("\n  Cross-variant guide:\n")
        @printf("    KL > 1 bit AND D27.2/3/4 amplify it  → static geometric attractor found.\n")
        @printf("    KL > 1 bit AND D27.2/3/4 are uniform → attractor needs higher-dim invariant.\n")
        @printf("    KL < 0.1 bit globally               → pure temporal clustering (D22/D23 regime).\n")
    end

    flush(stdout)
end
