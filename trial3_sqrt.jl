# =============================================================================
#  trial3_sqrt.jl  --  O(p)-time DLP solver via birthday collision on LP1 keys
#                       (equivalently O(√ell), since ell ~ p² for genus 2 — see
#                       WHY THIS WORKS below. Do NOT read this as O(√p); that
#                       was a theory bug in earlier revisions.)
#
#  ALGORITHM (no factor base, no linalg, no RREF, no DSU)
#  ─────────────────────────────────────────────────────
#  Pick a single frozen anchor P (a random affine F_p point).
#
#  Phase 2  (β = 0, precompute table):
#    Repeat until O(p) entries stored (≈ isqrt(ell)):
#      α  ← rand(1..ell-1)
#      D  ← α·G                              (β=0 ⟹ pure G-multiple)
#      build φ through P and D
#      recover residual pair R+S (LP1: P is "in FB", R+S is the unknown)
#      let key = lp1_key(R,S)               (NTuple{4,UInt32} Mumford pair, or
#                                             NTuple{2,Int} affine split pair)
#      table2[key] = α
#
#  Phase 3  (β ≠ 0, online matching):
#    Repeat until match found or step_cap reached:
#      α₂, β  ← rand(1..ell-1) each
#      D       ← α₂·G + β·T
#      build φ through same frozen P and D
#      recover residual pair → key
#      if key ∈ table2:
#        α_pre  = table2[key]
#        k      = (α_pre - α₂) · β⁻¹  mod  ell
#        verify k·G == T  →  return k
#
#  WHY THIS WORKS
#  ──────────────
#  The LP1 key is (a representation of) the residual degree-2 divisor R+S,
#  which is a general point of J(C/F_p) — NOT a size-~p object indexed by a
#  single coordinate. By Hasse-Weil for a genus-2 curve, #J(F_p) ~ p², so the
#  space of distinct keys reachable has size ~p² (this was the theory bug in
#  earlier revisions of this file, which assumed ~p "one per α" — wrong: α
#  itself already ranges over ell ~ p² values, and there is no collapse to a
#  p-sized key space along the way).
#
#  The number of D=α·G values actually visited is bounded by |⟨G⟩| = ell, and
#  since ell is chosen as (close to) the largest prime factor of #J(F_p), we
#  have ell = Θ(p²) for a good curve — so the *effective* key space size is
#  min(ell, ~p²) = Θ(p²) either way. Birthday paradox needs O(√N) samples
#  for a collision in a space of size N, so here that's O(√(p²)) = O(p)
#  entries — NOT O(√p). This is exactly why table_cap below defaults to
#  isqrt(ell)+1 rather than isqrt(p)+1: isqrt(ell) ~ isqrt(p²) ~ p already
#  gives the right O(p) sizing. (If ell ever has a large cofactor and is NOT
#  close to #J(F_p), isqrt(ell) degrades gracefully to the true bound
#  min(ell, p²), since the walk can never visit more than ell distinct D's.)
#
#  Both phase-2 and phase-3 keys are drawn from this same pool (the R+S residual
#  when the anchor is the same frozen P).  After O(p) entries in the table the
#  birthday paradox guarantees ~O(1) expected collisions per further step.
#  On a match, the relation
#       P + R + S - 2·∞  ≡  α·G           (phase-2 entry)
#       P + R + S - 2·∞  ≡  α₂·G + β·T   (phase-3 step, same key ⟹ same R+S)
#  subtracts to give (α - α₂)·G ≡ β·T, i.e. k = (α - α₂)·β⁻¹ mod ell.
#
#  BOTH RESIDUAL TYPES
#  ────────────────────
#  • Split (rs_split): key = min/max-ordered pair (R, S) of affine points.
#    We use the NTuple{4,Int} (x_R,y_R,x_S,y_S) with (R,S) lex-sorted so
#    the same unordered pair maps to the same key regardless of which root
#    φ returned first.
#  • Conjugate (!rs_split): key = the NTuple{4,UInt32} Mumford pair of the
#    degree-2 residual (identical representation as in phase2_worker).
#
#  THREADING
#  ─────────
#  Phase 2 is single-threaded (building the shared table is the bottleneck).
#  Phase 3 spawns n_threads independent walkers that share the read-only
#  phase-2 table; the first successful match broadcasts the result.
#
#  EXPORTED
#  ────────
#    sqrt_dlp(G, T, ell; verbose, step_cap, table_size) → Union{Int,Nothing}
#    sqrt_dlp_main(; verbose, step_cap, table_size)      → main entry-point
# =============================================================================

# ---------------------------------------------------------------------------
#  SqrtLP1Table  —  the phase-2 lookup table
#
#  We use two separate Dicts so the key type is concrete (Julia Dict is
#  parametric; a Union key would box).
#    split_table  : NTuple{4,Int}   → Int  (sorted affine pair → α)
#    conj_table   : NTuple{4,UInt32} → Int  (Mumford pair → α)
# ---------------------------------------------------------------------------
struct SqrtLP1Table
    split_table ::Dict{NTuple{4,Int},    Int}
    conj_table  ::Dict{NTuple{4,UInt32}, Int}
end

function SqrtLP1Table(capacity::Int)::SqrtLP1Table
    SqrtLP1Table(
        sizehint!(Dict{NTuple{4,Int},    Int}(), capacity),
        sizehint!(Dict{NTuple{4,UInt32}, Int}(), capacity))
end

@inline function table_size(t::SqrtLP1Table)::Int
    length(t.split_table) + length(t.conj_table)
end

# ---------------------------------------------------------------------------
#  lp1_split_key  —  canonical key for a split (two affine points) residual
#
#  We lex-sort (R, S) so the key is independent of which root φ returned
#  first.  The key is a 4-tuple (xR, yR, xS, yS) with (xR,yR) ≤ (xS,yS).
# ---------------------------------------------------------------------------
@inline function lp1_split_key(R::NTuple{2,Int}, S::NTuple{2,Int})::NTuple{4,Int}
    if R <= S
        return (R[1], R[2], S[1], S[2])
    else
        return (S[1], S[2], R[1], R[2])
    end
end

# ---------------------------------------------------------------------------
#  sqrt_build_phase2!
#
#  Fills the phase-2 table by walking D = α·G through the frozen anchor P.
#
#  Arguments:
#    tbl        — SqrtLP1Table to populate (modified in place)
#    P          — frozen anchor point (NTuple{2,Int})
#    G          — generator (Div2)
#    ell        — group order (Int)
#    table_cap  — stop after storing this many entries (default: isqrt(ell)+1)
#    step_cap   — hard limit on raw walk steps
#    verbose    — print progress lines
#
#  Returns:
#    (n_stored, n_raw_steps, n_valid_steps)
# ---------------------------------------------------------------------------
function sqrt_build_phase2!(
        tbl        ::SqrtLP1Table,
        P          ::NTuple{2,Int},
        G          ::Div2,
        ell        ::Int;
        table_cap  ::Int   = isqrt(ell) + 1,
        step_cap   ::Int   = 50 * table_cap,
        verbose    ::Bool  = true)::NTuple{3,Int}

    t0 = time()
    px, py = P

    # Current walk state: D_cur = alpha_cur · G
    alpha_cur = rand(1:ell-1)
    D_cur     = jac_mul(G, alpha_cur, ell)

    # Precompute a pool of random G-multiples to add each step (β=0)
    POOL = 512
    step_D = Vector{Div2}(undef, POOL)
    step_a = Vector{Int}(undef,  POOL)
    for i in 1:POOL
        a = rand(1:ell-1)
        step_D[i] = jac_mul(G, a, ell)
        step_a[i] = a
    end

    n_raw   = 0
    n_valid = 0
    n_stored_total = 0

    while table_size(tbl) < table_cap && n_raw < step_cap
        n_raw += 1

        # Random G-step (β=0)
        si         = rand(1:POOL)
        D_cur      = jac_add(D_cur, step_D[si])
        alpha_cur  = mod(alpha_cur + step_a[si], ell)

        # Gate: must be a degree-2 divisor
        fp3_deg(D_cur.u) != 2 && continue

        u0 = D_cur.u[1]; u1 = D_cur.u[2]
        v0 = D_cur.v[1]; v1 = D_cur.v[2]

        # Gate: P must not be in the support of D_cur
        upx = fp(fp(px*px) + fp(u1*px) + u0)
        upx == 0 && continue

        # Build φ and recover residual
        phi_c = build_phi_mumford(px, py, u0, u1, v0, v1)
        phi_c === nothing && continue
        a_phi, b_phi, c_phi, _ = phi_c

        res_R, res_S, RS_mumford = phi_residual_mumford(a_phi, b_phi, c_phi, px, u0, u1)
        RS_mumford === SENTINEL_MUMFORD && continue

        n_valid += 1

        if res_R !== SENTINEL_PT
            # Split residual: two affine F_p points
            key = lp1_split_key(res_R, res_S)
            if !haskey(tbl.split_table, key)
                tbl.split_table[key] = alpha_cur
                n_stored_total += 1
            end
        else
            # Conjugate residual: Mumford pair over F_p²
            key = RS_mumford
            if !haskey(tbl.conj_table, key)
                tbl.conj_table[key] = alpha_cur
                n_stored_total += 1
            end
        end
    end

    if verbose
        elapsed = time() - t0
        @printf("[sqrt phase2 | t=%.2fs] raw=%d valid=%d stored=%d (split=%d conj=%d) target=%d\n",
                elapsed, n_raw, n_valid, n_stored_total,
                length(tbl.split_table), length(tbl.conj_table), table_cap)
        flush(stdout)
    end

    return (n_stored_total, n_raw, n_valid)
end

# ---------------------------------------------------------------------------
#  sqrt_phase3_worker
#
#  One β≠0 walk thread.  Reads phase-2 table (read-only), writes to result
#  channel when a collision is found.
#
#  Returns Union{Int,Nothing}: the recovered k, or nothing.
# ---------------------------------------------------------------------------
function sqrt_phase3_worker(
        tid        ::Int,
        P          ::NTuple{2,Int},
        G          ::Div2,
        T          ::Div2,
        ell        ::Int,
        tbl        ::SqrtLP1Table,
        step_cap   ::Int;
        verbose    ::Bool = true)::Union{Int,Nothing}

    t0 = time()
    px, py = P

    # Current walk state: D_cur = alpha_cur·G + beta_cur·T
    alpha_cur = rand(1:ell-1)
    beta_cur  = rand(1:ell-1)
    D_cur     = jac_add(jac_mul(G, alpha_cur, ell),
                        jac_mul(T, beta_cur,  ell))

    # Precompute a mixed pool (for phase 3, steps have both α and β components)
    POOL = 512
    step_D = Vector{Div2}(undef, POOL)
    step_a = Vector{Int}(undef,  POOL)
    step_b = Vector{Int}(undef,  POOL)
    for i in 1:POOL
        a = rand(1:ell-1); b = rand(1:ell-1)
        step_D[i] = jac_add(jac_mul(G, a, ell), jac_mul(T, b, ell))
        step_a[i] = a; step_b[i] = b
    end

    n_raw    = 0
    n_valid  = 0
    n_miss   = 0
    n_hit    = 0
    k_rec    = nothing

    while k_rec === nothing && n_raw < step_cap
        n_raw += 1

        si        = rand(1:POOL)
        D_cur     = jac_add(D_cur, step_D[si])
        alpha_cur = mod(alpha_cur + step_a[si], ell)
        beta_cur  = mod(beta_cur  + step_b[si], ell)

        # Gate: degree-2
        fp3_deg(D_cur.u) != 2 && continue
        # Gate: P not in support
        u0 = D_cur.u[1]; u1 = D_cur.u[2]
        v0 = D_cur.v[1]; v1 = D_cur.v[2]
        upx = fp(fp(px*px) + fp(u1*px) + u0)
        upx == 0 && continue

        phi_c = build_phi_mumford(px, py, u0, u1, v0, v1)
        phi_c === nothing && continue
        a_phi, b_phi, c_phi, _ = phi_c
        res_R, res_S, RS_mumford = phi_residual_mumford(a_phi, b_phi, c_phi, px, u0, u1)
        RS_mumford === SENTINEL_MUMFORD && continue

        n_valid += 1

        # ── Lookup in phase-2 table ────────────────────────────────────────
        alpha_pre = nothing

        if res_R !== SENTINEL_PT
            key = lp1_split_key(res_R, res_S)
            alpha_pre = get(tbl.split_table, key, nothing)
        else
            key = RS_mumford
            alpha_pre = get(tbl.conj_table, key, nothing)
        end

        if alpha_pre === nothing
            n_miss += 1
            continue
        end

        # ── Collision: solve for k ─────────────────────────────────────────
        # Phase-2 relation: P + R+S ≡ α_pre · G
        # Phase-3 relation: P + R+S ≡ α_cur·G + β_cur·T
        # Subtract: 0 ≡ (α_pre - α_cur)·G + (-β_cur)·T
        # ⟹ β_cur · T ≡ (α_pre - α_cur)·G
        # ⟹ k = (α_pre - α_cur) · β_cur⁻¹  mod  ell
        beta_cur == 0 && continue   # degenerate; skip (shouldn't happen for rand)

        diff_al  = mod(alpha_pre - alpha_cur, ell)
        beta_inv = powermod(beta_cur, ell - 2, ell)
        k_cand   = Int(mod(BigInt(diff_al) * BigInt(beta_inv), ell))

        # Verify
        if jac_mul(G, k_cand, ell) == T
            n_hit += 1
            k_rec = k_cand
            # (verification passed — break out of loop)
            break
        end
        # If verify fails: false positive (hash collision or gauge artefact); continue
    end

    if verbose
        elapsed = time() - t0
        @printf("[sqrt phase3 tid=%d | t=%.2fs] raw=%d valid=%d miss=%d hit=%d k=%s\n",
                tid, elapsed, n_raw, n_valid, n_miss, n_hit,
                k_rec === nothing ? "none" : string(k_rec))
        flush(stdout)
    end

    return k_rec
end

# ---------------------------------------------------------------------------
#  sqrt_dlp
#
#  Top-level solver.  Builds the phase-2 table once (amortized over all
#  targets — phase 2 has no T dependence), then runs phase-3 for each target.
#
#  Single-target form:   sqrt_dlp(G, T, ell)  → Union{Int,Nothing}
#  Multi-target form:    sqrt_dlp(G, targets, ell)
#                        where targets::Vector{Tuple{Div2,Union{Int,Nothing}}}
#                        i.e. [(T_i, k_true_i), ...]  — k_true_i for verification,
#                        or nothing if unknown.
#                        Returns Vector{Union{Int,Nothing}}.
#
#  Arguments:
#    G          — generator (Div2)
#    T_or_targets — single Div2 target, or Vector of (T, k_true) pairs
#    ell        — prime group order (Int)
#    table_size — phase-2 table cap (default: isqrt(ell) + 1)
#    step_cap   — per-thread phase-3 step limit (per target)
#    n_threads  — number of phase-3 threads per target (default: Threads.nthreads())
#    verbose    — progress output
# ---------------------------------------------------------------------------

# ── Internal: solve a list of targets against an already-built table ─────────
#
#  Parallelism is over targets: one thread per target, each running an
#  independent phase-3 walk against the shared read-only table.  No locking,
#  no atomic signalling — threads never touch each other's state.
#  tid is used only for the verbose log line.
function _sqrt_dlp_phase3_all(
        targets    ::Vector{<:Tuple{Div2, <:Union{Int,Nothing}}},
        P          ::NTuple{2,Int},
        G          ::Div2,
        ell        ::Int,
        tbl        ::SqrtLP1Table;
        step_cap   ::Int  = 20 * table_size(tbl),
        verbose    ::Bool = true)::Vector{Union{Int,Nothing}}

    n     = length(targets)
    all_k = Vector{Union{Int,Nothing}}(undef, n)
    t_all = time()

    @sync for ti in 1:n
        Threads.@spawn begin
            T_i, k_true_i = targets[ti]
            k_rec = sqrt_phase3_worker(
                ti, P, G, T_i, ell, tbl, step_cap;
                verbose = verbose)
            all_k[ti] = k_rec

            if verbose
                k_s = k_rec === nothing ? "none" : string(k_rec)
                if k_true_i !== nothing
                    match_s = k_rec == k_true_i ? "YES ✓" : (k_rec === nothing ? "MISS" : "MISMATCH ✗")
                    @printf("  [target %d/%d] k=%s  true=%d  %s\n",
                            ti, n, k_s, k_true_i, match_s)
                else
                    @printf("  [target %d/%d] k=%s\n", ti, n, k_s)
                end
                flush(stdout)
            end
        end
    end

    if verbose
        n_ok = count(!isnothing, all_k)
        @printf("  phase3 all targets: %d/%d solved  t=%.2fs\n", n_ok, n, time() - t_all)
        flush(stdout)
    end
    return all_k
end

# ── Single-target convenience wrapper ────────────────────────────────────────
function sqrt_dlp(
        G          ::Div2,
        T          ::Div2,
        ell        ::Int;
        table_size ::Int  = isqrt(ell) + 1,
        step_cap   ::Int  = 20 * table_size,
        verbose    ::Bool = true)::Union{Int,Nothing}

    k_vec = sqrt_dlp_multi(G, [(T, nothing)], ell;
                           table_size=table_size, step_cap=step_cap,
                           verbose=verbose)
    return k_vec[1]
end

# ── Multi-target entry point ──────────────────────────────────────────────────
function sqrt_dlp_multi(
        G          ::Div2,
        targets    ::Vector{<:Tuple{Div2, <:Union{Int,Nothing}}},
        ell        ::Int;
        table_size ::Int  = isqrt(ell) + 1,
        step_cap   ::Int  = 20 * table_size,
        verbose    ::Bool = true)::Vector{Union{Int,Nothing}}

    t0 = time()
    n  = length(targets)

    # ── Pick frozen anchor P ──────────────────────────────────────────────────
    pts = sample_curve_points(200)
    isempty(pts) && throw(ErrorException("sqrt_dlp_multi: no rational affine points on curve"))
    P = pts[rand(1:length(pts))]

    if verbose
        @printf("\n══ sqrt DLP  ell=%d  targets=%d  table_cap=%d  step_cap=%d  threads=%d ══\n",
                ell, n, table_size, step_cap, Threads.nthreads())
        @printf("  anchor P = (%d, %d)\n", P[1], P[2])
        flush(stdout)
    end

    # ── Phase 2: build the table once (no T dependence) ──────────────────────
    t_ph2 = time()
    tbl = SqrtLP1Table(table_size)
    n_stored, n_raw2, n_valid2 = sqrt_build_phase2!(
        tbl, P, G, ell;
        table_cap = table_size,
        step_cap  = 50 * table_size,
        verbose   = verbose)

    if verbose
        @printf("  phase2 done: %d entries in %.2fs  (raw=%d valid=%d)\n",
                n_stored, time() - t_ph2, n_raw2, n_valid2)
        flush(stdout)
    end
    n_stored < cld(table_size, 2) &&
        @printf("  [WARN] table only %d/%d full — birthday probability reduced\n",
                n_stored, table_size)

    # ── Phase 3: one pass per target, threads within each ────────────────────
    all_k = _sqrt_dlp_phase3_all(targets, P, G, ell, tbl;
                                  step_cap=step_cap, verbose=verbose)

    if verbose
        n_ok = count(!isnothing, all_k)
        @printf("\n  phase3 summary: %d/%d targets solved  total_time=%.2fs\n",
                n_ok, n, time() - t0)
        flush(stdout)
    end

    return all_k
end

# ---------------------------------------------------------------------------
#  sqrt_dlp_main
#
#  Self-contained entry point: bootstraps G, picks random k, runs sqrt_dlp,
#  checks result.
# ---------------------------------------------------------------------------
function sqrt_dlp_main(;
        verbose    ::Bool = true,
        table_size ::Union{Int,Nothing} = nothing,
        step_cap   ::Union{Int,Nothing} = nothing,
        n_targets  ::Int  = 1)

    println("="^70)
    println("  trial3_sqrt.jl — O(p)-time DLP via birthday LP1 collision (≈ √ell)")
    println("="^70)

    # Bootstrap G and ell
    pts = sample_curve_points(200)
    isempty(pts) && throw(ErrorException("No rational points on curve"))
    G, ell = frobenius_find_ell_generator(pts)
    @printf("  ell = %d  (%.1f bits)\n", ell, log2(ell))

    # Generate random targets
    targets = [(jac_mul(G, rand(2:ell-1), ell), k) for k in
               [rand(2:ell-1) for _ in 1:n_targets]]
    # Rebuild as proper typed vector
    targets_typed = Tuple{Div2, Union{Int,Nothing}}[
        (jac_mul(G, k, ell), k) for k in [rand(2:ell-1) for _ in 1:n_targets]]
    for (i, (T, k)) in enumerate(targets_typed)
        @printf("  target %d: k_true = %d\n", i, k)
    end
    println()

    local ts   = table_size === nothing ? isqrt(ell) + 1 : table_size
    local scap = step_cap   === nothing ? 20 * ts         : step_cap

    all_k = sqrt_dlp_multi(G, targets_typed, ell;
                           table_size = ts,
                           step_cap   = scap,
                           verbose    = verbose)

    println()
    println("── Summary ─────────────────────────────────────────────────────────")
    n_ok = 0
    for (i, (k_rec, (_, k_true))) in enumerate(zip(all_k, targets_typed))
        if k_rec !== nothing
            match = k_rec == k_true
            match && (n_ok += 1)
            @printf("  target %d: k_rec=%-10d  k_true=%-10d  %s\n",
                    i, k_rec, k_true, match ? "YES ✓" : "MISMATCH ✗")
            match || throw(ErrorException(
                "sqrt_dlp_main: target $i mismatch k_rec=$k_rec k_true=$k_true"))
        else
            @printf("  target %d: NOT RECOVERED\n", i)
        end
    end
    @printf("  %d / %d targets solved\n", n_ok, n_targets)
    println("="^70)
end

# ---------------------------------------------------------------------------
#  CLI entry point (optional)
# ---------------------------------------------------------------------------
if abspath(PROGRAM_FILE) == @__FILE__
    # Parse simple CLI: --table-size N --step-cap N
    # Wrapped in let to avoid soft-scope warnings for ts / scap / i.
    let
        local ts   = nothing
        local scap = nothing
        local i    = 1
        while i <= length(ARGS)
            if ARGS[i] == "--table-size" && i + 1 <= length(ARGS)
                ts = parse(Int, ARGS[i+1]); i += 2
            elseif ARGS[i] == "--step-cap" && i + 1 <= length(ARGS)
                scap = parse(Int, ARGS[i+1]); i += 2
            else
                i += 1
            end
        end
        sqrt_dlp_main(; table_size=ts, step_cap=scap)
    end
end
