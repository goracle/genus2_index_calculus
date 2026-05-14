# =============================================================================
#  early_solve_monitor.jl  --  Online phase-transition diagnostics for the
#                               index-calculus relation matrix.
#
#  Implements the three signals identified empirically:
#
#    (1) DSU giant-component fraction  (cheap, updated per-relation)
#         largest_component / nF  >  0.5  →  connectivity transition
#         Note: this lags the actual solve threshold; treat as informational.
#
#    (2) 2-core size  (maintained incrementally via column-degree tracking)
#         core_rows > core_cols  →  dense-solve regime entered
#         core_cols > 0          →  kernel plausible
#
#    (3) Betti number b₁ = m − rank(M_m)  (exact, computed on demand)
#         b₁ > 0  →  first nontrivial kernel exists; try to solve NOW
#
#  Threading model:
#    EarlySolveMonitor is NOT thread-safe by design — it is intended to be
#    maintained by a single coordinator thread (or called under a lock).
#    In the current architecture the incremental solve loop in
#    index_calculus_walk (trial3_fixed.jl) already runs single-threaded after
#    phase-2 merging, so this is fine.
#
#  Usage:
#    mon = EarlySolveMonitor(nF, ell)
#    monitor_add_relation!(mon, support_cols)   # called per new relation
#    sig = monitor_check(mon, rel_rows, alpha_vec, beta_vec)
#    if sig.b1_positive; try_solve(); end
# =============================================================================

# ---------------------------------------------------------------------------
#  EarlySolveMonitor
# ---------------------------------------------------------------------------
mutable struct EarlySolveMonitor
    nF      ::Int
    ell     ::Int

    # ── DSU (union-find) on FB columns ──────────────────────────────────────
    dsu_parent  ::Vector{Int}
    dsu_rank    ::Vector{Int}
    dsu_size    ::Vector{Int}   # size of the component rooted here
    largest_comp::Int           # cached max component size

    # ── Column-degree tracking for 2-core estimation ─────────────────────────
    col_degree  ::Vector{Int}   # how many active rows touch each column
    col_to_rows ::Vector{Vector{Int}}   # column → list of row indices
    row_support ::Vector{Vector{Int}}   # row index → sorted column support
    row_active  ::Vector{Bool}
    col_active  ::Vector{Bool}
    core_cols   ::Int
    core_rows   ::Int
    n_rows      ::Int           # total rows added so far

    # ── Betti tracking ───────────────────────────────────────────────────────
    last_rank   ::Int           # rank of matrix at last full rank computation
    last_rank_m ::Int           # m at which last_rank was computed
    b1          ::Int           # cached b₁ = m − rank  (lower bound when stale)

    # ── Checkpointing ────────────────────────────────────────────────────────
    next_check_rows ::Int       # next row count at which to do a rank check
    check_interval  ::Int       # how many rows between checks
    betti_history   ::Vector{Tuple{Int,Int}}  # (m, b₁) snapshots
end

function EarlySolveMonitor(nF::Int, ell::Int; check_interval::Int = 10)
    check_interval > 0 || throw(ArgumentError("check_interval must be positive"))
    EarlySolveMonitor(
        nF, ell,
        collect(1:nF),          # dsu_parent
        zeros(Int, nF),         # dsu_rank
        ones(Int, nF),          # dsu_size
        1,                      # largest_comp
        zeros(Int, nF),         # col_degree
        [Int[] for _ in 1:nF],  # col_to_rows
        Vector{Int}[],          # row_support
        Bool[],                 # row_active
        trues(nF),              # col_active
        0,                      # core_cols
        0,                      # core_rows
        0,                      # n_rows
        0,                      # last_rank
        0,                      # last_rank_m
        0,                      # b1
        check_interval,         # next_check_rows
        check_interval,         # check_interval
        Tuple{Int,Int}[],       # betti_history
    )
end

# ---------------------------------------------------------------------------
#  DSU helpers (path-compressed, union-by-rank)
# ---------------------------------------------------------------------------
function _dsu_find!(mon::EarlySolveMonitor, x::Int)::Int
    while mon.dsu_parent[x] != x
        mon.dsu_parent[x] = mon.dsu_parent[mon.dsu_parent[x]]   # path halving
        x = mon.dsu_parent[x]
    end
    return x
end

function _dsu_union!(mon::EarlySolveMonitor, a::Int, b::Int)
    ra = _dsu_find!(mon, a)
    rb = _dsu_find!(mon, b)
    ra == rb && return
    # Union by rank; merge smaller into larger
    if mon.dsu_rank[ra] < mon.dsu_rank[rb]
        ra, rb = rb, ra
    end
    mon.dsu_parent[rb] = ra
    mon.dsu_size[ra]  += mon.dsu_size[rb]
    mon.dsu_size[rb]   = 0
    if mon.dsu_rank[ra] == mon.dsu_rank[rb]
        mon.dsu_rank[ra] += 1
    end
    if mon.dsu_size[ra] > mon.largest_comp
        mon.largest_comp = mon.dsu_size[ra]
    end
end

# ---------------------------------------------------------------------------
#  monitor_add_relation!
#
#  Call once per new relation as it arrives.  Updates DSU and degree tracking.
#  Does NOT recompute the 2-core (that is done lazily in monitor_check).
# ---------------------------------------------------------------------------
function monitor_add_relation!(mon::EarlySolveMonitor,
                                support::AbstractVector{Int})
    m = mon.n_rows + 1
    mon.n_rows = m
    push!(mon.row_support, sort(collect(support)))
    push!(mon.row_active, true)

    # ── DSU update ───────────────────────────────────────────────────────────
    valid = [c for c in support if 1 <= c <= mon.nF]
    if length(valid) >= 2
        c1 = valid[1]
        for i in 2:length(valid)
            _dsu_union!(mon, c1, valid[i])
        end
    end

    # ── Degree update ─────────────────────────────────────────────────────────
    for c in valid
        mon.col_degree[c] += 1
        push!(mon.col_to_rows[c], m)
    end
end

# ---------------------------------------------------------------------------
#  _recompute_core!
#
#  Full leaf-stripping from scratch on the current active set.
#  O(m · avg_row_weight) — called at most every check_interval rows.
# ---------------------------------------------------------------------------
function _recompute_core!(mon::EarlySolveMonitor)
    nF   = mon.nF
    m    = mon.n_rows

    # Rebuild per-column degrees and row→column map from scratch.
    # (Incremental deg tracking above suffices for DSU, but peeling needs
    #  clean degree counts that exclude already-peeled rows.)
    deg        = zeros(Int, nF)
    col2rows   = [Int[] for _ in 1:nF]
    for i in 1:m
        for c in mon.row_support[i]
            deg[c] += 1
            push!(col2rows[c], i)
        end
    end

    active_col = trues(nF)
    active_row = trues(m)
    q = [j for j in 1:nF if deg[j] <= 1]

    while !isempty(q)
        j = pop!(q)
        active_col[j] || continue
        deg[j] > 1 && continue
        active_col[j] = false
        for ri in col2rows[j]
            active_row[ri] || continue
            active_row[ri] = false
            for k in mon.row_support[ri]
                k == j || continue
                !active_col[k] && continue
                deg[k] -= 1
                deg[k] <= 1 && push!(q, k)
            end
        end
    end

    mon.col_active = active_col
    mon.row_active = active_row
    mon.core_cols  = count(identity, active_col)
    mon.core_rows  = count(identity, active_row)
end

# ---------------------------------------------------------------------------
#  _incremental_rank
#
#  Compute rank of the relation matrix over GF(ell) using the *core* rows
#  only (the 2-core of the column graph).  For the early-stop use-case we
#  only need to know whether rank < m (i.e. b₁ > 0); we return the actual
#  rank for diagnostics.
#
#  Uses Nemo/FLINT when available, pure-Julia fallback otherwise.
# ---------------------------------------------------------------------------
function _incremental_rank(rel_rows   ::Vector{Dict{Int,Int}},
                            core_row_indices::Vector{Int},
                            nF         ::Int,
                            ell        ::Int)::Int
    rows = rel_rows[core_row_indices]
    isempty(rows) && return 0

    m2 = length(rows)

    # Build compressed column index (only columns that appear in core rows).
    col_set = Set{Int}()
    for r in rows, (j, _) in r
        1 <= j <= nF && push!(col_set, j)
    end
    col_list  = sort(collect(col_set))
    col_remap = Dict(c => i for (i, c) in enumerate(col_list))
    n2 = length(col_list)
    n2 == 0 && return 0

    try
        F      = Nemo.GF(ell)
        Mn     = zero_matrix(F, m2, n2)
        for (i, r) in enumerate(rows)
            for (j, v) in r
                haskey(col_remap, j) || continue
                Mn[i, col_remap[j]] = mod(v, ell)
            end
        end
        return rank(Mn)
    catch e
        @warn "_incremental_rank: Nemo failed ($e), using pure-Julia"
    end

    # Pure-Julia fallback: row-echelon on a dense (m2 × n2) matrix.
    A    = zeros(Int, m2, n2)
    for (i, r) in enumerate(rows)
        for (j, v) in r
            haskey(col_remap, j) || continue
            A[i, col_remap[j]] = mod(v, ell)
        end
    end
    rk   = 0
    prow = 1
    for col in 1:n2
        piv = 0
        for r in prow:m2
            A[r, col] != 0 && (piv = r; break)
        end
        piv == 0 && continue
        piv != prow && (A[[prow, piv], :] = A[[piv, prow], :])
        inv_v = powermod(A[prow, col], ell - 2, ell)
        for c in col:n2; A[prow, c] = mod(A[prow, c] * inv_v, ell); end
        for r in 1:m2
            r == prow && continue
            f = A[r, col]; f == 0 && continue
            for c in col:n2; A[r, c] = mod(A[r, c] - f * A[prow, c], ell); end
        end
        rk   += 1
        prow += 1
        prow > m2 && break
    end
    return rk
end

# ---------------------------------------------------------------------------
#  MonitorSignal — result returned by monitor_check
# ---------------------------------------------------------------------------
struct MonitorSignal
    m               ::Int
    giant_frac      ::Float64   # largest_comp / nF
    giant_formed    ::Bool      # giant_frac > 0.5
    core_cols       ::Int
    core_rows       ::Int
    core_solvable   ::Bool      # core_rows > core_cols (dense-solve regime)
    core_kernel_plausible::Bool # core_cols > 0
    b1              ::Int       # b₁ = m − rank (0 ⟹ no kernel yet)
    b1_positive     ::Bool      # b₁ > 0 ⟹ try solve now
    rank_computed   ::Bool      # was b₁ freshly computed this call?
    support2_found  ::Bool      # any relation pair share identical support
end

# ---------------------------------------------------------------------------
#  monitor_check
#
#  Called at each chunk boundary in the incremental solve loop.
#  Returns a MonitorSignal; if sig.b1_positive the caller should immediately
#  attempt left_kernel_all on the current relation set.
#
#  Arguments:
#    mon         — the monitor (updated in-place with core/rank cache)
#    rel_rows    — ALL relation rows collected so far (sparse dicts)
#    alpha_vec, beta_vec — coefficients (not used here; passed for completeness)
#    force_rank  — bypass the check_interval gate and always compute rank
# ---------------------------------------------------------------------------
function monitor_check(mon       ::EarlySolveMonitor,
                        rel_rows  ::Vector{Dict{Int,Int}},
                        alpha_vec ::Vector{Int},
                        beta_vec  ::Vector{Int};
                        force_rank::Bool = false,
                        verbose   ::Bool = true)::MonitorSignal

    m    = length(rel_rows)
    m == 0 && return MonitorSignal(0, 0.0, false, 0, 0, false, false, 0, false, false, false)

    # Sync n_rows (caller may batch-add without calling monitor_add_relation!
    # for phase-1 rows — handle gracefully).
    if mon.n_rows < m
        for i in (mon.n_rows + 1):m
            sup = [j for (j, _) in rel_rows[i] if 1 <= j <= mon.nF]
            monitor_add_relation!(mon, sup)
        end
    end

    # ── (1) Giant component ───────────────────────────────────────────────────
    giant_frac   = mon.largest_comp / mon.nF
    giant_formed = giant_frac > 0.5

    # ── (2) 2-core ───────────────────────────────────────────────────────────
    # Recompute from scratch every check_interval rows.
    if m >= mon.next_check_rows || force_rank
        _recompute_core!(mon)
        mon.next_check_rows = m + mon.check_interval
    end

    core_kernel_plausible = mon.core_cols > 0
    core_solvable         = mon.core_rows > mon.core_cols

    # ── (3) Betti b₁ ─────────────────────────────────────────────────────────
    rank_computed = false
    if (core_kernel_plausible && m >= mon.next_check_rows - mon.check_interval) ||
       force_rank
        core_idx = [i for i in 1:m if i <= length(mon.row_active) && mon.row_active[i]]
        if !isempty(core_idx)
            rk = _incremental_rank(rel_rows, core_idx, mon.nF, mon.ell)
            b1 = length(core_idx) - rk
            mon.last_rank   = rk
            mon.last_rank_m = m
            mon.b1          = b1
            rank_computed   = true
            push!(mon.betti_history, (m, b1))
        end
    end

    b1          = mon.b1
    b1_positive = b1 > 0

    # ── (4) Support-2 collision scan (cheap heuristic) ────────────────────────
    # Check if any two rows share an identical 2-element support — this is the
    # "accidental duplicate-edge collision" that produced the empirical T_ker=102
    # result.  Only scan the last check_interval rows against all previous.
    support2_found = false
    if m >= 2
        support2_set = Set{Tuple{Int,Int}}()
        for i in max(1, m - mon.check_interval):m
            sup = mon.row_support[i]
            length(sup) == 2 || continue
            key = (sup[1], sup[2])
            if key in support2_set
                support2_found = true
                break
            end
            push!(support2_set, key)
        end
    end

    if verbose
        @printf("  [EarlySolveMonitor | m=%d] giant=%.3f(%s) core=%d/%d rows=%d solvable=%s b1=%d%s%s\n",
                m,
                giant_frac, giant_formed ? "✓" : "·",
                mon.core_cols, mon.nF, mon.core_rows,
                core_solvable ? "✓" : "·",
                b1, rank_computed ? " [rank recomputed]" : "",
                support2_found ? " ⚡support-2 collision!" : "")
        flush(stdout)
    end

    return MonitorSignal(m, giant_frac, giant_formed,
                         mon.core_cols, mon.core_rows,
                         core_solvable, core_kernel_plausible,
                         b1, b1_positive, rank_computed, support2_found)
end

# ---------------------------------------------------------------------------
#  monitor_print_history
#
#  Print the Betti trace captured during a run — directly analogous to the
#  "m=101 b₁=0 / m=102 b₁=1" output described in the GPT analysis.
# ---------------------------------------------------------------------------
function monitor_print_history(mon::EarlySolveMonitor)
    println("Betti trace (EarlySolveMonitor):")
    isempty(mon.betti_history) && println("  (no rank computations recorded)")
    for (m, b1) in mon.betti_history
        @printf("  m=%d  b₁=%d%s\n", m, b1, b1 > 0 ? "  ← first kernel" : "")
    end
    flush(stdout)
end

# ---------------------------------------------------------------------------
#  Integration helper: build a monitor from an already-collected rel_rows.
#  Use this in the post-walk incremental solve loop when phase-2 is complete.
# ---------------------------------------------------------------------------
function build_monitor_from_relations(rel_rows ::Vector{Dict{Int,Int}},
                                       nF       ::Int,
                                       ell      ::Int;
                                       check_interval::Int = max(1, length(rel_rows) ÷ 20))::EarlySolveMonitor
    check_interval > 0 || throw(ArgumentError("check_interval must be positive, got $check_interval"))
    mon = EarlySolveMonitor(nF, ell; check_interval=check_interval)
    for i in eachindex(rel_rows)
        sup = [j for (j, _) in rel_rows[i] if 1 <= j <= nF]
        monitor_add_relation!(mon, sup)
    end
    return mon
end
