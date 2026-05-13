# =============================================================================
#  trial3_linalg.jl  --  Linear algebra over GF(ell) and matrix diagnostics.
#
#  Functions:
#    left_kernel_all       — compute the full left null-space of the relation
#                            matrix over GF(ell) via Nemo/FLINT (with a
#                            pure-Julia fallback).
#    analyze_relation_matrix — sparsity, connectivity, and peel statistics.
#    spectral_gap_report   — normalized adjacency spectrum of the column
#                            co-occurrence graph.
#    asymptotic_report     — scaling diagnostics over relation-count prefixes.
# =============================================================================

# ---------------------------------------------------------------------------
#  left_kernel_all
#
#  Returns ALL left null vectors of the (m × n) relation matrix R over GF(ell),
#  where m = length(rel_rows) and n = nF.
#
#  Strategy: build Rᵀ (n × m) and compute its right null-space via Nemo's
#  dense FLINT backend.  Building cell-by-cell avoids materialising the full
#  n × m dense buffer in one allocation — at n=10k, m=11k that would be
#  ~880 MB.  Falls back to pure-Julia augmented-matrix elimination if Nemo
#  is unavailable or throws.
# ---------------------------------------------------------------------------
function left_kernel_all(rel_rows::Vector{Dict{Int,Int}}, nF::Int, ell::Int)::Vector{Vector{Int}}
    m = length(rel_rows)
    n = nF
    m == 0 && return Vector{Int}[]

    # ── Nemo / FLINT path ──────────────────────────────────────────────────
    try
        F       = Nemo.GF(ell)
        Rnemo_t = zero_matrix(F, n, m)   # n × m transpose
        for i in 1:m, (j, v) in rel_rows[i]
            1 <= j <= n || continue
            Rnemo_t[j, i] = mod(v, ell)
        end

        nu, K = nullspace(Rnemo_t)
        Rnemo_t = nothing              # release before iterating K

        result = Vector{Int}[]
        for col in 1:nu
            γ = [Int(lift(ZZ, K[row, col])) for row in 1:m]
            any(!=(0), γ) && push!(result, γ)
        end
        return result
    catch e
        @warn "Nemo nullspace failed ($e); falling back to pure-Julia."
    end

    # ── Pure-Julia fallback — augmented row reduction [I | R] ──────────────
    # Any row that becomes [γ | 0 … 0] contributes γ to the left kernel.
    aug = zeros(Int, m, m + n)
    for i in 1:m
        aug[i, i] = 1
        for (j, v) in rel_rows[i]
            1 <= j <= n || continue
            aug[i, m + j] = mod(aug[i, m + j] + v, ell)
        end
    end

    prow = 1
    for col in (m + 1):(m + n)
        # Find pivot in column `col` at or below `prow`.
        piv = 0
        for r in prow:m
            aug[r, col] != 0 && (piv = r; break)
        end
        piv == 0 && continue

        piv != prow && (aug[[prow, piv], :] = aug[[piv, prow], :])

        inv_val = powermod(aug[prow, col], ell - 2, ell)
        for c in 1:(m + n)
            aug[prow, c] = mod(aug[prow, c] * inv_val, ell)
        end

        for r in 1:m
            r == prow && continue
            factor = aug[r, col]
            factor == 0 && continue
            for c in 1:(m + n)
                aug[r, c] = mod(aug[r, c] - factor * aug[prow, c], ell)
            end
        end

        prow += 1
        prow > m && break
    end

    # Rows whose R-block (columns m+1 … m+n) is all-zero give kernel vectors
    # from their I-block (columns 1 … m).
    result = Vector{Int}[]
    for r in 1:m
        all(aug[r, c] == 0 for c in (m + 1):(m + n)) || continue
        γ = aug[r, 1:m]
        any(!=(0), γ) && push!(result, γ)
    end
    return result
end

# ---------------------------------------------------------------------------
#  analyze_relation_matrix
#
#  Reports three things about the m × nF sparse relation matrix:
#    1. Row/column sparsity statistics (weight histogram, column degrees).
#    2. Column co-occurrence graph: connected components via union-find.
#    3. Leaf-stripping / peeling core: after iteratively removing degree-≤1
#       columns (and the rows touching them), what fraction of the matrix
#       remains?  A small core means sparse elimination can do a lot of work
#       before any dense solve.
# ---------------------------------------------------------------------------
function analyze_relation_matrix(rel_rows::Vector{Dict{Int,Int}}, nF::Int; verbose::Bool=true)
    nrel = length(rel_rows)
    nrel == 0 && return nothing

    supports    = Vector{Vector{Int}}(undef, nrel)
    col_to_rows = [Int[] for _ in 1:nF]
    coldeg      = zeros(Int, nF)
    row_hist    = Dict{Int,Int}()
    total_nz    = 0

    for i in 1:nrel
        cols = [j for (j, v) in rel_rows[i] if v != 0 && 1 <= j <= nF]
        sort!(cols)
        supports[i] = cols
        w = length(cols)
        row_hist[w] = get(row_hist, w, 0) + 1
        total_nz += w
        for j in cols
            coldeg[j] += 1
            push!(col_to_rows[j], i)
        end
    end

    # --- Column-degree statistics ---
    deg_sorted  = sort(coldeg)
    zero_cols   = count(==(0), coldeg)
    deg1_cols   = count(==(1), coldeg)
    deg2_cols   = count(==(2), coldeg)
    avg_w       = total_nz / nrel
    density     = total_nz / (nrel * nF)

    # --- Connected components of the column co-occurrence graph (union-find) ---
    parent = collect(1:nF)
    rnk    = zeros(Int, nF)

    function findroot(x::Int)::Int
        y = x
        while parent[y] != y; y = parent[y]; end
        while parent[x] != x; px = parent[x]; parent[x] = y; x = px; end
        return y
    end

    function unite(a::Int, b::Int)
        ra = findroot(a); rb = findroot(b)
        ra == rb && return
        if     rnk[ra] < rnk[rb]; parent[ra] = rb
        elseif rnk[ra] > rnk[rb]; parent[rb] = ra
        else                       parent[rb] = ra; rnk[ra] += 1
        end
    end

    for cols in supports
        length(cols) <= 1 && continue
        c1 = cols[1]
        for k in 2:length(cols); unite(c1, cols[k]); end
    end

    comp_sizes = Dict{Int,Int}()
    for j in 1:nF
        r = findroot(j)
        comp_sizes[r] = get(comp_sizes, r, 0) + 1
    end
    comps          = sort(collect(values(comp_sizes)), rev=true)
    ncomp          = length(comps)
    largest_comp   = isempty(comps) ? 0 : comps[1]
    singleton_comps = count(==(1), comps)

    # --- Peeling / leaf-stripping core ---
    # Repeatedly remove columns with degree ≤ 1 (and their incident rows),
    # decrementing degrees of newly-exposed columns.  The surviving core is
    # where a dense or iterative solver must do the real work.
    active_col = trues(nF)
    active_row = trues(nrel)
    deg        = copy(coldeg)
    q          = [j for j in 1:nF if deg[j] <= 1]

    while !isempty(q)
        j = pop!(q)
        active_col[j] || continue
        deg[j] > 1 && continue
        active_col[j] = false
        for ri in col_to_rows[j]
            active_row[ri] || continue
            active_row[ri] = false
            for k in supports[ri]
                k == j || !active_col[k] && continue
                deg[k] -= 1
                deg[k] <= 1 && push!(q, k)
            end
        end
    end

    core_cols = count(identity, active_col)
    core_rows = count(identity, active_row)

    if verbose
        println("Matrix diagnostics for LA:")
        @printf("  rows = %d, cols = %d, nonzeros = %d, avg row weight = %.3f, density = %.4g\n",
                nrel, nF, total_nz, avg_w, density)

        row_keys  = sort(collect(keys(row_hist)))
        println("  row-weight histogram: ", join(["$k:$(row_hist[k])" for k in row_keys], ", "))

        @printf("  column degrees: zero=%d, deg1=%d, deg2=%d, min=%d, median=%d, max=%d\n",
                zero_cols, deg1_cols, deg2_cols,
                isempty(deg_sorted) ? 0 : deg_sorted[1],
                isempty(deg_sorted) ? 0 : deg_sorted[(length(deg_sorted)+1) ÷ 2],
                isempty(deg_sorted) ? 0 : deg_sorted[end])
        @printf("  component graph: %d components, largest=%d, singletons=%d\n",
                ncomp, largest_comp, singleton_comps)
        @printf("  peel/core estimate: core cols = %d, core rows = %d, peeled cols = %d\n",
                core_cols, core_rows, nF - core_cols)
        largest_comp < nF &&
            @printf("  note: matrix is block-disconnected — sub-problems can be split off\n")
        core_cols < nF &&
            @printf("  note: leaf-stripping removes %d/%d columns before any dense solve\n",
                    nF - core_cols, nF)
    end

    return (supports=supports, row_hist=row_hist, coldeg=coldeg, components=comps,
            core_cols=core_cols, core_rows=core_rows, density=density, total_nz=total_nz)
end

# ---------------------------------------------------------------------------
#  spectral_gap_report
#
#  Build the weighted co-occurrence graph on factor-base columns (each relation
#  contributes a complete subgraph on its support), then compute the second
#  eigenvalue λ₂ of the normalised adjacency matrix B = D^{-1/2} W D^{-1/2}.
#  Spectral gap = 1 - λ₂: a larger gap indicates better expansion / mixing,
#  which generally predicts that sparse iterative LA will converge faster.
#
#  Evaluates at several relation-count prefixes chosen on a geometric grid.
# ---------------------------------------------------------------------------
function spectral_gap_report(rel_rows::Vector{Dict{Int,Int}}, nF::Int;
                             prefixes::Vector{Int}=Int[],
                             verbose::Bool=true)
    nrel = length(rel_rows)
    nrel == 0 && return nothing

    prefixes = isempty(prefixes) ? unique(sort(Int[
        min(nrel, max(50,  nrel ÷ 8)),
        min(nrel, max(100, nrel ÷ 4)),
        min(nrel, max(200, nrel ÷ 2)),
        nrel,
    ])) : unique(sort(filter(x -> 1 <= x <= nrel, prefixes)))

    function gap_for_prefix(m::Int)
        W = zeros(Float64, nF, nF)
        for i in 1:m
            cols = [j for (j, v) in rel_rows[i] if v != 0 && 1 <= j <= nF]
            length(cols) <= 1 && continue
            w = 1.0 / (length(cols) - 1)
            for a in 1:length(cols)-1, b in a+1:length(cols)
                i1 = cols[a]; i2 = cols[b]
                W[i1, i2] += w; W[i2, i1] += w
            end
        end
        deg = vec(sum(W, dims=2))
        nz  = findall(>(0.0), deg)
        length(nz) <= 1 && return (m=m, gap=NaN, lambda2=NaN, lambda1=NaN, comp_size=length(nz))
        Ws       = W[nz, nz]
        ds       = deg[nz]
        invsqrt  = Diagonal(1.0 ./ sqrt.(ds))
        B        = invsqrt * Ws * invsqrt
        vals     = sort(real.(eigvals(Symmetric(B))), rev=true)
        λ1       = vals[1]
        λ2       = length(vals) >= 2 ? vals[2] : NaN
        return (m=m, gap=1.0-λ2, lambda2=λ2, lambda1=λ1, comp_size=length(nz))
    end

    stats = map(gap_for_prefix, prefixes)
    if verbose
        println("Spectral gap diagnostics (normalized adjacency of column graph):")
        for s in stats
            if isnan(s.gap)
                @printf("  rows=%d: insufficient support to estimate gap\n", s.m)
            else
                @printf("  rows=%d: active cols=%d, lambda1=%.6f, lambda2=%.6f, gap=%.6f\n",
                        s.m, s.comp_size, s.lambda1, s.lambda2, s.gap)
            end
        end
        if length(stats) >= 2 && !isnan(stats[end].gap) && !isnan(stats[1].gap)
            @printf("  gap change: %.6f -> %.6f\n", stats[1].gap, stats[end].gap)
        end
    end
    return stats
end

# ---------------------------------------------------------------------------
#  asymptotic_report
#
#  Scaling diagnostics aimed at p-dependent behaviour rather than per-instance
#  correctness.  At several relation-count prefixes it reports:
#    - total nonzeros, average row weight, density,
#    - peel/core size after leaf-stripping,
#    - spectral gap,
#    - log-log power-law fit exponents (total_nz ~ rows^a, etc.).
# ---------------------------------------------------------------------------
function asymptotic_report(rel_rows::Vector{Dict{Int,Int}}, nF::Int;
                           prefixes    ::Vector{Int} = Int[],
                           hits_total  ::Int = 0,
                           walk_steps  ::Int = 0,
                           hits_full   ::Int = 0,
                           hits_tree   ::Int = 0,
                           hits_lp     ::Int = 0,
                           hits_lp2    ::Int = 0,
                           verbose     ::Bool = true)
    nrel = length(rel_rows)
    nrel == 0 && return nothing

    prefixes = isempty(prefixes) ? unique(sort(Int[
        min(nrel, max(50,  nrel ÷ 16)),
        min(nrel, max(100, nrel ÷ 8)),
        min(nrel, max(200, nrel ÷ 4)),
        min(nrel, max(400, nrel ÷ 2)),
        nrel,
    ])) : unique(sort(filter(x -> 1 <= x <= nrel, prefixes)))

    # Build supports once; prefix statistics reuse them.
    supports = [sort([j for (j, v) in rel_rows[i] if v != 0 && 1 <= j <= nF])
                for i in 1:nrel]

    function prefix_core_stats(m::Int)
        coldeg      = zeros(Int, nF)
        col_to_rows = [Int[] for _ in 1:nF]
        total_nz    = 0
        row_hist    = Dict{Int,Int}()
        for i in 1:m
            cols = supports[i]
            w    = length(cols)
            row_hist[w] = get(row_hist, w, 0) + 1
            total_nz += w
            for j in cols; coldeg[j] += 1; push!(col_to_rows[j], i); end
        end

        active_col = trues(nF)
        active_row = trues(m)
        deg        = copy(coldeg)
        q          = [j for j in 1:nF if deg[j] <= 1]
        while !isempty(q)
            j = pop!(q)
            active_col[j] || continue
            deg[j] > 1 && continue
            active_col[j] = false
            for ri in col_to_rows[j]
                active_row[ri] || continue
                active_row[ri] = false
                for k in supports[ri]
                    k == j || !active_col[k] && continue
                    deg[k] -= 1
                    deg[k] <= 1 && push!(q, k)
                end
            end
        end

        core_cols = count(identity, active_col)
        core_rows = count(identity, active_row)
        return (m=m, total_nz=total_nz, avg_w=total_nz/m, density=total_nz/(m*nF),
                row_hist=row_hist,
                zero_cols=count(==(0), coldeg), deg1_cols=count(==(1), coldeg),
                deg2_cols=count(==(2), coldeg),
                core_cols=core_cols, core_rows=core_rows,
                peeled_cols=nF-core_cols, core_frac=core_cols/nF,
                peel_frac=(nF-core_cols)/nF)
    end

    prefix_stats = map(prefix_core_stats, prefixes)
    gap_stats    = spectral_gap_report(rel_rows, nF; prefixes=prefixes, verbose=false)
    gap_by_m     = Dict(s.m => s for s in gap_stats)

    function loglog_slope(xs::Vector{Float64}, ys::Vector{Float64})
        pts = [(x, y) for (x, y) in zip(xs, ys) if x > 0 && y > 0 && isfinite(x) && isfinite(y)]
        length(pts) < 2 && return NaN
        lx = log.(first.(pts)); ly = log.(last.(pts))
        mx = sum(lx)/length(lx); my = sum(ly)/length(ly)
        num = sum((lx[i]-mx)*(ly[i]-my) for i in eachindex(lx))
        den = sum((lx[i]-mx)^2          for i in eachindex(lx))
        den == 0 && return NaN
        return num / den
    end

    if verbose
        println("Asymptotic diagnostics (prefix growth across the matrix):")
        @printf("  walk yield: %d valid steps / %d total = %.4f\n",
                hits_total, walk_steps, walk_steps == 0 ? 0.0 : hits_total/walk_steps)
        if hits_total > 0
            @printf("  relation mix: full=%d, tree=%d, LP-partials=%d, LP-pairs=%d\n",
                    hits_full, hits_tree, hits_lp, hits_lp2)
            @printf("  normalized: full/valid=%.4f  tree/valid=%.4f  LP-pairs/valid=%.4f\n",
                    hits_full/hits_total, hits_tree/hits_total, hits_lp2/hits_total)
        end
        for s in prefix_stats
            g = get(gap_by_m, s.m, nothing)
            gap_str = (g === nothing || isnan(g.gap)) ? "n/a" : @sprintf("%.6f", g.gap)
            @printf("  rows=%d: nz=%d, avg_w=%.2f, core=%d/%d (%.3f), peel=%d, gap=%s\n",
                    s.m, s.total_nz, s.avg_w, s.core_cols, nF, s.core_frac, s.peeled_cols, gap_str)
        end

        ms  = Float64[s.m          for s in prefix_stats]
        nzs = Float64[s.total_nz   for s in prefix_stats]
        ccs = Float64[s.core_cols  for s in prefix_stats]
        crs = Float64[s.core_rows  for s in prefix_stats]
        ps  = Float64[s.peel_frac  for s in prefix_stats]
        avs = Float64[s.avg_w      for s in prefix_stats]
        @printf("  log-log fit total_nz ~ rows^a:         a=%.4f\n", loglog_slope(ms, nzs))
        @printf("  log-log fit avg row weight ~ rows^a:   a=%.4f\n", loglog_slope(ms, avs))
        @printf("  log-log fit core cols ~ rows^a:        a=%.4f\n", loglog_slope(ms, ccs))
        @printf("  log-log fit core rows ~ rows^a:        a=%.4f\n", loglog_slope(ms, crs))
        @printf("  log-log fit peel fraction ~ rows^a:    a=%.4f\n", loglog_slope(ms, ps))
    end

    return (prefix_stats=prefix_stats, gap_stats=gap_stats)
end
