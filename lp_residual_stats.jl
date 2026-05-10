
# =============================================================================
#  LP Residual Statistics
#
#  Implements the diagnostics proposed in the ChatGPT analysis:
#
#    1.  Distinct LP residual count + occupancy vs. uniform expectation
#    2.  Revisit frequencies per LP point (collision histogram)
#    3.  Entropy of the empirical LP distribution (compared to H_max)
#    4.  Autocorrelation of the alpha / beta sequences emitted at LP events
#    5.  Residual graph clustering (LP–LP and LP–FB bipartite structure)
#    6.  Compressed-space heuristic: estimate M_effective vs. naive M = p
#
#  Every function is pure (read-only on its inputs) and returns a named
#  tuple so callers can archive the raw numbers alongside the printout.
#
#  Wire-up: call collect_lp_residual_data! inside phase2_worker to fill
#  an LPResidualCollector, then pass it to lp_residual_report() at the
#  end of index_calculus_walk.
# =============================================================================

# ---------------------------------------------------------------------------
#  Collector struct
#
#  Filled by each worker thread.  Merge across threads with merge_collectors.
#  All fields are plain Julia primitive types so no locking is needed as long
#  as each thread writes only its own collector.
# ---------------------------------------------------------------------------
mutable struct LPResidualCollector
    # Raw LP events: each 1-LP step records (lp_point, alpha, beta, walk_step).
    lp_points   ::Vector{NTuple{2,Int}}   # the LP Jacobian point (x,y)
    lp_alphas   ::Vector{Int}             # alpha at the moment of 1-LP step
    lp_betas    ::Vector{Int}             # beta  at the moment of 1-LP step
    lp_steps    ::Vector{Int}             # raw_step counter at event

    # 2-LP events
    lp2_pairs   ::Vector{NTuple{2, NTuple{2,Int}}}   # (left, right) LP point pairs
    lp2_steps   ::Vector{Int}

    # Closure events (1-LP pair that cancelled)
    closure_steps::Vector{Int}            # raw_step when a 1-LP closure fired
    closure_gaps ::Vector{Int}            # raw_step gap since the first half
end

function LPResidualCollector()
    LPResidualCollector(
        NTuple{2,Int}[],
        Int[], Int[], Int[],
        NTuple{2, NTuple{2,Int}}[],
        Int[],
        Int[], Int[]
    )
end

function merge_collectors(cols::Vector{LPResidualCollector})::LPResidualCollector
    merged = LPResidualCollector()
    for c in cols
        append!(merged.lp_points,    c.lp_points)
        append!(merged.lp_alphas,    c.lp_alphas)
        append!(merged.lp_betas,     c.lp_betas)
        append!(merged.lp_steps,     c.lp_steps)
        append!(merged.lp2_pairs,    c.lp2_pairs)
        append!(merged.lp2_steps,    c.lp2_steps)
        append!(merged.closure_steps, c.closure_steps)
        append!(merged.closure_gaps,  c.closure_gaps)
    end
    merged
end

# Call this inside phase2_worker whenever a 1-LP step is observed.
function record_lp1!(col::LPResidualCollector,
                     lp_pt::NTuple{2,Int},
                     alpha::Int, beta::Int,
                     raw_step::Int)
    push!(col.lp_points, lp_pt)
    push!(col.lp_alphas, alpha)
    push!(col.lp_betas,  beta)
    push!(col.lp_steps,  raw_step)
end

function record_lp2!(col::LPResidualCollector,
                     left::NTuple{2,Int}, right::NTuple{2,Int},
                     raw_step::Int)
    pair = left <= right ? (left, right) : (right, left)
    push!(col.lp2_pairs, pair)
    push!(col.lp2_steps, raw_step)
end

function record_closure!(col::LPResidualCollector,
                         raw_step::Int,
                         first_step::Int)
    push!(col.closure_steps, raw_step)
    push!(col.closure_gaps,  raw_step - first_step)
end


# ---------------------------------------------------------------------------
#  1. Distinct LP count and occupancy
# ---------------------------------------------------------------------------
function lp_occupancy(col::LPResidualCollector; p_field::Int)
    isempty(col.lp_points) && return nothing
    freq = Dict{NTuple{2,Int},Int}()
    for pt in col.lp_points
        freq[pt] = get(freq, pt, 0) + 1
    end
    n_distinct = length(freq)
    n_total    = length(col.lp_points)
    # Naive expectation: uniform over p points  → distinct ≈ p*(1-e^{-N/p})
    expected_distinct = p_field * (1.0 - exp(-n_total / p_field))
    compression_ratio = expected_distinct / max(1, n_distinct)

    return (
        n_total           = n_total,
        n_distinct        = n_distinct,
        naive_expected    = expected_distinct,
        compression_ratio = compression_ratio,   # > 1 means residuals cluster
        avg_revisits      = n_total / n_distinct,
    )
end


# ---------------------------------------------------------------------------
#  2.  Revisit frequency histogram
# ---------------------------------------------------------------------------
function lp_revisit_histogram(col::LPResidualCollector)
    isempty(col.lp_points) && return nothing
    freq = Dict{NTuple{2,Int},Int}()
    for pt in col.lp_points
        freq[pt] = get(freq, pt, 0) + 1
    end
    hist = Dict{Int,Int}()   # multiplicity → count of LP points with that multiplicity
    for v in values(freq)
        hist[v] = get(hist, v, 0) + 1
    end
    sorted_mults = sort(collect(keys(hist)))
    # Fraction of total LP events that come from "heavy hitter" points (mult >= 3)
    heavy_events  = sum(k * hist[k] for k in sorted_mults if k >= 3; init=0)
    total_events  = length(col.lp_points)
    return (
        histogram       = hist,                     # Dict: mult => n_lp_pts
        sorted_mults    = sorted_mults,
        heavy_frac      = heavy_events / max(1, total_events),
        max_multiplicity = sorted_mults[end],
        singleton_frac  = get(hist, 1, 0) / max(1, length(freq)),
    )
end


# ---------------------------------------------------------------------------
#  3.  Empirical entropy of LP distribution
#
#  H = -sum_i p_i * log2(p_i)  where p_i = freq_i / N
#  H_max = log2(n_distinct)  if uniform over observed support
#  H_unif = log2(p)          if uniform over all p points
# ---------------------------------------------------------------------------
function lp_entropy(col::LPResidualCollector; p_field::Int)
    isempty(col.lp_points) && return nothing
    freq = Dict{NTuple{2,Int},Int}()
    for pt in col.lp_points
        freq[pt] = get(freq, pt, 0) + 1
    end
    N = length(col.lp_points)
    H = 0.0
    for v in values(freq)
        if v > 0
            pv = v / N
            H -= pv * log2(pv)
        end
    end
    H_max_obs  = log2(max(1, length(freq)))   # uniform over observed distinct
    H_max_unif = log2(max(1, p_field))         # uniform over all p field points
    return (
        entropy              = H,
        H_max_observed       = H_max_obs,
        H_max_uniform        = H_max_unif,
        entropy_fraction_obs  = H / max(1e-12, H_max_obs),   # 1.0 = uniform over seen
        entropy_fraction_unif = H / max(1e-12, H_max_unif),  # 1.0 = uniform over F_p
    )
end


# ---------------------------------------------------------------------------
#  4.  Autocorrelation of alpha/beta sequences
#
#  For each lag τ in {1, 2, 4, 8, 16}, compute normalized autocorrelation:
#
#      r(τ) = cov(x_i, x_{i+τ}) / var(x)
#
#  A value near 0 means the walk forgets quickly; a large positive value
#  means consecutive LP events share similar alpha (i.e. the walk is sticky).
# ---------------------------------------------------------------------------
function lp_autocorrelation(col::LPResidualCollector;
                             lags::Vector{Int} = [1, 2, 4, 8, 16, 32])
    n = length(col.lp_alphas)
    n < 2 && return nothing

    function acf(seq::Vector{Int}, lag::Int)
        lag >= length(seq) && return NaN
        m   = sum(seq) / length(seq)
        var = sum((x - m)^2 for x in seq) / length(seq)
        var < 1e-12 && return NaN
        cov = sum((seq[i] - m) * (seq[i + lag] - m)
                  for i in 1:length(seq) - lag) / (length(seq) - lag)
        return cov / var
    end

    alpha_acf = Dict(τ => acf(col.lp_alphas, τ) for τ in lags if τ < n)
    beta_acf  = Dict(τ => acf(col.lp_betas,  τ) for τ in lags if τ < n)

    # Also test x-coordinates of LP points directly
    xs = [pt[1] for pt in col.lp_points]
    x_acf = Dict(τ => acf(xs, τ) for τ in lags if τ < n)

    return (
        lags      = lags,
        alpha_acf = alpha_acf,
        beta_acf  = beta_acf,
        x_acf     = x_acf,
    )
end


# ---------------------------------------------------------------------------
#  5.  Residual graph clustering
#
#  Build a bipartite graph:  LP_points × FB_columns.
#  Edge (lp_pt, fb_col) exists if any step had both that LP point and that
#  FB column in its P0/R/S triple.
#
#  We track this from the collector's lp_points alongside fb_row information.
#  Since the collector doesn't store the fb_row per event by default, we
#  provide a separate lightweight path: analyze the LP–LP co-occurrence
#  from 2-LP pairs (lp2_pairs) directly.
#
#  For LP–LP:
#    - Build a graph where nodes are LP points seen in 2-LP steps.
#    - Edge = co-occurrence in a 2-LP event.
#    - Compute number of connected components; if small, state space is compressed.
#
#  We also compute the LP–FB incidence if fb_rows are supplied separately.
# ---------------------------------------------------------------------------
function lp_clustering(col::LPResidualCollector)
    isempty(col.lp2_pairs) && return nothing

    # Union-Find on LP points seen in 2-LP events
    all_lp_pts = unique(vcat([[p[1], p[2]] for p in col.lp2_pairs]...))
    pt_to_id   = Dict(pt => i for (i, pt) in enumerate(all_lp_pts))
    n_pts      = length(all_lp_pts)
    parent     = collect(1:n_pts)

    function findroot(x)
        while parent[x] != x
            parent[x] = parent[parent[x]]
            x = parent[x]
        end
        return x
    end

    function unite(a, b)
        ra = findroot(a); rb = findroot(b)
        ra != rb && (parent[ra] = rb)
    end

    for (l, r) in col.lp2_pairs
        unite(pt_to_id[l], pt_to_id[r])
    end

    comp_sizes = Dict{Int,Int}()
    for i in 1:n_pts
        r = findroot(i)
        comp_sizes[r] = get(comp_sizes, r, 0) + 1
    end
    sizes = sort(collect(values(comp_sizes)), rev=true)

    # Co-occurrence degree of LP points (how many distinct LP partners)
    lp_degree = Dict{NTuple{2,Int},Int}()
    for (l, r) in col.lp2_pairs
        lp_degree[l] = get(lp_degree, l, 0) + 1
        lp_degree[r] = get(lp_degree, r, 0) + 1
    end
    degrees = sort(collect(values(lp_degree)), rev=true)

    return (
        n_lp_nodes        = n_pts,
        n_lp2_edges       = length(col.lp2_pairs),
        n_components      = length(sizes),
        largest_component = isempty(sizes) ? 0 : sizes[1],
        singleton_comps   = count(==(1), sizes),
        component_sizes   = sizes,
        max_lp_degree     = isempty(degrees) ? 0 : degrees[1],
        mean_lp_degree    = isempty(degrees) ? 0.0 : sum(degrees) / length(degrees),
    )
end


# ---------------------------------------------------------------------------
#  6.  Effective state-space size M_effective
#
#  Under the birthday-paradox heuristic, the expected number of steps until
#  the first LP closure is:
#
#      E[steps] ≈ sqrt(π * M_effective / 2)
#
#  We estimate M_effective from the observed mean inter-closure gap.
# ---------------------------------------------------------------------------
function lp_effective_space(col::LPResidualCollector; p_field::Int)
    isempty(col.closure_gaps) && return nothing

    mean_gap = sum(col.closure_gaps) / length(col.closure_gaps)
    # E[gap] ≈ sqrt(π * M / 2)  → M ≈ 2 * E[gap]^2 / π
    M_eff = 2.0 * mean_gap^2 / π

    return (
        n_closures       = length(col.closure_gaps),
        mean_gap_steps   = mean_gap,
        median_gap_steps = sort(col.closure_gaps)[(length(col.closure_gaps)+1)÷2],
        M_effective      = M_eff,
        M_naive          = Float64(p_field),
        M_compression    = p_field / max(1.0, M_eff),   # >> 1 means compressed
    )
end


# ---------------------------------------------------------------------------
#  Master report function
#
#  Call after merging all thread collectors.
# ---------------------------------------------------------------------------
function lp_residual_report(col::LPResidualCollector;
                             p_field::Int,
                             verbose::Bool = true)

    println()
    println("══════════════════════════════════════════════════════════════════")
    println("  LP Residual Statistics")
    println("══════════════════════════════════════════════════════════════════")

    # ── 1. Occupancy ────────────────────────────────────────────────────────
    occ = lp_occupancy(col; p_field=p_field)
    if occ !== nothing
        println("\n── 1. LP Point Occupancy ───────────────────────────────────────────")
        @printf("  Total 1-LP events recorded:  %d\n", occ.n_total)
        @printf("  Distinct LP points seen:     %d\n", occ.n_distinct)
        @printf("  Expected distinct (uniform): %.1f   (p*(1-e^{-N/p}))\n",
                occ.naive_expected)
        @printf("  Compression ratio:           %.4fx  (> 1 = clustered, < 1 = sparse)\n",
                occ.compression_ratio)
        @printf("  Average revisits per point:  %.3f\n", occ.avg_revisits)
        if occ.compression_ratio > 2.0
            @printf("  *** HIGH COMPRESSION: residual space ~%.1fx smaller than naive p-scale ***\n",
                    occ.compression_ratio)
        end
    else
        println("\n── 1. LP Point Occupancy: no 1-LP data collected ───────────────────")
    end

    # ── 2. Revisit histogram ────────────────────────────────────────────────
    rev = lp_revisit_histogram(col)
    if rev !== nothing
        println("\n── 2. LP Revisit Frequency Histogram ───────────────────────────────")
        @printf("  Multiplicities present: %s\n",
                join(string.(rev.sorted_mults), ", "))
        top_mults = rev.sorted_mults[end:-1:max(1, end-4)]
        for m in top_mults
            @printf("    mult=%3d: %d LP points\n", m, get(rev.histogram, m, 0))
        end
        @printf("  Singleton LP points (seen once): %.3f%%\n",
                100.0 * rev.singleton_frac)
        @printf("  Events from 'heavy' points (mult >= 3): %.3f%%\n",
                100.0 * rev.heavy_frac)
        @printf("  Max multiplicity: %d\n", rev.max_multiplicity)
    end

    # ── 3. Entropy ──────────────────────────────────────────────────────────
    ent = lp_entropy(col; p_field=p_field)
    if ent !== nothing
        println("\n── 3. LP Distribution Entropy ──────────────────────────────────────")
        @printf("  Empirical entropy H:              %.4f bits\n", ent.entropy)
        @printf("  H_max over observed support:      %.4f bits\n", ent.H_max_observed)
        @printf("  H_max uniform over F_p:           %.4f bits\n", ent.H_max_uniform)
        @printf("  H / H_max(observed):              %.4f   (1.0 = uniform over seen)\n",
                ent.entropy_fraction_obs)
        @printf("  H / H_max(uniform/F_p):           %.4f   (1.0 = uniform over F_p)\n",
                ent.entropy_fraction_unif)
        if ent.entropy_fraction_unif < 0.5
            @printf("  *** LOW ENTROPY: LP visits a much smaller effective space than F_p ***\n")
        end
    end

    # ── 4. Autocorrelation ──────────────────────────────────────────────────
    acf = lp_autocorrelation(col)
    if acf !== nothing
        println("\n── 4. Alpha/Beta Autocorrelation at LP Events ─────────────────────")
        println("  lag    alpha_acf    beta_acf    x_acf")
        for τ in sort(collect(keys(acf.alpha_acf)))
            aa = get(acf.alpha_acf, τ, NaN)
            ba = get(acf.beta_acf,  τ, NaN)
            xa = get(acf.x_acf,    τ, NaN)
            @printf("  %4d   %+.6f   %+.6f   %+.6f\n", τ, aa, ba, xa)
        end
        lag1_alpha = get(acf.alpha_acf, 1, NaN)
        if !isnan(lag1_alpha) && abs(lag1_alpha) > 0.2
            @printf("  *** SIGNIFICANT LAG-1 ALPHA AUTOCORR (%.4f): walk is sticky in alpha ***\n",
                    lag1_alpha)
        end
    end

    # ── 5. Clustering ───────────────────────────────────────────────────────
    clu = lp_clustering(col)
    if clu !== nothing
        println("\n── 5. LP–LP Residual Graph Clustering ──────────────────────────────")
        @printf("  LP nodes in 2-LP graph:   %d\n",  clu.n_lp_nodes)
        @printf("  2-LP co-occurrence edges: %d\n",  clu.n_lp2_edges)
        @printf("  Connected components:      %d\n",  clu.n_components)
        @printf("  Largest component size:   %d  (%.2f%% of LP nodes)\n",
                clu.largest_component,
                100.0 * clu.largest_component / max(1, clu.n_lp_nodes))
        @printf("  Singleton components:     %d\n",  clu.singleton_comps)
        @printf("  Max LP node degree:       %d\n",  clu.max_lp_degree)
        @printf("  Mean LP node degree:      %.3f\n", clu.mean_lp_degree)
        if length(clu.component_sizes) >= 2
            @printf("  Top-5 component sizes:    %s\n",
                    join(string.(clu.component_sizes[1:min(5,end)]), ", "))
        end
        if clu.largest_component > clu.n_lp_nodes / 2
            @printf("  *** GIANT COMPONENT: LP residuals densely interconnected ***\n")
        end
    else
        println("\n── 5. LP–LP Residual Graph Clustering: no 2-LP data ───────────────")
    end

    # ── 6. Effective state-space estimate ───────────────────────────────────
    eff = lp_effective_space(col; p_field=p_field)
    if eff !== nothing
        println("\n── 6. Effective LP State-Space Size M_eff ──────────────────────────")
        @printf("  Closure events recorded:     %d\n",    eff.n_closures)
        @printf("  Mean inter-closure gap:      %.1f steps\n", eff.mean_gap_steps)
        @printf("  Median inter-closure gap:    %d steps\n",   eff.median_gap_steps)
        @printf("  M_effective (from gap):      %.3e   (birthday: M = 2*gap^2/π)\n",
                eff.M_effective)
        @printf("  M_naive (= p):               %.3e\n",   eff.M_naive)
        @printf("  Compression M_naive/M_eff:   %.4fx\n",  eff.M_compression)
        if eff.M_compression > 4.0
            @printf("  *** COMPRESSED: effective LP space is ~%.1fx smaller than p ***\n",
                    eff.M_compression)
            @printf("  *** This would imply LP closures scale as closures ~ N^2/M_eff ***\n")
            @printf("  *** = roughly %.2fx speedup over naive birthday expectation ***\n",
                    sqrt(eff.M_compression))
        end
    else
        println("\n── 6. Effective LP State-Space: no closure gaps recorded ───────────")
    end

    println()
    println("══════════════════════════════════════════════════════════════════")
    flush(stdout)

    return (
        occupancy   = occ,
        revisit     = rev,
        entropy     = ent,
        autocorr    = acf,
        clustering  = clu,
        effective   = eff,
    )
end
