# =============================================================================
#  LP Residual Statistics
#
#  Implements diagnostics for residual LP behavior with a bias toward
#  low-allocation, low-churn data flow:
#
#    1.  Distinct LP residual count + occupancy vs. uniform expectation
#    2.  Revisit frequencies per LP point (collision histogram)
#    3.  Entropy of the empirical LP distribution (compared to H_max)
#    4.  Autocorrelation of the alpha / beta sequences emitted at LP events
#    5.  Residual graph clustering (LP–LP bipartite structure)
#    6.  Compressed-space heuristic: estimate M_effective vs. naive M = p
#
#  The collector keeps the raw event streams compact, and the report code
#  reuses a single sorted frequency pass instead of rebuilding hash maps in
#  every statistic.
# =============================================================================

using Printf

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

    # Hard cap on lp_points / lp2_pairs records (per thread).
    # Diagnostics need only O(thousands) samples; without a cap these vectors
    # grow at ~50% of raw step rate and exhaust memory before any relation is found.
    max_lp1_records ::Int
    max_lp2_records ::Int
end

const DEFAULT_MAX_LP1_RECORDS = 100_000
const DEFAULT_MAX_LP2_RECORDS =  50_000

function LPResidualCollector(;
        max_lp1_records::Int = DEFAULT_MAX_LP1_RECORDS,
        max_lp2_records::Int = DEFAULT_MAX_LP2_RECORDS)
    LPResidualCollector(
        NTuple{2,Int}[],
        Int[], Int[], Int[],
        NTuple{2, NTuple{2,Int}}[],
        Int[],
        Int[], Int[],
        max_lp1_records, max_lp2_records
    )
end

function merge_collectors(cols::Vector{LPResidualCollector})::LPResidualCollector
    max1 = isempty(cols) ? DEFAULT_MAX_LP1_RECORDS : maximum(c.max_lp1_records for c in cols)
    max2 = isempty(cols) ? DEFAULT_MAX_LP2_RECORDS : maximum(c.max_lp2_records for c in cols)
    merged = LPResidualCollector(; max_lp1_records = max1 * max(1, length(cols)),
                                    max_lp2_records = max2 * max(1, length(cols)))
    for c in cols
        append!(merged.lp_points,     c.lp_points)
        append!(merged.lp_alphas,     c.lp_alphas)
        append!(merged.lp_betas,      c.lp_betas)
        append!(merged.lp_steps,      c.lp_steps)
        append!(merged.lp2_pairs,     c.lp2_pairs)
        append!(merged.lp2_steps,     c.lp2_steps)
        append!(merged.closure_steps,  c.closure_steps)
        append!(merged.closure_gaps,   c.closure_gaps)
    end
    merged
end

# Call this inside phase2_worker whenever a 1-LP step is observed.
function record_lp1!(col::LPResidualCollector,
                     lp_pt::NTuple{2,Int},
                     alpha::Int, beta::Int,
                     raw_step::Int)
    length(col.lp_points) >= col.max_lp1_records && return
    push!(col.lp_points, lp_pt)
    push!(col.lp_alphas, alpha)
    push!(col.lp_betas,  beta)
    push!(col.lp_steps,  raw_step)
end

function record_lp2!(col::LPResidualCollector,
                     left::NTuple{2,Int}, right::NTuple{2,Int},
                     raw_step::Int)
    length(col.lp2_pairs) >= col.max_lp2_records && return
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
#  Shared low-allocation helpers
# ---------------------------------------------------------------------------
function _sorted_lp_points(col::LPResidualCollector)
    isempty(col.lp_points) && return NTuple{2,Int}[]
    pts = copy(col.lp_points)
    sort!(pts)
    return pts
end

function _point_counts(col::LPResidualCollector)
    pts = _sorted_lp_points(col)
    isempty(pts) && return NTuple{2,Int}[], Int[]

    uniq_pts = NTuple{2,Int}[]
    counts   = Int[]
    sizehint!(uniq_pts, length(pts))
    sizehint!(counts,   length(pts))

    cur = pts[1]
    c = 1
    @inbounds for i in 2:length(pts)
        p = pts[i]
        if p == cur
            c += 1
        else
            push!(uniq_pts, cur)
            push!(counts, c)
            cur = p
            c = 1
        end
    end
    push!(uniq_pts, cur)
    push!(counts, c)
    return uniq_pts, counts
end

function _sorted_run_lengths(values::AbstractVector{Int})
    isempty(values) && return Int[], Int[]
    tmp = copy(values)
    sort!(tmp)

    uniq_vals = Int[]
    counts    = Int[]
    sizehint!(uniq_vals, length(tmp))
    sizehint!(counts,    length(tmp))

    cur = tmp[1]
    c = 1
    @inbounds for i in 2:length(tmp)
        v = tmp[i]
        if v == cur
            c += 1
        else
            push!(uniq_vals, cur)
            push!(counts, c)
            cur = v
            c = 1
        end
    end
    push!(uniq_vals, cur)
    push!(counts, c)
    return uniq_vals, counts
end

@inline function _acf(seq::Vector{Int}, lag::Int)
    lag >= length(seq) && return NaN
    n = length(seq)
    m = 0.0
    @inbounds for x in seq
        m += x
    end
    m /= n

    var = 0.0
    @inbounds for x in seq
        dx = x - m
        var += dx * dx
    end
    var /= n
    var < 1e-12 && return NaN

    cov = 0.0
    upper = n - lag
    @inbounds for i in 1:upper
        cov += (seq[i] - m) * (seq[i + lag] - m)
    end
    cov /= upper
    return cov / var
end


# ---------------------------------------------------------------------------
#  1. Distinct LP count and occupancy
# ---------------------------------------------------------------------------
function lp_occupancy(col::LPResidualCollector; p_field::Int)
    isempty(col.lp_points) && return nothing
    _, counts = _point_counts(col)
    n_distinct = length(counts)
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
    _, counts = _point_counts(col)
    isempty(counts) && return nothing

    mults, mult_counts = _sorted_run_lengths(counts)
    heavy_events = 0
    singleton_points = 0
    @inbounds for i in 1:length(mults)
        m = mults[i]
        npts = mult_counts[i]
        if m == 1
            singleton_points = npts
        elseif m >= 3
            heavy_events += m * npts
        end
    end

    total_events = length(col.lp_points)
    max_mult = mults[end]
    return (
        multiplicities       = mults,
        multiplicity_counts  = mult_counts,
        heavy_frac           = heavy_events / max(1, total_events),
        max_multiplicity     = max_mult,
        singleton_frac       = singleton_points / max(1, length(counts)),
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
    _, counts = _point_counts(col)
    N = length(col.lp_points)
    H = 0.0
    @inbounds for v in counts
        if v > 0
            pv = v / N
            H -= pv * log2(pv)
        end
    end
    H_max_obs  = log2(max(1, length(counts)))
    H_max_unif = log2(max(1, p_field))
    return (
        entropy               = H,
        H_max_observed        = H_max_obs,
        H_max_uniform         = H_max_unif,
        entropy_fraction_obs  = H / max(1e-12, H_max_obs),
        entropy_fraction_unif = H / max(1e-12, H_max_unif),
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

    active_lags = Int[]
    alpha_vals  = Float64[]
    beta_vals   = Float64[]
    x_vals      = Float64[]

    xs = Int[pt[1] for pt in col.lp_points]
    @inbounds for τ in lags
        τ < n || continue
        push!(active_lags, τ)
        push!(alpha_vals, _acf(col.lp_alphas, τ))
        push!(beta_vals,  _acf(col.lp_betas,  τ))
        push!(x_vals,     _acf(xs, τ))
    end

    return (
        lags      = active_lags,
        alpha_acf = alpha_vals,
        beta_acf  = beta_vals,
        x_acf     = x_vals,
    )
end


# ---------------------------------------------------------------------------
#  5.  Residual graph clustering
#
#  Build a graph on LP points that co-occur in 2-LP events.
#  We avoid hash tables by sorting the unique point list once, then using
#  binary search for point-to-id lookup.
# ---------------------------------------------------------------------------
function lp_clustering(col::LPResidualCollector)
    isempty(col.lp2_pairs) && return nothing

    all_lp_pts = NTuple{2,Int}[]
    sizehint!(all_lp_pts, 2 * length(col.lp2_pairs))
    @inbounds for (l, r) in col.lp2_pairs
        push!(all_lp_pts, l)
        push!(all_lp_pts, r)
    end
    sort!(all_lp_pts)
    unique!(all_lp_pts)

    n_pts  = length(all_lp_pts)
    parent = collect(1:n_pts)

    function findroot(x::Int)
        while parent[x] != x
            parent[x] = parent[parent[x]]
            x = parent[x]
        end
        return x
    end

    function unite(a::Int, b::Int)
        ra = findroot(a)
        rb = findroot(b)
        ra != rb && (parent[ra] = rb)
        return nothing
    end

    @inbounds for (l, r) in col.lp2_pairs
        li = searchsortedfirst(all_lp_pts, l)
        ri = searchsortedfirst(all_lp_pts, r)
        unite(li, ri)
    end

    comp_sizes = zeros(Int, n_pts)
    @inbounds for i in 1:n_pts
        comp_sizes[findroot(i)] += 1
    end
    sizes = Int[]
    sizehint!(sizes, n_pts)
    @inbounds for s in comp_sizes
        s > 0 && push!(sizes, s)
    end
    sort!(sizes, rev=true)

    # Co-occurrence degree of LP points (how many distinct 2-LP incidences)
    degrees = zeros(Int, n_pts)
    @inbounds for (l, r) in col.lp2_pairs
        degrees[searchsortedfirst(all_lp_pts, l)] += 1
        degrees[searchsortedfirst(all_lp_pts, r)] += 1
    end
    degvals = Int[]
    sizehint!(degvals, n_pts)
    @inbounds for d in degrees
        d > 0 && push!(degvals, d)
    end
    sort!(degvals, rev=true)

    return (
        n_lp_nodes        = n_pts,
        n_lp2_edges       = length(col.lp2_pairs),
        n_components      = length(sizes),
        largest_component = isempty(sizes) ? 0 : sizes[1],
        singleton_comps   = count(==(1), sizes),
        component_sizes   = sizes,
        max_lp_degree     = isempty(degvals) ? 0 : degvals[1],
        mean_lp_degree    = isempty(degvals) ? 0.0 : sum(degvals) / length(degvals),
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

    gaps_sorted = sort(copy(col.closure_gaps))
    median_gap = gaps_sorted[(length(gaps_sorted) + 1) ÷ 2]

    return (
        n_closures       = length(col.closure_gaps),
        mean_gap_steps   = mean_gap,
        median_gap_steps = median_gap,
        M_effective      = M_eff,
        M_naive          = Float64(p_field),
        M_compression    = p_field / max(1.0, M_eff),
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
                join(string.(rev.multiplicities), ", "))
        top_mults = rev.multiplicities[end:-1:max(1, end-4)]
        for m in top_mults
            idx = searchsortedfirst(rev.multiplicities, m)
            @printf("    mult=%3d: %d LP points\n", m, rev.multiplicity_counts[idx])
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
        @inbounds for i in eachindex(acf.lags)
            τ  = acf.lags[i]
            aa = acf.alpha_acf[i]
            ba = acf.beta_acf[i]
            xa = acf.x_acf[i]
            @printf("  %4d   %+.6f   %+.6f   %+.6f\n", τ, aa, ba, xa)
        end
        if !isempty(acf.lags)
            lag1_alpha = acf.alpha_acf[1]
            if !isnan(lag1_alpha) && abs(lag1_alpha) > 0.2
                @printf("  *** SIGNIFICANT LAG-1 ALPHA AUTOCORR (%.4f): walk is sticky in alpha ***\n",
                        lag1_alpha)
            end
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
