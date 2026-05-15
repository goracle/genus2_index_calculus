# =============================================================================
#  kernel_phase_diag.jl  —  Phase-transition instrumentation for the DLP solve
#
#  Instruments the quantities identified in the ChatGPT analysis:
#
#    1.  Δ = T_ker - nF  distribution across trials
#    2.  Kernel-vector diagnostics at first-kernel:
#          * support size
#          * β-projection  (Σ cᵢ βᵢ mod ell)
#          * α-projection  (Σ cᵢ αᵢ mod ell)
#          * immediate solvability (β ≠ 0 → k recoverable)
#    3.  Betti number b₁(m) = m - rank(M_m)  as a function of row count m
#          using an incremental rank-deficiency scan
#    4.  Row-weight distribution at first-kernel formation
#    5.  Per-prefix core size and spectral gap snapshot at T_ker
#
#  Usage
#  -----
#  At the top of trial3_fixed.jl (after `include("trial1_autoell_p10.jl")`):
#
#      include("kernel_phase_diag.jl")
#
#  Then inside `index_calculus_walk` (or wherever you have the final
#  rel_rows / alpha_vec / beta_vec), call:
#
#      diag = kernel_phase_instrumentation(rel_rows, alpha_vec, beta_vec, nF, ell;
#                                          G=G, T=T, verbose=true)
#
#  For multi-trial Δ collection, accumulate results:
#
#      push!(delta_samples, diag.delta)
#      delta_report(delta_samples; nF=nF)
#
# =============================================================================

using Printf, Statistics, LinearAlgebra

# ---------------------------------------------------------------------------
#  Flattened row storage
# ---------------------------------------------------------------------------
#
#  The input rows are still accepted as Vector{Dict{Int,Int}} for compatibility,
#  but the heavy lifting is done on a compact flattened representation:
#
#      row_ptr[i] : row_ptr[i+1]-1
#          indexes the nonzeros for row i in `cols` / `vals`
#
#  This removes the repeated per-row Dict traversal from the hot paths.
# ---------------------------------------------------------------------------

struct FlatRelRows
    row_ptr::Vector{Int}   # 1-based CSR row pointers, length nrows + 1
    cols::Vector{Int}      # factor-base column indices
    vals::Vector{Int}      # coefficients reduced mod ell
end

@inline nrows(flat::FlatRelRows) = length(flat.row_ptr) - 1

@inline function row_range(flat::FlatRelRows, i::Int)
    @inbounds return flat.row_ptr[i]:(flat.row_ptr[i + 1] - 1)
end

function flatten_rel_rows(rel_rows::Vector{Dict{Int,Int}},
                          nF::Int,
                          ell_val::Integer)::FlatRelRows
    nrel = length(rel_rows)
    nrel == 0 && throw(ArgumentError("flatten_rel_rows: rel_rows is empty"))
    ell_val < 2 && throw(ArgumentError("flatten_rel_rows: ell_val=$ell_val < 2"))

    row_ptr = Vector{Int}(undef, nrel + 1)
    row_ptr[1] = 1

    nnz = 0
    @inbounds for i in 1:nrel
        row = rel_rows[i]
        for (j, v) in row
            if 1 <= j <= nF && v != 0
                nnz += 1
            end
        end
        row_ptr[i + 1] = nnz + 1
    end

    cols = Vector{Int}(undef, nnz)
    vals = Vector{Int}(undef, nnz)

    pos = 1
    @inbounds for i in 1:nrel
        for (j, v) in rel_rows[i]
            if 1 <= j <= nF && v != 0
                cols[pos] = j
                vals[pos] = mod(v, ell_val)
                pos += 1
            end
        end
    end

    return FlatRelRows(row_ptr, cols, vals)
end

# ---------------------------------------------------------------------------
#  Data types
# ---------------------------------------------------------------------------

"""Result of a single-trial kernel-phase instrumentation run."""
struct KernelPhaseDiag
    nF         ::Int
    nrel_total ::Int

    # --- Δ = T_ker - nF ---
    T_ker      ::Union{Int, Nothing}
    delta      ::Union{Int, Nothing}

    # --- kernel vector stats at T_ker ---
    gamma_support_size ::Union{Int, Nothing}
    gamma_beta_proj    ::Union{Int, Nothing}
    gamma_alpha_proj   ::Union{Int, Nothing}
    gamma_solvable     ::Union{Bool, Nothing}

    # --- k recovery ---
    k_candidate        ::Union{Int, Nothing}
    k_correct          ::Union{Bool, Nothing}

    # --- Betti b₁ trace ---
    betti_trace        ::Vector{Tuple{Int,Int}}
    first_nonzero_betti::Union{Int, Nothing}

    # --- row-weight distribution at T_ker ---
    weight_histogram   ::Vector{Tuple{Int,Int}}
    avg_weight_at_tker ::Float64

    # --- spectral gap at T_ker (if available) ---
    gap_at_tker        ::Float64
end


# ---------------------------------------------------------------------------
#  Dense prefix materialisation helpers
# ---------------------------------------------------------------------------

@inline function fill_dense_prefix!(entries::Vector{Int},
                                    flat::FlatRelRows,
                                    m::Int,
                                    nF::Int)
    fill!(entries, 0)
    @inbounds for i in 1:m
        base = (i - 1) * nF
        for p in row_range(flat, i)
            entries[base + flat.cols[p]] = flat.vals[p]
        end
    end
    return entries
end

@inline function prefix_matrix(F, flat::FlatRelRows, m::Int, nF::Int, entries::Vector{Int})
    fill_dense_prefix!(entries, flat, m, nF)
    if length(entries) == m * nF
        return Nemo.matrix(F, m, nF, entries)
    end
    return Nemo.matrix(F, m, nF, view(entries, 1:(m * nF)))
end

@inline function prefix_has_kernel(flat::FlatRelRows,
                                    nF::Int,
                                    ell_val::Integer,
                                    m::Int,
                                    F,
                                    entries::Vector{Int})::Bool
    Mm = prefix_matrix(F, flat, m, nF, entries)
    return m - Nemo.rank(Mm) >= 1
end


# ---------------------------------------------------------------------------
#  Betti-number scan
#
#  Incrementally tracks rank(M_m) as rows are added one at a time.
#  Uses FLINT/Nemo for speed (same backend as left_kernel_all).
#
#  Returns a vector of (m, b1) tuples and the first m with b1 ≥ 1.
# ---------------------------------------------------------------------------
function betti_trace(flat::FlatRelRows,
                     nF       ::Int,
                     ell_val::Integer;
                     step     ::Int = 1,
                     verbose  ::Bool = false)::Tuple{Vector{Tuple{Int,Int}}, Union{Int,Nothing}}

    m = nrows(flat)
    m == 0 && throw(ArgumentError("betti_trace: rel_rows is empty"))
    step < 1 && throw(ArgumentError("betti_trace: step must be ≥ 1"))

    F      = Nemo.GF(ell_val)
    trace  = Tuple{Int,Int}[]
    buf    = Vector{Int}(undef, m * nF)
    first_nonzero = nothing

    for row_limit in 1:step:m
        Mm = prefix_matrix(F, flat, row_limit, nF, buf)
        rank_m = Nemo.rank(Mm)
        b1 = row_limit - rank_m
        push!(trace, (row_limit, b1))

        if first_nonzero === nothing && b1 >= 1
            first_nonzero = row_limit
            verbose && @printf("[betti_trace] b₁ first ≥ 1 at m=%d  (b₁=%d, rank=%d)\n",
                               row_limit, b1, rank_m)
        end
    end

    if isempty(trace) || trace[end][1] != m
        Mm = prefix_matrix(F, flat, m, nF, buf)
        rank_m = Nemo.rank(Mm)
        b1 = m - rank_m
        push!(trace, (m, b1))
        if first_nonzero === nothing && b1 >= 1
            first_nonzero = m
        end
    end

    return trace, first_nonzero
end

function betti_trace(rel_rows::Vector{Dict{Int,Int}},
                     nF       ::Int,
                     ell_val::Integer;
                     step     ::Int = 1,
                     verbose  ::Bool = false)::Tuple{Vector{Tuple{Int,Int}}, Union{Int,Nothing}}
    flat = flatten_rel_rows(rel_rows, nF, ell_val)
    return betti_trace(flat, nF, ell_val; step=step, verbose=verbose)
end


# ---------------------------------------------------------------------------
#  Efficient first-kernel finder
#
#  Binary-searches for the smallest m with rank(M_m) < m (i.e. b₁ ≥ 1),
#  then records the kernel vector at that m.  Avoids the O(m²) full trace
#  when only T_ker is needed.
# ---------------------------------------------------------------------------
function find_first_kernel_row(flat::FlatRelRows,
                               nF        ::Int,
                               ell_val::Integer)::Union{Int, Nothing}

    m = nrows(flat)
    m == 0 && throw(ArgumentError("find_first_kernel_row: rel_rows is empty"))

    F = Nemo.GF(ell_val)
    buf = Vector{Int}(undef, m * nF)

    # Quick check: does the full matrix have a kernel at all?
    if !prefix_has_kernel(flat, nF, ell_val, m, F, buf)
        return nothing
    end

    lo, hi = min(m, max(1, nF - 10)), m

    # Ensure lo truly has no kernel, walking down in chunks.
    while lo >= 1
        if !prefix_has_kernel(flat, nF, ell_val, lo, F, buf)
            break
        end
        lo = max(1, lo - 10)
    end
    lo = max(1, lo)

    while lo < hi
        mid = (lo + hi) ÷ 2
        if prefix_has_kernel(flat, nF, ell_val, mid, F, buf)
            hi = mid
        else
            lo = mid + 1
        end
    end

    return lo
end

function find_first_kernel_row(rel_rows::Vector{Dict{Int,Int}},
                               nF        ::Int,
                               ell_val::Integer)::Union{Int, Nothing}
    flat = flatten_rel_rows(rel_rows, nF, ell_val)
    return find_first_kernel_row(flat, nF, ell_val)
end


# ---------------------------------------------------------------------------
#  Extract first kernel vector at exactly m rows
# ---------------------------------------------------------------------------
function first_kernel_vector(flat::FlatRelRows,
                             nF      ::Int,
                             ell_val::Integer,
                             m       ::Int)::Union{Vector{Int}, Vector{BigInt}, Nothing}

    m < 1 && throw(ArgumentError("first_kernel_vector: m=$m < 1"))
    m > nrows(flat) && throw(ArgumentError(
        "first_kernel_vector: m=$m exceeds rel_rows length $(nrows(flat))"))

    F       = Nemo.GF(ell_val)
    entries  = Vector{Int}(undef, m * nF)
    Mnemo    = prefix_matrix(F, flat, m, nF, entries)

    # Left kernel = right kernel of transpose.
    Mt    = Nemo.transpose(Mnemo)
    nu, K = Nemo.nullspace(Mt)
    nu < 1 && return nothing

    # Lift kernel vector from GF(ell) to BigInt; entries are in [0, ell-1].
    # We use BigInt here so the vector is safe for any ell (including ell > 2^31).
    γ = Vector{BigInt}(undef, m)
    @inbounds for r in 1:m
        γ[r] = BigInt(Nemo.lift(Nemo.ZZ, K[r, 1]))
    end
    any(!=(0), γ) || return nothing
    # Convert to Int if ell fits in Int64 (common case — avoids BigInt overhead downstream).
    if ell_val <= typemax(Int)
        return Int.(γ)
    end
    return γ
end

function first_kernel_vector(rel_rows::Vector{Dict{Int,Int}},
                             nF      ::Int,
                             ell_val::Integer,
                             m       ::Int)::Union{Vector{Int}, Vector{BigInt}, Nothing}
    flat = flatten_rel_rows(rel_rows, nF, ell_val)
    return first_kernel_vector(flat, nF, ell_val, m)
end


# ---------------------------------------------------------------------------
#  Row-weight histogram for first m rows
# ---------------------------------------------------------------------------
function row_weight_histogram(flat::FlatRelRows, m::Int,
                              nF::Int)::Tuple{Vector{Tuple{Int,Int}}, Float64}
    lim = min(m, nrows(flat))
    counts = zeros(Int, nF + 1)
    total = 0

    @inbounds for i in 1:lim
        w = flat.row_ptr[i + 1] - flat.row_ptr[i]
        counts[w + 1] += 1
        total += w
    end

    hist = Tuple{Int,Int}[]
    @inbounds for w in 0:nF
        c = counts[w + 1]
        c == 0 && continue
        push!(hist, (w, c))
    end

    avg = lim == 0 ? 0.0 : total / lim
    return hist, avg
end

function row_weight_histogram(rel_rows::Vector{Dict{Int,Int}}, m::Int,
                              nF::Int)::Tuple{Vector{Tuple{Int,Int}}, Float64}
    lim = min(m, length(rel_rows))
    counts = zeros(Int, nF + 1)
    total = 0
    @inbounds for i in 1:lim
        w = 0
        for (j, v) in rel_rows[i]
            if 1 <= j <= nF && v != 0
                w += 1
            end
        end
        counts[w + 1] += 1
        total += w
    end
    hist = Tuple{Int,Int}[]
    @inbounds for w in 0:nF
        c = counts[w + 1]
        c == 0 && continue
        push!(hist, (w, c))
    end
    avg = lim == 0 ? 0.0 : total / lim
    return hist, avg
end


# ---------------------------------------------------------------------------
#  Main instrumentation entry point
# ---------------------------------------------------------------------------
"""
    kernel_phase_instrumentation(rel_rows, alpha_vec, beta_vec, nF, ell_val;
                                  G=nothing, T=nothing,
                                  k_true=nothing,
                                  verbose=true,
                                  full_betti_trace=false,
                                  betti_step=1) → KernelPhaseDiag

Instruments the phase transition around T_ker = first row at which b₁ ≥ 1.

Arguments
---------
- `rel_rows`  : vector of sparse factor-base rows (Dict{Int,Int})
- `alpha_vec` : α coefficients (one per row)
- `beta_vec`  : β coefficients (one per row)
- `nF`        : factor-base size
- `ell_val`   : group order (prime)
- `G`, `T`    : Jacobian elements (used for k-recovery verification)
- `k_true`    : true secret (optional; used only for verification printout)
- `verbose`   : print diagnostic table
- `full_betti_trace` : if true, compute b₁(m) for every `betti_step` rows
                       (expensive for large matrices; default false)
- `betti_step` : stride for full Betti trace (ignored if full_betti_trace=false)

Returns a KernelPhaseDiag named tuple.
"""
function kernel_phase_instrumentation(
        rel_rows  ::Vector{Dict{Int,Int}},
        alpha_vec ::Vector{<:Integer},
        beta_vec  ::Vector{<:Integer},
        nF        ::Int,
        ell_val::Integer;
        G                 = nothing,
        T                 = nothing,
        k_true            = nothing,
        verbose    ::Bool = true,
        full_betti_trace::Bool = false,
        betti_step ::Int = 1)::KernelPhaseDiag

    nrel = length(rel_rows)
    nrel == 0 && throw(ArgumentError("kernel_phase_instrumentation: rel_rows is empty"))
    length(alpha_vec) != nrel && throw(ArgumentError(
        "kernel_phase_instrumentation: alpha_vec length $(length(alpha_vec)) ≠ nrel=$nrel"))
    length(beta_vec) != nrel && throw(ArgumentError(
        "kernel_phase_instrumentation: beta_vec length $(length(beta_vec)) ≠ nrel=$nrel"))
    ell_val < 2 && throw(ArgumentError("kernel_phase_instrumentation: ell_val=$ell_val < 2"))

    flat = flatten_rel_rows(rel_rows, nF, ell_val)
    nrel = nrows(flat)

    verbose && begin
        println()
        @printf("── Kernel Phase Diagnostics ────────────────────────────────────────\n")
        @printf("  nF=%d  nrel=%d  ell=%d\n", nF, nrel, ell_val)
        flush(stdout)
    end

    # ── 1. Find T_ker (binary search) ────────────────────────────────────────
    t0 = time()
    T_ker = find_first_kernel_row(flat, nF, ell_val)
    t_tker = time() - t0

    if T_ker === nothing
        verbose && @printf("  T_ker: NOT FOUND (no kernel in %d rows)\n", nrel)
        return KernelPhaseDiag(nF, nrel, nothing, nothing,
                               nothing, nothing, nothing, nothing,
                               nothing, nothing,
                               Tuple{Int,Int}[], nothing,
                               Tuple{Int,Int}[], 0.0, NaN)
    end

    delta = T_ker - nF
    verbose && @printf("  T_ker=%d   nF=%d   Δ = T_ker - nF = %+d   (found in %.3fs)\n",
                       T_ker, nF, delta, t_tker)

    # ── 2. Kernel vector at T_ker ─────────────────────────────────────────────
    γ = first_kernel_vector(flat, nF, ell_val, T_ker)

    gamma_support_size = nothing
    gamma_beta_proj    = nothing
    gamma_alpha_proj   = nothing
    gamma_solvable     = nothing
    k_candidate        = nothing
    k_correct          = nothing

    if γ !== nothing
        gamma_support_size = 0
        @inbounds for x in γ
            x != 0 && (gamma_support_size += 1)
        end

        # Accumulate Σ γᵢ·αᵢ and Σ γᵢ·βᵢ mod ell using BigInt to handle ell > 2^31.
        ell_big = BigInt(ell_val)
        Sa = BigInt(0)
        Sb = BigInt(0)
        @inbounds for i in 1:T_ker
            Sa = mod(Sa + BigInt(γ[i]) * BigInt(alpha_vec[i]), ell_big)
            Sb = mod(Sb + BigInt(γ[i]) * BigInt(beta_vec[i]), ell_big)
        end
        # Store as Int when safe (ell fits in Int64 and result is in [0, ell-1]).
        gamma_alpha_proj = ell_val <= typemax(Int) ? Int(Sa) : Sa
        gamma_beta_proj  = ell_val <= typemax(Int) ? Int(Sb) : Sb
        gamma_solvable   = (Sb != 0)

        verbose && begin
            @printf("  Kernel vector (at m=%d):\n", T_ker)
            @printf("    support size:    %d  (of %d rows)\n", gamma_support_size, T_ker)
            @printf("    α-projection:    %s  (Σγᵢαᵢ mod ell)\n", string(gamma_alpha_proj))
            @printf("    β-projection:    %s  (Σγᵢβᵢ mod ell)\n", string(gamma_beta_proj))
            @printf("    solvable (β≠0):  %s\n", string(gamma_solvable))
        end

        # k recovery: k = −Sa · Sb⁻¹ mod ell
        if gamma_solvable && G !== nothing && T !== nothing
            k_candidate = Int(mod(-Sa * powermod(Sb, ell_big - 2, ell_big), ell_big))
            k_correct   = jac_mul(G, k_candidate) == T
            verbose && @printf("    k_candidate:     %d   k·G==T: %s%s\n",
                               k_candidate, string(k_correct),
                               k_true !== nothing ? "   true k: $k_true" : "")
        elseif gamma_solvable === false
            verbose && @printf("    β=0: kernel vec doesn't solve DLP this round\n")
        end
    else
        verbose && @printf("  [WARN] Kernel vector extraction returned nothing at m=%d\n", T_ker)
    end

    # ── 3. Betti trace ────────────────────────────────────────────────────────
    betti_tr = Tuple{Int,Int}[]
    first_nonzero_betti = T_ker

    if full_betti_trace
        verbose && @printf("  Computing full Betti trace (step=%d)...\n", betti_step)
        t_bt = time()
        betti_tr, first_nonzero_betti = betti_trace(flat, nF, ell_val;
                                                    step=betti_step, verbose=verbose)
        verbose && @printf("  Betti trace computed in %.3fs  (%d sample points)\n",
                           time() - t_bt, length(betti_tr))
        if verbose && !isempty(betti_tr)
            println("  Betti trace (selected):")
            shown = 0
            for (m_pt, b1_pt) in betti_tr
                (b1_pt > 0 || m_pt <= nF + 5 || shown < 4) && begin
                    @printf("    m=%d  b₁=%d\n", m_pt, b1_pt)
                    shown += 1
                end
                shown > 12 && break
            end
        end
    else
        # Minimal trace: just bracket around T_ker.
        F = Nemo.GF(ell_val)
        buf = Vector{Int}(undef, nF * nrel)
        for m_check in max(1, T_ker - 3):min(nrel, T_ker + 3)
            try
                Mm = prefix_matrix(F, flat, m_check, nF, buf)
                b1 = m_check - Nemo.rank(Mm)
                push!(betti_tr, (m_check, b1))
            catch
                # Non-fatal; skip this point.
            end
        end
        if verbose && !isempty(betti_tr)
            println("  Betti trace (±3 around T_ker):")
            for (m_pt, b1_pt) in betti_tr
                @printf("    m=%d  b₁=%d%s\n", m_pt, b1_pt,
                        m_pt == T_ker ? "  ← T_ker" : "")
            end
        end
    end

    # ── 4. Row-weight histogram at T_ker ──────────────────────────────────────
    wt_hist, avg_wt = row_weight_histogram(flat, T_ker, nF)
    if verbose
        @printf("  Row-weight histogram at T_ker=%d:\n", T_ker)
        for (w, c) in wt_hist
            @printf("    weight %2d: %d rows\n", w, c)
        end
        @printf("  Average row weight at T_ker: %.3f\n", avg_wt)
    end

    # ── 5. Spectral gap at T_ker (best-effort reuse of existing function) ─────
    gap_at_tker = NaN
    try
        gap_stats = spectral_gap_report(rel_rows[1:T_ker], nF;
                                        prefixes=[T_ker], verbose=false)
        if !isempty(gap_stats)
            gap_at_tker = gap_stats[1].gap
        end
        verbose && @printf("  Spectral gap at T_ker=%d: %.6f\n", T_ker,
                           isnan(gap_at_tker) ? 0.0 : gap_at_tker)
    catch e
        verbose && @printf("  [gap] spectral_gap_report failed: %s\n", string(e))
    end

    verbose && println("── End Kernel Phase Diagnostics ─────────────────────────────────")
    flush(stdout)

    return KernelPhaseDiag(
        nF, nrel,
        T_ker, delta,
        gamma_support_size, gamma_beta_proj, gamma_alpha_proj, gamma_solvable,
        k_candidate, k_correct,
        betti_tr, first_nonzero_betti,
        wt_hist, avg_wt,
        gap_at_tker
    )
end


# ---------------------------------------------------------------------------
#  Multi-trial Δ report
# ---------------------------------------------------------------------------
"""
    delta_report(delta_samples; nF=nothing)

Print a statistical summary of Δ = T_ker - nF collected across multiple trials.

`delta_samples` is a `Vector{Union{Int,Nothing}}` accumulated by pushing
`diag.delta` after each trial.  `nothing` entries (no kernel found) are counted
separately.
"""
function delta_report(delta_samples::Vector{Union{Int,Nothing}};
                      nF::Union{Int,Nothing}=nothing)

    isempty(delta_samples) && throw(ArgumentError("delta_report: delta_samples is empty"))

    n_total  = length(delta_samples)
    n_solved = count(!isnothing, delta_samples)
    n_failed = n_total - n_solved

    println()
    @printf("── Δ = T_ker - nF  Distribution Report ─────────────────────────────\n")
    nF !== nothing && @printf("  nF = %d\n", nF)
    @printf("  trials total:   %d\n", n_total)
    @printf("  solved (kernel found): %d  (%.1f%%)\n",
            n_solved, 100.0 * n_solved / n_total)
    @printf("  failed (no kernel):    %d\n", n_failed)

    if n_solved == 0
        println("  No solved trials — cannot compute Δ statistics.")
        println("── End Δ Report ─────────────────────────────────────────────────────")
        return
    end

    vals = Int[]
    sizehint!(vals, n_solved)
    for d in delta_samples
        d === nothing || push!(vals, d)
    end

    μ    = mean(vals)
    σ    = n_solved > 1 ? std(vals) : NaN
    med  = median(vals)
    mn   = minimum(vals)
    mx   = maximum(vals)

    @printf("  Δ statistics:\n")
    @printf("    mean   = %.3f\n", μ)
    @printf("    std    = %.3f\n", σ)
    @printf("    median = %.1f\n", med)
    @printf("    min    = %d\n",   mn)
    @printf("    max    = %d\n",   mx)

    sort!(vals)
    println("  Histogram (Δ → count):")
    i = 1
    while i <= length(vals)
        v = vals[i]
        j = i + 1
        while j <= length(vals) && vals[j] == v
            j += 1
        end
        c = j - i
        bar = repeat("█", min(c, 50))
        @printf("    Δ=%+3d : %3d  %s\\n", v, c, bar)
        i = j
    end
    println("── End Δ Report ─────────────────────────────────────────────────────")
    flush(stdout)
end


# ---------------------------------------------------------------------------
#  Convenience: multi-trial runner
#
#  Runs `n_trials` independent index_calculus_walk calls, accumulates Δ
#  samples and kernel-vector solvability rates, then calls delta_report.
#
#  Requires that `index_calculus_walk` returns a named tuple with fields
#  `rel_rows`, `alpha_vec`, `beta_vec`, and `nF` — or adjust the accessor
#  lambda `walk_result_extractor` accordingly.
#
#  Usage:
#      multi_trial_delta_run(G, T, 20; fb_size=200, ell_val=ell)
# ---------------------------------------------------------------------------
function multi_trial_delta_run(
        G, T,
        n_trials ::Int;
        fb_size  ::Int  = 200,
        ell_val::Integer  = ell,
        verbose_walk::Bool = false,
        verbose_diag::Bool = true)

    n_trials < 1 && throw(ArgumentError("multi_trial_delta_run: n_trials=$n_trials < 1"))

    delta_samples   = Union{Int,Nothing}[]
    n_solvable      = 0
    n_correct_k     = 0
    nF_observed     = nothing

    for trial in 1:n_trials
        @printf("\n[multi_trial] ── trial %d / %d ─────────────────────────────────\n",
                trial, n_trials)
        flush(stdout)

        # Run the walk with solve=false — we do our own targeted instrumentation.
        # index_calculus_walk now returns a NamedTuple with fields:
        #   k, rel_rows, alpha_vec, beta_vec, nF, shortfall
        wres = index_calculus_walk(G, T;
                                   fb_size        = fb_size,
                                   verbose        = verbose_walk,
                                   analyze_matrix = false,
                                   asymptotic     = false,
                                   solve          = false)

        if wres === nothing || wres.shortfall
            @printf("[multi_trial] trial %d: walk shortfall (too few relations)\n", trial)
            push!(delta_samples, nothing)
            continue
        end

        rr      = wres.rel_rows
        av      = wres.alpha_vec
        bv      = wres.beta_vec
        nF_obs  = wres.nF
        nF_observed === nothing && (nF_observed = nF_obs)

        diag = kernel_phase_instrumentation(rr, av, bv, nF_obs, ell_val;
                                            G       = G,
                                            T       = T,
                                            verbose = verbose_diag)

        push!(delta_samples, diag.delta)
        diag.gamma_solvable === true  && (n_solvable  += 1)
        diag.k_correct      === true  && (n_correct_k += 1)
    end

    delta_report(delta_samples; nF = nF_observed)
    @printf("  solvable kernel vectors:  %d / %d trials\n", n_solvable, n_trials)
    @printf("  correct k recovered:      %d / %d trials\n", n_correct_k, n_trials)
    flush(stdout)
    return delta_samples
end
