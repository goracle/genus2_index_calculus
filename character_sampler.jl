#!/usr/bin/env julia
#
# character_sampler_threaded.jl
#
# Threaded version of character_sampler.jl's core sampling loop.
#
# WHY THE ORIGINAL WASN'T THREADED
# ---------------------------------
# `julia -t 20` only allocates 20 OS threads for Julia to use; it does
# NOT retroactively parallelize a plain `for i in 1:m ... end` loop.
# The original run_character_sampler has no @threads / @spawn / Threads.@
# anywhere -- grep confirms it -- so `-t 20` changed nothing about how
# the loop executed. This file adds real parallelism to that loop.
#
# THE ONE REAL GOTCHA: RNG THREAD-SAFETY
# ----------------------------------------
# The original passes a single shared `rng::AbstractRNG` (typically a
# MersenneTwister) into `random_character` on every iteration. Calling
# a single non-thread-safe RNG concurrently from multiple tasks is a
# real bug -- at best it silently corrupts the statistical
# independence of your samples (shared mutable state race), at worst
# it segfaults or throws.
#
# The fix below splits the m samples into Threads.nthreads() static,
# contiguous chunks up front and @spawns one task per chunk, each
# closing over its own independently-seeded RNG. Each task only
# touches its own chunk's array indices and its own RNG -- there is no
# shared mutable state between tasks. Earlier drafts of this file
# instead indexed a per-thread RNG vector by threadid() inside
# @threads; that is UNSAFE under Julia's >=1.9 dynamic scheduler,
# since threadid() is not guaranteed to stay within 1:nthreads() (task
# migration between the default/interactive pools), and produced a
# BoundsError in practice. Do not index anything by threadid() -- tie
# per-task resources to the task/chunk itself via closures instead, as
# done in run_character_sampler_threaded below.
#
# Everything else (group model, S_F, semicircle comparison) is
# unchanged from character_sampler.jl -- included in full here as a
# standalone script so it can be dropped in and used directly.

using Random
using Printf
using Statistics
using Base.Threads: nthreads

# ---------------------------------------------------------------
# Group model (identical to character_sampler.jl)
# ---------------------------------------------------------------

struct AbelianGroup
    invariant_factors::Vector{Int}
end

order(G::AbelianGroup) = prod(BigInt.(G.invariant_factors))

function random_character(rng::AbstractRNG, G::AbelianGroup)
    while true
        chi = [rand(rng, 0:(d-1)) for d in G.invariant_factors]
        any(!=(0), chi) && return chi
    end
end

function character_value(chi_idx::Vector{Int}, x::Vector{Int}, invariant_factors::Vector{Int})
    phase = 0.0
    @inbounds for j in eachindex(chi_idx)
        phase += (chi_idx[j] * x[j]) / invariant_factors[j]
    end
    phase *= 2pi
    return cis(phase)
end

function S_F(chi_idx::Vector{Int}, F::Vector{Vector{Int}}, invariant_factors::Vector{Int})
    s = 0.0 + 0.0im
    @inbounds for x in F
        s += character_value(chi_idx, x, invariant_factors)
    end
    return s
end

# ---------------------------------------------------------------
# Threaded sampler
# ---------------------------------------------------------------

"""
    run_character_sampler_threaded(G, F; m, seed, k_size=nothing, report_every)

Threaded drop-in replacement for run_character_sampler. Splits the m
samples into Threads.nthreads() STATIC, CONTIGUOUS CHUNKS up front and
@spawns one task per chunk, each closing over its own independently-
seeded RNG (seed XOR'd with chunk index -- deterministic given `seed`
and the thread count). Each task writes only to the indices in its own
chunk, so there is no shared-state race on either the RNGs or the
output arrays.

Earlier version of this function indexed a per-thread RNG vector by
threadid() inside @threads -- that is UNSAFE under Julia's >=1.9
dynamic scheduler, since threadid() is not guaranteed to stay within
1:nthreads() (task migration between the default/interactive pools),
which produced a BoundsError in practice. The fix is to never index
anything by threadid(); tie per-task resources (like an RNG) to the
task/chunk itself via closures instead, as done here.

Returns the same named tuple shape as the original: chis, S_vals,
U_vals, M8_running, M4_running, k_size -- the *_running vectors are
still valid running estimates at each prefix length i (computed by a
cheap serial O(m) pass over the per-sample magnitudes after the
parallel part completes), so all downstream code (summarize_tail,
ratio prints, plotting) works unchanged.

NOTE ON REPRODUCIBILITY: results are deterministic for a fixed
(seed, nthreads()) pair, but changing the thread count changes the
chunk boundaries and hence which RNG stream produces which sample, so
results will NOT bit-for-bit match a different thread count or the
single-threaded original (different, but equally valid, samples of
the same distribution). This is standard for parallel MC and not a
bug -- compare summary statistics (means, ratios, tail counts), not
raw per-sample sequences, across thread counts.

Cost: same O(m * |F|) total work, wall-clock divided across threads
(up to per-thread overhead / false sharing near the boundaries).
"""
function run_character_sampler_threaded(G::AbelianGroup, F::Vector{Vector{Int}};
                                          m::Int,
                                          seed::Int = 1,
                                          k_size::Union{Nothing,Real} = nothing,
                                          report_every::Int = max(1, m ÷ 20))
    Gord = Float64(order(G))
    Gord_nontrivial = Gord - 1.0
    ksz  = k_size === nothing ? Gord^(1.0 / length(G.invariant_factors)) : Float64(k_size)

    nt = nthreads()
    println("Sampling $m non-trivial characters of a group of order ~$(Gord) ",
            "(|F| = $(length(F))) across $nt thread(s)...")
    if nt == 1
        @warn "nthreads() == 1 -- Julia was not started with multiple threads. " *
              "Run with `julia -t auto` or `julia -t N` (N>1) to actually use " *
              "multiple threads; this script cannot create OS threads Julia " *
              "wasn't started with."
    end

    chis    = Vector{Vector{Int}}(undef, m)
    S_vals  = Vector{ComplexF64}(undef, m)
    U_vals  = Vector{ComplexF64}(undef, m)
    mag4v   = Vector{Float64}(undef, m)
    mag8v   = Vector{Float64}(undef, m)

    # IMPORTANT: threadid() is NOT safe to use as a 1:nthreads() array
    # index since Julia 1.9's dynamic scheduler (interactive/default
    # thread pools, task migration) -- it can return values outside
    # 1:nthreads(), which is exactly what produced the BoundsError
    # above. Do not index a per-thread resource by threadid(). Instead,
    # split the work into nt STATIC CHUNKS up front and @spawn one task
    # per chunk, each closing over its own local RNG -- this ties the
    # RNG to the task/chunk, never to a thread id, so it's correct
    # regardless of how the scheduler assigns chunks to OS threads.
    chunk_bounds = let
        bounds = Vector{UnitRange{Int}}(undef, nt)
        base, rem = divrem(m, nt)
        lo = 1
        for t in 1:nt
            len = base + (t <= rem ? 1 : 0)
            bounds[t] = lo:(lo + len - 1)
            lo += len
        end
        bounds
    end

    tasks = Vector{Task}(undef, nt)
    for t in 1:nt
        rng_t = MersenneTwister(seed ⊻ (0x9E3779B9 * t))   # local to this task/closure
        range_t = chunk_bounds[t]
        tasks[t] = Threads.@spawn begin
            for i in range_t
                chi = random_character(rng_t, G)
                s   = S_F(chi, F, G.invariant_factors)
                mag2 = abs2(s)
                mag4 = mag2 * mag2
                mag8 = mag4 * mag4

                chis[i]   = chi
                S_vals[i] = s
                U_vals[i] = s / sqrt(ksz)
                mag4v[i]  = mag4
                mag8v[i]  = mag8
            end
        end
    end
    foreach(wait, tasks)

    # Running estimates are inherently sequential (cumulative mean up
    # to index i) -- reconstruct them as a cheap serial pass over the
    # already-computed per-sample magnitudes. This is O(m), negligible
    # next to the O(m*|F|) parallel part above.
    M8_running = Vector{Float64}(undef, m)
    M4_running = Vector{Float64}(undef, m)
    sum8 = 0.0
    sum4 = 0.0
    for i in 1:m
        sum8 += mag8v[i]
        sum4 += mag4v[i]
        M8_running[i] = Gord_nontrivial * (sum8 / i)
        M4_running[i] = Gord_nontrivial * (sum4 / i)
        if i % report_every == 0 || i == m
            @printf("  [%6d/%6d]  running M4_hat = %.4e   running M8_hat = %.4e\n",
                    i, m, M4_running[i], M8_running[i])
        end
    end

    return (; chis, S_vals, U_vals, M8_running, M4_running, k_size = ksz)
end

# ---------------------------------------------------------------
# Semicircle comparison (identical to character_sampler.jl)
# ---------------------------------------------------------------

function semicircle_pdf(x::Real)
    (abs(x) > 2) && return 0.0
    return sqrt(4 - x^2) / (2pi)
end

function summarize_tail(U_vals::Vector{ComplexF64}; bound::Real = 2.0)
    mags = abs.(U_vals)
    n_over = count(>(bound), mags)
    frac_over = n_over / length(mags)
    println("\n--- Tail summary (|U(chi)|, target bound = $bound) ---")
    @printf("  samples exceeding bound: %d / %d  (%.4f%%)\n",
            n_over, length(mags), 100 * frac_over)
    @printf("  max |U(chi)| observed:   %.4f\n", maximum(mags))
    @printf("  mean |U(chi)|:           %.4f   (semicircle mean |Tr|: ~1.273)\n",
            mean(mags))
    return (; n_over, frac_over, max_mag = maximum(mags))
end

# ---------------------------------------------------------------
# Sidon helpers (identical to character_sampler.jl)
# ---------------------------------------------------------------

function greedy_sidon_subset(N::Int, target_size::Int, rng::AbstractRNG)
    elems = Int[]
    sums_seen = Set{Int}()
    candidates = collect(0:(N-1))
    Random.shuffle!(rng, candidates)
    for x in candidates
        ok = true
        new_sums = Int[]
        for y in elems
            s = mod(x + y, N)
            if s in sums_seen
                ok = false
                break
            end
            push!(new_sums, s)
        end
        if ok
            s2 = mod(2x, N)
            (s2 in sums_seen) && (ok = false)
        end
        if ok
            push!(elems, x)
            union!(sums_seen, new_sums)
            push!(sums_seen, mod(2x, N))
        end
        length(elems) >= target_size && break
    end
    return elems
end

function sidon_defect(elems::Vector{Int}, N::Int)
    counts = Dict{Int,Int}()
    for i in eachindex(elems), j in i:length(elems)
        g = mod(elems[i] + elems[j], N)
        counts[g] = get(counts, g, 0) + 1
    end
    return sum(v - 1 for v in values(counts) if v > 1; init = 0)
end

# ---------------------------------------------------------------
# Demo / smoke test (threaded)
# ---------------------------------------------------------------

function demo_threaded(; N::Int = 100_003,
                          B::Int = round(Int, N^0.4),
                          m::Int = 20_000,
                          seed::Int = 1)
    rng = MersenneTwister(seed)
    G = AbelianGroup([N])

    F_int = greedy_sidon_subset(N, B, rng)
    defect = sidon_defect(F_int, N)
    println("=== Threaded smoke test: cyclic group Z/$N, |F| = $(length(F_int)) ===")
    println("Sidon defect: $defect")
    F = [[x] for x in F_int]

    t0 = time()
    result = run_character_sampler_threaded(G, F; m = m, seed = seed, k_size = N)
    elapsed = time() - t0
    @printf("elapsed: %.3fs  (%.1f samples/sec, %d thread(s))\n",
            elapsed, m / elapsed, nthreads())

    summarize_tail(result.U_vals)
    Bf = Float64(length(F_int))
    @printf("ratio MC-estimate / flat-B^8-over-N = %.4f\n",
            result.M8_running[end] / ((Bf^8) / N))

    return result
end

if abspath(PROGRAM_FILE) == @__FILE__
    demo_threaded()
end
