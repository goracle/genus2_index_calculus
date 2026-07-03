# =============================================================================
#  trial3_anchor_sweep_diag.jl — anchor-neighborhood independence measurement.
#
#  PURPOSE
#  -------
#  Before implementing rank-1 (Sherman-Morrison-Woodbury / symbolic-Cramer)
#  updates for build_phi_general!, we need one number the math can't give us:
#  for a fixed walk state (a "base" K-tuple of anchors + Mumford divisor D),
#  if we replace exactly one anchor P_k with every other factor-base point,
#  are the resulting residuals close to independent fresh samples, or do
#  they collapse to essentially the same relation / all fail the same way?
#
#  This module brute-forces that measurement using the EXISTING numeric
#  path (step_phi_k!) — no linear-algebra speedup implemented or assumed.
#  It reuses ThreadScratchpad{K}, ok. Wire it in behind a CLI flag or run it
#  standalone from a REPL against a handful of real base tuples pulled out
#  of a live walk.
#
#  WHAT TO LOOK AT IN THE OUTPUT
#  ------------------------------
#    - dup_rate: fraction of successful candidates whose relation_key
#      (canonical hash of the sorted residual roots) collides with an
#      earlier candidate in the SAME sweep. High dup_rate = neighborhood
#      is degenerate, the idea dies. Near-zero = good sign.
#    - roots_count / u_RS_len distributions: compare the sweep's empirical
#      distribution against your existing D27/D28 baseline distributions
#      from ordinary (non-swept) walk steps. If they look statistically
#      indistinguishable, the neighborhood is behaving like fresh samples.
#      If the sweep distribution is much narrower/spikier, that's
#      correlation.
#    - lp_hit_rate (fraction of successful candidates with ZERO roots
#      landing in the factor base, i.e. candidates that could only close
#      via LP1/LP2 store rather than an immediate 0-LP hit): compare
#      against your baseline 0lp/1lp/... rates from report_worker_progress.
#
#  ASSUMPTIONS TO VERIFY AGAINST YOUR ACTUAL CLASSIFIER
#  ------------------------------------------------------
#  This file only has trial3_phase2.jl and trial3_phi_general.jl to go on.
#  In particular:
#    - `pt2idx` is used exactly as at trial3_phase2.jl:2036/2043/2123 —
#      Dict{NTuple{2,Int},Int} (or equivalent), get(pt2idx, pt, 0) != 0
#      means pt is a factor-base point.
#    - "relation_key" here is a cheap proxy (hash of sorted residual
#      roots), NOT your real handle_1lp_affine!/handle_2lp_affine!/
#      handle_1lp_conj! classification. It's meant to catch gross
#      degeneracy (literally the same intersection points recurring),
#      not to reproduce your LP-store dedup logic exactly. If you want
#      the real closure/dup semantics, swap relation_key's body for a
#      call into whatever canonicalizes rows in your LP1/LP2 tables.
# =============================================================================

using Printf

# Include this AFTER trial3_phi_general.jl (needs FpArith/StandardArith/p,
# ThreadScratchpad, rr_basis_cached, build_phi_general!, phi_residual_general!
# all already defined) — same convention as conj_closure_dataset.jl.

# ---------------------------------------------------------------------------
#  SweepOutcome — one record per candidate anchor replacement.
# ---------------------------------------------------------------------------
struct SweepOutcome
    candidate      ::NTuple{2,Int}
    stage          ::Symbol   # :ok, :fail_build, :fail_residual, :skipped_degenerate
    roots_count    ::Int      # scratch.roots_count[1] at success, else 0
    roots_in_fb    ::Int      # how many of those roots are factor-base points
    u_rs_len       ::Int      # scratch.u_RS_len[1] (residual poly length; degree = len-1)
    relation_key   ::UInt64   # canonical hash of sorted residual roots (0 if not :ok)
end

# ---------------------------------------------------------------------------
#  relation_key — canonical hash of the residual root set.
#
#  Sorting first makes this order-invariant (root-finding order shouldn't
#  matter for "is this the same relation"). This is a coarse dedup proxy —
#  see the module docstring above for what it isn't.
# ---------------------------------------------------------------------------
function relation_key(scratch::ThreadScratchpad{K})::UInt64 where K
    n = scratch.roots_count[1]
    n == 0 && return zero(UInt64)
    pts = Vector{NTuple{2,Int}}(undef, n)
    @inbounds for i in 1:n
        pts[i] = scratch.roots_out[i]
    end
    sort!(pts)
    h = hash(:relation_key)
    for pt in pts
        h = hash(pt, h)
    end
    return h
end

# ---------------------------------------------------------------------------
#  sweep_one_anchor! — the core experiment.
#
#  base_anchors : the fixed K-tuple (walk state) to perturb.
#  slot         : which anchor index (1..K) to replace.
#  candidates   : points to try in that slot (e.g. a few hundred sampled
#                 factor-base elements — pass your existing `fb` vector, or
#                 a random subsample of it for cost reasons).
#  pt2idx       : factor-base membership map, same convention as
#                 trial3_phase2.jl (get(pt2idx, pt, 0) != 0 => in FB).
#
#  Candidates equal to the current value of `slot`, or equal to any of the
#  OTHER k-1 fixed anchors, are skipped (:skipped_degenerate) — the former
#  is a no-op measurement, the latter would push build_phi_general! into
#  its m>=2 tangency path, which is a structurally different row (not the
#  clean "one row swapped" case this experiment is meant to characterize).
# ---------------------------------------------------------------------------
function sweep_one_anchor!(
    scratch    ::ThreadScratchpad{K},
    base_anchors::NTuple{K,NTuple{2,Int}},
    slot       ::Int,
    candidates ::AbstractVector{NTuple{2,Int}},
    u0::Int, u1::Int, v0::Int, v1::Int,
    pt2idx;
    backend::FpArith = StandardArith(p)
)::Vector{SweepOutcome} where K

    @assert 1 <= slot <= K "slot=$slot out of range 1:$K"

    out = Vector{SweepOutcome}(undef, 0)
    sizehint!(out, length(candidates))

    other_anchors = ntuple(i -> base_anchors[i], Val(K))  # copy for closure clarity

    for cand in candidates
        # Skip: identity replacement, or collision with another fixed anchor
        # (both change the row structure away from the "one clean row swap"
        # case — see docstring above).
        is_degenerate = (cand == base_anchors[slot])
        if !is_degenerate
            for i in 1:K
                i == slot && continue
                if other_anchors[i] == cand
                    is_degenerate = true
                    break
                end
            end
        end
        if is_degenerate
            push!(out, SweepOutcome(cand, :skipped_degenerate, 0, 0, 0, zero(UInt64)))
            continue
        end

        new_anchors = ntuple(i -> i == slot ? cand : base_anchors[i], Val(K))

        success_build = build_phi_general!(scratch, new_anchors, u0, u1, v0, v1; backend=backend)
        if !success_build
            push!(out, SweepOutcome(cand, :fail_build, 0, 0, 0, zero(UInt64)))
            continue
        end

        nb = K + 3
        basis = rr_basis_cached(nb)::Vector{NTuple{2,Int}}
        success_residual = phi_residual_general!(scratch, basis, new_anchors, u0, u1)
        if !success_residual || scratch.u_RS_is_fail[1]
            push!(out, SweepOutcome(cand, :fail_residual, 0, 0, 0, zero(UInt64)))
            continue
        end

        rc = scratch.roots_count[1]
        in_fb = 0
        @inbounds for i in 1:rc
            get(pt2idx, scratch.roots_out[i], 0) != 0 && (in_fb += 1)
        end
        rk = relation_key(scratch)
        push!(out, SweepOutcome(cand, :ok, rc, in_fb, scratch.u_RS_len[1], rk))
    end

    return out
end

# ---------------------------------------------------------------------------
#  summarize_sweep — prints the numbers you actually asked for:
#  residual distribution, LP-hit proxy, duplicate rate, emission rate.
# ---------------------------------------------------------------------------
function summarize_sweep(out::Vector{SweepOutcome}; label::String = "")
    n_total    = length(out)
    n_skip     = count(o -> o.stage == :skipped_degenerate, out)
    n_fb       = count(o -> o.stage == :fail_build,         out)
    n_fr       = count(o -> o.stage == :fail_residual,      out)
    ok         = filter(o -> o.stage == :ok, out)
    n_ok       = length(ok)
    n_attempted = n_total - n_skip

    tag = isempty(label) ? "" : " $label"
    @printf("[SWEEP%s] candidates=%d  skipped(degenerate)=%d  attempted=%d\n",
            tag, n_total, n_skip, n_attempted)
    if n_attempted == 0
        @printf("[SWEEP%s] nothing attempted — check candidate list / base tuple.\n", tag)
        return
    end
    @printf("[SWEEP%s] fail_build=%d (%.1f%%)  fail_residual=%d (%.1f%%)  ok=%d (%.1f%%)\n",
            tag, n_fb, 100.0*n_fb/n_attempted, n_fr, 100.0*n_fr/n_attempted,
            n_ok, 100.0*n_ok/n_attempted)

    if n_ok == 0
        @printf("[SWEEP%s] no successful candidates — nothing further to report.\n", tag)
        return
    end

    # residual distribution
    rc_vals = [o.roots_count for o in ok]
    ul_vals = [o.u_rs_len    for o in ok]
    @printf("[SWEEP%s] roots_count: mean=%.2f  min=%d  max=%d\n",
            tag, sum(rc_vals)/n_ok, minimum(rc_vals), maximum(rc_vals))
    @printf("[SWEEP%s] u_RS_len:    mean=%.2f  min=%d  max=%d\n",
            tag, sum(ul_vals)/n_ok, minimum(ul_vals), maximum(ul_vals))

    # LP-hit proxy: fraction of ok candidates with zero roots landing in FB
    # (i.e. everything found is a large-prime candidate, not an immediate
    # 0-LP close). Cross-check this rate against your baseline
    # report_worker_progress 0lp/1lp/2lp rates for non-swept steps.
    n_zero_fb = count(o -> o.roots_in_fb == 0, ok)
    @printf("[SWEEP%s] candidates with 0 roots-in-FB: %d/%d (%.1f%%)  — proxy for \"needs LP store\"\n",
            tag, n_zero_fb, n_ok, 100.0*n_zero_fb/n_ok)

    # duplicate rate via relation_key collisions
    seen = Dict{UInt64,Int}()
    dup_count = 0
    for o in ok
        c = get(seen, o.relation_key, 0)
        dup_count += c > 0 ? 1 : 0
        seen[o.relation_key] = c + 1
    end
    n_unique = length(seen)
    @printf("[SWEEP%s] relation_key: %d unique / %d ok  (dup_rate=%.1f%%)\n",
            tag, n_unique, n_ok, 100.0*dup_count/n_ok)
    if dup_count > 0
        top = sort(collect(seen), by = kv -> -kv[2])[1:min(5,end)]
        @printf("[SWEEP%s] most-repeated relation_key counts: %s\n", tag,
                join(["$(c)" for (_,c) in top], ", "))
    end
    flush(stdout)
end

# ---------------------------------------------------------------------------
#  write_sweep_csv — raw per-candidate rows for offline analysis (histograms,
#  correlation with px distance-from-nothing, etc. in Python/Julia/whatever).
# ---------------------------------------------------------------------------
function write_sweep_csv(path::AbstractString, base_id::Int, out::Vector{SweepOutcome})
    open(path, "a") do io
        for o in out
            @printf(io, "%d,%d,%d,%s,%d,%d,%d,%s\n",
                    base_id, o.candidate[1], o.candidate[2], String(o.stage),
                    o.roots_count, o.roots_in_fb, o.u_rs_len, string(o.relation_key))
        end
    end
    return nothing
end

function write_sweep_csv_header(path::AbstractString)
    open(path, "w") do io
        println(io, "base_id,cand_px,cand_py,stage,roots_count,roots_in_fb,u_rs_len,relation_key")
    end
    return nothing
end

# ---------------------------------------------------------------------------
#  run_anchor_sweep_experiment — top-level driver over several base tuples.
#
#  base_tuples: Vector of (anchors::NTuple{K,...}, u0,u1,v0,v1) — pull these
#  from a live walk (e.g. log cur_anchors/u0/u1/v0/v1 the first N times
#  step_phi_k! succeeds, then feed them in here) so the base states are
#  representative of what the real walk actually visits, not synthetic ones.
#
#  slot: which anchor position to sweep (try slot=K, i.e. the most recently
#  assigned anchor, first — matches the "extend a live walk state" framing
#  from the original proposal).
#
#  candidates: shared candidate list applied to every base tuple (e.g. 200
#  random fb points, resampled per base tuple if you want less shared
#  structure across trials — resampling is the more conservative choice).
# ---------------------------------------------------------------------------
function run_anchor_sweep_experiment(
    scratch     ::ThreadScratchpad{K},
    base_tuples ::AbstractVector{<:Tuple{NTuple{K,NTuple{2,Int}},Int,Int,Int,Int}},
    slot        ::Int,
    candidates  ::AbstractVector{NTuple{2,Int}},
    pt2idx;
    backend     ::FpArith = StandardArith(p),
    csv_path    ::Union{Nothing,String} = nothing
) where K

    csv_path !== nothing && write_sweep_csv_header(csv_path)

    all_out = SweepOutcome[]   # every outcome (ok + fail_build + fail_residual + skipped)
    for (base_id, (anchors, u0, u1, v0, v1)) in enumerate(base_tuples)
        out = sweep_one_anchor!(scratch, anchors, slot, candidates, u0, u1, v0, v1, pt2idx; backend=backend)
        summarize_sweep(out; label = "base=$base_id slot=$slot")
        csv_path !== nothing && write_sweep_csv(csv_path, base_id, out)
        append!(all_out, out)
    end

    @printf("\n[SWEEP] ==== aggregate across %d base tuples ====\n", length(base_tuples))
    # NOTE: dup_rate in this aggregate view is pooled across ALL base tuples,
    # so it conflates "duplicates within one base tuple's neighborhood" with
    # "different base tuples happening to produce the same relation" — the
    # per-base-tuple lines printed above (one per base_id) are the ones that
    # actually answer the "is one walk state's neighborhood degenerate"
    # question; use this aggregate line only for the overall fail-rate /
    # roots_count / u_RS_len distribution, not for dup_rate.
    summarize_sweep(all_out; label = "AGGREGATE")
    return filter(o -> o.stage == :ok, all_out)
end
