# =============================================================================
#  lp1_conj_deep_diag_d19.jl  --  D19: Factor-base element productivity.
#
#  Answers: which factor-base elements (by index i0 / prev_col) participate
#  most frequently in LP1-conj closures?
#
#  Data source
#  ───────────
#  ConjDeepStat.d19_fb_close_counts  ::Dict{Int,Int}
#      fb_index → number of closure events that touched this element
#      (each closure increments both i0 and prev_col independently,
#       so a single closure adds 2 counts total across the dict).
#
#  ConjDeepStat.d19_fb_pair_counts   ::Dict{NTuple{2,Int},Int}
#      (min(i0,prev_col), max(i0,prev_col)) → co-occurrence count
#      Capped at D19_MAX_PAIRS to bound memory.
#
#  ConjDeepStat.d19_anchor_sample_rels ::Dict{Int, Vector{NTuple{4,Int}}}
#      fb_index → up to 5 sample relations as (i0, prev_col, combined_al, combined_be)
#      tuples, keyed by whichever of i0/prev_col is the "anchor" (higher-count)
#      side.  Populated by record_d19_closure! alongside d19_fb_close_counts.
#      (See lp1_conj_deep_diag_core.jl for struct field and recorder.)
#
#  Report sections
#  ───────────────
#  D19-A  Top-50 FB elements by closure count; Gini + Hill exponent.
#  D19-B  Top-20×20 co-occurrence sub-matrix for the hottest elements.
#  D19-C  Marginal asymmetry: elements that appear significantly more
#         often as the *current* anchor (i0) vs. the *stored* anchor
#         (prev_col).  Requires the split counters.
#
#  Wiring (see lp1_conj_deep_diag.jl and lp1_conj_deep_diag_core.jl)
#  ───────────────────────────────────────────────────────────────────
#  1.  record_d19_closure! called from handle_1lp_conj! at every CLOSE,
#      passing both i0 and prev_col.
#  2.  _report_d19 called from print_conj_deep_report after _report_d12_d18.
# =============================================================================

# ---------------------------------------------------------------------------
#  _report_d19
# ---------------------------------------------------------------------------
function _report_d19(deep_stat::ConjDeepStat; fb_size::Int = 0)

    fc      = deep_stat.d19_fb_close_counts      # Dict{Int,Int}
    fc_i    = deep_stat.d19_fb_i0_counts         # Dict{Int,Int}  (i0 side)
    fc_p    = deep_stat.d19_fb_prev_counts        # Dict{Int,Int}  (prev_col side)
    pair    = deep_stat.d19_fb_pair_counts        # Dict{NTuple{2,Int},Int}
    samples = deep_stat.d19_anchor_sample_rels    # Dict{Int,Vector{NTuple{4,Int}}}

    @printf("\n── D19: Factor-base element productivity ────────────────────────────\n")

    n_tracked = length(fc)
    n_pairs   = length(pair)
    @printf("  Tracked FB elements : %d%s\n",
            n_tracked,
            fb_size > 0 ? " / $(fb_size)" : "")
    @printf("  Tracked FB pairs    : %d\n", n_pairs)

    if n_tracked == 0
        @printf("  (no closure data — skipping D19)\n")
        return
    end

    # ── D19-A: Top-50 elements ──────────────────────────────────────────
    @printf("\n  D19-A  Top-50 FB elements by closure participation\n")
    @printf("  %-8s  %-10s  %-10s  %-10s  %-8s\n",
            "fb_idx", "total", "as_i0", "as_prev", "asym_%")

    sorted_all = sort(collect(fc), by = kv -> kv[2], rev = true)
    top_n      = min(50, length(sorted_all))
    top_idxs   = [kv[1] for kv in sorted_all[1:top_n]]

    for idx in top_idxs
        tot  = fc[idx]
        ci0  = get(fc_i, idx, 0)
        cprev = get(fc_p, idx, 0)
        asym = tot > 0 ? 100.0 * (ci0 - cprev) / tot : 0.0
        @printf("  %-8d  %-10d  %-10d  %-10d  %+.1f%%\n",
                idx, tot, ci0, cprev, asym)
    end

    # ── D19-A sample relations for top-5 anchors ────────────────────────
    @printf("\n  D19-A  Sample relations for top-5 anchors\n")
    top5_idxs = top_idxs[1:min(5, top_n)]
    for anchor in top5_idxs
        tot  = fc[anchor]
        ci0  = get(fc_i, anchor, 0)
        cprev = get(fc_p, anchor, 0)
        @printf("  Anchor fb[%d]  (total=%d  as_i0=%d  as_prev=%d)\n",
                anchor, tot, ci0, cprev)
        rels = get(samples, anchor, NTuple{4,Int}[])
        if isempty(rels)
            @printf("    (no sample relations recorded)\n")
        else
            @printf("    %-6s  %-8s  %-8s  %-12s  %-12s\n",
                    "i0", "prev_col", "row", "combined_al", "combined_be")
            for (i0_s, pc_s, al_s, be_s) in rels[1:min(5, length(rels))]
                # row is always {i0=>+1, prev_col=>-1}
                @printf("    %-6d  %-8d  [%d:+1, %d:-1]  %-12d  %-12d\n",
                        i0_s, pc_s, i0_s, pc_s, al_s, be_s)
            end
        end
    end

    # ── D19-A tail statistics ────────────────────────────────────────────
    all_counts = [kv[2] for kv in sorted_all]
    total_hits = sum(all_counts)
    gini_val   = _gini(all_counts)
    hill_val   = _hill_exponent(all_counts; k = min(50, length(all_counts) - 1))
    top1_share = n_tracked > 0 ? all_counts[1] / max(1, total_hits) : 0.0
    top5_share = _top_share(all_counts, 5.0 / max(1, n_tracked))

    @printf("\n  Total closure participations (2× closures)  : %d\n", total_hits)
    @printf("  Gini coefficient                            : %.4f\n", gini_val)
    @printf("  Hill tail exponent (k=50)                   : %.4f\n", hill_val)
    @printf("  Top-1  share                                : %.2f%%\n", 100.0 * top1_share)
    @printf("  Top-5  share                                : %.2f%%\n", 100.0 * top5_share)

    # ── D19-B: Co-occurrence sub-matrix for top-20 ──────────────────────
    @printf("\n  D19-B  Co-occurrence sub-matrix (top-%d × top-%d)\n",
            min(20, top_n), min(20, top_n))

    hot = top_idxs[1:min(20, top_n)]
    nh  = length(hot)
    idx_to_pos = Dict{Int,Int}(hot[i] => i for i in 1:nh)

    # Print header row.
    @printf("  %8s", "")
    for j in 1:nh
        @printf("  %6d", hot[j])
    end
    @printf("\n")

    for i in 1:nh
        @printf("  %8d", hot[i])
        for j in 1:nh
            if i == j
                @printf("  %6s", "——")
            else
                lo, hi = minmax(hot[i], hot[j])
                cnt = get(pair, (lo, hi), 0)
                if cnt == 0
                    @printf("  %6s", ".")
                else
                    @printf("  %6d", cnt)
                end
            end
        end
        @printf("\n")
    end

    # ── D19-C: Marginal asymmetry summary ───────────────────────────────
    @printf("\n  D19-C  Asymmetry summary (i0-biased vs prev_col-biased elements)\n")
    @printf("  %-8s  %-10s  %-10s  %-10s  %-10s\n",
            "fb_idx", "total", "as_i0", "as_prev", "asym")

    # Build asymmetry list for elements with >= 10 total hits.
    asym_list = Tuple{Int, Int, Int, Int, Float64}[]
    for (idx, tot) in fc
        tot < 10 && continue
        ci0   = get(fc_i, idx, 0)
        cprev = get(fc_p, idx, 0)
        asym  = (ci0 - cprev) / Float64(tot)
        push!(asym_list, (idx, tot, ci0, cprev, asym))
    end

    # Most i0-biased (tend to initiate closures).
    sort!(asym_list, by = t -> t[5], rev = true)
    @printf("  -- Most i0-biased (top 10) --\n")
    for (idx, tot, ci0, cprev, asym) in asym_list[1:min(10, length(asym_list))]
        @printf("  %-8d  %-10d  %-10d  %-10d  %+.3f\n",
                idx, tot, ci0, cprev, asym)
    end

    # Most prev_col-biased (tend to be the stored / matched element).
    @printf("  -- Most prev_col-biased (top 10) --\n")
    for (idx, tot, ci0, cprev, asym) in reverse(asym_list)[1:min(10, length(asym_list))]
        @printf("  %-8d  %-10d  %-10d  %-10d  %+.3f\n",
                idx, tot, ci0, cprev, asym)
    end

    flush(stdout)
    return nothing
end
