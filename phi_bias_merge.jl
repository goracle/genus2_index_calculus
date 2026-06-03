# =============================================================================
#  phi_bias_merge.jl  --  Per-thread stat reduction.
# =============================================================================

# ---------------------------------------------------------------------------
#  merge_phi_bias_stats — reduce per-thread stats into one aggregate.
# ---------------------------------------------------------------------------
function merge_phi_bias_stats(stats::Vector{PhiBiasStat})::PhiBiasStat
    isempty(stats) && error("merge_phi_bias_stats: empty input")
    # Use first element as prototype for bucket count.
    p_dummy = length(stats[1].split_hist)^2   # approximate p (bucket count = √p)
    merged = PhiBiasStat(p_dummy)
    # Resize histograms to match (they should all be the same length).
    nb = length(stats[1].split_hist)
    resize!(merged.split_hist,       nb); fill!(merged.split_hist,       0)
    resize!(merged.nonsplit_hist,    nb); fill!(merged.nonsplit_hist,    0)
    resize!(merged.post_lp_a_hist,   nb); fill!(merged.post_lp_a_hist,  0)
    resize!(merged.baseline_a_hist,  nb); fill!(merged.baseline_a_hist, 0)
    resize!(merged.lp1_conj_a_hist,  nb); fill!(merged.lp1_conj_a_hist, 0)
    resize!(merged.run_hist_split,    MAX_RUN_LEN); fill!(merged.run_hist_split,    0)
    resize!(merged.run_hist_nonsplit, MAX_RUN_LEN); fill!(merged.run_hist_nonsplit, 0)

    for s in stats
        merged.total            += s.total
        merged.a_zero           += s.a_zero
        merged.a_zero_split     += s.a_zero_split
        merged.a_zero_fb        += s.a_zero_fb
        merged.image_collisions += s.image_collisions
        for i in eachindex(merged.split_hist)
            merged.split_hist[i]       += s.split_hist[i]
            merged.nonsplit_hist[i]    += s.nonsplit_hist[i]
            merged.post_lp_a_hist[i]   += s.post_lp_a_hist[i]
            merged.baseline_a_hist[i]  += s.baseline_a_hist[i]
            merged.lp1_conj_a_hist[i]  += s.lp1_conj_a_hist[i]
        end
        for k in 1:MAX_RUN_LEN
            merged.run_hist_split[k]    += s.run_hist_split[k]
            merged.run_hist_nonsplit[k] += s.run_hist_nonsplit[k]
        end
        # α₂ timeseries: concatenate LP1-conj partial stream across threads, capped.
        merged._event_hash_state ⊻= s._event_hash_state   # fold per-thread digests
        let n_rem = MAX_LP1_CONJ_BLOG - length(merged.lp1_conj_key_blog)
            if n_rem > 0
                n_take = min(n_rem, length(s.lp1_conj_key_blog))
                append!(merged.lp1_conj_key_blog, s.lp1_conj_key_blog[1:n_take])
            end
        end
        let n_rem = MAX_LP1_CONJ_ARRIVALS - length(merged.lp1_conj_arrivals)
            if n_rem > 0
                n_take = min(n_rem, length(s.lp1_conj_arrivals))
                append!(merged.lp1_conj_arrivals,  s.lp1_conj_arrivals[1:n_take])
                append!(merged.lp1_conj_keys,      s.lp1_conj_keys[1:n_take])
                append!(merged.lp1_conj_bucket_log, s.lp1_conj_bucket_log[1:n_take])
            end
        end
    end
    return merged
end
