# =============================================================================
#  lp1_conj_deep_diag_d22_d24.jl
#
#  D22 — Entry-event burst geometry
#         "What walks into a productive micro-configuration?"
#         Conditions on cold-entry emissions (gap ≥ mean/2) and reports
#         the burst-size distribution, key-bucket entropy, and a-bucket
#         entropy of burst openers.  High concentration → algebraically
#         thin entry surface.
#
#  D23 — Kill-renewal cascade probe (observational)
#         Counts additional LP1-conj emissions within D23_CASCADE_WINDOW steps
#         of each emission without modifying the walk.  Separates cold-entry
#         cascades (gap_to_prev ≥ mean/2) from warm-entry cascades (in-burst).
#         Answers: "are bursts 1-hit or multi-hit, and does cold vs warm matter?"
#
#  D24 — Cross-thread burst alignment
#         Checks whether emission-containing step-buckets (width D24_BUCKET_STEPS)
#         co-occur across ≥2 threads.  High co-occurrence → global walk structure
#         (e.g. shared FB geometry).  Low co-occurrence → purely thread-local
#         phenomenon.
#
#  All three diagnostics are designed to remain meaningful even with N=32
#  emissions by using coarse bucketing and relative statistics.
#
#  Relationship to prior diagnostics:
#    D22 isolates the *entry* into productive regions (vs D4 which measures
#        persistence once inside).
#    D23 is the observational equivalent of GPT's "kill-renewal and see what
#        happens" experiment — we measure the actual cascade multiplicity
#        without modifying the walk.
#    D24 provides the cross-thread test GPT suggested; it costs one dict-insert
#        per emission per thread.
# =============================================================================

# ---------------------------------------------------------------------------
#  _report_d22 — Entry-event burst geometry
# ---------------------------------------------------------------------------
function _report_d22(deep_stat::ConjDeepStat)
    @printf("\n  D22 — Entry-event burst geometry\n")
    @printf("  ─────────────────────────────────────────────────────────────────\n")

    burst_sizes   = deep_stat.d22_burst_sizes
    cold_entries  = deep_stat.d22_cold_entries
    n_bursts      = length(burst_sizes)
    n_cold        = length(cold_entries)

    @printf("    Total finalised bursts       : %d\n", n_bursts)
    @printf("    Cold-entry records           : %d\n", n_cold)

    if n_bursts == 0
        @printf("    (no finalised bursts — walk may still be running or too few emissions)\n")
        return
    end

    # ── Burst-size distribution ───────────────────────────────────────────
    max_bs  = maximum(burst_sizes)
    mean_bs = sum(burst_sizes) / n_bursts
    @printf("    Burst-size distribution:\n")
    @printf("      mean=%.2f  max=%d\n", mean_bs, max_bs)
    for sz in 1:min(max_bs, 8)
        cnt = count(==(sz), burst_sizes)
        pct = 100.0 * cnt / n_bursts
        bar = "█" ^ round(Int, pct / 5)
        @printf("      size=%d: %5d (%5.1f%%)  %s\n", sz, cnt, pct, bar)
    end
    if max_bs > 8
        cnt = count(>(8), burst_sizes)
        @printf("      size≥9: %5d (%5.1f%%)\n", cnt, 100.0 * cnt / n_bursts)
    end

    # Geometric fit test: if bursts were renewal events with prob p = 1/mean_bs,
    # the size distribution should be Geometric(p).  We compute the KS statistic
    # against that null.
    if n_bursts >= 5
        p_geo   = 1.0 / mean_bs
        sizes_sorted = sort(burst_sizes)
        ks = 0.0
        for (i, s) in enumerate(sizes_sorted)
            empirical_cdf = i / n_bursts
            theo_cdf      = 1.0 - (1.0 - p_geo)^s
            ks = max(ks, abs(empirical_cdf - theo_cdf))
        end
        verdict = ks < 0.1 ? "(≈ geometric / memoryless)" :
                  ks < 0.2 ? "← MILD deviation from geometric" :
                              "← NON-GEOMETRIC (heavy tail or bimodal)"
        @printf("    KS vs Geometric(1/mean_size)=%.4f: KS=%.4f  %s\n",
                p_geo, ks, verdict)
    end

    # ── Cold-entry analysis ───────────────────────────────────────────────
    if n_cold < 3
        @printf("    (too few cold-entry records for geometry analysis: %d)\n", n_cold)
        return
    end

    cold_kbkts = [e[1] for e in cold_entries]
    cold_abkts = [e[2] for e in cold_entries]
    cold_bsizes = [e[3] for e in cold_entries]

    # Key-bucket entropy of cold-entry openers.
    kbkt_counts = Dict{Int,Int}()
    for b in cold_kbkts
        kbkt_counts[b] = get(kbkt_counts, b, 0) + 1
    end
    H_kbkt = 0.0
    for (_, c) in kbkt_counts
        p = c / n_cold
        H_kbkt -= p * log2(p)
    end
    H_max_kbkt = log2(DEEP_DIAG_N_BUCKETS)
    @printf("    Cold-entry key-bucket entropy  : %.3f / %.3f bits (%.1f%% of uniform)\n",
            H_kbkt, H_max_kbkt, 100.0 * H_kbkt / H_max_kbkt)
    if H_kbkt < 0.7 * H_max_kbkt
        @printf("      ↑ CONCENTRATED: cold entries cluster in few key-space buckets → thin entry surface\n")
    else
        @printf("      (≈ spread: cold entries cover key-space broadly)\n")
    end

    # a-bucket entropy of cold-entry openers.
    abkt_counts = Dict{Int,Int}()
    for b in cold_abkts
        abkt_counts[b] = get(abkt_counts, b, 0) + 1
    end
    H_abkt = 0.0
    for (_, c) in abkt_counts
        p = c / n_cold
        H_abkt -= p * log2(p)
    end
    # The a-buckets here are raw a-values clamp-cast to UInt16; compute uniform H.
    H_max_abkt = log2(max(2, length(abkt_counts)))
    @printf("    Cold-entry a-bucket entropy    : %.3f bits  (%d distinct a-buckets)\n",
            H_abkt, length(abkt_counts))

    # Conditional burst-size given cold vs all.
    mean_cold_bs = n_cold > 0 ? sum(cold_bsizes) / n_cold : 0.0
    @printf("    Mean burst-size at cold entry  : %.2f  (overall mean: %.2f)\n",
            mean_cold_bs, mean_bs)
    if mean_cold_bs > 1.5 * mean_bs
        @printf("      ↑ COLD entries produce LARGER bursts — entry geometry matters\n")
    elseif mean_cold_bs < mean_bs / 1.5
        @printf("      ↓ Cold entries produce smaller bursts — burst size not entry-dependent\n")
    else
        @printf("      (cold burst size ≈ overall — no strong entry-size correlation)\n")
    end
end

# ---------------------------------------------------------------------------
#  _report_d23 — Kill-renewal cascade probe
# ---------------------------------------------------------------------------
function _report_d23(deep_stat::ConjDeepStat)
    @printf("\n  D23 — Kill-renewal cascade probe  (window=%d steps)\n",
            D23_CASCADE_WINDOW)
    @printf("  ─────────────────────────────────────────────────────────────────\n")

    recs = deep_stat.d23_records
    n    = length(recs)

    @printf("    Cascade records collected    : %d\n", n)
    n < 3 && (@printf("    (too few records for analysis)\n"); return)

    gaps     = [r[1] for r in recs]
    cascades = [r[2] for r in recs]

    mean_cascade = sum(cascades) / n
    frac_multi   = count(>(0), cascades) / n

    @printf("    Mean cascade count           : %.3f  (hits in next %d steps)\n",
            mean_cascade, D23_CASCADE_WINDOW)
    @printf("    Fraction with ≥1 cascade hit : %.1f%%\n", 100.0 * frac_multi)

    # Distribution of cascade counts.
    for k in 0:min(5, maximum(cascades))
        cnt = count(==(k), cascades)
        @printf("      cascade=%d: %d (%.1f%%)\n", k, cnt, 100.0 * cnt / n)
    end

    # Condition on cold vs warm entry (gap ≥ 0 means there was a previous emission).
    valid_gaps = filter(r -> r[1] >= 0, recs)
    if length(valid_gaps) >= 4
        # Estimate mean gap from the valid pairs.
        mean_gap_obs = sum(r[1] for r in valid_gaps) / length(valid_gaps)
        thresh       = mean_gap_obs / 2.0

        cold_recs = filter(r -> r[1] >= thresh, valid_gaps)
        warm_recs = filter(r -> r[1] <  thresh, valid_gaps)

        if !isempty(cold_recs) && !isempty(warm_recs)
            mean_cold = sum(r[2] for r in cold_recs) / length(cold_recs)
            mean_warm = sum(r[2] for r in warm_recs) / length(warm_recs)
            @printf("    Cold-entry (gap ≥ %.0f) cascade mean: %.3f  (n=%d)\n",
                    thresh, mean_cold, length(cold_recs))
            @printf("    Warm-entry (gap <  %.0f) cascade mean: %.3f  (n=%d)\n",
                    thresh, mean_warm, length(warm_recs))
            if mean_warm > 2.0 * mean_cold + 0.01
                @printf("      ↑ WARM entries cascade MORE → bursts are self-reinforcing (renewal)\n")
            elseif mean_cold > 2.0 * mean_warm + 0.01
                @printf("      ↑ COLD entries cascade MORE → cold geometric access is productive\n")
            else
                @printf("      (cold ≈ warm cascade rate — cascade independent of entry temperature)\n")
            end
        end
    end

    # Counterfactual narrative: what would happen if we suppressed K steps post-hit?
    # We estimate: α₂ lift = burst_frac / mean_cascade.
    if mean_cascade > 0.0 && frac_multi > 0.0
        # If we killed the cascade, we'd lose frac_multi × mean_cascade / n_total hits.
        # The remaining hits would be roughly (1 - frac_multi) + frac_multi × 1/cascade = cold openers.
        # So effective emission rate drops by factor: (n - sum_cascade) / n
        sum_cascade = sum(cascades)
        cold_frac_approx = (n - sum_cascade) / max(1, n + sum_cascade)
        @printf("    Cascade-suppression estimate:\n")
        @printf("      total cascade hits (would be lost)  : %d of %d (%.1f%%)\n",
                sum_cascade, n + sum_cascade, 100.0 * sum_cascade / (n + sum_cascade))
        @printf("      residual emission fraction if killed : %.3f\n", cold_frac_approx)
        @printf("      (↑ if close to 1.0: cascades are rare; if << 1: bursts dominate emission count)\n")
    end
end

# ---------------------------------------------------------------------------
#  _report_d24 — Cross-thread burst alignment
# ---------------------------------------------------------------------------
function _report_d24(deep_stat::ConjDeepStat; n_threads::Int = 1)
    @printf("\n  D24 — Cross-thread burst alignment  (bucket_width=%d steps)\n",
            D24_BUCKET_STEPS)
    @printf("  ─────────────────────────────────────────────────────────────────\n")

    # deep_stat is the *merged* stat; d24_emission_buckets has accumulated
    # counts across all threads.  A bucket with count ≥ 2 means ≥2 threads
    # had at least one emission in the same step window (since each thread
    # contributes at most once per bucket if it has 1 emission there, but
    # also could be a single thread with 2 emissions in the same window).
    # To distinguish, we compare bucket count to n_threads.
    bkts = deep_stat.d24_emission_buckets
    n_occupied    = length(bkts)
    total_emits   = sum(values(bkts); init=0)
    total_steps   = deep_stat.d24_total_walk_steps

    @printf("    Total walk steps recorded    : %d\n", total_steps)
    @printf("    Occupied step-buckets        : %d  (of %d possible)\n",
            n_occupied, max(1, total_steps ÷ D24_BUCKET_STEPS + 1))
    @printf("    Total emission-bucket tally  : %d\n", total_emits)

    n_occupied == 0 && (@printf("    (no data)\n"); return)

    # Buckets with count ≥ 2 are "multi-thread coincidences" if n_threads > 1,
    # or just within-thread multi-emissions if n_threads == 1.
    multi_bkts = filter(kv -> kv[2] >= 2, bkts)
    n_multi    = length(multi_bkts)
    frac_multi = n_multi / n_occupied

    @printf("    Buckets with ≥2 hits         : %d / %d  (%.1f%%)\n",
            n_multi, n_occupied, 100.0 * frac_multi)

    if n_threads > 1
        # Expected fraction under independence: 1 - (1 - λ)^{n_threads} ≈ n_threads × λ
        # where λ = n_occupied / n_total_buckets (probability any given bucket is hit per thread).
        n_total_bkts = max(1, total_steps ÷ D24_BUCKET_STEPS + 1)
        lambda       = n_occupied / n_total_bkts
        expected_multi_frac = 1.0 - (1.0 - lambda)^n_threads
        lift = n_multi > 0 ? frac_multi / max(1e-10, expected_multi_frac) : 0.0
        @printf("    Expected coincidence (indep.) : %.1f%%  (lift=%.2f×)\n",
                100.0 * expected_multi_frac, lift)
        if lift > 2.0
            @printf("      ↑ GLOBAL STRUCTURE: bursts co-occur across threads → shared walk geometry\n")
        elseif lift < 0.5
            @printf("      ↓ ANTI-CORRELATED: threads avoid same windows → effective load-balancing\n")
        else
            @printf("      (≈ independent: thread bursts are not coordinated)\n")
        end
    else
        # Single-thread: multi-hits = within-thread consecutive bursts in same bucket.
        @printf("    (single-thread merge — cross-thread test requires n_threads > 1)\n")
        @printf("    Within-thread multi-hit rate : %.1f%%  (bursts compact in step-space)\n",
                100.0 * frac_multi)
    end

    # Top-5 hottest buckets.
    if n_occupied > 0
        sorted_bkts = sort(collect(bkts), by=kv -> -kv[2])
        @printf("    Top-5 hottest step-buckets:\n")
        for (bkt, cnt) in sorted_bkts[1:min(5, end)]
            step_lo = bkt * D24_BUCKET_STEPS
            step_hi = step_lo + D24_BUCKET_STEPS - 1
            @printf("      steps [%9d, %9d] : %d hit(s)\n", step_lo, step_hi, cnt)
        end
    end
end

# ---------------------------------------------------------------------------
#  _report_d22_d24 — top-level dispatcher called from print_conj_deep_report.
# ---------------------------------------------------------------------------
function _report_d22_d24(deep_stat::ConjDeepStat; n_threads::Int = 1)
    _report_d22(deep_stat)
    _report_d23(deep_stat)
    _report_d24(deep_stat; n_threads = n_threads)
end
