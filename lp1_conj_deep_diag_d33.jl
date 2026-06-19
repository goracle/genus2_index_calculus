# =============================================================================
#  lp1_conj_deep_diag_d33.jl  --  D33: φ a-coefficient residue bias.
#
#  a = (v1·px + v0 - py) / u(px) is the single scalar computed in
#  build_phi_mumford that fully determines (b, c) and therefore the entire
#  residual Mumford key u_RS for the next step. If the α₂ = 0.59-ish
#  collision concentration reflects genuine algebraic structure in the
#  curve (rather than temporal/anchor-distribution clustering), it should
#  show up as a non-uniform distribution of a mod q for small primes q —
#  structure that D14's 64-bucket histogram (~76M-wide buckets) cannot
#  resolve.
#
#  This module reports:
#    1. Marginal residue histograms of a mod q for q ∈ D33_PRIMES, each
#       with an exact χ² statistic against the uniform null and the
#       implied χ²/dof, so bias is comparable across primes of different
#       size.
#    2. The joint (a mod 3, a mod 5) 15-cell table, its own χ²/dof against
#       the product-uniform null, and the max single-cell deviation as a
#       quick pointer to which residue combination is most over/under
#       represented.
# =============================================================================

# ---------------------------------------------------------------------------
#  _d33_chi2 — exact χ² statistic for a histogram against a uniform null.
#
#  counts : observed counts per cell (length k)
#  n      : total observations (sum of counts)
#  Returns (chi2, chi2_per_dof) where dof = k - 1.
# ---------------------------------------------------------------------------
function _d33_chi2(counts::AbstractVector{Int}, n::Int)
    k = length(counts)
    n == 0 && return (0.0, 0.0)
    expected = n / k
    chi2 = 0.0
    for c in counts
        d = c - expected
        chi2 += d * d / expected
    end
    dof = max(k - 1, 1)
    return (chi2, chi2 / dof)
end

# ---------------------------------------------------------------------------
#  _report_d33 — print the D33 section.
# ---------------------------------------------------------------------------
function _report_d33(deep_stat::ConjDeepStat)
    n = deep_stat.d33_n_stores

    @printf("\n── D33: φ a-coefficient residue bias (small-prime modular structure) ──\n")
    if n == 0
        @printf("  (no 1LP-conj store events with a_val >= 0 — skipping)\n")
        return
    end
    @printf("  Store events analyzed (a_val >= 0) : %d\n", n)
    @printf("  %-10s %-8s %-10s %-12s %s\n", "prime q", "dof", "chi2", "chi2/dof", "residue counts")

    max_chi2_per_dof = 0.0
    max_chi2_prime   = 0

    for (i, q) in enumerate(D33_PRIMES)
        off = D33_HIST_OFFSETS[i]
        counts = @view deep_stat.d33_hist_flat[off:off+q-1]
        chi2, chi2_dof = _d33_chi2(counts, n)
        counts_str = join(counts, ",")
        @printf("  %-10d %-8d %-10.2f %-12.4f [%s]\n", q, q - 1, chi2, chi2_dof, counts_str)
        if chi2_dof > max_chi2_per_dof
            max_chi2_per_dof = chi2_dof
            max_chi2_prime   = q
        end
    end

    @printf("---------------------------------------------------------------------\n")
    @printf("  Joint (a mod 3, a mod 5) table — rows = a mod 3, cols = a mod 5:\n")
    @printf("  %-10s", "")
    for c5 in 0:4
        @printf(" mod5=%d", c5)
    end
    @printf("\n")
    for r3 in 0:2
        @printf("  mod3=%-5d", r3)
        for c5 in 0:4
            idx = r3 * 5 + c5 + 1
            @printf(" %6d", deep_stat.d33_joint_3_5[idx])
        end
        @printf("\n")
    end

    joint_chi2, joint_chi2_dof = _d33_chi2(deep_stat.d33_joint_3_5, n)
    @printf("  Joint chi2 = %.2f, dof = 14, chi2/dof = %.4f\n", joint_chi2, joint_chi2_dof)

    expected_joint = n / 15
    max_dev = 0.0
    max_dev_cell = (0, 0)
    for r3 in 0:2, c5 in 0:4
        idx = r3 * 5 + c5 + 1
        dev = abs(deep_stat.d33_joint_3_5[idx] - expected_joint) / expected_joint
        if dev > max_dev
            max_dev = dev
            max_dev_cell = (r3, c5)
        end
    end
    @printf("  Largest single-cell deviation: (a mod 3 = %d, a mod 5 = %d), %.1f%% off uniform\n",
            max_dev_cell[1], max_dev_cell[2], 100 * max_dev)

    @printf("---------------------------------------------------------------------\n")
    if max_chi2_prime != 0
        @printf("  Strongest marginal bias: mod %d (chi2/dof = %.4f)\n", max_chi2_prime, max_chi2_per_dof)
    end
    # Rough rule of thumb: chi2/dof >> 3 is a strong signal for these dof
    # ranges (1..12); chi2/dof ~ 1 is consistent with the uniform null.
    if max_chi2_per_dof > 3.0
        @printf("  => Bias detected: 'a' is NOT uniform mod %d. This is consistent with\n", max_chi2_prime)
        @printf("     an algebraic attractor in the φ map and a direct candidate\n")
        @printf("     explanation for the α2 ≈ 0.60 pinning.\n")
    else
        @printf("  => No strong small-prime residue bias detected in 'a'. The α2 gap\n")
        @printf("     likely does not originate at this point in the causal chain;\n")
        @printf("     consider D32-revised (u-polynomial self-return rate) next.\n")
    end
end
