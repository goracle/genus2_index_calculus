# ==============================================================================
# 05_branch_series.jl
# Split fragment of trial3_phi_general.jl (lines 1521-1737 of original).
# NOT standalone-includable yet -- wiring/includes to be sorted out separately.
# ==============================================================================

function branch_series!(
    out_y   ::AbstractVector{Int},
    px      ::Int,
    py      ::Int,
    m       ::Int,
    f_tay   ::AbstractVector{Int},
    poly_buf::AbstractVector{Int},
    backend ::FpArith = StandardArith(p)
)::Nothing

    @assert m ≥ 1

    # -----------------------------
    # m = 1 trivial branch value
    # -----------------------------
    if m == 1
        @inbounds out_y[1] = py
        return nothing
    end

    # -----------------------------
    # We assume F(x,y)=0 is encoded
    # via Taylor coefficients:
    # f_tay[k] = ∂^k_x F(x, y(x)) at px
    # -----------------------------

    @inbounds out_y[1] = py

    # Precompute partial derivatives of F w.r.t y at base point
    # We assume caller ensures f_tay includes mixed contributions;
    # but we explicitly reconstruct Fy via first variation structure.

    # NOTE: for hyperelliptic model, Fy = 2y
    Fy = fpmul_b(backend, to_repr(backend, 2), py)
    Fy_inv = fpinv_b(backend, Fy)

    # ----------------------------------------------------
    # First derivative from implicit function theorem:
    #
    # F_x + F_y y' = 0
    # y' = -F_x / F_y
    # ----------------------------------------------------
    @inbounds begin
        rhs = f_tay[2]
        neg_rhs = fpsub_b(backend, to_repr(backend, 0), rhs)
        out_y[2] = fpmul_b(backend, neg_rhs, Fy_inv)
    end

    # ----------------------------------------------------
    # Higher derivatives: recursive implicit differentiation
    #
    # F_xx + 2F_xy y' + F_yy (y')^2 + F_y y'' = 0
    # etc.
    #
    # We build using stored jet out_y[1..s]
    # ----------------------------------------------------
    for s in 2:m-1

        rhs = f_tay[s+1]

        # subtract all lower-order contributions
        for k in 1:s-1
            # combinatorial coefficient for jet product
            c = k * (s - k + 1)

            rhs = fp_b(
                backend,
                rhs - fpmul_b(backend,
                              to_repr(backend, c),
                              fpmul_b(backend,
                                      out_y[k+1],
                                      out_y[s-k+1]))
            )
        end

        out_y[s+1] = fpmul_b(backend, rhs, Fy_inv)
    end

    return nothing
end

# ---------------------------------------------------------------------------
#  Monomial series (in-place): write the coefficients of t^0..t^(m-1) in
#  x^i * y^j(x) (evaluated at x = px+t, y = y_ser) into `out`.
#
#  x^i = (px + t)^i = Σ C(i,r) * px^(i-r) * t^r  (binomial expansion)
#  x^i * y^j: convolve the two series mod t^m.
#
#  For j=0: coeff of t^s in (px+t)^i = C(i,s) * px^(i-s)  (or 0 if s>i).
#  For j=1: convolve x-series with y-series.
#
#  `out`, `xi_scratch`, `binom_scratch`, `pxpow_scratch` are all
#  length-m buffers owned by the caller and reused across every monomial
#  and every column — this is the allocation hotspot the original
#  per-call `Vector{Int}` returns were causing (one outer vector + four
#  temporaries per monomial, times n columns, times every anchor group,
#  times every walk step).  Writing in place eliminates all of that.
# ---------------------------------------------------------------------------
# ---------------------------------------------------------------------------
#  _xi_series_cached!(xi_scratch, i, px, m, binom_scratch, pxpow_table,
#                      small_inv, xi_cache_i, xi_cache_px, xi_cache_m,
#                      xi_cache_buf, backend)
#
#  Computes the (px+t)^i binomial expansion (coeffs of t^0..t^(m-1)) into
#  xi_scratch — this is exactly the part of the old monomial_series_coeffs!
#  body that depended only on (i, px, m), never on j or y_ser.
#
#  PERFORMANCE: rr_basis interleaves (i,0) and (i,1) basis entries by pole
#  order (see rr_basis's own header comment), so for K>=3 the SAME i shows
#  up as TWO separate basis columns within one fill_monomial_block! call —
#  one with j=0, one with j=1 — and both used to redo this exact binomial
#  recurrence from scratch, wastefully, since it's j-independent. This
#  single-slot memo (xi_cache_i/px/m + xi_cache_buf, all owned by the
#  caller's ThreadScratchpad) turns the second call of each such pair into
#  a cache hit: a plain copy instead of the full recurrence. Any mismatch
#  in (i, px, m) against the cached triple — including the very first call
#  ever, since xi_cache_i starts at -1, an i value rr_basis never
#  produces — is treated as a miss and recomputes+re-stores, so a stale
#  entry from a previous anchor or walk step can never produce a wrong
#  answer, only one avoidable-but-harmless recompute.
# ---------------------------------------------------------------------------
@inline function _xi_series_cached!(
    xi_scratch::AbstractVector{Int},
    i::Int,
    px::Int,
    m::Int,
    binom_scratch::AbstractVector{Int},
    pxpow_table::AbstractVector{Int},
    small_inv::AbstractVector{Int},
    xi_cache_i::AbstractVector{Int},
    xi_cache_px::AbstractVector{Int},
    xi_cache_m::AbstractVector{Int},
    xi_cache_buf::AbstractVector{Int},
    backend::FpArith,
)::Nothing
    @inbounds if xi_cache_i[1] == i && xi_cache_px[1] == px && xi_cache_m[1] == m
        @inbounds copyto!(xi_scratch, 1, xi_cache_buf, 1, m)
        return nothing
    end

    fill!(xi_scratch, 0)
    maxs = min(i, m - 1)

    # FIX (root cause of the monomial_series_coeffs! constant-coefficient
    # assert under MontgomeryArith): fpmul_b(backend, a, x) for
    # MontgomeryArith computes a*x*R^-1 mod p, the REDC product. This is
    # only the correct field-multiplication result when BOTH a and x are
    # already in backend (Montgomery) representation — one bare R factor
    # from each operand, cancelled by the single R^-1 in REDC. Passing a
    # raw (non-Montgomery) integer as either operand leaves the product off
    # by a factor of R^-1 mod p, silently.
    #
    # binom_scratch[1] was previously seeded with the raw literal `1`, then
    # used as an operand to fpmul_b — under Montgomery arithmetic that is
    # NOT the multiplicative identity (only to_repr(backend, 1) = R mod p
    # is). Must be converted via to_repr, same as every other operand that
    # participates in fpmul_b in this function.
    binom_scratch[1] = to_repr(backend, 1)

    for s in 1:maxs
        binom_scratch[s + 1] =
            fpmul_b(
                backend,
                binom_scratch[s],
                fpmul_b(
                    backend,
                    to_repr(backend, i - s + 1),   # was: raw `i - s + 1` — same
                                                    # bug as binom_scratch[1] above;
                                                    # small_inv[s] is backend-repr
                                                    # (see init_scratch_caches!),
                                                    # so its fpmul_b partner must
                                                    # be backend-repr too.
                    small_inv[s],
                ),
            )
    end

    for s in 0:maxs
        xi_scratch[s + 1] =
            fpmul_b(
                backend,
                binom_scratch[s + 1],
                pxpow_table[i - s + 1],
            )
    end

    @inbounds begin
        xi_cache_i[1]  = i
        xi_cache_px[1] = px
        xi_cache_m[1]  = m
        copyto!(xi_cache_buf, 1, xi_scratch, 1, m)
    end

    return nothing
end

# ---------------------------------------------------------------------------
#  Monomial series (in-place): write the coefficients of t^0..t^(m-1) in
#  x^i * y^j(x) (evaluated at x = px+t, y = y_ser) into `out`.
#
#  x^i = (px + t)^i = Σ C(i,r) * px^(i-r) * t^r  (binomial expansion)
#  x^i * y^j: convolve the two series mod t^m.
#
#  For j=0: coeff of t^s in (px+t)^i = C(i,s) * px^(i-s)  (or 0 if s>i).
#  For j=1: convolve x-series with y-series.
#
#  `out`, `xi_scratch`, `binom_scratch`, `pxpow_scratch` are all
#  length-m buffers owned by the caller and reused across every monomial
#  and every column — this is the allocation hotspot the original
#  per-call `Vector{Int}` returns were causing (one outer vector + four
#  temporaries per monomial, times n columns, times every anchor group,
#  times every walk step).  Writing in place eliminates all of that.
#
#  The i-dependent (px+t)^i expansion itself is now delegated to
#  _xi_series_cached! (see above), which memoizes it across the two basis
#  columns (j=0 and j=1) that rr_basis can produce for the same i.
# ---------------------------------------------------------------------------
