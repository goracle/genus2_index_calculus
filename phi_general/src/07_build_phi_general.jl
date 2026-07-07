# ==============================================================================
# 07_build_phi_general.jl
# Split fragment of trial3_phi_general.jl (lines 2406-2974 of original).
# NOT standalone-includable yet -- wiring/includes to be sorted out separately.
# ==============================================================================

function build_phi_general!(
    scratch,
    anchors,
    u0,
    u1,
    v0,
    v1;
    backend::B=StandardArith(p)
    )::Bool where {B<:FpArith}

    # TIMING INSTRUMENTATION (series phase start): the PhiTimingStats
    # struct/report machinery above has existed for a while but ns_series/
    # ns_gauss/ns_residual were never actually written anywhere in this
    # file -- only read back out in print_phi_timing_report, which is why
    # --phi-timing has always printed "no samples" regardless of whether
    # PHI_TIMING_ENABLED[] was set (n_calls WAS being bumped in
    # step_phi_k!, but nothing ever timed anything). Wiring it in here:
    # "series" covers everything from function entry through the Mumford-
    # block fill (basis lookup, anchor loop / branch_series! calls,
    # monomial column fills, RHS fill) -- i.e. all setup work BEFORE the
    # linear solve. Gated on PHI_TIMING_ENABLED[] exactly like n_calls, so
    # normal (disabled) runs pay one Bool check and skip the time_ns()
    # call entirely, per this file's original zero-alloc/opt-in design.
    _pt_series_t0 = PHI_TIMING_ENABLED[] ? time_ns() : UInt64(0)

    K  = length(anchors)
    nb = K + 3

    basis = rr_basis_cached(nb)

    # ============================================================
    # 1. Validate structure assumptions
    # ============================================================

    @assert K > 0
    @assert K <= K_MAX "build_phi_general!: K=$K exceeds K_MAX=$K_MAX — scratch's static buffers were sized for K_MAX and will not have room for this many anchors"
    @assert length(anchors) == K "build_phi_general!: length(anchors)=$(length(anchors)) != K=$K"
    @assert length(basis) == nb
    @assert length(scratch.coeffs_out) == K + 3 "build_phi_general!: scratch.coeffs_out length $(length(scratch.coeffs_out)) != K+3=$(K+3) — scratch was built for a different K"
    @assert length(scratch.seen_counts) == K
    @assert length(scratch.visited_flags) == K

    # basis sanity: all exponents are small and non-negative
    @inbounds for i in 1:nb
        px, py = basis[i]
        @assert px >= 0
        @assert py >= 0
    end

    # ============================================================
    # 1b. Locate the y-monomial normalization index.
    # ============================================================
    #
    # ACTUAL FIX (root cause of the K=2 "column 4 structurally singular"
    # failure): the normalization convention fixed by the reference
    # implementation (build_phi_mumford in trial3_phi.jl: φ = a·x²+b·x+c+d·y
    # with d=1 ALWAYS) is "the y-monomial's coefficient is 1" — a statement
    # about WHICH MONOMIAL, not about WHICH BASIS POSITION. rr_basis orders
    # by pole order, and only for nb=4 (K=1) does that ordering happen to
    # put y last; for nb=5 (K=2) it puts x³ last instead, and y sorts to
    # index nb-1. This function finds y explicitly and uses its real index
    # everywhere a "normalization index" is needed, instead of assuming
    # it's basis[end]/basis[nb].
    #
    # y_idx == nb is NOT expected to hold in general — do not assert it.
    # rr_basis_cached only guarantees "a y-monomial exists somewhere in the
    # basis" (see its own assert), not "it's last"; that guarantee was
    # deliberately weakened once fill_monomial_block!/fill_mumford_block!/
    # the coeffs_out write-back were fixed to use y_idx directly rather
    # than basis[end]. y_idx varying with nb (4→y_idx=4, 5→y_idx=4, 6→? )
    # is the CORRECT, now-fully-supported behavior, not a warning sign.
    y_idx = findfirst(bi -> bi == (0, 1), basis)
    @assert y_idx !== nothing "build_phi_general!: K=$K, nb=$nb — RR basis contains no y-monomial (0,1) at all: basis=$basis. The reference φ construction always includes a y-term (d=1 fixed); a basis without one means rr_basis's pole-order enumeration is broken for this nb."
    @assert 1 <= y_idx <= nb "build_phi_general!: y_idx=$y_idx out of range 1:$nb (basis length $(length(basis)))"
    # DEFENSIVE ASSERT: y must appear EXACTLY once. findfirst only checks
    # existence-and-first-position; if rr_basis's enumeration ever produced
    # a duplicate (0,1) entry (e.g. a future edit to the candidate-stream
    # construction introducing an off-by-one that double-counts i=0,j=1),
    # findfirst would silently return the first occurrence and every
    # column-mapping loop below would then have a genuine second (0,1)
    # column masquerading as an ordinary solved-for unknown — a subtle
    # dimension-counting bug that wouldn't necessarily make fp_gauss! fail
    # (two identical-looking (0,1) rows/columns can still be technically
    # distinct columns in the matrix) but WOULD make the solved φ wrong.
    @assert count(bi -> bi == (0, 1), basis) == 1 "build_phi_general!: K=$K, nb=$nb — basis contains $(count(bi -> bi == (0,1), basis)) copies of the y-monomial (0,1), expected exactly 1: basis=$basis. rr_basis's candidate enumeration is producing a duplicate; findfirst above silently picked the first one, which would corrupt the column-index mapping used by fill_monomial_block!/fill_mumford_block!/coeffs_out."

    # ============================================================
    # 2. Convert inputs once (no repeated conversions later)
    # ============================================================

    u0_b = to_repr(backend, u0)
    u1_b = to_repr(backend, u1)
    v0_b = to_repr(backend, v0)
    v1_b = to_repr(backend, v1)

    anchors_b = ntuple(i -> (
        to_repr(backend, anchors[i][1]),
        to_repr(backend, anchors[i][2])
    ), Val(K))

    # ============================================================
    # 3. Determine max x-exponent needed from the basis (this is a
    #    property of the RR basis only — independent of any anchor).
    # ============================================================
    #
    # BUGFIX (root cause of the monomial_series_coeffs! constant-coefficient
    # assert firing under general-k phi runs):
    # this block previously ALSO called build_xpow_cache!(scratch.pxpow_buf,
    # 1, max_basis_i, backend) right here, i.e. ONCE, before the anchor loop,
    # using the literal x-coordinate `1` instead of the anchor's real px.
    # The loop variable here is named `px` too (it's actually the x-EXPONENT
    # field of basis[i], not an x-coordinate — unfortunate naming collision
    # with the anchor px below), which is almost certainly how a hardcoded
    # `1` ended up passed as the cache's base. Because pxpow_buf was filled
    # with powers of 1 (every entry ≡ 1), every xi_scratch[s+1] computed
    # downstream collapsed to just binom_scratch[s+1] — i.e.
    # fpmul_b(backend, binom_scratch[s+1], pxpow_table[i-s+1]) silently used
    # pxpow_table[i-s+1] ≡ 1 regardless of the anchor's actual x-coordinate.
    # This is wrong for every anchor with px != 1. The self-referential
    # sanity assert (out[1] == fpmul_b(pxpow_table[i+1], y_ser[1])) can't
    # catch it — both sides read the same corrupted table — it only shows up
    # as a downstream inconsistency (singular/garbage linear system).
    #
    # The cache must be keyed on the CURRENT anchor's real px and rebuilt
    # every time px changes — i.e. once per anchor, inside the loop below,
    # not once per build_phi_general! call.

    max_basis_i = 0
    @inbounds for i in 1:nb
        exp_i, _ = basis[i]
        if exp_i > max_basis_i
            max_basis_i = exp_i
        end
    end

    @assert max_basis_i >= 0

    # ACTUAL FIX: populate the x_pow_mod_u_r0/r1 cache that
    # reduce_monomial_mod_D_cached depends on (used both by
    # fill_mumford_block! below and by step_phi_k!'s secondary consistency
    # check). This only depends on u0/u1, which are constant for the whole
    # call — unlike pxpow_buf, which is rebuilt per-anchor — so one fill
    # here suffices. Needs entries up to exponent max_basis_i+1: the j==1
    # branch of reduce_monomial_mod_D_cached looks up index i+2, i.e.
    # exponent i+1, for the largest i in the basis (max_basis_i).
    build_xmodu_cache!(
        scratch.x_pow_mod_u_r0, scratch.x_pow_mod_u_r1,
        u0, u1, max_basis_i + 1, backend
    )
    @assert max_basis_i + 2 <= length(scratch.x_pow_mod_u_r0) "build_phi_general!: x_pow_mod_u cache filled up to exponent $(max_basis_i+1) (index $(max_basis_i+2)) but reduce_monomial_mod_D_cached's j=1 branch will need that index"

    # ============================================================
    # 4. Reset linear system
    # ============================================================

    fill!(scratch.A_mat, 0)
    fill!(scratch.rhs_vec, 0)

    row_idx = 1
    total_rows = 0

    # ============================================================
    # 5. Main anchor loop
    # ============================================================

    for a in 1:K

        px, py = anchors_b[a]

        # UPSTREAM INVARIANT (catch double/missing to_repr at the source,
        # not 3 frames down in fill_f_tay!): px, py here MUST be
        # backend-repr values, i.e. exactly to_repr(backend, <raw coord>)
        # as constructed in anchors_b above — never the raw anchor coords
        # and never re-converted. Verify by round-tripping: converting a
        # backend-repr value's raw form back to repr must reproduce it
        # exactly. This is a no-op check under StandardArith (to_repr =
        # from_repr = identity, so it can't catch anything there — the
        # earlier build_xpow_cache! comment block explains why this bug
        # class is Montgomery-only), but under MontgomeryArith it directly
        # catches: (a) a caller passing raw coords straight through
        # (px would then be mistaken for R-form and mis-decoded), and
        # (b) a caller double-applying to_repr before reaching here
        # (the same failure mode fill_f_tay! had).
        @assert to_repr(backend, from_repr(backend, px)) == px "build_phi_general!: anchor $a's px=$px failed the backend-repr round-trip check — this means px is NOT in the backend representation anchors_b is supposed to produce (either a raw coordinate leaked through, or to_repr was applied more than once upstream). Check anchors_b's construction and every call in this loop that receives px before assuming the bug is downstream in fill_f_tay!/compute_branch_series!."
        @assert to_repr(backend, from_repr(backend, py)) == py "build_phi_general!: anchor $a's py=$py failed the backend-repr round-trip check — same double/missing to_repr hazard as px above, check anchors_b's construction first."

        # ------------------------------------------------------------
        # TANGENCY DETECTION: if this anchor's (raw, un-converted) point
        # already occurred earlier in the tuple, this occurrence does NOT
        # get its own row. Its constraint was already absorbed into the
        # earlier occurrence's row via a bumped `m` (see below) — that's
        # what "vanishing order 2 at P" means: one evaluation row (t^0
        # coefficient) plus one derivative row (t^1 coefficient), not two
        # separate evaluation rows at the same point (which is exactly
        # the guaranteed-singular duplicate-row bug this replaces).
        #
        # This must run BEFORE anything below computes/writes a row for
        # anchor `a`, and must key off `anchors` (raw coordinates), not
        # `anchors_b` (backend-repr) — repr equality and raw equality
        # agree for both StandardArith (to_repr is identity) and
        # MontgomeryArith (to_repr is injective), so either would work,
        # but `anchors` avoids relying on that injectivity assumption.
        is_repeat_of_earlier = false
        @inbounds for prev in 1:a-1
            if anchors[prev] == anchors[a]
                is_repeat_of_earlier = true
                break
            end
        end

        if is_repeat_of_earlier
            # Row-budget bookkeeping only: no row written for this anchor.
            continue
        end

        # How many times does THIS anchor's point occur at or after
        # position a? (i.e. this occurrence plus any later repeats it
        # will absorb.) Only 1 or 2 is supported — see fill_f_tay!'s
        # docstring for what m>=3 (triple-or-higher tangency) would need.
        occ_count = 0
        @inbounds for later in a:K
            anchors[later] == anchors[a] && (occ_count += 1)
        end
        @assert occ_count == 1 || occ_count == 2 "build_phi_general!: anchor $(anchors[a]) occurs $occ_count times in this $K-tuple — only single points (m=1) and simple tangency (m=2, occurring exactly twice) are implemented. A point repeated 3+ times needs fill_f_tay! extended to f_tay[3..] and is not yet supported; _anchor_tuple_valid upstream should not be constructing tuples like this."

        m = occ_count

        # --- sub-timer: setup (x-power cache rebuild for this anchor) ---
        _pt_ser_setup_t0 = PHI_TIMING_ENABLED[] ? time_ns() : UInt64(0)

        # Rebuild the x-power cache for THIS anchor's x-coordinate.
        # (Must happen before fill_monomial_block!/fill_rhs! below, both of
        # which read scratch.pxpow_buf via monomial_series_coeffs!.)
        #
        # IMPORTANT: build_xpow_cache! calls to_repr(backend, px) internally
        # — it expects a RAW (pre-conversion) integer, not a backend-repr
        # value. `px` here is anchors_b[a][1], which was already converted
        # via to_repr at the top of this function (anchors_b construction).
        # Passing that through build_xpow_cache! would double-apply to_repr,
        # which is a no-op for StandardArith but corrupts the value under
        # MontgomeryArith (to_repr is not idempotent there). Use the raw,
        # un-converted anchor coordinate instead.
        build_xpow_cache!(scratch.pxpow_buf, anchors[a][1], max_basis_i, backend)

        # invariant: cache size must match expectation
        @assert length(scratch.pxpow_buf) >= max_basis_i + 1

        @assert px != 0
        @assert py != 0  # hyperelliptic / branch validity assumption

        if PHI_TIMING_ENABLED[]
            phi_timing_stats().ns_ser_setup += time_ns() - _pt_ser_setup_t0
        end

        # --- sub-timer: branch_series (compute_branch_series! only) ---
        _pt_ser_branch_t0 = PHI_TIMING_ENABLED[] ? time_ns() : UInt64(0)

        # --- compute local branch expansion ---
        compute_branch_series!(
            scratch.out_y,
            px,
            py,
            m,
            scratch,
            backend
        )

        if PHI_TIMING_ENABLED[]
            phi_timing_stats().ns_ser_branch += time_ns() - _pt_ser_branch_t0
        end

        # strict structural invariant: branch series must match expected size
        @assert length(scratch.out_y) >= m + 1

        # ========================================================
        # 5a. Fill matrix block
        # ========================================================

        _pt_ser_cols_t0 = PHI_TIMING_ENABLED[] ? time_ns() : UInt64(0)

        fill_monomial_block!(
            scratch.A_mat,
            scratch.rhs_vec,
            row_idx,
            basis,
            y_idx,
            px,
            scratch.out_y,
            m,
            scratch,
            backend
        )

        # DEFENSIVE ASSERT (tangency row cross-check): when m==2, independently
        # recompute what the derivative row (row_idx+1) SHOULD contain for
        # every column and compare against what fill_monomial_block! just
        # wrote into A_mat. For a pure-x column (i,0), the t^1 coefficient of
        # (px+t)^i is i*px^(i-1) — a completely independent formula from
        # monomial_series_coeffs!'s binomial-recurrence path, computed here
        # via direct exponentiation, so a bug in the recurrence (wrong
        # small_inv indexing, wrong binom_scratch seed, off-by-one in maxs,
        # etc.) is caught at the exact column it corrupts, rather than
        # surfacing as an opaque whole-row "phi_val == 0" failure two
        # functions later with no indication of WHICH column is wrong.
        # (Columns with j==1, i.e. x^i*y, are skipped here — their t^1
        # coefficient depends on out_y[2] too, which is already
        # independently checked by compute_branch_series!'s tangent-slope
        # assert above; re-deriving the full product rule here would just
        # duplicate that check rather than add new coverage.)
        if m == 2
            col_chk = 0
            @inbounds for bidx in 1:length(basis)
                bidx == y_idx && continue
                col_chk += 1
                (bi, bj) = basis[bidx]
                bj == 1 && continue   # see comment above: skip y-mixed columns here
                bi == 0 && continue   # constant column: derivative is identically 0, trivially consistent
                # pxpow_buf[k+1] = px^k in backend representation (see
                # build_xpow_cache!), so pxpow_buf[bi] = px^(bi-1) already in
                # backend repr — use it directly, don't from_repr/to_repr it.
                expected_deriv_b = fpmul_b(
                    backend,
                    to_repr(backend, bi),
                    scratch.pxpow_buf[bi]
                )
                actual_deriv = scratch.A_mat[row_idx + 1, col_chk]
                @assert expected_deriv_b == actual_deriv "build_phi_general!: tangency derivative-row MISMATCH at anchor px=$(from_repr(backend,px)) column $col_chk (basis[$bidx]=($bi,$bj)) — fill_monomial_block! wrote A_mat[$(row_idx+1),$col_chk]=$actual_deriv but the independently-recomputed derivative i*px^(i-1) gives $expected_deriv_b. This points at monomial_series_coeffs!'s binomial-recurrence path (small_inv/binom_scratch/pxpow_table indexing) for THIS specific column, not at branch_series!/fill_f_tay! (already checked separately) or at row/column bookkeeping (row_idx placement already asserted correct)."
            end
        end

        if PHI_TIMING_ENABLED[]
            phi_timing_stats().ns_ser_cols += time_ns() - _pt_ser_cols_t0
        end

        # ========================================================
        # 5b. Fill RHS
        # ========================================================
        #
        # ACTUAL FIX: pass basis[y_idx] (the y-monomial, wherever it
        # actually lives) instead of basis[end]. For K=1's nb=4 these are
        # the same thing (y_idx==nb==4), so this changes nothing there; for
        # K=2's nb=5, y_idx==4 != nb==5, and this is the actual fix.

        _pt_ser_rhs_t0 = PHI_TIMING_ENABLED[] ? time_ns() : UInt64(0)

        fill_rhs!(
            scratch.rhs_vec,
            row_idx,
            basis,
            basis[y_idx][1],
            basis[y_idx][2],
            px,
            scratch.out_y,
            m,
            scratch,
            backend
        )

        if PHI_TIMING_ENABLED[]
            phi_timing_stats().ns_ser_rhs += time_ns() - _pt_ser_rhs_t0
        end

        # ========================================================
        # 5c. Row bookkeeping (explicit invariant)
        # ========================================================

        row_idx += m
        total_rows += m

        @assert row_idx == total_rows + 1
    end

    # WILLY-NILLY ASSERT: fill_mumford_block! assumes the anchor loop above
    # wrote exactly K rows (rows 1..K) and left row_idx sitting at K+1. If a
    # future change to the anchor loop (e.g. supporting m>1 tangency orders)
    # advances row_idx by something other than 1 per anchor, this fires
    # before silently writing the Mumford rows into the wrong place.
    @assert row_idx == K + 1 "build_phi_general!: expected row_idx==K+1=$(K+1) before Mumford block, got row_idx=$row_idx (total_rows=$total_rows)"
    @assert total_rows == K "build_phi_general!: expected total_rows==K=$K before Mumford block, got $total_rows"

    # ACTUAL FIX: write the 2 Mumford rows (φ(x,v(x)) ≡ 0 mod u(x), split
    # into constant-term / x-term equations) into rows K+1, K+2. row_idx is
    # already sitting at K+1 here (it was advanced by `m=1` per anchor in
    # the loop above), so this lands exactly where it should.
    n_cols = nb - 1   # == K+2 == N2, the unknown columns (basis[y_idx] is normalised, RHS-only)

    _pt_ser_mumford_t0 = PHI_TIMING_ENABLED[] ? time_ns() : UInt64(0)

    fill_mumford_block!(
        scratch,
        scratch.A_mat,
        scratch.rhs_vec,
        row_idx,
        basis,
        y_idx,
        n_cols,
        v0_b, v1_b,
        backend
    )

    if PHI_TIMING_ENABLED[]
        phi_timing_stats().ns_ser_mumford += time_ns() - _pt_ser_mumford_t0
    end

    row_idx += 2
    total_rows += 2

    # WILLY-NILLY ASSERT: verify the fix actually produced a fully-
    # constrained (K+2)x(K+2) system now, instead of the previous silent
    # 2-all-zero-trailing-rows situation. Kept as a permanent net: if a
    # future refactor breaks fill_mumford_block!'s row bookkeeping again,
    # this fires immediately instead of degrading into "build_phi_general!
    # mysteriously always returns false" or worse.
    @assert total_rows == K + 2 "build_phi_general!: expected K+2=$(K+2) rows written (K anchor rows + 2 Mumford rows) but only wrote $total_rows"
    @assert row_idx == total_rows + 1 "build_phi_general!: row_idx=$row_idx inconsistent with total_rows=$total_rows after Mumford block"
    @assert size(scratch.A_mat, 1) == K + 2
    @assert size(scratch.A_mat, 2) == K + 2
    @assert length(scratch.rhs_vec) == K + 2

    # ============================================================
    # 6. Solve system
    # ============================================================

    if PHI_TIMING_ENABLED[]
        s = phi_timing_stats()
        s.ns_series += time_ns() - _pt_series_t0
    end

    _pt_gauss_t0 = PHI_TIMING_ENABLED[] ? time_ns() : UInt64(0)

    ok = fp_gauss!(
        scratch.A_mat,
        scratch.rhs_vec,
        scratch.prefix_buf,
        backend
    )

    if PHI_TIMING_ENABLED[]
        phi_timing_stats().ns_gauss += time_ns() - _pt_gauss_t0
    end

    # FIX: fp_gauss! returning false means the linear system was singular —
    # a legitimate, expected outcome for some anchor-tuple/divisor
    # configurations (e.g. anchors in special position), not a correctness
    # bug. Every other degenerate case in this function (anchor in supp(D),
    # etc.) returns false rather than asserting; this one must too, or a
    # single ordinary singular system takes down the entire worker task.
    if !ok
        # NOTE: do NOT also bump n_fail_build_gauss_singular here — fp_gauss!
        # and fp_gauss_batch_invert_diag! now increment that (plus their own
        # finer forward_pivot/diag_d1/diag_di sub-counters) at their actual
        # return-false sites, since only they know WHICH of the three
        # singularity checks fired. Double-incrementing here would silently
        # inflate n_fail_build_gauss_singular past n_fail_build and break the
        # phase2_worker stall-assert's `unaccounted == 0` reconciliation.
        s = phi_timing_stats()
        s.n_fail_build += 1
        return false
    end

    # ------------------------------------------------------------------
    # BUGFIX: scratch.coeffs_out was never populated anywhere in this
    # codebase. fp_gauss! solves the system in place into scratch.rhs_vec
    # (N2 = K+2 entries) and returns only a success Bool — nothing ever
    # copied that solution into coeffs_out (N3 = K+3 entries: the K+2
    # solved coefficients for basis[1..N2], plus 1 normalised entry for
    # basis[end], whose coefficient was fixed to 1 by construction when
    # fill_rhs! moved basis[end]'s monomial to the RHS above).
    #
    # Every downstream reader of coeffs_out — phi_to_EY!, the two
    # "PHI VANISHING CHECK" asserts in step_phi_k!, phi_residual_general!
    # — was therefore always reading all-zero coefficients (coeffs_out's
    # zeros(...) initializer, untouched). Every `coeff == 0 && continue`
    # skip fired on every basis column, every "phi_val == 0" / "r0_acc ==
    # r1_acc == 0" assert trivially passed for the wrong reason (nothing
    # was ever summed), and build_N_inplace!/phi_residual_general! ran on
    # a degenerate all-zero E(x)/Y(x) (deg_E=0, deg_Y=-1) on every K>1
    # call ever made — this pipeline has never actually executed on real
    # data before. That also explains why fixing the earlier Montgomery
    # representation bug didn't converge: it let execution reach this
    # point (past the old assert), only to fall through into this
    # separate, pre-existing gap and immediately run brand-new code
    # (degree/root-finding against fixed-size length-8 buffers) for the
    # first time ever, on data whose "degree" bookkeeping was never
    # validated against a genuine nonzero polynomial.
    #
    # Representation: rhs_vec is in backend (Montgomery) form, since
    # fp_gauss! computes entirely via fpmul_b. coeffs_out is consumed
    # downstream (phi_to_EY!, build_N_inplace!, the vanishing checks,
    # phi_residual_general!, ...) exclusively via the plain, non-backend
    # fp/fpmul/fpinv functions, so it must be converted to raw
    # representation via from_repr before being stored.
    #
    # ACTUAL FIX (part 2): rhs_vec's solved entries are indexed by A_MAT
    # COLUMN — i.e. by position in the skip-y_idx traversal that
    # fill_monomial_block!/fill_mumford_block! used (bidx 1..nb, skipping
    # y_idx, mapped in order onto columns 1..n_cols) — NOT by basis index
    # directly. coeffs_out, by contrast, is indexed by BASIS POSITION
    # (coeffs_out[bidx] == coefficient of basis[bidx]), since that's the
    # ordering every downstream reader (phi_to_EY!, phi_eval, the
    # "PHI VANISHING CHECK" asserts, phi_residual_general!) assumes.
    #
    # For K=1 (y_idx==nb==4) these two orderings coincide for every
    # bidx < nb, and the old direct `coeffs_out[idx] = rhs_vec[idx]` copy
    # was consequently correct BY COINCIDENCE. Doing the mapping explicitly
    # here (skip y_idx, advance a separate column counter) means this is no
    # longer coincidental — it is correct for whatever index y actually
    # occupies, e.g. K=2's y_idx=4 != nb=5.
    col = 0
    @inbounds for bidx in 1:nb
        if bidx == y_idx
            scratch.coeffs_out[bidx] = 1   # normalised: coefficient of y is fixed to 1
        else
            col += 1
            scratch.coeffs_out[bidx] = from_repr(backend, scratch.rhs_vec[col])
        end
    end
    # DEFENSIVE ASSERT: the traversal above must have consumed every one of
    # rhs_vec's n_cols solved entries exactly once — mirrors the analogous
    # post-loop checks in fill_monomial_block!/fill_mumford_block!, so a
    # future edit that changes nb, y_idx, or the loop bounds independently
    # in only one of these three places fails loudly here instead of
    # silently dropping or duplicating a coefficient.
    n_cols = length(scratch.rhs_vec)
    @assert col == n_cols "build_phi_general!: coeffs_out write-back consumed $col of rhs_vec's $n_cols entries — skip-y_idx=$y_idx traversal over 1:$nb did not visit exactly n_cols non-y indices, so coeffs_out is now inconsistent with the solved system."
    @assert length(scratch.coeffs_out) == nb "build_phi_general!: coeffs_out length $(length(scratch.coeffs_out)) != nb=$nb after write-back — every basis position 1:nb should have received exactly one coefficient (either solved or the fixed y-normalisation)."

    # DEFENSIVE ASSERT (self-verification, ALL anchors, not just repeats):
    # re-evaluate phi(px,py) for every anchor in this tuple using a
    # completely independent evaluation path — plain powermod over the
    # PLAIN (non-backend) coeffs_out, deliberately NOT eval_monomial's
    # cached-table machinery (scratch.pxpow_buf, x_pow_mod_u caches, etc.),
    # which by this point in the call may hold state left over from
    # whichever anchor the loop above processed LAST, not necessarily the
    # anchor being checked. This runs for K=1 too (trivially, one anchor),
    # so if this exact check has never fired before on a real K=2 run, its
    # first failure here — WITH full build_phi_general! context (K, nb,
    # y_idx, which anchors were treated as repeats) still in scope — is the
    # most direct evidence available for whether plain (non-tangent) K=2
    # evaluation itself has a latent bug, independent of anything the
    # tangency work touched.
    @inbounds for a in 1:K
        (chk_px, chk_py) = anchors[a]
        chk_val = 0
        for bidx in 1:nb
            coeff = scratch.coeffs_out[bidx]
            coeff == 0 && continue
            (bi, bj) = basis[bidx]
            mono = bj == 0 ? powermod(chk_px, bi, p) : fpmul(powermod(chk_px, bi, p), chk_py)
            chk_val = fp(chk_val + fpmul(coeff, mono))
        end
        @assert chk_val == 0 "build_phi_general!: SELF-VERIFICATION failed inside build_phi_general! itself (before returning to step_phi_k!) — anchor a=$a (px,py)=($chk_px,$chk_py) of $K, phi_val=$chk_val (expected 0). K=$K nb=$nb y_idx=$y_idx anchors=$anchors coeffs_out=$(scratch.coeffs_out[1:nb]) basis=$basis. This is evaluated via plain powermod, independent of eval_monomial/scratch.pxpow_buf, so a failure here rules out stale-scratch-state as the cause and points at either the linear solve itself (fp_gauss!) or the row/column construction (fill_monomial_block!/fill_rhs!/fill_mumford_block!) producing a self-inconsistent system that fp_gauss! nonetheless solved without reporting singularity."
    end

    return true
end

# ---------------------------------------------------------------------------
#  phi_to_EY! (Zero-Allocation & Memory-Isolated Edition)
#
#  Splits φ(x,y) = E(x) + y * Y(x) directly inside scratch spaces.
#  
#  Saves:
#    E(x) coefficients into scratch.poly_buf[1 : deg_E + 1]
#    Y(x) coefficients into scratch.poly_buf[33 : 33 + deg_Y]
#
#  Returns:
#    (deg_E, deg_Y) :: NTuple{2, Int}
# ---------------------------------------------------------------------------
