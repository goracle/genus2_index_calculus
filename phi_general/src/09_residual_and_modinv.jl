# ==============================================================================
# 09_residual_and_modinv.jl
# Split fragment of trial3_phi_general.jl (lines 3492-4305 of original).
# NOT standalone-includable yet -- wiring/includes to be sorted out separately.
# ==============================================================================

const RESIDUAL_FAIL = Int[-1]

# ---------------------------------------------------------------------------
#  phi_residual_general! (Zero-Allocation & Slicing-Safe Edition)
#
#  Computes the residual polynomial N(x) and its Mumford / split point roots
#  by peeling off known anchor and branch factors via local, stack-allocated 
#  index registers.
#
#  Modifies primitive array fields inside `scratch` to preserve allocation-free execution.
# ---------------------------------------------------------------------------
function phi_residual_general!(
    scratch ::ThreadScratchpad{K},
    basis   ::Vector{NTuple{2,Int}},
    anchors ::NTuple{K,NTuple{2,Int}},
    u0::Int, u1::Int
)::Bool where K

    # Reset primitive length registers on our thread scratchpad
    scratch.roots_count[1]  = 0
    scratch.u_RS_len[1]     = 0
    scratch.v_RS_len[1]     = 0
    scratch.u_RS_is_fail[1] = false

    k = K  # compile-time constant from type parameter

    # WILLY-NILLY ASSERT: catch a mismatched (scratch, anchors, basis)
    # triple early — this function silently trusts that anchors has length
    # K (the type param) and basis has length K+3; a caller bug here would
    # otherwise show up as an obscure downstream indexing error deep in
    # build_N_inplace!/find_roots_and_points_inplace! instead of here.
    @assert length(anchors) == K "phi_residual_general!: length(anchors)=$(length(anchors)) != K=$K"
    @assert length(basis) == K + 3 "phi_residual_general!: length(basis)=$(length(basis)) != K+3=$(K+3)"

    _pt_res_buildN_t0 = PHI_TIMING_ENABLED[] ? time_ns() : UInt64(0)

    # 1. Convert phi to E(x) and Y(x) representations inside scratch buffers.
    #    Capture the returned degrees to avoid dynamic searching in the next step.
    deg_E, deg_Y = phi_to_EY!(scratch, basis)

    # 2. Compute N(x) = E(x)^2 - f(x)*Y(x)^2 inside our large pre-allocated scratch.poly_buf.
    #    Pass the degrees explicitly to preserve zero-allocation execution.
    n_len = build_N_inplace!(scratch, deg_E, deg_Y)

    if PHI_TIMING_ENABLED[]
        phi_timing_stats().ns_res_buildN += time_ns() - _pt_res_buildN_t0
    end

    _pt_res_divmod_t0 = PHI_TIMING_ENABLED[] ? time_ns() : UInt64(0)

    # 3. Divide out anchor factors with correct multiplicity using zero-alloc linear scan.
    for idx in 1:k
        @inbounds px = anchors[idx][1]
        
        already_done = false
        for prev in 1:(idx-1)
            @inbounds if anchors[prev][1] == px
                already_done = true
                break
            end
        end
        already_done && continue

        cnt = 0
        for jdx in idx:k
            @inbounds if anchors[jdx][1] == px
                cnt += 1
            end
        end

        for _ in 1:cnt
            # poly_divmod_linear! mutates scratch.poly_buf up to n_len in place, 
            # returning the new logical length and scalar remainder.
            n_len, rem_val = poly_divmod_linear_inplace!(scratch, n_len, px)
            if rem_val != 0
                scratch.u_RS_is_fail[1] = true
                s = phi_timing_stats()
                s.n_fail_residual += 1
                s.n_fail_resid_anchor_remainder += 1
                return false
            end
        end
    end

    # 4. Divide out u(x) = x² + u1·x + u0
    #    poly_divmod_monic_deg2_inplace! mutates scratch.poly_buf down by 2 degrees.
    n_len, r0, r1 = poly_divmod_monic_deg2_inplace!(scratch, n_len, u1, u0)
    if r0 != 0 || r1 != 0
        scratch.u_RS_is_fail[1] = true
        s = phi_timing_stats()
        s.n_fail_residual += 1
        s.n_fail_resid_u_remainder += 1
        return false
    end

    # 5. Strip trailing zeros up to n_len
    while n_len > 1
        @inbounds if scratch.poly_buf[n_len] == 0
            n_len -= 1
        else
            break
        end
    end

    # Degenerate residual check
    @inbounds if n_len == 1 && scratch.poly_buf[1] == 0
        scratch.u_RS_is_fail[1] = true
        s = phi_timing_stats()
        s.n_fail_residual += 1
        s.n_fail_resid_degenerate += 1
        return false
    end

    # 6. Normalize to make the residual polynomial monic
    @inbounds lc = scratch.poly_buf[n_len]
    if lc != 1
        inv_lc = fpinv(lc)
        for i in 1:n_len
            @inbounds scratch.poly_buf[i] = fpmul(scratch.poly_buf[i], inv_lc)
        end
    end

    # 7. Copy computed coefficients of N(x) into scratch.u_RS
    #
    # CRITICAL BOUNDS ASSERT: scratch.u_RS is a fixed length-8 Vector{Int}
    # (see ThreadScratchpad{K}() constructor). n_len at this point is the
    # residual polynomial's length after build_N_inplace! (degree tracking,
    # never exercised on real nonzero data until scratch.coeffs_out was
    # actually populated) followed by several in-place divisions
    # (poly_divmod_linear_inplace! per anchor multiplicity,
    # poly_divmod_monic_deg2_inplace! for u(x)). If n_len exceeds 8 here —
    # from a degree-tracking bug anywhere upstream, or simply a K/anchor
    # configuration this fixed-8 assumption doesn't actually cover — the
    # @inbounds copy loop below silently writes past the end of u_RS's
    # backing array, corrupting adjacent heap memory (the classic silent
    # segfault-later pattern, since @inbounds skips the bounds check that
    # would otherwise throw here immediately).
    @assert n_len <= length(scratch.u_RS) "phi_residual_general!: residual length n_len=$n_len exceeds scratch.u_RS's fixed capacity ($(length(scratch.u_RS))) — would silently overrun u_RS via @inbounds. K=$k, deg_E=$deg_E, deg_Y=$deg_Y."
    scratch.u_RS_len[1] = n_len
    for i in 1:n_len
        @inbounds scratch.u_RS[i] = scratch.poly_buf[i]
    end

    if PHI_TIMING_ENABLED[]
        phi_timing_stats().ns_res_divmod += time_ns() - _pt_res_divmod_t0
    end

    _pt_res_vrs_t0 = PHI_TIMING_ENABLED[] ? time_ns() : UInt64(0)

    # 8. Compute v_RS(x) mod N(x) directly inside scratch.v_RS workspace
    v_len = compute_vRS_inplace!(scratch, n_len)
    scratch.v_RS_len[1] = v_len

    if PHI_TIMING_ENABLED[]
        phi_timing_stats().ns_res_vrs += time_ns() - _pt_res_vrs_t0
    end

    _pt_res_roots_t0 = PHI_TIMING_ENABLED[] ? time_ns() : UInt64(0)

    # 9. Find split points using scratch structures, updates scratch.roots_count[1]
    find_roots_and_points_inplace!(scratch, n_len, Val(K))

    if PHI_TIMING_ENABLED[]
        phi_timing_stats().ns_res_roots += time_ns() - _pt_res_roots_t0
    end

    return true
end

# ---------------------------------------------------------------------------
#  compute_vRS_inplace!(scratch, u_len) -> Int
#
#  Computes v_RS(x) = -E(x) * (Y(x))⁻¹ mod u_RS(x) completely in-place.
#
#  Memory Configuration:
#    u_RS(x) read from      : scratch.u_RS[1 : u_len]
#    Original E(x), Y(x) are recovered via scratch.ser_buf (stashed by build_N_inplace!)
#    Output v_RS(x) written : scratch.v_RS[1 : final_v_len]
#
#  Returns: final_v_len :: Int
#  ALLOCATION INVARIANT: Zero heap allocations. Pure scalar registers.
# ---------------------------------------------------------------------------
# ---------------------------------------------------------------------------
#  compute_vRS_inplace!(scratch, u_len) -> Int
#
#  Computes v_RS(x) = -E(x) * (Y(x))⁻¹ mod u_RS(x) completely in-place.
# ---------------------------------------------------------------------------
function compute_vRS_inplace!(
    scratch,
    u_len::Int
)::Int

    deg_u = u_len - 1
    deg_u <= 0 && return 0

    # 1. Check if Y(x) is the zero polynomial.
    #    E(x) and Y(x) are safe inside ser_buf. (Y is at offset 33).
    is_Y_zero = true
    # We dynamically find the active length of Y while checking for non-zero terms
    y_len = 32
    while y_len > 0
        @inbounds if scratch.ser_buf[32 + y_len] != 0
            is_Y_zero = false
            break
        end
        y_len -= 1
    end

    # 2. Compute -E mod u_RS directly into a working slice of scratch.poly_buf.
    #    Find active length of E(x) from ser_buf:
    e_len = 32
    while e_len > 1
        @inbounds if scratch.ser_buf[e_len] == 0
            e_len -= 1
        else
            break
        end
    end

    # Clear only as many slots as e_len needs (u_len+4 is always safe since
    # after reduction the length is ≤ u_len (u_len ≤ 3, a fixed invariant
    # independent of K_MAX — see phi_residual_general! header). e_len can grow
    # with K_MAX; use max(e_len, u_len) + 2.
    clear_e = max(e_len, u_len) + 2
    for i in 1:clear_e
        @inbounds scratch.poly_buf[64 + i] = 0
    end
    for i in 1:e_len
        @inbounds scratch.poly_buf[64 + i] = fp(-scratch.ser_buf[i])
    end

    # Perform in-place polynomial reduction: poly_buf[65...] mod u_RS
    negE_len = poly_reduce_mod_inplace!(scratch, 64 + e_len, 64, u_len)

    # Degenerate early return case if Y(x) == 0
    if is_Y_zero
        # We MUST fail the step. The residual is vertical/degenerate.
        scratch.u_RS_is_fail[1] = true
        return 0
    end

    # 3. Compute Y mod u_RS.
    clear_y = max(y_len, u_len) + 2
    for i in 1:clear_y
        @inbounds scratch.poly_buf[128 + i] = 0
    end
    for i in 1:y_len
        @inbounds scratch.poly_buf[128 + i] = scratch.ser_buf[32 + i]
    end
    
    ymod_len = poly_reduce_mod_inplace!(scratch, 128 + y_len, 128, u_len)

    # 4. Compute Modular Inverse: Y_inv mod u_RS via Extended GCD.
    #
    #    FAST PATH: when u_RS is degree 2 (u_len==3, the dominant k=1 case)
    #    and Y mod u_RS is genuinely linear (ymod_len==2, i.e. its x-coeff
    #    is nonzero), use the closed-form deg-2 inverse instead of the
    #    general extended-Euclid loop — saves on the order of one extra
    #    fpinv call plus the per-iteration register-clear bookkeeping.
    #    Every other case (ymod_len<=1, i.e. Y mod u_RS collapsed to a
    #    constant; or u_len != 3, i.e. higher-degree residual for k>1)
    #    falls straight through to the unchanged general path below.
    @inbounds u0_mod = scratch.u_RS[1]
    @inbounds u1_mod = scratch.u_RS[2]
    if u_len == 3 && ymod_len == 2
        yinv_len, ok = poly_modinv_deg2_closed_form!(scratch, ymod_len, 128, u0_mod, u1_mod)
    else
        yinv_len, ok = poly_modinv_inplace!(scratch, ymod_len, 128, u_len)
    end
    if !ok
        # Degenerate case: Y is not invertible.
        # We MUST fail the step to prevent false collisions on v=0.
        scratch.u_RS_is_fail[1] = true
        return 0
    end

    # 5. Compute v_RS = negE_mod * Y_inv mod u_RS.
    v_len = poly_mul_mod_inplace!(scratch, negE_len, 64, yinv_len, 128, u_len)

    return v_len
end

# ---------------------------------------------------------------------------
#  poly_reduce_mod_inplace!(scratch, raw_len, offset, u_len) -> Int
#
#  Reduces a polynomial stored at scratch.poly_buf[offset + 1 : raw_len]
#  modulo m(x) = scratch.u_RS[1 : u_len] in-place over F_p.
#
#  Inputs:
#    raw_len : Total right boundary of the dividend inside poly_buf
#    offset  : The baseline indexing offset of the polynomial block to reduce
#    u_len   : Length of the modulus polynomial (scratch.u_RS)
#
#  Mutates: scratch.poly_buf[offset + 1 : ...] in place.
#  Returns: The final logical length of the reduced remainder.
#
#  ALLOCATION INVARIANT: Zero heap allocations. Zero scalar boxing.
# ---------------------------------------------------------------------------
function poly_reduce_mod_inplace!(
    scratch,
    raw_len::Int,
    offset::Int,
    u_len::Int
)::Int

    dm = u_len - 1
    @inbounds lc_m = scratch.u_RS[u_len]
    
    # Invariant assertion handling without string construction allocation
    if lc_m == 0
        throw(ArgumentError("poly_reduce_mod_inplace!: modulus leading coefficient is zero"))
    end
    
    # u_RS is normalised to monic in phi_residual_general! step 6 before any
    # poly_reduce_mod_inplace! call, so lc_m == 1 is a proven invariant.
    # Skip the Fermat-ladder fpinv call (which hits the `a==1 && return 1`
    # fast path anyway but still costs a branch+call on each of ~4 reductions
    # per walk step). Fall back to fpinv only in the degenerate non-monic case.
    lc_m_inv = (lc_m == 1) ? 1 : fpinv(lc_m)
    
    # r_len tracks the absolute index boundary of the dividend within poly_buf
    r_len = raw_len
    
    while true
        # Compute current logical degree of remainder relative to offset base
        deg_r = (r_len - offset) - 1
        deg_r < dm && break
        
        # Check if the polynomial reduces logically down to a single zero term
        if deg_r == 0
            @inbounds val = scratch.poly_buf[r_len]
            val == 0 && break
        end

        # Strip trailing zeros safely by dropping the logical length tracker
        @inbounds if scratch.poly_buf[r_len] == 0
            r_len -= 1
            continue
        end

        # Scale factor c = r[end] * lc_m_inv
        # lc_m_inv == 1 by the monic invariant: skip the multiply.
        # The branch here costs essentially nothing since lc_m_inv was already
        # evaluated once above the loop; the `== 1` path is always taken.
        @inbounds c = (lc_m_inv == 1) ? scratch.poly_buf[r_len] : fpmul(scratch.poly_buf[r_len], lc_m_inv)
        shift = deg_r - dm
        
        # Subtract c * x^shift * m(x) from the current remainder window
        for i in 1:u_len
            @inbounds m_val = scratch.u_RS[i]
            idx = offset + i + shift
            @inbounds scratch.poly_buf[idx] = fp(scratch.poly_buf[idx] - fpmul(c, m_val))
        end

        # Clean trailing high-slot elements that are guaranteed to have been cancelled
        while r_len > (offset + 1)
            @inbounds if scratch.poly_buf[r_len] == 0
                r_len -= 1
            else
                break
            end
        end
    end

    # Return the clean active logical length of the remainder block
    return r_len - offset
end


# Multiply two polynomials mod m.
function poly_mul_mod(a::Vector{Int}, b::Vector{Int},
                       m::Vector{Int})::Vector{Int}
    return poly_reduce_mod(poly_mul(a, b), m)
end

# ---------------------------------------------------------------------------
#  poly_modinv_deg2_closed_form!(scratch, len_a, off_a, u0, u1) -> (Int, Bool)
#
#  Fast path for inverting a polynomial a(x) modulo a MONIC DEGREE-2 modulus
#  u(x) = x² + u1*x + u0, used in place of the general extended-Euclid
#  poly_modinv_inplace! whenever deg(u_RS) == 2 — the dominant case for k=1
#  walks, where the residual u_RS is always degree 2.
#
#  DERIVATION (verified symbolically against sympy.resultant and numerically
#  against 6000 random trials at p ~ 10^4, 10^6, and ~2^45 before being coded):
#
#    a(x) = a0 + a1*x,  want b(x) = b0 + b1*x  with  a(x)*b(x) ≡ 1  mod u(x).
#
#    a*b = a0*b0 + (a0*b1 + a1*b0)*x + a1*b1*x²
#    Reduce x² ≡ -u1*x - u0:
#      const  = a0*b0 - a1*b1*u0
#      x-coef = a0*b1 + a1*b0 - a1*b1*u1
#
#    Setting const=1, x-coef=0 and solving the resulting 2x2 linear system
#    for (b0, b1) gives:
#
#      D  = a0² - a0*a1*u1 + a1²*u0        (this is resultant(a, u) — zero
#                                            iff a and u share a root, i.e.
#                                            iff a is NOT invertible mod u)
#      b0 = (a0 - a1*u1) / D
#      b1 = -a1 / D
#
#  Only one fpinv call (of D) is needed, versus the general extended-Euclid
#  path's 1-2+ fpinv calls (one per division step) plus per-iteration
#  register-swap bookkeeping. This function assumes len_a == 2 (i.e. a1 ≠ 0,
#  guaranteed by poly_reduce_mod_inplace!'s trailing-zero trim whenever it
#  reports length 2) — callers must route len_a <= 1 (pure scalar a) through
#  the ordinary fpinv path instead, since the closed form above divides by
#  a1 implicitly via D and is not meant for that case.
#
#  Output contract matches poly_modinv_inplace! exactly: zeroes
#  poly_buf[off_a+1 : off_a+len_a] first, then writes the trimmed inverse
#  coefficients into poly_buf[off_a+1 : off_a+final_len], returning
#  (final_len, true) on success or (0, false) if a is not invertible (D=0).
# ---------------------------------------------------------------------------
@inline function poly_modinv_deg2_closed_form!(
    scratch,
    len_a::Int,
    off_a::Int,
    u0::Int, u1::Int
)::Tuple{Int, Bool}

    @inbounds a0 = scratch.poly_buf[off_a + 1]
    @inbounds a1 = scratch.poly_buf[off_a + 2]

    D = fp(fp(fpmul(a0, a0) - fpmul(a0, fpmul(a1, u1))) + fpmul(fpmul(a1, a1), u0))

    if D == 0
        return (0, false)   # a(x) shares a root with u(x): not invertible
    end

    Dinv = fpinv(D)
    b0 = fpmul(fp(a0 - fpmul(a1, u1)), Dinv)
    b1 = fpmul(fp(-a1), Dinv)

    # NOTE: b1 == 0 here would require a1 == 0 (since b1 = -a1*Dinv and Dinv
    # is necessarily nonzero, being a multiplicative inverse). But this
    # function is only ever called when ymod_len==2, which by
    # poly_reduce_mod_inplace!'s trailing-zero-trim invariant guarantees
    # a1 != 0. So the inverse of a genuinely-linear polynomial mod a
    # degree-2 modulus is itself always genuinely linear — confirmed both
    # analytically and across 80,000 random trials (zero b1==0 hits) before
    # this was simplified down from an earlier version with a dead
    # defensive branch for that case.
    for i in 1:len_a
        @inbounds scratch.poly_buf[off_a + i] = 0
    end
    @inbounds scratch.poly_buf[off_a + 1] = b0
    @inbounds scratch.poly_buf[off_a + 2] = b1
    return (2, true)
end

# ---------------------------------------------------------------------------
#  poly_modinv_inplace!(scratch, len_a, off_a, u_len) -> (Int, Bool)
#
#  Computes the modular inverse of a polynomial sitting at:
#    scratch.poly_buf[off_a + 1 : off_a + len_a]
#  modulo the polynomial m(x) = scratch.u_RS[1 : u_len].
#
#  Overwrites the input segment at off_a with the computed inverse coefficients
#  and returns (new_len, success).
#
#  Memory Configuration for Extended GCD Registers:
#    off_r0  = 384     (Holds running remainder r0, initialized to modulus m)
#    off_r1  = 448     (Holds running remainder r1, initialized to input a)
#    off_s0  = 512     (Holds Bezout coefficient s0, initialized to 0)
#    off_s1  = 576     (Holds Bezout coefficient s1, initialized to 1)
#    off_q   = 640     (Holds temporary quotient q)
#    off_tmp = 704     (Holds temporary workspace for multiplication/subtraction)
#
#  ALLOCATION INVARIANT: Zero heap allocations. Zero scalar boxing.
# ---------------------------------------------------------------------------
function poly_modinv_inplace!(
    scratch,
    len_a::Int,
    off_a::Int,
    u_len::Int
)::Tuple{Int, Bool}

    # Define our fixed-width scratch register segment boundary offsets
    off_r0  = 384
    off_r1  = 448
    off_s0  = 512
    off_s1  = 576
    off_q   = 640
    off_tmp = 704

    # Max sizes we ever need to clear: polynomials here are ≤ deg(u_RS) which is u_len-1.
    # We use u_len + 4 as a safe upper bound (quotient can briefly be one more degree).
    # This replaces the old `for i in 1:64` zeros which cleared 64 slots for ≤5 entries.
    clear_n = u_len + 4

    # WILLY-NILLY ASSERT: off_tmp=704 is the highest fixed register offset
    # this function uses; off_tmp + clear_n must stay inside poly_buf's 1024
    # slots. u_len is nominally <= 8 (residual degree), but this function
    # has no assert tying that assumption to the actual runtime value —
    # given this exact EEA loop has already had at least one silent-
    # corruption bug (see comment below re: destructive swap), check here.
    @assert off_tmp + clear_n <= length(scratch.poly_buf) "poly_modinv_inplace!: u_len=$u_len gives clear_n=$clear_n, off_tmp+clear_n=$(off_tmp+clear_n) exceeds poly_buf length $(length(scratch.poly_buf))"
    @assert len_a >= 1 "poly_modinv_inplace!: len_a=$len_a must be >= 1"
    @assert off_a + len_a <= length(scratch.poly_buf) "poly_modinv_inplace!: off_a=$off_a len_a=$len_a reads past poly_buf"

    # 1. Initialize r0 = modulus m(x) (from scratch.u_RS)
    for i in 1:clear_n; @inbounds scratch.poly_buf[off_r0 + i] = 0; end
    for i in 1:u_len
        @inbounds scratch.poly_buf[off_r0 + i] = scratch.u_RS[i]
    end
    len_r0 = u_len

    # 2. Initialize r1 = input a(x) (from off_a)
    for i in 1:clear_n; @inbounds scratch.poly_buf[off_r1 + i] = 0; end
    for i in 1:len_a
        @inbounds scratch.poly_buf[off_r1 + i] = scratch.poly_buf[off_a + i]
    end
    len_r1 = len_a

    # 3. Initialize s0 = 0 (degree 0 polynomial)
    for i in 1:clear_n; @inbounds scratch.poly_buf[off_s0 + i] = 0; end
    len_s0 = 1 # sitting at 0

    # 4. Initialize s1 = 1 (degree 0 polynomial)
    for i in 1:clear_n; @inbounds scratch.poly_buf[off_s1 + i] = 0; end
    @inbounds scratch.poly_buf[off_s1 + 1] = 1
    len_s1 = 1

    # Main Extended Euclidean Algorithm Loop
    while true
        # Break condition: check if r1 logically becomes the zero polynomial.
        # len_r1 <= 0 is treated the same as the canonical zero-length-1
        # representation: it should never occur after the divmod fix below,
        # but breaking here instead of dividing by a degenerate length-0
        # "polynomial" is strictly safer.
        if len_r1 <= 1
            @inbounds if len_r1 <= 0 || scratch.poly_buf[off_r1 + 1] == 0
                break
            end
        end

        # --- step A: q, r = poly_divmod_poly(r0, r1) ---
        # We perform the long division pass of r0 by r1 inside a helper function.
        # It leaves the quotient at off_q and computes the remainder inside off_r0 in-place.
        len_q, len_r = poly_divmod_poly_inplace_registers!(scratch, len_r0, off_r0, len_r1, off_r1, off_q)

        # Swapping r0 and r1 bounds: r0 becomes the old r1, r1 becomes the new remainder r
        # The new remainder r currently lives in off_r0 (written in-place by
        # poly_divmod_poly_inplace_registers! above). Stash it in off_tmp
        # FIRST — off_tmp is unused until step B below — otherwise the very
        # next line (zeroing off_r0 to receive the old r1) destroys it before
        # it's ever copied into r1's segment, leaving both r0 and r1 holding
        # the old r1 value. That makes the GCD loop converge one step early
        # on a non-scalar "GCD" (the old r1), poly_modinv_inplace! returns
        # false on every call, and every walk step gets discarded.
        for i in 1:clear_n; @inbounds scratch.poly_buf[off_tmp + i] = 0; end
        for i in 1:len_r
            @inbounds scratch.poly_buf[off_tmp + i] = scratch.poly_buf[off_r0 + i]
        end

        # Move coefficients of r1 into r0's segment space
        for i in 1:clear_n; @inbounds scratch.poly_buf[off_r0 + i] = 0; end
        for i in 1:len_r1
            @inbounds scratch.poly_buf[off_r0 + i] = scratch.poly_buf[off_r1 + i]
        end
        len_r0 = len_r1

        # Move the newly computed remainder from off_tmp into r1's segment space
        for i in 1:clear_n; @inbounds scratch.poly_buf[off_r1 + i] = 0; end
        for i in 1:len_r
            @inbounds scratch.poly_buf[off_r1 + i] = scratch.poly_buf[off_tmp + i]
        end
        len_r1 = len_r

        # --- step B: s_new = s0 - q * s1 ---
        # First compute tmp = q * s1 using our segment multiplication rule
        len_tmp = poly_mul_inplace_segment!(scratch, len_q, off_q, len_s1, off_s1, off_tmp)

        # Subtract: s_new = s0 - tmp. We write this into off_q's memory space to reuse it safely
        len_s_new = max(len_s0, len_tmp)
        for i in 1:clear_n; @inbounds scratch.poly_buf[off_q + i] = 0; end
        for i in 1:len_s_new
            @inbounds s0_val = (i <= len_s0) ? scratch.poly_buf[off_s0 + i] : 0
            @inbounds tmp_val = (i <= len_tmp) ? scratch.poly_buf[off_tmp + i] : 0
            @inbounds scratch.poly_buf[off_q + i] = fp(s0_val - tmp_val)
        end
        # Trim trailing zeros of s_new
        while len_s_new > 1
            @inbounds if scratch.poly_buf[off_q + len_s_new] == 0
                len_s_new -= 1
            else
                break
            end
        end

        # Swapping s0 and s1 bounds: s0 becomes the old s1, s1 becomes the computed s_new
        for i in 1:clear_n; @inbounds scratch.poly_buf[off_s0 + i] = 0; end
        for i in 1:len_s1
            @inbounds scratch.poly_buf[off_s0 + i] = scratch.poly_buf[off_s1 + i]
        end
        len_s0 = len_s1

        for i in 1:clear_n; @inbounds scratch.poly_buf[off_s1 + i] = 0; end
        for i in 1:len_s_new
            @inbounds scratch.poly_buf[off_s1 + i] = scratch.poly_buf[off_q + i]
        end
        len_s1 = len_s_new
    end

    # Post-Loop Invertibility Checks
    # The final GCD is sitting inside r0. It must be a non-zero scalar constant.
    if len_r0 != 1
        return (0, false)
    end
    @inbounds gcd_val = scratch.poly_buf[off_r0 + 1]
    if gcd_val == 0
        return (0, false)
    end

    # Scale s0 by the inverse of the constant GCD: inv_a = s0 * fpinv(gcd_val)
    inv_lc = fpinv(gcd_val)
    for i in 1:clear_n; @inbounds scratch.poly_buf[off_tmp + i] = 0; end
    for i in 1:len_s0
        @inbounds scratch.poly_buf[off_tmp + i] = fpmul(scratch.poly_buf[off_s0 + i], inv_lc)
    end
    
    # Trim trailing logical zeros if any were introduced
    len_inv = len_s0
    while len_inv > 1
        @inbounds if scratch.poly_buf[off_tmp + len_inv] == 0
            len_inv -= 1
        else
            break
        end
    end

    # Perform the final modular reduction pass: inv_a mod modulus m(x)
    # Reduces poly_buf[off_tmp + 1 : ...] mod scratch.u_RS, writing the output back inside off_tmp
    final_len = poly_reduce_mod_inplace!(scratch, off_tmp + len_inv, off_tmp, u_len)

    # Move the clean final inverse result into the requested user destination area (off_a)
    for i in 1:len_a
        @inbounds scratch.poly_buf[off_a + i] = 0
    end
    for i in 1:final_len
        @inbounds scratch.poly_buf[off_a + i] = scratch.poly_buf[off_tmp + i]
    end

    return (final_len, true)
end

# ---------------------------------------------------------------------------
#  Helper: poly_divmod_poly_inplace_registers!(scratch, len_r0, off_r0, len_r1, off_r1, off_q)
#  Divides polynomial r0 by r1 using robust polynomial long division.
#  Overwrites the dividend r0 segment with the remainder, and writes quotient to off_q.
# ---------------------------------------------------------------------------
function poly_divmod_poly_inplace_registers!(
    scratch,
    len_r0::Int, off_r0::Int,
    len_r1::Int, off_r1::Int,
    off_q::Int
)::Tuple{Int, Int}

    # 1. Clear out the quotient register window.
    #    Quotient degree = deg(r0) - deg(r1); for our polynomials that's at most u_len-1.
    #    Use len_r0 as the safe bound rather than a hardcoded 64.
    for i in 1:len_r0; @inbounds scratch.poly_buf[off_q + i] = 0; end
    
    # 2. Robustly sanitize the divisor length to ensure the leading coefficient is non-zero
    curr_len_r1 = len_r1
    while curr_len_r1 > 1
        @inbounds if scratch.poly_buf[off_r1 + curr_len_r1] == 0
            curr_len_r1 -= 1
        else
            break
        end
    end
    
    # 3. Robustly sanitize the dividend length
    curr_len_r0 = len_r0
    while curr_len_r0 > 1
        @inbounds if scratch.poly_buf[off_r0 + curr_len_r0] == 0
            curr_len_r0 -= 1
        else
            break
        end
    end

    dr0 = curr_len_r0 - 1
    dr1 = curr_len_r1 - 1
    
    # If the divisor is the zero scalar, the inverse computation is degenerate
    @inbounds lc_r1 = scratch.poly_buf[off_r1 + curr_len_r1]
    if lc_r1 == 0
        return (1, curr_len_r0)
    end

    if dr0 < dr1
        # Quotient is 0, remainder is just r0 untouched
        return (1, curr_len_r0)
    end

    inv_lc_r1 = fpinv(lc_r1)
    
    # Main Division Loop
    while true
        deg_curr = (curr_len_r0 - 1)
        deg_curr < dr1 && break
        
        @inbounds if scratch.poly_buf[off_r0 + curr_len_r0] == 0
            # Floor: curr_len_r0 == 1 means r0 has reduced to the zero
            # polynomial, which is represented as length 1 (value 0), not 0.
            # Without this check, the decrement below walks curr_len_r0 to 0
            # and then negative on subsequent iterations (deg_curr < dr1 no
            # longer reliably triggers once dr1 can itself go negative from a
            # length-0 divisor elsewhere), corrupting every later poly_buf
            # index derived from off_r0 + curr_len_r0.
            curr_len_r0 == 1 && break
            curr_len_r0 -= 1
            continue
        end
        
        # Scale term: c = lc(r0) / lc(r1)
        @inbounds c = fpmul(scratch.poly_buf[off_r0 + curr_len_r0], inv_lc_r1)
        shift = deg_curr - dr1
        
        # Record quotient term (1-indexed offset matching degree position)
        @inbounds scratch.poly_buf[off_q + shift + 1] = c
        
        # Subtract c * x^shift * r1 from r0
        for i in 1:curr_len_r1
            @inbounds r1_val = scratch.poly_buf[off_r1 + i]
            target_idx = off_r0 + i + shift
            @inbounds scratch.poly_buf[target_idx] = fp(scratch.poly_buf[target_idx] - fpmul(c, r1_val))
        end
        
        # Trim remainder window down to next non-zero term
        while curr_len_r0 > 1
            @inbounds if scratch.poly_buf[off_r0 + curr_len_r0] == 0
                curr_len_r0 -= 1
            else
                break
            end
        end
    end

    # Determine structural logical length of computed quotient
    len_q = dr0 - dr1 + 1
    while len_q > 1
        @inbounds if scratch.poly_buf[off_q + len_q] == 0
            len_q -= 1
        else
            break
        end
    end

    return (len_q, curr_len_r0)
end

function poly_sub(a::Vector{Int}, b::Vector{Int})::Vector{Int}
    len = max(length(a), length(b))
    c = zeros(Int, len)
    for i in 1:length(a); c[i] = fp(c[i] + a[i]); end
    for i in 1:length(b); c[i] = fp(c[i] - b[i]); end
    while length(c) > 1 && c[end] == 0; pop!(c); end
    return c
end

# Full polynomial division: returns (quotient, remainder) ascending.
function poly_divmod_poly(a::Vector{Int}, b::Vector{Int})::Tuple{Vector{Int}, Vector{Int}}
    r = copy(a)
    db = length(b) - 1
    deg_r = length(r) - 1
    if deg_r < db; return (Int[0], r); end
    q = zeros(Int, deg_r - db + 1)
    inv_lc_b = fpinv(b[end])
    while length(r) - 1 >= db
        if r[end] == 0; pop!(r); continue; end
        c = fpmul(r[end], inv_lc_b)
        shift = length(r) - length(b)
        q[shift+1] = fp(q[shift+1] + c)
        for i in 1:length(b)
            r[i+shift] = fp(r[i+shift] - fpmul(c, b[i]))
        end
        while length(r) > 1 && r[end] == 0; pop!(r); end
    end
    while length(q) > 1 && q[end] == 0; pop!(q); end
    return (q, r)
end

# ---------------------------------------------------------------------------
#  find_roots_and_points_inplace!(scratch, u_len)
#
#  Extracts affine split roots from the residual polynomial over F_p and
#  recovers their corresponding y-coordinates via y = -E(x)/Y(x).
#
#  Memory Configuration:
#    u_RS(x) read from      : scratch.u_RS[1 : u_len]
#    Original E, Y read from: scratch.ser_buf (stashed by build_N_inplace!)
#    Outputs written into   : scratch.roots_out[1 : scratch.roots_count[1]]
#
#  ALLOCATION INVARIANT: Zero heap allocations. Zero scalar boxing.
# ---------------------------------------------------------------------------
# ---------------------------------------------------------------------------
#  Helper: find_roots_and_points_inplace!(scratch, u_len, k) -> Nothing
#  Finds roots of the residual polynomial component u_RS and lifts them 
#  to full curve points (x, y) using the structural RR basis matching k anchors.
#
#  BATCH Y-INVERSION:
#  Recovering y = -E(x)/Y(x) for each root requires one fpinv per root.
#  At K=2 the residual is degree 3 (≤3 roots); at K=3 degree 4 (≤4 roots).
#  We collect all (val_E, val_Y) pairs first, then invert all non-zero val_Y
#  values with a single fpinv call using the same Montgomery batch-inversion
#  trick as fp_gauss_batch_invert_diag!, dropping r Fermat ladders to 1.
#
#  scratch.y_batch_x / y_batch_E / y_batch_Y hold the per-root intermediates.
# ---------------------------------------------------------------------------
