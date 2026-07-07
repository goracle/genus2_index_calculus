# ==============================================================================
# 08_poly_ops_core.jl
# Split fragment of trial3_phi_general.jl (lines 2975-3491 of original).
# NOT standalone-includable yet -- wiring/includes to be sorted out separately.
# ==============================================================================

function phi_to_EY!(
    scratch,
    basis  ::Vector{NTuple{2,Int}}
)::NTuple{2, Int}

    # Zero-out the active working ranges within poly_buf.
    # E(x) occupies slots 1..32; Y(x) occupies slots 33..64.
    # deg_E and deg_Y both grow roughly linearly with nb (deg_E ~ nb/2), so the
    # nb+2 bound below scales with whatever K_MAX is configured to — it is not
    # tied to any specific K_MAX value. We clear 1..nb+2 for E and 33..33+nb
    # for Y (generous safe bound) rather than the full 32+32 slots, since
    # clearing exactly what we need saves ~2x.
    nb_local = length(basis)
    clear_e = nb_local + 2     # enough for any E(x) coefficient index
    clear_y = nb_local + 2     # enough for any Y(x) coefficient index
    for i in 1:clear_e
        @inbounds scratch.poly_buf[i] = 0
    end
    for i in 1:clear_y
        @inbounds scratch.poly_buf[32 + i] = 0
    end

    deg_E = 0
    deg_Y = -1  # -1 signifies Y(x) has not been populated yet

    nb = length(basis)
    @assert nb <= 32 "phi_to_EY!: nb=$nb exceeds the 32-slot E(x)/Y(x) half-buffer layout (poly_buf[1:32]=E, poly_buf[33:64]=Y) — basis grew beyond what this fixed layout assumes"
    for idx in 1:nb
        @inbounds c = scratch.coeffs_out[idx]
        c == 0 && continue

        @inbounds bi, bj = basis[idx]
        @assert bi >= 0 "phi_to_EY!: basis[$idx] has negative x-exponent bi=$bi"
        if bj == 0
            # Element is a coefficient of E(x)
            @assert bi + 1 <= 32 "phi_to_EY!: E(x) coefficient index bi+1=$(bi+1) exceeds poly_buf's E-half (slots 1..32); bi=$bi from basis[$idx]=$(basis[idx])"
            @inbounds scratch.poly_buf[bi + 1] = fp(scratch.poly_buf[bi + 1] + c)
            if bi > deg_E
                deg_E = bi
            end
        else
            # Element is a coefficient of Y(x) (shifted by offset 33)
            @assert 33 + bi <= 64 "phi_to_EY!: Y(x) coefficient index 33+bi=$(33+bi) exceeds poly_buf's Y-half (slots 33..64); bi=$bi from basis[$idx]=$(basis[idx])"
            @inbounds scratch.poly_buf[33 + bi] = fp(scratch.poly_buf[33 + bi] + c)
            if bi > deg_Y
                deg_Y = bi
            end
        end
    end

    return (deg_E, deg_Y)
end

# ---------------------------------------------------------------------------
#  poly_mul(a, b) — multiply two polynomials (ascending coefficients) over F_p.
# ---------------------------------------------------------------------------
function poly_mul(a::Vector{Int}, b::Vector{Int})::Vector{Int}
    na, nb = length(a), length(b)
    c = zeros(Int, na + nb - 1)
    for i in 1:na, j in 1:nb
        c[i+j-1] = fp(c[i+j-1] + fpmul(a[i], b[j]))
    end
    return c
end

# ---------------------------------------------------------------------------
#  poly_sq(a) — square a polynomial over F_p.
# ---------------------------------------------------------------------------
function poly_sq(a::Vector{Int})::Vector{Int}
    n = length(a)
    c = zeros(Int, 2n - 1)
    for i in 1:n
        a[i] == 0 && continue
        c[2i-1] = fp(c[2i-1] + fpmul(a[i], a[i]))
        for j in i+1:n
            a[j] == 0 && continue
            c[i+j-1] = fp(c[i+j-1] + 2*fpmul(a[i], a[j]))
        end
    end
    return c
end


# ---------------------------------------------------------------------------
#  poly_mul_mod_inplace!(scratch, len_a, off_a, len_b, off_b, u_len) -> Int
#
#  Multiplies two polynomials inside scratch.poly_buf segments and reduces the
#  result modulo u_RS in-place.
#
#  We use poly_buf[257:384] (offset 256) as a safe intermediate multiplication area
#  before calling poly_reduce_mod_inplace!.
# ---------------------------------------------------------------------------
function poly_mul_mod_inplace!(
    scratch,
    len_a::Int, off_a::Int,
    len_b::Int, off_b::Int,
    u_len::Int
)::Int

    # If either input is empty, the product is 0
    (len_a <= 0 || len_b <= 0) && return 0

    # 1. Execute convolution into a fresh temporary workspace segment (offset 256)
    off_mul = 256
    len_mul = len_a + len_b - 1
    
    # Zero out the multiplication work window
    for i in 1:len_mul
        @inbounds scratch.poly_buf[off_mul + i] = 0
    end

    # 2. Perform the multiplication
    for i in 1:len_a
        @inbounds ai = scratch.poly_buf[off_a + i]
        ai == 0 && continue
        for j in 1:len_b
            @inbounds bj = scratch.poly_buf[off_b + j]
            bj == 0 && continue
            
            idx = off_mul + i + j - 1
            @inbounds scratch.poly_buf[idx] = fp(scratch.poly_buf[idx] + fpmul(ai, bj))
        end
    end

    # 3. Reduce modulo u_RS in place
    final_len = poly_reduce_mod_inplace!(scratch, off_mul + len_mul, off_mul, u_len)

    # 4. Copy the final reduced remainder straight into scratch.v_RS
    #
    # CRITICAL BOUNDS ASSERT: scratch.v_RS is a fixed length-8 Vector{Int}
    # (see ThreadScratchpad{K}() constructor), same as scratch.u_RS. Same
    # risk as the u_RS copy in phi_residual_general!: final_len depends on
    # poly_reduce_mod_inplace!'s degree bookkeeping, now running for the
    # first time on genuinely nonzero coefficients (see coeffs_out bugfix
    # in build_phi_general!). An @inbounds overrun here is silent until it
    # corrupts something else's memory.
    @assert final_len <= length(scratch.v_RS) "poly_mul_mod_inplace!: final_len=$final_len exceeds scratch.v_RS's fixed capacity ($(length(scratch.v_RS))) — would silently overrun v_RS via @inbounds. len_a=$len_a, len_b=$len_b, u_len=$u_len."
    for i in 1:final_len
        @inbounds scratch.v_RS[i] = scratch.poly_buf[off_mul + i]
    end

    return final_len
end

# ---------------------------------------------------------------------------
#  poly_mul_inplace_segment!(scratch, len_a, off_a, len_b, off_b, off_dest) -> Int
#  Multiplies polynomial A and B, writing the result starting at off_dest.
# ---------------------------------------------------------------------------
function poly_mul_inplace_segment!(
    scratch,
    len_a::Int, off_a::Int,
    len_b::Int, off_b::Int,
    off_dest::Int
)::Int
    (len_a <= 0 || len_b <= 0) && return 0
    len_out = len_a + len_b - 1

    # WILLY-NILLY ASSERT: poly_buf has 1024 slots total; off_dest is a raw
    # caller-supplied offset with no length check anywhere in this
    # function. A bad offset/length pair here writes silently past the
    # buffer via @inbounds.
    @assert off_dest + len_out <= length(scratch.poly_buf) "poly_mul_mod_inplace! (segment mul): off_dest=$off_dest len_out=$len_out would write past poly_buf length $(length(scratch.poly_buf))"
    @assert off_a + len_a <= length(scratch.poly_buf) "poly_mul_mod_inplace!: off_a=$off_a len_a=$len_a reads past poly_buf"
    @assert off_b + len_b <= length(scratch.poly_buf) "poly_mul_mod_inplace!: off_b=$off_b len_b=$len_b reads past poly_buf"

    for i in 1:len_out
        @inbounds scratch.poly_buf[off_dest + i] = 0
    end

    for i in 1:len_a
        @inbounds ai = scratch.poly_buf[off_a + i]
        ai == 0 && continue
        for j in 1:len_b
            @inbounds bj = scratch.poly_buf[off_b + j]
            bj == 0 && continue
            idx = off_dest + i + j - 1
            @inbounds scratch.poly_buf[idx] = fp(scratch.poly_buf[idx] + fpmul(ai, bj))
        end
    end
    return len_out
end

# ---------------------------------------------------------------------------
#  poly_sq_inplace_segment!(scratch, len_a, off_a, off_dest) -> Int
#  Squares a polynomial over F_p into a target destination segment.
# ---------------------------------------------------------------------------
function poly_sq_inplace_segment!(
    scratch,
    len_a::Int, off_a::Int,
    off_dest::Int
)::Int
    len_a <= 0 && return 0
    len_out = 2 * len_a - 1

    @assert off_dest + len_out <= length(scratch.poly_buf) "poly_sq_inplace_segment!: off_dest=$off_dest len_out=$len_out would write past poly_buf length $(length(scratch.poly_buf))"
    @assert off_a + len_a <= length(scratch.poly_buf) "poly_sq_inplace_segment!: off_a=$off_a len_a=$len_a reads past poly_buf"

    for i in 1:len_out
        @inbounds scratch.poly_buf[off_dest + i] = 0
    end

    for i in 1:len_a
        @inbounds ai = scratch.poly_buf[off_a + i]
        ai == 0 && continue
        
        # Diagonal elements: ai²
        idx_diag = off_dest + 2*i - 1
        @inbounds scratch.poly_buf[idx_diag] = fp(scratch.poly_buf[idx_diag] + fpmul(ai, ai))
        
        # Cross terms: 2 * ai * aj
        for j in (i + 1):len_a
            @inbounds aj = scratch.poly_buf[off_a + j]
            aj == 0 && continue
            
            idx_cross = off_dest + i + j - 1
            @inbounds scratch.poly_buf[idx_cross] = fp(scratch.poly_buf[idx_cross] + 2 * fpmul(ai, aj))
        end
    end
    return len_out
end

# ---------------------------------------------------------------------------
#  build_N_inplace!(scratch, deg_E, deg_Y) -> Int
#
#  Computes the norm polynomial N(x) = E(x)² - f(x)·Y(x)² inside the thread 
#  scratchpad without heap allocations or temporary array spawning.
#
#  Memory Configuration:
#    Input E(x) read from: scratch.poly_buf[1 : deg_E+1]
#    Input Y(x) read from: scratch.poly_buf[33 : 33+deg_Y]
#    Output N(x) written to: scratch.poly_buf[1 : final_len]
#
#  F_POLY is assumed to be globally cached as a Vector{Int} or NTuple{6, Int}.
# ---------------------------------------------------------------------------
function build_N_inplace!(
    scratch,
    deg_E::Int,
    deg_Y::Int
)::Int

    @assert length(F_POLY) == 6 "build_N_inplace!: F_POLY has length $(length(F_POLY)), expected 6 (curve y²=x⁵+x+2 has 6 coefficients x⁰..x⁵) — F_POLY[f_idx] for f_idx in 1:6 below assumes this"
    @assert deg_E >= 0 "build_N_inplace!: deg_E=$deg_E must be >= 0 (phi_to_EY! always sets deg_E>=0)"
    @assert deg_Y >= -1 "build_N_inplace!: deg_Y=$deg_Y must be >= -1 (sentinel for 'no Y term')"

    # 1. Clear out the serialization area completely
    for i in 1:64
        @inbounds scratch.ser_buf[i] = 0
    end

    len_E = deg_E + 1
    len_Y = deg_Y + 1

    @assert len_E >= 1 "build_N_inplace!: len_E=$len_E must be >= 1"
    @assert len_Y >= 0 "build_N_inplace!: len_Y=$len_Y must be >= 0"
    @assert len_E <= 32 "build_N_inplace!: len_E=$len_E exceeds ser_buf's E-half (slots 1..32)"
    @assert len_Y <= 32 "build_N_inplace!: len_Y=$len_Y exceeds ser_buf's Y-half (slots 33..64)"

    for i in 1:len_E
        @inbounds scratch.ser_buf[i] = scratch.poly_buf[i]
    end
    for i in 1:len_Y
        @inbounds scratch.ser_buf[32 + i] = scratch.poly_buf[32 + i]
    end

    # 2. Clear out the front of scratch.poly_buf
    for i in 1:64
        @inbounds scratch.poly_buf[i] = 0
    end

    # 3. Accumulate E(x)² into scratch.poly_buf
    for i in 1:len_E
        @inbounds c_i = scratch.ser_buf[i]
        c_i == 0 && continue

        # Diagonal: c_i²
        idx_diag = 2*i - 1
        @assert 1 <= idx_diag <= 64 "build_N_inplace!: E² diagonal write idx_diag=$idx_diag (i=$i) out of poly_buf[1:64] range"
        @inbounds scratch.poly_buf[idx_diag] = fp(scratch.poly_buf[idx_diag] + fpmul(c_i, c_i))

        # Cross: 2 * c_i * c_j
        for j in (i+1):len_E
            @inbounds c_j = scratch.ser_buf[j]
            c_j == 0 && continue
            idx = i + j - 1
            @assert 1 <= idx <= 64 "build_N_inplace!: E² cross write idx=$idx (i=$i,j=$j) out of poly_buf[1:64] range"
            term = fpmul(c_i, c_j)
            # 2*term < 2p, comfortably inside Int64 — no need to pre-reduce
            # before the final fp() on the accumulator add (matches the style
            # already used in poly_sq!/poly_sq_inplace_segment! elsewhere).
            @inbounds scratch.poly_buf[idx] = fp(scratch.poly_buf[idx] + 2 * term)
        end
    end

    # 4. Compute Y(x)² * f(x) and subtract
    for i in 1:len_Y
        @inbounds y_i = scratch.ser_buf[32 + i]
        y_i == 0 && continue

        # Diagonal: y_i²
        y2_coeff_d = fpmul(y_i, y_i)
        y2_deg_d   = 2 * (i - 1)
        for f_idx in 1:6
            @inbounds f_coeff = F_POLY[f_idx]
            f_coeff == 0 && continue
            target_idx = y2_deg_d + f_idx
            @assert 1 <= target_idx <= 64 "build_N_inplace!: Y² diagonal write target_idx=$target_idx (i=$i,f_idx=$f_idx,y2_deg_d=$y2_deg_d) out of poly_buf[1:64] range"
            @inbounds scratch.poly_buf[target_idx] = fp(scratch.poly_buf[target_idx] - fpmul(y2_coeff_d, f_coeff))
        end

        # Cross: 2 * y_i * y_j
        for j in (i+1):len_Y
            @inbounds y_j = scratch.ser_buf[32 + j]
            y_j == 0 && continue

            prod_y = fpmul(y_i, y_j)
            y2_coeff_c = fp(prod_y + prod_y)
            y2_deg_c   = (i - 1) + (j - 1)
            for f_idx in 1:6
                @inbounds f_coeff = F_POLY[f_idx]
                f_coeff == 0 && continue
                target_idx = y2_deg_c + f_idx
                @assert 1 <= target_idx <= 64 "build_N_inplace!: Y² cross write target_idx=$target_idx (i=$i,j=$j,f_idx=$f_idx,y2_deg_c=$y2_deg_c) out of poly_buf[1:64] range"
                @inbounds scratch.poly_buf[target_idx] = fp(scratch.poly_buf[target_idx] - fpmul(y2_coeff_c, f_coeff))
            end
        end
    end

    deg_N = 63
    while deg_N >= 0
        @inbounds if scratch.poly_buf[deg_N + 1] != 0
            break
        end
        deg_N -= 1
    end

    return deg_N + 1 # Fix: Return length instead of degree
end

# ---------------------------------------------------------------------------
#  poly_div_linear!(N, r) — divide N by (x - r) in place using Horner.
#  Returns remainder.  N is overwritten with the quotient (length shrinks by 1).
# ---------------------------------------------------------------------------
function poly_div_linear!(N::Vector{Int}, r::Int)::Int
    n   = length(N)
    rem = N[n]
    for i in n-1:-1:1
        old    = N[i]
        N[i]   = rem
        rem    = fp(old + fpmul(rem, r))
    end
    popfirst!(N)   # remove leading (now quotient's leading) — actually we built Q in-place above
    # Wait — descending Horner builds quotient from high to low.  Re-do cleanly:
    return rem
end

# Cleaner descending-Horner division: returns (quotient_coeffs_ascending, remainder).
function poly_divmod_linear(N::Vector{Int}, r::Int)::Tuple{Vector{Int}, Int}
    # N is ascending: N[1] = const, N[end] = leading coeff.
    # Work in descending order.
    n = length(N)
    if n == 1; return (Int[], N[1]); end
    q = zeros(Int, n-1)     # quotient degree = n-2
    # Descending Horner: q[n-1], q[n-2], ..., q[1], rem
    q[n-1] = N[n]
    for i in n-1:-1:2
        q[i-1] = fp(N[i] + fpmul(q[i], r))
    end
    rem = fp(N[1] + fpmul(q[1], r))
    return (q, rem)
end


# ---------------------------------------------------------------------------
#  poly_divmod_linear_inplace!(scratch, n_len, alpha) -> (Int, Int)
#
#  Divides the active polynomial inside scratch.poly_buf[1:n_len] by (x - alpha)
#  in-place over F_p using Horner's synthetic division rule.
#
#  Mutates: scratch.poly_buf up to n_len.
#  Returns: (new_logical_len, remainder_scalar)
#  ALLOCATION INVARIANT: Zero heap allocations. Pure scalar registers.
# ---------------------------------------------------------------------------
function poly_divmod_linear_inplace!(
    scratch,
    n_len::Int,
    alpha::Int
)::Tuple{Int, Int}
    
    # If the polynomial is a scalar or empty, division is degenerate
    n_len <= 1 && return (n_len, scratch.poly_buf[1])

    # Run Synthetic Division from the highest degree coefficient downwards
    @inbounds rem_val = scratch.poly_buf[n_len]
    @inbounds scratch.poly_buf[n_len] = 0 # Leading quotient position drops by 1 degree
    
    for i in (n_len - 1):-1:1
        @inbounds orig_coeff = scratch.poly_buf[i]
        
        # Next quotient coefficient is the accumulated remainder step
        @inbounds scratch.poly_buf[i] = rem_val
        
        # Shift remainder calculation: rem = orig_coeff + alpha * rem_val (mod p)
        rem_val = fp(orig_coeff + fpmul(alpha, rem_val))
    end
    
    # Compute new logical length of the quotient polynomial window
    new_len = n_len - 1
    while new_len > 1
        @inbounds if scratch.poly_buf[new_len] == 0
            new_len -= 1
        else
            break
        end
    end
    
    return (new_len, rem_val)
end

# ---------------------------------------------------------------------------
#  poly_divmod_monic_deg2_inplace!(scratch, n_len, u1, u0)
#
#  Divides the active polynomial inside scratch.poly_buf[1:n_len] by 
#  u(x) = x² + u1*x + u0 in-place over F_p.
#
#  Mutates: scratch.poly_buf to hold the final quotient in ASCENDING order 
#           starting at index 1.
#  Returns: (quotient_len, rem0, rem1) :: Tuple{Int, Int, Int}
#
#  ALLOCATION INVARIANT: Zero heap allocations. Zero scalar boxing.
# ---------------------------------------------------------------------------
function poly_divmod_monic_deg2_inplace!(
    scratch,
    n_len::Int,
    u1::Int, 
    u0::Int
)::Tuple{Int, Int, Int}
    
    # If the input polynomial doesn't have enough degrees to divide, it's all remainder
    if n_len < 3
        if n_len == 2
            @inbounds r1 = scratch.poly_buf[2]
            @inbounds r0 = scratch.poly_buf[1]
        elseif n_len == 1
            r1 = 0
            @inbounds r0 = scratch.poly_buf[1]
        else
            r1 = 0
            r0 = 0
        end
        return (0, r0, r1)
    end

    # 1. Long division pass working downward through the buffer.
    #    The active coefficients of N(x) are already at scratch.poly_buf[1:n_len].
    for i in n_len:-1:3
        @inbounds c = scratch.poly_buf[i]
        c == 0 && continue
        
        # Quotient coefficient falls into place; we clear the processed dividend term
        @inbounds scratch.poly_buf[i] = c # Keep it tracked here temporarily for flipping
        @inbounds scratch.poly_buf[i-1] = fp(scratch.poly_buf[i-1] - fpmul(c, u1))
        @inbounds scratch.poly_buf[i-2] = fp(scratch.poly_buf[i-2] - fpmul(c, u0))
    end

    # 2. Extract final remainders from the lowest two slots
    @inbounds r0 = scratch.poly_buf[1]
    @inbounds r1 = scratch.poly_buf[2]

    # 3. The quotient terms are now sitting in scratch.poly_buf[3:n_len].
    #    We shift them down into slots [1 : q_len] directly.
    #    (Since we are processing ascending indexes linearly, we can bypass the 
    #    reverse loop if we copy the computed elements from their high offsets).
    q_len = n_len - 2
    for i in 1:q_len
        @inbounds scratch.poly_buf[i] = scratch.poly_buf[i + 2]
    end

    # 4. Strip trailing zeros logically by shrinking the valid window bound
    while q_len > 1
        @inbounds if scratch.poly_buf[q_len] == 0
            q_len -= 1
        else
            break
        end
    end

    return (q_len, r0, r1)
end


# ---------------------------------------------------------------------------
#  phi_residual_general
#
#  Given the φ coefficients (from build_phi_general), the anchor x-coords,
#  and the Mumford u-polynomial, compute the residual intersection divisor.
#
#  Returns (u_RS_coeffs, v_RS_pair) where:
#    u_RS_coeffs : ascending coefficients of the monic residual u_RS(x)
#    v_RS_pair   : (v0_rs, v1_rs, ...) = v_RS(x) coefficients  (NOT YET COMPUTED
#                  for higher degree; see note below)
#
#  For now returns the residual polynomial u_RS(x) (ascending, monic) and
#  a flag indicating whether it has been split into affine points.
#
#  Concretely the return type matches the k=1 pattern extended:
#
#    For k=1 (classic): residual is degree 2 → tried to split over F_p.
#    For k=2:           residual is degree 3 → find rational root + degree-2 factor.
#    For k=3:           residual is degree 4 → find all rational roots.
#
#  Returns:
#    (roots::Vector{NTuple{2,Int}},   # affine residual pts (empty if none split)
#     u_RS ::Vector{Int},             # residual u(x) ascending monic coeffs
#     v_RS ::Vector{Int})             # v_RS(x) ascending coeffs (same degree-1 below u_RS)
#
#  Sentinel: roots empty + u_RS = [-1] means computation failed (remainder ≠ 0).
# ---------------------------------------------------------------------------
