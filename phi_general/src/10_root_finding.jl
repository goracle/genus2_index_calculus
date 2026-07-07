# ==============================================================================
# 10_root_finding.jl
# Split fragment of trial3_phi_general.jl (lines 4306-4829 of original).
# NOT standalone-includable yet -- wiring/includes to be sorted out separately.
# ==============================================================================

# ============================================================
# 1. Root finding
# ============================================================

@inline function find_x_roots!(
    scratch,
    u_len::Int,
    ::Val{K}
) where K
    scratch.roots_count[1] = 0
    deg = u_len - 1

    @assert deg >= 0

    if deg == 0
        return 0
    end

    n = _find_x_roots_dispatch!(scratch, u_len)

    @assert n >= 0
    @assert n <= length(scratch.y_batch_x)

    return n
end


@inline function _find_x_roots_dispatch!(scratch, u_len::Int)
    deg = u_len - 1

    if deg == 2
        _pt_rq_t0 = PHI_TIMING_ENABLED[] ? time_ns() : UInt64(0)
        n = _solve_quadratic_roots!(scratch)
        if PHI_TIMING_ENABLED[]
            phi_timing_stats().ns_res_roots_quad += time_ns() - _pt_rq_t0
        end
        return n
    else
        _pt_ro_t0 = PHI_TIMING_ENABLED[] ? time_ns() : UInt64(0)
        n = _solve_oscar_roots!(scratch, u_len)
        if PHI_TIMING_ENABLED[]
            phi_timing_stats().ns_res_roots_oscar += time_ns() - _pt_ro_t0
        end
        return n
    end
end


@inline function _solve_quadratic_roots!(scratch)
    @inbounds c0 = scratch.u_RS[1]
    @inbounds c1 = scratch.u_RS[2]

    disc = fp(fpmul(c1, c1) - 4 * c0)
    sq = sqrt_fp_hot(disc)

    if sq < 0
        return 0
    end

    # scratch.small_inv[s] is stored in BACKEND (Montgomery) representation
    # (see init_scratch_caches!: small_inv[s] = to_repr(backend, fpinv(s))),
    # while everywhere else in this function (c0, c1, sq, and the plain
    # `fpmul` used throughout) operates in RAW representation — the same
    # convention as scratch.u_RS/coeffs_out established after the
    # phi_to_EY!/build_N_inplace! fix. Using scratch.small_inv[2] directly
    # with the plain (non-backend) fpmul would mix a Montgomery-form operand
    # into a raw-representation multiply — identical bug class to the
    # earlier binom_scratch[1]/small_inv[s] issue in monomial_series_coeffs!.
    # Use the raw inverse of 2 instead — cached once per thread in
    # scratch.inv2_raw by init_scratch_caches! rather than recomputed via a
    # full Fermat ladder on every call (that recompute was the dominant cost
    # in this function: ~12.7us/call, see the PHI-TIMING roots breakdown).
    inv2 = scratch.inv2_raw[]

    x1 = fpmul(fp(-c1 + sq), inv2)
    x2 = fpmul(fp(-c1 - sq), inv2)

    @inbounds scratch.y_batch_x[1] = x1
    @inbounds scratch.y_batch_x[2] = x2

    return 2
end


@inline function _solve_oscar_roots!(scratch, u_len::Int)
    Fp = scratch.oscar_Fp[]::FqField
    Rx = scratch.oscar_Rx[]::FqPolyRing

    coeff_buf = scratch.oscar_coeff_buf[]::Vector{FqFieldElem}

    @assert length(coeff_buf) >= u_len

    @inbounds for i in 1:u_len
        coeff_buf[i] = Fp(scratch.u_RS[i])
    end

    f_oscar = Rx(coeff_buf[1:u_len])
    rs = roots(f_oscar)

    # UPSTREAM ASSERT (polynomial construction sanity): confirm f_oscar
    # actually came out as a degree-(u_len-1) polynomial, not silently
    # something else. Two concrete ways this could go wrong even though
    # Rx(...) "succeeds": (a) a future edit reintroduces a SubArray/view
    # or otherwise-wrong-shaped argument that Nemo happens to accept via
    # some other method overload instead of erroring like the SubArray
    # case did; (b) coeff_buf[u_len] (the leading coefficient) is zero
    # mod p, in which case Nemo normalizes the polynomial and degree(f_oscar)
    # comes back LOWER than u_len-1 — silently desyncing this function's
    # polynomial from the "degree u_len-1" assumption the caller's n_len
    # bookkeeping is built on. Catching that here, right after
    # construction, is more actionable than letting it surface as a
    # root-count mismatch in the loop below (which only checks an upper
    # bound, not that the count matches what a genuine degree-(u_len-1)
    # polynomial should produce).
    @assert degree(f_oscar) == u_len - 1 "_solve_oscar_roots!: f_oscar has degree $(degree(f_oscar)), expected u_len-1=$(u_len-1) — either coeff_buf[$u_len] (the leading coefficient) is zero mod p and Nemo normalized the polynomial down, or Rx(coeff_buf[1:u_len]) did not build the polynomial this function assumes it built. u_RS(1:$u_len)=$(scratch.u_RS[1:u_len])"

    # CRITICAL BOUNDS ASSERT: scratch.y_batch_x is a fixed-size MVector{N2}
    # (N2 = K+2, at most 8 for K up to 6). A degree-(u_len-1) polynomial has
    # at most u_len-1 roots, which should never exceed N2 given how n_len is
    # derived upstream — but every upstream degree computation in this call
    # chain (build_N_inplace!, the divmod pipeline) is only now running on
    # genuinely nonzero data for the first time. Assert explicitly here
    # rather than silently indexing past y_batch_x's end if any of those
    # upstream degree invariants turn out to be violated.
    n = 0
    for r in rs
        n += 1
        @assert n <= length(scratch.y_batch_x) "_solve_oscar_roots!: root count n=$n exceeds y_batch_x capacity ($(length(scratch.y_batch_x))) for u_len=$u_len (degree $(u_len-1)) — degree/root-count invariant violated upstream."
        @inbounds scratch.y_batch_x[n] = Int(lift(ZZ, r))
    end

    return n
end


# ============================================================
# 2. Evaluate E(x), Y(x)
# ============================================================

@inline function evaluate_candidates!(
    scratch,
    n_cands::Int,
    K::Int
)
    basis = rr_basis_cached(K + 3)

    max_pow = _compute_max_pow(basis)
    norm_x, norm_y = basis[K + 3]

    @assert max_pow >= 0
    # WILLY-NILLY ASSERT: y_batch_x/E/Y are MVector{N2,Int} with N2=K+2 slots.
    # n_cands comes from root-finding on the residual polynomial; if its
    # degree ever exceeds N2 (e.g. a bug upstream in degree bookkeeping,
    # or simply this fixed-N2 assumption not covering some K), this loop's
    # @inbounds writes below in _evaluate_single_candidate! would silently
    # overrun the stack-allocated MVector.
    @assert n_cands <= length(scratch.y_batch_x) "evaluate_candidates!: n_cands=$n_cands exceeds y_batch_x capacity $(length(scratch.y_batch_x)) (K=$K)"
    @assert max_pow + 1 <= length(scratch.pxpow_buf) "evaluate_candidates!: max_pow=$max_pow needs pxpow_buf length >= $(max_pow+1), have $(length(scratch.pxpow_buf))"

    for ci in 1:n_cands
        _evaluate_single_candidate!(
            scratch, ci, basis, max_pow, norm_x, norm_y
        )
    end
end


@inline function _compute_max_pow(basis)
    m = 0
    @inbounds for i in eachindex(basis)
        p, _ = basis[i]
        if p > m
            m = p
        end
    end
    return m
end


@inline function _evaluate_single_candidate!(
    scratch,
    ci::Int,
    basis,
    max_pow::Int,
    norm_x::Int,
    norm_y::Int
)
    @inbounds x = scratch.y_batch_x[ci]

    scratch.pxpow_buf[1] = 1
    for e in 1:max_pow
        scratch.pxpow_buf[e + 1] =
            fpmul(scratch.pxpow_buf[e], x)
    end

    val_E = 0
    val_Y = 0

    nb = length(basis)

    @inbounds for idx in 1:(nb - 1)
        coeff = scratch.coeffs_out[idx]
        coeff == 0 && continue

        px, py = basis[idx]
        term = scratch.pxpow_buf[px + 1]
        scaled = fpmul(coeff, term)

        if py == 0
            val_E = fp(val_E + scaled)
        else
            val_Y = fp(val_Y + scaled)
        end
    end

    norm_term = scratch.pxpow_buf[norm_x + 1]
    if norm_y == 0
        val_E = fp(val_E + norm_term)
    else
        val_Y = fp(val_Y + norm_term)
    end

    @inbounds scratch.y_batch_E[ci] = val_E
    @inbounds scratch.y_batch_Y[ci] = val_Y

    # IMPORTANT invariant
    @assert typeof(val_E) == typeof(val_Y)
end


# ============================================================
# 3. Filter valid roots
# ============================================================

@inline function compact_valid_roots!(
    scratch,
    n_cands::Int
)
    n_valid = 0

    for i in 1:n_cands
        @inbounds yv = scratch.y_batch_Y[i]

        if yv != 0
            n_valid += 1

            if n_valid != i
                @inbounds begin
                    scratch.y_batch_x[n_valid] = scratch.y_batch_x[i]
                    scratch.y_batch_E[n_valid] = scratch.y_batch_E[i]
                    scratch.y_batch_Y[n_valid] = yv
                end
            end
        end
    end

    @assert n_valid <= n_cands
    return n_valid
end


# ============================================================
# 4. Batch inversion + reconstruction
# ============================================================

@inline function solve_roots_from_batches!(
    scratch,
    n_valid::Int
)
    if n_valid == 0
        return 0
    end

    # WILLY-NILLY ASSERT: roots_out is a fixed length-8 Vector (see
    # ThreadScratchpad{K}() constructor) regardless of K. n_valid comes from
    # compact_valid_roots!, ultimately bounded by the residual polynomial's
    # degree — if that ever exceeds 8 for some K, the @inbounds-free but
    # unchecked writes below (scratch.roots_out[n_out] = ...) would throw a
    # normal BoundsError at best, or silently corrupt if this ever gets
    # wrapped in @inbounds later. Check explicitly, loudly, here.
    @assert n_valid <= length(scratch.roots_out) "solve_roots_from_batches!: n_valid=$n_valid exceeds roots_out's fixed capacity $(length(scratch.roots_out))"
    @assert n_valid <= length(scratch.xi_buf) "solve_roots_from_batches!: n_valid=$n_valid exceeds xi_buf length $(length(scratch.xi_buf)) (used here for prefix products)"

    if n_valid == 1
        val_E = scratch.y_batch_E[1]
        val_Y = scratch.y_batch_Y[1]

        @assert val_Y != 0

        y = fpmul(fp(-val_E), fpinv(val_Y))

        scratch.roots_out[1] = (scratch.y_batch_x[1], y)
        scratch.roots_count[1] = 1
        return 1
    end

    # prefix products
    scratch.xi_buf[1] = scratch.y_batch_Y[1]

    for i in 2:n_valid
        scratch.xi_buf[i] =
            fpmul(scratch.xi_buf[i - 1], scratch.y_batch_Y[i])
    end

    running = fpinv(scratch.xi_buf[n_valid])

    n_out = 0

    for i in n_valid:-1:2
        inv_i = fpmul(running, scratch.xi_buf[i - 1])
        running = fpmul(running, scratch.y_batch_Y[i])

        y = fpmul(fp(-scratch.y_batch_E[i]), inv_i)

        n_out += 1
        scratch.roots_out[n_out] = (scratch.y_batch_x[i], y)
    end

    y = fpmul(fp(-scratch.y_batch_E[1]), running)
    n_out += 1
    scratch.roots_out[n_out] = (scratch.y_batch_x[1], y)

    scratch.roots_count[1] = n_out

    @assert n_out == n_valid

    return n_out
end


# ============================================================
# 5. Top-level orchestration
# ============================================================

function find_roots_and_points_inplace!(
    scratch,
    u_len::Int,
    ::Val{K}
) where K

    n_cands = find_x_roots!(scratch, u_len, Val(K))

    if n_cands == 0
        scratch.roots_count[1] = 0
        return nothing
    end

    evaluate_candidates!(scratch, n_cands, K)

    n_valid = compact_valid_roots!(scratch, n_cands)

    solve_roots_from_batches!(scratch, n_valid)

    return nothing
end


# ---------------------------------------------------------------------------

#  Helper: recover_y_from_phi_inplace(scratch, x, k) -> Union{Int, Nothing}
#  Correctly isolates and evaluates E(x) and Y(x) mod p at a root x by 
#  unrolling the explicit Riemann-Roch basis structure.
#  
#  φ(x,y) = E(x) + y * Y(x) == 0  =>  y = -E(x) / Y(x)
# ---------------------------------------------------------------------------
function recover_y_from_phi_inplace(scratch::ThreadScratchpad{K}, x::Int, ::Val{K} = Val(K))::Int where K
    nb = K + 3  # compile-time constant
    # Retrieve the canonical monomial basis vector (poles sorted: x^i or x^i * y)
    basis = rr_basis_cached(nb)::Vector{NTuple{2, Int}}

    # Precompute x^0, x^1, ..., x^(max_pow) in one ascending pass.
    # Max x-power in basis grows with K_MAX (e.g. K_MAX=3 → nb=6, basis:
    # 1,x,x²,y,x³,xy, max x-power 3); scales per rr_basis, not a fixed bound.
    # Uses pxpow_buf (length 32) from scratch — borrowing it here; it's not live
    # during root recovery (find_roots_and_points calls us after residual is done).
    max_pow = 0
    for idx in 1:nb
        @inbounds pi, _ = basis[idx]
        pi > max_pow && (max_pow = pi)
    end
    @assert max_pow + 1 <= length(scratch.pxpow_buf) "recover_y_from_phi_inplace: max_pow=$max_pow needs pxpow_buf length >= $(max_pow+1), have $(length(scratch.pxpow_buf))"
    scratch.pxpow_buf[1] = 1
    for e in 1:max_pow
        @inbounds scratch.pxpow_buf[e+1] = fpmul(scratch.pxpow_buf[e], x)
    end

    val_E = 0
    val_Y = 0

    # 1. Evaluate the linear combination of the first (nb - 1) solved coefficients
    for idx in 1:(nb - 1)
        @inbounds coeff = scratch.coeffs_out[idx]
        coeff == 0 && continue
        
        @inbounds pow_x, pow_y = basis[idx]
        @inbounds term = scratch.pxpow_buf[pow_x + 1]
        scaled_term = fpmul(coeff, term)

        if pow_y == 0
            val_E = fp(val_E + scaled_term)
        else
            val_Y = fp(val_Y + scaled_term)
        end
    end

    # 2. Add the contribution of the highest pole monomial (monic, coefficient is 1)
    @inbounds norm_x, norm_y = basis[nb]
    @inbounds norm_term = scratch.pxpow_buf[norm_x + 1]

    if norm_y == 0
        val_E = fp(val_E + norm_term)
    else
        val_Y = fp(val_Y + norm_term)
    end

    # Handle singular/tangent cases where Y(x) evaluates to 0
    val_Y == 0 && return SQRT_FP_NONSQUARE   # sentinel: no valid y

    # y = -E(x) / Y(x) mod p
    return fpmul(fp(-val_E), fpinv(val_Y))
end

# ---------------------------------------------------------------------------
#  Helper: poly_eval_fp_inplace(scratch, offset, len, x) -> Int
# ---------------------------------------------------------------------------
function poly_eval_fp_inplace(scratch, offset::Int, len::Int, x::Int)::Int
    len == 0 && return 0
    @inbounds val = scratch.poly_buf[offset + len]
    for i in (len - 1):-1:1
        @inbounds val = fp(scratch.poly_buf[offset + i] + fpmul(val, x))
    end
    return val
end

# ---------------------------------------------------------------------------
#  Helper: poly_divmod_linear_inplace_segment!(scratch, offset, len, r)
#  Horner linear synthetic division working directly inside an array segment.
# ---------------------------------------------------------------------------
function poly_divmod_linear_inplace_segment!(
    scratch,
    offset::Int,
    n_len::Int,
    r::Int
)::Tuple{Int, Int}
    @inbounds rem_val = scratch.poly_buf[offset + n_len]
    @inbounds scratch.poly_buf[offset + n_len] = 0

    for i in (n_len - 1):-1:2
        @inbounds next_rem = fp(scratch.poly_buf[offset + i] + fpmul(rem_val, r))
        @inbounds scratch.poly_buf[offset + i] = rem_val
        rem_val = next_rem
    end
    
    @inbounds final_rem = fp(scratch.poly_buf[offset + 1] + fpmul(rem_val, r))
    @inbounds scratch.poly_buf[offset + 1] = rem_val

    new_len = n_len - 1
    while new_len > 1
        @inbounds if scratch.poly_buf[offset + new_len] == 0
            new_len -= 1
        else
            break
        end
    end
    return (new_len, final_rem)
end


function poly_eval_fp(coeffs::Vector{Int}, x::Int)::Int
    isempty(coeffs) && return 0
    r = coeffs[end]
    for i in length(coeffs)-1:-1:1
        r = fp(fpmul(r, x) + coeffs[i])
    end
    return r
end

function recover_y_from_phi(E::Vector{Int}, Y::Vector{Int}, x::Int)::Union{Int,Nothing}
    ex = poly_eval_fp(E, x)
    yx = poly_eval_fp(Y, x)
    if yx == 0
        # φ = E(x) at this point — if E(x) ≠ 0 then not a zero of φ
        ex == 0 || return nothing
        # Degenerate: φ vanishes regardless of y; return nothing (skip)
        return nothing
    end
    # y = -E(x) / Y(x)
    return fpmul(fp(-ex), fpinv(yx))
end

# Vector-dispatch shim for step_phi_k!: converts anchors (a Vector or MVector
# whose length may exceed K, e.g. the K_MAX-sized cur_anchors buffer shared
# across all round-robin tuple lengths) into a NTuple{K,...} so the hot path
# above gets a compile-time K, reading only the first K entries.  ntuple with
# Val(K) is zero-cost — K is a type parameter of `scratch`, so the caller
# selects K by choosing which ThreadScratchpad{K} to pass in (see
# step_phi_dispatch!, which picks the right one for the current round-robin
# tuple length at runtime).
@inline function step_phi_k!(
    scratch ::ThreadScratchpad{K},
    anchors ::Vector{NTuple{2,Int}},
    u0::Int, u1::Int, v0::Int, v1::Int;
    backend::FpArith = StandardArith(p)
)::Bool where K
    # WILLY-NILLY ASSERT: comment above says anchors's length "may exceed K"
    # (K_MAX-sized shared buffer) — but never checks it's at least K.
    @assert length(anchors) >= K "step_phi_k! (Vector shim): anchors has length $(length(anchors)) < K=$K, ntuple slice would read past the end"
    # Convert to NTuple{K,...} — zero allocation, compiler inlines the ntuple.
    anc_tup = ntuple(i -> anchors[i], Val(K))
    step_phi_k!(scratch, anc_tup, u0, u1, v0, v1; backend=backend)
end

@inline function step_phi_k!(
    scratch ::ThreadScratchpad{K},
    anchors ::MVector{<:Any, NTuple{2,Int}},
    u0::Int, u1::Int, v0::Int, v1::Int;
    backend::FpArith = StandardArith(p)
)::Bool where K
    @assert length(anchors) >= K "step_phi_k! (MVector shim): anchors has length $(length(anchors)) < K=$K, ntuple slice would read past the end"
    # Convert MVector to NTuple{K,...} — zero allocation, compiler inlines the ntuple.
    anc_tup = ntuple(i -> anchors[i], Val(K))
    step_phi_k!(scratch, anc_tup, u0, u1, v0, v1; backend=backend)
end


# ---------------------------------------------------------------------------
