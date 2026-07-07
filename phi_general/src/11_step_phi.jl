# ==============================================================================
# 11_step_phi.jl
# Split fragment of trial3_phi_general.jl (lines 4830-5193 of original).
# NOT standalone-includable yet -- wiring/includes to be sorted out separately.
# ==============================================================================

#  Compatibility shim:  build_phi_mumford_general(anchors, u0, u1, v0, v1)
#
#  Wraps the above for the k=1 case, returning (a, b, c, 1) as before.
#  For k=1 the basis is {1, x, x², y} and coefficients are (c, b, a, 1).
# ---------------------------------------------------------------------------
function build_phi_mumford_general(px::Int, py::Int,
                                    u0::Int, u1::Int,
                                    v0::Int, v1::Int)::Union{NTuple{4,Int}, Nothing}
    coeffs = build_phi_general([(px, py)], u0, u1, v0, v1)
    coeffs === nothing && return nothing
    # coeffs = [c_1, c_x, c_x2, 1] in basis order (1, x, x², y)
    # = (c, b, a, 1) in original notation
    return (coeffs[3], coeffs[2], coeffs[1], 1)
end

# ---------------------------------------------------------------------------
#  phi_residual_mumford_general — k=1 wrapper matching original return type.
#
#  Returns (R, S, RS_mumford) with the same sentinel conventions as the
#  original phi_residual_mumford.
# ---------------------------------------------------------------------------
function phi_residual_mumford_general(a::Int, b::Int, c::Int,
                                       px::Int,
                                       u0::Int, u1::Int
    )::Tuple{NTuple{2,Int}, NTuple{2,Int}, NTuple{4,Int}}

    # Reconstruct φ from (a,b,c,1): basis = {1,x,x²,y}, coeffs = [c,b,a,1]
    basis  = rr_basis(4)
    coeffs = Int[c, b, a, 1]

    # We need E and Y to call the general residual
    E = Int[c, b, a]      # E(x) = c + b*x + a*x²
    Y = Int[1]             # Y(x) = 1  (the y coefficient)

    N = build_N(E, Y)

    # Divide by (x - px)
    q, rem = poly_divmod_linear(N, px)
    rem != 0 && return (SENTINEL_PT, SENTINEL_PT, SENTINEL_MUMFORD)
    N = q

    # Divide by u(x) = x² + u1*x + u0
    q2, r0, r1 = poly_divmod_monic_deg2(N, u1, u0)
    (r0 != 0 || r1 != 0) && return (SENTINEL_PT, SENTINEL_PT, SENTINEL_MUMFORD)
    u_RS = q2   # should be degree 2: [c0, c1, 1]

    length(u_RS) != 3 && return (SENTINEL_PT, SENTINEL_PT, SENTINEL_MUMFORD)

    c0_rs = u_RS[1]; c1_rs = u_RS[2]
    # v_RS(x) = -(a*x² + b*x + c) mod u_RS; since y-coeff is 1:
    v1_rs = fp(fpmul(a, c1_rs) - b)
    v0_rs = fp(fpmul(a, c0_rs) - c)

    mumford_key = (c0_rs, c1_rs, v0_rs, v1_rs)

    disc = fp(fpmul(c1_rs, c1_rs) - 4*c0_rs)
    sq   = sqrt_fp_hot(disc)

    if sq < 0
        return (SENTINEL_PT, SENTINEL_PT, mumford_key)
    end

    inv2 = fpinv(2)
    xR   = fpmul(fp(-c1_rs + sq), inv2)
    xS   = fpmul(fp(-c1_rs - sq), inv2)

    yR = fp(-fpmul(a, fpmul(xR,xR)) - fpmul(b,xR) - c)
    yS = fp(-fpmul(a, fpmul(xS,xS)) - fpmul(b,xS) - c)

    return ((xR, yR), (xS, yS), mumford_key)
end

# ---------------------------------------------------------------------------
#  High-level API for multi-anchor walks (Zero-Allocation Edition)
#
#  step_phi_k!(scratch, anchors, u0, u1, v0, v1) -> Bool
#
#  Entry point for a walk step with k anchors. `anchors` is a length-k
#  vector of (px,py) points — repeated entries encode higher vanishing order.
#
#  ALLOCATION INVARIANT: Zero heap allocations. Zero scalar boxing. 
#  Mutates internal fields of `scratch` on a successful step (`true`).
#  Returns `false` if φ cannot be constructed or if the step fails.
# ---------------------------------------------------------------------------
# Tuple-dispatch entry point (hot path).
# anchors::NTuple{K,NTuple{2,Int}} — compile-time K from ThreadScratchpad{K}.
# The Vector-accepting overload below converts and calls this one.
function step_phi_k!(
    scratch ::ThreadScratchpad{K},
    anchors ::NTuple{K,NTuple{2,Int}},
    u0::Int, u1::Int, v0::Int, v1::Int;
    backend::FpArith = StandardArith(p)
)::Bool where K

    # ------------------------------------------------------------
    # bookkeeping
    # ------------------------------------------------------------
    PHI_TIMING_ENABLED[] && (phi_timing_stats().n_calls += 1)

    success_build = build_phi_general!(scratch, anchors, u0, u1, v0, v1; backend=backend)
    !success_build && return false

    k  = K
    nb = K + 3

    @assert k == K && k == length(anchors) "step_phi_k!: k=$k, K=$K, length(anchors)=$(length(anchors)) must all agree"

    basis = rr_basis_cached(nb)::Vector{NTuple{2, Int}}

    @assert length(scratch.coeffs_out) ≥ nb
    @assert length(basis) == nb

    # ------------------------------------------------------------
    # PHI VANISHING CHECK (ANCHORS)
    # ------------------------------------------------------------
    #
    # ROOT-CAUSE FIX: this previously called eval_monomial(i,j,px,py,...),
    # which evaluates x^i*y^j via reduce_monomial_mod_D_cached — i.e. by
    # reducing x^i MOD THE WALK STEP'S DIVISOR u(x) (cached into
    # scratch.x_pow_mod_u_r0/r1 by build_phi_general!'s call to
    # build_xmodu_cache!) and only THEN combining with py. That reduction
    # is mathematically equivalent to a direct evaluation of x^i at px
    # ONLY WHEN px IS A ROOT OF u(x) — true for the SECONDARY CONSISTENCY
    # CHECK below (which deliberately evaluates phi at u(x)'s roots via
    # (v0,v1)), but false here: this check verifies phi at the walk's
    # ANCHOR points, which have no required relationship to whatever
    # divisor u(x) the walk happens to be stepping through right now.
    # eval_monomial's own doc comment ("evaluate ... at an affine point")
    # promises unconditional evaluation but the implementation silently
    # assumes the mod-u(x) precondition — a latent bug that was invisible
    # for K=1 (where this pipeline was never actually reached before the
    # earlier coeffs_out-never-populated bug was fixed) and only surfaced
    # now that K=2 anchors are real, non-degenerate points independent of
    # the current u(x).
    #
    # Fixed by evaluating directly: plain powermod against p, combined
    # with coeffs_out (already in plain, non-backend representation) —
    # exactly mirroring build_phi_general!'s own self-verification loop
    # (added earlier), which uses this same direct formula and passes.
    let
        for idx in 1:k
            @inbounds (px, py) = anchors[idx]

            phi_val = 0

            for col in 1:nb
                @inbounds coeff = scratch.coeffs_out[col]
                coeff == 0 && continue

                @inbounds (i, j) = basis[col]

                val = j == 0 ? powermod(px, i, p) : fpmul(powermod(px, i, p), py)

                phi_val = fp(phi_val + fpmul(coeff, val))
            end

            # DEFENSIVE ASSERT: was a bare `@assert phi_val == 0` with no
            # message — meaning a failure here gave no way to tell whether
            # the failing anchor was a repeated/tangent point (pointing at
            # the m=2 machinery) or an ordinary distinct point (pointing at
            # something wrong in plain K>1 evaluation that predates and is
            # unrelated to the tangency work). Dump everything needed to
            # distinguish those two cases, plus the actual coeffs_out
            # (basis-position-indexed) and basis itself, so a failure here
            # is immediately actionable instead of requiring another
            # instrumentation round-trip.
            is_repeat_anchor = false
            @inbounds for other in 1:k
                other != idx && anchors[other] == anchors[idx] && (is_repeat_anchor = true; break)
            end
            @assert phi_val == 0 "step_phi_k!: PHI VANISHING CHECK failed at anchor idx=$idx (px,py)=($px,$py), k=$k, is_repeat_anchor=$is_repeat_anchor — phi_val=$phi_val (expected 0). coeffs_out(basis-indexed)=$(scratch.coeffs_out[1:nb]), basis=$basis. If is_repeat_anchor=false, this is a PLAIN (non-tangent) evaluation failure — unrelated to the m=2 tangency machinery (none of compute_branch_series!'s tangent-slope assert, build_phi_general!'s derivative-row cross-check, or step_phi_k!'s own tangency-derivative check fired before this, which only happens if this anchor never went through the m=2 path at all). If is_repeat_anchor=true, check those three tangency-specific assert sites' output first — this one alone doesn't say which column is wrong."
        end
    end

    # ------------------------------------------------------------
    # PHI TANGENCY CHECK (repeated anchors only):
    # for any anchor point that occurs more than once in this tuple,
    # independently verify d/dt[phi(px+t, py+y'*t)]|_{t=0} == 0, using the
    # ACTUAL SOLVED coefficients (coeffs_out) and a completely fresh
    # computation of f'(px) and y' — deliberately not reusing scratch.out_y
    # or scratch.f_tay, since by this point in step_phi_k! those scratch
    # buffers reflect whichever anchor build_phi_general!'s loop processed
    # LAST, not necessarily the repeated anchor being checked here. This is
    # the definitive end-to-end check for the m=2 tangency implementation:
    # if the plain PHI VANISHING CHECK above passes but THIS fails, the bug
    # is specifically in the derivative machinery (fill_f_tay!,
    # branch_series!'s m=2 path, or monomial_series_coeffs!'s per-column
    # derivative), not in ordinary evaluation or row/column bookkeeping.
    # ------------------------------------------------------------
    let
        for idx in 1:k
            @inbounds (px, py) = anchors[idx]

            is_repeat = false
            @inbounds for other in 1:k
                other != idx && anchors[other] == anchors[idx] && (is_repeat = true; break)
            end
            !is_repeat && continue

            @assert py != 0 "step_phi_k!: tangency check hit a repeated Weierstrass anchor ($px,$py) — this should have been rejected upstream by _anchor_tuple_valid"

            # Fresh f'(px) via Horner, in PLAIN (non-backend) representation
            # — coeffs_out and eval_monomial both operate in plain repr, so
            # this check must too, matching the PHI VANISHING CHECK above.
            deg = length(F_POLY_DESC) - 1
            # F_POLY_DESC is stored in backend repr (see
            # init_phi_general_caches!); convert each coefficient back to
            # plain repr before using it in this plain-repr computation.
            fprime_px = 0
            @inbounds for pidx in 1:deg
                power = deg - pidx + 1
                power == 0 && break
                c_plain = from_repr(backend, F_POLY_DESC[pidx])
                fprime_px = fp(fpmul(fprime_px, px) + fpmul(power, c_plain))
            end
            yprime = fpmul(fprime_px, fpinv(fp(2 * py)))

            # d/dt[phi(px+t, py+y'*t)]|_{t=0} = sum_col coeff[col] * d/dt[monomial_col(px+t,py+y'*t)]|_0
            #   monomial (i,0): d/dt[(px+t)^i]|_0 = i*px^(i-1)
            #   monomial (i,1): d/dt[(px+t)^i*(py+y'*t)]|_0 = i*px^(i-1)*py + px^i*y'
            dphi_val = 0
            for col in 1:nb
                @inbounds coeff = scratch.coeffs_out[col]
                coeff == 0 && continue
                @inbounds (i, j) = basis[col]

                if j == 0
                    i == 0 && continue   # constant column: derivative 0
                    dmono = fpmul(i, powermod(px, i - 1, p))
                else
                    term1 = i == 0 ? 0 : fpmul(fpmul(i, powermod(px, i - 1, p)), py)
                    term2 = fpmul(powermod(px, i, p), yprime)
                    dmono = fp(term1 + term2)
                end

                dphi_val = fp(dphi_val + fpmul(coeff, dmono))
            end

            @assert dphi_val == 0 "step_phi_k!: TANGENCY DERIVATIVE CHECK FAILED at repeated anchor (px,py)=($px,$py) — d/dt[phi] at t=0 = $dphi_val, expected 0 (plain vanishing DID pass, so this isolates the bug to the derivative/tangency machinery specifically: fill_f_tay!'s sign or value, branch_series!'s m=2 combination of f_tay with Fy_inv, or monomial_series_coeffs!'s per-column t^1 coefficient — check compute_branch_series!'s own tangent-slope assert output from THIS SAME anchor earlier in the log, and the per-column derivative-row cross-check in build_phi_general!'s anchor loop, to narrow further)."
        end
    end

    # ------------------------------------------------------------
    # SECONDARY CONSISTENCY CHECK:
    # phi(x, v(x)) mod u(x)
    # ------------------------------------------------------------
    let
        r0_acc = 0
        r1_acc = 0

        for col in 1:nb
            @inbounds coeff = scratch.coeffs_out[col]
            coeff == 0 && continue

            @inbounds (i, j) = basis[col]

            rr0, rr1 = reduce_monomial_mod_D_cached(
                i, j,
                to_repr(backend, v0),
                to_repr(backend, v1),
                scratch,
                backend
            )

            r0_acc = fp(r0_acc + fpmul(coeff, from_repr(backend, rr0)))
            r1_acc = fp(r1_acc + fpmul(coeff, from_repr(backend, rr1)))
        end

        @assert r0_acc == 0
        @assert r1_acc == 0
    end

    # ------------------------------------------------------------
    # residual extraction
    # ------------------------------------------------------------
    _pt_resid_t0 = PHI_TIMING_ENABLED[] ? time_ns() : UInt64(0)
    success_residual = phi_residual_general!(scratch, basis, anchors, u0, u1)
    if PHI_TIMING_ENABLED[]
        phi_timing_stats().ns_residual += time_ns() - _pt_resid_t0
    end

    if !success_residual || scratch.u_RS_is_fail[1]
        return false
    end

    return true
end

# ---------------------------------------------------------------------------
#  step_phi_dispatch! — runtime-k entry point for the round-robin walk.
#
#  Once anchor tuple length k varies step-to-step (round-robin over
#  1..K_ceil rather than a single fixed K), the scratch buffer needed for
#  the general step_phi_k! path must vary with it too: ThreadScratchpad{K}
#  bakes K into every field size (A_mat is (K+2)x(K+2), seen_counts has K
#  slots, etc.), so one scratchpad instance can only ever serve one K.
#
#  The caller (phase2 worker) therefore holds a heterogeneous tuple
#  `scratch_by_k` with one concretely-typed ThreadScratchpad{k} per length
#  k = 1..K_ceil (built once at worker init via
#  `ntuple(k -> init_scratch_caches!(ThreadScratchpad{k}(), p), Val(K_ceil))`).
#  Indexing that tuple with a *runtime* k directly (`scratch_by_k[k_cur]`)
#  is type-unstable — its element type is a Union across all K, which the
#  compiler can't specialize away. Instead we dispatch through a manually
#  unrolled if/elseif chain built once via @generated from the tuple's
#  *type* (so its length adapts automatically if K_ceil/K_MAX changes —
#  no hand-editing needed here when the run's ceiling grows or shrinks).
#  Each branch below binds `scratch_by_k[$i]` with a literal index known at
#  generation time, so inside that branch the compiler sees a concrete
#  ThreadScratchpad{i} and step_phi_k! compiles monomorphically just as it
#  always did for the old fixed-K case — the runtime cost is exactly one
#  chain of integer comparisons (k_cur == 1, == 2, ...) to pick the branch,
#  which is negligible next to the φ-construction work each branch does.
#
#  Returns (success::Bool, scratch) so the caller can read roots_out /
#  u_RS / v_RS / coeffs_out etc. off the SAME scratch instance that was
#  actually used for this step, without a second runtime-k lookup.
# ---------------------------------------------------------------------------
#  NOTE ON `backend`: this used to be a bare @generated function with no
#  `backend` parameter at all, so every call silently fell through to
#  step_phi_k!'s own default (StandardArith(p)) no matter what the caller
#  wanted. Since step_phi_dispatch! is the ONLY call site phase2_worker
#  uses for k>=2 steps (see trial3_phase2.jl), that made MontgomeryArith
#  completely unreachable from the actual walk loop even though the
#  interior functions (build_phi_general!, fp_gauss!, etc.) were already
#  backend-parametrized. Fixed by splitting into a thin runtime wrapper
#  that accepts `backend` as an ordinary keyword and an inner @generated
#  function that forwards it into every unrolled branch — code generation
#  still only depends on the TYPE of scratch_by_k, so specialization is
#  unaffected; `backend` is just plumbed through as an extra positional arg.
function step_phi_dispatch!(
    scratch_by_k ::Tuple,
    k_cur        ::Int,
    anchors,
    u0::Int, u1::Int, v0::Int, v1::Int;
    backend::FpArith = StandardArith(p)
)
    @assert k_cur >= 1 "step_phi_dispatch!: k_cur=$k_cur must be >= 1"
    @assert k_cur <= length(scratch_by_k) "step_phi_dispatch!: k_cur=$k_cur exceeds scratch_by_k length $(length(scratch_by_k))"
    return _step_phi_dispatch_gen!(scratch_by_k, k_cur, anchors, u0, u1, v0, v1, backend)
end


# Add this extraction helper
@inline function extract_step_results(scratch::ThreadScratchpad{K}) where K
    nb_k = K + 3
    
    # 1. Extract a-coeff
    a_val = 0
    basis = rr_basis_cached(nb_k)::Vector{NTuple{2, Int}}
    for ki in 1:nb_k
        @inbounds basis_elem = basis[ki]
        if basis_elem[1] == 2 && basis_elem[2] == 0
            @inbounds a_val = scratch.coeffs_out[ki]
            break
        end
    end
    
    # 2. Extract roots
    n_roots = scratch.roots_count[1]
    res_R = n_roots >= 2 ? scratch.roots_out[1] : SENTINEL_PT
    res_S = n_roots >= 2 ? scratch.roots_out[2] : SENTINEL_PT
    
    # 3. Extract Mumford
    u_len = scratch.u_RS_len[1]
    v_len = scratch.v_RS_len[1]
    if u_len == 3
        u0_rs = scratch.u_RS[1]
        u1_rs = scratch.u_RS[2]
        v0_rs = v_len == 0 ? 0 : scratch.v_RS[1]
        v1_rs = v_len >= 2 ? scratch.v_RS[2] : 0
        RS_mumford = (u0_rs, u1_rs, v0_rs, v1_rs)
    else
        RS_mumford = SENTINEL_MUMFORD
    end
    
    return (res_R, res_S, RS_mumford, a_val)
end

# Update the generated function
@generated function _step_phi_dispatch_gen!(
    scratch_by_k ::T,
    k_cur        ::Int,
    anchors,
    u0::Int, u1::Int, v0::Int, v1::Int,
    backend      ::B
) where {T<:Tuple, B<:FpArith}

    n = length(T.parameters)
    ex = :(error("step_phi_dispatch!: k_cur=", k_cur, " out of range 1:", $n))
    for i in n:-1:1
        ex = quote
            if k_cur == $i
                success = step_phi_k!(scratch_by_k[$i], anchors, u0, u1, v0, v1; backend=backend)
                if !success
                    return (false, SENTINEL_PT, SENTINEL_PT, SENTINEL_MUMFORD, 0)
                end
                res_R, res_S, RS_mumford, a_val = extract_step_results(scratch_by_k[$i])
                return (true, res_R, res_S, RS_mumford, a_val)
            else
                $ex
            end
        end
    end
    return ex
end
