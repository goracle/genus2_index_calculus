# =============================================================================
#  trial3_phi_symbolic2.jl  --  Symbolic (last-TWO-anchors-free) phi construction.
#
#  COMPANION TO: trial3_phi_general.jl (build_phi_general! / phi_residual_general!)
#  GENERALIZES:  trial3_phi_symbolic.jl (ONE symbolic anchor, over
#                Ft2 = F_p(t)[w]/(w^2-f(t)))
#
#  WHAT THIS IS
#  ------------
#  trial3_phi_symbolic.jl fixes anchors 1..K-1 concrete and leaves anchor K
#  symbolic (t,w). This module fixes anchors 1..K-2 concrete and leaves the
#  LAST TWO anchors symbolic:
#     anchor K-1 : (t1, w1),  w1^2 = f(t1)
#     anchor K   : (t2, w2),  w2^2 = f(t2)
#  t1, t2 are independent indeterminates. Every coefficient of phi, E, Y, N,
#  u_RS, v_RS now lives in
#
#       Ft4 := F_p(t1,t2)[w1,w2] / (w1^2 - f(t1),  w2^2 - f(t2))
#
#  an 8-dimensional... no -- a DEGREE-4 extension of F_p(t1,t2) (basis
#  {1, w1, w2, w1*w2}), built here as an ITERATED TOWER rather than a single
#  flat 4-component struct:
#
#       Level1 = QuadExt{RFun2}       -- adjoins w1 over F_p(t1,t2)
#       Level2 = QuadExt{Level1}      -- adjoins w2 over Level1
#
#  QuadExt{B} is a small generic "B[w]/(w^2-disc)" ring, written ONCE with
#  +,-,*,inv defined purely in terms of B's own +,-,*,inv,is_zero. It is used
#  TWICE (B=RFun2, then B=Level1), so none of the Ft2-style arithmetic in
#  trial3_phi_symbolic.jl had to be copy-pasted and re-derived by hand for a
#  4-dimensional case -- it falls out of composing the 2-dimensional case
#  with itself. Level2 elements print as a + b*w1 + c*w2 + d*w1*w2 with
#  a,b,c,d in F_p(t1,t2) (see `pretty`).
#
#  Every polynomial-in-x helper below (divmod by a linear factor, divmod by
#  the monic quadratic u(x), mod/invmod/mulmod by a Level2-valued modulus,
#  Gaussian elimination for the (K+2)x(K+2) system) is likewise written ONCE,
#  generically over a type parameter T, and instantiated with T=Level2 --
#  mirroring the corresponding Ft2-specific functions in
#  trial3_phi_symbolic.jl but without re-deriving each one for a new type.
#
#  SCOPE / LIMITATIONS (same spirit as trial3_phi_symbolic.jl's header, plus
#  one new item):
#    - Anchors are pairwise DISTINCT, m=1 each (no tangency), same as the
#      one-symbolic-anchor module. This applies to the two symbolic anchors
#      too: t1 and t2 are treated as formally distinct indeterminates, and
#      any concrete evaluation (t1_0,t2_0) you plug in must satisfy t1_0 !=
#      t2_0 mod p -- symbolic_residual2_concrete asserts this.
#    - u(x), v(x) (the Mumford divisor) are concrete, exactly as before.
#    - RFun2 (elements of F_p(t1,t2)) is stored as num/den where num is an
#      expanded BiPoly but den is a FACTORED multiset of BiPoly factors
#      (Dict{BiPoly,Int} => exponent). This is NOT a real bivariate GCD/
#      factorization engine (F_p[t1,t2] is a UFD, not Euclidean -- an actual
#      factoring routine would go via resultants or Groebner bases). Instead:
#      the denominator alphabet in this module's actual use (gauss_solve2 on
#      a Level2-valued system) is small and mostly RECURRING -- pivot
#      denominators, f(t1), f(t2), (t1-t2)-type factors get reused verbatim
#      over and over rather than being genuinely new polynomials each time.
#      Representing den as factor=>exponent and merging by structural
#      equality (BiPoly's own ==, which Dict already gives for free) turns
#      the dominant cost -- repeatedly multiplying the SAME growing
#      denominator into itself across an elimination column -- from
#      "convolve two huge Dicts" into "increment an integer". Numerators are
#      still expanded (they don't blow up nearly as fast in this module's
#      use, and keeping them expanded keeps bipoly_add/bipoly_eval trivial).
#      This is not a substitute for a real bivariate GCD (no cancellation is
#      attempted between num and den), but it removes the specific
#      catastrophic-blowup mode that made gauss_solve2 hang on sample 1: see
#      RFun2's +,-,*,inv below.
#    - Requires p prime and p > everything touched, same general-position
#      assumption as the rest of trial3.
#    - NOT YET RUN: Julia was not available in the environment this was
#      written in, so this has NOT been executed or cross-checked against
#      build_phi_general!/phi_residual_general! the way
#      trial3_phi_symbolic.jl was (see that file's header: "checked to
#      agree numerically for K=1,2,3"). Please run the equivalent
#      cross-check here (symbolic_residual2_concrete(K, fixed_anchors, ...,
#      t1_0,y1_0,t2_0,y2_0) vs. build_phi_general!/phi_residual_general! run
#      directly with (t1_0,y1_0) and (t2_0,y2_0) as the last two concrete
#      anchors) before trusting this for real work.
#
#  USAGE
#  -----
#      result = symbolic_residual2(K, fixed_anchors, u0,u1,v0,v1, F_POLY_ASC, p)
#      print_symbolic_residual2(result)
#
#  fixed_anchors :: Vector{Tuple{Int,Int}}, length K-2 -- the FIXED anchors'
#                   (px,py). Anchors K-1 and K are symbolic and are NOT
#                   passed in.
#  u0,u1,v0,v1,F_POLY_ASC,p :: same conventions as trial3_phi_symbolic.jl.
#
#  result.u_RS, result.v_RS :: Vector{Level2}, i.e. genuine
#  F_p(t1,t2)[w1,w2]/(w1^2-f(t1),w2^2-f(t2)) elements (never assumed to
#  collapse to anything smaller -- see trial3_phi_symbolic.jl's "WHY THE
#  OUTPUT DOES NOT COLLAPSE" discussion; the same reasoning applies here
#  once more, now for two independent symbolic anchors instead of one).
#
#  To get a concrete F_p residual for specific real anchor points (t1_0,y1_0)
#  and (t2_0,y2_0) with y1_0^2==f(t1_0), y2_0^2==f(t2_0) mod p, use:
#
#      u_RS_c, v_RS_c = symbolic_residual2_concrete(K, fixed_anchors,
#                           u0,u1,v0,v1, F_POLY_ASC, p, t1_0,y1_0,t2_0,y2_0)
# =============================================================================

# =============================================================================
#  trial3_phi_symbolic2_oscar.jl  --  Symbolic (last-TWO-anchors-free) phi
#  construction, powered by OSCAR.jl.
# =============================================================================

module PhiSymbolic2

using Oscar

export symbolic_residual2, symbolic_residual2_concrete,
       print_symbolic_residual2, print_symbolic_residual2_concrete


# =============================================================================
#  PART 1: Combinatorics and RR Basis (Integer operations, preserved)
# =============================================================================

function rr_basis2(n_basis::Int)::Vector{NTuple{2,Int}}
    basis = NTuple{2,Int}[]
    max_order = 2 * n_basis + 10
    candidates = Tuple{Int,Int,Int}[]
    for i in 0:max_order÷2
        push!(candidates, (2i, i, 0))
        push!(candidates, (2i+5, i, 1))
    end
    sort!(candidates, by = x -> x[1])
    seen = 0
    for (_, i, j) in candidates
        seen += 1
        push!(basis, (i, j))
        seen == n_basis && break
    end
    return basis
end

function build_xmodu_table2(max_i::Int, u0::Int, u1::Int, p::Int)::Tuple{Vector{Int},Vector{Int}}
    r0 = zeros(Int, max_i + 2)
    r1 = zeros(Int, max_i + 2)
    r0[1] = 1; r1[1] = 0
    if max_i + 1 >= 1
        r0[2] = 0; r1[2] = 1
    end
    for i in 2:(max_i+1)
        prev0, prev1 = r0[i], r1[i]
        r0[i+1] = mod(-prev1 * u0, p)
        r1[i+1] = mod(prev0 - prev1 * u1, p)
    end
    return (r0, r1)
end

function reduce_monomial_mod_u2(i::Int, j::Int, u0::Int, u1::Int, v0::Int, v1::Int,
                                 r0tab::Vector{Int}, r1tab::Vector{Int}, p::Int)::Tuple{Int,Int}
    a0, a1 = r0tab[i+1], r1tab[i+1]
    j == 0 && return (a0, a1)
    b0, b1 = r0tab[i+2], r1tab[i+2]
    r0 = mod(v0*a0 + v1*b0, p)
    r1 = mod(v0*a1 + v1*b1, p)
    return (r0, r1)
end

# =============================================================================
#  PART 2: Core Construction using OSCAR
# =============================================================================

struct SymbolicResidualResult2
    K::Int
    u_RS_coeffs::Vector{Any} # Coefficients in Level 2
    v_RS_coeffs::Vector{Any} # Coefficients in Level 2
    deg_E::Int
    deg_Y::Int
    n_len_before_divide::Int
end



function print_symbolic_residual2(K::Int, res; io::IO=stdout)
    println(io, "Symbolic Residual Result (K = $K):")
    println(io, "  u_RS(x; t1, t2):")
    for (i, coeff) in enumerate(res.u_RS_coeffs)
        # Using string representation from Oscar/AbstractAlgebra
        println(io, "    x^$(i-1): $(string(coeff))")
    end
    
    println(io, "  v_RS(x; t1, t2):")
    for (i, coeff) in enumerate(res.v_RS_coeffs)
        println(io, "    x^$(i-1): $(string(coeff))")
    end
end


function print_symbolic_residual2_concrete(K::Int, t1_0::Int, y1_0::Int, t2_0::Int, y2_0::Int,
                                            u_RS_concrete::Vector{Int}, v_RS_concrete::Vector{Int};
                                            io::IO=stdout)
    if isempty(u_RS_concrete) || isempty(v_RS_concrete)
        throw(ArgumentError("Cannot print empty concrete residuals. Check for anchor convergence or geometric degeneracy upstream."))
    end

    println(io, "=== Symbolic residual (concrete), K=$K, evaluated at (t1_0,y1_0)=($t1_0,$y1_0), (t2_0,y2_0)=($t2_0,$y2_0) ===")
    println(io, "u_RS(x)  [monic, deg $(length(u_RS_concrete)-1)]:  $u_RS_concrete")
    println(io, "v_RS(x)  [deg $(length(v_RS_concrete)-1)]:  $v_RS_concrete")
end



function symbolic_residual2(K::Int, fixed_anchors::Vector{Tuple{Int,Int}}, u0::Int, u1::Int, v0::Int, v1::Int,
                             F_POLY_ASC::Vector{Int}, p::Int)::SymbolicResidualResult2

    # Gracefully exit on degenerate (coincident) anchors to prevent batch crashes
    if K < 2 || length(fixed_anchors) != K - 2
        return SymbolicResidualResult2(K, Any[], Any[], -1, -1, 0)
    end
    for i in 1:length(fixed_anchors), j in (i+1):length(fixed_anchors)
        if fixed_anchors[i] == fixed_anchors[j]
            return SymbolicResidualResult2(K, Any[], Any[], -1, -1, 0)
        end
    end

    # 1. Setup Base Fields and Indeterminates in OSCAR
    Fp = GF(p)
    R_t, (t1, t2) = polynomial_ring(Fp, ["t1", "t2"])
    F_t = fraction_field(R_t)

    # Construct f(t1) and f(t2) directly inside F_t
    f_t1 = sum(F_t(Fp(c)) * t1^(i-1) for (i, c) in enumerate(F_POLY_ASC))
    f_t2 = sum(F_t(Fp(c)) * t2^(i-1) for (i, c) in enumerate(F_POLY_ASC))

    # 2. Build the Tower
    R_w1, w1_var = polynomial_ring(F_t, "w1")
    K1, _ = residue_ring(R_w1, w1_var^2 - f_t1)
    w1 = gen(K1)

    R_w2, w2_var = polynomial_ring(K1, "w2")
    K2, _ = residue_ring(R_w2, w2_var^2 - K1(f_t2))
    w2 = gen(K2)

    K2x, X = polynomial_ring(K2, "X")

    # Define explicit tower images for exact divisions later
    t1_K2 = K2(K1(t1))
    w1_K2 = K2(w1)
    t2_K2 = K2(K1(t2))
    w2_K2 = w2

    # 3. Setup Linear System directly over K2
    nb = K + 3
    basis = rr_basis2(nb)
    y_idx = findfirst(bi -> bi == (0,1), basis)
    if y_idx === nothing
        return SymbolicResidualResult2(K, Any[], Any[], -1, -1, 0)
    end

    n_unknowns = K + 2
    other_idx = [idx for idx in 1:nb if idx != y_idx]

    A = zero_matrix(K2, n_unknowns, n_unknowns)
    rhs = zero_matrix(K2, n_unknowns, 1)

    # Consolidate all anchor points into a single K2-valued vector
    anchor_pts = Vector{Tuple{elem_type(K2), elem_type(K2)}}(undef, K)
    for a in 1:(K-2)
        px_raw, py_raw = fixed_anchors[a]
        anchor_pts[a] = (K2(px_raw), K2(py_raw))
    end
    anchor_pts[K-1] = (t1_K2, w1_K2)
    anchor_pts[K]   = (t2_K2, w2_K2)

    # Rows 1..K (Anchors evaluated over K2)
    for a in 1:K
        px, py = anchor_pts[a]
        for (col, bidx) in enumerate(other_idx)
            bi, bj = basis[bidx]
            A[a, col] = (px^bi) * (bj == 1 ? py : K2(1))
        end
        bi_n, bj_n = basis[y_idx]
        rhs[a, 1] = -((px^bi_n) * (bj_n == 1 ? py : K2(1)))
    end

    # Rows K+1, K+2 (Mumford condition mod u)
    max_basis_i = maximum(bi for (bi,_) in basis)
    r0tab, r1tab = build_xmodu_table2(max_basis_i + 1, u0, u1, p)
    row0, row1 = K + 1, K + 2

    for (col, bidx) in enumerate(other_idx)
        bi, bj = basis[bidx]
        rr0, rr1 = reduce_monomial_mod_u2(bi, bj, u0, u1, v0, v1, r0tab, r1tab, p)
        A[row0, col] = K2(rr0)
        A[row1, col] = K2(rr1)
    end
    
    bi_n, bj_n = basis[y_idx]
    rn0, rn1 = reduce_monomial_mod_u2(bi_n, bj_n, u0, u1, v0, v1, r0tab, r1tab, p)
    rhs[row0, 1] = K2(mod(-rn0, p))
    rhs[row1, 1] = K2(mod(-rn1, p))

    # 4. Solve the matrix system directly over K2
    local c_sol
    try
        c_sol = solve(A, rhs; side = :right)
    catch e
        @error "Linear system resolution failed over K2" exception=e
        return SymbolicResidualResult2(K, Any[], Any[], -1, -1, 0)
    end

    # Reconstruct the full coefficients vector (restoring the y-monomial)
    coeffs_out = Vector{elem_type(K2)}(undef, nb)
    for (col, bidx) in enumerate(other_idx)
        coeffs_out[bidx] = c_sol[col, 1]
    end
    coeffs_out[y_idx] = K2(1)

    # 5. Extract E(x) and Y(x)
    E_poly = K2x(0)
    Y_poly = K2x(0)
    for bidx in 1:nb
        bi, bj = basis[bidx]
        c_here = coeffs_out[bidx]
        if bj == 0
            E_poly += c_here * X^bi
        else
            Y_poly += c_here * X^bi
        end
    end

    deg_E = iszero(E_poly) ? -1 : degree(E_poly)
    deg_Y = iszero(Y_poly) ? -1 : degree(Y_poly)

    # 6. Form N(x) = E(x)^2 - f(x)*Y(x)^2
    f_poly_K2x = sum(K2(c) * X^(i-1) for (i, c) in enumerate(F_POLY_ASC))
    Nx = E_poly^2 - f_poly_K2x * Y_poly^2
    n_len_before_divide = iszero(Nx) ? 0 : degree(Nx) + 1

    # 7. Exact division
    cur = Nx
    for (px_raw, _) in fixed_anchors
        cur = divexact(cur, X - K2(px_raw))
    end
    cur = divexact(cur, X - t1_K2)
    cur = divexact(cur, X - t2_K2)

    u_poly_K2x = X^2 + K2(u1)*X + K2(u0)
    cur = divexact(cur, u_poly_K2x)

    if iszero(cur)
        return SymbolicResidualResult2(K, Any[], Any[], deg_E, deg_Y, n_len_before_divide)
    end

    # Normalize to monic
    u_RS = cur * inv(leading_coefficient(cur))

    # 8. Compute v_RS(x)
    if iszero(Y_poly)
        return SymbolicResidualResult2(K, Any[], Any[], deg_E, deg_Y, n_len_before_divide)
    end

    _, Y_inv_mod, _ = gcdx(Y_poly, u_RS)
    v_RS = mod(-E_poly * Y_inv_mod, u_RS)

    return SymbolicResidualResult2(
        K,
        collect(coefficients(u_RS)),
        collect(coefficients(v_RS)),
        deg_E, deg_Y, n_len_before_divide
    )
end


function _eval_K2_to_Fp(val, t1_0::Int, y1_0::Int, t2_0::Int, y2_0::Int, p::Int)
    Fp = GF(p)
    val_w2 = data(val) # polynomial in w2 over K1
    
    c0 = coeff(val_w2, 0)
    c1 = coeff(val_w2, 1)

    function eval_K1(k1_val)
        k1_w1 = data(k1_val)
        b0 = coeff(k1_w1, 0)
        b1 = coeff(k1_w1, 1)

        eval_rfun(frac) = begin
            num_val = evaluate(numerator(frac), [Fp(t1_0), Fp(t2_0)])
            den_val = evaluate(denominator(frac), [Fp(t1_0), Fp(t2_0)])
            if iszero(den_val)
                return Fp(0) # Evaluate to zero safely on division issues
            end
            return num_val * inv(den_val)
        end

        res = eval_rfun(b0) + eval_rfun(b1) * Fp(y1_0)
        return res
    end

    final_val = eval_K1(c0) + eval_K1(c1) * Fp(y2_0)
    return Int(lift(ZZ, final_val)) # lifts back to Int (matches trial3_phi_symbolic.jl / trial3_phi_general.jl convention)
end

function symbolic_residual2_concrete(K::Int, fixed_anchors::Vector{Tuple{Int,Int}}, u0::Int, u1::Int, v0::Int, v1::Int,
                                      F_POLY_ASC::Vector{Int}, p::Int,
                                      t1_0::Int, y1_0::Int, t2_0::Int, y2_0::Int)::Tuple{Vector{Int},Vector{Int}}

    # Throw a hard exception on degenerate (coincident) evaluation points
    if mod(t1_0 - t2_0, p) == 0
        throw(ArgumentError("Evaluation failed: Coincident symbolic anchors evaluated at the same point mod p: t1_0 ($t1_0) == t2_0 ($t2_0). Anchors must be pairwise distinct."))
    end

    f_t1_0 = mod(sum(c * powermod(t1_0, i-1, p) for (i, c) in enumerate(F_POLY_ASC)), p)
    if mod(y1_0^2 - f_t1_0, p) != 0
        throw(DomainError(y1_0, "Point (t1_0, y1_0) does not lie on the curve mod p."))
    end

    f_t2_0 = mod(sum(c * powermod(t2_0, i-1, p) for (i, c) in enumerate(F_POLY_ASC)), p)
    if mod(y2_0^2 - f_t2_0, p) != 0
        throw(DomainError(y2_0, "Point (t2_0, y2_0) does not lie on the curve mod p."))
    end

    res = symbolic_residual2(K, fixed_anchors, u0, u1, v0, v1, F_POLY_ASC, p)
    if isempty(res.u_RS_coeffs) || isempty(res.v_RS_coeffs)
        throw(ErrorException("Symbolic calculation yielded empty equations unexpectedly."))
    end

    u_concrete = [_eval_K2_to_Fp(c, t1_0, y1_0, t2_0, y2_0, p) for c in res.u_RS_coeffs]
    v_concrete = [_eval_K2_to_Fp(c, t1_0, y1_0, t2_0, y2_0, p) for c in res.v_RS_coeffs]

    while length(u_concrete) > 1 && u_concrete[end] == 0; pop!(u_concrete); end
    while length(v_concrete) > 1 && v_concrete[end] == 0; pop!(v_concrete); end

    return (u_concrete, v_concrete)
end

end # module PhiSymbolic2
