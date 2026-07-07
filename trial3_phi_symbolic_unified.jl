# =============================================================================
#  trial3_phi_symbolic_unified.jl  --  Symbolic (last-c-anchors-free) phi construction.
# =============================================================================

module PhiSymbolic

using Oscar

export symbolic_residual, symbolic_residual_concrete,
       print_symbolic_residual, print_symbolic_residual_concrete,
       SymbolicResidualResult

# =============================================================================
#  PART 1: Combinatorics and RR Basis (Integer operations, preserved)
# =============================================================================

function rr_basis(n_basis::Int)::Vector{NTuple{2,Int}}
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

function build_xmodu_table(max_i::Int, u0::Int, u1::Int, p::Int)::Tuple{Vector{Int},Vector{Int}}
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

function reduce_monomial_mod_u(i::Int, j::Int, u0::Int, u1::Int, v0::Int, v1::Int,
                               r0tab::Vector{Int}, r1tab::Vector{Int}, p::Int)::Tuple{Int,Int}
    a0, a1 = r0tab[i+1], r1tab[i+1]
    j == 0 && return (a0, a1)
    b0, b1 = r0tab[i+2], r1tab[i+2]
    r0 = mod(v0*a0 + v1*b0, p)
    r1 = mod(v0*a1 + v1*b1, p)
    return (r0, r1)
end

# =============================================================================
#  PART 2: Core Construction using OSCAR (Generic Tower)
# =============================================================================

struct SymbolicResidualResult
    K::Int
    c::Int
    u_RS_coeffs::Vector{Any} # Coefficients in K_c
    v_RS_coeffs::Vector{Any} # Coefficients in K_c
    deg_E::Int
    deg_Y::Int
    n_len_before_divide::Int
end

function print_symbolic_residual(res::SymbolicResidualResult; io::IO=stdout)
    println(io, "=== Symbolic residual ($(res.c) symbolic anchor(s)), K=$(res.K) ===")
    println(io, "deg(E)=$(res.deg_E)  deg(Y)=$(res.deg_Y)  deg(N) before division = $(res.n_len_before_divide - 1)")
    if isempty(res.u_RS_coeffs) || isempty(res.v_RS_coeffs)
        println(io, "  (construction failed or degenerate -- no u_RS/v_RS coefficients to show)")
        return
    end
    println(io, "u_RS(x; t_i) [deg $(length(res.u_RS_coeffs)-1)]:")
    for (i, coeff) in enumerate(res.u_RS_coeffs)
        println(io, "    x^$(i-1): $(coeff)")
    end
    println(io, "v_RS(x; t_i) [deg $(length(res.v_RS_coeffs)-1)]:")
    for (i, coeff) in enumerate(res.v_RS_coeffs)
        println(io, "    x^$(i-1): $(coeff)")
    end
end

function print_symbolic_residual_concrete(K::Int, c::Int, sym_anchors::Vector{Tuple{Int,Int}},
                                          u_RS_concrete::Vector{Int}, v_RS_concrete::Vector{Int};
                                          io::IO=stdout)
    println(io, "=== Symbolic residual (concrete), K=$K, c=$c, evaluated at symbolic anchors=$sym_anchors ===")
    println(io, "u_RS(x)  [monic, deg $(length(u_RS_concrete)-1)]:  $u_RS_concrete")
    println(io, "v_RS(x)  [deg $(length(v_RS_concrete)-1)]:  $v_RS_concrete")
end

function symbolic_residual(K::Int, c::Int, fixed_anchors::Vector{Tuple{Int,Int}}, 
                           u0::Int, u1::Int, v0::Int, v1::Int,
                           F_POLY_ASC::Vector{Int}, p::Int)::SymbolicResidualResult

    # Gracefully exit on degenerate setups
    if K < c || length(fixed_anchors) != K - c
        return SymbolicResidualResult(K, c, Any[], Any[], -1, -1, 0)
    end
    for i in 1:length(fixed_anchors), j in (i+1):length(fixed_anchors)
        if fixed_anchors[i] == fixed_anchors[j]
            return SymbolicResidualResult(K, c, Any[], Any[], -1, -1, 0)
        end
    end

    # 1. Setup Base Fields and Indeterminates in OSCAR
    Fp = GF(p)
    if c == 0
        R_t, t_vars = Fp, []
    else
        R_t, t_vars = rational_function_field(Fp, ["t$i" for i in 1:c])
    end

    # 2. Build the Tower Iteratively
    K_curr = R_t
    w_vars = Any[]

    for i in 1:c
        f_ti = sum(K_curr(Fp(coeff)) * K_curr(t_vars[i])^(j-1) for (j, coeff) in enumerate(F_POLY_ASC))
        R_wi, wi_var = polynomial_ring(K_curr, "w$i")
        K_curr, _ = residue_ring(R_wi, wi_var^2 - f_ti)
        push!(w_vars, gen(K_curr))
        
        # Promote all previous vars into the new layer
        t_vars = [K_curr(tv) for tv in t_vars]
        for j in 1:(i-1)
            w_vars[j] = K_curr(w_vars[j])
        end
    end

    K_final = K_curr
    Kx, X = polynomial_ring(K_final, "X")

    # 3. Setup Linear System directly over K_final
    nb = K + 3
    basis = rr_basis(nb)
    y_idx = findfirst(bi -> bi == (0,1), basis)
    if y_idx === nothing
        return SymbolicResidualResult(K, c, Any[], Any[], -1, -1, 0)
    end

    n_unknowns = K + 2
    other_idx = [idx for idx in 1:nb if idx != y_idx]

    A = zero_matrix(K_final, n_unknowns, n_unknowns)
    rhs = zero_matrix(K_final, n_unknowns, 1)

    anchor_pts = Vector{Tuple{elem_type(K_final), elem_type(K_final)}}(undef, K)
    for a in 1:(K-c)
        px_raw, py_raw = fixed_anchors[a]
        anchor_pts[a] = (K_final(px_raw), K_final(py_raw))
    end
    for i in 1:c
        anchor_pts[K-c+i] = (t_vars[i], w_vars[i])
    end

    # Rows 1..K (Anchors evaluated over K_final)
    for a in 1:K
        px, py = anchor_pts[a]
        for (col, bidx) in enumerate(other_idx)
            bi, bj = basis[bidx]
            A[a, col] = (px^bi) * (bj == 1 ? py : K_final(1))
        end
        bi_n, bj_n = basis[y_idx]
        rhs[a, 1] = -((px^bi_n) * (bj_n == 1 ? py : K_final(1)))
    end

    # Rows K+1, K+2 (Mumford condition mod u)
    max_basis_i = maximum(bi for (bi,_) in basis)
    r0tab, r1tab = build_xmodu_table(max_basis_i + 1, u0, u1, p)
    row0, row1 = K + 1, K + 2

    for (col, bidx) in enumerate(other_idx)
        bi, bj = basis[bidx]
        rr0, rr1 = reduce_monomial_mod_u(bi, bj, u0, u1, v0, v1, r0tab, r1tab, p)
        A[row0, col] = K_final(rr0)
        A[row1, col] = K_final(rr1)
    end
    
    bi_n, bj_n = basis[y_idx]
    rn0, rn1 = reduce_monomial_mod_u(bi_n, bj_n, u0, u1, v0, v1, r0tab, r1tab, p)
    rhs[row0, 1] = K_final(mod(-rn0, p))
    rhs[row1, 1] = K_final(mod(-rn1, p))

    # 4. Solve the matrix system directly over K_final
    local c_sol
    try
        c_sol = solve(A, rhs; side = :right)
    catch e
        return SymbolicResidualResult(K, c, Any[], Any[], -1, -1, 0)
    end

    coeffs_out = Vector{elem_type(K_final)}(undef, nb)
    for (col, bidx) in enumerate(other_idx)
        coeffs_out[bidx] = c_sol[col, 1]
    end
    coeffs_out[y_idx] = K_final(1)

    # 5. Extract E(x) and Y(x)
    E_poly = Kx(0)
    Y_poly = Kx(0)
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
    f_poly_Kx = sum(K_final(coeff) * X^(i-1) for (i, coeff) in enumerate(F_POLY_ASC))
    Nx = E_poly^2 - f_poly_Kx * Y_poly^2
    n_len_before_divide = iszero(Nx) ? 0 : degree(Nx) + 1

    # 7. Exact division
    cur = Nx
    for (px_raw, _) in fixed_anchors
        cur = divexact(cur, X - K_final(px_raw))
    end
    for i in 1:c
        cur = divexact(cur, X - t_vars[i])
    end

    u_poly_Kx = X^2 + K_final(u1)*X + K_final(u0)
    cur = divexact(cur, u_poly_Kx)

    if iszero(cur)
        return SymbolicResidualResult(K, c, Any[], Any[], deg_E, deg_Y, n_len_before_divide)
    end

    # Normalize to monic
    u_RS = cur * inv(leading_coefficient(cur))

    # 8. Compute v_RS(x)
    if iszero(Y_poly)
        return SymbolicResidualResult(K, c, Any[], Any[], deg_E, deg_Y, n_len_before_divide)
    end

    _, Y_inv_mod, _ = gcdx(Y_poly, u_RS)
    v_RS = mod(-E_poly * Y_inv_mod, u_RS)

    return SymbolicResidualResult(
        K, c,
        collect(coefficients(u_RS)),
        collect(coefficients(v_RS)),
        deg_E, deg_Y, n_len_before_divide
    )
end

function _eval_tower_recursive(val, c::Int, level::Int, sym_anchors_concrete::Vector{Tuple{Int,Int}}, p::Int)
    Fp = GF(p)
    if level == 0
        # Base case: Rational function evaluation
        num = numerator(val)
        den = denominator(val)
        t_vals = [Fp(sym_anchors_concrete[i][1]) for i in 1:c]
        den_val = evaluate(den, t_vals)
        if iszero(den_val)
            return Fp(0)
        end
        return evaluate(num, t_vals) * inv(den_val)
    end

    val_poly = data(val)
    c0 = coeff(val_poly, 0)
    c1 = coeff(val_poly, 1)

    e0 = _eval_tower_recursive(c0, c, level - 1, sym_anchors_concrete, p)
    e1 = _eval_tower_recursive(c1, c, level - 1, sym_anchors_concrete, p)
    y_val = Fp(sym_anchors_concrete[level][2])

    return e0 + e1 * y_val
end

function symbolic_residual_concrete(K::Int, c::Int, fixed_anchors::Vector{Tuple{Int,Int}}, 
                                    u0::Int, u1::Int, v0::Int, v1::Int,
                                    F_POLY_ASC::Vector{Int}, p::Int,
                                    sym_anchors_concrete::Vector{Tuple{Int,Int}})::Tuple{Vector{Int},Vector{Int}}

    # Validate roots before attempting solving
    for i in 1:c
        t_0, y_0 = sym_anchors_concrete[i]
        f_t_0 = mod(sum(coeff * powermod(t_0, j-1, p) for (j, coeff) in enumerate(F_POLY_ASC)), p)
        if mod(y_0^2 - f_t_0, p) != 0
            return (Int[], Int[])
        end
    end

    res = symbolic_residual(K, c, fixed_anchors, u0, u1, v0, v1, F_POLY_ASC, p)
    if isempty(res.u_RS_coeffs) || isempty(res.v_RS_coeffs)
        return (Int[], Int[])
    end

    u_concrete = [Int(lift(ZZ, _eval_tower_recursive(coeff, c, c, sym_anchors_concrete, p))) for coeff in res.u_RS_coeffs]
    v_concrete = [Int(lift(ZZ, _eval_tower_recursive(coeff, c, c, sym_anchors_concrete, p))) for coeff in res.v_RS_coeffs]

    while length(u_concrete) > 1 && u_concrete[end] == 0; pop!(u_concrete); end
    while length(v_concrete) > 1 && v_concrete[end] == 0; pop!(v_concrete); end

    return (u_concrete, v_concrete)
end

end # module PhiSymbolic
