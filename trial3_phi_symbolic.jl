# =============================================================================
#  trial3_phi_symbolic.jl  --  Symbolic (last-anchor-free) phi construction.
#
#  COMPANION TO: trial3_phi_general.jl (build_phi_general! / phi_residual_general!)
#
#  WHAT THIS IS
#  ------------
#  trial3_phi_general.jl solves, for K concrete anchor points, the (K+2)x(K+2)
#  linear system for phi's coefficients, then divides N(x) = E(x)^2 - f(x)Y(x)^2
#  by the known factors (each anchor's (x-px_i), and u(x)) to get the residual
#  pair (u_RS, v_RS) -- all over F_p, all concrete numbers.
#
#  This module does the SAME construction, for general K, but with:
#     anchors 1..K-1  : fixed, concrete F_p points (px_i, py_i), as usual
#     anchor  K       : SYMBOLIC. Its x-coordinate is an indeterminate t,
#                       and its y-coordinate w is tied to the curve equation
#                       w^2 = f(t) -- i.e. we work in the coordinate ring
#                       F_p(t)[w]/(w^2 - f(t)), and every element normalizes
#                       to a(t) + b(t)*w with a,b in F_p(t). Any power of w
#                       >= 2 that arises gets reduced immediately via
#                       w^2 = f(t) (per Claire's instruction). We never take
#                       w = sqrt(f(t)) as a *rational* function of t -- the
#                       symbolic anchor genuinely lives in the degree-2
#                       extension, exactly like any other affine point on
#                       the curve.
#
#  The output is u_RS(x; t) and v_RS(x; t): the coefficients of the residual
#  Mumford divisor, each as a genuine element of Ft2 = F_p(t)[w]/(w^2-f(t))
#  -- i.e. each coefficient is a pair (a(t), b(t)) with a,b in F_p(t), NOT
#  a plain RFun -- see WHY THE OUTPUT DOES NOT COLLAPSE TO F_p(t) below.
#
#  WHY THE OUTPUT DOES NOT COLLAPSE TO F_p(t): Ft2 all the way through
#  ----------------------------------------------------------------------
#  An earlier version of this module asserted that N(x) = E(x)^2 - f(x)*Y(x)^2
#  must have b(t) == 0 in every coefficient, on the theory that
#  N(x) = phi(x,y)*phi(x,-y) is invariant under the hyperelliptic involution
#  y -> -y, and that this involution acts on the symbolic anchor's
#  y-coordinate as w -> -w. That assertion was WRONG and fired on every
#  input; the fix (per Claire, 2026-07-05) was to drop it and carry
#  u_RS, v_RS as genuine Ft2 objects.
#
#  The error was conflating two different involutions:
#
#    (1) w -> -w, i.e. sigma: F_p(t)[w]/(w^2-f(t)) -> itself, fixing F_p(t).
#        This is the Galois/Frobenius-type automorphism of the FIELD the
#        symbolic anchor's y-coordinate lives in -- it changes WHICH curve
#        point (t,w) vs (t,-w) got anchored, i.e. moves to a different,
#        generically unrelated divisor with its own (E,Y). Verified
#        numerically (p=10007, K=1): applying sigma to every input of the
#        linear system sends each phi-coefficient's (a,b) -> (a,-b) exactly
#        (real Galois conjugation, working as designed) -- but N(x) formed
#        from the sigma-twisted (E,Y) is NOT the sigma-image of the
#        original N(x): the a-parts of N(x) do agree either way (that part
#        of the identity is fine), but the b-parts are different nonzero
#        elements of F_p(t) in each case, not related to each other by
#        negation or anything else. So sigma-invariance of N(x) is simply
#        false, and asserting b(t)==0 from it was asserting a false thing.
#
#    (2) y -> -y in the DEFINITION N(x) := phi(x,y)*phi(x,-y). Here y is
#        the free curve-coordinate variable that Y(x)*y multiplies against
#        -- NOT the anchor's w. This is the involution that actually makes
#        N(x) = E(x)^2 - f(x)*Y(x)^2 a polynomial in x alone, and it holds
#        unconditionally by construction (E(x)^2 - f(x)Y(x)^2 is manifestly
#        the "y -> -y norm" regardless of what E, Y are) -- no assertion
#        needed for this part; it was never in question.
#
#  What (1) and (2) do NOT combine to give is: "N(x)'s coefficients, as
#  elements of F_p(t)[w]/(w^2-f(t)) built from an anchor at (t,w), are
#  themselves fixed by w -> -w." They aren't, because E(x), Y(x) depend on
#  w only through which point was anchored (via (1)), and N(x) doesn't
#  undo that dependence -- it only guarantees polynomiality in x (via (2)),
#  which is a property of the OTHER variable. A symbolic anchor (t,w) is a
#  point of the curve over F_p(t), not over F_p(t) itself (w satisfies a
#  degree-2 relation over F_p(t) that is irreducible, deg f = 5 odd), so
#  there is no general reason for objects built from it -- u_RS, v_RS
#  included -- to descend to F_p(t). They are honest Ft2 elements.
#
#  The concrete-evaluation entry point (symbolic_residual_concrete, see
#  USAGE below) is where a REAL branch gets chosen: plugging in a specific
#  curve point (t0, y0) with y0^2 = f(t0) and combining a(t0) + b(t0)*y0
#  lands back in plain F_p automatically (real + real*real = real), and
#  matches trial3_phi_general.jl's build_phi_general!/phi_residual_general!
#  run directly with (t0,y0) as the K-th concrete anchor -- this has been
#  checked to agree numerically for K=1,2,3. That's the only place a
#  "collapse" ever legitimately happens; it does not happen at the Ft2
#  level, and this module no longer claims that it does.
#
#  SCOPE / LIMITATIONS
#  --------------------
#    - Anchors are assumed pairwise DISTINCT, m=1 each (no tangency). The
#      concrete build_phi_general! supports m=2 tangency via a Taylor
#      branch-series expansion; extending that to a symbolic anchor would
#      need a symbolic branch series (deg(f) x-derivatives packaged as
#      F_p(t) rational functions) -- not attempted here.
#    - u(x), v(x) (the Mumford divisor) are concrete, as in
#      phi_residual_general!. Only anchor K is symbolic.
#    - Requires p prime and p > everything touched, same general-position
#      assumption as the rest of trial3.
#
#  USAGE
#  -----
#      result = symbolic_residual(K, fixed_anchors, u0, u1, v0, v1, F_POLY_ASC, p)
#      print_symbolic_residual(result)
#
#  fixed_anchors  :: Vector{Tuple{Int,Int}}, length K-1 -- the FIXED anchors'
#                    (px,py). The K-th (last) anchor is the symbolic one and
#                    is NOT passed in (there's nothing to pass -- it's t).
#  u0,u1          :: u(x) = x^2 + u1*x + u0  (concrete Mumford divisor)
#  v0,v1          :: v(x) = v1*x + v0        (concrete Mumford divisor)
#  F_POLY_ASC     :: f(x) coefficients, ASCENDING, F_POLY_ASC[i] = coeff of
#                    x^(i-1). NOTE this is the opposite order from
#                    trial3_phi_general.jl's F_POLY_DESC (descending); it
#                    matches that file's OTHER convention instead (poly_mul,
#                    poly_sq, scratch.poly_buf are all ascending there too).
#  p              :: the prime field characteristic.
#
#  result.u_RS, result.v_RS are Vector{Ft2} (see WHY THE OUTPUT DOES NOT
#  COLLAPSE above) -- each coefficient is a genuine a(t)+b(t)*w pair, not a
#  bare RFun. To get a concrete F_p residual for a specific real anchor
#  point (t0,y0) with y0^2 == f(t0) mod p, use:
#
#      u_RS_concrete, v_RS_concrete =
#          symbolic_residual_concrete(K, fixed_anchors, u0,u1,v0,v1,
#                                      F_POLY_ASC, p, t0, y0)
#
#  which evaluates a(t0), b(t0) and recombines a(t0)+b(t0)*y0 (this is the
#  ONLY point in the pipeline where a specific y0-branch is chosen, and it's
#  where the result becomes a plain Vector{Int} over F_p, checked to agree
#  with running trial3_phi_general.jl's build_phi_general!/
#  phi_residual_general! directly with (t0,y0) as the K-th concrete anchor).
# =============================================================================

module PhiSymbolic

using Oscar

export RFun, Ft2, symbolic_residual, symbolic_residual_concrete,
       print_symbolic_residual, print_symbolic_residual_concrete,
       SymbolicResidualResult, pretty

# =============================================================================
#  PART 1 & 2: OSCAR Wrappers for Drop-In Compatibility
# =============================================================================

struct RFun
    ex::Any # Oscar Rational Function Field element
end

struct Ft2
    ex::Any # Oscar Quotient/Residue Ring element
end

# Forwarding standard ring operations for RFun
Base.:+(a::RFun, b::RFun) = RFun(a.ex + b.ex)
Base.:-(a::RFun, b::RFun) = RFun(a.ex - b.ex)
Base.:-(a::RFun)          = RFun(-a.ex)
Base.:*(a::RFun, b::RFun) = RFun(a.ex * b.ex)
Base.:/(a::RFun, b::RFun) = RFun(a.ex / b.ex)
Base.inv(a::RFun)         = RFun(inv(a.ex))
Base.:(==)(a::RFun, b::RFun) = a.ex == b.ex
is_zero(a::RFun)          = iszero(a.ex)

Base.:+(a::RFun, b::Integer) = RFun(a.ex + b)
Base.:+(a::Integer, b::RFun) = RFun(a + b.ex)
Base.:-(a::RFun, b::Integer) = RFun(a.ex - b)
Base.:-(a::Integer, b::RFun) = RFun(a - b.ex)
Base.:*(a::RFun, b::Integer) = RFun(a.ex * b)
Base.:*(a::Integer, b::RFun) = RFun(a * b.ex)

# Forwarding standard ring operations for Ft2
Base.:+(x::Ft2, y::Ft2) = Ft2(x.ex + y.ex)
Base.:-(x::Ft2, y::Ft2) = Ft2(x.ex - y.ex)
Base.:-(x::Ft2)         = Ft2(-x.ex)
Base.:*(x::Ft2, y::Ft2) = Ft2(x.ex * y.ex)
Base.:/(x::Ft2, y::Ft2) = Ft2(x.ex / y.ex)
Base.inv(x::Ft2)        = Ft2(inv(x.ex))
is_zero(x::Ft2)         = iszero(x.ex)

Base.:+(x::Ft2, y::RFun) = Ft2(x.ex + y.ex)
Base.:+(y::RFun, x::Ft2) = Ft2(y.ex + x.ex)
Base.:-(x::Ft2, y::RFun) = Ft2(x.ex - y.ex)
Base.:-(y::RFun, x::Ft2) = Ft2(y.ex - x.ex)
Base.:*(x::Ft2, y::RFun) = Ft2(x.ex * y.ex)
Base.:*(y::RFun, x::Ft2) = Ft2(y.ex * x.ex)

Base.:+(x::Ft2, n::Integer) = Ft2(x.ex + n)
Base.:+(n::Integer, x::Ft2) = Ft2(n + x.ex)
Base.:-(x::Ft2, n::Integer) = Ft2(x.ex - n)
Base.:*(x::Ft2, n::Integer) = Ft2(x.ex * n)
Base.:*(n::Integer, x::Ft2) = Ft2(n * x.ex)

# Native string representation mappings
pretty(a::RFun) = string(a.ex)
pretty(x::Ft2)  = string(x.ex)

# =============================================================================
#  PART 3: Riemann-Roch Basis Bookkeeping
# =============================================================================

function rr_basis(n_basis::Int)::Vector{NTuple{2,Int}}
    basis = NTuple{2,Int}[]
    max_order = 2 * n_basis + 10
    candidates = Tuple{Int,Int,Int}[]
    for i in 0:max_order÷2
        push!(candidates, (2i,   i, 0))
        push!(candidates, (2i+5, i, 1))
    end
    sort!(candidates, by=x->x[1])
    seen = 0
    for (_, i, j) in candidates
        seen += 1
        push!(basis, (i, j))
        seen == n_basis && break
    end
    return basis
end

# =============================================================================
#  PART 4: Schoolbook Gaussian Elimination Over OSCAR Field/Ring Elements
# =============================================================================

function gauss_solve(A::Matrix{T}, rhs::Vector{T}) where T
    n = length(rhs)
    @assert size(A) == (n, n)
    M = copy(A)
    b = copy(rhs)
    for col in 1:n
        piv = findfirst(r -> !iszero(M[r, col]), col:n)
        @assert piv !== nothing "gauss_solve: matrix is singular (no nonzero pivot in column $col)"
        piv += col - 1
        if piv != col
            M[col, :], M[piv, :] = M[piv, :], M[col, :]
            b[col], b[piv] = b[piv], b[col]
        end
        pinv = inv(M[col, col])
        for r in (col+1):n
            iszero(M[r, col]) && continue
            factor = M[r, col] * pinv
            for c in col:n
                M[r, c] = M[r, c] - factor * M[col, c]
            end
            b[r] = b[r] - factor * b[col]
        end
    end
    x = Vector{T}(undef, n)
    for row in n:-1:1
        acc = b[row]
        for c in (row+1):n
            acc = acc - M[row, c] * x[c]
        end
        x[row] = acc * inv(M[row, row])
    end
    return x
end

# =============================================================================
#  PART 5: The Construction Proper
# =============================================================================

struct SymbolicResidualResult
    K::Int
    u_RS::Vector{Ft2}
    v_RS::Vector{Ft2}
    deg_E::Int
    deg_Y::Int
    n_len_before_divide::Int
end

function symbolic_residual(K::Int, fixed_anchors, u0::Int, u1::Int, v0::Int, v1::Int,
                            F_POLY_ASC::Vector{Int}, p::Int)::SymbolicResidualResult
    @assert K >= 1
    @assert length(fixed_anchors) == K - 1 "symbolic_residual: need exactly K-1 fixed anchors"

    for i in 1:length(fixed_anchors), j in (i+1):length(fixed_anchors)
        if fixed_anchors[i] == fixed_anchors[j]
            throw(ArgumentError("symbolic_residual: fixed anchors coincide (m=2 not supported)"))
        end
    end

    nb = K + 3
    basis = rr_basis(nb)
    y_idx = findfirst(bi -> bi == (0,1), basis)
    @assert y_idx !== nothing "symbolic_residual: no y-monomial in RR basis"

    # --- Setup OSCAR Rings & Fields ---
    Fp = GF(p)
    K_field, t = rational_function_field(Fp, "t")
    Kt, w_poly = polynomial_ring(K_field, "w")

    f_t = zero(K_field)
    for (i, c) in enumerate(F_POLY_ASC)
        f_t += Fp(c) * t^(i-1)
    end

    # Unpack the 2-tuple (Ring, Map) returned by OSCAR's residue_ring
    Q, _ = residue_ring(Kt, w_poly^2 - f_t)
    w = Q(w_poly)
    t_Q = Q(Kt(t))

    n_unknowns = K + 2
    other_idx = [idx for idx in 1:nb if idx != y_idx]
    @assert length(other_idx) == n_unknowns

    A   = Matrix{elem_type(Q)}(undef, n_unknowns, n_unknowns)
    rhs = Vector{elem_type(Q)}(undef, n_unknowns)

    anchor_pts = Vector{Tuple{elem_type(Q), elem_type(Q)}}(undef, K)
    for a in 1:(K-1)
        px_raw, py_raw = fixed_anchors[a]
        anchor_pts[a] = (Q(px_raw), Q(py_raw))
    end
    anchor_pts[K] = (t_Q, w)

    # -- Rows 1..K: Anchor Equations --
    for a in 1:K
        px, py = anchor_pts[a]
        for (col, bidx) in enumerate(other_idx)
            bi, bj = basis[bidx]
            A[a, col] = px^bi * py^bj
        end
        bi_n, bj_n = basis[y_idx]
        rhs[a] = -(px^bi_n * py^bj_n)
    end

    # -- Rows K+1, K+2: Mumford conditions mod u(x) via native OSCAR rings --
    Fpx, x_Fp = polynomial_ring(Fp, "x")
    u_Fp = x_Fp^2 + Fp(u1)*x_Fp + Fp(u0)
    v_Fp = Fp(v1)*x_Fp + Fp(v0)

    row0 = K + 1
    row1 = K + 2
    for (col, bidx) in enumerate(other_idx)
        bi, bj = basis[bidx]
        poly_mon = x_Fp^bi * (bj == 1 ? v_Fp : one(Fpx))
        rem_poly = mod(poly_mon, u_Fp)
        A[row0, col] = Q(K_field(coeff(rem_poly, 0)))
        A[row1, col] = Q(K_field(coeff(rem_poly, 1)))
    end
    
    bi_n, bj_n = basis[y_idx]
    poly_mon_n = x_Fp^bi_n * (bj_n == 1 ? v_Fp : one(Fpx))
    rem_poly_n = mod(poly_mon_n, u_Fp)
    rhs[row0] = -Q(K_field(coeff(rem_poly_n, 0)))
    rhs[row1] = -Q(K_field(coeff(rem_poly_n, 1)))

    # -- Solve Matrix System --
    c = gauss_solve(A, rhs)

    coeffs_out = zeros(Q, nb)
    for (col, bidx) in enumerate(other_idx)
        coeffs_out[bidx] = c[col]
    end
    coeffs_out[y_idx] = one(Q)

    # -- Build E(x) and Y(x) over Q[x] --
    Rx, x_var = polynomial_ring(Q, "x")
    E_poly = zero(Rx)
    Y_poly = zero(Rx)
    for bidx in 1:nb
        bi, bj = basis[bidx]
        c_here = coeffs_out[bidx]
        if bj == 0
            E_poly += c_here * x_var^bi
        else
            Y_poly += c_here * x_var^bi
        end
    end

    deg_E = degree(E_poly) < 0 ? 0 : degree(E_poly)
    deg_Y = degree(Y_poly)

    # -- Construct N(x) = E(x)^2 - f(x)*Y(x)^2 --
    f_x = zero(Rx)
    for (i, coeff_val) in enumerate(F_POLY_ASC)
        f_x += Q(K_field(Fp(coeff_val))) * x_var^(i-1)
    end
    Nx = E_poly^2 - f_x * Y_poly^2
    n_len_before_divide = degree(Nx) + 1

    # -- Exact Polynomial Division of All Roots --
    cur = Nx
    for (px_raw, _) in fixed_anchors
        cur, remv = divrem(cur, x_var - Q(px_raw))
        @assert iszero(remv) "symbolic_residual: dividing out fixed anchor factor left remainder"
    end
    cur, remv = divrem(cur, x_var - t_Q)
    @assert iszero(remv) "symbolic_residual: dividing out symbolic anchor factor left remainder"

    u_poly = x_var^2 + Q(K_field(Fp(u1))) * x_var + Q(K_field(Fp(u0)))
    cur, remv = divrem(cur, u_poly)
    @assert iszero(remv) "symbolic_residual: dividing by u(x) left remainder"

    # Make monic
    lc = leading_coefficient(cur)
    if !isone(lc)
        cur = divexact(cur, lc)
    end
    u_RS_poly = cur

    # -- Compute v_RS(x) = -E(x) * Y(x)^-1 mod u_RS(x) via modular polynomial inversion --
    @assert !iszero(Y_poly) "symbolic_residual: Y(x) is identically zero"
    g, s, _ = gcdx(Y_poly, u_RS_poly)
    Y_inv_mod = s * inv(leading_coefficient(g))
    v_RS_poly = mod(-E_poly * Y_inv_mod, u_RS_poly)

    # Extract clean vectors of coefficients wrapped as Ft2 objects
    u_RS_coeffs = Ft2[Ft2(coeff(u_RS_poly, i)) for i in 0:max(0, degree(u_RS_poly))]
    v_RS_coeffs = Ft2[Ft2(coeff(v_RS_poly, i)) for i in 0:max(0, degree(v_RS_poly))]

    return SymbolicResidualResult(K, u_RS_coeffs, v_RS_coeffs, deg_E, deg_Y, n_len_before_divide)
end

function symbolic_residual_concrete(K::Int, fixed_anchors, u0::Int, u1::Int, v0::Int, v1::Int,
                                     F_POLY_ASC::Vector{Int}, p::Int, t0::Int, y0::Int)
    res = symbolic_residual(K, fixed_anchors, u0, u1, v0, v1, F_POLY_ASC, p)
    Fp = GF(p)

    eval_ft2(val::Ft2) = begin
        poly_rep = lift(val.ex)
        a_t = coeff(poly_rep, 0)
        b_t = coeff(poly_rep, 1)

        num_a = numerator(a_t)
        den_a = denominator(a_t)
        val_a = evaluate(num_a, Fp(t0)) / evaluate(den_a, Fp(t0))

        num_b = numerator(b_t)
        den_b = denominator(b_t)
        val_b = evaluate(num_b, Fp(t0)) / evaluate(den_b, Fp(t0))

        return Int(lift(ZZ, val_a + val_b * Fp(y0)))
    end

    u_concrete = [eval_ft2(c) for c in res.u_RS]
    v_concrete = [eval_ft2(c) for c in res.v_RS]

    return u_concrete, v_concrete
end

# =============================================================================
#  PART 6: Output Helpers
# =============================================================================

function print_symbolic_residual(res::SymbolicResidualResult; io::IO = stdout)
    println(io, "Symbolic Residual Result (K = $(res.K)):")
    println(io, "  deg_E = $(res.deg_E), deg_Y = $(res.deg_Y)")
    println(io, "  n_len_before_divide = $(res.n_len_before_divide)")
    println(io, "  u_RS(x; t):")
    for (i, c) in enumerate(res.u_RS)
        println(io, "    x^$(i-1): $(pretty(c))")
    end
    println(io, "  v_RS(x; t):")
    for (i, c) in enumerate(res.v_RS)
        println(io, "    x^$(i-1): $(pretty(c))")
    end
end

function print_symbolic_residual_concrete(K::Int, t_0::Int, y_0::Int,
                                           u_RS_concrete::Vector{Int}, v_RS_concrete::Vector{Int};
                                           io::IO=stdout)
    if K < 1
        throw(ArgumentError("K must be a positive integer, got $K"))
    end
    
    println(io, "=== Symbolic residual (concrete), K=$K, evaluated at (t_0,y_0)=($t_0,$y_0) ===")
    println(io, "u_RS(x)  [monic, deg $(length(u_RS_concrete)-1)]:  $u_RS_concrete")
    println(io, "v_RS(x)  [deg $(length(v_RS_concrete)-1)]:  $v_RS_concrete")
end

end # module
