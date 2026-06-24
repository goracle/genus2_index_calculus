# =============================================================================
#  trial3_phi_general.jl  --  Generalised φ-function for k-anchor walks.
#
#  Replaces the single-anchor quadratic φ in trial3_phi.jl with a family
#  parameterised by the number of anchor points k ≥ 1.
#
#  MATHEMATICAL BACKGROUND
#  -----------------------
#  The curve is C: y² = f(x),  f degree 5  (genus g=2).
#
#  The Riemann-Roch space L(n·∞) on a hyperelliptic curve of genus g has
#  a canonical monomial basis ordered by pole order at the points at
#  infinity.  For genus 2 the basis elements and their pole orders are:
#
#    Monomial   Pole order   Index
#    ---------  ----------   -----
#    1            0           1
#    x            2           2
#    x²           4           3
#    y            5           4    ← normalise coefficient to 1 (d=1)
#    x³           6           5
#    xy           7           6
#    x⁴           8           7
#    x²y          9           8
#    x⁵          10           9
#    x³y         11          10
#    ...
#
#  General pattern: xⁱ has pole order 2i; xⁱy has pole order 2i+5.
#  Interleaved in increasing order they give the sequence
#    2·0, 2·1, 2·2, 5, 2·3, 7, 2·4, 9, ...
#  which (after the leading 1) is  0, 2, 4, 5, 6, 7, 8, 9, 10, 11, …
#
#  For k anchor points + a degree-2 Mumford divisor D=[u(x),v(x)],
#  the total number of vanishing conditions is k+2.  We choose the
#  smallest Riemann-Roch basis B with |B| = k+3 elements (one extra
#  for normalization: we set the coefficient of the last/highest-pole
#  element to 1 and solve for the remaining k+2 coefficients).
#
#  Denote the chosen basis B = {m₁, …, m_{k+3}}, ordered by pole order.
#  Normalise: coefficient of m_{k+3} is 1.  Define the column vector
#  of unknowns  c = (c₁, …, c_{k+2})ᵀ  corresponding to {m₁,…,m_{k+2}}.
#
#  φ(x,y) = Σⱼ cⱼ mⱼ(x,y)  +  m_{k+3}(x,y)
#
#  Vanishing conditions (k+2 equations):
#
#    (A)  k anchor equations:  for each anchor Pᵢ = (pxᵢ, pyᵢ):
#           Σⱼ cⱼ mⱼ(pxᵢ, pyᵢ)  =  -m_{k+3}(pxᵢ, pyᵢ)
#
#    (B)  2 Mumford equations:  φ(x, v(x)) ≡ 0 mod u(x)
#         Since deg u = 2, this means the const and x-coefficient of
#         φ(x, v(x)) mod u(x) are both zero.  For each basis monomial mⱼ,
#         define   rⱼ = (r0ⱼ, r1ⱼ)  = (mⱼ(x,v(x)) mod u(x)) as a linear poly.
#         The two equations become:
#           Σⱼ cⱼ r0ⱼ  =  -r0_{k+3}
#           Σⱼ cⱼ r1ⱼ  =  -r1_{k+3}
#
#  This gives a (k+2) × (k+2) linear system over F_p, solved by Gaussian
#  elimination.
#
#  RESIDUAL INTERSECTION
#  ---------------------
#  Split φ(x,y) = E(x) + y·Y(x) into its x-only and y·(x-only) parts.
#  Then
#       φ(x,y)·φ(x,-y) = E(x)² - f(x)·Y(x)² =: N(x)
#  is a polynomial in x of degree  deg(N) = max(2·deg(E), 5+2·deg(Y)).
#
#  The known zeros of N are:
#    • each anchor xᵢ (simple zero, since P₀ is not in supp D by design)
#    • the roots of u(x) = x²+u1·x+u0  (degree 2)
#  Dividing N by  (Π (x-pxᵢ)) · u(x)  gives the residual polynomial
#  u_RS(x) whose roots are the residual intersection points.
#
#  For k=1 (current code): deg(E)=2, deg(Y)=0, deg(N)=5; known zeros:
#  (x-px1)·u(x) degree 3 → residual u_RS degree 2. ✓
#
#  For k anchors: deg(N) grows with the basis; we always divide out
#  k+2 known zeros to get a residual of degree deg(N)-(k+2).
#  The residual is a monic polynomial over F_p; we try to split it.
#
#  SCOPE: The linear solver is general for any k and any multiplicity pattern.
#  Tangency of order m at a point P requires m conditions (Taylor coefficients
#  of φ along the curve branch at P, orders 0..m-1), computed via branch series
#  expansion.  Requires p > max multiplicity used.
# =============================================================================

# ---------------------------------------------------------------------------
#  Riemann-Roch basis enumeration
#
#  Returns a vector of (i, j) pairs meaning x^i * y^j (j ∈ {0,1}),
#  in increasing pole-order, of length n_basis.
#
#  Pole order: (i, 0) → 2i;   (i, 1) → 2i+5.
# ---------------------------------------------------------------------------
function rr_basis(n_basis::Int)::Vector{NTuple{2,Int}}
    basis = NTuple{2,Int}[]
    # Enumerate in order of pole order.  Max pole order we need:
    # interleaved x^i (order 2i) and x^i*y (order 2i+5), starting from i=0.
    # Orders: 0(x⁰), 2(x¹), 4(x²), 5(y), 6(x³), 7(xy), 8(x⁴), 9(x²y), ...
    # After the first four (i=0,1,2 pure-x and i=0 y-term), each consecutive
    # pair has pole orders 2k and 2k+5 interleaved.  We just stream pairs
    # (i,0) and (i-3,1) by walking pole order ≤ max_order.
    max_order = 2 * n_basis + 10   # generous upper bound
    candidates = Tuple{Int,Int,Int}[]  # (pole_order, i, j)
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

# ---------------------------------------------------------------------------
#  Evaluate a monomial x^i * y^j at an affine point (px, py).
# ---------------------------------------------------------------------------
@inline function eval_monomial(i::Int, j::Int, px::Int, py::Int)::Int
    xi = i == 0 ? 1 : begin
        r = px
        for _ in 2:i; r = fpmul(r, px); end
        r
    end
    j == 0 && return fp(xi)
    return fpmul(xi, py)
end

# ---------------------------------------------------------------------------
#  Reduce x^i * v(x) mod u(x) = x² + u1*x + u0
#  Returns (r0, r1) = const + r1*x  (the linear remainder).
#
#  We work with the full polynomial x^i * v(x) reduced mod u(x).
#  v(x) = v0 + v1*x is degree 1, so x^i*v(x) is degree i+1.
#  We reduce the degree-i+1 poly mod u(x) iteratively.
# ---------------------------------------------------------------------------
function reduce_xiv_mod_u(i::Int, v0::Int, v1::Int,
                           u0::Int, u1::Int)::NTuple{2,Int}
    # Build coefficients of x^i * v(x):  coeff[k] = coeff of x^k
    # x^i * (v0 + v1*x) = v0*x^i + v1*x^(i+1)
    # Represent as vector indexed 0..i+1
    deg = i + 1
    coeffs = zeros(Int, deg + 1)  # 1-indexed: coeffs[k+1] = coeff of x^k
    coeffs[i+1]   = fp(v0)        # x^i coefficient
    coeffs[i+2]   = fp(v1)        # x^(i+1) coefficient
    # Reduce mod u(x) = x^2 + u1*x + u0, i.e. x^2 ≡ -u1*x - u0
    for d in deg:-1:2
        if coeffs[d+1] != 0
            c = coeffs[d+1]
            coeffs[d+1] = 0
            coeffs[d]   = fp(coeffs[d]   - fpmul(c, u1))
            coeffs[d-1] = fp(coeffs[d-1] - fpmul(c, u0))
        end
    end
    return (coeffs[1], coeffs[2])
end

# ---------------------------------------------------------------------------
#  Reduce x^i mod u(x) → (r0, r1).
# ---------------------------------------------------------------------------
function reduce_xi_mod_u(i::Int, u0::Int, u1::Int)::NTuple{2,Int}
    if i == 0; return (1, 0); end
    if i == 1; return (0, 1); end
    # Build coefficient vector of x^i
    deg = i
    coeffs = zeros(Int, deg + 1)
    coeffs[deg+1] = 1
    for d in deg:-1:2
        if coeffs[d+1] != 0
            c = coeffs[d+1]
            coeffs[d+1] = 0
            coeffs[d]   = fp(coeffs[d]   - fpmul(c, u1))
            coeffs[d-1] = fp(coeffs[d-1] - fpmul(c, u0))
        end
    end
    return (coeffs[1], coeffs[2])
end

# ---------------------------------------------------------------------------
#  Reduce monomial x^i * y^j mod the divisor D = [u(x), v(x)].
#  On the curve y = v(x) mod u(x), so x^i*y^j → x^i * v(x)^j mod u(x).
#  j ∈ {0,1} for the monomials we use.
#  Returns (r0, r1): the linear remainder a0 + a1*x.
# ---------------------------------------------------------------------------
@inline function reduce_monomial_mod_D(i::Int, j::Int,
                                        u0::Int, u1::Int,
                                        v0::Int, v1::Int)::NTuple{2,Int}
    if j == 0
        return reduce_xi_mod_u(i, u0, u1)
    else
        return reduce_xiv_mod_u(i, v0, v1, u0, u1)
    end
end

# ---------------------------------------------------------------------------
#  Gaussian elimination over F_p.
#
#  Solves A * x = b where A is (n×n), b is (n,), all entries are Ints in F_p.
#  Returns solution vector or nothing if singular.
#
#  Mutates A and b in place.
# ---------------------------------------------------------------------------
function fp_gauss!(A::Matrix{Int}, b::Vector{Int})::Union{Vector{Int}, Nothing}
    n = size(A, 1)
    for col in 1:n
        # Find pivot
        pivot_row = 0
        for row in col:n
            if A[row, col] != 0
                pivot_row = row
                break
            end
        end
        pivot_row == 0 && return nothing   # singular

        if pivot_row != col
            A[col, :], A[pivot_row, :] = A[pivot_row, :], A[col, :]
            b[col], b[pivot_row] = b[pivot_row], b[col]
        end

        inv_pivot = fpinv(A[col, col])
        for j in col:n
            A[col, j] = fpmul(A[col, j], inv_pivot)
        end
        b[col] = fpmul(b[col], inv_pivot)

        for row in 1:n
            row == col && continue
            if A[row, col] != 0
                factor = A[row, col]
                for j in col:n
                    A[row, j] = fp(A[row, j] - fpmul(factor, A[col, j]))
                end
                b[row] = fp(b[row] - fpmul(factor, b[col]))
            end
        end
    end
    return b
end

# ---------------------------------------------------------------------------
#  build_phi_general
#
#  Given k anchor points `anchors` and a degree-2 Mumford divisor (u0,u1,v0,v1),
#  returns the coefficient vector `coeffs` of length k+3 in the Riemann-Roch
#  basis returned by rr_basis(k+3), with coeffs[end] = 1 (normalisation).
#
#  φ(x,y) = Σᵢ coeffs[i] * mᵢ(x,y)
#
#  Returns nothing if:
#    • any anchor is in supp(D)  (u(px) = 0)
#    • the linear system is singular
#
#  PERFORMANCE NOTE: Allocates a (k+2)×(k+2) matrix.  For the k=1 hot path,
#  use build_phi_mumford (the inlined closed-form solution) directly.
# ---------------------------------------------------------------------------
function build_phi_general(
        anchors ::Vector{NTuple{2,Int}},   # [(px1,py1), (px2,py2), ...]
        u0::Int, u1::Int,
        v0::Int, v1::Int
    )::Union{Vector{Int}, Nothing}

    k    = length(anchors)
    n    = k + 2          # number of unknowns (= number of equations)
    nb   = k + 3          # total basis size (including the normalised element)

    basis = rr_basis(nb)

    # Guard: no anchor may be in supp(D)
    for (px, _) in anchors
        upx = fp(fp(px * px) + fpmul(u1, px) + u0)
        upx == 0 && return nothing
    end

    # Compute multiplicity-grouped anchor list.
    # For each distinct anchor point, count how many times it appears.
    # A point of multiplicity m contributes m vanishing conditions:
    #   (d/dx)^s [φ(x, y(x))]|_P = 0   for s = 0, 1, ..., m-1
    # where d/dx is the intrinsic derivative along the curve branch.
    #
    # We compute these by truncated Taylor expansion: for each monomial
    # x^i * y^j, we expand it as a power series in t = x - px using the
    # branch y(x) = Σ y_s * t^s determined by the curve equation
    # y² = f(x), initialised at (px, py).
    #
    # The s-th coefficient of the Taylor expansion of monomial m at P
    # is exactly (1/s!) * (d/dx)^s m(x,y(x))|_{x=px}.
    # We use the *unnormalised* coefficients (i.e. the coefficients of t^s
    # in the series), which scale each row by s! relative to the true
    # derivative — but since each condition is just "= 0", the scaling
    # is irrelevant and we avoid working in characteristic-0.
    #
    # NOTE: if p ≤ m-1, some factorial s! = 0 mod p, making the scaling
    # degenerate.  Guard: raise an error if p < m (extremely rare in practice).

    # Build ordered list of (px, py, multiplicity) in first-occurrence order.
    seen_counts = Dict{NTuple{2,Int},Int}()
    for pt in anchors
        seen_counts[pt] = get(seen_counts, pt, 0) + 1
    end
    point_orders = NTuple{3,Int}[]   # (px, py, multiplicity)
    visited = Set{NTuple{2,Int}}()
    for pt in anchors
        pt ∈ visited && continue
        push!(visited, pt)
        push!(point_orders, (pt[1], pt[2], seen_counts[pt]))
    end

    # Total vanishing conditions = sum of multiplicities = k
    n_cond = sum(m for (_, _, m) in point_orders)
    @assert n_cond == k

    # Guard: characteristic p must exceed max multiplicity so that
    # the Taylor-coefficient approach (scaling by 1/s!) is valid.
    max_mult = maximum(m for (_, _, m) in point_orders)
    max_mult >= p && throw(ArgumentError(
        "anchor multiplicity $max_mult ≥ p=$p: Taylor-coefficient rows degenerate mod p"))

    # Guard: tangency (mult ≥ 2) requires py ≠ 0.
    for (px, py, m) in point_orders
        m >= 2 && py == 0 && return nothing
    end

    # ---------------------------------------------------------------------------
    #  Branch series: compute y-series coefficients y[0], y[1], ..., y[m-1]
    #  where y(px + t) = Σ y[s] * t^s mod t^m,
    #  determined by y² = f(px + t)  with y[0] = py.
    #
    #  Expanding f(px + t) = Σ f_s * t^s (Taylor coefficients of f at px):
    #    f_s = f^(s)(px) / s!  — but we work with the *actual* Taylor coeffs
    #    (including the 1/s! denominator), which requires computing them mod p.
    #
    #  From y² = f we get: 2*y[0]*y[s] = f_s - Σ_{r=1}^{s-1} y[r]*y[s-r]
    #  → y[s] = (f_s - Σ_{r=1}^{s-1} y[r]*y[s-r]) / (2*y[0])
    #
    #  f_s = (1/s!) f^(s)(px):  we compute iteratively.
    # ---------------------------------------------------------------------------
    function branch_series(px::Int, py::Int, m::Int)::Vector{Int}
        # Taylor coefficients of f at px up to order m-1.
        # f_s: coefficient of t^s in f(px+t), i.e. f^(s)(px)/s!.
        # We compute these by repeated division (synthetic differentiation).
        # Represent f in descending order for Horner; F_POLY is ascending.
        f_desc = reverse(F_POLY)   # descending coefficients
        f_tay  = zeros(Int, m)     # f_tay[s+1] = coefficient of t^s
        # Iterated Horner: divide f(x) by (x - px) repeatedly.
        # The remainders give the Taylor coefficients.
        poly = copy(f_desc)        # working copy, descending
        for s in 0:m-1
            # Evaluate poly at px (Horner) → f_tay[s+1]
            val = poly[1]
            for ci in poly[2:end]
                val = fp(fpmul(val, px) + ci)
            end
            f_tay[s+1] = val
            # Deflate: poly ← poly / (x - px) — quotient only (drop remainder)
            if s < m-1
                n_poly = length(poly)
                q = zeros(Int, n_poly - 1)
                q[1] = poly[1]
                for ci in 2:n_poly-1
                    q[ci] = fp(fpmul(q[ci-1], px) + poly[ci])
                end
                poly = q
            end
        end
        # However, the above computes f(px), f'(px), f''(px), ... (not divided by s!).
        # We need f_tay[s+1] = f^(s)(px) / s!.  Divide by s!:
        fact = 1
        for s in 1:m-1
            fact = fp(fpmul(fact, fp(s)))
            fact == 0 && throw(ArgumentError(
                "s! = 0 mod p for s=$s, p=$p: characteristic too small for order-$m tangency"))
            f_tay[s+1] = fpmul(f_tay[s+1], fpinv(fact))
        end

        # Now compute y-series: y[s] for s = 0 .. m-1.
        y = zeros(Int, m)
        y[1] = py   # y[0]
        inv2y0 = fpinv(fp(2 * py))
        for s in 1:m-1
            # 2*y0*y[s] = f_s - Σ_{r=1}^{s-1} y[r]*y[s-r]
            rhs_s = f_tay[s+1]
            for r in 1:s-1
                rhs_s = fp(rhs_s - fpmul(y[r+1], y[s-r+1]))
            end
            y[s+1] = fpmul(rhs_s, inv2y0)
        end
        return y   # y[s+1] = coefficient of t^s in y(px+t)
    end

    # ---------------------------------------------------------------------------
    #  Monomial series: compute the coefficient of t^s in x^i * y^j(x)
    #  evaluated at x = px + t, y = Σ y[r] t^r.
    #
    #  x^i = (px + t)^i = Σ C(i,r) * px^(i-r) * t^r  (binomial expansion)
    #  x^i * y^j: convolve the two series mod t^m.
    #
    #  For j=0: coeff of t^s in (px+t)^i = C(i,s) * px^(i-s)  (or 0 if s>i).
    #  For j=1: convolve x-series with y-series.
    # ---------------------------------------------------------------------------
    function monomial_series_coeffs(i::Int, j::Int,
                                     px::Int, y_ser::Vector{Int},
                                     m::Int)::Vector{Int}
        # Coefficients of t^0..t^(m-1) in x^i (as a series in t = x-px).
        # C(i, s) * px^(i-s), for s = 0..min(i,m-1); zero for s > i.
        xi_ser = zeros(Int, m)
        # Compute binomial coefficients C(i,0), C(i,1), ..., C(i,m-1) mod p.
        binom = zeros(Int, m)
        binom[1] = 1   # C(i,0) = 1
        for s in 1:min(i, m-1)
            # C(i,s) = C(i,s-1) * (i-s+1) / s
            binom[s+1] = fpmul(binom[s], fpmul(fp(i - s + 1), fpinv(fp(s))))
        end
        # px^(i-s) for s = 0..i; use descending powers.
        px_pow = zeros(Int, m)   # px_pow[s+1] = px^(i-s) for s ≤ i
        for s in 0:min(i, m-1)
            e = i - s
            if e == 0
                px_pow[s+1] = 1
            elseif e == 1
                px_pow[s+1] = px
            else
                t2 = px
                for _ in 2:e; t2 = fpmul(t2, px); end
                px_pow[s+1] = t2
            end
        end
        for s in 0:min(i, m-1)
            xi_ser[s+1] = fpmul(binom[s+1], px_pow[s+1])
        end

        j == 0 && return xi_ser

        # j == 1: convolve xi_ser with y_ser mod t^m.
        result = zeros(Int, m)
        for a in 0:m-1, b in 0:m-1
            a + b >= m && continue
            result[a+b+1] = fp(result[a+b+1] + fpmul(xi_ser[a+1], y_ser[b+1]))
        end
        return result
    end

    # Build linear system A * c = rhs
    A   = zeros(Int, n, n)
    rhs = zeros(Int, n)

    # Normalised monomial index
    i_norm, j_norm = basis[nb]

    row_idx = 0
    for (px, py, m) in point_orders
        # Compute branch series y(px+t) to order m-1.
        y_ser = branch_series(px, py, m)

        # Compute Taylor series of each basis monomial to order m-1.
        # basis_ser[col_idx][s+1] = coefficient of t^s.
        basis_sers = Vector{Vector{Int}}(undef, n)
        for col_idx in 1:n
            ii, jj = basis[col_idx]
            basis_sers[col_idx] = monomial_series_coeffs(ii, jj, px, y_ser, m)
        end
        norm_ser = monomial_series_coeffs(i_norm, j_norm, px, y_ser, m)

        # Emit m rows: one for each order s = 0, 1, ..., m-1.
        for s in 0:m-1
            row_idx += 1
            for col_idx in 1:n
                A[row_idx, col_idx] = basis_sers[col_idx][s+1]
            end
            rhs[row_idx] = fp(-norm_ser[s+1])
        end
    end

    # --- Mumford rows: const (row k+1) and x-coeff (row k+2) ---
    for col_idx in 1:n
        i, j = basis[col_idx]
        r0, r1 = reduce_monomial_mod_D(i, j, u0, u1, v0, v1)
        A[k+1, col_idx] = r0
        A[k+2, col_idx] = r1
    end
    # RHS: -remainder of normalised monomial
    rn0, rn1 = reduce_monomial_mod_D(i_norm, j_norm, u0, u1, v0, v1)
    rhs[k+1] = fp(-rn0)
    rhs[k+2] = fp(-rn1)

    sol = fp_gauss!(A, rhs)
    sol === nothing && return nothing

    # Append the normalised coefficient
    result = Vector{Int}(undef, nb)
    result[1:n] .= sol
    result[nb]   = 1
    return result
end

# ---------------------------------------------------------------------------
#  phi_eval(coeffs, basis, px, py) — evaluate φ at (px, py).
# ---------------------------------------------------------------------------
@inline function phi_eval(coeffs::Vector{Int},
                           basis ::Vector{NTuple{2,Int}},
                           px::Int, py::Int)::Int
    s = 0
    for (k, (i, j)) in enumerate(basis)
        s = fp(s + fpmul(coeffs[k], eval_monomial(i, j, px, py)))
    end
    return s
end

# ---------------------------------------------------------------------------
#  phi_to_EY(coeffs, basis) — split φ = E(x) + y*Y(x).
#
#  Returns:
#    E_coeffs : Vector{Int}  (ascending powers of x, length = deg(E)+1)
#    Y_coeffs : Vector{Int}  (ascending powers of x, length = deg(Y)+1)
#
#  Sizes depend on the basis:  if the highest pure-x monomial is x^d_E
#  then deg(E) = d_E; if the highest y-monomial is x^d_Y * y then deg(Y) = d_Y.
# ---------------------------------------------------------------------------
function phi_to_EY(coeffs::Vector{Int},
                   basis ::Vector{NTuple{2,Int}})::Tuple{Vector{Int}, Vector{Int}}
    max_E_deg = maximum(i for (i,j) in basis if j==0; init=0)
    max_Y_deg = maximum(i for (i,j) in basis if j==1; init=-1)

    E = zeros(Int, max_E_deg + 1)    # E[k+1] = coeff of x^k
    Y = zeros(Int, max(max_Y_deg + 1, 1))

    for (idx, (i, j)) in enumerate(basis)
        c = coeffs[idx]
        c == 0 && continue
        if j == 0
            E[i+1] = fp(E[i+1] + c)
        else
            Y[i+1] = fp(Y[i+1] + c)
        end
    end
    return E, Y
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
#  build_N(E, Y) — compute N(x) = E(x)² - f(x)·Y(x)²
#
#  f(x) = Σ F_POLY[i] * x^(i-1)  (1-indexed), degree 5.
# ---------------------------------------------------------------------------
function build_N(E::Vector{Int}, Y::Vector{Int})::Vector{Int}
    E2 = poly_sq(E)
    Y2 = poly_sq(Y)
    f  = F_POLY                           # already a Vector{Int}, length 6
    fY2 = poly_mul(f, Y2)
    # Subtract: N = E² - f*Y²
    len = max(length(E2), length(fY2))
    N   = zeros(Int, len)
    for i in 1:length(E2);  N[i] = fp(N[i] + E2[i]);  end
    for i in 1:length(fY2); N[i] = fp(N[i] - fY2[i]); end
    # Strip trailing zeros
    while length(N) > 1 && N[end] == 0; pop!(N); end
    return N
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
#  poly_divmod_monic_deg2(N, u1, u0) — divide N by u(x) = x²+u1*x+u0.
#  Returns (quotient ascending, rem0, rem1).
# ---------------------------------------------------------------------------
function poly_divmod_monic_deg2(N::Vector{Int},
                                 u1::Int, u0::Int)::Tuple{Vector{Int}, Int, Int}
    deg_N = length(N) - 1
    @assert deg_N >= 2 "polynomial degree too low for deg-2 division"
    q = copy(N)                    # will shrink to quotient
    # Standard long division descending; q[end] is leading coeff.
    for i in length(q):-1:3
        c = q[i]
        c == 0 && continue
        q[i]   = 0
        q[i-1] = fp(q[i-1] - fpmul(c, u1))
        q[i-2] = fp(q[i-2] - fpmul(c, u0))
    end
    r0 = q[1]; r1 = q[2]
    quotient = q[3:end]
    # Reverse to get ascending coefficients
    return (quotient, r0, r1)
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
const RESIDUAL_FAIL = Int[-1]

function phi_residual_general(
        coeffs  ::Vector{Int},
        basis   ::Vector{NTuple{2,Int}},
        anchors ::Vector{NTuple{2,Int}},   # [(px1,py1), ...] — may contain repeats
        u0::Int, u1::Int
    )::Tuple{Vector{NTuple{2,Int}}, Vector{Int}, Vector{Int}}

    k = length(anchors)

    E, Y = phi_to_EY(coeffs, basis)

    # N(x) = E(x)² - f(x)·Y(x)²
    N = build_N(E, Y)

    # Divide out anchor factors with correct multiplicity.
    # For a point appearing m times in `anchors`, the factor (x - px) divides N
    # with multiplicity m (φ vanishes to order m at that point on C, so N = φ·φ̄
    # acquires (x-px)^m from φ alone).
    px_counts = Dict{Int,Int}()
    for (px, _) in anchors
        px_counts[px] = get(px_counts, px, 0) + 1
    end
    for (px, cnt) in px_counts
        for _ in 1:cnt
            q, rem = poly_divmod_linear(N, px)
            if rem != 0
                return (NTuple{2,Int}[], RESIDUAL_FAIL, Int[])
            end
            N = q
        end
    end

    # Divide out u(x) = x² + u1·x + u0
    q, r0, r1 = poly_divmod_monic_deg2(N, u1, u0)
    if r0 != 0 || r1 != 0
        return (NTuple{2,Int}[], RESIDUAL_FAIL, Int[])
    end
    N = q   # residual polynomial; should be monic of degree deg(N_original) - k - 2

    # Make monic
    if !isempty(N) && N[end] != 0 && N[end] != 1
        inv_lc = fpinv(N[end])
        N = [fpmul(c, inv_lc) for c in N]
    end

    deg_RS = length(N) - 1   # degree of residual (= 2 for k=1, 3 for k=2, etc.)

    # Compute v_RS(x): on the residual points, v_RS = -E(x)/Y(x) mod u_RS(x).
    # More carefully: φ(x,y) = E(x) + y*Y(x) = 0 → y = -E(x)/Y(x).
    # We compute  v_RS(x) = -E(x) * Y_inv(x) mod N(x),  where Y_inv is the
    # modular inverse of Y(x) mod N(x).  For now this is left as a helper.
    # For k=1 the original code computed v_RS explicitly; here we provide
    # the polynomial form.
    v_RS = compute_vRS(E, Y, N)   # defined below

    # Try to find affine points from the residual
    roots = find_roots_and_points(N, E, Y)

    return (roots, N, v_RS)
end

# ---------------------------------------------------------------------------
#  compute_vRS(E, Y, u_RS) — compute v_RS(x) = -E(x) mod u_RS(x) / Y(x).
#
#  On the residual divisor defined by u_RS(x), each root xᵢ satisfies
#  E(xᵢ) + yᵢ * Y(xᵢ) = 0  →  yᵢ = -E(xᵢ)/Y(xᵢ).
#  As a polynomial:  v_RS(x) = -E(x) * (Y(x))⁻¹ mod u_RS(x).
#
#  If Y(x) = 0 (e.g. no y-monomials in φ), v_RS(x) = 0 trivially.
#  Returns ascending coefficients, degree < deg(u_RS).
# ---------------------------------------------------------------------------
function compute_vRS(E::Vector{Int}, Y::Vector{Int},
                     u_RS::Vector{Int})::Vector{Int}
    n = length(u_RS) - 1   # degree of u_RS
    n == 0 && return Int[]

    # -E mod u_RS
    negE_mod = poly_reduce_mod(map(x -> fp(-x), E), u_RS)

    # Check if Y is the zero polynomial
    all(==(0), Y) && return negE_mod

    # Compute Y_inv mod u_RS via extended GCD
    Y_mod = poly_reduce_mod(Y, u_RS)
    Y_inv, ok = poly_modinv(Y_mod, u_RS)
    ok || return zeros(Int, n)   # Y not invertible mod u_RS — degenerate case

    v_RS = poly_mul_mod(negE_mod, Y_inv, u_RS)
    return v_RS
end

# Reduce polynomial a mod polynomial m (both ascending coefficients).
function poly_reduce_mod(a::Vector{Int}, m::Vector{Int})::Vector{Int}
    r = copy(a)
    dm = length(m) - 1
    while length(r) - 1 >= dm && (length(r) > 1 || r[1] != 0)
        deg_r = length(r) - 1
        if r[end] == 0; pop!(r); continue; end
        # Leading coeff of r divided by leading coeff of m (monic)
        c = r[end]
        shift = deg_r - dm
        for i in 1:length(m)
            idx = i + shift
            r[idx] = fp(r[idx] - fpmul(c, m[i]))
        end
        while length(r) > 1 && r[end] == 0; pop!(r); end
    end
    return r
end

# Multiply two polynomials mod m.
function poly_mul_mod(a::Vector{Int}, b::Vector{Int},
                       m::Vector{Int})::Vector{Int}
    return poly_reduce_mod(poly_mul(a, b), m)
end

# Extended GCD for polynomials over F_p (ascending coefficients).
# Returns (inverse of a mod b, true) or ([], false) if not invertible.
function poly_modinv(a::Vector{Int}, b::Vector{Int})::Tuple{Vector{Int}, Bool}
    # Extended Euclidean algorithm
    r0, r1 = copy(b), copy(a)
    s0, s1 = Int[0], Int[1]
    while !(length(r1) == 1 && r1[1] == 0)
        # q, r = divmod(r0, r1)
        q, r = poly_divmod_poly(r0, r1)
        r0, r1 = r1, r
        s_new = poly_sub(s0, poly_mul(q, s1))
        s0, s1 = s1, s_new
    end
    # r0 = gcd; must be constant for invertibility
    length(r0) == 1 || return (Int[], false)
    r0[1] == 0 && return (Int[], false)
    inv_lc = fpinv(r0[1])
    inv_a = [fpmul(c, inv_lc) for c in s0]
    inv_a = poly_reduce_mod(inv_a, b)
    return (inv_a, true)
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
#  find_roots_and_points — extract affine points from the residual polynomial.
#
#  Tries all x in F_p only for small residuals (deg ≤ 4).  For production
#  use the caller would do factor-base lookup instead.  Here we compute
#  y from φ(x,y)=0 directly:  y = -E(x)/Y(x).
# ---------------------------------------------------------------------------
function find_roots_and_points(u_RS::Vector{Int},
                                E   ::Vector{Int},
                                Y   ::Vector{Int})::Vector{NTuple{2,Int}}
    deg = length(u_RS) - 1
    points = NTuple{2,Int}[]

    if deg == 2
        # Quadratic: try discriminant sqrt (same as original code)
        c0, c1 = u_RS[1], u_RS[2]   # u_RS = x² + c1*x + c0 (monic)
        disc = fp(fpmul(c1, c1) - 4*c0)
        sq   = sqrt_fp(disc)
        sq === nothing && return points
        inv2 = fpinv(2)
        xR   = fpmul(fp(-c1 + sq), inv2)
        xS   = fpmul(fp(-c1 - sq), inv2)
        for xr in (xR, xS)
            yr = recover_y_from_phi(E, Y, xr)
            yr === nothing && continue
            push!(points, (xr, yr))
        end
        return points
    end

    # For deg 3 or 4: scan for rational roots then deflate
    # (Acceptable for precomputation; hot-path callers will use pt2idx lookup instead)
    remaining = copy(u_RS)
    for x in 0:p-1
        length(remaining) <= 1 && break
        val = poly_eval_fp(remaining, x)
        if val == 0
            q, _ = poly_divmod_linear(remaining, x)
            remaining = q
            yr = recover_y_from_phi(E, Y, x)
            yr !== nothing && push!(points, (x, yr))
        end
    end
    return points
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

# ---------------------------------------------------------------------------
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
    sq   = sqrt_fp(disc)

    if sq === nothing
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
#  High-level API for multi-anchor walks
#
#  step_phi_k(anchors, D_mumford) → (coeffs, basis, roots, u_RS, v_RS)
#
#  Entry point for a walk step with k anchors.  `anchors` is a length-k
#  vector of (px,py) points — repeated entries encode higher vanishing order:
#    k=1, unique point           → single zero (classic)
#    k=2, two distinct pts       → two simple zeros
#    k=2, same point twice       → order-2 tangency at P
#    k=n, same point n times     → order-n tangency at P (conditions s=0..n-1)
#    k=3, {P,P,Q}                → order-2 tangency at P, simple zero at Q
#    k=m+r, {P×m, Q1, …, Qr}    → order-m tangency at P, r simple zeros
#  etc.  Any multiplicity m ≥ 2 at a Weierstrass point (py=0) is degenerate
#  and returns nothing.  Requires p > max multiplicity (characteristic guard).
#
#  Returns nothing if φ cannot be constructed (singular system, anchor in supp D,
#  or degenerate tangency).
#
#  `roots` contains the split residual affine points (may be empty if u_RS has
#  no F_p roots).  The Mumford pair (u_RS, v_RS) is always returned for
#  conjugate-pair handling.
# ---------------------------------------------------------------------------
function step_phi_k(
        anchors       ::Vector{NTuple{2,Int}},
        u0::Int, u1::Int, v0::Int, v1::Int
    )::Union{
        Tuple{Vector{Int}, Vector{NTuple{2,Int}}, Vector{NTuple{2,Int}}, Vector{Int}, Vector{Int}},
        Nothing}

    coeffs = build_phi_general(anchors, u0, u1, v0, v1)
    coeffs === nothing && return nothing

    k     = length(anchors)
    nb    = k + 3
    basis = rr_basis(nb)

    roots, u_RS, v_RS = phi_residual_general(coeffs, basis, anchors, u0, u1)
    u_RS === RESIDUAL_FAIL && return nothing

    return (coeffs, basis, roots, u_RS, v_RS)
end
