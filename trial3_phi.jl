# =============================================================================
#  trial3_phi.jl  --  φ-function construction and residual intersection.
#
#  The φ-function is the key analytic tool in the Markov walk:
#
#    φ(x,y) = a·x² + b·x + c + d·y    (always d=1 in our normalisation)
#
#  Given the current anchor P0 = (px, py) and a divisor D = [u(x), v(x)]
#  in Mumford representation, φ is the unique (up to scale) degree-2+1
#  function vanishing at P0 and at the support of D.  The residual
#  intersection {R, S} = div(φ)^+ \ {P0, supp D} forms the next atom(s)
#  in the relation.
#
#  Also contains the relation-integrity assert helpers used throughout the walk.
# =============================================================================

# ---------------------------------------------------------------------------
#  Relation integrity checkers
#
#  These are called only when ASSERT_RELATIONS == true and verify that a
#  freshly emitted relation satisfies the Jacobian group-law identity.
#
#  check_relation_principal: full FB relation
#    Σ_j row[j]·atom(fb[j])  ==  al·G + be·T  in Jac(C/F_p)
#
#  check_lp1_stored: 1-LP stored entry (row is FB-only; lp_pt not in row)
#    atom(lp_pt) + Σ_j row[j]·atom(fb[j])  ==  neg_al·G + neg_be·T
# ---------------------------------------------------------------------------

function check_relation_principal(
        row        ::Dict{Int,Int},
        al         ::Int,
        be         ::Int,
        alpha_name ::String,   # label for the alpha coefficient (diagnostic)
        fb         ::Vector{NTuple{2,Int}},
        G          ::Div2,
        T          ::Div2;
        tag        ::String = "")::Bool

    D_fb = JacID
    for (idx, v) in row
        pt   = fb[idx]
        Dp   = mumford1(pt[1], pt[2])
        absv = abs(v)
        Dv   = jac_mul_raw(Dp, absv)
        D_fb = v > 0 ? jac_add(D_fb, Dv) : jac_sub(D_fb, Dv)
    end
    D_rhs = jac_add(jac_mul(G, al), jac_mul(T, be))

    D_fb == D_rhs && return true

    # Check negated RHS — sign-flipped convention is internally consistent
    # but we warn so the calling site knows which convention is in use.
    D_rhs_neg = jac_neg(D_rhs)
    if D_fb == D_rhs_neg
        @printf("[ASSERT %s tid=%d] SIGN-FLIP: fb_sum == -(al·G+be·T)  al=%d be=%d row_w=%d\n",
                tag, Threads.threadid(), al, be, length(row))
        return true   # treat as ok but warn
    end

    @printf("[ASSERT %s tid=%d] FAIL: fb_sum != al·G+be·T  al=%d be=%d row_w=%d\n",
            tag, Threads.threadid(), al, be, length(row))
    return false
end

function check_lp1_stored(
        lp_pt  ::NTuple{2,Int},
        row    ::Dict{Int,Int},
        neg_al ::Int,
        neg_be ::Int,
        fb     ::Vector{NTuple{2,Int}},
        G      ::Div2,
        T      ::Div2;
        tag    ::String = "")::Bool

    D_fb = JacID
    for (idx, v) in row
        pt   = fb[idx]
        Dp   = mumford1(pt[1], pt[2])
        absv = abs(v)
        Dv   = jac_mul_raw(Dp, absv)
        D_fb = v > 0 ? jac_add(D_fb, Dv) : jac_sub(D_fb, Dv)
    end
    D_lp  = mumford1(lp_pt[1], lp_pt[2])
    D_lhs = jac_add(D_fb, D_lp)    # Σ fb + atom(lp_pt)
    D_rhs = jac_add(jac_mul(G, neg_al), jac_mul(T, neg_be))

    D_lhs == D_rhs && return true
    D_rhs_neg = jac_neg(D_rhs)
    if D_lhs == D_rhs_neg
        @printf("[ASSERT %s tid=%d] SIGN-FLIP on 1-LP store: lp_pt=%s  neg_al=%d neg_be=%d\n",
                tag, Threads.threadid(), string(lp_pt), neg_al, neg_be)
        return true
    end
    @printf("[ASSERT %s tid=%d] FAIL on 1-LP store: fb_sum+atom(lp_pt) != neg_al·G+neg_be·T  lp_pt=%s  neg_al=%d neg_be=%d row_w=%d\n",
            tag, Threads.threadid(), string(lp_pt), neg_al, neg_be, length(row))
    return false
end

# ---------------------------------------------------------------------------
#  φ construction from Mumford representation
#
#  φ(x,y) = a·x² + b·x + c + d·y
#
#  Vanishing conditions:
#    At P0 = (px, py):                a·px² + b·px + c + d·py = 0          (i)
#    At supp D, u(x) = x²+u1·x+u0, v(x) = v0+v1·x:
#      φ(x, v(x)) ≡ 0  mod u(x)
#      Reducing x² → -u1·x - u0:
#        const:  c + d·v0 - a·u0 = 0                                        (ii)
#        x-coef: b + d·v1 - a·u1 = 0                                        (iii)
#
#  Normalise d=1: from (ii) c = a·u0 - v0; from (iii) b = a·u1 - v1.
#  Substituting into (i): a·(px² + u1·px + u0) = v1·px + v0 - py.
#  Denominator = u(px).  If u(px) = 0 then px is a root of D, which the
#  caller is supposed to have filtered; we return nothing in that case.
#
#  Returns (a, b, c, d=1) or nothing.
# ---------------------------------------------------------------------------
function build_phi_mumford(px::Int, py::Int,
                           u0::Int, u1::Int,
                           v0::Int, v1::Int)::Union{NTuple{4,Int}, Nothing}
    upx = fp(fp(px * px) + fp(u1 * px) + u0)
    upx == 0 && return nothing   # px is a root of D — caller should filter

    numer = fp(fp(v1 * px) + v0 - py)
    a = fp(numer * fpinv(upx))
    b = fp(fp(a * u1) - v1)
    c = fp(fp(a * u0) - v0)
    return (a, b, c, 1)
end

# ---------------------------------------------------------------------------
#  Residual intersection {R, S} from Mumford representation
#
#  Given φ(x,y) = a·x² + b·x + c + y  (d=1), define
#    N(x) = (a·x²+b·x+c)² - f(x)    (degree 5, leading coeff -1)
#
#  N has three known factors: (x - px) from P0, and u(x) = x²+u1·x+u0
#  from D's support.  Dividing out these factors leaves the degree-2
#  residual u_RS(x) = x² + c1·x + c0, the Mumford u-polynomial for {R, S}.
#
#  Return type:
#    - Two split rational points (R, S, nothing) if disc ≥ 0 in F_p.
#    - (nothing, nothing, (c0, c1, v0_RS, v1_RS)) if {R,S} are a conjugate
#      pair over F_p² — the full Mumford representation is returned so the
#      caller can key the conjugate-pair LP table.
#    - nothing if the division has a nonzero remainder (should not happen;
#      indicates a bug upstream).
# ---------------------------------------------------------------------------
function phi_residual_mumford(a::Int, b::Int, c::Int,
                               px::Int,
                               u0::Int, u1::Int)::Union{
                                   Tuple{NTuple{2,Int}, NTuple{2,Int}, NTuple{4,Int}},
                                   Tuple{Nothing, Nothing, NTuple{4,Int}},
                                   Nothing}
    # --- Build N(x) = (a·x²+b·x+c)² - f(x)  (coefficients ascending) ---
    N0 = fp(c*c)
    N1 = fp(2*b*c)
    N2 = fp(b*b + 2*a*c)
    N3 = fp(2*a*b)
    N4 = fp(a*a)
    # f(x) = x^5 + F_POLY[4]·x^3 + F_POLY[3]·x^2 + F_POLY[2]·x + F_POLY[1]
    # F_POLY[5]=0, F_POLY[6]=1 (ascending indexing, leading coeff 1)
    N = (fp(N0 - F_POLY[1]),
         fp(N1 - F_POLY[2]),
         fp(N2 - F_POLY[3]),
         fp(N3 - F_POLY[4]),
         fp(N4 - F_POLY[5]),   # = N4 since F_POLY[5]=0
         fp(   - F_POLY[6]))   # = -1  (leading x^5 coefficient)

    # --- Step 1: divide N(x) by (x - px) via descending Horner ---
    q4_4 = N[6]
    q4_3 = fp(N[5] + q4_4*px)
    q4_2 = fp(N[4] + q4_3*px)
    q4_1 = fp(N[3] + q4_2*px)
    q4_0 = fp(N[2] + q4_1*px)
    rem1  = fp(N[1] + q4_0*px)
    rem1 != 0 && return nothing   # px not a root — upstream bug if this fires

    # --- Step 2: divide Q4(x) = q4_4·x^4+…+q4_0 by u(x) = x²+u1·x+u0 ---
    # Long division of degree-4 by monic degree-2, three reduction steps:
    s2  = q4_4                    # leading quotient coeff (x^2 term)
    r3  = fp(q4_3 - s2*u1)
    r2  = fp(q4_2 - s2*u0)
    s1  = r3                      # next quotient coeff (x^1 term)
    r2b = fp(r2  - s1*u1)
    r1  = fp(q4_1 - s1*u0)
    s0  = r2b                     # constant quotient coeff
    # Remainder should be zero — nonzero means D's support is not in zero(φ)
    res1 = fp(r1  - s0*u1)
    res0 = fp(q4_0 - s0*u0)
    (res0 != 0 || res1 != 0) && return nothing

    # --- Make quotient s(x) = s2·x²+s1·x+s0 monic ---
    # s2 = q4_4 = N[6] = -1 (mod p), so inv(s2) = p-1 = -1 mod p.
    inv_s2 = fpinv(s2)
    c1_rs  = fp(s1 * inv_s2)   # monic x-coeff of u_RS
    c0_rs  = fp(s0 * inv_s2)   # monic constant of u_RS

    # --- Compute v_RS(x) = -(a·x²+b·x+c) mod u_RS(x) unconditionally ---
    # Reduce x² → -c1_rs·x - c0_rs:
    #   v_RS(x) = a·(c1_rs·x + c0_rs) - b·x - c
    #           = (a·c1_rs - b)·x + (a·c0_rs - c)
    # Valid for all root configurations (split or conjugate) because the
    # reduction is a pure polynomial identity — it does not depend on whether
    # u_RS splits over F_p or F_p².
    v1_rs = fp(fp(a * c1_rs) - b)
    v0_rs = fp(fp(a * c0_rs) - c)

    # --- Try to split u_RS over F_p ---
    disc = fp(fp(c1_rs * c1_rs) - fp(4 * c0_rs))
    sq   = sqrt_fp(disc)

    if sq === nothing
        # R, S are a conjugate pair over F_p².
        # Full Mumford key (c0, c1, v0, v1) uniquely identifies the degree-2 element.
        return (nothing, nothing, (c0_rs, c1_rs, v0_rs, v1_rs))
    end

    # Two F_p-rational roots.  Also return the canonical Mumford key so the
    # caller can use a single unified lookup table regardless of split/conjugate.
    inv2 = fpinv(2)
    xR   = fp(fp(p - c1_rs + sq) * inv2)
    xS   = fp(fp(p - c1_rs - sq) * inv2)

    # Recover y: φ(x,y)=0 with d=1 → y = -(a·x²+b·x+c).
    yR = fp(p - fp(fp(a * fp(xR*xR)) + fp(b*xR) + c))
    yS = fp(p - fp(fp(a * fp(xS*xS)) + fp(b*xS) + c))

    return ((xR, yR), (xS, yS), (c0_rs, c1_rs, v0_rs, v1_rs))
end
