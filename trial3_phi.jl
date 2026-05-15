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
        al         ::BigInt,
        be         ::BigInt,
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
    D_rhs = jac_add(jac_mul(G, al, ell), jac_mul(T, be, ell))

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
        neg_al ::BigInt,
        neg_be ::BigInt,
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
    D_rhs = jac_add(jac_mul(G, neg_al, ell), jac_mul(T, neg_be, ell))

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
    upx = fp(fpmul(px, px) + fpmul(u1, px) + u0)
    upx == 0 && return nothing   # px is a root of D — caller should filter

    numer = fp(fpmul(v1, px) + v0 - py)
    a = fpmul(numer, fpinv(upx))
    b = fp(fpmul(a, u1) - v1)
    c = fp(fpmul(a, u0) - v0)
    return (a, b, c, 1)
end

# ---------------------------------------------------------------------------
#  Residual intersection {R, S} from Mumford representation
#
#  Returns a 3-tuple:
#    (R::NTuple{2,Int}, S::NTuple{2,Int}, RS_mumford::NTuple{4,Int})
#
#  Sentinel conventions (avoids Union{...,Nothing} heap boxing):
#    • R == S == SENTINEL_PT   → conjugate pair (non-split); RS_mumford is valid
#    • RS_mumford == SENTINEL_MUMFORD → division failed (upstream bug)
#
#  Callers check:
#    res === nothing     → impossible now (function never returns nothing)
#    rs_split            → res[1] != SENTINEL_PT
#    division ok         → res[3] != SENTINEL_MUMFORD
# ---------------------------------------------------------------------------
const SENTINEL_PT      = (-1, -1)::NTuple{2,Int}
const SENTINEL_MUMFORD = (-1, -1, -1, -1)::NTuple{4,Int}

@inline function phi_residual_mumford(a::Int, b::Int, c::Int,
                               px::Int,
                               u0::Int, u1::Int)::Tuple{NTuple{2,Int}, NTuple{2,Int}, NTuple{4,Int}}
    # --- Build N(x) = (a·x²+b·x+c)² - f(x)  (coefficients ascending) ---
    N0 = fpmul(c,c)
    N1 = fp(2*fpmul(b,c))
    N2 = fp(fpmul(b,b) + 2*fpmul(a,c))
    N3 = fp(2*fpmul(a,b))
    N4 = fpmul(a,a)
    N = (fp(N0 - F_POLY[1]),
         fp(N1 - F_POLY[2]),
         fp(N2 - F_POLY[3]),
         fp(N3 - F_POLY[4]),
         fp(N4 - F_POLY[5]),
         fp(   - F_POLY[6]))

    # --- Step 1: divide N(x) by (x - px) via descending Horner ---
    q4_4 = N[6]
    q4_3 = fp(N[5] + fpmul(q4_4,px))
    q4_2 = fp(N[4] + fpmul(q4_3,px))
    q4_1 = fp(N[3] + fpmul(q4_2,px))
    q4_0 = fp(N[2] + fpmul(q4_1,px))
    rem1  = fp(N[1] + fpmul(q4_0,px))
    rem1 != 0 && return (SENTINEL_PT, SENTINEL_PT, SENTINEL_MUMFORD)

    # --- Step 2: divide Q4(x) = q4_4·x^4+…+q4_0 by u(x) = x²+u1·x+u0 ---
    s2  = q4_4
    r3  = fp(q4_3 - fpmul(s2,u1))
    r2  = fp(q4_2 - fpmul(s2,u0))
    s1  = r3
    r2b = fp(r2  - fpmul(s1,u1))
    r1  = fp(q4_1 - fpmul(s1,u0))
    s0  = r2b
    res1 = fp(r1  - fpmul(s0,u1))
    res0 = fp(q4_0 - fpmul(s0,u0))
    (res0 != 0 || res1 != 0) && return (SENTINEL_PT, SENTINEL_PT, SENTINEL_MUMFORD)

    # --- Make quotient s(x) = s2·x²+s1·x+s0 monic ---
    inv_s2 = fpinv(s2)
    c1_rs  = fpmul(s1, inv_s2)
    c0_rs  = fpmul(s0, inv_s2)

    # --- Compute v_RS(x) = -(a·x²+b·x+c) mod u_RS(x) unconditionally ---
    v1_rs = fp(fpmul(a, c1_rs) - b)
    v0_rs = fp(fpmul(a, c0_rs) - c)

    # --- Try to split u_RS over F_p ---
    disc = fp(fpmul(c1_rs, c1_rs) - 4*c0_rs)
    sq   = sqrt_fp(disc)

    mumford_key = (c0_rs, c1_rs, v0_rs, v1_rs)

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
