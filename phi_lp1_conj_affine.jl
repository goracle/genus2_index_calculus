# =============================================================================
#  phi_lp1_conj_affine.jl  --  φ construction from two Mumford divisors.
#
#  This implements the "chained LP1-conj affine" step:
#
#  Background
#  ----------
#  A standard LP1-conj step gives a partial:
#
#    atom(P0) + [u_RS, v_RS] = neg_al·G + neg_be·T          (★)
#
#  where P0 ∈ FB and [u_RS, v_RS] is a non-split (conjugate) residual.
#  We store this partial keyed by the Mumford 4-tuple (c0,c1,v0,v1) of [u_RS,v_RS]
#  and wait for a birthday collision.
#
#  New idea: instead of only waiting for a birthday, try to *continue the walk*
#  by building a second φ₂ that passes through the conjugate pair [u_RS, v_RS]
#  AND through the support of the base divisor D_α = α·G (also a Mumford pair).
#  The residual of φ₂ is a new degree-2 divisor [u_new, v_new].
#
#  Degree accounting
#  -----------------
#  φ₂(x,y) = ax² + bx + c + dy  (same function space as φ₁).
#  The divisor of zeros on C has degree 6.
#  We impose 4 vanishing conditions (2 per Mumford divisor):
#
#    Vanish at [u_RS, v_RS]:  φ₂(x, v_RS(x)) ≡ 0 mod u_RS(x)   → 2 eqs
#    Vanish at [u_α,  v_α ]:  φ₂(x, v_α(x))  ≡ 0 mod u_α(x)    → 2 eqs
#
#  Total: 4 linear equations in 4 unknowns (a,b,c,d).  The system is
#  generically non-degenerate (see degeneracy notes below).
#
#  The 4×4 system
#  --------------
#  For a Mumford pair [u: x²+u₁x+u₀, v: v₁x+v₀], reducing x²→-u₁x-u₀ gives:
#
#    Const coeff: c + d·v₀ - a·u₀ = 0          …(C)
#    x-coeff:     b + d·v₁ - a·u₁ = 0          …(X)
#
#  For two divisors (u_RS, v_RS) and (u_α, v_α):
#    (C_RS):  c + d·vRS₀ - a·uRS₀ = 0
#    (X_RS):  b + d·vRS₁ - a·uRS₁ = 0
#    (C_α):   c + d·vα₀  - a·uα₀  = 0
#    (X_α):   b + d·vα₁  - a·uα₁  = 0
#
#  Subtracting pairs:
#    (C_RS) - (C_α):  d·(vRS₀ - vα₀) = a·(uRS₀ - uα₀)        …(I)
#    (X_RS) - (X_α):  d·(vRS₁ - vα₁) = a·(uRS₁ - uα₁)        …(II)
#
#  Generically both (I) and (II) determine the same ratio d/a.  We solve by
#  choosing the equation with the larger (nonzero) coefficient for stability:
#
#    If (uRS₀ - uα₀) ≠ 0:  a = (vRS₀ - vα₀)·inv(uRS₀ - uα₀)·d
#                            normalise d=1 → a determined.
#    Else use (II).
#    Then: b = a·uRS₁ - vRS₁,  c = a·uRS₀ - vRS₀.
#
#  Degeneracy conditions (→ return nothing):
#    • u_RS = u_α  (same Mumford polynomial):  both Δu₀=0 and Δu₁=0.
#      This happens iff the two walks reach the same degree-2 divisor, which
#      would make φ₂ underdetermined.  Probability ≈ 1/p — negligible.
#    • uRS₀ = uα₀ AND uRS₁ = uα₁: identical polynomials (handled above).
#    • Sole remaining case: Δu₀=0 but Δu₁≠0 (or vice versa) — use the nonzero
#      equation.  Both Δu₀=0 AND Δu₁=0 is the degenerate case.
#
#  Relation accounting
#  -------------------
#  Define the relation carried by the partial (★) as:
#
#    atom(P0) + [u_RS, v_RS]  =  neg_al·G + neg_be·T
#
#  and the new φ₂ step as:
#
#    [u_RS, v_RS] + D_α  =  [u_new, v_new]     (divisor equation from φ₂)
#
#  where D_α = [u_α, v_α] = α_new·G.
#
#  Substituting: atom(P0) + D_α - [u_new, v_new] = neg_al·G + neg_be·T + α_new·G
#  → atom(P0) - [u_new, v_new] = (neg_al + α_new)·G + neg_be·T
#
#  The new partial is therefore:
#    atom(P0)  +  [u_new, v_new]  =  neg_al_new·G + neg_be_new·T
#  with  neg_al_new = -(neg_al + α_new) = -neg_al - α_new  (mod ell)
#        neg_be_new = -neg_be             (signs follow negation of the identity)
#
#  Wait — let's be careful with the sign convention used in the rest of the code.
#  In `handle_1lp_conj!` the stored tuple is (i0, neg_al, neg_be) satisfying:
#
#    atom(fb[i0])  +  [u_RS, v_RS]  =  neg_al·G + neg_be·T        (★)
#
#  φ₂ establishes that (in the Jacobian):
#
#    [u_RS, v_RS]  +  D_α  +  [u_new_neg, v_new_neg]  =  0        (from the φ divisor)
#
#  where [u_new_neg, v_new_neg] is the *negation* of [u_new, v_new] in the Jacobian
#  (the residual from the φ₂ zero divisor, which contributes with sign +1 to the
#  principal divisor; in our convention it appears as −[u_new, v_new]).
#
#  So:  [u_RS, v_RS]  =  -D_α - [u_new_neg, v_new_neg]
#                      =  α_new·(-G) + [u_new, v_new]         (negating D_α = α_new·G)
#
#  Substituting into (★):
#    atom(fb[i0]) + (-α_new·G) + [u_new, v_new]  =  neg_al·G + neg_be·T
#    atom(fb[i0]) + [u_new, v_new]  =  (neg_al + α_new)·G + neg_be·T
#
#  So the new partial has:
#    neg_al_new = mod(neg_al + α_new, ell)
#    neg_be_new = neg_be
#    parent_i0  = i0   (same FB anchor)
#
#  The LP key changes to the Mumford 4-tuple of [u_new, v_new].
#
#  If [u_new, v_new] splits over F_p into two affine points (xR,yR),(xS,yS):
#    • Check each against the factor base.
#    • Both in FB → emit full relation immediately (0-LP close on the chain).
#    • One in FB, one not → we have a new LP1-affine partial; store it.
#    • Neither in FB → new LP1-conj-affine partial with this as the LP key,
#                       but now both points are *affine* so treat as standard LP1-affine.
#      (The walk can continue or we store for birthday close.)
#
#  If [u_new, v_new] is again non-split → we have a chained LP1-conj residual.
#  We *store* this as a new LP1-conj partial (same table, different key) with
#  parent lineage (i0, neg_al_new, neg_be_new).  The next birthday collision on
#  THIS key either closes the chain or feeds another step.
#
#  The depth of chaining is bounded by a configurable MAX_CONJ_CHAIN_DEPTH to
#  prevent infinite loops.  In practice, each chaining step multiplies the
#  smoothness probability by ≈(B/p)², so chains of length >2–3 are unlikely
#  to close before exhausting the step budget.
#
# =============================================================================


# ---------------------------------------------------------------------------
#  build_phi_two_mumford
#
#  Construct φ(x,y) = ax² + bx + c + dy vanishing on two Mumford divisors.
#
#  Inputs:
#    (uRS0, uRS1, vRS0, vRS1) — Mumford pair from LP1-conj residual
#    (uA0,  uA1,  vA0,  vA1)  — Mumford pair for the new base divisor D_α
#
#  Returns (a, b, c, d) with d normalised to 1, or `nothing` if degenerate.
#
#  Degeneracy: uRS = uA (the two input divisors share the same u-polynomial).
#  This means the four vanishing conditions collapse to two (the two u-polynomials
#  are identical so (C_RS)=(C_α) and (X_RS)=(X_α)), leaving the system rank-2.
# ---------------------------------------------------------------------------
function build_phi_two_mumford(uRS0::Int, uRS1::Int, vRS0::Int, vRS1::Int,
                                uA0::Int,  uA1::Int,  vA0::Int,  vA1::Int
                               )::Union{NTuple{4,Int}, Nothing}
    # Δu components determine the ratio d/a via:
    #   d·ΔvC = a·ΔuC   where ΔuC = uRS0-uA0, ΔvC = vRS0-vA0
    #   d·ΔvX = a·ΔuX   where ΔuX = uRS1-uA1, ΔvX = vRS1-vA1
    ΔuC = fp(uRS0 - uA0)
    ΔuX = fp(uRS1 - uA1)
    ΔvC = fp(vRS0 - vA0)
    ΔvX = fp(vRS1 - vA1)

    # Full degeneracy: both Δu components are zero → u_RS = u_A → underdetermined.
    (ΔuC == 0 && ΔuX == 0) && return nothing

    # Normalise d = 1.  Solve for a:
    #   From (I):  a = ΔvC · inv(ΔuC)   (if ΔuC ≠ 0)
    #   From (II): a = ΔvX · inv(ΔuX)   (if ΔuX ≠ 0)
    # Prefer the equation with a nonzero denominator.
    a::Int = if ΔuC != 0
        fpmul(ΔvC, fpinv(ΔuC))
    else
        # ΔuC == 0 → ΔvC must equal 0 too (otherwise the system is inconsistent,
        # which cannot happen for valid Mumford pairs on the same curve).
        # Use equation (II) with ΔuX ≠ 0.
        fpmul(ΔvX, fpinv(ΔuX))
    end

    # d = 1, a determined.  Recover b and c from the RS equations:
    #   b = a·uRS₁ - vRS₁   (from (X_RS) with d=1)
    #   c = a·uRS₀ - vRS₀   (from (C_RS) with d=1)
    b = fp(fpmul(a, uRS1) - vRS1)
    c = fp(fpmul(a, uRS0) - vRS0)

    return (a, b, c, 1)
end


# ---------------------------------------------------------------------------
#  phi_two_mumford_residual
#
#  Given a φ built from two Mumford divisors, compute the residual degree-2
#  divisor [u_new, v_new] as a Mumford 4-tuple (c0_new, c1_new, v0_new, v1_new).
#
#  The approach mirrors phi_residual_mumford, but instead of dividing out a
#  single point P0 and then u_D, we divide out u_RS and u_α from N(x):
#
#    N(x) = (ax²+bx+c)² - f(x)
#
#  We know u_RS(x) | N(x) and u_α(x) | N(x) (by construction of φ).
#  We divide out both to get the residual monic degree-2 quotient.
#
#  Returns (c0_new, c1_new, v0_new, v1_new) or SENTINEL_MUMFORD on failure.
#
#  The residual is the THIRD degree-2 factor of the degree-6 polynomial N(x)/1,
#  after removing the two known factors u_RS and u_α.
#
#  N(x) = (a·x² + b·x + c)² - f(x) has degree 6.
#  We have two known monic degree-2 factors u_RS and u_α.
#  If they are coprime (which they must be — we checked ΔuC≠0 or ΔuX≠0 so they
#  differ), their product u_RS·u_α is a degree-4 polynomial, and dividing N(x)
#  by it yields a monic degree-2 quotient (the residual).
#
#  Note: we do NOT divide out a single point here; the full N(x) = u_RS·u_α·u_new
#  (up to leading coefficient), so two successive polynomial divisions suffice.
# ---------------------------------------------------------------------------
function phi_two_mumford_residual(a::Int, b::Int, c::Int,
                                   uRS0::Int, uRS1::Int,
                                   uA0::Int,  uA1::Int
                                  )::NTuple{4,Int}
    # --- Build N(x) = (ax²+bx+c)² - f(x), coefficients N[i] = coeff of x^(i-1) ---
    #  (ax²+bx+c)² = a²x⁴ + 2abx³ + (b²+2ac)x² + 2bcx + c²
    #  f(x) = F_POLY[1] + F_POLY[2]x + F_POLY[3]x² + F_POLY[4]x³ + F_POLY[5]x⁴ + F_POLY[6]x⁵
    #  F_POLY[6]=1 so the x⁵ term comes only from -f(x).
    N0 = fpmul(c, c)
    N1 = fp(2 * fpmul(b, c))
    N2 = fp(fpmul(b, b) + 2 * fpmul(a, c))
    N3 = fp(2 * fpmul(a, b))
    N4 = fpmul(a, a)
    N = (fp(N0 - F_POLY[1]),
         fp(N1 - F_POLY[2]),
         fp(N2 - F_POLY[3]),
         fp(N3 - F_POLY[4]),
         fp(N4 - F_POLY[5]),
         fp(   - F_POLY[6]))   # degree-5 coeff: 0 - 1·x⁵

    # --- Step 1: divide N(x) by u_RS(x) = x² + uRS1·x + uRS0 ---
    # N has degree 6 (leading coeff = -F_POLY[6] = -1 = p-1), so N[6]≠0.
    # Descending synthetic division: quotient Q has degree 4.
    q5 = N[6]                                         # coeff of x⁴ in Q = leading of N / 1
    q4 = fp(N[5] - fpmul(q5, uRS1))
    q3 = fp(N[4] - fpmul(q5, uRS0) - fpmul(q4, uRS1))
    q2 = fp(N[3]                   - fpmul(q4, uRS0) - fpmul(q3, uRS1))
    q1 = fp(N[2]                   - fpmul(q3, uRS0) - fpmul(q2, uRS1))
    r1 = fp(N[1]                   - fpmul(q2, uRS0) - fpmul(q1, uRS1))
    r0 = fp(                       - fpmul(q1, uRS0))

    # Verify remainder is zero (by construction of φ₂, it must be).
    if r0 != 0 || r1 != 0
        # Numerical inconsistency — caller's φ is not vanishing on u_RS as expected.
        return SENTINEL_MUMFORD
    end

    # Q(x) = q5·x⁴ + q4·x³ + q3·x² + q2·x + q1 (degree 4)

    # --- Step 2: divide Q(x) by u_A(x) = x² + uA1·x + uA0 ---
    # Quotient has degree 2; residual must be zero.
    s3 = q5
    s2 = fp(q4 - fpmul(s3, uA1))
    s1 = fp(q3 - fpmul(s3, uA0) - fpmul(s2, uA1))
    t1 = fp(q2 - fpmul(s2, uA0) - fpmul(s1, uA1))
    t0 = fp(q1 - fpmul(s1, uA0))

    if t0 != 0 || t1 != 0
        return SENTINEL_MUMFORD
    end

    # S(x) = s3·x² + s2·x + s1 — make it monic.
    s3 == 0 && return SENTINEL_MUMFORD    # degenerate degree
    inv_s3 = fpinv(s3)
    c1_new = fpmul(s2, inv_s3)
    c0_new = fpmul(s1, inv_s3)

    # --- Compute v_new(x) = -(ax²+bx+c) mod u_new(x) ---
    # Reduce ax² using x² ≡ -c1_new·x - c0_new:
    #   ax² → a·(-c1_new·x - c0_new)
    # So (ax²+bx+c) mod u_new = (b - a·c1_new)·x + (c - a·c0_new)
    # v_new = negation of this:
    v1_new = fp(fpmul(a, c1_new) - b)
    v0_new = fp(fpmul(a, c0_new) - c)

    return (c0_new, c1_new, v0_new, v1_new)
end


# ---------------------------------------------------------------------------
#  phi_two_mumford_split
#
#  Convenience wrapper: builds φ from two Mumford divisors, computes residual,
#  and attempts to split it into affine points.
#
#  Returns a named tuple:
#    ok        ::Bool                  — false if construction failed (degenerate)
#    phi       ::NTuple{4,Int}         — (a,b,c,d) or undefined if !ok
#    mumford   ::NTuple{4,Int}         — (c0,c1,v0,v1) of residual, SENTINEL_MUMFORD if failed
#    split     ::Bool                  — true if residual splits over F_p
#    R         ::NTuple{2,Int}         — first split point, SENTINEL_PT if !split
#    S         ::NTuple{2,Int}         — second split point, SENTINEL_PT if !split
#
#  This is the "inner kernel" called from the walk.  The walk logic decides
#  what to do with the result (0-LP emit, LP1-affine store, LP1-conj store).
# ---------------------------------------------------------------------------
function phi_two_mumford_split(uRS0::Int, uRS1::Int, vRS0::Int, vRS1::Int,
                                uA0::Int,  uA1::Int,  vA0::Int,  vA1::Int)
    phi = build_phi_two_mumford(uRS0, uRS1, vRS0, vRS1, uA0, uA1, vA0, vA1)
    if phi === nothing
        return (ok=false, phi=(0,0,0,0),
                mumford=SENTINEL_MUMFORD, split=false, R=SENTINEL_PT, S=SENTINEL_PT)
    end
    a, b, c, _ = phi

    mumford = phi_two_mumford_residual(a, b, c, uRS0, uRS1, uA0, uA1)
    if mumford === SENTINEL_MUMFORD
        return (ok=false, phi=phi,
                mumford=SENTINEL_MUMFORD, split=false, R=SENTINEL_PT, S=SENTINEL_PT)
    end

    c0_new, c1_new, v0_new, v1_new = mumford

    # Try to split u_new(x) = x² + c1_new·x + c0_new over F_p.
    disc = fp(fpmul(c1_new, c1_new) - 4 * c0_new)
    sq   = sqrt_fp(disc)
    if sq === nothing
        return (ok=true, phi=phi, mumford=mumford,
                split=false, R=SENTINEL_PT, S=SENTINEL_PT)
    end

    inv2 = fpinv(2)
    xR   = fpmul(fp(-c1_new + sq), inv2)
    xS   = fpmul(fp(-c1_new - sq), inv2)
    yR   = fp(-(fpmul(a, fpmul(xR, xR)) + fpmul(b, xR) + c))
    yS   = fp(-(fpmul(a, fpmul(xS, xS)) + fpmul(b, xS) + c))

    return (ok=true, phi=phi, mumford=mumford,
            split=true, R=(xR, yR), S=(xS, yS))
end


# ---------------------------------------------------------------------------
#  conj_chain_neg_al_new
#  conj_chain_neg_be_new
#
#  Scalar update for the chained LP1-conj partial.
#
#  Given a stored partial (★):
#    atom(fb[i0]) + [u_RS, v_RS] = neg_al·G + neg_be·T
#
#  and a new φ₂ step using base divisor D_{α_new} = α_new·G:
#    [u_RS, v_RS] + D_{α_new} + [u_new_residual] = 0  (principal divisor)
#    → [u_RS, v_RS] = -α_new·G - [u_new_residual]
#
#  (using the sign convention that the residual [u_new, v_new] from
#  phi_two_mumford_residual represents the v-negated form, i.e. the Mumford
#  coordinates already encode the subtraction sense)
#
#  Substituting:
#    atom(fb[i0]) + (-α_new·G - [u_new, v_new]) = neg_al·G + neg_be·T
#    atom(fb[i0]) - [u_new, v_new] = (neg_al + α_new)·G + neg_be·T
#    atom(fb[i0]) + [u_new, v_new] = (neg_al + α_new)·G + neg_be·T
#
#  So the new LP key is mumford([u_new,v_new]) and the updated scalars are:
#    neg_al_new = mod(neg_al + α_new, ell)
#    neg_be_new = neg_be   (unchanged; T carries the same coefficient)
#
#  NOTE: these are pure arithmetic helpers; the actual walk logic that builds
#  the new LP1-conj entry and routes to the appropriate store is in phase2.
# ---------------------------------------------------------------------------
@inline function conj_chain_neg_al_new(neg_al::Int, alpha_new::Int, ellI::Int)::Int
    mod(neg_al + alpha_new, ellI)
end

@inline function conj_chain_neg_be_new(neg_be::Int, ::Int, ::Int)::Int
    neg_be   # be is invariant under the chaining step
end


# ---------------------------------------------------------------------------
#  check_phi_two_mumford_consistency
#
#  Debug / assertion helper.
#  Verifies that the constructed φ actually vanishes on both input divisors
#  by checking φ(x, v(x)) mod u(x) = 0 for each.
#  Returns (ok1::Bool, ok2::Bool).
# ---------------------------------------------------------------------------
function check_phi_two_mumford_consistency(a::Int, b::Int, c::Int, d::Int,
                                            uRS0::Int, uRS1::Int, vRS0::Int, vRS1::Int,
                                            uA0::Int,  uA1::Int,  vA0::Int,  vA1::Int
                                           )::Tuple{Bool,Bool}
    # For divisor 1 [uRS], reduce x²→-uRS1·x-uRS0:
    # φ(x,vRS(x)) = a·x² + b·x + c + vRS1·x + vRS0
    #             → const: c + vRS0 - a·uRS0  (should be 0)
    #             → x:     b + vRS1 - a·uRS1  (should be 0)
    ok1_const = fp(c + fpmul(d, vRS0) - fpmul(a, uRS0)) == 0
    ok1_x     = fp(b + fpmul(d, vRS1) - fpmul(a, uRS1)) == 0

    ok2_const = fp(c + fpmul(d, vA0) - fpmul(a, uA0)) == 0
    ok2_x     = fp(b + fpmul(d, vA1) - fpmul(a, uA1)) == 0

    return (ok1_const && ok1_x, ok2_const && ok2_x)
end
