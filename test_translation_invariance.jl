#!/usr/bin/env julia
#
# test_translation_invariance.jl
#
# Numerical test of the translation-invariance claim for the NID fiber
# system's defining relation:
#
#     reduce(P1 + P2 - alpha*a)  ==  reduce(P3 + P4 - alpha'*a)          (*)
#
# on the genus-2 hyperelliptic Jacobian J of  y^2 = x^5 + x + 2  over
# F_p, matching nid_fiber_system.jl / Elim2's SampleSpecs conventions
# exactly (same curve, same p, same Mumford-representation variables
# wa1,wa2,wb1,wb2,a2,a1,b2,b1,U0,U1,V0,V1).
#
# CLAIM BEING TESTED: if (*) holds for a given (P1,P2,P3,P4,alpha,alpha'),
# then for ANY divisor T on J (any "Jacobian translation"), replacing
#
#     P1+P2 -> T + P1+P2        P3+P4 -> T + P3+P4
#
# (i.e. shifting BOTH sides of (*) by the same T before reducing) gives
# another solution of the same defining relation:
#
#     reduce(T + P1+P2 - alpha*a)  ==  reduce(T + P3+P4 - alpha'*a)      (**)
#
# This is just additivity of the Jacobian group law: if D1 == D2 as
# divisor classes, then T+D1 == T+D2 for any class T, since reduce()
# here computes the honest reduced Mumford representative of a divisor
# class, and Cantor composition IS the group law addition. The point of
# this script is to verify that numerically/computationally against the
# actual arithmetic used elsewhere in this repo (Cantor's algorithm over
# F_p), not to re-derive the group axiom symbolically.
#
# THE "12 EQUATIONS / 12 UNKNOWNS" SYSTEM:
# Exactly the fiber system nid_fiber_system.jl builds:
#   unknowns: wa1,wa2,wb1,wb2,a2,a1,b2,b1,U0,U1,V0,V1
#   equations:
#     curve_a1 :  wa1^2 - (a1^5+a1+2)        = 0
#     curve_a2 :  wa2^2 - (a2^5+a2+2)        = 0
#     curve_b1 :  wb1^2 - (b1^5+b1+2)        = 0
#     curve_b2 :  wb2^2 - (b2^5+b2+2)        = 0
#     Fu[1..2] :  U0,U1 forced to equal the Mumford u-poly coefficients
#                 of reduce(P1+P2 - alpha*a)   (2 scalar equations)
#     Fv[1..2] :  U0,U1 forced to equal the Mumford v-poly coefficients
#                 of reduce(P1+P2 - alpha*a)   (2 scalar equations)
#     [same 4, from the b-side] forcing (U0,U1,V0,V1) to ALSO equal the
#                 Mumford coordinates of reduce(P3+P4 - alpha'*a)
#   -> 4 curve relations + 2+2 (a-side Fu/Fv) + 2+2 (b-side Fu/Fv) = 12
#      equations in the 12 listed unknowns, and (*) says this system is
#      satisfiable (both sides define the SAME (U0,U1,V0,V1)).
#
# We plug in N_TRIALS independently-constructed "base" solutions and, for
# each, one "shifted" solution (that trial's P1,P2,P3,P4 translated by a
# fresh random T), and verify BOTH satisfy all 12 equations exactly, mod p,
# for every trial -- tallying pass/fail counts rather than eyeballing one
# instance.
#
# Usage: julia test_translation_invariance.jl
#   (edit N_TRIALS / VERBOSE_FIRST_K near the bottom of the file to change
#   the trial count or how many trials print full per-equation detail)

using Random

# ---------------------------------------------------------------------------
# Curve / field setup -- identical constants to Elim2.SampleSpecs
# ---------------------------------------------------------------------------

const P_MOD = 2371157                 # SampleSpecs.DEFAULT_P
const F_POLY = Int[2, 1, 0, 0, 0, 1]  # f(x) = x^5 + x + 2  (coeffs, ascending degree)
const SEED = 2026

# Generator G used by SampleSpecs.generate_sample_spec (u_G, v_G below)
const U_G = Int[2307335, 2061398, 1]
const V_G = Int[1348746, 397106]

# ---------------------------------------------------------------------------
# F_p[x] arithmetic + Cantor's algorithm -- copied verbatim (same
# algorithm/behavior) from Elim2/src/00_sample_specs.jl so this script has
# no package dependency and can be run standalone with `julia` only.
# ---------------------------------------------------------------------------

function p_trim(a::Vector{Int})
    d = length(a)
    while d > 1 && a[d] == 0
        d -= 1
    end
    return a[1:d]
end

function p_add(a::Vector{Int}, b::Vector{Int}, p::Int)
    n = max(length(a), length(b))
    res = zeros(Int, n)
    for i in 1:n
        va = i <= length(a) ? a[i] : 0
        vb = i <= length(b) ? b[i] : 0
        res[i] = mod(va + vb, p)
    end
    return p_trim(res)
end

function p_sub(a::Vector{Int}, b::Vector{Int}, p::Int)
    n = max(length(a), length(b))
    res = zeros(Int, n)
    for i in 1:n
        va = i <= length(a) ? a[i] : 0
        vb = i <= length(b) ? b[i] : 0
        res[i] = mod(va - vb, p)
    end
    return p_trim(res)
end

function p_mul(a::Vector{Int}, b::Vector{Int}, p::Int)
    if (length(a) == 1 && a[1] == 0) || (length(b) == 1 && b[1] == 0)
        return Int[0]
    end
    res = zeros(Int, length(a) + length(b) - 1)
    for i in 1:length(a), j in 1:length(b)
        res[i+j-1] = mod(res[i+j-1] + a[i] * b[j], p)
    end
    return p_trim(res)
end

function p_scale(a::Vector{Int}, c::Int, p::Int)
    c_mod = mod(c, p)
    if c_mod == 0
        return Int[0]
    end
    return p_trim(Int[mod(x * c_mod, p) for x in a])
end

function p_divrem(a::Vector{Int}, b::Vector{Int}, p::Int)
    a = p_trim(a)
    b = p_trim(b)
    if length(b) == 1 && b[1] == 0
        throw(DivideError())
    end
    deg_a = length(a) - 1
    deg_b = length(b) - 1
    if deg_a < deg_b
        return Int[0], a
    end

    rem_p = copy(a)
    q = zeros(Int, deg_a - deg_b + 1)
    inv_b_lead = invmod(b[end], p)

    for i in (deg_a - deg_b):-1:0
        cur_deg = i + deg_b
        coeff_val = mod(rem_p[cur_deg + 1] * inv_b_lead, p)
        q[i + 1] = coeff_val
        if coeff_val != 0
            for j in 0:deg_b
                rem_p[i + j + 1] = mod(rem_p[i + j + 1] - coeff_val * b[j + 1], p)
            end
        end
    end
    return p_trim(q), p_trim(rem_p)
end

function p_gcdx(a::Vector{Int}, b::Vector{Int}, p::Int)
    a = p_trim(a)
    b = p_trim(b)
    r0, r1 = a, b
    s0, s1 = Int[1], Int[0]
    t0, t1 = Int[0], Int[1]

    while !(length(r1) == 1 && r1[1] == 0)
        q, r2 = p_divrem(r0, r1, p)
        s2 = p_sub(s0, p_mul(q, s1, p), p)
        t2 = p_sub(t0, p_mul(q, t1, p), p)
        r0, r1 = r1, r2
        s0, s1 = s1, s2
        t0, t1 = t1, t2
    end

    lead = r0[end]
    if lead != 0 && lead != 1
        inv_lead = invmod(lead, p)
        r0 = p_scale(r0, inv_lead, p)
        s0 = p_scale(s0, inv_lead, p)
        t0 = p_scale(t0, inv_lead, p)
    end
    return r0, s0, t0
end

"""
    cantor_add(u1,v1,u2,v2,f,p) -> (u,v)

Cantor composition-and-reduction: returns the Mumford representative of
reduce(D1 + D2) for genus-2 divisors D1=(u1,v1), D2=(u2,v2) on
y^2 = f(x) mod p. This IS the "reduce(... )" operation in the defining
relation (*) -- composition and reduction are fused in Cantor's algorithm,
there is no separate standalone reduce() to call.
"""
function cantor_add(u1::Vector{Int}, v1::Vector{Int}, u2::Vector{Int}, v2::Vector{Int}, f::Vector{Int}, p::Int)
    g1, e1, e2 = p_gcdx(u1, u2, p)
    v_sum = p_add(v1, v2, p)
    g, c1, c2 = p_gcdx(g1, v_sum, p)

    s1 = p_mul(c1, e1, p)
    s2 = p_mul(c1, e2, p)
    s3 = c2

    u1u2 = p_mul(u1, u2, p)
    g2 = p_mul(g, g, p)
    u, _ = p_divrem(u1u2, g2, p)

    term1 = p_mul(p_mul(s1, u1, p), v2, p)
    term2 = p_mul(p_mul(s2, u2, p), v1, p)
    term3 = p_mul(s3, p_add(p_mul(v1, v2, p), f, p), p)
    num = p_add(p_add(term1, term2, p), term3, p)
    v_tmp, _ = p_divrem(num, g, p)
    _, v = p_divrem(v_tmp, u, p)

    while length(u) - 1 > 2
        v2_poly = p_mul(v, v, p)
        num_next = p_sub(f, v2_poly, p)
        u_next, _ = p_divrem(num_next, u, p)

        if length(u_next) == 1 && u_next[1] == 0
            throw(ErrorException("Cantor reduction produced zero polynomial u_next"))
        end

        inv_lead = invmod(u_next[end], p)
        u_next = p_scale(u_next, inv_lead, p)

        neg_v = p_scale(v, -1, p)
        _, v_next = p_divrem(neg_v, u_next, p)

        u, v = u_next, v_next
    end

    return u, v
end

function cantor_mul(u::Vector{Int}, v::Vector{Int}, n::Int, f::Vector{Int}, p::Int)
    if n <= 0
        throw(DomainError(n, "Scalar n must be a positive integer"))
    end

    curr_u, curr_v = u, v
    res_u, res_v = Int[], Int[]
    for b in reverse(digits(n, base=2))
        if !isempty(res_u)
            res_u, res_v = cantor_add(res_u, res_v, res_u, res_v, f, p)
        end
        if b == 1
            if isempty(res_u)
                res_u, res_v = curr_u, curr_v
            else
                res_u, res_v = cantor_add(res_u, res_v, curr_u, curr_v, f, p)
            end
        end
    end
    return res_u, res_v
end

"""
    cantor_neg(u,v,p) -> (u,v)

Hyperelliptic-involution negation: -D for D=(u,v) is (u,-v mod u).
"""
function cantor_neg(u::Vector{Int}, v::Vector{Int}, p::Int)
    return u, p_scale(v, -1, p)
end

"""
    point_divisor(x0::Int, f::Vector{Int}, p::Int) -> (u,v)

Degree-1 reduced Mumford divisor for the affine point (x0, y0) with
y0^2 = f(x0) mod p: u(x) = x - x0, v(x) = y0 (constant). Searches for a
valid y0 by trying successive x0 starting at the given seed until f(x0)
is a nonzero QR mod p (avoids ramification points / non-existent
points), returning both the chosen x0 and y0 so callers can build (a,wa)
style anchors directly.
"""
function point_on_curve(x0_seed::Int, f::Vector{Int}, p::Int)
    x0 = mod(x0_seed, p)
    for _ in 0:p-1
        fx = mod(f[1] + f[2]*x0 + f[3]*powermod(x0,2,p) + f[4]*powermod(x0,3,p) +
                  f[5]*powermod(x0,4,p) + f[6]*powermod(x0,5,p), p)
        if fx != 0
            y0 = sqrt_modp(fx, p)
            if y0 !== nothing
                return x0, y0
            end
        end
        x0 = mod(x0 + 1, p)
    end
    error("point_on_curve: no valid point found starting from seed $x0_seed")
end

"""
    sqrt_modp(a, p) -> Union{Int,Nothing}

Modular square root via exhaustive Tonelli-Shanks-free search is too slow
for p ~ 2.37e6 only if done naively per call many times; here we use the
standard square-and-test via Julia's own powermod for the p ≡ 3 (mod 4)
fast path, falling back to a short Tonelli-Shanks otherwise. Returns
`nothing` if `a` is a non-residue.
"""
function sqrt_modp(a::Int, p::Int)
    a = mod(a, p)
    a == 0 && return 0
    # Euler's criterion
    if powermod(a, div(p - 1, 2), p) != 1
        return nothing
    end
    if mod(p, 4) == 3
        r = powermod(a, div(p + 1, 4), p)
        return mod(r * r, p) == a ? r : nothing
    end
    # Tonelli-Shanks (general case)
    q, s = p - 1, 0
    while iseven(q)
        q = div(q, 2)
        s += 1
    end
    z = 2
    while powermod(z, div(p - 1, 2), p) != p - 1
        z += 1
    end
    m = s
    c = powermod(z, q, p)
    t = powermod(a, q, p)
    r = powermod(a, div(q + 1, 2), p)
    while t != 1
        i, temp = 0, t
        while temp != 1
            temp = mod(temp * temp, p)
            i += 1
            i == m && return nothing
        end
        b = powermod(c, 1 << (m - i - 1), p)
        m = i
        c = mod(b * b, p)
        t = mod(t * c, p)
        r = mod(r * b, p)
    end
    return r
end

function point_divisor(x0::Int, y0::Int)
    return Int[mod(-x0, P_MOD), 1], Int[mod(y0, P_MOD)]
end

"""
    curve_residual(x, w, p) -> Int

wa^2 - (a^5+a+2) mod p -- one of the 4 curve-relation residuals in the
12-equation system. Uses powermod (not native ^) for x^5/w^2: x,w can be
up to p-1 ~ 2.37e6, so x^5 ~ 10^32, which silently OVERFLOWS Julia's
64-bit Int (wraps around with NO error) if computed natively before
reducing mod p. Every curve-degree evaluation in this file routes through
powermod for exactly this reason.
"""
function curve_residual(x::Int, w::Int, p::Int)
    x5 = powermod(x, 5, p)
    return mod(powermod(w, 2, p) - (x5 + x + 2), p)
end

# ---------------------------------------------------------------------------
# alpha*G-style helper (generator G is fixed -- "a" in P1+P2-alpha*a).
# ---------------------------------------------------------------------------

const uG, vG = U_G, V_G

# ---------------------------------------------------------------------------
# Left side: reduce(P1 + P2 - alpha*a)  = cantor_add(P1,P2) + (-alpha*G)
# Right side: reduce(P3 + P4 - alpha'*a) = cantor_add(P3,P4) + (-alpha'*G)
# ---------------------------------------------------------------------------

function lhs_divisor(a1, wa1, a2, wa2, alpha_val, u_aG_, v_aG_)
    uP1, vP1 = point_divisor(a1, wa1)
    uP2, vP2 = point_divisor(a2, wa2)
    u12, v12 = cantor_add(uP1, vP1, uP2, vP2, F_POLY, P_MOD)
    u_neg_aG, v_neg_aG = cantor_neg(u_aG_, v_aG_, P_MOD)
    return cantor_add(u12, v12, u_neg_aG, v_neg_aG, F_POLY, P_MOD)
end

# Pad Mumford coords to (U0,U1,V0,V1) form (degree <=2 monic u, degree <=1 v);
# a degree-1 (or degree-0) reduced divisor is still valid -- pad with zeros
# in the "missing" leading slot the way extract_coords in SampleSpecs does.
function extract_UV(u::Vector{Int}, v::Vector{Int})
    # u should be monic degree <=2: [u0,u1,1] (deg2), [u0,1] (deg1), [1] (deg0/zero divisor)
    U0 = length(u) >= 1 ? u[1] : 0
    U1 = length(u) >= 2 ? u[2] : 0
    V0 = length(v) >= 1 ? v[1] : 0
    V1 = length(v) >= 2 ? v[2] : 0
    return U0, U1, V0, V1
end

"""
    split_degree2_divisor(u,v,p) -> Union{NTuple{2,Tuple{Int,Int}},Nothing}

Given a reduced degree-2 Mumford divisor (u,v) with u(x)=x^2+u1*x+u0 monic,
split it into its two points (b1,wb1),(b2,wb2) by solving u(x)=0 via the
quadratic formula mod p and evaluating v(x) at each root. Returns
`nothing` if u does not have two DISTINCT roots over F_p (discriminant a
zero/non-residue) -- caller retries with a different alpha'.
"""
function split_degree2_divisor(u::Vector{Int}, v::Vector{Int}, p::Int)
    (length(u) != 3 || u[3] != 1) && return nothing
    u0, u1 = u[1], u[2]
    disc = mod(u1*u1 - 4*u0, p)
    disc == 0 && return nothing
    sq = sqrt_modp(disc, p)
    sq === nothing && return nothing
    inv2 = invmod(2, p)
    r1 = mod((-u1 + sq) * inv2, p)
    r2 = mod((-u1 - sq) * inv2, p)
    veval(x) = mod(sum(c * powermod(x, i-1, p) for (i, c) in enumerate(v)), p)
    return (r1, veval(r1)), (r2, veval(r2))
end

function try_solve_P3P4(alphap_try::Int, D_u, D_v)
    # E = D + alpha'*G ; need P3+P4 = E (a degree-2 reduced divisor) so
    # that reduce(P3+P4-alpha'*a) = D exactly.
    u_apG_try, v_apG_try = cantor_mul(uG, vG, alphap_try, F_POLY, P_MOD)
    u_E, v_E = cantor_add(D_u, D_v, u_apG_try, v_apG_try, F_POLY, P_MOD)
    split = split_degree2_divisor(u_E, v_E, P_MOD)
    split === nothing && return nothing
    (b1_try, wb1_try), (b2_try, wb2_try) = split
    if curve_residual(b1_try, wb1_try, P_MOD) == 0 && curve_residual(b2_try, wb2_try, P_MOD) == 0
        return b1_try, wb1_try, b2_try, wb2_try
    end
    return nothing
end

function shifted_lhs_divisor(a1, wa1, a2, wa2, alpha_val, u_aG_, v_aG_, u_T_, v_T_)
    uP1, vP1 = point_divisor(a1, wa1)
    uP2, vP2 = point_divisor(a2, wa2)
    u12, v12 = cantor_add(uP1, vP1, uP2, vP2, F_POLY, P_MOD)
    # T + (P1+P2)
    u_Tsum, v_Tsum = cantor_add(u_T_, v_T_, u12, v12, F_POLY, P_MOD)
    u_neg_aG, v_neg_aG = cantor_neg(u_aG_, v_aG_, P_MOD)
    return cantor_add(u_Tsum, v_Tsum, u_neg_aG, v_neg_aG, F_POLY, P_MOD)
end

# ---------------------------------------------------------------------------
# Explicit check of all 12 equations, in the exact unknown order used by
# nid_fiber_system.jl: (wa1,wa2,wb1,wb2,a2,a1,b2,b1,U0,U1,V0,V1).
#
#   eq1  curve_a1 = wa1^2 - (a1^5+a1+2)
#   eq2  curve_a2 = wa2^2 - (a2^5+a2+2)
#   eq3  curve_b1 = wb1^2 - (b1^5+b1+2)
#   eq4  curve_b2 = wb2^2 - (b2^5+b2+2)
#   eq5  Fu_a[1]  = U0 - U0(reduce(P1+P2-alpha*a))
#   eq6  Fu_a[2]  = U1 - U1(reduce(P1+P2-alpha*a))
#   eq7  Fv_a[1]  = V0 - V0(reduce(P1+P2-alpha*a))
#   eq8  Fv_a[2]  = V1 - V1(reduce(P1+P2-alpha*a))
#   eq9  Fu_b[1]  = U0 - U0(reduce(P3+P4-alpha'*a))     [T=0]
#                 = U0 - U0(reduce(T+P3+P4-alpha'*a))   [T given]
#   eq10 Fu_b[2]  = analogous U1
#   eq11 Fv_b[1]  = analogous V0
#   eq12 Fv_b[2]  = analogous V1
#
# (U0,U1,V0,V1) unknowns are pinned to the COMMON value the (shifted or
# unshifted) relation forces. Pass `shift = (u_T,v_T)` to check the
# T-shifted variant, or `shift = nothing` for the unshifted base relation.
# All 12 residuals should be 0 mod p either way.
# ---------------------------------------------------------------------------

function check_12_equations(a1, wa1, a2, wa2, b1, wb1, b2, wb2,
                             alpha_val, alphap_val, U0, U1, V0, V1;
                             shift = nothing, verbose::Bool = false)
    residuals = Dict{String,Int}()
    residuals["curve_a1"] = curve_residual(a1, wa1, P_MOD)
    residuals["curve_a2"] = curve_residual(a2, wa2, P_MOD)
    residuals["curve_b1"] = curve_residual(b1, wb1, P_MOD)
    residuals["curve_b2"] = curve_residual(b2, wb2, P_MOD)

    u_aG_, v_aG_ = cantor_mul(uG, vG, alpha_val, F_POLY, P_MOD)
    u_apG_, v_apG_ = cantor_mul(uG, vG, alphap_val, F_POLY, P_MOD)

    if shift === nothing
        Ua, Va = lhs_divisor(a1, wa1, a2, wa2, alpha_val, u_aG_, v_aG_)
        Ub, Vb = lhs_divisor(b1, wb1, b2, wb2, alphap_val, u_apG_, v_apG_)
    else
        u_T_, v_T_ = shift
        Ua, Va = shifted_lhs_divisor(a1, wa1, a2, wa2, alpha_val, u_aG_, v_aG_, u_T_, v_T_)
        Ub, Vb = shifted_lhs_divisor(b1, wb1, b2, wb2, alphap_val, u_apG_, v_apG_, u_T_, v_T_)
    end
    Ua0, Ua1, Va0, Va1 = extract_UV(Ua, Va)
    Ub0, Ub1, Vb0, Vb1 = extract_UV(Ub, Vb)

    residuals["Fu_a[1] (U0 side)"] = mod(U0 - Ua0, P_MOD)
    residuals["Fu_a[2] (U1 side)"] = mod(U1 - Ua1, P_MOD)
    residuals["Fv_a[1] (V0 side)"] = mod(V0 - Va0, P_MOD)
    residuals["Fv_a[2] (V1 side)"] = mod(V1 - Va1, P_MOD)
    residuals["Fu_b[1] (U0 side)"] = mod(U0 - Ub0, P_MOD)
    residuals["Fu_b[2] (U1 side)"] = mod(U1 - Ub1, P_MOD)
    residuals["Fv_b[1] (V0 side)"] = mod(V0 - Vb0, P_MOD)
    residuals["Fv_b[2] (V1 side)"] = mod(V1 - Vb1, P_MOD)

    all_zero = all(r == 0 for r in values(residuals))
    if verbose
        for (label, r) in residuals
            status = r == 0 ? "OK  " : "FAIL"
            println("    [$status] $label residual = $r")
        end
    end
    return all_zero
end

# ---------------------------------------------------------------------------
# ONE TRIAL: constructs a fresh base solution (P1,P2,alpha,P3,P4,alpha'),
# verifies it against the 12-equation system, applies a fresh random
# translation T = k*G, and verifies the shifted solution too. Returns a
# NamedTuple of booleans/attempt-count so the driving loop can tally
# results without re-printing everything per trial (pass verbose=true to
# print full detail for a given trial, e.g. the first one).
# ---------------------------------------------------------------------------

function run_one_trial(rng, trial_idx::Int; verbose::Bool = false)
    a1, wa1 = point_on_curve(rand(rng, 1:1_000_000), F_POLY, P_MOD)
    a2, wa2 = point_on_curve(rand(rng, 1:1_000_000), F_POLY, P_MOD)
    alpha  = rand(rng, 2:100_000)

    @assert curve_residual(a1, wa1, P_MOD) == 0
    @assert curve_residual(a2, wa2, P_MOD) == 0

    u_aG, v_aG = cantor_mul(uG, vG, alpha, F_POLY, P_MOD)
    D_target_u, D_target_v = lhs_divisor(a1, wa1, a2, wa2, alpha, u_aG, v_aG)

    # Solve for (P3,P4,alpha') satisfying (*) exactly, by construction --
    # see the long note in the file header for why this beats drawing
    # (P1,P2,P3,P4) all independently at random (relation (*) would then
    # essentially never hold). Splits E=D+alpha'*G into two points; this
    # succeeds roughly half the time per attempt (a random monic quadratic
    # over F_p has two distinct roots with probability -> 1/2), so 500
    # attempts fail with probability ~0.5^500 -- not a real concern.
    alphap = rand(rng, 2:100_000)
    result = try_solve_P3P4(alphap, D_target_u, D_target_v)
    attempt = 1
    while result === nothing && attempt < 500
        alphap = rand(rng, 2:100_000)
        result = try_solve_P3P4(alphap, D_target_u, D_target_v)
        attempt += 1
    end
    result === nothing &&
        error("Trial $trial_idx: failed to solve for P3,P4 after 500 attempts " *
              "(this should be astronomically unlikely -- investigate if it happens).")
    b1, wb1, b2, wb2 = result

    u_apG, v_apG = cantor_mul(uG, vG, alphap, F_POLY, P_MOD)
    U_rhs, V_rhs = lhs_divisor(b1, wb1, b2, wb2, alphap, u_apG, v_apG)
    U0_rhs, U1_rhs, V0_rhs, V1_rhs = extract_UV(U_rhs, V_rhs)
    U0_lhs, U1_lhs, V0_lhs, V1_lhs = extract_UV(D_target_u, D_target_v)
    base_relation_holds = (U0_lhs, U1_lhs, V0_lhs, V1_lhs) == (U0_rhs, U1_rhs, V0_rhs, V1_rhs)

    if verbose
        println("  P1=(", a1, ",", wa1, ") P2=(", a2, ",", wa2, ") alpha=", alpha)
        println("  P3=(", b1, ",", wb1, ") P4=(", b2, ",", wb2, ") alpha'=", alphap,
                "  [", attempt, " attempt(s) to solve]")
        println("  D (both sides) = (U0,U1,V0,V1) = (",
                U0_lhs, ", ", U1_lhs, ", ", V0_lhs, ", ", V1_lhs, ")")
        println("  Relation (*) holds: ", base_relation_holds)
    end

    base_ok = check_12_equations(a1, wa1, a2, wa2, b1, wb1, b2, wb2,
                                  alpha, alphap, U0_lhs, U1_lhs, V0_lhs, V1_lhs;
                                  shift = nothing, verbose = verbose)

    # Shifted solution: T = k*G for fresh random k.
    k = rand(rng, 2:100_000)
    u_T, v_T = cantor_mul(uG, vG, k, F_POLY, P_MOD)

    U_lhs_shift, V_lhs_shift = shifted_lhs_divisor(a1, wa1, a2, wa2, alpha, u_aG, v_aG, u_T, v_T)
    U_rhs_shift, V_rhs_shift = shifted_lhs_divisor(b1, wb1, b2, wb2, alphap, u_apG, v_apG, u_T, v_T)
    U0ls, U1ls, V0ls, V1ls = extract_UV(U_lhs_shift, V_lhs_shift)
    U0rs, U1rs, V0rs, V1rs = extract_UV(U_rhs_shift, V_rhs_shift)
    shifted_relation_holds = (U0ls, U1ls, V0ls, V1ls) == (U0rs, U1rs, V0rs, V1rs)

    if verbose
        println("  T = ", k, "*G")
        println("  Shifted D (both sides) = (U0,U1,V0,V1) = (",
                U0ls, ", ", U1ls, ", ", V0ls, ", ", V1ls, ")")
        println("  Base D != Shifted D (nontrivial shift): ",
                (U0_lhs,U1_lhs,V0_lhs,V1_lhs) != (U0ls,U1ls,V0ls,V1ls))
        println("  Relation (**) holds: ", shifted_relation_holds)
    end

    shift_ok = check_12_equations(a1, wa1, a2, wa2, b1, wb1, b2, wb2,
                                   alpha, alphap, U0ls, U1ls, V0ls, V1ls;
                                   shift = (u_T, v_T), verbose = verbose)

    return (base_ok = base_ok, base_relation_holds = base_relation_holds,
            shift_ok = shift_ok, shifted_relation_holds = shifted_relation_holds,
            attempts = attempt, nontrivial_shift = (U0_lhs,U1_lhs,V0_lhs,V1_lhs) != (U0ls,U1ls,V0ls,V1ls))
end

# ---------------------------------------------------------------------------
# DRIVER: run N independent trials and tally results.
# ---------------------------------------------------------------------------

const N_TRIALS = 1000
const VERBOSE_FIRST_K = 3   # print full per-equation detail for the first K trials

println("=" ^ 78)
println("Running ", N_TRIALS, " independent trials of the translation-invariance")
println("test on y^2 = x^5+x+2 mod ", P_MOD, " (genus-2 Jacobian, Cantor's algorithm)")
println("=" ^ 78)
println()

rng = Random.MersenneTwister(SEED)

n_base_ok = 0
n_base_relation = 0
n_shift_ok = 0
n_shift_relation = 0
n_nontrivial_shift = 0
total_attempts = 0
failures = Tuple{Int,NamedTuple}[]

for trial in 1:N_TRIALS
    verbose = trial <= VERBOSE_FIRST_K
    if verbose
        println("-" ^ 78)
        println("Trial ", trial, " (verbose)")
        println("-" ^ 78)
    end

    r = run_one_trial(rng, trial; verbose = verbose)

    global n_base_ok += Int(r.base_ok)
    global n_base_relation += Int(r.base_relation_holds)
    global n_shift_ok += Int(r.shift_ok)
    global n_shift_relation += Int(r.shifted_relation_holds)
    global n_nontrivial_shift += Int(r.nontrivial_shift)
    global total_attempts += r.attempts

    if !(r.base_ok && r.base_relation_holds && r.shift_ok && r.shifted_relation_holds)
        push!(failures, (trial, r))
    end

    if verbose
        println("  Trial ", trial, " summary: base_ok=", r.base_ok,
                " base_relation=", r.base_relation_holds,
                " shift_ok=", r.shift_ok,
                " shift_relation=", r.shifted_relation_holds)
        println()
    end

    if trial % 100 == 0 && trial > VERBOSE_FIRST_K
        println("  ... completed ", trial, "/", N_TRIALS, " trials (",
                length(failures), " failure(s) so far)")
    end
end

println()
println("=" ^ 78)
println("FINAL SUMMARY over ", N_TRIALS, " trials")
println("=" ^ 78)
println("Base solution satisfies all 12 equations:      ", n_base_ok, " / ", N_TRIALS)
println("Base solution satisfies relation (*):           ", n_base_relation, " / ", N_TRIALS)
println("Shifted solution satisfies all 12 equations:    ", n_shift_ok, " / ", N_TRIALS)
println("Shifted solution satisfies relation (**):       ", n_shift_relation, " / ", N_TRIALS)
println("Trials where T actually changed the divisor D:  ", n_nontrivial_shift, " / ", N_TRIALS,
        " (shift was nontrivial, so this isn't a vacuous check)")
println("Average P3/P4-solve attempts per trial:         ", round(total_attempts / N_TRIALS, digits=2))
println("Failures: ", length(failures))
println()

if isempty(failures)
    println("CONFIRMED across all ", N_TRIALS, " trials: translating both sides of")
    println("the defining relation by a common Jacobian element T")
    println("(P1+P2 -> T+P1+P2, P3+P4 -> T+P3+P4) produces ANOTHER solution of the")
    println("same 12-equation fiber system, numerically verified mod p = ", P_MOD, ".")
else
    println("NOT CONFIRMED for ", length(failures), " trial(s):")
    for (trial, r) in failures
        println("  Trial ", trial, ": ", r)
    end
end
