"""
Genus-2 hyperelliptic curve arithmetic over F_p.

Ported from trial1_autoell_p10.jl (Cantor's algorithm on the Jacobian,
Mumford representation, Tonelli-Shanks sqrt, Frobenius point counting,
BSGS order-finding, and cryptographic-subgroup generator search).

Curve: C : y^2 = f(x) = x^5 + x + 2   over F_p  (default, matches the
Julia reference's F_POLY = [2, 1, 0, 0, 0, 1]).

Divisors on the genus-2 Jacobian are represented in Mumford form as a
pair of polynomials (u, v) with u monic of degree <= 2 and deg(v) < deg(u),
satisfying v(x)^2 ≡ f(x) (mod u(x)). We represent u as a length-3 tuple
(c0, c1, c2) meaning u(x) = c0 + c1*x + c2*x^2, and v as (c0, c1).
The identity element is u = (1, 0, 0), v = (0, 0).
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Optional, Sequence
import random

try:
    from sympy import isprime, nextprime, factorint
except ImportError as e:  # pragma: no cover
    raise ImportError(
        "This module requires sympy (pip install sympy --break-system-packages)"
    ) from e


# Default curve: y^2 = x^5 + x + 2
DEFAULT_F_POLY = (2, 1, 0, 0, 0, 1)  # coeff[i] = coefficient of x^i


# ============================================================
#  F_p scalar helpers
# ============================================================

def fp(x: int, p: int) -> int:
    return x % p


def fp_inv(a: int, p: int) -> int:
    a %= p
    if a == 0:
        raise ZeroDivisionError("attempted inversion of zero modulo p")
    return pow(a, -1, p)


def sqrt_fp(a: int, p: int) -> Optional[int]:
    """Tonelli-Shanks. Returns a root r with r^2 == a (mod p), or None if a
    is a non-residue. Mirrors sqrt_fp in the Julia reference."""
    a = a % p
    if a == 0:
        return 0
    if pow(a, (p - 1) // 2, p) != 1:
        return None
    if p % 4 == 3:
        r = pow(a, (p + 1) // 4, p)
        return r if (r * r) % p == a else None
    # Tonelli-Shanks for p == 1 (mod 4)
    q, s = p - 1, 0
    while q % 2 == 0:
        q //= 2
        s += 1
    z = 2
    while pow(z, (p - 1) // 2, p) != p - 1:
        z += 1
    m = s
    c = pow(z, q, p)
    t = pow(a, q, p)
    r = pow(a, (q + 1) // 2, p)
    while True:
        if t == 1:
            return r
        i, tmp = 1, (t * t) % p
        while tmp != 1:
            tmp = (tmp * tmp) % p
            i += 1
        b = pow(c, 1 << (m - i - 1), p)
        m = i
        c = (b * b) % p
        t = (t * c) % p
        r = (r * b) % p


# ============================================================
#  Curve
# ============================================================

class Curve:
    """C : y^2 = f(x), f given by f_poly (coeff[i] = coeff of x^i), over F_p."""

    def __init__(self, p: int, f_poly: Sequence[int] = DEFAULT_F_POLY):
        self.p = p
        self.f_poly = tuple(c % p for c in f_poly)
        if len(self.f_poly) != 6 or self.f_poly[5] == 0:
            raise ValueError("f_poly must be a degree-5 polynomial (6 coeffs, leading != 0)")

    def eval_f(self, x: int) -> int:
        return self._horner(x)

    def _horner(self, x: int) -> int:
        p = self.p
        acc = 0
        for c in reversed(self.f_poly):
            acc = (acc * x + c) % p
        return acc

    def is_on_curve(self, x: int, y: int) -> bool:
        return (y * y) % self.p == self.eval_f(x)


# ============================================================
#  Mumford divisors + Cantor's algorithm (genus 2)
# ============================================================

@dataclass(frozen=True)
class Div2:
    """Mumford representation of a genus-2 reduced divisor.
    u: (c0, c1, c2) with u(x) = c0 + c1 x + c2 x^2 (monic: c2 in {0,1})
    v: (c0, c1)     with v(x) = c0 + c1 x
    """
    u: tuple
    v: tuple


def _identity() -> Div2:
    return Div2((1, 0, 0), (0, 0))


def jac_identity() -> Div2:
    return _identity()


def jac_is_identity(D: Div2) -> bool:
    return D.u[1] == 0 and D.u[2] == 0


# ---- polynomial helpers over F_p (arbitrary degree, list-of-coeffs, low->high)

def _ptrim(a):
    a = list(a)
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a


def _pdeg(a):
    a = _ptrim(a)
    return len(a) - 1


def _padd(a, b, p):
    n = max(len(a), len(b))
    a = a + [0] * (n - len(a))
    b = b + [0] * (n - len(b))
    return _ptrim([(x + y) % p for x, y in zip(a, b)])


def _psub(a, b, p):
    n = max(len(a), len(b))
    a = a + [0] * (n - len(a))
    b = b + [0] * (n - len(b))
    return _ptrim([(x - y) % p for x, y in zip(a, b)])


def _pmul(a, b, p):
    if a == [0] or b == [0]:
        return [0]
    res = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        if ai == 0:
            continue
        for j, bj in enumerate(b):
            res[i + j] = (res[i + j] + ai * bj) % p
    return _ptrim(res)


def _pscale(a, s, p):
    return _ptrim([(x * s) % p for x in a])


def _pdivrem(a, b, p):
    """Polynomial division a = q*b + r over F_p. b must be nonzero."""
    a = _ptrim(list(a))
    b = _ptrim(list(b))
    if b == [0]:
        raise ZeroDivisionError("pdivrem: division by zero polynomial")
    if _pdeg(a) < _pdeg(b):
        return [0], a
    inv_lead = fp_inv(b[-1], p)
    rem = list(a)
    q = [0] * (len(a) - len(b) + 1)
    while _pdeg(rem) >= _pdeg(b) and rem != [0]:
        d = _pdeg(rem) - _pdeg(b)
        coeff = (rem[-1] * inv_lead) % p
        q[d] = coeff
        # rem -= coeff * x^d * b
        sub = [0] * d + _pscale(b, coeff, p)
        rem = _psub(rem, sub, p)
        rem = _ptrim(rem)
        if rem == [0]:
            break
    return _ptrim(q), _ptrim(rem)


def _pgcd_ext(a0, b0, p):
    """Extended Euclid: returns (g, s, t) with s*a0 + t*b0 = g, g monic."""
    r0, r1 = _ptrim(list(a0)), _ptrim(list(b0))
    s0, s1 = [1], [0]
    t0, t1 = [0], [1]
    while r1 != [0]:
        q, r = _pdivrem(r0, r1, p)
        r0, r1 = r1, r
        s0, s1 = s1, _psub(s0, _pmul(q, s1, p), p)
        t0, t1 = t1, _psub(t0, _pmul(q, t1, p), p)
    if r0 == [0]:
        raise ArithmeticError("pgcd_ext: gcd collapsed to zero polynomial")
    sc = fp_inv(r0[-1], p)
    return _pscale(r0, sc, p), _pscale(s0, sc, p), _pscale(t0, sc, p)


def _u_to_poly(u):
    # u = (c0,c1,c2) -> trimmed list
    return _ptrim(list(u))


def _v_to_poly(v):
    return _ptrim(list(v))


def _to_fp3(a, p):
    a = _ptrim(list(a))
    a = a + [0] * (3 - len(a))
    return (a[0] % p, a[1] % p, a[2] % p)


def _to_fp2(a, p):
    a = _ptrim(list(a))
    a = a + [0] * (2 - len(a))
    return (a[0] % p, a[1] % p)


def _f_as_list(curve: Curve):
    return list(curve.f_poly)


def jac_add(D1: Div2, D2: Div2, curve: Curve) -> Div2:
    """Cantor composition + reduction on the genus-2 Jacobian.
    General-purpose (heap-poly) version — always correct, ported from
    _jac_add_degenerate in the Julia reference so we don't need the
    fast-path degree bookkeeping. Correctness over speed for this project."""
    p = curve.p
    f = _f_as_list(curve)

    u1, v1 = _u_to_poly(D1.u), _v_to_poly(D1.v)
    u2, v2 = _u_to_poly(D2.u), _v_to_poly(D2.v)

    # Step 1: d1 = gcd(u1, u2) = e1*u1 + e2*u2
    d1, e1, e2 = _pgcd_ext(u1, u2, p)

    # Step 2: d = gcd(d1, v1+v2) = c1*d1 + c2*(v1+v2)
    vsum = _padd(v1, v2, p)
    if vsum == [0]:
        d, c1_, c2_ = d1, [1], [0]
    else:
        d, c1_, c2_ = _pgcd_ext(d1, vsum, p)

    # s1 = c1_*e1, s2 = c1_*e2, s3 = c2_  s.t. d = s1*u1 + s2*u2 + s3*(v1+v2)
    s1 = _pmul(c1_, e1, p)
    s2 = _pmul(c1_, e2, p)
    s3 = c2_

    # u = u1*u2 / d^2
    u1u2 = _pmul(u1, u2, p)
    d2 = _pmul(d, d, p)
    u_new, rem = _pdivrem(u1u2, d2, p)
    if rem != [0]:
        raise ArithmeticError("jac_add: u1*u2 not divisible by d^2 (invalid divisor input)")

    # v = (s1*u1*v2 + s2*u2*v1 + s3*(v1*v2 + f)) / d  mod u_new
    term1 = _pmul(s1, _pmul(u1, v2, p), p)
    term2 = _pmul(s2, _pmul(u2, v1, p), p)
    term3 = _pmul(s3, _padd(_pmul(v1, v2, p), f, p), p)
    numer = _padd(_padd(term1, term2, p), term3, p)
    v_raw, rem2 = _pdivrem(numer, d, p)
    if rem2 != [0]:
        raise ArithmeticError("jac_add: v numerator not divisible by d (invalid divisor input)")
    if _pdeg(u_new) > 0:
        _, v_raw = _pdivrem(v_raw, u_new, p)

    # Reduction: repeat until deg(u) <= 2 (genus 2)
    u_cur, v_cur = u_new, v_raw
    guard = 0
    while _pdeg(u_cur) > 2:
        guard += 1
        if guard > 20:
            raise ArithmeticError("jac_add: reduction did not converge")
        # u' = (f - v^2) / u   (monic-normalized)
        v2poly = _pmul(v_cur, v_cur, p)
        fmv2 = _psub(f, v2poly, p)
        u_next, rem3 = _pdivrem(fmv2, u_cur, p)
        if rem3 != [0]:
            raise ArithmeticError("jac_add: reduction division had nonzero remainder")
        # make monic
        if u_next != [0] and u_next[-1] != 1:
            inv_lead = fp_inv(u_next[-1], p)
            u_next = _pscale(u_next, inv_lead, p)
        # v' = (-v) mod u_next
        v_neg = _pscale(v_cur, p - 1, p)
        if _pdeg(u_next) > 0:
            _, v_next = _pdivrem(v_neg, u_next, p)
        else:
            v_next = [0]
        u_cur, v_cur = u_next, v_next

    # normalize u_cur to monic degree <=2 tuple form
    if u_cur == [0]:
        u_cur = [1]
    if u_cur[-1] != 1 and u_cur != [1]:
        inv_lead = fp_inv(u_cur[-1], p)
        u_cur = _pscale(u_cur, inv_lead, p)

    # Final canonicalization: v must always be reduced mod u (in particular,
    # when deg(u) == 0 the divisor is the identity and v must be [0] — the
    # main reduction loop above only fires for deg(u) > 2, so deg(u) in
    # {0,1} cases need this explicit reduce here).
    if _pdeg(u_cur) == 0:
        v_cur = [0]
    elif _pdeg(v_cur) >= _pdeg(u_cur):
        _, v_cur = _pdivrem(v_cur, u_cur, p)

    return Div2(_to_fp3(u_cur, p), _to_fp2(v_cur, p))


def jac_mul(D: Div2, n: int, curve: Curve) -> Div2:
    """n * D via double-and-add."""
    n = int(n)
    if n == 0:
        return _identity()
    if n < 0:
        # -D: negate v
        D = Div2(D.u, tuple((-c) % curve.p for c in D.v))
        n = -n
    R = _identity()
    Q = D
    while n > 0:
        if n & 1:
            R = jac_add(R, Q, curve)
        n >>= 1
        if n > 0:
            Q = jac_add(Q, Q, curve)
    return R


def mumford1(x0: int, y0: int, curve: Curve) -> Div2:
    p = curve.p
    return Div2((((-x0) % p), 1, 0), (y0 % p, 0))


def mumford2(x1: int, y1: int, x2: int, y2: int, curve: Curve) -> Div2:
    p = curve.p
    if x1 == x2:
        raise ValueError("mumford2: x1 == x2; use mumford_from_pts")
    u = [(x1 * x2) % p, (-(x1 + x2)) % p, 1]
    sl = ((y2 - y1) % p) * fp_inv((x2 - x1) % p, p) % p
    v = _ptrim([(y1 - sl * x1) % p, sl])
    return Div2(_to_fp3(u, p), _to_fp2(v, p))


def mumford_from_pts(P: tuple, Q: tuple, curve: Curve) -> Div2:
    x1, y1 = P
    x2, y2 = Q
    p = curve.p
    if x1 == x2 and y2 == (-y1) % p:
        return _identity()
    if x1 == x2:
        return jac_add(mumford1(x1, y1, curve), mumford1(x2, y2, curve), curve)
    return mumford2(x1, y1, x2, y2, curve)


def u2_roots(u: tuple, curve: Curve) -> Optional[tuple]:
    """For a degree-2 monic Mumford u-poly (c0,c1,c2=1), return both F_p
    roots as (r1, r2), or None if it doesn't split (irreducible or not
    degree 2)."""
    p = curve.p
    if u[2] != 1 or (u[2] == 0):
        # not degree exactly 2 (either 0 -> identity, or degree <2 already handled elsewhere)
        pass
    if u[2] != 1:
        return None
    c0, c1 = u[0], u[1]
    disc = (c1 * c1 - 4 * c0) % p
    sq = sqrt_fp(disc, p)
    if sq is None:
        return None
    inv2 = fp_inv(2, p)
    r1 = ((-c1 + sq) % p) * inv2 % p
    r2 = ((-c1 - sq) % p) * inv2 % p
    return (r1, r2)


def mumford_v_eval(v: tuple, x: int, p: int) -> int:
    c0, c1 = v
    return (c0 + c1 * x) % p


def split_divisor_to_points(D: Div2, curve: Curve) -> Optional[tuple]:
    """If D's u-poly is degree 2 and splits over F_p, return the two
    (x, y) curve points ((x1,y1), (x2,y2)) with y_i = v(x_i). Else None.
    This is the Python analogue of checking 'does u(x) split' + reading
    off the resulting curve points, as used when building F."""
    roots = u2_roots(D.u, curve)
    if roots is None:
        return None
    p = curve.p
    x1, x2 = roots
    y1 = mumford_v_eval(D.v, x1, p)
    y2 = mumford_v_eval(D.v, x2, p)
    # sanity: points should lie on the curve
    return (x1, y1), (x2, y2)


# ============================================================
#  Point counting / subgroup search
# ============================================================

def next_prime_at_least(n: int) -> int:
    if n < 2:
        return 2
    return n if isprime(n) else nextprime(n - 1)


def jacobian_order_bsgs(D: Div2, curve: Curve) -> int:
    """Exact order of D via baby-step giant-step, bounded by the Hasse-Weil
    bound (#Jac <= (sqrt(p)+1)^4). Ported from jac_order_bsgs. Intended for
    modest p (a full O(sqrt(#Jac)) table); use jacobian_order_frobenius for
    larger p."""
    p = curve.p
    B = (int(p ** 0.5) + 2) ** 4
    m = int(B ** 0.5) + 1

    baby = {}
    cur = _identity()
    for j in range(m):
        if cur not in baby:
            baby[cur] = j
        cur = jac_add(cur, D, curve)

    step = cur  # m*D
    giant = step
    best = 0
    for i in range(1, m + 1):
        if giant in baby:
            j = baby[giant]
            cand = i * m - j
            if cand > 0 and (best == 0 or cand < best):
                best = cand
        giant = jac_add(giant, step, curve)

    if best == 0:
        raise ArithmeticError("jacobian_order_bsgs failed to find order within Hasse-Weil bound")

    # reduce to exact order by dividing out prime factors that still kill D
    order = best
    for prime, _mult in factorint(order).items():
        while order % prime == 0:
            if jac_is_identity(jac_mul(D, order // prime, curve)):
                order //= prime
            else:
                break
    return order


def jacobian_order_frobenius(curve: Curve) -> int:
    """Exact #Jac(C/F_p) via point counts N1 = #C(F_p), N2 = #C(F_{p^2})
    and the genus-2 zeta function relation. Ported from
    jacobian_order_frobenius in the Julia reference. O(p) time — fine for
    the small/demo primes this project targets; for larger p this should
    be replaced (e.g. with a smarter point-counting method)."""
    p = curve.p

    # N1 = #C(F_p) (including point at infinity)
    n1 = 1
    for x in range(p):
        fx = curve.eval_f(x)
        if fx == 0:
            n1 += 1
        elif pow(fx, (p - 1) // 2, p) == 1:
            n1 += 2

    # N2 = #C(F_{p^2}), via F_{p^2} = F_p[g]/(g^2 - g0) with g0 a QNR
    g0 = 2
    while pow(g0, (p - 1) // 2, p) != p - 1:
        g0 += 1

    c0, c1, c2, c3, c4, c5 = curve.f_poly
    n2_affine = 0
    for b in range(p):
        for a in range(p):
            # z = a + b*sqrt(g0); compute f(z) = r + i*sqrt(g0)
            # represent as (real, imag) coefficients under basis {1, sqrt(g0)}
            def cmul(x, y):
                # (x0+x1*g)*(y0+y1*g) = (x0y0+g0*x1y1) + (x0y1+x1y0)*g
                return (
                    (x[0] * y[0] + g0 * x[1] * y[1]) % p,
                    (x[0] * y[1] + x[1] * y[0]) % p,
                )

            def cadd(x, y):
                return ((x[0] + y[0]) % p, (x[1] + y[1]) % p)

            z = (a, b)
            # Horner
            acc = (0, 0)
            for c in (c5, c4, c3, c2, c1, c0):
                acc = cadd(cmul(acc, z), (c % p, 0))
            fr, fi = acc
            if fr == 0 and fi == 0:
                n2_affine += 2
                continue
            norm_f = (fr * fr - g0 * fi * fi) % p
            if norm_f != 0 and pow(norm_f, (p - 1) // 2, p) == 1:
                n2_affine += 4

    n2 = n1 + n2_affine + 1  # + point at infinity over F_{p^2}

    s1 = n1 - (p + 1)
    s2 = (s1 * s1 - (n2 - (p * p + 1))) // 2
    return 1 - s1 + s2 - p * s1 + p * p


def random_point(curve: Curve, rng: random.Random) -> tuple:
    p = curve.p
    while True:
        x = rng.randrange(p)
        fx = curve.eval_f(x)
        y = sqrt_fp(fx, p)
        if y is not None:
            return (x, y)


def random_divisor(curve: Curve, rng: random.Random) -> Div2:
    """A random (likely full-degree-2) reduced divisor, as the sum of two
    random affine points."""
    P = random_point(curve, rng)
    Q = random_point(curve, rng)
    return mumford_from_pts(P, Q, curve)


def _order_of_divisor(D: Div2, jac_order: int, curve: Curve) -> int:
    """Exact order of D, given that ord(D) divides jac_order. Starts from
    jac_order and repeatedly strips prime factors that still kill D --
    standard order-from-group-order-and-factorization technique. D must
    not be the identity (raises ValueError if it is, since order-of-identity
    is a degenerate/ambiguous case callers should filter out first)."""
    if jac_is_identity(D):
        raise ValueError("_order_of_divisor: D is the identity")
    order = jac_order
    for prime, mult in factorint(order).items():
        for _ in range(mult):
            if order % prime == 0 and jac_is_identity(jac_mul(D, order // prime, curve)):
                order //= prime
            else:
                break
    return order


def find_subgroup_generator(curve: Curve, rng: random.Random, jac_order: Optional[int] = None,
                             use_bsgs_order: bool = True):
    """Find a generator `a` of the largest-prime-order subgroup of the
    Jacobian, along with that prime order `ell` and cofactor `h`.
    Ported from find_ell_generator. If jac_order is provided (e.g. from
    jacobian_order_frobenius), uses the exact-cofactor fast path;
    otherwise derives order per-candidate via BSGS.

    NOTE: the target ell/h come from #Jac itself (the largest prime factor
    of jac_order), not from whichever random D we happen to draw -- a
    random D's own order is in general a proper divisor of jac_order, so
    we must compute D's true order before deciding how to scale it, or
    the ell-order subgroup element is never actually reached (this was a
    prior bug: assuming ord(D) == jac_order caused an infinite loop, since
    jac_mul(D, jac_order/ell) is not order-ell unless D happens to be a
    full generator)."""
    if jac_order is not None:
        target_factors = factorint(jac_order)
        target_ell = max(target_factors.keys())
        if target_ell <= 3:
            raise ValueError(
                f"jac_order={jac_order} has no prime factor > 3 (largest is "
                f"{target_ell}); no usable cryptographic subgroup exists for this curve"
            )
        target_h = jac_order // target_ell

    attempts = 0
    max_attempts = 10000
    while True:
        attempts += 1
        if attempts > max_attempts:
            raise RuntimeError(
                f"find_subgroup_generator: no generator found after {max_attempts} "
                "random divisors"
            )

        D = random_divisor(curve, rng)
        if jac_is_identity(D):
            continue

        if jac_order is not None:
            # D's own order divides jac_order but usually isn't jac_order itself.
            ord_D = _order_of_divisor(D, jac_order, curve)
            if ord_D % target_ell != 0:
                # D isn't in the order-ell subgroup at all; try another D.
                continue
            ell, h = target_ell, target_h
            # Scale D down to the order-ell subgroup: D has order ord_D with
            # target_ell | ord_D, so (ord_D/target_ell)*D has order target_ell.
            a = jac_mul(D, ord_D // target_ell, curve)
        elif use_bsgs_order:
            ord_D = jacobian_order_bsgs(D, curve)
            if ord_D <= 1:
                continue
            ell = max(factorint(ord_D).keys())
            if ell <= 3:
                continue
            h = ord_D // ell
            if h == 0:
                continue
            a = jac_mul(D, h, curve)
        else:
            raise ValueError("Must supply jac_order or use_bsgs_order=True")

        if jac_is_identity(a):
            continue
        if jac_is_identity(jac_mul(a, ell, curve)):
            return a, ell, h


def find_cryptographic_subgroup(p_start: int, f_poly: Sequence[int] = DEFAULT_F_POLY,
                                 min_bits: Optional[int] = None, rng: Optional[random.Random] = None,
                                 max_prime_tries: int = 50):
    """Cycle through primes p >= p_start until we find a curve/subgroup
    with cofactor as small as possible (i.e. #Jac itself is prime, or has
    a large prime factor ell with small cofactor h). Mirrors the project
    spec: 'cycle through primes until we find such a subgroup.'

    Returns (curve, generator a, ell, h, p).
    """
    if rng is None:
        rng = random.Random()

    p = next_prime_at_least(p_start)
    best = None
    for _ in range(max_prime_tries):
        curve = Curve(p, f_poly)
        jac_order = jacobian_order_frobenius(curve)
        factors = factorint(jac_order)
        ell = max(factors.keys())
        h = jac_order // ell
        if min_bits is None or ell.bit_length() >= min_bits:
            a, ell_confirmed, h_confirmed = find_subgroup_generator(
                curve, rng, jac_order=jac_order
            )
            return curve, a, ell_confirmed, h_confirmed, p
        p = next_prime_at_least(p + 1)
    raise RuntimeError(f"No suitable subgroup found after {max_prime_tries} primes starting at {p_start}")
