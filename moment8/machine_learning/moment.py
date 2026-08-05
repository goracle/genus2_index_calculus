"""
8th-moment scorer for a candidate set F of genus-2 Jacobian-curve points,
via direct group convolution.

Setup
-----
F is a set of curve points P = (x, y). The quantity we minimize is the
number of solutions (over 8 free indices P1..P8 in F) to

    P1 + P2 - P3 - P4 = P5 + P6 - P7 - P8

where "+"/"-" is Jacobian addition/subtraction (points are lifted to
Mumford form via mumford1 before combining). Define

    T(s) = #{(P,Q) in F^2 : P + Q = s}       (1_F * 1_F, the pair-sum
                                               histogram)
    C(g) = #{(P1,P2,P3,P4) in F^4 : P1+P2-P3-P4 = g}

Writing s = P1+P2, t = P3+P4, the constraint P1+P2-P3-P4=g is s-t=g, so

    C(g) = sum_h T(g+h) T(h)

i.e. C is the self cross-correlation of T (not T convolved against the
*difference* histogram 1_F*1_{-F} -- that different-looking but easily
confused object corresponds to P3-P4, not P3+P4, and does not compute
this equation; an earlier version of this module used it by mistake and
was caught by the brute-force check below, specifically because it gave
C(identity)=0 when the "P1=P4,P2=P3 swap" identity forces C(identity) to
be at least B^2 for any F of size B).

Then the original 8-index equation says the "left" quadruple (P1..P4) and
the "right" quadruple (P5..P8) hit the same g, so the total solution count
is

    E4(F) = sum_g C(g)^2

This is the honest 8-point / 8th-moment statistic. No discrete log is
needed -- T and C are indexed directly by Jacobian elements (hashable
Div2 tuples), not by residues mod the subgroup order ell.

Complexity: T is O(B^2) to build (at most B^2 nonzero entries). C is a
self-correlation of T, built as a sparse double loop over T's support:
O(supp(T)^2), worst case O(B^4) since supp(T) <= B^2. That's the intended
complexity class here -- far below the O(B^8) of literal 8-index
enumeration, and correctness against that literal enumeration is checked
below for small B.
"""

from __future__ import annotations

from collections import Counter
from typing import Sequence, Tuple

from curve import Curve, Div2, jac_add, mumford1


# ============================================================
#  Jacobian negation / subtraction
# ============================================================

def jac_negate(D: Div2, curve: Curve) -> Div2:
    """-D in Mumford form: same u, v -> -v mod p (mirrors the negation
    branch already used internally by jac_mul for negative scalars)."""
    p = curve.p
    return Div2(D.u, tuple((-c) % p for c in D.v))


def jac_sub(D1: Div2, D2: Div2, curve: Curve) -> Div2:
    return jac_add(D1, jac_negate(D2, curve), curve)


# ============================================================
#  Pair-sum histogram T = 1_F * 1_F
# ============================================================

Point = Tuple[int, int]


def pair_sum_histogram(lifted: Sequence[Div2], curve: Curve) -> Counter:
    """T(g) = #{(P,Q) in F^2 : P + Q = g}. O(B^2)."""
    T: Counter = Counter()
    for Di in lifted:
        for Dj in lifted:
            T[jac_add(Di, Dj, curve)] += 1
    return T


# ============================================================
#  Self-correlation C = T corr T,  and  E4(F) = sum_g C(g)^2
# ============================================================

def quad_histogram(points: Sequence[Point], curve: Curve) -> Counter:
    """Build C(g) = #{(P1,P2,P3,P4) in F^4 : P1+P2-P3-P4 = g}
    = sum_h T(g+h) T(h), the self cross-correlation of the pair-sum
    histogram T = 1_F*1_F (see module docstring for the derivation and
    why this is T-correlated-with-T, not T convolved with a difference
    histogram).

    O(supp(T)^2) group operations; supp(T) <= B^2, so worst case O(B^4)
    -- the right complexity class for this problem, versus O(B^8) for
    literal 8-index enumeration.
    """
    lifted = [mumford1(x, y, curve) for x, y in points]
    T = pair_sum_histogram(lifted, curve)

    # C(g) = sum over (s,t) in T x T with s - t = g, weighted by T(s)*T(t)
    C: Counter = Counter()
    for gs, cs in T.items():
        for gt, ct in T.items():
            g = jac_sub(gs, gt, curve)
            C[g] += cs * ct
    return C


def e4_from_quad_histogram(C: Counter) -> int:
    """sum_g C(g)^2."""
    return sum(count ** 2 for count in C.values())


def e4_moment(points: Sequence[Point], curve: Curve) -> int:
    """Convenience wrapper: build C = T corr T (T = 1_F*1_F) and sum its
    squared values -- the true 8-point / 8th-moment collision count for
    P1+P2-P3-P4 = P5+P6-P7-P8."""
    C = quad_histogram(points, curve)
    return e4_from_quad_histogram(C)


# ============================================================
#  Incremental state for greedy set construction
#
#  Rebuilding quad_histogram from scratch at every greedy step relifts
#  every point and rebuilds T = 1_F*1_F by an O(B^2) double loop just to
#  add one point -- wasteful when greedy only ever adds one point at a
#  time. IncrementalMoment instead maintains T directly: adding a point x
#  only requires O(|F|) new pair-sums (x with each existing point, plus
#  x+x), so T stays current in O(B) per step rather than O(B^2). C is
#  then rebuilt from the (cheaply updated) T at O(supp(T)^2) -- since
#  supp(T) <= B^2 stays small at the B ~ 10-20 scale here, this is fast
#  regardless, and this class avoids the O(B) relift-everything cost that
#  dominated the naive per-step call.
# ============================================================

class IncrementalMoment:
    """Maintains T = 1_F*1_F for a growing set F, supports cheap
    what-if scoring of F + {x} for candidate points x without mutating
    state, and cheap commit of the chosen addition."""

    def __init__(self, curve: Curve):
        self.curve = curve
        self.lifted: list = []       # Div2 elements currently in F
        self.T: Counter = Counter()  # pair-sum histogram of current F

    def _delta_for(self, Dx: Div2) -> Counter:
        """T_{F+{x}} - T_F, as a Counter, for candidate lift Dx. O(|F|)."""
        curve = self.curve
        delta: Counter = Counter()
        for Dp in self.lifted:
            s = jac_add(Dp, Dx, curve)
            delta[s] += 2  # P+x and x+P are the same sum, counted twice
        delta[jac_add(Dx, Dx, curve)] += 1  # x+x
        return delta

    def score_with(self, x: Point) -> int:
        """E4(F + {x}) without mutating state. O(|F|) to build the delta,
        O((supp(T)+supp(delta))^2) to rebuild C -- cheap since supports
        stay <= B^2 at this scale."""
        curve = self.curve
        Dx = mumford1(x[0], x[1], curve)
        delta = self._delta_for(Dx)
        T_new = self.T + delta
        C: Counter = Counter()
        for gs, cs in T_new.items():
            for gt, ct in T_new.items():
                g = jac_sub(gs, gt, curve)
                C[g] += cs * ct
        return e4_from_quad_histogram(C)

    def add(self, x: Point) -> None:
        """Commit x into F, updating T in place. O(|F|)."""
        curve = self.curve
        Dx = mumford1(x[0], x[1], curve)
        delta = self._delta_for(Dx)
        self.T += delta
        self.lifted.append(Dx)

    def current_e4(self) -> int:
        curve = self.curve
        C: Counter = Counter()
        for gs, cs in self.T.items():
            for gt, ct in self.T.items():
                g = jac_sub(gs, gt, curve)
                C[g] += cs * ct
        return e4_from_quad_histogram(C)


# ============================================================
#  Sanity-check-only naive reference (small B; O(B^8))
# ============================================================

def e4_naive_bruteforce(points: Sequence[Point], curve: Curve, limit: int = 8) -> int:
    """Directly counts 8-tuples (P1..P8) with P1+P2-P3-P4 = P5+P6-P7-P8,
    by literal Jacobian arithmetic on all ordered 8-tuples. O(B^8) --
    only for cross-checking e4_moment on tiny B (e.g. B <= `limit`).
    Raises if len(points) exceeds `limit`, since this is exponential and
    meant purely as a correctness oracle, not a real scorer.
    """
    B = len(points)
    if B > limit:
        raise ValueError(
            f"e4_naive_bruteforce: {B} points exceeds limit={limit}; "
            "this is O(B^8), use e4_moment instead"
        )
    lifted = [mumford1(x, y, curve) for x, y in points]

    def lhs(i1, i2, i3, i4):
        d = jac_add(lifted[i1], lifted[i2], curve)
        d = jac_sub(d, lifted[i3], curve)
        d = jac_sub(d, lifted[i4], curve)
        return d

    # collect all left-hand-side values with multiplicity, likewise for
    # the (identical, by symmetry) right-hand side, then count matches.
    lhs_vals = Counter()
    for i1 in range(B):
        for i2 in range(B):
            for i3 in range(B):
                for i4 in range(B):
                    lhs_vals[lhs(i1, i2, i3, i4)] += 1

    total = 0
    for count in lhs_vals.values():
        total += count * count
    return total
