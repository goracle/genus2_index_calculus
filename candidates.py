"""
Candidate pool generation for the genus-2 8th-moment set-selection project.

For a curve C, subgroup generator `a` of prime order `ell`, and a range of
scalars k, compute k*a on the Jacobian, check whether its Mumford u(x)
splits over F_p, and if so emit the two resulting curve points.

Each candidate point is tagged with:
  - k        : the scalar multiple (the "hidden"/spectrally-invisible label;
               not fed to the model, but needed for supervision/analysis)
  - pair_id  : which k produced it (both points from the same k share this)
  - x, y     : the F_p curve point

Roughly half of all k should split (Div2.u degree-2 splits over F_p with
probability ~1/2), so to get N candidate points we expect to need on the
order of N scalars tried.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import List, Optional

from curve import Curve, Div2, jac_mul, jac_is_identity, split_divisor_to_points


@dataclass(frozen=True)
class Candidate:
    k: int
    pair_id: int
    x: int
    y: int


def generate_candidates(
    curve: Curve,
    a: Div2,
    k_start: int = 1,
    k_max: Optional[int] = None,
    max_candidates: Optional[int] = None,
) -> List[Candidate]:
    """Scan k = k_start, k_start+1, ... computing k*a and collecting
    candidate points from splitting divisors.

    Exactly one of k_max / max_candidates should typically be set to bound
    the scan; if both are given, whichever limit is hit first stops the scan.

    Raises ValueError if k_start < 1 or if neither k_max nor max_candidates
    is provided (an unbounded scan is almost certainly a bug, not intent).
    """
    if k_start < 1:
        raise ValueError(f"k_start must be >= 1, got {k_start}")
    if k_max is None and max_candidates is None:
        raise ValueError("must provide k_max and/or max_candidates to bound the scan")

    out: List[Candidate] = []
    k = k_start
    while True:
        if k_max is not None and k > k_max:
            break
        if max_candidates is not None and len(out) >= max_candidates:
            break

        D = jac_mul(a, k, curve)
        if jac_is_identity(D):
            k += 1
            continue

        pts = split_divisor_to_points(D, curve)
        if pts is not None:
            (x1, y1), (x2, y2) = pts
            if not curve.is_on_curve(x1, y1):
                raise ArithmeticError(f"split point ({x1},{y1}) from k={k} fails curve check")
            if not curve.is_on_curve(x2, y2):
                raise ArithmeticError(f"split point ({x2},{y2}) from k={k} fails curve check")
            out.append(Candidate(k=k, pair_id=k, x=x1, y=y1))
            out.append(Candidate(k=k, pair_id=k, x=x2, y=y2))

        k += 1

    return out
