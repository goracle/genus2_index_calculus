"""
Group-structure features for the 8th-moment regression task, computed
directly from the pair-sum histogram T = 1_F * 1_F.

Why this exists
----------------
e4(F) = sum_g C(g)^2, where C = T correlated with T (see moment.py).
That means e4 is a function of T's multiplicity structure -- how
concentrated/collided T is on the Jacobian -- not a function of the
raw (x, y) coordinates in any way an MLP over sin/cos(2*pi*x/p) can
see. Confirmed empirically (see project conversation): a random
forest given raw (x,y) OR the hidden discrete-log k values scores
R^2 ~ 0 predicting e4, while a single scalar feature computed from T
(sum_g T(g)^2) correlates ~0.91 with the true e4.

T itself is cheap: O(B^2) group operations (jac_add calls), already
implemented in moment.py's pair_sum_histogram. This module wraps that
to produce a fixed-size feature vector per example, meant to replace
(or augment) the raw-point encoding in data.py.

Feature vector (7 dims), all computed from the multiset of T's
nonzero values {T(g) : g in support(T)}:
  0: sum_T2       = sum_g T(g)^2            (the ~0.91-correlated feature)
  1: max_T        = max_g T(g)
  2: supp_T       = number of distinct nonzero g (|support(T)|)
  3: n_collisions = count of g with T(g) >= 2
  4: mean_T       = sum_T2's denominator sanity companion: mean multiplicity
                     over the support (supp_T is B^2 total mass / mean_T)
  5: B            = |F| (points count) -- included so the network can
                     normalize the above by set size if B varies across
                     examples in a dataset
  6: log1p_sum_T2 = log1p(sum_T2), a rescaled companion to feature 0 so
                     the network doesn't have to learn the log itself
                     (sum_T2 ranges over orders of magnitude across a
                     dataset the same way e4 does -- see data.py's
                     docstring on why raw e4 is a poor regression target)

All 7 features are cheap to add; drop ones that don't help once you've
run a real comparison. sum_T2 (feature 0) is the one with actual
empirical justification -- treat the rest as "worth trying", not as
independently validated.
"""

from __future__ import annotations

import math
from typing import List, Sequence, Tuple

import torch

from curve import Curve, mumford1
from moment import pair_sum_histogram

Point = Tuple[int, int]

N_T_FEATURES = 7


def compute_t_features(points: Sequence[Point], curve: Curve) -> List[float]:
    """O(B^2) group operations (same cost as computing e4's T step).
    Returns a length-N_T_FEATURES list of floats."""
    lifted = [mumford1(x, y, curve) for x, y in points]
    T = pair_sum_histogram(lifted, curve)

    counts = list(T.values())
    B = len(points)

    sum_T2 = float(sum(c * c for c in counts))
    max_T = float(max(counts)) if counts else 0.0
    supp_T = float(len(counts))
    n_collisions = float(sum(1 for c in counts if c >= 2))
    mean_T = (sum(counts) / supp_T) if supp_T > 0 else 0.0

    return [
        sum_T2,
        max_T,
        supp_T,
        n_collisions,
        mean_T,
        float(B),
        math.log1p(sum_T2),
    ]


def encode_points_with_t_features(
    points: Sequence[Point], p: int, curve: Curve
) -> torch.Tensor:
    """Per-point cyclic encoding (same as data.py's encode_points),
    concatenated with the T-derived features broadcast onto every
    point row. Output: (B, 4 + N_T_FEATURES) tensor.

    Broadcasting the (same) T-feature vector onto every point row is a
    deliberate, simple choice so this drops into the existing Deep Sets
    architecture (model.py) with only an in_dim change (4 -> 4+7) --
    the phi network sees T-derived context alongside each point's own
    coordinates, and mean-pooling still works since every row carries
    the same T-feature block. This is NOT the only way to use these
    features (see train_with_t_features.py's alternate "concat after
    pooling" architecture, which is probably the better long-run choice
    since it doesn't force the per-point phi network to redundantly
    re-learn to ignore the constant T block B times) -- both are wired
    up so you can compare.
    """
    two_pi = 2.0 * math.pi
    t_feats = compute_t_features(points, curve)

    rows = []
    for x, y in points:
        theta_x = two_pi * x / p
        theta_y = two_pi * y / p
        row = [
            math.cos(theta_x), math.sin(theta_x),
            math.cos(theta_y), math.sin(theta_y),
        ] + t_feats
        rows.append(row)
    return torch.tensor(rows, dtype=torch.float32)


def t_features_only(points: Sequence[Point], curve: Curve) -> torch.Tensor:
    """Just the T-feature vector, length N_T_FEATURES, no per-point
    coordinates at all. Use this for the "does the model even need the
    raw points" sanity check -- a small MLP on this alone should beat
    the current DeepSetsRegressor if the diagnosis is right."""
    return torch.tensor(compute_t_features(points, curve), dtype=torch.float32)
