"""
Dataset loading for the 8th-moment ("e4" in the codebase's naming --
see moment.py's docstring for why that name is misleading) regression
task.

Why log(e4 - floor + 1) instead of raw e4
------------------------------------------
Empirically (checked directly against the uploaded dataset.jsonl,
5000 examples, B=10, pool_size=305): ~39% of examples sit at the exact
minimum value, and 99% of all examples fall within ~2% of that minimum
-- only a long thin tail of rare examples deviates meaningfully upward.
Regressing raw e4 with MSE lets the loss be dominated by getting the
shared ~176000 constant right, and gives essentially no gradient signal
for distinguishing "at floor" from "slightly elevated" from "rare bad
outlier" -- which is exactly the distinction that matters. Subtracting
the floor and log-transforming spreads that structure out: floor
examples map to exactly log(1)=0, and the log compresses the long right
tail so a few extreme outliers (up to +21% of floor in this data)
don't dominate the loss the way they would in raw space.

The floor is computed from the training data itself (min of e4 over
the training split), not hardcoded, since a different curve/pool/B
would give a different floor.
"""

from __future__ import annotations

import json
import math
from dataclasses import dataclass
from typing import List, Optional, Tuple

import torch
from torch.utils.data import Dataset


@dataclass
class Example:
    points: List[Tuple[int, int]]  # length B, each (x, y) in F_p
    e4: int


def load_examples(path: str) -> List[Example]:
    out = []
    with open(path) as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            rec = json.loads(line)
            pts = [(x, y) for x, y in rec["points"]]
            out.append(Example(points=pts, e4=rec["e4"]))
    return out


def encode_points(points: List[Tuple[int, int]], p: int) -> torch.Tensor:
    """Encode B (x, y) points, each in F_p, as a (B, 4) float tensor:
    [cos(2*pi*x/p), sin(2*pi*x/p), cos(2*pi*y/p), sin(2*pi*y/p)].

    Raw residues mod p aren't meaningful NN inputs on their own -- e.g.
    a linear/MLP layer would treat "p-1" and "0" as maximally far apart,
    when as field elements they carry no such ordering, and there's no
    reason to believe the network should treat x=5 as "closer to" x=6
    than to x=200 in any way that matters for this problem. The
    sin/cos-of-angle encoding is the standard fix for a categorical/
    cyclic value: it's injective (each residue maps to a distinct point
    on the unit circle) and doesn't impose a false linear order.
    """
    vals = []
    two_pi = 2.0 * math.pi
    for x, y in points:
        theta_x = two_pi * x / p
        theta_y = two_pi * y / p
        vals.append([
            math.cos(theta_x), math.sin(theta_x),
            math.cos(theta_y), math.sin(theta_y),
        ])
    return torch.tensor(vals, dtype=torch.float32)


class MomentDataset(Dataset):
    """Wraps a list of Examples. Returns (points_encoded, target, raw_e4)
    per item, where target = log(e4 - floor + 1) using a floor supplied
    at construction time (so train/val/test all share the SAME floor --
    see split_dataset below for why this must be computed once on the
    training split, not per-split).
    """

    def __init__(self, examples: List[Example], p: int, floor: int):
        self.examples = examples
        self.p = p
        self.floor = floor

    def __len__(self) -> int:
        return len(self.examples)

    def __getitem__(self, idx: int):
        ex = self.examples[idx]
        enc = encode_points(ex.points, self.p)
        shifted = ex.e4 - self.floor
        if shifted < 0:
            # Can happen for val/test examples if they happen to score
            # below every training example's floor. Clamp rather than
            # error -- log(negative) is undefined, and a val example
            # slightly below the train-derived floor is not a bug, just
            # a slightly-out-of-sample floor estimate.
            shifted = 0
        target = math.log1p(shifted)  # log(1 + shifted), stable at shifted=0
        return enc, torch.tensor(target, dtype=torch.float32), torch.tensor(float(ex.e4))


def target_to_e4(target: torch.Tensor, floor: int) -> torch.Tensor:
    """Inverse of the log1p-shift transform, for turning model output
    back into an actual e4 prediction: e4 = floor + (exp(target) - 1)."""
    return floor + (torch.expm1(target))


def split_dataset(
    examples: List[Example],
    val_frac: float = 0.15,
    test_frac: float = 0.15,
    seed: int = 0,
) -> Tuple[List[Example], List[Example], List[Example]]:
    """Random train/val/test split. Shuffles with a fixed seed for
    reproducibility. Does NOT stratify by e4 value -- with 39% of mass
    at a single floor value, a plain random split already guarantees
    all three splits are dominated by floor examples in about the same
    proportion, so stratification isn't needed here.
    """
    import random
    idx = list(range(len(examples)))
    random.Random(seed).shuffle(idx)

    n = len(examples)
    n_val = int(n * val_frac)
    n_test = int(n * test_frac)
    n_train = n - n_val - n_test
    if n_train <= 0:
        raise ValueError(
            f"val_frac+test_frac={val_frac+test_frac} leaves no training "
            f"examples out of {n} total"
        )

    train_idx = idx[:n_train]
    val_idx = idx[n_train:n_train + n_val]
    test_idx = idx[n_train + n_val:]

    train = [examples[i] for i in train_idx]
    val = [examples[i] for i in val_idx]
    test = [examples[i] for i in test_idx]
    return train, val, test


def compute_floor(examples: List[Example]) -> int:
    return min(ex.e4 for ex in examples)
