"""
Sequential set-construction environment for the e4-minimization task.

Motivation
----------
The original DeepSetsRegressor was handed a finished set F and asked to
predict e4(F) from static (x,y) geometry -- diagnosed as ill-posed,
since e4 is a function of the pair-sum histogram T = 1_F*1_F, which has
no relationship to the smooth cyclic point embedding that was used (see
t_features.py's docstring).

This module instead exposes set construction as a sequential decision
process: start with F={}, repeatedly choose the next point (under
Claire's monotonic constraint -- each new pool index must exceed the
previously chosen index, which both canonicalizes the search space to
one path per set and shrinks the action space every step), and expose
the *trajectory* of T-feature snapshots, not just the final one. A
value/policy network trained on this can in principle learn from how T
evolves move-to-move (e.g. "this move is about to create a collision"),
not just from a static endpoint summary.

This module has NO torch dependency -- it only produces plain Python /
list-of-float state. t_features.py (which does import torch) can be
layered on top for network input; this module is usable standalone for
the random-rollout value baseline (no network at all).

Built on moment.py's IncrementalMoment, which already maintains T in
O(|F|) per added point rather than rebuilding it in O(B^2) -- so a full
B-step rollout costs O(B^2) total (same as one static e4 computation),
not O(B^3).
"""

from __future__ import annotations

import math
import random
from dataclasses import dataclass, field
from typing import List, Optional, Sequence, Tuple

from curve import Curve
from moment import IncrementalMoment

Point = Tuple[int, int]

N_STEP_FEATURES = 7  # must match t_features.py's N_T_FEATURES -- see _t_features_from_T


def _t_features_from_T(T, B: int) -> List[float]:
    """Same 7 features as t_features.py's compute_t_features, but computed
    directly from an already-built T (IncrementalMoment's .T), so a
    rollout doesn't have to re-lift points or rebuild T from scratch just
    to get features -- this is the whole reason ConstructionEnv keeps its
    own copy of this logic rather than importing compute_t_features,
    which takes raw points and curve and rebuilds T internally.

    Raises if T is empty and B > 0, since that would mean IncrementalMoment's
    state is out of sync with the reported point count -- silently
    returning zeros there would hide a real bug.
    """
    counts = list(T.values())
    if B > 0 and not counts:
        raise RuntimeError(
            f"_t_features_from_T: B={B} but T has no entries -- "
            "IncrementalMoment state is inconsistent (T should have at "
            "least the B diagonal x+x entries by this point)"
        )
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


@dataclass
class ConstructionState:
    """One step of a construction trajectory. `t_features` is the
    snapshot AFTER committing `chosen_idx` (or the all-zero initial
    snapshot at step 0, before any point is chosen)."""
    step: int                      # 0 = initial (empty F), 1..B = after each add
    last_idx: int                  # pool index most recently added; -1 if step==0
    n_remaining_legal: int         # legal next-move count under monotonic constraint
    t_features: List[float]
    e4_so_far: int                 # IncrementalMoment.current_e4() at this step


@dataclass
class ConstructionTrajectory:
    pool_indices_chosen: List[int]
    states: List[ConstructionState]  # length B+1 (initial state + one per add)
    final_e4: int

    def __post_init__(self) -> None:
        if len(self.states) != len(self.pool_indices_chosen) + 1:
            raise AssertionError(
                f"ConstructionTrajectory: {len(self.states)} states but "
                f"{len(self.pool_indices_chosen)} chosen indices -- expected "
                "states to be exactly one longer (initial + one per add)"
            )
        if self.states[-1].e4_so_far != self.final_e4:
            raise AssertionError(
                f"ConstructionTrajectory: last state's e4_so_far "
                f"({self.states[-1].e4_so_far}) != final_e4 "
                f"({self.final_e4}) -- trajectory is internally inconsistent"
            )


class ConstructionEnv:
    """Sequential builder for one set F, under the monotonic pool-index
    constraint. Not reused across trajectories -- construct a fresh
    ConstructionEnv per rollout/episode (cheap: it just wraps an
    IncrementalMoment and an index cursor)."""

    def __init__(self, curve: Curve, pool: Sequence[Point], B: int):
        if B <= 0:
            raise ValueError(f"ConstructionEnv: B must be positive, got {B}")
        if B > len(pool):
            raise ValueError(
                f"ConstructionEnv: B={B} exceeds pool size {len(pool)}"
            )
        self.curve = curve
        self.pool = pool
        self.B = B
        self.inc = IncrementalMoment(curve)
        self.chosen: List[int] = []
        self.last_idx = -1

    def legal_moves(self) -> List[int]:
        """Pool indices strictly greater than the last chosen index, with
        enough of them remaining to still reach B total points. Empty
        list means this state is a dead end under the monotonic
        constraint (should not happen if you only ever call step() with
        moves drawn from a prior legal_moves() call)."""
        n = len(self.pool)
        steps_left = self.B - len(self.chosen)
        # need at least steps_left candidates strictly after last_idx
        latest_allowed_start = n - steps_left
        if latest_allowed_start <= self.last_idx:
            return []
        return list(range(self.last_idx + 1, n))

    def snapshot(self) -> ConstructionState:
        t_feats = _t_features_from_T(self.inc.T, len(self.chosen))
        e4 = self.inc.current_e4() if self.chosen else 0
        return ConstructionState(
            step=len(self.chosen),
            last_idx=self.last_idx,
            n_remaining_legal=len(self.legal_moves()),
            t_features=t_feats,
            e4_so_far=e4,
        )

    def step(self, pool_idx: int) -> ConstructionState:
        """Commit pool[pool_idx] as the next point. Raises on any
        violation of the monotonic constraint or double-selection --
        these indicate a bug in the caller (e.g. a policy that ignored
        legal_moves()), not a recoverable condition."""
        if len(self.chosen) >= self.B:
            raise RuntimeError(
                f"ConstructionEnv.step: already have {len(self.chosen)} "
                f"points (B={self.B}); cannot add another"
            )
        if pool_idx <= self.last_idx:
            raise ValueError(
                f"ConstructionEnv.step: pool_idx={pool_idx} does not exceed "
                f"last_idx={self.last_idx} -- violates the monotonic "
                "selection constraint"
            )
        if pool_idx >= len(self.pool):
            raise IndexError(
                f"ConstructionEnv.step: pool_idx={pool_idx} out of range "
                f"for pool of size {len(self.pool)}"
            )
        self.inc.add(self.pool[pool_idx])
        self.chosen.append(pool_idx)
        self.last_idx = pool_idx
        return self.snapshot()

    def is_done(self) -> bool:
        return len(self.chosen) == self.B


def random_trajectory(
    curve: Curve, pool: Sequence[Point], B: int, rng: random.Random
) -> ConstructionTrajectory:
    """One full random rollout under the monotonic constraint, recording
    every intermediate T-feature snapshot. This is the trajectory
    representation intended for the eventual value/policy network input
    -- the network would see states[0..step] leading up to a move, not
    just the final state[-1]."""
    env = ConstructionEnv(curve, pool, B)
    states = [env.snapshot()]
    for _ in range(B):
        moves = env.legal_moves()
        if not moves:
            raise RuntimeError(
                "random_trajectory: ran out of legal moves before reaching "
                f"B={B} points (chose {len(env.chosen)}) -- pool too small "
                "for this B, should have been caught by ConstructionEnv.__init__"
            )
        pick = rng.choice(moves)
        states.append(env.step(pick))
    return ConstructionTrajectory(
        pool_indices_chosen=list(env.chosen),
        states=states,
        final_e4=env.inc.current_e4(),
    )


def estimate_value(
    curve: Curve,
    pool: Sequence[Point],
    B: int,
    prefix_indices: Sequence[int],
    n_rollouts: int,
    rng: random.Random,
) -> Tuple[float, float]:
    """Random-rollout value estimate for a partial state: fix
    `prefix_indices` (a legal partial monotonic sequence, possibly
    empty), finish it `n_rollouts` times with uniform-random legal
    moves, return (mean final e4, stdev). This is the "value function
    baseline, no network yet" step from the build plan -- it tells you
    whether partial-T is predictive of final e4 *during* construction,
    not just at the end, before you commit to training anything.

    Raises if prefix_indices is not a strictly increasing, in-range
    sequence, since silently repairing it would mask a caller bug.
    """
    if len(prefix_indices) > B:
        raise ValueError(
            f"estimate_value: prefix has {len(prefix_indices)} indices, "
            f"exceeds B={B}"
        )
    for a, b in zip(prefix_indices, prefix_indices[1:]):
        if b <= a:
            raise ValueError(
                f"estimate_value: prefix_indices not strictly increasing "
                f"at {a} -> {b}"
            )
    if n_rollouts <= 0:
        raise ValueError(f"estimate_value: n_rollouts must be positive, got {n_rollouts}")

    finals: List[int] = []
    for _ in range(n_rollouts):
        env = ConstructionEnv(curve, pool, B)
        for idx in prefix_indices:
            env.step(idx)
        while not env.is_done():
            moves = env.legal_moves()
            if not moves:
                raise RuntimeError(
                    "estimate_value: rollout ran out of legal moves given "
                    f"prefix {prefix_indices} -- prefix may be too far into "
                    "the pool to leave B-len(prefix) candidates remaining"
                )
            env.step(rng.choice(moves))
        finals.append(env.inc.current_e4())

    mean = sum(finals) / len(finals)
    var = sum((f - mean) ** 2 for f in finals) / len(finals)
    return mean, math.sqrt(var)
