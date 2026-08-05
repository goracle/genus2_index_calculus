"""
Structured (non-uniform) subset samplers over the candidate pool.

Motivation (see project conversation): uniform random sampling of size-B
subsets F from the pool concentrates e4(F) into an extremely narrow band
near a floor value -- confirmed empirically at both (p=311, B=10) and
(p=3037, B=25) -- leaving too little variance/tail for a regression
model to learn anything beyond "always predict the mean". The fix is
upstream of the model: bias subset *construction* toward sets more
likely to exhibit structure (arithmetic-progression-like or coset-like
patterns in the underlying scalar k), which per the project's advisory
notes is the known source of elevated (non-generic) 8th-moment
behavior (Singer/Bose-Chowla-type constructions, Shkredov's higher-
energy dichotomy).

All samplers here operate on an existing `pool: list[Candidate]` (as
built by gen_dataset.py's build_pool) -- they select which pool
elements to include in F, they do not call generate_candidates
themselves. This keeps them agnostic to how the pool was built and
avoids re-deriving Jacobian points.

Every sampler returns (chosen: list[Candidate], mode: str) so callers
can stamp each generated example with its construction method --
important for later stratifying/inspecting the dataset by how each
example was built, and for detecting if one mode is silently
dominating or absent from a run.
"""

from __future__ import annotations

import random
from typing import List, Tuple

from candidates import Candidate


def sample_uniform(pool: List[Candidate], B: int, rng: random.Random) -> Tuple[List[Candidate], str]:
    """Baseline: uniform random size-B subset (matches the original
    gen_dataset.py behavior). Kept here so all sampling modes live in
    one place and callers can pick among them uniformly-at-random too,
    if mixing multiple modes into one dataset."""
    return rng.sample(pool, B), "uniform"


def sample_ap(
    pool: List[Candidate],
    B: int,
    rng: random.Random,
    jitter: float = 0.0,
) -> Tuple[List[Candidate], str]:
    """Pick F by targeting an arithmetic progression in k: k0, k0+d,
    k0+2d, ..., k0+(B-1)d, then for each target value selecting the
    pool candidate whose actual k is closest to it (since not every
    integer k has a pool entry -- see candidates.py's docstring: only
    ~half of scanned k split). Each pool candidate can only be used
    once even if it's the closest match for two different target slots
    (handled by removing selected candidates from the search set as we
    go); if the pool is exhausted before B distinct candidates are
    found (only possible for pathologically small pools), falls back to
    uniform sampling from what's left.

    jitter in [0, 1]: fraction of the B target slots that get replaced
    by a uniformly random pool pick instead of the AP-nearest pick --
    0.0 is a pure AP-shaped set, 1.0 degenerates to sample_uniform.
    This is what makes structured-ness gradable rather than a binary
    "obviously-AP or not" label -- see project conversation for why
    that matters (avoiding a model that just learns to detect obvious
    AP-shape rather than engage with harder, partially-structured
    cases).
    """
    if not (0.0 <= jitter <= 1.0):
        raise ValueError(f"jitter must be in [0,1], got {jitter}")

    k_values = sorted(c.k for c in pool)
    k_min, k_max = k_values[0], k_values[-1]
    span = max(1, k_max - k_min)

    # random AP: pick k0 and a step d such that the full AP roughly fits
    # within the observed k range (keeps target slots plausible instead
    # of running off past every real k value in the pool)
    max_step = max(1, span // max(1, B - 1))
    d = rng.randint(1, max_step)
    k0 = rng.randint(k_min, max(k_min, k_max - d * (B - 1)))

    targets = [k0 + i * d for i in range(B)]

    # track by pool INDEX, not object identity (id()) or value-equality --
    # index is unambiguous regardless of whether pool candidates are the
    # literal same Python objects across calls (id() breaks if pool is
    # ever rebuilt/reloaded from JSON) or whether the pool happens to
    # contain two value-equal Candidates (value-equality would wrongly
    # merge them; build_pool's dedup-by-(x,y) should prevent that, but
    # this function shouldn't silently assume that invariant holds)
    order = list(range(len(pool)))
    rng.shuffle(order)  # so ties / fallback exhaustion aren't positionally biased
    chosen: List[Candidate] = []
    used_indices = set()

    for slot_idx, t in enumerate(targets):
        use_jitter = rng.random() < jitter
        available = [i for i in order if i not in used_indices]
        if not available:
            break
        if use_jitter:
            pick_idx = available[0]
        else:
            # nearest-by-k among not-yet-used indices
            pick_idx = min(available, key=lambda i: abs(pool[i].k - t))

        chosen.append(pool[pick_idx])
        used_indices.add(pick_idx)

    if len(chosen) < B:
        # pool exhausted (only realistic for very small pools) -- top up
        # uniformly from whatever's left rather than returning a short set
        leftover_indices = [i for i in range(len(pool)) if i not in used_indices]
        need = B - len(chosen)
        topup_indices = rng.sample(leftover_indices, min(need, len(leftover_indices)))
        chosen.extend(pool[i] for i in topup_indices)

    mode = "ap" if jitter == 0.0 else f"ap_jitter{jitter:.2f}"
    return chosen, mode


def sample_coset(
    pool: List[Candidate],
    B: int,
    rng: random.Random,
    modulus: int,
    jitter: float = 0.0,
) -> Tuple[List[Candidate], str]:
    """Pick F from pool candidates whose k falls in a single randomly
    chosen residue class mod `modulus` (a coset-like restriction on the
    scalar range), rather than an AP. If fewer than B pool candidates
    share that residue class, falls back to the closest-residue
    candidates outside the class to fill out F (mirrors sample_ap's
    graceful degradation rather than raising).

    modulus should be chosen relative to the pool's k-range -- e.g.
    modulus ~ sqrt(pool_size) gives residue classes with a handful of
    members each; too large a modulus makes classes mostly-empty and
    this degrades toward uniform sampling anyway.

    jitter behaves as in sample_ap: fraction of slots replaced by a
    uniformly random pick instead of a same-class pick.
    """
    if not (0.0 <= jitter <= 1.0):
        raise ValueError(f"jitter must be in [0,1], got {jitter}")
    if modulus < 1:
        raise ValueError(f"modulus must be >= 1, got {modulus}")

    residue = rng.randrange(modulus)
    in_class = [c for c in pool if c.k % modulus == residue]
    out_class = [c for c in pool if c.k % modulus != residue]
    rng.shuffle(in_class)
    rng.shuffle(out_class)

    chosen: List[Candidate] = []
    in_iter = iter(in_class)
    out_iter = iter(out_class)

    for _ in range(B):
        use_jitter = rng.random() < jitter
        pick = None
        if not use_jitter:
            pick = next(in_iter, None)
        if pick is None:
            pick = next(out_iter, None)
        if pick is None:
            break
        chosen.append(pick)

    if len(chosen) < B:
        remaining = [c for c in pool if c not in chosen]
        need = B - len(chosen)
        chosen.extend(rng.sample(remaining, min(need, len(remaining))))

    mode = f"coset_mod{modulus}" if jitter == 0.0 else f"coset_mod{modulus}_jitter{jitter:.2f}"
    return chosen, mode


def sample_mixed(
    pool: List[Candidate],
    B: int,
    rng: random.Random,
    mode_weights: dict,
    coset_modulus: int,
) -> Tuple[List[Candidate], str]:
    """Convenience dispatcher: picks a sampling mode at random according
    to mode_weights (e.g. {"uniform": 0.5, "ap": 0.3, "coset": 0.2}),
    then delegates. Jitter, when applicable, is drawn uniformly from
    [0, 1] per call so the resulting dataset has a graded spread of
    structured-ness rather than only the pure (jitter=0) and fully
    random (uniform mode) extremes.

    Use this from gen_dataset.py in place of a bare
    `sample_rng.sample(pool, B)` call to get a dataset that mixes
    construction methods -- pass mode_weights summing to 1.0 (not
    strictly enforced here, just normalized).
    """
    modes = list(mode_weights.keys())
    weights = list(mode_weights.values())
    choice = rng.choices(modes, weights=weights, k=1)[0]

    if choice == "uniform":
        return sample_uniform(pool, B, rng)
    elif choice == "ap":
        j = rng.random()
        return sample_ap(pool, B, rng, jitter=j)
    elif choice == "coset":
        j = rng.random()
        return sample_coset(pool, B, rng, modulus=coset_modulus, jitter=j)
    else:
        raise ValueError(f"unknown mode {choice!r} in mode_weights")
