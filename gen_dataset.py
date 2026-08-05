"""
Generate a training dataset for the 8th-moment set-selection task.

Fixed curve + cryptographic subgroup, fixed candidate pool (built once).
Each example is a size-B subset F of the pool, drawn according to
mode_weights (uniform random, AP-in-k, or coset-in-k -- see
structured_sampling.py), scored by e4_moment. Written incrementally to
a JSONL checkpoint file so a long run can be interrupted/resumed
without losing progress.

Why not pure uniform sampling: confirmed empirically (see project
conversation) that uniform random F concentrates e4(F) into an
extremely narrow band near a floor value, leaving too little
variance/tail for a regression model to learn anything beyond
"predict the mean". Mixing in structured (AP/coset) sampling biases
some fraction of the dataset toward sets more likely to exhibit
elevated e4 -- the structured constructions the project's advisory
notes identify as the known source of non-generic 8th-moment
behavior.

Output schema (one JSON object per line):
{
  "example_id": int,
  "k_values": [int, ...],       # hidden label: which scalar multiples of
                                 # the generator produced each point in F
                                 # (not fed to the model -- for
                                 # supervision/analysis only)
  "pair_ids": [int, ...],       # spectrally-visible label: same length/
                                 # order as k_values; here pair_id == k
                                 # per generate_candidates' convention, but
                                 # kept as a separate field to match the
                                 # spec's "hidden part vs spectrally
                                 # visible part" framing
  "points": [[x, y], ...],      # the actual model input: F itself
  "e4": int,                    # target: E4(F), to be minimized
  "sampling_mode": str          # which sampler produced F -- "uniform",
                                 # "ap"/"ap_jitterX.XX", or
                                 # "coset_modM"/"coset_modM_jitterX.XX".
                                 # Lets later analysis/training stratify
                                 # by construction method, and lets you
                                 # verify structured sampling actually
                                 # reached the intended fraction of the
                                 # dataset rather than silently failing.
}

Curve parameters (p, f_poly, subgroup order ell, cofactor h, generator a)
are written once to a header line / sidecar file, since they're constant
across the whole dataset. mode_weights and coset_modulus are also
written to meta, since they materially define the dataset's sampling
distribution (unlike a plain uniform-sampling run where there was
nothing extra to record).
"""

from __future__ import annotations

import json
import random
import time
from pathlib import Path

from curve import Curve, find_cryptographic_subgroup
from candidates import generate_candidates, Candidate
from moment import e4_moment
from structured_sampling import sample_mixed


def build_pool(curve: Curve, a, ell: int, max_candidates: int) -> list:
    """Scan k=1.. to build a candidate pool, deduplicated by (x,y) point
    so no two entries in the pool are the literal same point (a given
    point could otherwise appear twice from different k, which would
    make 'sample B points from the pool' ill-defined for a proper set)."""
    raw = generate_candidates(curve, a, k_start=1, max_candidates=max_candidates, k_max=ell)
    seen = {}
    for c in raw:
        pt = (c.x, c.y)
        if pt not in seen:
            seen[pt] = c
    return list(seen.values())


def generate_dataset(
    out_path: str,
    meta_path: str,
    n_examples: int,
    B: int,
    curve: Curve,
    a,
    ell: int,
    h: int,
    p: int,
    pool: list,
    seed: int,
    start_index: int = 0,
    checkpoint_every: int = 50,
    log_every: int = 25,
    mode_weights: dict | None = None,
    coset_modulus: int | None = None,
):
    """Generate examples [start_index, start_index + n_examples), appending
    to out_path. Uses a seeded RNG advanced deterministically by
    start_index draws so repeated resumed calls (each a fresh process)
    produce the same sequence a single long run would have -- calling
    this with start_index=0..999 then 1000..1999 etc. gives the identical
    dataset to one call with n_examples=2000, just spread across
    multiple process invocations to fit within a wall-clock budget.

    mode_weights: dict passed to structured_sampling.sample_mixed, e.g.
    {"uniform": 0.5, "ap": 0.3, "coset": 0.2}. Defaults to pure uniform
    sampling (matching the original behavior) if not given -- so callers
    that don't pass this get byte-for-byte the old dataset shape (modulo
    the added sampling_mode field on each record).

    coset_modulus: required if mode_weights includes a nonzero "coset"
    weight; passed through to sample_coset. A reasonable default is
    round(sqrt(pool_size)) -- see this module's __main__ for where
    that's computed once the pool size is known.

    NOTE on resumability: sample_mixed makes a variable number of RNG
    calls per example (depends which mode gets chosen and which branch
    it takes internally), unlike the old bare `sample_rng.sample(pool,
    B)` which always made exactly one call. Fast-forwarding by replaying
    start_index draws is still EXACT (a freshly seeded Random(seed) is
    fully deterministic regardless of call-pattern complexity), it's
    just no longer a fixed cost per skipped example -- replaying to a
    large start_index costs roughly the same as generating that many
    real examples, not less.
    """
    if mode_weights is None:
        mode_weights = {"uniform": 1.0}
    if any(k == "coset" for k in mode_weights) and coset_modulus is None:
        raise ValueError("coset_modulus must be given when mode_weights includes 'coset'")

    sample_rng = random.Random(seed)
    # fast-forward the RNG stream to start_index by drawing (and discarding)
    # the same number of samples a from-scratch run would have consumed
    for _ in range(start_index):
        sample_mixed(pool, B, sample_rng, mode_weights=mode_weights, coset_modulus=coset_modulus or 1)

    if start_index == 0:
        meta = {
            "p": p,
            "f_poly": list(curve.f_poly),
            "ell": ell,
            "h": h,
            "generator_u": list(a.u),
            "generator_v": list(a.v),
            "B": B,
            "pool_size": len(pool),
            "seed": seed,
            "mode_weights": mode_weights,
            "coset_modulus": coset_modulus,
        }
        Path(meta_path).write_text(json.dumps(meta, indent=2))

    t_start = time.time()
    mode = "a" if start_index > 0 else "w"
    with open(out_path, mode) as f:
        for offset in range(n_examples):
            i = start_index + offset
            chosen, sampling_mode = sample_mixed(
                pool, B, sample_rng, mode_weights=mode_weights, coset_modulus=coset_modulus or 1
            )
            points = [(c.x, c.y) for c in chosen]
            e4 = e4_moment(points, curve)
            record = {
                "example_id": i,
                "k_values": [c.k for c in chosen],
                "pair_ids": [c.pair_id for c in chosen],
                "points": [[c.x, c.y] for c in chosen],
                "e4": e4,
                "sampling_mode": sampling_mode,
            }
            f.write(json.dumps(record) + "\n")

            if (offset + 1) % checkpoint_every == 0:
                f.flush()
            if (offset + 1) % log_every == 0:
                elapsed = time.time() - t_start
                rate = (offset + 1) / elapsed
                print(
                    f"[{offset+1}/{n_examples} this chunk, global idx {i}] "
                    f"e4={e4} mode={sampling_mode} elapsed={elapsed:.1f}s rate={rate:.2f}/s",
                    flush=True,
                )

    print(f"chunk done: examples {start_index}..{start_index+n_examples-1} "
          f"written to {out_path}", flush=True)


if __name__ == "__main__":
    import sys

    n_examples = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    out_path = sys.argv[2] if len(sys.argv) > 2 else "/home/claude/genus2ml/dataset.jsonl"
    meta_path = sys.argv[3] if len(sys.argv) > 3 else "/home/claude/genus2ml/dataset_meta.json"
    start_index = int(sys.argv[4]) if len(sys.argv) > 4 else 0

    rng = random.Random(2024)
    curve, a, ell, h, p = find_cryptographic_subgroup(p_start=300, min_bits=8, rng=rng)
    B = round(p ** 0.4)
    print(f"curve: p={p} ell={ell} h={h} B={B}", flush=True)

    pool = build_pool(curve, a, ell, max_candidates=2000)
    print(f"pool: {len(pool)} distinct candidate points", flush=True)

    coset_modulus = max(2, round(len(pool) ** 0.5))
    mode_weights = {"uniform": 0.5, "ap": 0.3, "coset": 0.2}
    print(f"mode_weights={mode_weights} coset_modulus={coset_modulus}", flush=True)

    generate_dataset(
        out_path=out_path,
        meta_path=meta_path,
        n_examples=n_examples,
        B=B,
        curve=curve,
        a=a,
        ell=ell,
        h=h,
        p=p,
        pool=pool,
        seed=77,
        start_index=start_index,
        mode_weights=mode_weights,
        coset_modulus=coset_modulus,
    )
