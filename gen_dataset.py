"""
Generate a training dataset for the 8th-moment set-selection task.

Fixed curve + cryptographic subgroup, fixed candidate pool (built once).
Each example is a uniformly random size-B subset F of the pool, scored by
e4_moment. Written incrementally to a JSONL checkpoint file so a long run
can be interrupted/resumed without losing progress.

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
  "e4": int                     # target: E4(F), to be minimized
}

Curve parameters (p, f_poly, subgroup order ell, cofactor h, generator a)
are written once to a header line / sidecar file, since they're constant
across the whole dataset.
"""

from __future__ import annotations

import json
import random
import time
from pathlib import Path

from curve import Curve, find_cryptographic_subgroup
from candidates import generate_candidates, Candidate
from moment import e4_moment


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
):
    """Generate examples [start_index, start_index + n_examples), appending
    to out_path. Uses a seeded RNG advanced deterministically by
    start_index draws so repeated resumed calls (each a fresh process)
    produce the same sequence a single long run would have -- calling
    this with start_index=0..999 then 1000..1999 etc. gives the identical
    dataset to one call with n_examples=2000, just spread across
    multiple process invocations to fit within a wall-clock budget.
    """
    sample_rng = random.Random(seed)
    # fast-forward the RNG stream to start_index by drawing (and discarding)
    # the same number of samples a from-scratch run would have consumed
    for _ in range(start_index):
        sample_rng.sample(pool, B)

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
        }
        Path(meta_path).write_text(json.dumps(meta, indent=2))

    t_start = time.time()
    mode = "a" if start_index > 0 else "w"
    with open(out_path, mode) as f:
        for offset in range(n_examples):
            i = start_index + offset
            chosen: list[Candidate] = sample_rng.sample(pool, B)
            points = [(c.x, c.y) for c in chosen]
            e4 = e4_moment(points, curve)
            record = {
                "example_id": i,
                "k_values": [c.k for c in chosen],
                "pair_ids": [c.pair_id for c in chosen],
                "points": [[c.x, c.y] for c in chosen],
                "e4": e4,
            }
            f.write(json.dumps(record) + "\n")

            if (offset + 1) % checkpoint_every == 0:
                f.flush()
            if (offset + 1) % log_every == 0:
                elapsed = time.time() - t_start
                rate = (offset + 1) / elapsed
                print(
                    f"[{offset+1}/{n_examples} this chunk, global idx {i}] "
                    f"e4={e4} elapsed={elapsed:.1f}s rate={rate:.2f}/s",
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
    )
