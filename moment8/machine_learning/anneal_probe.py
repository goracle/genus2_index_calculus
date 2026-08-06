"""
Existence probe: can any construction beat the observed e4 floor for a
given (curve, B, pool) instance -- before investing in AlphaZero-style
MCTS?

Two searches, both using the monotonic constraint Claire proposed
(each new point's pool index must be strictly greater than the
previously selected index -- this doubles as a free canonicalization:
a set is visited via exactly one increasing path, so there's no need
for a transposition table):

  1. Greedy: at each step, try every remaining candidate (pool index >
     last chosen), score F+{x} via IncrementalMoment.score_with (O(|F|)
     per candidate, not O(B^2)), commit whichever minimizes e4. Purely
     deterministic, O(B * pool_size) IncrementalMoment scores total.

  2. Simulated annealing over the same monotonic-sequence search space:
     state = a strictly-increasing sequence of B pool indices. Propose
     a move by resampling one index and repairing monotonicity, accept
     via Metropolis criterion on e4, cool geometrically. This explores
     more than pure greedy at the cost of many more score evaluations.

Both report whether they ever beat the floor for the CURRENT instance
(passed via --floor, or auto-derived from a matching dataset JSONL's
observed minimum e4 -- see resolve_floor), not just their final
answer -- a transient dip below floor during search is exactly the
"does a below-floor set exist at all" signal, even if the search
doesn't end there.

IMPORTANT: the floor value is instance-specific (depends on p, B, and
the curve) -- an earlier version of this script hardcoded FLOOR=175870
(the p=311, B=10 value) as a module-level constant, which silently
produced meaningless deltas/below_floor_hits when run against a
different (p, B) instance (e.g. p=3037, B=25, where the real floor is
~8.3M, not 175870). There is deliberately no hardcoded fallback now --
see resolve_floor.

Raises (does not silently degrade) if:
  - dataset_meta.json is missing or the reconstructed pool size
    doesn't match its recorded pool_size (would indicate build_pool's
    dedup logic or the generator params drifted from what produced
    the dataset)
  - no --floor is given and no matching dataset JSONL can be found to
    derive one from (see resolve_floor) -- silently defaulting to some
    other instance's floor is exactly the bug this docstring describes
"""

from __future__ import annotations

import argparse
import json
import math
import multiprocessing as mp
import os
import random
from collections import Counter
from pathlib import Path
from typing import List, Optional, Sequence, Tuple

from curve import Curve, Div2, jac_mul
from candidates import generate_candidates
from moment import IncrementalMoment


def resolve_floor(meta_path: str, floor_arg: Optional[float]) -> int:
    """Determine the correct floor for THIS instance (p, B, curve),
    never a hardcoded constant from a different instance.

    Priority:
      1. --floor if explicitly given on the CLI -- always trusted as-is.
      2. Otherwise, look for a dataset JSONL next to meta_path (same
         stem, e.g. dataset_p3000_test_meta.json -> dataset_p3000_test.jsonl,
         or dataset_meta.json -> dataset.jsonl) and use its observed
         minimum e4 as the floor.

    Raises if neither is available -- there is intentionally no
    silent fallback to some other instance's floor (that was the bug:
    a stale hardcoded 175870 produced plausible-looking but meaningless
    deltas when run against p=3037 data)."""
    if floor_arg is not None:
        return int(floor_arg)

    meta_p = Path(meta_path)
    # dataset_meta.json -> dataset.jsonl ; dataset_X_meta.json -> dataset_X.jsonl
    stem = meta_p.stem
    if stem.endswith("_meta"):
        jsonl_stem = stem[: -len("_meta")]
    else:
        raise ValueError(
            f"resolve_floor: --meta path '{meta_path}' does not end in "
            "'_meta' before the extension, can't infer the matching "
            "dataset JSONL filename -- pass --floor explicitly instead"
        )
    jsonl_path = meta_p.with_name(jsonl_stem + ".jsonl")
    if not jsonl_path.exists():
        raise ValueError(
            f"resolve_floor: no --floor given and no matching dataset "
            f"found at {jsonl_path} to derive one from -- pass --floor "
            "explicitly (there is no hardcoded default; a stale floor "
            "from a different instance would silently produce "
            "meaningless deltas, which is exactly what happened before "
            "this was fixed)"
        )

    min_e4 = None
    n = 0
    with open(jsonl_path) as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            e4 = json.loads(line)["e4"]
            n += 1
            if min_e4 is None or e4 < min_e4:
                min_e4 = e4
    if min_e4 is None:
        raise ValueError(f"resolve_floor: {jsonl_path} exists but has no records")
    print(f"(floor auto-derived: min e4 = {min_e4} over {n} examples in {jsonl_path})")
    return int(min_e4)


# ============================================================
#  Reconstruct the exact candidate pool from dataset_meta.json
# ============================================================

def load_pool(meta_path: str) -> Tuple[Curve, List[Tuple[int, int]], dict]:
    meta = json.loads(Path(meta_path).read_text())

    p = meta["p"]
    f_poly = tuple(meta["f_poly"])
    ell = meta["ell"]
    pool_size = meta["pool_size"]
    gu = tuple(meta["generator_u"])
    gv = tuple(meta["generator_v"])

    curve = Curve(p, f_poly)
    a = Div2(gu, gv)

    # build_pool in gen_dataset.py scans k=1.. via generate_candidates
    # with max_candidates=2000 (a hardcoded raw-candidate scan bound,
    # NOT the same as pool_size -- pool_size is what's left after
    # dedup-by-(x,y), which is smaller since each k can yield 0-2
    # points and duplicates get collapsed). Must match gen_dataset.py's
    # literal 2000 to reconstruct the same pool.
    raw = generate_candidates(curve, a, k_start=1, max_candidates=2000, k_max=ell)
    seen = {}
    for c in raw:
        pt = (c.x, c.y)
        if pt not in seen:
            seen[pt] = c
    pool = [(c.x, c.y) for c in seen.values()]

    if len(pool) != pool_size:
        raise ValueError(
            f"reconstructed pool size {len(pool)} != dataset_meta.json "
            f"pool_size {pool_size} -- generator/curve params or "
            "generate_candidates behavior have drifted from what "
            "produced the original dataset; refusing to proceed with "
            "a pool that isn't provably the same one the floor was "
            "measured against"
        )
    return curve, pool, meta


# ============================================================
#  Greedy: monotonic pool-index selection, always take the argmin
#
#  The inner loop scores every remaining candidate independently
#  (score_with does not mutate state) -- embarrassingly parallel. This
#  is the actual bottleneck: up to ~pool_size candidates per step, and
#  each score_with call is O(supp(T)^2), with supp(T) growing every
#  step (observed ~doubling near B=10 on this pool per the prior
#  version's comment). Annealing is NOT parallelized this way since
#  each proposal depends on the previously accepted state -- restarts
#  are parallelized instead, since those are independent.
# ============================================================

# Per-worker globals, set once via _init_worker at process-pool startup
# so each candidate task doesn't repickle curve/pool on every dispatch
# -- workers are long-lived, this is the standard pattern for "same
# large read-only context, many small tasks".
_W_CURVE: Optional[Curve] = None
_W_POOL: Optional[Sequence[Tuple[int, int]]] = None


def _init_worker(curve: Curve, pool: Sequence[Tuple[int, int]]) -> None:
    global _W_CURVE, _W_POOL
    _W_CURVE = curve
    _W_POOL = pool


def _score_candidate(args: Tuple[dict, list, int]) -> Tuple[int, int]:
    """Worker task: given the current T (as a plain dict, picklable),
    the current lifted-points list, and a candidate pool index, return
    (idx, e4-if-added).

    Both T and lifted must be seeded -- score_with's delta computation
    (_delta_for) iterates self.lifted, not self.T, to build the
    candidate's pairwise sums against every existing point. Seeding
    only T (as an earlier version of this function did) leaves
    inc.lifted empty, so _delta_for silently treats the candidate as
    though it were the only point in F (only the x+x term gets added)
    -- every score comes out wrong-but-plausible (too low, and still
    monotonically increasing step to step, which is what made the bug
    easy to miss until the final current_e4() assertion caught the
    mismatch). Seeding both keeps this consistent with a non-parallel
    IncrementalMoment that had .add() called for every prior step.
    """
    if _W_CURVE is None or _W_POOL is None:
        raise RuntimeError(
            "_score_candidate: worker globals not initialized -- this task "
            "ran on a pool that did not go through _init_worker"
        )
    T_dict, lifted, idx = args
    inc = IncrementalMoment(_W_CURVE)
    inc.T = Counter(T_dict)
    inc.lifted = list(lifted)
    e4 = inc.score_with(_W_POOL[idx])
    return idx, e4


def greedy_search(curve: Curve, pool: Sequence[Tuple[int, int]], B: int,
                   verbose: bool = True, n_workers: int = 1) -> Tuple[List[int], int]:
    """Returns (chosen pool indices, final e4). Deterministic regardless
    of n_workers -- multiprocessing only parallelizes the independent
    per-candidate scoring within a step; argmin selection is still
    exact. n_workers=1 runs single-process (no pool startup cost)."""
    import time
    if n_workers <= 0:
        raise ValueError(f"greedy_search: n_workers must be positive, got {n_workers}")

    inc = IncrementalMoment(curve)
    chosen: List[int] = []
    last_idx = -1
    n = len(pool)

    procpool = None
    if n_workers > 1:
        ctx = mp.get_context("spawn")
        procpool = ctx.Pool(processes=n_workers, initializer=_init_worker, initargs=(curve, pool))

    try:
        for step in range(B):
            t0 = time.time()
            remaining = n - (last_idx + 1)
            if remaining < B - step:
                raise RuntimeError(
                    f"greedy_search: only {remaining} candidates left after index "
                    f"{last_idx} but need {B - step} more points -- pool "
                    f"exhausted under the monotonic constraint (pool_size={n}, B={B})"
                )
            candidate_idxs = range(last_idx + 1, n)
            best_idx = None
            best_e4 = None

            if procpool is not None:
                T_snapshot = dict(inc.T)
                lifted_snapshot = list(inc.lifted)
                tasks = [(T_snapshot, lifted_snapshot, idx) for idx in candidate_idxs]
                chunksize = max(1, len(tasks) // (n_workers * 4))
                for idx, e4 in procpool.imap_unordered(_score_candidate, tasks, chunksize=chunksize):
                    if best_e4 is None or e4 < best_e4:
                        best_e4 = e4
                        best_idx = idx
            else:
                for idx in candidate_idxs:
                    e4 = inc.score_with(pool[idx])
                    if best_e4 is None or e4 < best_e4:
                        best_e4 = e4
                        best_idx = idx

            inc.add(pool[best_idx])
            chosen.append(best_idx)
            last_idx = best_idx
            if verbose:
                print(f"  step {step+1}/{B}: idx={best_idx} e4={best_e4} "
                      f"({time.time()-t0:.1f}s, supp(T)={len(inc.T)})", flush=True)
    finally:
        if procpool is not None:
            procpool.close()
            procpool.join()

    final_e4 = inc.current_e4()
    if final_e4 != best_e4:
        raise AssertionError(
            f"greedy_search: incremental final e4 ({final_e4}) disagrees with "
            f"last committed score_with result ({best_e4}) -- IncrementalMoment "
            "state is inconsistent, do not trust this result"
        )
    return chosen, final_e4


# ============================================================
#  Simulated annealing over strictly-increasing index sequences
# ============================================================

def _random_monotonic_sequence(n: int, B: int, rng: random.Random) -> List[int]:
    if B > n:
        raise ValueError(f"B={B} exceeds pool size n={n}")
    return sorted(rng.sample(range(n), B))


def _e4_of_sequence(curve: Curve, pool: Sequence[Tuple[int, int]], seq: Sequence[int]) -> int:
    inc = IncrementalMoment(curve)
    for idx in seq:
        inc.add(pool[idx])
    return inc.current_e4()


def _propose(seq: List[int], n: int, rng: random.Random) -> List[int]:
    """Resample one index to a value not already present, re-sort to
    restore the strictly-increasing invariant. O(B log B)."""
    seq = list(seq)
    pos = rng.randrange(len(seq))
    existing = set(seq)
    # rejection-sample a replacement not already in the sequence; pool
    # sizes here (hundreds) make this fast in expectation
    for _ in range(10_000):
        candidate = rng.randrange(n)
        if candidate not in existing:
            seq[pos] = candidate
            seq.sort()
            return seq
    raise RuntimeError(
        "_propose: failed to find a replacement index not already in the "
        f"sequence after 10000 tries (pool n={n}, |seq|={len(seq)}) -- "
        "pool is too small relative to B for this rejection sampler"
    )


def anneal_search(
    curve: Curve,
    pool: Sequence[Tuple[int, int]],
    B: int,
    iters: int,
    t0: float,
    t_min: float,
    seed: int,
    floor: int,
    restart_id: int = 0,
    progress_every: float = 5.0,
) -> Tuple[int, List[int], int, int]:
    """Metropolis simulated annealing. Returns (restart_id, best_seq,
    best_e4, n_below_floor) -- n_below_floor counts how many *distinct
    visited* states (not just the final/best) ever scored under `floor`,
    since that's the existence signal we actually care about. `floor`
    must be the value for THIS (curve, B, pool) instance -- see
    resolve_floor; there is no hardcoded default here on purpose.

    Prints its own progress at most every `progress_every` seconds
    (wall clock, per this restart), tagged with restart_id, so when run
    under a multiprocessing Pool each worker's own stdout still reaches
    the terminal (child-process stdout is inherited, not captured) --
    without this, a Pool.map call is silent until every restart
    finishes, which is indistinguishable from a hang."""
    import time
    rng = random.Random(seed)
    n = len(pool)

    cur_seq = _random_monotonic_sequence(n, B, rng)
    cur_e4 = _e4_of_sequence(curve, pool, cur_seq)
    best_seq, best_e4 = cur_seq, cur_e4
    n_below_floor = 1 if cur_e4 < floor else 0

    cooling = (t_min / t0) ** (1.0 / max(iters, 1))
    temp = t0

    t_start = time.time()
    t_last_print = t_start

    for i in range(iters):
        cand_seq = _propose(cur_seq, n, rng)
        cand_e4 = _e4_of_sequence(curve, pool, cand_seq)

        if cand_e4 < floor:
            n_below_floor += 1

        delta = cand_e4 - cur_e4
        if delta <= 0 or rng.random() < math.exp(-delta / max(temp, 1e-12)):
            cur_seq, cur_e4 = cand_seq, cand_e4
            if cur_e4 < best_e4:
                best_seq, best_e4 = cur_seq, cur_e4

        temp *= cooling

        now = time.time()
        if now - t_last_print >= progress_every:
            rate = (i + 1) / (now - t_start)
            print(
                f"    [restart {restart_id}] iter {i+1}/{iters} "
                f"({rate:.1f}/s) best_e4={best_e4} cur_e4={cur_e4} "
                f"temp={temp:.1f} below_floor_hits={n_below_floor}",
                flush=True,
            )
            t_last_print = now

    print(
        f"    [restart {restart_id}] DONE {iters} iters in "
        f"{time.time()-t_start:.1f}s, best_e4={best_e4}, "
        f"below_floor_hits={n_below_floor}",
        flush=True,
    )
    return restart_id, best_seq, best_e4, n_below_floor


def _anneal_restart_worker(args: Tuple[Curve, Sequence[Tuple[int, int]], int, int, float, float, int, int, int]) -> Tuple[int, List[int], int, int]:
    """Top-level (picklable) wrapper so anneal_search can run under
    Pool.imap_unordered -- restarts are independent (each seeds its own
    rng and starting sequence), so unlike greedy this parallelizes at
    the restart level rather than needing shared per-step state."""
    curve, pool, B, iters, t0, t_min, seed, restart_id, floor = args
    return anneal_search(curve, pool, B, iters=iters, t0=t0, t_min=t_min,
                          seed=seed, restart_id=restart_id, floor=floor)


# ============================================================
#  CLI
# ============================================================

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--meta", default="dataset_meta.json")
    ap.add_argument("--iters", type=int, default=5000, help="annealing iterations per restart")
    ap.add_argument("--t0", type=float, default=float(FLOOR) * 0.05, help="initial temperature")
    ap.add_argument("--t-min", type=float, default=1.0, help="final temperature")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--restarts", type=int, default=None,
                     help="independent annealing restarts, each fully sequential "
                          "internally but embarrassingly parallel across restarts -- "
                          "default matches --workers so all cores get used (a low "
                          "--restarts count like the old default of 3 leaves most "
                          "workers idle regardless of --workers)")
    ap.add_argument("--skip-greedy", action="store_true",
                     help="skip greedy (its per-step cost grows sharply with |F|, "
                          "observed ~doubling each step near B=10 on this pool; "
                          "can take several minutes even parallelized -- default "
                          "is to run it anyway")
    ap.add_argument("--workers", type=int, default=max(1, (os.cpu_count() or 1) - 1),
                     help="worker processes for greedy candidate scoring and for "
                          "parallelizing annealing restarts (default: cpu_count-1)")
    args = ap.parse_args()
    if args.restarts is None:
        args.restarts = args.workers

    curve, pool, meta = load_pool(args.meta)
    B = meta["B"]
    print(f"Loaded pool: p={meta['p']}, pool_size={len(pool)}, B={B}, floor={FLOOR}, workers={args.workers}")

    if args.skip_greedy:
        print("\n=== Greedy: skipped (--skip-greedy) ===")
    else:
        print("\n=== Greedy (monotonic pool-index, argmin at each step) ===")
        print(f"(parallelized over {args.workers} workers; still expect the "
              "last couple of steps to dominate wall time since supp(T) "
              "grows with each addition)")
        g_idx, g_e4 = greedy_search(curve, pool, B, n_workers=args.workers)
        print(f"greedy final e4 = {g_e4}  (floor={FLOOR}, delta={g_e4 - FLOOR:+d})")
        if g_e4 < FLOOR:
            print(f"*** GREEDY BEAT THE FLOOR *** indices={g_idx}")

    print(f"\n=== Simulated annealing ({args.restarts} restarts x {args.iters} iters, "
          f"parallelized across restarts) ===")
    global_best_e4 = None
    global_best_seq = None
    total_below_floor = 0

    restart_args = [
        (curve, pool, B, args.iters, args.t0, args.t_min, args.seed + r, r)
        for r in range(args.restarts)
    ]
    n_restart_workers = min(args.workers, args.restarts)
    print(f"(each restart prints its own progress line every ~5s -- tagged "
          f"'[restart N]'; {n_restart_workers} restarts run concurrently, "
          f"so lines will interleave)")
    ctx = mp.get_context("spawn")
    with ctx.Pool(processes=n_restart_workers) as restart_pool:
        # imap_unordered (not map): results are yielded as each restart
        # finishes, not all at once after every restart completes -- so
        # you see "[restart N] DONE" lines streaming in rather than one
        # silent wall of nothing until the slowest restart finishes.
        results = list(restart_pool.imap_unordered(_anneal_restart_worker, restart_args))

    for restart_id, seq, e4, n_below in results:
        total_below_floor += n_below
        tag = " <-- BELOW FLOOR" if e4 < FLOOR else ""
        print(f"  restart {restart_id}: best e4 = {e4}  (delta={e4 - FLOOR:+d}){tag}")
        if global_best_e4 is None or e4 < global_best_e4:
            global_best_e4, global_best_seq = e4, seq

    print(f"\nBest over all restarts: e4={global_best_e4} (delta={global_best_e4 - FLOOR:+d})")
    print(f"Total visited states scoring below floor across all restarts: {total_below_floor}")
    if global_best_e4 < FLOOR:
        print(f"*** ANNEALING BEAT THE FLOOR *** indices={global_best_seq}")
    else:
        print(
            "No search beat the floor. This is evidence (not proof) that "
            f"{FLOOR} is close to a real combinatorial lower bound rather "
            "than an artifact of uniform sampling -- worth the analytic "
            "B_h[g]/Sidon-set sanity check before investing in MCTS."
        )


if __name__ == "__main__":
    main()
