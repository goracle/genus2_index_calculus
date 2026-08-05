"""
Sage-accelerated version of sweep.py, for pushing the (p, floor) power-law
fit out to p ~ 10^4 - 10^6+, which the pure-Python O(p^2) order-finder
couldn't reach in reasonable time.

Two speedups over the original sweep.py:
  1. Jacobian order via Sage's HyperellipticCurve(...).frobenius_polynomial()
     (Kedlaya's algorithm, ~O(p^{1/2} polylog p)) instead of the O(p^2)
     direct point-count in curve.py. This is the only thing that makes
     p in the 10^4-10^6 range tractable at all.
  2. multiprocessing.Pool to run independent uniform-F draws (the
     e4_moment/quad_histogram computation) across cores in parallel, since
     each draw is embarrassingly parallel (independent RNG samples of F,
     scored independently) -- this doesn't change per-draw complexity, it
     just uses however many cores you have.

Run with ONE of these, depending on what your Sage build accepts (they
are not all guaranteed to work the same way across Sage versions -- try
in order, use whichever actually gets past argument parsing):

    sage --python sage_sweep.py 5000 20000 --draws 60 --procs 8
    sage -python sage_sweep.py -- 5000 20000 --draws 60 --procs 8
    $(sage -sh -c 'which python3') sage_sweep.py 5000 20000 --draws 60 --procs 8

The third form is the most reliable: it asks Sage for the path to ITS
OWN bundled python3 (the one with the `sage` library importable) and
invokes that directly, bypassing Sage's own CLI arg parser entirely --
useful since some `sage` launchers try to interpret every flag/arg
themselves (as happened with `-python` above) before anything reaches
this script's argparse.

A print() has been added immediately at import time (see bottom of
file, "SAGE_SWEEP: process started") specifically to distinguish "the
Sage loader is hanging/silent before main() ever runs" from "main()
ran but produced no visible output" -- if you don't see that line at
all, the problem is upstream of this script (invocation/loader), not
in the script's logic.

Writes/appends to sage_sweep_results.json incrementally (one line flushed
per completed p point), same shape as sweep.py's output plus a couple of
extra fields, so it can be loaded alongside the earlier pure-python results
for a combined fit.

NOTE: this still uses curve.py's Cantor-arithmetic / candidates.py /
moment.py Python implementation for everything EXCEPT the order
computation -- Sage is only used as a subprocess-free in-process call to
compute #Jac(C/F_p) quickly (curve.py already has
jacobian_order_frobenius_sage, which shells out to a `sage` binary; here
we call the equivalent Sage library functions directly in-process instead,
since this whole script is meant to be run under `sage -python`, i.e.
Sage's own Python environment, not a subprocess).

Everything downstream of the order (subgroup generator search, candidate
generation, pair-sum/quad-histogram e4_moment computation) is still your
existing pure-Python code -- unchanged, just fed a curve whose order came
from Sage instead of from the slow direct count. If B/pool sizes get large
enough that quad_histogram's O(supp(T)^2) becomes the new bottleneck,
that's a separate optimization (not attempted here, per your "don't
bother much testing" -- ping me if a specific p turns out to hang there
and we can profile it).
"""
from __future__ import annotations

import json
import os
import random
import sys
import time
import multiprocessing as mp

print("SAGE_SWEEP: process started, argv=", sys.argv, flush=True)

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from curve import Curve, find_subgroup_generator, next_prime_at_least
from candidates import generate_candidates
from moment import e4_moment

# sympy for factoring the (now Sage-derived) jacobian order
from sympy import factorint


def jac_order_sage_inprocess(curve: Curve) -> int:
    """Compute #Jac(C/F_p) via Sage's frobenius_polynomial(), called
    in-process (this file must be run under `sage -python`). Mirrors
    curve.py's jacobian_order_frobenius_sage but avoids the subprocess
    round trip since we're already inside Sage."""
    t_import = time.time()
    from sage.all import GF, PolynomialRing, HyperellipticCurve, ZZ
    print(f"SAGE_SWEEP: sage.all import took {time.time()-t_import:.1f}s (only shown first call in a process)", flush=True)

    p = curve.p
    F = GF(p)
    R = PolynomialRing(F, 'x')
    x = R.gen()
    f = sum(int(c) * x**i for i, c in enumerate(curve.f_poly))
    H = HyperellipticCurve(f)
    chi = H.frobenius_polynomial()
    N = ZZ(chi(1))
    return int(N)


def find_subgroup_sage(p_start, min_bits, rng, f_poly=None, max_prime_tries=50):
    """Same shape as curve.find_cryptographic_subgroup, but uses the
    in-process Sage order function above instead of curve.py's
    subprocess-based jacobian_order_frobenius_sage (faster: no repeated
    subprocess spawn cost across the p-search loop) and instead of the
    O(p^2) pure-python fallback (too slow at these p)."""
    kwargs = {}
    if f_poly is not None:
        kwargs["f_poly"] = f_poly
    p = next_prime_at_least(p_start)
    for _ in range(max_prime_tries):
        curve = Curve(p, **kwargs) if f_poly is not None else Curve(p)
        jac_order = jac_order_sage_inprocess(curve)
        factors = factorint(jac_order)
        ell = max(factors.keys())
        h = jac_order // ell
        if min_bits is None or ell.bit_length() >= min_bits:
            a, ell_c, h_c = find_subgroup_generator(curve, rng, jac_order=jac_order)
            return curve, a, ell_c, h_c, p
        p = next_prime_at_least(p + 1)
    raise RuntimeError(f"no suitable subgroup found from p_start={p_start}")


def build_pool(curve, a, ell, max_candidates=2000):
    cands = generate_candidates(curve, a, k_start=1, max_candidates=max_candidates, k_max=ell)
    seen = {}
    for c in cands:
        pt = (c.x, c.y)
        if pt not in seen:
            seen[pt] = c
    return list(seen.values())


# ---- multiprocessing worker -------------------------------------------------
#
# Each worker draws a uniform-random size-B subset from the pool (given a
# per-worker seed so draws across workers don't repeat the same subset) and
# scores it with e4_moment. curve/pool are passed via a module-level global
# set by _init_worker, populated once per worker process (avoids re-pickling
# the (potentially large) pool/curve on every single task).

_worker_curve = None
_worker_pool = None
_worker_B = None


def _init_worker(curve, pool, B):
    global _worker_curve, _worker_pool, _worker_B
    _worker_curve = curve
    _worker_pool = pool
    _worker_B = B


def _draw_and_score(seed):
    rng = random.Random(seed)
    F = rng.sample(_worker_pool, _worker_B)
    points = [(c.x, c.y) for c in F]
    return e4_moment(points, _worker_curve)


def measure_floor_parallel(curve, a, ell, B, n_draws, base_seed, procs, pool_max=2000):
    t0 = time.time()
    pool = build_pool(curve, a, ell, max_candidates=pool_max)
    t_pool = time.time() - t0

    if len(pool) < B:
        raise RuntimeError(f"pool too small ({len(pool)}) for B={B} at p={curve.p}")

    seeds = [base_seed + i for i in range(n_draws)]
    t0 = time.time()
    if procs and procs > 1:
        with mp.Pool(processes=procs, initializer=_init_worker, initargs=(curve, pool, B)) as p_:
            e4_vals = p_.map(_draw_and_score, seeds)
    else:
        _init_worker(curve, pool, B)
        e4_vals = [_draw_and_score(s) for s in seeds]
    t_draws = time.time() - t0

    return {
        "p": curve.p,
        "B": B,
        "pool_size": len(pool),
        "n_draws": n_draws,
        "floor": min(e4_vals),
        "mean": sum(e4_vals) / len(e4_vals),
        "max": max(e4_vals),
        "t_pool_s": round(t_pool, 2),
        "t_draws_s": round(t_draws, 2),
        "procs": procs,
    }


def run_one(p_start, n_draws, procs, results_path):
    rng = random.Random(2024 + p_start)
    try:
        t0 = time.time()
        curve, a, ell, h, p = find_subgroup_sage(p_start, min_bits=6, rng=rng)
        t_subgroup = time.time() - t0
        B = max(4, round(p ** 0.4))
        res = measure_floor_parallel(curve, a, ell, B, n_draws=n_draws, base_seed=77, procs=procs)
        res["p_start"] = p_start
        res["t_subgroup_s"] = round(t_subgroup, 2)
        res["ell_bits"] = ell.bit_length()
        print("done:", res, flush=True)
    except Exception as e:
        res = {"p_start": p_start, "error": str(e)}
        print(f"FAILED at p_start={p_start}: {e}", flush=True)

    try:
        with open(results_path) as f:
            existing = json.load(f)
    except FileNotFoundError:
        existing = []
    existing.append(res)
    with open(results_path, "w") as f:
        json.dump(existing, f, indent=2)
    return res


if __name__ == "__main__":
    print("SAGE_SWEEP: entered __main__", flush=True)
    import argparse

    ap = argparse.ArgumentParser()
    ap.add_argument("p_starts", type=int, nargs="+", help="one or more p_start values to sweep")
    ap.add_argument("--draws", type=int, default=60, help="uniform draws per p point (default 60)")
    ap.add_argument("--procs", type=int, default=max(1, (os.cpu_count() or 4) - 1),
                     help="worker processes for parallel draws (default: cpu_count-1)")
    ap.add_argument("--out", default="sage_sweep_results.json")
    args = ap.parse_args()

    print(f"procs={args.procs}  draws={args.draws}  p_starts={args.p_starts}", flush=True)

    for p_start in args.p_starts:
        run_one(p_start, n_draws=args.draws, procs=args.procs, results_path=args.out)

    print(f"all done, results in {args.out}")
