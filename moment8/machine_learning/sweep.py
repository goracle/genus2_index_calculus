"""
Measure the e4_moment floor (min over many uniform random size-B subsets F)
across several (p, B) points, to get an actual multi-point exponent fit
instead of the earlier 2-point eyeball.

Uses the pure-Python O(p^2) jacobian_order_frobenius (no Sage available in
this sandbox), so p is capped in the low thousands to keep order-finding
and pool-building tractable within a reasonable wall clock.
"""
from __future__ import annotations

import json
import random
import time

from curve import Curve, find_subgroup_generator, jacobian_order_frobenius, next_prime_at_least
from candidates import generate_candidates
from moment import e4_moment


def find_subgroup_pure_python(p_start, min_bits, rng, f_poly=None, max_prime_tries=50):
    """Same shape as curve.find_cryptographic_subgroup but uses the
    pure-Python jacobian_order_frobenius instead of the Sage-backed one
    (no Sage on this box)."""
    from sympy import factorint
    kwargs = {}
    if f_poly is not None:
        kwargs["f_poly"] = f_poly
    p = next_prime_at_least(p_start)
    for _ in range(max_prime_tries):
        curve = Curve(p, **kwargs) if f_poly is not None else Curve(p)
        jac_order = jacobian_order_frobenius(curve)
        factors = factorint(jac_order)
        ell = max(factors.keys())
        h = jac_order // ell
        if min_bits is None or ell.bit_length() >= min_bits:
            a, ell_c, h_c = find_subgroup_generator(curve, rng, jac_order=jac_order)
            return curve, a, ell_c, h_c, p
        p = next_prime_at_least(p + 1)
    raise RuntimeError(f"no suitable subgroup found from p_start={p_start}")


def measure_floor(curve, a, ell, B, n_draws, seed, pool_max=2000):
    p = curve.p
    t0 = time.time()
    cands = generate_candidates(curve, a, k_start=1, max_candidates=pool_max, k_max=ell)
    seen = {}
    for c in cands:
        pt = (c.x, c.y)
        if pt not in seen:
            seen[pt] = c
    pool = list(seen.values())
    t_pool = time.time() - t0

    if len(pool) < B:
        raise RuntimeError(f"pool too small ({len(pool)}) for B={B} at p={p}")

    rng = random.Random(seed)
    e4_vals = []
    t0 = time.time()
    for _ in range(n_draws):
        F = rng.sample(pool, B)
        points = [(c.x, c.y) for c in F]
        e4_vals.append(e4_moment(points, curve))
    t_draws = time.time() - t0

    floor = min(e4_vals)
    return {
        "p": p,
        "ell_bits": ell.bit_length(),
        "B": B,
        "pool_size": len(pool),
        "n_draws": n_draws,
        "floor": floor,
        "mean": sum(e4_vals) / len(e4_vals),
        "max": max(e4_vals),
        "t_pool_s": round(t_pool, 2),
        "t_draws_s": round(t_draws, 2),
    }


if __name__ == "__main__":
    rng = random.Random(2024)
    results = []

    # Sweep 1: B ~ round(p^0.4), matching gen_dataset.py's convention,
    # across several p to get an actual multi-point exponent fit.
    p_starts = [150, 300, 600, 1200, 2500]
    for p_start in p_starts:
        try:
            curve, a, ell, h, p = find_subgroup_pure_python(p_start, min_bits=6, rng=rng)
            B = max(4, round(p ** 0.4))
            res = measure_floor(curve, a, ell, B, n_draws=300, seed=77)
            res["sweep"] = "B~p^0.4"
            results.append(res)
            print("done:", res, flush=True)
        except Exception as e:
            print(f"FAILED at p_start={p_start}: {e}", flush=True)

    with open("sweep_results.json", "w") as f:
        json.dump(results, f, indent=2)
    print("wrote sweep_results.json")
