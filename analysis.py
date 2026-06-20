#!/usr/bin/env python3
"""
Analyze CONJCLOS store-event .bin files.

Expected schema JSON format:
{
  "magic": "CONJCLOS",
  "version": 3,
  "header_bytes": 16,
  "record_bytes": 192,
  "dtype": "int64",
  "endian": "little",
  "n_fields": 24,
  "fields": [...]
}

Usage:
  python analyze_conjclos.py --bin store_events.bin --schema schema.json
  python analyze_conjclos.py --bin store_events.bin --schema schema.json --tid 7
  python analyze_conjclos.py --bin store_events.bin --schema schema.json --limit 2000000
"""

from __future__ import annotations

import argparse
import json
import math
import statistics
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Iterable, List, Tuple

import numpy as np


# -----------------------------
# Loading
# -----------------------------

FIELD_ORDER = [
    "c0", "c1", "v0", "v1", "i0", "neg_al", "neg_be", "raw_steps",
    "prev_col", "prev_al", "prev_be", "store_step", "px_store", "py_store",
    "combined_al", "combined_be", "step_gap", "al_cur", "px_anchor",
    "py_anchor", "a_raw", "a_bucket", "tid", "_pad"
]


def build_dtype(schema: dict) -> np.dtype:
    endian = schema.get("endian", "little")
    if endian != "little":
        raise ValueError(f"Only little-endian supported in this script, got {endian!r}")

    fields = schema["fields"]
    names = [f["name"] for f in fields]
    offsets = [int(f["offset"]) for f in fields]
    if names != FIELD_ORDER:
        # Keep this warning strict-ish because downstream code assumes these names.
        missing = [n for n in FIELD_ORDER if n not in names]
        extra = [n for n in names if n not in FIELD_ORDER]
        raise ValueError(
            "Field list does not match expected CONJCLOS layout.\n"
            f"Missing: {missing}\nExtra: {extra}\nGot: {names}"
        )

    descr = []
    for f in fields:
        name = f["name"]
        dt = f["dtype"]
        if dt != "int64":
            raise ValueError(f"Only int64 fields supported, got {name}={dt}")
        descr.append((name, "<i8"))

    dtype = np.dtype(descr, align=False)
    if dtype.itemsize != int(schema["record_bytes"]):
        raise ValueError(
            f"dtype.itemsize={dtype.itemsize} != record_bytes={schema['record_bytes']}"
        )
    return dtype


def load_conjclos(bin_path: Path, schema_path: Path, limit: int | None = None) -> np.memmap:
    schema = json.loads(schema_path.read_text())
    if schema.get("magic") != "CONJCLOS":
        raise ValueError(f"Bad magic: {schema.get('magic')!r}")
    if int(schema.get("version", -1)) != 3:
        raise ValueError(f"Unexpected version: {schema.get('version')!r}")

    header_bytes = int(schema["header_bytes"])
    dtype = build_dtype(schema)

    st = bin_path.stat()
    total_bytes = st.st_size
    if total_bytes < header_bytes:
        raise ValueError("File too small to contain header")

    n_records = (total_bytes - header_bytes) // dtype.itemsize
    if (total_bytes - header_bytes) % dtype.itemsize != 0:
        print(
            f"[warn] file size not an exact multiple of record size; "
            f"ignoring trailing {((total_bytes - header_bytes) % dtype.itemsize)} bytes"
        )

    if limit is not None:
        n_records = min(n_records, int(limit))

    return np.memmap(
        bin_path,
        dtype=dtype,
        mode="r",
        offset=header_bytes,
        shape=(n_records,),
    )


# -----------------------------
# Small utilities
# -----------------------------

def counter_from_array(arr: np.ndarray) -> Counter:
    return Counter(map(int, arr))


def counter_from_pairs(a: np.ndarray, b: np.ndarray) -> Counter:
    return Counter(zip(map(int, a), map(int, b)))


def renyi2_support_from_counts(counts: Counter) -> Tuple[int, int, float, float]:
    """
    Returns:
      N: total mass
      K: distinct items
      S2: collision-support estimate N^2 / sum n_i^2
      H2: log(S2) (natural log)
    """
    N = sum(counts.values())
    K = len(counts)
    f2 = sum(v * v for v in counts.values())
    if f2 == 0:
        return N, K, float("nan"), float("nan")
    S2 = (N * N) / f2
    H2 = math.log(S2)
    return N, K, S2, H2


def alpha2_from_S2(S2: float, p: int) -> float:
    """
    If S2 ~ p^(2*alpha), then alpha = log(S2) / (2 log p).
    """
    return math.log(S2) / (2.0 * math.log(p))


def shannon_entropy_from_counts(counts: Counter) -> float:
    N = sum(counts.values())
    if N == 0:
        return float("nan")
    H = 0.0
    for v in counts.values():
        if v <= 0:
            continue
        p = v / N
        H -= p * math.log(p)
    return H


def conditional_shannon_entropy(x: np.ndarray, y: np.ndarray) -> float:
    """
    H(X|Y) in nats, computed from discrete counts.
    """
    xy = counter_from_pairs(x, y)
    y_cnt = counter_from_array(y)
    N = len(x)
    if N == 0:
        return float("nan")
    H = 0.0
    for (xv, yv), c in xy.items():
        py = y_cnt[int(yv)] / N
        pxy = c / N
        H -= pxy * math.log(pxy / py)
    return H


def discrete_mutual_information(x: np.ndarray, y: np.ndarray) -> float:
    """
    I(X;Y) in nats.
    """
    return shannon_entropy_from_counts(counter_from_array(x)) + shannon_entropy_from_counts(counter_from_array(y)) - shannon_entropy_from_counts(counter_from_pairs(x, y))


def autocorr_int64(x: np.ndarray, lag: int) -> float:
    if lag <= 0 or lag >= len(x):
        return float("nan")
    a = x[:-lag].astype(np.float64)
    b = x[lag:].astype(np.float64)
    a -= a.mean()
    b -= b.mean()
    denom = a.std() * b.std()
    if denom == 0:
        return float("nan")
    return float(np.mean(a * b) / denom)


def bucketize(values: np.ndarray, n_bins: int, lo: int | None = None, hi: int | None = None) -> np.ndarray:
    """
    Return integer bins 0..n_bins-1.
    """
    v = values.astype(np.int64)
    if lo is None:
        lo = int(v.min())
    if hi is None:
        hi = int(v.max()) + 1
    if hi <= lo:
        return np.zeros_like(v, dtype=np.int64)

    edges = np.linspace(lo, hi, n_bins + 1, dtype=np.float64)
    out = np.searchsorted(edges, v, side="right") - 1
    out = np.clip(out, 0, n_bins - 1)
    return out.astype(np.int64)


def lagged_conditional_prob(hit: np.ndarray, lag: int) -> float:
    """
    P(hit[t+lag]=1 | hit[t]=1)
    """
    if lag <= 0 or lag >= len(hit):
        return float("nan")
    src = hit[:-lag]
    dst = hit[lag:]
    denom = int(src.sum())
    if denom == 0:
        return float("nan")
    return float((src & dst).sum() / denom)


# -----------------------------
# Graph routines
# -----------------------------

def tarjan_scc(nodes: List[int], edges: Dict[int, Dict[int, int]]) -> List[List[int]]:
    """
    Tarjan SCC on a small directed graph represented by adjacency dicts.
    Works well for prev_col-sized graphs (typically ~1e3-1e4 nodes).
    """
    index = 0
    stack: List[int] = []
    on_stack = set()
    idx: Dict[int, int] = {}
    low: Dict[int, int] = {}
    out: List[List[int]] = []

    def strongconnect(v: int):
        nonlocal index
        idx[v] = index
        low[v] = index
        index += 1
        stack.append(v)
        on_stack.add(v)

        for w in edges.get(v, {}):
            if w not in idx:
                strongconnect(w)
                low[v] = min(low[v], low[w])
            elif w in on_stack:
                low[v] = min(low[v], idx[w])

        if low[v] == idx[v]:
            comp = []
            while True:
                w = stack.pop()
                on_stack.remove(w)
                comp.append(w)
                if w == v:
                    break
            out.append(comp)

    for v in nodes:
        if v not in idx:
            strongconnect(v)

    return out


def pagerank_sparse(nodes: List[int], edges: Dict[int, Dict[int, int]], iters: int = 100, tol: float = 1e-12, damping: float = 0.85) -> Dict[int, float]:
    """
    Simple weighted PageRank over a sparse adjacency dictionary.
    """
    n = len(nodes)
    if n == 0:
        return {}
    node_to_i = {v: i for i, v in enumerate(nodes)}
    pr = np.full(n, 1.0 / n, dtype=np.float64)

    out_w = np.zeros(n, dtype=np.float64)
    for v in nodes:
        i = node_to_i[v]
        out_w[i] = sum(edges.get(v, {}).values())

    for _ in range(iters):
        new = np.full(n, (1.0 - damping) / n, dtype=np.float64)
        dangling_mass = pr[out_w == 0].sum()
        new += damping * dangling_mass / n

        for v in nodes:
            i = node_to_i[v]
            wsum = out_w[i]
            if wsum <= 0:
                continue
            for w, c in edges.get(v, {}).items():
                j = node_to_i[w]
                new[j] += damping * pr[i] * (c / wsum)

        delta = np.abs(new - pr).sum()
        pr = new
        if delta < tol:
            break

    return {v: float(pr[node_to_i[v]]) for v in nodes}


# -----------------------------
# Diagnostics
# -----------------------------

def summarize_basic(data: np.ndarray) -> None:
    print("=== Basic summary ===")
    print(f"records               : {len(data)}")
    print(f"threads               : {len(np.unique(data['tid']))}")
    print(f"raw_steps min/max     : {int(data['raw_steps'].min())} / {int(data['raw_steps'].max())}")
    print(f"store_step min/max    : {int(data['store_step'].min())} / {int(data['store_step'].max())}")
    print(f"step_gap min/median/max: {int(data['step_gap'].min())} / {float(np.median(data['step_gap'])):.1f} / {int(data['step_gap'].max())}")
    print(f"prev_col unique       : {len(np.unique(data['prev_col']))}")
    print(f"i0 unique             : {len(np.unique(data['i0']))}")
    print(f"px_store unique       : {len(np.unique(data['px_store']))}")
    print(f"px_anchor unique      : {len(np.unique(data['px_anchor']))}")
    print(f"a_raw unique          : {len(np.unique(data['a_raw']))}")
    print(f"a_bucket unique       : {len(np.unique(data['a_bucket']))}")
    print()


def summarize_supports(data: np.ndarray, p: int) -> None:
    print("=== Rényi-2 / support diagnostics ===")

    projections = {
        "prev_col": data["prev_col"],
        "i0": data["i0"],
        "px_store": data["px_store"],
        "py_store": data["py_store"],
        "(prev_col,i0)": None,
        "(px_store,py_store)": None,
        "(prev_col,px_store)": None,
        "(a_bucket,px_store)": None,
    }

    proj_pairs = {
        "(prev_col,i0)": (data["prev_col"], data["i0"]),
        "(px_store,py_store)": (data["px_store"], data["py_store"]),
        "(prev_col,px_store)": (data["prev_col"], data["px_store"]),
        "(a_bucket,px_store)": (data["a_bucket"], data["px_store"]),
    }

    for name, arr in projections.items():
        if arr is None:
            continue
        cnt = counter_from_array(arr)
        N, K, S2, H2 = renyi2_support_from_counts(cnt)
        alpha2 = alpha2_from_S2(S2, p)
        print(f"{name:18s} N={N:9d}  K={K:8d}  S2={S2:12.4g}  alpha2={alpha2:.4f}")

    for name, (x, y) in proj_pairs.items():
        cnt = counter_from_pairs(x, y)
        N, K, S2, H2 = renyi2_support_from_counts(cnt)
        alpha2 = alpha2_from_S2(S2, p)
        print(f"{name:18s} N={N:9d}  K={K:8d}  S2={S2:12.4g}  alpha2={alpha2:.4f}")

    print()


def summarize_entropies(data: np.ndarray) -> None:
    print("=== Shannon entropy / mutual information ===")
    pairs = [
        ("a_raw", "px_store"),
        ("a_raw", "py_store"),
        ("a_raw", "prev_col"),
        ("a_bucket", "px_store"),
        ("a_bucket", "prev_col"),
        ("px_store", "py_store"),
        ("px_store", "prev_col"),
        ("i0", "prev_col"),
    ]
    for xname, yname in pairs:
        x = data[xname]
        y = data[yname]
        Hx = shannon_entropy_from_counts(counter_from_array(x))
        Hy = shannon_entropy_from_counts(counter_from_array(y))
        Hxy = shannon_entropy_from_counts(counter_from_pairs(x, y))
        I = Hx + Hy - Hxy
        Hxg = conditional_shannon_entropy(x, y)
        Hyg = conditional_shannon_entropy(y, x)
        print(
            f"{xname:10s} vs {yname:10s} | "
            f"I={I:.4f} nats | H({xname}|{yname})={Hxg:.4f} | H({yname}|{xname})={Hyg:.4f}"
        )
    print()


def summarize_lag_acf(data: np.ndarray) -> None:
    print("=== Lag autocorrelations ===")
    series_list = [
        ("a_raw", data["a_raw"]),
        ("a_bucket", data["a_bucket"]),
        ("prev_col", data["prev_col"]),
        ("px_store", data["px_store"]),
        ("step_gap", data["step_gap"]),
    ]
    lags = [1, 2, 3, 5, 10, 20, 50, 100, 200]
    for name, x in series_list:
        print(f"-- {name} --")
        for lag in lags:
            if lag < len(x):
                r = autocorr_int64(x, lag)
                print(f"  lag={lag:3d}  r={r:+.6f}")
        print()
    print()


def summarize_transition_graph(data: np.ndarray, per_tid: bool = True) -> None:
    """
    Build transitions prev_col[t] -> prev_col[t+1] within each thread ordered by raw_steps.
    """
    print("=== Transition graph on prev_col ===")
    edges: Dict[int, Dict[int, int]] = defaultdict(lambda: defaultdict(int))

    if per_tid:
        tids = np.unique(data["tid"])
        chain_lengths = []
        for tid in tids:
            sub = data[data["tid"] == tid]
            order = np.argsort(sub["raw_steps"], kind="mergesort")
            cols = sub["prev_col"][order].astype(np.int64)
            chain_lengths.append(len(cols))
            for a, b in zip(cols[:-1], cols[1:]):
                edges[int(a)][int(b)] += 1
        print(f"threads               : {len(tids)}")
        print(f"chain length min/med/max: {min(chain_lengths)} / {statistics.median(chain_lengths):.1f} / {max(chain_lengths)}")
    else:
        order = np.argsort(data["raw_steps"], kind="mergesort")
        cols = data["prev_col"][order].astype(np.int64)
        for a, b in zip(cols[:-1], cols[1:]):
            edges[int(a)][int(b)] += 1

    nodes = sorted(set(edges.keys()) | {w for adj in edges.values() for w in adj.keys()})
    print(f"nodes                 : {len(nodes)}")
    print(f"directed edges (uniq)  : {sum(len(adj) for adj in edges.values())}")
    print(f"weighted edges         : {sum(sum(adj.values()) for adj in edges.values())}")

    # SCCs
    sccs = tarjan_scc(nodes, edges)
    scc_sizes = sorted((len(c) for c in sccs), reverse=True)
    print(f"SCC count             : {len(sccs)}")
    print("top SCC sizes         :", ", ".join(map(str, scc_sizes[:10])) if scc_sizes else "(none)")

    # PageRank
    pr = pagerank_sparse(nodes, edges, iters=100)
    if pr:
        vals = np.array(list(pr.values()), dtype=np.float64)
        vals /= vals.sum()
        H = -np.sum(vals * np.log(vals + 1e-300))
        H2 = -math.log(np.sum(vals * vals))
        print(f"PageRank Shannon H    : {H:.4f} nats")
        print(f"PageRank Rényi-2 H2   : {H2:.4f} nats")
        top = sorted(pr.items(), key=lambda kv: kv[1], reverse=True)[:10]
        print("top PageRank nodes    :", ", ".join(f"{k}:{v:.3e}" for k, v in top))
    print()


def summarize_closure_lag_structure(data: np.ndarray) -> None:
    """
    Reproduce a D37-style closure-indexed readout:
    compare how close successive closures are in px_store / px_anchor.
    """
    print("=== Closure-indexed spatial ACF ===")
    order = np.argsort(data["raw_steps"], kind="mergesort")
    sub = data[order]

    # use closure index as the sequence variable
    px_close = sub["px_anchor"].astype(np.float64)
    px_store = sub["px_store"].astype(np.float64)

    lags = [1, 2, 3, 5, 10, 20, 50, 100, 200]
    for name, x in [("px_close", px_close), ("px_store", px_store)]:
        print(f"-- {name} --")
        # z-score-style correlation against lagged series
        x0 = x - x.mean()
        s = x0.std()
        for lag in lags:
            if lag >= len(x):
                continue
            a = x0[:-lag]
            b = x0[lag:]
            denom = a.std() * b.std()
            r = float(np.mean(a * b) / denom) if denom > 0 else float("nan")
            print(f"  lag={lag:3d}  r={r:+.6f}")
        print()

    # Bucketed proximity in px_store across closures
    if len(sub) >= 2:
        diffs = np.abs(np.diff(sub["px_store"].astype(np.int64)))
        print(f"px_store |Δ| mean/median/max : {float(diffs.mean()):.2f} / {float(np.median(diffs)):.2f} / {int(diffs.max())}")
        print(f"px_store |Δ| <= 10           : {int(np.sum(diffs <= 10))} / {len(diffs)}")
        print(f"px_store |Δ| <= 100          : {int(np.sum(diffs <= 100))} / {len(diffs)}")
    print()


def summarize_thread_bursts(data: np.ndarray) -> None:
    print("=== Per-thread burst / gap summaries ===")
    tids = np.unique(data["tid"])
    rows = []
    for tid in tids:
        sub = data[data["tid"] == tid]
        order = np.argsort(sub["raw_steps"], kind="mergesort")
        x = sub["step_gap"][order].astype(np.int64)
        if len(x) < 2:
            continue
        rows.append((int(tid), len(x), float(x.mean()), float(x.std(ddof=0)), int(x.min()), int(np.median(x)), int(x.max())))
    rows.sort(key=lambda r: r[1], reverse=True)

    print("tid   n      mean_gap   std_gap    min   med   max")
    for tid, n, mean_g, std_g, mn, med, mx in rows[:20]:
        print(f"{tid:3d}  {n:6d}  {mean_g:9.2f}  {std_g:8.2f}  {mn:5d} {med:5d} {mx:5d}")
    print()


def summarize_a_bucket_vs_px(data: np.ndarray, n_bins: int = 64) -> None:
    print("=== a_bucket vs px_store 2D concentration ===")
    a = data["a_bucket"].astype(np.int64)
    px = data["px_store"].astype(np.int64)

    a_bins = int(a.max()) + 1 if a.size else 1
    px_bins = n_bins
    px_b = bucketize(px, px_bins)

    grid = np.zeros((a_bins, px_bins), dtype=np.int64)
    for ai, pi in zip(a, px_b):
        grid[int(ai), int(pi)] += 1

    obs = grid.ravel().astype(np.float64)
    N = obs.sum()
    expected = N / len(obs) if len(obs) > 0 else 0.0
    if expected > 0:
        chi2 = np.sum((obs - expected) ** 2 / expected)
        dof = len(obs) - 1
        print(f"grid shape            : {grid.shape}")
        print(f"chi2/dof              : {chi2/dof:.4f}")
    else:
        print("empty grid")
    print()


def summarize_histograms(data: np.ndarray) -> None:
    print("=== Marginal histograms ===")
    for name in ["a_bucket", "prev_col", "px_store", "py_store", "i0"]:
        x = data[name].astype(np.int64)
        cnt = counter_from_array(x)
        N, K, S2, H2 = renyi2_support_from_counts(cnt)
        print(
            f"{name:10s} unique={K:8d}  "
            f"mean_mult={N / K:.3f}  "
            f"S2={S2:.4g}"
        )
    print()


def summarize_top_repeats(data: np.ndarray) -> None:
    """
    Show whether any key-like objects actually repeat.
    """
    print("=== Repeat structure ===")
    for name in ["prev_col", "i0", "px_store", "py_store", "a_raw", "a_bucket"]:
        cnt = counter_from_array(data[name])
        top = cnt.most_common(5)
        max_mult = top[0][1] if top else 0
        n_gt1 = sum(1 for v in cnt.values() if v >= 2)
        print(f"{name:10s} distinct={len(cnt):8d}  keys>=2={n_gt1:8d}  max_mult={max_mult:5d}  top={top}")
    print()


# -----------------------------
# Main
# -----------------------------

def main() -> None:
    ap = argparse.ArgumentParser(description="Analyze CONJCLOS store events")
    ap.add_argument("--bin", dest="bin_path", required=True, type=Path, help="Path to .bin file")
    ap.add_argument("--schema", dest="schema_path", required=True, type=Path, help="Path to schema JSON")
    ap.add_argument("--limit", type=int, default=None, help="Max records to read")
    ap.add_argument("--tid", type=int, default=None, help="Analyze only one thread id")
    ap.add_argument("--p", type=int, default=2371147, help="Prime p for alpha2 scaling (default: 2371147)")
    args = ap.parse_args()

    data = load_conjclos(args.bin_path, args.schema_path, limit=args.limit)

    if args.tid is not None:
        data = data[data["tid"] == args.tid]
        print(f"[filter] tid={args.tid}, remaining records={len(data)}")
        if len(data) == 0:
            print("No records after tid filter.")
            return

    summarize_basic(data)
    summarize_histograms(data)
    summarize_top_repeats(data)
    summarize_supports(data, args.p)
    summarize_entropies(data)
    summarize_lag_acf(data)
    summarize_transition_graph(data, per_tid=True)
    summarize_closure_lag_structure(data)
    summarize_a_bucket_vs_px(data, n_bins=64)
    summarize_thread_bursts(data)

    # A few especially useful one-line diagnostics
    print("=== Focused one-liners ===")
    cnt_prev = counter_from_array(data["prev_col"])
    N, K, S2, H2 = renyi2_support_from_counts(cnt_prev)
    print(f"alpha2(prev_col) = {alpha2_from_S2(S2, args.p):.4f}")

    cnt_pair = counter_from_pairs(data["prev_col"], data["i0"])
    N2, K2, S2_pair, H2_pair = renyi2_support_from_counts(cnt_pair)
    print(f"alpha2(prev_col,i0) = {alpha2_from_S2(S2_pair, args.p):.4f}")

    cnt_geom = counter_from_pairs(data["px_store"], data["py_store"])
    N3, K3, S2_geom, H2_geom = renyi2_support_from_counts(cnt_geom)
    print(f"alpha2(px_store,py_store) = {alpha2_from_S2(S2_geom, args.p):.4f}")

    print("Done.")


if __name__ == "__main__":
    main()
