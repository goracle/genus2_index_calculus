"""
Load sweep_results.json (pure-python, small p) and/or sage_sweep_results.json
(Sage-accelerated, larger p), fit floor ~ C * p^alpha, and push that through
to the Paley-Zygmund restart-count / total-group-op complexity exponent.

Usage:
    python3 fit_complexity.py sweep_results.json sage_sweep_results.json

Any number of result files can be given; all successful (non-error) points
across all of them are pooled into one fit. Prints the fitted alpha, the
implied asymptotic total-ops exponent (alpha - 0.8), a residual table, and
extrapolated total-ops at a few representative p (including cryptographic
sizes) for a sanity look at where things land.
"""
import json
import math
import sys


def load_points(paths):
    pts = []
    for path in paths:
        try:
            with open(path) as f:
                data = json.load(f)
        except FileNotFoundError:
            print(f"(skipping missing file {path})")
            continue
        for rec in data:
            if "error" in rec:
                continue
            pts.append((rec["p"], rec["B"], rec["floor"]))
    return pts


def fit_power_law(pts):
    xs = [math.log(p) for p, B, f in pts]
    ys = [math.log(f) for p, B, f in pts]
    n = len(xs)
    mx, my = sum(xs) / n, sum(ys) / n
    cov = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
    var = sum((x - mx) ** 2 for x in xs)
    alpha = cov / var
    intercept = my - alpha * mx
    C = math.exp(intercept)
    return alpha, C


def main():
    paths = sys.argv[1:] or ["sweep_results.json", "sage_sweep_results.json"]
    pts = load_points(paths)
    pts = sorted(set(pts))
    if len(pts) < 2:
        print(f"need >=2 successful points, got {len(pts)}: {pts}")
        return

    print(f"loaded {len(pts)} points from {paths}:")
    for p, B, floor in pts:
        print(f"  p={p:>12} B={B:>5} floor={floor}")
    print()

    alpha, C = fit_power_law(pts)
    print(f"fit: floor ~ {C:.4g} * p^{alpha:.4f}")
    print()
    print("residuals (floor / predicted):")
    for p, B, floor in pts:
        pred = C * p ** alpha
        print(f"  p={p:>12}  floor={floor:>16}  pred={pred:>16.0f}  ratio={floor/pred:.3f}")
    print()

    total_ops_exp = alpha - 0.8
    print(f"analytic asymptotic exponent of total group-ops in p: alpha - 0.8 = {total_ops_exp:.4f}")
    print(f"  i.e. total_ops ~ O(p^{total_ops_exp:.3f})")
    print(f"  vs. (H0)-optimistic claimed complexity: O(p^0.8)")
    print()

    print("numeric extrapolation (B ~ round(p^0.4), Paley-Zygmund w/ fitted floor):")
    print(f"{'p':>16} {'B':>6} {'floor_fit':>16} {'Pr(hit) PZ':>14} {'restarts':>14} {'total_ops (B*restarts)':>24}")
    for p in [151, 2503, 10**4, 10**5, 10**6, 2**32, 2**64, 2**128, 2**256]:
        B = max(4, round(p ** 0.4))
        N = p ** 2
        EX = B ** 4 / N
        floor = C * p ** alpha
        EX2 = floor / N
        pz = EX ** 2 / EX2
        restarts = 1 / pz
        total = B * restarts
        print(f"{p:>16} {B:>6} {floor:>16.3e} {pz:>14.3e} {restarts:>14.3e} {total:>24.3e}")


if __name__ == "__main__":
    main()
