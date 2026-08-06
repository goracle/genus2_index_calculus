"""
Quick comparison: does regressing on T-histogram features (t_features.py)
beat the current raw-(x,y) DeepSetsRegressor (model.py) on the same
train/val/test split?

This is deliberately a separate, minimal script rather than a modification
of train.py, so you can run it standalone and diff the results against
your existing train.py runs on the same dataset/meta files.

Two models are trained and compared:
  1. "baseline" -- the existing DeepSetsRegressor over raw cyclic (x,y)
     encoding, i.e. exactly what train.py does (re-implemented inline
     here so this file has no import-order dependency on train.py).
  2. "t_feat"   -- a plain MLP over the 7-dim T-histogram feature vector
     (t_features.py:t_features_only), no per-point info at all.

Both use the same log1p-shift target, the same train/val/test split
(same seed), and the same floor (computed once from train). If the
diagnosis in the project conversation is right, t_feat should show
dramatically lower val/test MSE and a much higher e4-space correlation
than baseline, despite having ~40x fewer input dims and no positional
detail whatsoever.

Usage:
    python train_t_features.py --data dataset.jsonl --meta dataset_meta.json

Note: computing T-features requires one pair_sum_histogram call per
example (O(B^2) group ops each) -- for datasets in the thousands of
examples at B~10-25 this should take well under a minute on CPU, but
if you're running a much bigger dataset, consider caching t_features.py's
compute_t_features output to a sidecar file rather than recomputing it
on every run.
"""

from __future__ import annotations

import argparse
import json
import math
import statistics

import torch
import torch.nn as nn
from torch.utils.data import DataLoader, Dataset

from curve import Curve
from data import compute_floor, load_examples, split_dataset, target_to_e4, encode_points
from model import DeepSetsRegressor
from t_features import compute_t_features, N_T_FEATURES


# ============================================================
#  Datasets
# ============================================================

class RawPointDataset(Dataset):
    """Same as data.py's MomentDataset -- duplicated here so this file
    has no hidden dependency on train.py's exact class, just data.py's
    helpers (floor, split, target_to_e4)."""

    def __init__(self, examples, p, floor):
        self.examples = examples
        self.p = p
        self.floor = floor

    def __len__(self):
        return len(self.examples)

    def __getitem__(self, idx):
        ex = self.examples[idx]
        enc = encode_points(ex.points, self.p)
        shifted = max(0, ex.e4 - self.floor)
        target = math.log1p(shifted)
        return enc, torch.tensor(target, dtype=torch.float32), torch.tensor(float(ex.e4))


class TFeatureDataset(Dataset):
    """T-histogram features only, no raw coordinates. Features are
    precomputed once in __init__ (not per __getitem__) since they're
    deterministic given (points, curve) and recomputing per-epoch would
    waste the O(B^2) group-op cost repeatedly for no reason."""

    def __init__(self, examples, curve: Curve, floor):
        self.floor = floor
        self._feats = []
        self._targets = []
        self._e4s = []
        for ex in examples:
            feats = compute_t_features(ex.points, curve)
            shifted = max(0, ex.e4 - floor)
            target = math.log1p(shifted)
            self._feats.append(torch.tensor(feats, dtype=torch.float32))
            self._targets.append(torch.tensor(target, dtype=torch.float32))
            self._e4s.append(torch.tensor(float(ex.e4)))

    def __len__(self):
        return len(self._feats)

    def __getitem__(self, idx):
        return self._feats[idx], self._targets[idx], self._e4s[idx]


# ============================================================
#  Models
# ============================================================

class TFeatureRegressor(nn.Module):
    """Plain MLP over the fixed-size T-feature vector. No permutation-
    invariance machinery needed since there's no per-point structure
    left to be invariant over -- T already summarizes the set."""

    def __init__(self, in_dim: int = N_T_FEATURES, hidden: int = 32, dropout: float = 0.1):
        super().__init__()
        self.net = nn.Sequential(
            nn.Linear(in_dim, hidden),
            nn.ReLU(),
            nn.Dropout(dropout),
            nn.Linear(hidden, hidden),
            nn.ReLU(),
            nn.Linear(hidden, 1),
        )

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        return self.net(x).squeeze(-1)


# ============================================================
#  Shared train/eval loop
# ============================================================

def evaluate(model, loader, floor, device):
    model.eval()
    total_sq_err_log = 0.0
    total_abs_err_log = 0.0
    total_abs_err_e4 = 0.0
    n = 0
    preds_e4 = []
    actual_e4 = []
    with torch.no_grad():
        for inputs, target, e4_raw in loader:
            inputs, target = inputs.to(device), target.to(device)
            pred = model(inputs)

            diff = pred - target
            total_sq_err_log += (diff ** 2).sum().item()
            total_abs_err_log += diff.abs().sum().item()

            pred_e4 = target_to_e4(pred.cpu(), floor)
            total_abs_err_e4 += (pred_e4 - e4_raw).abs().sum().item()
            preds_e4.extend(pred_e4.tolist())
            actual_e4.extend(e4_raw.tolist())

            n += inputs.size(0)

    # Pearson correlation in e4-space -- a more interpretable "did it
    # learn anything at all" number than MSE alone, and comparable
    # across the two models even though their input dims differ.
    if n > 1 and statistics.pstdev(preds_e4) > 0 and statistics.pstdev(actual_e4) > 0:
        corr = statistics.correlation(preds_e4, actual_e4)
    else:
        corr = float("nan")

    return {
        "mse_log": total_sq_err_log / n,
        "mae_log": total_abs_err_log / n,
        "mae_e4": total_abs_err_e4 / n,
        "corr_e4": corr,
        "n": n,
    }


def train_model(model, train_loader, val_loader, floor, device, epochs, lr, weight_decay, patience, label):
    optimizer = torch.optim.Adam(model.parameters(), lr=lr, weight_decay=weight_decay)
    loss_fn = torch.nn.MSELoss()

    best_val_mse = float("inf")
    best_state = None
    epochs_since_improve = 0

    for epoch in range(1, epochs + 1):
        model.train()
        running_loss = 0.0
        n_seen = 0
        for inputs, target, _e4_raw in train_loader:
            inputs, target = inputs.to(device), target.to(device)
            optimizer.zero_grad()
            pred = model(inputs)
            loss = loss_fn(pred, target)
            loss.backward()
            optimizer.step()
            running_loss += loss.item() * inputs.size(0)
            n_seen += inputs.size(0)

        val_metrics = evaluate(model, val_loader, floor, device)
        train_loss = running_loss / n_seen

        improved = val_metrics["mse_log"] < best_val_mse
        if improved:
            best_val_mse = val_metrics["mse_log"]
            best_state = {k: v.clone() for k, v in model.state_dict().items()}
            epochs_since_improve = 0
        else:
            epochs_since_improve += 1

        if epoch % 10 == 0 or epoch == 1 or improved:
            print(
                f"[{label}] epoch {epoch:4d}  train_mse_log={train_loss:.4f}  "
                f"val_mse_log={val_metrics['mse_log']:.4f}  "
                f"val_corr_e4={val_metrics['corr_e4']:.4f}"
                f"{'  *' if improved else ''}"
            )

        if epochs_since_improve >= patience:
            print(f"[{label}] early stopping at epoch {epoch}")
            break

    if best_state is not None:
        model.load_state_dict(best_state)
    return model


# ============================================================
#  Main
# ============================================================

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--data", required=True)
    ap.add_argument("--meta", required=True)
    ap.add_argument("--epochs", type=int, default=200)
    ap.add_argument("--batch-size", type=int, default=64)
    ap.add_argument("--lr", type=float, default=1e-3)
    ap.add_argument("--weight-decay", type=float, default=1e-4)
    ap.add_argument("--patience", type=int, default=20)
    ap.add_argument("--seed", type=int, default=0)
    args = ap.parse_args()

    with open(args.meta) as f:
        meta = json.load(f)
    p = meta["p"]
    curve = Curve(p=p, f_poly=tuple(meta["f_poly"]))

    device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
    print(f"device: {device}")

    examples = load_examples(args.data)
    print(f"loaded {len(examples)} examples (p={p}, B={meta['B']}, pool_size={meta['pool_size']})")

    train_ex, val_ex, test_ex = split_dataset(examples, val_frac=0.15, test_frac=0.15, seed=args.seed)
    floor = compute_floor(train_ex)
    print(f"train/val/test sizes: {len(train_ex)}/{len(val_ex)}/{len(test_ex)}; floor={floor}")

    torch.manual_seed(args.seed)

    # ---- baseline: raw (x,y) DeepSetsRegressor ----
    print("\n=== baseline: DeepSetsRegressor on raw (x,y) ===")
    train_ds_raw = RawPointDataset(train_ex, p=p, floor=floor)
    val_ds_raw = RawPointDataset(val_ex, p=p, floor=floor)
    test_ds_raw = RawPointDataset(test_ex, p=p, floor=floor)

    train_loader_raw = DataLoader(train_ds_raw, batch_size=args.batch_size, shuffle=True)
    val_loader_raw = DataLoader(val_ds_raw, batch_size=256, shuffle=False)
    test_loader_raw = DataLoader(test_ds_raw, batch_size=256, shuffle=False)

    baseline_model = DeepSetsRegressor().to(device)
    baseline_model = train_model(
        baseline_model, train_loader_raw, val_loader_raw, floor, device,
        args.epochs, args.lr, args.weight_decay, args.patience, label="baseline",
    )
    baseline_test = evaluate(baseline_model, test_loader_raw, floor, device)

    # ---- t_feat: MLP on T-histogram features ----
    print("\n=== t_feat: MLP on T-histogram features ===")
    print("(computing T features for all examples -- O(B^2) group ops each)")
    train_ds_t = TFeatureDataset(train_ex, curve, floor)
    val_ds_t = TFeatureDataset(val_ex, curve, floor)
    test_ds_t = TFeatureDataset(test_ex, curve, floor)

    train_loader_t = DataLoader(train_ds_t, batch_size=args.batch_size, shuffle=True)
    val_loader_t = DataLoader(val_ds_t, batch_size=256, shuffle=False)
    test_loader_t = DataLoader(test_ds_t, batch_size=256, shuffle=False)

    t_model = TFeatureRegressor().to(device)
    t_model = train_model(
        t_model, train_loader_t, val_loader_t, floor, device,
        args.epochs, args.lr, args.weight_decay, args.patience, label="t_feat",
    )
    t_test = evaluate(t_model, test_loader_t, floor, device)

    # ---- comparison ----
    print("\n=== final test comparison ===")
    print(f"baseline (raw xy):  mse_log={baseline_test['mse_log']:.4f}  "
          f"mae_e4={baseline_test['mae_e4']:.1f}  corr_e4={baseline_test['corr_e4']:.4f}")
    print(f"t_feat (T-hist):    mse_log={t_test['mse_log']:.4f}  "
          f"mae_e4={t_test['mae_e4']:.1f}  corr_e4={t_test['corr_e4']:.4f}")
    print(
        "\nIf t_feat's corr_e4 is meaningfully higher than baseline's, that confirms "
        "the raw (x,y) cyclic encoding -- not sparse data -- was the bottleneck: "
        "T-histogram features carry the signal that the per-point encoding hides."
    )


if __name__ == "__main__":
    main()
