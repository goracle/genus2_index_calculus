"""
Train DeepSetsWithTFeatures (model.py) -- the production candidate that
combines raw-point Deep Sets pooling with T-histogram features
(t_features.py), concatenated after pooling.

This is the natural next step after train_t_features.py's diagnostic
comparison confirmed T-features carry the signal raw (x,y) alone
doesn't. Where train_t_features.py trained two SEPARATE small models
to isolate the effect, this script trains the ONE combined model meant
to actually be used going forward (e.g. as the fitness surrogate for
selecting F, or wrapped in a greedy/search loop over candidate
multiples).

T-feature normalization
------------------------
t_features.py's 7 raw features span very different scales (sum_T2 in
the hundreds, B a small integer, log1p_sum_T2 already compressed).
Feeding them raw into a linear layer lets the largest-scale feature
dominate that layer's gradients regardless of actual relevance. This
script standardizes each T-feature to zero mean / unit variance using
statistics computed ONCE from the training split (mirroring how
data.py's floor is computed once from train only, for the same
reason: val/test must be transformed with train's statistics, not
their own, or you leak information about their distribution into
what's supposed to be an out-of-sample evaluation).

Usage:
    python train_model_with_t_features.py --data dataset.jsonl --meta dataset_meta.json
"""

from __future__ import annotations

import argparse
import json
import math

import torch
import torch.nn as nn
from torch.utils.data import DataLoader, Dataset

from curve import Curve
from data import compute_floor, load_examples, split_dataset, target_to_e4, encode_points
from model import DeepSetsWithTFeatures
from t_features import compute_t_features, N_T_FEATURES


# ============================================================
#  Dataset: raw points + T-features together
# ============================================================

class CombinedDataset(Dataset):
    """Returns (points_encoded, t_feats_normalized, target, raw_e4).
    T-features are precomputed once in __init__ (same reasoning as
    train_t_features.py's TFeatureDataset: they're deterministic given
    (points, curve), no reason to recompute per-epoch)."""

    def __init__(self, examples, p, curve: Curve, floor, t_feat_mean=None, t_feat_std=None):
        self.p = p
        self.floor = floor

        raw_t_feats = [compute_t_features(ex.points, curve) for ex in examples]
        t_tensor = torch.tensor(raw_t_feats, dtype=torch.float32)

        if t_feat_mean is None:
            # Only the caller building the TRAIN dataset should leave
            # these as None -- val/test datasets must be constructed
            # with the train split's mean/std explicitly passed in.
            self.t_feat_mean = t_tensor.mean(dim=0)
            self.t_feat_std = t_tensor.std(dim=0).clamp_min(1e-8)  # avoid div-by-zero on constant features
        else:
            self.t_feat_mean = t_feat_mean
            self.t_feat_std = t_feat_std

        self._t_feats_norm = (t_tensor - self.t_feat_mean) / self.t_feat_std
        self._points_enc = [encode_points(ex.points, p) for ex in examples]
        self._targets = [math.log1p(max(0, ex.e4 - floor)) for ex in examples]
        self._e4s = [float(ex.e4) for ex in examples]

    def __len__(self):
        return len(self._points_enc)

    def __getitem__(self, idx):
        return (
            self._points_enc[idx],
            self._t_feats_norm[idx],
            torch.tensor(self._targets[idx], dtype=torch.float32),
            torch.tensor(self._e4s[idx]),
        )


# ============================================================
#  Train / eval
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
        for points, t_feats, target, e4_raw in loader:
            points, t_feats, target = points.to(device), t_feats.to(device), target.to(device)
            pred = model(points, t_feats)

            diff = pred - target
            total_sq_err_log += (diff ** 2).sum().item()
            total_abs_err_log += diff.abs().sum().item()

            pred_e4 = target_to_e4(pred.cpu(), floor)
            total_abs_err_e4 += (pred_e4 - e4_raw).abs().sum().item()
            preds_e4.extend(pred_e4.tolist())
            actual_e4.extend(e4_raw.tolist())

            n += points.size(0)

    import statistics
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


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--data", required=True)
    ap.add_argument("--meta", required=True)
    ap.add_argument("--epochs", type=int, default=200)
    ap.add_argument("--batch-size", type=int, default=64)
    ap.add_argument("--lr", type=float, default=1e-3)
    ap.add_argument("--weight-decay", type=float, default=1e-4)
    ap.add_argument("--patience", type=int, default=20)
    ap.add_argument("--out", default="checkpoint_t_feat.pt")
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

    print("computing T-features for all splits (O(B^2) group ops per example)...")
    train_ds = CombinedDataset(train_ex, p, curve, floor)
    val_ds = CombinedDataset(val_ex, p, curve, floor,
                              t_feat_mean=train_ds.t_feat_mean, t_feat_std=train_ds.t_feat_std)
    test_ds = CombinedDataset(test_ex, p, curve, floor,
                               t_feat_mean=train_ds.t_feat_mean, t_feat_std=train_ds.t_feat_std)

    train_loader = DataLoader(train_ds, batch_size=args.batch_size, shuffle=True)
    val_loader = DataLoader(val_ds, batch_size=256, shuffle=False)
    test_loader = DataLoader(test_ds, batch_size=256, shuffle=False)

    torch.manual_seed(args.seed)
    model = DeepSetsWithTFeatures(t_feat_dim=N_T_FEATURES).to(device)
    optimizer = torch.optim.Adam(model.parameters(), lr=args.lr, weight_decay=args.weight_decay)
    loss_fn = torch.nn.MSELoss()

    best_val_mse = float("inf")
    best_state = None
    epochs_since_improve = 0

    for epoch in range(1, args.epochs + 1):
        model.train()
        running_loss = 0.0
        n_seen = 0
        for points, t_feats, target, _e4_raw in train_loader:
            points, t_feats, target = points.to(device), t_feats.to(device), target.to(device)
            optimizer.zero_grad()
            pred = model(points, t_feats)
            loss = loss_fn(pred, target)
            loss.backward()
            optimizer.step()
            running_loss += loss.item() * points.size(0)
            n_seen += points.size(0)

        val_metrics = evaluate(model, val_loader, floor, device)
        train_loss = running_loss / n_seen

        improved = val_metrics["mse_log"] < best_val_mse
        if improved:
            best_val_mse = val_metrics["mse_log"]
            best_state = {k: v.clone() for k, v in model.state_dict().items()}
            epochs_since_improve = 0
        else:
            epochs_since_improve += 1

        if epoch % 5 == 0 or epoch == 1 or improved:
            print(
                f"epoch {epoch:4d}  train_mse_log={train_loss:.4f}  "
                f"val_mse_log={val_metrics['mse_log']:.4f}  "
                f"val_corr_e4={val_metrics['corr_e4']:.4f}"
                f"{'  *' if improved else ''}"
            )

        if epochs_since_improve >= args.patience:
            print(f"early stopping at epoch {epoch} (no val improvement for {args.patience} epochs)")
            break

    if best_state is not None:
        model.load_state_dict(best_state)

    test_metrics = evaluate(model, test_loader, floor, device)
    print("\n=== final test results ===")
    print(f"mse_log={test_metrics['mse_log']:.4f}  mae_log={test_metrics['mae_log']:.4f}  "
          f"mae_e4={test_metrics['mae_e4']:.1f}  corr_e4={test_metrics['corr_e4']:.4f}")
    print("(compare corr_e4 here against train_t_features.py's baseline/t_feat numbers)")

    torch.save({
        "model_state": model.state_dict(),
        "floor": floor,
        "p": p,
        "B": meta["B"],
        "t_feat_mean": train_ds.t_feat_mean,
        "t_feat_std": train_ds.t_feat_std,
    }, args.out)
    print(f"\nsaved checkpoint to {args.out}")


if __name__ == "__main__":
    main()
