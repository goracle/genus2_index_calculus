"""
Train the DeepSetsRegressor on the log1p-shifted e4 target.

Usage:
    python train.py --data /path/to/dataset.jsonl --meta /path/to/dataset_meta.json

Reports two evaluation views on val/test:
  - log-space MSE/MAE: what the model is actually trained on
  - real e4-space MAE (after inverting the transform): the number that
    actually answers "how far off is the model's e4 estimate, in the
    same units as the raw label" -- log-space error alone can look
    small while translating to a large real-space error near the top
    of the range, so both are reported rather than just the loss the
    optimizer sees.

Also reports a same-metrics baseline (constant prediction = training
mean of the target) so the trained model's numbers have something
concrete to beat -- given how concentrated this label distribution is
(see data.py's docstring), a model needs to demonstrably beat "always
predict the mean" to prove it learned something, not just that a low
absolute loss number looks good in isolation.
"""

from __future__ import annotations

import argparse
import json

import torch
from torch.utils.data import DataLoader

from data import (
    MomentDataset,
    compute_floor,
    load_examples,
    split_dataset,
    target_to_e4,
)
from model import DeepSetsRegressor


def evaluate(model, loader, floor, device):
    model.eval()
    total_sq_err_log = 0.0
    total_abs_err_log = 0.0
    total_abs_err_e4 = 0.0
    n = 0
    with torch.no_grad():
        for points, target, e4_raw in loader:
            points, target = points.to(device), target.to(device)
            pred = model(points)

            diff = pred - target
            total_sq_err_log += (diff ** 2).sum().item()
            total_abs_err_log += diff.abs().sum().item()

            pred_e4 = target_to_e4(pred.cpu(), floor)
            total_abs_err_e4 += (pred_e4 - e4_raw).abs().sum().item()

            n += points.size(0)

    return {
        "mse_log": total_sq_err_log / n,
        "mae_log": total_abs_err_log / n,
        "mae_e4": total_abs_err_e4 / n,
        "n": n,
    }


def baseline_metrics(train_examples, eval_examples, floor):
    """Constant-prediction baseline: always predict the training set's
    mean log-target. Establishes the bar a trained model must clear."""
    import math
    import statistics

    train_targets = [
        math.log1p(max(0, ex.e4 - floor)) for ex in train_examples
    ]
    mean_target = statistics.mean(train_targets)
    mean_e4_pred = floor + (math.expm1(mean_target))

    sq_err_log = 0.0
    abs_err_log = 0.0
    abs_err_e4 = 0.0
    for ex in eval_examples:
        t = math.log1p(max(0, ex.e4 - floor))
        diff = mean_target - t
        sq_err_log += diff ** 2
        abs_err_log += abs(diff)
        abs_err_e4 += abs(mean_e4_pred - ex.e4)

    n = len(eval_examples)
    return {
        "mse_log": sq_err_log / n,
        "mae_log": abs_err_log / n,
        "mae_e4": abs_err_e4 / n,
        "n": n,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--data", required=True, help="path to dataset.jsonl")
    ap.add_argument("--meta", required=True, help="path to dataset_meta.json")
    ap.add_argument("--epochs", type=int, default=200)
    ap.add_argument("--batch-size", type=int, default=64)
    ap.add_argument("--lr", type=float, default=1e-3)
    ap.add_argument("--weight-decay", type=float, default=1e-4)
    ap.add_argument("--patience", type=int, default=20,
                     help="early-stopping patience, in epochs with no val improvement")
    ap.add_argument("--out", default="/home/claude/genus2ml/checkpoint.pt")
    ap.add_argument("--seed", type=int, default=0)
    args = ap.parse_args()

    with open(args.meta) as f:
        meta = json.load(f)
    p = meta["p"]

    device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
    print(f"device: {device}")

    examples = load_examples(args.data)
    print(f"loaded {len(examples)} examples (p={p}, B={meta['B']}, pool_size={meta['pool_size']})")

    train_ex, val_ex, test_ex = split_dataset(examples, val_frac=0.15, test_frac=0.15, seed=args.seed)
    floor = compute_floor(train_ex)  # computed ONCE, from train only -- see data.py docstring
    print(f"train/val/test sizes: {len(train_ex)}/{len(val_ex)}/{len(test_ex)}; floor={floor}")

    train_ds = MomentDataset(train_ex, p=p, floor=floor)
    val_ds = MomentDataset(val_ex, p=p, floor=floor)
    test_ds = MomentDataset(test_ex, p=p, floor=floor)

    train_loader = DataLoader(train_ds, batch_size=args.batch_size, shuffle=True)
    val_loader = DataLoader(val_ds, batch_size=256, shuffle=False)
    test_loader = DataLoader(test_ds, batch_size=256, shuffle=False)

    torch.manual_seed(args.seed)
    model = DeepSetsRegressor().to(device)
    optimizer = torch.optim.Adam(model.parameters(), lr=args.lr, weight_decay=args.weight_decay)
    loss_fn = torch.nn.MSELoss()

    best_val_mse = float("inf")
    best_state = None
    epochs_since_improve = 0

    for epoch in range(1, args.epochs + 1):
        model.train()
        running_loss = 0.0
        n_seen = 0
        for points, target, _e4_raw in train_loader:
            points, target = points.to(device), target.to(device)
            optimizer.zero_grad()
            pred = model(points)
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
                f"val_mae_e4={val_metrics['mae_e4']:.1f}"
                f"{'  *' if improved else ''}"
            )

        if epochs_since_improve >= args.patience:
            print(f"early stopping at epoch {epoch} (no val improvement for {args.patience} epochs)")
            break

    if best_state is not None:
        model.load_state_dict(best_state)

    test_metrics = evaluate(model, test_loader, floor, device)
    base_metrics = baseline_metrics(train_ex, test_ex, floor)

    print("\n=== final test results ===")
    print(f"model:    mse_log={test_metrics['mse_log']:.4f}  mae_log={test_metrics['mae_log']:.4f}  mae_e4={test_metrics['mae_e4']:.1f}")
    print(f"baseline: mse_log={base_metrics['mse_log']:.4f}  mae_log={base_metrics['mae_log']:.4f}  mae_e4={base_metrics['mae_e4']:.1f}")
    print("(baseline = always predict the training mean; model should beat this on all three)")

    torch.save({
        "model_state": model.state_dict(),
        "floor": floor,
        "p": p,
        "B": meta["B"],
    }, args.out)
    print(f"\nsaved checkpoint to {args.out}")


if __name__ == "__main__":
    main()
