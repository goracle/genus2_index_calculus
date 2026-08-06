"""
Permutation-invariant regressor for the 8th-moment task.

F is a SET of B points -- the labeling e4(F) does not depend on the
order the points happen to be listed in (moment.py's construction sums
over all P1..P8 in F, order-independent). A plain MLP over the
flattened/concatenated (B, 4) input would have to separately learn
this invariance from data (i.e. learn that all B! orderings of the
same set should produce the same output), wasting model capacity and
data on a symmetry we already know holds exactly. Building it into the
architecture (Deep Sets: Zaheer et al. 2017) removes that burden.

Architecture: each point (already encoded as a 4-dim cyclic feature,
see data.py:encode_points) goes through a shared per-point MLP (phi),
producing a per-point embedding. Embeddings are pooled (mean) across
the B points -- pooling is what makes the whole thing order-invariant,
since mean/sum are symmetric functions of their inputs. The pooled
vector goes through a second MLP (rho) to produce the scalar target
prediction.
"""

from __future__ import annotations

import torch
import torch.nn as nn


class DeepSetsRegressor(nn.Module):
    def __init__(
        self,
        in_dim: int = 4,
        phi_hidden: int = 64,
        embed_dim: int = 64,
        rho_hidden: int = 64,
        dropout: float = 0.1,
    ):
        super().__init__()
        self.phi = nn.Sequential(
            nn.Linear(in_dim, phi_hidden),
            nn.ReLU(),
            nn.Linear(phi_hidden, embed_dim),
            nn.ReLU(),
        )
        self.rho = nn.Sequential(
            nn.Linear(embed_dim, rho_hidden),
            nn.ReLU(),
            nn.Dropout(dropout),
            nn.Linear(rho_hidden, rho_hidden // 2),
            nn.ReLU(),
            nn.Linear(rho_hidden // 2, 1),
        )

    def forward(self, points: torch.Tensor) -> torch.Tensor:
        """points: (batch, B, in_dim) -> (batch,) scalar predictions
        (in log1p-shifted-e4 space, matching data.py's target)."""
        per_point = self.phi(points)          # (batch, B, embed_dim)
        pooled = per_point.mean(dim=1)         # (batch, embed_dim) -- order-invariant
        out = self.rho(pooled)                 # (batch, 1)
        return out.squeeze(-1)


class DeepSetsWithTFeatures(nn.Module):
    """DeepSetsRegressor extended with T-histogram features
    (t_features.py), concatenated ONCE after pooling rather than
    broadcast onto every point row.

    Why concat-after-pooling instead of concat-per-point (the approach
    train_t_features.py's encode_points_with_t_features used for the
    quick comparison): broadcasting the same T-feature block onto all
    B point rows forces phi -- which is applied identically and
    independently to every row -- to either learn to ignore that block
    (redundant, wastes capacity) or leak it into every per-point
    embedding before pooling averages it back down anyway. Concatenating
    after the pool is both cheaper (T-features pass through their own
    small head once per example, not B times) and architecturally
    honest: T-features are a property of the SET, not of any individual
    point, so they belong at the point where the set-level
    representation already exists (the pooled vector), not smeared
    across point-level ones.

    phi/pooling over raw points is kept (not dropped) because per-point
    (x,y) position might still carry some marginal signal beyond what
    the 7 summary T-features capture (e.g. finer-grained structure in
    T's support, not just its moments) -- this lets training decide how
    much to weight each source rather than assuming raw points are
    useless. If ablations show the raw-point branch contributes nothing
    once T-features are present, it can be removed to simplify the
    model (see t_features.py's t_features_only for that ablation).
    """

    def __init__(
        self,
        in_dim: int = 4,
        t_feat_dim: int = 7,
        phi_hidden: int = 64,
        embed_dim: int = 64,
        t_feat_embed_dim: int = 16,
        rho_hidden: int = 64,
        dropout: float = 0.1,
    ):
        super().__init__()
        self.phi = nn.Sequential(
            nn.Linear(in_dim, phi_hidden),
            nn.ReLU(),
            nn.Linear(phi_hidden, embed_dim),
            nn.ReLU(),
        )
        # Small head for the T-feature block, applied once per example
        # (not once per point) -- projects the 7 raw features (which
        # span very different scales, e.g. sum_T2 in the hundreds vs
        # n_collisions in the tens) into a learned embedding before
        # concatenation, rather than concatenating raw feature values
        # directly, so scale differences don't dominate the first rho
        # layer's weights.
        self.t_feat_head = nn.Sequential(
            nn.Linear(t_feat_dim, t_feat_embed_dim),
            nn.ReLU(),
        )
        self.rho = nn.Sequential(
            nn.Linear(embed_dim + t_feat_embed_dim, rho_hidden),
            nn.ReLU(),
            nn.Dropout(dropout),
            nn.Linear(rho_hidden, rho_hidden // 2),
            nn.ReLU(),
            nn.Linear(rho_hidden // 2, 1),
        )

    def forward(self, points: torch.Tensor, t_feats: torch.Tensor) -> torch.Tensor:
        """points: (batch, B, in_dim), t_feats: (batch, t_feat_dim)
        -> (batch,) scalar predictions (log1p-shifted-e4 space)."""
        per_point = self.phi(points)              # (batch, B, embed_dim)
        pooled = per_point.mean(dim=1)             # (batch, embed_dim)
        t_embed = self.t_feat_head(t_feats)        # (batch, t_feat_embed_dim)
        combined = torch.cat([pooled, t_embed], dim=-1)  # (batch, embed_dim + t_feat_embed_dim)
        out = self.rho(combined)                   # (batch, 1)
        return out.squeeze(-1)
