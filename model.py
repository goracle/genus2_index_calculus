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
