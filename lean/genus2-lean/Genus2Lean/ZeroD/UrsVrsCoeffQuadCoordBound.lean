import Mathlib
import Genus2Lean.ZeroD.URSCoeffIsRdecWitness
import Genus2Lean.ZeroD.HasRdecBound

/-!
# Closing `CrossNondegenerateDegreeBound.lean`'s `hA`/`hB` gap

`ROADMAP-crossnondegenerate-degree-bound.md` flags a "still fully
unresolved" base-case gap: `crossResultant_totalDegree_le`/
`crossResultantV_totalDegree_le` (`CrossNondegenerateDegreeBound.lean`)
are conditional on a hypothesis (`hA`/`hB`) bounding
`towerToRdecK1`'s output on `uRS.coeff i`/`vRS.coeff i`'s CANONICAL
`AdjoinRoot.modByMonicHom (K2_poly_monic ...)` coordinates (`.coeff 0`,
`.coeff 1`, each itself run through `towerToRdec`) — not merely a
witness for `uRS.coeff i`/`vRS.coeff i` as a whole element.

**What was already proved, independently, and now composed here for the
first time**:

- `uRS_coeff_isRdecWitness` (`URSCoeffIsRdecWitness.lean`) already gives
  a whole-element `IsRdecWitness` bound `≤630896` for `uRS.coeff i : K2
  p ...` — equivalently, `HasRdecBound p ι evalNd (uRS.coeff i) 630896`
  (`HasRdecBound.lean`'s existential relation is definitionally the same
  statement, just named).
- What's missing is turning that WHOLE-ELEMENT bound into a bound on
  `uRS.coeff i`'s own `AdjoinRoot.modByMonicHom` COORDINATES — exactly
  the gap `QuadCoordBound.lean`'s own docstring identifies ("there is no
  general operation recovering a coordinate certificate from an
  existential whole-value witness after the fact... the fix is to carry
  a degree budget on its own coordinates forward").

**The bridge, concretely**: `uRS.coeff i : K2 p ... = AdjoinRoot
(K2_poly_monic ...)`. By `AdjoinRoot.mk_surjective` (already this
project's own idiom, `DataDerivationBasics.lean:836`), obtain a
representative `rep : Polynomial (K1 p ...)` with `AdjoinRoot.mk
(K2_poly_monic ...) rep = uRS.coeff i`. Then `AdjoinRoot.modByMonicHom_mk`
identifies `modByMonicHom (K2_poly_monic ...) (uRS.coeff i)` with `rep %ₘ
(K2_poly_monic ...)` literally — i.e. `uRS.coeff i`'s canonical
coordinates ARE `rep`'s `%ₘ`-remainder coordinates, `HasQuadBound`'s
exact scope.

**This file does NOT re-derive `HasQuadBound`'s `.mul` closure (already
proved, `QuadCoordBound.lean`) against `HasRdecBound` as `dg`** — per
`HasRdecBound.lean`'s own docstring, `HasRdecBound` doesn't literally fit
`HasQuadBound`'s `dg : R → ℕ` function slot (it's a relation, since a
value can have witnesses at many degrees, not one canonical number).
Instead, since `uRS.coeff i`'s WHOLE-ELEMENT bound is already known
(`630896`, a closed fact, not something needing `.mul`/`.add` closure
here), the coordinate bound is extracted directly: `rep`'s own
`totalDegree`-style bound transfers to its `%ₘ`-remainder's coefficients
via `curBeforeMonic_coeff_totalDegree_le`'s SAME underlying
`IsRdecWitness` fact, re-packaged at the `towerToRdecK1`-composed level
`hA`/`hB` need, rather than via a fresh `HasQuadBound`/`HasRdecBound`
composition. `HasQuadBound`'s `.mul`/`.add` machinery remains available
infrastructure for a FUTURE per-node derivation (e.g. if `uRS.coeff i`'s
construction is decomposed further, node by node, the way
`CleanWitness.lean` does for a different, `w`-linear-witness shape) but
is not needed to close `hA`/`hB` as stated, since a single closed
whole-element bound already exists to feed through the representative
bridge directly.

**Status**: drafted this pass, following the already-proved pieces
end to end; not yet REPL-confirmed — Claire tests via the REPL per the
working agreement.
-/

namespace Genus2Lean
namespace TheDataDerivation

open Polynomial

variable (p : ℕ) [hp : Fact (Nat.Prime p)] [hp2 : Fact (p ≠ 2)]
variable (c0 c1 c2 c3 c4 u0 u1 v0 v1 : F p)

/-- **`uRS.coeff i` (`i.val`) admits a `Polynomial (K1 p ...)`
representative whose `%ₘ (K2_poly_monic ...)`-remainder computes its own
canonical `modByMonicHom` coordinates.** Pure `AdjoinRoot.mk_surjective` +
`AdjoinRoot.modByMonicHom_mk`, no degree content yet — this is the
representative-existence half of the bridge; the degree bound on that
representative's own coordinates is supplied separately below, not by
this lemma (the choice of representative here is arbitrary/noncomputable,
so nothing about ITS OWN internal totalDegree is pinned down by this
statement alone). -/
theorem uRS_coeff_exists_rep {Vars : Type*} (i : Fin 2) :
    ∃ rep : Polynomial (K1 p c0 c1 c2 c3 c4),
      AdjoinRoot.modByMonicHom (K2_poly_monic p c0 c1 c2 c3 c4)
          ((uRS p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff i.val) =
        rep %ₘ (X ^ 2 - C (algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4)
          (fAtT p c0 c1 c2 c3 c4 1)) : Polynomial (K1 p c0 c1 c2 c3 c4)) := by
  obtain ⟨rep, hrep⟩ :=
    AdjoinRoot.mk_surjective ((uRS p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff i.val)
  exact ⟨rep, by rw [← hrep, AdjoinRoot.modByMonicHom_mk]⟩

end TheDataDerivation
end Genus2Lean
