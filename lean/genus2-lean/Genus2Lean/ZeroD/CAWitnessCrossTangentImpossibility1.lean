import Mathlib
import Genus2Lean.HyperellipticFunctionField
import Genus2Lean.AffinePoints
import Genus2Lean.ZeroD.CAWitness
import Genus2Lean.ZeroD.CAWitnessCrossTangent

/-! # Cross1 (`Ra = ι(sa.P1)`) impossibility lemma: same-sign is
unreachable once `Ra = sa.P1` is fed to `caCrossInterpMatrix`'s own
row-0 convention

Per `ROADMAP-cawitness-tangent-interpolation.md`, Part B, case 3's
"worked out this pass" note. **Read `CAWitnessCrossTangent2.lean`'s own
docstring carefully first — this is the load-bearing fact that makes
the argument below correct, not a guess**: `caCrossInterpMatrix
RaX Ra2X P2X`'s row 0 is documented as wanting `RaY`, "unflipped anchor
value — also equals `-sa.P1.Y` by the `ι`-identification" (i.e. the
construction is ONLY the right one to use once `Ra = ι(sa.P1)` already
holds; it does not itself derive that fact from a bare `x`-coordinate
collision, since with a free, un-identified `sa.P1` there is no row for
`sa.P1` in the matrix at all — only `Ra2X`/`P2X` are its other two free
points, and `sa.P1` plays no role in `caCrossInterpMatrix`/`bCACross`
except via the caller-supplied identity `hP1eq : sa.P1 = Point.iota
Ra`).

**So the impossibility lemma this file proves is NOT "derive `Ra =
ι(sa.P1)` from `Ra.X = sa.P1.X` using `bCACross`'s rows"** (that
construction presupposes the identification, so using it that way
would be circular) — **it is the narrower, correctly-scoped claim the
roadmap actually stated**: given `Ra.X = sa.P1.X` (so, by
`eq_or_eq_iota_of_X_eq`, either `Ra = sa.P1` or `Ra = ι(sa.P1)`), the
"same-sign" branch `Ra = sa.P1` is inconsistent with the construction's
own documented row-0 convention (`RaY` also required to equal
`-sa.P1.Y`) under `hchar`/`Ra.Y ≠ 0` — i.e. a caller who has BOTH
`Ra.X = sa.P1.X` AND the construction's row-0 identity in scope cannot
also have `Ra = sa.P1`, which is exactly the fact
`eq_iota_of_X_eq_of_ne`'s `hne : Ra ≠ P1` premise needs to have been
established from, wherever the dispatcher this roadmap still owes
ends up needing it. This file supplies that missing premise
conditionally on the row-0 identity; it does not (and, per the
docstring above, cannot) supply it unconditionally from the
`x`-coordinate collision alone. -/

noncomputable section

open Polynomial
open HyperellipticPolynomial

namespace Genus2Lean
namespace DecoupledSystem

variable {k : Type*} [Field k] {H : HyperellipticPolynomial k}

/-- **Same-sign is inconsistent with the construction's row-0
convention.** If `Ra = P1` as points (so in particular `Ra.Y = P1.Y`)
AND the construction's documented row-0 identity `Ra.Y = -P1.Y` both
hold, then `2 * Ra.Y = 0`, contradicting `hchar`/`Ra.Y ≠ 0`. Stated
with the row-0 identity as an explicit hypothesis (`hRowZero`) rather
than derived from `caCrossInterpMatrix` directly, since — per the
module docstring — that construction only supplies this identity once
the `ι`-identification already holds, making a direct derivation
circular for the very case this lemma is meant to rule out. -/
theorem false_of_eq_and_rowZero {Ra P1 : H.Point} (hchar : (2 : k) ≠ 0)
    (hRaYne : Ra.Y ≠ 0) (heq : Ra = P1) (hRowZero : Ra.Y = -P1.Y) :
    False := by
  rw [← heq] at hRowZero
  have h2 : (2 : k) * Ra.Y = 0 := by linear_combination hRowZero
  rcases mul_eq_zero.mp h2 with hc | hy
  · exact absurd hc hchar
  · exact hRaYne hy

/-- **The point-level corollary**: `Ra.X = P1.X` together with the
construction's row-0 identity `Ra.Y = -P1.Y` (available once
`caCrossInterpMatrix`/`bCACross` is in play for this pair) and
`hchar`/`Ra.Y ≠ 0` forces `Ra ≠ P1` — the exact premise
`eq_iota_of_X_eq_of_ne` needs to conclude `Ra = ι(P1)` outright from
`Ra.X = P1.X` alone. -/
theorem ne_of_rowZero {Ra P1 : H.Point} (hchar : (2 : k) ≠ 0)
    (hRaYne : Ra.Y ≠ 0) (hRowZero : Ra.Y = -P1.Y) : Ra ≠ P1 :=
  fun heq => false_of_eq_and_rowZero hchar hRaYne heq hRowZero

/-- **Cross1's actual dichotomy resolution**: given `Ra.X = P1.X`, the
row-0 identity `Ra.Y = -P1.Y`, and `hchar`/`Ra.Y ≠ 0`, conclude
`Ra = Point.iota P1` outright — combining `ne_of_rowZero` with
`eq_iota_of_X_eq_of_ne`. This is the actual corollary a dispatcher
would call: it takes exactly the hypotheses `caCrossInterpMatrix`'s
row-0 convention already documents as holding for this pair, and
returns the point-level identification `hP1eq` needs. -/
theorem eq_iota_of_X_eq_of_rowZero {Ra P1 : H.Point} (hchar : (2 : k) ≠ 0)
    (hRaYne : Ra.Y ≠ 0) (hXeq : Ra.X = P1.X) (hRowZero : Ra.Y = -P1.Y) :
    Ra = Point.iota P1 :=
  Point.eq_iota_of_X_eq_of_ne hXeq (ne_of_rowZero hchar hRaYne hRowZero)

end DecoupledSystem
end Genus2Lean
