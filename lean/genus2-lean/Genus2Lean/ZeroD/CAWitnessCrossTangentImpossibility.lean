import Mathlib
import Genus2Lean.HyperellipticFunctionField
import Genus2Lean.AffinePoints
import Genus2Lean.ZeroD.CAWitness
import Genus2Lean.ZeroD.CAWitnessCrossTangent

/-! # Cross-pair impossibility lemmas (all four variants):
same-sign is unreachable once the doubled anchor's row is fed the
construction's own row-convention identity

Per `ROADMAP-cawitness-tangent-interpolation.md`, Part B, case 3's
"worked out this pass" note. **Read `CAWitnessCrossTangent2.lean`'s /
`CAWitnessCrossTangentV{2,3,4}.lean`'s own docstrings carefully first
— this is the load-bearing fact that makes the argument below
correct, not a guess**: in every one of the four cross variants, the
doubled anchor point's row in `caCrossInterpMatrix`-family is
documented as wanting the anchor's own unflipped `Y` value, "also
equal to `-`(target point's `Y`) by the `ι`-identification" — i.e.
each construction is ONLY the right one to use once its own
identification already holds; none of them derives that fact from a
bare `x`-coordinate collision, since with a free, un-identified target
point there is no row for it in the matrix at all (only the OTHER
three free points are). The identification is always supplied by the
caller as a hypothesis (`hP1eq`/`hP2eq`, per variant), never derived
from the matrix.

**Which anchor/target pair each of the four variants identifies** (so
each variant's own `AlphaLocusDegreeUniformCross{1,2,3,4}.lean` knows
which two arguments — call them `Ra`/`P1` below — to instantiate the
lemmas at):
- **Cross1** (`CAWitnessCrossTangent2.lean`): `Ra1 = ι(sa.P1)` —
  instantiate with `Ra := Ra1`, `P1 := sa.P1`.
- **Cross2** (`CAWitnessCrossTangentV2.lean`): `Ra1 = ι(sa.P2)` —
  instantiate with `Ra := Ra1`, `P1 := sa.P2`.
- **Cross3** (`CAWitnessCrossTangentV3.lean`): `Ra2 = ι(sa.P1)` —
  instantiate with `Ra := Ra2`, `P1 := sa.P1`.
- **Cross4** (`CAWitnessCrossTangentV4.lean`): `Ra2 = ι(sa.P2)` —
  instantiate with `Ra := Ra2`, `P1 := sa.P2`.

The row-position/adjacency and determinant-sign differences documented
across the four variants' own files are all about the OTHER two rows
(the ordinary, non-doubled ones) and don't affect this file's
argument at all — the doubled row's own RHS convention (unflipped
anchor value, also equal to the negated target value) is identical in
shape across all four, which is why one generic `Ra`/`P1` pair of
theorems below covers all four variants without repetition, rather
than needing four near-duplicate copies.

**So the impossibility lemmas this file proves are NOT "derive `Ra =
ι(P1)` from `Ra.X = P1.X` using the interpolation matrix's rows"**
(the construction presupposes the identification, so using it that
way would be circular) — **it is the narrower, correctly-scoped claim
the roadmap actually stated**: given `Ra.X = P1.X` (so, by
`eq_or_eq_iota_of_X_eq`, either `Ra = P1` or `Ra = ι(P1)`), the
"same-sign" branch `Ra = P1` is inconsistent with the construction's
own documented row convention (`Ra.Y` also required to equal
`-P1.Y`) under `hchar`/`Ra.Y ≠ 0` — i.e. a caller who has BOTH
`Ra.X = P1.X` AND the construction's row identity in scope cannot
also have `Ra = P1`, which is exactly the fact
`eq_iota_of_X_eq_of_ne`'s `hne : Ra ≠ P1` premise needs to have been
established from, wherever the dispatcher this roadmap still owes
ends up needing it. This file supplies that missing premise
conditionally on the row identity; it does not (and, per the
docstring above, cannot) supply it unconditionally from the
`x`-coordinate collision alone. -/

noncomputable section

open Polynomial
open HyperellipticPolynomial

namespace Genus2Lean
namespace DecoupledSystem

variable {k : Type*} [Field k] {H : HyperellipticPolynomial k}

/-- **Same-sign is inconsistent with the construction's doubled-row
convention.** If `Ra = P1` as points (so in particular `Ra.Y = P1.Y`)
AND the construction's documented doubled-row identity `Ra.Y = -P1.Y`
both hold, then `2 * Ra.Y = 0`, contradicting `hchar`/`Ra.Y ≠ 0`.
Stated with the row identity as an explicit hypothesis (`hRowZero`)
rather than derived from any variant's interpolation matrix directly,
since — per the module docstring — each construction only supplies
this identity once its own `ι`-identification already holds, making a
direct derivation circular for the very case this lemma is meant to
rule out. -/
theorem false_of_eq_and_rowZero {Ra P1 : H.Point} (hchar : (2 : k) ≠ 0)
    (hRaYne : Ra.Y ≠ 0) (heq : Ra = P1) (hRowZero : Ra.Y = -P1.Y) :
    False := by
  rw [← heq] at hRowZero
  have h2 : (2 : k) * Ra.Y = 0 := by linear_combination hRowZero
  rcases mul_eq_zero.mp h2 with hc | hy
  · exact absurd hc hchar
  · exact hRaYne hy

/-- **The point-level corollary**: `Ra.X = P1.X` together with the
construction's doubled-row identity `Ra.Y = -P1.Y` (available once the
relevant `caCrossInterpMatrix`-family construction is in play for this
pair) and `hchar`/`Ra.Y ≠ 0` forces `Ra ≠ P1` — the exact premise
`eq_iota_of_X_eq_of_ne` needs to conclude `Ra = ι(P1)` outright from
`Ra.X = P1.X` alone. -/
theorem ne_of_rowZero {Ra P1 : H.Point} (hchar : (2 : k) ≠ 0)
    (hRaYne : Ra.Y ≠ 0) (hRowZero : Ra.Y = -P1.Y) : Ra ≠ P1 :=
  fun heq => false_of_eq_and_rowZero hchar hRaYne heq hRowZero

/-- **Cross-pair dichotomy resolution (all four variants)**: given
`Ra.X = P1.X`, the doubled row's own identity `Ra.Y = -P1.Y`, and
`hchar`/`Ra.Y ≠ 0`, conclude `Ra = Point.iota P1` outright — combining
`ne_of_rowZero` with `eq_iota_of_X_eq_of_ne`. This is the actual
corollary a dispatcher (or any of the four `AlphaLocusDegreeUniform
Cross{1,2,3,4}.lean` files) would call: it takes exactly the
hypotheses each variant's own interpolation-matrix row convention
already documents as holding for its doubled pair, and returns the
point-level identification (`hP1eq`/`hP2eq`, per variant) needs. See
the module docstring's table for which concrete `Ra`/`P1` each variant
instantiates this at. -/
theorem eq_iota_of_X_eq_of_rowZero {Ra P1 : H.Point} (hchar : (2 : k) ≠ 0)
    (hRaYne : Ra.Y ≠ 0) (hXeq : Ra.X = P1.X) (hRowZero : Ra.Y = -P1.Y) :
    Ra = Point.iota P1 :=
  Point.eq_iota_of_X_eq_of_ne hXeq (ne_of_rowZero hchar hRaYne hRowZero)

end DecoupledSystem
end Genus2Lean
