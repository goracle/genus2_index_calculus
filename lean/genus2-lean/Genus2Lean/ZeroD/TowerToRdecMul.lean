import Mathlib
import Genus2Lean.ZeroD.TheDataDerivation.DataDerivationMumford

/-!
# `IsRdecWitness`: a field-agnostic, cross-multiplied numerator/denominator
witness predicate, and its multiplicativity

New this pass. Per a ChatGPT consultation on the genuine gap
`ROADMAP-crossnondegenerate-degree-bound.md`/`MatrixEntryTotalDegree.lean`'s
own status note flagged: `matrixA`/`rhsVec`'s entries are `K2`-valued
PRODUCTS of `towerToRdec`-bounded pieces (`px ^ bi * (py or 1)`), but
`towerToRdec` is a denominator-clearing NORMAL-FORM map, not a ring
homomorphism — `towerToRdec (a * b)` is generally a completely different
(more reduced) pair than `((towerToRdec a).1 * (towerToRdec b).1,
(towerToRdec a).2 * (towerToRdec b).2)`, so no direct `totalDegree`
composition through `towerToRdec` itself is possible.

**The fix, per ChatGPT's answer**: stop treating `towerToRdec`'s output as
*the* representation and instead treat it as *a* witness for a semantic
"is a valid numerator/denominator pair" predicate, `IsRdecWitness`, phrased
via cross-multiplication (`evalTo n = evalTo d * v`, no division) against
an arbitrary field embedding — exactly the shape `towerToRdec_spec`
(`DataDerivationMumford.lean`, already proved, no `sorry`) already
provides at the `K2` level, just not yet named/packaged this way. Given
`IsRdecWitness`, multiplicativity (`(na*nb, da*db)` is a valid witness for
`a*b`, given valid witnesses `(na,da)`/`(nb,db)` for `a`/`b`) is "essentially
trivial algebra" (ChatGPT's own phrase) — a direct `map_mul`/`ring`
computation, no induction on the tower needed at this layer, since
`towerToRdec_spec` already did that induction.

**What this deliberately does NOT do**: prove `towerToRdec (a*b) =
(product pair)` — per ChatGPT's analysis this is false in general (both
`IsFractionRing.num/.den`'s reduced-fraction choice at the base case, and
`modByMonicHom`'s remainder-normalization at each tower level, can produce
a DIFFERENT, more-reduced representative for the product than the raw
product of witnesses). That's fine: the degree bound this file exists to
support only needs *some* valid witness's degree, not the literal
recursively-computed one, since `totalDegree`-bounding a witness pair only
needs the cross-multiplied equation to hold, not that it's the CANONICAL
witness.

**REPL-confirmed green** (Claire's build).
-/

namespace Genus2Lean
namespace TheDataDerivation

open Polynomial

variable (p : ℕ) [hp : Fact (Nat.Prime p)] [hp2 : Fact (p ≠ 2)]

/-- **The cross-multiplied numerator/denominator witness predicate.**
`IsRdecWitness ι v (n, d)` means `evalTo(n) = evalTo(d) * v` under the field
embedding `ι` — i.e. `(n, d)` is *a* valid numerator/denominator
representation of `v` (as `n/d` when `evalTo d ≠ 0`), stated without
division so the multiplicativity proof below is pure `ring`, no
`field_simp`/nonzero-denominator bookkeeping needed. Deliberately does NOT
require `evalTo d ≠ 0`: the degree bound this predicate feeds only needs
the equation, and dropping the nonzero requirement makes `.mul` hold
unconditionally rather than needing `da ≠ 0`/`db ≠ 0` as side hypotheses
(the reduced/canonical `towerToRdec`-computed witnesses ARE always
nonzero-denominator in practice, per `towerToRdec_spec`'s own use, but
that fact is not needed here and is not threaded through). -/
def IsRdecWitness {Vars K L : Type*} [CommRing K] [CommRing L]
    (ι : K →+* L) (evalNd : MvPolynomial Vars (F p) →+* L) (v : K)
    (nd : MvPolynomial Vars (F p) × MvPolynomial Vars (F p)) : Prop :=
  evalNd nd.1 = evalNd nd.2 * ι v

/-- **Multiplicativity, the actual target.** Given valid witnesses for `a`
and `b` under the SAME `ι`/`evalNd` pair, the pointwise product pair
`(na*nb, da*db)` is a valid witness for `a*b` — pure algebra:
`evalNd(na*nb) = evalNd(na)*evalNd(nb) = (evalNd(da)*ι a)*(evalNd(db)*ι b)
= (evalNd(da)*evalNd(db))*(ι a * ι b) = evalNd(da*db)*ι(a*b)`, via
`map_mul` on both `evalNd`/`ι` and `ring` to reassociate/commute. -/
theorem IsRdecWitness.mul {Vars K L : Type*} [CommRing K] [CommRing L]
    {ι : K →+* L} {evalNd : MvPolynomial Vars (F p) →+* L}
    {a b : K} {na da nb db : MvPolynomial Vars (F p)}
    (ha : IsRdecWitness p ι evalNd a (na, da))
    (hb : IsRdecWitness p ι evalNd b (nb, db)) :
    IsRdecWitness p ι evalNd (a * b) (na * nb, da * db) := by
  unfold IsRdecWitness at *
  simp only [map_mul] at *
  rw [ha, hb]
  ring

/-- **Division.** Given valid witnesses for `a` and `b` under the SAME
`ι`/`evalNd` pair, PLUS `evalNd db ≠ 0` and `ι b ≠ 0` (both needed so
`ι (a / b) = ι a / ι b` is the honest field quotient, not the junk
`0`-denominator convention), the cross-multiplied pair `(na*db, da*nb)`
is a valid witness for `a / b` — mirrors `IsRdecWitness.mul` but needs
`K`/`L` to be `Field`s (not just `CommRing`s): `ι (a / b) = ι a / ι b`
(`map_div₀`) needs `ι` to be a genuine field homomorphism, and the proof
itself divides inside `L`, which needs `L` a field too (the only
instantiation this project actually uses, `L := FractionRing
(MvPolynomial Vars (F p))`, already is one). Needed to convert a witness
for `Matrix.cramer M rhs i` (the un-normalized Cramer NUMERATOR, `=
M.det * (cramer solution)`) into a witness for the actual Cramer
SOLUTION `M.cramer rhs i / M.det` itself — see
`CoeffsOutTotalDegree.lean`'s own use. -/
theorem IsRdecWitness.div {Vars K L : Type*} [Field K] [Field L]
    {ι : K →+* L} {evalNd : MvPolynomial Vars (F p) →+* L}
    {a b : K} {na da nb db : MvPolynomial Vars (F p)}
    (ha : IsRdecWitness p ι evalNd a (na, da))
    (hb : IsRdecWitness p ι evalNd b (nb, db))
    (hdb : evalNd db ≠ 0) (hιb : ι b ≠ 0) :
    IsRdecWitness p ι evalNd (a / b) (na * db, da * nb) := by
  unfold IsRdecWitness at *
  -- Goal: `evalNd (na * db) = evalNd (da * nb) * ι (a / b)`. Substitute
  -- `ha`/`hb` directly (eliminating `evalNd na`/`evalNd nb` in favor of
  -- `ι a`/`ι b`) and `ι (a / b) = ι a * (ι b)⁻¹` (`map_div₀`), then the
  -- remaining identity `evalNd da * ι a * evalNd db = evalNd da *
  -- (evalNd db * ι b) * (ι a * (ι b)⁻¹)` is pure field algebra given
  -- `ι b ≠ 0` (`mul_inv_cancel₀`), closed by `field_simp`/`ring`.
  rw [map_mul, map_mul, map_div₀, ha, hb]
  field_simp

/-- **`towerToRdec_spec`, restated as `IsRdecWitness`.** `towerToRdec_spec`
(`DataDerivationMumford.lean`, already proved, no `sorry`) is EXACTLY
`IsRdecWitness` at `K := K2 p c0 c1 c2 c3 c4`, `L := FractionRing
(MvPolynomial Vars (F p))`, `evalNd := algebraMap (MvPolynomial Vars (F p))
(FractionRing (MvPolynomial Vars (F p)))`, `ι` as given — restated under
this name so downstream call sites can invoke `IsRdecWitness.mul` directly
against `towerToRdec`'s own output without re-deriving the connection each
time. -/
theorem towerToRdec_isRdecWitness {Vars : Type*} [DecidableEq Vars]
    (c0 c1 c2 c3 c4 : F p) (sg : SideGens Vars) (v : K2 p c0 c1 c2 c3 c4)
    (ι : K2 p c0 c1 c2 c3 c4 →+* FractionRing (MvPolynomial Vars (F p)))
    (hι_t : ∀ i : Fin 2, ι (algebraMap (K1 p c0 c1 c2 c3 c4) (K2 p c0 c1 c2 c3 c4)
        (algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4)
          (algebraMap (MvPolynomial (Fin 2) (F p)) (K0 p) (MvPolynomial.X i)))) =
      algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p)))
        (MvPolynomial.X (sg.tGen i)))
    (hι_w1 : ι (algebraMap (K1 p c0 c1 c2 c3 c4) (K2 p c0 c1 c2 c3 c4) (w1 p c0 c1 c2 c3 c4)) =
      algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p)))
        (MvPolynomial.X (sg.wGen 0)))
    (hι_w2 : ι (w2 p c0 c1 c2 c3 c4) =
      algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p)))
        (MvPolynomial.X (sg.wGen 1))) :
    IsRdecWitness p ι
      (algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p))))
      v (towerToRdec p sg v) :=
  towerToRdec_spec p (c0 := c0) (c1 := c1) (c2 := c2) (c3 := c3) (c4 := c4)
    sg v ι hι_t hι_w1 hι_w2

/-- **The corollary this file exists for**: given the ambient `ι`
satisfying `towerToRdec_spec`'s hypotheses, `towerToRdec a` and
`towerToRdec b`'s pointwise product pair is a valid witness for `a * b` —
NOT (in general) equal to `towerToRdec (a * b)` itself (per this file's
header — `towerToRdec` is a normal-form map, not multiplicative), but a
valid witness nonetheless, which is all a downstream `totalDegree` bound
needs. -/
theorem towerToRdec_mul_isRdecWitness {Vars : Type*} [DecidableEq Vars]
    (c0 c1 c2 c3 c4 : F p) (sg : SideGens Vars) (a b : K2 p c0 c1 c2 c3 c4)
    (ι : K2 p c0 c1 c2 c3 c4 →+* FractionRing (MvPolynomial Vars (F p)))
    (hι_t : ∀ i : Fin 2, ι (algebraMap (K1 p c0 c1 c2 c3 c4) (K2 p c0 c1 c2 c3 c4)
        (algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4)
          (algebraMap (MvPolynomial (Fin 2) (F p)) (K0 p) (MvPolynomial.X i)))) =
      algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p)))
        (MvPolynomial.X (sg.tGen i)))
    (hι_w1 : ι (algebraMap (K1 p c0 c1 c2 c3 c4) (K2 p c0 c1 c2 c3 c4) (w1 p c0 c1 c2 c3 c4)) =
      algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p)))
        (MvPolynomial.X (sg.wGen 0)))
    (hι_w2 : ι (w2 p c0 c1 c2 c3 c4) =
      algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p)))
        (MvPolynomial.X (sg.wGen 1))) :
    IsRdecWitness p ι
      (algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p))))
      (a * b)
      ((towerToRdec p sg a).1 * (towerToRdec p sg b).1,
        (towerToRdec p sg a).2 * (towerToRdec p sg b).2) :=
  IsRdecWitness.mul p
    (towerToRdec_isRdecWitness p c0 c1 c2 c3 c4 sg a ι hι_t hι_w1 hι_w2)
    (towerToRdec_isRdecWitness p c0 c1 c2 c3 c4 sg b ι hι_t hι_w1 hι_w2)

/-! ## Status, this pass

**Drafted, REPL-confirmed green.** Per a ChatGPT consultation (prompt/reply not separately filed as an `.md`, per
project convention of asking directly): `IsRdecWitness` is the field-
agnostic cross-multiplied predicate, `IsRdecWitness.mul` is the "essentially
trivial algebra" multiplicativity corollary (`map_mul` + `ring`, no
induction), and `towerToRdec_isRdecWitness`/`towerToRdec_mul_isRdecWitness`
connect it to `towerToRdec_spec` (`DataDerivationMumford.lean`, already
proved, no `sorry`) — no new tower induction needed, since `towerToRdec_spec`
already did that work; this file only repackages it.

**What this does NOT yet close**: `IsRdecWitness`'s witness pair still
needs its own `totalDegree` bound before `matrixA`/`rhsVec`'s entry theorem
can be assembled — i.e. a theorem of the shape "if `IsRdecWitness ι evalNd
v (n,d)` and [some UFD/reducedness argument], then `totalDegree n ≤ ...`."
This is NOT automatic from `IsRdecWitness` alone (an arbitrary witness pair
can have arbitrarily large degree — e.g. `(n,d) = (2*n₀, 2*d₀)` for any
valid `(n₀,d₀)` is also a valid witness, same degree, but `(n² * n₀, n² *
d₀)` inflates degree for no reason). The degree bound instead has to come
from EACH SIDE's own already-proved bound (`anchor1_fst/snd_totalDegree_le`
etc., `MatrixEntryTotalDegree.lean`/`AnchorTotalDegree.lean`) applied
directly to the multiplied pair's factors (`na*nb`'s degree ≤ `na`'s degree
+ `nb`'s degree, via `MvPolynomial.totalDegree_mul`, NOT via `IsRdecWitness`
at all) — `IsRdecWitness`'s only job is establishing that `(na*nb, da*db)`
is legitimately `a*b`'s witness so THAT degree bound is meaningful for the
right value, not a free-floating pair. The actual `matrixA`/`rhsVec` entry
assembly (composing this with `totalDegree_pow_le`/`rrBasis5_getD_bi_le_three`
per `MatrixEntryTotalDegree.lean`'s own status note) is still the next step,
not attempted in this file. -/

end TheDataDerivation
end Genus2Lean
