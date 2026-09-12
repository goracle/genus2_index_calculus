import Mathlib
import Genus2Lean.ZeroD.QuadCoordBound
import Genus2Lean.ZeroD.TowerToRdecMul
import Genus2Lean.ZeroD.NpolyTotalDegree
import Genus2Lean.ZeroD.RhsVecTotalDegree

/-!
# `HasRdecBound`: `HasQuadBound`'s abstract `dg` instantiated as
"has a bounded `IsRdecWitness`"

New this pass, per option (2) from `QuadCoordBound.lean`'s own open
question: rather than routing a genuinely mixed tower element (e.g.
`curBeforeMonic.coeff i`, per `CrossResultantIsRdecWitness.lean`'s own
docstring, NOT a base-case `algebraMap` lift) through an `IsLocalization
.mk'`-witness bridge, apply `HasQuadBound`'s existing coordinate-tracking
machinery directly, with `dg` instantiated as **existence of a bounded
`IsRdecWitness`** rather than a literal degree function.

**Why this needs a NEW predicate, not literally `HasQuadBound` itself**:
`HasQuadBound dg c x a0 a1` requires `dg : R → ℕ`, an actual FUNCTION —
but "has an `IsRdecWitness` pair of `totalDegree ≤ D`" is a RELATION on
`(v : K) (D : ℕ)` (a value can have witnesses at many different bounds,
so there is no canonical single number to hand back). `HasRdecBound`
below is the direct relational analogue: same four closure properties
(`zero`/`neg`/`add`/`mul`, matching `HasQuadBound`'s `dg 0`/`hdg_neg`/
`hdg_add`/`hdg_mul` hypotheses exactly, now as separate lemmas rather
than side-conditions on an opaque `dg`), then `HasQuadCoordBound` mirrors
`HasQuadBound` itself, phrased against `HasRdecBound` for its two
coordinates directly instead of via a `dg`-application.

**Confirmed against the actual combinator suite in `TowerToRdecMul.lean`/
`NpolyTotalDegree.lean`/`RhsVecTotalDegree.lean`** (not assumed): `.zero`
(the trivial `(0,1)` pair, degree `0`), `.neg` (`(n,d) ↦ (-n,d)`, degree
unchanged on the numerator side, `MvPolynomial.totalDegree_neg`), `.add`
(`(na*db+nb*da, da*db)`, so `totalDegree ≤ max(Da+Db, Da+Db) = Da+Db` on
the numerator — a SUM, not a max, unlike `HasQuadBound`'s abstract
`hdg_add`'s `max` shape; see the correction note on `hasRdecBound_add`
below for why this file states a slightly different, but still
sufficient, bound), `.mul` (`(na*nb, da*db)`, `totalDegree ≤ Da+Db` on
both sides — this one DOES match `hdg_mul`'s `dg u + dg v` shape exactly).

**Scope of this pass**: only the four relation-level closure lemmas
(`hasRdecBound_zero/_neg/_add/_mul`) plus `HasQuadCoordBound`'s
definition are drafted here. Wiring this into `curBeforeMonic.coeff i`'s
actual `%ₘ`-chain construction (the concrete instantiation this file
exists to enable) is NOT attempted in this pass — flagged as the
concrete next step, per the working agreement's "write general
infrastructure even before the exact call site is nailed down" mindset.

**Not yet REPL-confirmed** — drafted this pass; Claire tests via the REPL.
-/

namespace Genus2Lean
namespace TheDataDerivation

variable (p : ℕ) [hp : Fact (Nat.Prime p)] [hp2 : Fact (p ≠ 2)]

open Polynomial

/-! ## The bound relation -/

/-- **`v` has a bounded `IsRdecWitness`.** The relational analogue of
`HasQuadBound`'s abstract `dg v ≤ D`, instantiated so that "the degree
of `v`" means "the least `totalDegree` we can currently exhibit a valid
cross-multiplied numerator/denominator witness at" rather than a single
canonical number — this is exactly the shape `CoeffsOutTotalDegree.lean`'s
own `∃ nd, IsRdecWitness ... ∧ nd.1.totalDegree ≤ D₁ ∧ ...` idiom already
uses ad hoc at several call sites; naming it here lets it compose via
general closure lemmas instead of being re-derived by hand each time. -/
def HasRdecBound {Vars K L : Type*} [CommRing K] [CommRing L]
    (ι : K →+* L) (evalNd : MvPolynomial Vars (F p) →+* L) (v : K) (D : ℕ) : Prop :=
  ∃ nd : MvPolynomial Vars (F p) × MvPolynomial Vars (F p),
    IsRdecWitness p ι evalNd v nd ∧ nd.1.totalDegree ≤ D ∧ nd.2.totalDegree ≤ D

/-! ## Closure lemmas, matching `TowerToRdecMul.lean`/`NpolyTotalDegree.lean`/
`RhsVecTotalDegree.lean`'s own combinator suite exactly -/

/-- **Zero.** The trivial witness `(0, 1)` — `evalNd 0 = 0 = evalNd 1 * ι 0`
(`map_zero`/`mul_zero`) — has numerator `totalDegree 0` (`MvPolynomial.
totalDegree_zero`) and denominator `totalDegree 0` (`MvPolynomial.
totalDegree_one`), so `HasRdecBound` holds at any `D` (monotonicity is
baked into the definition via `≤`, not a separate lemma). -/
theorem hasRdecBound_zero {Vars K L : Type*} [CommRing K] [CommRing L]
    (ι : K →+* L) (evalNd : MvPolynomial Vars (F p) →+* L) (D : ℕ) :
    HasRdecBound p ι evalNd (0 : K) D := by
  refine ⟨(0, 1), ?_, ?_, ?_⟩
  · unfold IsRdecWitness
    simp
  · -- `(0 : MvPolynomial Vars (F p)).totalDegree = 0` — left to `simp` rather than a guessed
    -- lemma name (no confirmed `MvPolynomial.totalDegree_zero` name found in this project's
    -- own usage; `simp` finds whatever the actual simp-tagged fact is).
    simp
  · rw [MvPolynomial.totalDegree_one]; exact Nat.zero_le D

/-- **Negation.** `IsRdecWitness.neg` sends `(n,d) ↦ (-n,d)`
(`RhsVecTotalDegree.lean`), so the numerator's `totalDegree` is unchanged
(`MvPolynomial.totalDegree_neg`) and the denominator is literally the
same polynomial — both bounds transfer unchanged. -/
theorem hasRdecBound_neg {Vars K L : Type*} [CommRing K] [CommRing L]
    {ι : K →+* L} {evalNd : MvPolynomial Vars (F p) →+* L}
    {v : K} {D : ℕ} (hv : HasRdecBound p ι evalNd v D) :
    HasRdecBound p ι evalNd (-v) D := by
  obtain ⟨⟨n, d⟩, hwit, hn, hd⟩ := hv
  refine ⟨(-n, d), IsRdecWitness.neg p hwit, ?_, hd⟩
  simpa using hn

/-- **Addition.** `IsRdecWitness.add` sends `(na,da),(nb,db) ↦
(na*db+nb*da, da*db)` (`NpolyTotalDegree.lean`). Given `Da`-bounded and
`Db`-bounded witnesses, the combined numerator has `totalDegree ≤
max(Da+Db, Db+Da) = Da+Db` (`totalDegree_add`/`_mul`'s triangle
inequalities) and the denominator has `totalDegree ≤ Da+Db`
(`totalDegree_mul`) — **note this is a SUM, not the `max` `HasQuadBound`'s
abstract `hdg_add` hypothesis states**: `IsRdecWitness.add`'s
cross-multiplication genuinely costs more than a `max`-style bound would
(it multiplies witnesses together, unlike `HasQuadBound`'s direct
coordinate subtraction/addition, which never needs to clear a common
denominator). This does not block reusing `HasQuadBound`'s statement
shape, since `HasQuadCoordBound` below is stated fresh against
`HasRdecBound` directly rather than by feeding `HasRdecBound` into
`HasQuadBound`'s existing `hdg_add` slot — the `max`-vs-`sum` mismatch
only matters if one tries to instantiate `HasQuadBound`'s `dg`
hypothesis LITERALLY with this relation coerced into a function, which
this file deliberately does not do. -/
theorem hasRdecBound_add {Vars K L : Type*} [CommRing K] [CommRing L]
    {ι : K →+* L} {evalNd : MvPolynomial Vars (F p) →+* L}
    {a b : K} {Da Db : ℕ}
    (ha : HasRdecBound p ι evalNd a Da) (hb : HasRdecBound p ι evalNd b Db) :
    HasRdecBound p ι evalNd (a + b) (Da + Db) := by
  obtain ⟨⟨na, da⟩, hwa, hna, hda⟩ := ha
  obtain ⟨⟨nb, db⟩, hwb, hnb, hdb⟩ := hb
  refine ⟨(na * db + nb * da, da * db), IsRdecWitness.add p hwa hwb, ?_, ?_⟩
  · calc (na * db + nb * da).totalDegree
        ≤ max (na * db).totalDegree (nb * da).totalDegree :=
          MvPolynomial.totalDegree_add _ _
      _ ≤ Da + Db := by
          apply max_le
          · exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add hna hdb)
          · calc (nb * da).totalDegree ≤ nb.totalDegree + da.totalDegree :=
                MvPolynomial.totalDegree_mul _ _
              _ ≤ Db + Da := Nat.add_le_add hnb hda
              _ = Da + Db := by ring
  · exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add hda hdb)

/-- **Multiplication.** `IsRdecWitness.mul` sends `(na,da),(nb,db) ↦
(na*nb, da*db)` (`TowerToRdecMul.lean`) — pointwise, no cross terms — so
both the numerator and denominator have `totalDegree ≤ Da+Db` directly
via `MvPolynomial.totalDegree_mul`. This DOES match `HasQuadBound`'s
`hdg_mul : dg (u*v) ≤ dg u + dg v` shape exactly (unlike `.add` above),
since `.mul`'s witness never needs to clear a denominator the way
`.add`'s cross-multiplication does. -/
theorem hasRdecBound_mul {Vars K L : Type*} [CommRing K] [CommRing L]
    {ι : K →+* L} {evalNd : MvPolynomial Vars (F p) →+* L}
    {a b : K} {Da Db : ℕ}
    (ha : HasRdecBound p ι evalNd a Da) (hb : HasRdecBound p ι evalNd b Db) :
    HasRdecBound p ι evalNd (a * b) (Da + Db) := by
  obtain ⟨⟨na, da⟩, hwa, hna, hda⟩ := ha
  obtain ⟨⟨nb, db⟩, hwb, hnb, hdb⟩ := hb
  refine ⟨(na * nb, da * db), IsRdecWitness.mul p hwa hwb, ?_, ?_⟩
  · exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add hna hnb)
  · exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add hda hdb)

/-! ## Coordinate-level wrapper, mirroring `HasQuadBound` -/

/-- **`x`'s canonical quadratic-extension coordinates each have a bounded
`IsRdecWitness`.** The direct analogue of `QuadCoordBound.lean`'s
`HasQuadBound`, with `dg (coordinate) ≤ D` replaced by `HasRdecBound
... (coordinate) D` throughout — i.e. this does NOT reuse `HasQuadBound`
itself (since `HasRdecBound` is a relation, not a function fitting
`HasQuadBound`'s `dg : R → ℕ` slot), but restates the same coordinate
bookkeeping fresh, one level up, against `R := K` (the tower level whose
elements `x %ₘ (X^2 - C c)` decomposes). -/
def HasQuadCoordBound {K L : Type*} [CommRing K] [CommRing L] [Nontrivial K]
    {Vars : Type*} (ι : K →+* L) (evalNd : MvPolynomial Vars (F p) →+* L)
    (c : K) (x : Polynomial K) (a0 a1 : ℕ) : Prop :=
  HasRdecBound p ι evalNd ((x %ₘ (X ^ 2 - C c)).coeff 0) a0 ∧
  HasRdecBound p ι evalNd ((x %ₘ (X ^ 2 - C c)).coeff 1) a1

end TheDataDerivation
end Genus2Lean
