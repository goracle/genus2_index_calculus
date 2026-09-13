import Mathlib
import Genus2Lean.ZeroD.FinrankLeOfMonicAnnihilator

/-!
# Stages 0–3 degree bound: linear-elimination generators (core lemma)

Item 2 of `ROADMAP-monic-annihilator-degree-uniform.md`'s file plan, step
3 of its "Suggested order" (after the core lemma and the already-monic
curve relations, before the harder `_ext`-shaped stages 4–7).

**Shape, from `PeelChainAssembly.lean` (traced via `DecoupledSystemRegular
.lean`'s `regular_of_linear_elim`)**: each of the four matching-generator
stages (`Fu0 = u1_num(0) − U0·u1_den(0)`, and similarly `Fu1`/`Fu2`/`Fu3`)
is, in the newly-peeled variable, exactly `c − X·d` for `c, d` in the
algebra built from the previous stages — linear, but NOT monic as
written (its `X`-leading coefficient is `-d`, not `1`).

**What this file provides**: a single generic per-stage lemma,
`finrank_le_of_linear_elim`, taking the "leading coefficient is a unit"
hypothesis the roadmap calls for (`IsUnit d`, NOT bare `d ≠ 0`) and
concluding the degree-1 `finrank` bound `finrank k B ≤ finrank k A`. Like
`CurveRelationsDegreeBound.lean`, this is stated abstractly over any
commutative ring `A` and any `c d : A` — NOT yet specialized to `Rdec p`
or wired into the literal `genList`/`Fu0` definitions; that identification
is later Assembly work (item 5), matching this project's existing split
between "single-stage fact" (this file) and "chaining across stages"
(later files).

**Proof strategy**: `c − X·d` is not monic, but since `d` is a unit it
generates the SAME ideal in `Polynomial A` as `X − C (d⁻¹ * c)` (unit
multiples generate equal ideals — `Ideal.span_singleton_mul_left_unit`,
which needs no `IsDomain` hypothesis), which IS monic of degree 1
(`Polynomial.monic_X_sub_C`). So `AdjoinRoot (c - X*d) ≃+* AdjoinRoot (X -
C (d⁻¹*c))` (via `AdjoinRoot.algEquivOfEq`/`Ideal.span`-level equality,
mirroring how `CurveRelationsDegreeBound.lean` builds its own `AdjoinRoot`
argument), and `finrank_le_of_monic_annihilator` applies to the monic
side with `d_deg := 1`. Since `natDegree = 1`, the final bound reads
`finrank k B ≤ 1 * finrank k A`, matching stages 0–3's linear shape (as
opposed to stages 8–11's `d = 2`). -/

namespace Genus2Lean

open Polynomial

variable {k A : Type*} [Field k] [CommRing A] [Nontrivial A] [Algebra k A]
  [StrongRankCondition A] [Module.Finite k A]

/-- The (non-monic, as written) linear-elimination polynomial `C c − X *
C d`, matching `Fu0`/`Fu1`/`Fu2`/`Fu3`'s literal shape `numerator − X *
denominator` before any unit-rescaling. -/
noncomputable def linearElimPoly (c d : A) : Polynomial A :=
  Polynomial.C c - Polynomial.X * Polynomial.C d

/-- The monic rescaling of `linearElimPoly c d` once `d` is a unit:
`X − C (d⁻¹ * c)`, a unit multiple of `linearElimPoly c d` (specifically
`(-d⁻¹) • linearElimPoly c d`, so it generates the same ideal — see
`linearElimPoly_span_eq` below), and monic of degree 1 by
`Polynomial.monic_X_sub_C`. -/
noncomputable def linearElimMonicPoly (c d : A) (hd : IsUnit d) : Polynomial A :=
  Polynomial.X - Polynomial.C (↑hd.unit⁻¹ * c)

theorem linearElimMonicPoly_monic (c d : A) (hd : IsUnit d) :
    (linearElimMonicPoly c d hd).Monic :=
  Polynomial.monic_X_sub_C _

theorem linearElimMonicPoly_natDegree (c d : A) (hd : IsUnit d) :
    (linearElimMonicPoly c d hd).natDegree = 1 :=
  Polynomial.natDegree_X_sub_C _

/-- The two generators are unit multiples of one another, hence generate
the same principal ideal of `Polynomial A`: `linearElimPoly c d =
(-C d) * linearElimMonicPoly c d hd` (check by `ring`-style expansion
after unfolding both, using `hd.unit`'s defining equation `d * d⁻¹ = 1`
to cancel `d * (d⁻¹ * c)` down to `c`), and `C d` is a unit in
`Polynomial A` since `d` is a unit in `A` (`Polynomial.isUnit_C`). -/
theorem linearElimPoly_eq_unit_mul (c d : A) (hd : IsUnit d) :
    linearElimPoly c d = (-(Polynomial.C d)) * linearElimMonicPoly c d hd := by
  unfold linearElimPoly linearElimMonicPoly
  have hcancel : d * (↑hd.unit⁻¹ * c) = c := by
    have hdu : d * ↑hd.unit⁻¹ = 1 := by
      nth_rewrite 1 [← hd.unit_spec]
      exact hd.unit.mul_inv
    rw [← mul_assoc, hdu, one_mul]
  have : (-(Polynomial.C d)) * (Polynomial.X - Polynomial.C (↑hd.unit⁻¹ * c)) =
      Polynomial.C d * Polynomial.C (↑hd.unit⁻¹ * c) - Polynomial.C d * Polynomial.X := by
    ring
  rw [this, ← Polynomial.C_mul, hcancel]
  ring

/-- Generic, definition-free helper: `Ideal.span {u * q} = Ideal.span {q}`
whenever `u` is a unit. Split out from `linearElimPoly_span_eq` so that the
elaborator unifies `Ideal.span_singleton_mul_left_unit` against plain
variables `u q : Polynomial A` here, rather than against the unfolded
`linearElimPoly`/`linearElimMonicPoly` definitions directly — the latter,
combined with this file's heavy ambient typeclass stack on `A`
(`CommRing`, `Nontrivial`, `StrongRankCondition`, `Module.Finite k A`),
was enough to blow the `whnf` heartbeat budget during unification even
after raising `maxHeartbeats`. This lemma carries none of that context in
its statement, so it elaborates cheaply, and `linearElimPoly_span_eq`
below only has to specialize it via a plain `rw` + `exact`. -/
theorem span_of_isUnit_mul_left {u q : Polynomial A} (hu : IsUnit u) :
    Ideal.span ({u * q} : Set (Polynomial A)) = Ideal.span ({q} : Set (Polynomial A)) :=
  Ideal.span_singleton_mul_left_unit hu q

theorem linearElimPoly_span_eq (c d : A) (hd : IsUnit d) :
    Ideal.span {linearElimPoly c d} = Ideal.span ({linearElimMonicPoly c d hd} : Set (Polynomial A)) := by
  have hCd : IsUnit (-(Polynomial.C d) : Polynomial A) := by
    rw [← map_neg Polynomial.C d]
    exact Polynomial.isUnit_C.mpr hd.neg
  rw [linearElimPoly_eq_unit_mul c d hd]
  exact span_of_isUnit_mul_left hCd

variable {B : Type*} [CommRing B] [Algebra A B] [Algebra k B] [IsScalarTower k A B]

/-- Transport a root of `linearElimPoly c d` across an `A`-algebra `B` to a
root of the monic rescaling `linearElimMonicPoly c d hd`, and back. Both
directions are immediate from `linearElimPoly_eq_unit_mul` (`aeval` is a
ring hom, so it turns the unit-multiple identity `linearElimPoly c d =
(-(C d)) * linearElimMonicPoly c d hd` into a product-in-`B` identity) plus
cancellation against the unit `aeval t (-(C d)) = -(algebraMap A B d)`,
whose invertibility in `B` comes straight from `hd : IsUnit d` via
`RingHom.isUnit_map`. No use of `linearElimPoly_span_eq` / `Ideal.span` is
needed here — this is a direct algebraic argument, one step shorter. -/
theorem aeval_linearElimPoly_eq_zero_iff (c d : A) (hd : IsUnit d) (t : B) :
    (Polynomial.aeval t) (linearElimPoly c d) = 0 ↔
      (Polynomial.aeval t) (linearElimMonicPoly c d hd) = 0 := by
  have hstep : (Polynomial.aeval t) (linearElimPoly c d) =
      (Polynomial.aeval t) (-(Polynomial.C d)) * (Polynomial.aeval t) (linearElimMonicPoly c d hd) := by
    rw [← map_mul, ← linearElimPoly_eq_unit_mul c d hd]
  have hunit : IsUnit ((Polynomial.aeval t) (-(Polynomial.C d)) : B) := by
    have hCd : IsUnit (-(Polynomial.C d) : Polynomial A) := by
      rw [← map_neg Polynomial.C d]
      exact Polynomial.isUnit_C.mpr hd.neg
    exact (Polynomial.aeval t).toRingHom.isUnit_map hCd
  rw [hstep]
  exact hunit.mul_right_eq_zero

/-- **This file's headline deliverable** (per the module docstring): the
degree-1 `finrank` bound for each of the four matching-generator peel-chain
stages (`Fu0`–`Fu3`), stated abstractly. If `t : B` is an `A`-algebra
element satisfying the (non-monic) linear-elimination relation `c = t * d`
(equivalently `aeval t (linearElimPoly c d) = 0`, i.e. `t` is a root of
`C c − X * C d`) for a unit `d : A`, and `t` generates `B` as an
`A`-algebra, then `finrank k B ≤ finrank k A`.

**Proof**: transport the root property to the monic rescaling
`linearElimMonicPoly c d hd` via `aeval_linearElimPoly_eq_zero_iff`, then
apply the already-proved core fact `finrank_le_of_monic_annihilator` with
`G := linearElimMonicPoly c d hd` (monic by `linearElimMonicPoly_monic`,
`natDegree = 1` by `linearElimMonicPoly_natDegree`), and simplify the
resulting `1 * finrank k A` down to `finrank k A`. -/
theorem finrank_le_of_linear_elim (c d : A) (hd : IsUnit d) (t : B)
    (ht : (Polynomial.aeval t) (linearElimPoly c d) = 0)
    (hgen : Algebra.adjoin A {t} = (⊤ : Subalgebra A B)) :
    Module.finrank k B ≤ Module.finrank k A := by
  have ht' : (Polynomial.aeval t) (linearElimMonicPoly c d hd) = 0 :=
    (aeval_linearElimPoly_eq_zero_iff c d hd t).mp ht
  have hbound := finrank_le_of_monic_annihilator (k := k) (A := A) (B := B)
    (linearElimMonicPoly c d hd) (linearElimMonicPoly_monic c d hd) t ht' hgen
  rwa [linearElimMonicPoly_natDegree c d hd, one_mul] at hbound

end Genus2Lean
