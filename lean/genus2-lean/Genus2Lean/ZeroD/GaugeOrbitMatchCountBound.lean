import Mathlib
import Genus2Lean.DivisorClassGroup
import Genus2Lean.RiemannRochGenus2
import Genus2Lean.ZeroD.MatchingSolutionSwapSymmetry
import Genus2Lean.ZeroD.MatchingEquationTranslation

/-!
# The gauge orbit of eq 1 versus the fixed-pair-sum fiber

## Status (2026-09-18): the earlier main theorem was FALSE as stated

This file used to end in `gaugeOrbitSolutions_eq_swapImages`, claiming
`GaugeOrbitSolutions δ₀ a alpha alpha' = swapImages P1 P2 P3 P4`, with one
`sorry` at the step "every `x` in the gauge orbit has the reference's
pair-sums". That step is not merely unproved, it is false:

* `GaugeOrbitSolutions`'s `c` is vacuous: `(alpha+c)-(alpha'+c) = alpha-alpha'`
  (`eq1_gauge_invariant`). So the set is exactly the difference-only set
  `{x | s P1 + s P2 - s P3 - s P4 = (alpha-alpha')•a}` — the set
  `MatchingSolutionSwapSymmetry.lean`'s module docstring already records as
  not bounded independently of `p`.
* It is the union, over pair-sum classes `A'`, of
  `FixedTargetSolutions A' (A' - Δ)` (`gaugeOrbit_eq_iUnion_fixedTarget`).
  `IsOnlyEffectiveInClass` bounds each piece by 4 and says nothing about how
  many classes `A'` occur. For instance, any quadruple with pair-sums
  `(A+a, B+a)` (the `c = 1` shift of the reference pair-sums) has the same
  difference but is not a swap of the reference unless `a = 0`.
  `gaugeOrbit_ne_swapImages_of_pairSum_ne` is the precise obstruction.
* The gauge-shift-on-`D` argument of `ROADMAP-alpha-locus.md` shows the SAME
  four points persist in each shifted 0D system WITH THE TRANSPORTED TARGET.
  Transported targets have UNCHANGED pair-sums `(A,B)`, so what that argument
  controls is the single fiber `FixedTargetSolutions A B` — already known to
  be ≤ 4. It never reaches a solution whose own pair-sums differ from `(A,B)`.

## What is here now (no `sorry`; drafted without a Lean toolchain, needs a build)

* `gaugeOrbit_eq_iUnion_fixedTarget`: the honest decomposition of the whole
  `Δ`-fiber into fixed-target fibers, one per pair-sum class.
* `gaugeOrbit_inter_fixedTarget_eq_swapImages`: the TRUE statement — the gauge
  orbit intersected with the reference's own pair-sum fiber is exactly
  `swapImages`. `..._ncard_le_four` is the corollary.
* `gaugeOrbit_ne_swapImages_of_pairSum_ne`: why the old equality cannot hold.

## What remains open

Bounding the number of pair-sum classes `A'` realized by a given `Δ` (for the
factor-base-restricted count this is what `matchCount T Δ ≤ K` needs). Nothing
in this file, and nothing in the gauge-shift argument, addresses it. See the
"actual gap" paragraph of `ROADMAP-alpha-locus.md`. -/

open HyperellipticPolynomial
open Divisor
open Genus2Lean.MatchingSolutionSwapSymmetry
open Genus2Lean.HyperellipticPolynomialMatching

namespace Genus2Lean
namespace GaugeOrbitMatchCountBound

variable {k : Type*} [Field k] {H : HyperellipticPolynomial k}
variable (D : PrincipalDivisorData H)
variable [IsDedekindDomain (CoordinateRing H)]

/-! ## The gauge-orbit solution set, and the ≤4 bound -/

/-- **`GaugeOrbitSolutions δ₀ a alpha alpha'`**: every `H.Point`-quadruple
solving eq 1 for SOME `(alpha+c, alpha'+c)`. Since `(alpha+c)-(alpha'+c) =
alpha-alpha'` for every `c`, the `c` is vacuous: this is the WHOLE `Δ`-fiber
`{x | s x.1 + s x.2.1 - s x.2.2.1 - s x.2.2.2 = (alpha-alpha')•a}` — the object
`matchCount T Δ` counts — and in particular it ranges over ALL pair-sum
classes, not one. -/
def GaugeOrbitSolutions (δ₀ : H.Point) (a : Jacobian H D) (alpha alpha' : ℤ) :
    Set (H.Point × H.Point × H.Point × H.Point) :=
  {x | ∃ c : ℤ,
    s D δ₀ x.1 + s D δ₀ x.2.1 - s D δ₀ x.2.2.1 - s D δ₀ x.2.2.2 =
      ((alpha + c) - (alpha' + c)) • a}

/-- **The reference solution lies in its own gauge orbit** (take `c = 0`).
Since eq 1 only depends on `alpha,alpha'` through their difference
(`eq1_gauge_invariant`), this is pure `AddCommGroup` algebra from `heq`. -/
theorem gaugeOrbit_reference_persists
    (δ₀ : H.Point) (a : Jacobian H D) (alpha alpha' : ℤ)
    (P1 P2 P3 P4 : H.Point)
    (heq : s D δ₀ P1 + s D δ₀ P2 - s D δ₀ P3 - s D δ₀ P4 = (alpha - alpha') • a) :
    (P1, P2, P3, P4) ∈ GaugeOrbitSolutions D δ₀ a alpha alpha' := by
  refine ⟨0, ?_⟩
  simpa using heq

/-- **All 4 `swapImages` elements are in `GaugeOrbitSolutions`.** Swapping
`P1,P2` (resp. `P3,P4`) doesn't change the pair-sum, so each swap solves
the same reference equation as `(P1,P2,P3,P4)` and
`gaugeOrbit_reference_persists` applies to it too. -/
theorem swapImages_subset_gaugeOrbit
    (δ₀ : H.Point) (a : Jacobian H D) (alpha alpha' : ℤ)
    (P1 P2 P3 P4 : H.Point)
    (heq : s D δ₀ P1 + s D δ₀ P2 - s D δ₀ P3 - s D δ₀ P4 = (alpha - alpha') • a) :
    swapImages P1 P2 P3 P4 ⊆ GaugeOrbitSolutions D δ₀ a alpha alpha' := by
  have heq21 : s D δ₀ P2 + s D δ₀ P1 - s D δ₀ P3 - s D δ₀ P4 = (alpha - alpha') • a := by
    rw [add_comm]; exact heq
  have heq12' : s D δ₀ P1 + s D δ₀ P2 - s D δ₀ P4 - s D δ₀ P3 = (alpha - alpha') • a := by
    rw [sub_right_comm]; exact heq
  have heq21' : s D δ₀ P2 + s D δ₀ P1 - s D δ₀ P4 - s D δ₀ P3 = (alpha - alpha') • a := by
    rw [add_comm]; exact heq12'
  intro q hq
  simp only [swapImages, Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with h | h | h | h
  · rw [h]; exact gaugeOrbit_reference_persists D δ₀ a alpha alpha' P1 P2 P3 P4 heq
  · rw [h]; exact gaugeOrbit_reference_persists D δ₀ a alpha alpha' P2 P1 P3 P4 heq21
  · rw [h]; exact gaugeOrbit_reference_persists D δ₀ a alpha alpha' P1 P2 P4 P3 heq12'
  · rw [h]; exact gaugeOrbit_reference_persists D δ₀ a alpha alpha' P2 P1 P4 P3 heq21'


/-- **Unpacking `GaugeOrbitSolutions` into `FixedTargetSolutions`-shape
membership.** Every element is, for some `c`, in the fixed-target fiber cut out
by ITS OWN pair-sums, with the `c`-shifted difference equation. NOTE the
target of that fiber is computed from `x` itself, so this says nothing about
`x`'s pair-sums agreeing with any reference's — see the module docstring. -/
theorem gaugeOrbit_mem_iff (δ₀ : H.Point) (a : Jacobian H D) (alpha alpha' : ℤ)
    (x : H.Point × H.Point × H.Point × H.Point) :
    x ∈ GaugeOrbitSolutions D δ₀ a alpha alpha' ↔
      ∃ c : ℤ, x ∈ FixedTargetSolutions D δ₀
        (s D δ₀ x.1 + s D δ₀ x.2.1) (s D δ₀ x.2.2.1 + s D δ₀ x.2.2.2) ∧
        s D δ₀ x.1 + s D δ₀ x.2.1 - (s D δ₀ x.2.2.1 + s D δ₀ x.2.2.2) =
          ((alpha + c) - (alpha' + c)) • a := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, ⟨rfl, rfl⟩, by rw [← hc]; abel⟩
  · rintro ⟨c, -, hc⟩
    exact ⟨c, by rw [← hc]; abel⟩

/-- **Membership in `FixedTargetSolutions`, unfolded.** `Iff.rfl`; stated so
later proofs can `rw` instead of relying on anonymous-constructor unfolding of
a non-reducible `def`. -/
theorem mem_fixedTargetSolutions_iff (δ₀ : H.Point) (A B : Jacobian H D)
    (x : H.Point × H.Point × H.Point × H.Point) :
    x ∈ FixedTargetSolutions D δ₀ A B ↔
      s D δ₀ x.1 + s D δ₀ x.2.1 = A ∧ s D δ₀ x.2.2.1 + s D δ₀ x.2.2.2 = B :=
  Iff.rfl

/-- **The `Δ`-fiber is the union of the fixed-target fibers, one per pair-sum
class.** With `Δ := (alpha-alpha')•a`, a quadruple has difference `Δ` iff its
own pair-sums are `(A', A'-Δ)` for `A' := s x.1 + s x.2.1`. This is the honest
form of the roadmap's "actual gap" decomposition: each piece is ≤ 4
(`fixedTargetSolutions_ncard_le_four`), and nothing here bounds how many `A'`
occur. -/
theorem gaugeOrbit_eq_iUnion_fixedTarget
    (δ₀ : H.Point) (a : Jacobian H D) (alpha alpha' : ℤ) :
    GaugeOrbitSolutions D δ₀ a alpha alpha' =
      ⋃ A : Jacobian H D,
        FixedTargetSolutions D δ₀ A (A - (alpha - alpha') • a) := by
  ext x
  rw [Set.mem_iUnion]
  constructor
  · rintro ⟨c, hc⟩
    rw [← eq1_gauge_invariant a alpha alpha' c] at hc
    refine ⟨s D δ₀ x.1 + s D δ₀ x.2.1, ?_⟩
    rw [mem_fixedTargetSolutions_iff]
    refine ⟨rfl, ?_⟩
    rw [← hc]
    abel
  · rintro ⟨A, hx⟩
    rw [mem_fixedTargetSolutions_iff] at hx
    obtain ⟨hA, hB⟩ := hx
    refine ⟨0, ?_⟩
    rw [← eq1_gauge_invariant a alpha alpha' 0]
    calc s D δ₀ x.1 + s D δ₀ x.2.1 - s D δ₀ x.2.2.1 - s D δ₀ x.2.2.2
        = (s D δ₀ x.1 + s D δ₀ x.2.1) - (s D δ₀ x.2.2.1 + s D δ₀ x.2.2.2) := by abel
      _ = A - (A - (alpha - alpha') • a) := by rw [hA, hB]
      _ = (alpha - alpha') • a := by abel

/-- **A fixed pair-sum fiber sits inside `swapImages` of any base solution.**
Same argument as the inlined `hsub` in `fixedTargetSolutions_ncard_le_four`
(`MatchingSolutionSwapSymmetry.lean`), exported as a set inclusion so it can
be reused without the cardinality bound. -/
theorem fixedTargetSolutions_subset_swapImages
    {hdeg : H.f.natDegree = 5} {δ₀ : H.Point}
    (hbridge : D.P ≤ principalSubgroup H hdeg)
    {P1 P2 P3 P4 : H.Point}
    (heffective12 : IsOnlyEffectiveInClass hdeg P1 P2)
    (heffective34 : IsOnlyEffectiveInClass hdeg P3 P4) :
    FixedTargetSolutions D δ₀ (s D δ₀ P1 + s D δ₀ P2) (s D δ₀ P3 + s D δ₀ P4) ⊆
      swapImages P1 P2 P3 P4 := by
  rintro ⟨P1', P2', P3', P4'⟩ ⟨h1, h2⟩
  have hA' : s D δ₀ P1' + s D δ₀ P2' = s D δ₀ P1 + s D δ₀ P2 := h1
  have hB' : s D δ₀ P3' + s D δ₀ P4' = s D δ₀ P3 + s D δ₀ P4 := h2
  have hiff12 := (s_add_s_eq_s_add_s_iff D δ₀ P1 P2 P1' P2').mp hA'.symm
  have hiff34 := (s_add_s_eq_s_add_s_iff D δ₀ P3 P4 P3' P4').mp hB'.symm
  have hmem12 : (single P1 + single P2 - single P1' - single P2' : Divisor H) ∈
      principalSubgroup H hdeg := hbridge hiff12
  have hmem34 : (single P3 + single P4 - single P3' - single P4' : Divisor H) ∈
      principalSubgroup H hdeg := hbridge hiff34
  have hset12 : ({P1', P2'} : Set H.Point) = {P1, P2} := heffective12 P1' P2' hmem12
  have hset34 : ({P3', P4'} : Set H.Point) = {P3, P4} := heffective34 P3' P4' hmem34
  have hcase12 := pair_eq_pair_cases hset12
  have hcase34 := pair_eq_pair_cases hset34
  simp only [swapImages, Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases hcase12 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases hcase34 with ⟨e3, e4⟩ | ⟨e3, e4⟩
  · exact Or.inl (by rw [e1, e2, e3, e4])
  · exact Or.inr (Or.inr (Or.inl (by rw [e1, e2, e3, e4])))
  · exact Or.inr (Or.inl (by rw [e1, e2, e3, e4]))
  · exact Or.inr (Or.inr (Or.inr (by rw [e1, e2, e3, e4])))

/-- **Main theorem (the true one).** The gauge orbit, intersected with the
reference solution's OWN pair-sum fiber `FixedTargetSolutions (s P1+s P2)
(s P3+s P4)`, is exactly `swapImages P1 P2 P3 P4`. The pair-sum pinning is
essential: without it the left side is the whole `Δ`-fiber, which is not
`swapImages` in general (`gaugeOrbit_ne_swapImages_of_pairSum_ne`). ⊆ is
`fixedTargetSolutions_subset_swapImages`; ⊇ is `swapImages_subset_gaugeOrbit`
plus the fact that swapping within a pair preserves its pair-sum. -/
theorem gaugeOrbit_inter_fixedTarget_eq_swapImages
    {hdeg : H.f.natDegree = 5} {δ₀ : H.Point} {a : Jacobian H D} {alpha alpha' : ℤ}
    (hbridge : D.P ≤ principalSubgroup H hdeg)
    {P1 P2 P3 P4 : H.Point}
    (heffective12 : IsOnlyEffectiveInClass hdeg P1 P2)
    (heffective34 : IsOnlyEffectiveInClass hdeg P3 P4)
    (heq : s D δ₀ P1 + s D δ₀ P2 - s D δ₀ P3 - s D δ₀ P4 = (alpha - alpha') • a) :
    GaugeOrbitSolutions D δ₀ a alpha alpha' ∩
        FixedTargetSolutions D δ₀ (s D δ₀ P1 + s D δ₀ P2) (s D δ₀ P3 + s D δ₀ P4) =
      swapImages P1 P2 P3 P4 := by
  apply Set.Subset.antisymm
  · intro x hx
    exact fixedTargetSolutions_subset_swapImages D hbridge heffective12 heffective34 hx.2
  · intro x hx
    refine ⟨swapImages_subset_gaugeOrbit D δ₀ a alpha alpha' P1 P2 P3 P4 heq hx, ?_⟩
    rw [mem_fixedTargetSolutions_iff]
    simp only [swapImages, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨rfl, rfl⟩
    · exact ⟨add_comm _ _, rfl⟩
    · exact ⟨rfl, add_comm _ _⟩
    · exact ⟨add_comm _ _, add_comm _ _⟩

/-- **The ≤4 bound, for the correct set.** Corollary of
`gaugeOrbit_inter_fixedTarget_eq_swapImages` and `swapImages_ncard_le`. -/
theorem gaugeOrbit_inter_fixedTarget_ncard_le_four [DecidableEq H.Point]
    {hdeg : H.f.natDegree = 5} {δ₀ : H.Point} {a : Jacobian H D} {alpha alpha' : ℤ}
    (hbridge : D.P ≤ principalSubgroup H hdeg)
    {P1 P2 P3 P4 : H.Point}
    (heffective12 : IsOnlyEffectiveInClass hdeg P1 P2)
    (heffective34 : IsOnlyEffectiveInClass hdeg P3 P4)
    (heq : s D δ₀ P1 + s D δ₀ P2 - s D δ₀ P3 - s D δ₀ P4 = (alpha - alpha') • a) :
    (GaugeOrbitSolutions D δ₀ a alpha alpha' ∩
        FixedTargetSolutions D δ₀ (s D δ₀ P1 + s D δ₀ P2)
          (s D δ₀ P3 + s D δ₀ P4)).ncard ≤ 4 := by
  rw [gaugeOrbit_inter_fixedTarget_eq_swapImages D hbridge heffective12 heffective34 heq]
  exact swapImages_ncard_le P1 P2 P3 P4

/-- **Why the unpinned equality `GaugeOrbitSolutions = swapImages` cannot
hold.** A single gauge-orbit member whose own first pair-sum differs from the
reference's already breaks it: swaps never change the pair-sum. (Such members
exist, e.g. any quadruple with pair-sums `(A+a, B+a)` when both classes have
effective representatives and `a ≠ 0` — a mathematical remark, not proved
here.) -/
theorem gaugeOrbit_ne_swapImages_of_pairSum_ne
    {δ₀ : H.Point} {a : Jacobian H D} {alpha alpha' : ℤ}
    {P1 P2 P3 P4 : H.Point} {x : H.Point × H.Point × H.Point × H.Point}
    (hx : x ∈ GaugeOrbitSolutions D δ₀ a alpha alpha')
    (hne : s D δ₀ x.1 + s D δ₀ x.2.1 ≠ s D δ₀ P1 + s D δ₀ P2) :
    GaugeOrbitSolutions D δ₀ a alpha alpha' ≠ swapImages P1 P2 P3 P4 := by
  intro h
  rw [h] at hx
  simp only [swapImages, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact hne rfl
  · exact hne (add_comm _ _)
  · exact hne rfl
  · exact hne (add_comm _ _)

end GaugeOrbitMatchCountBound
end Genus2Lean
