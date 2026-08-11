import Mathlib
import Genus2Lean.HyperellipticFunctionField
import Genus2Lean.AffinePoints
import Genus2Lean.DivisorClassGroup
import Genus2Lean.PrincipalDivisors
import Genus2Lean.PrincipalDivisorSubgroup
import Genus2Lean.FFKSidon
import Genus2Lean.HyperellipticClassProof
import Genus2Lean.RiemannRochGenus2
noncomputable section

open Classical

set_option linter.style.header false

open Polynomial

/-!
# Closure collapse: every `principalSubgroup` element is the divisor of a single ratio

**Extracted from `PrincipalSubgroupCollapse.lean`** so that `RiemannRochCrux.lean`
can import this material directly, without an import cycle. The two steps proved
here are entirely independent of `RiemannRochCrux.lean`'s `uniqueDegree2MapToP1`
(the cited, genuinely hard external fact) — they only became stranded downstream
of it because they originally lived in a file that (for its own final-assembly
theorems) also imported `RiemannRochCrux.lean`. Splitting them out lets
`RiemannRochCrux.lean`'s own `isOnlyEffectiveInClass_of_uniqueDegree2MapToP1`
consume them directly and close its `sorry`, while `PrincipalSubgroupCollapse.lean`
now imports this file instead of duplicating its content.

1. **Closure collapse**: every `D ∈ principalSubgroup H hdeg` is the divisor of some
   single nonzero ratio `z : FractionRing (CoordinateRing H)` (not merely a finite
   ± combination of `divToPairRatio` generators) — `isRatioDivisor_of_mem_principalSubgroup`.
2. **Support matching**: given that single ratio `z` for the specific target
   `D = (x₁)+(x₂)-(x₃)-(x₄)`, place `z` (or `z⁻¹`) in `LPairCarrier x₁ x₂` (resp.
   `x₂ x₁`) so `uniqueDegree2MapToP1` can apply downstream, then read off
   `{x₃,x₄} = {x₁,x₂}` from `z` being forced constant — `mem_LPairCarrier_of_isRatioDivisor`.

**Verification status: drafted without a live Lean toolchain (this file is a
line-for-line extraction of previously-drafted material, no proof bodies
changed), same PLAUSIBLE-tier caveat as the rest of this project's unverified
scaffolding — not yet `lake build`-checked.**
-/

namespace HyperellipticPolynomial

open Divisor

variable {k : Type*} [Field k]
variable {H : HyperellipticPolynomial k}
-- `[IsAlgClosed k]` — see `RiemannRochGenus2.lean`'s docstring on its own
-- `variable [IsAlgClosed k]` for why this is now a genuine, necessary
-- standing hypothesis (not a convenience): this file's `IsRatioDivisor`/
-- `mem_LPairCarrier_of_isRatioDivisor` results feed `uniqueDegree2MapToP1`
-- (`RiemannRochCrux.lean`), which is false over a non-algebraically-closed
-- `k` via the `z = 1/q(x)` counterexample documented there.
variable [IsAlgClosed k]
variable [IsDedekindDomain (CoordinateRing H)]

/-- `z` is a `k`-constant inside `FractionRing (CoordinateRing H)`: the image of
some `c : k` under the composite `k → k[X] → CoordinateRing H → FractionRing
(CoordinateRing H)`. Phrased this way (rather than "`z` has empty pole divisor")
because it is the notion `finrank_L_pair`'s conclusion (`ℓ = 1`, spanned by `1`)
actually needs: every element of `LPair x₁ x₂` is *this*, not merely "has no
poles" (the two coincide for a genus ≥ 1 curve, but the constant phrasing is the
one that transfers directly into a `finrank = 1` proof via `1` spanning).

**Moved here from `RiemannRochCrux.lean`**: `mem_LPairCarrier_of_isRatioDivisor`
below states its conclusion in terms of `IsConstantFraction`, and this file is
upstream of `RiemannRochCrux.lean` (which now imports this file, not the other
way around), so the definition has to live here. `RiemannRochCrux.lean` uses
this same definition rather than redeclaring it. -/
def IsConstantFraction (z : FractionRing (CoordinateRing H)) : Prop :=
  ∃ c : k, z = algebraMap (CoordinateRing H) (FractionRing (CoordinateRing H))
    (algebraMap k[X] (CoordinateRing H) (C c))

/-! ## §1. Negation invariance of `ordAt`/`ordInfOfPair` on pairs

Needed for the `neg` case of the closure induction: `divToPairRatio A₁ B₁ S₁ A₂ B₂
S₂`'s negative should again be expressible as a `divToPairRatio`
(swap the two halves), and the underlying ratio `z⁻¹` needs the same
`ordAt`/`ordInfOfPair` values as `z` up to sign — actually simpler than that: since
`divToPairRatio A₁ B₁ S₁ A₂ B₂ S₂ = divToPair A₁ B₁ S₁ - divToPair A₂ B₂ S₂`, its
negative is literally `divToPairRatio A₂ B₂ S₂ A₁ B₁ S₁` (swap), no `ordAt_neg` /
`ordInfOfPair_neg` facts about a *negated polynomial pair* are actually needed for
this file's purposes — swapping the two sides of the ratio already gives negation.
This section is accordingly short: only the ratio-level fact is recorded. -/

/-- `-(divToPairRatio A₁ B₁ S₁ A₂ B₂ S₂) = divToPairRatio A₂ B₂ S₂ A₁ B₁ S₁`: swapping
the numerator/denominator halves negates the divisor. Pure `sub`/`neg` bookkeeping,
no valuation theory needed. -/
theorem divToPairRatio_swap_neg (A₁ B₁ : k[X]) (S₁ : Finset H.Point)
    (A₂ B₂ : k[X]) (S₂ : Finset H.Point) :
    -(divToPairRatio A₁ B₁ S₁ A₂ B₂ S₂) = divToPairRatio A₂ B₂ S₂ A₁ B₁ S₁ := by
  unfold divToPairRatio
  abel

/-! ## §2. `IsRatioDivisor`: the divisor of a single nonzero ratio

The predicate step 1 collapses `principalSubgroup` membership into. Phrased via
`polePairToFraction`-style data (numerator pair, denominator pair, and an explicit
finite support `S` covering every point where either `ordAt` is nonzero) rather
than via an existential over `FractionRing (CoordinateRing H)` directly, so that
`ordAt`/`ordInfOfPair` facts about `D` stay expressed at the `(A,B)`-pair level the
rest of this project already works in. -/

/-- `D` is the divisor `∑_{P ∈ S} (ordAt P A B - ordAt P A' B') • (P)` of a genuine
ratio `toPair H A B / toPair H A' B'`, both sides nonzero, for some explicit
support `S` and some matching `ordInfOfPair` (so the ratio has no pole/zero at
infinity contributing to the affine-degree count — matching
`deg_divToPairRatio_eq_zero`'s hypothesis shape). This is exactly
`D = divToPairRatio A B S A' B' S` (same `S` for both halves is WLOG: pad each
support with the other's via `hsupp`, since `ordAt` outside `S` is `0` and
contributes nothing to the `divToPair` sum either way). -/
def IsRatioDivisor (_hdeg : H.f.natDegree = 5) (D : Divisor H) : Prop :=
  ∃ (A B A' B' : k[X]) (S : Finset H.Point),
    ¬ (A = 0 ∧ B = 0) ∧ ¬ (A' = 0 ∧ B' = 0) ∧
    ordInfOfPair A B = ordInfOfPair A' B' ∧
    (∀ P, P ∉ S → ordAt P A B = 0 ∧ ordAt P A' B' = 0) ∧
    D = divToPairRatio A B S A' B' S

/-- `IsRatioDivisor` holds of `0`: take `A = A' = 1`, `B = B' = 0`, `S = ∅`. -/
theorem isRatioDivisor_zero (hdeg : H.f.natDegree = 5) :
    IsRatioDivisor hdeg (0 : Divisor H) := by
  refine ⟨1, 0, 1, 0, ∅, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun h => one_ne_zero h.1
  · exact fun h => one_ne_zero h.1
  · rfl
  · intro P _
    exact ⟨ordAt_one_zero P, ordAt_one_zero P⟩
  · unfold divToPairRatio divToPair
    simp

/-- `IsRatioDivisor` is closed under negation: swap numerator/denominator (and
correspondingly swap which of the matched `ordInfOfPair`s / `hsupp` clauses go
where), via `divToPairRatio_swap_neg`. -/
theorem isRatioDivisor_neg (hdeg : H.f.natDegree = 5) {D : Divisor H}
    (hD : IsRatioDivisor hdeg D) : IsRatioDivisor hdeg (-D) := by
  obtain ⟨A, B, A', B', S, hAB, hA'B', hmatch, hsupp, rfl⟩ := hD
  refine ⟨A', B', A, B, S, hA'B', hAB, hmatch.symm, fun P hP => (hsupp P hP).symm, ?_⟩
  rw [divToPairRatio_swap_neg]

/-- **The genuinely new plumbing step**: `IsRatioDivisor` is closed under addition.
Given ratios `z₁ = toPair A₁ B₁ / toPair A'₁ B'₁` and `z₂ = toPair A₂ B₂ / toPair
A'₂ B'₂` with divisors `D₁, D₂`, their product `z₁ * z₂` has divisor `D₁ + D₂`
(divisor of a product is the sum of divisors — the same additivity
`ordAt_toPair_mul_of_ne_zero'` already supplies pointwise, plus
`ordInfOfPair_add_of_toPair_mul` for the matching-at-infinity condition), realized
concretely via `toPair_mul`'s explicit formula for both the new numerator
`toPair H A₁ B₁ * toPair H A₂ B₂ = toPair H (A₁A₂+B₁B₂f) (A₁B₂+A₂B₁)` and the new
denominator likewise. **No longer `sorry`'d** (an earlier draft of this docstring
called the support-combination step "left `sorry`'d" before the proof body below
was actually filled in; that note was stale and has been corrected here rather
than left to mislead a future session). The mechanical step it describes —
combining the two supports into `S₁ ∪ S₂` and re-deriving `hsupp` for the
*product* pair at every point outside that union — is carried out in full below,
via `ordAt_toPair_mul_of_ne_zero'` pointwise plus `Finset.sum_subset` to widen
each original support up to the union. Not a copy from `LPairCarrier_add_smul`
(whose common-denominator argument is scoped to the fixed two-point pole set
`{x₁,x₂}`, not the unbounded support needed here). -/
theorem isRatioDivisor_add (hdeg : H.f.natDegree = 5) {D₁ D₂ : Divisor H}
    (hD₁ : IsRatioDivisor hdeg D₁) (hD₂ : IsRatioDivisor hdeg D₂) :
    IsRatioDivisor hdeg (D₁ + D₂) := by
  obtain ⟨A₁, B₁, A₁', B₁', S₁, hAB₁, hA'B'₁, hmatch₁, hsupp₁, rfl⟩ := hD₁
  obtain ⟨A₂, B₂, A₂', B₂', S₂, hAB₂, hA'B'₂, hmatch₂, hsupp₂, rfl⟩ := hD₂
  -- Nonzero-as-`toPair` versions of the four hypotheses, used repeatedly below.
  have hAB₁ne : toPair H A₁ B₁ ≠ 0 := fun h => hAB₁ ((toPair_eq_zero_iff H A₁ B₁).mp h)
  have hAB₂ne : toPair H A₂ B₂ ≠ 0 := fun h => hAB₂ ((toPair_eq_zero_iff H A₂ B₂).mp h)
  have hA'B'₁ne : toPair H A₁' B₁' ≠ 0 := fun h => hA'B'₁ ((toPair_eq_zero_iff H A₁' B₁').mp h)
  have hA'B'₂ne : toPair H A₂' B₂' ≠ 0 := fun h => hA'B'₂ ((toPair_eq_zero_iff H A₂' B₂').mp h)
  -- The explicit product formulas, via `toPair_mul`, matching the numerator/
  -- denominator pairs `refine` below commits to.
  have hNmul : toPair H (A₁ * A₂ + B₁ * B₂ * H.f) (A₁ * B₂ + A₂ * B₁) =
      toPair H A₁ B₁ * toPair H A₂ B₂ := (toPair_mul A₁ B₁ A₂ B₂).symm
  have hDmul : toPair H (A₁' * A₂' + B₁' * B₂' * H.f) (A₁' * B₂' + A₂' * B₁') =
      toPair H A₁' B₁' * toPair H A₂' B₂' := (toPair_mul A₁' B₁' A₂' B₂').symm
  have hNne : toPair H (A₁ * A₂ + B₁ * B₂ * H.f) (A₁ * B₂ + A₂ * B₁) ≠ 0 := by
    rw [hNmul]; exact mul_ne_zero hAB₁ne hAB₂ne
  have hDne : toPair H (A₁' * A₂' + B₁' * B₂' * H.f) (A₁' * B₂' + A₂' * B₁') ≠ 0 := by
    rw [hDmul]; exact mul_ne_zero hA'B'₁ne hA'B'₂ne
  -- The `¬(A=0∧B=0)` forms of `hNne`/`hDne`, needed by `ordInfOfPair_add_of_toPair_mul`
  -- (whose `hA₃B₃` hypothesis is stated that way, not as `toPair ... ≠ 0`).
  have hNAB : ¬ (A₁ * A₂ + B₁ * B₂ * H.f = 0 ∧ A₁ * B₂ + A₂ * B₁ = 0) :=
    fun h => hNne ((toPair_eq_zero_iff H _ _).mpr h)
  have hDAB : ¬ (A₁' * A₂' + B₁' * B₂' * H.f = 0 ∧ A₁' * B₂' + A₂' * B₁' = 0) :=
    fun h => hDne ((toPair_eq_zero_iff H _ _).mpr h)
  refine ⟨A₁ * A₂ + B₁ * B₂ * H.f, A₁ * B₂ + A₂ * B₁,
    A₁' * A₂' + B₁' * B₂' * H.f, A₁' * B₂' + A₂' * B₁',
    S₁ ∪ S₂, hNAB, hDAB, ?_, ?_, ?_⟩
  · -- matching `ordInfOfPair` for the product pairs: `ordInfOfPair_add_of_toPair_mul`
    -- applied on both the numerator and denominator sides, then `hmatch₁`/`hmatch₂`
    -- combine termwise.
    haveI : IsDomain (CoordinateRing H) := IsDedekindDomain.toIsDomain
    rw [ordInfOfPair_add_of_toPair_mul hdeg A₁ B₁ A₂ B₂
          (A₁ * A₂ + B₁ * B₂ * H.f) (A₁ * B₂ + A₂ * B₁) hAB₁ hAB₂ hNAB hNmul,
        ordInfOfPair_add_of_toPair_mul hdeg A₁' B₁' A₂' B₂'
          (A₁' * A₂' + B₁' * B₂' * H.f) (A₁' * B₂' + A₂' * B₁') hA'B'₁ hA'B'₂ hDAB hDmul,
        hmatch₁, hmatch₂]
  · -- support outside `S₁ ∪ S₂`: `ordAt_toPair_mul_of_ne_zero'` pointwise, using
    -- `hsupp₁`/`hsupp₂` to get each factor's `ordAt = 0` there.
    intro P hP
    simp only [Finset.mem_union, not_or] at hP
    obtain ⟨hP1, hP2⟩ := hP
    by_cases h_bot : pointIdeal P = ⊥
    · have hz0' : ∀ (a b : k[X]), ordAt P a b = 0 := by
        intro a b
        unfold ordAt
        by_cases hab : toPair H a b = 0
        · rw [if_pos hab]
        · rw [if_neg hab, dif_pos h_bot]
      exact ⟨hz0' _ _, hz0' _ _⟩
    · refine ⟨?_, ?_⟩
      · rw [ordAt_toPair_mul_of_ne_zero' P h_bot A₁ B₁ A₂ B₂
          (A₁ * A₂ + B₁ * B₂ * H.f) (A₁ * B₂ + A₂ * B₁) hAB₁ne hAB₂ne hNmul,
          (hsupp₁ P hP1).1, (hsupp₂ P hP2).1, add_zero]
      · rw [ordAt_toPair_mul_of_ne_zero' P h_bot A₁' B₁' A₂' B₂'
          (A₁' * A₂' + B₁' * B₂' * H.f) (A₁' * B₂' + A₂' * B₁') hA'B'₁ne hA'B'₂ne hDmul,
          (hsupp₁ P hP1).2, (hsupp₂ P hP2).2, add_zero]
  · -- divisor-level identity `divToPairRatio (…product…) (S₁∪S₂) (…product…) (S₁∪S₂)
    -- = divToPairRatio A₁ B₁ S₁ A₁' B₁' S₁ + divToPairRatio A₂ B₂ S₂ A₂' B₂' S₂`:
    -- unfolds to a `Finset.sum` reindexing over `S₁ ∪ S₂` on each side plus the
    -- pointwise `ordAt` additivity above; genuinely the most bookkeeping-heavy of
    -- the five goals here.
    unfold divToPairRatio divToPair
    have hnum : ∀ P ∈ S₁ ∪ S₂, ordAt P (A₁ * A₂ + B₁ * B₂ * H.f) (A₁ * B₂ + A₂ * B₁) =
        ordAt P A₁ B₁ + ordAt P A₂ B₂ := by
      intro P _
      by_cases h_bot : pointIdeal P = ⊥
      · -- `pointIdeal P = ⊥` forces every `ordAt P _ _ = 0` unconditionally
        -- (`ordAt`'s own definition takes the `dif_pos h_bot` branch regardless of
        -- whether the underlying `toPair` is zero), for all three pairs appearing
        -- here — no case split on nonzero-ness is needed at all, unlike a generic
        -- point, since the `pointIdeal P = ⊥` branch doesn't consult `toPair`'s
        -- vanishing.
        have hz0' : ∀ (a b : k[X]), ordAt P a b = 0 := by
          intro a b
          unfold ordAt
          by_cases hab : toPair H a b = 0
          · rw [if_pos hab]
          · rw [if_neg hab, dif_pos h_bot]
        rw [hz0' (A₁ * A₂ + B₁ * B₂ * H.f) (A₁ * B₂ + A₂ * B₁), hz0' A₁ B₁, hz0' A₂ B₂,
          add_zero]
      · exact ordAt_toPair_mul_of_ne_zero' P h_bot A₁ B₁ A₂ B₂
          (A₁ * A₂ + B₁ * B₂ * H.f) (A₁ * B₂ + A₂ * B₁) hAB₁ne hAB₂ne hNmul
    have hden : ∀ P ∈ S₁ ∪ S₂, ordAt P (A₁' * A₂' + B₁' * B₂' * H.f) (A₁' * B₂' + A₂' * B₁') =
        ordAt P A₁' B₁' + ordAt P A₂' B₂' := by
      intro P _
      by_cases h_bot : pointIdeal P = ⊥
      · have hz0' : ∀ (a b : k[X]), ordAt P a b = 0 := by
          intro a b
          unfold ordAt
          by_cases hab : toPair H a b = 0
          · rw [if_pos hab]
          · rw [if_neg hab, dif_pos h_bot]
        rw [hz0' (A₁' * A₂' + B₁' * B₂' * H.f) (A₁' * B₂' + A₂' * B₁'), hz0' A₁' B₁',
          hz0' A₂' B₂', add_zero]
      · exact ordAt_toPair_mul_of_ne_zero' P h_bot A₁' B₁' A₂' B₂'
          (A₁' * A₂' + B₁' * B₂' * H.f) (A₁' * B₂' + A₂' * B₁') hA'B'₁ne hA'B'₂ne hDmul
    -- Rewrite each summand pointwise via `hnum`/`hden`, split the resulting `add`
    -- inside each `zsmul`, distribute the sums, then shrink each of the four
    -- resulting sums from `S₁ ∪ S₂` down to its own smaller support
    -- (`Finset.sum_subset`, since the added points contribute `0` per `hsupp`).
    -- Done as one flat sequence of rewrites on the goal rather than a `calc` chain,
    -- so there is no risk of an intermediate line's shape not matching what the
    -- rewrites actually produce.
    have e1 : (∑ P ∈ S₁, ordAt P A₁ B₁ • single P) =
        ∑ P ∈ S₁ ∪ S₂, ordAt P A₁ B₁ • single P :=
      Finset.sum_subset Finset.subset_union_left
        (fun P _ hP => by rw [(hsupp₁ P hP).1]; simp)
    have e2 : (∑ P ∈ S₂, ordAt P A₂ B₂ • single P) =
        ∑ P ∈ S₁ ∪ S₂, ordAt P A₂ B₂ • single P :=
      Finset.sum_subset Finset.subset_union_right
        (fun P _ hP => by rw [(hsupp₂ P hP).1]; simp)
    have e3 : (∑ P ∈ S₁, ordAt P A₁' B₁' • single P) =
        ∑ P ∈ S₁ ∪ S₂, ordAt P A₁' B₁' • single P :=
      Finset.sum_subset Finset.subset_union_left
        (fun P _ hP => by rw [(hsupp₁ P hP).2]; simp)
    have e4 : (∑ P ∈ S₂, ordAt P A₂' B₂' • single P) =
        ∑ P ∈ S₁ ∪ S₂, ordAt P A₂' B₂' • single P :=
      Finset.sum_subset Finset.subset_union_right
        (fun P _ hP => by rw [(hsupp₂ P hP).2]; simp)
    have hrw1 : (∑ P ∈ S₁ ∪ S₂, ordAt P (A₁ * A₂ + B₁ * B₂ * H.f) (A₁ * B₂ + A₂ * B₁) • single P) =
        ∑ P ∈ S₁ ∪ S₂, (ordAt P A₁ B₁ + ordAt P A₂ B₂) • single P :=
      Finset.sum_congr rfl (fun P hP => by rw [hnum P hP])
    have hrw2 : (∑ P ∈ S₁ ∪ S₂, ordAt P (A₁' * A₂' + B₁' * B₂' * H.f) (A₁' * B₂' + A₂' * B₁') • single P) =
        ∑ P ∈ S₁ ∪ S₂, (ordAt P A₁' B₁' + ordAt P A₂' B₂') • single P :=
      Finset.sum_congr rfl (fun P hP => by rw [hden P hP])
    rw [hrw1, hrw2]
    simp only [add_zsmul, Finset.sum_add_distrib]
    rw [← e1, ← e2, ← e3, ← e4]
    abel


/-- **§1's target**: every `D ∈ principalSubgroup H hdeg` is `IsRatioDivisor`.
`AddSubgroup.closure_induction` against the three cases just proved
(`isRatioDivisor_zero` for the base `AddSubgroup.closure` includes `0`
automatically via its own `one`/`zero` case, but is supplied explicitly here since
the generating set itself does not literally contain `0`), `isRatioDivisor_add` for
`add`, `isRatioDivisor_neg` for `neg`, and the generators themselves (each
`divToPairRatio A₁ B₁ S₁ A₂ B₂ S₂` with matching `ordInfOfPair`, i.e. literally an
instance of `IsRatioDivisor` with `S := S₁ ∪ S₂` after re-deriving `hsupp` for the
union — the same small support-widening argument `isRatioDivisor_add`'s `hsupp`
goals need, so not duplicated here beyond noting it recurs).

**PLAUSIBLE, not checked against a live goal**: the exact argument order/naming of
`AddSubgroup.closure_induction` in the Mathlib version this project builds against
was not confirmed (no live toolchain) — the call below assumes the standard shape
`(mem : ∀ x ∈ s, p x) (one : p 0) (mul : ∀ x y, p x → p y → p (x+y)) (inv : ∀ x, p x
→ p (-x))`; if the actual signature differs (e.g. argument order, or `Hp`-named
implicit motive requiring `induction D using AddSubgroup.closure_induction'`
instead), only this one invocation needs adjusting, not the three lemmas it
consumes. -/
theorem isRatioDivisor_of_mem_principalSubgroup (hdeg : H.f.natDegree = 5)
    {D : Divisor H} (hD : D ∈ principalSubgroup H hdeg) :
    IsRatioDivisor hdeg D := by
  rw [principalSubgroup] at hD
  refine AddSubgroup.closure_induction ?_ (isRatioDivisor_zero hdeg)
    (fun x y _ _ hx hy => isRatioDivisor_add hdeg hx hy)
    (fun x _ hx => isRatioDivisor_neg hdeg hx) hD
  rintro D ⟨A₁, B₁, S₁, hAB₁, hsupp₁, _hspec₁, _hfin₁, A₂, B₂, S₂, hAB₂, hsupp₂, _hspec₂,
    _hfin₂, hmatch, rfl⟩
  -- A generator is `divToPairRatio A₁ B₁ S₁ A₂ B₂ S₂` with possibly *different*
  -- supports `S₁ ≠ S₂`. `IsRatioDivisor` as defined above insists on one shared
  -- `S`, so widen both to `S₁ ∪ S₂` — `divToPair` over a superset agrees since the
  -- added points contribute `ordAt = 0` (`hsupp₁`/`hsupp₂` outside their own `S`).
  refine ⟨A₁, B₁, A₂, B₂, S₁ ∪ S₂, hAB₁, hAB₂, hmatch, ?_, ?_⟩
  · intro P hP
    simp only [Finset.mem_union, not_or] at hP
    exact ⟨hsupp₁ P hP.1, hsupp₂ P hP.2⟩
  · -- `divToPairRatio A₁ B₁ S₁ A₂ B₂ S₂ = divToPairRatio A₁ B₁ (S₁∪S₂) A₂ B₂ (S₁∪S₂)`:
    -- each `divToPair _ _ S` extends to `divToPair _ _ (S ∪ S')` for free since the
    -- extra terms are `ordAt P _ _ • single P` with `ordAt P _ _ = 0` (`hsupp`),
    -- i.e. `0 • single P = 0`, contributing nothing to the `Finset.sum` —
    -- `Finset.sum_subset` applied to each `divToPair` summand separately.
    -- **PLAUSIBLE, not checked against a live goal**: in particular whether `rw
    -- [(hsupp₁ P hP)]; simp` actually closes `ordAt P A₁ B₁ • single P = 0` (needs
    -- `zero_smul`, which `simp` should find, but the exact rewrite target — `ordAt
    -- P A₁ B₁` appearing under a binder inside the `Finset.sum`'s summand function
    -- — was not test-run).
    unfold divToPairRatio divToPair
    congr 1
    · exact Finset.sum_subset Finset.subset_union_left
        (fun P _ hP => by rw [(hsupp₁ P hP)]; simp)
    · exact Finset.sum_subset Finset.subset_union_right
        (fun P _ hP => by rw [(hsupp₂ P hP)]; simp)

/-! ## §3. Support matching: assembling `isOnlyEffectiveInClass_of_uniqueDegree2MapToP1`

With `IsRatioDivisor` in hand, `(x₁)+(x₂)-(x₃)-(x₄) ∈ principalSubgroup H hdeg`
gives a single ratio `z = toPair H A B / toPair H A' B'` whose divisor is exactly
`(x₁)+(x₂)-(x₃)-(x₄)`. The remaining step — reading off from this that `z` (or
`z⁻¹`) lies in `LPairCarrier x₁ x₂` so `uniqueDegree2MapToP1`/
`finrank_LPair_eq_one_of_uniqueDegree2MapToP1`'s consequence ("only constants
survive unless `x₂ = ι x₁`") pins `{x₃,x₄} = {x₁,x₂}` — needs matching the
*specific* four-point support of `divToPairRatio A B S A' B' S` against
`{x₁,x₂,x₃,x₄}` pointwise (i.e. `ordAt x₁ A B - ordAt x₁ A' B' = 1`,
`ordAt x₃ A B - ordAt x₃ A' B' = -1`, and `= 0` at every other point of `S`), via
a `Finsupp`/`Finset.sum` coefficient-extraction argument. **No longer `sorry`'d**
(an earlier draft of this docstring called the step "isolated as its own `sorry`,
distinct from and downstream of `isRatioDivisor_of_mem_principalSubgroup`" before
the proof body below was filled in; that note was stale and has been corrected
here). See `mem_LPairCarrier_of_isRatioDivisor` below for the completed proof. -/

/-- The support-matching step: given the single-ratio witness `IsRatioDivisor`
supplies for `(x₁)+(x₂)-(x₃)-(x₄)`, `z` (suitably oriented) lands in
`LPairCarrier x₁ x₂`, i.e. its zero/pole structure is bounded exactly at `x₁, x₂`
matching `IsPoleBoundedAtPair`'s clauses — read off from the divisor identity by
comparing `Finsupp` coefficients at each of the (at most four) named points and at
every other point of the witness's support `S`.

Stated in the direct (not contrapositive) shape `isOnlyEffectiveInClass_of_
uniqueDegree2MapToP1'` actually consumes: if `{x₃,x₄} ≠ {x₁,x₂}`, `z` is
non-constant — this is the direction that combines with `uniqueDegree2MapToP1`
(which forces every member of `LPairCarrier x₁ x₂` to be constant) to produce a
contradiction, rather than the earlier (equivalent, but awkward to apply forward)
phrasing via `≠ → ≠`.

**Weakened (not fabricated) to take `hreduced` explicitly, mirroring
`uniqueDegree2MapToP1_of_elementary`'s own honest weakening
(`LPairFinrankOne.lean`).** `IsRatioDivisor`'s existential (`hD`) gives no
reducedness guarantee on its witness — `hcoef` only pins the *difference*
`ordAt P A B - ordAt P A' B'` outside `{x₁,x₂,x₃,x₄}` to `0`, which is
consistent with both orders being equal and positive there (a genuine common
factor), so `hreduced` for `(A,B,A',B')` is not derivable from `hD` alone, for
the same class-group-obstruction reason documented at
`uniqueDegree2MapToP1_of_elementary`. Rather than leaving `hD`'s witness
implicit (which would make stating `hreduced` about it impossible from outside),
this theorem destructures `hD` in its own signature so the caller sees
`A, B, A', B', S` directly and can supply `hreduced` for that exact witness —
whoever discharges `isRatioDivisor_of_mem_principalSubgroup`'s output owes this
alongside it now. -/
theorem mem_LPairCarrier_of_isRatioDivisor (hdeg : H.f.natDegree = 5)
    (x₁ x₂ x₃ x₄ : H.Point) (A B A' B' : k[X]) (S : Finset H.Point)
    (hAB : ¬ (A = 0 ∧ B = 0)) (hA'B' : ¬ (A' = 0 ∧ B' = 0))
    (hmatch : ordInfOfPair A B = ordInfOfPair A' B')
    (hsupp : ∀ P, P ∉ S → ordAt P A B = 0 ∧ ordAt P A' B' = 0)
    (hdiv : (single x₁ + single x₂ - single x₃ - single x₄ : Divisor H) =
      divToPairRatio A B S A' B' S)
    (hreduced : ∀ P : H.Point, ordAt P A B = 0 ∨ ordAt P A' B' = 0)
    (hne : ({x₃, x₄} : Set H.Point) ≠ {x₁, x₂}) :
    -- **Exposes the witness pair directly** (rather than the weaker
    -- `∃ z, z ∈ LPairCarrier x₁ x₂ ∧ ...`) so the caller —
    -- `isOnlyEffectiveInClass_of_uniqueDegree2MapToP1` — can hand this exact
    -- witness straight to `uniqueDegree2MapToP1_of_elementary`, which needs
    -- `hreduced` for the specific pair, not mere carrier membership.
    -- `IsPoleBoundedAtPair x₁ x₂ C D C' D' ∧ z = polePairToFraction C D C' D'`
    -- is definitionally what `z ∈ LPairCarrier x₁ x₂` unfolds to, so nothing
    -- is lost versus the old return type. The witness pair below is
    -- `(A', B', A, B)` (numerator/denominator swapped from this theorem's own
    -- `A,B,A',B'` naming — see the `polePairToFraction` comment in the proof
    -- for why), and `hreduced` restated for that swapped pair is literally
    -- the same disjunction (`∨` is symmetric), so it transfers for free.
    ∃ (z : FractionRing (CoordinateRing H)) (C D C' D' : k[X]),
      IsPoleBoundedAtPair x₁ x₂ C D C' D' ∧
      z = polePairToFraction (H := H) C D C' D' ∧
      (∀ P : H.Point, ordAt P C D = 0 ∨ ordAt P C' D' = 0) ∧
      ¬ IsConstantFraction z := by
  have hABne : toPair H A B ≠ 0 := fun h => hAB ((toPair_eq_zero_iff H A B).mp h)
  have hA'B'ne : toPair H A' B' ≠ 0 := fun h => hA'B' ((toPair_eq_zero_iff H A' B').mp h)
  -- `divToPairRatio A B S A' B' S` evaluated at any point `P` (not just
  -- `P ∈ S`) equals `ordAt P A B - ordAt P A' B'`: for `P ∈ S` this is the
  -- `Finset.sum`'s summand directly, and for `P ∉ S` both sides are `0`
  -- (`hsupp`, resp. the sum simply omitting `P`). Hoisted to top level (rather
  -- than local to the pole-boundedness goal) since the non-constancy branch
  -- below needs it too.
  have hcoef : ∀ P : H.Point,
      ordAt P A B - ordAt P A' B' =
        (if P = x₁ then (1:ℤ) else 0) + (if P = x₂ then 1 else 0) -
          (if P = x₃ then 1 else 0) - (if P = x₄ then 1 else 0) := by
    intro P
    -- `coeffAt P (divToPair A B S)` reduces to `ordAt P A B` (when `P ∈ S`) or
    -- `0` (when `P ∉ S`, via `hsupp`) purely through the `AddMonoidHom` API
    -- (`map_sum`, `map_zsmul`, `coeffAt_single`) — never applying a `Divisor
    -- H`-typed term directly as a function, which does not typecheck (`Divisor
    -- H` is a plain, non-`abbrev` wrapper around `H.Point →₀ ℤ`; see
    -- `coeffAt`'s own docstring in `DivisorClassGroup.lean`).
    have hcoeffDivToPair : ∀ (a b : k[X]) (T : Finset H.Point),
        (∀ Q ∉ T, ordAt Q a b = 0) →
        Divisor.coeffAt P (divToPair a b T) = ordAt P a b := by
      intro a b T hT
      unfold divToPair
      rw [map_sum]
      by_cases hPT : P ∈ T
      · rw [Finset.sum_eq_single P
          (fun Q _ hQP => by
            rw [map_zsmul, Divisor.coeffAt_single, if_neg (Ne.symm hQP)]; simp)
          (fun hPT' => absurd hPT hPT')]
        rw [map_zsmul, Divisor.coeffAt_single_self]
        simp
      · rw [Finset.sum_eq_zero (fun Q hQ => by
          have hQP : Q ≠ P := fun h => hPT (h ▸ hQ)
          rw [map_zsmul, Divisor.coeffAt_single, if_neg (Ne.symm hQP)]; simp)]
        rw [hT P hPT]
    have hL : Divisor.coeffAt P (divToPairRatio A B S A' B' S) =
        ordAt P A B - ordAt P A' B' := by
      unfold divToPairRatio
      rw [map_sub, hcoeffDivToPair A B S (fun Q hQ => (hsupp Q hQ).1),
        hcoeffDivToPair A' B' S (fun Q hQ => (hsupp Q hQ).2)]
    have hR : Divisor.coeffAt P
        (single x₁ + single x₂ - single x₃ - single x₄ : Divisor H) =
        (if P = x₁ then (1:ℤ) else 0) + (if P = x₂ then 1 else 0) -
          (if P = x₃ then 1 else 0) - (if P = x₄ then 1 else 0) := by
      rw [map_sub, map_sub, map_add, Divisor.coeffAt_single, Divisor.coeffAt_single,
        Divisor.coeffAt_single, Divisor.coeffAt_single]
    rw [← hdiv, hR] at hL
    exact hL.symm
  -- `z := polePairToFraction A' B' A B`, i.e. `toPair A' B' / toPair A B`: the
  -- `(A,B)`-side witnesses the zero divisor `(x₁)+(x₂)` (it is the *positive*
  -- part of `divToPairRatio A B S A' B' S = (x₁)+(x₂)-(x₃)-(x₄)`), so it is
  -- `A, B` — not `A', B'` — that must sit in the denominator for `z`'s poles
  -- to land at `x₁, x₂` as `LPairCarrier x₁ x₂` requires.
  refine ⟨polePairToFraction A' B' A B, A', B', A, B, ?_, rfl, fun P => (hreduced P).symm, ?_⟩
  · -- `IsPoleBoundedAtPair x₁ x₂ A' B' A B`: both clauses are read off
    -- `hcoef` directly.
    refine ⟨hAB, ge_of_eq hmatch.symm, ?_⟩
    -- Pointwise pole bound, now a single `∀ P` clause (post the
    -- `IsPoleBoundedAtPair` fix in `RiemannRochGenus2.lean`, which folded
    -- the old three separate clauses — elsewhere / at `x₁` / at `x₂` — into
    -- one indicator-sum bound). The goal `ordAt P A' B' ≥ ordAt P A B -
    -- ((if P=x₁ then 1 else 0)+(if P=x₂ then 1 else 0))` is exactly `hcoef
    -- P` rearranged: `hcoef P` gives `ordAt P A B - ordAt P A' B' = (if
    -- P=x₁..) + (if P=x₂..) - (if P=x₃..) - (if P=x₄..)`, and the
    -- subtracted `x₃,x₄` indicators only help (make the RHS smaller), so
    -- `omega` closes it directly from the four resolved `ite`s. This also
    -- resolves the case `x₁ = x₂` that needed a genuine `-2` bound and was
    -- previously unprovable against the old three-clause definition — with
    -- both indicators now summing at a coincident point, the bound is
    -- exactly right.
    intro P
    have hp := hcoef P
    split_ifs at hp ⊢ <;> omega
  ·
    -- Non-constancy: if `z = toPair A' B' / toPair A B` were constant, its
    -- divisor would be `0` everywhere, forcing `{x₃,x₄} = {x₁,x₂}` via `hcoef`
    -- — contradicting `hne`.
    rintro ⟨c, hc⟩
    apply hne
    -- Unfold `polePairToFraction`/`IsConstantFraction`'s witness and rewrite
    -- `toPair H (C c) 0` as `algebraMap k[X] (CoordinateRing H) (C c)`
    -- (`toPair`'s `B = 0` case collapses to the plain `algebraMap`), matching
    -- what `hc`'s RHS already is.
    have hCc_eq : toPair H (C c) (0 : k[X]) = algebraMap k[X] (CoordinateRing H) (C c) := by
      unfold toPair; simp
    rw [polePairToFraction, ← hCc_eq] at hc
    -- Cross-multiply in the fraction field: both `algebraMap`-images below are
    -- nonzero (`hABne`, `hA'B'ne`, `IsFractionRing.injective`), so
    -- `div_eq_iff` turns the quotient equation into a product equation.
    have hABmapne : algebraMap (CoordinateRing H) (FractionRing (CoordinateRing H))
        (toPair H A B) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (CoordinateRing H)
        (FractionRing (CoordinateRing H)))).mpr hABne
    rw [div_eq_iff hABmapne] at hc
    -- Push the product equation back down from `FractionRing (CoordinateRing
    -- H)` to `CoordinateRing H` itself via injectivity of `algebraMap
    -- (CoordinateRing H) (FractionRing (CoordinateRing H))`, then further down
    -- to the explicit `toPair`-product shape `toPair_mul` supplies.
    rw [← map_mul] at hc
    have hc' : toPair H A' B' = toPair H (C c) 0 * toPair H A B :=
      IsFractionRing.injective (CoordinateRing H) (FractionRing (CoordinateRing H)) hc
    -- With `toPair H A' B' = toPair H (C c) 0 * toPair H A B`, `ordAt P A' B'
    -- = ordAt P A B` at every point `P`: `c ≠ 0` (else `toPair H A' B' = 0`,
    -- contradicting `hA'B'ne`), so `toPair H (C c) 0` is a unit (inverse
    -- `algebraMap _ _ (C c⁻¹)`, via `C c * C c⁻¹ = 1`), hence not in the
    -- maximal ideal `pointIdeal P` for any `P` — giving `ordAt P (C c) 0 = 0`
    -- via `ordAt_eq_zero_of_notMem` — and multiplicativity
    -- (`ordAt_toPair_mul_of_ne_zero'`) does the rest. The `pointIdeal P = ⊥`
    -- case is handled separately since `ordAt`'s own definition special-cases
    -- it to `0` regardless of `toPair`'s vanishing.
    have hcne : c ≠ 0 := by
      rintro rfl
      apply hA'B'ne
      have hz : toPair H (C (0:k)) (0:k[X]) = 0 := by unfold toPair; simp
      rw [hc', hz, zero_mul]
    have hCc_unit : IsUnit (algebraMap k[X] (CoordinateRing H) (C c)) := by
      have hCc_inv_poly : (C c : k[X]) * C c⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel₀ hcne, map_one]
      have hCc_inv : algebraMap k[X] (CoordinateRing H) (C c) *
          algebraMap k[X] (CoordinateRing H) (C c⁻¹) = 1 := by
        rw [← map_mul, hCc_inv_poly, map_one]
      exact ⟨⟨algebraMap k[X] (CoordinateRing H) (C c),
          algebraMap k[X] (CoordinateRing H) (C c⁻¹), hCc_inv,
          by rw [mul_comm]; exact hCc_inv⟩, rfl⟩
    have hordeq : ∀ P : H.Point, ordAt P A' B' = ordAt P A B := by
      intro P
      by_cases h_bot : pointIdeal P = ⊥
      · have hz0' : ∀ (a b : k[X]), ordAt P a b = 0 := by
          intro a b
          unfold ordAt
          by_cases hab : toPair H a b = 0
          · rw [if_pos hab]
          · rw [if_neg hab, dif_pos h_bot]
        rw [hz0', hz0']
      · have hCc0 : ordAt P (C c) (0 : k[X]) = 0 := by
          apply ordAt_eq_zero_of_notMem
          rw [hCc_eq]
          intro hmem
          exact (pointIdeal_isMaximal P).ne_top
            (Ideal.eq_top_of_isUnit_mem (pointIdeal P) hmem hCc_unit)
        have hCcne : toPair H (C c) (0 : k[X]) ≠ 0 := by
          rw [hCc_eq]; intro h; rw [h] at hCc_unit; exact not_isUnit_zero hCc_unit
        have hstep := ordAt_toPair_mul_of_ne_zero' P h_bot (C c) 0 A B A' B' hCcne hABne hc'
        rw [hstep, hCc0, zero_add]
    -- `hordeq` makes `hcoef`'s LHS vanish everywhere, so the target set
    -- equality follows pointwise: `P ∈ {x₃,x₄} ↔ P ∈ {x₁,x₂}` for every `P`,
    -- via `hcoef P` with `ordAt P A B - ordAt P A' B' = 0`.
    ext P
    have hz := hcoef P
    rw [hordeq P] at hz
    simp only [sub_self] at hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    -- Resolve each of `hz`'s four `ite`s. `split_ifs <;> first | tauto |
    -- omega`, `split_ifs <;> first | omega | (subst_vars; tauto)`, and
    -- `split_ifs <;> first | omega | simp_all` were all tried and all
    -- failed (heartbeat timeout, `whnf` timeout, and max recursion depth
    -- respectively): every one of `tauto`, `subst_vars`, and `simp_all`
    -- does some form of expensive proof search or unfolding against
    -- `H.Point` — a subtype of `k × k` cut out by `Equation`, under
    -- `open Classical` — that either blows the heartbeat budget or loops.
    -- Written fully manually instead, avoiding all of `split_ifs`, `tauto`,
    -- `subst`, and `simp_all` (and, after an argument-order slip using
    -- `iff_of_true`/`iff_of_false`/`Or.elim` directly, now via `constructor`
    -- + `intro`/`rcases` instead, which sidesteps needing to recall any of
    -- those lemmas' exact argument order): `by_cases` on each of the four
    -- equalities `P = xᵢ` (a plain decidability split, no search), rewrite
    -- `hz`'s `ite`s away with `if_pos`/`if_neg` against the case hypotheses
    -- directly (no `H.Point` unfolding), then in each of the 16 branches:
    -- 9 are arithmetically inconsistent (`hz` becomes a false numeral
    -- equation, closed by `omega`), and the remaining 7 consistent branches
    -- all close uniformly by splitting the goal `Iff` into its two
    -- implications and case-splitting the antecedent `Or`, discharging each
    -- resulting subgoal from whichever `h1,h2,h3,h4` proves or refutes it
    -- (`exact` for the true cases, `exact absurd ‹_› ‹_›` for the
    -- impossible ones the case split still generates).
    by_cases h1 : P = x₁ <;> by_cases h2 : P = x₂ <;>
      by_cases h3 : P = x₃ <;> by_cases h4 : P = x₄ <;>
      (try rw [if_pos h1] at hz) <;> (try rw [if_neg h1] at hz) <;>
      (try rw [if_pos h2] at hz) <;> (try rw [if_neg h2] at hz) <;>
      (try rw [if_pos h3] at hz) <;> (try rw [if_neg h3] at hz) <;>
      (try rw [if_pos h4] at hz) <;> (try rw [if_neg h4] at hz) <;>
      first
        | exact absurd hz (by omega)
        | (refine ⟨fun h => ?_, fun h => ?_⟩ <;>
            rcases h with h | h <;>
            first
              | exact Or.inl h1 | exact Or.inr h2
              | exact Or.inl h3 | exact Or.inr h4
              | exact absurd h h1 | exact absurd h h2
              | exact absurd h h3 | exact absurd h h4)

end HyperellipticPolynomial
