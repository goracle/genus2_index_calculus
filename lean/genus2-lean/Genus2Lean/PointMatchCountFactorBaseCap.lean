import Mathlib
import Genus2Lean.MatchCountFactorBaseBridge
import Genus2Lean.ZeroD.FixedTargetBoundCanonical
import Genus2Lean.SidonBridge
set_option linter.style.header false

/-!
# An unconditional `d = 4·B²` cap on `pointMatchCount`, for the canonical `D`
# (`ROADMAP-current.md` open item 1, sub-gap (1b) — the `d`-side, NOT via
# `decoupledSystem_degree_uniform`/`GenericPeelChainHyp`)

## Why this file exists, and why it does NOT go through `AlphaLocusDegreeUniform`

`ZeroD/MatchCountFactorBaseBridge.lean` (the most recent file in the live
proof graph) gives `matchCount (sidonSet D δ₀ F₀) Δ ≤ pointMatchCount D δ₀ F₀
Δ` — an unconditional `H.Point`-level lower bound on reachable mass, with `d`
left completely open on the `pointMatchCount` side. The obvious place to look
for `d` is `ZeroD/AlphaLocusDegreeUniform.lean`'s
`decoupledSystem_degree_uniform`, but that theorem is NOT the right tool
here, for two independent reasons:

1. It is off the live import graph entirely (confirmed by grep: nothing in
   the `matchCount`/`SolverReaches`/`pointMatchCount` chain imports
   `AlphaLocusDegreeUniform.lean`).
2. Per Claire, its `n` (in `d := p ^ n`) is a genuinely open, unpinned
   placeholder exponent — `GenericPeelChainHyp.hfinrank_le` bounds a
   0-DIMENSIONAL peel-chain quotient's `F_p`-dimension, but the peel-chain
   ideal is suspected (not yet resolved either way) to actually be
   2-dimensional as a symbolic system for a FIXED target
   `(alpha,alpha')` — i.e. Case B of the ChatGPT consult recorded in this
   pass: `alpha, alpha'` are already specialized to field elements before
   `genList` is built (`Rdec p := MvPolynomial Idx (F p)`, no `alpha`/`alpha'`
   among `Idx`), so if the ideal genuinely has height `< Idx.card` there
   for generic targets, no regular sequence of the needed length can exist
   there at all — a structural obstruction, not merely an unproved bound.
   Building `d` on top of that theorem would inherit an exponent that may
   not correspond to any real degree bound.

**What this file does instead**: bounds `pointMatchCount` directly and
elementarily, using only the ALREADY-DISCHARGED `≤ 4` fixed-target bound
(`ZeroD/FixedTargetBoundCanonical.lean`) plus a pigeonhole count over
pair-sum classes realized within a FINITE factor base `F₀` — no peel-chain,
no regular sequence, no `GenericPeelChainHyp`, no unpinned exponent.

## The key observation

`pointMatchCount D δ₀ F₀ Δ` counts quadruples `(P1,P2,P3,P4) ∈ F₀⁴` with
`s P1 + s P2 - s P3 - s P4 = Δ`. Group by the pair-sum class
`A' := s P1 + s P2`: for each `A'` actually realized by some `(P1,P2) ∈ F₀²`,
the quadruples landing on that `A'` are exactly `FixedTargetSolutions D δ₀
A' (A' - Δ)` intersected with `F₀⁴` — at most 4 by
`fixedTargetSolutions_ncard_le_four`, PROVIDED a witness pair for `A'` (and
independently for `A' - Δ`) satisfies the non-involution condition
`isOnlyEffectiveInClass_of_uniqueDegree2MapToP1_general` needs. That
condition is `nonInvolution_of_avoidsInvolutionPairs` below, free once `F₀`
satisfies `AvoidsInvolutionPairs`/`NoWeierstrassPoints` — the SAME two
hypotheses `IndexCalculusComplexityRealHitCount.lean` and
`MatchCountFactorBaseBridge.lean`'s own `sidonSet`/`F₀` setup already carry,
so this file introduces no hypothesis beyond what is already standing on
this exact factor base elsewhere in the project.

The number of pair-sum classes realized by `F₀ ×ˢ F₀` is at most `F₀.card²`
trivially (there are only that many pairs to realize them). So

    pointMatchCount D δ₀ F₀ Δ ≤ 4 · F₀.card².

## What this does NOT do

* It does not use `SidonRepBound`/`SidonDichotomy` at all — this is a
  DIFFERENT, cruder bound than `HitRateSumsetReduction.lean`'s Sidon-fed
  `overlap`/`matchCount` machinery (which bounds the ABSTRACT-group
  `matchCount`, not `pointMatchCount`), and does not need `SidonRepBound`
  because it works one level down, directly on `H.Point`-quadruples, where
  the `≤ 4` bound already does all the work `SidonRepBound` would otherwise
  be needed for.
* It does not attempt to make the bound tight — `4 · B²` is the crude
  pigeonhole count of REALIZABLE classes, not the count of classes that
  actually intersect `F₀`'s own difference set at `Δ`; a sharper bound
  (using that only `A'` with `A' - Δ` ALSO realized by `F₀²` contribute) is
  possible but not attempted here, since `4·B²` is already enough to
  instantiate `SolverReaches`'s `d`.
* It does not itself instantiate `SolverReaches F d q` — that still needs
  `q` (still fully abstract, per `IndexCalculusReachability.lean`'s own
  scoping) and a choice of `F : Finset (Jacobian H D)` (here, `sidonSet D δ₀
  F₀`) — this file supplies the `d` side of that pair, via the SOUND
  substitution `matchCount_sidonSet_le_pointMatchCount` already licenses:
  `matchCount F Δ ≤ pointMatchCount D δ₀ F₀ Δ ≤ 4·F₀.card²`, so
  `d := 4 * F₀.card ^ 2` is a valid uniform cap for `SolverReaches` at
  `F := sidonSet D δ₀ F₀`, REGARDLESS of `SolverReaches`'s own `q`.

## Verification status

Drafted without a Lean toolchain, per the working agreement — NOT `lake
build`-checked. `Finset.card_le_card_of_injOn`-style pigeonhole and
`Finset.sum_le_sum` are the only non-trivial Mathlib calls, both with
in-project precedent (`HitRateSumsetReduction.lean`,
`InvolutionPairsCount.lean`).
-/

open HyperellipticPolynomial
open Divisor
open Genus2Lean.MatchingSolutionSwapSymmetry
open Genus2Lean.MatchCountFactorBaseBridge

namespace Genus2Lean
namespace PointMatchCountFactorBaseCap

variable {k : Type*} [Field k] {H : HyperellipticPolynomial k}
variable [IsDedekindDomain (CoordinateRing H)]
variable [DecidableEq H.Point]

/-- **The non-involution fact, for free, from `AvoidsInvolutionPairs` +
`NoWeierstrassPoints`.** For ANY `x₁ x₂ ∈ F₀` (no `x₁ ≠ x₂` needed): if
`x₂ = ι x₁` then `ι x₁ ∈ F₀` (since `x₂ ∈ F₀`), so `AvoidsInvolutionPairs`
applied to `x₁` gives `x₁ = ι x₁`, contradicting `NoWeierstrassPoints x₁`.
This is the missing link `ZeroD/GaugeOrbitMatchCountBound.lean`'s own "What
remains open" paragraph flags (bounding realized pair-sum classes needs a
per-class non-involution witness) — supplied here from hypotheses already
standing on the SAME `F₀` elsewhere in the project
(`IndexCalculusComplexityRealHitCount.lean`,
`MatchCountFactorBaseBridge.lean`), not a new assumption. -/
theorem nonInvolution_of_avoidsInvolutionPairs {F₀ : Finset H.Point}
    (hAvoid : AvoidsInvolutionPairs F₀) (hNoWeier : NoWeierstrassPoints F₀)
    {x₁ x₂ : H.Point} (hx₁ : x₁ ∈ F₀) (hx₂ : x₂ ∈ F₀) :
    x₂ ≠ Point.iota x₁ := by
  intro heq
  have hιx₁_mem : Point.iota x₁ ∈ F₀ := heq ▸ hx₂
  exact hNoWeier x₁ hx₁ (hAvoid x₁ hx₁ hιx₁_mem).symm

/-- **Every pair-sum class realized within `F₀` has a genuine `≤ 4`
fixed-target bound, for the canonical `D`.** Direct instantiation of
`fixedTargetSolutions_ncard_le_four` (`MatchingSolutionSwapSymmetry.lean`)
via `isOnlyEffectiveInClass_of_uniqueDegree2MapToP1_general`, fed the
non-involution witness `nonInvolution_of_avoidsInvolutionPairs` supplies for
free. Stated directly against the two witness PAIRS `(P1,P2)`/`(P3,P4)`
rather than the classes `A B` themselves, matching
`fixedTargetSolutions_ncard_le_four`'s own hypothesis shape. -/
theorem fixedTargetSolutions_ncard_le_four_of_avoidsInvolutionPairs
    (hdeg : H.f.natDegree = 5) (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    {F₀ : Finset H.Point} (hAvoid : AvoidsInvolutionPairs F₀)
    (hNoWeier : NoWeierstrassPoints F₀)
    {δ₀ P1 P2 P3 P4 : H.Point}
    (hP1 : P1 ∈ F₀) (hP2 : P2 ∈ F₀) (hP3 : P3 ∈ F₀) (hP4 : P4 ∈ F₀) :
    (FixedTargetSolutions (principalDivisorData H hdeg) δ₀
      (s (principalDivisorData H hdeg) δ₀ P1 + s (principalDivisorData H hdeg) δ₀ P2)
      (s (principalDivisorData H hdeg) δ₀ P3 + s (principalDivisorData H hdeg) δ₀ P4)).ncard
      ≤ 4 :=
  fixedTargetSolutions_ncard_le_four
    (D := principalDivisorData H hdeg) (hdeg := hdeg) (δ₀ := δ₀)
    (Genus2Lean.DecoupledSystem.principalDivisorData_P_le_principalSubgroup hdeg)
    (isOnlyEffectiveInClass_of_uniqueDegree2MapToP1_general hdeg hchar hsf P1 P2
      (nonInvolution_of_avoidsInvolutionPairs hAvoid hNoWeier hP1 hP2))
    (isOnlyEffectiveInClass_of_uniqueDegree2MapToP1_general hdeg hchar hsf P3 P4
      (nonInvolution_of_avoidsInvolutionPairs hAvoid hNoWeier hP3 hP4))
    _ _ rfl rfl

/-- **The pigeonhole step: `pointMatchCount`'s quadruples, grouped by a fixed
`(P1,P2)`, have a `≤ 4`-element fiber over `(P3,P4) ∈ F₀ ×ˢ F₀`.** Fixing
`(P1,P2)` fixes the target pair-sum `A' := s P1 + s P2`, so
`{(P3,P4) ∈ F₀² : s P1 + s P2 - s P3 - s P4 = Δ}` is exactly
`{(P3,P4) ∈ F₀² : s P3 + s P4 = A' - Δ}`
(pure group rearrangement, `hrw` below), which is
`(FixedTargetSolutions D δ₀ A' (A' - Δ) ∩ ↑(F₀ ×ˢ F₀))` read as a `Finset`
— a subset of `FixedTargetSolutions D δ₀ A' (A' - Δ)` as a `Set`, itself
bounded by 4 via `fixedTargetSolutions_ncard_le_four_of_avoidsInvolutionPairs`
(taking `P1,P2` as `A'`'s own witness pair). -/
theorem pointMatchCount_fiber_le_four
    (hdeg : H.f.natDegree = 5)
    [DecidableEq (Jacobian H (principalDivisorData H hdeg))]
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    {F₀ : Finset H.Point} (hAvoid : AvoidsInvolutionPairs F₀)
    (hNoWeier : NoWeierstrassPoints F₀)
    (δ₀ : H.Point) (Δ : Jacobian H (principalDivisorData H hdeg))
    (P1 P2 : H.Point) (hP1 : P1 ∈ F₀) (hP2 : P2 ∈ F₀) :
    ((F₀ ×ˢ F₀).filter (fun q : H.Point × H.Point =>
        s (principalDivisorData H hdeg) δ₀ P1 + s (principalDivisorData H hdeg) δ₀ P2
          - s (principalDivisorData H hdeg) δ₀ q.1 - s (principalDivisorData H hdeg) δ₀ q.2
          = Δ)).card ≤ 4 := by
  classical
  -- No `set` for `D`/`A'` here — deliberately: folding through `.filter`'s
  -- bound-variable predicate proved fragile (the goal's own display after
  -- `set` did not reliably match what later `rw`s expected). Work with
  -- `principalDivisorData H hdeg` spelled out throughout instead, and
  -- transport the whole bound through a single explicit `Finset.card_le_card`
  -- off a proven subset, rather than rewriting the goal's filter predicate.
  have hrw : ∀ q : H.Point × H.Point,
      (s (principalDivisorData H hdeg) δ₀ P1 + s (principalDivisorData H hdeg) δ₀ P2
        - s (principalDivisorData H hdeg) δ₀ q.1 - s (principalDivisorData H hdeg) δ₀ q.2 = Δ) ↔
        (s (principalDivisorData H hdeg) δ₀ q.1 + s (principalDivisorData H hdeg) δ₀ q.2
          = s (principalDivisorData H hdeg) δ₀ P1 + s (principalDivisorData H hdeg) δ₀ P2 - Δ) := by
    intro q
    -- Reduces to `sub_eq_zero`-in-both-directions off a single generic
    -- abelian-group identity (`hgen`), proved once and instantiated twice,
    -- rather than rewriting `Δ` into the goal (which risks a motive error
    -- via dependent occurrences elsewhere). `hgen` is `abel`-closable with
    -- no named Mathlib group lemma needed beyond `sub_eq_zero`.
    have hgen : ∀ a b c d : Jacobian H (principalDivisorData H hdeg),
        a - b - c - d = -((b + c) - (a - d)) := by
      intros; abel
    have hkey := hgen
      (s (principalDivisorData H hdeg) δ₀ P1 + s (principalDivisorData H hdeg) δ₀ P2)
      (s (principalDivisorData H hdeg) δ₀ q.1) (s (principalDivisorData H hdeg) δ₀ q.2) Δ
    constructor
    · intro h
      have h0 : s (principalDivisorData H hdeg) δ₀ P1 + s (principalDivisorData H hdeg) δ₀ P2
          - s (principalDivisorData H hdeg) δ₀ q.1 - s (principalDivisorData H hdeg) δ₀ q.2 - Δ
          = 0 := by rw [h]; abel
      rw [hkey, neg_eq_zero, sub_eq_zero] at h0
      exact h0
    · intro h
      have h0 : s (principalDivisorData H hdeg) δ₀ q.1 + s (principalDivisorData H hdeg) δ₀ q.2
          - (s (principalDivisorData H hdeg) δ₀ P1 + s (principalDivisorData H hdeg) δ₀ P2 - Δ)
          = 0 := by rw [h]; abel
      have h0' : s (principalDivisorData H hdeg) δ₀ P1 + s (principalDivisorData H hdeg) δ₀ P2
          - s (principalDivisorData H hdeg) δ₀ q.1 - s (principalDivisorData H hdeg) δ₀ q.2 - Δ
          = 0 := by rw [hkey, neg_eq_zero]; exact h0
      rw [sub_eq_zero] at h0'
      exact h0'
  have hmapsto : ∀ q ∈ (F₀ ×ˢ F₀).filter (fun q : H.Point × H.Point =>
        s (principalDivisorData H hdeg) δ₀ P1 + s (principalDivisorData H hdeg) δ₀ P2
          - s (principalDivisorData H hdeg) δ₀ q.1 - s (principalDivisorData H hdeg) δ₀ q.2
          = Δ),
      (P1, P2, q.1, q.2) ∈ FixedTargetSolutions (principalDivisorData H hdeg) δ₀
          (s (principalDivisorData H hdeg) δ₀ P1 + s (principalDivisorData H hdeg) δ₀ P2)
          (s (principalDivisorData H hdeg) δ₀ P1 + s (principalDivisorData H hdeg) δ₀ P2 - Δ) := by
    intro q hq
    rw [Finset.mem_filter] at hq
    exact ⟨rfl, (hrw q).mp hq.2⟩
  have hinj : Set.InjOn (fun q : H.Point × H.Point => (P1, P2, q.1, q.2))
      ((F₀ ×ˢ F₀).filter (fun q : H.Point × H.Point =>
        s (principalDivisorData H hdeg) δ₀ P1 + s (principalDivisorData H hdeg) δ₀ P2
          - s (principalDivisorData H hdeg) δ₀ q.1 - s (principalDivisorData H hdeg) δ₀ q.2
          = Δ) : Finset (H.Point × H.Point)) := by
    rintro ⟨q1, q2⟩ _ ⟨q1', q2'⟩ _ heq
    have hq1 : q1 = q1' := congrArg (fun p => p.2.2.1) heq
    have hq2 : q2 = q2' := congrArg (fun p => p.2.2.2) heq
    exact Prod.ext hq1 hq2
  -- `fixedTargetSolutions_ncard_le_four_of_avoidsInvolutionPairs` needs an
  -- actual witness PAIR `(P3,P4) ∈ F₀²` summing to `A' - Δ` (here spelled
  -- out) to invoke the `≤ 4` bound. Case-split directly on whether the
  -- `Finset` we actually need to bound is empty, rather than trying to
  -- route an empty case through the `Set.ncard` bound above (which needs
  -- the same witness and so cannot supply one when none exists).
  rcases Finset.eq_empty_or_nonempty ((F₀ ×ˢ F₀).filter (fun q : H.Point × H.Point =>
      s (principalDivisorData H hdeg) δ₀ P1 + s (principalDivisorData H hdeg) δ₀ P2
        - s (principalDivisorData H hdeg) δ₀ q.1 - s (principalDivisorData H hdeg) δ₀ q.2
        = Δ)) with hempty | ⟨⟨P3, P4⟩, hP34mem⟩
  · rw [hempty]; simp
  · have hP34mem' := hP34mem
    rw [Finset.mem_filter] at hP34mem'
    have hP34 := hP34mem'.2
    rw [Finset.mem_filter, Finset.mem_product] at hP34mem
    obtain ⟨⟨hP3, hP4⟩, -⟩ := hP34mem
    have hncard : ((F₀ ×ˢ F₀).filter (fun q : H.Point × H.Point =>
          s (principalDivisorData H hdeg) δ₀ P1 + s (principalDivisorData H hdeg) δ₀ P2
            - s (principalDivisorData H hdeg) δ₀ q.1 - s (principalDivisorData H hdeg) δ₀ q.2
            = Δ)).card ≤
        (FixedTargetSolutions (principalDivisorData H hdeg) δ₀
          (s (principalDivisorData H hdeg) δ₀ P1 + s (principalDivisorData H hdeg) δ₀ P2)
          (s (principalDivisorData H hdeg) δ₀ P1 + s (principalDivisorData H hdeg) δ₀ P2 - Δ)).ncard := by
      -- `Set.toFinite` cannot discharge finiteness here: there is no
      -- `Finite H.Point` instance project-wide (see
      -- `MatchingSolutionSwapSymmetry.lean`'s `swapImages_finite`
      -- docstring). Instead, get finiteness the same way that file's
      -- own `fixedTargetSolutions_ncard_le_four` does internally:
      -- `FixedTargetSolutions` embeds in the concretely-finite
      -- `swapImages P1 P2 P3 P4`, using `(P1,P2)`/`(P3,P4)` as the
      -- witness pairs for the two fixed classes `A'`/`A' - Δ`.
      have hsub_swap : FixedTargetSolutions (principalDivisorData H hdeg) δ₀
          (s (principalDivisorData H hdeg) δ₀ P1 + s (principalDivisorData H hdeg) δ₀ P2)
          (s (principalDivisorData H hdeg) δ₀ P1 + s (principalDivisorData H hdeg) δ₀ P2 - Δ)
          ⊆ swapImages P1 P2 P3 P4 := by
        rintro ⟨P1', P2', P3', P4'⟩ ⟨h1, h2⟩
        have heq12 : s (principalDivisorData H hdeg) δ₀ P1 + s (principalDivisorData H hdeg) δ₀ P2
            = s (principalDivisorData H hdeg) δ₀ P1' + s (principalDivisorData H hdeg) δ₀ P2' :=
          h1.symm
        have hP34' : s (principalDivisorData H hdeg) δ₀ P3 + s (principalDivisorData H hdeg) δ₀ P4
            = s (principalDivisorData H hdeg) δ₀ P1 + s (principalDivisorData H hdeg) δ₀ P2 - Δ := by
          have h0 : s (principalDivisorData H hdeg) δ₀ P1 + s (principalDivisorData H hdeg) δ₀ P2
              - Δ - (s (principalDivisorData H hdeg) δ₀ P3 + s (principalDivisorData H hdeg) δ₀ P4)
              = 0 := by rw [← hP34]; abel
          rw [sub_eq_zero] at h0
          exact h0.symm
        have heq34 : s (principalDivisorData H hdeg) δ₀ P3 + s (principalDivisorData H hdeg) δ₀ P4
            = s (principalDivisorData H hdeg) δ₀ P3' + s (principalDivisorData H hdeg) δ₀ P4' :=
          hP34'.trans h2.symm
        have hiff12 := (s_add_s_eq_s_add_s_iff (principalDivisorData H hdeg) δ₀ P1 P2 P1' P2').mp heq12
        have hiff34 := (s_add_s_eq_s_add_s_iff (principalDivisorData H hdeg) δ₀ P3 P4 P3' P4').mp heq34
        have hmem12 : (single P1 + single P2 - single P1' - single P2' : Divisor H) ∈
            principalSubgroup H hdeg :=
          Genus2Lean.DecoupledSystem.principalDivisorData_P_le_principalSubgroup hdeg hiff12
        have hmem34 : (single P3 + single P4 - single P3' - single P4' : Divisor H) ∈
            principalSubgroup H hdeg :=
          Genus2Lean.DecoupledSystem.principalDivisorData_P_le_principalSubgroup hdeg hiff34
        have hset12 : ({P1', P2'} : Set H.Point) = {P1, P2} :=
          isOnlyEffectiveInClass_of_uniqueDegree2MapToP1_general hdeg hchar hsf P1 P2
            (nonInvolution_of_avoidsInvolutionPairs hAvoid hNoWeier hP1 hP2) P1' P2' hmem12
        have hset34 : ({P3', P4'} : Set H.Point) = {P3, P4} :=
          isOnlyEffectiveInClass_of_uniqueDegree2MapToP1_general hdeg hchar hsf P3 P4
            (nonInvolution_of_avoidsInvolutionPairs hAvoid hNoWeier hP3 hP4) P3' P4' hmem34
        have hcase12 := pair_eq_pair_cases hset12
        have hcase34 := pair_eq_pair_cases hset34
        simp only [swapImages, Set.mem_insert_iff, Set.mem_singleton_iff]
        rcases hcase12 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases hcase34 with ⟨e3, e4⟩ | ⟨e3, e4⟩
        · exact Or.inl (by rw [e1, e2, e3, e4])
        · exact Or.inr (Or.inr (Or.inl (by rw [e1, e2, e3, e4])))
        · exact Or.inr (Or.inl (by rw [e1, e2, e3, e4]))
        · exact Or.inr (Or.inr (Or.inr (by rw [e1, e2, e3, e4])))
      have hfin : (FixedTargetSolutions (principalDivisorData H hdeg) δ₀
          (s (principalDivisorData H hdeg) δ₀ P1 + s (principalDivisorData H hdeg) δ₀ P2)
          (s (principalDivisorData H hdeg) δ₀ P1 + s (principalDivisorData H hdeg) δ₀ P2 - Δ)).Finite :=
        (swapImages_finite P1 P2 P3 P4).subset hsub_swap
      have hsub' : (↑(((F₀ ×ˢ F₀).filter (fun q : H.Point × H.Point =>
            s (principalDivisorData H hdeg) δ₀ P1 + s (principalDivisorData H hdeg) δ₀ P2
              - s (principalDivisorData H hdeg) δ₀ q.1 - s (principalDivisorData H hdeg) δ₀ q.2
              = Δ)).image (fun q : H.Point × H.Point => (P1, P2, q.1, q.2)) :
          Finset (H.Point × H.Point × H.Point × H.Point)) : Set (H.Point × H.Point × H.Point × H.Point))
          ⊆ FixedTargetSolutions (principalDivisorData H hdeg) δ₀
            (s (principalDivisorData H hdeg) δ₀ P1 + s (principalDivisorData H hdeg) δ₀ P2)
            (s (principalDivisorData H hdeg) δ₀ P1 + s (principalDivisorData H hdeg) δ₀ P2 - Δ) := by
        intro x hx
        simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
        obtain ⟨q, hq, rfl⟩ := hx
        exact hmapsto q hq
      calc ((F₀ ×ˢ F₀).filter (fun q : H.Point × H.Point =>
            s (principalDivisorData H hdeg) δ₀ P1 + s (principalDivisorData H hdeg) δ₀ P2
              - s (principalDivisorData H hdeg) δ₀ q.1 - s (principalDivisorData H hdeg) δ₀ q.2
              = Δ)).card
          = (((F₀ ×ˢ F₀).filter (fun q : H.Point × H.Point =>
              s (principalDivisorData H hdeg) δ₀ P1 + s (principalDivisorData H hdeg) δ₀ P2
                - s (principalDivisorData H hdeg) δ₀ q.1 - s (principalDivisorData H hdeg) δ₀ q.2
                = Δ)).image (fun q : H.Point × H.Point => (P1, P2, q.1, q.2))).card :=
            (Finset.card_image_of_injOn hinj).symm
        _ = (↑(((F₀ ×ˢ F₀).filter (fun q : H.Point × H.Point =>
              s (principalDivisorData H hdeg) δ₀ P1 + s (principalDivisorData H hdeg) δ₀ P2
                - s (principalDivisorData H hdeg) δ₀ q.1 - s (principalDivisorData H hdeg) δ₀ q.2
                = Δ)).image (fun q : H.Point × H.Point => (P1, P2, q.1, q.2)) :
              Finset (H.Point × H.Point × H.Point × H.Point)) : Set _).ncard :=
            (Set.ncard_coe_finset _).symm
        _ ≤ _ := Set.ncard_le_ncard hsub' hfin
    refine le_trans hncard ?_
    -- Avoid `rw [← hP34]` + `exact` here: that rewrites `Δ` into the raw
    -- 4-term expression `s P1+s P2-s P3-s P4`, leaving the goal's second
    -- `FixedTargetSolutions` argument as `A' - (s P1+s P2-s P3-s P4)`
    -- rather than the lemma's expected `s P3 + s P4` — syntactically
    -- different, group-theoretically equal only via `abel`-level
    -- reasoning, which sent `exact`'s unifier into a `whnf` timeout
    -- trying to close the gap by unfolding definitions instead. Prove
    -- the needed equality explicitly first (same `sub_eq_zero` pattern
    -- as `hP34'` above), then `rw` that exact equality so the final
    -- `exact` is a syntactic match.
    have hAminusΔ : s (principalDivisorData H hdeg) δ₀ P1 + s (principalDivisorData H hdeg) δ₀ P2 - Δ
        = s (principalDivisorData H hdeg) δ₀ P3 + s (principalDivisorData H hdeg) δ₀ P4 := by
      have h0 : s (principalDivisorData H hdeg) δ₀ P1 + s (principalDivisorData H hdeg) δ₀ P2 - Δ
          - (s (principalDivisorData H hdeg) δ₀ P3 + s (principalDivisorData H hdeg) δ₀ P4) = 0 := by
        rw [← hP34]; abel
      rw [sub_eq_zero] at h0
      exact h0
    rw [hAminusΔ]
    exact fixedTargetSolutions_ncard_le_four_of_avoidsInvolutionPairs
      hdeg hchar hsf hAvoid hNoWeier hP1 hP2 hP3 hP4

/-- **The main bound.** `pointMatchCount D δ₀ F₀ Δ ≤ 4 · F₀.card²`,
unconditionally in `Δ`, for `D := principalDivisorData H hdeg`, given only
`hchar`, `hsf`, and `F₀` satisfying `AvoidsInvolutionPairs`/
`NoWeierstrassPoints` (the standing hypotheses this exact `F₀` already
carries in `IndexCalculusComplexityRealHitCount.lean`). No peel-chain, no
`GenericPeelChainHyp`, no `decoupledSystem_degree_uniform` — see the module
docstring for why that theorem is the wrong tool here.

Proof: group `pointMatchCount`'s counted quadruples by their first pair
`(P1,P2)` (`Finset.card_eq_sum_card_fiberwise` over `F₀ ×ˢ F₀`, reindexing
the nested-tuple `Finset` `F₀ ×ˢ F₀ ×ˢ F₀ ×ˢ F₀` via the obvious
`H.Point × H.Point × H.Point × H.Point ≃ (H.Point × H.Point) × (H.Point ×
H.Point)` grouping), then bound each of the `F₀.card²` fibers by 4 via
`pointMatchCount_fiber_le_four`. -/
theorem pointMatchCount_le_four_mul_card_sq
    (hdeg : H.f.natDegree = 5) (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    {F₀ : Finset H.Point} (hAvoid : AvoidsInvolutionPairs F₀)
    (hNoWeier : NoWeierstrassPoints F₀)
    [Fintype (Jacobian H (principalDivisorData H hdeg))]
    [DecidableEq (Jacobian H (principalDivisorData H hdeg))]
    (δ₀ : H.Point) (Δ : Jacobian H (principalDivisorData H hdeg)) :
    pointMatchCount (principalDivisorData H hdeg) δ₀ F₀ Δ ≤ 4 * F₀.card ^ 2 := by
  classical
  -- No `set` for `D` here — deliberately, same reason
  -- `pointMatchCount_fiber_le_four` avoids it: `set` rewriting
  -- `principalDivisorData H hdeg` inside `Δ`'s own TYPE (not just its
  -- value) desyncs the local `Δ` from the goal's `Δ`, silently producing
  -- an inaccessible `Δ✝` that later `rw`s can no longer find. Spell
  -- `principalDivisorData H hdeg` out everywhere instead.
  -- Reindex `F₀ ×ˢ F₀ ×ˢ F₀ ×ˢ F₀` (nested tuples) as `(F₀ ×ˢ F₀) ×ˢ
  -- (F₀ ×ˢ F₀)` via an explicit two-sided bijection between the two
  -- filtered `Finset`s, so the count can be grouped by its first factor
  -- with `Finset.card_eq_sum_card_fiberwise`. Uses `Finset.card_bij'`
  -- directly (explicit forward/backward maps, `rfl` gluing obligations)
  -- rather than routing through `Finset.filter_image`/`card_image_of_injOn`,
  -- which needs a defeq the nested-tuple projections don't hand over for
  -- free.
  have hcard_eq : pointMatchCount (principalDivisorData H hdeg) δ₀ F₀ Δ =
      (((F₀ ×ˢ F₀) ×ˢ (F₀ ×ˢ F₀)).filter
        (fun r : (H.Point × H.Point) × (H.Point × H.Point) =>
          s (principalDivisorData H hdeg) δ₀ r.1.1 + s (principalDivisorData H hdeg) δ₀ r.1.2
            - s (principalDivisorData H hdeg) δ₀ r.2.1 - s (principalDivisorData H hdeg) δ₀ r.2.2
            = Δ)).card := by
    unfold pointMatchCount
    refine Finset.card_bij'
      (fun p _ => ((p.1, p.2.1), (p.2.2.1, p.2.2.2)))
      (fun r _ => (r.1.1, r.1.2, r.2.1, r.2.2))
      ?_ ?_ ?_ ?_
    · rintro ⟨p1, p2, p3, p4⟩ hp
      simp only [Finset.mem_filter, Finset.mem_product] at hp ⊢
      exact ⟨⟨⟨hp.1.1, hp.1.2.1⟩, ⟨hp.1.2.2.1, hp.1.2.2.2⟩⟩, hp.2⟩
    · rintro ⟨⟨r1, r2⟩, ⟨r3, r4⟩⟩ hr
      simp only [Finset.mem_filter, Finset.mem_product] at hr ⊢
      exact ⟨⟨hr.1.1.1, hr.1.1.2, hr.1.2.1, hr.1.2.2⟩, hr.2⟩
    · rintro ⟨p1, p2, p3, p4⟩ _
      rfl
    · rintro ⟨⟨r1, r2⟩, ⟨r3, r4⟩⟩ _
      rfl
  rw [hcard_eq]
  -- Group by the first coordinate `r.1 ∈ F₀ ×ˢ F₀`; each fiber over
  -- `(P1,P2)` is exactly `pointMatchCount_fiber_le_four`'s `(F₀ ×ˢ
  -- F₀).filter (...)`, bounded by 4.
  have hfiber_eq : ∀ (p1p2 : H.Point × H.Point), p1p2 ∈ F₀ ×ˢ F₀ →
      (((F₀ ×ˢ F₀) ×ˢ (F₀ ×ˢ F₀)).filter
        (fun r : (H.Point × H.Point) × (H.Point × H.Point) =>
          s (principalDivisorData H hdeg) δ₀ r.1.1 + s (principalDivisorData H hdeg) δ₀ r.1.2
            - s (principalDivisorData H hdeg) δ₀ r.2.1 - s (principalDivisorData H hdeg) δ₀ r.2.2
            = Δ)
        |>.filter (fun r => r.1 = p1p2)).card ≤ 4 := by
    intro p1p2 hp1p2
    rw [Finset.mem_product] at hp1p2
    -- Explicit two-sided inverse (`Finset.card_bij'`, not the one-sided
    -- `Finset.card_bij`) between the two filters: `r ↦ r.2` forward,
    -- `q ↦ (p1p2, q)` backward. Chosen over `card_bij` specifically because
    -- its `left_inv`/`right_inv` obligations are literal `rfl`s once the
    -- membership conditions are unpacked, with no `Prod.ext`-style
    -- casing needed — safer to get right without a REPL.
    have hcongr : (((F₀ ×ˢ F₀) ×ˢ (F₀ ×ˢ F₀)).filter
        (fun r : (H.Point × H.Point) × (H.Point × H.Point) =>
          s (principalDivisorData H hdeg) δ₀ r.1.1 + s (principalDivisorData H hdeg) δ₀ r.1.2
            - s (principalDivisorData H hdeg) δ₀ r.2.1 - s (principalDivisorData H hdeg) δ₀ r.2.2
            = Δ)
        |>.filter (fun r => r.1 = p1p2)).card =
      ((F₀ ×ˢ F₀).filter (fun q : H.Point × H.Point =>
        s (principalDivisorData H hdeg) δ₀ p1p2.1 + s (principalDivisorData H hdeg) δ₀ p1p2.2
          - s (principalDivisorData H hdeg) δ₀ q.1 - s (principalDivisorData H hdeg) δ₀ q.2
          = Δ)).card := by
      refine Finset.card_bij' (fun r _ => r.2) (fun q _ => (p1p2, q)) ?_ ?_ ?_ ?_
      · rintro ⟨r1, r2⟩ hr
        rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_product] at hr
        obtain ⟨⟨⟨hr1mem, hr2mem⟩, hreq⟩, hr1eq⟩ := hr
        -- `hr1eq : (r1, r2).1 = p1p2`, i.e. `r1 = p1p2`; `hreq` is the
        -- sum-equation at `(r1,r2)`. Goal: `r2 ∈ (F₀×ˢF₀).filter (fun q
        -- => s p1p2.1 + s p1p2.2 - s q.1 - s q.2 = Δ)`.
        rw [Finset.mem_filter]
        refine ⟨hr2mem, ?_⟩
        rw [← hr1eq]
        exact hreq
      · rintro q hq
        rw [Finset.mem_filter] at hq
        obtain ⟨hqmem, hqeq⟩ := hq
        rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_product]
        refine ⟨⟨⟨Finset.mem_product.mpr hp1p2, hqmem⟩, ?_⟩, rfl⟩
        exact hqeq
      · rintro ⟨r1, r2⟩ hr
        rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_product] at hr
        have hr1eq : r1 = p1p2 := hr.2
        exact Prod.ext hr1eq.symm rfl
      · rintro q hq
        rfl
    rw [hcongr]
    exact pointMatchCount_fiber_le_four hdeg hchar hsf hAvoid hNoWeier δ₀ Δ
      p1p2.1 p1p2.2 hp1p2.1 hp1p2.2
  calc (((F₀ ×ˢ F₀) ×ˢ (F₀ ×ˢ F₀)).filter
        (fun r : (H.Point × H.Point) × (H.Point × H.Point) =>
          s (principalDivisorData H hdeg) δ₀ r.1.1 + s (principalDivisorData H hdeg) δ₀ r.1.2
            - s (principalDivisorData H hdeg) δ₀ r.2.1 - s (principalDivisorData H hdeg) δ₀ r.2.2
            = Δ)).card
      = ∑ p1p2 ∈ F₀ ×ˢ F₀,
          (((F₀ ×ˢ F₀) ×ˢ (F₀ ×ˢ F₀)).filter
            (fun r : (H.Point × H.Point) × (H.Point × H.Point) =>
              s (principalDivisorData H hdeg) δ₀ r.1.1 + s (principalDivisorData H hdeg) δ₀ r.1.2
                - s (principalDivisorData H hdeg) δ₀ r.2.1 - s (principalDivisorData H hdeg) δ₀ r.2.2
                = Δ)
            |>.filter (fun r => r.1 = p1p2)).card := by
        rw [Finset.card_eq_sum_card_fiberwise
          (f := fun r : (H.Point × H.Point) × (H.Point × H.Point) => r.1)
          (t := F₀ ×ˢ F₀)]
        intro r hr
        simp only [Finset.mem_coe] at hr ⊢
        rw [Finset.mem_filter, Finset.mem_product] at hr
        exact hr.1.1
    _ ≤ ∑ _p1p2 ∈ F₀ ×ˢ F₀, 4 := Finset.sum_le_sum hfiber_eq
    _ = (F₀ ×ˢ F₀).card * 4 := by rw [Finset.sum_const, smul_eq_mul]
    _ = 4 * F₀.card ^ 2 := by rw [Finset.card_product, sq]; ring

end PointMatchCountFactorBaseCap
end Genus2Lean
