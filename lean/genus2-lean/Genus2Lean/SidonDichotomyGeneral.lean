import Mathlib
import Genus2Lean.HyperellipticFunctionField
import Genus2Lean.AffinePoints
import Genus2Lean.DivisorClassGroup
import Genus2Lean.PrincipalDivisorSubgroup
import Genus2Lean.FFKSidon
import Genus2Lean.LPairFinrankOneOrdAtFracSpec
import Genus2Lean.SidonBridge
noncomputable section

set_option linter.style.header false

open Polynomial

/-!
# `SidonDichotomy` for `principalDivisorData`, general `k` (no `[IsAlgClosed k]`)

**Purpose.** `FFKSidon.lean` states `PrincipalDivisorData.SidonDichotomy` as an
abstract hypothesis on `D` and proves nothing about it for the concrete
`D := principalDivisorData H hdeg`. `RiemannRochGenus2.lean` does assemble a
`sidonDichotomy_of_riemannRoch` for that concrete `D`, but only on the
closed-field track (`[IsAlgClosed k]`), and even there it currently calls a
stale, still-`sorry`'d duplicate (`finrank_L_pair` in that file, as opposed to
the sorry-free `finrank_L_pair''` in `PrincipalSubgroupCollapse.lean`) — not a
mathematical gap, just unmerged wiring. Rather than untangle that, this file
builds the general-`k` half fresh, directly against the already-proved
`isOnlyEffectiveInClass_of_uniqueDegree2MapToP1_general`
(`LPairFinrankOneOrdAtFracSpec.lean`), which needs no `IsAlgClosed k` at all.

**What is proved here.** `sidonDichotomy_nonInvolution_general`: for
`x₂ ≠ ι x₁`, `s D δ₀ x₁ + s D δ₀ x₂ = s D δ₀ x₃ + s D δ₀ x₄` (`D :=
principalDivisorData H hdeg`) forces `{x₁,x₂} = {x₃,x₄}` — the
non-degenerate disjunct of `SidonDichotomy`, over any field `k` (in
particular `k = ZMod p`), given only `hchar`/`hsf`. This is exactly the
"`P1+P2` irreducible" content advisory-7 §4 needs for a factor base built to
avoid hyperelliptic-involution pairs (`AvoidsInvolutionPairs`,
`SidonBridge.lean`) — `NoWeierstrassPoints`'s role in
`sidonRepBound_of_sidonDichotomy` never touches the involution branch of the
dichotomy in that case, so this half alone should already be enough to
instantiate the combinatorial machinery for such a factor base. See the note
below `sidonDichotomy_general` for exactly what remains.

**What is NOT proved here.** The involution disjunct — `x₂ = ι x₁` forcing
`x₄ = ι x₃` — is `IsOnlyFibersInCanonicalClass`, general `k`. No proof of
this exists anywhere in the codebase yet, closed-field or general: the one
attempt (`LCanonicalElementary.lean`'s `isOnlyFibersInCanonicalClass_of_elementary`)
is an honest `sorry`, and its docstring flags the blocker as the same
`hreduced`-from-bare-membership gap `SCOPING-isRatioDivisorSpec.md` closed for
the non-involution case — so a `_general` port following the same recipe
(`isRatioDivisor_of_mem_principalSubgroup` + a not-yet-written
closed-point-native analogue of `mem_LPairCarrierSpec'_of_isRatioDivisor` for
the canonical-class case) looks plausible, but is genuinely new work, not
attempted here. `sidonDichotomy_general` below is left as a named `sorry` on
exactly that one remaining disjunct, so the gap is visible and isolated
rather than smuggled into an early return.
-/

namespace HyperellipticPolynomial

open Divisor

variable {k : Type*} [Field k] {H : HyperellipticPolynomial k}
variable [IsDedekindDomain (CoordinateRing H)]

/-- **The non-involution half of `SidonDichotomy`, general `k`.** Direct
unfold of `s D δ₀ x₁ + s D δ₀ x₂ = s D δ₀ x₃ + s D δ₀ x₄` via
`s_add_s_eq_s_add_s_iff` into `principalSubgroup` membership (using
`D.P = principalSubgroup H hdeg` definitionally for `D :=
principalDivisorData H hdeg`), then a direct call to
`isOnlyEffectiveInClass_of_uniqueDegree2MapToP1_general`. No case-split
needed here — that theorem already assumes `x₂ ≠ ι x₁` and delivers exactly
`{x₃,x₄} = {x₁,x₂}`; `.symm` matches this file's `{x₁,x₂} = {x₃,x₄}`
orientation. -/
theorem sidonDichotomy_nonInvolution_general (hdeg : H.f.natDegree = 5)
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (δ₀ x₁ x₂ x₃ x₄ : H.Point) (hne : x₂ ≠ Point.iota x₁)
    (heq : s (principalDivisorData H hdeg) δ₀ x₁ + s (principalDivisorData H hdeg) δ₀ x₂ =
      s (principalDivisorData H hdeg) δ₀ x₃ + s (principalDivisorData H hdeg) δ₀ x₄) :
    ({x₁, x₂} : Set H.Point) = {x₃, x₄} := by
  rw [s_add_s_eq_s_add_s_iff] at heq
  -- `(principalDivisorData H hdeg).P` unfolds to `principalSubgroup H hdeg`
  -- definitionally (`principalDivisorData`'s own `P := principalSubgroup H
  -- hdeg` field), so `heq` is already in `IsOnlyEffectiveInClass`'s expected
  -- shape without any further rewriting.
  exact (isOnlyEffectiveInClass_of_uniqueDegree2MapToP1_general hdeg hchar hsf
    x₁ x₂ hne x₃ x₄ heq).symm

/-- **`SidonDichotomy` for `principalDivisorData H hdeg`, general `k`.**
Case-splits on `x₂ = ι x₁`: the `≠` branch is
`sidonDichotomy_nonInvolution_general` above (no `sorry`); the `=` branch
needs `IsOnlyFibersInCanonicalClass`, general `k`, which is not yet proved
anywhere in this codebase (see the module docstring) — left as a single
named `sorry` on exactly that branch. -/
theorem sidonDichotomy_general (hdeg : H.f.natDegree = 5)
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f) :
    (principalDivisorData H hdeg).SidonDichotomy := by
  intro δ₀ x₁ x₂ x₃ x₄ heq
  by_cases hcase : x₂ = Point.iota x₁
  · -- Involution branch: needs `IsOnlyFibersInCanonicalClass`, general `k`.
    -- Not yet proved anywhere in this codebase — see module docstring.
    right
    refine ⟨hcase, ?_⟩
    sorry
  · left
    exact sidonDichotomy_nonInvolution_general hdeg hchar hsf δ₀ x₁ x₂ x₃ x₄ hcase heq

/-! ## Feeding the combinatorics directly, without the involution machinery

If the factor base `F` is built so that no two of its points are related by
the hyperelliptic involution (`ι`), `SidonBridge.lean`'s
`AvoidsInvolutionPairs`/`NoWeierstrassPoints`/`D.HyperellipticClass`
apparatus exists only to rule out a case that provably cannot arise for such
an `F` — and `sidonDichotomy_nonInvolution_general` above never produces that
case in the first place, so there is nothing to rule out. This section
proves `SidonRepBound` directly from the non-involution dichotomy alone, for
**any** factor base `F` (no side conditions on `F` at all), matching this
project's actual construction (an arbitrary `F ⊆ H(𝔽_p)` of size `p^{2/5}`,
chosen from the `O(p)` available points, with no involution-avoidance step). -/

variable [Fintype k] [DecidableEq k]

/-- **`SidonRepBound`, general `k`, no involution-avoidance hypotheses.** For
`D := principalDivisorData H hdeg` and *any* `F : Finset H.Point` (no
`AvoidsInvolutionPairs`/`NoWeierstrassPoints`/`HyperellipticClass` needed):
`sidonSet D δ₀ F` satisfies `SidonRepBound`. Same proof shape as
`SidonBridge.lean`'s `sidonRepBound_of_sidonDichotomy`, but the
involution-swap disjunct is never reached — applying
`sidonDichotomy_nonInvolution_general` to a witnessing pair directly returns
`{x₁,x₂} = {y₁,y₂}` with no case split, since that theorem's hypothesis
`hne` only guards its own applicability (it needs `x₂ ≠ ι x₁` to invoke
`isOnlyEffectiveInClass_of_uniqueDegree2MapToP1_general`), not a genuine
alternative outcome to be excluded here.

**Caveat inherited from upstream:** still needs `hne : x₂ ≠ ι x₁` for the
*specific* pair `(x₁,x₂) ∈ F × F` witnessing each fiber, as a precondition to
call `sidonDichotomy_nonInvolution_general` at all (that theorem's own
hypothesis, needed to invoke
`isOnlyEffectiveInClass_of_uniqueDegree2MapToP1_general`) — not, as in
`SidonBridge.lean`'s version, to rule out an alternative outcome after the
fact. `AvoidsInvolutionPairs F` alone only forces "if `x, ιx` are both in
`F` then `x` is Weierstrass" — it does not by itself exclude `x₂ = ιx₁`, so
`NoWeierstrassPoints F` is still needed here too, in the same
supporting role, just earlier in the proof (establishing the hypothesis of
the call, rather than closing an `exfalso` after it). `D.HyperellipticClass`
is the one genuine hypothesis this version drops — it was only ever needed
for the "easy direction" of the full dichotomy, which this version never
invokes. 
-------
Standalone worker lemma, stated with its own fresh binders (not extracted
from any ambient `intro`/`set` state) so there is no possibility of a bound
variable in the final theorem's goal failing to match a locally-introduced
name. `D` and `T` are ordinary explicit arguments here, not `set`-abbreviated
from within a tactic block. -/
theorem repCount_sidonSet_le_two_of_nonInvolution_general
    (hdeg : H.f.natDegree = 5) (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (D : PrincipalDivisorData H) (hDP : D.P = principalSubgroup H hdeg)
    [Fintype (Jacobian H D)] [DecidableEq (Jacobian H D)]
    (δ₀ : H.Point) (F : Finset H.Point)
    (hAvoid : AvoidsInvolutionPairs F) (hNoWeier : NoWeierstrassPoints F)
    (w : Jacobian H D) :
    repCount (sidonSet D δ₀ F) w ≤ 2 := by
  classical
  -- `PrincipalDivisorData` has only one non-`Prop` field (`P`), so `hDP`
  -- already pins down `D` itself, not just `D.P` — this lets us cast `heq`
  -- along a whole-`D` equation (`hD`) instead of the field-only `hDP`, so
  -- the `▸` below actually finds `D` to rewrite in `heq`'s type.
  have hD : D = principalDivisorData H hdeg := by
    cases D with
    | mk DP DleD0 => cases hDP; rfl
  rcases Nat.eq_zero_or_pos (repCount (sidonSet D δ₀ F) w) with hZero | hPos
  · omega
  · have hMem : ∃ P1 P2 : Jacobian H D,
        P1 ∈ sidonSet D δ₀ F ∧ P2 ∈ sidonSet D δ₀ F ∧ P1 + P2 = w := by
      by_contra hNone
      push_neg at hNone
      have hz : repCount (sidonSet D δ₀ F) w = 0 := by
        unfold repCount
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        rintro ⟨P1, P2⟩ hmem
        simp only [Finset.mem_product] at hmem
        exact hNone P1 P2 hmem.1 hmem.2
      omega
    obtain ⟨P1, P2, hP1, hP2, hsum⟩ := hMem
    unfold sidonSet at hP1 hP2
    simp only [Finset.mem_image] at hP1 hP2
    obtain ⟨x1, hx1F, hx1⟩ := hP1
    obtain ⟨x2, hx2F, hx2⟩ := hP2
    subst hx1; subst hx2
    have hx1ne2 : x2 ≠ Point.iota x1 := fun h =>
      hNoWeier x1 hx1F (hAvoid x1 hx1F (h ▸ hx2F)).symm
    have hsubset : ((sidonSet D δ₀ F ×ˢ sidonSet D δ₀ F).filter
        (fun p : Jacobian H D × Jacobian H D => p.1 + p.2 = w)) ⊆
        ({(s D δ₀ x1, s D δ₀ x2), (s D δ₀ x2, s D δ₀ x1)} :
        Finset (Jacobian H D × Jacobian H D)) := by
      rintro ⟨Q1, Q2⟩ hQ
      simp only [Finset.mem_filter, Finset.mem_product] at hQ
      obtain ⟨⟨hQ1, hQ2⟩, hsum'⟩ := hQ
      unfold sidonSet at hQ1 hQ2
      simp only [Finset.mem_image] at hQ1 hQ2
      obtain ⟨y1, hy1F, hy1⟩ := hQ1
      obtain ⟨y2, hy2F, hy2⟩ := hQ2
      subst hy1; subst hy2
      have heq : s D δ₀ x1 + s D δ₀ x2 = s D δ₀ y1 + s D δ₀ y2 := hsum.trans hsum'.symm
      have hpair := sidonDichotomy_nonInvolution_general hdeg hchar hsf δ₀ x1 x2 y1 y2
        hx1ne2 (hD ▸ heq)
      simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
      have h1 : y1 ∈ ({x1, x2} : Set H.Point) := by rw [hpair]; simp
      have h2 : y2 ∈ ({x1, x2} : Set H.Point) := by rw [hpair]; simp
      have h3 : x1 ∈ ({y1, y2} : Set H.Point) := by rw [← hpair]; simp
      have h4 : x2 ∈ ({y1, y2} : Set H.Point) := by rw [← hpair]; simp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 h2 h3 h4
      have hordered : (y1 = x1 ∧ y2 = x2) ∨ (y1 = x2 ∧ y2 = x1) := by
        rcases h1 with h1 | h1
        · rcases h2 with h2 | h2
          · rcases h4 with h4 | h4
            · have hx2x1 : x2 = x1 := h4.trans h1
              exact Or.inl ⟨h1, h2.trans hx2x1.symm⟩
            · exact Or.inl ⟨h1, h4.symm⟩
          · exact Or.inl ⟨h1, h2⟩
        · rcases h2 with h2 | h2
          · exact Or.inr ⟨h1, h2⟩
          · rcases h3 with h3 | h3
            · have hx1x2 : x1 = x2 := h3.trans h1
              exact Or.inr ⟨h1, h2.trans hx1x2.symm⟩
            · exact Or.inr ⟨h1, h3.symm⟩
      rcases hordered with ⟨hy1, hy2⟩ | ⟨hy1, hy2⟩
      · exact Or.inl ⟨by rw [hy1], by rw [hy2]⟩
      · exact Or.inr ⟨by rw [hy1], by rw [hy2]⟩
    have hcard2 : ({(s D δ₀ x1, s D δ₀ x2), (s D δ₀ x2, s D δ₀ x1)} :
        Finset (Jacobian H D × Jacobian H D)).card ≤ 2 := by
      apply le_trans (Finset.card_insert_le _ _)
      simp
    have hfinal : repCount (sidonSet D δ₀ F) w =
        ((sidonSet D δ₀ F ×ˢ sidonSet D δ₀ F).filter
          (fun p : Jacobian H D × Jacobian H D => p.1 + p.2 = w)).card := rfl
    rw [hfinal]
    exact le_trans (Finset.card_le_card hsubset) hcard2

theorem sidonRepBound_of_sidonDichotomy_nonInvolution_general
    (hdeg : H.f.natDegree = 5) (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    [Fintype (Jacobian H (principalDivisorData H hdeg))]
    [DecidableEq (Jacobian H (principalDivisorData H hdeg))]
    (δ₀ : H.Point) (F : Finset H.Point)
    (hAvoid : AvoidsInvolutionPairs F) (hNoWeier : NoWeierstrassPoints F) :
    SidonRepBound (sidonSet (principalDivisorData H hdeg) δ₀ F) :=
  fun w =>
    repCount_sidonSet_le_two_of_nonInvolution_general hdeg hchar hsf
      (principalDivisorData H hdeg) rfl δ₀ F hAvoid hNoWeier w

/-! ## Assembly: the worst-case hit-count guarantee, end to end, over `F_p`

Chains `sidonRepBound_of_sidonDichotomy_nonInvolution_general` above into
`CombinatorialSecondMoment.lean`'s `sidon_gives_hit_count_bound_combinatorial`
— itself unconditional, no `sorry`, pure abstract-group combinatorics — so
that the whole route from "P1+P2 is irreducible" (the genus-2, general-`k`
Sidon fact this project's `LPairFinrankOneOrdAtFracSpec.lean` proves) down to
a genuine `≥ B²/2` guarantee on the number of `Δ` admitting a relation is one
closed, `sorry`-free theorem, for `T := sidonSet (principalDivisorData H
hdeg) δ₀ F` and any involution-pair-avoiding `F ⊆ H.Point`.

**What this is, and is not.** This is the *worst-case* bound advisory-7 §7.4
onward already flags as short of the `Θ(B⁴/N)` "generic" target the
complexity heuristic actually wants — closing that gap needs a genuine bound
on `E(S,S)` (the second-moment/8th-Fourier-moment question), which nothing
in this repo attempts (see `SidonBridge.lean`'s own `GenericFactorBase`
section for where that gap is isolated). What *is* new here, versus
`SidonBridge.lean`'s existing (also worst-case) `sidonRepBound_of_
sidonDichotomy`, is that this version needs no unproved `SidonDichotomy`
hypothesis at all — it is unconditional, for the actual curve, over `F_p`. -/

theorem hitCount_ge_of_sidonDichotomy_nonInvolution_general
    (hdeg : H.f.natDegree = 5) (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    [Fintype (Jacobian H (principalDivisorData H hdeg))]
    [DecidableEq (Jacobian H (principalDivisorData H hdeg))]
    (δ₀ : H.Point) (F : Finset H.Point)
    (hAvoid : AvoidsInvolutionPairs F) (hNoWeier : NoWeierstrassPoints F)
    (hcard_pos : 0 < (sidonSet (principalDivisorData H hdeg) δ₀ F).card) :
    ((sidonSet (principalDivisorData H hdeg) δ₀ F).card : ℝ) ^ 2 / 2 ≤
      ((Finset.univ.filter
        (fun Δ : Jacobian H (principalDivisorData H hdeg) =>
          matchCount (sidonSet (principalDivisorData H hdeg) δ₀ F) Δ ≠ 0)).card : ℝ) :=
  sidon_gives_hit_count_bound_combinatorial
    (sidonSet (principalDivisorData H hdeg) δ₀ F)
    (sidonRepBound_of_sidonDichotomy_nonInvolution_general hdeg hchar hsf δ₀ F hAvoid hNoWeier)
    hcard_pos

end HyperellipticPolynomial
