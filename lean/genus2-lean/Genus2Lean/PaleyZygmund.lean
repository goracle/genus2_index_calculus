import Mathlib
import Genus2Lean.AverageComplexity

/-!
# Genus-2 index calculus: conditional hit-probability bound (advisory-7, eq 11)

This file adds the Paley–Zygmund step on top of `AverageComplexity.lean`.

Everything here is either:
  (a) unconditional (the Paley–Zygmund inequality itself, proved from scratch
      for a finite uniform space via Mathlib's finite Cauchy–Schwarz, no
      measure theory needed), or
  (b) explicitly conditional on a named hypothesis `SecondMomentBound`,
      which is NOT proved anywhere in this file. That hypothesis is exactly
      the still-open additive-energy question flagged in advisory-7 §7.4.

No claim here should be read as resolving the open problem — only as
formalizing the *reduction* "second moment bound ⟹ hit-probability bound"
so that whatever eventually proves (or assumes, for a paper) the energy
bound gets this consequence for free.
-/

open Finset

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

omit [AddCommGroup G] [DecidableEq G] in
/-- Finite Paley–Zygmund. For a nonnegative `X` on a finite type, the
probability (uniform counting measure) that `X > 0` is at least
`(∑ X)² / (|G| · ∑ X²)`. Stated in the "cross-multiplied" form to avoid
division-by-zero side conditions; see `paley_zygmund_prob` below for the
probability form when `∑ X² ≠ 0`.

Proof: Cauchy–Schwarz on the support of `X`, treating the indicator as one
factor and `X` as the other, then bounding the support's size by `|G|`. -/
theorem paley_zygmund_finite (X : G → ℝ) (_hX : ∀ Δ, 0 ≤ X Δ) :
    (∑ Δ, X Δ) ^ 2 ≤
      ((univ.filter (fun Δ => X Δ ≠ 0)).card : ℝ) * ∑ Δ, (X Δ) ^ 2 := by
  set S := univ.filter (fun Δ => X Δ ≠ 0) with hS
  have hsplit : ∑ Δ, X Δ = ∑ Δ ∈ S, X Δ := by
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun Δ => X Δ ≠ 0) X]
    have : ∑ Δ ∈ univ.filter (fun Δ => ¬ X Δ ≠ 0), X Δ = 0 := by
      apply Finset.sum_eq_zero
      intro Δ hΔ
      simp only [Finset.mem_filter, not_not] at hΔ
      exact hΔ.2
    rw [this, add_zero]
  have hsplit2 : ∑ Δ, (X Δ) ^ 2 = ∑ Δ ∈ S, (X Δ) ^ 2 := by
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun Δ => X Δ ≠ 0) (fun Δ => (X Δ)^2)]
    have : ∑ Δ ∈ univ.filter (fun Δ => ¬ X Δ ≠ 0), (X Δ)^2 = 0 := by
      apply Finset.sum_eq_zero
      intro Δ hΔ
      simp only [Finset.mem_filter, not_not] at hΔ
      simp [hΔ.2]
    rw [this, add_zero]
  rw [hsplit, hsplit2]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1:ℝ)) X
  simp only [one_mul, one_pow] at hcs
  calc (∑ Δ ∈ S, X Δ) ^ 2
      ≤ (∑ _Δ ∈ S, (1:ℝ)) * ∑ Δ ∈ S, (X Δ)^2 := hcs
    _ = (S.card : ℝ) * ∑ Δ ∈ S, (X Δ)^2 := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]

omit [AddCommGroup G] [DecidableEq G] in
/-- Probability form of `paley_zygmund_finite`: when `∑ X² ≠ 0`, the *fraction*
of `Δ : G` with `X Δ ≠ 0` (i.e. the uniform-measure probability) is at least
`(∑ X)² / (|G| · ∑ X²)`. This is exactly `paley_zygmund_finite` divided through
by `|G| · ∑ X²`, phrased as a probability rather than a count — the form
advisory-7 actually states its bounds in (e.g. eq 11, 17). -/
theorem paley_zygmund_prob (X : G → ℝ) (hX : ∀ Δ, 0 ≤ X Δ)
    (hsq : ∑ Δ : G, (X Δ) ^ 2 ≠ 0) :
    (∑ Δ, X Δ) ^ 2 / ((Fintype.card G : ℝ) * ∑ Δ, (X Δ) ^ 2) ≤
      ((univ.filter (fun Δ => X Δ ≠ 0)).card : ℝ) / (Fintype.card G : ℝ) := by
  have hcard_pos : (0:ℝ) < (Fintype.card G : ℝ) := by
    have hne : (univ.filter (fun Δ => X Δ ≠ 0)).card ≤ Fintype.card G :=
      Finset.card_le_univ _
    have hpos : 0 < Fintype.card G := by
      by_contra h
      push_neg at h
      have hG0 : Fintype.card G = 0 := Nat.le_zero.mp h
      have : IsEmpty G := Fintype.card_eq_zero_iff.mp hG0
      have hsum0 : ∑ Δ : G, (X Δ) ^ 2 = 0 := by
        simp [Finset.univ_eq_empty]
      exact hsq hsum0
    exact_mod_cast hpos
  have hsq_nonneg : (0:ℝ) ≤ ∑ Δ : G, (X Δ) ^ 2 :=
    Finset.sum_nonneg (fun Δ _ => sq_nonneg _)
  have hsq_pos : (0:ℝ) < ∑ Δ : G, (X Δ) ^ 2 := lt_of_le_of_ne hsq_nonneg (Ne.symm hsq)
  have hfin := paley_zygmund_finite X hX
  have hdenom_pos : (0:ℝ) < (Fintype.card G : ℝ) * ∑ Δ, (X Δ) ^ 2 :=
    mul_pos hcard_pos hsq_pos
  -- Clear the left-hand denominator first (single use of `div_le_iff₀`,
  -- already used successfully elsewhere in this file).
  rw [div_le_iff₀ hdenom_pos]
  -- Goal is now: (∑ X)² ≤ (count / card) * (card * ∑ X²).
  -- Rewrite the right side back to `count * ∑ X²` by cancelling card/card,
  -- then finish with `hfin` directly.
  have hcard_ne : (Fintype.card G : ℝ) ≠ 0 := ne_of_gt hcard_pos
  have hrhs :
      ((univ.filter (fun Δ => X Δ ≠ 0)).card : ℝ) / (Fintype.card G : ℝ) *
          ((Fintype.card G : ℝ) * ∑ Δ, (X Δ) ^ 2) =
        ((univ.filter (fun Δ => X Δ ≠ 0)).card : ℝ) * ∑ Δ, (X Δ) ^ 2 := by
    field_simp
  rw [hrhs]
  exact hfin

/-- Named hypothesis: a bound on the second moment `∑ N(Δ)²`. This is
*not* proved here — it is exactly the open additive-energy question from
advisory-7 §7.4 (roughly: `∑ N(Δ)² ≤ M` for some explicit `M` in terms of
`B` and `|G|`, coming from bounding the additive energy of `F`). Anything
downstream of this hypothesis is conditional, and is labeled as such. -/
def SecondMomentBound (F : Finset G) (M : ℝ) : Prop :=
  ∑ Δ : G, (matchCount F Δ : ℝ) ^ 2 ≤ M

/-- **Conditional** hit-probability bound (advisory-7 eq (11), the
Paley–Zygmund step). Given a second-moment bound `M` for `F` (NOT proved by
this file — supply it as a hypothesis, e.g. from a Sidon/additive-energy
argument), the number of `Δ` for which `N(Δ) > 0` is at least
`B⁸ / (|G| · M)`, i.e. a constant fraction of `G` when `M = O(B⁴)`.

This theorem proves nothing about whether `SecondMomentBound` holds for any
particular `F` — that remains open. It only proves the reduction. -/
theorem hit_count_ge_of_second_moment_bound
    (F : Finset G) (M : ℝ) (hM : SecondMomentBound F M) (hMpos : 0 < M) :
    ((F.card : ℝ) ^ 4) ^ 2 / M ≤
      ((univ.filter (fun Δ => matchCount F Δ ≠ 0)).card : ℝ) := by
  have hX : ∀ Δ, 0 ≤ (matchCount F Δ : ℝ) := fun Δ => Nat.cast_nonneg _
  have hpz := paley_zygmund_finite (fun Δ => (matchCount F Δ : ℝ)) hX
  have hsum : ∑ Δ : G, (matchCount F Δ : ℝ) = (F.card : ℝ) ^ 4 := by
    have h := sum_matchCount_eq_card_pow_four F
    have : (∑ Δ : G, (matchCount F Δ : ℝ)) = ((F.card ^ 4 : ℕ) : ℝ) := by
      rw [← h]; push_cast; rfl
    rw [this]; push_cast; ring
  rw [hsum] at hpz
  have hfilter_eq :
      univ.filter (fun Δ => (matchCount F Δ : ℝ) ≠ 0) =
        univ.filter (fun Δ => matchCount F Δ ≠ 0) := by
    apply Finset.filter_congr
    intro Δ _
    simp
  rw [hfilter_eq] at hpz
  have hM' : ∑ Δ : G, (matchCount F Δ : ℝ) ^ 2 ≤ M := hM
  have hstep : ((F.card : ℝ) ^ 4) ^ 2 ≤
      ((univ.filter (fun Δ => matchCount F Δ ≠ 0)).card : ℝ) * M := by
    calc ((F.card : ℝ) ^ 4) ^ 2
        ≤ ((univ.filter (fun Δ => matchCount F Δ ≠ 0)).card : ℝ) *
            ∑ Δ : G, (matchCount F Δ : ℝ) ^ 2 := hpz
      _ ≤ ((univ.filter (fun Δ => matchCount F Δ ≠ 0)).card : ℝ) * M := by
          apply mul_le_mul_of_nonneg_left hM'
          exact Nat.cast_nonneg _
  rw [div_le_iff₀ hMpos]
  linarith [hstep]
