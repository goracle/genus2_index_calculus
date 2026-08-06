import Mathlib
import Genus2Lean.AverageComplexity
import Genus2Lean.SidonEnergy
set_option linter.style.header false

/-!
# Genus-2 index calculus: matchCount as autocorrelation of repCount (advisory-7 §6.2/§7.5)

This file generalizes `SidonEnergy.lean`'s `matchCount_zero_eq_energy` (the `Δ = 0`
slice) to *every* `Δ`, and draws the one pointwise consequence that follows from
Sidon-ness alone.

Advisory-7's §6.2 correction states the identity in words:

    X(Δ) = Σ_g r_{T,T}(g) · r_{T,T}(g - Δ)

i.e. `matchCount` is the autocorrelation of `repCount` with itself. The advisory
uses this only descriptively, to explain why finiteness-of-fibers (§6.2) does NOT
bound `X(Δ)` pointwise. It does not go on to extract the pointwise Sidon bound
below — that is a small further observation made here, not lifted from the text.

Everything in this file is a direct corollary of lemmas already proved
unconditionally (`matchCount_zero_eq_energy`'s proof technique, `sum_repCount_eq_card_sq`)
plus the same `SidonRepBound` hypothesis already used in `SidonEnergy.lean`. No new
external theorem, no Fourier analysis — same style of erosion as the rest of this
project.
-/

open Finset

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- **Unconditional identity** (advisory-7 §6.2's correction, stated in words there):
`matchCount T Δ` — the count of quadruples `(a,b,c,d) ∈ T⁴` with `a+b-c-d=Δ` — equals
the autocorrelation of `repCount T` with itself at `Δ`. This generalizes
`matchCount_zero_eq_energy` (the `Δ = 0` case, where autocorrelation-at-0 is exactly
the additive energy `Σ_g r(g)²`) to every `Δ`.

Proof: identical fiberwise double-counting to `matchCount_zero_eq_energy` — group
quadruples `(a,b,c,d)` by `g := a+b`, and note `a+b-c-d=Δ ∧ a+b=g` iff `c+d=g-Δ ∧ a+b=g`. -/
theorem matchCount_eq_autocorr (T : Finset G) (Δ : G) :
    matchCount T Δ = ∑ g : G, repCount T g * repCount T (g - Δ) := by
  unfold matchCount repCount
  have hfiber :
      ((T ×ˢ T ×ˢ T ×ˢ T).filter
        (fun p : G × G × G × G => p.1 + p.2.1 - p.2.2.1 - p.2.2.2 = Δ)).card =
        ∑ g : G,
          ((T ×ˢ T ×ˢ T ×ˢ T).filter
            (fun p : G × G × G × G =>
              p.1 + p.2.1 - p.2.2.1 - p.2.2.2 = Δ ∧ p.1 + p.2.1 = g)).card := by
    have h := Finset.sum_fiberwise
      (s := (T ×ˢ T ×ˢ T ×ˢ T).filter
        (fun p : G × G × G × G => p.1 + p.2.1 - p.2.2.1 - p.2.2.2 = Δ))
      (g := fun p : G × G × G × G => p.1 + p.2.1)
      (f := fun _ : G × G × G × G => (1 : ℕ))
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at h
    rw [← h]
    apply Finset.sum_congr rfl
    intro g _
    congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_product]
    tauto
  rw [hfiber]
  apply Finset.sum_congr rfl
  intro g _
  rw [← Finset.card_product]
  apply Finset.card_bij
    (i := fun p _ => ((p.1, p.2.1), (p.2.2.1, p.2.2.2)))
  · rintro ⟨a, b, c, d⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨ha, hb, hc, hd⟩, heq, hsum⟩ := hp
    simp only [Finset.mem_product, Finset.mem_filter]
    refine ⟨⟨⟨ha, hb⟩, hsum⟩, ⟨hc, hd⟩, ?_⟩
    have h1 : a + b - (c + d) = Δ := by
      have : a + b - c - d = a + b - (c + d) := by abel
      rw [← this]; exact heq
    rw [hsum] at h1
    have h2 := sub_eq_iff_eq_add.mp h1
    rw [h2]; abel
  · rintro ⟨a, b, c, d⟩ hp ⟨a', b', c', d'⟩ hp' heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨⟨ha, hb⟩, hc, hd⟩ := heq
    simp [ha, hb, hc, hd]
  · rintro ⟨⟨a, b⟩, c, d⟩ hq
    simp only [Finset.mem_product, Finset.mem_filter] at hq
    obtain ⟨⟨⟨ha, hb⟩, hab⟩, ⟨hc, hd⟩, hcd⟩ := hq
    refine ⟨(a, b, c, d), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨ha, hb, hc, hd⟩, ?_, hab⟩
    have hgd : c + d = g - Δ := hcd
    calc a + b - c - d = g - (c + d) := by rw [← hab]; abel
      _ = g - (g - Δ) := by rw [hgd]
      _ = Δ := by abel

/-- **Reindexing lemma**: `Σ_g repCount T (g - Δ) = Σ_g repCount T g`, since
`g ↦ g - Δ` is a bijection of `G`. Used to turn the autocorrelation identity into
a clean pointwise bound below. -/
theorem sum_repCount_shift (T : Finset G) (Δ : G) :
    ∑ g : G, repCount T (g - Δ) = ∑ g : G, repCount T g := by
  apply Finset.sum_nbij' (fun g => g - Δ) (fun g => g + Δ)
  · intros; exact Finset.mem_univ _
  · intros; exact Finset.mem_univ _
  · intros; abel
  · intros; abel
  · intros; rfl

/-- **Sidon-only pointwise cap on `matchCount`, at every `Δ`** (not just `Δ = 0`).
This is the small further step past `matchCount_zero_bound` (`SidonEnergy.lean`):
combining the autocorrelation identity above with `SidonRepBound` (`repCount ≤ 2`
pointwise) and the reindexing lemma bounds `matchCount T Δ` uniformly, for every `Δ`
simultaneously, by `2 · B²` — not merely at the diagonal `Δ = 0`.

Proof: `matchCount T Δ = Σ_g repCount(g) · repCount(g-Δ) ≤ Σ_g 2 · repCount(g-Δ)
= 2 · Σ_g repCount(g-Δ) = 2 · Σ_g repCount(g) = 2 · B²`, using `sidon_energy_bound`'s
hypothesis, `sum_repCount_shift`, and `sum_repCount_eq_card_sq`. -/
theorem matchCount_le_two_card_sq (T : Finset G) (hSidon : SidonRepBound T) (Δ : G) :
    matchCount T Δ ≤ 2 * T.card ^ 2 := by
  rw [matchCount_eq_autocorr]
  have hpt : ∀ g : G, repCount T g * repCount T (g - Δ) ≤ 2 * repCount T (g - Δ) := by
    intro g
    exact Nat.mul_le_mul_right _ (hSidon g)
  calc ∑ g : G, repCount T g * repCount T (g - Δ)
      ≤ ∑ g : G, 2 * repCount T (g - Δ) := Finset.sum_le_sum (fun g _ => hpt g)
    _ = 2 * ∑ g : G, repCount T (g - Δ) := by rw [Finset.mul_sum]
    _ = 2 * ∑ g : G, repCount T g := by rw [sum_repCount_shift]
    _ = 2 * T.card ^ 2 := by rw [sum_repCount_eq_card_sq]
