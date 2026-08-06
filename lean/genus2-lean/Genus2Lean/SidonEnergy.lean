import Mathlib
import Genus2Lean.AverageComplexity
set_option linter.style.header false

/-!
# Genus-2 index calculus: Sidon-set energy bound (advisory-7, eq 5-6)

This file formalizes the additive-energy bound for a Sidon set `T`, from
advisory-7 §4 (the Forey–Fresán–Kowalski step). Unlike `AverageComplexity.lean`
and `PaleyZygmund.lean`, this is *not* about the factor base `F` itself, but
about `T = s(F) ⊆ G`, the image of `F` under the Sidon embedding.

The Sidon property of `T` (eq 5: every element of `G` has at most 2 ordered
representations as a sum of two elements of `T`) is a genuine geometric fact
proved by Forey–Fresán–Kowalski (2023) — it is NOT reproved here. It is taken
as a named hypothesis `SidonRepBound`, exactly as `SecondMomentBound` is taken
as a hypothesis in `PaleyZygmund.lean`. This file formalizes only the
downstream combinatorial consequence: Sidon ⟹ low energy (eq 6).

The bound proved here (`E(T,T) ≤ 2·B²`) is the clean form of eq (6); the
advisory's stated intermediate step `E(T,T) ≤ 4·#T ≤ 4·C(B,2)` is a slightly
looser version of the same fact and is not separately formalized.
-/

open Finset

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The representation function `r_{T,T}(g)` = number of *ordered* pairs
`(P1, P2) ∈ T × T` with `P1 + P2 = g`. This is advisory-7's `r_{T,T}`. -/
noncomputable def repCount (T : Finset G) (g : G) : ℕ :=
  ((T ×ˢ T).filter (fun p : G × G => p.1 + p.2 = g)).card

/-- Advisory-7, eq (like eq 9 for `matchCount`): summing `r_{T,T}(g)` over
every `g` recovers `B²` exactly — unconditional, no Sidon input needed. -/
theorem sum_repCount_eq_card_sq (T : Finset G) :
    ∑ g : G, repCount T g = T.card ^ 2 := by
  have hcard : (T ×ˢ T).card = T.card ^ 2 := by
    simp [Finset.card_product, sq]
  have hfiber :
      (T ×ˢ T).card =
        ∑ g ∈ (Finset.univ : Finset G),
          ((T ×ˢ T).filter (fun p : G × G => p.1 + p.2 = g)).card :=
    Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
  rw [← hcard, hfiber]
  rfl

/-- Named hypothesis (advisory-7, eq 5): `T` is Sidon, meaning every group
element has at most 2 ordered representations as a sum of two elements of
`T`. This is NOT proved here — it is exactly the Forey–Fresán–Kowalski
structural theorem (2023, Thm 1, case g=2) applied to `T = s(F)`, under the
side condition that `F` avoids hyperelliptic-involution pairs. -/
def SidonRepBound (T : Finset G) : Prop :=
  ∀ g : G, repCount T g ≤ 2

/-- **Conditional** additive-energy bound (advisory-7, eq 6). Given that `T`
is Sidon (`SidonRepBound`, NOT proved by this file), the additive energy
`E(T,T) = ∑_g r_{T,T}(g)²` is at most `2 · B²`.

Proof: since `0 ≤ r(g) ≤ 2` pointwise, `r(g)² ≤ 2 · r(g)` for every `g`
(as `r(g) ∈ {0,1,2}`, checked by `interval_cases` on the bound), so summing
over `g` and using `sum_repCount_eq_card_sq` gives the result. -/
theorem sidon_energy_bound (T : Finset G) (hSidon : SidonRepBound T) :
    ∑ g : G, (repCount T g : ℝ) ^ 2 ≤ 2 * (T.card : ℝ) ^ 2 := by
  have hpt : ∀ g : G, (repCount T g : ℝ) ^ 2 ≤ 2 * (repCount T g : ℝ) := by
    intro g
    have hle : repCount T g ≤ 2 := hSidon g
    have : (repCount T g : ℝ) ≤ 2 := by exact_mod_cast hle
    have hnn : (0:ℝ) ≤ repCount T g := Nat.cast_nonneg _
    nlinarith
  have hsum_le : ∑ g : G, (repCount T g : ℝ) ^ 2 ≤ ∑ g : G, 2 * (repCount T g : ℝ) :=
    Finset.sum_le_sum (fun g _ => hpt g)
  have hsum_eq : ∑ g : G, (2:ℝ) * (repCount T g : ℝ) = 2 * ∑ g : G, (repCount T g : ℝ) := by
    rw [Finset.mul_sum]
  have hbase : ∑ g : G, (repCount T g : ℝ) = (T.card : ℝ) ^ 2 := by
    have h := sum_repCount_eq_card_sq T
    have : (∑ g : G, (repCount T g : ℝ)) = ((T.card ^ 2 : ℕ) : ℝ) := by
      rw [← h]; push_cast; rfl
    rw [this]; push_cast; ring
  calc ∑ g : G, (repCount T g : ℝ) ^ 2
      ≤ ∑ g : G, 2 * (repCount T g : ℝ) := hsum_le
    _ = 2 * ∑ g : G, (repCount T g : ℝ) := hsum_eq
    _ = 2 * (T.card : ℝ) ^ 2 := by rw [hbase]
