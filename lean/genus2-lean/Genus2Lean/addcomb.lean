import Mathlib
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
set_option linter.style.header false
set_option linter.unusedFintypeInType false


open Finset BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]

namespace AddComb

/-! ### Fiber Degree Sum Identity -/

def fiber (f : X → Y) (y : Y) : Finset X :=
  Finset.univ.filter (fun x => f x = y)

def fiberDegree (f : X → Y) (y : Y) : ℕ :=
  (fiber f y).card

/-- Fiber sum theorem: ∑_{y ∈ Y} |f⁻¹(y)| = |X| -/
theorem sum_fiberDegrees_eq_card (f : X → Y) :
    ∑ y : Y, fiberDegree f y = Fintype.card X := by
  unfold fiberDegree fiber
  have h := Finset.sum_fiberwise (s := (Finset.univ : Finset X)) (g := f)
    (f := fun _ : X => (1 : ℕ))
  simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ] at h
  -- h : ∑ y : Y, (univ.filter (fun x => f x = y)).card = Fintype.card X
  exact h

/-! ### Target Hits Partition Identity -/

def repFunction (S : Finset G) (g : G) : ℕ :=
  ((S ×ˢ S).filter (fun p => p.1 + p.2 = g)).card

def targetHits (S : Finset G) (delta : G) : ℕ :=
  repFunction S delta

/-- Partition identity: Total target hits across finite group G equal |S|² -/
theorem sum_targetHits_eq_square (S : Finset G) :
    (∑ delta : G, targetHits S delta) = S.card ^ 2 := by
  unfold targetHits repFunction
  have h := Finset.sum_fiberwise (s := S ×ˢ S) (g := fun p : G × G => p.1 + p.2)
    (f := fun _ : G × G => (1 : ℕ))
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at h
  -- h : ∑ delta : G, ((S ×ˢ S).filter (fun p => p.1 + p.2 = delta)).card = #(S ×ˢ S)
  rw [h, Finset.card_product]
  ring

/-! ### Additive Energy Positivity -/

def sumSet (S : Finset G) : Finset G :=
  (S ×ˢ S).image (fun p => p.1 + p.2)

def additiveEnergy (S : Finset G) : ℕ :=
  ∑ g ∈ sumSet S, (repFunction S g)^2

/-- Non-empty set guarantees strictly positive additive energy E(S,S) > 0 -/
theorem additiveEnergy_pos (S : Finset G) (hS : S.Nonempty) :
    0 < additiveEnergy S := by
  rcases hS with ⟨x, hx⟩
  have hx_sum : x + x ∈ sumSet S := by
    unfold sumSet
    exact Finset.mem_image.mpr ⟨(x, x), Finset.mem_product.mpr ⟨hx, hx⟩, rfl⟩
  have h_rep_pos : 0 < repFunction S (x + x) := by
    unfold repFunction
    refine Finset.card_pos.mpr ⟨(x, x), ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hx⟩, rfl⟩
  have h_sq_pos : 0 < (repFunction S (x + x))^2 := by
    exact Nat.pow_pos h_rep_pos
  unfold additiveEnergy
  have hle : (repFunction S (x + x))^2 ≤ ∑ g ∈ sumSet S, (repFunction S g)^2 := by
    exact Finset.single_le_sum
      (f := fun g => (repFunction S g)^2) (fun _ _ => Nat.zero_le _) hx_sum
  exact lt_of_lt_of_le h_sq_pos hle

end AddComb
