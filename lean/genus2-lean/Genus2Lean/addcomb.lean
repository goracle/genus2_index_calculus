import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
open Finset BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]

/-! ### Fiber Degree Sum Identity -/

def fiber (f : X → Y) (y : Y) : Finset X :=
  Finset.univ.filter (fun x => f x = y)

def fiberDegree (f : X → Y) (y : Y) : ℕ :=
  (fiber f y).card

/-- Fiber sum theorem: ∑_{y ∈ Y} |f⁻¹(y)| = |X| -/
theorem sum_fiberDegrees_eq_card (f : X → Y) :
    ∑ y : Y, fiberDegree f y = Fintype.card X := by
  unfold fiberDegree fiber
  rw [← Finset.card_univ]
  exact Finset.sum_card_fiberwise_eq_card_univ f

/-! ### Target Hits Partition Identity -/

def repFunction (S : Finset G) (g : G) : ℕ :=
  ((S ×ˢ S).filter (fun p => p.1 + p.2 = g)).card

def targetHits (S : Finset G) (delta : G) : ℕ :=
  repFunction S delta

/-- Partition identity: Total target hits across finite group G equal |S|² -/
theorem sum_targetHits_eq_square (S : Finset G) :
    (∑ delta : G, targetHits S delta) = S.card ^ 2 := by
  unfold targetHits repFunction
  have h := Finset.card_eq_sum_card_fiberwise (f := fun p : G × G => p.1 + p.2) (s := S ×ˢ S)
  rw [h, Finset.card_prod]
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
  exact Lt.trans_le h_sq_pos (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hx_sum)
