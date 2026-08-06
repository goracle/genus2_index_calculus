import Mathlib
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
set_option linter.style.header false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false


open Finset BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]

/-! ### 1. Sidon Sets and Representation Bounds -/

def IsSidon (S : Finset G) : Prop :=
  ∀ a b c d, a ∈ S → b ∈ S → c ∈ S → d ∈ S → 
    a + b = c + d → ({a, b} : Finset G) = {c, d}

def repFunction (S : Finset G) (g : G) : ℕ :=
  ((S ×ˢ S).filter (fun p => p.1 + p.2 = g)).card

theorem repFunction_bound_of_sidon {S : Finset G} (hS : IsSidon S) (g : G) :
    repFunction S g ≤ 2 := by
  unfold repFunction
  set F := (S ×ˢ S).filter (fun p => p.1 + p.2 = g) with hF_def
  by_cases hF : F.Nonempty
  · rcases hF with ⟨⟨a, b⟩, hab⟩
    have hab_mem : (a, b) ∈ S ×ˢ S ∧ a + b = g := Finset.mem_filter.mp hab
    have ha : a ∈ S := (Finset.mem_product.mp hab_mem.1).1
    have hb : b ∈ S := (Finset.mem_product.mp hab_mem.1).2
    have hab_sum : a + b = g := hab_mem.2
    have h_sub : F ⊆ {(a, b), (b, a)} := by
      intro ⟨c, d⟩ hcd
      have hcd_mem : (c, d) ∈ S ×ˢ S ∧ c + d = g := Finset.mem_filter.mp hcd
      have hc : c ∈ S := (Finset.mem_product.mp hcd_mem.1).1
      have hd : d ∈ S := (Finset.mem_product.mp hcd_mem.1).2
      have hcd_sum : c + d = g := hcd_mem.2
      have h_eq_sum : c + d = a + b := by rw [hcd_sum, hab_sum]
      have h_set_eq : ({c, d} : Finset G) = {a, b} := hS c d a b hc hd ha hb h_eq_sum
      have hcd_mem_pair : c ∈ ({a, b} : Finset G) := by
        rw [← h_set_eq]
        exact Finset.mem_insert_self c {d}
      have hdc_mem_pair : d ∈ ({a, b} : Finset G) := by
        rw [← h_set_eq]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self d)
      rw [Finset.mem_insert, Finset.mem_singleton] at hcd_mem_pair hdc_mem_pair
      rw [Finset.mem_insert, Finset.mem_singleton]
      -- c, d ∈ {a, b} pointwise; combined with c + d = a + b this pins down
      -- (c, d) as either (a, b) or (b, a) (the c = d = a or c = d = b cases
      -- force a = b via the sum equation, landing on the same conclusion).
      rcases hcd_mem_pair with hc_eq | hc_eq <;> rcases hdc_mem_pair with hd_eq | hd_eq
      · -- c = a, d = a: sum equation forces a = b, so (c,d) = (a,a) = (a,b)
        left
        have hsum2 : a + a = a + b := by
          calc a + a = c + d := by rw [hc_eq, hd_eq]
            _ = a + b := h_eq_sum
        have hab_eq : a = b := add_left_cancel hsum2
        rw [Prod.mk.injEq]
        exact ⟨hc_eq, hd_eq.trans hab_eq⟩
      · -- c = a, d = b: (c,d) = (a,b)
        left
        rw [Prod.mk.injEq]
        exact ⟨hc_eq, hd_eq⟩
      · -- c = b, d = a: (c,d) = (b,a)
        right
        rw [Prod.mk.injEq]
        exact ⟨hc_eq, hd_eq⟩
      · -- c = b, d = b: sum equation forces b = a, so (c,d) = (b,b) = (b,a)
        right
        have hsum2 : b + b = a + b := by
          calc b + b = c + d := by rw [hc_eq, hd_eq]
            _ = a + b := h_eq_sum
        have hab_eq : b = a := add_right_cancel hsum2
        rw [Prod.mk.injEq]
        exact ⟨hc_eq, hd_eq.trans hab_eq⟩
    have h_card := Finset.card_le_card h_sub
    have h_pair_card : ({(a, b), (b, a)} : Finset (G × G)).card ≤ 2 := Finset.card_insert_le (a, b) {(b, a)}
    omega
  · rw [Finset.not_nonempty_iff_eq_empty] at hF
    rw [hF, Finset.card_empty]
    omega

/-! ### 2. Representation Moments and Additive Energy -/

def sumSet (S : Finset G) : Finset G :=
  (S ×ˢ S).image (fun p => p.1 + p.2)

def representationMoment (S : Finset G) (k : ℕ) : ℕ :=
  ∑ g ∈ sumSet S, (repFunction S g)^k

def additiveEnergy (S : Finset G) : ℕ :=
  representationMoment S 2

def moment8 (S : Finset G) : ℕ :=
  representationMoment S 8

theorem moment_le_moment_of_le {S : Finset G} {k m : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) :
    representationMoment S k ≤ representationMoment S m := by
  unfold representationMoment
  refine Finset.sum_le_sum ?_
  intro g _
  by_cases h : repFunction S g = 0
  · rw [h]
    have hk0 : 0 ^ k = 0 := Nat.zero_pow (by omega)
    have hm0 : 0 ^ m = 0 := Nat.zero_pow (by omega)
    rw [hk0, hm0]
  · have hpos : 0 < repFunction S g := Nat.pos_of_ne_zero h
    exact Nat.pow_le_pow_right hpos hkm

theorem additiveEnergy_le_moment8 (S : Finset G) :
    additiveEnergy S ≤ moment8 S := by
  exact moment_le_moment_of_le (by decide) (by decide)

/-! ### 3. Fiber Conservation and Degree Stability -/

def fiber (f : X → Y) (y : Y) : Finset X :=
  Finset.univ.filter (fun x => f x = y)

def fiberDegree (f : X → Y) (y : Y) : ℕ :=
  (fiber f y).card

def IsGenericTargetPoint (f : X → Y) (d : ℕ) (y : Y) : Prop :=
  fiberDegree f y = d

theorem generic_fiber_degree_stable 
    (f : X → Y) (d : ℕ) (U : Finset Y)
    (hU : ∀ y ∈ U, IsGenericTargetPoint f d y) (y1 y2 : Y)
    (hy1 : y1 ∈ U) (hy2 : y2 ∈ U) :
    fiberDegree f y1 = fiberDegree f y2 := by
  have h1 : fiberDegree f y1 = d := hU y1 hy1
  have h2 : fiberDegree f y2 = d := hU y2 hy2
  rw [h1, h2]

theorem sum_fiberDegrees_eq_card_bound (f : X → Y) :
    ∑ y : Y, fiberDegree f y = Fintype.card X := by
  unfold fiberDegree fiber
  have h := Finset.sum_fiberwise (s := (Finset.univ : Finset X)) (g := f)
    (f := fun _ : X => (1 : ℕ))
  simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ] at h
  exact h
