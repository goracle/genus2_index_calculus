import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]

/-! ### 1. Sidon Sets and Representation Bounds -/

/-- A finset S ⊆ G is a Sidon set if a + b = c + d implies {a, b} = {c, d} -/
def IsSidon (S : Finset G) : Prop :=
  ∀ a b c d, a ∈ S → b ∈ S → c ∈ S → d ∈ S → 
    a + b = c + d → ({a, b} : Finset G) = {c, d}

/-- The sumset representation function r_{S,S}(g) = |{(a,b) ∈ S × S : a + b = g}| -/
def repFunction (S : Finset G) (g : G) : ℕ :=
  ((S ×ˢ S).filter (fun p => p.1 + p.2 = g)).card

/-- Bounding r_{S,S}(g) ≤ 2 for any Sidon set S -/
theorem repFunction_bound_of_sidon {S : Finset G} (hS : IsSidon S) (g : G) :
    repFunction S g ≤ 2 := by
  unfold repFunction
  let F := (S ×ˢ S).filter (fun p => p.1 + p.2 = g)
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
      rw [Finset.pair_eq_pair_iff] at h_set_eq
      rcases h_set_eq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Finset.mem_insert_self (a, b) {(b, a)}
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self (b, a))
    have h_card := Finset.card_le_card h_sub
    have h_pair_card : ({(a, b), (b, a)} : Finset (G × G)).card ≤ 2 := Finset.card_insert_le (a, b) {(b, a)}
    omega
  · rw [Finset.not_nonempty_iff_eq_empty] at hF
    rw [hF, Finset.card_empty]
    omega

/-! ### 2. Representation Moments and Additive Energy -/

/-- Sumset domain definition -/
def sumSet (S : Finset G) : Finset G :=
  (S ×ˢ S).image (fun p => p.1 + p.2)

/-- k-th moment of the representation function M_k(S) = ∑_g r_{S,S}(g)^k -/
def representationMoment (S : Finset G) (k : ℕ) : ℕ :=
  ∑ g ∈ sumSet S, (repFunction S g)^k

/-- Additive Energy E(S,S) defined as the 2nd moment M_2(S) -/
def additiveEnergy (S : Finset G) : ℕ :=
  representationMoment S 2

/-- 8th Moment M_8(S) -/
def moment8 (S : Finset G) : ℕ :=
  representationMoment S 8

/-- Monotonicity theorem for representation moments: M_k(S) ≤ M_m(S) for 1 ≤ k ≤ m -/
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

/-- Direct inequality linking Additive Energy E(S,S) to the 8th Moment M_8(S) -/
theorem additiveEnergy_le_moment8 (S : Finset G) :
    additiveEnergy S ≤ moment8 S := by
  exact moment_le_moment_of_le (by decide) (by decide)

/-! ### 3. Fiber Conservation and Degree Stability -/

/-- Preimage fiber of a map f -/
def fiber (f : X → Y) (y : Y) : Finset X :=
  Finset.univ.filter (fun x => f x = y)

/-- Cardinality of preimage fiber -/
def fiberDegree (f : X → Y) (y : Y) : ℕ :=
  (fiber f y).card

/-- Definition of generic target point of constant degree d -/
def IsGenericPoint (f : X → Y) (d : ℕ) (y : Y) : Prop :=
  fiberDegree f y = d

/-- Invariance of fiber degree across any two points in the generic target domain -/
theorem generic_fiber_degree_stable 
    (f : X → Y) (d : ℕ) (U : Finset Y)
    (hU : ∀ y ∈ U, IsGenericPoint f d y) (y1 y2 : Y)
    (hy1 : y1 ∈ U) (hy2 : y2 ∈ U) :
    fiberDegree f y1 = fiberDegree f y2 := by
  have h1 : fiberDegree f y1 = d := hU y1 hy1
  have h2 : fiberDegree f y2 = d := hU y2 hy2
  rw [h1, h2]

/-- Fiber sum partition identity: Total fiber sizes sum to |X| -/
theorem sum_fiberDegrees_eq_card (f : X → Y) :
    ∑ y : Y, fiberDegree f y = Fintype.card X := by
  unfold fiberDegree fiber
  rw [← Finset.card_univ]
  exact Finset.sum_card_fiberwise_eq_card_univ f
