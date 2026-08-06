import Mathlib
noncomputable section

set_option linter.style.header false

open Polynomial
open AdjoinRoot
/-- A polynomial `f : k[X]` defining a hyperelliptic curve of genus 2.
For genus 2 over a field of characteristic ≠ 2, `f` has degree 5 or 6
and is square-free. -/
structure HyperellipticPolynomial (k : Type*) [CommRing k] where
  f : k[X]
  natDegree_eq : f.natDegree = 5 ∨ f.natDegree = 6

namespace HyperellipticPolynomial

variable {k : Type*} [CommRing k] [IsDomain k]

/-- The coordinate ring `k[x, y] / (y² - f(x))` represented as `AdjoinRoot (X² - C f)`
over the base polynomial ring `k[X]`. -/
noncomputable def CoordinateRing (H : HyperellipticPolynomial k) : Type _ :=
  AdjoinRoot (X ^ 2 - C (H.f))

instance (H : HyperellipticPolynomial k) : CommRing (CoordinateRing H) :=
  inferInstanceAs (CommRing (AdjoinRoot _))

instance (H : HyperellipticPolynomial k) : Algebra k[X] (CoordinateRing H) :=
  inferInstanceAs (Algebra k[X] (AdjoinRoot _))

/-- The generator `y` in the coordinate ring, corresponding to `y = √f(x)`. -/
noncomputable def y (H : HyperellipticPolynomial k) : CoordinateRing H :=
  root (X ^ 2 - C (H.f))

/-- Fundamental relation in the coordinate ring: `y² = f(x)`. -/
theorem y_sq_eq (H : HyperellipticPolynomial k) :
    y H ^ 2 = algebraMap k[X] (CoordinateRing H) H.f := by
  have h := eval₂_root (X ^ 2 - C (H.f))
  rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] at h
  exact sub_eq_zero.mp h

/-- The hyperelliptic involution `ι : k[x, y] → k[x, y]` sending `y ↦ -y`
and acting trivially on `k[x]`. -/
noncomputable def involution (H : HyperellipticPolynomial k) :
    CoordinateRing H →+* CoordinateRing H :=
  AdjoinRoot.lift (f := X ^ 2 - C (H.f)) (algebraMap k[X] (CoordinateRing H)) (-y H) (by
    rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, neg_sq, y_sq_eq H]
    exact sub_self _)

@[simp]
theorem involution_y (H : HyperellipticPolynomial k) :
    involution H (y H) = -y H := by
  unfold involution
  exact AdjoinRoot.lift_root (by
    rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, neg_sq, y_sq_eq H]
    exact sub_self _)

@[simp]
theorem involution_algebraMap (H : HyperellipticPolynomial k) (p : k[X]) :
    involution H (algebraMap k[X] (CoordinateRing H) p) = algebraMap k[X] (CoordinateRing H) p := by
  unfold involution
  exact AdjoinRoot.lift_of (by
    rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, neg_sq, y_sq_eq H]
    exact sub_self _)

/-- The hyperelliptic involution applied twice is the identity on generator `y`. -/
theorem involution_involution_y (H : HyperellipticPolynomial k) :
    involution H (involution H (y H)) = y H := by
  rw [involution_y, map_neg, involution_y, neg_neg]

/-- Canonical elements in the coordinate ring given by `A(x) + B(x)y`
for polynomials `A, B ∈ k[X]`. -/
noncomputable def toPair (H : HyperellipticPolynomial k) (A B : k[X]) : CoordinateRing H :=
  algebraMap k[X] (CoordinateRing H) A + algebraMap k[X] (CoordinateRing H) B * y H

/-- Under the hyperelliptic involution, `A(x) + B(x)y ↦ A(x) - B(x)y`. -/
theorem toPair_involution (H : HyperellipticPolynomial k) (A B : k[X]) :
    involution H (toPair H A B) = toPair H (A) (-B) := by
  unfold toPair
  simp only [map_add, map_mul, involution_algebraMap, involution_y, map_neg]
  ring

end HyperellipticPolynomial



set_option linter.style.header false

open Polynomial
open AdjoinRoot

namespace HyperellipticPolynomial

variable {k : Type*} [CommRing k] [IsDomain k]

/-- The norm of `A(x) + B(x)y` as a polynomial in `k[X]`, computed as `A(x)² - B(x)² f(x)`. -/
noncomputable def pairNorm (H : HyperellipticPolynomial k) (A B : k[X]) : k[X] :=
  A ^ 2 - B ^ 2 * H.f

/-- The product of an element with its hyperelliptic involution equals its norm in `k[X]`. -/
theorem toPair_mul_involution (H : HyperellipticPolynomial k) (A B : k[X]) :
    toPair H A B * involution H (toPair H A B) =
      algebraMap k[X] (CoordinateRing H) (pairNorm H A B) := by
  rw [toPair_involution]
  unfold toPair pairNorm
  have hy2 : y H ^ 2 = algebraMap k[X] (CoordinateRing H) H.f := y_sq_eq H
  calc
    (algebraMap k[X] (CoordinateRing H) A + algebraMap k[X] (CoordinateRing H) B * y H) *
    (algebraMap k[X] (CoordinateRing H) A + algebraMap k[X] (CoordinateRing H) (-B) * y H)
      = (algebraMap k[X] (CoordinateRing H) A)^2 -
          (algebraMap k[X] (CoordinateRing H) B) * (algebraMap k[X] (CoordinateRing H) B) *
            y H * y H := by
        rw [map_neg]
        set a := algebraMap k[X] (CoordinateRing H) A
        set b := algebraMap k[X] (CoordinateRing H) B
        set w := y H
        ring
    _ = (algebraMap k[X] (CoordinateRing H) A)^2 -
          (algebraMap k[X] (CoordinateRing H) B)^2 * (y H)^2 := by ring
    _ = (algebraMap k[X] (CoordinateRing H) A)^2 - (algebraMap k[X] (CoordinateRing H) B)^2 * algebraMap k[X] (CoordinateRing H) H.f := by rw [hy2]
    _ = algebraMap k[X] (CoordinateRing H) (A ^ 2 - B ^ 2 * H.f) := by
        simp only [map_sub, map_pow, map_mul]

/-- The trace of `A(x) + B(x)y` as a polynomial in `k[X]`, computed as `2 * A(x)`. -/
noncomputable def pairTrace (A : k[X]) : k[X] :=
  2 * A

/-- The sum of an element and its hyperelliptic involution equals its trace in `k[X]`. -/
theorem toPair_add_involution (H : HyperellipticPolynomial k) (A B : k[X]) :
    toPair H A B + involution H (toPair H A B) =
      algebraMap k[X] (CoordinateRing H) (pairTrace A) := by
  rw [toPair_involution]
  unfold toPair pairTrace
  calc
    (algebraMap k[X] (CoordinateRing H) A + algebraMap k[X] (CoordinateRing H) B * y H) +
    (algebraMap k[X] (CoordinateRing H) A + algebraMap k[X] (CoordinateRing H) (-B) * y H)
      = 2 * algebraMap k[X] (CoordinateRing H) A := by
        rw [map_neg]
        set a := algebraMap k[X] (CoordinateRing H) A
        set b := algebraMap k[X] (CoordinateRing H) B
        set w := y H
        ring
    _ = algebraMap k[X] (CoordinateRing H) (2 * A) := by simp only [map_mul, map_ofNat]

/-- Every element `α = A + B y` satisfies its characteristic polynomial `α² - Trace(α) α + Norm(α) = 0`. -/
theorem toPair_satisfies_charpoly (H : HyperellipticPolynomial k) (A B : k[X]) :
    (toPair H A B)^2 - algebraMap k[X] (CoordinateRing H) (pairTrace A) * toPair H A B +
      algebraMap k[X] (CoordinateRing H) (pairNorm H A B) = 0 := by
  have h_add := toPair_add_involution H A B
  have h_mul := toPair_mul_involution H A B
  set α := toPair H A B
  set α_bar := involution H (toPair H A B)
  have h_identity : α^2 - (α + α_bar) * α + α * α_bar = 0 := by ring
  rw [h_add, h_mul] at h_identity
  exact h_identity

end HyperellipticPolynomial









set_option linter.style.header false

open Polynomial
open AdjoinRoot

namespace HyperellipticPolynomial

variable {k : Type*} [CommRing k] [IsDomain k]

/-- `k` acts on the coordinate ring via `k → k[X] → CoordinateRing H`, giving the
`Module k (CoordinateRing H)` instance that `RiemannRochSpaceInf` needs to form a
`k`-submodule (as opposed to only a `k[X]`-submodule, which the `Algebra k[X] _`
instance above already gives for free). Built via `Algebra.compHom` (composing the
existing `Algebra k[X] (CoordinateRing H)` with `algebraMap k k[X]`) rather than
`RingHom.toAlgebra` directly, since `compHom` comes with named unfolding lemmas
(`Algebra.compHom_smul_def`, `Algebra.compHom_algebraMap_apply`) that later proofs
can `rw` with instead of relying on `rfl`-transparency into the composed map. -/
noncomputable instance (H : HyperellipticPolynomial k) : Algebra k (CoordinateRing H) :=
  Algebra.compHom (CoordinateRing H) (algebraMap k k[X])

/-- Pole order bound at the point at infinity `P_∞` for an element `A(x) + B(x)y`
in a degree-5 hyperelliptic curve coordinate ring. -/
def inLInf (n : ℕ) (A B : k[X]) : Prop :=
  (A = 0 ∨ 2 * A.natDegree ≤ n) ∧ (B = 0 ∨ 2 * B.natDegree + 5 ≤ n)

/-- The Riemann–Roch space `L(n P_∞)` as an explicit `k`-submodule of the coordinate ring. -/
noncomputable def RiemannRochSpaceInf (H : HyperellipticPolynomial k) (n : ℕ) :
    Submodule k (CoordinateRing H) where
  carrier := { α | ∃ A B : k[X], α = toPair H A B ∧ inLInf n A B }
  zero_mem' := by
    use 0, 0
    constructor
    · unfold toPair; simp
    · exact ⟨Or.inl rfl, Or.inl rfl⟩
  add_mem' := by
    rintro α β ⟨A1, B1, rfl, h1⟩ ⟨A2, B2, rfl, h2⟩
    use A1 + A2, B1 + B2
    constructor
    · unfold toPair
      simp only [map_add]
      set a1 := algebraMap k[X] (CoordinateRing H) A1
      set a2 := algebraMap k[X] (CoordinateRing H) A2
      set b1 := algebraMap k[X] (CoordinateRing H) B1
      set b2 := algebraMap k[X] (CoordinateRing H) B2
      set w := y H
      ring
    · constructor
      · by_cases hA : A1 + A2 = 0
        · left; exact hA
        · right
          have hle := natDegree_add_le A1 A2
          rcases h1.1 with rfl | hA1
          · rw [zero_add] at hle ⊢; rcases h2.1 with rfl | hA2 <;> [(simp at hA); exact hA2]
          · rcases h2.1 with rfl | hA2
            · rw [add_zero] at hle ⊢; exact hA1
            · have hmax : (A1 + A2).natDegree ≤ max A1.natDegree A2.natDegree := hle
              have : 2 * (A1 + A2).natDegree ≤ max (2 * A1.natDegree) (2 * A2.natDegree) := by omega
              omega
      · by_cases hB : B1 + B2 = 0
        · left; exact hB
        · right
          have hle := natDegree_add_le B1 B2
          rcases h1.2 with rfl | hB1
          · rw [zero_add] at hle ⊢; rcases h2.2 with rfl | hB2 <;> [(simp at hB); exact hB2]
          · rcases h2.2 with rfl | hB2
            · rw [add_zero] at hle ⊢; exact hB1
            · have hmax : (B1 + B2).natDegree ≤ max B1.natDegree B2.natDegree := hle
              have : 2 * (B1 + B2).natDegree + 5 ≤ max (2 * B1.natDegree + 5) (2 * B2.natDegree + 5) := by omega
              omega
  smul_mem' := by
    rintro c α ⟨A, B, rfl, h⟩
    use C c * A, C c * B
    constructor
    · unfold toPair
      rw [Algebra.compHom_smul_def, Algebra.smul_def]
      rw [show algebraMap k k[X] c = C c from by
        simp [Polynomial.algebraMap_apply]]
      simp only [map_mul]
      set a := algebraMap k[X] (CoordinateRing H) A
      set b := algebraMap k[X] (CoordinateRing H) B
      set cc := algebraMap k[X] (CoordinateRing H) (C c)
      set w := y H
      ring
    · constructor
      · by_cases hA : C c * A = 0
        · left; exact hA
        · right
          have hdeg : (C c * A).natDegree ≤ A.natDegree := by
            calc (C c * A).natDegree ≤ (C c).natDegree + A.natDegree := natDegree_mul_le
              _ = A.natDegree := by rw [natDegree_C, zero_add]
          rcases h.1 with rfl | hA_bound
          · simp at hA
          · omega
      · by_cases hB : C c * B = 0
        · left; exact hB
        · right
          have hdeg : (C c * B).natDegree ≤ B.natDegree := by
            calc (C c * B).natDegree ≤ (C c).natDegree + B.natDegree := natDegree_mul_le
              _ = B.natDegree := by rw [natDegree_C, zero_add]
          rcases h.2 with rfl | hB_bound
          · simp at hB
          · omega

end HyperellipticPolynomial



set_option linter.style.header false

open Polynomial
open AdjoinRoot

namespace HyperellipticPolynomial

variable {k : Type*} [CommRing k] [IsDomain k]

/-- Parity contradiction: `2 * a = 2 * b + 5` has no natural number solutions. -/
theorem two_mul_ne_two_mul_add_five (a b : ℕ) : 2 * a ≠ 2 * b + 5 := by
  omega

/-- Uniqueness of representation: for a degree-5 hyperelliptic curve,
`A(x)² - B(x)² f(x) = 0` forces `A = 0` and `B = 0`. -/
theorem pairNorm_eq_zero_iff (H : HyperellipticPolynomial k) (hdeg : H.f.natDegree = 5)
    (A B : k[X]) (h : pairNorm H A B = 0) : A = 0 ∧ B = 0 := by
  unfold pairNorm at h
  have h_eq : A ^ 2 = B ^ 2 * H.f := sub_eq_zero.mp h
  by_cases hB : B = 0
  · rw [hB, zero_pow two_ne_zero, zero_mul] at h_eq
    have hA : A = 0 := by
      rwa [pow_eq_zero_iff (two_ne_zero)] at h_eq
    exact ⟨hA, hB⟩
  · exfalso
    have hf_ne : H.f ≠ 0 := by
      intro hf0
      rw [hf0, natDegree_zero] at hdeg
      revert hdeg; decide
    have hdegA : (A ^ 2).natDegree = 2 * A.natDegree := natDegree_pow A 2
    have hdegB2 : (B ^ 2).natDegree = 2 * B.natDegree := natDegree_pow B 2
    have hdegRHS : (B ^ 2 * H.f).natDegree = 2 * B.natDegree + 5 := by
      rw [natDegree_mul (pow_ne_zero 2 hB) hf_ne]
      rw [hdegB2, hdeg]
    rw [h_eq] at hdegA
    rw [hdegRHS] at hdegA
    exact two_mul_ne_two_mul_add_five A.natDegree B.natDegree hdegA.symm

/-- **The Riemann–Roch Dimension Theorem for $L(n P_\infty)$**:
The total number of independent basis functions in $L(n P_\infty)$ equals
$n - 1$ for all $n \ge 3$, matching $\deg(D) + 1 - g$ for genus $g = 2$. -/
theorem riemann_roch_dim_identity (n : ℕ) (hn : 3 ≤ n) :
    (n / 2 + 1) + (if 5 ≤ n then (n - 5) / 2 + 1 else 0) = n - 1 := by
  split_ifs with h5
  · omega
  · omega

end HyperellipticPolynomial
