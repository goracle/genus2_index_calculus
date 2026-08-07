import Mathlib

set_option linter.style.header false
set_option linter.unusedSimpArgs false

namespace Genus2Lean

variable {k K L : Type*} [Field k] [Field K] [Field L]
variable [Algebra (Polynomial k) K] [IsFractionRing (Polynomial k) K]
variable [Algebra (Polynomial k) L] [Algebra K L] [IsScalarTower (Polynomial k) K L]

structure HyperellipticData (k : Type*) [Field k] where
  f : Polynomial k

variable (H : HyperellipticData k) (yL : L)

/-- Characterization of membership in the integral closure via polynomial coefficients. -/
axiom mem_integralClosure_iff_poly_coefficients
    (pairL_exists : ∀ x : L, ∃ a b : K, x = (algebraMap K L) a + (algebraMap K L) b * yL)
    (pairL_injective : ∀ a₁ b₁ a₂ b₂ : K,
      (algebraMap K L) a₁ + (algebraMap K L) b₁ * yL =
        (algebraMap K L) a₂ + (algebraMap K L) b₂ * yL →
        a₁ = a₂ ∧ b₁ = b₂)
    (yL_sq : yL ^ 2 = (algebraMap (Polynomial k) L) H.f)
    (h2 : (2 : k) ≠ 0)
    (x : L) :
    x ∈ integralClosure (Polynomial k) L ↔
      ∃ (a b : Polynomial k), x = algebraMap (Polynomial k) L a + algebraMap (Polynomial k) L b * yL

/-- The integral closure of k[X] in L is spanned as a k[X]-module by 1 and yL. -/
theorem integralClosure_eq_span
    (pairL_exists : ∀ x : L,
      ∃ a b : K, x = (algebraMap K L) a + (algebraMap K L) b * yL)
    (pairL_injective : ∀ a₁ b₁ a₂ b₂ : K,
      (algebraMap K L) a₁ + (algebraMap K L) b₁ * yL =
        (algebraMap K L) a₂ + (algebraMap K L) b₂ * yL →
        a₁ = a₂ ∧ b₁ = b₂)
    (yL_sq : yL ^ 2 = (algebraMap (Polynomial k) L) H.f)
    (h2 : (2 : k) ≠ 0) :
    (integralClosure (Polynomial k) L).toSubmodule =
      Submodule.span (Polynomial k) {1, yL} := by
  ext x
  rw [Subalgebra.mem_toSubmodule]
  rw [mem_integralClosure_iff_poly_coefficients H yL pairL_exists pairL_injective yL_sq h2]
  rw [Submodule.mem_span_pair]
  constructor
  · rintro ⟨a, b, rfl⟩
    refine ⟨a, b, ?_⟩
    rw [Algebra.smul_def, mul_one, Algebra.smul_def]
  · rintro ⟨a, b, hx⟩
    refine ⟨a, b, ?_⟩
    rw [Algebra.smul_def, mul_one, Algebra.smul_def] at hx
    exact hx.symm

end Genus2Lean
