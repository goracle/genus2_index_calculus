/-
Copyright (c) 2026 Claire H. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claire H
-/
import Mathlib
import Genus2Lean.HyperellipticFunctionField
import Genus2Lean.AffinePoints
import Genus2Lean.DivisorClassGroup
import Genus2Lean.DedekindClosure2
import Genus2Lean.DedekindClosure3

/-!
# Quadratic Minimal Polynomials and Integrality for Hyperelliptic Fields

This module proves that every element $x \in L$ satisfies a quadratic relation defined 
by its `traceLFun` and `normLFun`, and establishes integrality over $k[X]$.
-/

noncomputable section

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.show false
set_option linter.unusedSectionVars false

open Polynomial

namespace HyperellipticPolynomial

variable {k : Type*} [Field k] (H : HyperellipticPolynomial k)

variable {L : Type*} [Field L] [Algebra (CoordinateRing H) L]
  [IsFractionRing (CoordinateRing H) L] [Algebra k[X] L] [IsScalarTower k[X] (CoordinateRing H) L]
  [Algebra (FractionRing k[X]) L] [IsScalarTower k[X] (FractionRing k[X]) L]
  (yL : L) (pairL_exists : ∀ x : L,
    ∃ a b : FractionRing k[X], x = (algebraMap (FractionRing k[X]) L) a +
      (algebraMap (FractionRing k[X]) L) b * yL)

local notation "K" => FractionRing k[X]

/-- Every element `x : L` satisfies `x^2 - trace(x)*x + norm(x) = 0`. -/
theorem elem_sq_sub_trace_mul_add_norm_eq_zero
    (pairL_injective : ∀ a₁ b₁ a₂ b₂ : K,
      (algebraMap K L) a₁ + (algebraMap K L) b₁ * yL =
        (algebraMap K L) a₂ + (algebraMap K L) b₂ * yL →
        a₁ = a₂ ∧ b₁ = b₂)
    (yL_sq : yL ^ 2 = (algebraMap k[X] L) H.f)
    (x : L) :
    x ^ 2 - (algebraMap K L) (traceLFun yL pairL_exists x) * x +
      (algebraMap K L) (normLFun H yL pairL_exists x) = 0 := by
  have h_trace := algebraMap_traceLFun_eq H yL pairL_exists pairL_injective yL_sq x
  have h_norm := algebraMap_normLFun_eq H yL pairL_exists pairL_injective yL_sq x
  rw [h_trace, h_norm]
  generalize involutionL H yL pairL_exists pairL_injective yL_sq x = x_inv
  ring

/-- An element `x : L` is integral over `k[X]` if its trace and norm lie in `k[X]`. -/
theorem isIntegral_of_trace_norm_mem
    (pairL_injective : ∀ a₁ b₁ a₂ b₂ : K,
      (algebraMap K L) a₁ + (algebraMap K L) b₁ * yL =
        (algebraMap K L) a₂ + (algebraMap K L) b₂ * yL →
        a₁ = a₂ ∧ b₁ = b₂)
    (yL_sq : yL ^ 2 = (algebraMap k[X] L) H.f)
    (x : L)
    (a b : k[X])
    (htr : traceLFun yL pairL_exists x = algebraMap k[X] K a)
    (hnorm : normLFun H yL pairL_exists x = algebraMap k[X] K b) :
    IsIntegral k[X] x := by
  have h_eq := elem_sq_sub_trace_mul_add_norm_eq_zero H yL pairL_exists pairL_injective yL_sq x
  rw [htr, hnorm] at h_eq
  have h_cast1 : (algebraMap K L) (algebraMap k[X] K a) = algebraMap k[X] L a := by
    rw [← IsScalarTower.algebraMap_apply]
  have h_cast2 : (algebraMap K L) (algebraMap k[X] K b) = algebraMap k[X] L b := by
    rw [← IsScalarTower.algebraMap_apply]
  rw [h_cast1, h_cast2] at h_eq
  have h_deg2 : (X ^ 2 : Polynomial k[X]).degree = 2 := degree_X_pow 2
  have hq : (- C a * X + C b : Polynomial k[X]).degree < (X ^ 2 : Polynomial k[X]).degree := by
    rw [h_deg2]
    calc (- C a * X + C b).degree
      _ ≤ max (- C a * X).degree (C b).degree := degree_add_le _ _
      _ ≤ 1 := by
        refine max_le ?_ (degree_C_le.trans (by decide))
        calc (- C a * X).degree
          _ ≤ (- C a).degree + X.degree := degree_mul_le _ _
          _ ≤ 0 + 1 := add_le_add (by rw [← C_neg]; exact degree_C_le) degree_X_le
          _ = 1 := by rfl
      _ < 2 := by decide
  have h_monic_add : (X ^ 2 + (- C a * X + C b) : Polynomial k[X]).Monic := by
    dsimp [Monic]
    rw [add_comm]
    rw [leadingCoeff_add_of_degree_lt hq]
    exact monic_X_pow 2
  have h_monic : (X ^ 2 - C a * X + C b : Polynomial k[X]).Monic := by
    convert h_monic_add using 1
    ring
  use X ^ 2 - C a * X + C b
  refine ⟨h_monic, ?_⟩
  simp only [eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C]
  exact h_eq

end HyperellipticPolynomial
