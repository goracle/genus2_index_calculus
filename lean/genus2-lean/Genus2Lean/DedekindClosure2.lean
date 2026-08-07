import Mathlib
import Genus2Lean.HyperellipticFunctionField
import Genus2Lean.AffinePoints
import Genus2Lean.DivisorClassGroup
import Genus2Lean.PrincipalDivisors

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
  (pairL_injective : ∀ a₁ b₁ a₂ b₂ : FractionRing k[X],
    (algebraMap (FractionRing k[X]) L) a₁ + (algebraMap (FractionRing k[X]) L) b₁ * yL =
      (algebraMap (FractionRing k[X]) L) a₂ + (algebraMap (FractionRing k[X]) L) b₂ * yL →
      a₁ = a₂ ∧ b₁ = b₂)
  (yL_sq : yL ^ 2 = (algebraMap k[X] L) H.f)

local notation "K" => FractionRing k[X]

section Coeffs

noncomputable def coeffA (x : L) : K := (pairL_exists x).choose
noncomputable def coeffB (x : L) : K := (pairL_exists x).choose_spec.choose

theorem coeffAB_spec (x : L) :
    x = (algebraMap K L) (coeffA yL pairL_exists x) +
      (algebraMap K L) (coeffB yL pairL_exists x) * yL :=
  (pairL_exists x).choose_spec.choose_spec

theorem coeffAB_unique (pairL_injective : ∀ a₁ b₁ a₂ b₂ : K,
    (algebraMap K L) a₁ + (algebraMap K L) b₁ * yL =
      (algebraMap K L) a₂ + (algebraMap K L) b₂ * yL →
      a₁ = a₂ ∧ b₁ = b₂)
    (x : L) (a b : K)
    (hx : x = (algebraMap K L) a + (algebraMap K L) b * yL) :
    a = coeffA yL pairL_exists x ∧ b = coeffB yL pairL_exists x :=
  pairL_injective a b _ _ (hx.symm.trans (coeffAB_spec yL pairL_exists x))

theorem coeffA_of_eq (pairL_injective : ∀ a₁ b₁ a₂ b₂ : K,
    (algebraMap K L) a₁ + (algebraMap K L) b₁ * yL =
      (algebraMap K L) a₂ + (algebraMap K L) b₂ * yL →
      a₁ = a₂ ∧ b₁ = b₂) (a b : K) :
    coeffA yL pairL_exists ((algebraMap K L) a + (algebraMap K L) b * yL) = a :=
  ((coeffAB_unique yL pairL_exists pairL_injective _ a b rfl).1).symm

theorem coeffB_of_eq (pairL_injective : ∀ a₁ b₁ a₂ b₂ : K,
    (algebraMap K L) a₁ + (algebraMap K L) b₁ * yL =
      (algebraMap K L) a₂ + (algebraMap K L) b₂ * yL →
      a₁ = a₂ ∧ b₁ = b₂) (a b : K) :
    coeffB yL pairL_exists ((algebraMap K L) a + (algebraMap K L) b * yL) = b :=
  ((coeffAB_unique yL pairL_exists pairL_injective _ a b rfl).2).symm

end Coeffs

theorem yL_sq' (yL_sq : yL ^ 2 = (algebraMap k[X] L) H.f) :
    yL ^ 2 = (algebraMap K L) (algebraMap k[X] K H.f) := by
  rw [← IsScalarTower.algebraMap_apply k[X] K L]
  exact yL_sq

noncomputable def involutionLFun (x : L) : L :=
  (algebraMap K L) (coeffA yL pairL_exists x) -
    (algebraMap K L) (coeffB yL pairL_exists x) * yL

theorem involutionLFun_pair (pairL_injective : ∀ a₁ b₁ a₂ b₂ : K,
    (algebraMap K L) a₁ + (algebraMap K L) b₁ * yL =
      (algebraMap K L) a₂ + (algebraMap K L) b₂ * yL →
      a₁ = a₂ ∧ b₁ = b₂) (a b : K) :
    involutionLFun yL pairL_exists
      ((algebraMap K L) a + (algebraMap K L) b * yL) =
      (algebraMap K L) a - (algebraMap K L) b * yL := by
  unfold involutionLFun
  rw [coeffA_of_eq yL pairL_exists pairL_injective,
    coeffB_of_eq yL pairL_exists pairL_injective]

theorem involutionLFun_add (pairL_injective : ∀ a₁ b₁ a₂ b₂ : K,
    (algebraMap K L) a₁ + (algebraMap K L) b₁ * yL =
      (algebraMap K L) a₂ + (algebraMap K L) b₂ * yL →
      a₁ = a₂ ∧ b₁ = b₂) (x x' : L) :
    involutionLFun yL pairL_exists (x + x') =
      involutionLFun yL pairL_exists x + involutionLFun yL pairL_exists x' := by
  have hx := coeffAB_spec yL pairL_exists x
  have hx' := coeffAB_spec yL pairL_exists x'
  set a := coeffA yL pairL_exists x
  set b := coeffB yL pairL_exists x
  set a' := coeffA yL pairL_exists x'
  set b' := coeffB yL pairL_exists x'
  have hsum : x + x' = (algebraMap K L) (a + a') + (algebraMap K L) (b + b') * yL := by
    rw [hx, hx']; simp only [map_add]; ring
  rw [hsum]
  rw [involutionLFun_pair yL pairL_exists pairL_injective]
  rw [hx, hx']
  rw [involutionLFun_pair yL pairL_exists pairL_injective]
  rw [involutionLFun_pair yL pairL_exists pairL_injective]
  simp only [map_add, map_sub]
  ring

theorem involutionLFun_mul (pairL_injective : ∀ a₁ b₁ a₂ b₂ : K,
    (algebraMap K L) a₁ + (algebraMap K L) b₁ * yL =
      (algebraMap K L) a₂ + (algebraMap K L) b₂ * yL →
      a₁ = a₂ ∧ b₁ = b₂)
    (yL_sq : yL ^ 2 = (algebraMap k[X] L) H.f) (x x' : L) :
    involutionLFun yL pairL_exists (x * x') =
      involutionLFun yL pairL_exists x * involutionLFun yL pairL_exists x' := by
  have hx := coeffAB_spec yL pairL_exists x
  have hx' := coeffAB_spec yL pairL_exists x'
  set a := coeffA yL pairL_exists x
  set b := coeffB yL pairL_exists x
  set a' := coeffA yL pairL_exists x'
  set b' := coeffB yL pairL_exists x'
  have hy2 := yL_sq' H yL yL_sq
  have hprod : x * x' = (algebraMap K L) (a * a' + b * b' * (algebraMap k[X] K H.f)) +
      (algebraMap K L) (a * b' + a' * b) * yL := by
    rw [hx, hx']
    have expand : ((algebraMap K L) a + (algebraMap K L) b * yL) *
        ((algebraMap K L) a' + (algebraMap K L) b' * yL) =
        (algebraMap K L) a * (algebraMap K L) a' +
          (algebraMap K L) b * (algebraMap K L) b' * yL ^ 2 +
          ((algebraMap K L) a * (algebraMap K L) b' +
            (algebraMap K L) a' * (algebraMap K L) b) * yL := by ring
    rw [expand, hy2]
    simp only [map_add, map_mul]
  have hinv : involutionLFun yL pairL_exists x * involutionLFun yL pairL_exists x' =
      (algebraMap K L) (a * a' + b * b' * (algebraMap k[X] K H.f)) -
        (algebraMap K L) (a * b' + a' * b) * yL := by
    rw [hx, hx']
    rw [involutionLFun_pair yL pairL_exists pairL_injective]
    rw [involutionLFun_pair yL pairL_exists pairL_injective]
    have expand : ((algebraMap K L) a - (algebraMap K L) b * yL) *
        ((algebraMap K L) a' - (algebraMap K L) b' * yL) =
        (algebraMap K L) a * (algebraMap K L) a' +
          (algebraMap K L) b * (algebraMap K L) b' * yL ^ 2 -
          ((algebraMap K L) a * (algebraMap K L) b' +
            (algebraMap K L) a' * (algebraMap K L) b) * yL := by ring
    rw [expand, hy2]
    simp only [map_add, map_sub, map_mul]
  rw [hprod]
  rw [involutionLFun_pair yL pairL_exists pairL_injective]
  rw [hinv]

theorem involutionLFun_one (pairL_injective : ∀ a₁ b₁ a₂ b₂ : K,
    (algebraMap K L) a₁ + (algebraMap K L) b₁ * yL =
      (algebraMap K L) a₂ + (algebraMap K L) b₂ * yL →
      a₁ = a₂ ∧ b₁ = b₂) :
    involutionLFun yL pairL_exists (1 : L) = 1 := by
  have h1 : (1 : L) = (algebraMap K L) (1 : K) + (algebraMap K L) (0 : K) * yL := by
    simp
  rw [h1, involutionLFun_pair yL pairL_exists pairL_injective]
  simp

noncomputable def involutionL (pairL_injective : ∀ a₁ b₁ a₂ b₂ : K,
    (algebraMap K L) a₁ + (algebraMap K L) b₁ * yL =
      (algebraMap K L) a₂ + (algebraMap K L) b₂ * yL →
      a₁ = a₂ ∧ b₁ = b₂) (yL_sq : yL ^ 2 = (algebraMap k[X] L) H.f) : L →+* L where
  toFun := involutionLFun yL pairL_exists
  map_one' := involutionLFun_one yL pairL_exists pairL_injective
  map_mul' := involutionLFun_mul H yL pairL_exists pairL_injective yL_sq
  map_zero' := by
    have h0 : (0 : L) = (algebraMap K L) (0 : K) + (algebraMap K L) (0 : K) * yL := by simp
    rw [h0, involutionLFun_pair yL pairL_exists pairL_injective]; simp
  map_add' := involutionLFun_add yL pairL_exists pairL_injective

@[simp]
theorem involutionL_yL (pairL_injective : ∀ a₁ b₁ a₂ b₂ : K,
    (algebraMap K L) a₁ + (algebraMap K L) b₁ * yL =
      (algebraMap K L) a₂ + (algebraMap K L) b₂ * yL →
      a₁ = a₂ ∧ b₁ = b₂) (yL_sq : yL ^ 2 = (algebraMap k[X] L) H.f) :
    involutionL H yL pairL_exists pairL_injective yL_sq yL = -yL := by
  have h : (algebraMap K L) (0 : K) + (algebraMap K L) (1 : K) * yL = yL := by simp
  have h_inv := involutionLFun_pair yL pairL_exists pairL_injective 0 1
  rw [h] at h_inv
  change involutionLFun yL pairL_exists yL = -yL
  rw [h_inv]
  simp

@[simp]
theorem involutionL_algebraMap (pairL_injective : ∀ a₁ b₁ a₂ b₂ : K,
    (algebraMap K L) a₁ + (algebraMap K L) b₁ * yL =
      (algebraMap K L) a₂ + (algebraMap K L) b₂ * yL →
      a₁ = a₂ ∧ b₁ = b₂) (yL_sq : yL ^ 2 = (algebraMap k[X] L) H.f) (c : K) :
    involutionL H yL pairL_exists pairL_injective yL_sq ((algebraMap K L) c) = (algebraMap K L) c := by
  have h : (algebraMap K L) c + (algebraMap K L) (0 : K) * yL = (algebraMap K L) c := by simp
  have h_inv := involutionLFun_pair yL pairL_exists pairL_injective c 0
  rw [h] at h_inv
  change involutionLFun yL pairL_exists ((algebraMap K L) c) = (algebraMap K L) c
  rw [h_inv]
  simp

end HyperellipticPolynomial
