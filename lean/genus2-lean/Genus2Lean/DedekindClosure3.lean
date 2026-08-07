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

/-!
# Field Norm and Trace for Hyperelliptic Function Fields

This module establishes the field norm and trace maps down to K = Frac(k[X]) for
hyperelliptic function fields, proving multiplicative properties and relation to the involution.
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
  (pairL_injective : ∀ a₁ b₁ a₂ b₂ : FractionRing k[X],
    (algebraMap (FractionRing k[X]) L) a₁ + (algebraMap (FractionRing k[X]) L) b₁ * yL =
      (algebraMap (FractionRing k[X]) L) a₂ + (algebraMap (FractionRing k[X]) L) b₂ * yL →
      a₁ = a₂ ∧ b₁ = b₂)
  (yL_sq : yL ^ 2 = (algebraMap k[X] L) H.f)

local notation "K" => FractionRing k[X]

noncomputable def traceLFun (x : L) : K :=
  2 * coeffA yL pairL_exists x

noncomputable def normLFun (x : L) : K :=
  (coeffA yL pairL_exists x) ^ 2 - (coeffB yL pairL_exists x) ^ 2 * (algebraMap k[X] K H.f)

theorem traceLFun_pair (pairL_injective : ∀ a₁ b₁ a₂ b₂ : K,
    (algebraMap K L) a₁ + (algebraMap K L) b₁ * yL =
      (algebraMap K L) a₂ + (algebraMap K L) b₂ * yL →
      a₁ = a₂ ∧ b₁ = b₂) (a b : K) :
    traceLFun yL pairL_exists ((algebraMap K L) a + (algebraMap K L) b * yL) = 2 * a := by
  unfold traceLFun
  rw [coeffA_of_eq yL pairL_exists pairL_injective]

theorem normLFun_pair (pairL_injective : ∀ a₁ b₁ a₂ b₂ : K,
    (algebraMap K L) a₁ + (algebraMap K L) b₁ * yL =
      (algebraMap K L) a₂ + (algebraMap K L) b₂ * yL →
      a₁ = a₂ ∧ b₁ = b₂) (a b : K) :
    normLFun H yL pairL_exists ((algebraMap K L) a + (algebraMap K L) b * yL) =
      a ^ 2 - b ^ 2 * (algebraMap k[X] K H.f) := by
  unfold normLFun
  rw [coeffA_of_eq yL pairL_exists pairL_injective,
    coeffB_of_eq yL pairL_exists pairL_injective]

theorem algebraMap_normLFun_eq (pairL_injective : ∀ a₁ b₁ a₂ b₂ : K,
    (algebraMap K L) a₁ + (algebraMap K L) b₁ * yL =
      (algebraMap K L) a₂ + (algebraMap K L) b₂ * yL →
      a₁ = a₂ ∧ b₁ = b₂) (yL_sq : yL ^ 2 = (algebraMap k[X] L) H.f) (x : L) :
    (algebraMap K L) (normLFun H yL pairL_exists x) =
      x * involutionL H yL pairL_exists pairL_injective yL_sq x := by
  have hx := coeffAB_spec yL pairL_exists x
  have hy2 := yL_sq' H yL yL_sq
  conv_lhs => rw [hx]
  conv_rhs => rw [hx]
  rw [normLFun_pair H yL pairL_exists pairL_injective]
  dsimp [involutionL]
  rw [involutionLFun_pair yL pairL_exists pairL_injective]
  simp only [map_sub, map_pow, map_mul]
  rw [← hy2]
  ring

theorem algebraMap_traceLFun_eq (pairL_injective : ∀ a₁ b₁ a₂ b₂ : K,
    (algebraMap K L) a₁ + (algebraMap K L) b₁ * yL =
      (algebraMap K L) a₂ + (algebraMap K L) b₂ * yL →
      a₁ = a₂ ∧ b₁ = b₂) (yL_sq : yL ^ 2 = (algebraMap k[X] L) H.f) (x : L) :
    (algebraMap K L) (traceLFun yL pairL_exists x) =
      x + involutionL H yL pairL_exists pairL_injective yL_sq x := by
  have hx := coeffAB_spec yL pairL_exists x
  conv_lhs => rw [hx]
  conv_rhs => rw [hx]
  rw [traceLFun_pair yL pairL_exists pairL_injective]
  dsimp [involutionL]
  rw [involutionLFun_pair yL pairL_exists pairL_injective]
  simp only [map_mul, map_ofNat]
  ring

theorem normLFun_mul (pairL_injective : ∀ a₁ b₁ a₂ b₂ : K,
    (algebraMap K L) a₁ + (algebraMap K L) b₁ * yL =
      (algebraMap K L) a₂ + (algebraMap K L) b₂ * yL →
      a₁ = a₂ ∧ b₁ = b₂) (yL_sq : yL ^ 2 = (algebraMap k[X] L) H.f)
    (h_inj_K : Function.Injective (algebraMap K L)) (x x' : L) :
    normLFun H yL pairL_exists (x * x') =
      normLFun H yL pairL_exists x * normLFun H yL pairL_exists x' := by
  apply h_inj_K
  rw [map_mul, algebraMap_normLFun_eq H yL pairL_exists pairL_injective yL_sq (x * x'),
    algebraMap_normLFun_eq H yL pairL_exists pairL_injective yL_sq x,
    algebraMap_normLFun_eq H yL pairL_exists pairL_injective yL_sq x',
    map_mul (involutionL H yL pairL_exists pairL_injective yL_sq)]
  ring

end HyperellipticPolynomial
