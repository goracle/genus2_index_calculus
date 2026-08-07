/-
Copyright (c) 2026 Claire H. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claire H
-/
import Mathlib
import Genus2Lean.HyperellipticFunctionField
import Genus2Lean.AffinePoints
import Genus2Lean.DivisorClassGroup
import Genus2Lean.PrincipalDivisors
import Genus2Lean.PrincipalDivisorsDedekind
import Genus2Lean.DedekindClosure2
import Genus2Lean.DedekindClosure3
import Genus2Lean.DedekindClosure4

/-!
# Integral Closure Characterization for Hyperelliptic Function Fields

This module proves the bi-implication that an element $x \in L$ is integral over $k[X]$ 
if and only if its trace and norm lie in $k[X]$, establishing the full structure of 
the Dedekind ring of integers $\mathcal{O}_L$.
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
  (yL : L)

local notation "K" => FractionRing k[X]

/-- An element $x \in L$ is integral over $k[X]$ if and only if both its 
    `traceLFun` and `normLFun` originate from polynomials in $k[X]$. -/
theorem isIntegral_iff_trace_norm_mem
    (pairL_exists : ∀ x : L,
      ∃ a b : K, x = (algebraMap K L) a + (algebraMap K L) b * yL)
    (pairL_injective : ∀ a₁ b₁ a₂ b₂ : K,
      (algebraMap K L) a₁ + (algebraMap K L) b₁ * yL =
        (algebraMap K L) a₂ + (algebraMap K L) b₂ * yL →
        a₁ = a₂ ∧ b₁ = b₂)
    (yL_sq : yL ^ 2 = (algebraMap k[X] L) H.f)
    (x : L) :
    IsIntegral k[X] x ↔
      (∃ a : k[X], traceLFun yL pairL_exists x = algebraMap k[X] K a) ∧
      (∃ b : k[X], normLFun H yL pairL_exists x = algebraMap k[X] K b) := by
  constructor
  · intro hx
    rcases pairL_exists x with ⟨a_K, b_K, hx_eq⟩
    set P := minpoly k[X] x
    have hP_monic : P.Monic := minpoly.monic hx
    have hP_eval : aeval x P = 0 := minpoly.aeval k[X] x
    
    -- Construct conjugate x_bar = a_K - b_K * yL = involutionL x
    set x_bar := (algebraMap K L) a_K - (algebraMap K L) b_K * yL with hx_bar_def
    have hx_bar_eq : x_bar = involutionLFun yL pairL_exists x := by
      rw [hx_eq, involutionLFun_pair yL pairL_exists pairL_injective]
    have h_conj_int : IsIntegral k[X] x_bar := by
      refine ⟨P, hP_monic, ?_⟩
      -- `involutionL` is a ring hom fixing `algebraMap k[X] L` (it fixes `algebraMap K L`,
      -- and `algebraMap k[X] L` factors through it by `IsScalarTower`), so it commutes with
      -- evaluation of a `k[X]`-polynomial: `aeval (φ x) P = φ (aeval x P)`.
      have hfix : ∀ p : k[X], involutionLFun yL pairL_exists (algebraMap k[X] L p) =
          algebraMap k[X] L p := by
        intro p
        rw [IsScalarTower.algebraMap_apply k[X] K L]
        exact involutionL_algebraMap H yL pairL_exists pairL_injective yL_sq (algebraMap k[X] K p)
      have h_map : aeval x_bar P = 0 := by
        rw [hx_bar_eq]
        show eval₂ (algebraMap k[X] L) (involutionLFun yL pairL_exists x) P = 0
        have hcomp : (involutionL H yL pairL_exists pairL_injective yL_sq).comp
            (algebraMap k[X] L) = algebraMap k[X] L := RingHom.ext hfix
        show eval₂ (algebraMap k[X] L)
            (involutionL H yL pairL_exists pairL_injective yL_sq x) P = 0
        rw [← hcomp,
          ← hom_eval₂ P (algebraMap k[X] L)
            (involutionL H yL pairL_exists pairL_injective yL_sq) x]
        show involutionL H yL pairL_exists pairL_injective yL_sq (aeval x P) = 0
        rw [hP_eval, map_zero]
      exact h_map
    -- Trace and Norm are integral over k[X] as sum/product of integral elements
    have hxbar_eq_inv : x_bar = involutionL H yL pairL_exists pairL_injective yL_sq x := hx_bar_eq
    have h_tr_int : IsIntegral k[X] ((algebraMap K L) (traceLFun yL pairL_exists x)) := by
      have h_sum := IsIntegral.add hx h_conj_int
      rw [hxbar_eq_inv] at h_sum
      rwa [algebraMap_traceLFun_eq H yL pairL_exists pairL_injective yL_sq]
    have h_nm_int : IsIntegral k[X] ((algebraMap K L) (normLFun H yL pairL_exists x)) := by
      have h_prod := IsIntegral.mul hx h_conj_int
      rw [hxbar_eq_inv] at h_prod
      rwa [algebraMap_normLFun_eq H yL pairL_exists pairL_injective yL_sq]
    -- Pull back from K to k[X] via integral closure of PID k[X]
    have h_tr_K : IsIntegral k[X] (traceLFun yL pairL_exists x) :=
      (isIntegral_algebraMap_iff (R := k[X]) (A := K) (B := L)
        (algebraMap K L).injective).mp h_tr_int
    have h_nm_K : IsIntegral k[X] (normLFun H yL pairL_exists x) :=
      (isIntegral_algebraMap_iff (R := k[X]) (A := K) (B := L)
        (algebraMap K L).injective).mp h_nm_int
    obtain ⟨a_poly, ha⟩ := (IsIntegrallyClosed.isIntegral_iff).mp h_tr_K
    obtain ⟨b_poly, hb⟩ := (IsIntegrallyClosed.isIntegral_iff).mp h_nm_K
    exact ⟨⟨a_poly, ha.symm⟩, ⟨b_poly, hb.symm⟩⟩
  · rintro ⟨⟨a, htr⟩, ⟨b, hnorm⟩⟩
    exact isIntegral_of_trace_norm_mem H yL pairL_exists pairL_injective yL_sq x a b htr hnorm   




/-- Halving a polynomial coefficient in characteristic 0 / char ≠ 2 -/
theorem poly_coeff_of_two_mul (h2 : (2 : k) ≠ 0) {a_K : K}
    (h : ∃ p : k[X], 2 * a_K = algebraMap k[X] K p) :
    ∃ a : k[X], a_K = algebraMap k[X] K a := by
  rcases h with ⟨p, hp⟩
  refine ⟨C (2⁻¹) * p, ?_⟩
  rw [map_mul, ← hp]
  have h2_map : (2 : K) = algebraMap k[X] K (C 2) := by simp [map_ofNat]
  rw [h2_map, ← mul_assoc, ← map_mul, ← C_mul, inv_mul_cancel₀ h2, map_one, map_one, one_mul]

/-- Square-free denominator reduction -/
theorem poly_coeff_of_norm {a : k[X]} {b_K : K}
    (hnorm : ∃ q : k[X], (algebraMap k[X] K a) ^ 2 - b_K ^ 2 * algebraMap k[X] K H.f = algebraMap k[X] K q) :
    ∃ b : k[X], b_K = algebraMap k[X] K b := by
  rcases hnorm with ⟨q, hq⟩
  -- Rewrite into the shape `sq_mul_mem_of_squarefree` expects:
  -- `b_K ^ 2 * (algebraMap H.f) = algebraMap (a ^ 2 - q)`.
  have hb : ∃ c : k[X], b_K ^ 2 * algebraMap k[X] K H.f = algebraMap k[X] K c := by
    refine ⟨a ^ 2 - q, ?_⟩
    rw [map_sub, map_pow]
    linear_combination -hq
  obtain ⟨b, hb_eq⟩ := sq_mul_mem_of_squarefree H.f H.squarefree_f b_K hb
  exact ⟨b, hb_eq.symm⟩

/-- Every integral element $x \in L$ over $k[X]$ can be expressed as $a + b \cdot y_L$ 
    where $a, b \in k[X]$. -/
theorem mem_integralClosure_iff_poly_coefficients
    (pairL_exists : ∀ x : L,
      ∃ a b : K, x = (algebraMap K L) a + (algebraMap K L) b * yL)
    (pairL_injective : ∀ a₁ b₁ a₂ b₂ : K,
      (algebraMap K L) a₁ + (algebraMap K L) b₁ * yL =
        (algebraMap K L) a₂ + (algebraMap K L) b₂ * yL →
        a₁ = a₂ ∧ b₁ = b₂)
    (yL_sq : yL ^ 2 = (algebraMap k[X] L) H.f)
    (h2 : (2 : k) ≠ 0)
    (x : L) :
    x ∈ integralClosure k[X] L ↔
      ∃ a b : k[X], x = (algebraMap k[X] L) a + (algebraMap k[X] L) b * yL := by
  constructor
  · intro hx
    rw [mem_integralClosure_iff] at hx
    have h_tn := (isIntegral_iff_trace_norm_mem H yL pairL_exists pairL_injective yL_sq x).mp hx
    rcases pairL_exists x with ⟨a_K, b_K, hx_decomp⟩
    obtain ⟨a', ha'⟩ := h_tn.1
    obtain ⟨b', hb'⟩ := h_tn.2
    rw [hx_decomp, traceLFun_pair yL pairL_exists pairL_injective] at ha'
    rw [hx_decomp, normLFun_pair H yL pairL_exists pairL_injective] at hb'
    obtain ⟨a, ha⟩ := poly_coeff_of_two_mul h2 ⟨a', ha'⟩
    have hb_norm : ∃ q : k[X],
        (algebraMap k[X] K a) ^ 2 - b_K ^ 2 * algebraMap k[X] K H.f = algebraMap k[X] K q := by
      refine ⟨b', ?_⟩
      rw [← ha]
      exact hb'
    obtain ⟨b, hb⟩ := poly_coeff_of_norm H hb_norm
    refine ⟨a, b, ?_⟩
    rw [hx_decomp, ha, hb, IsScalarTower.algebraMap_apply k[X] K L,
      IsScalarTower.algebraMap_apply k[X] K L]
  · rintro ⟨a, b, rfl⟩
    have h_int_a : IsIntegral k[X] ((algebraMap k[X] L) a) := isIntegral_algebraMap
    have h_int_b : IsIntegral k[X] ((algebraMap k[X] L) b) := isIntegral_algebraMap
    have h_int_y : IsIntegral k[X] yL := by
      refine ⟨X ^ 2 - C H.f, ?_, ?_⟩
      · show (X ^ 2 - C H.f : Polynomial k[X]).leadingCoeff = 1
        rw [leadingCoeff_sub_of_degree_lt]
        · exact monic_X_pow 2
        · rw [degree_X_pow]
          exact degree_C_le.trans_lt (by decide)
      · change eval₂ (algebraMap k[X] L) yL (X ^ 2 - C H.f) = 0
        rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, yL_sq, sub_self]
    have h_int_by : IsIntegral k[X] ((algebraMap k[X] L) b * yL) := IsIntegral.mul h_int_b h_int_y
    exact IsIntegral.add h_int_a h_int_by


end HyperellipticPolynomial
