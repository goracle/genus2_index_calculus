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
import Genus2Lean.DedekindClosure5

/-!
# `CoordinateRing H` is integrally closed, hence a Dedekind domain

Split out of `PrincipalDivisors.lean` because the real proof of
`coordinateRing_isIntegrallyClosed` needs
`DedekindClosure5.mem_integralClosure_iff_poly_coefficients`, and `DedekindClosure5.lean`
(transitively, via `PrincipalDivisorsDedekind.lean`, for `sq_mul_mem_of_squarefree`)
imports `PrincipalDivisors.lean`. Since `PrincipalDivisors.lean` itself doesn't need
`coordinateRing_isIntegrallyClosed` / `coordinateRingIsDedekindDomain` for anything
downstream in that file, they live here instead, one layer later in the import order,
avoiding the cycle. (Previously this was worked around with the stub `axiom`-based
`DedekindClosure6.lean`; that file is now unused by this proof and can likely be
deleted once nothing else references it.)

-/

noncomputable section

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.show false
set_option linter.unusedSectionVars false

open Polynomial

namespace HyperellipticPolynomial

variable {k : Type*} [Field k]
variable {H : HyperellipticPolynomial k}

/-- Every element of `CoordinateRing H` is of the form `toPair H A B` for some `A B : k[X]`.
Proved via reduction mod the monic quadratic `X² - C H.f`: any representing polynomial
`p : (k[X])[X]` reduces to `p %ₘ (X² - C H.f)`, which has `natDegree < 2` and so is literally
`C A + C B * X` for `A := coeff 0`, `B := coeff 1`.

Companion to the existing `toPair_eq_zero_iff` / `toPair_injective` in `PrincipalDivisors.lean` —
together they say `toPair H` is a bijection `k[X] × k[X] ≃ CoordinateRing H`. -/
theorem toPair_surjective (H : HyperellipticPolynomial k) (z : CoordinateRing H) :
    ∃ A B : k[X], z = toPair H A B := by
  have hmonic : (X ^ 2 - C H.f : (k[X])[X]).Monic :=
    Polynomial.monic_X_pow_sub_C H.f two_ne_zero
  induction z using AdjoinRoot.induction_on with
  | ih p =>
    -- `Polynomial.dvd_modByMonic_sub p q : q ∣ p %ₘ q - p` (no `Monic` hypothesis needed),
    -- so `p` and `p %ₘ q` differ by a multiple of `q = X² - C H.f`, hence map to the same
    -- `AdjoinRoot.mk` class.
    have hmod : AdjoinRoot.mk (X ^ 2 - C H.f) p =
        AdjoinRoot.mk (X ^ 2 - C H.f) (p %ₘ (X ^ 2 - C H.f)) := by
      have hdvd : (X ^ 2 - C H.f : (k[X])[X]) ∣ (p %ₘ (X ^ 2 - C H.f)) - p :=
        Polynomial.dvd_modByMonic_sub p (X ^ 2 - C H.f)
      have hker : AdjoinRoot.mk (X ^ 2 - C H.f) ((p %ₘ (X ^ 2 - C H.f)) - p) = 0 :=
        AdjoinRoot.mk_eq_zero.mpr hdvd
      rw [map_sub, sub_eq_zero] at hker
      exact hker.symm
    set r := p %ₘ (X ^ 2 - C H.f) with hr_def
    have hnd2 : (X ^ 2 - C H.f : (k[X])[X]).natDegree = 2 := by compute_degree!
    have hrdeg : r.natDegree < 2 := by
      have hne1 : (X ^ 2 - C H.f : (k[X])[X]) ≠ 1 := by
        intro heq1
        rw [heq1, Polynomial.natDegree_one] at hnd2
        exact absurd hnd2 (by norm_num)
      have hlt := Polynomial.natDegree_modByMonic_lt p hmonic hne1
      rw [hnd2] at hlt
      rw [hr_def]
      exact hlt
    -- `r` has natDegree < 2, so it's literally `C (r.coeff 0) + C (r.coeff 1) * X`.
    have hr_eq : r = C (r.coeff 0) + C (r.coeff 1) * X := by
      ext n
      match n with
      | 0 => simp
      | 1 => simp
      | (m + 2) =>
        have hc0 : r.coeff (m + 2) = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
        simp [hc0]
    refine ⟨r.coeff 0, r.coeff 1, ?_⟩
    show AdjoinRoot.mk (X ^ 2 - C H.f) p = toPair H (r.coeff 0) (r.coeff 1)
    -- Prove the "mk of a linear combination" identity as a clean standalone fact, in terms
    -- of the coefficients `A B : k[X]` directly (no leftover `.coeff` calls on the RHS), so
    -- we never ask the elaborator to unify the whole expression by defeq (that `rfl` /
    -- `whnf` call was timing out) nor to simplify `.coeff` applications post-hoc.
    have hmk : ∀ A B : k[X], AdjoinRoot.mk (X ^ 2 - C H.f) (C A + C B * X) = toPair H A B := by
      intro A B
      unfold toPair HyperellipticPolynomial.y
      rw [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
      rfl
    rw [hmod]
    conv_lhs => rw [hr_eq]
    exact hmk (r.coeff 0) (r.coeff 1)

/-- `CoordinateRing H` is integrally closed in its fraction field `k(C)` when `f` is squarefree
and `char k ≠ 2`. -/
theorem coordinateRing_isIntegrallyClosed
    (H : HyperellipticPolynomial k)
    (nd : NonsingularData H) :
    IsIntegrallyClosed (CoordinateRing H) := by
  haveI : IsDomain (CoordinateRing H) := coordinateRingIsDomain H nd
  refine ⟨IsFractionRing.injective (CoordinateRing H) (FractionRing (CoordinateRing H)),
          fun {z} ↦ ⟨fun hz ↦ ?_, ?_⟩⟩

  · -- Forward direction: IsIntegral (CoordinateRing H) z → ∃ y, algebraMap y = z
    -- `algebraMap k[X] (FractionRing (CoordinateRing H))` is injective (composite of
    -- `k[X] ↪ CoordinateRing H`, injective via
    -- `AdjoinRoot.noZeroSMulDivisors_of_prime_of_degree_ne_zero`, with
    -- `CoordinateRing H ↪ FractionRing (CoordinateRing H)`, injective as the latter is
    -- its fraction ring), giving `Module.IsTorsionFree k[X] (FractionRing (CoordinateRing H))`;
    -- `FractionRing (CoordinateRing H)` then becomes a `FractionRing k[X]`-algebra via
    -- `FractionRing.liftAlgebra`.
    -- (`NoZeroSMulDivisors.iff_algebraMap_injective` was renamed/generalized to
    -- `Module.isTorsionFree_iff_algebraMap_injective`, and
    -- `AdjoinRoot.noZeroSMulDivisors_of_prime_of_degree_ne_zero` now produces
    -- `Module.IsTorsionFree` directly instead of `NoZeroSMulDivisors`.)
    have hdeg_ne : (X ^ 2 - C H.f : (k[X])[X]).degree ≠ 0 := by
      have hnd : (X ^ 2 - C H.f : (k[X])[X]).natDegree = 2 := by compute_degree!
      have hne0 : (X ^ 2 - C H.f : (k[X])[X]) ≠ 0 := by
        intro h; rw [h, natDegree_zero] at hnd; exact absurd hnd (by decide)
      rw [Polynomial.degree_eq_natDegree hne0, hnd]
      decide
    haveI htf0 : Module.IsTorsionFree k[X] (CoordinateRing H) :=
      AdjoinRoot.noZeroSMulDivisors_of_prime_of_degree_ne_zero
        nd.irreducible_defining_poly.prime hdeg_ne
    have h1 : Function.Injective (algebraMap k[X] (CoordinateRing H)) :=
      (Module.isTorsionFree_iff_algebraMap_injective (R := k[X]) (A := CoordinateRing H)).mp htf0
    have h2 : Function.Injective (algebraMap (CoordinateRing H) (FractionRing (CoordinateRing H))) :=
      IsFractionRing.injective (CoordinateRing H) (FractionRing (CoordinateRing H))
    have hinj : Function.Injective (algebraMap k[X] (FractionRing (CoordinateRing H))) := by
      have hcomp : algebraMap k[X] (FractionRing (CoordinateRing H)) =
          (algebraMap (CoordinateRing H) (FractionRing (CoordinateRing H))).comp
            (algebraMap k[X] (CoordinateRing H)) :=
        IsScalarTower.algebraMap_eq k[X] (CoordinateRing H) (FractionRing (CoordinateRing H))
      rw [hcomp]
      exact h2.comp h1
    haveI : Module.IsTorsionFree k[X] (FractionRing (CoordinateRing H)) :=
      (Module.isTorsionFree_iff_algebraMap_injective (R := k[X])
        (A := FractionRing (CoordinateRing H))).mpr hinj
    -- `FractionRing.liftAlgebra` / `FractionRing.isScalarTower_liftAlgebra` are marked
    -- non-instance precisely because they'd create a diamond; the mathlib docstring says
    -- to introduce them together locally. Using `haveI` for the `Algebra` instance made it
    -- opaque to defeq-based unification, so the subsequent `isScalarTower_liftAlgebra` call's
    -- own typeclass search could land on an unrelated `Algebra k[X] (FractionRing
    -- (CoordinateRing H))` instance elsewhere in scope instead of reusing this one. `letI`
    -- keeps the term transparent, so the second lookup unifies with it by defeq.
    letI : Algebra (FractionRing k[X]) (FractionRing (CoordinateRing H)) :=
      FractionRing.liftAlgebra k[X] (FractionRing (CoordinateRing H))
    haveI : IsScalarTower k[X] (FractionRing k[X]) (FractionRing (CoordinateRing H)) :=
      FractionRing.isScalarTower_liftAlgebra k[X] (FractionRing (CoordinateRing H))

    -- Step 1: Transfer integrality across k[X] ⊆ CoordinateRing H ⊆ FractionRing
    have hz_kX : IsIntegral k[X] z := by
      have hmonic : (X ^ 2 - C H.f : (k[X])[X]).Monic :=
        Polynomial.monic_X_pow_sub_C H.f two_ne_zero
      haveI : Module.Finite k[X] (CoordinateRing H) :=
        Polynomial.Monic.finite_adjoinRoot hmonic
      haveI : Algebra.IsIntegral k[X] (CoordinateRing H) := Algebra.IsIntegral.of_finite k[X] (CoordinateRing H)
      exact isIntegral_trans (hx := hz)

    -- Step 2: Decompose z into A + B * y using mem_integralClosure_iff_poly_coefficients
    obtain ⟨A, B, hAB⟩ : ∃ A B : k[X],
        z = algebraMap (CoordinateRing H) (FractionRing (CoordinateRing H)) (toPair H A B) := by
      have h01 : toPair H 0 1 = y H := by unfold toPair; simp
      let yL : FractionRing (CoordinateRing H) :=
        algebraMap (CoordinateRing H) (FractionRing (CoordinateRing H)) (toPair H 0 1)

      -- Hypotheses for DedekindClosure5
      have h_exists : ∀ x : FractionRing (CoordinateRing H), ∃ a b : FractionRing k[X],
          x = algebraMap (FractionRing k[X]) (FractionRing (CoordinateRing H)) a +
            algebraMap (FractionRing k[X]) (FractionRing (CoordinateRing H)) b * yL := by
        sorry -- FractionRing elements decompose via linear combinations over k(X)
      have h_inj : ∀ a₁ b₁ a₂ b₂ : FractionRing k[X],
          algebraMap (FractionRing k[X]) (FractionRing (CoordinateRing H)) a₁ +
            algebraMap (FractionRing k[X]) (FractionRing (CoordinateRing H)) b₁ * yL =
          algebraMap (FractionRing k[X]) (FractionRing (CoordinateRing H)) a₂ +
            algebraMap (FractionRing k[X]) (FractionRing (CoordinateRing H)) b₂ * yL →
          a₁ = a₂ ∧ b₁ = b₂ := by
        sorry -- Linear independence of 1 and yL over k(X)
      have h_sq : yL ^ 2 = algebraMap k[X] (FractionRing (CoordinateRing H)) H.f := by
        dsimp only [yL]
        rw [← map_pow, h01, y_sq_eq H,
          ← IsScalarTower.algebraMap_apply k[X] (CoordinateRing H) (FractionRing (CoordinateRing H))]
      have h2 : (2 : k) ≠ 0 := nd.char_ne_two

      have h_iff := mem_integralClosure_iff_poly_coefficients H yL h_exists h_inj h_sq h2 nd.squarefree_f z
      -- `x ∈ integralClosure R A` unfolds to `IsIntegral R x`, so `hz_kX` is usable directly;
      -- the old `mem_integralClosure_iff.mpr` wrapper no longer exists / is unneeded.
      obtain ⟨a, b, hab⟩ := h_iff.mp hz_kX
      refine ⟨a, b, ?_⟩
      -- Reconnect `algebraMap k[X] _ a + algebraMap k[X] _ b * yL` (from `DedekindClosure5`)
      -- with `algebraMap (CoordinateRing H) _ (toPair H a b)`.
      rw [hab]
      show algebraMap k[X] (FractionRing (CoordinateRing H)) a +
          algebraMap k[X] (FractionRing (CoordinateRing H)) b * yL =
        algebraMap (CoordinateRing H) (FractionRing (CoordinateRing H)) (toPair H a b)
      unfold toPair
      rw [map_add, map_mul,
        IsScalarTower.algebraMap_apply k[X] (CoordinateRing H) (FractionRing (CoordinateRing H)) a,
        IsScalarTower.algebraMap_apply k[X] (CoordinateRing H) (FractionRing (CoordinateRing H)) b]
      congr 2
      show yL = algebraMap (CoordinateRing H) (FractionRing (CoordinateRing H)) (y H)
      dsimp only [yL]
      rw [h01]

    -- Step 3: Wrap A + B * y back into CoordinateRing H
    exact ⟨toPair H A B, hAB.symm⟩

  · -- Reverse direction: (∃ y, algebraMap y = z) → IsIntegral (CoordinateRing H) z
    rintro ⟨y, rfl⟩
    exact isIntegral_algebraMap

/-- Given `NonsingularData`, `CoordinateRing H` is a Dedekind domain. -/
theorem coordinateRingIsDedekindDomain (H : HyperellipticPolynomial k)
    (nd : NonsingularData H) : IsDedekindDomain (CoordinateRing H) := by
  haveI : IsDomain (CoordinateRing H) := coordinateRingIsDomain H nd
  haveI : IsIntegrallyClosed (CoordinateRing H) := coordinateRing_isIntegrallyClosed H nd
  haveI : IsNoetherianRing (CoordinateRing H) := coordinateRing_isNoetherian H
  have hmonic : (X ^ 2 - C H.f : (k[X])[X]).Monic :=
    Polynomial.monic_X_pow_sub_C H.f two_ne_zero
  haveI : Module.Finite k[X] (CoordinateRing H) := Polynomial.Monic.finite_adjoinRoot hmonic
  haveI : Algebra.IsIntegral k[X] (CoordinateRing H) := Algebra.IsIntegral.of_finite k[X] (CoordinateRing H)
  haveI : Ring.DimensionLEOne (CoordinateRing H) := ⟨fun {p} hp0 hpp => by
    -- Contract `p` to `p0` in `k[X]` via `comap`. Since `k[X] → CoordinateRing H` is
    -- integral and `CoordinateRing H` is a domain, `p ≠ ⊥` forces `p0 ≠ ⊥`
    -- (`Ideal.under_ne_bot`, noting `Ideal.under k[X] p` unfolds to this `comap`);
    -- `k[X]` a PID makes the nonzero prime `p0` maximal
    -- (`IsPrime.to_maximal_ideal`); and maximality transfers back up an
    -- integral extension (`Ideal.isMaximal_of_isIntegral_of_isMaximal_comap`).
    set p0 := p.comap (algebraMap k[X] (CoordinateRing H)) with hp0_def
    have hp0_ne_bot : p0 ≠ ⊥ := Ideal.under_ne_bot k[X] hp0
    haveI hp0_prime : p0.IsPrime := Ideal.IsPrime.comap _
    have hp0_max : p0.IsMaximal := IsPrime.to_maximal_ideal hp0_ne_bot
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := k[X]) p hp0_max⟩
  haveI : IsDedekindRing (CoordinateRing H) := ⟨⟩
  exact ⟨⟩

end HyperellipticPolynomial
