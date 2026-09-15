import Mathlib
import Genus2Lean.ZeroD.SharedPivotResultantElim

/-!
# Finiteness-exporting version of the shared-pivot resultant bound

`SharedPivotResultantElim.lean`'s `finrank_le_of_shared_linear_elim_pair`
bounds `finrank k B` by `finrank k (A ⧸ span {resultant})`, but does NOT
conclude `Module.Finite k B` — exactly the gap
`FinrankLeOfMonicAnnihilatorFinite.lean`'s own docstring already
diagnosed for the single-relation case (`Module.finrank` alone is
junk-valued `0` on an infinite-dimensional module, so a bound on it says
nothing about actual finiteness) and fixed there by exporting
`Module.Finite` as an extra conclusion rather than leaving it to be
independently re-derived at every stage. This file is the same fix,
one level up: `Assembly` (`GenListFinrankResultantAssembly.lean`) needs
`Module.Finite (F p) (...)`/`Nontrivial (...)` on the doubly-extended
ring `Rdec p ⧸ Ideal.ofList (gens ++ [g1, g2])` to hand to the NEXT
resultant-elimination stage (or to the curve chain, once all four
pivots are eliminated) — a finrank bound alone cannot supply that.

**The fix, read directly off `finrank_le_of_shared_linear_elim_pair`'s
own proof (not guessed)**: that proof already builds an explicit
SURJECTIVE `k`-linear map `ψₗ : (A ⧸ Ideal.span {resultant}) →ₗ[k] B`
(via `Ideal.Quotient.lift` on the resultant ideal, justified by the
resultant vanishing in `B`) and gets its `finrank` bound from
`LinearMap.finrank_le_finrank_of_surjective` applied to it. A surjective
`k`-linear map out of a `Module.Finite` domain gives `Module.Finite` on
the codomain directly, `Module.Finite.of_surjective` — the exact
transport `FinrankLeOfSpanSurjective.lean`'s own `hfin` step already uses
for the one-hop version of this same fact. So this file re-derives
`finrank_le_of_shared_linear_elim_pair`'s proof from scratch (rather
than trying to extract the surjection from the already-completed proof
term, which Lean does not expose), adding `Module.Finite k (A ⧸
Ideal.span {resultant})` as an explicit hypothesis and concluding
`Module.Finite k B` alongside the same `finrank` bound. `Nontrivial B`
is NOT concluded here — unlike the monic-annihilator case, surjectivity
alone does not transport `Nontrivial` backwards along `ψₗ` (a surjection
from a nontrivial ring can still have a trivial codomain), so it stays
an explicit hypothesis at each call site, matching
`SharedPivotStageWiring.lean`'s own already-established
`[Nontrivial (A ⧸ span {mk g1})]`-style pattern for the intermediate
ring. -/

namespace Genus2Lean

open Polynomial

variable {k A : Type*} [Field k] [CommRing A] [Nontrivial A] [Algebra k A]
  [StrongRankCondition A] [Module.Finite k A]

/-- **Finiteness-exporting version of `finrank_le_of_shared_linear_elim_
pair`.** Same hypotheses, plus `Module.Finite k (A ⧸ Ideal.span
{n2*d1-n1*d2})` on the resultant quotient (supplied explicitly, not
resolved by instance search, so it can be threaded through an explicit
multi-stage composition). Concludes the same `finrank` bound AND
`Module.Finite k B`. -/
theorem finrank_le_and_finite_of_shared_linear_elim_pair
    {B : Type*} [CommRing B] [Algebra A B] [Algebra k B] [IsScalarTower k A B]
    (n1 d1 n2 d2 : A) (hd1 : IsUnit d1) (t : B)
    (ht1 : (Polynomial.aeval t) (linearElimPoly n1 d1) = 0)
    (ht2 : (Polynomial.aeval t) (linearElimPoly n2 d2) = 0)
    (hgen : Algebra.adjoin A {t} = (⊤ : Subalgebra A B))
    (hfinRes : Module.Finite k (A ⧸ Ideal.span ({n2 * d1 - n1 * d2} : Set A))) :
    Module.Finite k B ∧
    Module.finrank k B ≤
      Module.finrank k (A ⧸ Ideal.span ({n2 * d1 - n1 * d2} : Set A)) := by
  -- Identical setup to `finrank_le_of_shared_linear_elim_pair`'s own
  -- proof, up through constructing the surjective linear map `ψₗ`.
  have ht1' : (Polynomial.aeval t) (linearElimMonicPoly n1 d1 hd1) = 0 :=
    (aeval_linearElimPoly_eq_zero_iff n1 d1 hd1 t).mp ht1
  have htval : t = algebraMap A B (↑hd1.unit⁻¹ * n1) := by
    have h := ht1'
    unfold linearElimMonicPoly at h
    rw [Polynomial.aeval_def, Polynomial.eval₂_sub, Polynomial.eval₂_X,
      Polynomial.eval₂_C, sub_eq_zero] at h
    rw [h]
  have hres_zero : algebraMap A B (↑hd1.unit⁻¹ * (n2 * d1 - n1 * d2)) = 0 := by
    have h2 : algebraMap A B n2 - t * algebraMap A B d2 = 0 := by
      have := ht2
      unfold linearElimPoly at this
      rwa [Polynomial.aeval_def, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
        Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_C] at this
    rw [htval] at h2
    have hd1u : d1 * (↑hd1.unit⁻¹ : A) = 1 := by
      nth_rewrite 1 [← hd1.unit_spec]
      exact hd1.unit.mul_inv
    have hkey : (↑hd1.unit⁻¹ : A) * (n2 * d1 - n1 * d2)
        = n2 - (↑hd1.unit⁻¹ * n1) * d2 := by
      have hu2 : (↑hd1.unit⁻¹ : A) * (n2 * d1) = n2 := by
        calc (↑hd1.unit⁻¹ : A) * (n2 * d1) = n2 * (d1 * ↑hd1.unit⁻¹) := by ring
          _ = n2 * 1 := by rw [hd1u]
          _ = n2 := mul_one n2
      rw [mul_sub, hu2]
      ring
    rw [hkey, map_sub, map_mul]
    exact h2
  have hres_zero' : algebraMap A B (n2 * d1 - n1 * d2) = 0 := by
    have hunit : IsUnit (algebraMap A B (↑hd1.unit⁻¹ : A)) :=
      (algebraMap A B).isUnit_map hd1.unit⁻¹.isUnit
    rw [map_mul] at hres_zero
    exact hunit.mul_right_eq_zero.mp hres_zero
  have hgen' : Algebra.adjoin A {t} ≤ (Algebra.ofId A B).range := by
    rw [Algebra.adjoin_le_iff]
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨↑hd1.unit⁻¹ * n1, htval.symm⟩
  rw [hgen] at hgen'
  have hsurj : Function.Surjective (algebraMap A B) := by
    intro b
    have hb : b ∈ (⊤ : Subalgebra A B) := trivial
    obtain ⟨a, ha⟩ := hgen' hb
    exact ⟨a, ha⟩
  set I := Ideal.span ({n2 * d1 - n1 * d2} : Set A) with hI_def
  have hImap : I ≤ RingHom.ker (algebraMap A B) := by
    rw [hI_def, Ideal.span_le]
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst hx
    exact hres_zero'
  set ψ : (A ⧸ I) →+* B :=
    Ideal.Quotient.lift I (algebraMap A B) (fun x hx => RingHom.mem_ker.mp (hImap hx))
    with hψ_def
  have hψ_surj : Function.Surjective ψ := by
    intro b
    obtain ⟨a, ha⟩ := hsurj b
    exact ⟨Ideal.Quotient.mk I a, by rw [hψ_def]; simpa using ha⟩
  have hψ_lin : ∀ (c : k) (x : A ⧸ I), ψ (c • x) = c • ψ x := by
    have hcomm : ∀ a : A, ψ (algebraMap A (A ⧸ I) a) = algebraMap A B a := by
      intro a
      rw [hψ_def]
      exact Ideal.Quotient.lift_mk I (algebraMap A B) _
    intro c x
    rw [Algebra.smul_def, Algebra.smul_def, map_mul,
      IsScalarTower.algebraMap_apply k A (A ⧸ I),
      IsScalarTower.algebraMap_apply k A B, hcomm]
  set ψₗ : (A ⧸ I) →ₗ[k] B :=
    { toFun := ψ, map_add' := map_add ψ, map_smul' := hψ_lin } with hψₗ_def
  have hψₗ_surj : Function.Surjective ψₗ := hψ_surj
  -- The one new step relative to `finrank_le_of_shared_linear_elim_pair`:
  -- `Module.Finite k B` from `Module.Finite k (A ⧸ I)` (`hfinRes`, which
  -- is `hfinRes` up to `I`'s `set`-definition unfolding to the same
  -- ideal) transported along the surjection `ψₗ`.
  refine ⟨Module.Finite.of_surjective ψₗ hψₗ_surj, ?_⟩
  exact LinearMap.finrank_le_finrank_of_surjective hψₗ_surj

end Genus2Lean
