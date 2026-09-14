import Mathlib
import Genus2Lean.ZeroD.LinearElimDegreeBound
import Genus2Lean.ZeroD.FinrankLeOfMonicAnnihilatorFinite

/-!
# Shared-pivot elimination: two linear-elimination generators in the SAME
# new variable, bounded via their resultant

`ROADMAP-monic-annihilator-degree-uniform.md`'s "Correction" entry (the
pivot-table finding: `U0` is pivoted by BOTH `Fu0` and `Fu1`, `U1` by
`Fu2`/`Fu3`, etc. — not a clean one-generator-one-pivot triangular
system) identifies the concrete piece needed to make the corrected
"eliminate `U0,U1,V0,V1` first via their resultants" plan real: a lemma
bounding `finrank` for a ring extended by ONE new variable `X` subject to
TWO simultaneous linear relations `n1 - X*d1` and `n2 - X*d2`, in terms
of `finrank` of the SAME base ring further quotiented by the classical
resultant `n1*d2 - n2*d1` alone — no `X` involved.

**Why this is exactly the missing piece.** `LinearElimDegreeBound.lean`
already bounds `finrank` for ONE such relation (`finrank_le_of_linear_elim`,
degree 1, needs `d` a unit). `MvPolynomialSharedTargetSolve.lean` already
found, at the POINT-existence level, that two such relations sharing `X`
are simultaneously satisfiable exactly where their resultant
`n1*d2 - n2*d1` vanishes. This file is the IDEAL/finrank-level version of
that same fact: rather than asking whether some point satisfies both
relations, it bounds the DIMENSION of the ring where both relations hold
as ideal generators, and shows that dimension is controlled by the
dimension of the ring where only the resultant holds — the resultant
ideal is a ring in the ORIGINAL variables only (no `X`), exactly the
"eliminate `U0` first, reducing to the 8-variable coefficient block"
step the corrected roadmap plan calls for.

**Proof strategy actually used** (simpler than an earlier draft's
`AdjoinRoot`-two-stage plan, which needed a fabricated lemma name and is
dropped): work directly in the abstract algebra `B` the theorem is
stated for, never introducing `AdjoinRoot` explicitly.

1. From `ht1 : aeval t (linearElimPoly n1 d1) = 0` and `hd1 : IsUnit d1`,
   `t`'s value in `B` is forced to `algebraMap A B (d1⁻¹ * n1)` — a
   direct unfolding of `aeval`/`eval₂` at `linearElimPoly n1 d1 = C n1 -
   X * C d1`, solved for `t` using `hd1.unit`'s defining equation
   `d1 * d1⁻¹ = 1`.
2. Substituting that forced value into `ht2`'s statement
   (`algebraMap A B n2 - t * algebraMap A B d2 = 0`) and clearing the
   `d1⁻¹` factor (using `hd1.unit`'s inverse being a unit in `B` too,
   via `RingHom.isUnit_map`) shows `algebraMap A B (n2*d1 - n1*d2) = 0`
   — the resultant vanishes in `B`.
3. `t` itself lies in the image of `algebraMap A B` (step 1), so
   `hgen : Algebra.adjoin A {t} = ⊤` forces `algebraMap A B` to be
   SURJECTIVE outright (adjoining an already-in-the-image element adds
   nothing new). Since the resultant maps to `0` (step 2), `algebraMap A
   B` factors through `A ⧸ Ideal.span {n2*d1 - n1*d2}`
   (`Ideal.Quotient.lift`), giving a surjective `k`-linear map from that
   quotient onto `B`, and `LinearMap.finrank_le_finrank_of_surjective`
   finishes. No `AdjoinRoot`, `linearElimMonicPoly`'s `AdjoinRoot`
   incarnation, or two-element `Ideal.span` manipulation is needed —
   only `LinearElimDegreeBound.lean`'s existing
   `aeval_linearElimPoly_eq_zero_iff` (to get `t`'s forced value cleanly)
   plus direct `algebraMap`/`Ideal.Quotient` bookkeeping. -/

namespace Genus2Lean

open Polynomial

variable {k A : Type*} [Field k] [CommRing A] [Nontrivial A] [Algebra k A]
  [StrongRankCondition A] [Module.Finite k A]

/-- **This file's headline deliverable.** Two linear-elimination
relations `n1 - X*d1` and `n2 - X*d2`, sharing the SAME new variable `X`
(exactly `Fu0`/`Fu1`'s shape at `U0`, or `Fu2`/`Fu3` at `U1`, etc. — see
module docstring), with `d1` a unit. If `t : B` is an `A`-algebra element
satisfying BOTH relations (`aeval t (linearElimPoly n1 d1) = 0` and
`aeval t (linearElimPoly n2 d2) = 0`) and generates `B` as an
`A`-algebra, then `finrank k B` is bounded by `finrank k` of the
RESULTANT quotient ring `A ⧸ Ideal.span {n2*d1 - n1*d2}` — not by `B`
needing to literally BE that quotient (a genuinely different `B`, built
abstractly the way every per-stage lemma in this project's Assembly is
stated), but via `t`'s value being forced to `d1⁻¹ * n1` by the first
relation (proved directly in `B`, not through a separate `AdjoinRoot`
detour), substituted into the second relation to show the resultant's
image in `B` vanishes, then transporting `finrank` across the resulting
surjection `A ⧸ Ideal.span {resultant} ↠ B`. -/
theorem finrank_le_of_shared_linear_elim_pair
    {B : Type*} [CommRing B] [Algebra A B] [Algebra k B] [IsScalarTower k A B]
    (n1 d1 n2 d2 : A) (hd1 : IsUnit d1) (t : B)
    (ht1 : (Polynomial.aeval t) (linearElimPoly n1 d1) = 0)
    (ht2 : (Polynomial.aeval t) (linearElimPoly n2 d2) = 0)
    (hgen : Algebra.adjoin A {t} = (⊤ : Subalgebra A B)) :
    Module.finrank k B ≤
      Module.finrank k (A ⧸ Ideal.span ({n2 * d1 - n1 * d2} : Set A)) := by
  -- `t`'s value is forced: from `ht1`, `t = d1⁻¹ * n1` in `B` (the same
  -- computation `aeval_linearElimPoly_eq_zero_iff` + `linearElimMonicPoly`
  -- already package at the `AdjoinRoot` level; here we need it directly
  -- in `B`).
  have ht1' : (Polynomial.aeval t) (linearElimMonicPoly n1 d1 hd1) = 0 :=
    (aeval_linearElimPoly_eq_zero_iff n1 d1 hd1 t).mp ht1
  have htval : t = algebraMap A B (↑hd1.unit⁻¹ * n1) := by
    have h := ht1'
    unfold linearElimMonicPoly at h
    rw [Polynomial.aeval_def, Polynomial.eval₂_sub, Polynomial.eval₂_X,
      Polynomial.eval₂_C, sub_eq_zero] at h
    rw [h]
  -- Substitute into `ht2` to get the resultant vanishing directly in `B`.
  have hres_zero : algebraMap A B (↑hd1.unit⁻¹ * (n2 * d1 - n1 * d2)) = 0 := by
    have h2 : algebraMap A B n2 - t * algebraMap A B d2 = 0 := by
      have := ht2
      unfold linearElimPoly at this
      rwa [Polynomial.aeval_def, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
        Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_C] at this
    rw [htval] at h2
    -- `h2 : algebraMap A B n2 - algebraMap A B (↑hd1.unit⁻¹ * n1) * algebraMap A B d2 = 0`
    have hd1u : d1 * (↑hd1.unit⁻¹ : A) = 1 := by
      nth_rewrite 1 [← hd1.unit_spec]
      exact hd1.unit.mul_inv
    -- Pure `A`-side identity: `u * (n2*d1 - n1*d2) = n2 - (u*n1)*d2`, using `d1*u = 1`.
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
  -- So `B` is an `A ⧸ Ideal.span {n2*d1 - n1*d2}`-algebra factoring
  -- through `algebraMap A B`, and `t ∈ Algebra.adjoin A {t} = ⊤` means
  -- `B` is generated over that smaller ring too. Bound `finrank` via
  -- `hgen` and the fact that `t` itself lies in the image of
  -- `algebraMap A B` (from `htval`), so `Algebra.adjoin (A ⧸ ...) {t}`
  -- (via the induced algebra map) is still all of `B` — in fact `B` is
  -- already generated by the IMAGE of `A` alone (no `t` needed beyond
  -- what `A`'s image supplies), since `htval` shows `t` is literally
  -- `algebraMap A B` applied to an `A`-element.
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
  -- `algebraMap A B` factors through `A ⧸ Ideal.span {n2*d1-n1*d2}`
  -- (since that ideal maps to `0`, `hres_zero'`), giving a surjective
  -- `k`-linear map from the resultant quotient onto `B`.
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
  -- `ψ` is `k`-linear (both sides are `k`-algebras via `A`, and `ψ`
  -- commutes with `algebraMap A ·` by `Ideal.Quotient.lift_mk`, hence
  -- with `algebraMap k ·` via `IsScalarTower`).
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
  exact LinearMap.finrank_le_finrank_of_surjective hψₗ_surj

end Genus2Lean
