import Mathlib
import Genus2Lean.ZeroD.CAWitnessTangent
import Genus2Lean.ZeroD.CAWitnessDivisorTangent

/-!
# The five-point divisor identity for `CAWitnessTangent.lean`'s
tangent-case `f := y - bCATangent(x)`

`ROADMAP-principal-witness-tangent-assembly.md`'s Step 3. Tangent-case
sibling of `CAWitnessDivisor.lean`'s `divToPair_eq_C_add_iotaA_of_split`,
now that Step 2's `ordAt_denomCATangent_eq_two_at_Ra`/`_eq_one_at_P1`/
`_eq_one_at_P2` (`CAWitnessDivisorTangent.lean`) supply the needed
`hA_ord` facts. Support set shrinks from the split case's four points to
THREE (`{Ra, PtιP1, PtιP2}`), and `Ra` carries coefficient `2`, not two
separate `single Ra1 + single Ra2` — matching the roadmap's stated
conclusion shape `2•single Ra + single ιP1 + single ιP2` (one fewer case
than the split case's six-point `by_cases` chain needs, in the sense
that `PtRa1`/`PtRa2` collapse into a single `by_cases` branch here).

**`hg_ne_eval` at `Ra`**: same computation as the split case's `Ra1`/
`Ra2` branches (`bCATangent.eval RaX = RaY` from `bCATangent_eval_Ra`,
then the `-RaY - RaY ≠ 0` non-Weierstrass argument via `hchar`), just
run once instead of twice — `bCATangent`'s row-0 identity plays exactly
the role `bCA_eval_Ra1`/`bCA_eval_Ra2` played there, since the doubled
node still has a single, well-defined `eval` value (`RaY`) even though
it also carries a derivative condition. -/

noncomputable section

open HyperellipticPolynomial
open HyperellipticPolynomial.Divisor
open Polynomial

namespace Genus2Lean
namespace DecoupledSystem

variable {k : Type*} [Field k] [DecidableEq k]
variable {H : HyperellipticPolynomial k} [IsDedekindDomain (CoordinateRing H)]

/-- **`f`'s divisor restricted to the three named points, tangent case:
`2•[Ra] + [ιP1] + [ιP2]`.** `f := toPair H (-bCATangent) 1`. `Ra` is the
doubled anchor root (`Ra1 = Ra2`); `PtιP1, PtιP2` are the hyperelliptic
conjugates of `P1, P2`, same convention as the split case. Mirrors
`divToPair_eq_C_add_iotaA_of_split` exactly, `hOrdRa`/`hOrdιP1`/
`hOrdιP2` supplied via `ordAt_eq_two_of_old_point`/
`ordAt_eq_one_of_old_point` (`PrincipalWitness.lean`) composed with
`ordAt_denomCATangent_eq_two_at_Ra`/`_eq_one_at_P1`/`_eq_one_at_P2`
(`CAWitnessDivisorTangent.lean`) for their respective `hA_ord`. -/
theorem divToPair_eq_C_add_iotaA_of_split_tangent
    [DecidableEq H.Point]
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (RaX P1X P2X RaY P1Y P2Y vaDerivAtRa : k)
    (hdet : (caTangentInterpMatrix RaX P1X P2X).det ≠ 0)
    (h1 : RaX ≠ P1X) (h2 : RaX ≠ P2X) (hPP : P1X ≠ P2X)
    (hRa_curve : RaY ^ 2 = H.f.eval RaX)
    (hP1_curve : P1Y ^ 2 = H.f.eval P1X) (hP2_curve : P2Y ^ 2 = H.f.eval P2X)
    (hRaDeriv : 2 * RaY * vaDerivAtRa = (derivative H.f).eval RaX)
    (hRaY_ne : RaY ≠ 0) (hP1Y_ne : P1Y ≠ 0) (hP2Y_ne : P2Y ≠ 0)
    (PtRa PtιP1 PtιP2 : H.Point)
    (hPtRaX : PtRa.X = RaX) (hPtRaY : PtRa.Y = RaY)
    (hPtιP1X : PtιP1.X = P1X) (hPtιP1Y : PtιP1.Y = -P1Y)
    (hPtιP2X : PtιP2.X = P2X) (hPtιP2Y : PtιP2.Y = -P2Y)
    (hne : H.f - (bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) ^ 2 ≠ 0)
    (hU_evalRa : (uCANewTangent H RaX P1X P2X RaY vaDerivAtRa P1Y P2Y).eval RaX ≠ 0)
    (hU_evalP1 : (uCANewTangent H RaX P1X P2X RaY vaDerivAtRa P1Y P2Y).eval P1X ≠ 0)
    (hU_evalP2 : (uCANewTangent H RaX P1X P2X RaY vaDerivAtRa P1Y P2Y).eval P2X ≠ 0) :
    divToPair (-bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) (1 : k[X])
        ({PtRa, PtιP1, PtιP2} : Finset H.Point) =
      (2 : ℤ) • single PtRa + single PtιP1 + single PtιP2 := by
  have h_bot : ∀ P : H.Point, pointIdeal P ≠ ⊥ := pointIdeal_ne_bot
  have hg_ne : toPair H (-bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) (1 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨_, hB⟩ => one_ne_zero hB
  have hAU : pairNorm H (-bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) (1 : k[X]) =
      denomPolyCATangent RaX P1X P2X *
        (-uCANewTangent H RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) := by
    unfold pairNorm
    have hfact := pairNormBCATangent_eq_denomPolyCATangent_mul_uCANewTangent H
      RaX P1X P2X RaY vaDerivAtRa P1Y P2Y hdet h1 h2 hPP
      hRa_curve hP1_curve hP2_curve hRaDeriv hne
    have : (bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) ^ 2 - (1 : k[X]) ^ 2 * H.f =
        -(H.f - (bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) ^ 2) := by ring
    rw [neg_sq, this, hfact]
    ring
  have hdenom_ne : denomPolyCATangent RaX P1X P2X ≠ 0 := by
    unfold denomPolyCATangent
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (X_sub_C_ne_zero RaX))
      (X_sub_C_ne_zero P1X)) (X_sub_C_ne_zero P2X)
  have hA_ne : toPair H (denomPolyCATangent RaX P1X P2X) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => hdenom_ne hA
  have hU_ne : toPair H (-uCANewTangent H RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    rintro ⟨hA, -⟩
    have : (uCANewTangent H RaX P1X P2X RaY vaDerivAtRa P1Y P2Y).eval RaX = 0 := by
      rw [neg_eq_zero] at hA; rw [hA]; simp
    exact hU_evalRa this
  -- The three pointwise `ordAt` facts.
  have hOrdRa : ordAt PtRa (-bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) (1 : k[X]) = 2 := by
    apply ordAt_eq_two_of_old_point PtRa (h_bot PtRa) _ _
      (denomPolyCATangent RaX P1X P2X) (-uCANewTangent H RaX P1X P2X RaY vaDerivAtRa P1Y P2Y)
      hg_ne _ hAU hA_ne hU_ne _ _
    · show (-bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y).eval PtRa.X +
          (-(1 : k[X])).eval PtRa.X * PtRa.Y ≠ 0
      simp only [hPtRaX, hPtRaY, eval_neg, eval_one]
      rw [bCATangent_eval_Ra RaX P1X P2X RaY vaDerivAtRa P1Y P2Y hdet]
      intro hcontra
      apply hRaY_ne
      have h2R : (2 : k) * RaY = 0 := by
        have : -RaY + (-1 : k) * RaY = -(2 * RaY) := by ring
        rw [this] at hcontra
        exact neg_eq_zero.mp hcontra
      rcases mul_eq_zero.mp h2R with h | h
      · exact absurd h hchar
      · exact h
    · exact ordAt_denomCATangent_eq_two_at_Ra hchar hsf RaX P1X P2X h1 h2
        PtRa (h_bot PtRa) hPtRaX (hPtRaY ▸ hRaY_ne)
    · simp only [hPtRaX, eval_neg]
      simpa using hU_evalRa
  have hOrdιP1 : ordAt PtιP1 (-bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) (1 : k[X]) = 1 := by
    apply ordAt_eq_one_of_old_point PtιP1 (h_bot PtιP1) _ _
      (denomPolyCATangent RaX P1X P2X) (-uCANewTangent H RaX P1X P2X RaY vaDerivAtRa P1Y P2Y)
      hg_ne _ hAU hA_ne hU_ne _ _
    · show (-bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y).eval PtιP1.X +
          (-(1 : k[X])).eval PtιP1.X * PtιP1.Y ≠ 0
      simp only [hPtιP1X, hPtιP1Y, eval_neg, eval_one]
      rw [bCATangent_eval_P1 RaX P1X P2X RaY vaDerivAtRa P1Y P2Y hdet]
      intro hcontra
      apply hP1Y_ne
      have h2R : (2 : k) * P1Y = 0 := by
        have : -(-P1Y) + (-1 : k) * (-P1Y) = 2 * P1Y := by ring
        rw [this] at hcontra
        exact hcontra
      rcases mul_eq_zero.mp h2R with h | h
      · exact absurd h hchar
      · exact h
    · exact ordAt_denomCATangent_eq_one_at_P1 hchar hsf RaX P1X P2X h1 hPP
        PtιP1 (h_bot PtιP1) hPtιP1X (by rw [hPtιP1Y]; exact neg_ne_zero.mpr hP1Y_ne)
    · simp only [hPtιP1X, eval_neg]
      simpa using hU_evalP1
  have hOrdιP2 : ordAt PtιP2 (-bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) (1 : k[X]) = 1 := by
    apply ordAt_eq_one_of_old_point PtιP2 (h_bot PtιP2) _ _
      (denomPolyCATangent RaX P1X P2X) (-uCANewTangent H RaX P1X P2X RaY vaDerivAtRa P1Y P2Y)
      hg_ne _ hAU hA_ne hU_ne _ _
    · show (-bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y).eval PtιP2.X +
          (-(1 : k[X])).eval PtιP2.X * PtιP2.Y ≠ 0
      simp only [hPtιP2X, hPtιP2Y, eval_neg, eval_one]
      rw [bCATangent_eval_P2 RaX P1X P2X RaY vaDerivAtRa P1Y P2Y hdet]
      intro hcontra
      apply hP2Y_ne
      have h2R : (2 : k) * P2Y = 0 := by
        have : -(-P2Y) + (-1 : k) * (-P2Y) = 2 * P2Y := by ring
        rw [this] at hcontra
        exact hcontra
      rcases mul_eq_zero.mp h2R with h | h
      · exact absurd h hchar
      · exact h
    · exact ordAt_denomCATangent_eq_one_at_P2 hchar hsf RaX P1X P2X h2 hPP
        PtιP2 (h_bot PtιP2) hPtιP2X (by rw [hPtιP2Y]; exact neg_ne_zero.mpr hP2Y_ne)
    · simp only [hPtιP2X, eval_neg]
      simpa using hU_evalP2
  -- Pairwise distinctness of the three named points, as `H.Point` values.
  have hne_of_X : ∀ {Q1 Q2 : H.Point}, Q1.X ≠ Q2.X → Q1 ≠ Q2 :=
    fun hX heq => hX (heq ▸ rfl)
  have hRaιP1' : PtRa ≠ PtιP1 := hne_of_X (hPtRaX ▸ hPtιP1X ▸ h1)
  have hRaιP2' : PtRa ≠ PtιP2 := hne_of_X (hPtRaX ▸ hPtιP2X ▸ h2)
  have hPP' : PtιP1 ≠ PtιP2 := hne_of_X (hPtιP1X ▸ hPtιP2X ▸ hPP)
  apply eq_of_coeffAt_eq
  intro P
  rw [coeffAt_divToPair]
  simp only [map_add, map_zsmul, coeffAt_single, smul_eq_mul]
  by_cases hEqRa : P = PtRa
  · rw [hEqRa]
    simpa [hOrdRa, hRaιP1', hRaιP2']
  by_cases hEqιP1 : P = PtιP1
  · rw [hEqιP1]
    have hιP1Ra' : PtιP1 ≠ PtRa := hRaιP1'.symm
    simpa [hOrdιP1, hιP1Ra', hPP']
  by_cases hEqιP2 : P = PtιP2
  · rw [hEqιP2]
    have hιP2Ra' : PtιP2 ≠ PtRa := hRaιP2'.symm
    have hιP2ιP1' : PtιP2 ≠ PtιP1 := hPP'.symm
    simpa [hOrdιP2, hιP2Ra', hιP2ιP1']
  · have hnmemS : P ∉ ({PtRa, PtιP1, PtιP2} : Finset H.Point) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push_neg
      exact ⟨hEqRa, hEqιP1, hEqιP2⟩
    simp only [if_neg hnmemS, if_neg hEqRa, if_neg hEqιP1, if_neg hEqιP2]
    ring

end DecoupledSystem
end Genus2Lean
