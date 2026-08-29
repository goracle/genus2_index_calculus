import Mathlib
import Genus2Lean.ZeroD.CAWitnessTangentTarget
import Genus2Lean.ZeroD.PrincipalWitness
import Genus2Lean.LPairFinrankOneOrdAtFrac

/-!
# The residual-point `ordAt` fact for `CAWitnessTangentTarget.lean`'s
# `f := y - bCATangentTarget(x)`

Target-axis sibling of `CAWitnessResidualTangent.lean` (itself the
anchor-axis sibling of `CAWitnessResidual.lean`). Same reason this
piece is needed, one axis over: `f` also vanishes on the roots of the
residual quadratic `uCANewTangentTarget` (equivalently `T1, T2`), which
are never among `f`'s named interpolation nodes — the support-widening
fix `PrincipalWitnessStep4Tangent.lean`'s own docstring already flags
for the anchor axis applies identically here.

Exactly the same recipe as `CAWitnessResidualTangent.lean`, with
`bCATangent → bCATangentTarget`, `denomPolyCATangent →
denomPolyCATangentTarget`, `uCANewTangent → uCANewTangentTarget`,
`caTangentInterpMatrix → caTangentTargetInterpMatrix`.
`uCANewTangentTarget` is still a single atomic polynomial, so
`ordAt_eq_rootMultiplicity_unramified` (`LPairFinrankOneOrdAtFrac.
lean`) again applies to it directly, covering both `T1X`'s and `T2X`'s
simple-root case (`m = 1`) uniformly. -/

noncomputable section

open Polynomial
open HyperellipticPolynomial
open HyperellipticPolynomial.Divisor

namespace Genus2Lean
namespace DecoupledSystem

variable {k : Type*} [Field k] [DecidableEq k]
variable {H : HyperellipticPolynomial k} [IsDedekindDomain (CoordinateRing H)]

/-- **`f`'s `ordAt` at a root of the target-tangent-case residual
factor `uCANewTangentTarget`, expressed via `uCANewTangentTarget`'s own
`rootMultiplicity` — no pre-split, no distinct-root hypothesis.**
Target-axis sibling of `ordAt_eq_rootMultiplicity_of_uCANewTangent_
root` (`CAWitnessResidualTangent.lean`), same proof shape verbatim
with the target-tangent objects substituted throughout. -/
theorem ordAt_eq_rootMultiplicity_of_uCANewTangentTarget_root
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP : k)
    (hdet : (caTangentTargetInterpMatrix Ra1X Ra2X PX).det ≠ 0)
    (h1 : Ra1X ≠ PX) (h2 : Ra2X ≠ PX) (h12 : Ra1X ≠ Ra2X)
    (hRa1_curve : Ra1Y ^ 2 = H.f.eval Ra1X) (hRa2_curve : Ra2Y ^ 2 = H.f.eval Ra2X)
    (hP_curve : PY ^ 2 = H.f.eval PX)
    (hPDeriv : 2 * PY * vDerivAtP = (derivative H.f).eval PX)
    (P : H.Point) (h_bot : pointIdeal P ≠ ⊥)
    (hU_ne0 : uCANewTangentTarget H Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP ≠ 0)
    (hAeval : (denomPolyCATangentTarget Ra1X Ra2X PX : k[X]).eval P.X ≠ 0)
    (hPY : P.Y = (bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP).eval P.X)
    (hPY_ne : P.Y ≠ 0)
    (m : ℕ)
    (hUmult : Polynomial.rootMultiplicity P.X
      (uCANewTangentTarget H Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP) = m) :
    ordAt P (-bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP : k[X]) (1 : k[X]) =
      (m : ℤ) := by
  have hne : H.f - (bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP) ^ 2 ≠ 0 := by
    intro hcontra
    apply hU_ne0
    show uCANewTangentTarget H Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP = 0
    unfold uCANewTangentTarget
    rw [hcontra, Polynomial.zero_divByMonic]
  set E := -bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP with hE_def
  set U := uCANewTangentTarget H Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP with hU_def
  set A := denomPolyCATangentTarget Ra1X Ra2X PX with hA_def
  have hAUraw : pairNorm H E (1 : k[X]) = A * (-U) := by
    unfold pairNorm
    have hfact := pairNormBCATangentTarget_eq_denomPolyCATangentTarget_mul_uCANewTangentTarget H
      Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP hdet h1 h2 h12
      hRa1_curve hRa2_curve hP_curve hPDeriv hne
    have hring : (bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP) ^ 2 -
        (1 : k[X]) ^ 2 * H.f =
        -(H.f - (bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP) ^ 2) := by ring
    rw [hE_def, neg_sq, hring, hfact]
    ring
  have hg_ne : toPair H E (1 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨_, hB⟩ => one_ne_zero hB
  have hA_ne0 : A ≠ 0 := by
    rw [hA_def]
    unfold denomPolyCATangentTarget
    exact mul_ne_zero (mul_ne_zero (X_sub_C_ne_zero Ra1X) (X_sub_C_ne_zero Ra2X))
      (pow_ne_zero 2 (X_sub_C_ne_zero PX))
  have hA_ne : toPair H A (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA0, _⟩ => hA_ne0 hA0
  have hUneg_ne0 : (-U : k[X]) ≠ 0 := neg_ne_zero.mpr hU_ne0
  have hU_ne : toPair H (-U) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA0, _⟩ => hUneg_ne0 hA0
  have hgbar_ne_eval : E.eval P.X + (-(1 : k[X])).eval P.X * P.Y ≠ 0 := by
    rw [hE_def]
    simp only [eval_neg, eval_one]
    rw [hPY]
    intro hcontra
    have h2 : (2 : k) *
        (bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP).eval P.X = 0 := by
      linear_combination -hcontra
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h hchar
    · apply hPY_ne
      rw [hPY, h]
  have hN_eq_mult : ordAt P E (1 : k[X]) = ordAt P (pairNorm H E (1 : k[X])) (0 : k[X]) :=
    ordAt_eq_ordAt_pairNorm_of_eval_eq_zero P h_bot E (1 : k[X]) hg_ne hgbar_ne_eval
  have hA_ord : ordAt P A (0 : k[X]) = 0 := by
    have hAmult : Polynomial.rootMultiplicity P.X A = 0 :=
      Polynomial.rootMultiplicity_eq_zero (by
        rw [Polynomial.IsRoot]; exact hAeval)
    have := ordAt_eq_rootMultiplicity_unramified (H := H) hchar A hA_ne0 P.X P h_bot rfl hPY_ne
    rw [this, hAmult]
    norm_num
  have hU_ord : ordAt P (-U) (0 : k[X]) = (m : ℤ) := by
    have hUneg_eq : (-U : k[X]) = Polynomial.C (-1 : k) * U := by
      rw [map_neg, map_one, neg_mul, one_mul]
    have hCU_ne : (Polynomial.C (-1 : k) * U : k[X]) ≠ 0 := hUneg_eq ▸ hUneg_ne0
    have hUneg_mult :
        Polynomial.rootMultiplicity P.X (-U : k[X]) = Polynomial.rootMultiplicity P.X U := by
      rw [hUneg_eq, Polynomial.rootMultiplicity_mul hCU_ne, Polynomial.rootMultiplicity_C]
      norm_num
    have := ordAt_eq_rootMultiplicity_unramified (H := H) hchar (-U) hUneg_ne0 P.X P h_bot rfl
      hPY_ne
    rw [this, hUneg_mult, hUmult]
  rw [hN_eq_mult, hAUraw,
    ordAt_add_of_pairNorm_eq_mul P h_bot (A * (-U)) A (-U) rfl hA_ne hU_ne, hA_ord, hU_ord]
  norm_num

end DecoupledSystem
end Genus2Lean
