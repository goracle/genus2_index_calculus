import Mathlib
import Genus2Lean.ZeroD.CAWitnessTangent
import Genus2Lean.ZeroD.PrincipalWitness
import Genus2Lean.LPairFinrankOneOrdAtFrac

/-!
# The residual-point `ordAt` fact for `CAWitnessTangent.lean`'s
# `f := y - bCATangent(x)`

Tangent-case sibling of `CAWitnessResidual.lean`. That file's own
docstring already explains why the split case needed this as a
separate piece from `CAWitnessDivisor.lean`'s named-point facts: `f`
also vanishes on the roots of the residual quadratic `uCANew`
(equivalently `T1, T2`), which are never among `f`'s named
interpolation nodes — a fact `PrincipalWitnessStep4Tangent.lean`'s
`cIotaAmIotaT_mem_principalSubgroup_tangent` had been missing entirely
(its `hsupp_f` claimed `ordAt P f = 0` for every `P` outside
`{PtRa, PtιP1, PtιP2}`, which is false at `PtT1, PtT2` — see that
file's corrected docstring/signature for the fix this theorem feeds).

Exactly the same recipe as `CAWitnessResidual.lean`, with `bCA →
bCATangent`, `denomPolyCA → denomPolyCATangent`, `uCANew →
uCANewTangent`, `caInterpMatrix → caTangentInterpMatrix`. `uCANewTangent`
is still a single atomic polynomial (a residual, not a product of named
factors), so `ordAt_eq_rootMultiplicity_unramified`
(`LPairFinrankOneOrdAtFrac.lean`) again applies to it directly, with no
named-root hypothesis and no pre-split — `hUmult` is left opaque exactly
as in the split-case file, so this one theorem covers both `T1X`'s and
`T2X`'s simple-root case (`m = 1`) uniformly, without assuming anything
about how many roots `uCANewTangent` has or how they relate to `RaX`
(which is provably distinct from both, but this file doesn't need that
fact to go through). -/

noncomputable section

open Polynomial
open HyperellipticPolynomial
open HyperellipticPolynomial.Divisor

namespace Genus2Lean
namespace DecoupledSystem

variable {k : Type*} [Field k] [DecidableEq k]
variable {H : HyperellipticPolynomial k} [IsDedekindDomain (CoordinateRing H)]

/-- **`f`'s `ordAt` at a root of the tangent-case residual factor
`uCANewTangent`, expressed via `uCANewTangent`'s own `rootMultiplicity` —
no pre-split, no distinct-root hypothesis.** Tangent sibling of
`ordAt_eq_rootMultiplicity_of_uCANew_root` (`CAWitnessResidual.lean`),
same proof shape verbatim with the tangent objects substituted
throughout.

**Sign note** (carried over unchanged): `hPY : P.Y =
bCATangent.eval P.X` pins `P` to the branch where `f = y -
bCATangent(x)` itself vanishes, which is what makes `hgbar_ne_eval`
provable from `hchar`/`hPY_ne` alone. -/
theorem ordAt_eq_rootMultiplicity_of_uCANewTangent_root
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (RaX P1X P2X RaY vaDerivAtRa P1Y P2Y : k)
    (hdet : (caTangentInterpMatrix RaX P1X P2X).det ≠ 0)
    (h1 : RaX ≠ P1X) (h2 : RaX ≠ P2X) (h3 : P1X ≠ P2X)
    (hRa_curve : RaY ^ 2 = H.f.eval RaX)
    (hP1_curve : P1Y ^ 2 = H.f.eval P1X) (hP2_curve : P2Y ^ 2 = H.f.eval P2X)
    (hRaDeriv : 2 * RaY * vaDerivAtRa = (derivative H.f).eval RaX)
    (P : H.Point) (h_bot : pointIdeal P ≠ ⊥)
    (hU_ne0 : uCANewTangent H RaX P1X P2X RaY vaDerivAtRa P1Y P2Y ≠ 0)
    (hAeval : (denomPolyCATangent RaX P1X P2X : k[X]).eval P.X ≠ 0)
    (hPY : P.Y = (bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y).eval P.X)
    (hPY_ne : P.Y ≠ 0)
    (m : ℕ)
    (hUmult : Polynomial.rootMultiplicity P.X
      (uCANewTangent H RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) = m) :
    ordAt P (-bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y : k[X]) (1 : k[X]) = (m : ℤ) := by
  -- `H.f - bCATangent² ≠ 0`: if it were `0`, `uCANewTangent`'s own
  -- definition (`(H.f - bCATangent²) /ₘ denomPolyCATangent`) would force
  -- `uCANewTangent = 0` too, contradicting `hU_ne0`.
  have hne : H.f - (bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) ^ 2 ≠ 0 := by
    intro hcontra
    apply hU_ne0
    show uCANewTangent H RaX P1X P2X RaY vaDerivAtRa P1Y P2Y = 0
    unfold uCANewTangent
    rw [hcontra, Polynomial.zero_divByMonic]
  set E := -bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y with hE_def
  set U := uCANewTangent H RaX P1X P2X RaY vaDerivAtRa P1Y P2Y with hU_def
  set A := denomPolyCATangent RaX P1X P2X with hA_def
  -- `pairNorm H E 1 = A * (-U)`.
  have hAUraw : pairNorm H E (1 : k[X]) = A * (-U) := by
    unfold pairNorm
    have hfact := pairNormBCATangent_eq_denomPolyCATangent_mul_uCANewTangent H
      RaX P1X P2X RaY vaDerivAtRa P1Y P2Y hdet h1 h2 h3
      hRa_curve hP1_curve hP2_curve hRaDeriv hne
    have hring : (bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) ^ 2 - (1 : k[X]) ^ 2 * H.f =
        -(H.f - (bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) ^ 2) := by ring
    rw [hE_def, neg_sq, hring, hfact]
    ring
  have hg_ne : toPair H E (1 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨_, hB⟩ => one_ne_zero hB
  have hA_ne0 : A ≠ 0 := by
    rw [hA_def]
    unfold denomPolyCATangent
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (X_sub_C_ne_zero RaX))
      (X_sub_C_ne_zero P1X)) (X_sub_C_ne_zero P2X)
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
    have h2 : (2 : k) * (bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y).eval P.X = 0 := by
      linear_combination -hcontra
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h hchar
    · apply hPY_ne
      rw [hPY, h]
  -- `ordAt P E 1 = ordAt P (pairNorm H E 1) 0` (lemma 4/6).
  have hN_eq_mult : ordAt P E (1 : k[X]) = ordAt P (pairNorm H E (1 : k[X])) (0 : k[X]) :=
    ordAt_eq_ordAt_pairNorm_of_eval_eq_zero P h_bot E (1 : k[X]) hg_ne hgbar_ne_eval
  -- `ordAt P A 0 = 0` — `P` not a root of `denomPolyCATangent`, via
  -- `rootMultiplicity` directly.
  have hA_ord : ordAt P A (0 : k[X]) = 0 := by
    have hAmult : Polynomial.rootMultiplicity P.X A = 0 :=
      Polynomial.rootMultiplicity_eq_zero (by
        rw [Polynomial.IsRoot]; exact hAeval)
    have := ordAt_eq_rootMultiplicity_unramified (H := H) hchar A hA_ne0 P.X P h_bot rfl hPY_ne
    rw [this, hAmult]
    norm_num
  -- `ordAt P (-U) 0 = U.rootMultiplicity P.X = m` — `rootMultiplicity`
  -- directly, no pre-factorization, unit-scaling-invariant.
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
  -- Assemble: `ordAt P E 1 = ordAt P (A*(-U)) 0 = ordAt P A 0 + ordAt P (-U) 0 = 0 + m`.
  rw [hN_eq_mult, hAUraw,
    ordAt_add_of_pairNorm_eq_mul P h_bot (A * (-U)) A (-U) rfl hA_ne hU_ne, hA_ord, hU_ord]
  norm_num

end DecoupledSystem
end Genus2Lean
