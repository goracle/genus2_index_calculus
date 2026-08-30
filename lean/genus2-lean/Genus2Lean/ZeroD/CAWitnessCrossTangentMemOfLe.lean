import Mathlib
import Genus2Lean.ZeroD.CAWitnessCrossTangent1Assembly
import Genus2Lean.ZeroD.CAWitnessCrossTangent2Assembly
import Genus2Lean.ZeroD.CAWitnessCrossTangent3Assembly
import Genus2Lean.ZeroD.CAWitnessCrossTangent4Assembly
import Genus2Lean.ZeroD.PrincipalWitnessStep4
import Genus2Lean.ZeroD.PrincipalWitnessFinalAssembly

/-! # Cross-pair tangent variants: `hD`-pushforward layer
(`ROADMAP-cawitness-tangent-interpolation.md`, Part B, case 3,
"still open" wiring item)

**Purpose.** `CAWitnessCrossTangent{1,2,3,4}Assembly.lean` each already
supply, sorry-free, `cIotaAmIotaT_mem_principalSubgroup_crossN` — the
raw `principalSubgroup`-membership fact on the honest five-point
support (one doubled node, two ordinary points, two residual `T`
points), mirroring the split case's `cIotaAmIotaT_mem_principalSubgroup`
before it is pushed forward along `hD` and rewritten into the explicit
`single`-sum shape (†) needs.

This file does exactly that pushforward/rewrite step, mirroring
`PrincipalWitnessFinalAssembly.lean`'s `cIotaAmIotaT_mem_of_le` line for
line, once per variant — the "mechanical wiring exercise" the roadmap's
Part B, case 3 note said would become available once all four
`bCACross*`/`uCANewCross*` layer-3 assemblies existed (they now do, see
that doc's own step 5 update).

**Also done, this pass**: the further `cAmιTmδmιδ_mem_of_le_crossN`-style
`G₁-G₂-G₃` composition, for all four variants, using
`fiber_diff_mem_of_le` (`PrincipalWitnessFinalAssembly.lean`, imported
here) called against the doubled node and the surviving un-doubled
target point per variant — the same `G₂,G₃ := fiber_diff_mem_of_le`
pattern `PrincipalWitnessFinalAssembly.lean`'s own `cAmιTmδmιδ_mem_of_le`
uses, just against a three-point (not four-point) surviving support.
**Not attempted here**: the eventual top-level
`reducedClass_eq_of_isReduction'`-style theorem consuming these four
(†)-shaped facts. -/

noncomputable section

open Polynomial
open HyperellipticPolynomial
open HyperellipticPolynomial.Divisor

namespace Genus2Lean
namespace DecoupledSystem

variable {k : Type*} [Field k] [DecidableEq k]
variable {H : HyperellipticPolynomial k} [IsDedekindDomain (CoordinateRing H)]

/-- **Cross variant 1 (`Ra1 = ι(sa.P1)`), `hD`-pushforward: `2•[PtRa] +
[PtRa2] + [PtιP2] - [ιT1] - [ιT2] - [δ₀] - [ιδ₀] ∈ D.P`.** Direct mirror
of `cIotaAmIotaT_mem_of_le`: push `cIotaAmIotaT_mem_principalSubgroup_cross1`
forward along `hD`, then rewrite both `f`'s and `h_T`'s divisors into
their explicit `single`-sum values
(`divToPair_eq_C_add_iotaA_add_T_of_split_cross1`, `divToPair_hT_eq`)
and cancel the shared `[PtT1]+[PtT2]` terms via `abel`. -/
theorem cIotaAmIotaT_mem_of_le_cross1
    [DecidableEq H.Point]
    (hdeg : H.f.natDegree = 5)
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (D : PrincipalDivisorData H) (hD : principalSubgroup H hdeg ≤ D.P)
    (RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y : k)
    (hdet : (caCrossInterpMatrix RaX Ra2X P2X).det ≠ 0)
    (hlead : caCrossCoeff RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y 3 ≠ 0)
    (h1 : RaX ≠ Ra2X) (h2 : RaX ≠ P2X) (h3 : Ra2X ≠ P2X)
    (hRa_curve : RaY ^ 2 = H.f.eval RaX) (hRa2_curve : Ra2Y ^ 2 = H.f.eval Ra2X)
    (hP2_curve : P2Y ^ 2 = H.f.eval P2X)
    (hP1Deriv : 2 * RaY * (-vDerivAtP1) = (derivative H.f).eval RaX)
    (hRaY_ne : RaY ≠ 0) (hRa2Y_ne : Ra2Y ≠ 0) (hP2Y_ne : P2Y ≠ 0)
    (PtRa PtRa2 PtιP2 : H.Point)
    (hPtRaX : PtRa.X = RaX) (hPtRaY : PtRa.Y = RaY)
    (hPtRa2X : PtRa2.X = Ra2X) (hPtRa2Y : PtRa2.Y = Ra2Y)
    (hPtιP2X : PtιP2.X = P2X) (hPtιP2Y : PtιP2.Y = -P2Y)
    (hne : H.f - (bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) ^ 2 ≠ 0)
    (hU_evalRa : (uCANewCross H RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y).eval RaX ≠ 0)
    (hU_evalRa2 : (uCANewCross H RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y).eval Ra2X ≠ 0)
    (hU_evalP2 : (uCANewCross H RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y).eval P2X ≠ 0)
    (hU_ne0 : uCANewCross H RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y ≠ 0)
    (T1X T2X : k)
    (hT1 : (uCANewCross H RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y).IsRoot T1X)
    (hT2 : (uCANewCross H RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y).IsRoot T2X)
    (hTne : T1X ≠ T2X)
    (Q1 Q2 : Polynomial k)
    (hQ1_def : uCANewCross H RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y =
      (X - C T1X) * (X - C T2X) * Q1)
    (hQ1T1 : Q1.eval T1X ≠ 0)
    (hQ2_def : uCANewCross H RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y =
      (X - C T2X) * (X - C T1X) * Q2)
    (hQ2T2 : Q2.eval T2X ≠ 0)
    (PtT1 PtT2 δ₀ : H.Point)
    (hAeval1 : (denomPolyCACross RaX Ra2X P2X : k[X]).eval PtT1.X ≠ 0)
    (hAeval2 : (denomPolyCACross RaX Ra2X P2X : k[X]).eval PtT2.X ≠ 0)
    (hPtT1X : PtT1.X = T1X)
    (hPtT1Y : PtT1.Y = (bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y).eval PtT1.X)
    (hPtT1Y_ne : PtT1.Y ≠ 0)
    (hPtT2X : PtT2.X = T2X)
    (hPtT2Y : PtT2.Y = (bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y).eval PtT2.X)
    (hPtT2Y_ne : PtT2.Y ≠ 0)
    (hRaT1 : RaX ≠ T1X) (hRaT2 : RaX ≠ T2X)
    (hRa2T1 : Ra2X ≠ T1X) (hRa2T2 : Ra2X ≠ T2X)
    (hP2T1 : P2X ≠ T1X) (hP2T2 : P2X ≠ T2X)
    (h1δ : T1X ≠ δ₀.X) (h2δ : T2X ≠ δ₀.X) (hδY : δ₀.Y ≠ 0)
    (hsupp_f : ∀ P, P ∉ ({PtRa, PtRa2, PtιP2, PtT1, PtT2} : Finset H.Point) →
      ordAt P (-bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) (1 : k[X]) = 0)
    (hspec_f : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span
        ({toPair H (-bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) 1} :
          Set (CoordinateRing H)))).factors ≠ 0 → ∃ P, v.asIdeal = pointIdeal P)
    [∀ P : ({PtRa, PtRa2, PtιP2, PtT1, PtT2} : Finset H.Point),
      Module.Finite k (CoordinateRing H ⧸ pointIdeal P.1 ^
        (ordAt P.1 (-bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) (1 : k[X])).toNat)]
    (hsupp_hT : ∀ P, P ∉ ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀, Point.iota δ₀} :
        Finset H.Point) →
      ordAt P ((linX T1X * linX T2X) * linX δ₀.X) (0 : k[X]) = 0)
    (hspec_hT : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span
        ({toPair H ((linX T1X * linX T2X) * linX δ₀.X) 0} :
          Set (CoordinateRing H)))).factors ≠ 0 → ∃ P, v.asIdeal = pointIdeal P)
    [∀ P : ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀, Point.iota δ₀} : Finset H.Point),
      Module.Finite k (CoordinateRing H ⧸ pointIdeal P.1 ^
        (ordAt P.1 ((linX T1X * linX T2X) * linX δ₀.X) (0 : k[X])).toNat)] :
    ((2 : ℤ) • single PtRa + single PtRa2 + single PtιP2 -
      single (Point.iota PtT1) - single (Point.iota PtT2) -
      single δ₀ - single (Point.iota δ₀) : Divisor H) ∈ D.P := by
  classical
  have hraw := cIotaAmIotaT_mem_principalSubgroup_cross1 (H := H) hdeg hchar hsf
    RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y hdet hlead h1 h2 h3
    hRa_curve hRa2_curve hP2_curve hP1Deriv hRaY_ne hRa2Y_ne hP2Y_ne
    PtRa PtRa2 PtιP2 hPtRaX hPtRaY hPtRa2X hPtRa2Y hPtιP2X hPtιP2Y hne
    hU_evalRa hU_evalRa2 hU_evalP2 T1X T2X hT1 hT2 hTne hU_ne0
    Q1 Q2 hQ1_def hQ1T1 hQ2_def hQ2T2 PtT1 PtT2 δ₀ hAeval1 hAeval2
    hPtT1X hPtT1Y hPtT1Y_ne hPtT2X hPtT2Y hPtT2Y_ne
    hRaT1 hRaT2 hRa2T1 hRa2T2 hP2T1 hP2T2 h1δ h2δ hδY
    hsupp_f hspec_f hsupp_hT hspec_hT
  have hLHS := divToPair_eq_C_add_iotaA_add_T_of_split_cross1 (H := H) hchar hsf
    RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y hdet h1 h2 h3
    hRa_curve hRa2_curve hP2_curve hP1Deriv hRaY_ne hRa2Y_ne hP2Y_ne
    PtRa PtRa2 PtιP2 hPtRaX hPtRaY hPtRa2X hPtRa2Y hPtιP2X hPtιP2Y hne
    hU_evalRa hU_evalRa2 hU_evalP2 hU_ne0 T1X T2X hT1 hT2 hTne
    Q1 Q2 hQ1_def hQ1T1 hQ2_def hQ2T2 PtT1 PtT2 hAeval1 hAeval2
    hPtT1X hPtT1Y hPtT1Y_ne hPtT2X hPtT2Y hPtT2Y_ne
    hRaT1 hRaT2 hRa2T1 hRa2T2 hP2T1 hP2T2
  have hPtT12ne : PtT1.X ≠ PtT2.X := by rw [hPtT1X, hPtT2X]; exact hTne
  have hPtT1δ : PtT1.X ≠ δ₀.X := by rw [hPtT1X]; exact h1δ
  have hPtT2δ : PtT2.X ≠ δ₀.X := by rw [hPtT2X]; exact h2δ
  have hRHS := divToPair_hT_eq (H := H) hchar hsf PtT1 PtT2 δ₀
    hPtT12ne hPtT1δ hPtT2δ hPtT1Y_ne hPtT2Y_ne hδY
  have hmem := hD hraw
  rw [← hPtT1X, ← hPtT2X] at hmem
  rw [hLHS, hRHS] at hmem
  have heq : ((2 : ℤ) • single PtRa + single PtRa2 + single PtιP2 + single PtT1 + single PtT2 -
      (single PtT1 + single PtT2 + single (Point.iota PtT1) + single (Point.iota PtT2) +
        single δ₀ + single (Point.iota δ₀)) : Divisor H) =
      ((2 : ℤ) • single PtRa + single PtRa2 + single PtιP2 -
      single (Point.iota PtT1) - single (Point.iota PtT2) -
      single δ₀ - single (Point.iota δ₀) : Divisor H) := by abel
  rwa [heq] at hmem

/-- **Cross variant 2 (`Ra1 = ι(sa.P2)`), `hD`-pushforward.** Same shape
as `cIotaAmIotaT_mem_of_le_cross1`, ported onto `CAWitnessCrossTangentV2.lean`'s
objects (doubled node `Ra`, ordinary anchor `Ra2`, ordinary target `ιP1`). -/
theorem cIotaAmIotaT_mem_of_le_cross2
    [DecidableEq H.Point]
    (hdeg : H.f.natDegree = 5)
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (D : PrincipalDivisorData H) (hD : principalSubgroup H hdeg ≤ D.P)
    (RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 : k)
    (hdet : (caCross2InterpMatrix RaX Ra2X P1X).det ≠ 0)
    (hlead : caCross2Coeff RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 3 ≠ 0)
    (h1 : RaX ≠ Ra2X) (h2 : RaX ≠ P1X) (h3 : Ra2X ≠ P1X)
    (hRa_curve : RaY ^ 2 = H.f.eval RaX) (hRa2_curve : Ra2Y ^ 2 = H.f.eval Ra2X)
    (hP1_curve : P1Y ^ 2 = H.f.eval P1X)
    (hP2Deriv : 2 * RaY * (-vDerivAtP2) = (derivative H.f).eval RaX)
    (hRaY_ne : RaY ≠ 0) (hRa2Y_ne : Ra2Y ≠ 0) (hP1Y_ne : P1Y ≠ 0)
    (PtRa PtRa2 PtιP1 : H.Point)
    (hPtRaX : PtRa.X = RaX) (hPtRaY : PtRa.Y = RaY)
    (hPtRa2X : PtRa2.X = Ra2X) (hPtRa2Y : PtRa2.Y = Ra2Y)
    (hPtιP1X : PtιP1.X = P1X) (hPtιP1Y : PtιP1.Y = -P1Y)
    (hne : H.f - (bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) ^ 2 ≠ 0)
    (hU_evalRa : (uCANewCross2 H RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2).eval RaX ≠ 0)
    (hU_evalRa2 : (uCANewCross2 H RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2).eval Ra2X ≠ 0)
    (hU_evalP1 : (uCANewCross2 H RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2).eval P1X ≠ 0)
    (hU_ne0 : uCANewCross2 H RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 ≠ 0)
    (T1X T2X : k)
    (hT1 : (uCANewCross2 H RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2).IsRoot T1X)
    (hT2 : (uCANewCross2 H RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2).IsRoot T2X)
    (hTne : T1X ≠ T2X)
    (Q1 Q2 : Polynomial k)
    (hQ1_def : uCANewCross2 H RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 =
      (X - C T1X) * (X - C T2X) * Q1)
    (hQ1T1 : Q1.eval T1X ≠ 0)
    (hQ2_def : uCANewCross2 H RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 =
      (X - C T2X) * (X - C T1X) * Q2)
    (hQ2T2 : Q2.eval T2X ≠ 0)
    (PtT1 PtT2 δ₀ : H.Point)
    (hAeval1 : (denomPolyCACross2 RaX Ra2X P1X : k[X]).eval PtT1.X ≠ 0)
    (hAeval2 : (denomPolyCACross2 RaX Ra2X P1X : k[X]).eval PtT2.X ≠ 0)
    (hPtT1X : PtT1.X = T1X)
    (hPtT1Y : PtT1.Y = (bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2).eval PtT1.X)
    (hPtT1Y_ne : PtT1.Y ≠ 0)
    (hPtT2X : PtT2.X = T2X)
    (hPtT2Y : PtT2.Y = (bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2).eval PtT2.X)
    (hPtT2Y_ne : PtT2.Y ≠ 0)
    (hRaT1 : RaX ≠ T1X) (hRaT2 : RaX ≠ T2X)
    (hRa2T1 : Ra2X ≠ T1X) (hRa2T2 : Ra2X ≠ T2X)
    (hP1T1 : P1X ≠ T1X) (hP1T2 : P1X ≠ T2X)
    (h1δ : T1X ≠ δ₀.X) (h2δ : T2X ≠ δ₀.X) (hδY : δ₀.Y ≠ 0)
    (hsupp_f : ∀ P, P ∉ ({PtRa, PtRa2, PtιP1, PtT1, PtT2} : Finset H.Point) →
      ordAt P (-bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) (1 : k[X]) = 0)
    (hspec_f : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span
        ({toPair H (-bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) 1} :
          Set (CoordinateRing H)))).factors ≠ 0 → ∃ P, v.asIdeal = pointIdeal P)
    [∀ P : ({PtRa, PtRa2, PtιP1, PtT1, PtT2} : Finset H.Point),
      Module.Finite k (CoordinateRing H ⧸ pointIdeal P.1 ^
        (ordAt P.1 (-bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) (1 : k[X])).toNat)]
    (hsupp_hT : ∀ P, P ∉ ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀, Point.iota δ₀} :
        Finset H.Point) →
      ordAt P ((linX T1X * linX T2X) * linX δ₀.X) (0 : k[X]) = 0)
    (hspec_hT : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span
        ({toPair H ((linX T1X * linX T2X) * linX δ₀.X) 0} :
          Set (CoordinateRing H)))).factors ≠ 0 → ∃ P, v.asIdeal = pointIdeal P)
    [∀ P : ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀, Point.iota δ₀} : Finset H.Point),
      Module.Finite k (CoordinateRing H ⧸ pointIdeal P.1 ^
        (ordAt P.1 ((linX T1X * linX T2X) * linX δ₀.X) (0 : k[X])).toNat)] :
    ((2 : ℤ) • single PtRa + single PtRa2 + single PtιP1 -
      single (Point.iota PtT1) - single (Point.iota PtT2) -
      single δ₀ - single (Point.iota δ₀) : Divisor H) ∈ D.P := by
  classical
  have hraw := cIotaAmIotaT_mem_principalSubgroup_cross2 (H := H) hdeg hchar hsf
    RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 hdet hlead h1 h2 h3
    hRa_curve hRa2_curve hP1_curve hP2Deriv hRaY_ne hRa2Y_ne hP1Y_ne
    PtRa PtRa2 PtιP1 hPtRaX hPtRaY hPtRa2X hPtRa2Y hPtιP1X hPtιP1Y hne
    hU_evalRa hU_evalRa2 hU_evalP1 T1X T2X hT1 hT2 hTne hU_ne0
    Q1 Q2 hQ1_def hQ1T1 hQ2_def hQ2T2 PtT1 PtT2 δ₀ hAeval1 hAeval2
    hPtT1X hPtT1Y hPtT1Y_ne hPtT2X hPtT2Y hPtT2Y_ne
    hRaT1 hRaT2 hRa2T1 hRa2T2 hP1T1 hP1T2 h1δ h2δ hδY
    hsupp_f hspec_f hsupp_hT hspec_hT
  have hLHS := divToPair_eq_C_add_iotaA_add_T_of_split_cross2 (H := H) hchar hsf
    RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 hdet h1 h2 h3
    hRa_curve hRa2_curve hP1_curve hP2Deriv hRaY_ne hRa2Y_ne hP1Y_ne
    PtRa PtRa2 PtιP1 hPtRaX hPtRaY hPtRa2X hPtRa2Y hPtιP1X hPtιP1Y hne
    hU_evalRa hU_evalRa2 hU_evalP1 hU_ne0 T1X T2X hT1 hT2 hTne
    Q1 Q2 hQ1_def hQ1T1 hQ2_def hQ2T2 PtT1 PtT2 hAeval1 hAeval2
    hPtT1X hPtT1Y hPtT1Y_ne hPtT2X hPtT2Y hPtT2Y_ne
    hRaT1 hRaT2 hRa2T1 hRa2T2 hP1T1 hP1T2
  have hPtT12ne : PtT1.X ≠ PtT2.X := by rw [hPtT1X, hPtT2X]; exact hTne
  have hPtT1δ : PtT1.X ≠ δ₀.X := by rw [hPtT1X]; exact h1δ
  have hPtT2δ : PtT2.X ≠ δ₀.X := by rw [hPtT2X]; exact h2δ
  have hRHS := divToPair_hT_eq (H := H) hchar hsf PtT1 PtT2 δ₀
    hPtT12ne hPtT1δ hPtT2δ hPtT1Y_ne hPtT2Y_ne hδY
  have hmem := hD hraw
  rw [← hPtT1X, ← hPtT2X] at hmem
  rw [hLHS, hRHS] at hmem
  have heq : ((2 : ℤ) • single PtRa + single PtRa2 + single PtιP1 + single PtT1 + single PtT2 -
      (single PtT1 + single PtT2 + single (Point.iota PtT1) + single (Point.iota PtT2) +
        single δ₀ + single (Point.iota δ₀)) : Divisor H) =
      ((2 : ℤ) • single PtRa + single PtRa2 + single PtιP1 -
      single (Point.iota PtT1) - single (Point.iota PtT2) -
      single δ₀ - single (Point.iota δ₀) : Divisor H) := by abel
  rwa [heq] at hmem

/-- **Cross variant 3 (`Ra2 = ι(sa.P1)`), `hD`-pushforward.** Same shape,
ported onto `CAWitnessCrossTangentV3.lean`'s objects (ordinary anchor
`Ra1`, doubled node `Ra`, ordinary target `ιP2` — the doubled node's
`single` weight sits on the SECOND summand here, matching
`divToPair_eq_C_add_iotaA_add_T_of_split_cross3`'s
`single PtRa1 + (2:ℤ)•single PtRa + ...` conclusion shape, not the
`(2:ℤ)•single PtRa + single PtRa2 + ...` shape variants 1/2 have. -/
theorem cIotaAmIotaT_mem_of_le_cross3
    [DecidableEq H.Point]
    (hdeg : H.f.natDegree = 5)
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (D : PrincipalDivisorData H) (hD : principalSubgroup H hdeg ≤ D.P)
    (Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y : k)
    (hdet : (caCross3InterpMatrix Ra1X RaX P2X).det ≠ 0)
    (hlead : caCross3Coeff Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y 3 ≠ 0)
    (h1 : Ra1X ≠ RaX) (h2 : Ra1X ≠ P2X) (h3 : RaX ≠ P2X)
    (hRa1_curve : Ra1Y ^ 2 = H.f.eval Ra1X) (hRa_curve : RaY ^ 2 = H.f.eval RaX)
    (hP2_curve : P2Y ^ 2 = H.f.eval P2X)
    (hP1Deriv : 2 * RaY * (-vDerivAtP1) = (derivative H.f).eval RaX)
    (hRa1Y_ne : Ra1Y ≠ 0) (hRaY_ne : RaY ≠ 0) (hP2Y_ne : P2Y ≠ 0)
    (PtRa1 PtRa PtιP2 : H.Point)
    (hPtRa1X : PtRa1.X = Ra1X) (hPtRa1Y : PtRa1.Y = Ra1Y)
    (hPtRaX : PtRa.X = RaX) (hPtRaY : PtRa.Y = RaY)
    (hPtιP2X : PtιP2.X = P2X) (hPtιP2Y : PtιP2.Y = -P2Y)
    (hne : H.f - (bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) ^ 2 ≠ 0)
    (hU_evalRa1 : (uCANewCross3 H Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y).eval Ra1X ≠ 0)
    (hU_evalRa : (uCANewCross3 H Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y).eval RaX ≠ 0)
    (hU_evalP2 : (uCANewCross3 H Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y).eval P2X ≠ 0)
    (hU_ne0 : uCANewCross3 H Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y ≠ 0)
    (T1X T2X : k)
    (hT1 : (uCANewCross3 H Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y).IsRoot T1X)
    (hT2 : (uCANewCross3 H Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y).IsRoot T2X)
    (hTne : T1X ≠ T2X)
    (Q1 Q2 : Polynomial k)
    (hQ1_def : uCANewCross3 H Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y =
      (X - C T1X) * (X - C T2X) * Q1)
    (hQ1T1 : Q1.eval T1X ≠ 0)
    (hQ2_def : uCANewCross3 H Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y =
      (X - C T2X) * (X - C T1X) * Q2)
    (hQ2T2 : Q2.eval T2X ≠ 0)
    (PtT1 PtT2 δ₀ : H.Point)
    (hAeval1 : (denomPolyCACross3 Ra1X RaX P2X : k[X]).eval PtT1.X ≠ 0)
    (hAeval2 : (denomPolyCACross3 Ra1X RaX P2X : k[X]).eval PtT2.X ≠ 0)
    (hPtT1X : PtT1.X = T1X)
    (hPtT1Y : PtT1.Y = (bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y).eval PtT1.X)
    (hPtT1Y_ne : PtT1.Y ≠ 0)
    (hPtT2X : PtT2.X = T2X)
    (hPtT2Y : PtT2.Y = (bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y).eval PtT2.X)
    (hPtT2Y_ne : PtT2.Y ≠ 0)
    (hRa1T1 : Ra1X ≠ T1X) (hRa1T2 : Ra1X ≠ T2X)
    (hRaT1 : RaX ≠ T1X) (hRaT2 : RaX ≠ T2X)
    (hP2T1 : P2X ≠ T1X) (hP2T2 : P2X ≠ T2X)
    (h1δ : T1X ≠ δ₀.X) (h2δ : T2X ≠ δ₀.X) (hδY : δ₀.Y ≠ 0)
    (hsupp_f : ∀ P, P ∉ ({PtRa1, PtRa, PtιP2, PtT1, PtT2} : Finset H.Point) →
      ordAt P (-bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) (1 : k[X]) = 0)
    (hspec_f : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span
        ({toPair H (-bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) 1} :
          Set (CoordinateRing H)))).factors ≠ 0 → ∃ P, v.asIdeal = pointIdeal P)
    [∀ P : ({PtRa1, PtRa, PtιP2, PtT1, PtT2} : Finset H.Point),
      Module.Finite k (CoordinateRing H ⧸ pointIdeal P.1 ^
        (ordAt P.1 (-bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) (1 : k[X])).toNat)]
    (hsupp_hT : ∀ P, P ∉ ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀, Point.iota δ₀} :
        Finset H.Point) →
      ordAt P ((linX T1X * linX T2X) * linX δ₀.X) (0 : k[X]) = 0)
    (hspec_hT : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span
        ({toPair H ((linX T1X * linX T2X) * linX δ₀.X) 0} :
          Set (CoordinateRing H)))).factors ≠ 0 → ∃ P, v.asIdeal = pointIdeal P)
    [∀ P : ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀, Point.iota δ₀} : Finset H.Point),
      Module.Finite k (CoordinateRing H ⧸ pointIdeal P.1 ^
        (ordAt P.1 ((linX T1X * linX T2X) * linX δ₀.X) (0 : k[X])).toNat)] :
    (single PtRa1 + (2 : ℤ) • single PtRa + single PtιP2 -
      single (Point.iota PtT1) - single (Point.iota PtT2) -
      single δ₀ - single (Point.iota δ₀) : Divisor H) ∈ D.P := by
  classical
  have hraw := cIotaAmIotaT_mem_principalSubgroup_cross3 (H := H) hdeg hchar hsf
    Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y hdet hlead h1 h2 h3
    hRa1_curve hRa_curve hP2_curve hP1Deriv hRa1Y_ne hRaY_ne hP2Y_ne
    PtRa1 PtRa PtιP2 hPtRa1X hPtRa1Y hPtRaX hPtRaY hPtιP2X hPtιP2Y hne
    hU_evalRa1 hU_evalRa hU_evalP2 T1X T2X hT1 hT2 hTne hU_ne0
    Q1 Q2 hQ1_def hQ1T1 hQ2_def hQ2T2 PtT1 PtT2 δ₀ hAeval1 hAeval2
    hPtT1X hPtT1Y hPtT1Y_ne hPtT2X hPtT2Y hPtT2Y_ne
    hRa1T1 hRa1T2 hRaT1 hRaT2 hP2T1 hP2T2 h1δ h2δ hδY
    hsupp_f hspec_f hsupp_hT hspec_hT
  have hLHS := divToPair_eq_C_add_iotaA_add_T_of_split_cross3 (H := H) hchar hsf
    Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y hdet h1 h2 h3
    hRa1_curve hRa_curve hP2_curve hP1Deriv hRa1Y_ne hRaY_ne hP2Y_ne
    PtRa1 PtRa PtιP2 hPtRa1X hPtRa1Y hPtRaX hPtRaY hPtιP2X hPtιP2Y hne
    hU_evalRa1 hU_evalRa hU_evalP2 hU_ne0 T1X T2X hT1 hT2 hTne
    Q1 Q2 hQ1_def hQ1T1 hQ2_def hQ2T2 PtT1 PtT2 hAeval1 hAeval2
    hPtT1X hPtT1Y hPtT1Y_ne hPtT2X hPtT2Y hPtT2Y_ne
    hRa1T1 hRa1T2 hRaT1 hRaT2 hP2T1 hP2T2
  have hPtT12ne : PtT1.X ≠ PtT2.X := by rw [hPtT1X, hPtT2X]; exact hTne
  have hPtT1δ : PtT1.X ≠ δ₀.X := by rw [hPtT1X]; exact h1δ
  have hPtT2δ : PtT2.X ≠ δ₀.X := by rw [hPtT2X]; exact h2δ
  have hRHS := divToPair_hT_eq (H := H) hchar hsf PtT1 PtT2 δ₀
    hPtT12ne hPtT1δ hPtT2δ hPtT1Y_ne hPtT2Y_ne hδY
  have hmem := hD hraw
  rw [← hPtT1X, ← hPtT2X] at hmem
  rw [hLHS, hRHS] at hmem
  have heq : (single PtRa1 + (2 : ℤ) • single PtRa + single PtιP2 + single PtT1 + single PtT2 -
      (single PtT1 + single PtT2 + single (Point.iota PtT1) + single (Point.iota PtT2) +
        single δ₀ + single (Point.iota δ₀)) : Divisor H) =
      (single PtRa1 + (2 : ℤ) • single PtRa + single PtιP2 -
      single (Point.iota PtT1) - single (Point.iota PtT2) -
      single δ₀ - single (Point.iota δ₀) : Divisor H) := by abel
  rwa [heq] at hmem

/-- **Cross variant 4 (`Ra2 = ι(sa.P2)`), `hD`-pushforward.** Same shape
as variant 3 (doubled node on the second anchor slot), ported onto
`CAWitnessCrossTangentV4.lean`'s objects (ordinary anchor `Ra1`, doubled
node `Ra`, ordinary target `ιP1`). -/
theorem cIotaAmIotaT_mem_of_le_cross4
    [DecidableEq H.Point]
    (hdeg : H.f.natDegree = 5)
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (D : PrincipalDivisorData H) (hD : principalSubgroup H hdeg ≤ D.P)
    (Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2 : k)
    (hdet : (caCross4InterpMatrix Ra1X RaX P1X).det ≠ 0)
    (hlead : caCross4Coeff Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2 3 ≠ 0)
    (h1 : Ra1X ≠ RaX) (h2 : Ra1X ≠ P1X) (h3 : RaX ≠ P1X)
    (hRa1_curve : Ra1Y ^ 2 = H.f.eval Ra1X) (hRa_curve : RaY ^ 2 = H.f.eval RaX)
    (hP1_curve : P1Y ^ 2 = H.f.eval P1X)
    (hP1Deriv : 2 * RaY * (-vDerivAtP2) = (derivative H.f).eval RaX)
    (hRa1Y_ne : Ra1Y ≠ 0) (hRaY_ne : RaY ≠ 0) (hP1Y_ne : P1Y ≠ 0)
    (PtRa1 PtRa PtιP1 : H.Point)
    (hPtRa1X : PtRa1.X = Ra1X) (hPtRa1Y : PtRa1.Y = Ra1Y)
    (hPtRaX : PtRa.X = RaX) (hPtRaY : PtRa.Y = RaY)
    (hPtιP1X : PtιP1.X = P1X) (hPtιP1Y : PtιP1.Y = -P1Y)
    (hne : H.f - (bCACross4 Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2) ^ 2 ≠ 0)
    (hU_evalRa1 : (uCANewCross4 H Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2).eval Ra1X ≠ 0)
    (hU_evalRa : (uCANewCross4 H Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2).eval RaX ≠ 0)
    (hU_evalP1 : (uCANewCross4 H Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2).eval P1X ≠ 0)
    (hU_ne0 : uCANewCross4 H Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2 ≠ 0)
    (T1X T2X : k)
    (hT1 : (uCANewCross4 H Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2).IsRoot T1X)
    (hT2 : (uCANewCross4 H Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2).IsRoot T2X)
    (hTne : T1X ≠ T2X)
    (Q1 Q2 : Polynomial k)
    (hQ1_def : uCANewCross4 H Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2 =
      (X - C T1X) * (X - C T2X) * Q1)
    (hQ1T1 : Q1.eval T1X ≠ 0)
    (hQ2_def : uCANewCross4 H Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2 =
      (X - C T2X) * (X - C T1X) * Q2)
    (hQ2T2 : Q2.eval T2X ≠ 0)
    (PtT1 PtT2 δ₀ : H.Point)
    (hAeval1 : (denomPolyCACross4 Ra1X RaX P1X : k[X]).eval PtT1.X ≠ 0)
    (hAeval2 : (denomPolyCACross4 Ra1X RaX P1X : k[X]).eval PtT2.X ≠ 0)
    (hPtT1X : PtT1.X = T1X)
    (hPtT1Y : PtT1.Y = (bCACross4 Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2).eval PtT1.X)
    (hPtT1Y_ne : PtT1.Y ≠ 0)
    (hPtT2X : PtT2.X = T2X)
    (hPtT2Y : PtT2.Y = (bCACross4 Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2).eval PtT2.X)
    (hPtT2Y_ne : PtT2.Y ≠ 0)
    (hRa1T1 : Ra1X ≠ T1X) (hRa1T2 : Ra1X ≠ T2X)
    (hRaT1 : RaX ≠ T1X) (hRaT2 : RaX ≠ T2X)
    (hP1T1 : P1X ≠ T1X) (hP1T2 : P1X ≠ T2X)
    (h1δ : T1X ≠ δ₀.X) (h2δ : T2X ≠ δ₀.X) (hδY : δ₀.Y ≠ 0)
    (hsupp_f : ∀ P, P ∉ ({PtRa1, PtRa, PtιP1, PtT1, PtT2} : Finset H.Point) →
      ordAt P (-bCACross4 Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2) (1 : k[X]) = 0)
    (hspec_f : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span
        ({toPair H (-bCACross4 Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2) 1} :
          Set (CoordinateRing H)))).factors ≠ 0 → ∃ P, v.asIdeal = pointIdeal P)
    [∀ P : ({PtRa1, PtRa, PtιP1, PtT1, PtT2} : Finset H.Point),
      Module.Finite k (CoordinateRing H ⧸ pointIdeal P.1 ^
        (ordAt P.1 (-bCACross4 Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2) (1 : k[X])).toNat)]
    (hsupp_hT : ∀ P, P ∉ ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀, Point.iota δ₀} :
        Finset H.Point) →
      ordAt P ((linX T1X * linX T2X) * linX δ₀.X) (0 : k[X]) = 0)
    (hspec_hT : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span
        ({toPair H ((linX T1X * linX T2X) * linX δ₀.X) 0} :
          Set (CoordinateRing H)))).factors ≠ 0 → ∃ P, v.asIdeal = pointIdeal P)
    [∀ P : ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀, Point.iota δ₀} : Finset H.Point),
      Module.Finite k (CoordinateRing H ⧸ pointIdeal P.1 ^
        (ordAt P.1 ((linX T1X * linX T2X) * linX δ₀.X) (0 : k[X])).toNat)] :
    (single PtRa1 + (2 : ℤ) • single PtRa + single PtιP1 -
      single (Point.iota PtT1) - single (Point.iota PtT2) -
      single δ₀ - single (Point.iota δ₀) : Divisor H) ∈ D.P := by
  classical
  have hraw := cIotaAmIotaT_mem_principalSubgroup_cross4 (H := H) hdeg hchar hsf
    Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2 hdet hlead h1 h2 h3
    hRa1_curve hRa_curve hP1_curve hP1Deriv hRa1Y_ne hRaY_ne hP1Y_ne
    PtRa1 PtRa PtιP1 hPtRa1X hPtRa1Y hPtRaX hPtRaY hPtιP1X hPtιP1Y hne
    hU_evalRa1 hU_evalRa hU_evalP1 T1X T2X hT1 hT2 hTne hU_ne0
    Q1 Q2 hQ1_def hQ1T1 hQ2_def hQ2T2 PtT1 PtT2 δ₀ hAeval1 hAeval2
    hPtT1X hPtT1Y hPtT1Y_ne hPtT2X hPtT2Y hPtT2Y_ne
    hRa1T1 hRa1T2 hRaT1 hRaT2 hP1T1 hP1T2 h1δ h2δ hδY
    hsupp_f hspec_f hsupp_hT hspec_hT
  have hLHS := divToPair_eq_C_add_iotaA_add_T_of_split_cross4 (H := H) hchar hsf
    Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2 hdet h1 h2 h3
    hRa1_curve hRa_curve hP1_curve hP1Deriv hRa1Y_ne hRaY_ne hP1Y_ne
    PtRa1 PtRa PtιP1 hPtRa1X hPtRa1Y hPtRaX hPtRaY hPtιP1X hPtιP1Y hne
    hU_evalRa1 hU_evalRa hU_evalP1 hU_ne0 T1X T2X hT1 hT2 hTne
    Q1 Q2 hQ1_def hQ1T1 hQ2_def hQ2T2 PtT1 PtT2 hAeval1 hAeval2
    hPtT1X hPtT1Y hPtT1Y_ne hPtT2X hPtT2Y hPtT2Y_ne
    hRa1T1 hRa1T2 hRaT1 hRaT2 hP1T1 hP1T2
  have hPtT12ne : PtT1.X ≠ PtT2.X := by rw [hPtT1X, hPtT2X]; exact hTne
  have hPtT1δ : PtT1.X ≠ δ₀.X := by rw [hPtT1X]; exact h1δ
  have hPtT2δ : PtT2.X ≠ δ₀.X := by rw [hPtT2X]; exact h2δ
  have hRHS := divToPair_hT_eq (H := H) hchar hsf PtT1 PtT2 δ₀
    hPtT12ne hPtT1δ hPtT2δ hPtT1Y_ne hPtT2Y_ne hδY
  have hmem := hD hraw
  rw [← hPtT1X, ← hPtT2X] at hmem
  rw [hLHS, hRHS] at hmem
  have heq : (single PtRa1 + (2 : ℤ) • single PtRa + single PtιP1 + single PtT1 + single PtT2 -
      (single PtT1 + single PtT2 + single (Point.iota PtT1) + single (Point.iota PtT2) +
        single δ₀ + single (Point.iota δ₀)) : Divisor H) =
      (single PtRa1 + (2 : ℤ) • single PtRa + single PtιP1 -
      single (Point.iota PtT1) - single (Point.iota PtT2) -
      single δ₀ - single (Point.iota δ₀) : Divisor H) := by abel
  rwa [heq] at hmem

/-! ## `G₁ - G₂ - G₃` composition: the honest cross-variant (†)

**Divisor arithmetic, worked out and symbolically checked before writing
any of the four theorems below** (not guessed): for each cross variant,
`cIotaAmIotaT_mem_of_le_crossN`'s conclusion (`G₁`) has the doubled node
`PtRa`/`PtRa1`-or-`PtRa` contributing `2•single` where the split case's
`G₁` has two separate `single`s (`single PtιP1 + single PtιP2`), and is
missing the `Point.iota` companion of the doubled node entirely (since
that companion never appears as its own generator on the `f`-divisor's
support — the doubled node's `x`-coordinate has multiplicity 2 there,
not a `Point`/`Point.iota` PAIR the way an ordinary split anchor point
would). Checked directly (free-abelian-group arithmetic, not assumed
from the split case's shape) that subtracting exactly TWO fiber-difference
divisors — one at the doubled node itself (`fiber_diff_mem_of_le _ _ _ _ _
PtRa δ₀`, supplying the missing `Point.iota PtRa` term and cancelling one
copy of the doubled `PtRa`) and one at the surviving ordinary target point
(`fiber_diff_mem_of_le _ _ _ _ _ PtP2-or-PtP1 δ₀`, mirroring the split
case's own `G₂`/`G₃` exactly) — lands exactly on the expected (†) shape
`[Ra1]+[Ra2]-[sa.P1]-[sa.P2]-[T1cur]-[T2cur]+[δ₀]+[ιδ₀]` with the doubled
node standing in for whichever of `Ra1,Ra2` collided with whichever of
`sa.P1,sa.P2`. No new mathematics beyond the split case's own `G₁-G₂-G₃`
pattern — the only difference is which point plays which role, since the
doubled node's own conjugate now has to be supplied by a `fiber_diff`
call rather than already sitting in `G₁` as a distinct named point. -/

/-- **Cross variant 1 (`Ra1 = ι(sa.P1)`), `G₁-G₂-G₃`: the honest (†).**
`PtRa` (`= Ra1 = ι(sa.P1)`) stands in for the top-level theorem's `Ra1`;
`sa.P1 = ι(PtRa)`; `PtRa2` stands in for `Ra2`; the surviving ordinary
target point is named `PtP2` here (unflipped, `hPtP2Y : PtP2.Y = P2Y`)
with `Point.iota PtP2 = PtιP2` proved inside the proof, exactly mirroring
`cAmιTmδmιδ_mem_of_le`'s own `PtP2`/`PtιP2` pair. -/
theorem cAmιTmδmιδ_mem_of_le_cross1
    [DecidableEq H.Point]
    (hdeg : H.f.natDegree = 5)
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (D : PrincipalDivisorData H) (hD : principalSubgroup H hdeg ≤ D.P)
    [∀ (a : k) (S : Finset H.Point),
      ∀ P : S, Module.Finite k (CoordinateRing H ⧸ pointIdeal P.1 ^ (ordAt P.1 (linX a) 0).toNat)]
    (hspec_linX : ∀ (a : k), ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk v.asIdeal).count
        (Associates.mk (Ideal.span ({toPair H (linX a) 0} : Set (CoordinateRing H)))).factors
          ≠ 0 → ∃ P, v.asIdeal = pointIdeal P)
    (RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y : k)
    (hdet : (caCrossInterpMatrix RaX Ra2X P2X).det ≠ 0)
    (hlead : caCrossCoeff RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y 3 ≠ 0)
    (h1 : RaX ≠ Ra2X) (h2 : RaX ≠ P2X) (h3 : Ra2X ≠ P2X)
    (hRa_curve : RaY ^ 2 = H.f.eval RaX) (hRa2_curve : Ra2Y ^ 2 = H.f.eval Ra2X)
    (hP2_curve : P2Y ^ 2 = H.f.eval P2X)
    (hP1Deriv : 2 * RaY * (-vDerivAtP1) = (derivative H.f).eval RaX)
    (hRaY_ne : RaY ≠ 0) (hRa2Y_ne : Ra2Y ≠ 0) (hP2Y_ne : P2Y ≠ 0)
    (PtRa PtRa2 PtP2 PtιP2 : H.Point)
    (hPtRaX : PtRa.X = RaX) (hPtRaY : PtRa.Y = RaY)
    (hPtRa2X : PtRa2.X = Ra2X) (hPtRa2Y : PtRa2.Y = Ra2Y)
    (hPtP2X : PtP2.X = P2X) (hPtP2Y : PtP2.Y = P2Y)
    (hPtιP2X : PtιP2.X = P2X) (hPtιP2Y : PtιP2.Y = -P2Y)
    (hne : H.f - (bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) ^ 2 ≠ 0)
    (hU_evalRa : (uCANewCross H RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y).eval RaX ≠ 0)
    (hU_evalRa2 : (uCANewCross H RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y).eval Ra2X ≠ 0)
    (hU_evalP2 : (uCANewCross H RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y).eval P2X ≠ 0)
    (hU_ne0 : uCANewCross H RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y ≠ 0)
    (T1X T2X : k)
    (hT1 : (uCANewCross H RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y).IsRoot T1X)
    (hT2 : (uCANewCross H RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y).IsRoot T2X)
    (hTne : T1X ≠ T2X)
    (Q1 Q2 : Polynomial k)
    (hQ1_def : uCANewCross H RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y =
      (X - C T1X) * (X - C T2X) * Q1)
    (hQ1T1 : Q1.eval T1X ≠ 0)
    (hQ2_def : uCANewCross H RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y =
      (X - C T2X) * (X - C T1X) * Q2)
    (hQ2T2 : Q2.eval T2X ≠ 0)
    (PtT1 PtT2 δ₀ : H.Point)
    (hAeval1 : (denomPolyCACross RaX Ra2X P2X : k[X]).eval PtT1.X ≠ 0)
    (hAeval2 : (denomPolyCACross RaX Ra2X P2X : k[X]).eval PtT2.X ≠ 0)
    (hPtT1X : PtT1.X = T1X)
    (hPtT1Y : PtT1.Y = (bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y).eval PtT1.X)
    (hPtT1Y_ne : PtT1.Y ≠ 0)
    (hPtT2X : PtT2.X = T2X)
    (hPtT2Y : PtT2.Y = (bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y).eval PtT2.X)
    (hPtT2Y_ne : PtT2.Y ≠ 0)
    (hRaT1 : RaX ≠ T1X) (hRaT2 : RaX ≠ T2X)
    (hRa2T1 : Ra2X ≠ T1X) (hRa2T2 : Ra2X ≠ T2X)
    (hP2T1 : P2X ≠ T1X) (hP2T2 : P2X ≠ T2X)
    (h1δ : T1X ≠ δ₀.X) (h2δ : T2X ≠ δ₀.X) (hδY : δ₀.Y ≠ 0)
    (hsupp_f : ∀ P, P ∉ ({PtRa, PtRa2, PtιP2, PtT1, PtT2} : Finset H.Point) →
      ordAt P (-bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) (1 : k[X]) = 0)
    (hspec_f : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span
        ({toPair H (-bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) 1} :
          Set (CoordinateRing H)))).factors ≠ 0 → ∃ P, v.asIdeal = pointIdeal P)
    [∀ P : ({PtRa, PtRa2, PtιP2, PtT1, PtT2} : Finset H.Point),
      Module.Finite k (CoordinateRing H ⧸ pointIdeal P.1 ^
        (ordAt P.1 (-bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) (1 : k[X])).toNat)]
    (hsupp_hT : ∀ P, P ∉ ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀, Point.iota δ₀} :
        Finset H.Point) →
      ordAt P ((linX T1X * linX T2X) * linX δ₀.X) (0 : k[X]) = 0)
    (hspec_hT : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span
        ({toPair H ((linX T1X * linX T2X) * linX δ₀.X) 0} :
          Set (CoordinateRing H)))).factors ≠ 0 → ∃ P, v.asIdeal = pointIdeal P)
    [∀ P : ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀, Point.iota δ₀} : Finset H.Point),
      Module.Finite k (CoordinateRing H ⧸ pointIdeal P.1 ^
        (ordAt P.1 ((linX T1X * linX T2X) * linX δ₀.X) (0 : k[X])).toNat)]
    (T1cur T2cur : H.Point)
    (hT1eq : T1cur = Point.iota PtT1) (hT2eq : T2cur = Point.iota PtT2) :
    (single PtRa + single PtRa2 - single (Point.iota PtRa) - single PtP2 -
      single T1cur - single T2cur +
      single δ₀ + single (Point.iota δ₀) : Divisor H) ∈ D.P := by
  classical
  subst hT1eq; subst hT2eq
  have hG1 := cIotaAmIotaT_mem_of_le_cross1 (H := H) hdeg hchar hsf D hD
    RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y hdet hlead h1 h2 h3
    hRa_curve hRa2_curve hP2_curve hP1Deriv hRaY_ne hRa2Y_ne hP2Y_ne
    PtRa PtRa2 PtιP2 hPtRaX hPtRaY hPtRa2X hPtRa2Y hPtιP2X hPtιP2Y hne
    hU_evalRa hU_evalRa2 hU_evalP2 hU_ne0 T1X T2X hT1 hT2 hTne
    Q1 Q2 hQ1_def hQ1T1 hQ2_def hQ2T2 PtT1 PtT2 δ₀ hAeval1 hAeval2
    hPtT1X hPtT1Y hPtT1Y_ne hPtT2X hPtT2Y hPtT2Y_ne
    hRaT1 hRaT2 hRa2T1 hRa2T2 hP2T1 hP2T2 h1δ h2δ hδY
    hsupp_f hspec_f hsupp_hT hspec_hT
  have hG2 := fiber_diff_mem_of_le (H := H) hdeg hchar hsf D hD hspec_linX PtRa δ₀
  have hG3 := fiber_diff_mem_of_le (H := H) hdeg hchar hsf D hD hspec_linX PtP2 δ₀
  have hcombine := D.P.sub_mem (D.P.sub_mem hG1 hG2) hG3
  have hιPtP2X : (Point.iota PtP2).X = PtιP2.X := by rw [Point.iota_X, hPtP2X, hPtιP2X]
  have hιPtP2Y : (Point.iota PtP2).Y = PtιP2.Y := by rw [Point.iota_Y, hPtP2Y, hPtιP2Y]
  have hιPtP2 : Point.iota PtP2 = PtιP2 := Subtype.ext (Prod.ext hιPtP2X hιPtP2Y)
  have heq :
      (((2 : ℤ) • single PtRa + single PtRa2 + single PtιP2 -
          single (Point.iota PtT1) - single (Point.iota PtT2) -
          single δ₀ - single (Point.iota δ₀)) -
        (single PtRa + single (Point.iota PtRa) - single δ₀ - single (Point.iota δ₀)) -
        (single PtP2 + single (Point.iota PtP2) - single δ₀ - single (Point.iota δ₀))
        : Divisor H) =
      (single PtRa + single PtRa2 - single (Point.iota PtRa) - single PtP2 -
        single (Point.iota PtT1) - single (Point.iota PtT2) +
        single δ₀ + single (Point.iota δ₀) : Divisor H) := by
    rw [hιPtP2]; abel
  rwa [heq] at hcombine

/-- **Cross variant 2 (`Ra1 = ι(sa.P2)`), `G₁-G₂-G₃`: the honest (†).**
Same shape as variant 1, with the surviving ordinary target point being
`sa.P1`, named `PtP1` here (`Point.iota PtP1 = PtιP1` proved inside). -/
theorem cAmιTmδmιδ_mem_of_le_cross2
    [DecidableEq H.Point]
    (hdeg : H.f.natDegree = 5)
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (D : PrincipalDivisorData H) (hD : principalSubgroup H hdeg ≤ D.P)
    [∀ (a : k) (S : Finset H.Point),
      ∀ P : S, Module.Finite k (CoordinateRing H ⧸ pointIdeal P.1 ^ (ordAt P.1 (linX a) 0).toNat)]
    (hspec_linX : ∀ (a : k), ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk v.asIdeal).count
        (Associates.mk (Ideal.span ({toPair H (linX a) 0} : Set (CoordinateRing H)))).factors
          ≠ 0 → ∃ P, v.asIdeal = pointIdeal P)
    (RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 : k)
    (hdet : (caCross2InterpMatrix RaX Ra2X P1X).det ≠ 0)
    (hlead : caCross2Coeff RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 3 ≠ 0)
    (h1 : RaX ≠ Ra2X) (h2 : RaX ≠ P1X) (h3 : Ra2X ≠ P1X)
    (hRa_curve : RaY ^ 2 = H.f.eval RaX) (hRa2_curve : Ra2Y ^ 2 = H.f.eval Ra2X)
    (hP1_curve : P1Y ^ 2 = H.f.eval P1X)
    (hP2Deriv : 2 * RaY * (-vDerivAtP2) = (derivative H.f).eval RaX)
    (hRaY_ne : RaY ≠ 0) (hRa2Y_ne : Ra2Y ≠ 0) (hP1Y_ne : P1Y ≠ 0)
    (PtRa PtRa2 PtP1 PtιP1 : H.Point)
    (hPtRaX : PtRa.X = RaX) (hPtRaY : PtRa.Y = RaY)
    (hPtRa2X : PtRa2.X = Ra2X) (hPtRa2Y : PtRa2.Y = Ra2Y)
    (hPtP1X : PtP1.X = P1X) (hPtP1Y : PtP1.Y = P1Y)
    (hPtιP1X : PtιP1.X = P1X) (hPtιP1Y : PtιP1.Y = -P1Y)
    (hne : H.f - (bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) ^ 2 ≠ 0)
    (hU_evalRa : (uCANewCross2 H RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2).eval RaX ≠ 0)
    (hU_evalRa2 : (uCANewCross2 H RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2).eval Ra2X ≠ 0)
    (hU_evalP1 : (uCANewCross2 H RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2).eval P1X ≠ 0)
    (hU_ne0 : uCANewCross2 H RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 ≠ 0)
    (T1X T2X : k)
    (hT1 : (uCANewCross2 H RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2).IsRoot T1X)
    (hT2 : (uCANewCross2 H RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2).IsRoot T2X)
    (hTne : T1X ≠ T2X)
    (Q1 Q2 : Polynomial k)
    (hQ1_def : uCANewCross2 H RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 =
      (X - C T1X) * (X - C T2X) * Q1)
    (hQ1T1 : Q1.eval T1X ≠ 0)
    (hQ2_def : uCANewCross2 H RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 =
      (X - C T2X) * (X - C T1X) * Q2)
    (hQ2T2 : Q2.eval T2X ≠ 0)
    (PtT1 PtT2 δ₀ : H.Point)
    (hAeval1 : (denomPolyCACross2 RaX Ra2X P1X : k[X]).eval PtT1.X ≠ 0)
    (hAeval2 : (denomPolyCACross2 RaX Ra2X P1X : k[X]).eval PtT2.X ≠ 0)
    (hPtT1X : PtT1.X = T1X)
    (hPtT1Y : PtT1.Y = (bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2).eval PtT1.X)
    (hPtT1Y_ne : PtT1.Y ≠ 0)
    (hPtT2X : PtT2.X = T2X)
    (hPtT2Y : PtT2.Y = (bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2).eval PtT2.X)
    (hPtT2Y_ne : PtT2.Y ≠ 0)
    (hRaT1 : RaX ≠ T1X) (hRaT2 : RaX ≠ T2X)
    (hRa2T1 : Ra2X ≠ T1X) (hRa2T2 : Ra2X ≠ T2X)
    (hP1T1 : P1X ≠ T1X) (hP1T2 : P1X ≠ T2X)
    (h1δ : T1X ≠ δ₀.X) (h2δ : T2X ≠ δ₀.X) (hδY : δ₀.Y ≠ 0)
    (hsupp_f : ∀ P, P ∉ ({PtRa, PtRa2, PtιP1, PtT1, PtT2} : Finset H.Point) →
      ordAt P (-bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) (1 : k[X]) = 0)
    (hspec_f : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span
        ({toPair H (-bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) 1} :
          Set (CoordinateRing H)))).factors ≠ 0 → ∃ P, v.asIdeal = pointIdeal P)
    [∀ P : ({PtRa, PtRa2, PtιP1, PtT1, PtT2} : Finset H.Point),
      Module.Finite k (CoordinateRing H ⧸ pointIdeal P.1 ^
        (ordAt P.1 (-bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) (1 : k[X])).toNat)]
    (hsupp_hT : ∀ P, P ∉ ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀, Point.iota δ₀} :
        Finset H.Point) →
      ordAt P ((linX T1X * linX T2X) * linX δ₀.X) (0 : k[X]) = 0)
    (hspec_hT : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span
        ({toPair H ((linX T1X * linX T2X) * linX δ₀.X) 0} :
          Set (CoordinateRing H)))).factors ≠ 0 → ∃ P, v.asIdeal = pointIdeal P)
    [∀ P : ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀, Point.iota δ₀} : Finset H.Point),
      Module.Finite k (CoordinateRing H ⧸ pointIdeal P.1 ^
        (ordAt P.1 ((linX T1X * linX T2X) * linX δ₀.X) (0 : k[X])).toNat)]
    (T1cur T2cur : H.Point)
    (hT1eq : T1cur = Point.iota PtT1) (hT2eq : T2cur = Point.iota PtT2) :
    (single PtRa + single PtRa2 - single (Point.iota PtRa) - single PtP1 -
      single T1cur - single T2cur +
      single δ₀ + single (Point.iota δ₀) : Divisor H) ∈ D.P := by
  classical
  subst hT1eq; subst hT2eq
  have hG1 := cIotaAmIotaT_mem_of_le_cross2 (H := H) hdeg hchar hsf D hD
    RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 hdet hlead h1 h2 h3
    hRa_curve hRa2_curve hP1_curve hP2Deriv hRaY_ne hRa2Y_ne hP1Y_ne
    PtRa PtRa2 PtιP1 hPtRaX hPtRaY hPtRa2X hPtRa2Y hPtιP1X hPtιP1Y hne
    hU_evalRa hU_evalRa2 hU_evalP1 hU_ne0 T1X T2X hT1 hT2 hTne
    Q1 Q2 hQ1_def hQ1T1 hQ2_def hQ2T2 PtT1 PtT2 δ₀ hAeval1 hAeval2
    hPtT1X hPtT1Y hPtT1Y_ne hPtT2X hPtT2Y hPtT2Y_ne
    hRaT1 hRaT2 hRa2T1 hRa2T2 hP1T1 hP1T2 h1δ h2δ hδY
    hsupp_f hspec_f hsupp_hT hspec_hT
  have hG2 := fiber_diff_mem_of_le (H := H) hdeg hchar hsf D hD hspec_linX PtRa δ₀
  have hG3 := fiber_diff_mem_of_le (H := H) hdeg hchar hsf D hD hspec_linX PtP1 δ₀
  have hcombine := D.P.sub_mem (D.P.sub_mem hG1 hG2) hG3
  have hιPtP1X : (Point.iota PtP1).X = PtιP1.X := by rw [Point.iota_X, hPtP1X, hPtιP1X]
  have hιPtP1Y : (Point.iota PtP1).Y = PtιP1.Y := by rw [Point.iota_Y, hPtP1Y, hPtιP1Y]
  have hιPtP1 : Point.iota PtP1 = PtιP1 := Subtype.ext (Prod.ext hιPtP1X hιPtP1Y)
  have heq :
      (((2 : ℤ) • single PtRa + single PtRa2 + single PtιP1 -
          single (Point.iota PtT1) - single (Point.iota PtT2) -
          single δ₀ - single (Point.iota δ₀)) -
        (single PtRa + single (Point.iota PtRa) - single δ₀ - single (Point.iota δ₀)) -
        (single PtP1 + single (Point.iota PtP1) - single δ₀ - single (Point.iota δ₀))
        : Divisor H) =
      (single PtRa + single PtRa2 - single (Point.iota PtRa) - single PtP1 -
        single (Point.iota PtT1) - single (Point.iota PtT2) +
        single δ₀ + single (Point.iota δ₀) : Divisor H) := by
    rw [hιPtP1]; abel
  rwa [heq] at hcombine

/-- **Cross variant 3 (`Ra2 = ι(sa.P1)`), `G₁-G₂-G₃`: the honest (†).**
Doubled node sits on the SECOND anchor slot here (`PtRa`, `= Ra2`);
`PtRa1` survives as an ordinary anchor point; surviving ordinary target
point is `sa.P2`, named `PtP2` here. -/
theorem cAmιTmδmιδ_mem_of_le_cross3
    [DecidableEq H.Point]
    (hdeg : H.f.natDegree = 5)
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (D : PrincipalDivisorData H) (hD : principalSubgroup H hdeg ≤ D.P)
    [∀ (a : k) (S : Finset H.Point),
      ∀ P : S, Module.Finite k (CoordinateRing H ⧸ pointIdeal P.1 ^ (ordAt P.1 (linX a) 0).toNat)]
    (hspec_linX : ∀ (a : k), ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk v.asIdeal).count
        (Associates.mk (Ideal.span ({toPair H (linX a) 0} : Set (CoordinateRing H)))).factors
          ≠ 0 → ∃ P, v.asIdeal = pointIdeal P)
    (Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y : k)
    (hdet : (caCross3InterpMatrix Ra1X RaX P2X).det ≠ 0)
    (hlead : caCross3Coeff Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y 3 ≠ 0)
    (h1 : Ra1X ≠ RaX) (h2 : Ra1X ≠ P2X) (h3 : RaX ≠ P2X)
    (hRa1_curve : Ra1Y ^ 2 = H.f.eval Ra1X) (hRa_curve : RaY ^ 2 = H.f.eval RaX)
    (hP2_curve : P2Y ^ 2 = H.f.eval P2X)
    (hP1Deriv : 2 * RaY * (-vDerivAtP1) = (derivative H.f).eval RaX)
    (hRa1Y_ne : Ra1Y ≠ 0) (hRaY_ne : RaY ≠ 0) (hP2Y_ne : P2Y ≠ 0)
    (PtRa1 PtRa PtP2 PtιP2 : H.Point)
    (hPtRa1X : PtRa1.X = Ra1X) (hPtRa1Y : PtRa1.Y = Ra1Y)
    (hPtRaX : PtRa.X = RaX) (hPtRaY : PtRa.Y = RaY)
    (hPtP2X : PtP2.X = P2X) (hPtP2Y : PtP2.Y = P2Y)
    (hPtιP2X : PtιP2.X = P2X) (hPtιP2Y : PtιP2.Y = -P2Y)
    (hne : H.f - (bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) ^ 2 ≠ 0)
    (hU_evalRa1 : (uCANewCross3 H Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y).eval Ra1X ≠ 0)
    (hU_evalRa : (uCANewCross3 H Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y).eval RaX ≠ 0)
    (hU_evalP2 : (uCANewCross3 H Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y).eval P2X ≠ 0)
    (hU_ne0 : uCANewCross3 H Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y ≠ 0)
    (T1X T2X : k)
    (hT1 : (uCANewCross3 H Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y).IsRoot T1X)
    (hT2 : (uCANewCross3 H Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y).IsRoot T2X)
    (hTne : T1X ≠ T2X)
    (Q1 Q2 : Polynomial k)
    (hQ1_def : uCANewCross3 H Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y =
      (X - C T1X) * (X - C T2X) * Q1)
    (hQ1T1 : Q1.eval T1X ≠ 0)
    (hQ2_def : uCANewCross3 H Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y =
      (X - C T2X) * (X - C T1X) * Q2)
    (hQ2T2 : Q2.eval T2X ≠ 0)
    (PtT1 PtT2 δ₀ : H.Point)
    (hAeval1 : (denomPolyCACross3 Ra1X RaX P2X : k[X]).eval PtT1.X ≠ 0)
    (hAeval2 : (denomPolyCACross3 Ra1X RaX P2X : k[X]).eval PtT2.X ≠ 0)
    (hPtT1X : PtT1.X = T1X)
    (hPtT1Y : PtT1.Y = (bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y).eval PtT1.X)
    (hPtT1Y_ne : PtT1.Y ≠ 0)
    (hPtT2X : PtT2.X = T2X)
    (hPtT2Y : PtT2.Y = (bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y).eval PtT2.X)
    (hPtT2Y_ne : PtT2.Y ≠ 0)
    (hRa1T1 : Ra1X ≠ T1X) (hRa1T2 : Ra1X ≠ T2X)
    (hRaT1 : RaX ≠ T1X) (hRaT2 : RaX ≠ T2X)
    (hP2T1 : P2X ≠ T1X) (hP2T2 : P2X ≠ T2X)
    (h1δ : T1X ≠ δ₀.X) (h2δ : T2X ≠ δ₀.X) (hδY : δ₀.Y ≠ 0)
    (hsupp_f : ∀ P, P ∉ ({PtRa1, PtRa, PtιP2, PtT1, PtT2} : Finset H.Point) →
      ordAt P (-bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) (1 : k[X]) = 0)
    (hspec_f : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span
        ({toPair H (-bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) 1} :
          Set (CoordinateRing H)))).factors ≠ 0 → ∃ P, v.asIdeal = pointIdeal P)
    [∀ P : ({PtRa1, PtRa, PtιP2, PtT1, PtT2} : Finset H.Point),
      Module.Finite k (CoordinateRing H ⧸ pointIdeal P.1 ^
        (ordAt P.1 (-bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) (1 : k[X])).toNat)]
    (hsupp_hT : ∀ P, P ∉ ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀, Point.iota δ₀} :
        Finset H.Point) →
      ordAt P ((linX T1X * linX T2X) * linX δ₀.X) (0 : k[X]) = 0)
    (hspec_hT : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span
        ({toPair H ((linX T1X * linX T2X) * linX δ₀.X) 0} :
          Set (CoordinateRing H)))).factors ≠ 0 → ∃ P, v.asIdeal = pointIdeal P)
    [∀ P : ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀, Point.iota δ₀} : Finset H.Point),
      Module.Finite k (CoordinateRing H ⧸ pointIdeal P.1 ^
        (ordAt P.1 ((linX T1X * linX T2X) * linX δ₀.X) (0 : k[X])).toNat)]
    (T1cur T2cur : H.Point)
    (hT1eq : T1cur = Point.iota PtT1) (hT2eq : T2cur = Point.iota PtT2) :
    (single PtRa1 + single PtRa - single (Point.iota PtRa) - single PtP2 -
      single T1cur - single T2cur +
      single δ₀ + single (Point.iota δ₀) : Divisor H) ∈ D.P := by
  classical
  subst hT1eq; subst hT2eq
  have hG1 := cIotaAmIotaT_mem_of_le_cross3 (H := H) hdeg hchar hsf D hD
    Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y hdet hlead h1 h2 h3
    hRa1_curve hRa_curve hP2_curve hP1Deriv hRa1Y_ne hRaY_ne hP2Y_ne
    PtRa1 PtRa PtιP2 hPtRa1X hPtRa1Y hPtRaX hPtRaY hPtιP2X hPtιP2Y hne
    hU_evalRa1 hU_evalRa hU_evalP2 hU_ne0 T1X T2X hT1 hT2 hTne
    Q1 Q2 hQ1_def hQ1T1 hQ2_def hQ2T2 PtT1 PtT2 δ₀ hAeval1 hAeval2
    hPtT1X hPtT1Y hPtT1Y_ne hPtT2X hPtT2Y hPtT2Y_ne
    hRa1T1 hRa1T2 hRaT1 hRaT2 hP2T1 hP2T2 h1δ h2δ hδY
    hsupp_f hspec_f hsupp_hT hspec_hT
  have hG2 := fiber_diff_mem_of_le (H := H) hdeg hchar hsf D hD hspec_linX PtRa δ₀
  have hG3 := fiber_diff_mem_of_le (H := H) hdeg hchar hsf D hD hspec_linX PtP2 δ₀
  have hcombine := D.P.sub_mem (D.P.sub_mem hG1 hG2) hG3
  have hιPtP2X : (Point.iota PtP2).X = PtιP2.X := by rw [Point.iota_X, hPtP2X, hPtιP2X]
  have hιPtP2Y : (Point.iota PtP2).Y = PtιP2.Y := by rw [Point.iota_Y, hPtP2Y, hPtιP2Y]
  have hιPtP2 : Point.iota PtP2 = PtιP2 := Subtype.ext (Prod.ext hιPtP2X hιPtP2Y)
  have heq :
      ((single PtRa1 + (2 : ℤ) • single PtRa + single PtιP2 -
          single (Point.iota PtT1) - single (Point.iota PtT2) -
          single δ₀ - single (Point.iota δ₀)) -
        (single PtRa + single (Point.iota PtRa) - single δ₀ - single (Point.iota δ₀)) -
        (single PtP2 + single (Point.iota PtP2) - single δ₀ - single (Point.iota δ₀))
        : Divisor H) =
      (single PtRa1 + single PtRa - single (Point.iota PtRa) - single PtP2 -
        single (Point.iota PtT1) - single (Point.iota PtT2) +
        single δ₀ + single (Point.iota δ₀) : Divisor H) := by
    rw [hιPtP2]; abel
  rwa [heq] at hcombine

/-- **Cross variant 4 (`Ra2 = ι(sa.P2)`), `G₁-G₂-G₃`: the honest (†).**
Doubled node sits on the SECOND anchor slot (`PtRa`, `= Ra2`); `PtRa1`
survives as an ordinary anchor point; surviving ordinary target point is
`sa.P1`, named `PtP1` here. -/
theorem cAmιTmδmιδ_mem_of_le_cross4
    [DecidableEq H.Point]
    (hdeg : H.f.natDegree = 5)
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (D : PrincipalDivisorData H) (hD : principalSubgroup H hdeg ≤ D.P)
    [∀ (a : k) (S : Finset H.Point),
      ∀ P : S, Module.Finite k (CoordinateRing H ⧸ pointIdeal P.1 ^ (ordAt P.1 (linX a) 0).toNat)]
    (hspec_linX : ∀ (a : k), ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk v.asIdeal).count
        (Associates.mk (Ideal.span ({toPair H (linX a) 0} : Set (CoordinateRing H)))).factors
          ≠ 0 → ∃ P, v.asIdeal = pointIdeal P)
    (Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2 : k)
    (hdet : (caCross4InterpMatrix Ra1X RaX P1X).det ≠ 0)
    (hlead : caCross4Coeff Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2 3 ≠ 0)
    (h1 : Ra1X ≠ RaX) (h2 : Ra1X ≠ P1X) (h3 : RaX ≠ P1X)
    (hRa1_curve : Ra1Y ^ 2 = H.f.eval Ra1X) (hRa_curve : RaY ^ 2 = H.f.eval RaX)
    (hP1_curve : P1Y ^ 2 = H.f.eval P1X)
    (hP1Deriv : 2 * RaY * (-vDerivAtP2) = (derivative H.f).eval RaX)
    (hRa1Y_ne : Ra1Y ≠ 0) (hRaY_ne : RaY ≠ 0) (hP1Y_ne : P1Y ≠ 0)
    (PtRa1 PtRa PtP1 PtιP1 : H.Point)
    (hPtRa1X : PtRa1.X = Ra1X) (hPtRa1Y : PtRa1.Y = Ra1Y)
    (hPtRaX : PtRa.X = RaX) (hPtRaY : PtRa.Y = RaY)
    (hPtP1X : PtP1.X = P1X) (hPtP1Y : PtP1.Y = P1Y)
    (hPtιP1X : PtιP1.X = P1X) (hPtιP1Y : PtιP1.Y = -P1Y)
    (hne : H.f - (bCACross4 Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2) ^ 2 ≠ 0)
    (hU_evalRa1 : (uCANewCross4 H Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2).eval Ra1X ≠ 0)
    (hU_evalRa : (uCANewCross4 H Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2).eval RaX ≠ 0)
    (hU_evalP1 : (uCANewCross4 H Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2).eval P1X ≠ 0)
    (hU_ne0 : uCANewCross4 H Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2 ≠ 0)
    (T1X T2X : k)
    (hT1 : (uCANewCross4 H Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2).IsRoot T1X)
    (hT2 : (uCANewCross4 H Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2).IsRoot T2X)
    (hTne : T1X ≠ T2X)
    (Q1 Q2 : Polynomial k)
    (hQ1_def : uCANewCross4 H Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2 =
      (X - C T1X) * (X - C T2X) * Q1)
    (hQ1T1 : Q1.eval T1X ≠ 0)
    (hQ2_def : uCANewCross4 H Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2 =
      (X - C T2X) * (X - C T1X) * Q2)
    (hQ2T2 : Q2.eval T2X ≠ 0)
    (PtT1 PtT2 δ₀ : H.Point)
    (hAeval1 : (denomPolyCACross4 Ra1X RaX P1X : k[X]).eval PtT1.X ≠ 0)
    (hAeval2 : (denomPolyCACross4 Ra1X RaX P1X : k[X]).eval PtT2.X ≠ 0)
    (hPtT1X : PtT1.X = T1X)
    (hPtT1Y : PtT1.Y = (bCACross4 Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2).eval PtT1.X)
    (hPtT1Y_ne : PtT1.Y ≠ 0)
    (hPtT2X : PtT2.X = T2X)
    (hPtT2Y : PtT2.Y = (bCACross4 Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2).eval PtT2.X)
    (hPtT2Y_ne : PtT2.Y ≠ 0)
    (hRa1T1 : Ra1X ≠ T1X) (hRa1T2 : Ra1X ≠ T2X)
    (hRaT1 : RaX ≠ T1X) (hRaT2 : RaX ≠ T2X)
    (hP1T1 : P1X ≠ T1X) (hP1T2 : P1X ≠ T2X)
    (h1δ : T1X ≠ δ₀.X) (h2δ : T2X ≠ δ₀.X) (hδY : δ₀.Y ≠ 0)
    (hsupp_f : ∀ P, P ∉ ({PtRa1, PtRa, PtιP1, PtT1, PtT2} : Finset H.Point) →
      ordAt P (-bCACross4 Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2) (1 : k[X]) = 0)
    (hspec_f : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span
        ({toPair H (-bCACross4 Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2) 1} :
          Set (CoordinateRing H)))).factors ≠ 0 → ∃ P, v.asIdeal = pointIdeal P)
    [∀ P : ({PtRa1, PtRa, PtιP1, PtT1, PtT2} : Finset H.Point),
      Module.Finite k (CoordinateRing H ⧸ pointIdeal P.1 ^
        (ordAt P.1 (-bCACross4 Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2) (1 : k[X])).toNat)]
    (hsupp_hT : ∀ P, P ∉ ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀, Point.iota δ₀} :
        Finset H.Point) →
      ordAt P ((linX T1X * linX T2X) * linX δ₀.X) (0 : k[X]) = 0)
    (hspec_hT : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span
        ({toPair H ((linX T1X * linX T2X) * linX δ₀.X) 0} :
          Set (CoordinateRing H)))).factors ≠ 0 → ∃ P, v.asIdeal = pointIdeal P)
    [∀ P : ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀, Point.iota δ₀} : Finset H.Point),
      Module.Finite k (CoordinateRing H ⧸ pointIdeal P.1 ^
        (ordAt P.1 ((linX T1X * linX T2X) * linX δ₀.X) (0 : k[X])).toNat)]
    (T1cur T2cur : H.Point)
    (hT1eq : T1cur = Point.iota PtT1) (hT2eq : T2cur = Point.iota PtT2) :
    (single PtRa1 + single PtRa - single (Point.iota PtRa) - single PtP1 -
      single T1cur - single T2cur +
      single δ₀ + single (Point.iota δ₀) : Divisor H) ∈ D.P := by
  classical
  subst hT1eq; subst hT2eq
  have hG1 := cIotaAmIotaT_mem_of_le_cross4 (H := H) hdeg hchar hsf D hD
    Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2 hdet hlead h1 h2 h3
    hRa1_curve hRa_curve hP1_curve hP1Deriv hRa1Y_ne hRaY_ne hP1Y_ne
    PtRa1 PtRa PtιP1 hPtRa1X hPtRa1Y hPtRaX hPtRaY hPtιP1X hPtιP1Y hne
    hU_evalRa1 hU_evalRa hU_evalP1 hU_ne0 T1X T2X hT1 hT2 hTne
    Q1 Q2 hQ1_def hQ1T1 hQ2_def hQ2T2 PtT1 PtT2 δ₀ hAeval1 hAeval2
    hPtT1X hPtT1Y hPtT1Y_ne hPtT2X hPtT2Y hPtT2Y_ne
    hRa1T1 hRa1T2 hRaT1 hRaT2 hP1T1 hP1T2 h1δ h2δ hδY
    hsupp_f hspec_f hsupp_hT hspec_hT
  have hG2 := fiber_diff_mem_of_le (H := H) hdeg hchar hsf D hD hspec_linX PtRa δ₀
  have hG3 := fiber_diff_mem_of_le (H := H) hdeg hchar hsf D hD hspec_linX PtP1 δ₀
  have hcombine := D.P.sub_mem (D.P.sub_mem hG1 hG2) hG3
  have hιPtP1X : (Point.iota PtP1).X = PtιP1.X := by rw [Point.iota_X, hPtP1X, hPtιP1X]
  have hιPtP1Y : (Point.iota PtP1).Y = PtιP1.Y := by rw [Point.iota_Y, hPtP1Y, hPtιP1Y]
  have hιPtP1 : Point.iota PtP1 = PtιP1 := Subtype.ext (Prod.ext hιPtP1X hιPtP1Y)
  have heq :
      ((single PtRa1 + (2 : ℤ) • single PtRa + single PtιP1 -
          single (Point.iota PtT1) - single (Point.iota PtT2) -
          single δ₀ - single (Point.iota δ₀)) -
        (single PtRa + single (Point.iota PtRa) - single δ₀ - single (Point.iota δ₀)) -
        (single PtP1 + single (Point.iota PtP1) - single δ₀ - single (Point.iota δ₀))
        : Divisor H) =
      (single PtRa1 + single PtRa - single (Point.iota PtRa) - single PtP1 -
        single (Point.iota PtT1) - single (Point.iota PtT2) +
        single δ₀ + single (Point.iota δ₀) : Divisor H) := by
    rw [hιPtP1]; abel
  rwa [heq] at hcombine

end DecoupledSystem
end Genus2Lean
