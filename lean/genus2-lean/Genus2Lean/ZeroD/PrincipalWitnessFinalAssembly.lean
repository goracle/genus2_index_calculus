import Mathlib
import Genus2Lean.ZeroD.PrincipalWitnessStep3
import Genus2Lean.ZeroD.PrincipalWitnessStep4

/-! # `ROADMAP-principal-witness-assembly.md`, closing step 0 (part c):
# the full `principalSubgroup` assembly, generic in `D : PrincipalDivisorData H`

`PrincipalWitnessStep4.lean` Part 3 proves `G₁` alone
(`cIotaAmIotaT_mem_principalSubgroup : div(f) - div(h_T) ∈ principalSubgroup`)
and states, in prose only, that composing it with two more generators `G₂,
G₃` (fiber-difference divisors at `sa.P1`/`δ₀` and `sa.P2`/`δ₀`) gives the
honest fact

    C - A - ι(T) + [δ₀] + [ιδ₀] ∈ principalSubgroup     (†)

**This file builds `G₂`/`G₃` and the composition, closing that gap.** Two
new pieces, both generic over `D : PrincipalDivisorData H` (rather than the
concrete `principalDivisorData H hdeg` `HyperellipticClassProof.lean` uses)
so this can feed `reducedClass_eq_of_isReduction'` directly via that
theorem's own `hD : principalSubgroup H hdeg ≤ D.P`:

1. `fiber_diff_mem_of_le` — the generic-`D` version of
   `HyperellipticClassProof.lean`'s `hyperellipticClass_principalDivisorData`
   (same proof, `principalDivisorData H hdeg` replaced by an abstract `D`
   with `hD : principalSubgroup H hdeg ≤ D.P`). Gives `G₂`, `G₃` directly.
2. `cIotaAmIotaT_mem_of_le` — `cIotaAmIotaT_mem_principalSubgroup`'s
   conclusion, pushed forward along `hD` and rewritten via
   `divToPair_eq_C_add_iotaA_add_T_of_split` (`PrincipalWitnessStep3.lean`,
   the explicit `C+ιA+T` value of `f`'s divisor) and `divToPair_hT_eq`
   (`PrincipalWitnessStep4.lean`, the explicit six-point value of `h_T`'s
   divisor) into an explicit `single`-sum statement — `G₁`, spelled out.
3. `cAmιTmδmιδ_mem_of_le` — `G₁ - G₂ - G₃`, composed by hand (`abel` after
   unfolding all three to explicit `single` sums), giving exactly (†) as a
   membership in `D.P`, generic `D`.

**Not done here**: wiring this into `reducedClass_eq_of_isReduction'`'s own
`sorry` (roadmap steps 3-4) — that needs `sa.reducedClass`'s own `N₂`
normalization bridged to (†)'s `Nι` one via `q`, which is a separate,
theorem-specific computation left to that file's own proof body. -/

noncomputable section

open Polynomial
open HyperellipticPolynomial
open HyperellipticPolynomial.Divisor

namespace Genus2Lean
namespace DecoupledSystem

variable {k : Type*} [Field k] [DecidableEq k]
variable {H : HyperellipticPolynomial k} [IsDedekindDomain (CoordinateRing H)]

/-- **`G₂`/`G₃`'s shared shape: a fiber-difference divisor is in `D.P` for
ANY `D` with `principalSubgroup H hdeg ≤ D.P`**, not just the concrete
`principalDivisorData H hdeg`. Identical proof to
`HyperellipticClassProof.lean`'s `hyperellipticClass_principalDivisorData`
— `divToPairRatio (linX x₁.X) 0 (fiberSupport x₁) (linX x₃.X) 0
(fiberSupport x₃)` is `[x₁]+[ιx₁]-[x₃]-[ιx₃]` (`divToPair_linX_eq` twice)
and a `principalSubgroup`-generator by construction (`ordInfOfPair_linX`
matches automatically at `-2` both sides) — only the last step (`∈ D.P`
vs `∈ principalDivisorData H hdeg |>.P`) differs, via `hD` instead of
unfolding `principalDivisorData`. -/
theorem fiber_diff_mem_of_le (hdeg : H.f.natDegree = 5)
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (D : PrincipalDivisorData H) (hD : principalSubgroup H hdeg ≤ D.P)
    [∀ (a : k) (S : Finset H.Point),
      ∀ P : S, Module.Finite k (CoordinateRing H ⧸ pointIdeal P.1 ^ (ordAt P.1 (linX a) 0).toNat)]
    (hspec : ∀ (a : k), ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk v.asIdeal).count
        (Associates.mk (Ideal.span ({toPair H (linX a) 0} : Set (CoordinateRing H)))).factors
          ≠ 0 → ∃ P, v.asIdeal = pointIdeal P)
    (x₁ x₃ : H.Point) :
    (single x₁ + single (Point.iota x₁) - single x₃ - single (Point.iota x₃) : Divisor H) ∈
      D.P := by
  classical
  apply hD
  have hgoal_eq : (single x₁ + single (Point.iota x₁) - single x₃ - single (Point.iota x₃)
        : Divisor H) =
      divToPairRatio (linX x₁.X) 0 (fiberSupport x₁) (linX x₃.X) 0 (fiberSupport x₃) := by
    unfold divToPairRatio
    rw [divToPair_linX_eq hchar hsf x₁, divToPair_linX_eq hchar hsf x₃]
    abel
  rw [hgoal_eq]
  show _ ∈ principalSubgroup H hdeg
  apply AddSubgroup.subset_closure
  refine ⟨linX x₁.X, 0, fiberSupport x₁, ?_, hsupp_linX hchar hsf x₁, hspec x₁.X,
    fun P => ‹∀ (a : k) (S : Finset H.Point), ∀ P : S, Module.Finite k
      (CoordinateRing H ⧸ pointIdeal P.1 ^ (ordAt P.1 (linX a) 0).toNat)› x₁.X (fiberSupport x₁) P,
    linX x₃.X, 0, fiberSupport x₃, ?_, hsupp_linX hchar hsf x₃, hspec x₃.X,
    fun P => ‹∀ (a : k) (S : Finset H.Point), ∀ P : S, Module.Finite k
      (CoordinateRing H ⧸ pointIdeal P.1 ^ (ordAt P.1 (linX a) 0).toNat)› x₃.X (fiberSupport x₃) P,
    ?_, rfl⟩
  · exact fun ⟨hA, _⟩ => linX_ne_zero x₁.X hA
  · exact fun ⟨hA, _⟩ => linX_ne_zero x₃.X hA
  · rw [ordInfOfPair_linX, ordInfOfPair_linX]

/-- **`G₁`, spelled out: `[Ra1]+[Ra2]+[ιP1]+[ιP2] - [T1]-[T2]-[ιT1]-[ιT2]-[δ₀]-[ιδ₀]
∈ D.P`**, for any `D` with `hD : principalSubgroup H hdeg ≤ D.P`.
`cIotaAmIotaT_mem_principalSubgroup`'s conclusion (`div(f) - div(h_T) ∈
principalSubgroup`), pushed forward along `hD`, then rewritten via
`divToPair_eq_C_add_iotaA_add_T_of_split` (`f`'s divisor `= C+ιA+T`
explicitly) and `divToPair_hT_eq` (`h_T`'s divisor `= T1+T2+ιT1+ιT2+δ₀+ιδ₀`
explicitly) — same hypothesis list as `cIotaAmIotaT_mem_principalSubgroup`
itself (this is purely that theorem's conclusion made explicit), plus
`divToPair_eq_C_add_iotaA_add_T_of_split`'s own hypotheses (mostly a
re-derivable subset of the same data, threaded through separately since
that theorem doesn't itself call `cIotaAmIotaT_mem_principalSubgroup`). -/
theorem cIotaAmIotaT_mem_of_le
    [DecidableEq H.Point]
    (hdeg : H.f.natDegree = 5)
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (D : PrincipalDivisorData H) (hD : principalSubgroup H hdeg ≤ D.P)
    (Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y : k)
    (hdet : (caInterpMatrix Ra1X Ra2X P1X P2X).det ≠ 0)
    (hlead : caCoeff Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y 3 ≠ 0)
    (h12 : Ra1X ≠ Ra2X) (h1P1 : Ra1X ≠ P1X) (h1P2 : Ra1X ≠ P2X)
    (h2P1 : Ra2X ≠ P1X) (h2P2 : Ra2X ≠ P2X) (hPP : P1X ≠ P2X)
    (hRa1_curve : Ra1Y ^ 2 = H.f.eval Ra1X) (hRa2_curve : Ra2Y ^ 2 = H.f.eval Ra2X)
    (hP1_curve : P1Y ^ 2 = H.f.eval P1X) (hP2_curve : P2Y ^ 2 = H.f.eval P2X)
    (hRa1Y_ne : Ra1Y ≠ 0) (hRa2Y_ne : Ra2Y ≠ 0) (hP1Y_ne : P1Y ≠ 0) (hP2Y_ne : P2Y ≠ 0)
    (PtRa1 PtRa2 PtιP1 PtιP2 : H.Point)
    (hPtRa1X : PtRa1.X = Ra1X) (hPtRa1Y : PtRa1.Y = Ra1Y)
    (hPtRa2X : PtRa2.X = Ra2X) (hPtRa2Y : PtRa2.Y = Ra2Y)
    (hPtιP1X : PtιP1.X = P1X) (hPtιP1Y : PtιP1.Y = -P1Y)
    (hPtιP2X : PtιP2.X = P2X) (hPtιP2Y : PtιP2.Y = -P2Y)
    (hU_evalRa1 : (uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y).eval Ra1X ≠ 0)
    (hU_evalRa2 : (uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y).eval Ra2X ≠ 0)
    (hU_evalP1 : (uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y).eval P1X ≠ 0)
    (hU_evalP2 : (uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y).eval P2X ≠ 0)
    (hU_ne0 : uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y ≠ 0)
    (T1X T2X : k)
    (hT1 : (uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y).IsRoot T1X)
    (hT2 : (uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y).IsRoot T2X)
    (hTne : T1X ≠ T2X)
    (Q1 Q2 : Polynomial k)
    (hQ1_def : uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y =
      (X - C T1X) * (X - C T2X) * Q1)
    (hQ1T1 : Q1.eval T1X ≠ 0)
    (hQ2_def : uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y =
      (X - C T2X) * (X - C T1X) * Q2)
    (hQ2T2 : Q2.eval T2X ≠ 0)
    (PtT1 PtT2 δ₀ : H.Point)
    (hAeval1 : (denomPolyCA Ra1X Ra2X P1X P2X : k[X]).eval PtT1.X ≠ 0)
    (hAeval2 : (denomPolyCA Ra1X Ra2X P1X P2X : k[X]).eval PtT2.X ≠ 0)
    (hPtT1X : PtT1.X = T1X)
    (hPtT1Y : PtT1.Y = (bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y).eval PtT1.X)
    (hPtT1Y_ne : PtT1.Y ≠ 0)
    (hPtT2X : PtT2.X = T2X)
    (hPtT2Y : PtT2.Y = (bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y).eval PtT2.X)
    (hPtT2Y_ne : PtT2.Y ≠ 0)
    (h1δ : T1X ≠ δ₀.X) (h2δ : T2X ≠ δ₀.X) (hδY : δ₀.Y ≠ 0)
    (hsupp_f : ∀ P, P ∉ ({PtRa1, PtRa2, PtιP1, PtιP2, PtT1, PtT2} : Finset H.Point) →
      ordAt P (-bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y) (1 : k[X]) = 0)
    (hspec_f : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span
        ({toPair H (-bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y) 1} :
          Set (CoordinateRing H)))).factors ≠ 0 → ∃ P, v.asIdeal = pointIdeal P)
    [∀ P : ({PtRa1, PtRa2, PtιP1, PtιP2, PtT1, PtT2} : Finset H.Point),
      Module.Finite k (CoordinateRing H ⧸ pointIdeal P.1 ^
        (ordAt P.1 (-bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y) (1 : k[X])).toNat)]
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
    (single PtRa1 + single PtRa2 + single PtιP1 + single PtιP2 -
      single (Point.iota PtT1) - single (Point.iota PtT2) -
      single δ₀ - single (Point.iota δ₀) : Divisor H) ∈ D.P := by
  classical
  have hraw := cIotaAmIotaT_mem_principalSubgroup (H := H) hdeg hchar hsf
    Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y hdet hlead h12 h1P1 h1P2 h2P1 h2P2 hPP
    hRa1_curve hRa2_curve hP1_curve hP2_curve hRa1Y_ne hRa2Y_ne hP1Y_ne hP2Y_ne
    PtRa1 PtRa2 PtιP1 PtιP2 δ₀ hPtRa1X hPtRa1Y hPtRa2X hPtRa2Y hPtιP1X hPtιP1Y hPtιP2X hPtιP2Y
    hU_evalRa1 hU_evalRa2 hU_evalP1 hU_evalP2 hU_ne0 T1X T2X hT1 hT2 hTne
    Q1 Q2 hQ1_def hQ1T1 hQ2_def hQ2T2 PtT1 PtT2 hAeval1 hAeval2
    hPtT1X hPtT1Y hPtT1Y_ne hPtT2X hPtT2Y hPtT2Y_ne h1δ h2δ hδY
    hsupp_f hspec_f hsupp_hT hspec_hT
  have hLHS := divToPair_eq_C_add_iotaA_add_T_of_split (H := H) hchar hsf
    Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y hdet h12 h1P1 h1P2 h2P1 h2P2 hPP
    hRa1_curve hRa2_curve hP1_curve hP2_curve hRa1Y_ne hRa2Y_ne hP1Y_ne hP2Y_ne
    PtRa1 PtRa2 PtιP1 PtιP2 hPtRa1X hPtRa1Y hPtRa2X hPtRa2Y hPtιP1X hPtιP1Y hPtιP2X hPtιP2Y
    hU_evalRa1 hU_evalRa2 hU_evalP1 hU_evalP2 hU_ne0 T1X T2X hT1 hT2 hTne
    Q1 Q2 hQ1_def hQ1T1 hQ2_def hQ2T2 PtT1 PtT2 hAeval1 hAeval2
    hPtT1X hPtT1Y hPtT1Y_ne hPtT2X hPtT2Y hPtT2Y_ne
  have hPtT12ne : PtT1.X ≠ PtT2.X := by rw [hPtT1X, hPtT2X]; exact hTne
  have hPtT1δ : PtT1.X ≠ δ₀.X := by rw [hPtT1X]; exact h1δ
  have hPtT2δ : PtT2.X ≠ δ₀.X := by rw [hPtT2X]; exact h2δ
  have hRHS := divToPair_hT_eq (H := H) hchar hsf PtT1 PtT2 δ₀
    hPtT12ne hPtT1δ hPtT2δ hPtT1Y_ne hPtT2Y_ne hδY
  have hmem := hD hraw
  rw [← hPtT1X, ← hPtT2X] at hmem
  rw [hLHS, hRHS] at hmem
  have heq : (single PtRa1 + single PtRa2 + single PtιP1 + single PtιP2 +
      single PtT1 + single PtT2 -
      (single PtT1 + single PtT2 + single (Point.iota PtT1) + single (Point.iota PtT2) +
        single δ₀ + single (Point.iota δ₀)) : Divisor H) =
      (single PtRa1 + single PtRa2 + single PtιP1 + single PtιP2 -
      single (Point.iota PtT1) - single (Point.iota PtT2) -
      single δ₀ - single (Point.iota δ₀) : Divisor H) := by abel
  rwa [heq] at hmem

/-- **The honest (†): `C - A - ι(T) + [δ₀] + [ιδ₀] ∈ D.P`**, `G₁ - G₂ - G₃`
composed, for any `D` with `hD : principalSubgroup H hdeg ≤ D.P`. `A :=
[PtιP1's un-iota'd source]+[...]` — spelled out with the actual named
points `PtP1, PtP2` (so that `ι(PtP1) = PtιP1`, matching `cIotaAmIotaT_mem_of_le`'s
`PtιP1,PtιP2` at the divisor level) rather than re-deriving `PtιP1` from
`PtP1` inside this theorem. -/
theorem cAmιTmδmιδ_mem_of_le
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
    (Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y : k)
    (hdet : (caInterpMatrix Ra1X Ra2X P1X P2X).det ≠ 0)
    (hlead : caCoeff Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y 3 ≠ 0)
    (h12 : Ra1X ≠ Ra2X) (h1P1 : Ra1X ≠ P1X) (h1P2 : Ra1X ≠ P2X)
    (h2P1 : Ra2X ≠ P1X) (h2P2 : Ra2X ≠ P2X) (hPP : P1X ≠ P2X)
    (hRa1_curve : Ra1Y ^ 2 = H.f.eval Ra1X) (hRa2_curve : Ra2Y ^ 2 = H.f.eval Ra2X)
    (hP1_curve : P1Y ^ 2 = H.f.eval P1X) (hP2_curve : P2Y ^ 2 = H.f.eval P2X)
    (hRa1Y_ne : Ra1Y ≠ 0) (hRa2Y_ne : Ra2Y ≠ 0) (hP1Y_ne : P1Y ≠ 0) (hP2Y_ne : P2Y ≠ 0)
    (PtRa1 PtRa2 PtP1 PtP2 PtιP1 PtιP2 : H.Point)
    (hPtRa1X : PtRa1.X = Ra1X) (hPtRa1Y : PtRa1.Y = Ra1Y)
    (hPtRa2X : PtRa2.X = Ra2X) (hPtRa2Y : PtRa2.Y = Ra2Y)
    (hPtP1X : PtP1.X = P1X) (hPtP1Y : PtP1.Y = P1Y)
    (hPtP2X : PtP2.X = P2X) (hPtP2Y : PtP2.Y = P2Y)
    (hPtιP1X : PtιP1.X = P1X) (hPtιP1Y : PtιP1.Y = -P1Y)
    (hPtιP2X : PtιP2.X = P2X) (hPtιP2Y : PtιP2.Y = -P2Y)
    (hU_evalRa1 : (uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y).eval Ra1X ≠ 0)
    (hU_evalRa2 : (uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y).eval Ra2X ≠ 0)
    (hU_evalP1 : (uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y).eval P1X ≠ 0)
    (hU_evalP2 : (uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y).eval P2X ≠ 0)
    (hU_ne0 : uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y ≠ 0)
    (T1X T2X : k)
    (hT1 : (uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y).IsRoot T1X)
    (hT2 : (uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y).IsRoot T2X)
    (hTne : T1X ≠ T2X)
    (Q1 Q2 : Polynomial k)
    (hQ1_def : uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y =
      (X - C T1X) * (X - C T2X) * Q1)
    (hQ1T1 : Q1.eval T1X ≠ 0)
    (hQ2_def : uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y =
      (X - C T2X) * (X - C T1X) * Q2)
    (hQ2T2 : Q2.eval T2X ≠ 0)
    (PtT1 PtT2 δ₀ : H.Point)
    (hAeval1 : (denomPolyCA Ra1X Ra2X P1X P2X : k[X]).eval PtT1.X ≠ 0)
    (hAeval2 : (denomPolyCA Ra1X Ra2X P1X P2X : k[X]).eval PtT2.X ≠ 0)
    (hPtT1X : PtT1.X = T1X)
    (hPtT1Y : PtT1.Y = (bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y).eval PtT1.X)
    (hPtT1Y_ne : PtT1.Y ≠ 0)
    (hPtT2X : PtT2.X = T2X)
    (hPtT2Y : PtT2.Y = (bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y).eval PtT2.X)
    (hPtT2Y_ne : PtT2.Y ≠ 0)
    (h1δ : T1X ≠ δ₀.X) (h2δ : T2X ≠ δ₀.X) (hδY : δ₀.Y ≠ 0)
    (hsupp_f : ∀ P, P ∉ ({PtRa1, PtRa2, PtιP1, PtιP2, PtT1, PtT2} : Finset H.Point) →
      ordAt P (-bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y) (1 : k[X]) = 0)
    (hspec_f : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span
        ({toPair H (-bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y) 1} :
          Set (CoordinateRing H)))).factors ≠ 0 → ∃ P, v.asIdeal = pointIdeal P)
    [∀ P : ({PtRa1, PtRa2, PtιP1, PtιP2, PtT1, PtT2} : Finset H.Point),
      Module.Finite k (CoordinateRing H ⧸ pointIdeal P.1 ^
        (ordAt P.1 (-bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y) (1 : k[X])).toNat)]
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
    -- **The `S := ι(T)` convention** (`CAWitness.lean`'s module docstring):
    -- the CALLER's residual points (`T1cur, T2cur` — what
    -- `reducedClass_eq_of_isReduction'` calls `T1, T2`, satisfying `u.IsRoot`
    -- against the TARGET Mumford pair `(u,v)`, `v := -bCA`) are the
    -- hyperelliptic conjugates of THIS file's `PtT1, PtT2` (`uCANew`'s own,
    -- unconjugated roots). Supplied as an explicit identification rather
    -- than derived, matching this project's convention of stating sign/
    -- normalization facts as hypotheses at the point they're needed.
    (T1cur T2cur : H.Point)
    (hT1eq : T1cur = Point.iota PtT1) (hT2eq : T2cur = Point.iota PtT2) :
    (single PtRa1 + single PtRa2 - single PtP1 - single PtP2 -
      single T1cur - single T2cur +
      single δ₀ + single (Point.iota δ₀) : Divisor H) ∈ D.P := by
  classical
  subst hT1eq; subst hT2eq
  have hG1 := cIotaAmIotaT_mem_of_le (H := H) hdeg hchar hsf D hD
    Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y hdet hlead h12 h1P1 h1P2 h2P1 h2P2 hPP
    hRa1_curve hRa2_curve hP1_curve hP2_curve hRa1Y_ne hRa2Y_ne hP1Y_ne hP2Y_ne
    PtRa1 PtRa2 PtιP1 PtιP2 hPtRa1X hPtRa1Y hPtRa2X hPtRa2Y hPtιP1X hPtιP1Y hPtιP2X hPtιP2Y
    hU_evalRa1 hU_evalRa2 hU_evalP1 hU_evalP2 hU_ne0 T1X T2X hT1 hT2 hTne
    Q1 Q2 hQ1_def hQ1T1 hQ2_def hQ2T2 PtT1 PtT2 δ₀ hAeval1 hAeval2
    hPtT1X hPtT1Y hPtT1Y_ne hPtT2X hPtT2Y hPtT2Y_ne h1δ h2δ hδY
    hsupp_f hspec_f hsupp_hT hspec_hT
  have hG2 := fiber_diff_mem_of_le (H := H) hdeg hchar hsf D hD hspec_linX PtP1 δ₀
  have hG3 := fiber_diff_mem_of_le (H := H) hdeg hchar hsf D hD hspec_linX PtP2 δ₀
  have hcombine := D.P.sub_mem (D.P.sub_mem hG1 hG2) hG3
  have hιPtP1X : (Point.iota PtP1).X = PtιP1.X := by rw [Point.iota_X, hPtP1X, hPtιP1X]
  have hιPtP1Y : (Point.iota PtP1).Y = PtιP1.Y := by rw [Point.iota_Y, hPtP1Y, hPtιP1Y]
  have hιPtP1 : Point.iota PtP1 = PtιP1 := Subtype.ext (Prod.ext hιPtP1X hιPtP1Y)
  have hιPtP2X : (Point.iota PtP2).X = PtιP2.X := by rw [Point.iota_X, hPtP2X, hPtιP2X]
  have hιPtP2Y : (Point.iota PtP2).Y = PtιP2.Y := by rw [Point.iota_Y, hPtP2Y, hPtιP2Y]
  have hιPtP2 : Point.iota PtP2 = PtιP2 := Subtype.ext (Prod.ext hιPtP2X hιPtP2Y)
  have heq :
      ((single PtRa1 + single PtRa2 + single PtιP1 + single PtιP2 -
          single (Point.iota PtT1) - single (Point.iota PtT2) -
          single δ₀ - single (Point.iota δ₀)) -
        (single PtP1 + single (Point.iota PtP1) - single δ₀ - single (Point.iota δ₀)) -
        (single PtP2 + single (Point.iota PtP2) - single δ₀ - single (Point.iota δ₀))
        : Divisor H) =
      (single PtRa1 + single PtRa2 - single PtP1 - single PtP2 -
        single (Point.iota PtT1) - single (Point.iota PtT2) +
        single δ₀ + single (Point.iota δ₀) : Divisor H) := by
    rw [hιPtP1, hιPtP2]; abel
  rwa [heq] at hcombine

end DecoupledSystem
end Genus2Lean
