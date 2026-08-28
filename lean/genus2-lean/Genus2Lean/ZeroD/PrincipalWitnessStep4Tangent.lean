import Mathlib
import Genus2Lean.ZeroD.CAWitnessTangent
import Genus2Lean.ZeroD.CAWitnessDivisorTangent
import Genus2Lean.ZeroD.CAWitnessAssemblyTangent
import Genus2Lean.ZeroD.PrincipalWitness
import Genus2Lean.ZeroD.PrincipalWitnessStep4
import Genus2Lean.PrincipalDivisorSubgroup

/-! # Tangent-case sibling of `PrincipalWitnessStep4.lean`'s Part 3
# (`cIotaAmIotaT_mem_principalSubgroup`)

`ROADMAP-principal-witness-tangent-assembly.md`'s Step 4. `Ra1 = Ra2 =: Ra`
(the doubled anchor root) sibling of `cIotaAmIotaT_mem_principalSubgroup`.
Same proof SHAPE as the split version: the goal is `divToPairRatio` of `f
:= y - bCATangent(x)` (support `{Ra,ιP1,ιP2}`, three points, `Ra` doubled)
against `h_T := (linX T1X * linX T2X) * linX δ₀X` (support
`{T1,T2,ιT1,ιT2,δ₀,ιδ₀}`, unchanged from the split case — `T1,T2,δ₀` are
never on the anchor's tangent axis, so `divToPair_hT_eq`
(`PrincipalWitnessStep4.lean`) needs no tangent sibling at all), closed via
`AddSubgroup.subset_closure` off the caller-supplied `hsupp_f`/`hspec_f`/
`hsupp_hT`/`hspec_hT` (support+spectral hypotheses on each side) plus a
matching pole-order pair. `bCATangent_ordInfOfPair` (`CAWitnessTangent.
lean`) supplies that pole order (`-6`) in place of the split case's
`bCA_ordInfOfPair`; `ordInfOfPair_hT` (`PrincipalWitnessStep4.lean`,
already generic) is reused unchanged for the `h_T` side.

**Support-set bookkeeping is the only real difference from the split
proof**: `divToPairRatio`'s LHS support is `{PtRa, PtιP1, PtιP2}` (three
points, `Ra1,Ra2` collapsed) rather than the split case's six-point
`{PtRa1,PtRa2,PtιP1,PtιP2,PtT1,PtT2}` — but the split case's own LHS
support in `cIotaAmIotaT_mem_principalSubgroup` is
`{PtRa1,PtRa2,PtιP1,PtιP2,PtT1,PtT2}` (it already folds `T1,T2` into the
same six-point set as the anchor/`A` points, since `f`'s zero-divisor
there is the full six-point sum). Here, `divToPair_eq_C_add_iotaA_of_
split_tangent`'s own conclusion only covers `{PtRa,PtιP1,PtιP2}` (three
points) — `T1,T2` are NOT part of `f`'s zero set in that theorem, they are
`uCANewTangent`'s roots, entering via a SEPARATE `IsRoot` hypothesis
exactly as `CAWitnessAssemblyTangent.lean`'s own module docstring frames
it (mirroring the split case's own `T1,T2`-via-`uCANew`-root pattern, not
a new wrinkle). -/

noncomputable section

open Polynomial
open HyperellipticPolynomial
open HyperellipticPolynomial.Divisor

namespace Genus2Lean
namespace DecoupledSystem

variable {k : Type*} [Field k] [DecidableEq k]
variable {H : HyperellipticPolynomial k} [IsDedekindDomain (CoordinateRing H)]

/-- **`G₁`, tangent case: `2•[Ra] + [ιP1] + [ιP2] - [T1]-[T2]-[ιT1]-[ιT2]
-[δ₀]-[ιδ₀] ∈ principalSubgroup`.** Tangent sibling of
`cIotaAmIotaT_mem_principalSubgroup`. `f := y - bCATangent(x)`'s divisor
on `{PtRa,PtιP1,PtιP2}` (`divToPair_eq_C_add_iotaA_of_split_tangent`)
minus `h_T := (linX T1X * linX T2X) * linX δ₀X`'s divisor
(`divToPair_hT_eq`, unchanged from the split case). Same
`divToPairRatio`/`AddSubgroup.subset_closure` assembly as the split
version, `bCATangent_ordInfOfPair` supplying the `-6` pole order in place
of `bCA_ordInfOfPair`. -/
theorem cIotaAmIotaT_mem_principalSubgroup_tangent
    [DecidableEq k] [DecidableEq H.Point]
    (hdeg : H.f.natDegree = 5)
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (RaX P1X P2X RaY P1Y P2Y vaDerivAtRa : k)
    (hdet : (caTangentInterpMatrix RaX P1X P2X).det ≠ 0)
    (hlead : caTangentCoeff RaX P1X P2X RaY vaDerivAtRa P1Y P2Y 3 ≠ 0)
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
    (hU_evalP2 : (uCANewTangent H RaX P1X P2X RaY vaDerivAtRa P1Y P2Y).eval P2X ≠ 0)
    (T1X T2X : k)
    (hT1 : (uCANewTangent H RaX P1X P2X RaY vaDerivAtRa P1Y P2Y).IsRoot T1X)
    (hT2 : (uCANewTangent H RaX P1X P2X RaY vaDerivAtRa P1Y P2Y).IsRoot T2X)
    (hTne : T1X ≠ T2X)
    (PtT1 PtT2 δ₀ : H.Point)
    (hPtT1X : PtT1.X = T1X)
    (hPtT1Y_ne : PtT1.Y ≠ 0)
    (hPtT2X : PtT2.X = T2X)
    (hPtT2Y_ne : PtT2.Y ≠ 0)
    (h1δ : T1X ≠ δ₀.X) (h2δ : T2X ≠ δ₀.X) (hδY : δ₀.Y ≠ 0)
    (hsupp_f : ∀ P, P ∉ ({PtRa, PtιP1, PtιP2} : Finset H.Point) →
      ordAt P (-bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) (1 : k[X]) = 0)
    (hspec_f : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span
        ({toPair H (-bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) 1} :
          Set (CoordinateRing H)))).factors ≠ 0 → ∃ P, v.asIdeal = pointIdeal P)
    [∀ P : ({PtRa, PtιP1, PtιP2} : Finset H.Point),
      Module.Finite k (CoordinateRing H ⧸ pointIdeal P.1 ^
        (ordAt P.1 (-bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) (1 : k[X])).toNat)]
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
    (divToPair (-bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) (1 : k[X])
        ({PtRa, PtιP1, PtιP2} : Finset H.Point) -
      divToPair ((linX T1X * linX T2X) * linX δ₀.X) (0 : k[X])
        ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀, Point.iota δ₀} : Finset H.Point)) ∈
      principalSubgroup H hdeg := by
  have hgoal_eq :
      (divToPair (-bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) (1 : k[X])
          ({PtRa, PtιP1, PtιP2} : Finset H.Point) -
        divToPair ((linX T1X * linX T2X) * linX δ₀.X) (0 : k[X])
          ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀, Point.iota δ₀} : Finset H.Point)) =
      divToPairRatio (-bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) (1 : k[X])
          ({PtRa, PtιP1, PtιP2} : Finset H.Point)
        ((linX T1X * linX T2X) * linX δ₀.X) (0 : k[X])
          ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀, Point.iota δ₀} : Finset H.Point) := rfl
  rw [hgoal_eq]
  apply AddSubgroup.subset_closure
  refine ⟨-bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y, 1,
    ({PtRa, PtιP1, PtιP2} : Finset H.Point),
    fun ⟨_, hB⟩ => one_ne_zero hB, hsupp_f, hspec_f, ‹_›,
    (linX T1X * linX T2X) * linX δ₀.X, 0,
    ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀, Point.iota δ₀} : Finset H.Point),
    ?_, hsupp_hT, hspec_hT, ‹_›, ?_, rfl⟩
  · refine fun ⟨hA, _⟩ => ?_
    exact mul_ne_zero (mul_ne_zero (linX_ne_zero T1X) (linX_ne_zero T2X)) (linX_ne_zero δ₀.X) hA
  · rw [bCATangent_ordInfOfPair RaX P1X P2X RaY vaDerivAtRa P1Y P2Y hlead, ordInfOfPair_hT]

end DecoupledSystem
end Genus2Lean
