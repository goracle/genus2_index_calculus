import Mathlib
import Genus2Lean.ZeroD.AlphaLocusDegreeUniform
import Genus2Lean.ZeroD.AlphaLocusDegreeUniformTangent

/-! # Shared `CoefficientData`/`ReductionData` bundles for the seven
`reducedClass_eq_of_isReduction'` variants

`ROADMAP-reducedClass-dispatcher.md`, "Suggested order" step 2. Per
that doc's own field-by-field diff of the two ALREADY-bundled variants
(`TangentCoefficientData`/`TangentReductionData`,
`AlphaLocusDegreeUniformTangent.lean`; `TangentTargetCoefficientData`/
`TangentTargetReductionData`, `AlphaLocusDegreeUniformTangentTarget.lean`):

- **`ReductionData` is IDENTICAL across both existing instances** —
  same `coeffs` projection, same `hReducedClass` statement, same proof
  term (`sampleP1P2_sub_two_delta_mem`). Nothing in it mentions
  `Ra`/`Ra2`/tangency/cross-identification at all; it is entirely
  about `sa.P1,sa.P2,δ₀`, which every one of the seven variants shares
  unchanged. One shared structure genuinely suffices.
- **`CoefficientData` differs by exactly one field** between the two
  existing instances: `TangentCoefficientData` (anchor doubled) has
  `coeff_hMumfordTarget : IsMumfordTarget4 ...`;
  `TangentTargetCoefficientData` (target doubled) has
  `coeff_hMumfordUa : IsMumfordUa ...` instead. Each file only names
  the Mumford fact for the side it does NOT make tangent — a real
  asymmetry, not an oversight. Resolved here by carrying BOTH fields
  unconditionally (`coeff_hMumfordUa` AND `coeff_hMumfordTarget`):
  this costs the caller one extra `Prop` to supply, not new proof
  content (both facts are independently available in any real
  instantiation, since the tangency itself is pinned down elsewhere,
  in the construction-specific `AssemblyData` tier that step 3 of the
  roadmap still owes) and lets every branch of the eventual dispatcher
  share one coefficient bundle rather than converting between two
  near-identical types depending on which branch fired.

This file does NOT yet touch the two existing
`Tangent(Target)?CoefficientData`/`...ReductionData` structures or
their call sites (it only imports `AlphaLocusDegreeUniformTangent.lean`
for `sampleP1P2_sub_two_delta_mem`, the shared proof-term helper — no
circularity risk, since that file predates this one and doesn't import
it back). Per the roadmap's own step 2 note, editing those existing
structures is a real edit to already-proved code and belongs with the
REPL-tested, one-theorem-at-a-time pass that comes after this file
exists and REPL-confirms clean on its own. This file is purely
additive: two new structures, no existing theorem's signature changed
yet. -/

noncomputable section

open Polynomial
open HyperellipticPolynomial
open HyperellipticPolynomial.Divisor

namespace Genus2Lean
namespace DecoupledSystem

open TheDataDerivation

variable {k : Type*} [Field k] {H : HyperellipticPolynomial k}
variable {D : PrincipalDivisorData H}

/-- **Shared curve/coefficient layer**, common to all seven
`reducedClass_eq_of_isReduction'` variants. Carries BOTH
`coeff_hMumfordUa` and `coeff_hMumfordTarget` (see module docstring for
why this is a superset of either existing `Tangent`/`TangentTarget`
`CoefficientData`, not a narrower common core) so every variant's
dispatcher branch can consume the same bundle type. -/
structure CoefficientData
    {p : ℕ} [Fact (Nat.Prime p)] [Fact (p ≠ 2)]
    {H : HyperellipticPolynomial (F p)} [IsDedekindDomain (CoordinateRing H)]
    {D : PrincipalDivisorData H}
    {aClass : Jacobian H D} {δ₀ : H.Point}
    (sa : SampleTargetFromAlpha p H D aClass δ₀) where
  coeff_c0 : F p
  coeff_c1 : F p
  coeff_c2 : F p
  coeff_c3 : F p
  coeff_c4 : F p
  coeff_ua0 : F p
  coeff_ua1 : F p
  coeff_va0 : F p
  coeff_va1 : F p
  coeff_hf : H.f = curvePoly p coeff_c0 coeff_c1 coeff_c2 coeff_c3 coeff_c4
  coeff_hMumfordUa : IsMumfordUa p coeff_c0 coeff_c1 coeff_c2 coeff_c3 coeff_c4
      coeff_ua0 coeff_ua1 coeff_va0 coeff_va1
  coeff_hMumfordTarget : IsMumfordTarget4 p coeff_c0 coeff_c1 coeff_c2 coeff_c3 coeff_c4
      sa.toSampleTarget.u0 sa.toSampleTarget.u1
      sa.toSampleTarget.v0 sa.toSampleTarget.v1

/-- **Shared `reducedClass`-decomposition layer**, common to all seven
variants. Identical to both existing `Tangent`/`TangentTarget`
`ReductionData` structures — `hReducedClass` mentions only
`sa.P1,sa.P2,δ₀`, never the anchor/target tangency data that
distinguishes the seven branches, so no per-variant field is needed
here at all. -/
structure ReductionData
    {p : ℕ} [Fact (Nat.Prime p)] [Fact (p ≠ 2)]
    {H : HyperellipticPolynomial (F p)} [IsDedekindDomain (CoordinateRing H)]
    {D : PrincipalDivisorData H}
    {aClass : Jacobian H D} {δ₀ : H.Point}
    (sa : SampleTargetFromAlpha p H D aClass δ₀) where
  coeffs : CoefficientData sa
  hReducedClass :
    sa.reducedClass =
      sa.alpha • aClass -
        toJacobian D
          (⟨single sa.P1 + single sa.P2 - (2 : ℤ) • single δ₀,
            sampleP1P2_sub_two_delta_mem sa⟩ : Divisor0 H)

end DecoupledSystem
end Genus2Lean
