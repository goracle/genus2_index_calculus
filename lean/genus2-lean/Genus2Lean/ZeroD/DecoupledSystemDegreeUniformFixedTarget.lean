import Mathlib
import Genus2Lean.ZeroD.AlphaLocusDegreeUniform
import Genus2Lean.ZeroD.MatchingSolutionSwapSymmetry

/-!
# The actual closing theorem: a `p`-independent bound on the fixed-target
# solution set, restated over `SampleTargetFromAlpha`

`decoupledSystem_degree_uniform` (`AlphaLocusDegreeUniform.lean`) is the
project's OLD target theorem, proved via `GenericPeelChainHyp`/
`Rdec p ⧸ Ideal.span (genList ...)` — the route `GenListFinrankAssembly
.lean`'s `genList_finrank_le` (still `sorry`) was building toward. Per
Claire's direction this pass: that whole route is superseded. The
`Stab(S)`/monic-annihilator machinery it depends on chased a much
harder problem (bounding `finrank` down to a sharp value, or ruling out
a whole gauge orbit of `(alpha,alpha')` pairs) than what
`decoupledSystem_degree_uniform` actually needs to close the 8th-moment
gap — a `p`-INDEPENDENT constant bound on the solution set, full stop,
no sharper.

**`fixedTargetSolutions_ncard_le_four`
(`MatchingSolutionSwapSymmetry.lean`) already IS that bound.** For fixed
classes `A B : Jacobian H D`, `(FixedTargetSolutions D δ₀ A B).ncard ≤
4` — unconditional in `p`, no `Bad`/exceptional-set machinery, no
`GenericPeelChainHyp`, no `Rdec p ⧸ Ideal.span _`. This file restates
that bound directly in terms of `SampleTargetFromAlpha` — `d := 4`,
proved outright, no existential search for `d` needed the way the old
statement's `p ^ n` placeholder implied. No `Bad`/exceptional set is
constructed or needed: the bound holds for every `(A,B)` pair, not
"outside finitely many bad ones" — see the main theorem's own docstring
for why this is NOT literally the same statement shape as
`decoupledSystem_degree_uniform` (different conclusion type — a
point-tuple `Set.ncard` bound, not a ring-quotient `Nat.card` bound),
just the same underlying goal, proved directly instead.

## What is genuinely new here vs. what already existed

Nothing mathematically new — this is a restatement/assembly, wiring
`fixedTargetSolutions_ncard_le_four` into the shape
`decoupledSystem_degree_uniform` was always meant to have (a bound
independent of the sample data, quantified the way the roadmap's
"uniform in `(alpha,alpha')`" goal actually asks for) and connecting it
to `SampleTargetFromAlpha p H D aClass δ₀` (`sa`/`sb`, carrying
`sa.alpha`/`sb.alpha`) rather than leaving the bound stated only in
terms of raw `A B : Jacobian H D`. The point-tuple solving the matching
equation for `sa`/`sb`'s own pair-sums is exactly
`FixedTargetSolutions D δ₀ (s D δ₀ sa.P1 + s D δ₀ sa.P2) (s D δ₀ sb.P1 +
s D δ₀ sb.P2)`.

## What this still does NOT prove — the honest remaining hypotheses

Carried over unchanged from `fixedTargetSolutions_ncard_le_four` itself,
not newly introduced or newly discharged here:

- `hbridge : D.P ≤ principalSubgroup H hdeg` — the bridge direction
  between `IsOnlyEffectiveInClass` and `s_add_s_eq_s_add_s_iff`, taken
  as an explicit hypothesis, not derived (the two subgroups' equality is
  itself unproved project-wide).
- `IsOnlyEffectiveInClass` for both `(sa.P1,sa.P2)` and `(sb.P1,sb.P2)`
  — taken as an explicit hypothesis rather than invoked by name, exactly
  matching `MatchingSolutionSwapSymmetry.lean`'s own stated caveat.

**Not attempted here, and not needed for the `p`-independent-bound goal
this file targets** (left for whoever eventually wants the sharper
"gravy" result, not required for `decoupledSystem_degree_uniform`'s own
purpose): the `Stab(S)`/gauge-symmetry argument
(`StabOfSmallSetTrivial.lean`, `ROADMAP-alpha-locus.md`'s `Stab(S)`
section) that would shrink 4 toward 1 by exploiting the
`(alpha,alpha') ↦ (alpha+c,alpha'+c)` gauge symmetry of the matching
equation. That symmetry is real (the equation only ever sees
`alpha - alpha'`), but sharpening the bound it implies is a genuine
strengthening on top of an already-sufficient result, not a gap in this
theorem. -/

open HyperellipticPolynomial
open Divisor
open Genus2Lean.MatchingSolutionSwapSymmetry

namespace Genus2Lean
namespace DecoupledSystem

variable {k : Type*} [Field k] {H : HyperellipticPolynomial k}
variable {D : PrincipalDivisorData H}
variable [IsDedekindDomain (CoordinateRing H)]

/-- **The actual closing theorem.** For any two `SampleTargetFromAlpha`
samples `sa`, `sb` sharing `aClass`/`δ₀`, the set of point-quadruples
`(P1',P2',P3',P4')` solving the SAME fixed-target matching problem as
`sa`/`sb` (i.e. `s P1'+s P2' = s sa.P1+s sa.P2` and `s P3'+s P4' = s
sb.P1+s sb.P2`) has at most 4 elements — a bound independent of `p` and
independent of `sa.alpha`/`sb.alpha`.

**Not the same statement shape as `decoupledSystem_degree_uniform`** —
that theorem's conclusion is `Nat.card (Rdec p ⧸ Ideal.span (genList
...)) ≤ d`, a RING-quotient cardinality, wrapped in an `∃ d Bad,
IsSmallExceptionalSet ... ∧ ...` existential built for the (now dead)
`GenericPeelChainHyp` route. Bridging a point-tuple `Set.ncard` bound
to that ring-quotient statement is not attempted here and is not
needed — this theorem is the direct, self-contained replacement for
what `decoupledSystem_degree_uniform` was FOR (the roadmap's TL;DR
target, `B^4 ≤ d · #{Delta : X(Delta) > 0}` with `d` independent of
`p`), not a term that typechecks against that theorem's old signature.
No `Bad`/exceptional set is needed at all: the bound below holds
unconditionally for every `(sa, sb)` pair satisfying the hypotheses
below, not "outside finitely many bad `(alpha,alpha')` pairs." -/
theorem fixedTargetSolutions_ncard_le_four_sampleTargetFromAlpha
    [DecidableEq H.Point]
    {p : ℕ} [Fact (Nat.Prime p)]
    {aClass : Jacobian H D} {δ₀ : H.Point}
    (sa sb : SampleTargetFromAlpha p H D aClass δ₀)
    {hdeg : H.f.natDegree = 5}
    (hbridge : D.P ≤ principalSubgroup H hdeg)
    (heffective12 : IsOnlyEffectiveInClass hdeg sa.P1 sa.P2)
    (heffective34 : IsOnlyEffectiveInClass hdeg sb.P1 sb.P2) :
    (FixedTargetSolutions D δ₀
      (s D δ₀ sa.P1 + s D δ₀ sa.P2) (s D δ₀ sb.P1 + s D δ₀ sb.P2)).ncard ≤ 4 :=
  fixedTargetSolutions_ncard_le_four (D := D) (hdeg := hdeg) (δ₀ := δ₀)
    hbridge heffective12 heffective34
    (s D δ₀ sa.P1 + s D δ₀ sa.P2) (s D δ₀ sb.P1 + s D δ₀ sb.P2) rfl rfl

end DecoupledSystem
end Genus2Lean
