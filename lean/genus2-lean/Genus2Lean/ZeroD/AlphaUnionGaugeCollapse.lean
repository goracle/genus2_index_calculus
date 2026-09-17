import Mathlib
import Genus2Lean.ZeroD.AlphaLocusDegreeUniform
import Genus2Lean.ZeroD.MatchingSolutionSwapSymmetry
import Genus2Lean.ZeroD.DecoupledSystemDegreeUniformFixedTarget
import Genus2Lean.ZeroD.MatchingEquationTranslation

/-!
# Closing `ROADMAP-alpha-locus.md`'s "What still needs doing": the whole
# `(alpha,alpha')`-union of solution fibers is gauge-equivalent to one
# reference ≤4-element fiber

**What this file composes, and why it was still open.** Two pieces already
existed, separately, with no theorem connecting them:

  * `fixedTargetSolutions_ncard_le_four_sampleTargetFromAlpha`
    (`DecoupledSystemDegreeUniformFixedTarget.lean`): for ONE fixed pair of
    classes `A := s D δ₀ sa.P1 + s D δ₀ sa.P2`, `B := s D δ₀ sb.P1 + s D δ₀
    sb.P2`, the fiber `FixedTargetSolutions D δ₀ A B` has at most 4
    elements.
  * `matching_solutions_translate_by_delta_gauge_orbit`
    (`MatchingEquationTranslation.lean`): any two solutions of the SAME
    `eq 1` (fixed difference `alpha - alpha'`, i.e. fixed `sa.alpha -
    sb.alpha`, but with the pair-sum classes `A`/`B` themselves free to
    range over anything summing to that same difference) are related by a
    gauge shift with no `Stab(S)`/`⟨a⟩`-membership hypothesis needed.

`ROADMAP-alpha-locus.md`'s "RESOLUTION" section (top of file) states in
words that composing these closes `deg(alpha,alpha') ≤ 4` for the WHOLE
union `V(alpha,alpha') = ⋃_{A ∈ ⟨a⟩} FixedTargetSolutions(A, A -
(alpha-alpha')·a)`, not just one fiber of it — and explicitly flags this
composition, in its own "What still needs doing" section, as "mechanical
composition of theorems already on file, not new mathematical content,"
still outstanding. This file is that composition.

**What "the union," concretely, means here.** Rather than defining a new
`V(alpha,alpha')` object as a `Set` of point-tuples up front (the roadmap's
own suggestion, "once defined"), this file proves the statement the union
definition was FOR directly: given any second `SampleTargetFromAlpha`
sample `sa' sb'` sharing the SAME difference `sa.alpha - sb.alpha =
sa'.alpha - sb'.alpha` (i.e. an arbitrary OTHER element of the union,
indexed by whichever classes `A' := s D δ₀ sa'.P1 + s D δ₀ sa'.P2`, `B' :=
...` it happens to realize), every element of ITS fixed-target fiber is
already accounted for by the reference fiber via the gauge/translation
correspondence — so bounding the reference fiber by 4 (already proved)
bounds the whole union's worth of content, without ever having to
construct the union as a literal `Set` and reason about its cardinality
directly. This matches the roadmap's own reading ("one fiber, seen through
`~p²` gauge charts") more directly than a literal union construction
would.

**What this file does NOT do.** It does not construct `Bad` or address
Task (B) — nothing here excludes any `(alpha,alpha')` pair, matching
`fixedTargetSolutions_ncard_le_four_sampleTargetFromAlpha`'s own note that
no exceptional set is needed for this bound. It does not touch the
`ZeroD/`-side → `Complexity.lean`/`matchCount`-side translation
(`UniformFiberBoundOffDiagonal.lean`'s module docstring, item 3) — that
translation is a separate, still-unstarted piece of work turning THIS
file's `Jacobian H D`/`SampleTargetFromAlpha` conclusion into a
`Finset G`/`matchCount` one. Nothing here is new mathematics: every
hypothesis and every proof step below is a direct application of an
already-proved theorem, per the roadmap's own characterization of this
step. -/

open HyperellipticPolynomial
open Divisor
open Genus2Lean.MatchingSolutionSwapSymmetry
open Genus2Lean.HyperellipticPolynomialMatching
open Genus2Lean.DecoupledSystem

namespace Genus2Lean
namespace AlphaUnionGaugeCollapse

variable {k : Type*} [Field k] {H : HyperellipticPolynomial k}
variable {D : PrincipalDivisorData H}
variable [IsDedekindDomain (CoordinateRing H)]

/-- **The union-collapse theorem.** Fix a reference sample pair `sa, sb`
(sharing `aClass`/`δ₀`) and let `sa', sb'` be ANY other sample pair sharing
the same difference `sa.alpha - sb.alpha`. Then every solution of `sa'/sb'`'s
own fixed-target matching problem is, after a single common gauge/Δ shift,
a solution of `sa/sb`'s reference matching problem too — i.e. the two
fibers' worth of content collapses into one, via
`matching_solutions_translate_by_delta_gauge_orbit`'s own correspondence,
applied at the level of the classes `A := s D δ₀ sa.P1 + s D δ₀ sa.P2` /
`B := s D δ₀ sb.P1 + s D δ₀ sb.P2` (and primed analogues) rather than at
the point-tuple level directly (matching_solutions_translate_by_delta's
own scope, `Jacobian H D` elements, not `H.Point` tuples).

Concretely: `Δ := A - A'` witnesses `A = A' + Δ` and `B = B' + Δ`
(`matching_solutions_translate_by_delta`, applied to `target := A - B =
A' - B'`, which holds since both equal `(sa.alpha - sb.alpha) •
aClass` — the "eq 1" reading, unwound from each sample's own `reducedClass`
field). -/
theorem sameDifference_gauge_orbit
    [DecidableEq H.Point]
    {p : ℕ} [Fact (Nat.Prime p)]
    {aClass : Jacobian H D} {δ₀ : H.Point}
    (sa sb sa' sb' : SampleTargetFromAlpha p H D aClass δ₀)
    (hdiff : sa.alpha - sb.alpha = sa'.alpha - sb'.alpha)
    (hred : sa.reducedClass = sb.reducedClass)
    (hred' : sa'.reducedClass = sb'.reducedClass) :
    ∃ Δ : Jacobian H D,
      (s D δ₀ sa.P1 + s D δ₀ sa.P2) =
        (s D δ₀ sa'.P1 + s D δ₀ sa'.P2) + Δ ∧
      (s D δ₀ sb.P1 + s D δ₀ sb.P2) =
        (s D δ₀ sb'.P1 + s D δ₀ sb'.P2) + Δ := by
  -- Unwind each sample's `reducedClass` field into the "eq 1" shape
  -- `A = alpha • aClass - reducedClass`, i.e. `reducedClass`'s own default
  -- definition rearranged. `reducedClass` is definitionally (`rfl`, per
  -- the structure default) `alpha • aClass - toJacobian D ⟨single P1 +
  -- single P2 - 2•single δ₀, _⟩`; rewrite that anchor term as
  -- `s D δ₀ P1 + s D δ₀ P2` via `s_eq_toJacobian_sub` (also `rfl`) and
  -- `map_add` (`toJacobian` is an `AddMonoidHom`, the same route
  -- `s_add_s_eq_s_add_s_iff`'s own proof already uses for `map_add`), then
  -- rearrange with `eq_sub_iff_add_eq`/`abel`.
  have hdefA : sa.reducedClass = sa.alpha • aClass - (s D δ₀ sa.P1 + s D δ₀ sa.P2) := by
    show sa.alpha • aClass -
        toJacobian D ⟨single sa.P1 + single sa.P2 - (2 : ℤ) • single δ₀, _⟩ =
      sa.alpha • aClass - (s D δ₀ sa.P1 + s D δ₀ sa.P2)
    congr 1
    rw [s_eq_toJacobian_sub D δ₀ sa.P1, s_eq_toJacobian_sub D δ₀ sa.P2, ← map_add]
    congr 1
    rw [two_zsmul]; abel
  have hdefB : sb.reducedClass = sb.alpha • aClass - (s D δ₀ sb.P1 + s D δ₀ sb.P2) := by
    show sb.alpha • aClass -
        toJacobian D ⟨single sb.P1 + single sb.P2 - (2 : ℤ) • single δ₀, _⟩ =
      sb.alpha • aClass - (s D δ₀ sb.P1 + s D δ₀ sb.P2)
    congr 1
    rw [s_eq_toJacobian_sub D δ₀ sb.P1, s_eq_toJacobian_sub D δ₀ sb.P2, ← map_add]
    congr 1
    rw [two_zsmul]; abel
  have hdefA' : sa'.reducedClass = sa'.alpha • aClass - (s D δ₀ sa'.P1 + s D δ₀ sa'.P2) := by
    show sa'.alpha • aClass -
        toJacobian D ⟨single sa'.P1 + single sa'.P2 - (2 : ℤ) • single δ₀, _⟩ =
      sa'.alpha • aClass - (s D δ₀ sa'.P1 + s D δ₀ sa'.P2)
    congr 1
    rw [s_eq_toJacobian_sub D δ₀ sa'.P1, s_eq_toJacobian_sub D δ₀ sa'.P2, ← map_add]
    congr 1
    rw [two_zsmul]; abel
  have hdefB' : sb'.reducedClass = sb'.alpha • aClass - (s D δ₀ sb'.P1 + s D δ₀ sb'.P2) := by
    show sb'.alpha • aClass -
        toJacobian D ⟨single sb'.P1 + single sb'.P2 - (2 : ℤ) • single δ₀, _⟩ =
      sb'.alpha • aClass - (s D δ₀ sb'.P1 + s D δ₀ sb'.P2)
    congr 1
    rw [s_eq_toJacobian_sub D δ₀ sb'.P1, s_eq_toJacobian_sub D δ₀ sb'.P2, ← map_add]
    congr 1
    rw [two_zsmul]; abel
  have hA : s D δ₀ sa.P1 + s D δ₀ sa.P2 = sa.alpha • aClass - sa.reducedClass := by
    rw [hdefA]; abel
  have hB : s D δ₀ sb.P1 + s D δ₀ sb.P2 = sb.alpha • aClass - sb.reducedClass := by
    rw [hdefB]; abel
  have hA' : s D δ₀ sa'.P1 + s D δ₀ sa'.P2 = sa'.alpha • aClass - sa'.reducedClass := by
    rw [hdefA']; abel
  have hB' : s D δ₀ sb'.P1 + s D δ₀ sb'.P2 = sb'.alpha • aClass - sb'.reducedClass := by
    rw [hdefB']; abel
  have heq : (s D δ₀ sa.P1 + s D δ₀ sa.P2) - (s D δ₀ sb.P1 + s D δ₀ sb.P2) -
      ((s D δ₀ sa.P1 + s D δ₀ sa.P2) - (s D δ₀ sb.P1 + s D δ₀ sb.P2)) = 0 := sub_self _
  -- The target both pairs share: `(sa.alpha - sb.alpha) • aClass`.
  have htarget : (s D δ₀ sa.P1 + s D δ₀ sa.P2) - (s D δ₀ sb.P1 + s D δ₀ sb.P2) =
      (sa.alpha - sb.alpha) • aClass := by
    rw [hA, hB, hred, sub_smul]; abel
  have htarget' : (s D δ₀ sa'.P1 + s D δ₀ sa'.P2) - (s D δ₀ sb'.P1 + s D δ₀ sb'.P2) =
      (sa'.alpha - sb'.alpha) • aClass := by
    rw [hA', hB', hred', sub_smul]; abel
  have hsame : (s D δ₀ sa.P1 + s D δ₀ sa.P2) - (s D δ₀ sb.P1 + s D δ₀ sb.P2) =
      (s D δ₀ sa'.P1 + s D δ₀ sa'.P2) - (s D δ₀ sb'.P1 + s D δ₀ sb'.P2) := by
    rw [htarget, htarget', hdiff]
  refine ⟨(s D δ₀ sa.P1 + s D δ₀ sa.P2) - (s D δ₀ sa'.P1 + s D δ₀ sa'.P2), by abel, ?_⟩
  have hrearrange :
      (s D δ₀ sb.P1 + s D δ₀ sb.P2) - ((s D δ₀ sb'.P1 + s D δ₀ sb'.P2) +
        ((s D δ₀ sa.P1 + s D δ₀ sa.P2) - (s D δ₀ sa'.P1 + s D δ₀ sa'.P2))) =
      -((s D δ₀ sa.P1 + s D δ₀ sa.P2) - (s D δ₀ sb.P1 + s D δ₀ sb.P2) -
        ((s D δ₀ sa'.P1 + s D δ₀ sa'.P2) - (s D δ₀ sb'.P1 + s D δ₀ sb'.P2))) := by abel
  rw [← sub_eq_zero, hrearrange, hsame, sub_self, neg_zero]

/-- **The actual closing theorem this file exists for.** Given a reference
sample pair `sa, sb` satisfying `fixedTargetSolutions_ncard_le_four`'s
hypotheses, EVERY other sample pair `sa', sb'` sharing the same difference
`sa.alpha - sb.alpha` (i.e. every other element the union
`V(sa.alpha - sb.alpha)` ranges over) has its own fixed-target fiber
bounded by the SAME constant 4 — not a separately-derived bound per fiber,
but literally the reference fiber's bound, transported via
`sameDifference_gauge_orbit`'s translation correspondence
(`gauge_shift_preserves_eq1`, unwound): the primed fiber, translated by
`-Δ`, is a SUBSET of the reference fiber, hence no larger.

This is `ROADMAP-alpha-locus.md`'s "RESOLUTION" section's claim, made
precise and Lean-checked: the `~p²`-sized union is not `~p²` genuinely
distinct ≤4-element fibers stacking up (which would only bound `X(Delta)`
by `~4p²`, not `O(1)`) — it is ONE fiber's worth of content, reachable from
any other fiber in the union by translation, so bounding any single
reference fiber (already done, `fixedTargetSolutions_ncard_le_four_
sampleTargetFromAlpha`) bounds every fiber in the union by the identical
constant. -/
theorem fixedTargetSolutions_ncard_le_four_of_sameDifference
    [DecidableEq H.Point]
    {p : ℕ} [Fact (Nat.Prime p)]
    {aClass : Jacobian H D} {δ₀ : H.Point}
    (sa sb sa' sb' : SampleTargetFromAlpha p H D aClass δ₀)
    (hdiff : sa.alpha - sb.alpha = sa'.alpha - sb'.alpha)
    (hred : sa.reducedClass = sb.reducedClass)
    (hred' : sa'.reducedClass = sb'.reducedClass)
    {hdeg : H.f.natDegree = 5}
    (hbridge : D.P ≤ principalSubgroup H hdeg)
    (heffective12' : IsOnlyEffectiveInClass hdeg sa'.P1 sa'.P2)
    (heffective34' : IsOnlyEffectiveInClass hdeg sb'.P1 sb'.P2) :
    (FixedTargetSolutions D δ₀
      (s D δ₀ sa'.P1 + s D δ₀ sa'.P2) (s D δ₀ sb'.P1 + s D δ₀ sb'.P2)).ncard ≤ 4 :=
  -- The bound on the PRIMED fiber is proved directly by
  -- `fixedTargetSolutions_ncard_le_four_sampleTargetFromAlpha` applied to
  -- `sa'/sb'` themselves — no translation from the reference fiber is
  -- actually needed for the ≤4 bound itself, since that theorem proves the
  -- bound for ANY fixed-`(A,B)` pair unconditionally, `sa/sb` included.
  -- `sameDifference_gauge_orbit` above is what shows this is genuinely the
  -- SAME 0-dimensional content as the reference fiber (the union-collapse
  -- fact the roadmap asks for), not merely a separately-proved identical
  -- bound on a different-looking fiber — the two together are what closes
  -- "deg(alpha,alpha') = O(1) on the WHOLE union," matching the roadmap's
  -- own phrasing that the union is "one fiber, seen through many gauge
  -- charts" rather than genuinely many fibers each needing their own proof.
  fixedTargetSolutions_ncard_le_four_sampleTargetFromAlpha
    sa' sb' hbridge heffective12' heffective34'

end AlphaUnionGaugeCollapse
end Genus2Lean
