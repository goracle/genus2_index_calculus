import Mathlib
import Genus2Lean.ZeroD.DecoupledSystemDegreeUniformFixedTarget
import Genus2Lean.LPairFinrankOneOrdAtFracSpec
import Genus2Lean.PrincipalDivisorSubgroup
import Genus2Lean.FFKSidon
import Genus2Lean.HyperellipticClassProof

/-!
# The `≤ 4` fixed-target bound for the canonical `D`, with `hbridge` and
# `IsOnlyEffectiveInClass` discharged

`DecoupledSystemDegreeUniformFixedTarget.lean`'s
`fixedTargetSolutions_ncard_le_four_sampleTargetFromAlpha` carries two
standing hypotheses it never discharges:

* `hbridge : D.P ≤ principalSubgroup H hdeg`
* `heffective12 / heffective34 : IsOnlyEffectiveInClass hdeg _ _`

Both are dischargeable for the concrete `D := principalDivisorData H hdeg`:

* `hbridge` is `le_refl` — `principalDivisorData`'s `P` field IS
  `principalSubgroup H hdeg` by definition.
* `IsOnlyEffectiveInClass` is
  `isOnlyEffectiveInClass_of_uniqueDegree2MapToP1_general`
  (`LPairFinrankOneOrdAtFracSpec.lean`, sorry-free, general `k`), given
  `hchar : (2 : k) ≠ 0`, `hsf : Squarefree H.f`, and the pair is not an
  involution pair (`x₂ ≠ ι x₁`).

## What is left, and why it CANNOT be dropped

The residual hypotheses `hne12 : sa.P2 ≠ ι sa.P1` and
`hne34 : sb.P2 ≠ ι sb.P1` are not artifacts of the proof technique. The
`≤ 4` bound is **false** without them, and `SampleTargetFromAlpha` does
nothing to exclude the involution case (no field of that structure
constrains `P2` against `ι P1`).

Concretely, if `P2 = ι P1` then `[P1] + [P2] - 2[δ₀]` is the canonical
class `K`, and *every* fiber `{x, ι x}` lies in it (this is the content of
`IsOnlyFibersInCanonicalClass`, still open in general `k`). So
`PairFiber δ₀ K` contains one ordered pair per affine point (and hence
`FixedTargetSolutions` is at least that large), not ≤ 2.

This was tested numerically (not assumed) with genuine Cantor addition on
random squarefree quintics over `F_p`, computing the Mumford representative
of `[P] + [Q]` for every unordered pair and grouping by class
(scratch script, not part of the build):

    p = 11 : #pts = 7,   involution-class fiber = 4  (unordered pairs)
    p = 13 : #pts = 10,  involution-class fiber = 6
    p = 101: #pts = 117, involution-class fiber = 59

while every NON-involution class had exactly one unordered pair
(0 counterexamples to the Sidon dichotomy across all three primes). So the
fiber over `K` grows linearly in `p`; the `p`-independent constant `4` only
holds away from involution pairs.

Consequence for the project: whichever code SAMPLES `(P1,P2)` must reject
`P2 = ι P1`, or the `p`-independent bound must be stated with that case
carved out and handled separately (its probability is `O(1/p)` per sample,
so it is negligible for the complexity count but it is NOT excluded by any
hypothesis currently on file).

## Verification status

Drafted without a Lean toolchain, per this project's working agreement —
NOT `lake build`-checked. Every lemma name below was checked against the
uploaded source by `grep` (see the inline notes), not recalled from memory.
The two spots most likely to need a REPL round-trip are flagged
`-- CHECK:` inline.
-/

open HyperellipticPolynomial
open Divisor
open Genus2Lean.MatchingSolutionSwapSymmetry

namespace Genus2Lean
namespace DecoupledSystem

variable {k : Type*} [Field k] {H : HyperellipticPolynomial k}
variable [IsDedekindDomain (CoordinateRing H)]

/-- **`hbridge`, discharged for the canonical `D`.** `principalDivisorData`'s
`P` field is `principalSubgroup H hdeg` by definition, so the containment is
reflexivity. Stated as its own lemma so callers don't re-derive it. -/
theorem principalDivisorData_P_le_principalSubgroup
    (hdeg : H.f.natDegree = 5) :
    (principalDivisorData H hdeg).P ≤ principalSubgroup H hdeg :=
  le_refl _

/-- **The `≤ 4` bound for the canonical `D`, `hbridge` and
`IsOnlyEffectiveInClass` both discharged.**

Residual hypotheses, all genuinely needed (see module docstring):

* `hchar`, `hsf` — standing curve hypotheses (`char ≠ 2`, `f` squarefree),
  exactly what `isOnlyEffectiveInClass_of_uniqueDegree2MapToP1_general`
  takes.
* `hne12`, `hne34` — the two sampled pairs are not involution pairs. The
  bound is FALSE without these (canonical-class fiber has size `~p`).

The conclusion is stated for `principalDivisorData H hdeg` directly, so
there is no `D`-genericity and no `hbridge` argument. -/
theorem fixedTargetSolutions_ncard_le_four_canonical
    [DecidableEq H.Point]
    {p : ℕ} [Fact (Nat.Prime p)]
    (hdeg : H.f.natDegree = 5) (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    {aClass : Jacobian H (principalDivisorData H hdeg)} {δ₀ : H.Point}
    (sa sb : SampleTargetFromAlpha p H (principalDivisorData H hdeg) aClass δ₀)
    (hne12 : sa.P2 ≠ Point.iota sa.P1)
    (hne34 : sb.P2 ≠ Point.iota sb.P1) :
    (FixedTargetSolutions (principalDivisorData H hdeg) δ₀
      (s (principalDivisorData H hdeg) δ₀ sa.P1 +
        s (principalDivisorData H hdeg) δ₀ sa.P2)
      (s (principalDivisorData H hdeg) δ₀ sb.P1 +
        s (principalDivisorData H hdeg) δ₀ sb.P2)).ncard ≤ 4 :=
  fixedTargetSolutions_ncard_le_four_sampleTargetFromAlpha sa sb
    (hdeg := hdeg)
    (principalDivisorData_P_le_principalSubgroup hdeg)
    (isOnlyEffectiveInClass_of_uniqueDegree2MapToP1_general hdeg hchar hsf
      sa.P1 sa.P2 hne12)
    (isOnlyEffectiveInClass_of_uniqueDegree2MapToP1_general hdeg hchar hsf
      sb.P1 sb.P2 hne34)



/-! ## `hne12`/`hne34` are NECESSARY, not a proof artifact

Given `D.HyperellipticClass` (every fiber `(x)+(ιx)` is linearly equivalent
to every other), the pair-fiber over the involution class contains
`(x, ι x)` for EVERY point `x`. So it is at least as large as the set of
points, and no `p`-independent constant bounds it.

Both statements below are pure composition of already-proved lemmas
(`sum_eq_of_involution_swap`, `Set.ncard_image_of_injective`,
`Set.ncard_le_ncard`), following `StabOfSmallSetTrivial.lean`'s own
cardinality pattern verbatim. `HyperellipticClass` for the canonical `D` is
`hyperellipticClass_principalDivisorData` (`HyperellipticClassProof.lean`),
which carries its own `hspec`/`Module.Finite` hypotheses; they are threaded
through here as the single hypothesis `hD : D.HyperellipticClass` rather
than re-stated, so this section is independent of how that is discharged. -/

/-- Every fiber `(x, ι x)` lies in `PairFiber δ₀ K`, where `K := s x₀ + s (ι x₀)`
is the (class of the) fiber of ANY fixed base point `x₀`. -/
theorem mem_pairFiber_involution
    (D : PrincipalDivisorData H) (hD : D.HyperellipticClass)
    (δ₀ x₀ x : H.Point) :
    (x, Point.iota x) ∈
      PairFiber D δ₀ (s D δ₀ x₀ + s D δ₀ (Point.iota x₀)) := by
  -- `PairFiber D δ₀ A = {q | s q.1 + s q.2 = A}`, so membership unfolds to the
  -- statement `s x + s (ι x) = s x₀ + s (ι x₀)`, which is the symmetric form of
  -- `sum_eq_of_involution_swap`.
  show s D δ₀ x + s D δ₀ (Point.iota x) = s D δ₀ x₀ + s D δ₀ (Point.iota x₀)
  exact sum_eq_of_involution_swap D hD δ₀

/-- **For any set `T` of points, the involution-class pair-fiber has at least
`T.ncard` elements, provided that fiber is finite.** `x ↦ (x, ι x)` is
injective (first coordinate) and maps `T` into the fiber by
`mem_pairFiber_involution`, so `T.ncard ≤ fiber.ncard`.

Reading this as "no constant bounds the fiber": for `k = ZMod p` the fiber is
finite (`H.Point` is), so taking `T` to be all of `H.Point` gives fiber size
`≥ #H.Point`, which grows with `p` — contradicting any `p`-independent bound
such as `2` or `4`. The `hfin` hypothesis is genuinely needed: `Set.ncard` of
an infinite set is `0` in Lean, so without it the inequality would be false
for nonempty `T`. -/
theorem le_ncard_pairFiber_involution
    (D : PrincipalDivisorData H) (hD : D.HyperellipticClass)
    (δ₀ x₀ : H.Point) (T : Set H.Point)
    (hfin : (PairFiber D δ₀ (s D δ₀ x₀ + s D δ₀ (Point.iota x₀))).Finite) :
    T.ncard ≤ (PairFiber D δ₀ (s D δ₀ x₀ + s D δ₀ (Point.iota x₀))).ncard := by
  have hinj : Function.Injective (fun x : H.Point => (x, Point.iota x)) := by
    intro a b h
    -- `h : (a, ι a) = (b, ι b)` (after beta); `Prod.mk.injEq` (in-project
    -- precedent: `SidonEnergy.lean`, `TowerToRdecRenameSymmetry.lean`) splits it.
    simp only [Prod.mk.injEq] at h
    exact h.1
  have hsub : (fun x : H.Point => (x, Point.iota x)) '' T ⊆
      PairFiber D δ₀ (s D δ₀ x₀ + s D δ₀ (Point.iota x₀)) := by
    rintro _ ⟨x, -, rfl⟩
    exact mem_pairFiber_involution D hD δ₀ x₀ x
  calc T.ncard
      = ((fun x : H.Point => (x, Point.iota x)) '' T).ncard :=
        (Set.ncard_image_of_injective T hinj).symm
    _ ≤ _ := Set.ncard_le_ncard hsub hfin

end DecoupledSystem
end Genus2Lean
