import Mathlib
import Genus2Lean.ZeroD.AlphaLocusDegreeUniform
import Genus2Lean.ZeroD.MatchingSolutionSwapSymmetry
import Genus2Lean.ZeroD.StabOfSmallSetTrivial

/-!
# `SampleTargetFromAlpha.memZmultiplesA`: the subgroup-closure consequence,
# and precisely what it does and does not yet connect to

`AlphaLocusDegreeUniform.lean`'s `SampleTargetFromAlpha` now carries
`memZmultiplesA`, the standing hypothesis (per `ROADMAP-alpha-locus.md`'s
`Stab(S)` argument) that a sample's pair-sum class `s D δ₀ P1 + s D δ₀ P2`
lies in `⟨aClass⟩`. This file proves the one honest, unconditional
consequence of that field — roadmap step 3, subgroup closure — and then
states precisely, rather than glossing over, why the further composition
with `StabOfSmallSetTrivial.delta_eq_zero_of_stabilizes_small_set` is
NOT a one-line corollary the way `ROADMAP-alpha-locus.md`'s step 4-6
sketch might suggest.

## Step 3 (roadmap): subgroup closure gives `Δ ∈ ⟨aClass⟩` for free

This part composes cleanly and is proved below
(`sub_mem_zmultiples_of_mem_mem`): if two pair-sums both lie in
`⟨aClass⟩`, their difference does too, by nothing more than
`AddSubgroup`'s closure under subtraction. No curve-specific content,
matches the roadmap's own framing exactly ("no new geometric content
needed here beyond step-2's algebra plus the standing hypothesis").

## Why steps 4-6 do NOT immediately follow by feeding this `Δ` into
## `delta_eq_zero_of_stabilizes_small_set`

`delta_eq_zero_of_stabilizes_small_set` needs `hstab : ∀ x ∈ S, x + Δ ∈
S` for `S : Set G` and `Δ : G`, i.e. a set of `Jacobian H D`-VALUED
elements genuinely closed under `+ Δ`. But
`MatchingSolutionSwapSymmetry.FixedTargetSolutions D δ₀ A B` — the ≤4-
bounded set `fixedTargetSolutions_ncard_le_four` actually controls — is
a set of `H.Point`-QUADRUPLES with both pair-sums PINNED to the fixed
constants `A`/`B`. Mapping it into `Jacobian H D` via its own pair-sum
(`x ↦ s D δ₀ x.1 + s D δ₀ x.2.1`) sends every element to the single
point `A` — a singleton image, not a set with room for `Δ`-translation
to act nontrivially on. This is not a Lean-engineering gap to route
around; it is because `FixedTargetSolutions` was corrected (see
`MatchingSolutionSwapSymmetry.lean`'s own module docstring) to fix BOTH
pair-sums independently, precisely so `IsOnlyEffectiveInClass` could
bound it — the same move that makes the ≤4 bound provable also makes
the pair-sum constant across `S`, so `Δ` (as roadmap step 2 defines it,
between two DIFFERENT solutions' `(P1,P2)`-pair-sums) is forced to be
`0` on `FixedTargetSolutions` only in the degenerate sense that there is
only ever one pair-sum value to begin with — not via the `Stab(S)`
orbit-counting mechanism `StabOfSmallSetTrivial.lean` formalizes.

**What this means for the roadmap**: the `Stab(S)` argument's `S` (roadmap
step 1: "the ... solution set of the matching equation ... for this
fixed `(alpha,alpha')`") and `MatchingSolutionSwapSymmetry`'s corrected
`FixedTargetSolutions` are not literally the same object — the roadmap's
`S` was scoped against the PRE-correction (difference-only) solution set,
where the pair-sum genuinely varies over solutions and `Stab(S)`-style
orbit-counting is the right tool. Reconciling the two — either by
restating `Stab(S)`'s argument against `FixedTargetSolutions` directly
(likely trivial once done honestly, since `FixedTargetSolutions`'s ≤4
bound may make singleton-ness provable by finite case-analysis on
`swapImages` instead of the group-theoretic route at all) or by
identifying a genuinely-varying carrier set the `Stab(S)` mechanism does
apply to — is NOT attempted in this file and is flagged here as the
actual remaining content, rather than forced through with a mismatched
or vacuous `hstab`. -/

open HyperellipticPolynomial
open Divisor

namespace Genus2Lean
namespace DecoupledSystem

variable {k : Type*} [Field k] {H : HyperellipticPolynomial k}
variable {D : PrincipalDivisorData H}

/-! ## Step 3 of the roadmap: two samples' `memZmultiplesA` combine, by
subgroup closure, into `Δ ∈ ⟨aClass⟩` for their pair-sum difference -/

/-- **`Δ ∈ ⟨aClass⟩` for free**, given both endpoints of the difference
individually lie in `⟨aClass⟩` — `AddSubgroup.zmultiples aClass` is
closed under subtraction, so this is pure subgroup algebra, exactly
matching `ROADMAP-alpha-locus.md` step 3 ("`Δ` is *defined* as a
difference of two elements already assumed to lie in the subgroup
`⟨a⟩`, hence itself in `⟨a⟩` by subgroup closure"). Stated generically
over the two raw classes (not tied to `SampleTargetFromAlpha` directly)
so it applies to either the `(P1,P2)`-side pair or the `(P3,P4)`-side
pair without duplication. -/
theorem sub_mem_zmultiples_of_mem_mem
    {aClass A A' : Jacobian H D}
    (hmemA : A ∈ AddSubgroup.zmultiples aClass)
    (hmemA' : A' ∈ AddSubgroup.zmultiples aClass) :
    A' - A ∈ AddSubgroup.zmultiples aClass :=
  sub_mem hmemA' hmemA

/-- **Instantiated against two `SampleTargetFromAlpha` samples sharing
`aClass`/`δ₀`.** `sa`'s and `sb`'s own `memZmultiplesA` fields feed
`sub_mem_zmultiples_of_mem_mem` directly — this is genuinely the
strongest true statement obtainable from `memZmultiplesA` alone,
matching the roadmap's step 3 exactly: `sb`'s pair-sum class MINUS
`sa`'s pair-sum class lies in `⟨aClass⟩`, unconditionally, no further
hypotheses beyond both samples' own standing `⟨aClass⟩`-membership. -/
theorem sampleTargetFromAlpha_pairSum_sub_mem_zmultiplesA
    {p : ℕ} [Fact (Nat.Prime p)] {aClass : Jacobian H D} {δ₀ : H.Point}
    (sa sb : SampleTargetFromAlpha p H D aClass δ₀) :
    (s D δ₀ sb.P1 + s D δ₀ sb.P2) - (s D δ₀ sa.P1 + s D δ₀ sa.P2) ∈
      AddSubgroup.zmultiples aClass :=
  sub_mem_zmultiples_of_mem_mem (aClass := aClass) sa.memZmultiplesA sb.memZmultiplesA

end DecoupledSystem
end Genus2Lean
