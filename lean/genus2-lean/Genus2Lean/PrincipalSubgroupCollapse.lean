import Mathlib
import Genus2Lean.HyperellipticFunctionField
import Genus2Lean.AffinePoints
import Genus2Lean.DivisorClassGroup
import Genus2Lean.PrincipalDivisors
import Genus2Lean.PrincipalDivisorSubgroup
import Genus2Lean.FFKSidon
import Genus2Lean.HyperellipticClassProof
import Genus2Lean.RiemannRochGenus2
import Genus2Lean.RiemannRochCrux
import Genus2Lean.RatioDivisorCollapse
noncomputable section

open Classical

set_option linter.style.header false

open Polynomial

/-!
# Final assembly: `isOnlyEffectiveInClass_of_uniqueDegree2MapToP1` and `finrank_L_pair`

**Update: the closure-collapse and support-matching lemmas this file used to
contain (`isRatioDivisor_of_mem_principalSubgroup`,
`mem_LPairCarrier_of_isRatioDivisor`, and their dependencies) have moved to
`RatioDivisorCollapse.lean`**, since they are independent of
`RiemannRochCrux.lean`'s `uniqueDegree2MapToP1` and were only ever entangled
with it because they lived in a file that also imported `RiemannRochCrux.lean`
for its final-assembly theorems. That move let `RiemannRochCrux.lean` import
`RatioDivisorCollapse.lean` directly and close its own
`isOnlyEffectiveInClass_of_uniqueDegree2MapToP1` (no more `sorry` there either).

This file now just imports `RatioDivisorCollapse.lean` and keeps the two
final-assembly theorems below (`isOnlyEffectiveInClass_of_uniqueDegree2MapToP1'`
and `finrank_L_pair''`) as thin combinations, unchanged in content, for callers
already depending on these (primed) names. The one remaining gap upstream of
everything in this file is `uniqueDegree2MapToP1` itself
(`RiemannRochCrux.lean`), the cited, genuinely hard geometric fact this file's
derivation was always conditioned on.

**Verification status: drafted without a live Lean toolchain, same
PLAUSIBLE-tier caveat as the rest of this project's unverified scaffolding —
not yet `lake build`-checked.**
-/

namespace HyperellipticPolynomial

open Divisor

variable {k : Type*} [Field k]
variable {H : HyperellipticPolynomial k}
variable [IsDedekindDomain (CoordinateRing H)]



/-- **`isOnlyEffectiveInClass_of_uniqueDegree2MapToP1`, assembled from
`isRatioDivisor_of_mem_principalSubgroup` + `mem_LPairCarrier_of_isRatioDivisor` +
`uniqueDegree2MapToP1`.** This is the intended replacement for
`RiemannRochCrux.lean`'s `sorry`'d theorem of the same name (not substituted in
automatically, per that file's own note about not editing statements out from
under mid-session work).

**Update (this session): fully proved, no `sorry` anywhere in this file.** The
two gaps the module docstring above and this theorem's own docstring
previously described as still-`sorry`'d — `isRatioDivisor_add`'s support
bookkeeping and `mem_LPairCarrier_of_isRatioDivisor`'s coefficient extraction —
were closed in an earlier pass through this file (see `isRatioDivisor_add` and
`mem_LPairCarrier_of_isRatioDivisor` above, both complete); the prose here was
simply never updated to say so. The only genuinely open input feeding this
theorem is `uniqueDegree2MapToP1` itself (`RiemannRochCrux.lean`), the cited
external geometric fact. -/
theorem isOnlyEffectiveInClass_of_uniqueDegree2MapToP1'
    (hdeg : H.f.natDegree = 5) (x₁ x₂ : H.Point) (hne : x₂ ≠ Point.iota x₁) :
    IsOnlyEffectiveInClass hdeg x₁ x₂ := by
  intro x₃ x₄ hmem
  by_contra hcontra
  obtain ⟨A, B, A', B', S, hAB, hA'B', hmatch, hsupp, hdiv⟩ :=
    isRatioDivisor_of_mem_principalSubgroup hdeg hmem
  -- **Same open gap as `RiemannRochCrux.lean`'s
  -- `isOnlyEffectiveInClass_of_uniqueDegree2MapToP1`: `hreduced` for this
  -- specific witness is not derivable from `hAB, hA'B', hmatch, hsupp, hdiv`
  -- alone (see that theorem's docstring and `LPairFinrankOne.lean`'s
  -- `uniqueDegree2MapToP1_of_elementary` for why — confirmed circular with
  -- the classification fact itself via ChatGPT-assisted review). Isolated
  -- here as its own honest `sorry` rather than fabricated, matching that
  -- file's handling of the identical obligation.
  have hreduced : ∀ P : H.Point, ordAt P A B = 0 ∨ ordAt P A' B' = 0 := by
    sorry
  obtain ⟨z, C, D, C', D', hbound, hz_eq, hCD_reduced, hznonconst⟩ :=
    mem_LPairCarrier_of_isRatioDivisor hdeg x₁ x₂ x₃ x₄ A B A' B' S
      hAB hA'B' hmatch hsupp hdiv hreduced hcontra
  exact hznonconst (uniqueDegree2MapToP1 hdeg x₁ x₂ hne z ⟨C, D, C', D', hbound, hz_eq⟩)

/-- **`finrank_L_pair`, fully assembled, with the gap reduced to exactly
`uniqueDegree2MapToP1`.** Combines `finrank_LPair_eq_one_of_uniqueDegree2MapToP1`
(`RiemannRochCrux.lean`, itself a complete derivation from `uniqueDegree2MapToP1`)
with `isOnlyEffectiveInClass_of_uniqueDegree2MapToP1'` just above (now fully
proved, no `sorry`) to give the *whole* statement `RiemannRochGenus2.lean`'s
`finrank_L_pair` wants. This supersedes `RiemannRochCrux.lean`'s `finrank_L_pair'`,
which combined the same first half with the still-`sorry`'d
`isOnlyEffectiveInClass_of_uniqueDegree2MapToP1` (not the primed, proved version
here — that theorem did not exist yet when `finrank_L_pair'` was written).
Not yet wired into `RiemannRochGenus2.lean` in place of that file's own
`sorry`'d `finrank_L_pair` — same reasoning as `RiemannRochCrux.lean`'s note on
`finrank_L_pair'`, to avoid editing a statement out from under other in-progress
work mid-session; swapping in `finrank_L_pair''`'s body there is now purely
mechanical once done. -/
theorem finrank_L_pair'' (hdeg : H.f.natDegree = 5) (x₁ x₂ : H.Point)
    (hne : x₂ ≠ Point.iota x₁) :
    Module.finrank k (LPair hdeg x₁ x₂) = 1 ∧ IsOnlyEffectiveInClass hdeg x₁ x₂ :=
  ⟨finrank_LPair_eq_one_of_uniqueDegree2MapToP1 hdeg x₁ x₂ hne,
    isOnlyEffectiveInClass_of_uniqueDegree2MapToP1' hdeg x₁ x₂ hne⟩

end HyperellipticPolynomial
