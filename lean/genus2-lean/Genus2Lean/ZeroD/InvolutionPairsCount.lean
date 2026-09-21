import Mathlib
import Genus2Lean.AffinePoints

/-!
# How many ordered pairs are involution pairs? Exactly `|H.Point|` of `|H.Point|²`

`FixedTargetBoundCanonical.lean` shows the `≤ 4` fixed-target bound needs
`P2 ≠ ι P1` and is FALSE without it (the involution class has a fiber of size
`~ #points`). Any sampler must therefore reject involution pairs. This file
makes the cost of that rejection exact rather than asserted:

    #{(P1,P2) : P2 = ι P1} * #H.Point = #(H.Point × H.Point)

i.e. a uniformly random ordered pair is an involution pair with probability
exactly `1 / #H.Point`, which is `~ 1/p` because `#H.Point ~ p`. Rejecting them
therefore changes the distribution of accepted samples only by a factor
`1 - 1/#H.Point` per draw.

**Not proved here:** that `#H.Point ~ p` (Hasse–Weil; not available). The
statement below is exact in `#H.Point` and says nothing about its size.

Generic in the `Fintype H.Point` / `DecidableEq H.Point` instances (no import of
`SidonBridge.lean`), so it composes with whichever instance is in scope.

Drafted without a Lean toolchain, per the working agreement; the only
Mathlib lemma names used (`Finset.card_image_of_injective`, `Finset.card_univ`,
`Fintype.card_prod`, `Finset.mem_filter`, `Finset.mem_image`) were checked
against docs or existing in-project use.
-/

open HyperellipticPolynomial

namespace Genus2Lean
namespace InvolutionPairs

variable {k : Type*} [Field k] {H : HyperellipticPolynomial k}
variable [Fintype H.Point] [DecidableEq H.Point]

/-- The involution pairs are exactly the image of `x ↦ (x, ι x)`. -/
theorem involutionPairs_eq_image :
    (Finset.univ.filter (fun q : H.Point × H.Point => q.2 = Point.iota q.1)) =
      Finset.univ.image (fun x : H.Point => (x, Point.iota x)) := by
  ext ⟨a, b⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
    Prod.mk.injEq]
  constructor
  · intro h
    exact ⟨a, rfl, h.symm⟩
  · rintro ⟨x, rfl, h⟩
    exact h.symm

/-- There are exactly `#H.Point` involution pairs: one per point. -/
theorem card_involutionPairs :
    (Finset.univ.filter (fun q : H.Point × H.Point => q.2 = Point.iota q.1)).card =
      Fintype.card H.Point := by
  rw [involutionPairs_eq_image]
  have hinj : Function.Injective (fun x : H.Point => (x, Point.iota x)) := by
    intro a b h
    simp only [Prod.mk.injEq] at h
    exact h.1
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]

/-- **Exact density.** `#(involution pairs) · #H.Point = #(all ordered pairs)`,
i.e. the involution pairs have density exactly `1 / #H.Point`. -/
theorem card_involutionPairs_mul_card :
    (Finset.univ.filter (fun q : H.Point × H.Point => q.2 = Point.iota q.1)).card *
        Fintype.card H.Point = Fintype.card (H.Point × H.Point) := by
  rw [card_involutionPairs, Fintype.card_prod]

end InvolutionPairs
end Genus2Lean
