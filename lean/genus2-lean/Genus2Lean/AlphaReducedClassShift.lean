import Mathlib
import Genus2Lean.DivisorClassGroup
import Genus2Lean.ZeroD.AlphaLocusDegreeUniform

/-!
# Shifting `alpha` before calling `Reduce` — the pure-algebra transport step

**Companion to `ROADMAP-alpha-locus.md`'s gauge-shift argument.** That
roadmap's step 2 (in its "RESOLVED" block) originally tried to derive the
shifted reduced-target class from a single call to `Reduce`, via an
assumed "shift-equivariance" law on `Reduce` itself
(`Reduce(x - c·a) = Reduce(x) - Delta(c)`). That framing was wrong and has
been corrected in the roadmap: `Reduce` isn't assembled as a callable
function anywhere in this project yet (see `Reduce/AlphaReduce.lean`'s
own "not yet built" note), so no equivariance law about it can even be
stated, let alone checked.

**The actual right order: shift `alpha` FIRST, at the `reducedClass`
level — which is plain `AddCommGroup`/`zsmul` algebra, not a `Reduce`
output — and only THEN invoke `Reduce`/`isReduction` fresh on the
already-shifted class**, exactly as if it were a brand-new independent
`SampleTargetFromAlpha` instance. This file proves that algebra step,
`sorry`-free, with no dependence on `Reduce`, `isReduction`, or any other
standing hypothesis this project carries. It is deliberately the
*minimal* honest piece: it does NOT assert that a
`SampleTargetFromAlpha` instance at `alpha+c` satisfying `isReduction`
actually exists — that remains a genuine per-`c` hypothesis (see the
roadmap's "Consequence for what's actually provable right now" note)
until `Reduce` is assembled as a callable and `isReduction` is upgraded
from an assumed field to a proved one.
-/

namespace Genus2Lean
namespace DecoupledSystem

open HyperellipticPolynomial
open HyperellipticPolynomial.Divisor
open Polynomial

variable {k : Type*} [Field k] {H : HyperellipticPolynomial k}
variable {D : PrincipalDivisorData H}

/-- **The reduced-target class, as a bare function of `alpha` with
everything else fixed** — the same formula `SampleTargetFromAlpha`'s
`reducedClass` field uses by default, extracted here so it can be
reasoned about independently of any particular structure instance
(instances are free to override the field, but the SHIFT argument only
ever needs this formula, not the structure). -/
noncomputable def reducedClassOfAlpha {p : ℕ} [Fact (Nat.Prime p)]
    (aClass : Jacobian H D) (δ₀ P1 P2 : H.Point) (alpha : ℤ) :
    Jacobian H D :=
  alpha • aClass -
    toJacobian D ⟨single P1 + single P2 - (2 : ℤ) • single δ₀,
      by
        have h1 := single_sub_single_mem_Divisor0 P1 δ₀
        have h2 := single_sub_single_mem_Divisor0 P2 δ₀
        have : single P1 + single P2 - (2 : ℤ) • single δ₀ =
            (single P1 - single δ₀) + (single P2 - single δ₀) := by
          rw [two_zsmul]; abel
        rw [this]
        exact add_mem h1 h2⟩

/-- **`SampleTargetFromAlpha.reducedClass` unfolds to
`reducedClassOfAlpha`, GIVEN that this instance uses the field's
default value.** `reducedClass` is a structure field with a *default*
(`:=`), not a derived/computed projection — a caller building a
`SampleTargetFromAlpha` is free to supply their own value for it
instead, so this equation is a genuine hypothesis (`hdefault` below),
not a `rfl`. Every instance actually constructed via the default (which
is every instance this project's roadmap discusses so far — nobody has
had a reason to override it) satisfies `hdefault` trivially by
`rfl`/`sa.reducedClass = sa.reducedClass` at the construction site, but
that has to be checked once per instance, not assumed globally here. -/
theorem sampleTargetFromAlpha_reducedClass_eq_reducedClassOfAlpha
    {p : ℕ} [Fact (Nat.Prime p)] {aClass : Jacobian H D} {δ₀ : H.Point}
    (sa : SampleTargetFromAlpha p H D aClass δ₀)
    (hdefault : sa.reducedClass =
      sa.alpha • aClass -
        toJacobian D ⟨single sa.P1 + single sa.P2 - (2 : ℤ) • single δ₀,
          by
            have h1 := single_sub_single_mem_Divisor0 sa.P1 δ₀
            have h2 := single_sub_single_mem_Divisor0 sa.P2 δ₀
            have heq : single sa.P1 + single sa.P2 - (2 : ℤ) • single δ₀ =
                (single sa.P1 - single δ₀) + (single sa.P2 - single δ₀) := by
              rw [two_zsmul]; abel
            rw [heq]
            exact add_mem h1 h2⟩) :
    sa.reducedClass = reducedClassOfAlpha (p := p) aClass δ₀ sa.P1 sa.P2 sa.alpha :=
  hdefault

/-- **The transport step, pure algebra.** Shifting `alpha` by `c` shifts
`reducedClassOfAlpha` by exactly `c • aClass` — the `toJacobian D (...)`
term is identical on both sides (it doesn't mention `alpha` at all), so
this reduces to `(alpha+c)•aClass = alpha•aClass + c•aClass`
(`add_zsmul`) followed by regrouping. No `Reduce`, no `isReduction`, no
standing hypothesis beyond what's already baked into
`reducedClassOfAlpha`'s own well-definedness. -/
theorem reducedClassOfAlpha_add {p : ℕ} [Fact (Nat.Prime p)]
    (aClass : Jacobian H D) (δ₀ P1 P2 : H.Point) (alpha c : ℤ) :
    reducedClassOfAlpha (p := p) aClass δ₀ P1 P2 (alpha + c) =
      reducedClassOfAlpha (p := p) aClass δ₀ P1 P2 alpha + c • aClass := by
  unfold reducedClassOfAlpha
  rw [add_zsmul]
  abel

/-- **Corollary, stated directly against a `SampleTargetFromAlpha`
instance's own `reducedClass` field** (via the unfolding lemma above) —
the shape actually usable at a roadmap call site: given `sa` at `alpha`,
the class a fresh instance at `alpha+c` (same `aClass, δ₀, P1, P2`)
*would* need its `reducedClass` field to equal, is pinned down exactly,
before any `isReduction` witness for that fresh instance is assumed. -/
theorem sampleTargetFromAlpha_reducedClass_shift
    {p : ℕ} [Fact (Nat.Prime p)] {aClass : Jacobian H D} {δ₀ : H.Point}
    (sa : SampleTargetFromAlpha p H D aClass δ₀)
    (hdefault : sa.reducedClass =
      sa.alpha • aClass -
        toJacobian D ⟨single sa.P1 + single sa.P2 - (2 : ℤ) • single δ₀,
          by
            have h1 := single_sub_single_mem_Divisor0 sa.P1 δ₀
            have h2 := single_sub_single_mem_Divisor0 sa.P2 δ₀
            have heq : single sa.P1 + single sa.P2 - (2 : ℤ) • single δ₀ =
                (single sa.P1 - single δ₀) + (single sa.P2 - single δ₀) := by
              rw [two_zsmul]; abel
            rw [heq]
            exact add_mem h1 h2⟩)
    (c : ℤ) :
    reducedClassOfAlpha (p := p) aClass δ₀ sa.P1 sa.P2 (sa.alpha + c) =
      sa.reducedClass + c • aClass := by
  rw [sampleTargetFromAlpha_reducedClass_eq_reducedClassOfAlpha sa hdefault,
    reducedClassOfAlpha_add]

end DecoupledSystem
end Genus2Lean
