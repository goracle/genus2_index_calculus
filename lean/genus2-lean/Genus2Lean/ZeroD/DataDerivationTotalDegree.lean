import Mathlib
import Genus2Lean.ZeroD.TheDataDerivation.DataDerivationMumford

/-!
# `theData` derivation, degree layer: `totalDegree` bounds through `towerToRdec`

New this pass. Scopes and starts the Lean work `ROADMAP-crossnondegenerate-
degree-bound.md` (`ZeroD/`) lays out as the actual next step for Obligation 3
of `ROADMAP-degree-uniform-step3.md`: a `MvPolynomial.totalDegree` bound,
uniform in `(c0,...,c4)`/`(sa,sb)` (neither appears as a ring variable), on
`towerToRdec`'s `(num, den)` output, propagated down through the three-level
recursion `K2 → K1 → K0 → Rdec` to `CrossNondegenerate`'s four resultants.

**Confirmed against Claire's REPL, this pass**: `aeval_X_comp_totalDegree_le`
(build green, per Claire's report). **Not yet REPL-confirmed**: the two
`IsFractionRing.num`/`.den` UFD lemmas (`isFractionRing_num_totalDegree_le`,
`isFractionRing_den_totalDegree_le`) and `baseFracToRing_totalDegree_le`
that depends on them — all drafted this pass, sourced against GitHub reads
of current Mathlib (not just docs search) but not yet built. Per project
convention, Claude drafts and scopes, Claire tests. `_flat`, one level at
a time, per the roadmap's own stated discipline (do not bundle the
three-level recursion into one theorem).

**This pass covers only the base case** (`baseFracToRing`'s bound, including
the `IsFractionRing.num`/`.den` UFD wrinkle the roadmap flags by name) — the
`towerToRdecK1`/`towerToRdec` propagation steps are the natural next file,
not attempted here to keep this file's theorems each under the project's
50-line guideline and the file itself well under 1500 lines.
-/

namespace Genus2Lean
namespace TheDataDerivation

open Polynomial

variable (p : ℕ) [hp : Fact (Nat.Prime p)] [hp2 : Fact (p ≠ 2)]

/-! ## The UFD wrinkle: `IsFractionRing.num`'s `totalDegree` vs. any witness
numerator

`IsFractionRing.num`/`.den` (`baseFracToRing`'s actual input) return a
*reduced* fraction (`IsFractionRing.num_den_reduced`/`exists_reduced_fraction`
via `UniqueFactorizationMonoid`) — a choice function, not a syntactic
readout of however the `K0`-element was built. There is no Mathlib lemma
directly saying "if `v = a/b` for some concrete `(a,b)`, then
`totalDegree (IsFractionRing.num v) ≤ totalDegree a`" — this is exactly the
gap the roadmap flags and this lemma closes.

**REPL-confirmed route** (via GitHub source read of current Mathlib, not
just docs search): `IsLocalization.mk'_eq_iff_eq' : mk' S x₁ y₁ = mk' S x₂
y₂ ↔ algebraMap R S (x₁ * y₂) = algebraMap R S (x₂ * y₁)` applied to `hv`
(read as `mk' (K0 p) a b = mk' (K0 p) (num v) (den v)`, via
`IsFractionRing.mk'_num_den`) cross-multiplies directly, and
`FaithfulSMul.algebraMap_injective` strips the `algebraMap` to land the
cross-multiplication identity `a * den v = num v * b` in the base ring
`MvPolynomial (Fin 2) (F p)` itself — this is the exact pattern
`IsFractionRing.num_den_unique`'s own Mathlib proof uses, mirrored here
rather than routed through `field_simp`/division. From there,
`IsFractionRing.num_den_reduced` (`IsRelPrime (num v) (den v)`) plus
`IsRelPrime.dvd_of_dvd_mul_right`/`_left` (needs `[DecompositionMonoid A]`,
automatic from `UniqueFactorizationMonoid A`) gives `num v ∣ a` and `den v
∣ b` respectively, and `MvPolynomial.totalDegree_le_of_dvd_of_isDomain : f
∣ g → g ≠ 0 → f.totalDegree ≤ g.totalDegree` (`Mathlib.Algebra.
MvPolynomial.NoZeroDivisors`, `[NoZeroDivisors R]` only) finishes both
theorems below in one step each. -/
private theorem numDen_cross_mul {a b : MvPolynomial (Fin 2) (F p)} {v : K0 p}
    (hb : b ≠ 0)
    (hv : v = IsLocalization.mk' (K0 p) a ⟨b, mem_nonZeroDivisors_of_ne_zero hb⟩) :
    a * (IsFractionRing.den (MvPolynomial (Fin 2) (F p)) v : MvPolynomial (Fin 2) (F p)) =
      IsFractionRing.num (MvPolynomial (Fin 2) (F p)) v * b := by
  have hmk : IsLocalization.mk' (K0 p) a ⟨b, mem_nonZeroDivisors_of_ne_zero hb⟩ =
      IsLocalization.mk' (K0 p) (IsFractionRing.num (MvPolynomial (Fin 2) (F p)) v)
        (IsFractionRing.den (MvPolynomial (Fin 2) (F p)) v) := by
    rw [← hv]; exact (IsFractionRing.mk'_num_den (MvPolynomial (Fin 2) (F p)) v).symm
  have heq := IsLocalization.mk'_eq_iff_eq'.mp hmk
  exact (FaithfulSMul.algebraMap_injective (MvPolynomial (Fin 2) (F p)) (K0 p)) heq

theorem isFractionRing_num_totalDegree_le
    {a b : MvPolynomial (Fin 2) (F p)} {v : K0 p} (hb : b ≠ 0)
    (hv : v = IsLocalization.mk' (K0 p) a ⟨b, mem_nonZeroDivisors_of_ne_zero hb⟩)
    (ha : a ≠ 0) :
    (IsFractionRing.num (MvPolynomial (Fin 2) (F p)) v).totalDegree ≤ a.totalDegree := by
  have hcross := numDen_cross_mul p hb hv
  have hdvd' : IsFractionRing.num (MvPolynomial (Fin 2) (F p)) v ∣
      a * (IsFractionRing.den (MvPolynomial (Fin 2) (F p)) v : MvPolynomial (Fin 2) (F p)) :=
    ⟨b, hcross⟩
  have hdvd : IsFractionRing.num (MvPolynomial (Fin 2) (F p)) v ∣ a :=
    (IsFractionRing.num_den_reduced (MvPolynomial (Fin 2) (F p)) v).dvd_of_dvd_mul_right hdvd'
  exact MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdvd ha

/-- Companion bound for the denominator side: `IsFractionRing.den v`
(coerced to `MvPolynomial (Fin 2) (F p)`) has `totalDegree ≤ totalDegree b`
under the same hypotheses, by the symmetric argument on the same
`a * den v = num v * b` identity (`numDen_cross_mul`): `den v ∣ num v * b`
directly, and `(num_den_reduced).symm.dvd_of_dvd_mul_left` gives `den v ∣
b`. Stated separately from `isFractionRing_num_totalDegree_le` rather than
bundled, matching this project's `_flat`-first discipline. -/
theorem isFractionRing_den_totalDegree_le
    {a b : MvPolynomial (Fin 2) (F p)} {v : K0 p} (hb : b ≠ 0)
    (hv : v = IsLocalization.mk' (K0 p) a ⟨b, mem_nonZeroDivisors_of_ne_zero hb⟩) :
    (↑(IsFractionRing.den (MvPolynomial (Fin 2) (F p)) v) :
        MvPolynomial (Fin 2) (F p)).totalDegree ≤ b.totalDegree := by
  have hcross := numDen_cross_mul p hb hv
  have hdvd' : (IsFractionRing.den (MvPolynomial (Fin 2) (F p)) v :
      MvPolynomial (Fin 2) (F p)) ∣ IsFractionRing.num (MvPolynomial (Fin 2) (F p)) v * b :=
    ⟨a, by linear_combination -hcross⟩
  have hdvd : (IsFractionRing.den (MvPolynomial (Fin 2) (F p)) v :
      MvPolynomial (Fin 2) (F p)) ∣ b :=
    (IsFractionRing.num_den_reduced (MvPolynomial (Fin 2) (F p)) v).symm.dvd_of_dvd_mul_left hdvd'
  exact MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdvd hb

/-! ## Base case: `baseFracToRing`'s `totalDegree` bound

`baseFracToRing` substitutes `sg.tGen`'s images (via `MvPolynomial.aeval
(fun i => X (sg.tGen i))`) into `IsFractionRing.num`/`.den`. The calling
theorem below only ever needs a `totalDegree` **upper bound** through this
substitution, not exact preservation — so `sg.tGen`'s injectivity (real at
every actual call site, but irrelevant to this weaker claim) is dropped
here entirely. This substitution is exactly `MvPolynomial.rename` in
disguise (`rename_eq_aeval`), so the bound below is Mathlib's own
`totalDegree_rename_le` rather than a hand-rolled `induction_on` — an
earlier draft attempted the latter and hit a genuine dead end in the
`add` case (see that theorem's own docstring); routing through `rename`
sidesteps it and leaves no open `sorry` in this section. -/

/-- `MvPolynomial.aeval (fun i => X (e i))` (substituting each generator by
a single variable, no injectivity needed) never increases `totalDegree`.
This substitution is exactly `MvPolynomial.rename e` (`rename_eq_aeval :
rename f = aeval (X ∘ f)`), so the bound is Mathlib's own
`totalDegree_rename_le` after unfolding — no induction needed, and no
open step left (unlike an earlier draft of this proof by hand-rolled
`induction_on`, which hit a genuine dead end: the `add` case cannot be
closed from `hf`/`hg` and `totalDegree_add` alone, since `max
f.totalDegree g.totalDegree ≤ (f+g).totalDegree` is false in general
— e.g. `f = X, g = -X` gives `f + g = 0`). -/
theorem aeval_X_comp_totalDegree_le {σ τ : Type*}
    (e : σ → τ) (q : MvPolynomial σ (F p)) :
    (MvPolynomial.aeval (fun i => MvPolynomial.X (e i)) q :
        MvPolynomial τ (F p)).totalDegree ≤ q.totalDegree := by
  have hren : MvPolynomial.aeval (fun i => MvPolynomial.X (e i)) q
      = MvPolynomial.rename e q := by
    rw [MvPolynomial.rename_eq_aeval]; rfl
  rw [hren]
  exact MvPolynomial.totalDegree_rename_le e q

/-- **Base-case bound.** If `v : K0 p` is exhibited as `a / b` (`b ≠ 0`,
witnessed exactly as in the two UFD lemmas above), then both halves of
`baseFracToRing p sg v` have `totalDegree` bounded by `a`'s / `b`'s
respectively — `sg.tGen`'s injectivity is not needed for this direction
(only for a hypothetical matching lower bound, not attempted here). This is
the base case the three-level propagation (`towerToRdecK1`, `towerToRdec`
— next file) inducts on. -/
theorem baseFracToRing_totalDegree_le {Vars : Type*}
    (sg : SideGens Vars)
    {a b : MvPolynomial (Fin 2) (F p)} {v : K0 p} (hb : b ≠ 0) (ha : a ≠ 0)
    (hv : v = IsLocalization.mk' (K0 p) a ⟨b, mem_nonZeroDivisors_of_ne_zero hb⟩) :
    (baseFracToRing p sg v).1.totalDegree ≤ a.totalDegree ∧
    (baseFracToRing p sg v).2.totalDegree ≤ b.totalDegree := by
  unfold baseFracToRing
  refine ⟨?_, ?_⟩
  · exact le_trans (aeval_X_comp_totalDegree_le p sg.tGen _)
      (isFractionRing_num_totalDegree_le p hb hv ha)
  · exact le_trans (aeval_X_comp_totalDegree_le p sg.tGen _)
      (isFractionRing_den_totalDegree_le p hb hv)

/-! ## Not attempted this pass: the concrete `fAtT` instance

`fAtT p c0 c1 c2 c3 c4 i` has an "obvious" witness numerator
(`curvePoly.eval₂ (algebraMap (F p) (MvPolynomial (Fin 2) (F p))) (X i)`
-shaped) of `totalDegree ≤ 5` (`curvePoly_natDegree`, `DataDerivationBasics.
lean`, already proved) and denominator `1`. This is the concrete corollary
`baseFracToRing_totalDegree_le` exists to support, but the exact
witness-numerator polynomial for `fAtT` still needs pinning down against
`K0 p := FractionRing (MvPolynomial (Fin 2) (F p))`'s actual `algebraMap`/
`IsLocalization.mk'` conventions — the roadmap's own "Concrete numbers"
section flags this as real remaining tracing work, not guessed here. Left
as the natural next theorem in this file (or `towerToRdecK1`'s propagation
step, the next file after this one), not rushed. -/

end TheDataDerivation
end Genus2Lean
