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

**Not run against Claire's REPL yet.** Per project convention, Claude drafts
and scopes, Claire tests. Every Mathlib lemma name below needs REPL
confirmation before trusting the proof compiles — see the per-lemma notes.
`_flat`, one level at a time, per the roadmap's own stated discipline (do not
bundle the three-level recursion into one theorem).

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

If `v : K0 p` is exhibited as `a / b` for `b ≠ 0`, then `IsFractionRing.
num` of `v` has `totalDegree` bounded by `a`'s. Proof route (per the
roadmap): from `IsFractionRing.mk'_num_den'`-style identities, `num v`
divides `a * den v`; reducedness (`num v` coprime to `den v`) plus `num v`
a nonzero divisor in the UFD `MvPolynomial (Fin 2) (F p)` then forces `num v
∣ a` outright (`IsRelPrime.dvd_of_dvd_mul_right`), and a nonzero divisor's
`totalDegree` is `≤` the dividend's whenever the dividend is nonzero
(`MvPolynomial.totalDegree_mul` on the witness `a = num v * k`, `k ≠ 0`
forced since `a ≠ 0`, `totalDegree k ≥ 0` making `totalDegree (num v) ≤
totalDegree a` immediate — no reverse-triangle-inequality lemma needed
beyond `totalDegree_mul`'s equality form for a domain). **Names not yet
REPL-confirmed**: `IsFractionRing.mk'_num_den'`, `IsRelPrime.dvd_of_dvd_
mul_right`, and whether `MvPolynomial.totalDegree_mul` is stated as an
equality (needs `IsDomain`, which `MvPolynomial (Fin 2) (F p)` has since
`F p` is a field) or only as `totalDegree_mul_le`. If only the `≤` form
exists for a domain too, swap the last step for the `≤` version applied to
`num v * k = a` directly (still gives `totalDegree (num v) ≤ totalDegree a`
via `omega` against `totalDegree_mul_le : (num v * k).totalDegree ≤
totalDegree (num v) + totalDegree k`, which is a strictly weaker fact than
needed here in the wrong direction — flagged for Claire's REPL check
first, this may need the `IsDomain` equality form specifically, not just
`_le`). -/
theorem isFractionRing_num_totalDegree_le
    {a b : MvPolynomial (Fin 2) (F p)} {v : K0 p} (hb : b ≠ 0)
    (hv : v = IsLocalization.mk' (K0 p) a ⟨b, mem_nonZeroDivisors_of_ne_zero hb⟩)
    (ha : a ≠ 0) :
    (IsFractionRing.num (MvPolynomial (Fin 2) (F p)) v).totalDegree ≤ a.totalDegree := by
  sorry

/-- Companion bound for the denominator side: `IsFractionRing.den v`
(coerced to `MvPolynomial (Fin 2) (F p)`) has `totalDegree ≤ totalDegree b`
under the same hypotheses, by the symmetric argument (`den v ∣ b` via the
same coprimality/UFD route, using `num v * b = a * den v`
(`IsFractionRing.mk'_num_den'` again) the other way). Stated separately
from `isFractionRing_num_totalDegree_le` rather than bundled, matching this
project's `_flat`-first discipline — a future pass can combine them into
one corollary once both are REPL-confirmed. -/
theorem isFractionRing_den_totalDegree_le
    {a b : MvPolynomial (Fin 2) (F p)} {v : K0 p} (hb : b ≠ 0)
    (hv : v = IsLocalization.mk' (K0 p) a ⟨b, mem_nonZeroDivisors_of_ne_zero hb⟩) :
    (↑(IsFractionRing.den (MvPolynomial (Fin 2) (F p)) v) :
        MvPolynomial (Fin 2) (F p)).totalDegree ≤ b.totalDegree := by
  sorry

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
