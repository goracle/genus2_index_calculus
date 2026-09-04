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

**Confirmed against Claire's REPL**: `aeval_X_comp_totalDegree_le`, the
`IsFractionRing.num`/`.den` UFD lemmas (`isFractionRing_num_totalDegree_le`,
`isFractionRing_den_totalDegree_le`), `baseFracToRing_totalDegree_le`,
`combine_totalDegree_le`, `towerToRdecK1_totalDegree_le`, and
`towerToRdec_totalDegree_le` (build green, per Claire's reports). **Not
yet REPL-confirmed**: `towerToRdec_coeff_totalDegree_le`, new this pass —
a pure substitution corollary (`v := poly.coeff i.val`), low risk.

**This pass adds the `coeffsToNumDen`-shaped corollary**
(`towerToRdec_coeff_totalDegree_le`), completing the roadmap's step 4/5
bridge: `DecoupledSystemRegular.lean`'s `coeffsToNumDen`/`theData` (its
eight `u1_num`/`u1_den`/etc. fields) are literally `towerToRdec p sg
(poly.coeff i.val)` for `poly ∈ {uRS, vRS}` — this theorem bounds exactly
that shape, so `DecoupledSystemRegular.lean` can now state each of
`theData`'s eight fields' degree bounds by one application, once it
imports this file. The base-case-forward degree bound (steps 1-4 of the
roadmap) is now complete end to end, `K0 → K1 → K2` (base case through
`towerToRdec`); still open, per the roadmap's own step 2/6: tracing the
*concrete* `D` value reaching `baseFracToRing` from `uRS`/`vRS` (the
`fAtT` witness note below), and deriving `CrossNondegenerate`'s resultant
bound as one further `totalDegree_mul`/`_add` step in
`DecoupledSystemRegular.lean` itself (roadmap step 5, the actual
resultant, not yet attempted — needs the new import and that file's own
`Idx`/`Rdec`/`hu0`/etc. names in scope, out of place here).
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

/-! ## Level 1: `towerToRdecK1`'s `totalDegree` bound

Per the roadmap's own "fixed, finite sequence of algebraic operations"
framing: `towerToRdecK1` combines two `baseFracToRing` outputs `(n0,den0),
(n1,den1)` via `num := n0*den1 + n1*den0*X(wGen 0)`, `den := den0*den1` —
exactly two multiplications and one addition, mechanical
`totalDegree_mul`/`totalDegree_add`-style triangle inequalities. Split
into a generic combinator lemma first (`combine_totalDegree_le`, no
mention of `towerToRdecK1`/`baseFracToRing` at all — pure algebra on four
polynomials and a bound `D`), then specialized to `towerToRdecK1` itself,
matching this project's `_flat`-first discipline: the combinator is
reusable verbatim for `towerToRdec` (`towerToRdecK1`'s own combination
step, one level up) in the next file. -/

variable (c0 c1 c2 c3 c4 : F p)

/-- **The combinator step**, abstracted away from `towerToRdecK1`/
`towerToRdec` specifics: given `n0,den0,n1,den1` all `totalDegree ≤ D`,
`n0*den1 + n1*den0*X w` has `totalDegree ≤ 2*D+1` and `den0*den1` has
`totalDegree ≤ 2*D`. The `+1` is `X w`'s own `totalDegree = 1`
(`totalDegree_X`); everything else is `totalDegree_mul`/`totalDegree_add`'s
`≤`-triangle inequalities chained via `omega`. -/
theorem combine_totalDegree_le {Vars : Type*} {D : ℕ}
    {n0 den0 n1 den1 : MvPolynomial Vars (F p)} (w : Vars)
    (hn0 : n0.totalDegree ≤ D) (hden0 : den0.totalDegree ≤ D)
    (hn1 : n1.totalDegree ≤ D) (hden1 : den1.totalDegree ≤ D) :
    (n0 * den1 + n1 * den0 * MvPolynomial.X w).totalDegree ≤ 2 * D + 1 ∧
    (den0 * den1).totalDegree ≤ 2 * D := by
  have hw : (MvPolynomial.X w : MvPolynomial Vars (F p)).totalDegree = 1 :=
    MvPolynomial.totalDegree_X w
  have h1 : (n0 * den1).totalDegree ≤ D + D :=
    le_trans (MvPolynomial.totalDegree_mul n0 den1) (by omega)
  have h2 : (n1 * den0 * MvPolynomial.X w).totalDegree ≤ D + D + 1 := by
    have hnd : (n1 * den0).totalDegree ≤ D + D :=
      le_trans (MvPolynomial.totalDegree_mul n1 den0) (by omega)
    have hstep : (n1 * den0 * MvPolynomial.X w).totalDegree ≤ (D + D) + 1 :=
      le_trans (MvPolynomial.totalDegree_mul (n1 * den0) (MvPolynomial.X w))
        (add_le_add hnd (le_of_eq hw))
    omega
  have hsum : (n0 * den1 + n1 * den0 * MvPolynomial.X w).totalDegree ≤ 2 * D + 1 :=
    le_trans (MvPolynomial.totalDegree_add (n0 * den1) (n1 * den0 * MvPolynomial.X w))
      (max_le (by omega) (by omega))
  have hprod : (den0 * den1).totalDegree ≤ 2 * D :=
    le_trans (MvPolynomial.totalDegree_mul den0 den1) (by omega)
  exact ⟨hsum, hprod⟩

/-- **`towerToRdecK1`'s bound.** If `baseFracToRing p sg` applied to `v`'s
two extracted `K0`-coefficients (`valPoly.coeff 0`, `valPoly.coeff 1`,
exactly as `towerToRdecK1`'s own definition computes them via
`AdjoinRoot.modByMonicHom`) both land inside `totalDegree ≤ D` (in both
coordinates — exactly the shape `baseFracToRing_totalDegree_le` produces,
with `D := max a.totalDegree b.totalDegree` if the two source witnesses
differ), then `towerToRdecK1 p sg v`'s output is `totalDegree ≤ 2*D+1` /
`≤ 2*D`. Stated with the coefficient-extraction spelled out explicitly in
the hypothesis (matching `towerToRdecK1`'s own `let`-chain verbatim,
rather than introducing a separate name for it) so `unfold` on the goal
lines up syntactically with the hypothesis without an extra bridging
lemma. -/
theorem towerToRdecK1_totalDegree_le {Vars : Type*}
    (sg : SideGens Vars) {D : ℕ} (v : K1 p c0 c1 c2 c3 c4)
    (h : (baseFracToRing p sg
            ((AdjoinRoot.modByMonicHom (K1_poly_monic p c0 c1 c2 c3 c4) v :
              Polynomial (K0 p)).coeff 0)).1.totalDegree ≤ D ∧
      (baseFracToRing p sg
            ((AdjoinRoot.modByMonicHom (K1_poly_monic p c0 c1 c2 c3 c4) v :
              Polynomial (K0 p)).coeff 0)).2.totalDegree ≤ D ∧
      (baseFracToRing p sg
            ((AdjoinRoot.modByMonicHom (K1_poly_monic p c0 c1 c2 c3 c4) v :
              Polynomial (K0 p)).coeff 1)).1.totalDegree ≤ D ∧
      (baseFracToRing p sg
            ((AdjoinRoot.modByMonicHom (K1_poly_monic p c0 c1 c2 c3 c4) v :
              Polynomial (K0 p)).coeff 1)).2.totalDegree ≤ D) :
    (towerToRdecK1 p sg v).1.totalDegree ≤ 2 * D + 1 ∧
    (towerToRdecK1 p sg v).2.totalDegree ≤ 2 * D := by
  unfold towerToRdecK1
  obtain ⟨h00, h01, h10, h11⟩ := h
  exact combine_totalDegree_le p (sg.wGen 0) h00 h01 h10 h11

/-! ## Not attempted this pass: the concrete `fAtT` instance

`fAtT p c0 c1 c2 c3 c4 i` has an "obvious" witness numerator
(`curvePoly.eval₂ (algebraMap (F p) (MvPolynomial (Fin 2) (F p))) (X i)`
-shaped) of `totalDegree ≤ 5` (`curvePoly_natDegree`, `DataDerivationBasics.
lean`, already proved) and denominator `1`. This is the concrete corollary
`baseFracToRing_totalDegree_le` exists to support, but the exact
witness-numerator polynomial for `fAtT` still needs pinning down against
`K0 p := FractionRing (MvPolynomial (Fin 2) (F p))`'s actual `algebraMap`/
`IsLocalization.mk'` conventions — the roadmap's own "Concrete numbers"
section flags this as real remaining tracing work, not guessed here.

## Level 2: `towerToRdec`'s `totalDegree` bound

`towerToRdec` (`K2 → Rdec`, the top-level entry point `theData`'s assembly
actually calls) has the identical combination shape one level up:
extracts `d0, d1 : K1 p c0 c1 c2 c3 c4` from `v : K2 p c0 c1 c2 c3 c4` via
`AdjoinRoot.modByMonicHom (K2_poly_monic ...)`, recurses via
`towerToRdecK1 p sg` on each (not `baseFracToRing` — one level up), and
combines with `sg.wGen 1` in place of `sg.wGen 0`. `combine_totalDegree_le`
is already general enough to close it verbatim, so the proof is the exact
same `unfold`/`obtain`/`combine_totalDegree_le` three-liner as
`towerToRdecK1_totalDegree_le`, with `towerToRdecK1_totalDegree_le`'s own
conclusion supplying the hypothesis in place of
`baseFracToRing_totalDegree_le`. -/
theorem towerToRdec_totalDegree_le {Vars : Type*}
    (sg : SideGens Vars) {D : ℕ} (v : K2 p c0 c1 c2 c3 c4)
    (h : (towerToRdecK1 p sg
            ((AdjoinRoot.modByMonicHom (K2_poly_monic p c0 c1 c2 c3 c4) v :
              Polynomial (K1 p c0 c1 c2 c3 c4)).coeff 0)).1.totalDegree ≤ D ∧
      (towerToRdecK1 p sg
            ((AdjoinRoot.modByMonicHom (K2_poly_monic p c0 c1 c2 c3 c4) v :
              Polynomial (K1 p c0 c1 c2 c3 c4)).coeff 0)).2.totalDegree ≤ D ∧
      (towerToRdecK1 p sg
            ((AdjoinRoot.modByMonicHom (K2_poly_monic p c0 c1 c2 c3 c4) v :
              Polynomial (K1 p c0 c1 c2 c3 c4)).coeff 1)).1.totalDegree ≤ D ∧
      (towerToRdecK1 p sg
            ((AdjoinRoot.modByMonicHom (K2_poly_monic p c0 c1 c2 c3 c4) v :
              Polynomial (K1 p c0 c1 c2 c3 c4)).coeff 1)).2.totalDegree ≤ D) :
    (towerToRdec p sg v).1.totalDegree ≤ 2 * D + 1 ∧
    (towerToRdec p sg v).2.totalDegree ≤ 2 * D := by
  unfold towerToRdec
  obtain ⟨h00, h01, h10, h11⟩ := h
  exact combine_totalDegree_le p (sg.wGen 1) h00 h01 h10 h11

/-! ## `coeffsToNumDen`-shaped corollary

`DecoupledSystemRegular.lean`'s `coeffsToNumDen c0 c1 c2 c3 c4 sg poly :=
fun i => towerToRdec p sg (poly.coeff i.val)` — the actual bridge feeding
`u1_num`/`u1_den`/`u2_num`/`u2_den`/`v1_num`/`v1_den`/`v2_num`/`v2_den`
(`theData`'s eight fields, per that file's own `theData` definition) — is
`towerToRdec` applied to `poly.coeff i.val` for an arbitrary
`poly : Polynomial (K2 p c0 c1 c2 c3 c4)` and `i : Fin 2`. This restates
`towerToRdec_totalDegree_le` with `v := poly.coeff i.val` substituted in,
so `DecoupledSystemRegular.lean` (once it imports this file) can bound
each of `theData`'s eight fields by a single application, without needing
`coeffsToNumDen`/`Idx`/`Rdec` themselves in scope here — this file stays
import-independent of `DecoupledSystemRegular.lean`, avoiding a new
cross-file dependency this pass. -/
theorem towerToRdec_coeff_totalDegree_le {Vars : Type*}
    (sg : SideGens Vars) {D : ℕ}
    (poly : Polynomial (K2 p c0 c1 c2 c3 c4)) (i : Fin 2)
    (h : (towerToRdecK1 p sg
            ((AdjoinRoot.modByMonicHom (K2_poly_monic p c0 c1 c2 c3 c4)
              (poly.coeff i.val) :
              Polynomial (K1 p c0 c1 c2 c3 c4)).coeff 0)).1.totalDegree ≤ D ∧
      (towerToRdecK1 p sg
            ((AdjoinRoot.modByMonicHom (K2_poly_monic p c0 c1 c2 c3 c4)
              (poly.coeff i.val) :
              Polynomial (K1 p c0 c1 c2 c3 c4)).coeff 0)).2.totalDegree ≤ D ∧
      (towerToRdecK1 p sg
            ((AdjoinRoot.modByMonicHom (K2_poly_monic p c0 c1 c2 c3 c4)
              (poly.coeff i.val) :
              Polynomial (K1 p c0 c1 c2 c3 c4)).coeff 1)).1.totalDegree ≤ D ∧
      (towerToRdecK1 p sg
            ((AdjoinRoot.modByMonicHom (K2_poly_monic p c0 c1 c2 c3 c4)
              (poly.coeff i.val) :
              Polynomial (K1 p c0 c1 c2 c3 c4)).coeff 1)).2.totalDegree ≤ D) :
    (towerToRdec p sg (poly.coeff i.val)).1.totalDegree ≤ 2 * D + 1 ∧
    (towerToRdec p sg (poly.coeff i.val)).2.totalDegree ≤ 2 * D :=
  towerToRdec_totalDegree_le p c0 c1 c2 c3 c4 sg (poly.coeff i.val) h


end TheDataDerivation
end Genus2Lean
