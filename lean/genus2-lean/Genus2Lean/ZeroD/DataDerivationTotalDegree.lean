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
`combine_totalDegree_le`, `towerToRdecK1_totalDegree_le`,
`towerToRdec_totalDegree_le`, `fAtT_eq_mk'_one`, and now
`curvePoly_eval_C_totalDegree_le` (build green, per Claire's reports).
**Not yet REPL-confirmed**: `towerToRdec_coeff_totalDegree_le`, a pure
substitution corollary (`v := poly.coeff i.val`), low risk. This file is
now `sorry`-free end to end.

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

/-! ## `fAtT`'s concrete `mk'` witness — attempted this pass

`fAtT p c0 c1 c2 c3 c4 i := curvePoly.eval₂ (algebraMap (F p) (K0 p)) (t0 p i)`
(`DataDerivationTower.lean`). `curvePoly_eval_eq_fAtT_shape`
(`DataDerivationBasics.lean`, already proved, `rfl`) confirms this is
literally `curvePoly.eval₂ (algebraMap (F p) (K0 p)) (algebraMap
(MvPolynomial (Fin 2) (F p)) (K0 p) (X i))` — `K0 p`'s `abbrev`-transparency
means no cross-ring subtlety hides here. `Polynomial.hom_eval₂` (already
used elsewhere in this project for exactly this `eval₂`-under-`algebraMap`
move, e.g. `DataDerivationSolve.lean`'s `hcoeff`/`hom_eval₂` steps) pushes
the outer `algebraMap` through: taking `g := algebraMap (MvPolynomial (Fin
2) (F p)) (K0 p)`, `f := algebraMap (F p) (MvPolynomial (Fin 2) (F p))`,
`g.comp f = algebraMap (F p) (K0 p)` by the scalar tower `F p → MvPolynomial
(Fin 2) (F p) → K0 p` (`IsScalarTower.algebraMap_eq`, unverified this pass
which exact instance path Lean resolves this through — flagged below
rather than guessed), giving `fAtT p ... i = algebraMap (MvPolynomial (Fin
2) (F p)) (K0 p) a` for `a := curvePoly.eval₂ (algebraMap (F p)
(MvPolynomial (Fin 2) (F p))) (X i) : MvPolynomial (Fin 2) (F p)`, i.e.
`mk' (K0 p) a 1` (`IsLocalization.mk'_one`, denominator `1`). `a.totalDegree
≤ 5`: `algebraMap (F p) (MvPolynomial (Fin 2) (F p)) = MvPolynomial.C`, and
`Polynomial.eval₂` at a `totalDegree ≤ 1` point (`X i`) of a `natDegree = 5`
polynomial is bounded by the sum-of-monomials route below —
**not yet REPL-confirmed**, this pass's one new unverified claim, flagged
rather than left silently assumed. -/

/-- **`fAtT`'s `mk'` witness.** `fAtT p ... i` equals `algebraMap
(MvPolynomial (Fin 2) (F p)) (K0 p)` applied to `curvePoly`'s own `eval₂`
straight into `MvPolynomial (Fin 2) (F p)` (via `C`, not `K0 p`) at `X i` —
i.e. `mk' (K0 p) a 1` for that same `a`, via `IsLocalization.mk'_spec'`
(confirmed Mathlib name) rather than an assumed `mk'_one` lemma.
Purely mechanical (`hom_eval₂` plus unfolding `t0`/`K0`), no new
mathematics; **not yet REPL-confirmed this pass**, unlike the theorems
above it in this file. -/
theorem fAtT_eq_mk'_one (c0 c1 c2 c3 c4 : F p) (i : Fin 2) :
    fAtT p c0 c1 c2 c3 c4 i =
      IsLocalization.mk' (K0 p)
        ((curvePoly p c0 c1 c2 c3 c4).eval₂
          (algebraMap (F p) (MvPolynomial (Fin 2) (F p))) (MvPolynomial.X i))
        (1 : ↥(nonZeroDivisors (MvPolynomial (Fin 2) (F p)))) := by
  unfold fAtT t0
  rw [IsScalarTower.algebraMap_eq (F p) (MvPolynomial (Fin 2) (F p)) (K0 p),
    ← Polynomial.hom_eval₂]
  set a : MvPolynomial (Fin 2) (F p) :=
    (curvePoly p c0 c1 c2 c3 c4).eval₂ (algebraMap (F p) (MvPolynomial (Fin 2) (F p)))
      (MvPolynomial.X i) with ha
  -- `mk' (K0 p) a 1 = algebraMap _ (K0 p) a` -- derived from `mk'_spec'`
  -- (`algebraMap R S ↑y * mk' S x y = algebraMap R S x`, confirmed Mathlib
  -- name) with `y := (1 : ↥(nonZeroDivisors _))` rather than an assumed
  -- `mk'_one` lemma name: `↑(1 : ↥M) = 1` (`OneMemClass.coe_one` /
  -- `Submonoid.coe_one`) and `algebraMap _ _ 1 = 1` (`map_one`) turn
  -- `mk'_spec'` into `1 * mk' (K0 p) a 1 = algebraMap _ (K0 p) a`.
  have hspec := IsLocalization.mk'_spec' (K0 p) a
    (1 : ↥(nonZeroDivisors (MvPolynomial (Fin 2) (F p))))
  simp only [OneMemClass.coe_one, map_one, one_mul] at hspec
  rw [← hspec]

/-- **The concrete degree-`5` bound `fAtT`'s witness numerator satisfies.**
`curvePoly.eval₂ C (X i)` (`C := algebraMap (F p) (MvPolynomial (Fin 2)
(F p))`) unfolds via `Polynomial.eval₂_eq_sum_range'` (`curvePoly.natDegree
< 6`, from `curvePoly_natDegree`) to `∑ j ∈ range 6, C (curvePoly.coeff j) *
(X i)^j`; each summand has `totalDegree ≤ j ≤ 5`
(`MvPolynomial.totalDegree_C`/`totalDegree_X_pow`/`totalDegree_mul`), and
`MvPolynomial.totalDegree_finsetSum_le` (confirmed Mathlib name, GitHub
source read this pass — `(∀ i ∈ s, (f i).totalDegree ≤ d) → (s.sum
f).totalDegree ≤ d`, exactly this shape) caps the whole sum at `5`.
**REPL-confirmed** (Claire's report): build green, needed the `algebraMap
= C` defeq-`show` step spelled out explicitly since `rw [totalDegree_C]`
does not fire through the syntactic `algebraMap` form. -/
theorem curvePoly_eval_C_totalDegree_le (c0 c1 c2 c3 c4 : F p) (i : Fin 2) :
    ((curvePoly p c0 c1 c2 c3 c4).eval₂
        (algebraMap (F p) (MvPolynomial (Fin 2) (F p))) (MvPolynomial.X i) :
      MvPolynomial (Fin 2) (F p)).totalDegree ≤ 5 := by
  rw [Polynomial.eval₂_eq_sum_range' (algebraMap (F p) (MvPolynomial (Fin 2) (F p)))
      (by rw [curvePoly_natDegree]; omega : (curvePoly p c0 c1 c2 c3 c4).natDegree < 6)]
  refine MvPolynomial.totalDegree_finsetSum_le (fun j hj => ?_)
  simp only [Finset.mem_range] at hj
  show (MvPolynomial.C ((curvePoly p c0 c1 c2 c3 c4).coeff j) *
      MvPolynomial.X i ^ j : MvPolynomial (Fin 2) (F p)).totalDegree ≤ 5
  refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
  rw [MvPolynomial.totalDegree_C, zero_add, MvPolynomial.totalDegree_X_pow]
  omega

/-! ## Level 2: `towerToRdec`'s `totalDegree` bound

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

/-! ## `Matrix.det`/`Matrix.cramer`'s `totalDegree` bound

New this pass, per a ChatGPT consultation (`chatgpt_prompt_cramer_totaldegree.md`,
`Genus2Lean/` top level) on the piece the roadmap's Question 1 flagged as
missing from Mathlib: a `totalDegree` bound for `Matrix.det`/`Matrix.cramer`
in terms of entrywise bounds. This is generic `MvPolynomial` linear algebra,
independent of `K0`/`K1`/`K2`/`towerToRdec` — stated here for a general
`Fin n` matrix, not `Fin 4`-specific, matching Mathlib's own genericity and
this project's "prove it once" preference. Two separate lemmas, per
ChatGPT's own distinction:

1. **Polynomial case** (`det_totalDegree_le`, DONE, sorry-free this pass): a
   genuine `Matrix (Fin n) (Fin n) (MvPolynomial Vars (F p))` with all
   entries `totalDegree ≤ D` has `det.totalDegree ≤ n * D` — every one of
   the `n!` Leibniz terms is a product of exactly `n` entries, so
   `totalDegree_mul` iterated `n-1` times bounds each term by `n*D`, and
   `totalDegree_finsetSum_le` (already REPL-confirmed present in this file,
   see `curvePoly_eval_C_totalDegree_le` above) bounds the WHOLE sum by
   that same uniform `n*D` directly (a one-shot implication from "every
   summand ≤ d" to "the sum ≤ d", not a max/sup computation), so the `n!`
   term count never enters the bound at all.
2. **Fractional/Cramer case** (`matrixA`/`rhsVec`'s ACTUAL shape — `K2`-
   valued, not `MvPolynomial`-valued; see the correction note further down
   this file): given entries `a_ij/b_ij` (witness numerator/denominator
   pairs, `totalDegree ≤ D` each, `b_ij ≠ 0`), the target is an explicit
   witness numerator/denominator pair for `cramer A b i / A.det` with
   `totalDegree ≤ n^2*D` each — via the common-denominator identity
   `Δ_A * det A = N_A` (`Δ_A := ∏ b_ij`, `N_A := ∑_σ sgn(σ) * ∏_j
   (a_{σ(j),j} * ∏_{(r,c)≠(σ(j),j)} b_rc)`), applied separately to `A` and
   to `A` with column `i` replaced by `b` (`Matrix.updateColumn`, per
   `Matrix.cramer_apply`), then combined via `N_i * Δ_A` / `Δ_i * N_A`
   (cross-multiplying the two fractions) — `≤ 16*D + 16*D = 32*D` for
   `n=4`. **NOT fully closed this pass**: `Δ_A`'s own bound
   (`cramerDeltaA_totalDegree_le`) is proved, but the identity
   `Δ_A * det A = N_A` itself (needed before the numerator/denominator
   pair can be assembled) is flagged, not proved — see that section's own
   notes for exactly what remains. -/

/-- **Leibniz-term bound, one summand.** For a fixed permutation `σ`, the
product `∏ i, M (σ i) i` of `n` entries each `totalDegree ≤ D` has
`totalDegree ≤ n * D` — plain iterated `totalDegree_mul` via
`totalDegree_finsetProd`-shaped induction, spelled out with
`Finset.prod_le`-style reasoning rather than assuming the exact Mathlib
name `totalDegree_finsetProd` (unconfirmed against this Mathlib snapshot
as of this pass) is present; if it is, this can be shortened to a one-line
application. -/
theorem finsetProd_totalDegree_le {Vars ι : Type*} {D : ℕ}
    (f : ι → MvPolynomial Vars (F p)) (hf : ∀ i, (f i).totalDegree ≤ D)
    (s : Finset ι) :
    (∏ i ∈ s, f i).totalDegree ≤ s.card * D := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.card_insert_of_notMem hx]
    calc (f x * ∏ i ∈ s, f i).totalDegree
        ≤ (f x).totalDegree + (∏ i ∈ s, f i).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
      _ ≤ D + s.card * D := add_le_add (hf x) ih
      _ = (s.card + 1) * D := by ring

/-- `Fintype`-indexed corollary of `finsetProd_totalDegree_le`, specialized
to `s := Finset.univ` — the shape `det_totalDegree_le`/`cramerDeltaA_
totalDegree_le` below actually call. -/
theorem prod_totalDegree_le {Vars ι : Type*} [Fintype ι] {D : ℕ}
    (f : ι → MvPolynomial Vars (F p)) (hf : ∀ i, (f i).totalDegree ≤ D) :
    (∏ i, f i).totalDegree ≤ Fintype.card ι * D :=
  finsetProd_totalDegree_le p f hf Finset.univ

/-- **The polynomial-matrix determinant bound.** `M.det.totalDegree ≤
Fintype.card n * D` given every entry `totalDegree ≤ D`. Via `Matrix.
det_apply'` (`M.det = ∑ σ : Perm n, sign σ * ∏ i, M (σ i) i`, confirmed
present in Mathlib per a web-docs search this pass, NOT yet checked against
this project's own Mathlib snapshot/REPL) and `totalDegree_finsetSum_le`
(the exact confirmed shape already used above for `curvePoly_eval_C_
totalDegree_le`: `(∀ i ∈ s, (f i).totalDegree ≤ d) → (s.sum f).totalDegree
≤ d`, a direct implication, not a `≤ max`-then-`sup_le` two-step) to bound
every one of the `n!` permutation terms by the SAME `Fintype.card n * D`
directly; each term is `sign σ * (a product of n entries)`, and `sign σ`
is a unit `±1` so `MvPolynomial.totalDegree_neg`
handles the `sign σ = -1` case (the `sign σ = 1` case is `one_mul`,
needing no lemma at all). **Flagged, not asserted as working**: the exact
type/cast of `Equiv.Perm.sign σ` in `Matrix.det_apply'`'s statement (`ℤˣ`,
possibly via a bundled `•`/`SMul` rather than a literal `(· : ℤ) → R` cast
composed with `Int.cast`, as spelled out in the proof below) was not
independently re-confirmed against this exact Mathlib version — the proof
below is one reasonable spelling (`((Equiv.Perm.sign σ : ℤ) :
MvPolynomial Vars (F p))`) but may need adjusting to whatever the ACTUAL
elaborated cast is once Claire's REPL reports the real error, per this
project's normal "Claude drafts, Claire tests" workflow; not a sign the
underlying math is wrong, just that the exact cast spelling is unverified. -/
theorem det_totalDegree_le {Vars n : Type*} [Fintype n] [DecidableEq n] {D : ℕ}
    (M : Matrix n n (MvPolynomial Vars (F p)))
    (hM : ∀ i j, (M i j).totalDegree ≤ D) :
    M.det.totalDegree ≤ Fintype.card n * D := by
  classical
  rw [Matrix.det_apply']
  refine MvPolynomial.totalDegree_finsetSum_le (fun σ _ => ?_)
  have hprod : (∏ i, M (σ i) i).totalDegree ≤ Fintype.card n * D :=
    prod_totalDegree_le p (fun i => M (σ i) i) (fun i => hM (σ i) i)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hsign | hsign
  · simpa [hsign] using hprod
  · have : ((Equiv.Perm.sign σ : ℤ) : MvPolynomial Vars (F p)) *
        ∏ i, M (σ i) i = -(∏ i, M (σ i) i) := by
      simp [hsign]
    calc (((Equiv.Perm.sign σ : ℤ) : MvPolynomial Vars (F p)) * ∏ i, M (σ i) i).totalDegree
        = (-(∏ i, M (σ i) i)).totalDegree := by rw [this]
      _ = (∏ i, M (σ i) i).totalDegree := MvPolynomial.totalDegree_neg _
      _ ≤ Fintype.card n * D := hprod

/-! ## The actual `K2`-valued case: `matrixA`/`rhsVec`/`cramerSolution`

**Correction, this pass**: an earlier draft of this section wrongly assumed
`matrixA`/`rhsVec` were already `MvPolynomial`-valued (so `cramer`/`det`
could be bounded directly via `det_totalDegree_le` with no fraction-
clearing). They are NOT — `matrixA p c0 c1 c2 c3 c4 u0 u1 v0 v1 : Matrix
(Fin 4) (Fin 4) (K2 p c0 c1 c2 c3 c4)` (`K2` a FIELD, per `DataDerivationSolve.
lean`), and `cramerSolution i := (matrixA.cramer rhsVec i) / matrixA.det`
is a genuine `K2`-valued field division. So the fractional/witness case
(ChatGPT's `Δ_A`/`N_A` common-denominator construction) is exactly what's
needed here, not a hypothetical future case — caught before being acted on
further, per this project's own rule against silently assuming the easy
case applies. -/

/-- **`Δ_A`'s own bound — the one piece of the Cramer-ratio witness
argument provable right now, independent of the rest.** The full plan
(ChatGPT's common-denominator identity, recorded here so it isn't lost):
given `A : Matrix (Fin 4) (Fin 4) R` (`R` any commutative ring) with each
entry `A i j = a i j / b i j` for `b i j` a unit, `(∏ i j, b i j) * A.det =
N_A` where `N_A := ∑ σ, sign σ * ∏ j, (a (σ j) j * ∏ (i',j') ∈ {(i',j') |
(i',j') ≠ (σ j, j)}, b i' j')` — proved by substituting `A i j = a i j *
(b i j)⁻¹` into `Matrix.det_apply'` and clearing every entry's own
denominator via the other entries' numerators. **Not attempted this
pass**: the `Finset.prod`-manipulation to actually verify `Δ_A * (sign σ *
∏ i, A (σ i) i) = sign σ * ∏ j, (a (σ j) j * ∏ (i',j')≠(σ j,j), b i' j')`
termwise (needs `Finset.prod_erase`/`Finset.mul_prod_erase`-style
bookkeeping over the `Fin 4 × Fin 4` index grid, splitting `∏ (i',j'),
b i' j'` into "the `(σ j, j)` factor" times "everything else" — a
finite/decidable but non-trivial index manipulation) — flagged as the
concrete remaining step rather than guessed at, since getting the exact
`Finset` identity wrong here would be more costly to unwind later than
leaving it open now. See `chatgpt_prompt_cramer_totaldegree.md`'s reply
for the full derivation this is transcribing; a second ChatGPT round-trip
focused purely on the `Finset.prod` manipulation (not the underlying math,
already settled) is the natural next step if a direct Mathlib search for
`Matrix.det`-vs-`Finset.prod`-splitting lemmas doesn't turn up a shortcut.

**What CAN be proved now, unconditionally, without that identity**: a
`totalDegree` bound on `Δ_A := ∏ i j, b i j` itself, via
`prod_totalDegree_le` applied twice (rows, then columns) — `n^2 * D` for
an `n×n` grid of `≤D`-degree factors, `16*D` for `n=4`. This is the lemma
actually proved below; `N_A`'s own bound (also `≤ n^2*D`, same shape, `n`
numerator factors `≤ n*D` plus `n^2-n` denominator factors `≤ (n^2-n)*D`,
matching ChatGPT's `nD+n(n-1)D=n^2D`) and the full witness-pair assembly
both wait on the identity above. -/
theorem cramerDeltaA_totalDegree_le {Vars : Type*} {D : ℕ}
    (b : Fin 4 → Fin 4 → MvPolynomial Vars (F p))
    (hb : ∀ i j, (b i j).totalDegree ≤ D) :
    (∏ i, ∏ j, b i j).totalDegree ≤ 16 * D := by
  have hrow : ∀ i, (∏ j, b i j).totalDegree ≤ 4 * D := by
    intro i
    have hcard : (∏ j, b i j).totalDegree ≤ Fintype.card (Fin 4) * D :=
      prod_totalDegree_le p (b i) (hb i)
    simpa using hcard
  have hcol : (∏ i, ∏ j, b i j).totalDegree ≤ Fintype.card (Fin 4) * (4 * D) :=
    prod_totalDegree_le p (fun i => ∏ j, b i j) hrow
  have : Fintype.card (Fin 4) * (4 * D) = 16 * D := by simp; ring
  rwa [this] at hcol

/-! ## The `Δ_A * A.det = N_A` identity — resolved via ChatGPT consultation

**Update, this pass**: the identity flagged as blocked in this section's
previous note is now closed, via a cleaner route than the `Finset.prod_erase`
grid-partition originally sketched — see `chatgpt_prompt_cramer_totaldegree.md`'s
follow-up reply for the full derivation this is transcribing. The key move:
convert the per-entry denominators into COLUMN denominators first, then let
`Matrix.det_mul_column` (confirmed present, exact signature `(v : n → R)
(A : Matrix n n R) : (Matrix.of fun i j => v i * A i j).det = (∏ i, v i) *
A.det` — note `v`'s index `i` there is the ROW index, matching what's needed
here since we're scaling column `j`'s `n` entries, which sit at varying row
index `i`) do essentially all the determinant bookkeeping, rather than
manually splitting a `Fin 4 × Fin 4` grid product along a permutation's
diagonal.

Concretely: for `A i j := a i j / b i j` (`b i j ≠ 0`), define

    C i j := a i j * ∏ i' ∈ univ \ {i}, b i' j

Then, pointwise, `C i j = (∏ i, b i j) * (a i j / b i j)` — this uses `b i j
≠ 0` only to cancel `b i j / b i j = 1` after re-inserting the `i' = i`
factor into the product. `Matrix.det_mul_column` (with `v i := ∏ i', b i' j`
depending on `j`... more precisely applied per-column, see the proof below
for how the `j`-dependence of `v` is handled) then gives `Δ_A * A.det =
C.det` directly, where `Δ_A := ∏ i j, b i j`, no `Finset.prod_erase`/grid
partition needed at all. The Leibniz-expansion form
(`N_A := ∑ σ, sign σ * ∏ j, (a (σ j) j * ∏ i' ≠ σ j, b i' j)`) originally
proposed is recovered by unfolding `Matrix.det_apply'` on `C` — it was
correct as first written, but is no longer needed as the primary
definition: `C.det` is the cleaner one to work with, and expand only when
the explicit permutation sum is actually needed (e.g. inside the degree
bound below, which goes through `det_totalDegree_le` instead and doesn't
need the explicit sum at all).

**Correction on the exact Mathlib route, this pass**: `Matrix.det_mul_column`
turned out to be the wrong tool to invoke directly here — its `v : n → R` is
a single function scaling every column identically, not naturally
column-indexed, and trying to force the construction below through it hit a
genuine bookkeeping mismatch (documented, then resolved, rather than
papered over — see the abandoned attempt this replaced, in this section's
git history/previous docstring revision if needed). **The clean fix**:
`C = A * Matrix.diagonal (fun j => ∏ i, b i j)` as an honest matrix
PRODUCT — `Matrix.mul_apply`'s dot product against a diagonal matrix
collapses to exactly one term, `(A * diagonal d) i j = A i j * d j`, which
is precisely "scale column `j` by `d j`," with no per-column-indexed
generalization of `det_mul_column` needed at all. Then `Matrix.det_mul`
(`(M*N).det = M.det * N.det`) and `Matrix.det_diagonal`
(`(diagonal d).det = ∏ i, d i`) finish the identity in two standard,
unambiguous lemmas. -/

/-- **Pointwise denominator-clearing identity.** `C`'s `(i,j)` entry (the
product of `a i j` with every OTHER row's `b`-entry in column `j`) equals
column `j`'s full `b`-product times `A`'s `(i,j)` entry `a i j / b i j`. The
`∏ i', b i' j` on the RHS splits into `b i j` (cancelling against the
division) times `∏ i' ≠ i, b i' j` (matching `C i j`'s own product), via
`Finset.prod_eq_mul_prod_diff_singleton` — a single `Finset.mem_univ`-indexed
singleton/complement split, not a full grid partition. -/
theorem cramerEntry_eq_denomProd_mul_ratio {n : Type*} [DecidableEq n] [Fintype n]
    {K : Type*} [Field K] (a b : n → n → K) (hb : ∀ i j, b i j ≠ 0) (i j : n) :
    a i j * ∏ i' ∈ Finset.univ \ {i}, b i' j =
      (∏ i', b i' j) * (a i j / b i j) := by
  have hsplit : ∏ i', b i' j = b i j * ∏ i' ∈ Finset.univ \ {i}, b i' j := by
    rw [← Finset.prod_eq_mul_prod_diff_singleton (Finset.mem_univ i)]
  rw [hsplit, mul_comm (b i j), mul_assoc, mul_div_cancel₀ _ (hb i j)]
  ring

/-- **`C` as a matrix product: `A` times the diagonal of column-products.**
`(A * Matrix.diagonal (fun j => ∏ i, b i j)) i j = A i j * (∏ i', b i' j)`
— `Matrix.mul_apply`'s dot product over `Matrix.diagonal`'s off-diagonal
zeros collapses to the single `k = j` term. Combined with
`cramerEntry_eq_denomProd_mul_ratio` (which identifies that product,
pointwise, with `C i j`), this is exactly `C = A * diagonal (...)` as
matrices — the bridge `cramerDenom_det_eq` below needs. -/
theorem mul_diagonal_apply_eq_mul {n : Type*} [DecidableEq n] [Fintype n]
    {K : Type*} [Field K] (A : Matrix n n K) (d : n → K) (i j : n) :
    (A * Matrix.diagonal d) i j = A i j * d j := by
  simp [Matrix.mul_apply, Matrix.diagonal, Finset.sum_ite_eq', Finset.mem_univ]

/-- **The determinant identity itself.** `C i j := a i j * ∏ i' ≠ i, b i' j`
(an honest `K`-valued matrix, no division) satisfies `Δ_A * A.det = C.det`,
where `Δ_A := ∏ i j, b i j` and `A i j := a i j / b i j`. Proved via
`C = A * diagonal (fun j => ∏ i, b i j)` (`mul_diagonal_apply_eq_mul` +
`cramerEntry_eq_denomProd_mul_ratio` identify the entries pointwise;
`Matrix.ext` assembles the matrix equality), then `Matrix.det_mul` +
`Matrix.det_diagonal` turn that into the determinant identity directly —
no `Finset.prod_erase` grid partition, and no column-indexed
generalization of `det_mul_column`, needed anywhere. -/
theorem cramerDenom_det_eq {n : Type*} [DecidableEq n] [Fintype n]
    {K : Type*} [Field K] (a b : n → n → K) (hb : ∀ i j, b i j ≠ 0) :
    (∏ i, ∏ j, b i j) * Matrix.det (Matrix.of fun i j => a i j / b i j) =
      Matrix.det (Matrix.of fun i j => a i j * ∏ i' ∈ Finset.univ \ {i}, b i' j) := by
  set A : Matrix n n K := Matrix.of fun i j => a i j / b i j with hA_def
  set d : n → K := fun j => ∏ i, b i j with hd_def
  have hCeq : (Matrix.of fun i j => a i j * ∏ i' ∈ Finset.univ \ {i}, b i' j) =
      A * Matrix.diagonal d := by
    ext i j
    rw [mul_diagonal_apply_eq_mul]
    exact (cramerEntry_eq_denomProd_mul_ratio a b hb i j).symm
  rw [hCeq, Matrix.det_mul, Matrix.det_diagonal]
  rw [show (∏ i, ∏ i' : n, b i' i) = (∏ i, ∏ j, b i j) from Finset.prod_comm]
  ring

/-! ## Status, this section: identity closed, degree corollary next

**Closed, this pass**: `cramerDenom_det_eq` (the `Δ_A * A.det = C.det`
identity ChatGPT's consultation scoped) is proved outright, via the
diagonal-matrix route (`C = A * diagonal (column-products)`, then
`Matrix.det_mul`/`Matrix.det_diagonal`) rather than the originally-sketched
`Finset.prod_erase` grid partition, or the column-indexed `det_mul_column`
attempt that preceded this version and hit a genuine index-convention
mismatch (documented, then routed around, not silently dropped). **Not yet
REPL-confirmed** — `mul_diagonal_apply_eq_mul`'s `simp` call and
`Finset.prod_comm`'s exact application in the final `congr` step are the
two spots most likely to need adjusting once Claire's REPL reports the
actual goal state, per this project's normal workflow.

**Next step**: derive `C.det`'s `totalDegree ≤ n^2 * D` (given `a i j`/
`b i j` both `≤ D`) from `det_totalDegree_le` above — `C`'s own entries are
`≤ n * D` each (via `finsetProd_totalDegree_le`/`prod_totalDegree_le`-style
reasoning on the `n-1`-factor product plus the `a i j` factor), so
`det_totalDegree_le` gives `≤ n * (n*D) = n^2*D` directly. Not yet stated
as its own theorem this pass — `cramerDenom_det_eq` was the harder,
identity-level piece; the degree bound is now a direct corollary once
stated. Once that's in place, `CrossNondegenerate`'s resultant degree bound
(the actual next layer up, in `DecoupledSystemRegular.lean`) is one more
application away. -/

end TheDataDerivation
end Genus2Lean
