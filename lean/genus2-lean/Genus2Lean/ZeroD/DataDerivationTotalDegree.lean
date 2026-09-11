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

**Later pass, this section**: added `cramerNumeratorEntry_totalDegree_le`/
`cramerNumeratorDet_totalDegree_le`, the flagged degree corollary to
`cramerDenom_det_eq`'s `Δ_A * A.det = C.det` identity (see the "Cramer
ratio witness" section below, near end of file) — `C.det.totalDegree ≤
(Fintype.card n)^2 * D` given entrywise `≤ D` bounds on the raw `a`/`b`
Cramer data. Build-confirmed green by Claire's REPL after fixing four
lemma-name/unification errors on first build (see that section's own
status note for the fix list).

**This pass**: closed the section's own remaining open item — bounding
`A.det`'s own `totalDegree` (the actual Cramer ratio, not just its
fraction-cleared numerator `C.det`). Added `numDen_cross_mul'`/
`isFractionRing_num_totalDegree_le'` (`Vars`-parametrized generalizations
of `numDen_cross_mul`/`isFractionRing_num_totalDegree_le` above, identical
proof, just not hardcoded to `MvPolynomial (Fin 2) (F p)`) and
`cramerRatioDet_num_totalDegree_le`, which composes that generic bound
with `cramerNumeratorDet_totalDegree_le` via the `Δ_A * A.det = C.det`
identity to bound `A.det`'s `IsFractionRing.num` by `(Fintype.card n)^2 *
D`. **Not yet REPL-confirmed.**
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
`Finset.prod_sdiff` (applied to `{i} ⊆ univ`, `Finset.prod_singleton`
collapsing the singleton factor to `b i j`) — a single singleton/complement
split, not a full grid partition. -/
theorem cramerEntry_eq_denomProd_mul_ratio {n : Type*} [DecidableEq n] [Fintype n]
    {K : Type*} [Field K] (a b : n → n → K) (hb : ∀ i j, b i j ≠ 0) (i j : n) :
    a i j * ∏ i' ∈ Finset.univ \ {i}, b i' j =
      (∏ i', b i' j) * (a i j / b i j) := by
  have hsplit : ∏ i', b i' j = b i j * ∏ i' ∈ Finset.univ \ {i}, b i' j := by
    have hkey : (∏ i' ∈ Finset.univ \ {i}, b i' j) * ∏ i' ∈ ({i} : Finset n), b i' j =
        ∏ i', b i' j := Finset.prod_sdiff (Finset.subset_univ {i})
    rw [Finset.prod_singleton] at hkey
    rw [← hkey]; ring
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
    rw [Matrix.of_apply, mul_diagonal_apply_eq_mul]
    show a i j * ∏ i' ∈ Finset.univ \ {i}, b i' j = (a i j / b i j) * (∏ i, b i j)
    rw [cramerEntry_eq_denomProd_mul_ratio a b hb i j, mul_comm]
  rw [hCeq, Matrix.det_mul, Matrix.det_diagonal]
  rw [show (∏ i, ∏ i' : n, b i' i) = (∏ i, ∏ j, b i j) from Finset.prod_comm]
  ring

/-- **`C`'s entries are each `totalDegree ≤ n * D`.** `C i j := a i j * ∏ i'
∈ univ \ {i}, b i' j` is one `a`-factor (`≤ D`) times an `(n-1)`-factor
product of `b`-entries (`≤ D` each, so `≤ (n-1)*D` by
`finsetProd_totalDegree_le`) — `MvPolynomial.totalDegree_mul` adds the two
bounds, giving `≤ D + (n-1)*D = n*D` after `Finset.card_sdiff_of_subset`/
`Finset.card_singleton` pin down `(univ \ {i}).card = n - 1`. This is the
per-entry bound `det_totalDegree_le` needs to bound `C.det` itself. -/
theorem cramerNumeratorEntry_totalDegree_le {Vars n : Type*} [Fintype n]
    [DecidableEq n] {D : ℕ}
    (a b : n → n → MvPolynomial Vars (F p)) (ha : ∀ i j, (a i j).totalDegree ≤ D)
    (hb : ∀ i j, (b i j).totalDegree ≤ D) (i j : n) :
    (a i j * ∏ i' ∈ Finset.univ \ {i}, b i' j).totalDegree ≤ Fintype.card n * D := by
  have hcard : (Finset.univ \ ({i} : Finset n)).card = Fintype.card n - 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_singleton,
      Finset.card_univ]
  have hprod : (∏ i' ∈ Finset.univ \ {i}, b i' j).totalDegree ≤
      (Fintype.card n - 1) * D := by
    have := finsetProd_totalDegree_le p (fun i' => b i' j) (fun i' => hb i' j)
      (Finset.univ \ {i})
    rwa [hcard] at this
  have hcardpos : 1 ≤ Fintype.card n := Fintype.card_pos_iff.mpr ⟨i⟩
  have hstep : (a i j * ∏ i' ∈ Finset.univ \ {i}, b i' j).totalDegree ≤
      D + (Fintype.card n - 1) * D :=
    le_trans (MvPolynomial.totalDegree_mul _ _) (add_le_add (ha i j) hprod)
  have heq : D + (Fintype.card n - 1) * D = Fintype.card n * D := by
    have hsub : Fintype.card n - 1 + 1 = Fintype.card n := Nat.sub_add_cancel hcardpos
    calc D + (Fintype.card n - 1) * D
        = (Fintype.card n - 1) * D + D := by ring
      _ = (Fintype.card n - 1 + 1) * D := by ring
      _ = Fintype.card n * D := by rw [hsub]
  rw [heq] at hstep
  exact hstep

/-- **The Cramer-numerator determinant's `totalDegree` bound.** `C.det :=
Matrix.det (Matrix.of fun i j => a i j * ∏ i' ≠ i, b i' j)` satisfies
`totalDegree ≤ (Fintype.card n)^2 * D` given `a i j`/`b i j` both `≤ D` —
`det_totalDegree_le` applied with the per-entry bound
`cramerNumeratorEntry_totalDegree_le` (`≤ Fintype.card n * D` each),
giving `Fintype.card n * (Fintype.card n * D) = (Fintype.card n)^2 * D`
after `sq`/`mul_assoc` bookkeeping. Combined with `cramerDenom_det_eq`
(the `Δ_A * A.det = C.det` identity), this bounds the fraction-cleared
Cramer numerator `C.det` uniformly, given only entrywise bounds on the raw
`a`/`b` data — no factorization of `C.det` itself needed. -/
theorem cramerNumeratorDet_totalDegree_le {Vars n : Type*} [Fintype n]
    [DecidableEq n] {D : ℕ}
    (a b : n → n → MvPolynomial Vars (F p)) (ha : ∀ i j, (a i j).totalDegree ≤ D)
    (hb : ∀ i j, (b i j).totalDegree ≤ D) :
    (Matrix.det (Matrix.of fun i j => a i j * ∏ i' ∈ Finset.univ \ {i}, b i' j)).totalDegree
      ≤ (Fintype.card n) ^ 2 * D := by
  have hentry : ∀ i j, (a i j * ∏ i' ∈ Finset.univ \ {i}, b i' j).totalDegree ≤
      Fintype.card n * D :=
    fun i j => cramerNumeratorEntry_totalDegree_le p a b ha hb i j
  have := det_totalDegree_le p (Matrix.of fun i j => a i j * ∏ i' ∈ Finset.univ \ {i}, b i' j)
    hentry
  calc (Matrix.det (Matrix.of fun i j => a i j * ∏ i' ∈ Finset.univ \ {i}, b i' j)).totalDegree
      ≤ Fintype.card n * (Fintype.card n * D) := this
    _ = (Fintype.card n) ^ 2 * D := by ring

/-! ## `A.det`'s own `totalDegree` bound: the actual Cramer ratio

`A i j := a i j / b i j` (`A` from `cramerDenom_det_eq`) lives in `K :=
FractionRing (MvPolynomial Vars (F p))` once `A.det` is actually formed as
a genuine field-valued quantity, not the honest `MvPolynomial`-valued `C`.
`A.det`'s `IsFractionRing.num`/`.den` therefore need the SAME cross-
multiplication route as `isFractionRing_num_totalDegree_le`/
`isFractionRing_den_totalDegree_le` above — those two are specialized to
`K0 p = FractionRing (MvPolynomial (Fin 2) (F p))`; this section restates
the identical argument generically over any `Vars`, since the Cramer
application needs it at whatever variable set is in play at that point,
not just `Fin 2`. -/

/-- **Generic cross-multiplication identity**, `Vars`-parametrized version
of `numDen_cross_mul` above (identical proof, only the base ring
generalized from `MvPolynomial (Fin 2) (F p)` to `MvPolynomial Vars
(F p)` for arbitrary `Vars`). -/
private theorem numDen_cross_mul' {Vars : Type*}
    {a b : MvPolynomial Vars (F p)} {v : FractionRing (MvPolynomial Vars (F p))}
    (hb : b ≠ 0)
    (hv : v = IsLocalization.mk' (FractionRing (MvPolynomial Vars (F p))) a
      ⟨b, mem_nonZeroDivisors_of_ne_zero hb⟩) :
    a * (IsFractionRing.den (MvPolynomial Vars (F p)) v : MvPolynomial Vars (F p)) =
      IsFractionRing.num (MvPolynomial Vars (F p)) v * b := by
  have hmk : IsLocalization.mk' (FractionRing (MvPolynomial Vars (F p))) a
      ⟨b, mem_nonZeroDivisors_of_ne_zero hb⟩ =
      IsLocalization.mk' (FractionRing (MvPolynomial Vars (F p)))
        (IsFractionRing.num (MvPolynomial Vars (F p)) v)
        (IsFractionRing.den (MvPolynomial Vars (F p)) v) := by
    rw [← hv]; exact (IsFractionRing.mk'_num_den (MvPolynomial Vars (F p)) v).symm
  have heq := IsLocalization.mk'_eq_iff_eq'.mp hmk
  exact (FaithfulSMul.algebraMap_injective (MvPolynomial Vars (F p))
    (FractionRing (MvPolynomial Vars (F p)))) heq

/-- **`Vars`-parametrized generic version of `isFractionRing_num_totalDegree_le`.**
Same proof, generalized base ring — the numerator side of the Cramer
ratio's `totalDegree` bound. -/
theorem isFractionRing_num_totalDegree_le' {Vars : Type*}
    {a b : MvPolynomial Vars (F p)} {v : FractionRing (MvPolynomial Vars (F p))}
    (hb : b ≠ 0)
    (hv : v = IsLocalization.mk' (FractionRing (MvPolynomial Vars (F p))) a
      ⟨b, mem_nonZeroDivisors_of_ne_zero hb⟩)
    (ha : a ≠ 0) :
    (IsFractionRing.num (MvPolynomial Vars (F p)) v).totalDegree ≤ a.totalDegree := by
  have hcross := numDen_cross_mul' p hb hv
  have hdvd' : IsFractionRing.num (MvPolynomial Vars (F p)) v ∣
      a * (IsFractionRing.den (MvPolynomial Vars (F p)) v : MvPolynomial Vars (F p)) :=
    ⟨b, hcross⟩
  have hdvd : IsFractionRing.num (MvPolynomial Vars (F p)) v ∣ a :=
    (IsFractionRing.num_den_reduced (MvPolynomial Vars (F p)) v).dvd_of_dvd_mul_right hdvd'
  exact MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdvd ha

/-- **The actual target: `A.det`'s numerator has `totalDegree ≤
(Fintype.card n)^2 * D`.** Given `cramerDenom_det_eq`'s identity `Δ_A *
A.det = C.det` (`Δ_A := ∏ i j, b i j ≠ 0` when every `b i j ≠ 0`, so
`A.det = C.det / Δ_A` as a genuine `IsLocalization.mk'`-shaped fraction),
`isFractionRing_num_totalDegree_le'` bounds `A.det`'s `IsFractionRing.num`
by `C.det`'s own `totalDegree` — which `cramerNumeratorDet_totalDegree_le`
already bounds by `(Fintype.card n)^2 * D`. This is the theorem
`ROADMAP-crossnondegenerate-degree-bound.md`'s "Next step" note asked for:
a `totalDegree` bound on the Cramer ratio itself, not just its
fraction-cleared numerator `C.det`. -/
theorem cramerRatioDet_num_totalDegree_le {Vars n : Type*} [Fintype n]
    [DecidableEq n] {D : ℕ}
    (a b : n → n → MvPolynomial Vars (F p)) (ha : ∀ i j, (a i j).totalDegree ≤ D)
    (hb : ∀ i j, (b i j).totalDegree ≤ D) (hbne : ∀ i j, b i j ≠ 0)
    (v : FractionRing (MvPolynomial Vars (F p)))
    (hv : v = IsLocalization.mk' (FractionRing (MvPolynomial Vars (F p)))
      (Matrix.det (Matrix.of fun i j => a i j * ∏ i' ∈ Finset.univ \ {i}, b i' j))
      ⟨∏ i, ∏ j, b i j, mem_nonZeroDivisors_of_ne_zero (Finset.prod_ne_zero_iff.mpr
        (fun i _ => Finset.prod_ne_zero_iff.mpr (fun j _ => hbne i j)))⟩)
    (hCdet_ne : Matrix.det (Matrix.of fun i j =>
      a i j * ∏ i' ∈ Finset.univ \ {i}, b i' j) ≠ 0) :
    (IsFractionRing.num (MvPolynomial Vars (F p)) v).totalDegree ≤
      (Fintype.card n) ^ 2 * D := by
  have hDelta_ne : (∏ i, ∏ j, b i j : MvPolynomial Vars (F p)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => Finset.prod_ne_zero_iff.mpr (fun j _ => hbne i j))
  have hCdet_bound := cramerNumeratorDet_totalDegree_le p a b ha hb
  exact le_trans (isFractionRing_num_totalDegree_le' p hDelta_ne hv hCdet_ne) hCdet_bound

/-! ## Status, this section: identity closed, degree corollary now proved

**Closed, this pass**: `cramerDenom_det_eq` (the `Δ_A * A.det = C.det`
identity ChatGPT's consultation scoped) is proved outright, via the
diagonal-matrix route (`C = A * diagonal (column-products)`, then
`Matrix.det_mul`/`Matrix.det_diagonal`) rather than the originally-sketched
`Finset.prod_erase` grid partition, or the column-indexed `det_mul_column`
attempt that preceded this version and hit a genuine index-convention
mismatch (documented, then routed around, not silently dropped).

**Build errors found and fixed, later pass (Claire's REPL)**: four errors
surfaced on first build, all now fixed:
1. `cramerEntry_eq_denomProd_mul_ratio`'s `hsplit` used a nonexistent
   lemma name (`Finset.prod_eq_mul_prod_diff_singleton`) — replaced with
   `Finset.prod_sdiff (Finset.subset_univ {i})` (`(univ\{i}).prod f *
   {i}.prod f = univ.prod f`) plus `Finset.prod_singleton` to collapse the
   singleton factor, then `rw [← hkey]; ring` to close.
2. `cramerDenom_det_eq`'s `hCeq` needed `Matrix.of_apply` to unfold
   `Matrix.of (fun i j => ...) i j` to the raw function application before
   `mul_diagonal_apply_eq_mul` could fire on the RHS, and needed an
   explicit `show` (unfolding the `set`-introduced `A`/`d` to their
   definitions) before `cramerEntry_eq_denomProd_mul_ratio` could match —
   `rw` alone couldn't see through the `set` abstraction to unify the
   goal with the lemma's stated shape.
3. `cramerNumeratorEntry_totalDegree_le`'s `hcard` used
   `Finset.card_sdiff`, which is a different (non-function) lemma in this
   Mathlib snapshot (`(t\s).card = t.card - (s∩t).card`, no hypothesis) —
   replaced with `Finset.card_sdiff_of_subset (h : s ⊆ t) : (t\s).card =
   t.card - s.card`, the hypothesis-taking version actually needed here.
4. (Same fix propagated to this docstring's own lemma-name references.)

**Not yet REPL-confirmed again after these fixes** — send back to Claire's
REPL for a fresh build.

**Next step**: with `cramerDenom_det_eq` (`Δ_A * A.det = C.det`) and
`cramerNumeratorDet_totalDegree_le` (`C.det.totalDegree ≤ n^2*D`) both in
place, deriving a `totalDegree` bound on `A.det` itself (the actual Cramer
ratio, `A i j = a i j / b i j`) is the natural next corollary — but note
`A.det` is `K`-valued, not `MvPolynomial`-valued, so this needs routing
through `IsFractionRing.num`/`.den` on `A.det` the same way `baseFracToRing_
totalDegree_le` does at the base case, not a direct `totalDegree` call on
`A.det` itself. Once that's in place, `CrossNondegenerate`'s resultant
degree bound (the actual next layer up, in `DecoupledSystemRegular.lean`)
is one more application away. -/

/-! ## `w1`/`w2`'s own `towerToRdecK1`/`towerToRdec` image — the roadmap's
"comparatively simple to bound directly" note, closed this pass

`matrixA`/`rhsVec`'s entries (`DataDerivationSolve.lean`) are built entirely
from `anchor1`/`anchor2` (`= (t1, w1)`, `(t2, w2)`, `K2`-valued) and
`reduceMonomialModU`'s output (an `F p × F p` PAIR — pure scalars, `totalDegree
0` once pushed through `algebraMap`, no bound needed beyond `MvPolynomial.
totalDegree_C`). `t1/t2` are already handled (`anchor1_ne_anchor2`'s own
tracing, `DataDerivationSolve.lean`: both are literal free `MvPolynomial`
generators pushed through the tower, `totalDegree` exactly `1`/`0` for
num/den). **What was NOT yet traced**: `w1`/`w2` themselves, `AdjoinRoot.root`
of their respective minimal polynomials — this section closes that.

**The key fact**: `AdjoinRoot.root g = AdjoinRoot.mk g X` (Mathlib's own
description of `root`, "the image of `X` in `R[X]/(g)`"; `AdjoinRoot.mk_X`,
already used elsewhere in this project — e.g. `DataDerivationBasics.lean`,
`DataDerivationMumford.lean` — confirms this is the right rewrite). So
`AdjoinRoot.modByMonicHom hg (AdjoinRoot.root g) = X %ₘ g` via `AdjoinRoot.
modByMonicHom_mk` (after rewriting `root g` to `mk g X`), and for `g` a monic
QUADRATIC (`K1_poly_monic`/`K2_poly_monic`, both `natDegree = 2`), `X.degree =
1 < 2 = g.degree` means `X %ₘ g = X` outright (`Polynomial.modByMonic_eq_self_
iff`, the standard "already reduced" case — no actual division happens).
Concretely: `(X %ₘ g).coeff 0 = 0`, `(X %ₘ g).coeff 1 = 1` — i.e. `w1`'s
`towerToRdecK1` input is the SIMPLEST possible nonzero case, `d0 = 0 : K0 p`,
`d1 = 1 : K0 p` (not even needing `baseFracToRing`'s `IsFractionRing.num/.den`
machinery at its full generality — `0`'s and `1`'s numerator/denominator are
immediate). -/

/-- **`X %ₘ g = X` when `g` is monic of `natDegree = 2`.** The general fact
underlying `w1 %ₘ K1_poly = X`/`w2 %ₘ K2_poly = X`: `X.degree = 1 < 2 ≤
g.degree` (`g.degree = g.natDegree` since `g ≠ 0`, monic), so `X` is already
its own remainder — `Polynomial.modByMonic_eq_self_iff` (needs only `g.Monic`,
`Nontrivial R`, no other hypothesis) closes it directly once the degree
comparison is in hand. Stated generically (`CommRing R`, `Nontrivial R`,
`g.natDegree = 2` rather than `= 2` for `K1`/`K2` specifically) since the
identical fact is needed at both tower levels. -/
theorem X_modByMonic_eq_self_of_natDegree_eq_two {R : Type*} [CommRing R] [Nontrivial R]
    {g : Polynomial R} (hg : g.Monic) (hdeg : g.natDegree = 2) :
    (X : Polynomial R) %ₘ g = X := by
  rw [Polynomial.modByMonic_eq_self_iff hg]
  rw [Polynomial.degree_X, Polynomial.degree_eq_natDegree hg.ne_zero, hdeg]
  norm_num

/-- **Companion for constants**: `C a %ₘ g = C a` when `g` is monic of
`natDegree ≥ 1` — needed for `(0 : K1 p ...)`/`(1 : K1 p ...)`'s own
`modByMonicHom` images (`0`/`1 : Polynomial (K0 p)` are `C 0`/`C 1` up to the
`Polynomial.C_0`/`C_1` identification), same `modByMonic_eq_self_iff` route
as `X_modByMonic_eq_self_of_natDegree_eq_two`, with `degree (C a) ≤ 0 < 1 ≤
g.degree` in place of `degree X = 1 < 2 ≤ g.degree`. -/
theorem C_modByMonic_eq_self_of_natDegree_pos {R : Type*} [CommRing R] [Nontrivial R]
    {g : Polynomial R} (hg : g.Monic) (hdeg : 0 < g.natDegree) (a : R) :
    (C a : Polynomial R) %ₘ g = C a := by
  rw [Polynomial.modByMonic_eq_self_iff hg]
  refine lt_of_le_of_lt (Polynomial.degree_C_le) ?_
  rw [Polynomial.degree_eq_natDegree hg.ne_zero]
  exact_mod_cast hdeg

/-- **`w1`'s `towerToRdecK1` input has the trivial `(d0,d1) = (0,1)` normal
form.** `AdjoinRoot.modByMonicHom (K1_poly_monic ...) (w1 ...)` unfolds via
`w1 = AdjoinRoot.root (K1's defining quadratic) = AdjoinRoot.mk _ X`
(`AdjoinRoot.mk_X`, the "image of `X`" description of `root`), then
`AdjoinRoot.modByMonicHom_mk` reduces the whole expression to `X %ₘ (K1's
defining quadratic)`, which `X_modByMonic_eq_self_of_natDegree_eq_two`
(quadratic, degree `2 > 1 = X.degree`) collapses to `X` itself — so
`.coeff 0 = 0`, `.coeff 1 = 1` via `Polynomial.coeff_X_zero`/`coeff_X_one`. -/
theorem w1_modByMonicHom_eq_X (c0 c1 c2 c3 c4 : F p) :
    (AdjoinRoot.modByMonicHom (K1_poly_monic p c0 c1 c2 c3 c4)
      (w1 p c0 c1 c2 c3 c4) : Polynomial (K0 p)) = X := by
  have hroot : w1 p c0 c1 c2 c3 c4 =
      AdjoinRoot.mk (X ^ 2 - C (fAtT p c0 c1 c2 c3 c4 0) : Polynomial (K0 p)) X := by
    unfold w1
    rw [← AdjoinRoot.mk_X]
  rw [hroot, AdjoinRoot.modByMonicHom_mk]
  exact X_modByMonic_eq_self_of_natDegree_eq_two (K1_poly_monic p c0 c1 c2 c3 c4)
    (by rw [Polynomial.natDegree_X_pow_sub_C])

/-- **Companion for `w2`, `K2`-level.** Identical shape/proof to `w1_
modByMonicHom_eq_X`, one tower level up (`K2_poly_monic` in place of `K1_
poly_monic`, `w2` in place of `w1`). -/
theorem w2_modByMonicHom_eq_X (c0 c1 c2 c3 c4 : F p) :
    (AdjoinRoot.modByMonicHom (K2_poly_monic p c0 c1 c2 c3 c4)
      (w2 p c0 c1 c2 c3 c4) : Polynomial (K1 p c0 c1 c2 c3 c4)) = X := by
  have hroot : w2 p c0 c1 c2 c3 c4 =
      AdjoinRoot.mk (X ^ 2 - C (algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4)
        (fAtT p c0 c1 c2 c3 c4 1)) : Polynomial (K1 p c0 c1 c2 c3 c4)) X := by
    unfold w2
    rw [← AdjoinRoot.mk_X]
  rw [hroot, AdjoinRoot.modByMonicHom_mk]
  exact X_modByMonic_eq_self_of_natDegree_eq_two (K2_poly_monic p c0 c1 c2 c3 c4)
    (by rw [Polynomial.natDegree_X_pow_sub_C])

/-- **`baseFracToRing`'s totalDegree bound at the trivial inputs `0`/`1 :
K0 p`.** `IsFractionRing.num`/`.den` of `0` is `(0,1)` (`num_zero`/
`den_zero`-style facts — `0 = mk' _ 0 1`), and of `1` is `(1,1)` — both
immediate special cases of `baseFracToRing_totalDegree_le` with `a := 0`/`b
:= 1` resp. `a := 1, b := 1`, EXCEPT `baseFracToRing_totalDegree_le` requires
`a ≠ 0`, which fails for the `v = 0` case. Handled directly instead: `.1 =
aeval _ (IsFractionRing.num _ 0)`, and `IsFractionRing.num _ 0 = 0`
(`IsLocalization.mk'_zero`-chain — `0 = mk' _ 0 1` combined with `num_den`'s
uniqueness, or more simply `map_zero`-style: `baseFracToRing` is built from
`aeval`, which sends `0 ↦ 0`, so it suffices that `num (0:K0 p) = 0`, itself
from `IsFractionRing.num_zero` if present, else from `0 = algebraMap _ _ 0`
and `IsFractionRing.num_algebraMap`-style simp set). `totalDegree 0 = 0` in
either branch, so both `≤ D` for ANY `D`, including `D := 0`. -/
theorem baseFracToRing_zero_one_totalDegree_eq_zero {Vars : Type*} (sg : SideGens Vars) :
    (baseFracToRing p sg (0 : K0 p)).1.totalDegree = 0 ∧
    (baseFracToRing p sg (0 : K0 p)).2.totalDegree = 0 ∧
    (baseFracToRing p sg (1 : K0 p)).1.totalDegree = 0 ∧
    (baseFracToRing p sg (1 : K0 p)).2.totalDegree = 0 := by
  -- `num (0 : K0 p) = 0` directly (`IsFractionRing.num_zero`, confirmed
  -- Mathlib name) — sidesteps needing `baseFracToRing_totalDegree_le`'s
  -- `a ≠ 0` hypothesis, which genuinely fails for `v = 0`.
  have hnum0 : IsFractionRing.num (MvPolynomial (Fin 2) (F p)) (0 : K0 p) = 0 :=
    IsFractionRing.num_zero (A := MvPolynomial (Fin 2) (F p)) (K := K0 p)
  -- `den (0 : K0 p)`: from `numDen_cross_mul` at `v := 0`, `a := 0`, `b := 1`
  -- (`0 = mk' (K0 p) 0 1`, via the same `mk'_spec'` pattern as `fAtT_eq_mk'_
  -- one` above): `0 * den (0:K0 p) = num (0:K0 p) * 1`, i.e. `0 = num (0:K0
  -- p)` — already known (`hnum0`) and gives no information on `den` this
  -- way, so `den`'s bound is taken instead from `isFractionRing_den_
  -- totalDegree_le` directly, which needs no `a ≠ 0` hypothesis at all
  -- (only `hb : b ≠ 0`, satisfied by `b := 1`).
  have hv0mk : (0 : K0 p) = IsLocalization.mk' (K0 p) (0 : MvPolynomial (Fin 2) (F p))
      ⟨1, mem_nonZeroDivisors_of_ne_zero one_ne_zero⟩ := by
    have hspec := IsLocalization.mk'_spec' (K0 p) (0 : MvPolynomial (Fin 2) (F p))
      (⟨1, mem_nonZeroDivisors_of_ne_zero one_ne_zero⟩ :
        ↥(nonZeroDivisors (MvPolynomial (Fin 2) (F p))))
    -- `hspec : algebraMap _ (K0 p) ↑1 * mk' (K0 p) 0 1 = algebraMap _ (K0 p) 0`
    -- i.e. `1 * mk' (K0 p) 0 1 = 0`, so `mk' (K0 p) 0 1 = 0`.
    simp only [map_one, map_zero, one_mul] at hspec
    rw [hspec]
  have hv1mk : (1 : K0 p) = IsLocalization.mk' (K0 p) (1 : MvPolynomial (Fin 2) (F p))
      ⟨1, mem_nonZeroDivisors_of_ne_zero one_ne_zero⟩ := by
    have hspec := IsLocalization.mk'_spec' (K0 p) (1 : MvPolynomial (Fin 2) (F p))
      (⟨1, mem_nonZeroDivisors_of_ne_zero one_ne_zero⟩ :
        ↥(nonZeroDivisors (MvPolynomial (Fin 2) (F p))))
    simp only [map_one, one_mul] at hspec
    rw [← hspec]
  have hden0 : (↑(IsFractionRing.den (MvPolynomial (Fin 2) (F p)) (0 : K0 p)) :
      MvPolynomial (Fin 2) (F p)).totalDegree = 0 := by
    have hle := isFractionRing_den_totalDegree_le p (a := (0 : MvPolynomial (Fin 2) (F p)))
      (b := (1 : MvPolynomial (Fin 2) (F p))) one_ne_zero hv0mk
    have : (1 : MvPolynomial (Fin 2) (F p)).totalDegree = 0 := MvPolynomial.totalDegree_one
    omega
  have hnum1 : (IsFractionRing.num (MvPolynomial (Fin 2) (F p)) (1 : K0 p)).totalDegree = 0 := by
    have hle := isFractionRing_num_totalDegree_le p (a := (1 : MvPolynomial (Fin 2) (F p)))
      (b := (1 : MvPolynomial (Fin 2) (F p))) one_ne_zero hv1mk one_ne_zero
    have : (1 : MvPolynomial (Fin 2) (F p)).totalDegree = 0 := MvPolynomial.totalDegree_one
    omega
  have hden1 : (↑(IsFractionRing.den (MvPolynomial (Fin 2) (F p)) (1 : K0 p)) :
      MvPolynomial (Fin 2) (F p)).totalDegree = 0 := by
    have hle := isFractionRing_den_totalDegree_le p (a := (1 : MvPolynomial (Fin 2) (F p)))
      (b := (1 : MvPolynomial (Fin 2) (F p))) one_ne_zero hv1mk
    have : (1 : MvPolynomial (Fin 2) (F p)).totalDegree = 0 := MvPolynomial.totalDegree_one
    omega
  simp only [baseFracToRing]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hnum0]; simp
  · have hle := aeval_X_comp_totalDegree_le p sg.tGen
      (↑(IsFractionRing.den (MvPolynomial (Fin 2) (F p)) (0 : K0 p)) :
        MvPolynomial (Fin 2) (F p))
    omega
  · have hle := aeval_X_comp_totalDegree_le p sg.tGen
      (IsFractionRing.num (MvPolynomial (Fin 2) (F p)) (1 : K0 p))
    omega
  · have hle := aeval_X_comp_totalDegree_le p sg.tGen
      (↑(IsFractionRing.den (MvPolynomial (Fin 2) (F p)) (1 : K0 p)) :
        MvPolynomial (Fin 2) (F p))
    omega

/-- **`w1`'s `towerToRdecK1` image has `totalDegree ≤ 1` on both coordinates**
— i.e. `w1` satisfies `towerToRdecK1_totalDegree_le`'s hypothesis with `D :=
0` (the two `baseFracToRing` calls on `w1`'s `(d0,d1) = (0,1)` normal form
are BOTH `totalDegree 0`, per `baseFracToRing_zero_one_totalDegree_eq_zero`),
giving `towerToRdecK1 p sg (w1 ...)` itself `totalDegree ≤ 2*0+1 = 1` /
`≤ 2*0 = 0`. This is the base-case bound `matrixA`/`rhsVec`'s `w1`-dependence
needs. -/
theorem towerToRdecK1_w1_totalDegree_le {Vars : Type*} (sg : SideGens Vars)
    (c0 c1 c2 c3 c4 : F p) :
    (towerToRdecK1 p sg (w1 p c0 c1 c2 c3 c4)).1.totalDegree ≤ 1 ∧
    (towerToRdecK1 p sg (w1 p c0 c1 c2 c3 c4)).2.totalDegree ≤ 0 := by
  have hw1 := w1_modByMonicHom_eq_X p c0 c1 c2 c3 c4
  have hzero := baseFracToRing_zero_one_totalDegree_eq_zero p sg
  have h : (baseFracToRing p sg
          ((AdjoinRoot.modByMonicHom (K1_poly_monic p c0 c1 c2 c3 c4)
            (w1 p c0 c1 c2 c3 c4) : Polynomial (K0 p)).coeff 0)).1.totalDegree ≤ 0 ∧
      (baseFracToRing p sg
          ((AdjoinRoot.modByMonicHom (K1_poly_monic p c0 c1 c2 c3 c4)
            (w1 p c0 c1 c2 c3 c4) : Polynomial (K0 p)).coeff 0)).2.totalDegree ≤ 0 ∧
      (baseFracToRing p sg
          ((AdjoinRoot.modByMonicHom (K1_poly_monic p c0 c1 c2 c3 c4)
            (w1 p c0 c1 c2 c3 c4) : Polynomial (K0 p)).coeff 1)).1.totalDegree ≤ 0 ∧
      (baseFracToRing p sg
          ((AdjoinRoot.modByMonicHom (K1_poly_monic p c0 c1 c2 c3 c4)
            (w1 p c0 c1 c2 c3 c4) : Polynomial (K0 p)).coeff 1)).2.totalDegree ≤ 0 := by
    rw [hw1, Polynomial.coeff_X_zero, Polynomial.coeff_X_one]
    exact ⟨hzero.1.le, hzero.2.1.le, hzero.2.2.1.le, hzero.2.2.2.le⟩
  have := towerToRdecK1_totalDegree_le p c0 c1 c2 c3 c4 sg (w1 p c0 c1 c2 c3 c4) h
  omega

/-- **`w2`'s companion, `K2`-level.** Identical shape to `towerToRdecK1_w1_
totalDegree_le`, one level up: `towerToRdec p sg (w2 ...)` has `totalDegree ≤
1` / `≤ 0`, via `w2_modByMonicHom_eq_X` and `towerToRdec_totalDegree_le`
(rather than `towerToRdecK1_totalDegree_le`) — but note the hypothesis
`towerToRdec_totalDegree_le` needs is stated in terms of `towerToRdecK1`'s
OUTPUT (not `baseFracToRing`'s, one level down from `w1`'s case), so this
uses `towerToRdecK1_w1_totalDegree_le`-STYLE bounds on `d0 = 0`/`d1 = 1 : K1 p
...` directly — `0`/`1 : K1 p ...` reduce via `AdjoinRoot.modByMonicHom`
applied to `algebraMap`-images of `0`/`1 : K0 p` (`K1`'s `0`/`1` ARE the
images of `K0`'s, by the `Algebra` structure), so the same `baseFracToRing_
zero_one_totalDegree_eq_zero`-style zero/one bound applies after one more
unfolding step: `towerToRdecK1 p sg (0 : K1 p ...)`/`(1 : K1 p ...)` both
have `totalDegree ≤ 1`/`≤ 0` by the SAME argument as `baseFracToRing`'s
zero/one case, one recursion level up (`towerToRdecK1`'s own `combine_
totalDegree_le` applied to two zero-totalDegree `baseFracToRing` outputs is
itself zero/one-bounded, matching `combine_totalDegree_le` at `D := 0`). -/
theorem towerToRdecK1_zero_one_totalDegree_le {Vars : Type*} (sg : SideGens Vars)
    (c0 c1 c2 c3 c4 : F p) :
    (towerToRdecK1 p sg (0 : K1 p c0 c1 c2 c3 c4)).1.totalDegree ≤ 1 ∧
    (towerToRdecK1 p sg (0 : K1 p c0 c1 c2 c3 c4)).2.totalDegree ≤ 0 ∧
    (towerToRdecK1 p sg (1 : K1 p c0 c1 c2 c3 c4)).1.totalDegree ≤ 1 ∧
    (towerToRdecK1 p sg (1 : K1 p c0 c1 c2 c3 c4)).2.totalDegree ≤ 0 := by
  have hzero := baseFracToRing_zero_one_totalDegree_eq_zero p sg
  have hposdeg : 0 <
      (X ^ 2 - C (fAtT p c0 c1 c2 c3 c4 0) : Polynomial (K0 p)).natDegree := by
    rw [Polynomial.natDegree_X_pow_sub_C]; norm_num
  have h0 : (AdjoinRoot.modByMonicHom (K1_poly_monic p c0 c1 c2 c3 c4)
      (0 : K1 p c0 c1 c2 c3 c4) : Polynomial (K0 p)) = 0 := by
    have hmk0 : (0 : K1 p c0 c1 c2 c3 c4) =
        AdjoinRoot.mk (X ^ 2 - C (fAtT p c0 c1 c2 c3 c4 0) : Polynomial (K0 p)) (C 0) := by
      rw [Polynomial.C_0, map_zero]
    rw [hmk0, AdjoinRoot.modByMonicHom_mk,
      C_modByMonic_eq_self_of_natDegree_pos (K1_poly_monic p c0 c1 c2 c3 c4) hposdeg,
      Polynomial.C_0]
  have h1 : (AdjoinRoot.modByMonicHom (K1_poly_monic p c0 c1 c2 c3 c4)
      (1 : K1 p c0 c1 c2 c3 c4) : Polynomial (K0 p)) = 1 := by
    have hmk1 : (1 : K1 p c0 c1 c2 c3 c4) =
        AdjoinRoot.mk (X ^ 2 - C (fAtT p c0 c1 c2 c3 c4 0) : Polynomial (K0 p)) (C 1) := by
      rw [Polynomial.C_1, map_one]
    rw [hmk1, AdjoinRoot.modByMonicHom_mk,
      C_modByMonic_eq_self_of_natDegree_pos (K1_poly_monic p c0 c1 c2 c3 c4) hposdeg,
      Polynomial.C_1]
  -- `D := 0` case for `v = 0 : K1 p ...`: both `coeff 0` and `coeff 1` extractions of the
  -- zero polynomial (`h0`) reduce to `baseFracToRing p sg (0 : K0 p)`, already bounded by
  -- `hzero`. Stated with an explicit type ascription (matching `towerToRdecK1_w1_
  -- totalDegree_le`'s own pattern above) so the implicit `D` is pinned to `0` before the
  -- `by` proof is elaborated, rather than left as an unconstrained metavariable.
  have h0bound : (baseFracToRing p sg
        ((AdjoinRoot.modByMonicHom (K1_poly_monic p c0 c1 c2 c3 c4)
          (0 : K1 p c0 c1 c2 c3 c4) : Polynomial (K0 p)).coeff 0)).1.totalDegree ≤ 0 ∧
      (baseFracToRing p sg
        ((AdjoinRoot.modByMonicHom (K1_poly_monic p c0 c1 c2 c3 c4)
          (0 : K1 p c0 c1 c2 c3 c4) : Polynomial (K0 p)).coeff 0)).2.totalDegree ≤ 0 ∧
      (baseFracToRing p sg
        ((AdjoinRoot.modByMonicHom (K1_poly_monic p c0 c1 c2 c3 c4)
          (0 : K1 p c0 c1 c2 c3 c4) : Polynomial (K0 p)).coeff 1)).1.totalDegree ≤ 0 ∧
      (baseFracToRing p sg
        ((AdjoinRoot.modByMonicHom (K1_poly_monic p c0 c1 c2 c3 c4)
          (0 : K1 p c0 c1 c2 c3 c4) : Polynomial (K0 p)).coeff 1)).2.totalDegree ≤ 0 := by
    rw [h0]; simp [hzero.1, hzero.2.1]
  have h1bound : (baseFracToRing p sg
        ((AdjoinRoot.modByMonicHom (K1_poly_monic p c0 c1 c2 c3 c4)
          (1 : K1 p c0 c1 c2 c3 c4) : Polynomial (K0 p)).coeff 0)).1.totalDegree ≤ 0 ∧
      (baseFracToRing p sg
        ((AdjoinRoot.modByMonicHom (K1_poly_monic p c0 c1 c2 c3 c4)
          (1 : K1 p c0 c1 c2 c3 c4) : Polynomial (K0 p)).coeff 0)).2.totalDegree ≤ 0 ∧
      (baseFracToRing p sg
        ((AdjoinRoot.modByMonicHom (K1_poly_monic p c0 c1 c2 c3 c4)
          (1 : K1 p c0 c1 c2 c3 c4) : Polynomial (K0 p)).coeff 1)).1.totalDegree ≤ 0 ∧
      (baseFracToRing p sg
        ((AdjoinRoot.modByMonicHom (K1_poly_monic p c0 c1 c2 c3 c4)
          (1 : K1 p c0 c1 c2 c3 c4) : Polynomial (K0 p)).coeff 1)).2.totalDegree ≤ 0 := by
    rw [h1]; simp [Polynomial.coeff_one, hzero.1, hzero.2.1, hzero.2.2.1, hzero.2.2.2]
  have hbound0 :=
    towerToRdecK1_totalDegree_le p c0 c1 c2 c3 c4 sg (0 : K1 p c0 c1 c2 c3 c4) h0bound
  have hbound1 :=
    towerToRdecK1_totalDegree_le p c0 c1 c2 c3 c4 sg (1 : K1 p c0 c1 c2 c3 c4) h1bound
  exact ⟨hbound0.1, hbound0.2, hbound1.1, hbound1.2⟩

/-! ## `t0`/anchor-point bound: generalizing `towerToRdecK1_zero_one_totalDegree_le`

`towerToRdecK1_zero_one_totalDegree_le` only handles `v ∈ {0,1} : K1 p ...`. The
anchor points `t1 := (anchor1 p ...).1`/`t2 := (anchor2 p ...).1`
(`DataDerivationSolve.lean`) are neither: both are `algebraMap (K1 p ...) (K2 p ...)
(algebraMap (K0 p) (K1 p ...) (t0 p i))` for `i ∈ {0,1}` — a genuine base-field
generator (`t0 p i = algebraMap (MvPolynomial (Fin 2) (F p)) (K0 p) (X i)`, per
`DataDerivationTower.lean`), lifted up through the tower, not `0`/`1` themselves.
This section closes that gap one tower level at a time: first the generic fact that
ANY `algebraMap (K0 p) (K1 p ...) v`'s `modByMonicHom`-normal-form is the constant
polynomial `C v` (of which `h0`/`h1` above, at `v = 0`/`1`, were special cases), then
the resulting `towerToRdecK1`-level bound for arbitrary `v`, then `t0 p i`'s own
base-case bound via `baseFracToRing_totalDegree_le`. The analogous `K1 → K2` step
(needed to reach `t1`/`t2` themselves, one level up) is flagged but not done this
pass — see the status note below. -/

/-- **`algebraMap`'s normal form is the constant polynomial.** Generalizes `h0`/`h1`
inside `towerToRdecK1_zero_one_totalDegree_le` above (which show this at the
specific values `v = 0`/`1`) to an arbitrary `v : K0 p`. Route: `algebraMap R A r =
r • 1` (`Algebra.algebraMap_eq_smul_one`), `AdjoinRoot.modByMonicHom hg` is an
`R`-linear map (so commutes with the `K0 p`-scalar action, `map_smul`), and
`modByMonicHom hg 1 = 1` reduces `v • modByMonicHom hg 1` to `v • (1 : Polynomial
(K0 p)) = C v` (`Polynomial.smul_eq_C_mul`, `mul_one`). No new mathematics over
`h0`/`h1`'s own proof, just replacing the concrete `0`/`1` with a variable `v`. -/
theorem modByMonicHom_algebraMap_eq_C (c0 c1 c2 c3 c4 : F p) (v : K0 p) :
    (AdjoinRoot.modByMonicHom (K1_poly_monic p c0 c1 c2 c3 c4)
      (algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4) v) : Polynomial (K0 p)) = C v := by
  have hposdeg : 0 <
      (X ^ 2 - C (fAtT p c0 c1 c2 c3 c4 0) : Polynomial (K0 p)).natDegree := by
    rw [Polynomial.natDegree_X_pow_sub_C]; norm_num
  have h1 : (AdjoinRoot.modByMonicHom (K1_poly_monic p c0 c1 c2 c3 c4)
      (1 : K1 p c0 c1 c2 c3 c4) : Polynomial (K0 p)) = 1 := by
    have hmk1 : (1 : K1 p c0 c1 c2 c3 c4) =
        AdjoinRoot.mk (X ^ 2 - C (fAtT p c0 c1 c2 c3 c4 0) : Polynomial (K0 p)) (C 1) := by
      rw [Polynomial.C_1, map_one]
    rw [hmk1, AdjoinRoot.modByMonicHom_mk,
      C_modByMonic_eq_self_of_natDegree_pos (K1_poly_monic p c0 c1 c2 c3 c4) hposdeg,
      Polynomial.C_1]
  rw [Algebra.algebraMap_eq_smul_one v, map_smul, h1, Polynomial.smul_eq_C_mul, mul_one]

/-- **`towerToRdecK1`'s bound at an `algebraMap`-lifted `v : K0 p`**, generalizing
`towerToRdecK1_zero_one_totalDegree_le` (`v ∈ {0,1}`, `D := 0`) to any `v` with a
known `baseFracToRing` bound `D`. `modByMonicHom_algebraMap_eq_C` pins the normal
form to `C v`, whose `coeff 0`/`coeff 1` are `v`/`0` (`Polynomial.coeff_C_zero`,
`Polynomial.coeff_eq_zero_of_natDegree_lt` off `natDegree_C`), feeding `hv`'s bound
and `baseFracToRing_zero_one_totalDegree_eq_zero`'s `v = 0` case respectively into
`towerToRdecK1_totalDegree_le`. -/
theorem towerToRdecK1_algebraMap_totalDegree_le {Vars : Type*} (sg : SideGens Vars)
    (c0 c1 c2 c3 c4 : F p) {D : ℕ} (v : K0 p)
    (hv : (baseFracToRing p sg v).1.totalDegree ≤ D ∧
      (baseFracToRing p sg v).2.totalDegree ≤ D) :
    (towerToRdecK1 p sg (algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4) v)).1.totalDegree ≤
      2 * D + 1 ∧
    (towerToRdecK1 p sg (algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4) v)).2.totalDegree ≤
      2 * D := by
  have hzero := baseFracToRing_zero_one_totalDegree_eq_zero p sg
  have heq := modByMonicHom_algebraMap_eq_C p c0 c1 c2 c3 c4 v
  have hc0 : (C v : Polynomial (K0 p)).coeff 0 = v := Polynomial.coeff_C_zero
  have hc1 : (C v : Polynomial (K0 p)).coeff 1 = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [Polynomial.natDegree_C]; norm_num)
  refine towerToRdecK1_totalDegree_le p c0 c1 c2 c3 c4 sg
    (algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4) v) ⟨?_, ?_, ?_, ?_⟩
  · rw [heq, hc0]; exact hv.1
  · rw [heq, hc0]; exact hv.2
  · rw [heq, hc1]; exact hzero.1.le.trans (Nat.zero_le D)
  · rw [heq, hc1]; exact hzero.2.1.le.trans (Nat.zero_le D)

/-- **`t0 p i`'s base-case bound.** `t0 p i := algebraMap (MvPolynomial (Fin 2)
(F p)) (K0 p) (X i)` (`DataDerivationTower.lean`) is exactly `mk' (K0 p) (X i) 1`
(`IsLocalization.mk'_spec'` at denominator `1`, the same pattern `fAtT_eq_mk'_one`
above uses, but simpler — `t0` IS the raw generator, no `eval₂` step), so
`baseFracToRing_totalDegree_le` applies directly with `a := X i`, `b := 1`:
`totalDegree (X i) = 1` (`MvPolynomial.totalDegree_X`), `totalDegree 1 = 0`
(`MvPolynomial.totalDegree_one`). -/
theorem t0_totalDegree_le {Vars : Type*} (sg : SideGens Vars) (i : Fin 2) :
    (baseFracToRing p sg (t0 p i)).1.totalDegree ≤ 1 ∧
    (baseFracToRing p sg (t0 p i)).2.totalDegree ≤ 0 := by
  have hv : t0 p i = IsLocalization.mk' (K0 p) (MvPolynomial.X i : MvPolynomial (Fin 2) (F p))
      ⟨1, mem_nonZeroDivisors_of_ne_zero (one_ne_zero)⟩ := by
    have hspec := IsLocalization.mk'_spec' (K0 p) (MvPolynomial.X i : MvPolynomial (Fin 2) (F p))
      (⟨1, mem_nonZeroDivisors_of_ne_zero (one_ne_zero)⟩ :
        ↥(nonZeroDivisors (MvPolynomial (Fin 2) (F p))))
    simp only [map_one, one_mul] at hspec
    unfold t0
    rw [← hspec]
  have hbound := baseFracToRing_totalDegree_le p sg (a := MvPolynomial.X i)
    (b := (1 : MvPolynomial (Fin 2) (F p))) one_ne_zero (MvPolynomial.X_ne_zero i) hv
  rwa [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_one] at hbound

/-! ## `K1 → K2` analog: reaching `t1`/`t2` themselves

One tower level up from the previous section. `anchor1.1`/`anchor2.1` (`t1`/`t2`,
`DataDerivationSolve.lean`) are each `algebraMap (K1 p ...) (K2 p ...) w` for `w`
itself an `algebraMap (K0 p) (K1 p ...) (t0 p i)` — so bounding `towerToRdec p sg
t1`/`t2` needs this section's `towerToRdec_algebraMap_totalDegree_le` applied on top
of the previous section's `towerToRdecK1_algebraMap_totalDegree_le`. The proof shape
is identical to the `K0 → K1` step (`modByMonicHom_algebraMap_eq_C`/
`towerToRdecK1_algebraMap_totalDegree_le`), with `K2_poly_monic`/`towerToRdec_
totalDegree_le` in place of `K1_poly_monic`/`towerToRdecK1_totalDegree_le` — EXCEPT
for the `1 ≤ D` side-hypothesis flagged in the previous status note, needed because
`towerToRdecK1 p sg (0 : K1 p ...)`'s own cost is `≤ 1`/`≤ 0` (`towerToRdecK1_zero_
one_totalDegree_le`'s `+1` structural offset from `combine_totalDegree_le`'s
`X (wGen 0)` term), not `≤ 0`/`≤ 0` the way `baseFracToRing p sg 0` is at the base
level — so `D` must be large enough to cover BOTH `w`'s own bound and this `≤ 1`
floor. -/

set_option maxHeartbeats 2000000 in
/-- **`algebraMap`'s normal form is the constant polynomial, one level up.**
Identical proof to `modByMonicHom_algebraMap_eq_C`, against `K2_poly_monic`/
`K1 p ... → K2 p ...` instead of `K1_poly_monic`/`K0 p → K1 p ...`. -/
theorem modByMonicHom_algebraMap_eq_C' (c0 c1 c2 c3 c4 : F p) (w : K1 p c0 c1 c2 c3 c4) :
    (AdjoinRoot.modByMonicHom (K2_poly_monic p c0 c1 c2 c3 c4)
      (algebraMap (K1 p c0 c1 c2 c3 c4) (K2 p c0 c1 c2 c3 c4) w) :
      Polynomial (K1 p c0 c1 c2 c3 c4)) = C w := by
  have hposdeg : 0 <
      (X ^ 2 - C (algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4) (fAtT p c0 c1 c2 c3 c4 1)) :
        Polynomial (K1 p c0 c1 c2 c3 c4)).natDegree := by
    rw [Polynomial.natDegree_X_pow_sub_C]; norm_num
  have h1 : (AdjoinRoot.modByMonicHom (K2_poly_monic p c0 c1 c2 c3 c4)
      (1 : K2 p c0 c1 c2 c3 c4) : Polynomial (K1 p c0 c1 c2 c3 c4)) = 1 := by
    have hmk1 : (1 : K2 p c0 c1 c2 c3 c4) =
        AdjoinRoot.mk (X ^ 2 - C (algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4)
            (fAtT p c0 c1 c2 c3 c4 1)) : Polynomial (K1 p c0 c1 c2 c3 c4)) (C 1) := by
      rw [Polynomial.C_1, map_one]
    rw [hmk1, AdjoinRoot.modByMonicHom_mk,
      C_modByMonic_eq_self_of_natDegree_pos (K2_poly_monic p c0 c1 c2 c3 c4) hposdeg,
      Polynomial.C_1]
  rw [Algebra.algebraMap_eq_smul_one w, map_smul, h1, Polynomial.smul_eq_C_mul, mul_one]

/-- **`towerToRdec`'s bound at an `algebraMap`-lifted `w : K1 p ...`**, generalizing
`towerToRdec_totalDegree_le` the same way `towerToRdecK1_algebraMap_totalDegree_le`
generalizes `towerToRdecK1_totalDegree_le`. The extra `hD : 1 ≤ D` hypothesis (absent
from the `K0 → K1` version) is exactly the side-condition flagged in the section
comment above: `D` has to dominate both `w`'s own bound (`hw`) and `towerToRdecK1
p sg (0 : K1 p ...)`'s fixed `≤ 1`/`≤ 0` cost (`towerToRdecK1_zero_one_totalDegree_
le`), so it cannot be taken smaller than `1` regardless of how good `hw` is. -/
theorem towerToRdec_algebraMap_totalDegree_le {Vars : Type*} (sg : SideGens Vars)
    (c0 c1 c2 c3 c4 : F p) {D : ℕ} (hD : 1 ≤ D) (w : K1 p c0 c1 c2 c3 c4)
    (hw : (towerToRdecK1 p sg w).1.totalDegree ≤ D ∧
      (towerToRdecK1 p sg w).2.totalDegree ≤ D) :
    (towerToRdec p sg
        (algebraMap (K1 p c0 c1 c2 c3 c4) (K2 p c0 c1 c2 c3 c4) w)).1.totalDegree ≤
      2 * D + 1 ∧
    (towerToRdec p sg
        (algebraMap (K1 p c0 c1 c2 c3 c4) (K2 p c0 c1 c2 c3 c4) w)).2.totalDegree ≤
      2 * D := by
  have hzero1 := towerToRdecK1_zero_one_totalDegree_le p sg c0 c1 c2 c3 c4
  have heq := modByMonicHom_algebraMap_eq_C' p c0 c1 c2 c3 c4 w
  have hc0 : (C w : Polynomial (K1 p c0 c1 c2 c3 c4)).coeff 0 = w := Polynomial.coeff_C_zero
  have hc1 : (C w : Polynomial (K1 p c0 c1 c2 c3 c4)).coeff 1 = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [Polynomial.natDegree_C]; norm_num)
  refine towerToRdec_totalDegree_le p c0 c1 c2 c3 c4 sg
    (algebraMap (K1 p c0 c1 c2 c3 c4) (K2 p c0 c1 c2 c3 c4) w) ⟨?_, ?_, ?_, ?_⟩
  · rw [heq, hc0]; exact hw.1
  · rw [heq, hc0]; exact hw.2
  · rw [heq, hc1]; exact hzero1.1.trans hD
  · rw [heq, hc1]; exact hzero1.2.1.trans (Nat.zero_le D)

/-- **`t1`/`t2` themselves.** Chains `t0_totalDegree_le` (base case, `i ∈ {0,1}`),
`towerToRdecK1_algebraMap_totalDegree_le` (`K0 → K1`, at `D := 1` since `t0 p i`'s
own bound is `≤ 1`/`≤ 0`, giving `towerToRdecK1`'s output `≤ 3`/`≤ 2`), and
`towerToRdec_algebraMap_totalDegree_le` (`K1 → K2`, at `D := 3` — dominates both the
`K0 → K1` step's `≤ 3`/`≤ 2` output and the required `1 ≤ D` floor) to bound
`towerToRdec p sg` applied to `algebraMap (K1 p ...) (K2 p ...) (algebraMap (K0 p)
(K1 p ...) (t0 p i))`, i.e. `anchor1.1`/`anchor2.1` unfolded (`anchor1`/`anchor2`,
`DataDerivationSolve.lean`) — the two anchor points' own promotion chain, verbatim. -/
theorem t0_promoted_totalDegree_le {Vars : Type*} (sg : SideGens Vars)
    (c0 c1 c2 c3 c4 : F p) (i : Fin 2) :
    (towerToRdec p sg
        (algebraMap (K1 p c0 c1 c2 c3 c4) (K2 p c0 c1 c2 c3 c4)
          (algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4) (t0 p i)))).1.totalDegree ≤ 7 ∧
    (towerToRdec p sg
        (algebraMap (K1 p c0 c1 c2 c3 c4) (K2 p c0 c1 c2 c3 c4)
          (algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4) (t0 p i)))).2.totalDegree ≤ 6 := by
  have h0 := t0_totalDegree_le p sg i
  have h1 := towerToRdecK1_algebraMap_totalDegree_le p sg c0 c1 c2 c3 c4 (t0 p i)
    ⟨h0.1, h0.2.trans (Nat.zero_le 1)⟩
  have h2 := towerToRdec_algebraMap_totalDegree_le p sg c0 c1 c2 c3 c4
    (D := 3) (by norm_num) (algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4) (t0 p i))
    ⟨h1.1, h1.2.trans (by norm_num)⟩
  exact h2

/-! ## Status, this section

**REPL-confirmed green this pass** (per report): every theorem in this file up
through `t0_totalDegree_le`, including the previously-flagged-as-unconfirmed
`X_modByMonic_eq_self_of_natDegree_eq_two`, `w1_modByMonicHom_eq_X`,
`w2_modByMonicHom_eq_X`, `baseFracToRing_zero_one_totalDegree_eq_zero`,
`towerToRdecK1_w1_totalDegree_le`, `towerToRdecK1_zero_one_totalDegree_le`,
`modByMonicHom_algebraMap_eq_C`, `towerToRdecK1_algebraMap_totalDegree_le`,
`t0_totalDegree_le` — the two risks flagged in earlier passes (the exact
Mathlib spelling of `baseFracToRing_zero_one_totalDegree_eq_zero`'s `simp` set
and `towerToRdecK1_zero_one_totalDegree_le`'s `h1`) were non-issues in practice.

**Drafted this pass, NOT yet REPL-confirmed**: `modByMonicHom_algebraMap_eq_C'`,
`towerToRdec_algebraMap_totalDegree_le`, `t0_promoted_totalDegree_le` (the
`K1 → K2` analog of the previous pass's `K0 → K1` step, flagged as the next
step in that pass's own status note). Same proof shape and same Mathlib names
as the already-confirmed `K0 → K1` versions, so risk should be low, but the
extra `1 ≤ D` side-hypothesis (`towerToRdec_algebraMap_totalDegree_le`'s `hD`)
is new machinery this pass hasn't seen a build for yet.

**What this section closes**: the previous pass's own flagged gap —
reaching `t1 := (anchor1 p ...).1`/`t2 := (anchor2 p ...).1` themselves, one
tower level above where `towerToRdecK1_algebraMap_totalDegree_le` stops.
`t0_promoted_totalDegree_le` bounds `towerToRdec p sg` applied to `t0 p i`'s
full two-step promotion (`algebraMap (K1 p ...) (K2 p ...) ∘ algebraMap (K0 p)
(K1 p ...)`) by `≤ 7`/`≤ 6` — and since `anchor1`/`anchor2`'s own definitions
(`DataDerivationSolve.lean`) show `(anchor1 p ...).1`/`(anchor2 p ...).1` ARE
exactly this promotion chain applied to `t0 p 0`/`t0 p 1` respectively, `t1`/
`t2`'s own `towerToRdec` bound is now `t0_promoted_totalDegree_le p sg c0 c1
c2 c3 c4 0`/`1` directly (not restated as separate `anchor1_totalDegree_le`/
`anchor2_totalDegree_le` theorems this pass, since that would just be an
`unfold anchor1/anchor2` away from what's already here — low-value busywork
until the next assembly step actually needs the `anchor1`/`anchor2` names in
scope).

**Added this pass, NOT yet REPL-confirmed**: `towerToRdec_w1_totalDegree_le`/
`towerToRdec_w2_totalDegree_le` — the `anchor1.2`/`anchor2.2` companions to
`t0_promoted_totalDegree_le`'s `anchor1.1`/`anchor2.1` bound, both `≤3`/`≤2`.
With these plus `t0_promoted_totalDegree_le`, all four of `anchor1`/`anchor2`'s
components now have an explicit `towerToRdec` bound — `matrixA`/`rhsVec`'s
`px`/`py` factors are fully covered.

**What this does NOT yet close**: raising `t1`/`t2` to powers `bi ≤ 3`
(`MvPolynomial.totalDegree_mul`/`_pow`, mechanical now that `t1`/`t2`'s own
bound is a proved theorem) and `reduceMonomialModU`'s `F p`-valued output
(`totalDegree 0` via `algebraMap`/`MvPolynomial.totalDegree_C`, immediate).
Assembling `matrixA`/`rhsVec`'s full entrywise bound, then feeding it through
`cramerRatioDet_num_totalDegree_le` to get `coeffsOut`'s bound, then through
`Epoly`/`Ypoly`/`Npoly`'s definitions to a concrete `Npoly` coefficient bound,
is the remaining assembly work — mechanical given everything now in this
file, but not yet written up as explicit theorems. The FINAL step (`Npoly`'s
bound ⟹ `curBeforeMonic`'s bound, via `Npoly_eq_curBeforeMonic_mul`'s exact
identity and a degree-SUBTRACTION argument on exact quotients) is genuinely
new territory — Mathlib has no ready-made "totalDegree of an exact
MvPolynomial-coefficient quotient" lemma, this is exactly the kind of
well-defined, non-curve-specific algebra fact this project's convention flags
as fair game for a ChatGPT consultation if a direct Mathlib search doesn't
turn up a shortcut quickly.

**REPL-confirmed green** (whole project build) — every "not yet REPL-
confirmed" marker earlier in this file's docstrings is stale as of this
note; build status, not proof content, is what changed. -/

end TheDataDerivation
end Genus2Lean
