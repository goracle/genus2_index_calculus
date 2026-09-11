import Mathlib
import Genus2Lean.ZeroD.DataDerivationTotalDegree

/-!
# `totalDegree` bounds on `matrixA`/`rhsVec`'s entries, at the `K2` level

New this pass. Per a ChatGPT consultation on how to bound `cramerSolution`'s
(`coeffsOut`'s, hence `Epoly`/`Ypoly`'s, hence `curBeforeMonic`'s) own
`totalDegree` after tower descent -- ChatGPT's proposed architecture is a
generic "raw algebraic complexity" (`HasWitness`) calculus over an arbitrary
tower expression, feeding into the ALREADY-PROVED `det_totalDegree_le`/
`cramerRatioDet_num_totalDegree_le` (`DataDerivationTotalDegree.lean`) -- both
of those already exist in this codebase and match ChatGPT's proposed
"determinant" and "Cramer ratio" modules closely (proved via the diagonal-
matrix `Δ_A·A.det=C.det` identity rather than ChatGPT's `det_mul_column`
route, but same shape/bound). **What was actually missing, and what this file
supplies, is narrower than ChatGPT's fully general calculus**: tracing
`matrixA`/`rhsVec`'s (`DataDerivationSolve.lean`) actual entries shows every
leaf feeding them is one of exactly three simple kinds, not an arbitrary deep
tower expression:

1. `t0 p i : K0 p` (`anchor1.1`/`anchor2.1`, algebraMap-lifted into `K2`) --
   literally `algebraMap _ (K0 p) (MvPolynomial.X i)`, i.e. `totalDegree 1`
   with denominator `1`.
2. `w1 p ...`/`w2 p ...` (`anchor1.2`/`anchor2.2`) -- the tower's OWN adjoined
   roots. Their `towerToRdecK1`/`towerToRdec` normal form is the TRIVIAL one
   (`AdjoinRoot.modByMonicHom` applied to `AdjoinRoot.root` itself reduces to
   `X`, i.e. `coeff 0 = 0, coeff 1 = 1`) -- proved below
   (`modByMonicHom_root_eq_X`), not assumed, closing the "needs checking"
   flag `ROADMAP-crossnondegenerate-degree-bound.md` left on this exact point.
3. `reduceMonomialModU`'s output (`DataDerivationBasics.lean`) -- bare `F p`
   values, `algebraMap`-lifted into `K2` in `rhsVec`; `totalDegree 0` at the
   `MvPolynomial` level before any lift, by `MvPolynomial.totalDegree_C`.

So rather than build ChatGPT's general `HasWitness` arithmetic calculus (add/
sub/mul/pow closure lemmas for arbitrary tower expressions), this file states
direct `towerToRdecK1`/`towerToRdec`-level bounds for exactly these three leaf
shapes, then composes them through `matrixA`/`rhsVec`'s own `if`-branching,
bounded-power formula (`px^bi * (if bj=1 then py else 1)`, `bi ≤ 4`) via
`totalDegree_mul`/`totalDegree_pow`/`totalDegree_finsetSum_le` -- the same
mechanical triangle-inequality style already used throughout
`DataDerivationTotalDegree.lean`, just one level shallower than the fully
general calculus ChatGPT sketched, since the actual leaves in THIS
construction don't need it.

**Not yet REPL-confirmed.** No build environment available this pass.
-/

namespace Genus2Lean
namespace TheDataDerivation

open Polynomial

variable (p : ℕ) [hp : Fact (Nat.Prime p)] [hp2 : Fact (p ≠ 2)]

/-! ## Leaf 1: `t0 p i`'s tower descent

`t0 p i := algebraMap (MvPolynomial (Fin 2) (F p)) (K0 p) (X i)` -- already
exactly the shape `fAtT_eq_mk'_one`/`curvePoly_eval_C_totalDegree_le` handle
for `fAtT`, just simpler (`X i` itself, `totalDegree 1`, rather than
`curvePoly` evaluated at `X i`, `totalDegree ≤ 5`). Stated directly rather
than routed through those two lemmas, since `t0`'s own `mk'`-shape is
simpler still (denominator literally `1`, not merely `≤ some bound`). -/

/-- **`t0 p i` as an explicit `IsLocalization.mk'` witness.** `t0 p i =
algebraMap _ (K0 p) (X i) = mk' (K0 p) (X i) 1` -- the same `mk'_spec'`
pattern `fAtT_eq_mk'_one` uses, one step simpler (no `curvePoly`/`eval₂`
in the way). -/
theorem t0_eq_mk'_one (i : Fin 2) :
    t0 p i = IsLocalization.mk' (K0 p) (MvPolynomial.X i : MvPolynomial (Fin 2) (F p))
      (1 : ↥(nonZeroDivisors (MvPolynomial (Fin 2) (F p)))) := by
  unfold t0
  have hspec := IsLocalization.mk'_spec' (K0 p) (MvPolynomial.X i : MvPolynomial (Fin 2) (F p))
    (1 : ↥(nonZeroDivisors (MvPolynomial (Fin 2) (F p))))
  simp only [OneMemClass.coe_one, map_one, one_mul] at hspec
  exact hspec.symm

/-! ## Leaf 2: `w1`/`w2`'s trivial tower normal form

The genuinely new fact this file supplies. -/

/-- **`AdjoinRoot.modByMonicHom` applied to `AdjoinRoot.root` itself reduces
to the bare polynomial `X`** -- i.e. the "genuinely new generator" case has
the TRIVIAL normal form, `coeff 0 = 0, coeff 1 = 1` (in the `{1,X}` basis),
exactly the fact `ROADMAP-crossnondegenerate-degree-bound.md` flagged as
"needs checking against `AdjoinRoot.modByMonicHom_mk`/`AdjoinRoot.root`'s
actual definition, not yet done" -- now done. Proof: `AdjoinRoot.root g =
AdjoinRoot.mk g X` (definitional/by `rfl`-adjacent unfolding -- `root` is
LITERALLY defined as `mk g X` in Mathlib), so `modByMonicHom hg (root g) =
modByMonicHom hg (mk g X) = X %ₘ g` by `modByMonicHom_mk`; since `g` is monic
of degree exactly 2 and `X.natDegree = 1 < 2`, `X %ₘ g = X` outright
(`Polynomial.modByMonic_eq_self_iff`/`natDegree_lt_iff`-style: a monic
divisor strictly bigger in degree than the dividend leaves it unchanged). -/
theorem modByMonicHom_root_eq_X {R : Type*} [CommRing R] [Nontrivial R] {g : Polynomial R}
    (hg : g.Monic) (hdeg : g.natDegree = 2) :
    AdjoinRoot.modByMonicHom hg (AdjoinRoot.root g) = X := by
  have hroot : AdjoinRoot.root g = AdjoinRoot.mk g X := rfl
  rw [hroot, AdjoinRoot.modByMonicHom_mk]
  refine (Polynomial.modByMonic_eq_self_iff hg).mpr ?_
  rw [Polynomial.degree_eq_natDegree hg.ne_zero, hdeg]
  calc (X : Polynomial R).degree ≤ (1 : ℕ) := Polynomial.degree_X_le
    _ < ((2 : ℕ) : WithBot ℕ) := by exact_mod_cast (by norm_num : (1:ℕ) < 2)


/-- **`w1`'s `towerToRdecK1` image is `(0, 1)`.** From
`modByMonicHom_root_eq_X` (applied to `K1_poly_monic`, degree 2 by
inspection of `X^2 - C _`'s definition), `d0 := (X).coeff 0 = 0`, `d1 :=
(X).coeff 1 = 1`. -/
theorem w1_modByMonicHom_coeff (c0 c1 c2 c3 c4 : F p) :
    (AdjoinRoot.modByMonicHom (K1_poly_monic p c0 c1 c2 c3 c4)
      (w1 p c0 c1 c2 c3 c4)).coeff 0 = 0 ∧
    (AdjoinRoot.modByMonicHom (K1_poly_monic p c0 c1 c2 c3 c4)
      (w1 p c0 c1 c2 c3 c4)).coeff 1 = 1 := by
  have hdeg2 : (X ^ 2 - C (fAtT p c0 c1 c2 c3 c4 0) : Polynomial (K0 p)).natDegree = 2 := by
    compute_degree!
  have heq := modByMonicHom_root_eq_X (K1_poly_monic p c0 c1 c2 c3 c4) hdeg2
  unfold w1 at *
  rw [heq]
  simp

/-- **`w2`'s `towerToRdec` image, one level up, same trivial shape.** Same
argument, `K2_poly_monic`/`w2` in place of `K1_poly_monic`/`w1`. -/
theorem w2_modByMonicHom_coeff (c0 c1 c2 c3 c4 : F p) :
    (AdjoinRoot.modByMonicHom (K2_poly_monic p c0 c1 c2 c3 c4)
      (w2 p c0 c1 c2 c3 c4)).coeff 0 = 0 ∧
    (AdjoinRoot.modByMonicHom (K2_poly_monic p c0 c1 c2 c3 c4)
      (w2 p c0 c1 c2 c3 c4)).coeff 1 = 1 := by
  have hdeg2 : (X ^ 2 - C (algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4)
      (fAtT p c0 c1 c2 c3 c4 1)) : Polynomial (K1 p c0 c1 c2 c3 c4)).natDegree = 2 := by
    compute_degree!
  have heq := modByMonicHom_root_eq_X (K2_poly_monic p c0 c1 c2 c3 c4) hdeg2
  unfold w2 at *
  rw [heq]
  simp

/-! ## Leaf 2, continued: `baseFracToRing`'s output on the trivial `K0`
values `0`/`1` -- needed to finish `w1`/`w2`'s tower descent

`w1_modByMonicHom_coeff`/`w2_modByMonicHom_coeff` give `d0 = 0, d1 = 1 : K0 p`
at `towerToRdecK1`'s first recursion step. To get `towerToRdecK1_totalDegree_le`'s
own hypothesis (a `totalDegree` bound on `baseFracToRing p sg d0`/`d1`), the
missing piece is bounding `baseFracToRing p sg 0` and `baseFracToRing p sg 1`
directly -- a genuinely separate case from `baseFracToRing_totalDegree_le`
above, since that theorem's proof needs `a ≠ 0` (the UFD `num v ∣ a`
divisibility argument is vacuous at `a = 0`), which fails exactly at `v = 0`.
Handled here as its own pair of small lemmas rather than forcing the general
theorem to cover a case its own proof structure can't reach. -/

/-- **`baseFracToRing p sg 0`'s `totalDegree` bound: `(0, ≤1)`.** `v = 0`'s
numerator is `0` outright (`IsFractionRing.num_zero`, Mathlib), so the first
component is trivially `totalDegree 0`. The denominator side still needs the
general cross-multiplication argument (`isFractionRing_den_totalDegree_le`
with the witness `a := 0, b := 1`), since `den v` need not be `1` merely
because `num v = 0` (only guaranteed to be *some* nonzero-divisor). -/
theorem baseFracToRing_zero_totalDegree_le {Vars : Type*} (sg : SideGens Vars) :
    (baseFracToRing p sg (0 : K0 p)).1.totalDegree ≤ 1 ∧
    (baseFracToRing p sg (0 : K0 p)).2.totalDegree ≤ 1 := by
  have hv0 : (0 : K0 p) = IsLocalization.mk' (K0 p)
      (0 : MvPolynomial (Fin 2) (F p))
      ⟨(1 : MvPolynomial (Fin 2) (F p)), mem_nonZeroDivisors_of_ne_zero one_ne_zero⟩ := by
    -- Same `mk'_spec'` pattern as `t0_eq_mk'_one`: `algebraMap _ _ ↑y * mk' K 0 y =
    -- algebraMap _ _ 0 = 0`; `algebraMap _ (K0 p) ↑(1:...) = 1 ≠ 0` in the field `K0 p`,
    -- so `mk' K0 0 y = 0` follows by cancelling a nonzero factor (`mul_eq_zero`).
    have hspec := IsLocalization.mk'_spec' (K0 p) (0 : MvPolynomial (Fin 2) (F p))
      (⟨(1 : MvPolynomial (Fin 2) (F p)), mem_nonZeroDivisors_of_ne_zero one_ne_zero⟩ :
        ↥(nonZeroDivisors (MvPolynomial (Fin 2) (F p))))
    simp only [map_zero, map_one, one_mul] at hspec
    exact hspec.symm
  have hnum : IsFractionRing.num (MvPolynomial (Fin 2) (F p)) (0 : K0 p) = 0 :=
    IsFractionRing.num_zero
  have hden := isFractionRing_den_totalDegree_le p (a := (0 : MvPolynomial (Fin 2) (F p)))
    (b := (1 : MvPolynomial (Fin 2) (F p))) one_ne_zero hv0
  constructor
  · have : (baseFracToRing p sg (0 : K0 p)).1 =
        MvPolynomial.aeval (fun i : Fin 2 => MvPolynomial.X (sg.tGen i))
          (IsFractionRing.num (MvPolynomial (Fin 2) (F p)) (0 : K0 p)) := rfl
    rw [this, hnum]
    simp
  · have hle := aeval_X_comp_totalDegree_le p sg.tGen
      (↑(IsFractionRing.den (MvPolynomial (Fin 2) (F p)) (0 : K0 p)) :
        MvPolynomial (Fin 2) (F p))
    have : (baseFracToRing p sg (0 : K0 p)).2 =
        MvPolynomial.aeval (fun i : Fin 2 => MvPolynomial.X (sg.tGen i))
          (↑(IsFractionRing.den (MvPolynomial (Fin 2) (F p)) (0 : K0 p)) :
            MvPolynomial (Fin 2) (F p)) := rfl
    rw [this]
    calc _ ≤ (↑(IsFractionRing.den (MvPolynomial (Fin 2) (F p)) (0 : K0 p)) :
          MvPolynomial (Fin 2) (F p)).totalDegree := hle
      _ ≤ (1 : MvPolynomial (Fin 2) (F p)).totalDegree := hden
      _ ≤ 1 := by simp

/-- **`baseFracToRing p sg 1`'s `totalDegree` bound: `(≤1, ≤1)`.** `v = 1`
via `mk' K0 1 1`, matching `t0_eq_mk'_one`'s pattern one step further (`a=1`
instead of `a=X i`) -- `a ≠ 0` holds here, so this DOES go through the
general `baseFracToRing_totalDegree_le` directly, no special-casing needed. -/
theorem baseFracToRing_one_totalDegree_le {Vars : Type*} (sg : SideGens Vars) :
    (baseFracToRing p sg (1 : K0 p)).1.totalDegree ≤ 1 ∧
    (baseFracToRing p sg (1 : K0 p)).2.totalDegree ≤ 1 := by
  have hv1 : (1 : K0 p) = IsLocalization.mk' (K0 p)
      (1 : MvPolynomial (Fin 2) (F p))
      ⟨(1 : MvPolynomial (Fin 2) (F p)), mem_nonZeroDivisors_of_ne_zero one_ne_zero⟩ := by
    -- Same `mk'_spec'` pattern as `hv0`/`t0_eq_mk'_one`, rather than assuming
    -- `IsLocalization.mk'_one`'s exact argument shape (it turned out not to unify
    -- directly against `mk' S 1 y`, so this sidesteps that guess entirely).
    have hspec := IsLocalization.mk'_spec' (K0 p) (1 : MvPolynomial (Fin 2) (F p))
      (⟨(1 : MvPolynomial (Fin 2) (F p)), mem_nonZeroDivisors_of_ne_zero one_ne_zero⟩ :
        ↥(nonZeroDivisors (MvPolynomial (Fin 2) (F p))))
    simp only [OneMemClass.coe_one, map_one, one_mul] at hspec
    exact hspec.symm
  have h := baseFracToRing_totalDegree_le p sg one_ne_zero one_ne_zero hv1
  refine ⟨le_trans h.1 ?_, le_trans h.2 ?_⟩ <;> simp

/-! ## Leaf 2, assembled: `w1`/`w2`'s own `towerToRdecK1`/`towerToRdec` bound

With `modByMonicHom_root_eq_X`'s two instances (`w1_modByMonicHom_coeff`/
`w2_modByMonicHom_coeff`, giving `d0=0, d1=1` at each level) and the two
trivial-value `baseFracToRing` bounds just above (`D=1` for both `v=0` and
`v=1`), `combine_totalDegree_le` closes `w1`'s `towerToRdecK1` image and
`w2`'s `towerToRdec` image directly -- completing leaf 2 end to end (the
"not yet assembled" gap this file's own status note flagged after the leaf
facts alone). -/

/-- **`w1`'s own `towerToRdecK1 p aSideGens` image has `totalDegree ≤ 3`
(num) `/ ≤ 2` (den).** Direct application of `combine_totalDegree_le` at
`D=1`, fed by `w1_modByMonicHom_coeff`'s `(d0,d1)=(0,1)` split and the two
trivial-value `baseFracToRing` bounds. `sg` is left as an arbitrary
`SideGens Idx` argument (not hardcoded to `aSideGens`) since `w1`'s
`towerToRdecK1` image is used on both the a-side and b-side of the
construction (via `anchor1`/`anchor2` on each sample) -- matching this
file's other leaf theorems, which are similarly `sg`-generic. -/
theorem w1_towerToRdecK1_totalDegree_le {Vars : Type*} (sg : SideGens Vars)
    (c0 c1 c2 c3 c4 : F p) :
    (towerToRdecK1 p sg (w1 p c0 c1 c2 c3 c4)).1.totalDegree ≤ 3 ∧
    (towerToRdecK1 p sg (w1 p c0 c1 c2 c3 c4)).2.totalDegree ≤ 2 := by
  have hcoeff := w1_modByMonicHom_coeff p c0 c1 c2 c3 c4
  have h0 := baseFracToRing_zero_totalDegree_le p sg
  have h1 := baseFracToRing_one_totalDegree_le p sg
  unfold towerToRdecK1
  simp only [hcoeff.1, hcoeff.2]
  exact combine_totalDegree_le p (sg.wGen 0) h0.1 h0.2 h1.1 h1.2

/-- **`towerToRdecK1 p sg 0`'s bound: `(0, ≤1)`.** The `K1`-level analogue of
`baseFracToRing_zero_totalDegree_le`, needed for `w2`'s recursion (`w2`'s
`(d0,d1)=(0,1)` are `K1`-valued, one level above `w1`'s `K0`-valued split).
`modByMonicHom (K1_poly_monic ...) 0 = 0` (`map_zero`), so both `coeff 0`
and `coeff 1` of the zero polynomial are `0 : K0 p`, landing back on
`baseFracToRing_zero_totalDegree_le` (both slots, not one `0`/one `1` the
way `w1` itself split) via `combine_totalDegree_le` at `D=1`. -/
theorem towerToRdecK1_zero_totalDegree_le {Vars : Type*} (sg : SideGens Vars)
    (c0 c1 c2 c3 c4 : F p) :
    (towerToRdecK1 p sg (0 : K1 p c0 c1 c2 c3 c4)).1.totalDegree ≤ 3 ∧
    (towerToRdecK1 p sg (0 : K1 p c0 c1 c2 c3 c4)).2.totalDegree ≤ 2 := by
  have h0 := baseFracToRing_zero_totalDegree_le p sg
  unfold towerToRdecK1
  simp only [map_zero, Polynomial.coeff_zero]
  exact combine_totalDegree_le p (sg.wGen 0) h0.1 h0.2 h0.1 h0.2

/-- **`towerToRdecK1 p sg 1`'s bound.** `modByMonicHom (K1_poly_monic ...) 1`
-- unlike the `0` case, this does NOT reduce to `1` outright in general (a
monic-mod-reduction of the constant polynomial `1` stays `1` only when the
divisor's degree is `> 0`, which `K1_poly_monic` satisfies, degree `2`) --
`Polynomial.modByMonic_eq_self_iff`-style reasoning, same shape as
`modByMonicHom_root_eq_X` itself but for the constant polynomial `C 1 = 1`
in place of `X`. States the needed fact directly via `map_one` +
`AdjoinRoot.modByMonicHom_mk`... **flagged, not yet proved cleanly**: unlike
`0`, `AdjoinRoot.mk g 1`'s `modByMonicHom` normal form needs its own small
argument (`(1 : Polynomial R).degree = 0 < g.degree` when `g.natDegree ≥
1`), stated inline below rather than via a separate named lemma, since it's
only needed here. -/
theorem towerToRdecK1_one_totalDegree_le {Vars : Type*} (sg : SideGens Vars)
    (c0 c1 c2 c3 c4 : F p) :
    (towerToRdecK1 p sg (1 : K1 p c0 c1 c2 c3 c4)).1.totalDegree ≤ 3 ∧
    (towerToRdecK1 p sg (1 : K1 p c0 c1 c2 c3 c4)).2.totalDegree ≤ 2 := by
  have h0 := baseFracToRing_zero_totalDegree_le p sg
  have h1 := baseFracToRing_one_totalDegree_le p sg
  -- `K1 p c0 c1 c2 c3 c4 := AdjoinRoot (X^2 - C (fAtT p c0 c1 c2 c3 c4 0))`
  -- (`DataDerivationTower.lean`'s own definition) -- referencing the
  -- underlying monic polynomial directly here, the same object
  -- `K1_poly_monic p c0 c1 c2 c3 c4` is a `.Monic` proof OF, rather than
  -- guessing a `.1`/`.2` projection on `K1_poly_monic` itself (it is a
  -- `Prop`-valued proof term, not a polynomial/degree pair).
  have hone : (AdjoinRoot.modByMonicHom (K1_poly_monic p c0 c1 c2 c3 c4)
      (1 : K1 p c0 c1 c2 c3 c4) : Polynomial (K0 p)) = 1 := by
    have h1eq : (1 : K1 p c0 c1 c2 c3 c4) =
        AdjoinRoot.mk (X ^ 2 - C (fAtT p c0 c1 c2 c3 c4 0) : Polynomial (K0 p)) 1 :=
      (map_one (AdjoinRoot.mk
        (X ^ 2 - C (fAtT p c0 c1 c2 c3 c4 0) : Polynomial (K0 p)))).symm
    rw [h1eq, AdjoinRoot.modByMonicHom_mk]
    refine (Polynomial.modByMonic_eq_self_iff (K1_poly_monic p c0 c1 c2 c3 c4)).mpr ?_
    calc (1 : Polynomial (K0 p)).degree = 0 := Polynomial.degree_one
      _ < 2 := by norm_num
      _ = (X ^ 2 - C (fAtT p c0 c1 c2 c3 c4 0) : Polynomial (K0 p)).degree := by
          rw [Polynomial.degree_eq_natDegree (K1_poly_monic p c0 c1 c2 c3 c4).ne_zero]
          have : (X ^ 2 - C (fAtT p c0 c1 c2 c3 c4 0) : Polynomial (K0 p)).natDegree = 2 := by
            compute_degree!
          rw [this]
          norm_cast
  unfold towerToRdecK1
  simp only [hone, Polynomial.coeff_one, if_neg (one_ne_zero (α := ℕ))]
  exact combine_totalDegree_le p (sg.wGen 0) h1.1 h1.2 h0.1 h0.2

/-- **`w2`'s own `towerToRdec p aSideGens` image, one level up.** `w2 : K2 p
...`, so its `modByMonicHom` normal form (via `K2_poly_monic`) gives
`(d0,d1) = (0,1) : K1 p ...` -- ONE LEVEL HIGHER than `w1`'s `(d0,d1) : K0 p
...` split, so `towerToRdec`'s own recursion calls `towerToRdecK1 p sg`
(NOT `baseFracToRing` directly -- `towerToRdec`'s definition recurses via
`towerToRdecK1`, confirmed against its actual `let`-body). This needs
`towerToRdecK1`'s own image at the trivial values `0`/`1 : K1 p ...`, which
in turn bottom out at the SAME `baseFracToRing_zero/one_totalDegree_le`
bounds via `modByMonicHom_root_eq_X`-style reasoning one level down -- but
`w2`'s `(0,1)` values are elements of `K1 p ...` directly (not obtained via
another `AdjoinRoot.root`), so `towerToRdecK1`'s own internal
`modByMonicHom (K1_poly_monic ...)` must be evaluated AT `0`/`1 : K1 p ...`
themselves, which is a different (easier, no root machinery needed) fact
than `w1_towerToRdecK1_totalDegree_le` -- not yet stated. Flagged rather
than guessed at: this theorem is NOT proved by naively reusing
`baseFracToRing`'s bounds the way `w1`'s version did, since the recursion
level doesn't match. See the two new `towerToRdecK1`-at-`0`/`1` lemmas
below, which this theorem actually depends on. -/
theorem w2_towerToRdec_totalDegree_le {Vars : Type*} (sg : SideGens Vars)
    (c0 c1 c2 c3 c4 : F p) :
    (towerToRdec p sg (w2 p c0 c1 c2 c3 c4)).1.totalDegree ≤ 7 ∧
    (towerToRdec p sg (w2 p c0 c1 c2 c3 c4)).2.totalDegree ≤ 6 := by
  have hcoeff := w2_modByMonicHom_coeff p c0 c1 c2 c3 c4
  have h0 := towerToRdecK1_zero_totalDegree_le p sg c0 c1 c2 c3 c4
  have h1 := towerToRdecK1_one_totalDegree_le p sg c0 c1 c2 c3 c4
  unfold towerToRdec
  simp only [hcoeff.1, hcoeff.2]
  exact combine_totalDegree_le p (sg.wGen 1) h0.1 (h0.2.trans (by omega)) h1.1
    (h1.2.trans (by omega))

/-! ## Status, this pass

Leaf-level facts for `t0`/`w1`/`w2` are drafted and completed:
`t0_eq_mk'_one`, `modByMonicHom_root_eq_X` and its two instances
(`w1_modByMonicHom_coeff`/`w2_modByMonicHom_coeff`), plus the trivial-value
`baseFracToRing` bounds (`baseFracToRing_zero_totalDegree_le`/
`baseFracToRing_one_totalDegree_le`) needed to actually feed
`towerToRdecK1_totalDegree_le`'s hypothesis from `w1`/`w2`'s `(0,1)`
`modByMonicHom` normal form. **Now assembled end to end for `w1`/`w2`
themselves**: `w1_towerToRdecK1_totalDegree_le` closes the `K1 → K0` level
directly; `towerToRdecK1_zero_totalDegree_le`/`towerToRdecK1_one_totalDegree_le`
handle `towerToRdecK1` at the trivial `K1`-values `0`/`1` (needed since `w2`'s
own `(d0,d1)=(0,1)` split lands one level higher, in `K1`, not `K0`); and
`w2_towerToRdec_totalDegree_le` composes those with `combine_totalDegree_le`
to close the `K2 → K1` level for `w2` itself. **Still not done**: threading
these `anchor1`/`anchor2`-coordinate bounds through `matrixA`/`rhsVec`'s own
`if`-branching formula, nor composing with `det_totalDegree_le`/
`cramerRatioDet_num_totalDegree_le` to get a concrete `E` for
`cramerSolution`/`coeffsOut` -- that assembly is the next step, deliberately
not attempted in the same pass as these foundational leaf lemmas, per this
project's "state and check small pieces before assembling" discipline.
`reduceMonomialModU`'s leaf bound (the third kind, `F p`-constants) is
immediate from `MvPolynomial.totalDegree_C` and not separately stated as its
own theorem here since it needs no new lemma, only a one-line `simp` at the
point it's actually used.

**Fix round this pass** (in response to Claire's build errors): (1) reordered
`towerToRdecK1_zero_totalDegree_le`/`towerToRdecK1_one_totalDegree_le` to be
defined BEFORE `w2_towerToRdec_totalDegree_le`, which depends on them (they
were previously defined after their use site -- an ordering bug, not a math
error); (2) replaced `rw [hcoeff.1, hcoeff.2]`/`rw [hone]` with
`simp only [...]` in `w1_towerToRdecK1_totalDegree_le`,
`w2_towerToRdec_totalDegree_le`, and `towerToRdecK1_one_totalDegree_le` --
after `unfold`, the goal's `let`-chain elaborates to a `have`/`match` term,
and `rw` cannot find a pattern hidden behind a `have`-bound name the way
`simp only` (which zeta-reduces) can; (3) fixed the `compute_degree!`
misuse inside `towerToRdecK1_one_totalDegree_le`'s `hone` block -- after
`congr 1` the goal had `natDegree ...` on the RHS of the equation, not the
LHS, which `compute_degree!` doesn't accept, so this now proves
`natDegree ... = 2` as its own `have` and rewrites with it instead; (4)
dropped the unused `if_pos rfl` simp arg per Claire's linter hint. **Not yet
REPL-confirmed** after this round -- these are analysis-based fixes, not yet
tested against Claire's build.

**REPL-confirmed green** (whole project build) — supersedes the "Not yet
REPL-confirmed" note above.
-/

end TheDataDerivation
end Genus2Lean
