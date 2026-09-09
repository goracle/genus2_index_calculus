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

/-! ## Status, this pass

Leaf-level facts for `t0`/`w1`/`w2` are drafted (`t0_eq_mk'_one`,
`modByMonicHom_root_eq_X` and its two instances). **Not yet assembled** into
an actual `totalDegree` bound on `anchor1`/`anchor2`'s coordinates after full
`towerToRdec` descent, nor threaded through `matrixA`/`rhsVec`'s
`if`-branching formula, nor composed with `det_totalDegree_le`/
`cramerRatioDet_num_totalDegree_le` to get a concrete `E` for
`cramerSolution`/`coeffsOut` -- that assembly is the next step, deliberately
not attempted in the same pass as these foundational leaf lemmas, per this
project's "state and check small pieces before assembling" discipline.
`reduceMonomialModU`'s leaf bound (the third kind, `F p`-constants) is
immediate from `MvPolynomial.totalDegree_C` and not separately stated as its
own theorem here since it needs no new lemma, only a one-line `simp` at the
point it's actually used.
-/

end TheDataDerivation
end Genus2Lean
