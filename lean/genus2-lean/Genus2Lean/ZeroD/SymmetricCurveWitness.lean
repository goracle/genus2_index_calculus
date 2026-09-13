import Mathlib
import Genus2Lean.ZeroD.GenListNeTopFromCurvePoint
import Genus2Lean.ZeroD.TowerToRdecRenameSymmetry

/-!
# A concrete, symbolic curve witness for Obligation 1, avoiding Hasse-Weil entirely

`ROADMAP-degree-uniform-step3.md`'s Obligation 1 needs an `assign : Idx → F p`
satisfying (a) all 4 curve relations, (b) `theData`'s 8 denominators nonzero,
(c) the 4 cross-resultants vanish, to feed
`ideal_ofList_genList_ne_top_of_curve_witness`
(`GenListNeTopFromCurvePoint.lean`).

**Why this file avoids Hasse-Weil.** The natural instinct is to hunt for a
witness via a counting/genericity argument (`CurvePointExistenceFromCounting.
lean`'s Hasse-Weil machinery). That's solving a harder problem than this
project needs: for a genuine DLP-attack instance, the attacker already HAS
two known points on the curve (that's what a discrete-log match consists
of) — existence of *some* point is never in question in the actual use
case. What's needed is a clean way to turn "one known point" into a full
`assign` satisfying (a)/(b)/(c), and `TowerToRdecRenameSymmetry.lean`
already supplies exactly this for (c): `cross_resultant_{u0,u1,v0,v1}_
eq_zero_of_symmetric` prove the four resultant equalities hold identically
(no curve computation, pure symmetry) at ANY `assign` fixed by `idxSwap`
(i.e. `assign b1 = assign a1`, `assign wb1 = assign wa1`, etc. — literally
`sa = sb` at the coordinate level) and ANY shared `s : SampleTarget p`.

So the plan: take ONE curve point pair `(a1,wa1), (a2,wa2)` (i.e. one
honest instance of (a)'s two independent scalar conditions), build the
symmetric `assign` that copies it onto the b-side coordinates verbatim,
get (c) for free from the file above, and reduce (a) to exactly the two
scalar curve conditions the input point already satisfies (down from 4
independent conditions to 2, since the b-side conditions become identical
to the a-side ones under the copy). (b) remains a genuine nonvanishing
check on `theData`'s 8 denominators at this specific `assign` — not
attempted here, this file only builds the `assign` and discharges (a)/(c).

**Status**: new file, not yet REPL-tested.
-/

namespace Genus2Lean

open TheDataDerivation hiding F
open DecoupledSystem
open MvPolynomial Idx

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (p ≠ 2)]

/-- **The symmetric witness assignment.** Given one point's worth of data
`(a1,wa1,a2,wa2)` and target coordinates `u0,u1,v0,v1` (shared by both
samples — this is where `sa = sb` lives), copy the a-side point onto the
b-side coordinates verbatim (`b1 := a1`, `wb1 := wa1`, etc.), and use the
common `u0,u1,v0,v1` values for `U0,U1,V0,V1`. This is `idxSwap`-fixed by
construction: swapping `a1↔b1` etc. does nothing, since both sides already
hold the same value. -/
noncomputable def symmetricAssign (a1 wa1 a2 wa2 u0 u1 v0 v1 : F p) : Idx → F p :=
  fun i => match i with
    | .a1 => a1 | .b1 => a1
    | .a2 => a2 | .b2 => a2
    | .wa1 => wa1 | .wb1 => wa1
    | .wa2 => wa2 | .wb2 => wa2
    | .U0 => u0 | .U1 => u1
    | .V0 => v0 | .V1 => v1

/-- `symmetricAssign` is fixed by `idxSwap`: this is what lets
`cross_resultant_*_eq_zero_of_symmetric` apply to it. `idxSwap_a1`/`_a2`/
`_wa1`/`_wa2` (`TowerToRdecRenameSymmetry.lean`) give the forward
direction (`idxSwap a1 = b1`, etc.); the reverse direction
(`idxSwap b1 = a1`, etc.) follows from `Equiv.swap`'s own involutivity,
since `idxSwapEquiv` is literally its own inverse (a product of disjoint
transpositions) — extracted via `Equiv.injective`/`(idxSwap_a1).symm ▸
Equiv.apply_eq_iff_eq ...`-style reasoning is one option, but the
project's own documented fallback for any `idxSwap`-at-a-constructor
fact is `decide`/unfold-and-`simp`, tried first here for the same
robustness reason file 25's own four lemmas use it. `U0,U1,V0,V1` are
untouched by any of `idxSwapEquiv`'s three transpositions (none of them
mention `U0`/`U1`/`V0`/`V1`), so `idxSwap` fixes them automatically. -/
theorem symmetricAssign_idxSwap_fixed (a1 wa1 a2 wa2 u0 u1 v0 v1 : F p) :
    (symmetricAssign a1 wa1 a2 wa2 u0 u1 v0 v1) ∘ idxSwap =
      symmetricAssign a1 wa1 a2 wa2 u0 u1 v0 v1 := by
  funext i
  fin_cases i <;>
    first
    | (show (symmetricAssign a1 wa1 a2 wa2 u0 u1 v0 v1) (idxSwap _) = _
        simp only [Function.comp_apply, idxSwap, idxSwapEquiv, Equiv.trans_apply,
          Equiv.swap_apply_def]
        simp [symmetricAssign])
    | decide
    | simp [Function.comp_apply, symmetricAssign, idxSwap, idxSwapEquiv,
        Equiv.swap_apply_def]

/-- **(a) collapses from 4 independent conditions to 2.** At
`symmetricAssign`, `curveB1`'s evaluation is DEFINITIONALLY the same
expression as `curveA1`'s (both read off `assign a1`/`assign wa1`, since
`assign b1 = assign a1` and `assign wb1 = assign wa1` by construction) —
so a single input hypothesis `wa1^2 = f(a1)` discharges BOTH `curveA1` and
`curveB1` at once, not two separate curve-point facts. Likewise for
`curveA2`/`curveB2`. This is the concrete payoff of the symmetric
construction for (a): the attacker's one known point (`a1,wa1`) and
(`a2,wa2`) is literally all of (a)'s content, no second point needed. -/
theorem symmetricAssign_curveA1_eq_curveB1 (c0 c1 c2 c3 c4 a1 wa1 a2 wa2 u0 u1 v0 v1 : F p) :
    MvPolynomial.eval (symmetricAssign a1 wa1 a2 wa2 u0 u1 v0 v1) (curveA1 p c0 c1 c2 c3 c4) =
    MvPolynomial.eval (symmetricAssign a1 wa1 a2 wa2 u0 u1 v0 v1) (curveB1 p c0 c1 c2 c3 c4) := by
  simp only [curveA1, curveB1, wa1', wb1', a1', b1', map_sub, map_pow, map_add, map_mul,
    MvPolynomial.eval_X, MvPolynomial.eval_C, symmetricAssign]

theorem symmetricAssign_curveA2_eq_curveB2 (c0 c1 c2 c3 c4 a1 wa1 a2 wa2 u0 u1 v0 v1 : F p) :
    MvPolynomial.eval (symmetricAssign a1 wa1 a2 wa2 u0 u1 v0 v1) (curveA2 p c0 c1 c2 c3 c4) =
    MvPolynomial.eval (symmetricAssign a1 wa1 a2 wa2 u0 u1 v0 v1) (curveB2 p c0 c1 c2 c3 c4) := by
  simp only [curveA2, curveB2, wa2', wb2', a2', b2', map_sub, map_pow, map_add, map_mul,
    MvPolynomial.eval_X, MvPolynomial.eval_C, symmetricAssign]

/-- **(a), fully discharged given the two scalar curve conditions.** With
`hA1 : wa1^2 = f(a1)` and `hA2 : wa2^2 = f(a2)` (the attacker's known
point, stated exactly the way `curveA1`/`curveA2`'s own polynomial shape
would evaluate), all four curve relations vanish at `symmetricAssign`. -/
theorem symmetricAssign_curve_relations
    (c0 c1 c2 c3 c4 a1 wa1 a2 wa2 u0 u1 v0 v1 : F p)
    (hA1 : wa1 ^ 2 = c0 + c1 * a1 + c2 * a1 ^ 2 + c3 * a1 ^ 3 + c4 * a1 ^ 4 + a1 ^ 5)
    (hA2 : wa2 ^ 2 = c0 + c1 * a2 + c2 * a2 ^ 2 + c3 * a2 ^ 3 + c4 * a2 ^ 4 + a2 ^ 5) :
    MvPolynomial.eval (symmetricAssign a1 wa1 a2 wa2 u0 u1 v0 v1) (curveA1 p c0 c1 c2 c3 c4) = 0 ∧
    MvPolynomial.eval (symmetricAssign a1 wa1 a2 wa2 u0 u1 v0 v1) (curveA2 p c0 c1 c2 c3 c4) = 0 ∧
    MvPolynomial.eval (symmetricAssign a1 wa1 a2 wa2 u0 u1 v0 v1) (curveB1 p c0 c1 c2 c3 c4) = 0 ∧
    MvPolynomial.eval (symmetricAssign a1 wa1 a2 wa2 u0 u1 v0 v1) (curveB2 p c0 c1 c2 c3 c4) = 0 := by
  have hA1' : MvPolynomial.eval (symmetricAssign a1 wa1 a2 wa2 u0 u1 v0 v1)
      (curveA1 p c0 c1 c2 c3 c4) = 0 := by
    simp only [curveA1, wa1', a1', map_sub, map_pow, map_add, map_mul, MvPolynomial.eval_X,
      MvPolynomial.eval_C, symmetricAssign]
    linear_combination hA1
  have hA2' : MvPolynomial.eval (symmetricAssign a1 wa1 a2 wa2 u0 u1 v0 v1)
      (curveA2 p c0 c1 c2 c3 c4) = 0 := by
    simp only [curveA2, wa2', a2', map_sub, map_pow, map_add, map_mul, MvPolynomial.eval_X,
      MvPolynomial.eval_C, symmetricAssign]
    linear_combination hA2
  exact ⟨hA1', hA2',
    (symmetricAssign_curveA1_eq_curveB1 c0 c1 c2 c3 c4 a1 wa1 a2 wa2 u0 u1 v0 v1) ▸ hA1',
    (symmetricAssign_curveA2_eq_curveB2 c0 c1 c2 c3 c4 a1 wa1 a2 wa2 u0 u1 v0 v1) ▸ hA2'⟩

/-- **(c), fully discharged for free** by `symmetricAssign_idxSwap_fixed`
plus `TowerToRdecRenameSymmetry.lean`'s symmetry theorems, taking
`s := ⟨u0,u1,v0,v1⟩` and `sa = sb = s` (matching this file's whole point:
the symmetric construction needs only ONE `SampleTarget`, not two). -/
theorem symmetricAssign_cross_resultants
    (c0 c1 c2 c3 c4 a1 wa1 a2 wa2 u0 u1 v0 v1 : F p)
    (hgcd : IsCoprime (Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1) (uRS p c0 c1 c2 c3 c4 u0 u1 v0 v1)) :
    let assign := symmetricAssign a1 wa1 a2 wa2 u0 u1 v0 v1
    let s : SampleTarget p := ⟨u0, u1, v0, v1⟩
    (MvPolynomial.eval assign
        (coeffsToNumDen p c0 c1 c2 c3 c4 aSideGens (uRS p c0 c1 c2 c3 c4 s.u0 s.u1 s.v0 s.v1) 0).1 *
      MvPolynomial.eval assign
        (coeffsToNumDen p c0 c1 c2 c3 c4 bSideGens (uRS p c0 c1 c2 c3 c4 s.u0 s.u1 s.v0 s.v1) 0).2 =
      MvPolynomial.eval assign
        (coeffsToNumDen p c0 c1 c2 c3 c4 bSideGens (uRS p c0 c1 c2 c3 c4 s.u0 s.u1 s.v0 s.v1) 0).1 *
      MvPolynomial.eval assign
        (coeffsToNumDen p c0 c1 c2 c3 c4 aSideGens (uRS p c0 c1 c2 c3 c4 s.u0 s.u1 s.v0 s.v1) 0).2)
    ∧
    (MvPolynomial.eval assign
        (coeffsToNumDen p c0 c1 c2 c3 c4 aSideGens (uRS p c0 c1 c2 c3 c4 s.u0 s.u1 s.v0 s.v1) 1).1 *
      MvPolynomial.eval assign
        (coeffsToNumDen p c0 c1 c2 c3 c4 bSideGens (uRS p c0 c1 c2 c3 c4 s.u0 s.u1 s.v0 s.v1) 1).2 =
      MvPolynomial.eval assign
        (coeffsToNumDen p c0 c1 c2 c3 c4 bSideGens (uRS p c0 c1 c2 c3 c4 s.u0 s.u1 s.v0 s.v1) 1).1 *
      MvPolynomial.eval assign
        (coeffsToNumDen p c0 c1 c2 c3 c4 aSideGens (uRS p c0 c1 c2 c3 c4 s.u0 s.u1 s.v0 s.v1) 1).2)
    ∧
    (MvPolynomial.eval assign
        (coeffsToNumDen p c0 c1 c2 c3 c4 aSideGens (vRS p c0 c1 c2 c3 c4 s.u0 s.u1 s.v0 s.v1 hgcd) 0).1 *
      MvPolynomial.eval assign
        (coeffsToNumDen p c0 c1 c2 c3 c4 bSideGens (vRS p c0 c1 c2 c3 c4 s.u0 s.u1 s.v0 s.v1 hgcd) 0).2 =
      MvPolynomial.eval assign
        (coeffsToNumDen p c0 c1 c2 c3 c4 bSideGens (vRS p c0 c1 c2 c3 c4 s.u0 s.u1 s.v0 s.v1 hgcd) 0).1 *
      MvPolynomial.eval assign
        (coeffsToNumDen p c0 c1 c2 c3 c4 aSideGens (vRS p c0 c1 c2 c3 c4 s.u0 s.u1 s.v0 s.v1 hgcd) 0).2)
    ∧
    (MvPolynomial.eval assign
        (coeffsToNumDen p c0 c1 c2 c3 c4 aSideGens (vRS p c0 c1 c2 c3 c4 s.u0 s.u1 s.v0 s.v1 hgcd) 1).1 *
      MvPolynomial.eval assign
        (coeffsToNumDen p c0 c1 c2 c3 c4 bSideGens (vRS p c0 c1 c2 c3 c4 s.u0 s.u1 s.v0 s.v1 hgcd) 1).2 =
      MvPolynomial.eval assign
        (coeffsToNumDen p c0 c1 c2 c3 c4 bSideGens (vRS p c0 c1 c2 c3 c4 s.u0 s.u1 s.v0 s.v1 hgcd) 1).1 *
      MvPolynomial.eval assign
        (coeffsToNumDen p c0 c1 c2 c3 c4 aSideGens (vRS p c0 c1 c2 c3 c4 s.u0 s.u1 s.v0 s.v1 hgcd) 1).2) := by
  have hsym := symmetricAssign_idxSwap_fixed a1 wa1 a2 wa2 u0 u1 v0 v1
  exact ⟨cross_resultant_u0_eq_zero_of_symmetric p c0 c1 c2 c3 c4 ⟨u0, u1, v0, v1⟩ _ hsym,
    cross_resultant_u1_eq_zero_of_symmetric p c0 c1 c2 c3 c4 ⟨u0, u1, v0, v1⟩ _ hsym,
    cross_resultant_v0_eq_zero_of_symmetric p c0 c1 c2 c3 c4 ⟨u0, u1, v0, v1⟩ hgcd _ hsym,
    cross_resultant_v1_eq_zero_of_symmetric p c0 c1 c2 c3 c4 ⟨u0, u1, v0, v1⟩ hgcd _ hsym⟩

/-! ## What remains: (b), the 8 denominators

**Deliberately NOT attempted in this file.** This is the one genuinely
open piece for Obligation 1 under this route: showing `theData`'s 8
denominators (`u1_den 0/1`, `u2_den 0/1`, `v1_den 0/1`, `v2_den 0/1`)
evaluate to nonzero at `symmetricAssign a1 wa1 a2 wa2 u0 u1 v0 v1` for
SOME concrete choice of `(a1,wa1,a2,wa2,u0,u1,v0,v1)` (with `u0,u1,v0,v1`
being the actual Mumford coefficients of the divisor `(a1,wa1)+(a2,wa2)`,
i.e. `sa = sb` in the fully-reduced case, not free parameters — see
`ROADMAP-degree-uniform-step3.md`'s (a)'s note that `(a1,wa1)` determine
`u0,u1,v0,v1` automatically via the Mumford correspondence once the two
points are distinct). Since `symmetricAssign` collapses BOTH samples onto
the SAME point, `u1_den i` and `u2_den i` become literally the same
polynomial expression evaluated at the same point (an a-side/b-side
symmetric pair, same argument as the curve-relation collapse above) — so
this reduces to checking 4 denominators, not 8, and reduces further to
whatever `theData`'s actual denominator formula degenerates to under
`a1≠a2` (the standard nondegeneracy condition for the Mumford
interpolation's `matrixA.det ≠ 0`, i.e. `MatrixNondegenerate`, which this
project already has machinery for elsewhere). Next concrete step: check
`theData`'s literal `u1_den`/`v1_den` formulas against `a1 ≠ a2` and
confirm nonvanishing, or identify the actual condition needed. -/

end Genus2Lean
