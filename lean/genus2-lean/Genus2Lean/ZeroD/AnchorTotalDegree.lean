import Mathlib
import Genus2Lean.ZeroD.DataDerivationTotalDegree

/-!
# Anchor-point `totalDegree` bounds: `anchor1`/`anchor2`'s `towerToRdec` images

New this pass. Continues `DataDerivationTotalDegree.lean`'s own "Next step"
note: that file closed `t0_promoted_totalDegree_le` (bounding `anchor1.1`/
`anchor2.1`, the `t1`/`t2` anchor abscissas) but flagged `w1`/`w2` — the
anchor *ordinates*, `anchor1.2`/`anchor2.2` — as needing one more step:
`anchor1.2 = algebraMap (K1 p ...) (K2 p ...) (w1 p ...)` (a `K1 → K2`
promotion of `w1`, mirroring `t0_promoted_totalDegree_le`'s own shape) and
`anchor2.2 = w2 p ...` directly (already `K2`-valued, no promotion step).
Both close here, using only theorems already proved and REPL-confirmed in
`DataDerivationTotalDegree.lean` — no new Mathlib API, no new mathematical
content, purely assembly. Not yet REPL-confirmed (no build environment
available this session; Claire's REPL is the source of truth per project
convention).

**Why a new file rather than appending to `DataDerivationTotalDegree.lean`**:
that file is close to this project's 1500-line-per-file guideline (~1400
lines before this work). This file picks up the same `totalDegree`-bound
thread one layer further downstream (towards `matrixA`/`rhsVec`'s entrywise
bounds, per `ROADMAP-crossnondegenerate-degree-bound.md`'s remaining
assembly work), rather than growing that file further.
-/

namespace Genus2Lean
namespace TheDataDerivation

open Polynomial

variable (p : ℕ) [hp : Fact (Nat.Prime p)] [hp2 : Fact (p ≠ 2)]
variable (c0 c1 c2 c3 c4 : F p)

/-- **`w2`'s own `towerToRdec` image has `totalDegree ≤ 3`/`≤ 2`.**
Mirrors `towerToRdecK1_w1_totalDegree_le` (`DataDerivationTotalDegree.lean`)
one tower level up: `w2_modByMonicHom_eq_X` reduces `w2`'s `modByMonicHom`
normal form to `X` itself (`.coeff 0 = 0`, `.coeff 1 = 1 : K1 p ...`), and
`towerToRdecK1_zero_one_totalDegree_le` already bounds `towerToRdecK1 p sg`
applied to `0`/`1 : K1 p ...` by `≤ 1`/`≤ 0` — feeding those into
`towerToRdec_totalDegree_le` (at `D := 1`, the common bound dominating all
four of `towerToRdecK1`'s `0`/`1`-branch outputs, `≤1,≤0,≤1,≤0`) gives
`towerToRdec`'s own output `≤ 2*1+1 = 3`, `≤ 2*1 = 2` — NOT `≤1`/`≤0`
(unlike `towerToRdecK1_w1_totalDegree_le`'s own bound one level down: that
theorem's `D` there is `0`, since `baseFracToRing`'s zero/one case is
`totalDegree = 0` outright, not `≤ 1`; here the input to the combining step
is already `towerToRdecK1`'s OUTPUT, whose zero/one bound is `≤1`/`≤0`, one
notch higher). -/
theorem towerToRdec_w2_totalDegree_le {Vars : Type*} (sg : SideGens Vars) :
    (towerToRdec p sg (w2 p c0 c1 c2 c3 c4)).1.totalDegree ≤ 3 ∧
    (towerToRdec p sg (w2 p c0 c1 c2 c3 c4)).2.totalDegree ≤ 2 := by
  have hw2 := w2_modByMonicHom_eq_X p c0 c1 c2 c3 c4
  have hzo := towerToRdecK1_zero_one_totalDegree_le p sg c0 c1 c2 c3 c4
  have h : (towerToRdecK1 p sg
          ((AdjoinRoot.modByMonicHom (K2_poly_monic p c0 c1 c2 c3 c4)
            (w2 p c0 c1 c2 c3 c4) : Polynomial (K1 p c0 c1 c2 c3 c4)).coeff 0)).1.totalDegree
        ≤ 1 ∧
      (towerToRdecK1 p sg
          ((AdjoinRoot.modByMonicHom (K2_poly_monic p c0 c1 c2 c3 c4)
            (w2 p c0 c1 c2 c3 c4) : Polynomial (K1 p c0 c1 c2 c3 c4)).coeff 0)).2.totalDegree
        ≤ 1 ∧
      (towerToRdecK1 p sg
          ((AdjoinRoot.modByMonicHom (K2_poly_monic p c0 c1 c2 c3 c4)
            (w2 p c0 c1 c2 c3 c4) : Polynomial (K1 p c0 c1 c2 c3 c4)).coeff 1)).1.totalDegree
        ≤ 1 ∧
      (towerToRdecK1 p sg
          ((AdjoinRoot.modByMonicHom (K2_poly_monic p c0 c1 c2 c3 c4)
            (w2 p c0 c1 c2 c3 c4) : Polynomial (K1 p c0 c1 c2 c3 c4)).coeff 1)).2.totalDegree
        ≤ 1 := by
    rw [hw2, Polynomial.coeff_X_zero, Polynomial.coeff_X_one]
    exact ⟨hzo.1, hzo.2.1.trans (Nat.zero_le 1), hzo.2.2.1, hzo.2.2.2.trans (Nat.zero_le 1)⟩
  have := towerToRdec_totalDegree_le p c0 c1 c2 c3 c4 sg (w2 p c0 c1 c2 c3 c4) h
  omega

/-- **`anchor1.2`'s `towerToRdec` image has `totalDegree ≤ 3`/`≤ 2`.**
`anchor1.2 = algebraMap (K1 p ...) (K2 p ...) (w1 p ...)`, a `K1 → K2`
promotion — same shape as `t0_promoted_totalDegree_le`'s own `K1 → K2` step
but starting from `w1`'s `towerToRdecK1`-level bound (`≤ 1`/`≤ 0`, from
`towerToRdecK1_w1_totalDegree_le`) rather than `t0`'s (`≤ 1`/`≤ 0` also,
coincidentally the same numbers, but via a different route — `w1` is not a
base-case generator, it's already one `towerToRdecK1` level up). Feeds
`towerToRdec_algebraMap_totalDegree_le` at `D := 1`, which needs BOTH
halves at the same `D` — `hw1`'s `≤ 0` half is widened to `≤ 1` via
`Nat.zero_le`/`.trans` before pairing, same move `towerToRdec_w2_
totalDegree_le` above makes on `hzo`. (First draft of this theorem missed
this widening and failed to typecheck against `towerToRdec_algebraMap_
totalDegree_le`'s `hw` hypothesis shape — fixed here.) -/
theorem anchor1_snd_totalDegree_le {Vars : Type*} (sg : SideGens Vars) :
    (towerToRdec p sg (anchor1 p c0 c1 c2 c3 c4).2).1.totalDegree ≤ 3 ∧
    (towerToRdec p sg (anchor1 p c0 c1 c2 c3 c4).2).2.totalDegree ≤ 2 := by
  have hw1 := towerToRdecK1_w1_totalDegree_le p sg c0 c1 c2 c3 c4
  have h2 := towerToRdec_algebraMap_totalDegree_le p sg c0 c1 c2 c3 c4
    (D := 1) (le_refl 1) (w1 p c0 c1 c2 c3 c4) ⟨hw1.1, hw1.2.trans (Nat.zero_le 1)⟩
  have heq : (anchor1 p c0 c1 c2 c3 c4).2 =
      algebraMap (K1 p c0 c1 c2 c3 c4) (K2 p c0 c1 c2 c3 c4) (w1 p c0 c1 c2 c3 c4) := rfl
  rw [heq]; exact h2

/-- **`anchor2.2`'s `towerToRdec` image has `totalDegree ≤ 3`/`≤ 2`.**
`anchor2.2 = w2 p ...` directly (no promotion step, unlike `anchor1.2`) —
this is exactly `towerToRdec_w2_totalDegree_le` above, restated under the
`anchor2`-facing name for the assembly steps that need `anchor1`/`anchor2`
in scope directly. -/
theorem anchor2_snd_totalDegree_le {Vars : Type*} (sg : SideGens Vars) :
    (towerToRdec p sg (anchor2 p c0 c1 c2 c3 c4).2).1.totalDegree ≤ 3 ∧
    (towerToRdec p sg (anchor2 p c0 c1 c2 c3 c4).2).2.totalDegree ≤ 2 :=
  towerToRdec_w2_totalDegree_le p c0 c1 c2 c3 c4 sg

/-! ## Status, this pass

**Drafted, NOT yet REPL-confirmed** — no build environment available this
session (per project convention, Claude scopes/drafts, Claire tests).
Same proof shapes as already-confirmed theorems in
`DataDerivationTotalDegree.lean` (`towerToRdecK1_w1_totalDegree_le`,
`t0_promoted_totalDegree_le`), so risk should be low, but every one of
these three theorems is new this pass and unverified.

**What this closes**: `anchor1`/`anchor2`'s full `(t_i, w_i)` pair now has
a `towerToRdec` bound on both components — `.1` via
`t0_promoted_totalDegree_le` (`DataDerivationTotalDegree.lean`, `≤7`/`≤6`),
`.2` via `anchor1_snd_totalDegree_le`/`anchor2_snd_totalDegree_le` above
(`≤3`/`≤2` for both, despite `anchor1.2` needing one more tower-promotion
step than `anchor2.2` — `anchor1.2`'s promotion step and `anchor2.2`'s
direct `w2_modByMonicHom_eq_X` route both bottom out at the same `D := 1`
combining step, so the extra promotion in `anchor1.2`'s route does not
raise its bound past `anchor2.2`'s here; a tighter bound might separate
them but was not sought this pass — `≤3`/`≤2` uniformly is what both
proofs actually establish).

**What this does NOT yet close** (the actual remaining work toward
`matrixA`/`rhsVec`'s entrywise bound, per `ROADMAP-crossnondegenerate-
degree-bound.md`):
1. Raising `t1`/`t2`/`w1`/`w2`'s bounds through `px ^ bi * (py or 1)`
   (`matrixA`'s row-0/row-1 shape) — mechanical `MvPolynomial.totalDegree_
   mul`/`_pow`, `bi ≤ 3` (`rrBasis5`'s own bound), not yet stated as an
   explicit theorem here.
2. `reduceMonomialModU`'s output is `F p`-valued (rows 2/3) — `totalDegree
   0` once pushed through `algebraMap`/`towerToRdec`'s base case
   (`t0_totalDegree_le`-style, but for a genuine field CONSTANT rather
   than a generator — needs its own one-line lemma via `MvPolynomial.
   totalDegree_C`, not yet written).
3. Assembling `matrixA`/`rhsVec`'s full `4×4` entrywise bound (max of the
   above four cases) as a single theorem, then feeding it into
   `cramerRatioDet_num_totalDegree_le` (`DataDerivationTotalDegree.lean`)
   to bound `coeffsOut`'s `totalDegree` — this is where a concrete `D`
   finally emerges, closing `ROADMAP-crossnondegenerate-degree-bound.md`'s
   long-open "trace the concrete `D`" item for the base case *feeding
   into* `Epoly`/`Ypoly`/`Npoly` (a separate, still-harder step: `Npoly`'s
   OWN `totalDegree`, then `curBeforeMonic`'s, via `Npoly_eq_
   curBeforeMonic_mul` — see that theorem's own docstring,
   `DataDerivationSolve.lean`, for why `curBeforeMonic`'s bound is not a
   direct `totalDegree_le_of_dvd_of_isDomain` corollary of `Npoly`'s: that
   lemma bounds one `MvPolynomial`'s `totalDegree` by a DIVISOR's, but
   `curBeforeMonic`'s `totalDegree` bound needed here is per-*coefficient*
   of a `Polynomial (K2 ...)`, and coefficient-wise divisibility does not
   follow automatically from the polynomial-level exact-quotient identity
   `Npoly_eq_curBeforeMonic_mul` states — this is the genuinely open
   "new territory" step both this file's import and `ROADMAP-
   crossnondegenerate-degree-bound.md`'s own final section flag, good
   ChatGPT-consultation material once items 1-3 above are closed and a
   concrete `Npoly` coefficient bound is in hand to consult about).
-/

end TheDataDerivation
end Genus2Lean
