import Mathlib
import Genus2Lean.ZeroD.AnchorTotalDegree
import Genus2Lean.ZeroD.RRBasisTotalDegree

/-!
# `matrixA`/`rhsVec`'s entrywise `totalDegree` building blocks

New this pass. Continues the remaining assembly work both
`AnchorTotalDegree.lean` and `CramerEntryTotalDegree.lean`'s own status
notes flag (`ROADMAP-crossnondegenerate-degree-bound.md`'s item 1/2):
threading `anchor1`/`anchor2`'s `towerToRdec` bounds through `matrixA`'s
`px ^ bi * (py or 1)` shape and `reduceMonomialModU`'s constant rows.

**This file supplies the pieces, not yet the full `matrixA`/`rhsVec`
entry theorem itself**: `matrixA`/`rhsVec`'s actual `let`/`if`-laden
definitions (`DataDerivationSolve.lean`) need `unfold`+`simp only`-style
unfolding whose exact shape is only safely pinned down against a real
build (`CramerEntryTotalDegree.lean`'s own status note documents several
`let`-elaboration surprises hit this way) — assembling the final entry
theorem is left to a following pass once these pieces are confirmed, per
this project's "small pieces before assembling" discipline.

**Not yet REPL-confirmed** — no build environment available this session;
per project convention, Claude drafts, Claire tests.
-/

namespace Genus2Lean
namespace TheDataDerivation

open Polynomial

variable (p : ℕ) [hp : Fact (Nat.Prime p)] [hp2 : Fact (p ≠ 2)]
variable (c0 c1 c2 c3 c4 : F p)

/-- **`totalDegree` of an `MvPolynomial` power, by induction on the
exponent.** Not found under a confirmed name in this Mathlib snapshot
(`totalDegree_pow` was searched for and not confirmed present) — proved
directly from `MvPolynomial.totalDegree_mul` (already confirmed and used
throughout `DataDerivationTotalDegree.lean`) and `MvPolynomial.
totalDegree_one`, `pow_succ`, exactly the "spell it out" fallback this
project's convention calls for when a Mathlib name search comes up
empty. -/
theorem totalDegree_pow_le {Vars : Type*} (f : MvPolynomial Vars (F p)) (n : ℕ) :
    (f ^ n).totalDegree ≤ n * f.totalDegree := by
  induction n with
  | zero => simp [MvPolynomial.totalDegree_one]
  | succ k ih =>
    rw [pow_succ]
    calc (f ^ k * f).totalDegree ≤ (f ^ k).totalDegree + f.totalDegree :=
          MvPolynomial.totalDegree_mul _ _
      _ ≤ k * f.totalDegree + f.totalDegree := by omega
      _ = (k + 1) * f.totalDegree := by ring

/-- **Anchor abscissas, restated in `anchor1`/`anchor2`-facing form.**
`t0_promoted_totalDegree_le` (`DataDerivationTotalDegree.lean`) bounds the
raw two-step promotion chain; `anchor1.1`/`anchor2.1` (`DataDerivationSolve.
lean`) unfold to exactly that chain applied to `t0 p 0`/`t0 p 1`
respectively — restated here under the `anchor1`/`anchor2`-facing name,
matching `anchor1_snd_totalDegree_le`/`anchor2_snd_totalDegree_le`'s own
naming (`AnchorTotalDegree.lean`), for use in the `matrixA`/`rhsVec`
assembly that needs both halves of each anchor pair in scope together. -/
theorem anchor1_fst_totalDegree_le {Vars : Type*} (sg : SideGens Vars) :
    (towerToRdec p sg (anchor1 p c0 c1 c2 c3 c4).1).1.totalDegree ≤ 7 ∧
    (towerToRdec p sg (anchor1 p c0 c1 c2 c3 c4).1).2.totalDegree ≤ 6 :=
  t0_promoted_totalDegree_le p sg c0 c1 c2 c3 c4 0

/-- **Companion for `anchor2.1`.** Same route, `t0 p 1` in place of `t0 p 0`. -/
theorem anchor2_fst_totalDegree_le {Vars : Type*} (sg : SideGens Vars) :
    (towerToRdec p sg (anchor2 p c0 c1 c2 c3 c4).1).1.totalDegree ≤ 7 ∧
    (towerToRdec p sg (anchor2 p c0 c1 c2 c3 c4).1).2.totalDegree ≤ 6 :=
  t0_promoted_totalDegree_le p sg c0 c1 c2 c3 c4 1

/-- **`reduceMonomialModU`'s output, pushed through `towerToRdec`, has
`totalDegree 0` on both halves.** `reduceMonomialModU`'s output is an
`F p`-valued pair (`DataDerivationBasics.lean`); once `algebraMap`-lifted
into `K2 p ...`, its `towerToRdec` image is the base-case-of-base-cases —
structurally the SAME shape `t0_promoted_totalDegree_le` (`DataDerivation
TotalDegree.lean`) already handles (a `K0 p`-element promoted through
`K1 → K2`), just starting from a different `K0`-element: `algebraMap
(F p) (K0 p) a` in place of `t0 p i`. Route: `MvPolynomial.algebraMap_apply`
gives `algebraMap (F p) (MvPolynomial (Fin 2) (F p)) a = C a` (`R = S₁ =
F p`, `algebraMap (F p) (F p) = id` via `RingHom.id_apply`/`Algebra.id.map_eq_id`),
so `algebraMap (F p) (K0 p) a = mk' (K0 p) (C a) 1` — same `mk'_spec'`
pattern as `t0_eq_mk'_one`/`t0_totalDegree_le`, with `C a` (`totalDegree 0`,
`MvPolynomial.totalDegree_C`) in place of `X i` (`totalDegree 1`). Feeding
`baseFracToRing_totalDegree_le` at `a := C a`, `b := 1` gives `baseFracToRing
p sg (algebraMap (F p) (K0 p) a)` both halves `= 0` (not merely `≤ D`, since
`C a`/`1` both have `totalDegree` EXACTLY `0`) — then `towerToRdecK1_
algebraMap_totalDegree_le`/`towerToRdec_algebraMap_totalDegree_le` (both
already proved, `DataDerivationTotalDegree.lean`) propagate that up through
`K1 → K2` at `D := 1` (the same floor `t0_promoted_totalDegree_le` itself
needs, from `towerToRdecK1 p sg (0 : K1 p ...)`'s own `≤1`/`≤0` structural
cost — `D := 0` would be too small even though the BASE input here is
genuinely `totalDegree 0`, not `≤ 1` the way `t0`'s own base case is). -/
theorem algebraMap_Fp_towerToRdec_totalDegree_eq {Vars : Type*} (sg : SideGens Vars)
    (a : F p) :
    (towerToRdec p sg
        (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) a)).1.totalDegree ≤ 7 ∧
    (towerToRdec p sg
        (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) a)).2.totalDegree ≤ 6 := by
  -- `algebraMap (F p) (K0 p) a`'s `baseFracToRing` bound, both halves `≤ 0`
  -- (in fact `= 0`, but `≤ 0` is all `towerToRdecK1_algebraMap_totalDegree_le`
  -- needs) — split on `a = 0` since `baseFracToRing_totalDegree_le` needs a
  -- nonzero numerator witness, mirroring `baseFracToRing_zero_one_
  -- totalDegree_eq_zero`'s own `v = 0` handling one level up.
  have hcompose : (algebraMap (F p) (K0 p) a) =
      algebraMap (MvPolynomial (Fin 2) (F p)) (K0 p)
        (algebraMap (F p) (MvPolynomial (Fin 2) (F p)) a) := by
    rw [← IsScalarTower.algebraMap_apply]
  have hCa : (algebraMap (F p) (MvPolynomial (Fin 2) (F p)) a) =
      (MvPolynomial.C a : MvPolynomial (Fin 2) (F p)) := by
    rw [MvPolynomial.algebraMap_apply]; rfl
  have hbase : (baseFracToRing p sg (algebraMap (F p) (K0 p) a)).1.totalDegree ≤ 0 ∧
      (baseFracToRing p sg (algebraMap (F p) (K0 p) a)).2.totalDegree ≤ 0 := by
    rcases eq_or_ne a 0 with ha0 | hane0
    · have h0 : algebraMap (F p) (K0 p) a = 0 := by rw [ha0]; exact map_zero _
      rw [h0]
      have hz := baseFracToRing_zero_one_totalDegree_eq_zero p sg
      exact ⟨hz.1.le, hz.2.1.le⟩
    · have hv : (algebraMap (F p) (K0 p) a) =
          IsLocalization.mk' (K0 p) (MvPolynomial.C a : MvPolynomial (Fin 2) (F p))
            ⟨1, mem_nonZeroDivisors_of_ne_zero (one_ne_zero)⟩ := by
        have hspec := IsLocalization.mk'_spec' (K0 p)
          (MvPolynomial.C a : MvPolynomial (Fin 2) (F p))
          (⟨1, mem_nonZeroDivisors_of_ne_zero (one_ne_zero)⟩ :
            ↥(nonZeroDivisors (MvPolynomial (Fin 2) (F p))))
        simp only [map_one, one_mul] at hspec
        rw [hcompose, hCa, ← hspec]
      have hCane0 : (MvPolynomial.C a : MvPolynomial (Fin 2) (F p)) ≠ 0 :=
        MvPolynomial.C_ne_zero.mpr hane0
      have hbound := baseFracToRing_totalDegree_le p sg
        (a := (MvPolynomial.C a : MvPolynomial (Fin 2) (F p)))
        (b := (1 : MvPolynomial (Fin 2) (F p))) one_ne_zero hCane0 hv
      rwa [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_one] at hbound
  -- Propagate through `K1 → K2` exactly as `t0_promoted_totalDegree_le` does
  -- for `t0 p i`, `D := 1` throughout (same floor, same route).
  have h1 := towerToRdecK1_algebraMap_totalDegree_le p sg c0 c1 c2 c3 c4
    (algebraMap (F p) (K0 p) a)
    ⟨hbase.1.trans (Nat.zero_le 1), hbase.2.trans (Nat.zero_le 1)⟩
  have h2 := towerToRdec_algebraMap_totalDegree_le p sg c0 c1 c2 c3 c4
    (D := 3) (by norm_num) (algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4) (algebraMap (F p) (K0 p) a))
    ⟨h1.1, h1.2.trans (by norm_num)⟩
  have heq : algebraMap (F p) (K2 p c0 c1 c2 c3 c4) a =
      algebraMap (K1 p c0 c1 c2 c3 c4) (K2 p c0 c1 c2 c3 c4)
        (algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4) (algebraMap (F p) (K0 p) a)) := by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  rw [heq]; exact h2

/-! ## Status, this pass

**All four theorems drafted and closed, no `sorry`** — `totalDegree_pow_le`,
`anchor1_fst_totalDegree_le`, `anchor2_fst_totalDegree_le`, and
`algebraMap_Fp_towerToRdec_totalDegree_eq`. Not yet REPL-confirmed (no
build environment available this session), but every proof step composes
already-proved, already-used lemmas from `DataDerivationTotalDegree.lean`
— no new Mathlib API beyond `MvPolynomial.algebraMap_apply` (confirmed via
web search against the current mathlib4 docs, not guessed) and
`IsScalarTower.algebraMap_apply` (standard, used for tower-composition
rewrites elsewhere in this style of proof).

**One thing worth flagging plainly**: an earlier draft of
`algebraMap_Fp_towerToRdec_totalDegree_eq` in this same pass used `sorry`
as a placeholder for the `a = 0`/`a ≠ 0` case split before working out the
actual argument — that was a mistake given this project's zero-sorry
state going in, caught and fixed before finalizing this file rather than
left in. The final proof case-splits on `a = 0`/`a ≠ 0` directly (mirroring
`baseFracToRing_zero_one_totalDegree_eq_zero`'s own `v = 0` handling one
level up) and contains no `sorry` or other placeholder.

**What remains after this file, still unstarted**: the actual `matrixA`/
`rhsVec` entry theorem, composing `anchor1_fst/snd_totalDegree_le`,
`anchor2_fst/snd_totalDegree_le`, `rrBasis5_getD_bi_le_three`,
`totalDegree_pow_le`, and `algebraMap_Fp_towerToRdec_totalDegree_eq`
through `matrixA`/`rhsVec`'s own `if`-branching — four cases (`row = 0`,
`row = 1`, `row = 2`, `row = 3`), each a `combine_totalDegree_le`-style
`mul`/`add` chain. Then one more step (`cramerRatioDet_num_totalDegree_le`,
`DataDerivationTotalDegree.lean`) to reach `coeffsOut`'s own bound. -/

end TheDataDerivation
end Genus2Lean
