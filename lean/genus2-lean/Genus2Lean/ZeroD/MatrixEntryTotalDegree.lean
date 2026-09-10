import Mathlib
import Genus2Lean.ZeroD.AnchorTotalDegree
import Genus2Lean.ZeroD.RRBasisTotalDegree
import Genus2Lean.ZeroD.TowerToRdecMul

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

**REPL-confirmed through at least one full build pass** (see "Status,
latest pass" below for the errors that build surfaced and how they were
fixed) — not a guarantee every theorem in this file is final: `row = 0`
specifically has round-tripped through Claire's REPL at least twice and
is confirmed; `row = 1` has been through two rounds of real REPL-
reported build errors, both fixed (fix #8, below), pending Claire's
final green confirmation; `row = 2`/`3` are still unattempted.
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

/-- **`px ^ bi * (py or 1)`'s witness pair has a `totalDegree` bound**, the
shape `matrixA`'s row-0/row-1 entries actually take (`px,py := anchor1`/
`anchor2`'s two components). Composes `totalDegree_pow_le` (on `px`'s own
`towerToRdec`-image degree, via `anchor1_fst_totalDegree_le`/`anchor2_fst_
totalDegree_le`, `≤7`/`≤6`) with `totalDegree_mul` (against `py`'s own
image, via `anchor1_snd_totalDegree_le`/`anchor2_snd_totalDegree_le` in
`AnchorTotalDegree.lean`, `≤3`/`≤2`, or against `(1,1)`'s trivial `totalDegree
0` in the `bj ≠ 1` branch) directly on the witness COMPONENTS — not via
`IsRdecWitness` (`TowerToRdecMul.lean`), which only certifies that
`((towerToRdec px).1 * (towerToRdec (py or 1)).1, ...)` is legitimately a
witness for the VALUE `px^bi * (py or 1)`, a separate concern from its
degree. `bi ≤ 3` (`rrBasis5_getD_bi_le_three`) bounds the power. -/
theorem anchorPow_mul_totalDegree_le {Vars : Type*}
    (nx dx ny dy : MvPolynomial Vars (F p)) {bi : ℕ} (hbi : bi ≤ 3)
    (hx1 : nx.totalDegree ≤ 7) (hx2 : dx.totalDegree ≤ 6)
    (hy1 : ny.totalDegree ≤ 3) (hy2 : dy.totalDegree ≤ 2) :
    (nx ^ bi * ny).totalDegree ≤ 24 ∧ (dx ^ bi * dy).totalDegree ≤ 20 := by
  have h1 : (nx ^ bi * ny).totalDegree ≤ (nx ^ bi).totalDegree + ny.totalDegree :=
    MvPolynomial.totalDegree_mul _ _
  have h2 : (dx ^ bi * dy).totalDegree ≤ (dx ^ bi).totalDegree + dy.totalDegree :=
    MvPolynomial.totalDegree_mul _ _
  have hp1 : (nx ^ bi).totalDegree ≤ bi * nx.totalDegree := totalDegree_pow_le p nx bi
  have hp2 : (dx ^ bi).totalDegree ≤ bi * dx.totalDegree := totalDegree_pow_le p dx bi
  -- `bi * nx.totalDegree ≤ 3 * 7` is a product of two bounded naturals
  -- (`hbi : bi ≤ 3`, `hx1 : nx.totalDegree ≤ 7`) — genuinely nonlinear, so
  -- `omega` alone can't multiply the two bounds together; `nlinarith` can,
  -- by considering the product of the two hypotheses directly.
  have hp1' : bi * nx.totalDegree ≤ 21 := by nlinarith
  have hp2' : bi * dx.totalDegree ≤ 18 := by nlinarith
  omega

/-- **The `bj ≠ 1` companion**: `px ^ bi * 1`'s witness pair, i.e. just
`px ^ bi`'s own bound (`ny,dy := 1,1`, `totalDegree 0` each — the trivial
case of `anchorPow_mul_totalDegree_le`, restated without the unused
`(ny,dy)` hypotheses since `MvPolynomial.totalDegree_one = 0` closes them
directly rather than needing them threaded through as arguments). -/
theorem anchorPow_totalDegree_le {Vars : Type*}
    (nx dx : MvPolynomial Vars (F p)) {bi : ℕ} (hbi : bi ≤ 3)
    (hx1 : nx.totalDegree ≤ 7) (hx2 : dx.totalDegree ≤ 6) :
    (nx ^ bi).totalDegree ≤ 21 ∧ (dx ^ bi).totalDegree ≤ 18 := by
  have hp1 : (nx ^ bi).totalDegree ≤ bi * nx.totalDegree := totalDegree_pow_le p nx bi
  have hp2 : (dx ^ bi).totalDegree ≤ bi * dx.totalDegree := totalDegree_pow_le p dx bi
  have hp1' : bi * nx.totalDegree ≤ 21 := by nlinarith
  have hp2' : bi * dx.totalDegree ≤ 18 := by nlinarith
  omega

/-! ## `matrixA row 0`/`matrixA row 1`'s entry witness and degree bound

The actual assembly step `TowerToRdecMul.lean`'s own status note flags as
"still the next step, not attempted in this file", and this file's own
earlier status note flagged as "not yet unfolded". Attempted now that
`anchorPow_mul_totalDegree_le`/`anchorPow_totalDegree_le` (above) and
`IsRdecWitness`/`.mul`/`towerToRdec_mul_isRdecWitness` (`TowerToRdecMul.lean`)
are both in place. -/

/-- **`matrixA row col`'s value, for `row.val = 0`, has an explicit
`IsRdecWitness` pair with a `totalDegree` bound.** `matrixA`'s `row = 0`
branch is `px ^ bi * (if bj = 1 then py else 1)` for `(px,py) := anchor1
p c0 c1 c2 c3 c4`, `(_, bi, bj) := rrBasis5.getD (otherIdx.getD col.val 0)
(0,0,0)` — a PRODUCT of two `K2`-valued factors, each individually
`towerToRdec`-witnessed (`anchor1_fst/snd_totalDegree_le`), so
`towerToRdec_mul_isRdecWitness`/`IsRdecWitness.mul`-style pointwise
products of those two witnesses are a valid witness for the whole entry
(NOT `towerToRdec` applied to the entry directly, which this file's
sibling `TowerToRdecMul.lean` already flags as generally a different,
more-reduced pair — a valid witness is all `totalDegree`-bounding needs).
States the `bj = 1` branch via `anchorPow_mul_totalDegree_le` and the
`bj ≠ 1` branch via `anchorPow_totalDegree_le`, matching `matrixA`'s own
`if bj = 1 then py else 1` split rather than trying to combine both into
one statement. **Genuinely new, not yet REPL-confirmed** — the one piece
of this file that actually unfolds `matrixA`'s `let`/`if` chain, which
this file's own earlier status note flagged as the real risk (`let`-
elaboration surprises need a real build to pin down safely per
`CramerEntryTotalDegree.lean`'s own documented experience with this exact
kind of unfolding) — send to Claire's REPL first, expect possible
`simp`/`unfold` adjustments before this closes. -/
theorem matrixA_row0_totalDegree_le {Vars : Type*} [DecidableEq Vars]
    (sg : SideGens Vars) (u0 u1 v0 v1 : F p) (col : Fin 4)
    (ι : K2 p c0 c1 c2 c3 c4 →+* FractionRing (MvPolynomial Vars (F p)))
    (hι_t : ∀ i : Fin 2, ι (algebraMap (K1 p c0 c1 c2 c3 c4) (K2 p c0 c1 c2 c3 c4)
        (algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4)
          (algebraMap (MvPolynomial (Fin 2) (F p)) (K0 p) (MvPolynomial.X i)))) =
      algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p)))
        (MvPolynomial.X (sg.tGen i)))
    (hι_w1 : ι (algebraMap (K1 p c0 c1 c2 c3 c4) (K2 p c0 c1 c2 c3 c4) (w1 p c0 c1 c2 c3 c4)) =
      algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p)))
        (MvPolynomial.X (sg.wGen 0)))
    (hι_w2 : ι (w2 p c0 c1 c2 c3 c4) =
      algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p)))
        (MvPolynomial.X (sg.wGen 1)))
    (hbidx : otherIdx.getD col.val 0 < 5) :
    ∃ nd : MvPolynomial Vars (F p) × MvPolynomial Vars (F p),
      IsRdecWitness p ι
        (algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p))))
        (matrixA p c0 c1 c2 c3 c4 u0 u1 v0 v1 ⟨0, by norm_num⟩ col)
        nd ∧ nd.1.totalDegree ≤ 24 ∧ nd.2.totalDegree ≤ 20 := by
  set bidx := otherIdx.getD col.val 0 with hbidx_def
  set bi := (rrBasis5.getD bidx (0, 0, 0)).2.1 with hbi_def
  set bj := (rrBasis5.getD bidx (0, 0, 0)).2.2 with hbj_def
  have hbi3 : bi ≤ 3 := by
    rw [hbi_def]; exact rrBasis5_getD_bi_le_three bidx hbidx
  -- `matrixA`'s `row = 0` branch, unfolded: `let` destructuring on
  -- `rrBasis5.getD bidx (0,0,0)` picks out exactly `bi`/`bj` as just
  -- defined (its first component, unused here, is left anonymous by
  -- `matrixA`'s own `let (_, bi, bj) := ...` pattern), and `⟨0,_⟩.val = 0`
  -- makes the `if row.val = 0 then ... else ...` reduce via `if_pos rfl`.
  have hentry : matrixA p c0 c1 c2 c3 c4 u0 u1 v0 v1 ⟨0, by norm_num⟩ col =
      (anchor1 p c0 c1 c2 c3 c4).1 ^ bi *
        (if bj = 1 then (anchor1 p c0 c1 c2 c3 c4).2 else 1) := by
    simp only [matrixA, hbidx_def.symm, hbi_def.symm, hbj_def.symm, if_true]
  rw [hentry]
  have hwx := anchor1_fst_totalDegree_le p c0 c1 c2 c3 c4 sg
  have hwy := anchor1_snd_totalDegree_le p c0 c1 c2 c3 c4 sg
  have hwitx := towerToRdec_isRdecWitness p c0 c1 c2 c3 c4 sg
    (anchor1 p c0 c1 c2 c3 c4).1 ι hι_t hι_w1 hι_w2
  have hwity := towerToRdec_isRdecWitness p c0 c1 c2 c3 c4 sg
    (anchor1 p c0 c1 c2 c3 c4).2 ι hι_t hι_w1 hι_w2
  -- `bi` is `set`-bound to `(rrBasis5.getD bidx (0,0,0)).2.1`; `induction`
  -- needs a genuinely free local variable, not one pinned by a `set`
  -- equation, so `clear_value bi` first drops the `let`-value, and
  -- `clear hbi_def` drops the separate equation hypothesis `set` also
  -- introduced (keeping just `bi` as a plain variable) — `clear_value`
  -- alone leaves `hbi_def` behind, and `induction bi` then tries to
  -- generalize over it too, corrupting the motive (REPL-confirmed).
  clear_value bi
  have hpow : IsRdecWitness p ι
      (algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p))))
      ((anchor1 p c0 c1 c2 c3 c4).1 ^ bi)
      ((towerToRdec p sg (anchor1 p c0 c1 c2 c3 c4).1).1 ^ bi,
        (towerToRdec p sg (anchor1 p c0 c1 c2 c3 c4).1).2 ^ bi) := by
    clear hbi3 hentry hbi_def
    induction bi with
    | zero => simp [IsRdecWitness]
    | succ k ih =>
        show IsRdecWitness p ι
          (algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p))))
          ((anchor1 p c0 c1 c2 c3 c4).1 ^ k * (anchor1 p c0 c1 c2 c3 c4).1)
          ((towerToRdec p sg (anchor1 p c0 c1 c2 c3 c4).1).1 ^ k *
              (towerToRdec p sg (anchor1 p c0 c1 c2 c3 c4).1).1,
            (towerToRdec p sg (anchor1 p c0 c1 c2 c3 c4).1).2 ^ k *
              (towerToRdec p sg (anchor1 p c0 c1 c2 c3 c4).1).2)
        exact IsRdecWitness.mul p ih hwitx
  by_cases hbj : bj = 1
  · -- `px ^ bi * py` branch: pointwise product of the two witnesses, via
    -- `IsRdecWitness.mul` applied to `px ^ bi`'s own witness (`hpow`,
    -- itself built from `bi` copies of `px`'s witness) and `py`'s witness
    -- directly.
    rw [if_pos hbj]
    refine ⟨((towerToRdec p sg (anchor1 p c0 c1 c2 c3 c4).1).1 ^ bi *
      (towerToRdec p sg (anchor1 p c0 c1 c2 c3 c4).2).1,
      (towerToRdec p sg (anchor1 p c0 c1 c2 c3 c4).1).2 ^ bi *
      (towerToRdec p sg (anchor1 p c0 c1 c2 c3 c4).2).2),
      IsRdecWitness.mul p hpow hwity, ?_, ?_⟩
    · show ((towerToRdec p sg (anchor1 p c0 c1 c2 c3 c4).1).1 ^ bi *
        (towerToRdec p sg (anchor1 p c0 c1 c2 c3 c4).2).1).totalDegree ≤ 24
      exact (anchorPow_mul_totalDegree_le p _ _ _ _ hbi3
        hwx.1 hwx.2 hwy.1 hwy.2).1
    · show ((towerToRdec p sg (anchor1 p c0 c1 c2 c3 c4).1).2 ^ bi *
        (towerToRdec p sg (anchor1 p c0 c1 c2 c3 c4).2).2).totalDegree ≤ 20
      exact (anchorPow_mul_totalDegree_le p _ _ _ _ hbi3
        hwx.1 hwx.2 hwy.1 hwy.2).2
  · -- `px ^ bi * 1` branch. Its own bound (`anchorPow_totalDegree_le`) is
    -- `≤21`/`≤18`, tighter than the shared `≤24`/`≤20` this theorem states
    -- (which has to cover the `bj=1` branch too) — `le_trans` widens.
    rw [if_neg hbj, mul_one]
    refine ⟨((towerToRdec p sg (anchor1 p c0 c1 c2 c3 c4).1).1 ^ bi,
      (towerToRdec p sg (anchor1 p c0 c1 c2 c3 c4).1).2 ^ bi), hpow, ?_, ?_⟩
    · show ((towerToRdec p sg (anchor1 p c0 c1 c2 c3 c4).1).1 ^ bi).totalDegree ≤ 24
      exact le_trans (anchorPow_totalDegree_le p _ _ hbi3 hwx.1 hwx.2).1 (by norm_num)
    · show ((towerToRdec p sg (anchor1 p c0 c1 c2 c3 c4).1).2 ^ bi).totalDegree ≤ 20
      exact le_trans (anchorPow_totalDegree_le p _ _ hbi3 hwx.1 hwx.2).2 (by norm_num)

/-- **`matrixA row col`'s value, for `row.val = 1`, has an explicit
`IsRdecWitness` pair with a `totalDegree` bound.** The direct `anchor2`
companion to `matrixA_row0_totalDegree_le` above — `matrixA`'s `row = 1`
branch is `px ^ bi * (if bj = 1 then py else 1)` for `(px,py) := anchor2
p c0 c1 c2 c3 c4` in place of `anchor1`, everything else (the `bi`/`bj`
extraction from `rrBasis5.getD`, the `IsRdecWitness.mul`-by-induction
witness for `px^bi`, the `bj=1`/`bj≠1` case split, the final degree
bounds `≤24`/`≤20`) identical in shape. The one genuine difference from
`row = 0`'s own unfolding: `⟨1, _⟩.val = 1` makes `matrixA`'s `if row.val
= 0 then ... else if row.val = 1 then ... else ...` reduce via `if_neg`
(on the first branch, since `1 ≠ 0`) then `if_pos rfl`/`if_true` (on the
second), rather than `row = 0`'s single `if_true` — `simp` handles both
steps together via `Nat.one_ne_zero`/`if_true` in the same `simp only`
call, no separate `if_neg` needed as a tactic step. -/
theorem matrixA_row1_totalDegree_le {Vars : Type*} [DecidableEq Vars]
    (sg : SideGens Vars) (u0 u1 v0 v1 : F p) (col : Fin 4)
    (ι : K2 p c0 c1 c2 c3 c4 →+* FractionRing (MvPolynomial Vars (F p)))
    (hι_t : ∀ i : Fin 2, ι (algebraMap (K1 p c0 c1 c2 c3 c4) (K2 p c0 c1 c2 c3 c4)
        (algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4)
          (algebraMap (MvPolynomial (Fin 2) (F p)) (K0 p) (MvPolynomial.X i)))) =
      algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p)))
        (MvPolynomial.X (sg.tGen i)))
    (hι_w1 : ι (algebraMap (K1 p c0 c1 c2 c3 c4) (K2 p c0 c1 c2 c3 c4) (w1 p c0 c1 c2 c3 c4)) =
      algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p)))
        (MvPolynomial.X (sg.wGen 0)))
    (hι_w2 : ι (w2 p c0 c1 c2 c3 c4) =
      algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p)))
        (MvPolynomial.X (sg.wGen 1)))
    (hbidx : otherIdx.getD col.val 0 < 5) :
    ∃ nd : MvPolynomial Vars (F p) × MvPolynomial Vars (F p),
      IsRdecWitness p ι
        (algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p))))
        (matrixA p c0 c1 c2 c3 c4 u0 u1 v0 v1 ⟨1, by norm_num⟩ col)
        nd ∧ nd.1.totalDegree ≤ 24 ∧ nd.2.totalDegree ≤ 20 := by
  set bidx := otherIdx.getD col.val 0 with hbidx_def
  set bi := (rrBasis5.getD bidx (0, 0, 0)).2.1 with hbi_def
  set bj := (rrBasis5.getD bidx (0, 0, 0)).2.2 with hbj_def
  have hbi3 : bi ≤ 3 := by
    rw [hbi_def]; exact rrBasis5_getD_bi_le_three bidx hbidx
  have hentry : matrixA p c0 c1 c2 c3 c4 u0 u1 v0 v1 ⟨1, by norm_num⟩ col =
      (anchor2 p c0 c1 c2 c3 c4).1 ^ bi *
        (if bj = 1 then (anchor2 p c0 c1 c2 c3 c4).2 else 1) := by
    simp only [matrixA, hbidx_def.symm, hbi_def.symm, hbj_def.symm]
    rw [if_neg (by norm_num : ¬ (1 : ℕ) = 0), if_true]
  rw [hentry]
  have hwx := anchor2_fst_totalDegree_le p c0 c1 c2 c3 c4 sg
  have hwy := anchor2_snd_totalDegree_le p c0 c1 c2 c3 c4 sg
  have hwitx := towerToRdec_isRdecWitness p c0 c1 c2 c3 c4 sg
    (anchor2 p c0 c1 c2 c3 c4).1 ι hι_t hι_w1 hι_w2
  have hwity := towerToRdec_isRdecWitness p c0 c1 c2 c3 c4 sg
    (anchor2 p c0 c1 c2 c3 c4).2 ι hι_t hι_w1 hι_w2
  clear_value bi
  have hpow : IsRdecWitness p ι
      (algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p))))
      ((anchor2 p c0 c1 c2 c3 c4).1 ^ bi)
      ((towerToRdec p sg (anchor2 p c0 c1 c2 c3 c4).1).1 ^ bi,
        (towerToRdec p sg (anchor2 p c0 c1 c2 c3 c4).1).2 ^ bi) := by
    clear hbi3 hentry hbi_def
    induction bi with
    | zero => simp [IsRdecWitness]
    | succ k ih =>
        show IsRdecWitness p ι
          (algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p))))
          ((anchor2 p c0 c1 c2 c3 c4).1 ^ k * (anchor2 p c0 c1 c2 c3 c4).1)
          ((towerToRdec p sg (anchor2 p c0 c1 c2 c3 c4).1).1 ^ k *
              (towerToRdec p sg (anchor2 p c0 c1 c2 c3 c4).1).1,
            (towerToRdec p sg (anchor2 p c0 c1 c2 c3 c4).1).2 ^ k *
              (towerToRdec p sg (anchor2 p c0 c1 c2 c3 c4).1).2)
        exact IsRdecWitness.mul p ih hwitx
  by_cases hbj : bj = 1
  · rw [if_pos hbj]
    refine ⟨((towerToRdec p sg (anchor2 p c0 c1 c2 c3 c4).1).1 ^ bi *
      (towerToRdec p sg (anchor2 p c0 c1 c2 c3 c4).2).1,
      (towerToRdec p sg (anchor2 p c0 c1 c2 c3 c4).1).2 ^ bi *
      (towerToRdec p sg (anchor2 p c0 c1 c2 c3 c4).2).2),
      IsRdecWitness.mul p hpow hwity, ?_, ?_⟩
    · show ((towerToRdec p sg (anchor2 p c0 c1 c2 c3 c4).1).1 ^ bi *
        (towerToRdec p sg (anchor2 p c0 c1 c2 c3 c4).2).1).totalDegree ≤ 24
      exact (anchorPow_mul_totalDegree_le p _ _ _ _ hbi3
        hwx.1 hwx.2 hwy.1 hwy.2).1
    · show ((towerToRdec p sg (anchor2 p c0 c1 c2 c3 c4).1).2 ^ bi *
        (towerToRdec p sg (anchor2 p c0 c1 c2 c3 c4).2).2).totalDegree ≤ 20
      exact (anchorPow_mul_totalDegree_le p _ _ _ _ hbi3
        hwx.1 hwx.2 hwy.1 hwy.2).2
  · rw [if_neg hbj, mul_one]
    refine ⟨((towerToRdec p sg (anchor2 p c0 c1 c2 c3 c4).1).1 ^ bi,
      (towerToRdec p sg (anchor2 p c0 c1 c2 c3 c4).1).2 ^ bi), hpow, ?_, ?_⟩
    · show ((towerToRdec p sg (anchor2 p c0 c1 c2 c3 c4).1).1 ^ bi).totalDegree ≤ 24
      exact le_trans (anchorPow_totalDegree_le p _ _ hbi3 hwx.1 hwx.2).1 (by norm_num)
    · show ((towerToRdec p sg (anchor2 p c0 c1 c2 c3 c4).1).2 ^ bi).totalDegree ≤ 20
      exact le_trans (anchorPow_totalDegree_le p _ _ hbi3 hwx.1 hwx.2).2 (by norm_num)

/-! ## Status, latest pass

**Attempted this pass**: `matrixA_row0_totalDegree_le`, the `row = 0`
entry witness/degree theorem — the assembly step `TowerToRdecMul.lean`
and this file's own earlier status note both flagged as next. **No
`sorry`** — an earlier draft in this same pass left the witness-validity
goal as `sorry` in both branches while the degree bounds were filled in;
per this project's rule against leaving `sorry` in as a placeholder
rather than working out the actual argument, that draft was replaced with
a real proof before finalizing this file: `px^bi`'s own witness is built
by induction on `bi` (`IsRdecWitness.mul` applied `bi` times to `px`'s own
`towerToRdec_isRdecWitness` witness, base case `bi=0` closing by `simp`
since `IsRdecWitness _ _ 1 (1,1)` is `1 = 1*1`), then combined with `py`'s
witness (`bj=1` branch) or left bare (`bj≠1` branch, `mul_one`) via one
more `IsRdecWitness.mul` — no gap left unproved.

**Build errors found and fixed, this pass (Claire's REPL)**:
1. `rrBasis5_getD_bi_le_three` takes no `p` argument (`rrBasis5` and its
   lemmas, `RRBasisTotalDegree.lean`, are entirely `p`-independent — no
   `variable (p ...)` in that file) — the call site wrongly passed `p`
   first, matching this file's own `variable (p ...)` convention rather
   than checking the callee's actual signature.
2. `hentry`'s `simp only [matrixA, ...]` call left a residual `(if True
   then X else Y) = X` goal — `if_pos rfl` (the lemma originally in the
   simp set) never fired because `decide`-normalization inside `simp`
   already reduced `⟨0,_⟩.val = 0` to the literal `True` before `if_pos`
   could match on `rfl`; replaced with `if_true`, which directly closes
   `if True then X else Y = X`.
3. `induction bi` inside `hpow`'s proof corrupted its own motive
   (`CommRing` instance mismatch on `rw [pow_succ]`) — `clear_value bi`
   detaches `bi`'s `let`-value but leaves the SEPARATE equation
   hypothesis `hbi_def : bi = (rrBasis5.getD bidx (0,0,0)).2.1` (`set`'s
   own naming) in context; `induction bi` then tries to generalize over
   `hbi_def` too, since it mentions `bi`, producing a malformed motive.
   Fixed by `clear hbi3 hentry hbi_def` (not just `hbi3 hentry`) right
   before the `induction` call.
4. The assembly theorem's own stated bound, `nd.2.totalDegree ≤ 21`, was
   wrong — `anchorPow_mul_totalDegree_le` (the `bj=1` branch) proves
   `≤20` on that side, not `≤21` (`anchorPow_totalDegree_le`, the `bj≠1`
   branch, proves `≤21`/`≤18` — the two branches have DIFFERENT bounds,
   and the shared statement needs the pointwise max, `≤24`/`≤20`, not a
   number copied from the wrong branch). Fixed the theorem statement to
   `≤24 ∧ ≤20`, and added `show`+`le_trans` in the `bj≠1` branch to widen
   its own tighter `≤21`/`≤18` up to the shared `≤24`/`≤20`.
5. Both branches' final two goals showed as `(a,b).1.totalDegree ≤ N`/
   `(a,b).2.totalDegree ≤ N` rather than reducing to `a.totalDegree ≤ N`/
   `b.totalDegree ≤ N` after `refine ⟨(a,b), ..., ?_, ?_⟩` — Lean does not
   automatically project through the anonymous pair constructor here;
   added an explicit `show` restating each goal in reduced form before
   `exact`/`le_trans`.

**The one place this pass's confidence is still genuinely lower**:
`hentry`'s overall unfolding strategy (`simp only [matrixA, ...]`) is now
REPL-confirmed to work (per the fixes above, which came from Claire's
actual build errors, not further blind guessing) — but this was the
`let`-elaboration territory this file's earlier status note and
`CramerEntryTotalDegree.lean`'s own documented build-error history both
flagged as needing a real build to pin down, and it took multiple
REPL-reported errors to get right rather than being correct on the first
attempt, so any structurally similar unfolding elsewhere in this file
(`row = 1`/`row = 2`/`row = 3`, not yet attempted) should expect the same
and not assume the `row = 0` fix pattern transfers without its own
REPL check.

**`row = 1`** (companion, `anchor2` in place of `anchor1`) now drafted —
see `matrixA_row1_totalDegree_le` and pass #3's status note below for
what transferred directly from `row = 0`'s confirmed fixes and what's
still genuinely untested about it (the two-level `if` unfolding).
**`row = 2`/`row = 3`** (the `reduceMonomialModU` rows) are NOT yet
connected here either, though their underlying degree fact
(`algebraMap_Fp_towerToRdec_totalDegree_eq`, this file, above) is already
proved — same unfolding risk applies there too, and per this pass's
experience, budget for at least one round of REPL-driven fixes rather
than expecting it to close on the first attempt.

**Build errors found and fixed, this pass #2 (Claire's REPL)**:
6. `hpow`'s `succ` case (`induction bi`) failed with "motive is not type
   correct" on `rw [pow_succ, pow_succ, pow_succ]` — rewriting the
   `^(k+1)` pattern directly inside the ambient goal tries to abstract a
   motive over a term whose type carries `K2 p c0 c1 c2 c3 c4`'s
   `CommRing` instance (built via `AdjoinRoot`), and that instance
   doesn't survive the abstraction, so `rw` produces an ill-typed motive.
   Fixed by replacing the three `rw [pow_succ]`s with a single `show`
   that restates the goal in its already-expanded (`^k * _`) form
   directly — valid because `a^(k+1)` is definitionally `a^k * a` for
   `Monoid.npow` in Lean4 Mathlib, so `show` closes by defeq with no
   motive abstraction at all, then `IsRdecWitness.mul p ih hwitx` closes
   it directly.
7. `anchorPow_totalDegree_le`'s call sites (`le_trans (anchorPow_
   totalDegree_le ...).1 (by norm_num)`) failed with an application type
   mismatch: the lemma's STATED conclusion was `(nx^bi * 1).totalDegree
   ≤ 21`, but its proof opened with `simp only [mul_one]`, so the actual
   term produced proves `(nx^bi).totalDegree ≤ 21` — a mismatch between
   the stated type and the elaborated proof term once Lean tries to
   unify it against `le_trans`'s expected argument. Fixed by dropping
   the spurious `* 1` from the theorem's stated conclusion (and the
   now-redundant `simp only [mul_one]` from its proof) so the signature
   matches what the proof actually produces; no change needed at the
   call sites, which already expected the `* 1`-free form.

**Superseded by this pass's fixes above** (kept for history): earlier
status notes in this file described `anchorPow_mul_totalDegree_le`/
`anchorPow_totalDegree_le` as using `interval_cases bi`, then as using
`gcongr`, before landing on the current `nlinarith`-based proof (see
those theorems' own doc comments above for the final, correct version);
described `matrixA`/`rhsVec`'s entry theorem as "still unstarted" (no
longer true — `matrixA_row0_totalDegree_le`, this pass, is a first
instance of it); and stated the assembly bound as `≤24`/`≤21` before this
pass's fix #4 above corrected it to `≤24`/`≤20`.

**Drafted this pass #3, then REPL-fixed (Claire's actual build error)**:
`matrixA_row1_totalDegree_le`, the `anchor2` companion to `matrixA_row0_
totalDegree_le` — same shape throughout (`bi`/`bj` extraction, the
`IsRdecWitness.mul`-by-induction witness for `px^bi`, the `bj=1`/`bj≠1`
split, `≤24`/`≤20`), `anchor2`/`anchor2_fst_totalDegree_le`/`anchor2_
snd_totalDegree_le` in place of `anchor1`'s versions throughout.

8. `hentry`'s unfolding is genuinely a THREE-clause sequential `if
   row.val = 0 then ... else if row.val = 1 then ... else ...` chain
   (`matrixA`'s actual definition, `DataDerivationSolve.lean` — not a
   two-level nested `if` as this file's earlier speculative note
   guessed). `simp only [matrixA, hbidx_def.symm, hbi_def.symm, hbj_def.
   symm]` alone left BOTH conditions only partially processed: the outer
   `row.val = 0` condition stayed as the literal unreduced proposition
   `1 = 0` (needing `norm_num`/`decide` to discharge, since it's not
   already a boolean literal), while the middle clause's condition
   `row.val = 1` got `decide`-normalized to the literal `True` but NOT
   consumed into its branch (i.e. `simp` decided the condition without
   applying the resulting `if True then a else b = a` step) — contrary
   to this file's earlier guess that the inner clause would fully
   collapse on its own the way `row0`'s single clause did. Two rounds
   of REPL-reported errors, two additive fixes: first `rw [if_neg (by
   norm_num : ¬ (1 : ℕ) = 0)]` to discharge the outer clause (leaving
   exactly `if True then (anchor2 branch) else (dead row.val=2/3
   branch)` as the remaining goal, confirmed by the second error's
   exact goal text), then `rw [..., if_true]` chained onto the same
   `rw` call to consume the literal-`True` middle clause and close by
   the trailing `rfl`. **Lesson for `row = 2`/`row = 3`, corrected from
   the wrong first guess**: don't assume `simp only [matrixA, ...]`
   alone resolves ANY clause of this three-way `if` chain to a literal
   applied branch — expect to need explicit `if_neg (by norm_num : ...)`
   for numeral-inequality clauses and explicit `if_true`/`if_pos rfl`
   for already-`decide`d-true clauses, chained together in one `rw`,
   checked against the actual REPL-reported goal rather than guessed
   from the file's structure alone.

**`row = 2`/`row = 3` (the `reduceMonomialModU` rows) remain
undrafted** — expect the SAME three-clause `if`-chain unfolding
difficulty as `row = 1` (fix #8, corrected above), likely needing TWO
`if_neg`s (both `row.val = 0` and `row.val = 1` are false at `row = 2`
or `row = 3`) before reaching the final `else` branch's own inner `if
row.val = 2` split — send to the REPL early and iterate on the actual
reported goal shape rather than assuming the pattern from `row0`/`row1`
transfers cleanly. Their shape differs more besides (no `bj=1`/`bj≠1`
witness-combination split, just `algebraMap_Fp_towerToRdec_totalDegree_
eq` directly, already proved above in this file). -/

end TheDataDerivation
end Genus2Lean
