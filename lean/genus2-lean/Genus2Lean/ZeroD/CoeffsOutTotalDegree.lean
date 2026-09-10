import Mathlib
import Genus2Lean.ZeroD.CramerWitnessAssembly
import Genus2Lean.ZeroD.MatrixEntryTotalDegree
import Genus2Lean.ZeroD.RhsVecTotalDegree

/-!
# `cramerSolution`'s own `totalDegree` bound, assembled

New this pass. `ROADMAP-crossnondegenerate-degree-bound.md`'s remaining
assembly step, per `CramerWitnessAssembly.lean`'s own closing note: compose
`cramerSolution_isRdecWitness_of_entries` (gives an `IsRdecWitness` pair for
`Matrix.cramer M rhs i`, no `totalDegree` bound attached) with
`matrixA_entry_totalDegree_le`/`rhsVec_entry_totalDegree_le` (give a
per-entry `IsRdecWitness` witness WITH an explicit `totalDegree` bound, but
only existentially — `∃ nd, IsRdecWitness ... nd ∧ nd.1.totalDegree ≤ D₁ ∧
nd.2.totalDegree ≤ D₂`, not a named `a`/`b` pair) plus
`cramerNumeratorDet_totalDegree_le`/`prod_totalDegree_le` (bound the
resulting witness pair's own `totalDegree`, `DataDerivationTotalDegree.lean`).

**The existential-vs-named mismatch, resolved via `Classical.choose`**:
`cramerSolution_isRdecWitness_of_entries` is stated for explicit witness
functions `a b : n → n → MvPolynomial Vars (F p)` (so its conclusion's
witness pair can be written down explicitly, matching `cramerDenom_det_eq`'s
own `C`). `matrixA_entry_totalDegree_le`/`rhsVec_entry_totalDegree_le` only
assert existence of SOME witness with a bounded degree, per entry. Since a
downstream `totalDegree` bound only needs SOME valid witness (not the
canonical one — `TowerToRdecMul.lean`'s own header makes exactly this
point about `IsRdecWitness` generally), extracting `Classical.choose` from
each of the 16 (`matrixA`) + 4 (`rhsVec`) existentials and feeding the
results into `cramerSolution_isRdecWitness_of_entries` as `a`/`b`/`ea`/`eb`
is legitimate, not a hack.

**What this needs as a genuinely open hypothesis, not yet resolved anywhere
in this project**: `cramerSolution_isRdecWitness_of_entries` requires
`evalNd (b i j) ≠ 0`/`evalNd (eb j) ≠ 0` — the CHOSEN witness denominators
are nonzero — which is NOT the same fact as `MatrixNondegenerate`
(`matrixA.det ≠ 0`), and no bridge between the two exists anywhere in this
project as of this pass (checked: `MatrixNondegenerate` is used nowhere
near `IsRdecWitness`/`towerToRdec` outside `DecoupledSystemRegular.lean`'s
own unrelated definition site). Per this project's own practice (weaken to
a named, checkable hypothesis rather than assume or `sorry`), this file
takes per-entry witness-denominator nonvanishing as an explicit hypothesis,
stated directly against the `Classical.choose`-extracted `b`/`eb` (not
packaged into a separate `def` — a `def`-wrapped `Prop` would need an
explicit `unfold`/`show` at the call site to line up with `cramerSolution_
isRdecWitness_of_entries`'s own implicit-argument shape by defeq, an
avoidable fragility; inlining the `∀ row col, evalNd (b row col) ≠ 0`
statement directly into the theorem signature, against the SAME `b` the
proof itself later `set`s, sidesteps that entirely) rather than deriving it
from `MatrixNondegenerate` — that derivation (if even true; the chosen
witness could in principle vanish at a point where `matrixA.det` itself
doesn't) is flagged as separate future work, not attempted here.

**`cramerSolution_totalDegree_le`: REPL-confirmed green** (Claire's build,
after fixing the `D := 24`/`D := 20` numerator/denominator mismatch this
pass — see that theorem's own `calc` blocks). **`coeffsOut_yIdx_isRdecWitness`
(added same pass, below): not yet REPL-confirmed** — Claire tests next.
-/

namespace Genus2Lean
namespace TheDataDerivation

open Polynomial

variable (p : ℕ) [hp : Fact (Nat.Prime p)] [hp2 : Fact (p ≠ 2)]
variable (c0 c1 c2 c3 c4 : F p)

set_option maxHeartbeats 2000000 in
/-- **`cramerSolution`'s own `totalDegree` bound — the actual assembly
target.** Given per-entry witness-denominator nonvanishing for both
`matrixA` and `rhsVec` (`hAne`/`hRne` — see this file's header for why
these are taken as hypotheses rather than derived from `MatrixNondegenerate`),
`Matrix.cramer (matrixA ...) (rhsVec ...) i`'s `Classical.choose`-extracted
`IsRdecWitness` numerator/denominator pair has `totalDegree ≤ 4^2 * 24 =
384` (numerator, via `cramerNumeratorDet_totalDegree_le` at `D := 24`,
`matrixA`'s own witness-numerator bound, `Fintype.card (Fin 4) = 4`) and
`≤ 4^2 * 20 = 320` (denominator, via `prod_totalDegree_le` applied twice
at `D := 20`, `matrixA`'s own witness-denominator bound) — `rhsVec`'s
tighter `≤7`/`≤6` bounds don't affect either number, since the assembled
pair's shape (per `cramerSolution_isRdecWitness_of_entries`) only ever uses
`rhsVec`'s witnesses at the SINGLE column `i` (the `if j = i then ea/eb
else a/b` split), so the uniform `matrixA`-side bound `D := 24`/`20` (the
max of the two entry bounds, `24 ≥ 7`, `20 ≥ 6`) safely covers both
branches uniformly, avoiding a `max`/case-split in the final numeral. Both
`hAne`/`hRne` are stated directly against the SAME `Classical.choose`
extraction the proof itself later `set`s as `b`/`eb`, so they line up with
`cramerSolution_isRdecWitness_of_entries`'s implicit `b`/`eb` arguments by
literal syntactic match once `set` folds them, not merely by defeq. -/
theorem cramerSolution_totalDegree_le {Vars : Type*} [DecidableEq Vars]
    (sg : SideGens Vars) (u0 u1 v0 v1 : F p)
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
    (hbidx : ∀ col : Fin 4, otherIdx.getD col.val 0 < 5)
    (hAne : ∀ row col : Fin 4,
      (algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p))))
        ((matrixA_entry_totalDegree_le p c0 c1 c2 c3 c4 sg u0 u1 v0 v1 row col ι
          hι_t hι_w1 hι_w2 (hbidx col)).choose.2) ≠ 0)
    (hRne : ∀ row : Fin 4,
      (algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p))))
        ((rhsVec_entry_totalDegree_le p c0 c1 c2 c3 c4 sg u0 u1 v0 v1 row ι
          hι_t hι_w1 hι_w2).choose.2) ≠ 0) (i : Fin 4) :
    ∃ nd : MvPolynomial Vars (F p) × MvPolynomial Vars (F p),
      IsRdecWitness p ι
        (algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p))))
        ((matrixA p c0 c1 c2 c3 c4 u0 u1 v0 v1).cramer
          (rhsVec p c0 c1 c2 c3 c4 u0 u1 v0 v1) i)
        nd ∧ nd.1.totalDegree ≤ 384 ∧ nd.2.totalDegree ≤ 320 := by
  classical
  set evalNd := algebraMap (MvPolynomial Vars (F p))
    (FractionRing (MvPolynomial Vars (F p))) with hevalNd
  set a : Fin 4 → Fin 4 → MvPolynomial Vars (F p) := fun row col =>
    (matrixA_entry_totalDegree_le p c0 c1 c2 c3 c4 sg u0 u1 v0 v1 row col ι
      hι_t hι_w1 hι_w2 (hbidx col)).choose.1 with ha_def
  set b : Fin 4 → Fin 4 → MvPolynomial Vars (F p) := fun row col =>
    (matrixA_entry_totalDegree_le p c0 c1 c2 c3 c4 sg u0 u1 v0 v1 row col ι
      hι_t hι_w1 hι_w2 (hbidx col)).choose.2 with hb_def
  set ea : Fin 4 → MvPolynomial Vars (F p) := fun row =>
    (rhsVec_entry_totalDegree_le p c0 c1 c2 c3 c4 sg u0 u1 v0 v1 row ι
      hι_t hι_w1 hι_w2).choose.1 with hea_def
  set eb : Fin 4 → MvPolynomial Vars (F p) := fun row =>
    (rhsVec_entry_totalDegree_le p c0 c1 c2 c3 c4 sg u0 u1 v0 v1 row ι
      hι_t hι_w1 hι_w2).choose.2 with heb_def
  have hwit : ∀ row col : Fin 4, IsRdecWitness p ι evalNd
      (matrixA p c0 c1 c2 c3 c4 u0 u1 v0 v1 row col) (a row col, b row col) := by
    intro row col
    exact (matrixA_entry_totalDegree_le p c0 c1 c2 c3 c4 sg u0 u1 v0 v1 row col ι
      hι_t hι_w1 hι_w2 (hbidx col)).choose_spec.1
  have ha_bound : ∀ row col : Fin 4, (a row col).totalDegree ≤ 24 := fun row col =>
    (matrixA_entry_totalDegree_le p c0 c1 c2 c3 c4 sg u0 u1 v0 v1 row col ι
      hι_t hι_w1 hι_w2 (hbidx col)).choose_spec.2.1
  have hb_bound : ∀ row col : Fin 4, (b row col).totalDegree ≤ 20 := fun row col =>
    (matrixA_entry_totalDegree_le p c0 c1 c2 c3 c4 sg u0 u1 v0 v1 row col ι
      hι_t hι_w1 hι_w2 (hbidx col)).choose_spec.2.2
  have hwitRhs : ∀ row : Fin 4, IsRdecWitness p ι evalNd
      (rhsVec p c0 c1 c2 c3 c4 u0 u1 v0 v1 row) (ea row, eb row) := by
    intro row
    exact (rhsVec_entry_totalDegree_le p c0 c1 c2 c3 c4 sg u0 u1 v0 v1 row ι
      hι_t hι_w1 hι_w2).choose_spec.1
  have hea_bound : ∀ row : Fin 4, (ea row).totalDegree ≤ 7 := fun row =>
    (rhsVec_entry_totalDegree_le p c0 c1 c2 c3 c4 sg u0 u1 v0 v1 row ι
      hι_t hι_w1 hι_w2).choose_spec.2.1
  have heb_bound : ∀ row : Fin 4, (eb row).totalDegree ≤ 6 := fun row =>
    (rhsVec_entry_totalDegree_le p c0 c1 c2 c3 c4 sg u0 u1 v0 v1 row ι
      hι_t hι_w1 hι_w2).choose_spec.2.2
  refine ⟨_, cramerSolution_isRdecWitness_of_entries p hwit hAne hwitRhs hRne i, ?_, ?_⟩
  · -- Numerator: `cramerNumeratorDet_totalDegree_le` at the merged bound `D := 24`,
    -- since every factor in the assembled witness's numerator is either an
    -- `a row col` (`≤ 24`) or an `ea row`/`eb row` (`≤ 7`/`≤ 6`, both `≤ 24`).
    have hnum := cramerNumeratorDet_totalDegree_le p
      (D := 24)
      (fun row col => if col = i then ea row else a row col)
      (fun row col => if col = i then eb row else b row col)
      (by intro row col; split_ifs
          · exact (hea_bound row).trans (by norm_num)
          · exact ha_bound row col)
      (by intro row col; split_ifs
          · exact (heb_bound row).trans (by norm_num)
          · exact (hb_bound row col).trans (by norm_num))
    calc _ ≤ (Fintype.card (Fin 4)) ^ 2 * 24 := hnum
      _ = 384 := by simp
  · -- Denominator: `prod_totalDegree_le` applied twice at the merged bound `D := 20`
    -- (matrixA's own witness-denominator bound; `eb`'s tighter `≤ 6` is also `≤ 20`).
    have hrow : ∀ row : Fin 4,
        (∏ col, (if col = i then eb row else b row col)).totalDegree ≤ 4 * 20 := by
      intro row
      have h := prod_totalDegree_le p (D := 20)
        (fun col => if col = i then eb row else b row col)
        (by intro col; split_ifs
            · exact (heb_bound row).trans (by norm_num)
            · exact hb_bound row col)
      simpa using h
    have hcol := prod_totalDegree_le p (D := 4 * 20)
      (fun row => ∏ col, (if col = i then eb row else b row col)) hrow
    calc (∏ row, ∏ col, (if col = i then eb row else b row col)).totalDegree
        ≤ Fintype.card (Fin 4) * (4 * 20) := hcol
      _ = 320 := by simp

/-- **`coeffsOut`'s `yIdx` slot — the trivial `= 1` case.** `coeffsOut`
takes the value `1 : K2 p c0 c1 c2 c3 c4` at `yIdx` (by its own `dif_pos`
branch), and `IsRdecWitness p ι evalNd 1 (1, 1)` holds unconditionally —
`evalNd 1 = 1 = 1 * ι 1 = evalNd 1 * ι 1` via `map_one` on both `evalNd`
and `ι`, no `Classical.choose`/tower induction needed at all, matching
this file's header note that this slot is `IsRdecWitness`'s own
reflexivity-style base case. Bound `(0, 0)`, both trivially `≤ 384`/`≤ 320`
so the same numerals as `cramerSolution_totalDegree_le` cover both slots
uniformly with no `max`/case-split needed downstream. -/
theorem coeffsOut_yIdx_isRdecWitness {Vars : Type*} [DecidableEq Vars]
    (ι : K2 p c0 c1 c2 c3 c4 →+* FractionRing (MvPolynomial Vars (F p))) :
    ∃ nd : MvPolynomial Vars (F p) × MvPolynomial Vars (F p),
      IsRdecWitness p ι
        (algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p))))
        (1 : K2 p c0 c1 c2 c3 c4) nd ∧
      nd.1.totalDegree ≤ 384 ∧ nd.2.totalDegree ≤ 320 := by
  refine ⟨(1, 1), ?_, ?_, ?_⟩
  · show (algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p)))) 1 =
      (algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p)))) 1 * ι 1
    simp
  · simp [MvPolynomial.totalDegree_one]
  · simp [MvPolynomial.totalDegree_one]

/-! ## Status, this pass

**Drafted, not yet REPL-confirmed.** Assembles `cramerSolution_
isRdecWitness_of_entries` (`CramerWitnessAssembly.lean`) with `matrixA_
entry_totalDegree_le`/`rhsVec_entry_totalDegree_le` (`MatrixEntryTotalDegree.
lean`/`RhsVecTotalDegree.lean`) via `Classical.choose` on the two entry
theorems' existentials, giving `cramerSolution_totalDegree_le` — a
`totalDegree` bound on `Matrix.cramer matrixA rhsVec i`'s own
`IsRdecWitness` pair, conditional on two per-entry witness-denominator
nonvanishing hypotheses (`hAne`/`hRne`, inlined directly into the theorem
signature rather than packaged into a separate `def` — see the header for
why) that this file does NOT derive from `MatrixNondegenerate` — see the
header for why that's a separate, unattempted piece of work, not an
oversight.

**One risk from an earlier draft was found and removed before finalizing,
not left for the REPL to catch**: the numerator/denominator `calc` steps
originally used `apply cramerNumeratorDet_totalDegree_le p _ _ ?_ ?_
|>.trans (by norm_num)`/`apply prod_totalDegree_le p _ ?_ |>.trans (...)`,
relying on `apply` to unify the callee's implicit `D` against numeral
bounds supplied only in the side goals — fragile, and with no precedent
elsewhere in this codebase. Replaced with `have hnum := ... (D := 24) ...`/
`have h := ... (D := 24) ...`, pinning `D` explicitly by named argument
before the `calc`, then a plain `calc _ ≤ (Fintype.card (Fin 4))^2 * 24 :=
hnum; _ = 384 := by simp` (and the denominator's two-level analogue) —
`simp` closes `Fintype.card (Fin 4) = 4`-style arithmetic via
`Fintype.card_fin`, the same pattern this project's own `cramerDeltaA_
totalDegree_le` (`DataDerivationTotalDegree.lean`) already uses
successfully for the identical `Fintype.card (Fin 4) * (4 * D) = 16 * D`
shape.

**What this closes**: `coeffsOut`'s bound at every `otherIdx` slot
(`cramerSolution_totalDegree_le`) AND at the remaining `yIdx` slot
(`coeffsOut_yIdx_isRdecWitness`, added this pass — the trivial `= 1` case,
witness `(1,1)`, bound `(0,0)`, both `≤ 384`/`≤ 320` so no `max`/case-split
is needed to cover both slots with the same two numerals). `coeffsOut`'s
own `totalDegree` bound is now fully closed across all 5 slots, modulo the
two open `hAne`/`hRne` hypotheses `cramerSolution_totalDegree_le` still
carries (see this file's header). `Epoly`/`Ypoly`/`fAtX`/`Npoly`'s own
bounds (per `RhsVecTotalDegree.lean`'s closing note) are the next assembly
layer up, not attempted in this file. -/

end TheDataDerivation
end Genus2Lean
