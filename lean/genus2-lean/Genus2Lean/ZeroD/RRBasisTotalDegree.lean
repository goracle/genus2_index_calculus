import Mathlib
import Genus2Lean.ZeroD.TheDataDerivation.DataDerivationSolve

/-!
# `rrBasis5`'s order and `bi`-component bound

New this pass. Supplies the one combinatorial fact `CramerEntryTotalDegree.
lean`'s own status note leaves as "not yet done": a bound on `matrixA`/
`rhsVec`'s `bi` exponent (`rrBasis5.getD _ (0,0,0)`'s `.2.1` component),
needed to bound the `px ^ bi` factor in `matrixA`'s row-0/row-1 entries
(`ROADMAP-crossnondegenerate-degree-bound.md`'s remaining assembly item 1).

**Route**: reuses the exact witness-list technique already proved and
REPL-confirmed in `rrBasis5_bj_eq_zero_of_ne_yIdx`'s own proof
(`DataDerivationSolve.lean`, the `t.1 ≥ 7` exclusion branch) — five
explicit, pairwise-distinct, order-`≤6` candidates
(`(0,0,0),(2,1,0),(4,2,0),(5,0,1),(6,3,0)`) already sit in `rrBasis5`'s
sorted-and-take-5 construction, so a 6th, order-`≥7` element also landing
in `rrBasis5` would force six distinct elements into a 5-slot `Nodup`
list — a contradiction, via `List.Sorted.rel_of_mem_take_of_mem_drop` +
`Subperm.length_le`. That argument did not need the `bj=1` restriction
`rrBasis5_bj_eq_zero_of_ne_yIdx` layered on top of it — stated here in its
general form (`∀ t ∈ rrBasis5, t.1 ≤ 6`, no `bj` hypothesis), then
`rrBasisCandidates`'s own `(2i,i,0)`/`(2i+5,i,1)` shape converts `t.1 ≤ 6`
directly into `t.2.1 ≤ 3` (`i ≤ 3` either way: `2i ≤ 6 → i ≤ 3`,
`2i+5 ≤ 6 → i ≤ 0 ≤ 3`).

**REPL-confirmed green** (whole project build).
-/

namespace Genus2Lean
namespace TheDataDerivation

open Polynomial

/-- **Every `rrBasis5` element has order (first component) `≤ 6`.**
General form of the exclusion argument inside `rrBasis5_bj_eq_zero_of_ne_
yIdx`'s proof (`DataDerivationSolve.lean`), with the `bj = 1` restriction
dropped — the six-elements-in-five-slots contradiction only used `t`'s
membership in `rrBasis5` and the five fixed order-`≤6` witnesses, never
`t`'s own `bj` value. -/
theorem rrBasis5_order_le_six : ∀ t ∈ rrBasis5, t.1 ≤ 6 := by
  intro t htmem
  by_contra hgt
  push_neg at hgt
  have hwit_facts : ∀ w ∈ ([(0,0,0), (2,1,0), (4,2,0), (5,0,1), (6,3,0)] :
      List (ℕ × ℕ × ℕ)), w ∈ rrBasisCandidates 20 ∧ w.1 ≤ 6 := by
    intro w hw
    fin_cases hw <;> exact ⟨by decide, by norm_num⟩
  have hs : List.Pairwise (fun a b => decide (a.1 ≤ b.1) = true)
      ((rrBasisCandidates 20).mergeSort (fun a b => decide (a.1 ≤ b.1))) := by
    apply List.pairwise_mergeSort
    · intro a b c hab hbc
      exact decide_eq_true (Nat.le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc))
    · intro a b
      rcases Nat.le_total a.1 b.1 with h | h
      · simp [decide_eq_true h]
      · simp [decide_eq_true h]
  have htake5 : t ∈ ((rrBasisCandidates 20).mergeSort
      (fun a b => decide (a.1 ≤ b.1))).take 5 := htmem
  have hwitness_in_take : ∀ w ∈ ([(0,0,0), (2,1,0), (4,2,0), (5,0,1), (6,3,0)] :
      List (ℕ × ℕ × ℕ)),
      w ∈ ((rrBasisCandidates 20).mergeSort (fun a b => decide (a.1 ≤ b.1))).take 5 := by
    intro w hw
    obtain ⟨hwcand, hworder⟩ := hwit_facts w hw
    have hwmem : w ∈ (rrBasisCandidates 20).mergeSort (fun a b => decide (a.1 ≤ b.1)) :=
      (List.mem_mergeSort).mpr hwcand
    by_contra hwnottake
    have hwdrop : w ∈ ((rrBasisCandidates 20).mergeSort
        (fun a b => decide (a.1 ≤ b.1))).drop 5 := by
      have hsplit := List.take_append_drop 5 ((rrBasisCandidates 20).mergeSort
        (fun a b => decide (a.1 ≤ b.1)))
      rw [← hsplit, List.mem_append] at hwmem
      tauto
    have hrel := hs.rel_of_mem_take_of_mem_drop htake5 hwdrop
    have hle : t.1 ≤ w.1 := of_decide_eq_true hrel
    omega
  have hsub6 : ([(0,0,0), (2,1,0), (4,2,0), (5,0,1), (6,3,0), t] :
      List (ℕ × ℕ × ℕ)).Nodup := by
    have h0 : (0,0,0) ≠ t := by intro h; have := congrArg Prod.fst h; omega
    have h1 : (2,1,0) ≠ t := by intro h; have := congrArg Prod.fst h; omega
    have h2 : (4,2,0) ≠ t := by intro h; have := congrArg Prod.fst h; omega
    have h3 : (5,0,1) ≠ t := by intro h; have := congrArg Prod.fst h; omega
    have h4 : (6,3,0) ≠ t := by intro h; have := congrArg Prod.fst h; omega
    simp [List.nodup_cons, h0, h1, h2, h3, h4]
  have hsub6mem : ([(0,0,0), (2,1,0), (4,2,0), (5,0,1), (6,3,0), t] :
      List (ℕ × ℕ × ℕ)) ⊆ ((rrBasisCandidates 20).mergeSort
        (fun a b => decide (a.1 ≤ b.1))).take 5 := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with h | h | h | h | h | h
    · exact h ▸ hwitness_in_take _ (by simp)
    · exact h ▸ hwitness_in_take _ (by simp)
    · exact h ▸ hwitness_in_take _ (by simp)
    · exact h ▸ hwitness_in_take _ (by simp)
    · exact h ▸ hwitness_in_take _ (by simp)
    · exact h ▸ htake5
  have hsubperm : ([(0,0,0), (2,1,0), (4,2,0), (5,0,1), (6,3,0), t] :
      List (ℕ × ℕ × ℕ)).Subperm (((rrBasisCandidates 20).mergeSort
        (fun a b => decide (a.1 ≤ b.1))).take 5) :=
    List.Nodup.subperm hsub6 hsub6mem
  have hlen6 : ([(0,0,0), (2,1,0), (4,2,0), (5,0,1), (6,3,0), t] :
      List (ℕ × ℕ × ℕ)).length ≤ (((rrBasisCandidates 20).mergeSort
        (fun a b => decide (a.1 ≤ b.1))).take 5).length := hsubperm.length_le
  simp only [List.length_cons, List.length_take] at hlen6
  omega

/-- **Every `rrBasis5` element's `bi`-component (`.2.1`) is `≤ 3`.**
Converts `rrBasis5_order_le_six`'s order bound via `rrBasisCandidates`'s
own `(2i,i,0)`/`(2i+5,i,1)` shape: `t ∈ rrBasisCandidates 20` (from
`t ∈ rrBasis5 ⊆ rrBasisCandidates 20`, `List.mem_mergeSort`/`mem_of_mem_
take`) unfolds to `t = (2i,i,0)` or `t = (2i+5,i,1)` for some `i`; either
way `t.1 ≤ 6` (`rrBasis5_order_le_six`) forces `i ≤ 3`. -/
theorem rrBasis5_bi_le_three : ∀ t ∈ rrBasis5, t.2.1 ≤ 3 := by
  intro t htmem
  have horder := rrBasis5_order_le_six t htmem
  have hsub : t ∈ rrBasisCandidates 20 := by
    have ht' : t ∈ (rrBasisCandidates 20).mergeSort (fun a b => decide (a.1 ≤ b.1)) :=
      List.mem_of_mem_take htmem
    exact (List.mem_mergeSort).mp ht'
  simp only [rrBasisCandidates, List.mem_flatMap, List.mem_range] at hsub
  obtain ⟨i, _, hti⟩ := hsub
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hti
  rcases hti with hti | hti <;> subst hti <;> simp only at horder ⊢ <;> omega

/-- **Corollary in `getD`-form**, matching how `matrixA`/`rhsVec`
(`DataDerivationSolve.lean`) actually access `rrBasis5` — via
`rrBasis5.getD bidx (0,0,0)` for `bidx < 5`, not direct list membership.
Restates `rrBasis5_bi_le_three` at that access pattern. -/
theorem rrBasis5_getD_bi_le_three (bidx : ℕ) (hbidx : bidx < 5) :
    (rrBasis5.getD bidx (0, 0, 0)).2.1 ≤ 3 := by
  have hlen : rrBasis5.length = 5 := by
    simp [rrBasis5, rrBasisCandidates, List.length_flatMap]
  have hblt : bidx < rrBasis5.length := hlen ▸ hbidx
  have htget : rrBasis5.getD bidx (0, 0, 0) = rrBasis5[bidx] := List.getD_eq_getElem _ _ hblt
  rw [htget]
  exact rrBasis5_bi_le_three rrBasis5[bidx] (List.getElem_mem hblt)

end TheDataDerivation
end Genus2Lean
