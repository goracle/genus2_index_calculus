import Mathlib
import Genus2Lean.ZeroD.MatrixEntryTotalDegree

/-!
# `rhsVec`'s `totalDegree` bound

New this pass. `MatrixEntryTotalDegree.lean`'s own header explicitly left
`rhsVec`'s entry theorem for "a following pass", flagging it as genuinely
separate work from `matrixA`'s own (different unfolding shape: `rhsVec`
uses a `dif`-on-`row.val < 2` split with a FIXED `(bi_n, bj_n) :=
rrBasis5.getD yIdx (0,1,1)` rather than `matrixA`'s `col`-dependent
`bi,bj`). Closes that gap.

**The key simplification `rhsVec` gets that `matrixA` didn't**:
`rrBasis5_yIdx_eq` (`DataDerivationSolve.lean`, already proved) pins
`rrBasis5.getD yIdx (0,1,1) = (5,0,1)` EXACTLY, so `bi_n = 0`, `bj_n = 1`
are concrete literals, not a `≤3`-bounded opaque quantity. `bi_n = 0`
means `px ^ bi_n = px ^ 0 = 1` — no `IsRdecWitness.mul`-by-induction
needed at all, unlike `matrixA_row0/row1`'s `bi`-induction. `bj_n = 1`
means the `if bj_n = 1 then py else 1` branch is always live, so
`rhsVec`'s row-0/1 entries reduce to exactly `-py` (`py := anchor1.2` or
`anchor2.2`), whose witness/bound is already `anchor1_snd_totalDegree_le`/
`anchor2_snd_totalDegree_le` (`AnchorTotalDegree.lean`) directly, just
negated. Row-2/3 entries are structurally identical to `matrixA`'s own
row-2/3 (`reduceMonomialModU`'s output, negated), so those two cases
reuse `algebraMap_Fp_towerToRdec_totalDegree_eq` exactly as `matrixA_row2/
row3_totalDegree_le` do.

**Negation**: no `IsRdecWitness.neg` existed before this file (`Tower
ToRdecMul.lean` only proves `.mul`) — added here as a two-line corollary,
since `evalNd`/`ι` are both ring homs (`map_neg`) and `(-n,d)` witnesses
`-v` whenever `(n,d)` witnesses `v`: `evalNd(-n) = -evalNd(n) = -(evalNd
d * ι v) = evalNd d * ι(-v)`. `totalDegree`-wise, `MvPolynomial.totalDegree_
neg` (already used in `DataDerivationTotalDegree.lean`) gives `(-n).totalDegree
= n.totalDegree` exactly, so no bound changes from negating.

**Not yet REPL-confirmed** — no build environment available this session;
per project convention, Claude drafts, Claire tests.

**Update, this pass**: rows 0/1's `hentry` proofs previously restated
`rhsVec`'s entire unfolded `dite`/`let`/`Matrix.cons` term via nested
`show` tactics — this is what triggered the kernel's deterministic
timeout (`RhsVecTotalDegree.lean:92:8`/`148:8`, i.e. the whole theorem
statement, not a specific tactic line: the kernel chokes re-checking the
`show`s' defeq claim against the huge unreduced term after elaboration
succeeds). `matrixA`'s own row0/row1 theorems
(`MatrixEntryTotalDegree.lean`) never hit this, because `matrixA`
doesn't build a `Fin 2 → K2 × K2` vector via `![anchor1, anchor2]` and
apply it — it inlines `anchor1`/`anchor2` directly per `if`-branch, so
there's no `Matrix.cons` reduction for the kernel to re-derive under a
`show`. `rhsVec`'s `let (px, py) := pxy ⟨row, h⟩` does route through
`Matrix.cons`, which is the extra weight. **Fixed by dropping `show`
entirely** in rows 0/1: `simp only [rhsVec, hyidx, dif_pos ...]`
zeta-reduces `rhsVec`'s nested `let`s and exposes `![anchor1,anchor2]
⟨row.val,h⟩` directly, which a separately-proved `have hvec0/hvec1 :
![anchor1,anchor2] ⟨i,_⟩ = anchor_i` lemma (proved by a plain `simp
[Matrix.cons_val_zero]`/`[Matrix.cons_val_one, Matrix.head_cons]`, small
enough that the kernel handles it fine on its own) then rewrites away
before the final `pow_zero, one_mul, if_true` cleanup — splitting the
vector-lookup fact out into its own small lemma, rather than asking one
`simp only` call to both zeta-reduce `rhsVec` AND resolve the
`Matrix.cons` lookup in the same pass, is what avoids the timeout
(the first attempt folded `Matrix.cons_val_zero` directly into the same
`simp only` list as `rhsVec`, which typechecked but left the `.2`-
projected vector lookup unresolved — `simp` needs the lookup stated at
exactly the projected type, not the pair type, to match). Rows 2/3
were never part of this timeout (no `Matrix.cons` in their `else`-branch
path) and are left as originally drafted.
-/

namespace Genus2Lean
namespace TheDataDerivation

open Polynomial

variable (p : ℕ) [hp : Fact (Nat.Prime p)] [hp2 : Fact (p ≠ 2)]
variable (c0 c1 c2 c3 c4 : F p)

/-- **Negation preserves `IsRdecWitness`, with the numerator flipped and
the denominator untouched.** `(n,d)` witnesses `v` iff `(-n,d)` witnesses
`-v` — both `evalNd`/`ι` are ring homs, so `-` commutes through the
witnessing equation directly. -/
theorem IsRdecWitness.neg {Vars K L : Type*} [CommRing K] [CommRing L]
    {ι : K →+* L} {evalNd : MvPolynomial Vars (F p) →+* L}
    {v : K} {n d : MvPolynomial Vars (F p)}
    (hv : IsRdecWitness p ι evalNd v (n, d)) :
    IsRdecWitness p ι evalNd (-v) (-n, d) := by
  unfold IsRdecWitness at *
  simp only [map_neg]
  rw [hv]
  ring

/-- **`rrBasis5_yIdx_eq`, restated at the default tuple `rhsVec` actually
uses.** `rrBasis5_yIdx_eq` states `rrBasis5.getD yIdx (0,0,0) = (5,0,1)` —
`List.getD`'s default argument only matters out of bounds, so it's
propositionally but not syntactically interchangeable with `rhsVec`'s own
`rrBasis5.getD yIdx (0,1,1)` call: the two aren't defeq, so `rhsVec`'s
`show`-based unfolding needs this restated version directly, not
`rrBasis5_yIdx_eq` itself (build error, first REPL pass: "Type mismatch ...
expected ... (0, 1, 1)"). Proved via `List.getD_eq_getElem` on both sides
(both in-bounds, `yIdx_lt_five`/`rrBasis5_length_eq_five`-style bound),
reducing both to the same `rrBasis5[yIdx]` and chaining through
`rrBasis5_yIdx_eq`'s own `getD_eq_getElem` step. -/
theorem rrBasis5_yIdx_eq' : rrBasis5.getD yIdx (0, 1, 1) = (5, 0, 1) := by
  have hlen : rrBasis5.length = 5 := by
    simp [rrBasis5, rrBasisCandidates, List.length_flatMap]
  have hlt : yIdx < rrBasis5.length := hlen ▸ yIdx_lt_five
  rw [List.getD_eq_getElem _ _ hlt]
  have h0 := rrBasis5_yIdx_eq
  rwa [List.getD_eq_getElem _ _ hlt] at h0

/-- **`rhsVec row`'s value, for `row.val = 0`, has an explicit
`IsRdecWitness` pair with a `totalDegree` bound.** `rhsVec`'s `row.val <
2` branch, at `row.val = 0`, is `-(px ^ bi_n * (if bj_n = 1 then py else
1))` for `(px,py) := anchor1 p c0 c1 c2 c3 c4`, `(bi_n,bj_n) :=
((rrBasis5.getD yIdx (0,1,1)).2.1, (rrBasis5.getD yIdx (0,1,1)).2.2)`.
`rrBasis5_yIdx_eq` pins `bi_n = 0, bj_n = 1` literally, collapsing the
entry to `-(1 * py) = -py` — no power/induction needed, unlike `matrixA`'s
`col`-dependent `bi`. Witness/bound come straight from `anchor1_snd_
totalDegree_le` (`AnchorTotalDegree.lean`), negated via `IsRdecWitness.neg`
above (`totalDegree` unaffected by negating the numerator). -/
theorem rhsVec_row0_totalDegree_le {Vars : Type*} [DecidableEq Vars]
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
        (MvPolynomial.X (sg.wGen 1))) :
    ∃ nd : MvPolynomial Vars (F p) × MvPolynomial Vars (F p),
      IsRdecWitness p ι
        (algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p))))
        (rhsVec p c0 c1 c2 c3 c4 u0 u1 v0 v1 ⟨0, by norm_num⟩)
        nd ∧ nd.1.totalDegree ≤ 3 ∧ nd.2.totalDegree ≤ 2 := by
  have hyidx : rrBasis5.getD yIdx (0, 1, 1) = (5, 0, 1) := rrBasis5_yIdx_eq'
  have hvec0 : (![anchor1 p c0 c1 c2 c3 c4, anchor2 p c0 c1 c2 c3 c4] (⟨0, by norm_num⟩ : Fin 2)) =
      anchor1 p c0 c1 c2 c3 c4 := by
    simp [Matrix.cons_val_zero]
  have hentry : rhsVec p c0 c1 c2 c3 c4 u0 u1 v0 v1 ⟨0, by norm_num⟩ =
      -(anchor1 p c0 c1 c2 c3 c4).2 := by
    simp only [rhsVec, hyidx, dif_pos (by norm_num : (0 : ℕ) < 2), hvec0, pow_zero, one_mul,
      if_true]
  rw [hentry]
  have hwy := anchor1_snd_totalDegree_le p c0 c1 c2 c3 c4 sg
  have hwity := towerToRdec_isRdecWitness p c0 c1 c2 c3 c4 sg
    (anchor1 p c0 c1 c2 c3 c4).2 ι hι_t hι_w1 hι_w2
  exact ⟨(-(towerToRdec p sg (anchor1 p c0 c1 c2 c3 c4).2).1,
      (towerToRdec p sg (anchor1 p c0 c1 c2 c3 c4).2).2),
    IsRdecWitness.neg p hwity,
    by rw [MvPolynomial.totalDegree_neg]; exact hwy.1, hwy.2⟩

/-- **The `row = 1` companion.** `rhsVec`'s `row.val < 2` branch at
`row.val = 1` swaps in `anchor2` for `anchor1`, otherwise identical to
`rhsVec_row0_totalDegree_le` above (same `bi_n = 0, bj_n = 1` collapse,
same `anchor2_snd_totalDegree_le` bound, same negation). -/
theorem rhsVec_row1_totalDegree_le {Vars : Type*} [DecidableEq Vars]
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
        (MvPolynomial.X (sg.wGen 1))) :
    ∃ nd : MvPolynomial Vars (F p) × MvPolynomial Vars (F p),
      IsRdecWitness p ι
        (algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p))))
        (rhsVec p c0 c1 c2 c3 c4 u0 u1 v0 v1 ⟨1, by norm_num⟩)
        nd ∧ nd.1.totalDegree ≤ 3 ∧ nd.2.totalDegree ≤ 2 := by
  have hyidx : rrBasis5.getD yIdx (0, 1, 1) = (5, 0, 1) := rrBasis5_yIdx_eq'
  have hvec1 : (![anchor1 p c0 c1 c2 c3 c4, anchor2 p c0 c1 c2 c3 c4] (⟨1, by norm_num⟩ : Fin 2)) =
      anchor2 p c0 c1 c2 c3 c4 := by
    simp [Matrix.cons_val_one, Matrix.head_cons]
  have hentry : rhsVec p c0 c1 c2 c3 c4 u0 u1 v0 v1 ⟨1, by norm_num⟩ =
      -(anchor2 p c0 c1 c2 c3 c4).2 := by
    simp only [rhsVec, hyidx, dif_pos (by norm_num : (1 : ℕ) < 2), hvec1, pow_zero, one_mul,
      if_true]
  rw [hentry]
  have hwy := anchor2_snd_totalDegree_le p c0 c1 c2 c3 c4 sg
  have hwity := towerToRdec_isRdecWitness p c0 c1 c2 c3 c4 sg
    (anchor2 p c0 c1 c2 c3 c4).2 ι hι_t hι_w1 hι_w2
  exact ⟨(-(towerToRdec p sg (anchor2 p c0 c1 c2 c3 c4).2).1,
      (towerToRdec p sg (anchor2 p c0 c1 c2 c3 c4).2).2),
    IsRdecWitness.neg p hwity,
    by rw [MvPolynomial.totalDegree_neg]; exact hwy.1, hwy.2⟩

/-- **`rhsVec row`'s value, for `row.val = 2`, has an explicit
`IsRdecWitness` pair with a `totalDegree` bound.** `rhsVec`'s `else`
branch (`¬ row.val < 2`), at `row.val = 2`, is `-algebraMap (F p) (K2 p
...) rn0` for `(rn0,rn1) := reduceMonomialModU p u0 u1 v0 v1 bi_n bj_n` —
structurally identical to `matrixA_row2_totalDegree_le`'s own entry
(same `reduceMonomialModU`/`algebraMap` shape), just negated and with
`(bi_n,bj_n)` fixed rather than `col`-dependent. Reuses
`algebraMap_Fp_towerToRdec_totalDegree_eq` (`MatrixEntryTotalDegree.lean`)
exactly as `matrixA_row2_totalDegree_le` does, then negates. -/
theorem rhsVec_row2_totalDegree_le {Vars : Type*} [DecidableEq Vars]
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
        (MvPolynomial.X (sg.wGen 1))) :
    ∃ nd : MvPolynomial Vars (F p) × MvPolynomial Vars (F p),
      IsRdecWitness p ι
        (algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p))))
        (rhsVec p c0 c1 c2 c3 c4 u0 u1 v0 v1 ⟨2, by norm_num⟩)
        nd ∧ nd.1.totalDegree ≤ 7 ∧ nd.2.totalDegree ≤ 6 := by
  have hyidx : rrBasis5.getD yIdx (0, 1, 1) = (5, 0, 1) := rrBasis5_yIdx_eq'
  have hentry : rhsVec p c0 c1 c2 c3 c4 u0 u1 v0 v1 ⟨2, by norm_num⟩ =
      -algebraMap (F p) (K2 p c0 c1 c2 c3 c4) (reduceMonomialModU p u0 u1 v0 v1 0 1).1 := by
    show (if h : (2 : ℕ) < 2 then
        let pxy : Fin 2 → K2 p c0 c1 c2 c3 c4 × K2 p c0 c1 c2 c3 c4 :=
          ![anchor1 p c0 c1 c2 c3 c4, anchor2 p c0 c1 c2 c3 c4]
        let (px, py) := pxy ⟨2, h⟩
        (-(px ^ (rrBasis5.getD yIdx (0, 1, 1)).2.1 *
            (if (rrBasis5.getD yIdx (0, 1, 1)).2.2 = 1 then py else 1)))
      else
        let (rn0, rn1) := reduceMonomialModU p u0 u1 v0 v1
          (rrBasis5.getD yIdx (0, 1, 1)).2.1 (rrBasis5.getD yIdx (0, 1, 1)).2.2
        (-algebraMap (F p) (K2 p c0 c1 c2 c3 c4) rn0)) =
      -algebraMap (F p) (K2 p c0 c1 c2 c3 c4) (reduceMonomialModU p u0 u1 v0 v1 0 1).1
    rw [dif_neg (by norm_num : ¬ (2 : ℕ) < 2), hyidx]
  rw [hentry]
  refine ⟨(-(towerToRdec p sg
      (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) (reduceMonomialModU p u0 u1 v0 v1 0 1).1)).1,
    (towerToRdec p sg
      (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) (reduceMonomialModU p u0 u1 v0 v1 0 1).1)).2),
    IsRdecWitness.neg p
      (towerToRdec_isRdecWitness p c0 c1 c2 c3 c4 sg _ ι hι_t hι_w1 hι_w2), ?_, ?_⟩
  · rw [MvPolynomial.totalDegree_neg]
    exact (algebraMap_Fp_towerToRdec_totalDegree_eq p c0 c1 c2 c3 c4 sg _).1
  · exact (algebraMap_Fp_towerToRdec_totalDegree_eq p c0 c1 c2 c3 c4 sg _).2

/-- **The `row = 3` companion.** `rhsVec`'s `else` branch at `row.val = 3`
takes `reduceMonomialModU`'s SECOND component (`rn1` in place of `rn0`) —
otherwise identical to `rhsVec_row2_totalDegree_le` above. -/
theorem rhsVec_row3_totalDegree_le {Vars : Type*} [DecidableEq Vars]
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
        (MvPolynomial.X (sg.wGen 1))) :
    ∃ nd : MvPolynomial Vars (F p) × MvPolynomial Vars (F p),
      IsRdecWitness p ι
        (algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p))))
        (rhsVec p c0 c1 c2 c3 c4 u0 u1 v0 v1 ⟨3, by norm_num⟩)
        nd ∧ nd.1.totalDegree ≤ 7 ∧ nd.2.totalDegree ≤ 6 := by
  have hyidx : rrBasis5.getD yIdx (0, 1, 1) = (5, 0, 1) := rrBasis5_yIdx_eq'
  have hentry : rhsVec p c0 c1 c2 c3 c4 u0 u1 v0 v1 ⟨3, by norm_num⟩ =
      -algebraMap (F p) (K2 p c0 c1 c2 c3 c4) (reduceMonomialModU p u0 u1 v0 v1 0 1).2 := by
    show (if h : (3 : ℕ) < 2 then
        let pxy : Fin 2 → K2 p c0 c1 c2 c3 c4 × K2 p c0 c1 c2 c3 c4 :=
          ![anchor1 p c0 c1 c2 c3 c4, anchor2 p c0 c1 c2 c3 c4]
        let (px, py) := pxy ⟨3, h⟩
        (-(px ^ (rrBasis5.getD yIdx (0, 1, 1)).2.1 *
            (if (rrBasis5.getD yIdx (0, 1, 1)).2.2 = 1 then py else 1)))
      else
        let (rn0, rn1) := reduceMonomialModU p u0 u1 v0 v1
          (rrBasis5.getD yIdx (0, 1, 1)).2.1 (rrBasis5.getD yIdx (0, 1, 1)).2.2
        (-algebraMap (F p) (K2 p c0 c1 c2 c3 c4) (if (3 : ℕ) = 2 then rn0 else rn1))) =
      -algebraMap (F p) (K2 p c0 c1 c2 c3 c4) (reduceMonomialModU p u0 u1 v0 v1 0 1).2
    rw [dif_neg (by norm_num : ¬ (3 : ℕ) < 2), hyidx]
    norm_num
  rw [hentry]
  refine ⟨(-(towerToRdec p sg
      (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) (reduceMonomialModU p u0 u1 v0 v1 0 1).2)).1,
    (towerToRdec p sg
      (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) (reduceMonomialModU p u0 u1 v0 v1 0 1).2)).2),
    IsRdecWitness.neg p
      (towerToRdec_isRdecWitness p c0 c1 c2 c3 c4 sg _ ι hι_t hι_w1 hι_w2), ?_, ?_⟩
  · rw [MvPolynomial.totalDegree_neg]
    exact (algebraMap_Fp_towerToRdec_totalDegree_eq p c0 c1 c2 c3 c4 sg _).1
  · exact (algebraMap_Fp_towerToRdec_totalDegree_eq p c0 c1 c2 c3 c4 sg _).2

/-! ## `rhsVec`'s full entry theorem: assembling rows 0–3

Same case-split assembly pattern as `matrixA_entry_totalDegree_le`
(`MatrixEntryTotalDegree.lean`), but `rhsVec`'s two possible bound pairs
(`≤3`/`≤2` for rows 0/1, `≤7`/`≤6` for rows 2/3) don't share a single
target bound the way `matrixA`'s four rows all land on `≤24`/`≤20` — so
this states the weaker common bound `≤7`/`≤6` throughout (rows 0/1's
`≤3`/`≤2` widen via `le_trans`), matching this project's preference for
one clean assembled statement over a case-dependent bound in the type.

**`rhsVec row`'s value, for ANY `row : Fin 4`, has an explicit
`IsRdecWitness` pair with a `totalDegree` bound `≤7`/`≤6`.** Dispatches on
`row.val` exactly as `matrixA_entry_totalDegree_le` does; rows 0/1's own
tighter `≤3`/`≤2` bound is widened via `le_trans`. -/
theorem rhsVec_entry_totalDegree_le {Vars : Type*} [DecidableEq Vars]
    (sg : SideGens Vars) (u0 u1 v0 v1 : F p) (row : Fin 4)
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
        (MvPolynomial.X (sg.wGen 1))) :
    ∃ nd : MvPolynomial Vars (F p) × MvPolynomial Vars (F p),
      IsRdecWitness p ι
        (algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p))))
        (rhsVec p c0 c1 c2 c3 c4 u0 u1 v0 v1 row)
        nd ∧ nd.1.totalDegree ≤ 7 ∧ nd.2.totalDegree ≤ 6 := by
  obtain ⟨rv, hrv⟩ := row
  interval_cases rv
  · obtain ⟨nd, hwit, h1, h2⟩ := rhsVec_row0_totalDegree_le p c0 c1 c2 c3 c4 sg u0 u1 v0 v1 ι
      hι_t hι_w1 hι_w2
    exact ⟨nd, hwit, h1.trans (by norm_num), h2.trans (by norm_num)⟩
  · obtain ⟨nd, hwit, h1, h2⟩ := rhsVec_row1_totalDegree_le p c0 c1 c2 c3 c4 sg u0 u1 v0 v1 ι
      hι_t hι_w1 hι_w2
    exact ⟨nd, hwit, h1.trans (by norm_num), h2.trans (by norm_num)⟩
  · exact rhsVec_row2_totalDegree_le p c0 c1 c2 c3 c4 sg u0 u1 v0 v1 ι hι_t hι_w1 hι_w2
  · exact rhsVec_row3_totalDegree_le p c0 c1 c2 c3 c4 sg u0 u1 v0 v1 ι hι_t hι_w1 hι_w2

/-! ## Status, this pass

**First REPL pass (Claire's actual build) surfaced four fixable errors,
addressed this pass, NOT yet re-sent to the REPL**:

1. **`rrBasis5_yIdx_eq` type mismatch, all four row theorems.**
   `rrBasis5_yIdx_eq` is stated at `List.getD`'s default `(0,0,0)`, not
   `rhsVec`'s own default `(0,1,1)` — the two aren't defeq (`getD`'s
   default only matters out of bounds), so `hyidx`'s original direct use
   of `rrBasis5_yIdx_eq` didn't typecheck against a goal stated at
   `(0,1,1)`. Fixed by adding `rrBasis5_yIdx_eq'` (this file, right after
   `IsRdecWitness.neg`), restated at `(0,1,1)` via `List.getD_eq_getElem`
   on both sides, and switching all four `hyidx` lines to it.
2. **Deterministic kernel timeout, rows 0/1's `hentry`.** The original
   single blunt `simp` after `rw [dif_pos ..., hyidx]` tried to unfold
   `![anchor1,anchor2] ⟨0,h⟩`'s `Matrix.cons` structure AND close the
   `if`/`pow_zero`/`one_mul` arithmetic in one call — too much for the
   kernel to check in the default budget. Fixed by splitting into an
   explicit second `show` (restating the goal with the vector application
   still opaque, deferring `rw [hyidx]` to AFTER that `show` rather than
   before it, so the first `show`'s defeq-check has less to chew through
   at once) followed by a narrow `simp only [Matrix.cons_val_zero]` (row 0)
   / `simp only [Matrix.cons_val_one, Matrix.head_cons]` (row 1) — the
   exact lemma pair this project's own `CAWitness.lean`/`CAWitnessCrossTangent*.lean`
   files already use for this identical `Matrix.cons`-lookup pattern —
   then a plain `rw [if_pos rfl, pow_zero, one_mul]` for the arithmetic,
   no `simp` left touching both concerns at once.
3. **Row 3's `show` pattern-match failure.** Fully downstream of fix 1 —
   once `hyidx`'s type mismatch is present, the elaborator's goal after
   `rw [dif_neg ..., hyidx]` was not what row 3's `show` expected, since
   `hyidx` itself didn't even typecheck. No separate fix needed beyond 1;
   left otherwise identical to `rhsVec_row2_totalDegree_le`'s already-
   working `show`/`rw [dif_neg ..., hyidx]`-only shape.
4. **Unknown constant `rhsVec_row1_totalDegree_le` in the assembly
   theorem.** Purely a consequence of row 1 failing to produce a kernel
   constant from errors 1/2 above — `rhsVec_entry_totalDegree_le`'s own
   `exact` call was always correct; nothing to change there once row 1
   itself compiles.

`[DecidableEq Vars]`-unused warnings (all five theorems) left as-is,
matching `matrixA`'s own row/entry theorems in `MatrixEntryTotalDegree.lean`,
which carry the same instance for consistency even where a given proof
doesn't literally mention it — not touched, since this is a lint warning,
not a build error, and this project's priority is errors first.

**Second REPL pass surfaced three more real issues, addressed this pass**:

5. **Rows 0/1's `rw [if_pos rfl, ...]` didn't match.** `rw [hyidx]` turns
   out to already normalize `if (5,0,1).2.2 = 1 then _ else _` down to
   `if True then _ else _` as part of the rewrite (the `Decidable (1=1)`
   instance computing through during the rewrite's own motive check, not
   left as a literal `_ = _` proposition the way this file's proof
   assumed) — so `rw [if_pos rfl]` had nothing matching `if ?a = ?a then
   _ else _` to find, and `Matrix.cons_val_zero`/`cons_val_one` similarly
   reported as "unused" by the linter (already resolved earlier in the
   same `rw`, not by the subsequent `simp`). Fixed by folding everything
   into one `simp only [Matrix.cons_val_zero, pow_zero, one_mul, if_true]`
   (row 0) / `simp only [Matrix.cons_val_one, Matrix.head_cons, pow_zero,
   one_mul, if_true]` (row 1) after `rw [hyidx]`, closing on `if_true`
   rather than `if_pos rfl` — matches what the goal actually looks like
   post-`rw`, rather than the pre-`rw` shape this file's draft assumed.
6. **Row 3's `show` genuinely failed independently of row 1 (not merely
   downstream of fix 1 as this file's status note previously guessed).**
   Root cause: this file's `show` for row 3's `else` branch was copy-
   pasted from row 2's, which hard-codes `rn0` directly rather than
   `rhsVec`'s actual `-algebraMap ... (if row.val = 2 then rn0 else rn1)`
   — for row 2 that happens to be defeq-transparent to `show` (`2 = 2`'s
   `Decidable` instance reduces trivially), but row 3 needs the `else`
   branch of that SAME inner `if`, which this file's `show` never wrote
   at all (it wrote `rn0` unconditionally, matching neither branch
   correctly by construction, not merely failing to reduce). Fixed by
   restoring the inner `if (3:ℕ) = 2 then rn0 else rn1` explicitly in
   row 3's `show`, then closing it with `rw [dif_neg ..., if_neg (by
   norm_num : ¬ (3:ℕ) = 2), hyidx]` rather than relying on `show`'s defeq
   check to silently pick the right branch.

**Third pass**: Claire's REPL surfaced a *deterministic kernel timeout*
on rows 0/1 (`rhsVec_row0_totalDegree_le`/`rhsVec_row1_totalDegree_le`),
plus the resulting `unknown constant rhsVec_row1_totalDegree_le` in
`rhsVec_entry_totalDegree_le`'s assembly (purely downstream, same as
issue 4 above — not a separate bug). Fixed by dropping `show` from
rows 0/1 in favor of `simp only [rhsVec, hyidx, dif_pos ...]`.

**Fourth pass**: that fix typechecked (no more timeout) but left an
unsolved goal in both rows 0/1 — `-(![anchor1,anchor2] ⟨0,_⟩).2 =
-(anchor1 ...).2` — because folding `Matrix.cons_val_zero`/`cons_val_one`
directly into the same `simp only [rhsVec, ...]` call left the `.2`-
projected lookup unmatched (also flagged by the linter as an unused simp
arg, confirming it never fired in that position). Fixed per the "Update,
this pass" note above: `hvec0`/`hvec1`, small standalone lemmas stating
the vector lookup directly at the projected pair, proved by their own
`simp` call and then fed into `hentry`'s `simp only` as ordinary
rewrite facts.

**Still NOT sent to Claire's REPL after this fourth round of fixes.**

**Next step once REPL-confirmed**: combine with `matrixA_entry_
totalDegree_le` (`MatrixEntryTotalDegree.lean`) through `cramerRatioDet_
num_totalDegree_le`/`cramerDenom_det_eq` (`DataDerivationTotalDegree.lean`)
to bound `cramerSolution`/`coeffsOut`'s own `totalDegree`, then `Epoly`/
`Ypoly` (linear combinations of `coeffsOut` against fixed-degree basis
monomials), then `Npoly = Epoly^2 - fAtX*Ypoly^2` — the piece `ROADMAP-
crossnondegenerate-degree-bound.md`'s "still fully unresolved" note
flags as needed before `curBeforeMonic`'s own bound (via `Npoly_eq_
curBeforeMonic_mul`'s exact-quotient identity) can be attempted.

**REPL-confirmed green** (whole project build) — supersedes the "not yet
REPL-confirmed" note earlier in this file.
-/

end TheDataDerivation
end Genus2Lean
