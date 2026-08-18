import Mathlib
import Genus2Lean.TheDataDerivation.DataDerivationTower

/-!
# `theData` derivation, part 3: the `4×4` linear solve and exact division

Third of four files — see `DataDerivationBasics.lean`'s header for the full
split rationale and file order. This file builds §4.2 items 4–5 (the `4×4`
Cramer's-rule solve, `E(x)`/`Y(x)`/`N(x) = E²-fY²`) and item 6 (exact
division of `N(x)` by `(X-t1)`, `(X-t2)`, and the target `u(x)`).

**This pass's work is entirely in item 6**, further into the two anchor
`sorry`s that the previous pass left after proving `dvd_N_anchor1`/
`dvd_N_anchor2` themselves:

- `anchor{1,2}_curve_relation` are **now fully proved, no `sorry`** — split
  into a genuinely-definitional half (`w{1,2}_sq_eq`, from
  `AdjoinRoot.eval₂_root` unfolded via `eval₂_sub`/`eval₂_pow`/`eval₂_X`/
  `eval₂_C` and `AdjoinRoot.algebraMap_eq`, fully proved) and an eval/
  algebraMap-compatibility half (`fAtX_eval_anchor{1,2}_eq`, still `sorry`,
  isolated as its own named lemma so the boundary between "closed" and
  "open" is precise). Concrete Mathlib lemma names for the closed half were
  looked up directly against the `mathlib4` source this pass (network
  access to `raw.githubusercontent.com` was available), not guessed.
- `anchor{1,2}_defining_eq` remain `sorry`, but with the proof restructured:
  a new shared lemma `matrixA_row_eval` isolates the row-unfolding case
  split, and the main proof now actually invokes `Matrix.mulVec_cramer`
  (confirmed to exist with this exact signature in `mathlib4`'s
  `LinearAlgebra/Matrix/Adjugate.lean`) rather than describing the argument
  in prose only — the docstring spells out all five steps precisely, with
  the remaining gap narrowed to exactly one reindexing step (`Fin 4`-sum via
  `otherIdx` vs. `Fin 5`-sum over all of `rrBasis5`) that is best closed by
  `decide`/computation against the concrete 5-element data once a
  toolchain is available, rather than guessed at here.

`dvd_N_u` (the target `u(x)`'s divisibility) is untouched this pass — still
fully open, no strategy found, same status as before.

Items 4–5 (`matrixA`, `rhsVec`, `MatrixNondegenerate`, `cramerSolution`,
`coeffsOut`, `Epoly`, `Ypoly`, `fAtX`, `Npoly`) are unchanged from before —
carried over verbatim.

**Compile status, unchanged**: no Lean toolchain was available this pass
either. The newly-closed lemmas (`w1_sq_eq`, `w2_sq_eq`,
`anchor1_curve_relation`, `anchor2_curve_relation`, `uRS_monic` in
`DataDerivationMumford.lean`) were checked by hand against Mathlib's actual
source (fetched this pass, not recalled from training data) for lemma names,
signatures, and argument order, which is a stronger check than previous
passes could do for their own `sorry`-closing attempts, but is still not a
kernel check — flagged explicitly rather than implied otherwise.
-/

namespace Genus2Lean
namespace TheDataDerivation

open Polynomial

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-! ## Item 4 (§4.2): the `4×4` matrix `A` and `rhs`

`nb = K+3 = 5`, `n_unknowns = K+2 = 4` for the `K=2,c=2` instance (this
file's top-level convention). `basis = rrBasis5`, `y_idx` the position of
`(0,1)` in it (the coefficient-of-`y` slot, singled out as the RHS per
§4.0 step 3), `other_idx` the remaining 4 positions filling the 4 matrix
columns. -/

/-- The two anchor points for the `K=2,c=2` instance: `(t1,w1)` and
`(t2,w2)`, both living in `K2` (`t1,t2` promoted up through the tower via
the two `algebraMap`s, matching Julia's "Promote all previous vars into the
new layer", lines 356–360). -/
noncomputable def anchor1 (c0 c1 c2 c3 c4 : F p) : K2 p c0 c1 c2 c3 c4 × K2 p c0 c1 c2 c3 c4 :=
  ( algebraMap (K1 p c0 c1 c2 c3 c4) (K2 p c0 c1 c2 c3 c4)
      (algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4) (t0 p 0)),
    algebraMap (K1 p c0 c1 c2 c3 c4) (K2 p c0 c1 c2 c3 c4) (w1 p c0 c1 c2 c3 c4) )

noncomputable def anchor2 (c0 c1 c2 c3 c4 : F p) : K2 p c0 c1 c2 c3 c4 × K2 p c0 c1 c2 c3 c4 :=
  ( algebraMap (K1 p c0 c1 c2 c3 c4) (K2 p c0 c1 c2 c3 c4)
      (algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4) (t0 p 1)),
    w2 p c0 c1 c2 c3 c4 )

/-- `y_idx`: the position of `(0,1)` in `rrBasis5`, i.e. the basis element
`x^0 * y = y` itself, singled out as the linear system's RHS (§4.0 step 3).
Computed rather than asserted, so a change to `rrBasis5`'s construction
above is automatically reflected here. -/
def yIdx : ℕ := (rrBasis5.findIdx (fun bij => bij.2.1 = 0 ∧ bij.2.2 = 1))

/-- `other_idx`: the four remaining basis positions (all of `Fin 5` except
`yIdx`), in increasing order — these become the 4 matrix columns / 4 solved
unknowns, matching Julia's `other_idx = [idx for idx in 1:nb if idx !=
y_idx]` (line 375). -/
def otherIdx : List ℕ := (List.range 5).filter (· ≠ yIdx)

/-- `yIdx < 5`, extracted as its own standalone fact (previously only proved
inline inside `otherIdx_length`) so the reindexing lemmas below (`otherMap`,
`sum_otherIdx_add_y`) can use it directly as a named hypothesis rather than
re-deriving it. Proved abstractly via `mergeSort`'s permutation/sortedness/
membership theorems (`List.mem_mergeSort`, `List.pairwise_mergeSort`,
`List.mergeSort_perm`, `List.findIdx_lt_length_of_exists`,
`List.findIdx_getElem`, `List.mem_iff_getElem`, `List.getElem?_take_of_lt`),
never by kernel-reducing `mergeSort` itself (which does not reduce via
`decide`/`rfl`/`native_decide` — its well-founded recursion is opaque to the
kernel, a known Lean4 issue). `decide` is used only on closed computations
that provably never touch `mergeSort`: `rrBasisCandidates 20`'s own `countP`
(plain `range`/`flatMap`), and (in `otherIdx_length` below) the final five
`(List.range 5).filter (· ≠ yIdx)` length checks (with `yIdx` rewritten to a
literal first via `change`, so `decide` never sees `rrBasis5`). -/
theorem yIdx_lt_five : yIdx < 5 := by
  let x : ℕ × ℕ × ℕ := (5, 0, 1)
  let q : (ℕ × ℕ × ℕ) → (ℕ × ℕ × ℕ) → Bool := fun a b => decide (a.1 ≤ b.1)
  let s : List (ℕ × ℕ × ℕ) := (rrBasisCandidates 20).mergeSort q

  /- Generic fact, independent of `mergeSort`: in a pairwise-`q`-sorted
     list, if `x` occurs and `q x x`, the first occurrence of `x` comes
     before the end of the "elements `q`-related to `x`" count. -/
  have findIdx_lt_countP_of_pairwise :
      ∀ {α : Type} [DecidableEq α] {q : α → α → Bool} {l : List α} {x : α},
        l.Pairwise (fun a b => q a b = true) → x ∈ l → q x x = true →
        l.findIdx (fun a => decide (a = x)) < l.countP (fun a => q a x) := by
    intro α _ q l
    induction l with
    | nil => intro x _ hx _; simp at hx
    | cons a l ih =>
      intro x hs hx hxx
      rw [List.pairwise_cons] at hs
      rcases List.mem_cons.mp hx with hxa | hxl
      · subst hxa; simp [List.findIdx_cons, hxx]
      · by_cases hax : a = x
        · subst hax; simp [List.findIdx_cons, hxx]
        · have hqax : q a x = true := hs.1 x hxl
          have ih' := ih hs.2 hxl hxx
          have hfind : (a :: l).findIdx (fun z => decide (z = x)) =
              l.findIdx (fun z => decide (z = x)) + 1 := by
            simp [List.findIdx_cons, hax]
          have hcount : (a :: l).countP (fun a => q a x) =
              l.countP (fun a => q a x) + 1 := by
            simp [hqax]
          rw [hfind, hcount]
          omega

  have hx_candidates : x ∈ rrBasisCandidates 20 := by
    norm_num [rrBasisCandidates, x]
  have hx_s : x ∈ s := by
    dsimp [s]; rw [List.mem_mergeSort]; exact hx_candidates
  have hs : s.Pairwise (fun a b => q a b = true) := by
    dsimp [s]
    apply List.pairwise_mergeSort
    · intro a b c hab hbc
      have hab' : a.1 ≤ b.1 := of_decide_eq_true hab
      have hbc' : b.1 ≤ c.1 := of_decide_eq_true hbc
      exact decide_eq_true (Nat.le_trans hab' hbc')
    · intro a b
      rcases Nat.le_total a.1 b.1 with h | h
      · have : q a b = true := decide_eq_true h
        simp [this]
      · have : q b a = true := decide_eq_true h
        simp [this]
  have hxx : q x x = true := by simp [q, x]
  have hcount_unsorted : (rrBasisCandidates 20).countP (fun a => q a x) = 4 := by
    dsimp [q, x, rrBasisCandidates]; decide
  have hperm : s.Perm (rrBasisCandidates 20) := by
    dsimp [s]; exact List.mergeSort_perm (rrBasisCandidates 20) q
  have hcount_sorted : s.countP (fun a => q a x) = 4 := by
    calc s.countP (fun a => q a x)
        = (rrBasisCandidates 20).countP (fun a => q a x) := hperm.countP_eq _
      _ = 4 := hcount_unsorted
  have hx_rank : s.findIdx (fun a => decide (a = x)) < 4 := by
    have h := findIdx_lt_countP_of_pairwise hs hx_s hxx
    rw [hcount_sorted] at h; exact h
  have hx_find_lt : s.findIdx (fun a => decide (a = x)) < s.length := by
    apply List.findIdx_lt_length_of_exists
    exact ⟨x, hx_s, by simp⟩
  have hx_at : s[s.findIdx (fun a => decide (a = x))] = x := by
    have hpred := List.findIdx_getElem (xs := s) (p := fun a => decide (a = x))
      (w := hx_find_lt)
    simpa using hpred
  have hx_take : x ∈ s.take 5 := by
    rw [List.mem_iff_getElem]
    refine ⟨s.findIdx (fun a => decide (a = x)), ?_, ?_⟩
    · rw [List.length_take]
      omega
    · have hopt : s[s.findIdx (fun a => decide (a = x))]? = some x :=
        (List.getElem_eq_iff hx_find_lt).mp hx_at
      have htake : (s.take 5)[s.findIdx (fun a => decide (a = x))]? =
          s[s.findIdx (fun a => decide (a = x))]? := by
        apply List.getElem?_take_of_lt; omega
      have hsome : (s.take 5)[s.findIdx (fun a => decide (a = x))]? = some x := by
        rw [htake]; exact hopt
      exact (List.getElem_eq_iff _).mpr hsome
  have hx_rrBasis5 : x ∈ rrBasis5 := by simpa [rrBasis5, s, q] using hx_take
  have hy_len : yIdx < rrBasis5.length := by
    apply List.findIdx_lt_length_of_exists
    refine ⟨x, hx_rrBasis5, ?_⟩
    simp [x]
  have hlen : rrBasis5.length = 5 := by
    simp [rrBasis5, rrBasisCandidates, List.length_flatMap]
  rw [hlen] at hy_len; exact hy_len

theorem otherIdx_length : otherIdx.length = 4 := by
  have hy := yIdx_lt_five
  have hy_cases : yIdx = 0 ∨ yIdx = 1 ∨ yIdx = 2 ∨ yIdx = 3 ∨ yIdx = 4 := by omega
  rcases hy_cases with h0 | h1 | h2 | h3 | h4
  · change ((List.range 5).filter (fun x => x ≠ yIdx)).length = 4
    rw [h0]; decide
  · change ((List.range 5).filter (fun x => x ≠ yIdx)).length = 4
    rw [h1]; decide
  · change ((List.range 5).filter (fun x => x ≠ yIdx)).length = 4
    rw [h2]; decide
  · change ((List.range 5).filter (fun x => x ≠ yIdx)).length = 4
    rw [h3]; decide
  · change ((List.range 5).filter (fun x => x ≠ yIdx)).length = 4
    rw [h4]; decide

/-- The `4×4` matrix `A` over `K2`, §4.0 step 3 / Julia lines 389–398 (rows
1–2 = anchor evaluation, rows 3–4 = mod-`u` reduction) folded together: row
`a ∈ {0,1}` (0-indexed here, `anchor1`/`anchor2`) evaluates each of the 4
`other_idx` basis monomials `x^bi * (y if bj=1 else 1)` at that anchor; rows
`{2,3}` use `reduceMonomialModU` instead (§4.0 step 3's "2 rows encoding
'reduce mod the target `u(x)`'"). Target data `(u0,u1,v0,v1)` is a further
parameter here (sample-specific — each of `elim2`'s two samples supplies
its own), unlike `(c0,...,c4)` which is shared across both samples/both
`a`- and `b`-side tower copies. -/
noncomputable def matrixA (c0 c1 c2 c3 c4 u0 u1 v0 v1 : F p) :
    Matrix (Fin 4) (Fin 4) (K2 p c0 c1 c2 c3 c4) :=
  fun row col =>
    let bidx := otherIdx.getD col.val 0
    let (bi, bj, _) := rrBasis5.getD bidx (0, 0, 0)
    -- Rows 0,1: anchor evaluation at `anchor1`/`anchor2` resp. (Julia rows
    -- `a=1,2`). Rows 2,3: mod-`u` reduction via `reduceMonomialModU`,
    -- taking its first/second component resp. (Julia rows `row0,row1`).
    if row.val = 0 then
      let (px, py) := anchor1 p c0 c1 c2 c3 c4
      px ^ bi * (if bj = 1 then py else 1)
    else if row.val = 1 then
      let (px, py) := anchor2 p c0 c1 c2 c3 c4
      px ^ bi * (if bj = 1 then py else 1)
    else
      let (r0, r1) := reduceMonomialModU p u0 u1 v0 v1 bi bj
      algebraMap (F p) (K2 p c0 c1 c2 c3 c4) (if row.val = 2 then r0 else r1)

/-- The RHS vector, same row split, using the `y_idx`-th basis element
(`(bi_n, bj_n) := basis[y_idx]`) evaluated the same two ways, negated
(Julia's `rhs[a,1] = -(...)`, `rhs[row0/1,1] = -rn0` / `-rn1` — the negation is
folded into `matrixA`'s sign convention here by keeping it explicit rather
than absorbing it, since `Matrix.cramer`/`.det` don't care about an overall
sign but a transcription slip on this specific minus sign would silently
flip every downstream coefficient). -/
noncomputable def rhsVec (c0 c1 c2 c3 c4 u0 u1 v0 v1 : F p) :
    Fin 4 → K2 p c0 c1 c2 c3 c4 :=
  fun row =>
    let (bi_n, bj_n, _) := rrBasis5.getD yIdx (0, 1, 1)
    if h : row.val < 2 then
      let pxy : Fin 2 → K2 p c0 c1 c2 c3 c4 × K2 p c0 c1 c2 c3 c4 :=
        ![anchor1 p c0 c1 c2 c3 c4, anchor2 p c0 c1 c2 c3 c4]
      let (px, py) := pxy ⟨row.val, h⟩
      let choose : K2 p c0 c1 c2 c3 c4 := (if bj_n = 1 then py else 1)
      (-(px ^ bi_n * choose))
    else
      let (rn0, rn1) := reduceMonomialModU p u0 u1 v0 v1 bi_n bj_n
      (-algebraMap (F p) (K2 p c0 c1 c2 c3 c4) (if row.val = 2 then rn0 else rn1))

/-- **The first genericity condition** (§4.1, last bullet): `theData` is
only well-defined where `A.det ≠ 0` — stated here as an explicit named
hypothesis, per the roadmap's instruction ("should be visible as a named
hypothesis from here on rather than folded away"), threaded into item 5
below. Not proved or assumed globally; a specific `(p,c0,...,c4,u0,u1,v0,v1)`
instance either satisfies it or it doesn't, and downstream statements take
it as a hypothesis. -/
def MatrixNondegenerate (c0 c1 c2 c3 c4 u0 u1 v0 v1 : F p) : Prop :=
  (matrixA p c0 c1 c2 c3 c4 u0 u1 v0 v1).det ≠ 0

/-! ## Item 5 (§4.2): `E(x), Y(x)` from `Matrix.cramer`, and `N(x) = E²-fY²`

Solved coefficients via `Matrix.cramer`, §4.0 steps 4–5. -/

/-- The 4 solved coefficients, `Matrix.cramer A rhs i / A.det` — Julia's
`solve(A, rhs; side=:right)` via Cramer's rule (§4.1: "the solution's
entries are `det(A_i)/det(A)`"), well-defined as a genuine solution only
under `MatrixNondegenerate` (division by a possibly-zero `A.det`
otherwise — the expression below still typechecks unconditionally since
field division by zero is `0` in Lean/Mathlib, but is only the CORRECT
solution to `A * c = rhs` when `A.det ≠ 0`). -/
noncomputable def cramerSolution (c0 c1 c2 c3 c4 u0 u1 v0 v1 : F p) :
    Fin 4 → K2 p c0 c1 c2 c3 c4 :=
  fun i =>
    (matrixA p c0 c1 c2 c3 c4 u0 u1 v0 v1).cramer (rhsVec p c0 c1 c2 c3 c4 u0 u1 v0 v1) i /
      (matrixA p c0 c1 c2 c3 c4 u0 u1 v0 v1).det

/-- `coeffs_out`: the full 5-slot coefficient vector, `cramerSolution` at
the 4 `other_idx` slots plus `1` at `y_idx` (Julia lines 425–429,
`coeffs_out[y_idx] = K_final(1)`).

**Avoids guessing at `List.findIdx?`/`List.indexOf?`/`List.idxOf` bound-
lemma names entirely.** A previous version called `List.indexOf?`, which
this project's toolchain does not have, and a subsequent attempt leaned on
an unverified `List.idxOf_lt_length` name. This version instead uses only
`List.mem_iff_getElem : a ∈ l ↔ ∃ (n) (h : n < l.length), l[n] = a`
(confirmed present in Lean's core `Init.Data.List.Lemmas`), which hands
back an in-bounds index directly as part of the existential — no separate
bound lemma needed at all. `bidx.val ∈ otherIdx` is established directly
from `bidx.val < 5` and `bidx.val ≠ yIdx` via `otherIdx`'s own definition
(`List.mem_filter`/`List.mem_range`, both basic and safe), then
`Classical.choose` on the resulting existential extracts the witness
index together with its bound in one step. -/
noncomputable def coeffsOut (c0 c1 c2 c3 c4 u0 u1 v0 v1 : F p) : Fin 5 → K2 p c0 c1 c2 c3 c4 :=
  fun bidx =>
    if hy : bidx.val = yIdx then 1
    else
      have hmem : bidx.val ∈ otherIdx := by
        simp only [otherIdx, List.mem_filter, List.mem_range, decide_eq_true_eq]
        exact ⟨bidx.isLt, hy⟩
      have hex : ∃ (n : ℕ) (_ : n < otherIdx.length), otherIdx[n] = bidx.val :=
        List.mem_iff_getElem.mp hmem
      have hlen : otherIdx.length = 4 := otherIdx_length
      have hlt : hex.choose < 4 := hlen ▸ hex.choose_spec.choose
      cramerSolution p c0 c1 c2 c3 c4 u0 u1 v0 v1 ⟨hex.choose, hlt⟩

/-- `E(x) = Σ_{bj=0} c_i x^i`, `Y(x) = Σ_{bj=1} c_i x^i` — §4.0 step 4,
Julia lines 432–442, folding the 5-slot `coeffsOut` into two polynomials
over `K2` by each basis pair's `j`-component. -/
noncomputable def Epoly (c0 c1 c2 c3 c4 u0 u1 v0 v1 : F p) : Polynomial (K2 p c0 c1 c2 c3 c4) :=
  ∑ bidx : Fin 5,
    let (bi, bj, _) := rrBasis5.getD bidx.val (0, 0, 0)
    if bj = 0 then C (coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 bidx) * X ^ bi else 0

noncomputable def Ypoly (c0 c1 c2 c3 c4 u0 u1 v0 v1 : F p) : Polynomial (K2 p c0 c1 c2 c3 c4) :=
  ∑ bidx : Fin 5,
    let (bi, bj, _) := rrBasis5.getD bidx.val (0, 0, 0)
    if bj = 1 then C (coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 bidx) * X ^ bi else 0

/-- `f` re-evaluated at the polynomial variable `x` (not at an anchor `t_i`
this time), mapped into `Polynomial (K2 p ...)` — §4.0 step 5's "`F_POLY_ASC`
... re-enters, now evaluated at the polynomial variable `x`". -/
noncomputable def fAtX (c0 c1 c2 c3 c4 : F p) (_u0 _u1 _v0 _v1 : F p) :
    Polynomial (K2 p c0 c1 c2 c3 c4) :=
  (curvePoly p c0 c1 c2 c3 c4).map (algebraMap (F p) (K2 p c0 c1 c2 c3 c4))

/-- `N(x) = E(x)^2 - f(x)*Y(x)^2` — §4.0 step 5, Julia line 449. This is
the last of item 5's targets; item 6 (the four `divexact` steps dividing
`N` by `(X-t1)`, `(X-t2)`, and `u(x) = X²+u1 X+u0`) picks up from here. -/
noncomputable def Npoly (c0 c1 c2 c3 c4 u0 u1 v0 v1 : F p) : Polynomial (K2 p c0 c1 c2 c3 c4) :=
  Epoly p c0 c1 c2 c3 c4 u0 u1 v0 v1 ^ 2 -
    fAtX p c0 c1 c2 c3 c4 u0 u1 v0 v1 * Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1 ^ 2

/-! ## Item 6 (§4.2): exact division — the hard step

Flagged by the roadmap as likely the single hardest new step in the whole
port. The roadmap's own proposed angle: `t_i` and the roots of `u(x)` are
CONSTRUCTED to be roots of `N(x)` by the linear system's own defining
equations (anchor rows force `E(t_i)^2 = f(t_i) Y(t_i)^2` directly), so
`Polynomial.dvd_iff_isRoot` (`X - C a ∣ p ↔ p.IsRoot a`) applied per-factor
should reduce "does `(X-t_i)` divide `N`" to "evaluate the defining linear
system at each anchor", closer to definitional unfolding than to a new
computation.

**This pass**: the two anchor facts (`dvd_N_anchor1`, `dvd_N_anchor2`) are
now proved, following exactly the roadmap's proposed angle. `dvd_N_u`
(divisibility by the target `u(x)`) remains `sorry` — the roadmap itself
flagged this one as having no sketched strategy, and that's still true; see
its own docstring below for why the anchor argument doesn't transfer.

### The anchor argument, worked out precisely

Row 0 of the defining linear system `A · coeffsOut = rhsVec` (via
`Matrix.mulVec_cramer`, dividing by `A.det ≠ 0` under `MatrixNondegenerate`)
unfolds, term by term, to exactly

    E(t1) + w1 * Y(t1) = 0        i.e.  E(t1) = -(w1 * Y(t1))

This is because: `A`'s row 0 evaluates every `other_idx` basis monomial at
anchor `(t1, w1)`, `rhsVec`'s row 0 evaluates the `y_idx = (0,1)` monomial
(namely `y` itself, i.e. `w1`) at the SAME anchor and negates it, and
`coeffsOut` packages `cramerSolution` together with the fixed `1` at
`y_idx`. So "row 0 of `A·coeffsOut = rhsVec`" and "the full weighted sum
`Σ coeffsOut(bidx) * t1^bi * (w1 if bj=1 else 1) = 0` over ALL FIVE slots
(not just the 4 `other_idx` ones)" are the same equation — moving `rhsVec`'s
term to the left flips its sign back, reintroducing exactly the `y_idx`
term `coeffsOut(yIdx) * t1^0 * w1 = 1 * w1 = w1` that `rhsVec` computes and
negates. That five-term sum splits, by each slot's `bj`, into
`Epoly(t1) + w1 * Ypoly(t1)` (this is literally `Epoly`/`Ypoly`'s own
definition: sum over `bj=0` slots gives `Epoly`, sum over `bj=1` slots gives
`Y`'s coefficients each multiplied by the extra `w1` factor `bj=1` rows
carry, i.e. `w1 * Ypoly(t1)`).

Given `E(t1) = -(w1 * Y(t1))`, squaring both sides: `E(t1)^2 = w1^2 *
Y(t1)^2`. The curve relation `w1^2 = f(t1)` (definitionally, from
`K1`'s construction as `AdjoinRoot (X^2 - C (fAtT ... 0))` — `w1` IS a root
of that polynomial by `AdjoinRoot.root`'s defining property) then gives
`E(t1)^2 = f(t1) * Y(t1)^2`, i.e. `N(t1) = 0`, i.e. `(X - C t1) ∣ N` via
`Polynomial.dvd_iff_isRoot`. `dvd_N_anchor2` is the identical argument one
level up (`w2^2 = f(t2)` this time definitional in `K2` itself rather than
promoted from `K1`, since `w2`'s defining quadratic lives directly over
`K1`, not `K0`). -/

section ExactDivision

variable (c0 c1 c2 c3 c4 u0 u1 v0 v1 : F p)

/-- **Row-unfolding lemma, shared by both anchors.** `matrixA`'s row `a ∈
{0,1}` and `rhsVec`'s row `a`, evaluated at ANY `col : Fin 4`, are literally
`px ^ bi * (if bj = 1 then py else 1)` for `(px,py)` the row's anchor and
`(bi,bj)` the basis pair at `otherIdx.getD col.val 0` (resp. at `yIdx` for
`rhsVec`, negated) — this is `matrixA`/`rhsVec`'s definition unfolded
literally, isolated here as its own lemma so `anchor1_defining_eq`/
`anchor2_defining_eq` below don't have to re-do the `if row.val = 0 then ...
else if row.val = 1 then ...` case split twice. Row `a = 0` is `anchor1`,
row `a = 1` is `anchor2` (`Fin 4 → ...` indexing matches `matrixA`'s own
`![...]`-free `if`-chain, so this is by `rfl`/`simp [matrixA]` once `row.val`
is fixed to a literal `0` or `1`). -/
private theorem matrixA_row_eval (a : Fin 2) (col : Fin 4) :
    matrixA p c0 c1 c2 c3 c4 u0 u1 v0 v1 ⟨a.val, by omega⟩ col =
      let (px, py) := (![anchor1 p c0 c1 c2 c3 c4, anchor2 p c0 c1 c2 c3 c4] : Fin 2 →
        K2 p c0 c1 c2 c3 c4 × K2 p c0 c1 c2 c3 c4) a
      let (bi, bj, _) := rrBasis5.getD (otherIdx.getD col.val 0) (0, 0, 0)
      px ^ bi * (if bj = 1 then py else 1) := by
  fin_cases a <;> simp [matrixA]

/-- Membership characterization for `otherIdx`, stated in `Prop` form (bridging
the `Bool`-valued `decide` that `List.filter`/`List.mem_filter` actually
produce). -/
private theorem mem_otherIdx_iff (n : ℕ) : n ∈ otherIdx ↔ n < 5 ∧ n ≠ yIdx := by
  unfold otherIdx
  rw [List.mem_filter, List.mem_range, decide_eq_true_eq]

/-- **The reindexing bijection**, `col : Fin 4 ↦ otherIdx[col] : Fin 5`.
Maps each of `otherIdx`'s 4 list positions into `Fin 5` (well-defined since
every element of `otherIdx` is `< 5`, by `otherIdx`'s own `filter (· < 5)`-via-
`range 5` construction). Does NOT assume `otherIdx`'s list-order matches
`Fin 4`'s numeral order — the injectivity/surjectivity lemmas below only use
`otherIdx.Nodup` and set membership, not any ordering fact. -/
def otherMap (col : Fin 4) : Fin 5 :=
  ⟨otherIdx.getD col.val 0, by
    have hcol : col.val < otherIdx.length := by rw [otherIdx_length]; exact col.isLt
    have hmem : otherIdx[col.val] ∈ otherIdx := List.getElem_mem hcol
    have hlt5 : otherIdx[col.val] < 5 := ((mem_otherIdx_iff _).mp hmem).1
    rw [List.getD_eq_getElem _ _ hcol]
    exact hlt5⟩

private theorem otherIdx_nodup : otherIdx.Nodup := by
  unfold otherIdx
  exact List.nodup_range.filter _

/-- `otherMap` is injective — from `otherIdx.Nodup`, no ordering assumption
needed. -/
theorem otherMap_injective : Function.Injective otherMap := by
  intro i j hij
  have hi : i.val < otherIdx.length := by rw [otherIdx_length]; exact i.isLt
  have hj : j.val < otherIdx.length := by rw [otherIdx_length]; exact j.isLt
  have hget : otherIdx[i.val] = otherIdx[j.val] := by
    have := congrArg Fin.val hij
    simp only [otherMap, List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at this
    exact this
  exact Fin.ext ((otherIdx_nodup.getElem_inj_iff (hi := hi) (hj := hj)).mp hget)

/-- Every `b : Fin 5` other than `yIdx` is hit by `otherMap`. -/
theorem otherMap_surjOn (b : Fin 5) (hby : b ≠ ⟨yIdx, yIdx_lt_five⟩) :
    ∃ col : Fin 4, otherMap col = b := by
  have hbval_ne : b.val ≠ yIdx := fun h => hby (Fin.ext h)
  have hbmem : b.val ∈ otherIdx := (mem_otherIdx_iff _).mpr ⟨b.isLt, hbval_ne⟩
  obtain ⟨n, hn, hne⟩ := List.mem_iff_getElem.mp hbmem
  have hn4 : n < 4 := by rw [← otherIdx_length]; exact hn
  refine ⟨⟨n, hn4⟩, Fin.ext ?_⟩
  show otherIdx.getD n 0 = b.val
  rw [List.getD_eq_getElem _ _ hn]
  exact hne

/-- **Step 4, the reindexing identity**: mapping `F : Fin 5 → K2 p ...` over
`otherIdx`'s 4 positions (via `otherMap`) plus the `yIdx` term separately is
the same as summing `F` over all of `Fin 5`. This is the one genuinely
combinatorial step in the `anchor{1,2}_defining_eq` argument (§ above,
"the five-slot defining identity", step 4). -/
theorem sum_otherIdx_add_y (F : Fin 5 → K2 p c0 c1 c2 c3 c4) :
    (∑ col : Fin 4, F (otherMap col)) + F ⟨yIdx, yIdx_lt_five⟩ =
      ∑ bidx : Fin 5, F bidx := by
  have hsum : (∑ col : Fin 4, F (otherMap col)) =
      ∑ b ∈ (Finset.univ.erase (⟨yIdx, yIdx_lt_five⟩ : Fin 5)), F b := by
    apply Finset.sum_bij (fun (col : Fin 4) (_ : col ∈ (Finset.univ : Finset (Fin 4))) =>
      otherMap col)
    · -- membership: otherMap col ∈ univ.erase yIdx
      intro col _
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      have hcol : col.val < otherIdx.length := by rw [otherIdx_length]; exact col.isLt
      have hmem : otherIdx[col.val] ∈ otherIdx := List.getElem_mem hcol
      have hmem' : otherIdx[col.val] ≠ yIdx := ((mem_otherIdx_iff _).mp hmem).2
      show (⟨otherIdx.getD col.val 0, _⟩ : Fin 5) ≠ ⟨yIdx, yIdx_lt_five⟩
      intro hcontra
      apply hmem'
      have heq : otherIdx.getD col.val 0 = yIdx := congrArg Fin.val hcontra
      rw [List.getD_eq_getElem _ _ hcol] at heq
      exact heq
    · -- injectivity: goal is `∀ a₁ ∈ univ, ∀ a₂ ∈ univ, otherMap a₁ = otherMap a₂ → a₁ = a₂`
      intro col1 _ col2 _ heq
      exact otherMap_injective heq
    · -- surjectivity: goal is `∀ b ∈ univ.erase yIdx, ∃ a, ∃ (_ : a ∈ univ), otherMap a = b`
      intro col1 hb
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hb
      obtain ⟨col, hcol⟩ := otherMap_surjOn col1 hb
      exact ⟨col, Finset.mem_univ _, hcol⟩
    · -- value agreement (`F` applied via `otherMap`, both sides literally the same term)
      intro col _
      rfl
  have hy_mem : (⟨yIdx, yIdx_lt_five⟩ : Fin 5) ∈ (Finset.univ : Finset (Fin 5)) :=
    Finset.mem_univ _
  have hsplit : (∑ bidx : Fin 5, F bidx) =
      F ⟨yIdx, yIdx_lt_five⟩ +
        ∑ b ∈ (Finset.univ.erase (⟨yIdx, yIdx_lt_five⟩ : Fin 5)), F b := by
    have hnotmem : (⟨yIdx, yIdx_lt_five⟩ : Fin 5) ∉
        Finset.univ.erase (⟨yIdx, yIdx_lt_five⟩ : Fin 5) := by
      simp [Finset.mem_erase]
    rw [← Finset.sum_insert hnotmem, Finset.insert_erase hy_mem]
  rw [hsum, hsplit]
  ring

/-- **Bridging `coeffsOut` and `cramerSolution` across `otherMap`.**
`coeffsOut`'s definition, at any `bidx ≠ yIdx`, uses `Classical.choose` to
extract SOME index `n < otherIdx.length` with `otherIdx[n] = bidx.val`, then
evaluates `cramerSolution` there. `otherMap col` is BY CONSTRUCTION such a
`bidx` for `n = col.val` (`otherMap col := ⟨otherIdx.getD col.val 0, _⟩`,
i.e. `otherIdx[col.val] = (otherMap col).val`). Since `otherIdx` has no
duplicates (`otherIdx_nodup`), any two witnessing indices for the same
`bidx.val` must agree, so the `Classical.choose`-selected index equals
`col.val` regardless of which witness `Classical.choose` happens to pick —
this is exactly what makes `coeffsOut (otherMap col) = cramerSolution col`
provable without pinning down `Classical.choose`'s actual output. -/
private theorem coeffsOut_otherMap (col : Fin 4) :
    coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 (otherMap col) =
      cramerSolution p c0 c1 c2 c3 c4 u0 u1 v0 v1 col := by
  have hcol : col.val < otherIdx.length := by rw [otherIdx_length]; exact col.isLt
  have hgetD : otherIdx.getD col.val 0 = otherIdx[col.val] := List.getD_eq_getElem _ _ hcol
  have hne : (otherMap col).val ≠ yIdx := by
    have hmem : otherIdx[col.val] ∈ otherIdx := List.getElem_mem hcol
    have : otherIdx[col.val] ≠ yIdx := ((mem_otherIdx_iff _).mp hmem).2
    show otherIdx.getD col.val 0 ≠ yIdx
    rw [hgetD]; exact this
  unfold coeffsOut
  rw [dif_neg hne]
  -- Now the goal is `cramerSolution ⟨hex.choose, hlt⟩ = cramerSolution col`,
  -- where `hex : ∃ n (_ : n < otherIdx.length), otherIdx[n] = (otherMap col).val`
  -- comes from `List.mem_iff_getElem.mp` applied to membership derived above.
  -- Reduce to showing the underlying indices agree via `otherIdx`'s nodup-ness.
  -- (Avoid `congr 1` here: `cramerSolution` unfolds through `Matrix.cramer`/
  -- division and triggers max-recursion-depth inside `congr`'s unifier. Instead
  -- prove the `Fin 4` arguments equal first via `Fin.ext`/`suffices`, so the
  -- rewrite only ever touches the index argument, never `cramerSolution`'s body.)
  set hex : ∃ (n : ℕ) (_ : n < otherIdx.length), otherIdx[n] = (otherMap col).val :=
    List.mem_iff_getElem.mp (by
      simp only [otherIdx, List.mem_filter, List.mem_range, decide_eq_true_eq]
      exact ⟨(otherMap col).isLt, hne⟩) with hex_def
  have hspec : otherIdx[hex.choose]'(hex.choose_spec.choose) = (otherMap col).val :=
    hex.choose_spec.choose_spec
  have hgoal_val : otherIdx[hex.choose]'(hex.choose_spec.choose) = otherIdx[col.val] := by
    rw [hspec]; show (otherMap col).val = otherIdx[col.val]; rw [← hgetD]; rfl
  have hidx_eq : hex.choose = col.val :=
    otherIdx_nodup.getElem_inj_iff.mp hgoal_val
  suffices h : (⟨hex.choose, hex.choose_spec.choose⟩ : Fin 4) = col by rw [h]
  exact Fin.ext hidx_eq

/-- **The five-slot defining identity**, row 0 of `A * coeffsOut = rhsVec`
restated additively over all of `Fin 5` (not just `other_idx`) — see the
docstring above §"The anchor argument, worked out precisely" for the
derivation.

**Proof strategy, spelled out precisely** (this is the "definitional
unfolding" step the roadmap's own angle predicts, not new algebra, but the
`Fin 4`-sum-vs-`Fin 5`-sum bookkeeping connecting `Matrix.mulVec_cramer`'s
`col : Fin 4` index to `Epoly`/`Ypoly`'s `bidx : Fin 5` sum is genuine
combinatorial work, not `rfl`):

1. `Matrix.mulVec_cramer (matrixA ...) (rhsVec ...)` gives, at row `⟨0,_⟩`:
   `∑ col, matrixA 0 col * cramer (matrixA ...) (rhsVec ...) col = A.det •
   rhsVec 0` (unfolding `Matrix.mulVec` and `•` as scalar mult in a field).
2. Divide both sides by `A.det` (licensed by `hA : A.det ≠ 0`) and rewrite
   `cramer A rhs col / A.det` as `cramerSolution col` (their definitional
   equality) to get `∑ col, matrixA 0 col * cramerSolution col = rhsVec 0`.
3. `matrixA_row_eval` above rewrites each `matrixA 0 col` term; `rhsVec`'s
   own definition (mirroring `matrixA`'s row-0 case) rewrites the RHS to
   `-(px₁ ^ bi_n * (if bj_n = 1 then py₁ else 1))` for `(bi_n,bj_n) :=
   rrBasis5.getD yIdx _` — moving it to the left flips the sign, producing a
   4-term sum PLUS this fifth term, i.e. exactly
   `∑ col : Fin 4, coeffsOut (otherIdx.getD col 0) * (matrixA-row-0 factor)
     + coeffsOut yIdx * (matrixA-row-0 factor at yIdx) = 0`
   using `coeffsOut`'s own definition (`coeffsOut bidx = cramerSolution col`
   when `bidx = otherIdx.getD col 0`, `= 1` at `yIdx`).
4. The reindexing `∑ col : Fin 4, g (otherIdx.getD col 0) + g yIdx = ∑ bidx :
   Fin 5, g bidx` (for the specific `g` arising here) holds because
   `otherIdx` is `(List.range 5).filter (· ≠ yIdx)`, a length-4 list
   enumerating `Fin 5 \ {yIdx}` — a `Finset.sum_filter`/`List.sum_eq_of_ne`-
   style bijection argument, or a direct `decide`/`Finset.sum_range_succ`
   unfolding since `yIdx` itself is a fully computed literal (`rrBasis5` is a
   closed `List` computation, so `yIdx`'s VALUE is decidable/computable, not
   symbolic) — this step is where a literal `#eval` or `decide` against the
   concrete 5-element `rrBasis5`/`yIdx`/`otherIdx` data is the cleanest route
   once a toolchain is available, rather than a general reindexing lemma.
5. Splitting the resulting `∑ bidx : Fin 5, coeffsOut bidx * (px^bi *
   (if bj=1 then py else 1))` by `bj` recovers `Epoly.eval px + py *
   Ypoly.eval px` exactly (`Epoly`/`Ypoly`'s own `∑ bidx, if bj = 0/1 then
   ... else 0` definitions, plus `Polynomial.eval_finset_sum`/`eval_C_mul_X_pow`
   to turn the polynomial-eval statement back into the same sum shape).

Steps 1–3 and 5 are routine algebraic rewriting; step 4 is the one piece
that is easiest to close by computation (`decide`/`rfl` on the concrete
5-element data) rather than a general lemma, and is exactly the kind of
step that benefits from an actual toolchain to get the `Finset`/`List`
API calls exactly right — **left as `sorry`** rather than risk a wrong
lemma name or off-by-one with no compiler to catch it, but the argument
above is a complete, checkable-in-principle proof sketch, one level more
precise than the previous draft's prose summary. -/
private theorem anchor_defining_eq_aux (hA : MatrixNondegenerate p c0 c1 c2 c3 c4 u0 u1 v0 v1)
    (a : Fin 2) :
    (Epoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).eval
        ((![anchor1 p c0 c1 c2 c3 c4, anchor2 p c0 c1 c2 c3 c4] :
          Fin 2 → K2 p c0 c1 c2 c3 c4 × K2 p c0 c1 c2 c3 c4) a).1 +
      ((![anchor1 p c0 c1 c2 c3 c4, anchor2 p c0 c1 c2 c3 c4] :
          Fin 2 → K2 p c0 c1 c2 c3 c4 × K2 p c0 c1 c2 c3 c4) a).2 *
        (Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).eval
          ((![anchor1 p c0 c1 c2 c3 c4, anchor2 p c0 c1 c2 c3 c4] :
            Fin 2 → K2 p c0 c1 c2 c3 c4 × K2 p c0 c1 c2 c3 c4) a).1 = 0 := by
  set A := matrixA p c0 c1 c2 c3 c4 u0 u1 v0 v1 with hA_def
  set rhs := rhsVec p c0 c1 c2 c3 c4 u0 u1 v0 v1 with hrhs_def
  have hdet : A.det ≠ 0 := hA
  -- Step 1: Cramer's rule, unfolded pointwise at row `⟨a.val, _⟩`.
  have hmul := Matrix.mulVec_cramer A rhs
  have hrow := congrFun hmul (⟨a.val, by omega⟩ : Fin 4)
  simp only [Matrix.mulVec, Matrix.dotProduct, Pi.smul_apply, smul_eq_mul] at hrow
  -- `hrow : ∑ col, A ⟨a.val,_⟩ col * A.cramer rhs col = A.det * rhs ⟨a.val,_⟩`.
  -- Step 2: divide by `A.det ≠ 0`, turning `cramer .../ det` into `cramerSolution`.
  have hrow' : ∑ col : Fin 4, A ⟨a.val, by omega⟩ col *
      (A.cramer rhs col / A.det) = rhs ⟨a.val, by omega⟩ := by
    have := congrArg (· / A.det) hrow
    dsimp only at this
    rw [mul_comm A.det (rhs ⟨a.val, by omega⟩), mul_div_assoc,
      mul_div_cancel_right₀ _ hdet] at this
    rw [← this, Finset.sum_div]
    congr 1
    ext col
    rw [mul_div_assoc]
  have hcramerSolution : ∀ col : Fin 4, A.cramer rhs col / A.det =
      cramerSolution p c0 c1 c2 c3 c4 u0 u1 v0 v1 col := fun col => rfl
  simp only [hcramerSolution] at hrow'
  -- Step 3: unfold `A ⟨a.val,_⟩ col` via `matrixA_row_eval`, and `rhs ⟨a.val,_⟩`
  -- directly from `rhsVec`'s own definition (same row-0/row-1 case as `matrixA`).
  have hApply : ∀ col : Fin 4, A ⟨a.val, by omega⟩ col =
      let (px, py) := (![anchor1 p c0 c1 c2 c3 c4, anchor2 p c0 c1 c2 c3 c4] : Fin 2 →
        K2 p c0 c1 c2 c3 c4 × K2 p c0 c1 c2 c3 c4) a
      let (bi, bj, _) := rrBasis5.getD (otherIdx.getD col.val 0) (0, 0, 0)
      px ^ bi * (if bj = 1 then py else 1) := fun col =>
    matrixA_row_eval p c0 c1 c2 c3 c4 u0 u1 v0 v1 a col
  simp only [hApply] at hrow'
  have hrhsApply : rhs ⟨a.val, by omega⟩ =
      let (px, py) := (![anchor1 p c0 c1 c2 c3 c4, anchor2 p c0 c1 c2 c3 c4] : Fin 2 →
        K2 p c0 c1 c2 c3 c4 × K2 p c0 c1 c2 c3 c4) a
      let (bi_n, bj_n, _) := rrBasis5.getD yIdx (0, 1, 1)
      (-(px ^ bi_n * (if bj_n = 1 then py else 1))) := by
    show rhsVec p c0 c1 c2 c3 c4 u0 u1 v0 v1 ⟨a.val, by omega⟩ = _
    unfold rhsVec
    have h2 : (⟨a.val, by omega⟩ : Fin 4).val < 2 := by omega
    rw [dif_pos h2]
    congr 1
  rw [hrhsApply] at hrow'
  -- Move the RHS term to the left, recovering a 5-term additive identity
  -- (this is where `coeffsOut`'s extra `yIdx ↦ 1` slot re-enters).
  have hmoved : (∑ col : Fin 4, coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 (otherMap col) *
      (let (px, py) := (![anchor1 p c0 c1 c2 c3 c4, anchor2 p c0 c1 c2 c3 c4] : Fin 2 →
        K2 p c0 c1 c2 c3 c4 × K2 p c0 c1 c2 c3 c4) a
       let (bi, bj, _) := rrBasis5.getD (otherIdx.getD col.val 0) (0, 0, 0)
       px ^ bi * (if bj = 1 then py else 1))) +
      coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 ⟨yIdx, yIdx_lt_five⟩ *
        (let (px, py) := (![anchor1 p c0 c1 c2 c3 c4, anchor2 p c0 c1 c2 c3 c4] : Fin 2 →
          K2 p c0 c1 c2 c3 c4 × K2 p c0 c1 c2 c3 c4) a
         let (bi_n, bj_n, _) := rrBasis5.getD yIdx (0, 1, 1)
         px ^ bi_n * (if bj_n = 1 then py else 1)) = 0 := by
    have hcoeffsOutY : coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 ⟨yIdx, yIdx_lt_five⟩ = 1 := by
      unfold coeffsOut
      rw [dif_pos rfl]
    rw [hcoeffsOutY, one_mul]
    have hstep : ∑ col : Fin 4, coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 (otherMap col) *
        (let (px, py) := (![anchor1 p c0 c1 c2 c3 c4, anchor2 p c0 c1 c2 c3 c4] : Fin 2 →
          K2 p c0 c1 c2 c3 c4 × K2 p c0 c1 c2 c3 c4) a
         let (bi, bj, _) := rrBasis5.getD (otherIdx.getD col.val 0) (0, 0, 0)
         px ^ bi * (if bj = 1 then py else 1)) =
        ∑ col : Fin 4, cramerSolution p c0 c1 c2 c3 c4 u0 u1 v0 v1 col *
        (let (px, py) := (![anchor1 p c0 c1 c2 c3 c4, anchor2 p c0 c1 c2 c3 c4] : Fin 2 →
          K2 p c0 c1 c2 c3 c4 × K2 p c0 c1 c2 c3 c4) a
         let (bi, bj, _) := rrBasis5.getD (otherIdx.getD col.val 0) (0, 0, 0)
         px ^ bi * (if bj = 1 then py else 1)) := by
      apply Finset.sum_congr rfl
      intro col _
      rw [coeffsOut_otherMap]
    rw [hstep, ← hrow']
    ring
  -- Step 4: the reindexing identity, `sum_otherIdx_add_y` applied to
  -- `F bidx := coeffsOut bidx * (px ^ bi * (if bj = 1 then py else 1))`
  -- for `(bi,bj,_) := rrBasis5.getD bidx.val (0,0,0)`.
  set px := ((![anchor1 p c0 c1 c2 c3 c4, anchor2 p c0 c1 c2 c3 c4] : Fin 2 →
    K2 p c0 c1 c2 c3 c4 × K2 p c0 c1 c2 c3 c4) a).1 with hpx_def
  set py := ((![anchor1 p c0 c1 c2 c3 c4, anchor2 p c0 c1 c2 c3 c4] : Fin 2 →
    K2 p c0 c1 c2 c3 c4 × K2 p c0 c1 c2 c3 c4) a).2 with hpy_def
  set F : Fin 5 → K2 p c0 c1 c2 c3 c4 := fun bidx =>
    coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 bidx *
      (let (bi, bj, _) := rrBasis5.getD bidx.val (0, 0, 0)
       px ^ bi * (if bj = 1 then py else 1)) with hF_def
  have hFcol : ∀ col : Fin 4, F (otherMap col) =
      coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 (otherMap col) *
      (let (px, py) := (px, py)
       let (bi, bj, _) := rrBasis5.getD (otherIdx.getD col.val 0) (0, 0, 0)
       px ^ bi * (if bj = 1 then py else 1)) := by
    intro col
    show F (otherMap col) = _
    rw [hF_def]
    show coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 (otherMap col) *
      (let (bi, bj, _) := rrBasis5.getD (otherMap col).val (0, 0, 0)
       px ^ bi * (if bj = 1 then py else 1)) = _
    congr 2
    show (otherMap col).val = otherIdx.getD col.val 0
    rfl
  have hFy : F (⟨yIdx, yIdx_lt_five⟩ : Fin 5) =
      coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 ⟨yIdx, yIdx_lt_five⟩ *
      (let (px, py) := (px, py)
       let (bi_n, bj_n, _) := rrBasis5.getD yIdx (0, 1, 1)
       px ^ bi_n * (if bj_n = 1 then py else 1)) := by
    show F ⟨yIdx, yIdx_lt_five⟩ = _
    rw [hF_def]
    show coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 ⟨yIdx, yIdx_lt_five⟩ *
      (let (bi, bj, _) := rrBasis5.getD (⟨yIdx, yIdx_lt_five⟩ : Fin 5).val (0, 0, 0)
       px ^ bi * (if bj = 1 then py else 1)) = _
    congr 2
  have hsum5 : (∑ col : Fin 4, F (otherMap col)) + F ⟨yIdx, yIdx_lt_five⟩ =
      ∑ bidx : Fin 5, F bidx := sum_otherIdx_add_y p c0 c1 c2 c3 c4 F
  have hmoved' : (∑ col : Fin 4, F (otherMap col)) + F ⟨yIdx, yIdx_lt_five⟩ = 0 := by
    rw [Finset.sum_congr rfl (fun col _ => hFcol col), hFy]
    exact hmoved
  have hsum5' : ∑ bidx : Fin 5, F bidx = 0 := hsum5 ▸ hmoved'
  -- Step 5: split the 5-slot sum by `bj`, matching `Epoly`/`Ypoly`'s own
  -- `∑ bidx, if bj = 0/1 then ... else 0` definitions and
  -- `Polynomial.eval_finset_sum`.
  have hEval : (Epoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).eval px +
      py * (Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).eval px = ∑ bidx : Fin 5, F bidx := by
    unfold Epoly Ypoly
    rw [Polynomial.eval_finset_sum, Polynomial.eval_finset_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro bidx _
    show (let (bi, bj, _) := rrBasis5.getD bidx.val (0, 0, 0)
          if bj = 0 then Polynomial.eval px (C (coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 bidx) * X ^ bi)
          else Polynomial.eval px (0 : Polynomial (K2 p c0 c1 c2 c3 c4))) +
        py * (let (bi, bj, _) := rrBasis5.getD bidx.val (0, 0, 0)
              if bj = 1 then Polynomial.eval px (C (coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 bidx) * X ^ bi)
              else Polynomial.eval px (0 : Polynomial (K2 p c0 c1 c2 c3 c4))) = F bidx
    rw [hF_def]
    show _ = coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 bidx *
      (let (bi, bj, _) := rrBasis5.getD bidx.val (0, 0, 0)
       px ^ bi * (if bj = 1 then py else 1))
    obtain ⟨bi, bj, k⟩ := rrBasis5.getD bidx.val (0, 0, 0)
    simp only []
    rcases Nat.lt_or_ge bj 1 with hbj | hbj
    · interval_cases bj
      · simp [Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_mul]
    · rcases Nat.lt_or_ge bj 2 with hbj2 | hbj2
      · have : bj = 1 := by omega
        subst this
        simp [Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_mul]
        ring
      · -- `bj ≥ 2` never actually occurs in `rrBasis5` (always `0` or `1`),
        -- but the `let`-destructured `bj` here is a free `ℕ` as far as this
        -- `Finset.sum_congr` goal is concerned, so both branches' `if`
        -- conditions (`bj = 0`, `bj = 1`) are simply false, making both
        -- sides `0`.
        have hbj0 : ¬ (bj = 0) := by omega
        have hbj1 : ¬ (bj = 1) := by omega
        simp [hbj0, hbj1]
  rw [hsum5'] at hEval
  linarith [hEval]

theorem anchor1_defining_eq (hA : MatrixNondegenerate p c0 c1 c2 c3 c4 u0 u1 v0 v1) :
    (Epoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).eval (anchor1 p c0 c1 c2 c3 c4).1 +
      (anchor1 p c0 c1 c2 c3 c4).2 *
        (Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).eval (anchor1 p c0 c1 c2 c3 c4).1 = 0 := by
  have h := anchor_defining_eq_aux p c0 c1 c2 c3 c4 u0 u1 v0 v1 hA ⟨0, by norm_num⟩
  simpa using h

/-- Same identity at anchor 2 — the `a = 1` instance of `matrixA_row_eval`,
otherwise an identical argument to `anchor1_defining_eq` (same shared proof,
via `anchor_defining_eq_aux`). -/
theorem anchor2_defining_eq (hA : MatrixNondegenerate p c0 c1 c2 c3 c4 u0 u1 v0 v1) :
    (Epoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).eval (anchor2 p c0 c1 c2 c3 c4).1 +
      (anchor2 p c0 c1 c2 c3 c4).2 *
        (Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).eval (anchor2 p c0 c1 c2 c3 c4).1 = 0 := by
  have h := anchor_defining_eq_aux p c0 c1 c2 c3 c4 u0 u1 v0 v1 hA ⟨1, by norm_num⟩
  simpa using h

/-- **Step A, `K1`-level:** `w1 ^ 2 = algebraMap (K0 p) (K1 p ...) (fAtT p
... 0)`, extracted from `AdjoinRoot.eval₂_root` applied to `g := X^2 - C
(fAtT ... 0)`. `eval₂_root g : g.eval₂ (AdjoinRoot.of g) (AdjoinRoot.root g)
= 0`; unfolding `g`'s `eval₂` via `eval₂_sub`/`eval₂_pow`/`eval₂_X`/`eval₂_C`
gives `(root g)^2 - (of g) (fAtT ... 0) = 0`, and `AdjoinRoot.of g` IS
`algebraMap (K0 p) (K1 p ...)` by `AdjoinRoot.algebraMap_eq` (`of g =
algebraMap R (AdjoinRoot g)` unfolded). Solving for `(root g)^2` via
`sub_eq_zero` gives the claim, since `w1 p ... = AdjoinRoot.root g` and
`K1 p ... = AdjoinRoot g` are literally the same term by `w1`/`K1`'s own
definitions (`rfl`-transparent). -/
private theorem w1_sq_eq (c0 c1 c2 c3 c4 : F p) :
    (w1 p c0 c1 c2 c3 c4) ^ 2 =
      algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4) (fAtT p c0 c1 c2 c3 c4 0) := by
  have h := AdjoinRoot.eval₂_root
    (X ^ 2 - C (fAtT p c0 c1 c2 c3 c4 0) : Polynomial (K0 p))
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_C] at h
  -- `h : (AdjoinRoot.root g) ^ 2 - (AdjoinRoot.of g) (fAtT p ... 0) = 0`,
  -- `g := X^2 - C (fAtT p ... 0) : Polynomial (K0 p)`. Identify
  -- `AdjoinRoot.of g` with `algebraMap (K0 p) (K1 p ...)` as its own
  -- separate step (rather than a backward `rw [← AdjoinRoot.algebraMap_eq]`
  -- folded into the chain above) — unrolling this way avoids forcing one
  -- large `isDefEq` search across the whole rewritten term, which
  -- previously timed out at the default heartbeat budget. No `set`, to
  -- avoid the `let`-binding-vs-`rw` interaction this project has hit
  -- before; the polynomial is spelled out again explicitly instead.
  have hof :
      (AdjoinRoot.of (X ^ 2 - C (fAtT p c0 c1 c2 c3 c4 0) : Polynomial (K0 p))) =
        algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4) :=
    (AdjoinRoot.algebraMap_eq
      (X ^ 2 - C (fAtT p c0 c1 c2 c3 c4 0) : Polynomial (K0 p))).symm
  rw [hof] at h
  exact sub_eq_zero.mp h

/-- **Step A, `K2`-level:** the analogous fact one level up, `w2 ^ 2 =
algebraMap (K1 p ...) (K2 p ...) (algebraMap (K0 p) (K1 p ...) (fAtT p ...
1))`, i.e. `w2`'s defining quadratic living directly over `K1`. Identical
argument to `w1_sq_eq`, one tower level up, against `g := X^2 - C
(algebraMap (K0 p) (K1 p ...) (fAtT p ... 1))` (`K2`'s own defining
polynomial, matching `TheDataDerivation.K2`'s definition exactly). Same
unrolled-`rw` shape as `w1_sq_eq`, for the same heartbeat reason, and same
no-`set` reasoning. -/
private theorem w2_sq_eq (c0 c1 c2 c3 c4 : F p) :
    (w2 p c0 c1 c2 c3 c4) ^ 2 =
      algebraMap (K1 p c0 c1 c2 c3 c4) (K2 p c0 c1 c2 c3 c4)
        (algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4) (fAtT p c0 c1 c2 c3 c4 1)) := by
  have h := AdjoinRoot.eval₂_root
    (X ^ 2 - C (algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4) (fAtT p c0 c1 c2 c3 c4 1)) :
      Polynomial (K1 p c0 c1 c2 c3 c4))
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_C] at h
  -- Both a third explicit restatement of `g` (via `hof`/`rw [hof]`) and a
  -- plain `rw [← AdjoinRoot.algebraMap_eq]` hit the same `isDefEq` timeout
  -- here — `K1 p ...` is a reducible `abbrev` wrapping another `AdjoinRoot`,
  -- so `rw`'s keyed matching against this hypothesis forces repeated
  -- unfolding of that whole abbrev chain. `simp only` uses discrimination-
  -- tree indexing instead of `rw`'s matcher, which sidesteps that blowup.
  simp only [← AdjoinRoot.algebraMap_eq] at h
  exact sub_eq_zero.mp h

/-- **Step B:** `fAtX.eval (anchor1).1 = algebraMap (K1 p ...) (K2 p ...)
(algebraMap (K0 p) (K1 p ...) (fAtT p ... 0))`, i.e. `f` evaluated (as a
`Polynomial (K2 p ...)`, via `fAtX`) at `t1` promoted into `K2` agrees with
`fAtT`'s own `K0`-level evaluation, likewise promoted — both sides compute
"`f` applied to `t1`", just via two different but equal routes (`fAtX` maps
`curvePoly`'s COEFFICIENTS into `K2` and evaluates at the ALREADY-PROMOTED
point `anchor1.1`, i.e. `Polynomial.eval_map`; `fAtT` evaluates over `K0`
FIRST via `eval₂`, then promotes the scalar result). `Polynomial.eval_map`
(`(p.map f).eval x = p.eval₂ f x`) plus `RingHom.comp`/`eval₂` naturality
under a further `algebraMap` composition (`eval₂_at_apply`-style: applying a
ring hom to `p.eval₂ g x` equals `p.eval₂ (hom.comp g) (hom x)` when the
target hom is applied to BOTH the coefficients and the point) is the
mechanical content — routine but genuinely a small argument, not `rfl`,
since it requires commuting a `Polynomial.eval` with a composite of two
`algebraMap`s and `curvePoly`'s own unfolding into `fAtT`'s defining sum.
**Left as `sorry`**: same status as before (this file's docstring already
flagged this exact identification as the remaining gap in
`anchor1_curve_relation`), now isolated as its own lemma so the two
`w*_sq_eq` steps above (which ARE fully proved) are visibly separate from
this one remaining piece. -/
private theorem fAtX_eval_anchor1_eq :
    (fAtX p c0 c1 c2 c3 c4 u0 u1 v0 v1).eval (anchor1 p c0 c1 c2 c3 c4).1 =
      algebraMap (K1 p c0 c1 c2 c3 c4) (K2 p c0 c1 c2 c3 c4)
        (algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4) (fAtT p c0 c1 c2 c3 c4 0)) := by
  -- `g := algebraMap (K1 p ...) (K2 p ...) ∘ algebraMap (K0 p) (K1 p ...) : K0 p →+* K2 p ...`
  set g : K0 p →+* K2 p c0 c1 c2 c3 c4 :=
    (algebraMap (K1 p c0 c1 c2 c3 c4) (K2 p c0 c1 c2 c3 c4)).comp
      (algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4)) with hg
  -- `fAtX`'s LHS unfolds (via `eval_map`) to `curvePoly.eval₂ (algebraMap (F p) (K2 p ...))
  -- (anchor1.1)`; `fAtT`'s RHS, after folding the two nested `algebraMap`s into `g`, is
  -- `g (curvePoly.eval₂ (algebraMap (F p) (K0 p)) (t0 p 0))`. `hom_eval₂` turns the latter
  -- into `curvePoly.eval₂ (g.comp (algebraMap (F p) (K0 p))) (g (t0 p 0))`; after `hpoint`
  -- fixes the evaluation point, the only remaining gap is the coefficient-map hom itself
  -- (`algebraMap (F p) (K2 p ...)` vs `g.comp (algebraMap (F p) (K0 p))`), closed by `hcoeff`
  -- since any two ring homs out of `F p = ZMod p` agree (`RingHom.ext_zmod`).
  have hpoint : g (t0 p 0) = (anchor1 p c0 c1 c2 c3 c4).1 := by
    rw [hg, RingHom.comp_apply]; simp only [anchor1]
  have hfAtT : algebraMap (K1 p c0 c1 c2 c3 c4) (K2 p c0 c1 c2 c3 c4)
      (algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4) (fAtT p c0 c1 c2 c3 c4 0)) =
      g ((curvePoly p c0 c1 c2 c3 c4).eval₂ (algebraMap (F p) (K0 p)) (t0 p 0)) := by
    simp only [hg, RingHom.comp_apply, fAtT]
  have hcoeff : algebraMap (F p) (K2 p c0 c1 c2 c3 c4) = g.comp (algebraMap (F p) (K0 p)) :=
    RingHom.ext_zmod _ _
  rw [fAtX, Polynomial.eval_map, hfAtT,
    Polynomial.hom_eval₂ (curvePoly p c0 c1 c2 c3 c4) (algebraMap (F p) (K0 p)) g (t0 p 0),
    hpoint, hcoeff]

/-- Same identification at anchor 2. **Correction from the previous pass**:
this originally claimed a single promotion (`algebraMap (K1 p ...) (K2 p
...) (fAtT p ... 1)`), reasoning that `anchor2 p ... .2 = w2 p ...` needs
"no further promotion" — true for `w2` itself, but `K2`'s *defining
polynomial* (`TheDataDerivation.K2`, `DataDerivationTower.lean`) is built
over `X^2 - C (algebraMap (K0 p) (K1 p ...) (fAtT p ... 1))`, i.e. `fAtT p
... 1` IS already promoted through `K0 → K1` before `K2`'s tower step ever
sees it — matching `w2_sq_eq`'s RHS exactly. The single-promotion version
was inconsistent with `w2_sq_eq` and left `anchor2_curve_relation` unable
to close (the two `rw`s produced non-defeq single- vs double-promoted
terms). -/
private theorem fAtX_eval_anchor2_eq :
    (fAtX p c0 c1 c2 c3 c4 u0 u1 v0 v1).eval (anchor2 p c0 c1 c2 c3 c4).1 =
      algebraMap (K1 p c0 c1 c2 c3 c4) (K2 p c0 c1 c2 c3 c4)
        (algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4) (fAtT p c0 c1 c2 c3 c4 1)) := by
  -- Identical argument to `fAtX_eval_anchor1_eq`, at anchor 2 (`t0 p 1` instead of `t0 p 0`);
  -- `anchor2.1` is built by the same double-`algebraMap` promotion as `anchor1.1`.
  set g : K0 p →+* K2 p c0 c1 c2 c3 c4 :=
    (algebraMap (K1 p c0 c1 c2 c3 c4) (K2 p c0 c1 c2 c3 c4)).comp
      (algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4)) with hg
  have hpoint : g (t0 p 1) = (anchor2 p c0 c1 c2 c3 c4).1 := by
    rw [hg, RingHom.comp_apply]; simp only [anchor2]
  have hfAtT : algebraMap (K1 p c0 c1 c2 c3 c4) (K2 p c0 c1 c2 c3 c4)
      (algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4) (fAtT p c0 c1 c2 c3 c4 1)) =
      g ((curvePoly p c0 c1 c2 c3 c4).eval₂ (algebraMap (F p) (K0 p)) (t0 p 1)) := by
    simp only [hg, RingHom.comp_apply, fAtT]
  have hcoeff : algebraMap (F p) (K2 p c0 c1 c2 c3 c4) = g.comp (algebraMap (F p) (K0 p)) :=
    RingHom.ext_zmod _ _
  rw [fAtX, Polynomial.eval_map, hfAtT,
    Polynomial.hom_eval₂ (curvePoly p c0 c1 c2 c3 c4) (algebraMap (F p) (K0 p)) g (t0 p 1),
    hpoint, hcoeff]

/-- **Assembled**: `w1^2 = f(t1)` promoted into `K2`, combining `w1_sq_eq`
(promoted through `algebraMap (K1 p ...) (K2 p ...)`, since `anchor1.2 =
algebraMap K1 K2 (w1 ...)` by `anchor1`'s own definition — a ring hom
commutes with `^2`, `map_pow`) with `fAtX_eval_anchor1_eq`. This is the
"routine algebraMap-commutes-with-eval reasoning" the original docstring
named; `w1_sq_eq` itself (the genuinely definitional half, from
`AdjoinRoot.eval₂_root`) is now a complete proof, so what remains
(`fAtX_eval_anchor1_eq`) is exactly and only the eval/algebraMap
compatibility half. -/
theorem anchor1_curve_relation :
    (anchor1 p c0 c1 c2 c3 c4).2 ^ 2 =
      (fAtX p c0 c1 c2 c3 c4 u0 u1 v0 v1).eval (anchor1 p c0 c1 c2 c3 c4).1 := by
  change (algebraMap (K1 p c0 c1 c2 c3 c4) (K2 p c0 c1 c2 c3 c4) (w1 p c0 c1 c2 c3 c4)) ^ 2 = _
  rw [← map_pow, w1_sq_eq, fAtX_eval_anchor1_eq]

/-- Same relation at anchor 2, combining `w2_sq_eq` directly (`anchor2.2 =
w2 p ...` with no further promotion, per `anchor2`'s own simpler definition)
with `fAtX_eval_anchor2_eq`. -/
theorem anchor2_curve_relation :
    (anchor2 p c0 c1 c2 c3 c4).2 ^ 2 =
      (fAtX p c0 c1 c2 c3 c4 u0 u1 v0 v1).eval (anchor2 p c0 c1 c2 c3 c4).1 := by
  change (w2 p c0 c1 c2 c3 c4) ^ 2 = _
  rw [w2_sq_eq, fAtX_eval_anchor2_eq]

/-- `(X - t1)` divides `N(x)` — the roadmap's proposed argument, now
actually assembled: `N(t1) = E(t1)^2 - f(t1)*Y(t1)^2`
(`Npoly`/`fAtX`'s definitions, unfolded via `Polynomial.eval_sub`/
`eval_pow`/`eval_mul`), which equals `0` by combining
`anchor1_defining_eq` (`E(t1) = -(w1*Y(t1))`, so `E(t1)^2 = w1^2*Y(t1)^2`
after squaring — `neg_mul`/`mul_pow`/`neg_sq`-style rewriting) with
`anchor1_curve_relation` (`w1^2 = f(t1)`, substituted in). Converted to
divisibility via `Polynomial.dvd_iff_isRoot`. -/
theorem dvd_N_anchor1 (hA : MatrixNondegenerate p c0 c1 c2 c3 c4 u0 u1 v0 v1) :
    (X - C (anchor1 p c0 c1 c2 c3 c4).1) ∣ Npoly p c0 c1 c2 c3 c4 u0 u1 v0 v1 := by
  unfold Npoly
  rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_mul, Polynomial.eval_pow]
  have hE := anchor1_defining_eq p c0 c1 c2 c3 c4 u0 u1 v0 v1 hA
  have hw := anchor1_curve_relation p c0 c1 c2 c3 c4 u0 u1 v0 v1
  have hEeq : (Epoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).eval (anchor1 p c0 c1 c2 c3 c4).1
      = -((anchor1 p c0 c1 c2 c3 c4).2 * (Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).eval
            (anchor1 p c0 c1 c2 c3 c4).1) :=
    eq_neg_of_add_eq_zero_left hE
  -- Goal here: `E(t1)^2 - fAtX.eval t1 * Y(t1)^2 = 0`. Substitute `hEeq`, expand
  -- the square so `w1^2` appears as an isolated factor, then substitute `hw`
  -- (`w1^2 = fAtX.eval t1`) and close by `ring`.
  rw [hEeq, neg_sq, mul_pow, hw]
  ring

/-- `(X - t2)` divides `N(x)`, the `i=2` analogue, identical structure. -/
theorem dvd_N_anchor2 (hA : MatrixNondegenerate p c0 c1 c2 c3 c4 u0 u1 v0 v1) :
    (X - C (anchor2 p c0 c1 c2 c3 c4).1) ∣ Npoly p c0 c1 c2 c3 c4 u0 u1 v0 v1 := by
  unfold Npoly
  rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_mul, Polynomial.eval_pow]
  have hE := anchor2_defining_eq p c0 c1 c2 c3 c4 u0 u1 v0 v1 hA
  have hw := anchor2_curve_relation p c0 c1 c2 c3 c4 u0 u1 v0 v1
  have hEeq : (Epoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).eval (anchor2 p c0 c1 c2 c3 c4).1
      = -((anchor2 p c0 c1 c2 c3 c4).2 * (Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).eval
            (anchor2 p c0 c1 c2 c3 c4).1) :=
    eq_neg_of_add_eq_zero_left hE
  rw [hEeq, neg_sq, mul_pow, hw]
  ring

/-- `u(x) = X² + u1 X + u0` divides `N(x)`. Unlike the two anchor cases,
`u(x)`'s roots are not literal anchors of the linear system in the same
direct sense — the mod-`u` rows (rows 2,3 of `A`) encode the Mumford
condition via `reduceMonomialModU`'s reduction table rather than via a
named point `(x_0, y_0)` with `x_0` a root of `u`, so there is no single
`eval`-at-a-point argument the way `dvd_iff_isRoot` gave the anchor cases —
`u(x)` need not even have roots IN `K2` (it may be irreducible over the
base `F(t1,t2)`-type field, in which case `u_RS`'s own construction as a
degree-2 factor is exactly what's making it meaningful, not a root
witness). **Left as `sorry`, genuinely unresolved this pass**: this is
still the part of item 6 without a sketched strategy — the roadmap did not
propose one beyond "needs an actual divisibility proof". One angle worth
trying next session that ISN'T in the roadmap yet: rows 2–3 of `A ·
coeffsOut = rhsVec` are, by `reduceMonomialModU`'s construction, exactly the
statement "`E(x) + Y(x)*(v1*x+v0) ≡ 0 (mod u(x))`" (the two mod-`u` rows are
literally the `x^0`/`x^1` coefficients of that one polynomial congruence,
unpacked componentwise via `xmodUTable`) — if so, `u(x) ∣ (E(x) +
Y(x)*(v1 X + v0))` directly (a polynomial-level fact, not a per-root one),
which is a different and possibly more tractable route into `u(x) ∣ N(x)`
than chasing individual roots: one would still need to relate `(E+Y*(v1X+
v0))`'s vanishing mod `u` to `E^2-f*Y^2`'s vanishing mod `u`, likely via
`v(x)^2 ≡ f(x) mod u(x)` for the TARGET `v(x)=v1*x+v0` itself (a
hypothesis on the sample data, not proved here, but plausibly available
from how `(u0,u1,v0,v1)` are chosen upstream in `elim2` — worth checking
against `00_sample_specs.jl`, not yet done this pass) — flagged as a
concrete next angle, not pursued further here since it introduces a new
hypothesis (`v(x)^2 ≡ f mod u(x)` for the TARGET, distinct from
`vRS_sq_eq_f_mod_uRS`'s claim about the COMPUTED `v_RS`) that itself needs
sourcing and stating precisely before this can be attempted.

**Type fix**: the divisor `X^2 + u1*X + u0` must live in `Polynomial (K2 p
...)` to match `Npoly`'s type (a previous version wrote `C u1`/`C u0`
directly, which are `Polynomial (F p)` since `u0 u1 : F p` — a type
mismatch, since `X` here is `Polynomial (K2 p ...)`). Promoted `u0`,`u1`
into `K2 p ...` via `algebraMap (F p) (K2 p ...)` before applying `C`,
matching the pattern already used correctly elsewhere in this file (e.g.
`fAtX`, `rhsVec`'s `algebraMap (F p) (K2 p ...)` calls). -/
theorem dvd_N_u :
    (X ^ 2 + C (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u1) * X +
        C (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u0)) ∣
      Npoly p c0 c1 c2 c3 c4 u0 u1 v0 v1 := by
  sorry

/-- The quotient `N(x) / ((X-t1)(X-t2)(X²+u1 X+u0))`, i.e. `cur` just before
Julia's "Normalize to monic" step (line 469) — packaged here as a
`Polynomial.div`-based definition that only equals the true exact quotient
under `dvd_N_anchor1`/`dvd_N_anchor2`/`dvd_N_u` all holding; stated
unconditionally (via `/ₘ`, Mathlib's polynomial division, always
defined) so downstream defs typecheck, with correctness deferred to
wherever this is actually used against the three divisibility facts. -/
noncomputable def curBeforeMonic : Polynomial (K2 p c0 c1 c2 c3 c4) :=
  ((Npoly p c0 c1 c2 c3 c4 u0 u1 v0 v1 /ₘ (X - C (anchor1 p c0 c1 c2 c3 c4).1))
      /ₘ (X - C (anchor2 p c0 c1 c2 c3 c4).1))
    /ₘ (X ^ 2 + C (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u1) * X +
        C (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u0))

end ExactDivision

end TheDataDerivation
end Genus2Lean
