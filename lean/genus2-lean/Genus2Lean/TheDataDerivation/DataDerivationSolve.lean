import Mathlib
import Genus2Lean.TheDataDerivation.DataDerivationTower

/-!
# `theData` derivation, part 3: the `4×4` linear solve and exact division

Third of four files — see `DataDerivationBasics.lean`'s header for the full
split rationale and file order. This file builds §4.2 items 4–5 (the `4×4`
Cramer's-rule solve, `E(x)`/`Y(x)`/`N(x) = E²-fY²`) and item 6 (exact
division of `N(x)` by `(X-t1)`, `(X-t2)`, and the target `u(x)`).

**This pass's work is entirely in item 6**, closing out the anchor `sorry`s
that earlier passes left after proving `dvd_N_anchor1`/`dvd_N_anchor2`
themselves:

- `anchor{1,2}_curve_relation` are **fully proved, no `sorry`** — split
  into a genuinely-definitional half (`w{1,2}_sq_eq`, from
  `AdjoinRoot.eval₂_root` unfolded via `eval₂_sub`/`eval₂_pow`/`eval₂_X`/
  `eval₂_C` and `AdjoinRoot.algebraMap_eq`, fully proved) and an eval/
  algebraMap-compatibility half (`fAtX_eval_anchor{1,2}_eq`, **also now
  fully proved, no `sorry`**). Concrete Mathlib lemma names were looked up
  directly against the `mathlib4` source, not guessed.
- `anchor{1,2}_defining_eq` (via the shared `anchor_defining_eq_aux`) are
  **now fully proved, no `sorry`**: the row-unfolding lemma `matrixA_row_eval`
  isolates the row-0/row-1 case split, `Matrix.mulVec_cramer` supplies
  step 1, a `field_simp`/`mul_right_cancel₀`-based argument (avoiding a
  fragile `congrArg (· / A.det)` rewrite that broke under `A`'s `set`-bound
  unfolding) supplies step 2, `matrixA_row_eval`/`rhsVec`'s own definition
  supply step 3, and the reindexing step (`Fin 4`-sum via `otherIdx` vs.
  `Fin 5`-sum over all of `rrBasis5`) is closed via `sum_otherIdx_add_y`.

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

-- Raised from the 200000 default (10x) per explicit instruction: this
-- file's proofs work over `Polynomial (K2 p c0 c1 c2 c3 c4)`, a
-- deliberately-reducible triple-stacked `AdjoinRoot`/`FractionRing` tower,
-- so `whnf`/`isDefEq` cost is structurally heavy even after replacing
-- `set` with `let`+`clear_value` at the worst offenders (see those sites'
-- comments). This is a scoped, deliberate loosening for this file's known
-- arithmetic weight, not a substitute for the opacity-boundary work.
set_option maxHeartbeats 2000000

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
    let (_, bi, bj) := rrBasis5.getD bidx (0, 0, 0)
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
    let (_, bi_n, bj_n) := rrBasis5.getD yIdx (0, 1, 1)
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
    let (_, bi, bj) := rrBasis5.getD bidx.val (0, 0, 0)
    if bj = 0 then C (coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 bidx) * X ^ bi else 0

noncomputable def Ypoly (c0 c1 c2 c3 c4 u0 u1 v0 v1 : F p) : Polynomial (K2 p c0 c1 c2 c3 c4) :=
  ∑ bidx : Fin 5,
    let (_, bi, bj) := rrBasis5.getD bidx.val (0, 0, 0)
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
      let (_, bi, bj) := rrBasis5.getD (otherIdx.getD col.val 0) (0, 0, 0)
      px ^ bi * (if bj = 1 then py else 1) := by
  fin_cases a <;> simp [matrixA]

/-- **Row-unfolding lemma for the mod-`u` rows.** `matrixA`'s row `2+a.val`
(`a : Fin 2`, so row 2 or row 3) evaluated at any `col : Fin 4` is the
`a`-th component (`.1` for row 2, `.2` for row 3) of `reduceMonomialModU`
applied to the basis pair at `otherIdx.getD col.val 0` — `matrixA`'s
`else` branch unfolded literally, same role as `matrixA_row_eval` for the
anchor rows. -/
private theorem matrixA_row23_eval (a : Fin 2) (col : Fin 4) :
    matrixA p c0 c1 c2 c3 c4 u0 u1 v0 v1 ⟨2 + a.val, by omega⟩ col =
      let (_, bi, bj) := rrBasis5.getD (otherIdx.getD col.val 0) (0, 0, 0)
      let (r0, r1) := reduceMonomialModU p u0 u1 v0 v1 bi bj
      algebraMap (F p) (K2 p c0 c1 c2 c3 c4) (if a.val = 0 then r0 else r1) := by
  fin_cases a <;> simp [matrixA]

/-- Same row-unfolding for `rhsVec`'s rows 2/3. -/
private theorem rhsVec_row23_eval (a : Fin 2) :
    rhsVec p c0 c1 c2 c3 c4 u0 u1 v0 v1 ⟨2 + a.val, by omega⟩ =
      let (_, bi_n, bj_n) := rrBasis5.getD yIdx (0, 1, 1)
      let (rn0, rn1) := reduceMonomialModU p u0 u1 v0 v1 bi_n bj_n
      (-algebraMap (F p) (K2 p c0 c1 c2 c3 c4) (if a.val = 0 then rn0 else rn1)) := by
  fin_cases a <;> simp [rhsVec]

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
  change otherIdx.getD n 0 = b.val
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
      change (⟨otherIdx.getD col.val 0, _⟩ : Fin 5) ≠ ⟨yIdx, yIdx_lt_five⟩
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
    change otherIdx.getD col.val 0 ≠ yIdx
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
    rw [hspec]
    change otherIdx.getD col.val 0 = otherIdx[col.val]
    exact hgetD
  have hidx_eq : hex.choose = col.val :=
    otherIdx_nodup.getElem_inj_iff.mp hgoal_val
  have hchoose_lt4 : hex.choose < 4 := by rw [← otherIdx_length]; exact hex.choose_spec.choose
  exact congrArg (cramerSolution p c0 c1 c2 c3 c4 u0 u1 v0 v1)
    (Fin.ext (a := (⟨hex.choose, hchoose_lt4⟩ : Fin 4)) (b := col) hidx_eq)


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
   ... else 0` definitions, plus `Polynomial.eval_finsetSum`/`eval_C_mul_X_pow`
   to turn the polynomial-eval statement back into the same sum shape).

Steps 1–3 and 5 are routine algebraic rewriting; step 4 is the one piece
that is easiest to close by computation (`decide`/`rfl` on the concrete
5-element data) rather than a general lemma, and is exactly the kind of
step that benefits from an actual toolchain to get the `Finset`/`List`
API calls exactly right — **left as `sorry`** rather than risk a wrong
lemma name or off-by-one with no compiler to catch it, but the argument
above is a complete, checkable-in-principle proof sketch, one level more
precise than the previous draft's prose summary. -/
private lemma anchor_defining_eq_aux (hA : MatrixNondegenerate p c0 c1 c2 c3 c4 u0 u1 v0 v1)
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
  -- Named once and reused everywhere below, rather than writing `by omega`
  -- afresh at each occurrence: two syntactically distinct (but propositionally
  -- equal) proof terms inside `⟨a.val, _⟩ : Fin 4` are not `rw`-unifiable
  -- without an `isDefEq` check, and repeating that check across every
  -- `Finset.sum_congr`/`rw` site below is what was forcing the `whnf` timeout.
  have haRow : a.val < 4 := by omega
  -- Step 1: Cramer's rule, unfolded pointwise at row `⟨a.val, _⟩`.
  have hmul := Matrix.mulVec_cramer A rhs
  have hrow := congrFun hmul (⟨a.val, haRow⟩ : Fin 4)
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hrow
  -- `hrow : ∑ col, A ⟨a.val,_⟩ col * A.cramer rhs col = A.det * rhs ⟨a.val,_⟩`.
  -- Step 2: divide by `A.det ≠ 0`, turning `cramer .../ det` into `cramerSolution`.
  have hrow' : ∑ col : Fin 4, A ⟨a.val, haRow⟩ col *
      (A.cramer rhs col / A.det) = rhs ⟨a.val, haRow⟩ := by
    have hstep : (∑ col : Fin 4, A ⟨a.val, haRow⟩ col * (A.cramer rhs col / A.det)) * A.det =
        rhs ⟨a.val, haRow⟩ * A.det := by
      rw [Finset.sum_mul]
      have : ∀ col : Fin 4, A ⟨a.val, haRow⟩ col * (A.cramer rhs col / A.det) * A.det =
          A ⟨a.val, haRow⟩ col * A.cramer rhs col := by
        intro col
        field_simp
      simp only [this]
      rw [hrow]
      ring
    exact mul_right_cancel₀ hdet hstep
  have hcramerSolution : ∀ col : Fin 4, A.cramer rhs col / A.det =
      cramerSolution p c0 c1 c2 c3 c4 u0 u1 v0 v1 col := fun col => rfl
  simp only [hcramerSolution] at hrow'
  -- `hrow' : ∑ col, A ⟨a.val,_⟩ col * cramerSolution ... col = rhs ⟨a.val,_⟩`.
  -- Step 3: unfold `A ⟨a.val,_⟩ col` via `matrixA_row_eval`, and `rhs ⟨a.val,_⟩`
  -- directly from `rhsVec`'s own definition (same row-0/row-1 case as `matrixA`).
  -- `hrow'` is deliberately left in terms of `A ⟨a.val,_⟩ col` here (not
  -- `simp`-unfolded) so its syntactic shape stays exactly what we wrote —
  -- unfolding happens only at the point of use below, via explicit `rw`s
  -- whose target shape we control completely.
  have hApply : ∀ col : Fin 4, A ⟨a.val, haRow⟩ col =
      let (px, py) := (![anchor1 p c0 c1 c2 c3 c4, anchor2 p c0 c1 c2 c3 c4] : Fin 2 →
        K2 p c0 c1 c2 c3 c4 × K2 p c0 c1 c2 c3 c4) a
      let (_, bi, bj) := rrBasis5.getD (otherIdx.getD col.val 0) (0, 0, 0)
      px ^ bi * (if bj = 1 then py else 1) := fun col =>
    matrixA_row_eval p c0 c1 c2 c3 c4 u0 u1 v0 v1 a col
  have hrhsApply : rhs ⟨a.val, haRow⟩ =
      let (px, py) := (![anchor1 p c0 c1 c2 c3 c4, anchor2 p c0 c1 c2 c3 c4] : Fin 2 →
        K2 p c0 c1 c2 c3 c4 × K2 p c0 c1 c2 c3 c4) a
      let (_, bi_n, bj_n) := rrBasis5.getD yIdx (0, 1, 1)
      (-(px ^ bi_n * (if bj_n = 1 then py else 1))) := by
    show rhsVec p c0 c1 c2 c3 c4 u0 u1 v0 v1 ⟨a.val, haRow⟩ = _
    unfold rhsVec
    have h2 : (⟨a.val, haRow⟩ : Fin 4).val < 2 := a.isLt
    simp only [dif_pos h2]
    
  -- 🛑 CLEAR VALUES HERE 🛑
  -- A and rhs become opaque variables. We still have `hA_def` and `hrhs_def` 
  -- if we desperately needed them, but the unifier can no longer silently 
  -- unfold them into giant polynomials during the `rw` steps below.
  clear_value A rhs

  rw [hrhsApply] at hrow'
  -- Move the RHS term to the left, recovering a 5-term additive identity
  -- (this is where `coeffsOut`'s extra `yIdx ↦ 1` slot re-enters).
  have hmoved : (∑ col : Fin 4, coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 (otherMap col) *
      (let (px, py) := (![anchor1 p c0 c1 c2 c3 c4, anchor2 p c0 c1 c2 c3 c4] : Fin 2 →
        K2 p c0 c1 c2 c3 c4 × K2 p c0 c1 c2 c3 c4) a
       let (_, bi, bj) := rrBasis5.getD (otherIdx.getD col.val 0) (0, 0, 0)
       px ^ bi * (if bj = 1 then py else 1))) +
      coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 ⟨yIdx, yIdx_lt_five⟩ *
        (let (px, py) := (![anchor1 p c0 c1 c2 c3 c4, anchor2 p c0 c1 c2 c3 c4] : Fin 2 →
          K2 p c0 c1 c2 c3 c4 × K2 p c0 c1 c2 c3 c4) a
         let (_, bi_n, bj_n) := rrBasis5.getD yIdx (0, 1, 1)
         px ^ bi_n * (if bj_n = 1 then py else 1)) = 0 := by
    have hcoeffsOutY : coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 ⟨yIdx, yIdx_lt_five⟩ = 1 := by
      unfold coeffsOut
      rw [dif_pos rfl]
    rw [hcoeffsOutY, one_mul]
    have hstep : ∑ col : Fin 4, coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 (otherMap col) *
        (let (px, py) := (![anchor1 p c0 c1 c2 c3 c4, anchor2 p c0 c1 c2 c3 c4] : Fin 2 →
          K2 p c0 c1 c2 c3 c4 × K2 p c0 c1 c2 c3 c4) a
         let (_, bi, bj) := rrBasis5.getD (otherIdx.getD col.val 0) (0, 0, 0)
         px ^ bi * (if bj = 1 then py else 1)) =
        ∑ col : Fin 4, cramerSolution p c0 c1 c2 c3 c4 u0 u1 v0 v1 col *
        (let (px, py) := (![anchor1 p c0 c1 c2 c3 c4, anchor2 p c0 c1 c2 c3 c4] : Fin 2 →
          K2 p c0 c1 c2 c3 c4 × K2 p c0 c1 c2 c3 c4) a
         let (_, bi, bj) := rrBasis5.getD (otherIdx.getD col.val 0) (0, 0, 0)
         px ^ bi * (if bj = 1 then py else 1)) := by
      apply Finset.sum_congr rfl
      intro col _
      rw [coeffsOut_otherMap p c0 c1 c2 c3 c4 u0 u1 v0 v1 col]
    -- Goal after `rw [hstep]`: `∑ col, cramerSolution ... col * (let-expr) = -(...)`.
    -- `hrow'` has factor order `A ⟨a.val,_⟩ col * cramerSolution ... col`
    -- (unmodified by `simp`, so its shape is exactly what we wrote above).
    -- Flip each summand to `A`-first form, matching `hrow'` exactly, then
    -- close directly — no `rw` into `hrow'` itself, avoiding any dependence
    -- on `simp`'s internal normal form.
    have horder : (∑ col : Fin 4, cramerSolution p c0 c1 c2 c3 c4 u0 u1 v0 v1 col *
          (let (px, py) := (![anchor1 p c0 c1 c2 c3 c4, anchor2 p c0 c1 c2 c3 c4] : Fin 2 →
            K2 p c0 c1 c2 c3 c4 × K2 p c0 c1 c2 c3 c4) a
           let (_, bi, bj) := rrBasis5.getD (otherIdx.getD col.val 0) (0, 0, 0)
           px ^ bi * (if bj = 1 then py else 1)))
        = ∑ col : Fin 4, A ⟨a.val, haRow⟩ col *
            cramerSolution p c0 c1 c2 c3 c4 u0 u1 v0 v1 col := by
      apply Finset.sum_congr rfl
      intro col _
      rw [mul_comm (cramerSolution p c0 c1 c2 c3 c4 u0 u1 v0 v1 col), hApply col]
    rw [hstep, horder, hrow']
    exact neg_add_cancel _
  -- Step 4: the reindexing identity, `sum_otherIdx_add_y` applied to
  -- `F bidx := coeffsOut bidx * (px ^ bi * (if bj = 1 then py else 1))`
  -- for `(bi,bj,_) := rrBasis5.getD bidx.val (0,0,0)`.
  set px := ((![anchor1 p c0 c1 c2 c3 c4, anchor2 p c0 c1 c2 c3 c4] : Fin 2 →
    K2 p c0 c1 c2 c3 c4 × K2 p c0 c1 c2 c3 c4) a).1 with hpx_def
  set py := ((![anchor1 p c0 c1 c2 c3 c4, anchor2 p c0 c1 c2 c3 c4] : Fin 2 →
    K2 p c0 c1 c2 c3 c4 × K2 p c0 c1 c2 c3 c4) a).2 with hpy_def
  set F : Fin 5 → K2 p c0 c1 c2 c3 c4 := fun bidx =>
    coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 bidx *
      (let (_, bi, bj) := rrBasis5.getD bidx.val (0, 0, 0)
       px ^ bi * (if bj = 1 then py else 1)) with hF_def
  have hFcol : ∀ col : Fin 4, F (otherMap col) =
      coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 (otherMap col) *
      (let (px, py) := (px, py)
       let (_, bi, bj) := rrBasis5.getD (otherIdx.getD col.val 0) (0, 0, 0)
       px ^ bi * (if bj = 1 then py else 1)) := by
    intro col
    change
      coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 (otherMap col) *
          (let (_, bi, bj) := rrBasis5.getD (otherMap col).val (0, 0, 0)
           px ^ bi * (if bj = 1 then py else 1)) = _
    rfl
  have hFy : F (⟨yIdx, yIdx_lt_five⟩ : Fin 5) =
      coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 ⟨yIdx, yIdx_lt_five⟩ *
      (let (px, py) := (px, py)
       let (_, bi_n, bj_n) := rrBasis5.getD yIdx (0, 1, 1)
       px ^ bi_n * (if bj_n = 1 then py else 1)) := by
    change
      coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 ⟨yIdx, yIdx_lt_five⟩ *
          (let (_, bi, bj) := rrBasis5.getD yIdx (0, 0, 0)
           px ^ bi * (if bj = 1 then py else 1)) = _
    have hy_len : yIdx < rrBasis5.length := by
      have hlen : rrBasis5.length = 5 := by
        simp [rrBasis5, rrBasisCandidates, List.length_flatMap]
      rw [hlen]
      exact yIdx_lt_five
    have hy_get : rrBasis5.getD yIdx (0, 0, 0) = rrBasis5.getD yIdx (0, 1, 1) := by
      rw [List.getD_eq_getElem _ _ hy_len, List.getD_eq_getElem _ _ hy_len]
    rw [hy_get]
  have hsum5 : (∑ col : Fin 4, F (otherMap col)) + F ⟨yIdx, yIdx_lt_five⟩ =
      ∑ bidx : Fin 5, F bidx := sum_otherIdx_add_y p c0 c1 c2 c3 c4 F
  have hmoved' : (∑ col : Fin 4, F (otherMap col)) + F ⟨yIdx, yIdx_lt_five⟩ = 0 := by
    calc
      (∑ col : Fin 4, F (otherMap col)) + F ⟨yIdx, yIdx_lt_five⟩ =
          (∑ col : Fin 4, coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 (otherMap col) *
            (let (px, py) := (px, py)
             let (_, bi, bj) := rrBasis5.getD (otherIdx.getD col.val 0) (0, 0, 0)
             px ^ bi * (if bj = 1 then py else 1))) +
            coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 ⟨yIdx, yIdx_lt_five⟩ *
              (let (px, py) := (px, py)
               let (_, bi_n, bj_n) := rrBasis5.getD yIdx (0, 1, 1)
               px ^ bi_n * (if bj_n = 1 then py else 1)) := by
            rw [Finset.sum_congr rfl (fun col _ => hFcol col), hFy]
      _ = 0 := hmoved
  have hsum5' : ∑ bidx : Fin 5, F bidx = 0 := hsum5 ▸ hmoved'
  -- Step 5: split the 5-slot sum by `bj`, matching `Epoly`/`Ypoly`'s own
  -- `∑ bidx, if bj = 0/1 then ... else 0` definitions and
  -- `Polynomial.eval_finsetSum`.
  have hEval : (Epoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).eval px +
      py * (Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).eval px = ∑ bidx : Fin 5, F bidx := by
    unfold Epoly Ypoly
    rw [Polynomial.eval_finsetSum, Polynomial.eval_finsetSum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro bidx hbmem
    have hbj0or1 :
        (rrBasis5.getD bidx.val (0, 0, 0)).2.2 = 0 ∨
        (rrBasis5.getD bidx.val (0, 0, 0)).2.2 = 1 := by
      have hlen : rrBasis5.length = 5 := by
        simp [rrBasis5, rrBasisCandidates, List.length_flatMap]
      have hlt : bidx.val < rrBasis5.length := by rw [hlen]; exact bidx.isLt
      rw [List.getD_eq_getElem _ _ hlt]
      exact rrBasis5_flag _ (List.getElem_mem hlt)
    rcases hbj0or1 with hb0 | hb1
    · have hb1' : (rrBasis5.getD bidx.val (0, 0, 0)).2.2 ≠ 1 := by omega
      simp only [if_pos hb0, if_neg hb1', Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_zero]
      dsimp only [F]
      rw [hb0]
      simp only [if_neg (show (0:ℕ) ≠ 1 by omega)]
      ring
    · have hb0' : (rrBasis5.getD bidx.val (0, 0, 0)).2.2 ≠ 0 := by omega
      simp only [if_neg hb0', if_pos hb1, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_zero]
      dsimp only [F]
      rw [hb1]
      simp only [if_true]
      ring
  rw [hsum5'] at hEval
  exact hEval

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

/-- `xmodUTable_correct`, lifted from `F p` to `K2 p ...` via `Polynomial.
map_modByMonic` (`map f (p %ₘ q) = map f p %ₘ map f q`, given `q.Monic`)
applied to `f := algebraMap (F p) (K2 p ...)`, `q := X^2+C u1*X+C u0`. The
LHS `map f (X^n %ₘ u) = (X^n : Polynomial K) %ₘ U` since `map f` commutes
with `X^n` (`Polynomial.map_pow`/`map_X`) and `map f u = U` (`map_add`/
`map_mul`/`map_C`/`map_X`/`map_pow`); the RHS similarly turns `map f (C a +
C b * X)` into `C (f a) + C (f b) * X`. -/
private theorem xmodUTable_correct_K (u0 u1 : F p) (n : ℕ) :
    (X ^ n : Polynomial (K2 p c0 c1 c2 c3 c4)) %ₘ
        (X ^ 2 + C (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u1) * X +
          C (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u0)) =
      C (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) (xmodUTable p u0 u1 n).1) +
        C (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) (xmodUTable p u0 u1 n).2) * X := by
  -- `let` + `clear_value` (not `set`): per the fix for this file's timeout,
  -- `set` performs a goal-wide occurrence search/replace, which is expensive
  -- against `K2`-typed terms; `let` binds the name cheaply and `clear_value`
  -- then makes it opaque to later defeq checks while keeping the defining
  -- equality (`hg_def`/`hu_def`) available at the one place it's needed.
  let g : F p →+* K2 p c0 c1 c2 c3 c4 := algebraMap (F p) (K2 p c0 c1 c2 c3 c4)
  clear_value (hg_def : g = algebraMap (F p) (K2 p c0 c1 c2 c3 c4))
  let u : Polynomial (F p) := X ^ 2 + C u1 * X + C u0
  clear_value (hu_def : u = X ^ 2 + C u1 * X + C u0)
  have hUmap : (X ^ 2 + C (g u1) * X + C (g u0) : Polynomial (K2 p c0 c1 c2 c3 c4)) = u.map g := by
    rw [hg_def, hu_def]
    simp [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C,
      Polynomial.map_X]
  have huMonic : u.Monic := by rw [hu_def]; exact uPoly_monic p u0 u1
  -- Fold the goal to `g`/`u`-form (`← hg_def` for the `algebraMap` occurrences,
  -- `hUmap` to turn the literal divisor into `u.map g`).
  rw [← hg_def, hUmap]
  -- `hmap : map g (X^n %ₘ u) = map g (X^n) %ₘ map g u = X^n %ₘ u.map g`
  -- (`map g (X^n) = X^n` since `g` is a ring hom fixing `X`-powers under `map`).
  have hmap := Polynomial.map_modByMonic g huMonic (p := (X ^ n : Polynomial (F p)))
  rw [show (X ^ n : Polynomial (F p)).map g = (X ^ n : Polynomial (K2 p c0 c1 c2 c3 c4)) by
    rw [hg_def]; simp [Polynomial.map_pow, Polynomial.map_X]] at hmap
  rw [← hmap]
  have hbase : (X ^ n : Polynomial (F p)) %ₘ u =
      C (xmodUTable p u0 u1 n).1 + C (xmodUTable p u0 u1 n).2 * X := by
    rw [hu_def]; exact xmodUTable_correct p u0 u1 n
  have hbaseMapped := congrArg (Polynomial.map g) hbase
  rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C,
    Polynomial.map_X] at hbaseMapped
  exact hbaseMapped

/-- **The five-slot defining identity for the mod-`u` rows**, `a = 0`
giving row 2 (the `.1`/`x^0`-coefficient row), `a = 1` giving row 3 (the
`.2`/`x^1`-coefficient row) — the exact analogue of `anchor_defining_eq_aux`
but for the two `reduceMonomialModU` rows instead of the two anchor rows.
Same five steps: Cramer's rule at row `2+a.val`, divide by `A.det`, unfold
via `matrixA_row23_eval`/`rhsVec_row23_eval`, reindex `Fin 4 → Fin 5` via
`sum_otherIdx_add_y`, split the resulting 5-slot sum by `bj` to land on
`Epoly`/`Ypoly`'s own coefficient-sum shape (via `reduceMonomialModU`'s own
`bj`-split definition, matching `Epoly`/`Ypoly`'s `if bj = 0/1 then ...`
sums termwise). -/
private lemma row23_defining_eq_aux (hA : MatrixNondegenerate p c0 c1 c2 c3 c4 u0 u1 v0 v1)
    (a : Fin 2) :
    (∑ bidx : Fin 5,
      let (_, bi, bj) := rrBasis5.getD bidx.val (0, 0, 0)
      coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 bidx *
        algebraMap (F p) (K2 p c0 c1 c2 c3 c4)
          (let (r0, r1) := reduceMonomialModU p u0 u1 v0 v1 bi bj
           if a.val = 0 then r0 else r1)) = 0 := by
  set A := matrixA p c0 c1 c2 c3 c4 u0 u1 v0 v1 with hA_def
  set rhs := rhsVec p c0 c1 c2 c3 c4 u0 u1 v0 v1 with hrhs_def
  have hdet : A.det ≠ 0 := hA
  have haRow : 2 + a.val < 4 := by omega
  -- Step 1: Cramer's rule at row `⟨2+a.val,_⟩`.
  have hmul := Matrix.mulVec_cramer A rhs
  have hrow := congrFun hmul (⟨2 + a.val, haRow⟩ : Fin 4)
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hrow
  -- Step 2: divide by `A.det ≠ 0`.
  have hrow' : ∑ col : Fin 4, A ⟨2 + a.val, haRow⟩ col *
      (A.cramer rhs col / A.det) = rhs ⟨2 + a.val, haRow⟩ := by
    have hstep : (∑ col : Fin 4, A ⟨2 + a.val, haRow⟩ col * (A.cramer rhs col / A.det)) * A.det =
        rhs ⟨2 + a.val, haRow⟩ * A.det := by
      rw [Finset.sum_mul]
      have : ∀ col : Fin 4, A ⟨2 + a.val, haRow⟩ col * (A.cramer rhs col / A.det) * A.det =
          A ⟨2 + a.val, haRow⟩ col * A.cramer rhs col := by
        intro col; field_simp
      simp only [this]
      rw [hrow]; ring
    exact mul_right_cancel₀ hdet hstep
  have hcramerSolution : ∀ col : Fin 4, A.cramer rhs col / A.det =
      cramerSolution p c0 c1 c2 c3 c4 u0 u1 v0 v1 col := fun col => rfl
  simp only [hcramerSolution] at hrow'
  -- Step 3: unfold both sides via the row-23 unfolding lemmas.
  have hApply : ∀ col : Fin 4, A ⟨2 + a.val, haRow⟩ col =
      let (_, bi, bj) := rrBasis5.getD (otherIdx.getD col.val 0) (0, 0, 0)
      let (r0, r1) := reduceMonomialModU p u0 u1 v0 v1 bi bj
      algebraMap (F p) (K2 p c0 c1 c2 c3 c4) (if a.val = 0 then r0 else r1) := fun col =>
    matrixA_row23_eval p c0 c1 c2 c3 c4 u0 u1 v0 v1 a col
  have hrhsApply : rhs ⟨2 + a.val, haRow⟩ =
      let (_, bi_n, bj_n) := rrBasis5.getD yIdx (0, 1, 1)
      let (rn0, rn1) := reduceMonomialModU p u0 u1 v0 v1 bi_n bj_n
      (-algebraMap (F p) (K2 p c0 c1 c2 c3 c4) (if a.val = 0 then rn0 else rn1)) := by
    show rhsVec p c0 c1 c2 c3 c4 u0 u1 v0 v1 ⟨2 + a.val, haRow⟩ = _
    exact rhsVec_row23_eval p c0 c1 c2 c3 c4 u0 u1 v0 v1 a
  clear_value A rhs
  rw [hrhsApply] at hrow'
  -- Move the RHS term to the left, recovering the 5-term additive identity.
  have hmoved : (∑ col : Fin 4, coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 (otherMap col) *
      (let (_, bi, bj) := rrBasis5.getD (otherIdx.getD col.val 0) (0, 0, 0)
       let (r0, r1) := reduceMonomialModU p u0 u1 v0 v1 bi bj
       algebraMap (F p) (K2 p c0 c1 c2 c3 c4) (if a.val = 0 then r0 else r1))) +
      coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 ⟨yIdx, yIdx_lt_five⟩ *
        (let (_, bi_n, bj_n) := rrBasis5.getD yIdx (0, 1, 1)
         let (rn0, rn1) := reduceMonomialModU p u0 u1 v0 v1 bi_n bj_n
         algebraMap (F p) (K2 p c0 c1 c2 c3 c4) (if a.val = 0 then rn0 else rn1)) = 0 := by
    have hcoeffsOutY : coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 ⟨yIdx, yIdx_lt_five⟩ = 1 := by
      unfold coeffsOut; rw [dif_pos rfl]
    rw [hcoeffsOutY, one_mul]
    have hstep : ∑ col : Fin 4, coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 (otherMap col) *
        (let (_, bi, bj) := rrBasis5.getD (otherIdx.getD col.val 0) (0, 0, 0)
         let (r0, r1) := reduceMonomialModU p u0 u1 v0 v1 bi bj
         algebraMap (F p) (K2 p c0 c1 c2 c3 c4) (if a.val = 0 then r0 else r1)) =
        ∑ col : Fin 4, cramerSolution p c0 c1 c2 c3 c4 u0 u1 v0 v1 col *
        (let (_, bi, bj) := rrBasis5.getD (otherIdx.getD col.val 0) (0, 0, 0)
         let (r0, r1) := reduceMonomialModU p u0 u1 v0 v1 bi bj
         algebraMap (F p) (K2 p c0 c1 c2 c3 c4) (if a.val = 0 then r0 else r1)) := by
      apply Finset.sum_congr rfl
      intro col _
      rw [coeffsOut_otherMap p c0 c1 c2 c3 c4 u0 u1 v0 v1 col]
    have horder : (∑ col : Fin 4, cramerSolution p c0 c1 c2 c3 c4 u0 u1 v0 v1 col *
          (let (_, bi, bj) := rrBasis5.getD (otherIdx.getD col.val 0) (0, 0, 0)
           let (r0, r1) := reduceMonomialModU p u0 u1 v0 v1 bi bj
           algebraMap (F p) (K2 p c0 c1 c2 c3 c4) (if a.val = 0 then r0 else r1)))
        = ∑ col : Fin 4, A ⟨2 + a.val, haRow⟩ col *
            cramerSolution p c0 c1 c2 c3 c4 u0 u1 v0 v1 col := by
      apply Finset.sum_congr rfl
      intro col _
      rw [mul_comm (cramerSolution p c0 c1 c2 c3 c4 u0 u1 v0 v1 col), hApply col]
    rw [hstep, horder, hrow']
    exact neg_add_cancel _
  -- Step 4: reindex `Fin 4 → Fin 5` via `sum_otherIdx_add_y`.
  -- `let` + `clear_value` (not `set`), named `Fsum` (not `F`): `F` is
  -- already this file's ambient base-field notation (`F p = ZMod p`), and a
  -- `let`-bound local of the same name self-shadows *inside its own body*
  -- (every `F p` inside the value being defined would resolve to the
  -- not-yet-fully-bound local `F : Fin 5 → K2 ...` instead of the ambient
  -- `F p`) — `set`/`have` don't hit this because they fully elaborate the
  -- RHS before binding the name, but `let` does not. Renaming avoids the
  -- collision. `clear_value` is also split into three steps here (`let` /
  -- `have ... := rfl` / `clear_value`) rather than hand-retyping the
  -- destructured body for `clear_value`'s inline binder, since the
  -- elaborated body contains a `match` from the `let (_, bi, bj) := ...`
  -- pattern that doesn't syntactically match a hand-written copy.
  let Fsum : Fin 5 → K2 p c0 c1 c2 c3 c4 := fun bidx =>
    coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 bidx *
      (let (_, bi, bj) := rrBasis5.getD bidx.val (0, 0, 0)
       algebraMap (F p) (K2 p c0 c1 c2 c3 c4)
         (let (r0, r1) := reduceMonomialModU p u0 u1 v0 v1 bi bj
          if a.val = 0 then r0 else r1))
  have hF_def : Fsum = fun bidx =>
      coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 bidx *
        (let (_, bi, bj) := rrBasis5.getD bidx.val (0, 0, 0)
         algebraMap (F p) (K2 p c0 c1 c2 c3 c4)
           (let (r0, r1) := reduceMonomialModU p u0 u1 v0 v1 bi bj
            if a.val = 0 then r0 else r1)) := rfl
  clear_value Fsum
  have hFcol : ∀ col : Fin 4, Fsum (otherMap col) =
      coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 (otherMap col) *
      (let (_, bi, bj) := rrBasis5.getD (otherIdx.getD col.val 0) (0, 0, 0)
       let (r0, r1) := reduceMonomialModU p u0 u1 v0 v1 bi bj
       algebraMap (F p) (K2 p c0 c1 c2 c3 c4) (if a.val = 0 then r0 else r1)) := by
    intro col
    -- `Fsum (otherMap col)` unfolds (via `hF_def`, a syntactic rewrite — not
    -- a defeq check through `K2`'s `abbrev` chain) to the same product with
    -- `bidx := otherMap col`; the only remaining gap is the *index*
    -- `(otherMap col).val = otherIdx.getD col.val 0`, an `Fin`/`ℕ`-level
    -- fact with no `K2` in it. Establishing that separately (`hidx`) and
    -- rewriting only at the index avoids asking `rfl`/`whnf` to walk the
    -- `K2`-typed `algebraMap` subterm, which is what caused the original
    -- whole-term `change ... ; rfl` to time out (forced full unfolding
    -- through the reducible `K2`/`AdjoinRoot`/`FractionRing` abbrev stack).
    have hidx : (otherMap col).val = otherIdx.getD col.val 0 := rfl
    simp only [hF_def, hidx]
  have hFy : Fsum (⟨yIdx, yIdx_lt_five⟩ : Fin 5) =
      coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 ⟨yIdx, yIdx_lt_five⟩ *
      (let (_, bi_n, bj_n) := rrBasis5.getD yIdx (0, 1, 1)
       let (rn0, rn1) := reduceMonomialModU p u0 u1 v0 v1 bi_n bj_n
       algebraMap (F p) (K2 p c0 c1 c2 c3 c4) (if a.val = 0 then rn0 else rn1)) := by
    have hy_len : yIdx < rrBasis5.length := by
      have hlen : rrBasis5.length = 5 := by
        simp [rrBasis5, rrBasisCandidates, List.length_flatMap]
      rw [hlen]; exact yIdx_lt_five
    have hy_get : rrBasis5.getD yIdx (0, 0, 0) = rrBasis5.getD yIdx (0, 1, 1) := by
      rw [List.getD_eq_getElem _ _ hy_len, List.getD_eq_getElem _ _ hy_len]
    simp only [hF_def, hy_get]
  have hsum5 : (∑ col : Fin 4, Fsum (otherMap col)) + Fsum ⟨yIdx, yIdx_lt_five⟩ =
      ∑ bidx : Fin 5, Fsum bidx := sum_otherIdx_add_y p c0 c1 c2 c3 c4 Fsum
  have hmoved' : (∑ col : Fin 4, Fsum (otherMap col)) + Fsum ⟨yIdx, yIdx_lt_five⟩ = 0 := by
    calc
      (∑ col : Fin 4, Fsum (otherMap col)) + Fsum ⟨yIdx, yIdx_lt_five⟩ =
          (∑ col : Fin 4, coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 (otherMap col) *
            (let (_, bi, bj) := rrBasis5.getD (otherIdx.getD col.val 0) (0, 0, 0)
             let (r0, r1) := reduceMonomialModU p u0 u1 v0 v1 bi bj
             algebraMap (F p) (K2 p c0 c1 c2 c3 c4) (if a.val = 0 then r0 else r1))) +
            coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 ⟨yIdx, yIdx_lt_five⟩ *
              (let (_, bi_n, bj_n) := rrBasis5.getD yIdx (0, 1, 1)
               let (rn0, rn1) := reduceMonomialModU p u0 u1 v0 v1 bi_n bj_n
               algebraMap (F p) (K2 p c0 c1 c2 c3 c4) (if a.val = 0 then rn0 else rn1)) := by
            rw [Finset.sum_congr rfl (fun col _ => hFcol col), hFy]
      _ = 0 := hmoved
  have hsum5' : ∑ bidx : Fin 5, Fsum bidx = 0 := hsum5 ▸ hmoved'
  -- The theorem's goal is stated directly via the `let`-match body (not
  -- through `Fsum`, which is opaque post-`clear_value`), so unfold
  -- pointwise via `hF_def` before closing.
  rw [hF_def] at hsum5'
  exact hsum5'

set_option maxHeartbeats 20000000
/-- **The mod-`u` congruence, assembled**: `(E(x) + Y(x)*(v1*X+v0)) %ₘ u(x)
= 0`, i.e. `u(x) ∣ E(x) + Y(x)*(v1*X+v0)`, obtained from `row23_defining_eq_aux`
by identifying its two coefficient sums (`a=0`,`a=1`) with the two
coefficients of `(E + Y*(v1 X+v0)) %ₘ u` via `xmodUTable_correct` (lifted to
`K2` by `Polynomial.map_modByMonic`/`Monic.map`) and `reduceMonomialModU`'s
own `j=0`/`j=1` split (`j=0`: `X^bi mod u`'s own coefficients, matching
`E`'s `bj=0` terms; `j=1`: `(v0+v1 X) * X^bi mod u`'s coefficients — since
`reduceMonomialModU`'s `j=1` branch computes `v0 * xmodUTable(bi) + v1 *
xmodUTable(bi+1)`, which is exactly `(v0 + v1*X) * X^bi mod u` by linearity
of `%ₘ` and `xmodUTable_correct` at both `bi` and `bi+1`, matching `Y`'s
`bj=1` terms multiplied by `(v1 X+v0)`). -/
theorem dvd_E_add_Y_mul_v (hA : MatrixNondegenerate p c0 c1 c2 c3 c4 u0 u1 v0 v1) :
    (X ^ 2 + C (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u1) * X +
        C (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u0)) ∣
      (Epoly p c0 c1 c2 c3 c4 u0 u1 v0 v1 +
        Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1 *
          (C (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) v1) * X +
            C (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) v0))) := by
  set K := K2 p c0 c1 c2 c3 c4 with hK_def
  -- `let` + `clear_value` (not `set`) for `g`/`u`/`U`: per this file's
  -- diagnosed fix elsewhere (`xmodUTable_correct_K`, `dvd_N_u`), `set`
  -- performs an expensive goal-wide occurrence search/replace against
  -- `K2`-typed terms. `let` binds cheaply and `clear_value` makes each name
  -- opaque, keeping only the defining equation available to `rw` in at the
  -- points that need it. Since (unlike `set`) this does NOT rewrite the
  -- goal automatically, the goal is folded back to `g`/`U`-form explicitly
  -- via `← hg_def`/`← hU_def` right before it's needed.
  let g : F p →+* K := algebraMap (F p) K
  clear_value (hg_def : g = algebraMap (F p) K)
  let u : Polynomial (F p) := X ^ 2 + C u1 * X + C u0
  clear_value (hu_def : u = X ^ 2 + C u1 * X + C u0)
  let U : Polynomial K := X ^ 2 + C (g u1) * X + C (g u0)
  clear_value (hU_def : U = X ^ 2 + C (g u1) * X + C (g u0))
  have hUmap : U = u.map g := by
    rw [hU_def, hu_def]
    simp [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C,
      Polynomial.map_X]
  have huMonic : u.Monic := by rw [hu_def]; exact uPoly_monic p u0 u1
  have hUMonic : U.Monic := hUmap ▸ huMonic.map g
  rw [← hg_def, ← hU_def]
  rw [← Polynomial.modByMonic_eq_zero_iff_dvd hUMonic]
  -- The target sum `R := E + Y*(v1X+v0)`. Its coefficients 0,1 are exactly
  -- `row23_defining_eq_aux`'s two sums (`a=0`,`a=1`); its higher coefficients
  -- vanish since `%ₘ U` has degree `< 2`, by `degree_modByMonic_lt`.
  set R : Polynomial K := Epoly p c0 c1 c2 c3 c4 u0 u1 v0 v1 +
      Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1 *
        (C (g v1) * X + C (g v0)) with hR_def
  -- `R` rewritten as a single sum over `bidx : Fin 5`, one term per basis
  -- slot, matching `Epoly`/`Ypoly`'s own `∑ bidx, if bj = 0/1 then ... else 0`
  -- definitions merged together with the `(v1 X + v0)` factor distributed in.
  have hRsum : R = ∑ bidx : Fin 5,
      let (_, bi, bj) := rrBasis5.getD bidx.val (0, 0, 0)
      if bj = 0 then C (coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 bidx) * X ^ bi
      else C (coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 bidx) * X ^ bi * (C (g v1) * X + C (g v0)) := by
    rw [hR_def]
    unfold Epoly Ypoly
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro bidx _
    have hbj0or1 : (rrBasis5.getD bidx.val (0, 0, 0)).2.2 = 0 ∨
        (rrBasis5.getD bidx.val (0, 0, 0)).2.2 = 1 := by
      have hlen : rrBasis5.length = 5 := by
        simp [rrBasis5, rrBasisCandidates, List.length_flatMap]
      have hlt : bidx.val < rrBasis5.length := by rw [hlen]; exact bidx.isLt
      rw [List.getD_eq_getElem _ _ hlt]
      exact rrBasis5_flag _ (List.getElem_mem hlt)
    rcases hbj0or1 with hb0 | hb1
    · have hb1' : (rrBasis5.getD bidx.val (0, 0, 0)).2.2 ≠ 1 := by omega
      simp only [if_pos hb0, if_neg hb1']
      ring
    · have hb0' : (rrBasis5.getD bidx.val (0, 0, 0)).2.2 ≠ 0 := by omega
      simp only [if_neg hb0', if_pos hb1]
      ring
  -- `%ₘ U` is `K`-linear (`Polynomial.modByMonicHom`), so distributes over
  -- the 5-term sum via `map_sum` (the general `AddMonoidHomClass` lemma
  -- `g (∑ x ∈ s, f x) = ∑ x ∈ s, g (f x)`, applied to `g := U.modByMonicHom`).
  have hRmod : R %ₘ U = ∑ bidx : Fin 5,
      (let (_, bi, bj) := rrBasis5.getD bidx.val (0, 0, 0)
       if bj = 0 then C (coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 bidx) * X ^ bi
       else C (coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 bidx) * X ^ bi *
         (C (g v1) * X + C (g v0))) %ₘ U := by
    rw [hRsum, ← Polynomial.modByMonicHom_apply,
      map_sum U.modByMonicHom
        (fun bidx : Fin 5 =>
          let (_, bi, bj) := rrBasis5.getD bidx.val (0, 0, 0)
          if bj = 0 then C (coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 bidx) * X ^ bi
          else C (coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 bidx) * X ^ bi *
            (C (g v1) * X + C (g v0)))
        Finset.univ]
    simp only [Polynomial.modByMonicHom_apply]
  -- Each term's `%ₘ U`, computed via `xmodUTable_correct_K`, is exactly what
  -- `reduceMonomialModU` returns (`j=0`: `X^bi %ₘ U`'s coefficients; `j=1`:
  -- `v0*xmodUTable(bi) + v1*xmodUTable(bi+1)`, matching `(v0+v1X)*X^bi %ₘ U`
  -- via `X^(bi+1) = X * X^bi` and `%ₘ U`'s `K`-linearity/multiplicativity).
  -- Shared smul-fact, synthesized ONCE against the `set`-opaque `K` rather
  -- than fresh inside each of `hterm`'s two branches: `Polynomial.smul_eq_C_mul`
  -- needs `Module K K[X]`/`DistribSMul K K[X]`, and synthesizing that against
  -- `K2 p c0 c1 c2 c3 c4` spelled out explicitly (as both branches' `hCterm`
  -- previously did in their type ascriptions) re-triggers the full triple-
  -- `AdjoinRoot` instance search at each site and blows the
  -- `synthInstance.maxHeartbeats` budget independently, one branch at a time.
  -- Stating it here once, against `K`, lets `set`'s opacity do its job: the
  -- instance is resolved once and both branches below reuse this term via
  -- `rw`/`simp only [hsmulC]` instead of re-invoking the lemma.
  have hsmulC : ∀ (c : K) (q : Polynomial K), c • q = C c * q := fun c q =>
    Polynomial.smul_eq_C_mul c
  have hterm : ∀ bidx : Fin 5, ∀ a : Fin 2,
      ((let (_, bi, bj) := rrBasis5.getD bidx.val (0, 0, 0)
        if bj = 0 then C (coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 bidx) * X ^ bi
        else C (coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 bidx) * X ^ bi *
          (C (g v1) * X + C (g v0))) %ₘ U).coeff a.val =
      coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 bidx *
        (let (_, bi, bj) := rrBasis5.getD bidx.val (0, 0, 0)
         g (let (r0, r1) := reduceMonomialModU p u0 u1 v0 v1 bi bj
            if a.val = 0 then r0 else r1)) := by
    intro bidx a
    -- NOT `set bi/bj/c := (rrBasis5.getD bidx.val (0,0,0)).2.1/.2.2/coeffsOut...`:
    -- the goal's own `let (_, bi, bj) := rrBasis5.getD bidx.val (0,0,0)`
    -- pattern-matches compile to a `match`/`Prod.rec` term, not literal
    -- `.2.1`/`.2.2` projections, so `set`'s syntactic occurrence search
    -- finds no match and falls back to an expensive whole-term `isDefEq`
    -- search — the same `match`-vs-hand-written-copy mismatch already
    -- diagnosed at `hFcol`/`hidx` above. `obtain` on the identical tuple
    -- expression instead lets `rcases`'s own match-compiler line up with
    -- the goal's compiled `match` structurally, which is cheap.
    have hbj0or1' : (rrBasis5.getD bidx.val (0, 0, 0)).2.2 = 0 ∨
        (rrBasis5.getD bidx.val (0, 0, 0)).2.2 = 1 := by
      have hlen : rrBasis5.length = 5 := by
        simp [rrBasis5, rrBasisCandidates, List.length_flatMap]
      have hlt : bidx.val < rrBasis5.length := by rw [hlen]; exact bidx.isLt
      rw [List.getD_eq_getElem _ _ hlt]
      exact rrBasis5_flag _ (List.getElem_mem hlt)
    -- `obtain`'s `cases` does NOT keep `bj` definitionally equal to the
    -- `.2.2` projection it replaced (attempting to `exact` `hbj0or1'`
    -- against a `bj`-phrased goal afterward fails outright) — so
    -- `hbj0or1'` must be `revert`ed *before* the `obtain`, letting the same
    -- case-split substitute consistently through both the goal and this
    -- fact, rather than trying to bridge them after the fact.
    revert hbj0or1'
    obtain ⟨_, bi, bj⟩ := rrBasis5.getD bidx.val (0, 0, 0)
    intro hbj0or1
    -- `obtain` on a bare term elaborates via `cases`, which leaves a
    -- residual `match (fst✝, bi, bj) with | (fst, bi, bj) => ...` wrapping
    -- the goal rather than substituting straight through. That `match` is
    -- applied to a literal constructor tuple, so it iota-reduces trivially
    -- — `dsimp only []` forces that reduction cheaply, restoring the goal
    -- to plain `if bj = 0 then _ else _` form for the `rw [if_pos/if_neg]`
    -- calls below.
    dsimp only [] at hbj0or1 ⊢
    -- NOT `set c := coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 bidx`: `set`
    -- elaborates its RHS as a fresh term before doing anything else, and
    -- that elaboration alone (against the large `K2` abbrev stack) is what
    -- timed out here — not the subsequent occurrence search. `generalize`
    -- instead abstracts the term as it already sits, pre-elaborated, in the
    -- goal, at whichever occurrences match syntactically. `generalize`'s own
    -- equation comes out reversed (`coeffsOut ... = c`) relative to `set`'s
    -- convention (`c = coeffsOut ...`), which downstream `simp [..., hc_def]`
    -- calls rely on — `.symm` restores it.
    generalize hc_def' : coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 bidx = c
    have hc_def := hc_def'.symm
    rcases hbj0or1 with hb0 | hb1
    · -- `j = 0`: term is `C c * X^bi`; `%ₘ` commutes with `C c *ₗ ·`
      -- (scalar multiplication, `modByMonicHom` is `K`-linear).
      have hCterm : (C c * X ^ bi : Polynomial K) = c • (X ^ bi) := by
        rw [hsmulC]
      rw [if_pos hb0]
      rw [hCterm, ← Polynomial.modByMonicHom_apply, map_smul, Polynomial.modByMonicHom_apply,
        hU_def, hg_def, xmodUTable_correct_K p c0 c1 c2 c3 c4 u0 u1 bi, ← hg_def]
      rw [hb0]
      simp only [reduceMonomialModU]
      -- `simp` (not `simp only`) previously timed out here: `simp`'s default
      -- set contains smul-normalization lemmas that unconditionally probe
      -- for a `Module`/`DistribSMul` instance whenever one is *available* on
      -- the ambient type, re-triggering the same expensive search against the
      -- raw triple-`AdjoinRoot` `K2`. `simp only` avoids that — but the goal
      -- genuinely still has a residual `•` (from `map_smul` above), so
      -- `hsmulC` (the pre-synthesized, `K`-typed smul fact) needs to be back
      -- in the explicit list to clear it, alongside the coeff lemmas.
      -- Residual goal (per REPL) had `X.coeff 0`/`X.coeff 1` left un-evaluated
      -- (`Polynomial.coeff_X_mul` was flagged unused: the goal shape here is
      -- `g (...) * X.coeff 0`, not `(g (...) * X).coeff 0`, so that lemma
      -- never matched). `Polynomial.coeff_X_zero`/`coeff_X_one` evaluate
      -- those directly to `1`/`0`; `mul_zero`/`add_zero` clean up the
      -- resulting arithmetic.
      -- `reduceIte` alone didn't discharge the `if 1 = 0 then _ else _` here
      -- (unlike the parallel spot in the `j=1` branch) — likely because this
      -- `1` descends from `a.val` post-`fin_cases` rather than being a bare
      -- numeral literal, so the simproc's pattern match doesn't fire on it.
      -- Supplying `if_neg (one_ne_zero (α := ℕ))` explicitly (same fact the
      -- `j=1` branch already uses via `rw` before its `fin_cases`) discharges
      -- it directly instead of relying on `reduceIte` to notice.
      fin_cases a <;> simp only [hsmulC, hc_def, Polynomial.coeff_add,
        Polynomial.coeff_C, Polynomial.coeff_C_mul, Polynomial.coeff_X_zero,
        Polynomial.coeff_X_one, reduceIte, if_neg (one_ne_zero (α := ℕ)),
        mul_zero, mul_one, add_zero, zero_add]
    · -- `j = 1`: term is `C c * X^bi * (C(g v1)*X + C(g v0))
      --         = C c * (C(g v1) * X^(bi+1) + C(g v0)*X^bi)`, so its `%ₘ U`
      -- is `C c • (C(g v1) * (X^(bi+1) %ₘ U) + C(g v0) * (X^bi %ₘ U))` by
      -- linearity, computed via `xmodUTable_correct_K` at `bi` and `bi+1`.
      have hCterm : (C c * X ^ bi * (C (g v1) * X + C (g v0)) :
          Polynomial K) =
          c • (g v1 • (X ^ (1 + bi)) + g v0 • (X ^ bi)) := by
        -- Stated with the exponent as `1 + bi`, not `bi + 1`: downstream,
        -- once this equation is `simp`-rewritten into the goal via
        -- `map_smul`/`Polynomial.modByMonicHom_apply` (below), Lean's own
        -- default `Nat`-addition normal form resurfaces the exponent as
        -- `1 + bi` regardless of which form is written here — `xmodUTable_
        -- correct_K` then has to be invoked at the matching `1 + bi` form to
        -- actually fire (previously invoked at `bi + 1`, which silently
        -- failed to match and left the goal in raw `%ₘ` form — diagnosed
        -- from `simp`'s "unused simp argument" warning on that call, not
        -- from a timeout or outright error). Matching the statement here to
        -- that same normal form up front avoids the mismatch entirely
        -- instead of trying to force a re-flip back to `bi + 1` afterward.
        -- Chained `rw [hsmulC, hsmulC, hsmulC]` timed out here: each `rw`
        -- re-unifies `hsmulC`'s instance argument against that specific
        -- occurrence's (defeq but not syntactically identical) instance path,
        -- and that unification cost — not fresh synthesis — is what
        -- re-accumulates across three separate `rw` calls. `simp only` keys
        -- off the head symbol once and rewrites all matching occurrences in
        -- a single pass, which is far cheaper here.
        -- `rw [pow_succ]` here also timed out for the same defeq-unification
        -- reason as the `rw [hsmulC, ...]` chain above: constructing the
        -- rewrite motive forces Lean to check defeq against the ambient
        -- fully-unfolded `K2` polynomial-ring instance stack. `ring` handles
        -- the `X ^ (bi + 1) = X ^ bi * X` exponent shift internally without
        -- needing a standalone motive, so it can absorb this step directly.
        simp only [hsmulC]
        ring
      have hb0' : bj ≠ 0 := by omega
      rw [if_neg hb0']
      -- This chained `rw` (7 lemmas back-to-back) hit the same wall as
      -- `hCterm`'s: each successive `rw`, especially `map_smul` (which needs
      -- `RingHom`/`SMul` structure unified against `K`/`K[X]`), re-checks its
      -- motive against the unfolded `K2` instance stack. `simp only` with the
      -- identical lemma set iterates to a fixed point in one pass instead of
      -- re-deriving a fresh motive per lemma. Split into several calls
      -- because the original `rw` used `Polynomial.modByMonicHom_apply` in
      -- BOTH directions (once backward, then forward), and `hg_def` in both
      -- directions too (forward to unfold `g` so `xmodUTable_correct_K`'s
      -- pattern matches, then backward to refold) — mixing opposite
      -- directions of the same lemma in a single `simp only` set risks a
      -- non-terminating rewrite loop between them, so each direction gets
      -- its own pass, in the same order the original `rw` chain used them.
      simp only [hCterm, ← Polynomial.modByMonicHom_apply, map_smul, map_add, map_smul,
        map_smul]
      -- Ground truth from the REPL: at this point the goal has
      -- `(...).modByMonicHom (X ^ (1+bi))`/`(...).modByMonicHom (X ^ bi)` —
      -- the *bundled-hom-application* form, not bare `%ₘ` notation, because
      -- the `← Polynomial.modByMonicHom_apply` rewrite two steps above
      -- converted every `%ₘ` occurrence to this form so `map_smul` could
      -- fire through the module hom. `U` itself is still the opaque local,
      -- never unfolded to `X^2 + C (g u1) * X + C (g u0)` (let alone
      -- further to `algebraMap`/`K2` form) by anything above.
      -- `xmodUTable_correct_K`'s stated pattern is `X^n %ₘ (X^2 + C
      -- (algebraMap (F p) (K2 ...) u1) * X + C (algebraMap (F p) (K2 ...)
      -- u0))` — bare `%ₘ`, so `Polynomial.modByMonicHom_apply` (forward
      -- this time) has to turn the two `.modByMonicHom` applications back
      -- into `%ₘ` form first. `hUalg` states the divisor equality for `U`
      -- (fully unfolded through `U → g,u0,u1-form → algebraMap-form →
      -- K2-form`) as its own fact, so `rw [hUalg]` retargets only the two
      -- (now-`%ₘ`-form) `U` occurrences to the fully-unfolded divisor —
      -- leaving every other `g v1 •`/`g v0 •`/RHS `g (if ...)` occurrence
      -- in the goal untouched, unlike a blanket `rw [hg_def]`/`hK_def` on
      -- the whole (or even just LHS-restricted) goal, which would also
      -- rewrite those and break the closing `ring`/`hgadd`/`hgmul` steps
      -- below that expect to still see plain `g` applications there.
      have hUalg : U = X ^ 2 +
          C (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u1) * X +
          C (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u0) := by
        -- NOT `rw [hU_def, hg_def, hK_def]`: `hK_def : K = K2 p c0 c1 c2
        -- c3 c4` rewrites the *type* `K` itself, and since `K` was
        -- introduced via `set` (so it's a local `let`-bound abbreviation,
        -- not an opaque variable), the rewrite has to abstract a motive
        -- over the type argument `_a` in `algebraMap (F p) _a`, which drags
        -- along the (type-dependent) `Field`/instance arguments elaborated
        -- concretely against `K`'s own unfolding — exactly the "motive is
        -- not type correct" failure. Since `hK_def` came from `set`, `K`
        -- and `K2 p c0 c1 c2 c3 c4` are already definitionally equal, so
        -- once `hU_def`/`hg_def` are unfolded the two sides agree by `rfl`
        -- with no further rewriting of the type needed.
        rw [hU_def, hg_def]
      rw [Polynomial.modByMonicHom_apply, Polynomial.modByMonicHom_apply, hUalg]
      rw [xmodUTable_correct_K p c0 c1 c2 c3 c4 u0 u1 (1 + bi),
        xmodUTable_correct_K p c0 c1 c2 c3 c4 u0 u1 bi]
      rw [hb1]
      simp only [reduceMonomialModU, if_neg (one_ne_zero (α := ℕ))]
      -- Mirrors the `j=0` branch's closing tactic, but also needs
      -- `mul_add`/`mul_assoc`: `j=0`'s `c • X^bi` was always a single smul
      -- term, but here `hCterm`'s RHS is `c • (term1 + term2)`, so once
      -- `hsmulC` turns the outer `•` into `C c * (term1 + term2)`, `mul_add`
      -- has to distribute that product across the sum before the coeff
      -- lemmas can see `term1`/`term2` separately; `Polynomial.coeff_add`
      -- then splits the `.coeff` across that distributed sum.
      -- After that, the LHS is `c * (g v1 * g b) + c * (g v0 * g a)`
      -- (`a := (xmodUTable bi).val`, `b := (xmodUTable (bi+1)).val`, for
      -- `val ∈ {1,2}` matching `a.val = 0`/`a.val = 1`) while the RHS is
      -- still `c * g (v0 * a + v1 * b)`: `g` needs to be pushed through the
      -- addition/multiplication to expose the same four factors, and only
      -- then does the goal become a pure commutative-ring rearrangement that
      -- `ring` can close. NOT the generic `map_add`/`map_mul` simp lemmas:
      -- Mathlib's own docs on this lemma family warn that seeing `⇑f x`
      -- triggers a search for an `AddHomClass`/`MulHomClass` (really
      -- `RingHomClass`) instance on `g`'s *type*, and against the unfolded
      -- `K2` abbrev stack that search is exactly the kind of expensive/
      -- silently-failing lookup this file has hit before (`simp` reports
      -- them "unused" rather than timing out, since it can fall back to not
      -- using them, but either way they don't fire). `hgadd`/`hgmul` below
      -- state the identical facts as plain equalities about `g`'s coercion,
      -- proved by `map_add`/`map_mul` applied as ordinary *terms* (not simp
      -- lemmas): as terms, elaboration unifies `g`'s already-known concrete
      -- type `F p →+* K` against `map_add`/`map_mul`'s expected `HomClass`
      -- argument directly, which is a single instance lookup against a
      -- *fixed, non-`K`-dependent* type (`RingHom.instRingHomClass` for
      -- `F p →+* K` as a whole) — cheap, unlike `simp`'s discrimination-tree
      -- probing of every `⇑f x` subterm in the goal against `K`'s unfolded
      -- structure, which is what actually blew up above. If `g.map_add'`/
      -- `g.map_mul'` (the raw structure-field route) resolve faster in the
      -- REPL, those are the fallback: `g`'s fields are set at `g`'s
      -- definition, independent of any instance search either way.
      have hgadd : ∀ x y : F p, g (x + y) = g x + g y := fun x y => map_add g x y
      have hgmul : ∀ x y : F p, g (x * y) = g x * g y := fun x y => map_mul g x y
      -- `reduceMonomialModU`'s unfold (just above) computes `xmodUTable p
      -- u0 u1 (1 + bi)` — its own `i + 1` clause resurfaces as `1 + bi`
      -- under `simp`'s default `Nat`-addition normal form, matching
      -- `hCterm`'s statement (also written as `1 + bi` above, for the same
      -- reason) and `xmodUTable_correct_K`'s invocation earlier in this
      -- branch — all three now agree, so no further exponent-form
      -- reconciliation is needed here.
      -- `mul_assoc` dropped (flagged unused): with `g v1 •`/`g v0 •` now
      -- fully expanded via `hgadd`/`hgmul`, both sides are already flat
      -- sums of one product per term, so there's no nested `(a*b)*c` left
      -- for `mul_assoc` to reassociate before `ring` takes over.
      -- `← hg_def` (tried in place of `hgK1`/`hgK2` below) did NOT fire,
      -- flagged unused by the linter: `simp`'s discrimination tree matches
      -- syntactically before attempting defeq, and `hg_def`'s LHS pattern
      -- (reversed) is `algebraMap (F p) K _` — with `K` a bare local
      -- constant — while the goal has `algebraMap (F p) (K2 p c0 c1 c2 c3
      -- c4) _`, an application. Those never even get compared up to defeq
      -- by simp's indexing, despite being defeq (`K` unfolds to exactly
      -- that application, since it came from `set`). `hgK1`/`hgK2` instead
      -- state the needed bridge as concrete `have`s, each proved by a
      -- one-shot `rw [hg_def]` where the goal is small enough that the
      -- defeq check between `K` and `K2 p c0 c1 c2 c3 c4` (needed for `rw`'s
      -- trailing `rfl`) is cheap, rather than asking `simp` to discover the
      -- same defeq while pattern-matching across the whole goal.
      have hgK1 : g (xmodUTable p u0 u1 (1 + bi)).1 =
          algebraMap (F p) (K2 p c0 c1 c2 c3 c4) (xmodUTable p u0 u1 (1 + bi)).1 := by
        rw [hg_def]
      have hgK2 : g (xmodUTable p u0 u1 bi).1 =
          algebraMap (F p) (K2 p c0 c1 c2 c3 c4) (xmodUTable p u0 u1 bi).1 := by
        rw [hg_def]
      have hgK3 : g (xmodUTable p u0 u1 (1 + bi)).2 =
          algebraMap (F p) (K2 p c0 c1 c2 c3 c4) (xmodUTable p u0 u1 (1 + bi)).2 := by
        rw [hg_def]
      have hgK4 : g (xmodUTable p u0 u1 bi).2 =
          algebraMap (F p) (K2 p c0 c1 c2 c3 c4) (xmodUTable p u0 u1 bi).2 := by
        rw [hg_def]
      fin_cases a <;> simp only [hsmulC, hc_def, mul_add, Polynomial.coeff_add,
        Polynomial.coeff_C, Polynomial.coeff_C_mul, Polynomial.coeff_X_zero,
        Polynomial.coeff_X_one, reduceIte, if_neg (one_ne_zero (α := ℕ)),
        mul_zero, mul_one, add_zero, zero_add, hgadd, hgmul, ← hgK1, ← hgK2,
        ← hgK3, ← hgK4] <;> ring
  have hcoeff : ∀ a : Fin 2, (R %ₘ U).coeff a.val = 0 := by
    intro a
    have haux := row23_defining_eq_aux p c0 c1 c2 c3 c4 u0 u1 v0 v1 hA a
    rw [← hg_def] at haux
    rw [hRmod, Polynomial.finsetSum_coeff]
    rw [show (∑ bidx : Fin 5, ((let (_, bi, bj) := rrBasis5.getD bidx.val (0, 0, 0)
        if bj = 0 then C (coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 bidx) * X ^ bi
        else C (coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 bidx) * X ^ bi *
          (C (g v1) * X + C (g v0))) %ₘ U).coeff a.val) =
        ∑ bidx : Fin 5, coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 bidx *
          (let (_, bi, bj) := rrBasis5.getD bidx.val (0, 0, 0)
           g (let (r0, r1) := reduceMonomialModU p u0 u1 v0 v1 bi bj
              if a.val = 0 then r0 else r1)) from
      Finset.sum_congr rfl (fun bidx _ => hterm bidx a)]
    exact haux
  have hdeg : (R %ₘ U).degree < U.degree := Polynomial.degree_modByMonic_lt R hUMonic
  have hUdeg : U.degree = (2 : ℕ) := by
    -- `compute_degree` needs the goal's head symbol to literally be
    -- `natDegree`/`degree`/`coeff` — going through `degree_eq_natDegree`
    -- first left the goal as a cast-equality (`↑U.natDegree = ↑2`) wrapped
    -- around an `Eq`, which isn't that shape. `compute_degree` handles
    -- `degree` goals directly, so unfold `U` and call it straight away.
    rw [hU_def]
    compute_degree!
  apply Polynomial.ext
  intro n
  match n with
  | 0 => simpa using hcoeff ⟨0, by norm_num⟩
  | 1 => simpa using hcoeff ⟨1, by norm_num⟩
  | (n + 2) =>
      apply Polynomial.coeff_eq_zero_of_degree_lt
      rw [hUdeg] at hdeg
      exact lt_of_lt_of_le hdeg (by
        -- `norm_num` alone left a residual rather than closing
        -- `(2 : WithBot ℕ) ≤ ↑(n + 2)` outright. `Nat.le_add_left 2 n : 2 ≤
        -- n + 2` is the underlying `ℕ` fact; `exact_mod_cast` bridges it
        -- across the `WithBot ℕ` coercion without needing a `WithBot`-
        -- specific lemma name.
        exact_mod_cast Nat.le_add_left 2 n)

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
**Fully proved, no `sorry`**: isolated as its own lemma so the two
`w*_sq_eq` steps above (also fully proved) stay visibly separate from this
eval/algebraMap-compatibility piece. -/
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

/-- **The target Mumford hypothesis**: `v(x) = v1*X + v0` squares to `f(x)`
modulo the target `u(x) = X²+u1 X+u0` — the geometric condition making
`(u,v)` an actual Mumford representative, distinct from `vRS_sq_eq_f_mod_uRS`
(`DataDerivationMumford.lean`, which is the analogous fact about the
COMPUTED `v_RS`, not the target `v` here). Not derived from anything else in
this file — it is a hypothesis on the sample data `(u0,u1,v0,v1)`, supplied
by whatever upstream construction produces a genuine Mumford pair (flagged
in the previous pass's docstring as needing sourcing against
`00_sample_specs.jl`; threaded here as an explicit named hypothesis per this
project's convention of not folding genericity/side conditions away). -/
def IsMumfordTarget (c0 c1 c2 c3 c4 u0 u1 v0 v1 : F p) : Prop :=
  (X ^ 2 + C (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u1) * X +
      C (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u0)) ∣
    ((C (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) v1) * X +
        C (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) v0)) ^ 2 -
      fAtX p c0 c1 c2 c3 c4 u0 u1 v0 v1)

/-- `u(x) = X² + u1 X + u0` divides `N(x)`. Assembled from `dvd_E_add_Y_mul_v`
(`u ∣ E + Y*(v1X+v0)`, rows 2–3 of the linear system, this pass's new
result) and `IsMumfordTarget` (`u ∣ v² - f`, the target Mumford condition),
via the algebraic identity

    N = E² - f Y² = (E - Y v)(E + Y v) + (v² - f) Y²

(`v := v1 X + v0`, checked by `ring`): the first summand is divisible by `u`
since `u ∣ E + Yv` (given) times anything; the second is divisible by `u`
since `u ∣ v² - f` (given) times `Y²`. Sum of two multiples of `u` is a
multiple of `u`. -/
theorem dvd_N_u (hA : MatrixNondegenerate p c0 c1 c2 c3 c4 u0 u1 v0 v1)
    (hMumford : IsMumfordTarget p c0 c1 c2 c3 c4 u0 u1 v0 v1) :
    (X ^ 2 + C (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u1) * X +
        C (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u0)) ∣
      Npoly p c0 c1 c2 c3 c4 u0 u1 v0 v1 := by
  -- `let` + `clear_value` throughout (not `set`): six large `K2`-typed
  -- definitions were previously introduced via `set`, each performing a
  -- goal-wide occurrence search/replace — the diagnosed cost driver behind
  -- this theorem's timeout. `let` binds each name once; `clear_value` then
  -- makes it opaque to later defeq/`isDefEq` checks, keeping only the
  -- defining equation (`hg_def`/`hU_def`/etc.) available to `rw` in at the
  -- specific points that actually need to see through to the concrete
  -- value (`huY`, `hVF`, `hNeq`) — `dvd_mul_of_dvd_right/left`/`dvd_add`
  -- never need to unfold `U`/`E`/`Y`/`V`/`f` at all, so those steps now
  -- operate on opaque names throughout.
  let g : F p →+* K2 p c0 c1 c2 c3 c4 := algebraMap (F p) (K2 p c0 c1 c2 c3 c4)
  clear_value (hg_def : g = algebraMap (F p) (K2 p c0 c1 c2 c3 c4))
  let U : Polynomial (K2 p c0 c1 c2 c3 c4) := X ^ 2 + C (g u1) * X + C (g u0)
  clear_value (hU_def : U = X ^ 2 + C (g u1) * X + C (g u0))
  let E : Polynomial (K2 p c0 c1 c2 c3 c4) := Epoly p c0 c1 c2 c3 c4 u0 u1 v0 v1
  clear_value (hE_def : E = Epoly p c0 c1 c2 c3 c4 u0 u1 v0 v1)
  let Y : Polynomial (K2 p c0 c1 c2 c3 c4) := Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1
  clear_value (hY_def : Y = Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1)
  let V : Polynomial (K2 p c0 c1 c2 c3 c4) := C (g v1) * X + C (g v0)
  clear_value (hV_def : V = C (g v1) * X + C (g v0))
  let f : Polynomial (K2 p c0 c1 c2 c3 c4) := fAtX p c0 c1 c2 c3 c4 u0 u1 v0 v1
  clear_value (hf_def : f = fAtX p c0 c1 c2 c3 c4 u0 u1 v0 v1)
  have huY : U ∣ E + Y * V := by
    rw [hU_def, hE_def, hY_def, hV_def, hg_def]
    exact dvd_E_add_Y_mul_v p c0 c1 c2 c3 c4 u0 u1 v0 v1 hA
  have hVF : U ∣ V ^ 2 - f := by
    rw [hU_def, hV_def, hf_def, hg_def]
    exact hMumford
  have h1 : U ∣ (E - Y * V) * (E + Y * V) := dvd_mul_of_dvd_right huY (E - Y * V)
  have h2 : U ∣ (V ^ 2 - f) * Y ^ 2 := dvd_mul_of_dvd_left hVF (Y ^ 2)
  have hadd : U ∣ (E - Y * V) * (E + Y * V) + (V ^ 2 - f) * Y ^ 2 := dvd_add h1 h2
  have hNeq : Npoly p c0 c1 c2 c3 c4 u0 u1 v0 v1 =
      (E - Y * V) * (E + Y * V) + (V ^ 2 - f) * Y ^ 2 := by
    rw [hE_def, hY_def, hV_def, hf_def, hg_def]; unfold Npoly; ring
  -- The goal's divisor is stated literally (`X^2 + C(g u1)*X + C(g u0)`, from
  -- the theorem signature), not via the opaque name `U` — `rw [hNeq]` alone
  -- only rewrites the `Npoly` side, so the divisor also needs `← hU_def`
  -- (and `← hg_def`, since `hU_def`'s RHS is stated in terms of `g`) to line
  -- up with `hadd`, which is stated entirely in terms of `U`.
  rw [hNeq, ← hg_def, ← hU_def]
  exact hadd

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
