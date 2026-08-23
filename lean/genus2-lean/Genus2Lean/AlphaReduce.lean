import Mathlib
import Genus2Lean.TheDataDerivation.DataDerivationBasics

/-!
# `Reduce`: Mumford reduction of `alpha • a - P1 - P2` down to `(u0,u1,v0,v1)`

Per `ROADMAP-alpha-locus.md`'s revised Step 1 (this pass): `alpha • a` is
NOT computed here — it is precomputed offline by the caller (Claire,
directly: `a` is a genus-2 Mumford divisor, not a simple point, and
`alpha • a`'s own Jacobian scalar-multiplication is produced by whatever
Cantor/group-law code generates the DLP problem instance in the first
place, out of scope for this file) and handed in as its own Mumford pair
`(u_a, v_a) : F p × F p`. What THIS file builds is the K=4 case of
`phi_general.zip`'s general-`K` Mumford-reduction recipe
(`build_phi_general!`/`phi_residual_general!`,
`07_build_phi_general.jl`/`09_residual_and_modinv.jl`, read directly this
pass — not the earlier secondhand paraphrase): reduce the 4-point divisor
`(u_a,v_a)`'s two Mumford roots together with two concrete curve points
`P1,P2` down to a single Mumford pair `(u0,u1,v0,v1)`.

## Relationship to `DataDerivationSolve.lean`'s existing K=2 machinery

`DataDerivationSolve.lean`/`DataDerivationBasics.lean` already implement
EXACTLY this recipe for `K=2` (`matrixA`, `rhsVec`, `MatrixNondegenerate`,
`cramerSolution`, `coeffsOut`, `Epoly`, `Ypoly`, `Npoly`,
`curBeforeMonic`), but over the TOWER field `K2 p c0 c1 c2 c3 c4` (built
for exactly 2 SYMBOLIC curve-relation anchors `(t0 p 0, w1)`/`(t0 p 1,
w2)`, `DataDerivationTower.lean`). That machinery is the right template —
same linear-algebra shape, same `E,Y,N` construction, same exact-division
pattern — but is hardcoded to `Fin 4`/`Fin 5`/2 anchors and cannot be
reused directly for `K=4`. This file re-derives the same pattern for
`K=4`, `nb=7`, over PLAIN `F p` (no tower needed: our anchors — `P1`,
`P2`, and `(u_a,v_a)`'s own two roots — are concrete field elements, not
symbolic curve-relation variables, so there is no field-extension
adjunction to perform at all here, which is genuinely simpler than the
K=2 case).

**Reused unchanged from `DataDerivationBasics.lean`**: `rrBasisCandidates`
(generic in `maxOrder`, no K-specific hardcoding), `xmodUTable`/
`reduceMonomialModU` (depend only on the TARGET `(u0,u1,v0,v1)`, not on
`K` or the anchors at all — proved correct there, `xmodUTable_spec`,
reused here as-is), `curvePoly` (`f`, plain `F p`-valued, degree 5
unconditionally).

**New in this file**: `rrBasis7`, `yIdx7`/`otherIdx7`, a `Fin 4`-anchor
version of `matrixA`/`rhsVec` (`K=4` anchor rows instead of `K=2`, still
exactly 2 Mumford rows), `Fin 6`/`Fin 7`-sized `cramerSolution7`/
`coeffsOut7`, `Epoly4`/`Ypoly4`/`Npoly4`, and the K=4 exact-division chain
producing `curBeforeMonic4`.

## The `u_a` split-vs-irreducible fork (flagged in the roadmap, resolved here)

`(u_a,v_a)`'s two "anchor points" are the two roots of
`u_a(x) = x²+u_{a,1}x+u_{a,0}`, which may or may not lie in `F p` (`u_a`
may be irreducible over `F p`). The Julia reference implementation
represents anchors as literal `(x,y) : F p × F p` pairs and so implicitly
assumes split anchors throughout — dividing `N(x)` by `(x - t_i)` for each
literal anchor `t_i`. **This file avoids that assumption entirely**: since
one of `Reduce`'s two "extra" anchors is always the pair coming from
`(u_a,v_a)`, and `u_a` is EXACTLY the polynomial `x²+u_{a,1}x+u_{a,0}`
regardless of whether it splits, dividing `N(x)` by `u_a` DIRECTLY as a
single quadratic factor (exactly the way `curBeforeMonic`/`dvd_N_u`
already divide by the TARGET `u(x)` in the K=2 file) sidesteps the split
question altogether — no root-extraction of `u_a` is needed, matching how
`DataDerivationSolve.lean`'s own `dvd_N_u`/`IsMumfordTarget` route already
handles a Mumford pair via its defining quadratic rather than via literal
roots. So the K=4 anchor data actually splits into TWO different kinds of
row, mirroring `matrixA`'s own K=2 split (anchor-evaluation rows vs.
mod-`u` reduction rows) doubled: 2 literal-point anchor rows (`P1,P2`) +
2 mod-`u_a` reduction rows (in place of 2 more literal-point rows) + 2
mod-`u`(target) reduction rows = 6 rows total, matching `(K+2)×(K+2) =
6×6` exactly. This is a genuine, useful simplification over the Julia
source's literal-anchor-list representation, not a deviation from it:
`phi_residual_general!`'s own item-6 division step (Step 3,
`07_build_phi_general.jl`/`09_residual_and_modinv.jl`, read this pass)
divides by whichever concrete factors are known — a monic quadratic
`u_a(x)` is exactly as valid a "known factor" as two literal roots.

**Status of this pass**: `matrixA4`/`rhsVec4`/`MatrixNondegenerate4`/
`cramerSolution4`/`coeffsOut4`/`Epoly4`/`Ypoly4`/`Npoly4`/`curBeforeMonic4`
are all written, and the full K=4 combinatorial layer (`otherMap4`,
`sum_otherIdx7_add_y`, `coeffsOut4_otherMap`, the six row-unfolding
lemmas) plus all THREE row-identity theorems (`row01_defining_eq_aux`,
`row23_defining_eq_aux`, `row45_defining_eq_aux` — the K=4 rescalings of
`anchor_defining_eq_aux`/`row23_defining_eq_aux` one row-block up) are now
proved, `sorry`-free. `dvd_N_P1`/`dvd_N_P2` (K=4 analogues of
`dvd_N_anchor1`/`dvd_N_anchor2`) are also proved, each taking an explicit
`P1`/`P2`-on-curve hypothesis (`hP1_curve`/`hP2_curve`) since `P1,P2` here
are plain `F p × F p` pairs, not tower-adjoined roots the way
`anchor1`/`anchor2` are — a genuine new precondition, not a shortcut, per
this project's "hypotheses instead of proof" convention already used by
`IsMumfordTarget`. **This pass**: `dvd_N_ua`/`dvd_N_u4` (the K=4 analogues
of `dvd_N_u`) are now also proved, `sorry`-free, via a new factored-out
bridge lemma `dvd_of_row_identity4` (the K=4, plain-`F p` analogue of
`dvd_E_add_Y_mul_v`'s `hRsum`/`hRmod`/`xmodUTable_correct` argument —
simpler here since no `algebraMap`/tower promotion is needed). Not yet
exercised against the real Lean toolchain in this pass (written and
reasoned through carefully, cross-checked against `dvd_E_add_Y_mul_v`'s
already-compiling K=2 proof and the file's own already-compiling
`map_smul`/`modByMonicHom` idiom at `hRmod`, but Claire's REPL is the
actual test — see her instruction at the top of this project). **Not
started**: `uRS4`/`vRS4`
(monic-normalization/root-finding — note this is genuinely root-finding
on `curBeforeMonic4`'s roots intersected with the curve, not a separate
Mumford-reduction step; `Reduce` IS this root-finding, not something built
on top of it) and the `Reduce` function itself wrapping everything into the
`F p × F p × F p × F p` signature `AlphaLocusDegreeUniform.lean` needs. -/

namespace Genus2Lean
namespace TheDataDerivation

open Polynomial

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-! ## RR basis, `nb = K+3 = 7` for `K=4` -/

/-- The `K=4` Riemann–Roch basis, `nb = 7` elements — same construction as
`rrBasis5` (`DataDerivationBasics.lean`), just taking 7 instead of 5 from
the same sorted candidate stream. Computed, not asserted: confirmed by
direct computation this pass to be
`[(0,0,0),(2,1,0),(4,2,0),(5,0,1),(6,3,0),(7,1,1),(8,4,0)]` — note TWO
`bj=1` entries here (`(5,0,1)` and `(7,1,1)`, i.e. `y` and `x*y`), unlike
`rrBasis5`'s single `bj=1` entry — a genuine structural difference from
K=2 that changes `Ypoly4`'s degree bound (`≤ 1`, not `≤ 0` the way
`Ypoly_natDegree_le_zero` has it for K=2) once that def is written. -/
def rrBasis7 : List (ℕ × ℕ × ℕ) :=
  ((rrBasisCandidates 20).mergeSort (fun a b => a.1 ≤ b.1)).take 7

/-- Every element of `rrBasis7` has flag component `0` or `1` — mirrors
`rrBasis5_flag` (`DataDerivationBasics.lean`) exactly, reusing the SAME
general `rrBasisCandidates_flag` fact (which holds for any `maxOrder`, not
just the `take`-length used downstream) via `rrBasis7 ⊆ rrBasisCandidates
20`. Needed by `row01_defining_eq_aux`'s `bj ∈ {0,1}` case split, the same
way `rrBasis5_flag` is needed by `anchor_defining_eq_aux`'s. -/
theorem rrBasis7_flag : ∀ t ∈ rrBasis7, t.2.2 = 0 ∨ t.2.2 = 1 := by
  intro t ht
  apply rrBasisCandidates_flag 20
  have ht' : t ∈ (rrBasisCandidates 20).mergeSort (fun a b => a.1 ≤ b.1) :=
    List.mem_of_mem_take ht
  exact (List.mem_mergeSort).mp ht'

/-- `y_idx` for the K=4 basis: the position of the FIRST `bj=1` entry,
`(5,0,1)` — matching `build_phi_general!`'s own `y_idx =
findfirst(bi -> bi == (0,1), basis)` (`07_build_phi_general.jl`, read this
pass), which always normalizes the BARE-`y` monomial's coefficient to `1`,
not `x*y`'s, even though `rrBasis7` (unlike `rrBasis5`) has a second
`bj=1` entry later in the list. -/
def yIdx7 : ℕ := (rrBasis7.findIdx (fun bij => bij.2.1 = 0 ∧ bij.2.2 = 1))

/-- The 6 remaining basis positions (all of `Fin 7` except `yIdx7`) — these
become the `(K+2)=6` matrix columns / solved unknowns, matching `otherIdx`
(`DataDerivationSolve.lean`) one level up in size. -/
def otherIdx7 : List ℕ := (List.range 7).filter (· ≠ yIdx7)

/-- `yIdx7 < 7`, needed the same way `yIdx_lt_five` was for K=2. **Proved
this pass** — direct adaptation of `yIdx_lt_five`'s proof
(`DataDerivationSolve.lean`): the witness `x := (5,0,1)`, the
`countP (fun a => q a x)`-over-`rrBasisCandidates 20` value (`4`, checked
by `decide` — CONFIRMED unchanged from K=2's own `hcount_unsorted = 4`,
since this count only depends on `x.1 = 5` and `rrBasisCandidates 20`
itself, not on how many elements are later `.take`n), and the final bound
`4 < 7` (K=2 needed `4 < 5`; both hold from the SAME rank, only the target
bound differs since `rrBasis7` takes 2 more elements than `rrBasis5`) are
the only genuinely K-dependent numbers in the whole argument — everything
else (the generic `findIdx_lt_countP_of_pairwise` lemma, the
`mergeSort`-pairwise/perm reasoning) transfers unchanged. -/
theorem yIdx7_lt_seven : yIdx7 < 7 := by
  let x : ℕ × ℕ × ℕ := (5, 0, 1)
  let q : (ℕ × ℕ × ℕ) → (ℕ × ℕ × ℕ) → Bool := fun a b => decide (a.1 ≤ b.1)
  let s : List (ℕ × ℕ × ℕ) := (rrBasisCandidates 20).mergeSort q
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
  have hx_take : x ∈ s.take 7 := by
    rw [List.mem_iff_getElem]
    refine ⟨s.findIdx (fun a => decide (a = x)), ?_, ?_⟩
    · rw [List.length_take]
      omega
    · have hopt : s[s.findIdx (fun a => decide (a = x))]? = some x :=
        (List.getElem_eq_iff hx_find_lt).mp hx_at
      have htake : (s.take 7)[s.findIdx (fun a => decide (a = x))]? =
          s[s.findIdx (fun a => decide (a = x))]? := by
        apply List.getElem?_take_of_lt; omega
      have hsome : (s.take 7)[s.findIdx (fun a => decide (a = x))]? = some x := by
        rw [htake]; exact hopt
      exact (List.getElem_eq_iff _).mpr hsome
  have hx_rrBasis7 : x ∈ rrBasis7 := by simpa [rrBasis7, s, q] using hx_take
  have hy_len : yIdx7 < rrBasis7.length := by
    apply List.findIdx_lt_length_of_exists
    refine ⟨x, hx_rrBasis7, ?_⟩
    simp [x]
  have hlen : rrBasis7.length = 7 := by
    simp [rrBasis7, rrBasisCandidates, List.length_flatMap]
  rw [hlen] at hy_len; exact hy_len

/-- `rrBasis7`'s value at `yIdx7` is exactly `(5,0,1)` — **proved this
pass**, direct adaptation of `rrBasis5_yIdx_eq`'s proof, `take 5`/`Fin 5`
replaced by `take 7`/`Fin 7` throughout; the uniqueness-of-`(5,0,1)`-in-
`rrBasisCandidates 20` argument is IDENTICAL (that uniqueness fact doesn't
depend on how many elements are later taken). -/
theorem rrBasis7_yIdx_eq : rrBasis7.getD yIdx7 (0, 0, 0) = (5, 0, 1) := by
  have hlen : rrBasis7.length = 7 := by
    simp [rrBasis7, rrBasisCandidates, List.length_flatMap]
  have hlt : yIdx7 < rrBasis7.length := hlen ▸ yIdx7_lt_seven
  have hunique : ∀ t ∈ rrBasisCandidates 20, (t.2.1 = 0 ∧ t.2.2 = 1) ↔ t = (5, 0, 1) := by
    intro t ht
    simp only [rrBasisCandidates, List.mem_flatMap, List.mem_range] at ht
    obtain ⟨i, _, hti⟩ := ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hti
    rcases hti with hti | hti
    · subst hti; constructor
      · rintro ⟨-, hbot⟩
        exact absurd hbot (by simp)
      · intro hbot
        simp only [Prod.mk.injEq] at hbot
        simp only
        omega
    · subst hti; constructor
      · rintro ⟨hbi, -⟩; subst hbi; rfl
      · intro heq
        have : i = 0 := by
          have := heq
          simpa using congrArg (fun t => t.2.1) this
        subst this; exact ⟨rfl, rfl⟩
  have hsub : ∀ t ∈ rrBasis7, t ∈ rrBasisCandidates 20 := by
    intro t ht
    have ht' : t ∈ (rrBasisCandidates 20).mergeSort (fun a b => decide (a.1 ≤ b.1)) :=
      List.mem_of_mem_take ht
    exact (List.mem_mergeSort).mp ht'
  have hpred_eq : ∀ t ∈ rrBasis7,
      decide (t.2.1 = 0 ∧ t.2.2 = 1) = decide (t = ((5, 0, 1) : ℕ × ℕ × ℕ)) := by
    intro t ht
    exact decide_eq_decide.mpr (hunique t (hsub t ht))
  have findIdx_eq_of_pred_eq_on :
      ∀ {α : Type} {p q : α → Bool} {l : List α},
        (∀ t ∈ l, p t = q t) → l.findIdx p = l.findIdx q := by
    intro α p q l
    induction l with
    | nil => intro _; rfl
    | cons a l ih =>
      intro heq
      have ha : p a = q a := heq a (by simp)
      simp only [List.findIdx_cons, ha]
      by_cases hqa : q a = true
      · simp [hqa]
      · simp only [hqa]
        have hrest : ∀ t ∈ l, p t = q t := fun t ht => heq t (List.mem_cons_of_mem a ht)
        rw [ih hrest]
  have hfind_eq : rrBasis7.findIdx (fun bij => decide (bij.2.1 = 0 ∧ bij.2.2 = 1)) =
      rrBasis7.findIdx (fun bij => decide (bij = ((5, 0, 1) : ℕ × ℕ × ℕ))) :=
    findIdx_eq_of_pred_eq_on hpred_eq
  have hlt' : rrBasis7.findIdx (fun bij => decide (bij = ((5, 0, 1) : ℕ × ℕ × ℕ))) <
      rrBasis7.length := hfind_eq ▸ hlt
  have hpred := List.findIdx_getElem (xs := rrBasis7)
    (p := fun bij => decide (bij = ((5, 0, 1) : ℕ × ℕ × ℕ))) (w := hlt')
  have hyidx_eq : yIdx7 = rrBasis7.findIdx (fun bij => decide (bij = ((5, 0, 1) : ℕ × ℕ × ℕ))) := by
    change rrBasis7.findIdx (fun bij => decide (bij.2.1 = 0 ∧ bij.2.2 = 1)) = _
    exact hfind_eq
  rw [List.getD_eq_getElem _ _ hlt]
  have hcast : rrBasis7[yIdx7] =
      rrBasis7[rrBasis7.findIdx (fun bij => decide (bij = ((5, 0, 1) : ℕ × ℕ × ℕ)))]'hlt' := by
    simp only [hyidx_eq]
  rw [hcast]
  simpa using hpred

/-- `otherIdx7.length = 6` — direct adaptation of `otherIdx_length`'s proof
(`DataDerivationSolve.lean`), `range 5`/5-way case split replaced by
`range 7`/7-way. -/
theorem otherIdx7_length : otherIdx7.length = 6 := by
  have hy := yIdx7_lt_seven
  have hy_cases : yIdx7 = 0 ∨ yIdx7 = 1 ∨ yIdx7 = 2 ∨ yIdx7 = 3 ∨ yIdx7 = 4 ∨
      yIdx7 = 5 ∨ yIdx7 = 6 := by omega
  rcases hy_cases with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · change ((List.range 7).filter (fun x => x ≠ yIdx7)).length = 6
    rw [h0]; decide
  · change ((List.range 7).filter (fun x => x ≠ yIdx7)).length = 6
    rw [h1]; decide
  · change ((List.range 7).filter (fun x => x ≠ yIdx7)).length = 6
    rw [h2]; decide
  · change ((List.range 7).filter (fun x => x ≠ yIdx7)).length = 6
    rw [h3]; decide
  · change ((List.range 7).filter (fun x => x ≠ yIdx7)).length = 6
    rw [h4]; decide
  · change ((List.range 7).filter (fun x => x ≠ yIdx7)).length = 6
    rw [h5]; decide
  · change ((List.range 7).filter (fun x => x ≠ yIdx7)).length = 6
    rw [h6]; decide

/-! ## Combinatorial layer: `Fin 6 → Fin 7` reindexing, K=4 rescaling of
`DataDerivationSolve.lean`'s `otherMap`/`sum_otherIdx_add_y`/
`coeffsOut_otherMap` apparatus (`Fin 4 → Fin 5` there). Needed by the
row-identity arguments (`row*_defining_eq_aux`, not yet ported — see module
docstring) the same way the K=2 originals are needed by
`anchor_defining_eq_aux`/`row23_defining_eq_aux`. -/

/-- `Prop`-form membership characterization for `otherIdx7`, mirroring
`mem_otherIdx_iff`. -/
private theorem mem_otherIdx7_iff (n : ℕ) : n ∈ otherIdx7 ↔ n < 7 ∧ n ≠ yIdx7 := by
  unfold otherIdx7
  rw [List.mem_filter, List.mem_range, decide_eq_true_eq]

private theorem otherIdx7_nodup : otherIdx7.Nodup := by
  unfold otherIdx7
  exact List.nodup_range.filter _

/-- **The reindexing bijection**, `col : Fin 6 ↦ otherIdx7[col] : Fin 7`,
mirroring `otherMap` one size up. -/
def otherMap4 (col : Fin 6) : Fin 7 :=
  ⟨otherIdx7.getD col.val 0, by
    have hcol : col.val < otherIdx7.length := by rw [otherIdx7_length]; exact col.isLt
    have hmem : otherIdx7[col.val] ∈ otherIdx7 := List.getElem_mem hcol
    have hlt7 : otherIdx7[col.val] < 7 := ((mem_otherIdx7_iff _).mp hmem).1
    rw [List.getD_eq_getElem _ _ hcol]
    exact hlt7⟩

theorem otherMap4_injective : Function.Injective otherMap4 := by
  intro i j hij
  have hi : i.val < otherIdx7.length := by rw [otherIdx7_length]; exact i.isLt
  have hj : j.val < otherIdx7.length := by rw [otherIdx7_length]; exact j.isLt
  have hget : otherIdx7[i.val] = otherIdx7[j.val] := by
    have := congrArg Fin.val hij
    simp only [otherMap4, List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at this
    exact this
  exact Fin.ext ((otherIdx7_nodup.getElem_inj_iff (hi := hi) (hj := hj)).mp hget)

theorem otherMap4_surjOn (b : Fin 7) (hby : b ≠ ⟨yIdx7, yIdx7_lt_seven⟩) :
    ∃ col : Fin 6, otherMap4 col = b := by
  have hbval_ne : b.val ≠ yIdx7 := fun h => hby (Fin.ext h)
  have hbmem : b.val ∈ otherIdx7 := (mem_otherIdx7_iff _).mpr ⟨b.isLt, hbval_ne⟩
  obtain ⟨n, hn, hne⟩ := List.mem_iff_getElem.mp hbmem
  have hn6 : n < 6 := by rw [← otherIdx7_length]; exact hn
  refine ⟨⟨n, hn6⟩, Fin.ext ?_⟩
  change otherIdx7.getD n 0 = b.val
  rw [List.getD_eq_getElem _ _ hn]
  exact hne

/-- **The `Fin 6 → Fin 7` reindexing identity**, mirroring
`sum_otherIdx_add_y` one size up: summing over `otherIdx7`'s 6 positions
(via `otherMap4`) plus the `yIdx7` term separately is the same as summing
over all of `Fin 7`. -/
theorem sum_otherIdx7_add_y (Fsum : Fin 7 → F p) :
    (∑ col : Fin 6, Fsum (otherMap4 col)) + Fsum ⟨yIdx7, yIdx7_lt_seven⟩ =
      ∑ bidx : Fin 7, Fsum bidx := by
  have hsum : (∑ col : Fin 6, Fsum (otherMap4 col)) =
      ∑ b ∈ (Finset.univ.erase (⟨yIdx7, yIdx7_lt_seven⟩ : Fin 7)), Fsum b := by
    apply Finset.sum_bij (fun (col : Fin 6) (_ : col ∈ (Finset.univ : Finset (Fin 6))) =>
      otherMap4 col)
    · intro col _
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      have hcol : col.val < otherIdx7.length := by rw [otherIdx7_length]; exact col.isLt
      have hmem : otherIdx7[col.val] ∈ otherIdx7 := List.getElem_mem hcol
      have hmem' : otherIdx7[col.val] ≠ yIdx7 := ((mem_otherIdx7_iff _).mp hmem).2
      change (⟨otherIdx7.getD col.val 0, _⟩ : Fin 7) ≠ ⟨yIdx7, yIdx7_lt_seven⟩
      intro hcontra
      apply hmem'
      have heq : otherIdx7.getD col.val 0 = yIdx7 := congrArg Fin.val hcontra
      rw [List.getD_eq_getElem _ _ hcol] at heq
      exact heq
    · intro col1 _ col2 _ heq
      exact otherMap4_injective heq
    · intro col1 hb
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hb
      obtain ⟨col, hcol⟩ := otherMap4_surjOn col1 hb
      exact ⟨col, Finset.mem_univ _, hcol⟩
    · intro col _
      rfl
  have hy_mem : (⟨yIdx7, yIdx7_lt_seven⟩ : Fin 7) ∈ (Finset.univ : Finset (Fin 7)) :=
    Finset.mem_univ _
  have hsplit : (∑ bidx : Fin 7, Fsum bidx) =
      Fsum ⟨yIdx7, yIdx7_lt_seven⟩ +
        ∑ b ∈ (Finset.univ.erase (⟨yIdx7, yIdx7_lt_seven⟩ : Fin 7)), Fsum b := by
    have hnotmem : (⟨yIdx7, yIdx7_lt_seven⟩ : Fin 7) ∉
        Finset.univ.erase (⟨yIdx7, yIdx7_lt_seven⟩ : Fin 7) := by
      simp [Finset.mem_erase]
    rw [← Finset.sum_insert hnotmem, Finset.insert_erase hy_mem]
  rw [hsum, hsplit]
  ring

/-! ## The `6×6` matrix, `E,Y,N`, and exact division — `K=4` instance

Row layout (per this file's module docstring, "the `u_a` split-vs-
irreducible fork" section): rows 0–1 evaluate at the two LITERAL points
`P1,P2`; rows 2–3 reduce mod `u_a(x) = x²+ua1*x+ua0` (in place of two more
literal-anchor rows, sidestepping whether `u_a` splits over `F p`); rows
4–5 reduce mod the TARGET `u(x) = x²+u1*x+u0` (same role as K=2's rows
2–3). `reduceMonomialModU`/`xmodUTable` (`DataDerivationBasics.lean`) are
reused UNCHANGED for both the `u_a`-rows and the target-rows — that
function only ever depended on a monic quadratic's coefficients, never on
`K` or on whether the quadratic came from a "target" or an intermediate
anchor, so the same function correctly serves both roles here. -/

variable (c0 c1 c2 c3 c4 : F p)

/-- The `6×6` matrix `A` over `F p` for the `K=4` reduction. Column
`col : Fin 6` picks out `otherIdx7`'s `col`-th basis position (mirroring
`matrixA`'s `otherIdx.getD col.val 0` step exactly). Row `row : Fin 6`:
`0,1` evaluate the column's monomial at `P1,P2` respectively; `2,3` use
`reduceMonomialModU` against `(ua0,ua1,va0,va1)` (`u_a`'s own coefficients
standing in for a "target" in `reduceMonomialModU`'s sense, which is valid
since that function only needs a monic quadratic divisor and a linear
`v`-value to reduce against — exactly what `(u_a,v_a)` supplies); `4,5`
use `reduceMonomialModU` against the ACTUAL target `(u0,u1,v0,v1)`. -/
noncomputable def matrixA4 (P1 P2 : F p × F p) (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p) :
    Matrix (Fin 6) (Fin 6) (F p) :=
  fun row col =>
    let bidx := otherIdx7.getD col.val 0
    let (_, bi, bj) := rrBasis7.getD bidx (0, 0, 0)
    if row.val = 0 then
      P1.1 ^ bi * (if bj = 1 then P1.2 else 1)
    else if row.val = 1 then
      P2.1 ^ bi * (if bj = 1 then P2.2 else 1)
    else if row.val = 2 ∨ row.val = 3 then
      let (r0, r1) := reduceMonomialModU p ua0 ua1 va0 va1 bi bj
      if row.val = 2 then r0 else r1
    else
      let (r0, r1) := reduceMonomialModU p u0 u1 v0 v1 bi bj
      if row.val = 4 then r0 else r1

/-- The RHS vector, same 6-row split as `matrixA4`, evaluating/reducing the
`yIdx7`-th basis element (the bare-`y` monomial) the same way, negated —
mirrors `rhsVec` (`DataDerivationSolve.lean`) exactly, one size up. -/
noncomputable def rhsVec4 (P1 P2 : F p × F p) (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p) :
    Fin 6 → F p :=
  fun row =>
    let (_, bi_n, bj_n) := rrBasis7.getD yIdx7 (0, 1, 1)
    if row.val = 0 then
      -(P1.1 ^ bi_n * (if bj_n = 1 then P1.2 else 1))
    else if row.val = 1 then
      -(P2.1 ^ bi_n * (if bj_n = 1 then P2.2 else 1))
    else if row.val = 2 ∨ row.val = 3 then
      let (rn0, rn1) := reduceMonomialModU p ua0 ua1 va0 va1 bi_n bj_n;
      -(if row.val = 2 then rn0 else rn1)
    else
      let (rn0, rn1) := reduceMonomialModU p u0 u1 v0 v1 bi_n bj_n;
      -(if row.val = 4 then rn0 else rn1)

/-- **Row-unfolding lemma for rows 0–1 (the `P1`/`P2` point-evaluation
rows), K=4 instance** — mirrors `matrixA_row_eval` one size up (`Fin 2 →
Fin 4` there becomes "row `a ∈ {0,1}`, `col : Fin 6`" here, `otherIdx`
becomes `otherIdx7`). `matrixA4`'s row-0/row-1 branches unfolded literally
via `fin_cases`/`simp`, isolated as its own lemma the same way
`matrixA_row_eval` avoids re-deriving the `if row.val = 0 then ... else if
...`-chain unfolding at every call site. -/
theorem matrixA4_row01_eval (P1 P2 : F p × F p) (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (a : Fin 2) (col : Fin 6) :
    matrixA4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ⟨a.val, by omega⟩ col =
      let (px, py) := (![P1, P2] : Fin 2 → F p × F p) a
      let (_, bi, bj) := rrBasis7.getD (otherIdx7.getD col.val 0) (0, 0, 0)
      px ^ bi * (if bj = 1 then py else 1) := by
  fin_cases a <;> simp [matrixA4]

/-- Row-unfolding lemma for rows 2–3 (the mod-`u_a` rows), K=4 instance —
mirrors `matrixA_row23_eval`. -/
theorem matrixA4_row23_eval (P1 P2 : F p × F p) (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (a : Fin 2) (col : Fin 6) :
    matrixA4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ⟨2 + a.val, by omega⟩ col =
      let (_, bi, bj) := rrBasis7.getD (otherIdx7.getD col.val 0) (0, 0, 0)
      let (r0, r1) := reduceMonomialModU p ua0 ua1 va0 va1 bi bj
      if a.val = 0 then r0 else r1 := by
  fin_cases a <;> simp [matrixA4]

/-- Row-unfolding lemma for rows 4–5 (the mod-target-`u` rows), K=4
instance — mirrors `matrixA_row23_eval`'s pattern one row-pair further
along; `matrixA4`'s catch-all `else` branch (rows 4/5, the only remaining
possibilities once `row.val ≠ 0,1,2,3`) unfolded the same way. -/
theorem matrixA4_row45_eval (P1 P2 : F p × F p) (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (a : Fin 2) (col : Fin 6) :
    matrixA4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ⟨4 + a.val, by omega⟩ col =
      let (_, bi, bj) := rrBasis7.getD (otherIdx7.getD col.val 0) (0, 0, 0)
      let (r0, r1) := reduceMonomialModU p u0 u1 v0 v1 bi bj
      if a.val = 0 then r0 else r1 := by
  fin_cases a <;> simp [matrixA4]

/-- Row-unfolding for `rhsVec4`'s rows 0–1, mirroring the `rhsVec`
row-0/row-1 shape (the analogue is inlined directly into
`row01_defining_eq_aux`'s `hrhsApply` step in the K=2 file rather than
named separately, but is broken out here as its own lemma for clarity). -/
theorem rhsVec4_row01_eval (P1 P2 : F p × F p) (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (a : Fin 2) :
    rhsVec4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ⟨a.val, by omega⟩ =
      let (px, py) := (![P1, P2] : Fin 2 → F p × F p) a
      let (_, bi_n, bj_n) := rrBasis7.getD yIdx7 (0, 1, 1)
      (-(px ^ bi_n * (if bj_n = 1 then py else 1))) := by
  fin_cases a <;> rfl

/-- Row-unfolding for `rhsVec4`'s rows 2–3, mirroring `rhsVec_row23_eval`. -/
theorem rhsVec4_row23_eval (P1 P2 : F p × F p) (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (a : Fin 2) :
    rhsVec4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ⟨2 + a.val, by omega⟩ =
      let (_, bi_n, bj_n) := rrBasis7.getD yIdx7 (0, 1, 1)
      let (rn0, rn1) := reduceMonomialModU p ua0 ua1 va0 va1 bi_n bj_n
      (-(if a.val = 0 then rn0 else rn1)) := by
  fin_cases a <;> rfl

/-- Row-unfolding for `rhsVec4`'s rows 4–5, mirroring `rhsVec_row23_eval`
one row-pair further along. -/
theorem rhsVec4_row45_eval (P1 P2 : F p × F p) (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (a : Fin 2) :
    rhsVec4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ⟨4 + a.val, by omega⟩ =
      let (_, bi_n, bj_n) := rrBasis7.getD yIdx7 (0, 1, 1)
      let (rn0, rn1) := reduceMonomialModU p u0 u1 v0 v1 bi_n bj_n
      (-(if a.val = 0 then rn0 else rn1)) := by
  fin_cases a <;> rfl

/-- **Genericity condition, K=4 instance** — mirrors `MatrixNondegenerate`
(`DataDerivationSolve.lean`) exactly: `theData`-for-`Reduce` is only
well-defined where `A.det ≠ 0`, a genuine further exceptional-locus
condition on `(P1,P2,u_a,v_a,\text{target})`, not proved or assumed
globally. -/
def MatrixNondegenerate4 (P1 P2 : F p × F p) (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p) : Prop :=
  (matrixA4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).det ≠ 0

/-- The 6 solved coefficients via Cramer's rule, mirroring `cramerSolution`
one size up. Well-defined as the correct solution to `A*c = rhs` only
under `MatrixNondegenerate4` — as with `cramerSolution`, this still
typechecks unconditionally (division by a possibly-zero determinant is `0`
in a field), correctness deferred to callers who supply the hypothesis. -/
noncomputable def cramerSolution4 (P1 P2 : F p × F p) (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p) :
    Fin 6 → F p :=
  fun i =>
    (matrixA4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).cramer
        (rhsVec4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) i /
      (matrixA4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).det

/-- The full 7-slot coefficient vector: `cramerSolution4` at the 6
`otherIdx7` slots, `1` at `yIdx7` — mirrors `coeffsOut` exactly, one size
up. **Proved this pass** (`otherIdx7_length` above supplies the length
fact this needs), same `List.mem_iff_getElem`-based pattern `coeffsOut`
uses. -/
noncomputable def coeffsOut4 (P1 P2 : F p × F p) (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p) :
    Fin 7 → F p :=
  fun bidx =>
    if hy : bidx.val = yIdx7 then 1
    else
      have hmem : bidx.val ∈ otherIdx7 := by
        simp only [otherIdx7, List.mem_filter, List.mem_range, decide_eq_true_eq]
        exact ⟨bidx.isLt, hy⟩
      have hex : ∃ (n : ℕ) (_ : n < otherIdx7.length), otherIdx7[n] = bidx.val :=
        List.mem_iff_getElem.mp hmem
      have hlt : hex.choose < 6 := otherIdx7_length ▸ hex.choose_spec.choose
      cramerSolution4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ⟨hex.choose, hlt⟩

/-- **Bridging `coeffsOut4` and `cramerSolution4` across `otherMap4`** —
mirrors `coeffsOut_otherMap` one size up (`Fin 4`/`otherIdx` replaced by
`Fin 6`/`otherIdx7` throughout). Needed by the (not yet ported) row-identity
arguments the same way `coeffsOut_otherMap` is needed by
`anchor_defining_eq_aux`/`row23_defining_eq_aux`. -/
theorem coeffsOut4_otherMap (P1 P2 : F p × F p) (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (col : Fin 6) :
    coeffsOut4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 (otherMap4 col) =
      cramerSolution4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 col := by
  have hcol : col.val < otherIdx7.length := by rw [otherIdx7_length]; exact col.isLt
  have hgetD : otherIdx7.getD col.val 0 = otherIdx7[col.val] := List.getD_eq_getElem _ _ hcol
  have hne : (otherMap4 col).val ≠ yIdx7 := by
    have hmem : otherIdx7[col.val] ∈ otherIdx7 := List.getElem_mem hcol
    have : otherIdx7[col.val] ≠ yIdx7 := ((mem_otherIdx7_iff _).mp hmem).2
    change otherIdx7.getD col.val 0 ≠ yIdx7
    rw [hgetD]; exact this
  unfold coeffsOut4
  rw [dif_neg hne]
  set hex : ∃ (n : ℕ) (_ : n < otherIdx7.length), otherIdx7[n] = (otherMap4 col).val :=
    List.mem_iff_getElem.mp (by
      simp only [otherIdx7, List.mem_filter, List.mem_range, decide_eq_true_eq]
      exact ⟨(otherMap4 col).isLt, hne⟩) with hex_def
  have hspec : otherIdx7[hex.choose]'(hex.choose_spec.choose) = (otherMap4 col).val :=
    hex.choose_spec.choose_spec
  have hgoal_val : otherIdx7[hex.choose]'(hex.choose_spec.choose) = otherIdx7[col.val] := by
    rw [hspec]
    change otherIdx7.getD col.val 0 = otherIdx7[col.val]
    exact hgetD
  have hidx_eq : hex.choose = col.val :=
    otherIdx7_nodup.getElem_inj_iff.mp hgoal_val
  have hchoose_lt6 : hex.choose < 6 := by rw [← otherIdx7_length]; exact hex.choose_spec.choose
  exact congrArg (cramerSolution4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (Fin.ext (a := (⟨hex.choose, hchoose_lt6⟩ : Fin 6)) (b := col) hidx_eq)


/-- `E(x) = Σ_{bj=0} c_i x^i` for the K=4 instance — mirrors `Epoly`
exactly, summing over `Fin 7` instead of `Fin 5`. -/
noncomputable def Epoly4 (P1 P2 : F p × F p) (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p) :
    Polynomial (F p) :=
  ∑ bidx : Fin 7,
    let (_, bi, bj) := rrBasis7.getD bidx.val (0, 0, 0)
    if bj = 0 then C (coeffsOut4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 bidx) * X ^ bi else 0

/-- `Y(x) = Σ_{bj=1} c_i x^i` for the K=4 instance. **Genuinely different
from `Ypoly`'s K=2 shape**: `rrBasis7` has TWO `bj=1` entries (`(5,0,1)`
and `(7,1,1)`, per `rrBasis7`'s own docstring), so `Ypoly4` has degree `≤
1` in general (a `c₃ + c₅·x` shape), not the constant `Ypoly_natDegree_le_zero`
proves for K=2 — this is the single largest structural difference from
the K=2 port, flagged here rather than assumed away. -/
noncomputable def Ypoly4 (P1 P2 : F p × F p) (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p) :
    Polynomial (F p) :=
  ∑ bidx : Fin 7,
    let (_, bi, bj) := rrBasis7.getD bidx.val (0, 0, 0)
    if bj = 1 then C (coeffsOut4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 bidx) * X ^ bi else 0

/-! ## The three row-identity theorems, K=4 instance

Direct rescaling of `anchor_defining_eq_aux`/`row23_defining_eq_aux`
(`DataDerivationSolve.lean`), `Fin 4 → Fin 5` replaced by `Fin 6 → Fin 7`
throughout, and split into THREE row-blocks (rows 0–1, 2–3, 4–5) instead
of two (rows 0–1, 2–3), matching `matrixA4`'s extra mod-`u_a` row-pair.
Same five-step Cramer's-rule argument each time: (1) `Matrix.mulVec_cramer`
at the target row, (2) divide by `A.det ≠ 0` to land on `cramerSolution4`,
(3) unfold both sides via the row-unfolding lemmas above, (4) reindex
`Fin 6 → Fin 7` via `sum_otherIdx7_add_y`, (5) the resulting 7-slot sum is
literally `Epoly4.eval + py*Ypoly4.eval` (rows 0–1) or the `reduceMonomialModU`-
combination (rows 2–3, 4–5) by `Epoly4`/`Ypoly4`'s own `bj`-split
definitions. -/

/-- **The seven-slot defining identity for the point-evaluation rows**
(rows 0–1, `P1`/`P2`) — the K=4 analogue of `anchor_defining_eq_aux`. -/
private theorem row01_defining_eq_aux (P1 P2 : F p × F p) (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (hA : MatrixNondegenerate4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) (a : Fin 2) :
    (Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval
        ((![P1, P2] : Fin 2 → F p × F p) a).1 +
      ((![P1, P2] : Fin 2 → F p × F p) a).2 *
        (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval
          ((![P1, P2] : Fin 2 → F p × F p) a).1 = 0 := by
  set A := matrixA4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 with hA_def
  set rhs := rhsVec4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 with hrhs_def
  have hdet : A.det ≠ 0 := hA
  have haRow : a.val < 6 := by omega
  have hmul := Matrix.mulVec_cramer A rhs
  have hrow := congrFun hmul (⟨a.val, haRow⟩ : Fin 6)
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hrow
  have hrow' : ∑ col : Fin 6, A ⟨a.val, haRow⟩ col *
      (A.cramer rhs col / A.det) = rhs ⟨a.val, haRow⟩ := by
    have hstep : (∑ col : Fin 6, A ⟨a.val, haRow⟩ col * (A.cramer rhs col / A.det)) * A.det =
        rhs ⟨a.val, haRow⟩ * A.det := by
      rw [Finset.sum_mul]
      have : ∀ col : Fin 6, A ⟨a.val, haRow⟩ col * (A.cramer rhs col / A.det) * A.det =
          A ⟨a.val, haRow⟩ col * A.cramer rhs col := by
        intro col; field_simp
      simp only [this]
      rw [hrow]; ring
    exact mul_right_cancel₀ hdet hstep
  have hcramerSolution : ∀ col : Fin 6, A.cramer rhs col / A.det =
      cramerSolution4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 col := fun col => rfl
  simp only [hcramerSolution] at hrow'
  have hApply : ∀ col : Fin 6, A ⟨a.val, haRow⟩ col =
      let (px, py) := (![P1, P2] : Fin 2 → F p × F p) a
      let (_, bi, bj) := rrBasis7.getD (otherIdx7.getD col.val 0) (0, 0, 0)
      px ^ bi * (if bj = 1 then py else 1) := fun col =>
    matrixA4_row01_eval p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 a col
  have hrhsApply : rhs ⟨a.val, haRow⟩ =
      let (px, py) := (![P1, P2] : Fin 2 → F p × F p) a
      let (_, bi_n, bj_n) := rrBasis7.getD yIdx7 (0, 1, 1)
      (-(px ^ bi_n * (if bj_n = 1 then py else 1))) :=
    rhsVec4_row01_eval p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 a
  clear_value A rhs
  rw [hrhsApply] at hrow'
  have hmoved : (∑ col : Fin 6, coeffsOut4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 (otherMap4 col) *
      (let (px, py) := (![P1, P2] : Fin 2 → F p × F p) a
       let (_, bi, bj) := rrBasis7.getD (otherIdx7.getD col.val 0) (0, 0, 0)
       px ^ bi * (if bj = 1 then py else 1))) +
      coeffsOut4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ⟨yIdx7, yIdx7_lt_seven⟩ *
        (let (px, py) := (![P1, P2] : Fin 2 → F p × F p) a
         let (_, bi_n, bj_n) := rrBasis7.getD yIdx7 (0, 1, 1)
         px ^ bi_n * (if bj_n = 1 then py else 1)) = 0 := by
    have hcoeffsOutY : coeffsOut4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ⟨yIdx7, yIdx7_lt_seven⟩ = 1 := by
      unfold coeffsOut4; rw [dif_pos rfl]
    rw [hcoeffsOutY, one_mul]
    have hstep : ∑ col : Fin 6, coeffsOut4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 (otherMap4 col) *
        (let (px, py) := (![P1, P2] : Fin 2 → F p × F p) a
         let (_, bi, bj) := rrBasis7.getD (otherIdx7.getD col.val 0) (0, 0, 0)
         px ^ bi * (if bj = 1 then py else 1)) =
        ∑ col : Fin 6, cramerSolution4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 col *
        (let (px, py) := (![P1, P2] : Fin 2 → F p × F p) a
         let (_, bi, bj) := rrBasis7.getD (otherIdx7.getD col.val 0) (0, 0, 0)
         px ^ bi * (if bj = 1 then py else 1)) := by
      apply Finset.sum_congr rfl
      intro col _
      rw [coeffsOut4_otherMap p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 col]
    have horder : (∑ col : Fin 6, cramerSolution4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 col *
          (let (px, py) := (![P1, P2] : Fin 2 → F p × F p) a
           let (_, bi, bj) := rrBasis7.getD (otherIdx7.getD col.val 0) (0, 0, 0)
           px ^ bi * (if bj = 1 then py else 1)))
        = ∑ col : Fin 6, A ⟨a.val, haRow⟩ col *
            cramerSolution4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 col := by
      apply Finset.sum_congr rfl
      intro col _
      rw [mul_comm (cramerSolution4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 col), hApply col]
    rw [hstep, horder, hrow']
    exact neg_add_cancel _
  set px := ((![P1, P2] : Fin 2 → F p × F p) a).1 with hpx_def
  set py := ((![P1, P2] : Fin 2 → F p × F p) a).2 with hpy_def
  set Fsum : Fin 7 → F p := fun bidx =>
    coeffsOut4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 bidx *
      (let (_, bi, bj) := rrBasis7.getD bidx.val (0, 0, 0)
       px ^ bi * (if bj = 1 then py else 1)) with hF_def
  have hFcol : ∀ col : Fin 6, Fsum (otherMap4 col) =
      coeffsOut4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 (otherMap4 col) *
      (let (px, py) := (px, py)
       let (_, bi, bj) := rrBasis7.getD (otherIdx7.getD col.val 0) (0, 0, 0)
       px ^ bi * (if bj = 1 then py else 1)) := by
    intro col
    change
      coeffsOut4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 (otherMap4 col) *
          (let (_, bi, bj) := rrBasis7.getD (otherMap4 col).val (0, 0, 0)
           px ^ bi * (if bj = 1 then py else 1)) = _
    rfl
  have hFy : Fsum (⟨yIdx7, yIdx7_lt_seven⟩ : Fin 7) =
      coeffsOut4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ⟨yIdx7, yIdx7_lt_seven⟩ *
      (let (px, py) := (px, py)
       let (_, bi_n, bj_n) := rrBasis7.getD yIdx7 (0, 1, 1)
       px ^ bi_n * (if bj_n = 1 then py else 1)) := by
    change
      coeffsOut4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ⟨yIdx7, yIdx7_lt_seven⟩ *
          (let (_, bi, bj) := rrBasis7.getD yIdx7 (0, 0, 0)
           px ^ bi * (if bj = 1 then py else 1)) = _
    have hy_len : yIdx7 < rrBasis7.length := by
      have hlen : rrBasis7.length = 7 := by
        simp [rrBasis7, rrBasisCandidates, List.length_flatMap]
      rw [hlen]; exact yIdx7_lt_seven
    have hy_get : rrBasis7.getD yIdx7 (0, 0, 0) = rrBasis7.getD yIdx7 (0, 1, 1) := by
      rw [List.getD_eq_getElem _ _ hy_len, List.getD_eq_getElem _ _ hy_len]
    rw [hy_get]
  have hsum7 : (∑ col : Fin 6, Fsum (otherMap4 col)) + Fsum ⟨yIdx7, yIdx7_lt_seven⟩ =
      ∑ bidx : Fin 7, Fsum bidx := sum_otherIdx7_add_y p Fsum
  have hmoved' : (∑ col : Fin 6, Fsum (otherMap4 col)) + Fsum ⟨yIdx7, yIdx7_lt_seven⟩ = 0 := by
    calc
      (∑ col : Fin 6, Fsum (otherMap4 col)) + Fsum ⟨yIdx7, yIdx7_lt_seven⟩ =
          (∑ col : Fin 6, coeffsOut4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 (otherMap4 col) *
            (let (px, py) := (px, py)
             let (_, bi, bj) := rrBasis7.getD (otherIdx7.getD col.val 0) (0, 0, 0)
             px ^ bi * (if bj = 1 then py else 1))) +
            coeffsOut4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ⟨yIdx7, yIdx7_lt_seven⟩ *
              (let (px, py) := (px, py)
               let (_, bi_n, bj_n) := rrBasis7.getD yIdx7 (0, 1, 1)
               px ^ bi_n * (if bj_n = 1 then py else 1)) := by
            rw [Finset.sum_congr rfl (fun col _ => hFcol col), hFy]
      _ = 0 := hmoved
  have hsum7' : ∑ bidx : Fin 7, Fsum bidx = 0 := hsum7 ▸ hmoved'
  have hEval : (Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval px +
      py * (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval px = ∑ bidx : Fin 7, Fsum bidx := by
    unfold Epoly4 Ypoly4
    rw [Polynomial.eval_finsetSum, Polynomial.eval_finsetSum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro bidx _
    generalize hget : rrBasis7.getD bidx.val (0, 0, 0) = g
    rcases g with ⟨fst, bi, bj⟩
    have hbj0or1 : bj = 0 ∨ bj = 1 := by
      have hlen : rrBasis7.length = 7 := by
        simp [rrBasis7, rrBasisCandidates, List.length_flatMap]
      have hlt : bidx.val < rrBasis7.length := by rw [hlen]; exact bidx.isLt
      have hflag :
          (rrBasis7.getD bidx.val (0, 0, 0)).2.2 = 0 ∨
            (rrBasis7.getD bidx.val (0, 0, 0)).2.2 = 1 := by
        rw [List.getD_eq_getElem _ _ hlt]
        exact rrBasis7_flag _ (List.getElem_mem hlt)
      rw [hget] at hflag
      exact hflag
    rw [hF_def]
    rcases hbj0or1 with hb0 | hb1
    · subst bj
      simp only [hget]
      norm_num [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
        Polynomial.eval_pow, Polynomial.eval_zero]
      <;> ring
    · subst bj
      simp only [hget]
      norm_num [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
        Polynomial.eval_pow, Polynomial.eval_zero]
      <;> ring
  exact hEval.trans hsum7'

/-- **The seven-slot defining identity for the mod-`u_a` rows** (rows
2–3) — the K=4 analogue of `row23_defining_eq_aux`
(`DataDerivationSolve.lean`), reducing against `(ua0,ua1,va0,va1)` instead
of the target `(u0,u1,v0,v1)`. Same five-step argument as
`row01_defining_eq_aux` above, with `matrixA4_row23_eval`/
`rhsVec4_row23_eval` supplying the row-unfolding step instead of
`matrixA4_row01_eval`/`rhsVec4_row01_eval`. -/
private theorem row23_defining_eq_aux (P1 P2 : F p × F p) (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (hA : MatrixNondegenerate4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) (a : Fin 2) :
    (∑ bidx : Fin 7,
      let (_, bi, bj) := rrBasis7.getD bidx.val (0, 0, 0)
      coeffsOut4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 bidx *
        (let (r0, r1) := reduceMonomialModU p ua0 ua1 va0 va1 bi bj
         if a.val = 0 then r0 else r1)) = 0 := by
  set A := matrixA4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 with hA_def
  set rhs := rhsVec4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 with hrhs_def
  have hdet : A.det ≠ 0 := hA
  have haRow : 2 + a.val < 6 := by omega
  have hmul := Matrix.mulVec_cramer A rhs
  have hrow := congrFun hmul (⟨2 + a.val, haRow⟩ : Fin 6)
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hrow
  have hrow' : ∑ col : Fin 6, A ⟨2 + a.val, haRow⟩ col *
      (A.cramer rhs col / A.det) = rhs ⟨2 + a.val, haRow⟩ := by
    have hstep : (∑ col : Fin 6, A ⟨2 + a.val, haRow⟩ col * (A.cramer rhs col / A.det)) * A.det =
        rhs ⟨2 + a.val, haRow⟩ * A.det := by
      rw [Finset.sum_mul]
      have : ∀ col : Fin 6, A ⟨2 + a.val, haRow⟩ col * (A.cramer rhs col / A.det) * A.det =
          A ⟨2 + a.val, haRow⟩ col * A.cramer rhs col := by
        intro col; field_simp
      simp only [this]
      rw [hrow]; ring
    exact mul_right_cancel₀ hdet hstep
  have hcramerSolution : ∀ col : Fin 6, A.cramer rhs col / A.det =
      cramerSolution4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 col := fun col => rfl
  simp only [hcramerSolution] at hrow'
  have hApply : ∀ col : Fin 6, A ⟨2 + a.val, haRow⟩ col =
      let (_, bi, bj) := rrBasis7.getD (otherIdx7.getD col.val 0) (0, 0, 0)
      let (r0, r1) := reduceMonomialModU p ua0 ua1 va0 va1 bi bj
      if a.val = 0 then r0 else r1 := fun col =>
    matrixA4_row23_eval p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 a col
  have hrhsApply : rhs ⟨2 + a.val, haRow⟩ =
      let (_, bi_n, bj_n) := rrBasis7.getD yIdx7 (0, 1, 1)
      let (rn0, rn1) := reduceMonomialModU p ua0 ua1 va0 va1 bi_n bj_n
      (-(if a.val = 0 then rn0 else rn1)) :=
    rhsVec4_row23_eval p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 a
  clear_value A rhs
  rw [hrhsApply] at hrow'
  have hmoved : (∑ col : Fin 6, coeffsOut4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 (otherMap4 col) *
      (let (_, bi, bj) := rrBasis7.getD (otherIdx7.getD col.val 0) (0, 0, 0)
       let (r0, r1) := reduceMonomialModU p ua0 ua1 va0 va1 bi bj
       if a.val = 0 then r0 else r1)) +
      coeffsOut4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ⟨yIdx7, yIdx7_lt_seven⟩ *
        (let (_, bi_n, bj_n) := rrBasis7.getD yIdx7 (0, 1, 1)
         let (rn0, rn1) := reduceMonomialModU p ua0 ua1 va0 va1 bi_n bj_n
         if a.val = 0 then rn0 else rn1) = 0 := by
    have hcoeffsOutY : coeffsOut4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ⟨yIdx7, yIdx7_lt_seven⟩ = 1 := by
      unfold coeffsOut4; rw [dif_pos rfl]
    rw [hcoeffsOutY, one_mul]
    have hstep : ∑ col : Fin 6, coeffsOut4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 (otherMap4 col) *
        (let (_, bi, bj) := rrBasis7.getD (otherIdx7.getD col.val 0) (0, 0, 0)
         let (r0, r1) := reduceMonomialModU p ua0 ua1 va0 va1 bi bj
         if a.val = 0 then r0 else r1) =
        ∑ col : Fin 6, cramerSolution4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 col *
        (let (_, bi, bj) := rrBasis7.getD (otherIdx7.getD col.val 0) (0, 0, 0)
         let (r0, r1) := reduceMonomialModU p ua0 ua1 va0 va1 bi bj
         if a.val = 0 then r0 else r1) := by
      apply Finset.sum_congr rfl
      intro col _
      rw [coeffsOut4_otherMap p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 col]
    have horder : (∑ col : Fin 6, cramerSolution4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 col *
          (let (_, bi, bj) := rrBasis7.getD (otherIdx7.getD col.val 0) (0, 0, 0)
           let (r0, r1) := reduceMonomialModU p ua0 ua1 va0 va1 bi bj
           if a.val = 0 then r0 else r1))
        = ∑ col : Fin 6, A ⟨2 + a.val, haRow⟩ col *
            cramerSolution4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 col := by
      apply Finset.sum_congr rfl
      intro col _
      rw [mul_comm (cramerSolution4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 col), hApply col]
    rw [hstep, horder, hrow']
    exact neg_add_cancel _
  set Fsum : Fin 7 → F p := fun bidx =>
    coeffsOut4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 bidx *
      (let (_, bi, bj) := rrBasis7.getD bidx.val (0, 0, 0)
       let (r0, r1) := reduceMonomialModU p ua0 ua1 va0 va1 bi bj
       if a.val = 0 then r0 else r1) with hF_def
  have hFcol : ∀ col : Fin 6, Fsum (otherMap4 col) =
      coeffsOut4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 (otherMap4 col) *
      (let (_, bi, bj) := rrBasis7.getD (otherIdx7.getD col.val 0) (0, 0, 0)
       let (r0, r1) := reduceMonomialModU p ua0 ua1 va0 va1 bi bj
       if a.val = 0 then r0 else r1) := by
    intro col
    have hidx : (otherMap4 col).val = otherIdx7.getD col.val 0 := rfl
    simp only [hF_def, hidx]
  have hFy : Fsum (⟨yIdx7, yIdx7_lt_seven⟩ : Fin 7) =
      coeffsOut4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ⟨yIdx7, yIdx7_lt_seven⟩ *
      (let (_, bi_n, bj_n) := rrBasis7.getD yIdx7 (0, 1, 1)
       let (rn0, rn1) := reduceMonomialModU p ua0 ua1 va0 va1 bi_n bj_n
       if a.val = 0 then rn0 else rn1) := by
    have hy_len : yIdx7 < rrBasis7.length := by
      have hlen : rrBasis7.length = 7 := by
        simp [rrBasis7, rrBasisCandidates, List.length_flatMap]
      rw [hlen]; exact yIdx7_lt_seven
    have hy_get : rrBasis7.getD yIdx7 (0, 0, 0) = rrBasis7.getD yIdx7 (0, 1, 1) := by
      rw [List.getD_eq_getElem _ _ hy_len, List.getD_eq_getElem _ _ hy_len]
    simp only [hF_def, hy_get]
  have hsum7 : (∑ col : Fin 6, Fsum (otherMap4 col)) + Fsum ⟨yIdx7, yIdx7_lt_seven⟩ =
      ∑ bidx : Fin 7, Fsum bidx := sum_otherIdx7_add_y p Fsum
  have hmoved' : (∑ col : Fin 6, Fsum (otherMap4 col)) + Fsum ⟨yIdx7, yIdx7_lt_seven⟩ = 0 := by
    calc
      (∑ col : Fin 6, Fsum (otherMap4 col)) + Fsum ⟨yIdx7, yIdx7_lt_seven⟩ =
          (∑ col : Fin 6, coeffsOut4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 (otherMap4 col) *
            (let (_, bi, bj) := rrBasis7.getD (otherIdx7.getD col.val 0) (0, 0, 0)
             let (r0, r1) := reduceMonomialModU p ua0 ua1 va0 va1 bi bj
             if a.val = 0 then r0 else r1)) +
            coeffsOut4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ⟨yIdx7, yIdx7_lt_seven⟩ *
              (let (_, bi_n, bj_n) := rrBasis7.getD yIdx7 (0, 1, 1)
               let (rn0, rn1) := reduceMonomialModU p ua0 ua1 va0 va1 bi_n bj_n
               if a.val = 0 then rn0 else rn1) := by
            rw [Finset.sum_congr rfl (fun col _ => hFcol col), hFy]
      _ = 0 := hmoved
  have hsum7' : ∑ bidx : Fin 7, Fsum bidx = 0 := hsum7 ▸ hmoved'
  rw [hF_def] at hsum7'
  exact hsum7'

/-- **The seven-slot defining identity for the mod-target-`u` rows** (rows
4–5) — the K=4 analogue of `row23_defining_eq_aux` one row-pair further
along, reducing against the ACTUAL target `(u0,u1,v0,v1)` instead of
`(ua0,ua1,va0,va1)`. Identical argument to `row23_defining_eq_aux` above
with the row offset shifted from `2+a.val` to `4+a.val` and
`matrixA4_row45_eval`/`rhsVec4_row45_eval` supplying the row-unfolding
step. -/
private theorem row45_defining_eq_aux (P1 P2 : F p × F p) (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (hA : MatrixNondegenerate4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) (a : Fin 2) :
    (∑ bidx : Fin 7,
      let (_, bi, bj) := rrBasis7.getD bidx.val (0, 0, 0)
      coeffsOut4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 bidx *
        (let (r0, r1) := reduceMonomialModU p u0 u1 v0 v1 bi bj
         if a.val = 0 then r0 else r1)) = 0 := by
  set A := matrixA4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 with hA_def
  set rhs := rhsVec4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 with hrhs_def
  have hdet : A.det ≠ 0 := hA
  have haRow : 4 + a.val < 6 := by omega
  have hmul := Matrix.mulVec_cramer A rhs
  have hrow := congrFun hmul (⟨4 + a.val, haRow⟩ : Fin 6)
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hrow
  have hrow' : ∑ col : Fin 6, A ⟨4 + a.val, haRow⟩ col *
      (A.cramer rhs col / A.det) = rhs ⟨4 + a.val, haRow⟩ := by
    have hstep : (∑ col : Fin 6, A ⟨4 + a.val, haRow⟩ col * (A.cramer rhs col / A.det)) * A.det =
        rhs ⟨4 + a.val, haRow⟩ * A.det := by
      rw [Finset.sum_mul]
      have : ∀ col : Fin 6, A ⟨4 + a.val, haRow⟩ col * (A.cramer rhs col / A.det) * A.det =
          A ⟨4 + a.val, haRow⟩ col * A.cramer rhs col := by
        intro col; field_simp
      simp only [this]
      rw [hrow]; ring
    exact mul_right_cancel₀ hdet hstep
  have hcramerSolution : ∀ col : Fin 6, A.cramer rhs col / A.det =
      cramerSolution4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 col := fun col => rfl
  simp only [hcramerSolution] at hrow'
  have hApply : ∀ col : Fin 6, A ⟨4 + a.val, haRow⟩ col =
      let (_, bi, bj) := rrBasis7.getD (otherIdx7.getD col.val 0) (0, 0, 0)
      let (r0, r1) := reduceMonomialModU p u0 u1 v0 v1 bi bj
      if a.val = 0 then r0 else r1 := fun col =>
    matrixA4_row45_eval p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 a col
  have hrhsApply : rhs ⟨4 + a.val, haRow⟩ =
      let (_, bi_n, bj_n) := rrBasis7.getD yIdx7 (0, 1, 1)
      let (rn0, rn1) := reduceMonomialModU p u0 u1 v0 v1 bi_n bj_n
      (-(if a.val = 0 then rn0 else rn1)) :=
    rhsVec4_row45_eval p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 a
  clear_value A rhs
  rw [hrhsApply] at hrow'
  have hmoved : (∑ col : Fin 6, coeffsOut4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 (otherMap4 col) *
      (let (_, bi, bj) := rrBasis7.getD (otherIdx7.getD col.val 0) (0, 0, 0)
       let (r0, r1) := reduceMonomialModU p u0 u1 v0 v1 bi bj
       if a.val = 0 then r0 else r1)) +
      coeffsOut4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ⟨yIdx7, yIdx7_lt_seven⟩ *
        (let (_, bi_n, bj_n) := rrBasis7.getD yIdx7 (0, 1, 1)
         let (rn0, rn1) := reduceMonomialModU p u0 u1 v0 v1 bi_n bj_n
         if a.val = 0 then rn0 else rn1) = 0 := by
    have hcoeffsOutY : coeffsOut4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ⟨yIdx7, yIdx7_lt_seven⟩ = 1 := by
      unfold coeffsOut4; rw [dif_pos rfl]
    rw [hcoeffsOutY, one_mul]
    have hstep : ∑ col : Fin 6, coeffsOut4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 (otherMap4 col) *
        (let (_, bi, bj) := rrBasis7.getD (otherIdx7.getD col.val 0) (0, 0, 0)
         let (r0, r1) := reduceMonomialModU p u0 u1 v0 v1 bi bj
         if a.val = 0 then r0 else r1) =
        ∑ col : Fin 6, cramerSolution4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 col *
        (let (_, bi, bj) := rrBasis7.getD (otherIdx7.getD col.val 0) (0, 0, 0)
         let (r0, r1) := reduceMonomialModU p u0 u1 v0 v1 bi bj
         if a.val = 0 then r0 else r1) := by
      apply Finset.sum_congr rfl
      intro col _
      rw [coeffsOut4_otherMap p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 col]
    have horder : (∑ col : Fin 6, cramerSolution4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 col *
          (let (_, bi, bj) := rrBasis7.getD (otherIdx7.getD col.val 0) (0, 0, 0)
           let (r0, r1) := reduceMonomialModU p u0 u1 v0 v1 bi bj
           if a.val = 0 then r0 else r1))
        = ∑ col : Fin 6, A ⟨4 + a.val, haRow⟩ col *
            cramerSolution4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 col := by
      apply Finset.sum_congr rfl
      intro col _
      rw [mul_comm (cramerSolution4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 col), hApply col]
    rw [hstep, horder, hrow']
    exact neg_add_cancel _
  set Fsum : Fin 7 → F p := fun bidx =>
    coeffsOut4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 bidx *
      (let (_, bi, bj) := rrBasis7.getD bidx.val (0, 0, 0)
       let (r0, r1) := reduceMonomialModU p u0 u1 v0 v1 bi bj
       if a.val = 0 then r0 else r1) with hF_def
  have hFcol : ∀ col : Fin 6, Fsum (otherMap4 col) =
      coeffsOut4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 (otherMap4 col) *
      (let (_, bi, bj) := rrBasis7.getD (otherIdx7.getD col.val 0) (0, 0, 0)
       let (r0, r1) := reduceMonomialModU p u0 u1 v0 v1 bi bj
       if a.val = 0 then r0 else r1) := by
    intro col
    have hidx : (otherMap4 col).val = otherIdx7.getD col.val 0 := rfl
    simp only [hF_def, hidx]
  have hFy : Fsum (⟨yIdx7, yIdx7_lt_seven⟩ : Fin 7) =
      coeffsOut4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ⟨yIdx7, yIdx7_lt_seven⟩ *
      (let (_, bi_n, bj_n) := rrBasis7.getD yIdx7 (0, 1, 1)
       let (rn0, rn1) := reduceMonomialModU p u0 u1 v0 v1 bi_n bj_n
       if a.val = 0 then rn0 else rn1) := by
    have hy_len : yIdx7 < rrBasis7.length := by
      have hlen : rrBasis7.length = 7 := by
        simp [rrBasis7, rrBasisCandidates, List.length_flatMap]
      rw [hlen]; exact yIdx7_lt_seven
    have hy_get : rrBasis7.getD yIdx7 (0, 0, 0) = rrBasis7.getD yIdx7 (0, 1, 1) := by
      rw [List.getD_eq_getElem _ _ hy_len, List.getD_eq_getElem _ _ hy_len]
    simp only [hF_def, hy_get]
  have hsum7 : (∑ col : Fin 6, Fsum (otherMap4 col)) + Fsum ⟨yIdx7, yIdx7_lt_seven⟩ =
      ∑ bidx : Fin 7, Fsum bidx := sum_otherIdx7_add_y p Fsum
  have hmoved' : (∑ col : Fin 6, Fsum (otherMap4 col)) + Fsum ⟨yIdx7, yIdx7_lt_seven⟩ = 0 := by
    calc
      (∑ col : Fin 6, Fsum (otherMap4 col)) + Fsum ⟨yIdx7, yIdx7_lt_seven⟩ =
          (∑ col : Fin 6, coeffsOut4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 (otherMap4 col) *
            (let (_, bi, bj) := rrBasis7.getD (otherIdx7.getD col.val 0) (0, 0, 0)
             let (r0, r1) := reduceMonomialModU p u0 u1 v0 v1 bi bj
             if a.val = 0 then r0 else r1)) +
            coeffsOut4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ⟨yIdx7, yIdx7_lt_seven⟩ *
              (let (_, bi_n, bj_n) := rrBasis7.getD yIdx7 (0, 1, 1)
               let (rn0, rn1) := reduceMonomialModU p u0 u1 v0 v1 bi_n bj_n
               if a.val = 0 then rn0 else rn1) := by
            rw [Finset.sum_congr rfl (fun col _ => hFcol col), hFy]
      _ = 0 := hmoved
  have hsum7' : ∑ bidx : Fin 7, Fsum bidx = 0 := hsum7 ▸ hmoved'
  rw [hF_def] at hsum7'
  exact hsum7'

/-- `N(x) = E(x)² - f(x)*Y(x)²` for the K=4 instance — mirrors `Npoly`
exactly, using the SAME `curvePoly` (`DataDerivationBasics.lean`, plain
`F p`-valued, no tower promotion needed here since everything already
lives in `F p`). -/
noncomputable def Npoly4 (P1 P2 : F p × F p) (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p) :
    Polynomial (F p) :=
  Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ^ 2 -
    curvePoly p c0 c1 c2 c3 c4 * Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ^ 2

/-- The quotient `N(x) / ((x-P1.x)(x-P2.x)(x²+ua1*x+ua0)(x²+u1*x+u0))` —
the K=4 analogue of `curBeforeMonic`, dividing out BOTH known quadratics
(`u_a` and the target `u`) directly rather than by literal roots, per this
file's module docstring ("the `u_a` split-vs-irreducible fork" section).
Stated unconditionally via `/ₘ` (always defined), correctness deferred to
wherever this is used against the analogues of `dvd_N_anchor1`/
`dvd_N_anchor2`/`dvd_N_u` — **none of those three divisibility facts are
proved for this K=4 instance yet**, left for the next pass exactly as
flagged in the module docstring. -/
noncomputable def curBeforeMonic4 (P1 P2 : F p × F p) (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p) :
    Polynomial (F p) :=
  (((Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 /ₘ (X - C P1.1))
      /ₘ (X - C P2.1))
    /ₘ (X ^ 2 + C ua1 * X + C ua0))
    /ₘ (X ^ 2 + C u1 * X + C u0)

/-! ## The four K=4 divisibility facts

Direct rescaling of `dvd_N_anchor1`/`dvd_N_anchor2`/`dvd_E_add_Y_mul_v`/
`dvd_N_u` (`DataDerivationSolve.lean`) using the three row-identity
theorems above. Two genuine (unavoidable) new hypotheses appear that have
no K=2 analogue: `P1`/`P2` here are plain `F p × F p` pairs (not tower-
adjoined roots the way `anchor1`/`anchor2` are, since this file works
directly over `F p` with no field extension — see the module docstring),
so "`P1`/`P2` actually lie on the curve" is not automatic and has to be
supplied as an explicit hypothesis (`hP1_curve`/`hP2_curve`), exactly the
same honest-hypothesis convention `IsMumfordTarget` already uses for the
target `(u0,u1,v0,v1)` below — not a shortcut, a genuine precondition on
the sample data (whoever supplies `P1,P2` has to supply actual curve
points). -/

/-- `(X - P1.1)` divides `N(x)`, K=4 instance — the `a=0` case of
`row01_defining_eq_aux` combined with the curve relation
`P1.2^2 = f(P1.1)`, same algebraic shape as `dvd_N_anchor1`. -/
theorem dvd_N_P1 (P1 P2 : F p × F p) (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (hA : MatrixNondegenerate4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hP1_curve : P1.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P1.1) :
    (X - C P1.1) ∣ Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 := by
  unfold Npoly4
  rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_mul, Polynomial.eval_pow]
  have hE := row01_defining_eq_aux p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hA ⟨0, by norm_num⟩
  have hEeq : (Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval P1.1 =
      -(P1.2 * (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval P1.1) := by
    simpa using (eq_neg_of_add_eq_zero_left hE)
  rw [hEeq, neg_sq, mul_pow, hP1_curve]
  ring

/-- `(X - P2.1)` divides `N(x)`, K=4 instance — the `a=1` analogue. -/
theorem dvd_N_P2 (P1 P2 : F p × F p) (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (hA : MatrixNondegenerate4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hP2_curve : P2.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P2.1) :
    (X - C P2.1) ∣ Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 := by
  unfold Npoly4
  rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_mul, Polynomial.eval_pow]
  have hE := row01_defining_eq_aux p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hA ⟨1, by norm_num⟩
  have hEeq : (Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval P2.1 =
      -(P2.2 * (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval P2.1) := by
    simpa using (eq_neg_of_add_eq_zero_left hE)
  rw [hEeq, neg_sq, mul_pow, hP2_curve]
  ring

/-- **The `u_a` Mumford hypothesis**: `v_a(x) = va1*X+va0` squares to
`f(x)` modulo `u_a(x) = X²+ua1*X+ua0` — the geometric condition making
`(u_a,v_a)` an actual Mumford representative of `alpha • a`'s own two
roots. Mirrors `IsMumfordTarget` exactly, applied to `u_a` instead of the
final target `u`. -/
def IsMumfordUa (ua0 ua1 va0 va1 : F p) : Prop :=
  (X ^ 2 + C ua1 * X + C ua0) ∣
    ((C va1 * X + C va0) ^ 2 - curvePoly p c0 c1 c2 c3 c4)

/-- **The target Mumford hypothesis, K=4 instance** — mirrors
`IsMumfordTarget` exactly, over plain `F p` (no `K2` promotion needed). -/
def IsMumfordTarget4 (u0 u1 v0 v1 : F p) : Prop :=
  (X ^ 2 + C u1 * X + C u0) ∣
    ((C v1 * X + C v0) ^ 2 - curvePoly p c0 c1 c2 c3 c4)

/-- **Bridge from the two `row23`/`row45`-style coefficient identities to
divisibility** — the K=4, plain-`F p` analogue of `dvd_E_add_Y_mul_v`'s
`hRsum`/`hRmod`/final-`xmodUTable_correct` argument, factored out so both
`dvd_N_ua` and `dvd_N_u4` can call it against their own `(tu0,tu1,tv0,tv1)`
quadratic. No `algebraMap`/tower promotion is needed here (unlike the K=2
version): everything already lives in `F p`. The hypothesis shape matches
exactly what `row23_defining_eq_aux hA ⟨0,_⟩` / `⟨1,_⟩` (or the `row45`
analogues) produce: for `a = 0, 1`, the sum over `bidx : Fin 7` of
`coeffsOut4 bidx * (reduceMonomialModU tu0 tu1 tv0 tv1 bi bj).{1,2}` (picked
by `a`) vanishes. -/
private theorem dvd_of_row_identity4 (P1 P2 : F p × F p) (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (tu0 tu1 tv0 tv1 : F p)
    (hrow : ∀ a : Fin 2, (∑ bidx : Fin 7,
        let (_, bi, bj) := rrBasis7.getD bidx.val (0, 0, 0)
        coeffsOut4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 bidx *
          (let (r0, r1) := reduceMonomialModU p tu0 tu1 tv0 tv1 bi bj
           if a.val = 0 then r0 else r1)) = 0) :
    (X ^ 2 + C tu1 * X + C tu0) ∣
      (Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 +
        Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 * (C tv1 * X + C tv0)) := by
  set U : Polynomial (F p) := X ^ 2 + C tu1 * X + C tu0 with hU_def
  have hUmonic : U.Monic := by rw [hU_def]; exact uPoly_monic p tu0 tu1
  rw [← Polynomial.modByMonic_eq_zero_iff_dvd hUmonic]
  set R : Polynomial (F p) :=
      Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 +
        Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 * (C tv1 * X + C tv0) with hR_def
  -- `R` as a single sum over `bidx : Fin 7`, mirroring `Epoly4`/`Ypoly4`'s
  -- own `∑ bidx, if bj = 0/1 then ... else 0` definitions merged with the
  -- `(tv1*X+tv0)` factor distributed in.
  have hRsum : R = ∑ bidx : Fin 7,
      let (_, bi, bj) := rrBasis7.getD bidx.val (0, 0, 0)
      if bj = 0 then C (coeffsOut4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 bidx) * X ^ bi
      else C (coeffsOut4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 bidx) * X ^ bi *
        (C tv1 * X + C tv0) := by
    rw [hR_def]
    unfold Epoly4 Ypoly4
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro bidx _
    have hbj0or1 : (rrBasis7.getD bidx.val (0, 0, 0)).2.2 = 0 ∨
        (rrBasis7.getD bidx.val (0, 0, 0)).2.2 = 1 := by
      have hlen : rrBasis7.length = 7 := by
        simp [rrBasis7, rrBasisCandidates, List.length_flatMap]
      have hlt : bidx.val < rrBasis7.length := by rw [hlen]; exact bidx.isLt
      rw [List.getD_eq_getElem _ _ hlt]
      exact rrBasis7_flag _ (List.getElem_mem hlt)
    rcases hbj0or1 with hb0 | hb1
    · have hb1' : (rrBasis7.getD bidx.val (0, 0, 0)).2.2 ≠ 1 := by omega
      simp only [if_pos hb0, if_neg hb1']
      ring
    · have hb0' : (rrBasis7.getD bidx.val (0, 0, 0)).2.2 ≠ 0 := by omega
      simp only [if_neg hb0', if_pos hb1]
      ring
  -- `%ₘ U` is linear, so distributes over the 7-term sum.
  have hRmod : R %ₘ U = ∑ bidx : Fin 7,
      (let (_, bi, bj) := rrBasis7.getD bidx.val (0, 0, 0)
       if bj = 0 then C (coeffsOut4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 bidx) * X ^ bi
       else C (coeffsOut4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 bidx) * X ^ bi *
         (C tv1 * X + C tv0)) %ₘ U := by
    rw [hRsum, ← Polynomial.modByMonicHom_apply,
      map_sum U.modByMonicHom
        (fun bidx : Fin 7 =>
          let (_, bi, bj) := rrBasis7.getD bidx.val (0, 0, 0)
          if bj = 0 then C (coeffsOut4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 bidx) * X ^ bi
          else C (coeffsOut4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 bidx) * X ^ bi *
            (C tv1 * X + C tv0))
        Finset.univ]
    simp only [Polynomial.modByMonicHom_apply]
  -- `%ₘ U` commutes with the `F p`-scalar action `c • q = C c * q`
  -- (`modByMonicHom` is `F p`-linear), the confirmed pattern from
  -- `dvd_E_add_Y_mul_v` (`DataDerivationSolve.lean`).
  have hsmulC : ∀ (c : F p) (q : Polynomial (F p)), c • q = C c * q :=
    fun c _ => Polynomial.smul_eq_C_mul c
  -- `%ₘ U` is additive and commutes with `C c * ·`, packaged as standalone
  -- one-line facts (rather than chained inline) so the two branches below
  -- don't need to track `%ₘ`/`modByMonicHom`-bundled-form back-and-forth.
  have hmod_add : ∀ q r : Polynomial (F p), (q + r) %ₘ U = q %ₘ U + r %ₘ U := by
    intro q r
    rw [← Polynomial.modByMonicHom_apply, ← Polynomial.modByMonicHom_apply,
      ← Polynomial.modByMonicHom_apply, map_add]
  have hmod_Cmul : ∀ (c : F p) (q : Polynomial (F p)), (C c * q) %ₘ U = C c * (q %ₘ U) := by
    intro c q
    rw [← hsmulC, ← Polynomial.modByMonicHom_apply, ← Polynomial.modByMonicHom_apply, map_smul,
      hsmulC]
  -- Each term's `%ₘ U`, via `xmodUTable_correct` at `bi`/`bi+1`, is exactly
  -- what `reduceMonomialModU tu0 tu1 tv0 tv1 bi bj` returns.
  have hterm : ∀ bidx : Fin 7,
      (let (_, bi, bj) := rrBasis7.getD bidx.val (0, 0, 0)
       if bj = 0 then C (coeffsOut4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 bidx) * X ^ bi
       else C (coeffsOut4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 bidx) * X ^ bi *
          (C tv1 * X + C tv0)) %ₘ U =
       let (_, bi, bj) := rrBasis7.getD bidx.val (0, 0, 0)
       let (r0, r1) := reduceMonomialModU p tu0 tu1 tv0 tv1 bi bj
       C (coeffsOut4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 bidx) * (C r0 + C r1 * X) := by
    intro bidx
    generalize hget : rrBasis7.getD bidx.val (0, 0, 0) = g
    rcases g with ⟨fst, bi, bj⟩
    have hbj0or1 : bj = 0 ∨ bj = 1 := by
      have hlen : rrBasis7.length = 7 := by
        simp [rrBasis7, rrBasisCandidates, List.length_flatMap]
      have hlt : bidx.val < rrBasis7.length := by rw [hlen]; exact bidx.isLt
      have hflag :
          (rrBasis7.getD bidx.val (0, 0, 0)).2.2 = 0 ∨
            (rrBasis7.getD bidx.val (0, 0, 0)).2.2 = 1 := by
        rw [List.getD_eq_getElem _ _ hlt]
        exact rrBasis7_flag _ (List.getElem_mem hlt)
      rw [hget] at hflag
      exact hflag
    generalize hc_def' : coeffsOut4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 bidx = c
    rcases hbj0or1 with hb0 | hb1
    · subst bj
      have hpow :
          X ^ bi %ₘ U =
            C (xmodUTable p tu0 tu1 bi).1 + C (xmodUTable p tu0 tu1 bi).2 * X := by
        simpa [hU_def] using xmodUTable_correct p tu0 tu1 bi
      calc
        (C c * X ^ bi) %ₘ U = C c * (X ^ bi %ₘ U) := hmod_Cmul c _
        _ = C c *
            (C (xmodUTable p tu0 tu1 bi).1 + C (xmodUTable p tu0 tu1 bi).2 * X) := by
          rw [hpow]
        _ = C c *
            (C (reduceMonomialModU p tu0 tu1 tv0 tv1 bi 0).1 +
              C (reduceMonomialModU p tu0 tu1 tv0 tv1 bi 0).2 * X) := by
          rfl
    · subst bj
      have hXmul : (C c * X ^ bi : Polynomial (F p)) * (C tv1 * X + C tv0) =
          C c * (C tv1 * X ^ (bi + 1)) + C c * (C tv0 * X ^ bi) := by ring
      have hpow_succ :
          X ^ (bi + 1) %ₘ U =
            C (xmodUTable p tu0 tu1 (bi + 1)).1 +
              C (xmodUTable p tu0 tu1 (bi + 1)).2 * X := by
        simpa [hU_def] using xmodUTable_correct p tu0 tu1 (bi + 1)
      have hpow :
          X ^ bi %ₘ U =
            C (xmodUTable p tu0 tu1 bi).1 + C (xmodUTable p tu0 tu1 bi).2 * X := by
        simpa [hU_def] using xmodUTable_correct p tu0 tu1 bi
      calc
        (C c * X ^ bi * (C tv1 * X + C tv0)) %ₘ U =
            (C c * (C tv1 * X ^ (bi + 1)) + C c * (C tv0 * X ^ bi)) %ₘ U := by
          rw [hXmul]
        _ = (C c * (C tv1 * X ^ (bi + 1))) %ₘ U +
              (C c * (C tv0 * X ^ bi)) %ₘ U := hmod_add _ _
        _ = C c * (C tv1 * (X ^ (bi + 1) %ₘ U)) +
              C c * (C tv0 * (X ^ bi %ₘ U)) := by
          have h1 := hmod_Cmul c (C tv1 * X ^ (bi + 1))
          have h1' := hmod_Cmul tv1 (X ^ (bi + 1))
          have h2 := hmod_Cmul c (C tv0 * X ^ bi)
          have h2' := hmod_Cmul tv0 (X ^ bi)
          rw [h1, h1', h2, h2']
        _ = C c * (C tv1 * (C (xmodUTable p tu0 tu1 (bi + 1)).1 +
              C (xmodUTable p tu0 tu1 (bi + 1)).2 * X)) +
              C c * (C tv0 * (C (xmodUTable p tu0 tu1 bi).1 +
                C (xmodUTable p tu0 tu1 bi).2 * X)) := by
          rw [hpow_succ, hpow]
        _ = C c *
              (C (reduceMonomialModU p tu0 tu1 tv0 tv1 bi 1).1 +
                C (reduceMonomialModU p tu0 tu1 tv0 tv1 bi 1).2 * X) := by
          have hcomm : bi + 1 = 1 + bi := Nat.add_comm bi 1
          simp only [reduceMonomialModU, xmodUTable, if_neg (one_ne_zero (α := ℕ)),
            map_add, map_mul, ← hcomm]
          ring
  have hrow0 := hrow ⟨0, by norm_num⟩
  have hrow1 := hrow ⟨1, by norm_num⟩
  simp at hrow0
  simp at hrow1
  have hrow0' : (∑ bidx : Fin 7,
      let (_, bi, bj) := rrBasis7.getD bidx.val (0, 0, 0)
      coeffsOut4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 bidx *
        (let (r0, _) := reduceMonomialModU p tu0 tu1 tv0 tv1 bi bj; r0)) = 0 := hrow0
  have hrow1' : (∑ bidx : Fin 7,
      let (_, bi, bj) := rrBasis7.getD bidx.val (0, 0, 0)
      coeffsOut4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 bidx *
        (let (_, r1) := reduceMonomialModU p tu0 tu1 tv0 tv1 bi bj; r1)) = 0 := hrow1
  have hRmodsum : R %ₘ U = ∑ bidx : Fin 7,
      let (_, bi, bj) := rrBasis7.getD bidx.val (0, 0, 0)
      let (r0, r1) := reduceMonomialModU p tu0 tu1 tv0 tv1 bi bj
      C (coeffsOut4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 bidx) * (C r0 + C r1 * X) := by
    rw [hRmod]; exact Finset.sum_congr rfl (fun bidx _ => hterm bidx)
  rw [hRmodsum]
  -- Split each summand `C coeff * (C r0 + C r1 * X)` into its `r0`-part and
  -- `r1`-part, then regroup via `Finset.sum_add_distrib` so the whole sum
  -- becomes `C (Σ coeff*r0) + C (Σ coeff*r1) * X` — at which point `hrow0`/
  -- `hrow1` (both `= 0`) finish it.
  have hsplit : (∑ bidx : Fin 7,
      let (_, bi, bj) := rrBasis7.getD bidx.val (0, 0, 0)
      let (r0, r1) := reduceMonomialModU p tu0 tu1 tv0 tv1 bi bj
      C (coeffsOut4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 bidx) * (C r0 + C r1 * X)) =
      (∑ bidx : Fin 7,
          let (_, bi, bj) := rrBasis7.getD bidx.val (0, 0, 0)
          C (coeffsOut4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 bidx *
            (let (r0, _) := reduceMonomialModU p tu0 tu1 tv0 tv1 bi bj; r0))) +
      (∑ bidx : Fin 7,
          let (_, bi, bj) := rrBasis7.getD bidx.val (0, 0, 0)
          C (coeffsOut4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 bidx *
            (let (_, r1) := reduceMonomialModU p tu0 tu1 tv0 tv1 bi bj; r1))) * X := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro bidx _
    obtain ⟨_, bi, bj⟩ := rrBasis7.getD bidx.val (0, 0, 0)
    obtain ⟨r0, r1⟩ := reduceMonomialModU p tu0 tu1 tv0 tv1 bi bj
    simp only [map_mul]
    ring
  rw [hsplit, ← map_sum, ← map_sum, hrow0', hrow1']
  simp

/-- `u_a(x) = X²+ua1*X+ua0` divides `N(x)` — combines `row23_defining_eq_aux`
(`u_a ∣ E + Y*(va1*X+va0)`, the two mod-`u_a` rows) with `IsMumfordUa`
(`u_a ∣ v_a² - f`) via the same `N = (E-Yv)(E+Yv) + (v²-f)Y²` identity
`dvd_N_u` uses. -/
theorem dvd_N_ua (P1 P2 : F p × F p) (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (hA : MatrixNondegenerate4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hMumfordUa : IsMumfordUa p c0 c1 c2 c3 c4 ua0 ua1 va0 va1) :
    (X ^ 2 + C ua1 * X + C ua0) ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 := by
  have huY : (X ^ 2 + C ua1 * X + C ua0) ∣
      (Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 +
        Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 * (C va1 * X + C va0)) :=
    dvd_of_row_identity4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ua0 ua1 va0 va1
      (fun a => row23_defining_eq_aux p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hA a)
  have hVF : (X ^ 2 + C ua1 * X + C ua0) ∣
      ((C va1 * X + C va0) ^ 2 - curvePoly p c0 c1 c2 c3 c4) := hMumfordUa
  set E := Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1
  set Y := Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1
  set V : Polynomial (F p) := C va1 * X + C va0
  set f := curvePoly p c0 c1 c2 c3 c4
  have h1 : (X ^ 2 + C ua1 * X + C ua0) ∣ (E - Y * V) * (E + Y * V) :=
    dvd_mul_of_dvd_right huY (E - Y * V)
  have h2 : (X ^ 2 + C ua1 * X + C ua0) ∣ (V ^ 2 - f) * Y ^ 2 := dvd_mul_of_dvd_left hVF (Y ^ 2)
  have hadd : (X ^ 2 + C ua1 * X + C ua0) ∣
      (E - Y * V) * (E + Y * V) + (V ^ 2 - f) * Y ^ 2 := dvd_add h1 h2
  have hNeq : Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 =
      (E - Y * V) * (E + Y * V) + (V ^ 2 - f) * Y ^ 2 := by
    unfold Npoly4; ring
  rw [hNeq]; exact hadd

/-- `u(x) = X²+u1*X+u0` (the actual target) divides `N(x)` — the `row45`
analogue of `dvd_N_ua`, using `IsMumfordTarget4` in place of `IsMumfordUa`. -/
theorem dvd_N_u4 (P1 P2 : F p × F p) (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (hA : MatrixNondegenerate4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hMumfordTarget : IsMumfordTarget4 p c0 c1 c2 c3 c4 u0 u1 v0 v1) :
    (X ^ 2 + C u1 * X + C u0) ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 := by
  have huY : (X ^ 2 + C u1 * X + C u0) ∣
      (Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 +
        Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 * (C v1 * X + C v0)) :=
    dvd_of_row_identity4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 u0 u1 v0 v1
      (fun a => row45_defining_eq_aux p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hA a)
  have hVF : (X ^ 2 + C u1 * X + C u0) ∣
      ((C v1 * X + C v0) ^ 2 - curvePoly p c0 c1 c2 c3 c4) := hMumfordTarget
  set E := Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1
  set Y := Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1
  set V : Polynomial (F p) := C v1 * X + C v0
  set f := curvePoly p c0 c1 c2 c3 c4
  have h1 : (X ^ 2 + C u1 * X + C u0) ∣ (E - Y * V) * (E + Y * V) :=
    dvd_mul_of_dvd_right huY (E - Y * V)
  have h2 : (X ^ 2 + C u1 * X + C u0) ∣ (V ^ 2 - f) * Y ^ 2 := dvd_mul_of_dvd_left hVF (Y ^ 2)
  have hadd : (X ^ 2 + C u1 * X + C u0) ∣
      (E - Y * V) * (E + Y * V) + (V ^ 2 - f) * Y ^ 2 := dvd_add h1 h2
  have hNeq : Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 =
      (E - Y * V) * (E + Y * V) + (V ^ 2 - f) * Y ^ 2 := by
    unfold Npoly4; ring
  rw [hNeq]; exact hadd

end TheDataDerivation
end Genus2Lean
