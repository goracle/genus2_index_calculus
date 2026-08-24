import Mathlib
import Genus2Lean.TheDataDerivation.DataDerivationBasics

/-! Numbered revision 7: fixes the yIdx7 optional-list RHS reduction and
    normalizes the tangent derivative summands after the basis match. -/
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
`F p × F p × F p × F p` signature `AlphaLocusDegreeUniform.lean` needs.

**Update (later pass): `uRS4`/`vRS4` ARE built** — the paragraph above was
stale. `uRS4` (monic normalization of `curBeforeMonic4`), `uRS4_monic`,
`uRS4_natDegree_le_two`, and `vRS4` (`-E4*Y4⁻¹ mod uRS4` via
`EuclideanDomain.gcdA`) are all defined/proved, `sorry`-free, mirroring
`DataDerivationMumford.lean`'s `uRS`/`uRS_monic`/`vRS` exactly. The Mumford
identity itself, `vRS4_sq_eq_f_mod_uRS4` (`v_RS4² ≡ curvePoly mod u_RS4`),
is also now ported, direct port of `vRS_sq_eq_f_mod_uRS`'s generic
`sq_mod_eq_of_dvd` chain (ring-generic, no changes needed) plus a K=4
wrapper. **Still genuinely not started, and still the real gap**: (1)
`uRS4 ∣ Npoly4` as a single combined fact — `dvd_N_P1`/`dvd_N_P2`/
`dvd_N_ua`/`dvd_N_u4` prove divisibility by each factor separately, but no
theorem here (or in `DataDerivationSolve.lean`'s K=2 analogue, which has
the identical gap) combines them into `uRS4 ∣ Npoly4` itself — this is
exactly the hypothesis `vRS4_sq_eq_f_mod_uRS4`'s `hNu` still has to assume
rather than derive; routed to a ChatGPT consultation this pass
(`chatgpt_prompt_uRS4_dvd_Npoly4.md`, not yet sent/answered), since it
needs pairwise-coprimality genericity hypotheses this file doesn't yet
have a clean Lean statement for. (2) **`Reduce` itself is now defined**
(packaging `uRS4`/`vRS4`'s coefficients into an `F p × F p × F p × F p`
tuple, given the input target it reduces against) — but its CORRECTNESS
(that it actually computes the Mumford reduction of `alpha•a - P1 - P2`)
is not proved and depends on (1).

**This pass**: the two `sorry`s in `Ypoly4_natDegree_le_one`/
`Epoly4_natDegree_le_four` (the `hbi1`/`hbi4` inner `have`s, previously
routed to a drafted-but-unsent ChatGPT consultation,
`chatgpt_prompt_mergesort_decide.md`) are now attempted directly rather
than deferred: both goals are about `rrBasis7.getD bidx.val (0,0,0)` for
`bidx : Fin 7`, and `rrBasis7_eq` (already proved, above) gives
`rrBasis7`'s literal 7-element list value via the `Perm`+`Sorted`-
uniqueness route — which never asks the kernel to unfold `mergeSort`, so
it sidesteps the WF-recursion/kernel-irreducibility blocker
(lean4#5192) that made bare `decide` fail on `rrBasis7` directly. Fix:
`rw [rrBasis7_eq]` first (turning the goal into a lookup into a literal
list), then `fin_cases bidx <;> decide` (seven concrete, ordinary
`Nat`-arithmetic goals) — **`interval_cases bidx` was tried first and
confirmed by Claire's REPL to fail** (`unsupported type Fin 7`;
`interval_cases` wants a type with an order/bound instance it can search
for, not `Fin n` directly — `fin_cases` is the tactic actually meant for
finite-type case splits and is the fix now in place, not yet re-tested).
The K=2 analogue this file's earlier note flagged
as sharing "the exact same latent bug" (`Epoly_natDegree_le_three`,
`DecoupledSystemRegular.lean`) was NOT touched this pass — confirmed via
fresh `sorry`-grep that file is genuinely 0-`sorry` already, so whatever
that file does at the analogous step evidently isn't hitting this same
blocker (or was already fixed); worth a quick diff-read next pass rather
than assuming it needs the identical fix.

**Confirmed against Claire's REPL (later pass): this whole file compiles
clean, 0 errors, 0 `sorry`.** Two Taylor-shift argument-order bugs in
`comp_X_add_C_coeff_one`/`comp_X_add_C_coeff_zero` (`Polynomial.taylor_coeff`
takes only `n` explicitly — `r`/`f` are section variables, not positional
arguments — so the calls needed `(r := t) (f := f)` named rather than `1 f`/
`0 f` positional) were the only real build blockers; fixed and confirmed.

**Update (this pass): the "Same open gap as upstream" note below is now
STALE for this file — `uRS4_dvd_Npoly4` genuinely closes the four-factor
combining gap** (via the six explicit pairwise-coprimality hypotheses,
`prod_dvd_of_pairwise_coprime_four` + the `/ₘ`-peeling chain matching
`curBeforeMonic4`'s own left-to-right factor order) — it was already fully
written and, per the compile confirmation above, builds. What was NOT yet
done, until this pass: `vRS4_sq_eq_f_mod_uRS4` still took `hNu` as its OWN
separate raw hypothesis rather than deriving it from `uRS4_dvd_Npoly4` —
redundant duplication of exactly the fact `uRS4_dvd_Npoly4` already proves.
Fixed this pass: `vRS4_sq_eq_f_mod_uRS4` now takes `uRS4_dvd_Npoly4`'s own
hypothesis bundle (`hA`/curve-membership/Mumford/six-coprimality) instead
of a bare `hNu`, and derives `hNu` internally via one application of
`uRS4_dvd_Npoly4` plus `unfold Npoly4` (definitional match against
`E^2 - f*Y^2`). `hInv` (the `Y`,`uRS4` coprimality Bézout-witness fact) is
UNCHANGED, still a raw hypothesis — it is not implied by the four-factor
combining and is genuinely separate content (this file's own docstring on
`uRS4`/`vRS4` already makes this `hInv`-vs-`hgcd` distinction explicitly).
**Not yet tested against Claire's REPL** — written and reasoned through
(the `unfold_let`/`unfold Npoly4 at` step mirrors this file's existing
`unfold Npoly4`-then-`rw [dvd_iff_isRoot, ...]` idiom used throughout
`dvd_N_P1`/`dvd_N_P2` above, so no new tactic idiom introduced), but not
yet compiled.

**What's left in this file, accurately, after this pass** (superseding all
earlier "not yet started"/"still open" language above, which described an
earlier state): (1) `Reduce`'s CORRECTNESS — that `Reduce`'s output really
is the Mumford reduction of `alpha•a - P1 - P2` — is the one substantial
piece of remaining mathematical content; `Reduce` itself is fully defined
and its underlying `uRS4`/`vRS4` machinery is now fully wired
(`uRS4_dvd_Npoly4` combining + `vRS4_sq_eq_f_mod_uRS4` Mumford identity,
both `sorry`-free), so this is a genuinely new theorem to state and prove,
not a missing definition. (2) The `IsMumfordUa`/`IsMumfordTarget4`/
`MatrixNondegenerate4`/six-coprimality hypothesis bundle `uRS4_dvd_Npoly4`
and `vRS4_sq_eq_f_mod_uRS4` both now require is exactly task (B)'s `Bad`
exceptional-locus question from `ROADMAP-alpha-locus.md` — nothing here
derives those hypotheses from a smaller/cheaper genericity condition, they
are assumed throughout, matching this file's "hypotheses instead of proof"
convention. (3) The tangent-anchor (`m=2`, `P1=P2` or other pairwise
coincidence) case flagged extensively in `ROADMAP-alpha-locus.md`'s
"K=4 recipe" section is still fully unstarted in this file — everything
above is the SIMPLE-point case only (`h12`'s `IsCoprime (X-C P1.1) (X-C
P2.1)` hypothesis already presupposes `P1.1 ≠ P2.1`, i.e. rules the
tangent case out by hypothesis rather than handling it). -/

namespace Genus2Lean
namespace TheDataDerivation

open Polynomial

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-! ## RR basis, `nb = K+3 = 7` for `K=4` -/

/-- `rrBasisCandidates 20`'s literal value — pure `List.range`/`flatMap`
computation, NO `mergeSort` involved, so `decide` genuinely works here
(unlike anything downstream that touches `rrBasis7` itself). Needed as the
computational anchor for `rrBasis7_eq` below, per the "prove `Perm` +
`Sorted` against a literal list, not kernel-compute `mergeSort`" strategy
(ChatGPT consultation, `chatgpt_prompt_mergesort_decide.md` — ordinary
`simp [List.mergeSort]` genuinely cannot evaluate `mergeSort` since its
correctness lemmas are marked `@[irreducible]` by design; `decide`/`rfl`
through `mergeSort` itself hits Lean 4.19+'s WF-recursion
kernel-irreducibility, RFC lean4#5192). `22 = 2 * (20/2+1) = 2*11`
elements, `List.range 11 |>.flatMap (fun i => [(2i,i,0),(2i+5,i,1)])`. -/
theorem rrBasisCandidates_20_eq : rrBasisCandidates 20 =
    [(0,0,0), (5,0,1), (2,1,0), (7,1,1), (4,2,0), (9,2,1), (6,3,0), (11,3,1),
     (8,4,0), (13,4,1), (10,5,0), (15,5,1), (12,6,0), (17,6,1), (14,7,0),
     (19,7,1), (16,8,0), (21,8,1), (18,9,0), (23,9,1), (20,10,0), (25,10,1)] := by
  decide

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
  ((rrBasisCandidates 20).mergeSort (fun a b => decide (a.1 ≤ b.1))).take 7

/-- **`rrBasis7`'s literal value, proved (not merely asserted).** The
`Perm` + `Sorted`-uniqueness route (ChatGPT consultation,
`chatgpt_prompt_mergesort_decide.md`), NOT kernel-computing `mergeSort`:
`List.sorted_mergeSort'` gives that the (full, un-`take`n) sorted result
is `Sorted (· ≤ ·)` (on the first component, via the `Preorder`-lifted
relation) and `List.perm_mergeSort`/the sort's own permutation fact gives
it's a permutation of `rrBasisCandidates 20` — hence, by
`rrBasisCandidates_20_eq`, a permutation of the 22-element literal list
above. Since the literal `full22` list below is ALSO sorted by first
component (checked by `decide` — ordinary arithmetic, no `mergeSort`) and
a permutation of the same 22-element list (checked by `decide` via
`List.Perm`'s decidability — also ordinary, no `mergeSort`), and sortedness
by `≤` on a list with strictly-increasing distinct first coordinates
forces list equality (two sorted permutations of the same multiset, with
distinct keys, must be the identical sequence), the actual `mergeSort`
output equals `full22`; `.take 7` of that is `rrBasis7`. -/
theorem rrBasis7_eq :
    rrBasis7 =
      [(0,0,0), (2,1,0), (4,2,0), (5,0,1), (6,3,0), (7,1,1), (8,4,0)] := by
  have hfull22 :
      (rrBasisCandidates 20).mergeSort (fun a b => decide (a.1 ≤ b.1)) =
      [(0,0,0), (2,1,0), (4,2,0), (5,0,1), (6,3,0), (7,1,1), (8,4,0), (9,2,1),
       (10,5,0), (11,3,1), (12,6,0), (13,4,1), (14,7,0), (15,5,1), (16,8,0),
       (17,6,1), (18,9,0), (19,7,1), (20,10,0), (21,8,1), (23,9,1), (25,10,1)] := by
    have hsorted : List.Pairwise (fun a b : ℕ × ℕ × ℕ => a.1 ≤ b.1)
        ((rrBasisCandidates 20).mergeSort (fun a b => decide (a.1 ≤ b.1))) := by
      have hb : List.Pairwise (fun a b : ℕ × ℕ × ℕ => decide (a.1 ≤ b.1) = true)
          ((rrBasisCandidates 20).mergeSort (fun a b => decide (a.1 ≤ b.1))) := by
        apply List.pairwise_mergeSort
        · intro a b c hab hbc
          exact decide_eq_true (Nat.le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc))
        · intro a b
          rcases Nat.le_total a.1 b.1 with h | h
          · have : decide (a.1 ≤ b.1) = true := decide_eq_true h
            simp [this]
          · have : decide (b.1 ≤ a.1) = true := decide_eq_true h
            simp [this]
      exact hb.imp (fun h => of_decide_eq_true h)
    have hperm :
        List.Perm ((rrBasisCandidates 20).mergeSort (fun a b => decide (a.1 ≤ b.1)))
          (rrBasisCandidates 20) :=
      List.mergeSort_perm (rrBasisCandidates 20) (fun a b => decide (a.1 ≤ b.1))
    rw [rrBasisCandidates_20_eq] at hperm
    -- `Std.Antisymm (fun a b => a.1 ≤ b.1)` is false in general on
    -- `ℕ × ℕ × ℕ` (two triples can share `.1` without being equal), so
    -- `List.Perm.eq_of_pairwise'` doesn't apply to that relation directly.
    -- But every element of `rrBasisCandidates 20` has a `.1` value distinct
    -- from every other element's (checked by `decide` on the concrete
    -- 22-element list via `rrBasisCandidates_20_eq`), so on elements drawn
    -- from this list, `.1 ≤` and `.1 =` collapse `≤`-antisymmetry down to
    -- ordinary equality; package that as `r a b := a.1 < b.1 ∨ a = b`,
    -- which IS unconditionally antisymmetric on all of `ℕ × ℕ × ℕ`, and
    -- transfer both `Pairwise` facts across using the distinctness lemma.
    have hne : ∀ a ∈ rrBasisCandidates 20, ∀ b ∈ rrBasisCandidates 20,
        a.1 = b.1 → a = b := by
      rw [rrBasisCandidates_20_eq]
      decide
    set r : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ → Prop := fun a b => a.1 < b.1 ∨ a = b with hr
    have hantisymm : ∀ a b : ℕ × ℕ × ℕ, r a b → r b a → a = b := by
      intro a b hab hba
      rcases hab with hab | hab
      · rcases hba with hba | hba
        · exact absurd (Nat.lt_trans hab hba) (lt_irrefl _)
        · exact hba.symm
      · exact hab
    have hsorted' : List.Pairwise r
        ((rrBasisCandidates 20).mergeSort (fun a b => decide (a.1 ≤ b.1))) := by
      apply List.Pairwise.imp_of_mem (R := fun a b : ℕ × ℕ × ℕ => a.1 ≤ b.1) (S := r)
      · intro a b ha hb hab
        rcases lt_or_eq_of_le hab with h | h
        · exact Or.inl h
        · exact Or.inr (hne a ((List.mem_mergeSort).mp ha) b ((List.mem_mergeSort).mp hb) h)
      · exact hsorted
    have htarget_perm :
        List.Perm
          [(0,0,0), (2,1,0), (4,2,0), (5,0,1), (6,3,0), (7,1,1), (8,4,0), (9,2,1),
           (10,5,0), (11,3,1), (12,6,0), (13,4,1), (14,7,0), (15,5,1), (16,8,0),
           (17,6,1), (18,9,0), (19,7,1), (20,10,0), (21,8,1), (23,9,1), (25,10,1)]
          [(0,0,0), (5,0,1), (2,1,0), (7,1,1), (4,2,0), (9,2,1), (6,3,0), (11,3,1),
           (8,4,0), (13,4,1), (10,5,0), (15,5,1), (12,6,0), (17,6,1), (14,7,0),
           (19,7,1), (16,8,0), (21,8,1), (18,9,0), (23,9,1), (20,10,0), (25,10,1)] := by
      decide
    have htarget_sorted' : List.Pairwise r
        [(0,0,0), (2,1,0), (4,2,0), (5,0,1), (6,3,0), (7,1,1), (8,4,0), (9,2,1),
         (10,5,0), (11,3,1), (12,6,0), (13,4,1), (14,7,0), (15,5,1), (16,8,0),
         (17,6,1), (18,9,0), (19,7,1), (20,10,0), (21,8,1), (23,9,1), (25,10,1)] := by
      decide
    haveI : Std.Antisymm r := ⟨hantisymm⟩
    exact List.Perm.eq_of_pairwise' hsorted' htarget_sorted' (hperm.trans htarget_perm.symm)
  show ((rrBasisCandidates 20).mergeSort (fun a b => decide (a.1 ≤ b.1))).take 7 = _
  rw [hfull22]
  rfl

/-- Every element of `rrBasis7` has flag component `0` or `1` — mirrors
`rrBasis5_flag` (`DataDerivationBasics.lean`) exactly, reusing the SAME
general `rrBasisCandidates_flag` fact (which holds for any `maxOrder`, not
just the `take`-length used downstream) via `rrBasis7 ⊆ rrBasisCandidates
20`. Needed by `row01_defining_eq_aux`'s `bj ∈ {0,1}` case split, the same
way `rrBasis5_flag` is needed by `anchor_defining_eq_aux`'s. -/
theorem rrBasis7_flag : ∀ t ∈ rrBasis7, t.2.2 = 0 ∨ t.2.2 = 1 := by
  intro t ht
  apply rrBasisCandidates_flag 20
  have ht' : t ∈ (rrBasisCandidates 20).mergeSort (fun a b => decide (a.1 ≤ b.1)) :=
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

/-! ## Tangent-anchor row content (`m=2` case), K=4 — the `P1=P2`
coincidence case

Per `ROADMAP-alpha-locus.md`'s "K=4 recipe... CONFIRMED against
`phi_general.zip`'s actual reference implementation" section (step (ii) of
the recommended scope), ported here verbatim from the confirmed Julia
source, not re-derived. **Claire's observation this pass, now recorded as
a standing hypothesis rather than re-derived from curve geometry each
time**: since this project's factor base excludes involution pairs
(`P`/`-P` never both sampled), `P1.1 = P2.1 ⟹ P1 = P2` for any `P1,P2`
this file is ever actually called with — so `P1.1 = P2.1` (checkable from
`h12`'s `IsCoprime (X - C P1.1) (X - C P2.1)` failing) IS the tangency
trigger, with no separate "same x, different y" sub-case to keep apart
from it (superseding the roadmap's earlier, more cautious phrasing on
this point).

This section builds only the STANDALONE arithmetic content — the branch
derivative and the two per-column tangent-row-entry formulas — not yet
wired into `matrixA4`/`Epoly4`/`Ypoly4` themselves (that wiring, and the
`uRS4_dvd_Npoly4`-tangent-case divisibility argument built from it, are
steps (iii)-(iv), still to come). -/

section TangentRow4

/-- **The branch derivative**: for a curve point `(px,py)` with `py ≠ 0`
(the standing nondegeneracy this project already needs throughout —
`py = 0` is a Weierstrass point, excluded via `Bad` as noted in
`ROADMAP-alpha-locus.md`'s point 3), the implicit-function-theorem
derivative of `y` along the branch `y² = f(x)` at `x = px` is
`f'(px) / (2·py)`. Confirmed against `phi_general.zip`'s
`branch_series!`/`fill_f_tay!` (`F_x(px) = -f'(px)`, `F_y = 2py`,
`y'(px) = -F_x/F_y`), not re-derived from scratch. -/
noncomputable def branchDeriv4 (c0 c1 c2 c3 c4 : F p) (px py : F p) : F p :=
  (derivative (curvePoly p c0 c1 c2 c3 c4)).eval px / (2 * py)

/-- **Tangent-row entry, pure-`x` column** (`(i,0)`-shaped basis monomial
`x^i`, no `y`-dependence): the derivative-row entry is the ORDINARY
polynomial derivative coefficient `i·px^(i-1)` — no branch-series
involvement, matching `ROADMAP-alpha-locus.md`'s point 3 exactly ("no
branch-series involvement, since this monomial has no `y`"). Stated via
`Polynomial.derivative_X_pow`'s closed form rather than a bespoke `i·x^(i-
1)` definition, to keep this provably equal to "the derivative of `x^i`
evaluated at `px`" rather than an independently-asserted formula (the
`Polynomial.derivative`-based route this file's earlier tangent-lemma
route, `comp_X_add_C_coeff_one`, already established as the correct way
to talk about derivatives-at-a-point in this file). -/
noncomputable def tangentRowEntryX4 (i : ℕ) (px : F p) : F p :=
  (derivative (X ^ i : Polynomial (F p))).eval px

/-- **Tangent-row entry, pure-`x` column, closed form** — confirms
`tangentRowEntryX4` really does compute `i·px^(i-1)` for `i ≥ 1` (the `i=0`
case, `x^0 = 1`, has zero derivative, matching `Nat.cast 0 = 0` on the
RHS's `i=0` instance automatically). Uses `Polynomial.derivative_X_pow`,
confirmed present in current Mathlib4. -/
theorem tangentRowEntryX4_eq (i : ℕ) (px : F p) :
    tangentRowEntryX4 p i px = (i : F p) * px ^ (i - 1) := by
  unfold tangentRowEntryX4
  rw [Polynomial.derivative_X_pow]
  simp

/-- **Tangent-row entry, mixed `x^i·y` column** (`(i,1)`-shaped basis
monomial `x^i·y`): the PRODUCT-RULE expansion against the branch series,
`i·px^(i-1)·py + px^i·y'(px)` — confirmed against
`phi_general.zip`'s `fill_monomial_block!` m=2 path, the genuinely new
per-column formula relative to the `m=1`/pure-evaluation case (not a
simple reuse of the ordinary derivative rule, since `y` itself varies
along the branch). `py`/`branchDeriv4 p c0 c1 c2 c3 c4 px py` play the
roles of `y(px)`/`y'(px)` respectively. -/
noncomputable def tangentRowEntryXY4 (c0 c1 c2 c3 c4 : F p) (i : ℕ) (px py : F p) : F p :=
  tangentRowEntryX4 p i px * py + px ^ i * branchDeriv4 p c0 c1 c2 c3 c4 px py

end TangentRow4

/-! ## Tangent matrix, `matrixA4Tangent`/`rhsVec4Tangent` — step (iii)

Per `ROADMAP-alpha-locus.md`'s recommended scope, step (iii): a SEPARATE
matrix/rhs pair for the `P1=P2` tangent case, rather than threading an
`if P1 = P2` branch through the already-working `matrixA4`/`rhsVec4`
(matching the roadmap's own "likely one lemma parametrized by which pair"
framing, and this project's convention of not destabilizing an
already-compiling proof). Rows 2–5 are copy-pasted UNCHANGED from
`matrixA4`/`rhsVec4` — they never reference `P1`/`P2` at all (only rows
0–1 do), so nothing about the `u_a`/target reduction rows changes when the
two literal-point anchors collapse into one tangent anchor. Only rows 0–1
change: row 0 is the ordinary evaluation row at `px := P1.1` (`m=1`'s
usual row, unchanged in form), row 1 is the NEW derivative-along-the-
branch row, using `tangentRowEntryX4`/`tangentRowEntryXY4` per-column
(the `bj=0`/`bj=1` split matching those two lemmas' own split exactly). -/

variable (px py : F p)

/-- The `6×6` tangent-case matrix. Row 0: ordinary evaluation at `(px,py)`
(same formula as `matrixA4`'s row-0/row-1, one point instead of two).
Row 1: the tangent/derivative row, `tangentRowEntryX4`/`tangentRowEntryXY4`
depending on the column's `bj`. Rows 2–5: byte-identical to `matrixA4`. -/
noncomputable def matrixA4Tangent (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p) :
    Matrix (Fin 6) (Fin 6) (F p) :=
  fun row col =>
    let bidx := otherIdx7.getD col.val 0
    let (_, bi, bj) := rrBasis7.getD bidx (0, 0, 0)
    if row.val = 0 then
      px ^ bi * (if bj = 1 then py else 1)
    else if row.val = 1 then
      if bj = 1 then tangentRowEntryXY4 p c0 c1 c2 c3 c4 bi px py
      else tangentRowEntryX4 p bi px
    else if row.val = 2 ∨ row.val = 3 then
      let (r0, r1) := reduceMonomialModU p ua0 ua1 va0 va1 bi bj
      if row.val = 2 then r0 else r1
    else
      let (r0, r1) := reduceMonomialModU p u0 u1 v0 v1 bi bj
      if row.val = 4 then r0 else r1

/-- The tangent-case RHS vector. Row 0: ordinary evaluation, unchanged
form. Row 1: the tangent-row entry applied to the `yIdx7`-th (bare-`y`)
basis element — `bj_n = 1` unconditionally for that element (per
`rrBasis7_yIdx_eq`), so this is always the `tangentRowEntryXY4` branch,
matching `matrixA4Tangent`'s row-1 `bj=1` case. Rows 2–5: byte-identical
to `rhsVec4`. -/
noncomputable def rhsVec4Tangent (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p) :
    Fin 6 → F p :=
  fun row =>
    let (_, bi_n, bj_n) := rrBasis7.getD yIdx7 (0, 1, 1)
    if row.val = 0 then
      -(px ^ bi_n * (if bj_n = 1 then py else 1))
    else if row.val = 1 then
      -(tangentRowEntryXY4 p c0 c1 c2 c3 c4 bi_n px py)
    else if row.val = 2 ∨ row.val = 3 then
      let (rn0, rn1) := reduceMonomialModU p ua0 ua1 va0 va1 bi_n bj_n;
      -(if row.val = 2 then rn0 else rn1)
    else
      let (rn0, rn1) := reduceMonomialModU p u0 u1 v0 v1 bi_n bj_n;
      -(if row.val = 4 then rn0 else rn1)

/-- Row-unfolding for `matrixA4Tangent`'s row 0 — identical shape to
`matrixA4_row01_eval`'s row-0 case, one point instead of two. -/
theorem matrixA4Tangent_row0_eval (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p) (col : Fin 6) :
    matrixA4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 ⟨0, by omega⟩ col =
      let (_, bi, bj) := rrBasis7.getD (otherIdx7.getD col.val 0) (0, 0, 0)
      px ^ bi * (if bj = 1 then py else 1) := by
  simp [matrixA4Tangent]

/-- Row-unfolding for `matrixA4Tangent`'s row 1 (the new derivative row) —
the `bj=0`/`bj=1` split matching `tangentRowEntryX4`/`tangentRowEntryXY4`
exactly. -/
theorem matrixA4Tangent_row1_eval (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p) (col : Fin 6) :
    matrixA4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 ⟨1, by omega⟩ col =
      let (_, bi, bj) := rrBasis7.getD (otherIdx7.getD col.val 0) (0, 0, 0)
      if bj = 1 then tangentRowEntryXY4 p c0 c1 c2 c3 c4 bi px py
      else tangentRowEntryX4 p bi px := by
  simp [matrixA4Tangent]

/-- Row-unfolding for `matrixA4Tangent`'s rows 2–3 — byte-identical to
`matrixA4_row23_eval` since those rows never reference `px`/`py`. -/
theorem matrixA4Tangent_row23_eval (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (a : Fin 2) (col : Fin 6) :
    matrixA4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 ⟨2 + a.val, by omega⟩ col =
      let (_, bi, bj) := rrBasis7.getD (otherIdx7.getD col.val 0) (0, 0, 0)
      let (r0, r1) := reduceMonomialModU p ua0 ua1 va0 va1 bi bj
      if a.val = 0 then r0 else r1 := by
  fin_cases a <;> simp [matrixA4Tangent]

/-- Row-unfolding for `matrixA4Tangent`'s rows 4–5 — byte-identical to
`matrixA4_row45_eval`. -/
theorem matrixA4Tangent_row45_eval (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (a : Fin 2) (col : Fin 6) :
    matrixA4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 ⟨4 + a.val, by omega⟩ col =
      let (_, bi, bj) := rrBasis7.getD (otherIdx7.getD col.val 0) (0, 0, 0)
      let (r0, r1) := reduceMonomialModU p u0 u1 v0 v1 bi bj
      if a.val = 0 then r0 else r1 := by
  fin_cases a <;> simp [matrixA4Tangent]

/-- Row-unfolding for `rhsVec4Tangent`'s row 0 — identical shape to
`rhsVec4_row01_eval`'s row-0 case. -/
theorem rhsVec4Tangent_row0_eval (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p) :
    rhsVec4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 ⟨0, by omega⟩ =
      let (_, bi_n, bj_n) := rrBasis7.getD yIdx7 (0, 1, 1)
      (-(px ^ bi_n * (if bj_n = 1 then py else 1))) := by
  rfl

/-- Row-unfolding for `rhsVec4Tangent`'s row 1 (the new derivative row). -/
theorem rhsVec4Tangent_row1_eval (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p) :
    rhsVec4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 ⟨1, by omega⟩ =
      let (_, bi_n, _) := rrBasis7.getD yIdx7 (0, 1, 1)
      (-(tangentRowEntryXY4 p c0 c1 c2 c3 c4 bi_n px py)) := by
  rfl

/-- Row-unfolding for `rhsVec4Tangent`'s rows 2–3 — byte-identical to
`rhsVec4_row23_eval`. -/
theorem rhsVec4Tangent_row23_eval (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p) (a : Fin 2) :
    rhsVec4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 ⟨2 + a.val, by omega⟩ =
      let (_, bi_n, bj_n) := rrBasis7.getD yIdx7 (0, 1, 1)
      let (rn0, rn1) := reduceMonomialModU p ua0 ua1 va0 va1 bi_n bj_n
      (-(if a.val = 0 then rn0 else rn1)) := by
  fin_cases a <;> rfl

/-- Row-unfolding for `rhsVec4Tangent`'s rows 4–5 — byte-identical to
`rhsVec4_row45_eval`. -/
theorem rhsVec4Tangent_row45_eval (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p) (a : Fin 2) :
    rhsVec4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 ⟨4 + a.val, by omega⟩ =
      let (_, bi_n, bj_n) := rrBasis7.getD yIdx7 (0, 1, 1)
      let (rn0, rn1) := reduceMonomialModU p u0 u1 v0 v1 bi_n bj_n
      (-(if a.val = 0 then rn0 else rn1)) := by
  fin_cases a <;> rfl

/-- **Genericity condition, tangent case** — mirrors `MatrixNondegenerate4`
exactly, for `matrixA4Tangent` in place of `matrixA4`. -/
def MatrixNondegenerate4Tangent (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p) : Prop :=
  (matrixA4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1).det ≠ 0

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

/-! ## Tangent-case coefficient assembly — step (iii) continued

`cramerSolution4Tangent`/`coeffsOut4Tangent`/`Epoly4Tangent`/`Ypoly4Tangent`
mirror `cramerSolution4`/`coeffsOut4`/`Epoly4`/`Ypoly4` exactly, substituting
`matrixA4Tangent`/`rhsVec4Tangent` for `matrixA4`/`rhsVec4`. `otherMap4`/
`otherIdx7`/`yIdx7` are REUSED unchanged — those are pure column/index
combinatorics independent of which matrix/rhs pair is being solved. -/

/-- Tangent-case Cramer's-rule solution — mirrors `cramerSolution4`. -/
noncomputable def cramerSolution4Tangent (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p) :
    Fin 6 → F p :=
  fun i =>
    (matrixA4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1).cramer
        (rhsVec4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1) i /
      (matrixA4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1).det

/-- Tangent-case full 7-slot coefficient vector — mirrors `coeffsOut4`. -/
noncomputable def coeffsOut4Tangent (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p) :
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
      cramerSolution4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1
        ⟨hex.choose, hlt⟩

/-- Tangent-case `otherMap4` bridge — mirrors `coeffsOut4_otherMap`
verbatim, substituting `coeffsOut4Tangent`/`cramerSolution4Tangent`. -/
theorem coeffsOut4Tangent_otherMap (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p) (col : Fin 6) :
    coeffsOut4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 (otherMap4 col) =
      cramerSolution4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 col := by
  have hcol : col.val < otherIdx7.length := by rw [otherIdx7_length]; exact col.isLt
  have hgetD : otherIdx7.getD col.val 0 = otherIdx7[col.val] := List.getD_eq_getElem _ _ hcol
  have hne : (otherMap4 col).val ≠ yIdx7 := by
    have hmem : otherIdx7[col.val] ∈ otherIdx7 := List.getElem_mem hcol
    have : otherIdx7[col.val] ≠ yIdx7 := ((mem_otherIdx7_iff _).mp hmem).2
    change otherIdx7.getD col.val 0 ≠ yIdx7
    rw [hgetD]; exact this
  unfold coeffsOut4Tangent
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
  exact congrArg (cramerSolution4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1)
    (Fin.ext (a := (⟨hex.choose, hchoose_lt6⟩ : Fin 6)) (b := col) hidx_eq)

/-- Tangent-case `E(x)` — mirrors `Epoly4`. -/
noncomputable def Epoly4Tangent (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p) :
    Polynomial (F p) :=
  ∑ bidx : Fin 7,
    let (_, bi, bj) := rrBasis7.getD bidx.val (0, 0, 0)
    if bj = 0 then
      C (coeffsOut4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 bidx) * X ^ bi
    else 0

/-- Tangent-case `Y(x)` — mirrors `Ypoly4`. -/
noncomputable def Ypoly4Tangent (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p) :
    Polynomial (F p) :=
  ∑ bidx : Fin 7,
    let (_, bi, bj) := rrBasis7.getD bidx.val (0, 0, 0)
    if bj = 1 then
      C (coeffsOut4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 bidx) * X ^ bi
    else 0

/-! ## Tangent row-identity theorems — step (iii) continued

Mirrors `row01_defining_eq_aux` (the K=4 simple-point value-vanishing
identity) but for the tangent case's two rows: row 0 is the ordinary
value identity at `(px,py)` (byte-identical algebraic content to
`row01_defining_eq_aux`, one point instead of two); row 1 is the NEW
derivative-along-the-branch identity, `E'(px) + py*Y'(px) +
px*... "` — concretely `phi`'s directional derivative along the branch
vanishes, i.e. `(E'.eval px) + (Y.eval px)*(branchDeriv) + py*(Y'.eval
px) = 0`, matching `tangentRowEntryXY4`'s product-rule construction per
column. Both proofs reuse the exact same five-step Cramer's-rule
skeleton as `row01_defining_eq_aux`; only the per-column entry formula
and the final "sum of entries = polynomial eval" identification differ,
so this is factored as one generic lemma (`rowTangent_defining_eq_aux`)
parametrized by the row index, then two one-line wrappers extract the
concrete value/derivative statements each downstream divisibility proof
actually needs. -/

section TangentRowIdentity4

variable (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)

/-- **Generic tangent row-identity**: for row `r : Fin 2` of
`matrixA4Tangent`/`rhsVec4Tangent`, the Cramer's-rule solution satisfies
the row's own defining linear equation, stated abstractly via the row's
column-entry function `entry` and RHS `negEntry` (rather than unfolding
`matrixA4Tangent`/`rhsVec4Tangent` inline) so it can serve both row 0
(`entry = fun bi _ => px^bi`-style, `bj`-split) and row 1
(`entry` = the tangent per-column formula) uniformly. Kept `private`,
matching this file's convention for these Cramer-rule plumbing lemmas. -/
private theorem rowTangent_defining_eq_aux (r : Fin 2)
    (hA : MatrixNondegenerate4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1)
    (entry : ℕ → ℕ → F p) (negEntry : F p)
    (hrow : ∀ col : Fin 6,
      matrixA4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 ⟨r.val, by omega⟩ col =
        let (_, bi, bj) := rrBasis7.getD (otherIdx7.getD col.val 0) (0, 0, 0)
        entry bi bj)
    (hrhs : rhsVec4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 ⟨r.val, by omega⟩ =
      negEntry)
    (hyentry : let (_, bi_n, bj_n) := rrBasis7.getD yIdx7 (0, 1, 1); entry bi_n bj_n = -negEntry) :
    (∑ bidx : Fin 7,
      let (_, bi, bj) := rrBasis7.getD bidx.val (0, 0, 0)
      coeffsOut4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 bidx * entry bi bj) = 0 := by
  have hdet : (matrixA4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1).det ≠ 0 := hA
  have hrRow : r.val < 6 := by omega
  have hmul := Matrix.mulVec_cramer
    (matrixA4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1)
    (rhsVec4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1)
  have hrow' : ∑ col : Fin 6,
      matrixA4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 ⟨r.val, hrRow⟩ col *
      cramerSolution4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 col =
      rhsVec4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 ⟨r.val, hrRow⟩ := by
    have hstep : (∑ col : Fin 6,
        matrixA4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 ⟨r.val, hrRow⟩ col *
        cramerSolution4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 col) *
        (matrixA4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1).det =
        rhsVec4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 ⟨r.val, hrRow⟩ *
          (matrixA4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1).det := by
      unfold cramerSolution4Tangent
      rw [Finset.sum_mul]
      have hcol : ∀ col : Fin 6,
          matrixA4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 ⟨r.val, hrRow⟩ col *
          ((matrixA4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1).cramer
              (rhsVec4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1) col /
            (matrixA4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1).det) *
          (matrixA4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1).det =
          matrixA4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 ⟨r.val, hrRow⟩ col *
          (matrixA4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1).cramer
              (rhsVec4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1) col := by
        intro col; field_simp
      simp only [hcol]
      have hthis := congrFun hmul (⟨r.val, hrRow⟩ : Fin 6)
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hthis
      rw [hthis]; ring
    exact mul_right_cancel₀ hdet hstep
  rw [hrhs] at hrow'
  have hswap : (∑ col : Fin 6,
      matrixA4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 ⟨r.val, hrRow⟩ col *
        cramerSolution4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 col) =
      ∑ col : Fin 6, coeffsOut4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1
        (otherMap4 col) *
        (let (_, bi, bj) := rrBasis7.getD (otherIdx7.getD col.val 0) (0, 0, 0); entry bi bj) := by
    apply Finset.sum_congr rfl
    intro col _
    rw [coeffsOut4Tangent_otherMap, mul_comm, hrow col]
  rw [hswap] at hrow'
  have hFsum : (∑ bidx : Fin 7,
      let (_, bi, bj) := rrBasis7.getD bidx.val (0, 0, 0)
      coeffsOut4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 bidx * entry bi bj) =
      (∑ col : Fin 6, coeffsOut4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1
        (otherMap4 col) *
        (let (_, bi, bj) := rrBasis7.getD (otherIdx7.getD col.val 0) (0, 0, 0); entry bi bj)) +
      coeffsOut4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1
        ⟨yIdx7, yIdx7_lt_seven⟩ *
        (let (_, bi_n, bj_n) := rrBasis7.getD yIdx7 (0, 1, 1); entry bi_n bj_n) := by
    let Fsum : Fin 7 → F p := fun bidx =>
      let (_, bi, bj) := rrBasis7.getD bidx.val (0, 0, 0)
      coeffsOut4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 bidx * entry bi bj
    have hFcol : ∀ col : Fin 6,
        Fsum (otherMap4 col) =
          coeffsOut4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1
            (otherMap4 col) *
            (let (_, bi, bj) := rrBasis7.getD (otherIdx7.getD col.val 0) (0, 0, 0); entry bi bj) := by
      intro col
      have hidx : (otherMap4 col).val = otherIdx7.getD col.val 0 := rfl
      simp only [Fsum, hidx]
    have hFy : Fsum (⟨yIdx7, yIdx7_lt_seven⟩ : Fin 7) =
        coeffsOut4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1
          ⟨yIdx7, yIdx7_lt_seven⟩ *
          (let (_, bi_n, bj_n) := rrBasis7.getD yIdx7 (0, 1, 1); entry bi_n bj_n) := by
      have hy_len : yIdx7 < rrBasis7.length := by
        have hlen : rrBasis7.length = 7 := by
          simp [rrBasis7, rrBasisCandidates, List.length_flatMap]
        rw [hlen]
        exact yIdx7_lt_seven
      have hy_get : rrBasis7.getD yIdx7 (0, 0, 0) =
          rrBasis7.getD yIdx7 (0, 1, 1) := by
        rw [List.getD_eq_getElem _ _ hy_len, List.getD_eq_getElem _ _ hy_len]
      unfold Fsum
      rw [hy_get]
    have hsum7 :
        (∑ col : Fin 6, Fsum (otherMap4 col)) +
            Fsum ⟨yIdx7, yIdx7_lt_seven⟩ =
          ∑ bidx : Fin 7, Fsum bidx :=
      sum_otherIdx7_add_y p Fsum
    calc
      ∑ bidx : Fin 7, Fsum bidx =
          (∑ col : Fin 6, Fsum (otherMap4 col)) + Fsum ⟨yIdx7, yIdx7_lt_seven⟩ :=
        hsum7.symm
      _ = (∑ col : Fin 6,
            coeffsOut4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1
              (otherMap4 col) *
              (let (_, bi, bj) := rrBasis7.getD (otherIdx7.getD col.val 0) (0, 0, 0); entry bi bj)) +
          coeffsOut4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1
            ⟨yIdx7, yIdx7_lt_seven⟩ *
            (let (_, bi_n, bj_n) := rrBasis7.getD yIdx7 (0, 1, 1); entry bi_n bj_n) := by
        rw [Finset.sum_congr rfl (fun col _ => hFcol col), hFy]
  rw [hFsum]
  have hcoeffsOutY : coeffsOut4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1
      ⟨yIdx7, yIdx7_lt_seven⟩ = 1 := by
    unfold coeffsOut4Tangent; rw [dif_pos rfl]
  rw [hcoeffsOutY, one_mul]
  simp only [hyentry]
  rw [hrow']
  ring

end TangentRowIdentity4

/-- **Value identity, tangent case** (row 0): `phi(px,py) = 0`, i.e.
`E(px) + py*Y(px) = 0` for `E := Epoly4Tangent`, `Y := Ypoly4Tangent` —
the tangent-case, single-point analogue of `row01_defining_eq_aux`. -/
private theorem rowTangent0_defining_eq_aux (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (hA : MatrixNondegenerate4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1) :
    (Epoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1).eval px +
      py * (Ypoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1).eval px = 0 := by
  have hsum := rowTangent_defining_eq_aux p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1
    (⟨0, by omega⟩ : Fin 2) hA (fun bi bj => px ^ bi * (if bj = 1 then py else 1))
    (-py)
    (fun col => matrixA4Tangent_row0_eval p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 col)
    (by
      have hy_len : yIdx7 < rrBasis7.length := by
        have hlen : rrBasis7.length = 7 := by
          simp [rrBasis7, rrBasisCandidates, List.length_flatMap]
        rw [hlen]
        exact yIdx7_lt_seven
      have hy_get : rrBasis7.getD yIdx7 (0, 0, 0) =
          rrBasis7.getD yIdx7 (0, 1, 1) := by
        rw [List.getD_eq_getElem _ _ hy_len, List.getD_eq_getElem _ _ hy_len]
      have hy_get11 : rrBasis7.getD yIdx7 (0, 1, 1) = (5, 0, 1) := by
        calc
          rrBasis7.getD yIdx7 (0, 1, 1) = rrBasis7.getD yIdx7 (0, 0, 0) := hy_get.symm
          _ = (5, 0, 1) := rrBasis7_yIdx_eq
      have hy_getElem : rrBasis7[yIdx7] = (5, 0, 1) := by
        rw [← List.getD_eq_getElem _ _ hy_len]
        exact rrBasis7_yIdx_eq
      have hy_getElem? : rrBasis7[yIdx7]? = some (5, 0, 1) := by
        simp [hy_len, hy_getElem]
      simp [rhsVec4Tangent, hy_getElem, hy_getElem?])
    (by
      have hy_len : yIdx7 < rrBasis7.length := by
        have hlen : rrBasis7.length = 7 := by
          simp [rrBasis7, rrBasisCandidates, List.length_flatMap]
        rw [hlen]
        exact yIdx7_lt_seven
      have hy_get : rrBasis7.getD yIdx7 (0, 0, 0) =
          rrBasis7.getD yIdx7 (0, 1, 1) := by
        rw [List.getD_eq_getElem _ _ hy_len, List.getD_eq_getElem _ _ hy_len]
      have hy_get11 : rrBasis7.getD yIdx7 (0, 1, 1) = (5, 0, 1) := by
        calc
          rrBasis7.getD yIdx7 (0, 1, 1) = rrBasis7.getD yIdx7 (0, 0, 0) := hy_get.symm
          _ = (5, 0, 1) := rrBasis7_yIdx_eq
      rw [hy_get11]
      simp)
  rw [show (Epoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1).eval px +
      py * (Ypoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1).eval px =
      ∑ bidx : Fin 7,
        let (_, bi, bj) := rrBasis7.getD bidx.val (0, 0, 0)
        coeffsOut4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 bidx *
          (px ^ bi * (if bj = 1 then py else 1)) from ?_]
  · exact hsum
  · unfold Epoly4Tangent Ypoly4Tangent
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
      have hflag : (rrBasis7.getD bidx.val (0, 0, 0)).2.2 = 0 ∨
          (rrBasis7.getD bidx.val (0, 0, 0)).2.2 = 1 := by
        rw [List.getD_eq_getElem _ _ hlt]
        exact rrBasis7_flag _ (List.getElem_mem hlt)
      rw [hget] at hflag
      exact hflag
    rcases hbj0or1 with hb0 | hb1
    · subst bj
      norm_num [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]
    · subst bj
      norm_num [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]
      ring

/-- **Derivative identity, tangent case** (row 1): the directional
derivative of `phi(x,y(x))` along the branch `y²=f(x)` vanishes at
`x=px` — `E'(px) + py*Y'(px) + Y(px)*branchDeriv = 0`, matching
`tangentRowEntryXY4`'s product-rule construction: this is exactly the
`m=2` row-block content confirmed against `phi_general.zip`
(`ROADMAP-alpha-locus.md`'s "K=4 recipe" §3), the fact
`sq_dvd_of_eval_derivative_eq_zero` needs alongside
`rowTangent0_defining_eq_aux` to conclude `(X-C px)²∣N`. -/
private theorem rowTangent1_defining_eq_aux (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (hA : MatrixNondegenerate4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1) :
    (derivative (Epoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1)).eval px +
      py * (derivative (Ypoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1)).eval px
      + (Ypoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1).eval px *
        branchDeriv4 p c0 c1 c2 c3 c4 px py = 0 := by
  have hsum := rowTangent_defining_eq_aux p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1
    (⟨1, by omega⟩ : Fin 2) hA
    (fun bi bj => if bj = 1 then tangentRowEntryXY4 p c0 c1 c2 c3 c4 bi px py
      else tangentRowEntryX4 p bi px)
    (rhsVec4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 ⟨1, by omega⟩)
    (fun col => matrixA4Tangent_row1_eval p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 col)
    rfl (by
      have hy_len : yIdx7 < rrBasis7.length := by
        have hlen : rrBasis7.length = 7 := by
          simp [rrBasis7, rrBasisCandidates, List.length_flatMap]
        rw [hlen]
        exact yIdx7_lt_seven
      have hy_get : rrBasis7.getD yIdx7 (0, 0, 0) =
          rrBasis7.getD yIdx7 (0, 1, 1) := by
        rw [List.getD_eq_getElem _ _ hy_len, List.getD_eq_getElem _ _ hy_len]
      have hy_get11 : rrBasis7.getD yIdx7 (0, 1, 1) = (5, 0, 1) := by
        calc
          rrBasis7.getD yIdx7 (0, 1, 1) = rrBasis7.getD yIdx7 (0, 0, 0) := hy_get.symm
          _ = (5, 0, 1) := rrBasis7_yIdx_eq
      rw [hy_get11]
      have hrow :
          rhsVec4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1
              (⟨1, by omega⟩ : Fin 6) =
            -(tangentRowEntryXY4 p c0 c1 c2 c3 c4 0 px py) := by
        unfold rhsVec4Tangent
        rw [hy_get11]
        rfl
      rw [hrow]
      simp)
  rw [show (derivative (Epoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1)).eval px +
      py * (derivative (Ypoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1)).eval px
      + (Ypoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1).eval px *
        branchDeriv4 p c0 c1 c2 c3 c4 px py =
      ∑ bidx : Fin 7,
        let (_, bi, bj) := rrBasis7.getD bidx.val (0, 0, 0)
        coeffsOut4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 bidx *
          (if bj = 1 then tangentRowEntryXY4 p c0 c1 c2 c3 c4 bi px py
           else tangentRowEntryX4 p bi px) from ?_]
  · exact hsum
  · unfold Epoly4Tangent Ypoly4Tangent tangentRowEntryXY4
    rw [Polynomial.derivative_sum, Polynomial.derivative_sum,
      Polynomial.eval_finsetSum, Polynomial.eval_finsetSum, Polynomial.eval_finsetSum,
      Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro bidx _
    generalize hget : rrBasis7.getD bidx.val (0, 0, 0) = g
    rcases g with ⟨fst, bi, bj⟩
    have hbj0or1 : bj = 0 ∨ bj = 1 := by
      have hlen : rrBasis7.length = 7 := by
        simp [rrBasis7, rrBasisCandidates, List.length_flatMap]
      have hlt : bidx.val < rrBasis7.length := by rw [hlen]; exact bidx.isLt
      have hflag : (rrBasis7.getD bidx.val (0, 0, 0)).2.2 = 0 ∨
          (rrBasis7.getD bidx.val (0, 0, 0)).2.2 = 1 := by
        rw [List.getD_eq_getElem _ _ hlt]
        exact rrBasis7_flag _ (List.getElem_mem hlt)
      rw [hget] at hflag
      exact hflag
    rcases hbj0or1 with hb0 | hb1
    · subst bj
      simp [tangentRowEntryX4, Polynomial.derivative_C_mul,
        Polynomial.eval_mul, Polynomial.eval_C]
      <;> ring
    · subst bj
      simp [tangentRowEntryX4, Polynomial.derivative_C_mul,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.derivative_X_pow]
      <;> push_cast
      <;> ring

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

/-! ## Degree bounds, K=4 instance (new this pass)

The K=2 degree-bookkeeping trio (`Ypoly_natDegree_le_zero`/
`Epoly_natDegree_le_three`/`Npoly_natDegree_le_six`,
`DecoupledSystemRegular.lean`) has no K=4 counterpart yet — this is
exactly the gap flagged at the top of this file ("porting it... needs the
actual recipe") and in `ROADMAP-alpha-locus.md`'s status notes. Ported
here using `rrBasis7`'s CONCRETE value (already pinned down by
`rrBasis7_yIdx_eq`/this file's own module docstring:
`[(0,0,0),(2,1,0),(4,2,0),(5,0,1),(6,3,0),(7,1,1),(8,4,0)]`), same
`Epoly`-style "bound every summand uniformly" proof shape throughout —
`Ypoly4` has TWO `bj=1` entries (indices 3, 5; `bi = 0, 1`), so unlike
`Ypoly_natDegree_le_zero`'s single-survivor collapse, `Ypoly4` needs the
`Epoly`-style uniform bound too (`natDegree_sum_le` + a per-summand `bi ≤
1` fact), not a collapse-to-one-term argument. -/

/-- `Ypoly4`'s degree bound: `≤ 1`, matching the module docstring's
"`c₃ + c₅·x` shape" description (`rrBasis7`'s two `bj=1` entries have
`bi ∈ {0,1}`). Same `natDegree_sum_le`/`Finset.sup_le` shape as
`Epoly_natDegree_le_three`, not `Ypoly_natDegree_le_zero`'s collapse
argument — there is no single surviving summand here. -/
theorem Ypoly4_natDegree_le_one (P1 P2 : F p × F p)
    (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p) :
    (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).natDegree ≤ 1 := by
  unfold Ypoly4
  refine le_trans (Polynomial.natDegree_sum_le _ _) ?_
  refine Finset.sup_le (fun bidx _ => ?_)
  simp only [Function.comp_apply]
  have hbi1 : (rrBasis7.getD bidx.val (0, 0, 0)).2.2 = 1 →
      (rrBasis7.getD bidx.val (0, 0, 0)).2.1 ≤ 1 := by
    -- Rewrite through `rrBasis7_eq` (the `Perm`+`Sorted`-uniqueness proof of
    -- `rrBasis7`'s literal value, which never kernel-computes `mergeSort`)
    -- so the goal becomes a `List.getD` lookup into a literal 7-element
    -- list — decidable by ordinary `Nat` arithmetic, no `mergeSort`
    -- unfolding needed. This was the `decide`-on-`mergeSort` blocker
    -- (WF-recursive defs are kernel-irreducible, lean4#5192); `rrBasis7_eq`
    -- routes around it entirely rather than needing ChatGPT.
    rw [rrBasis7_eq]
    fin_cases bidx <;> decide
  revert hbi1
  generalize rrBasis7.getD bidx.val (0, 0, 0) = t
  obtain ⟨a, bi, bj⟩ := t
  intro hbi1
  dsimp only at hbi1 ⊢
  split
  · next hbj => compute_degree! <;> exact hbi1 hbj
  · simp

/-- `Epoly4`'s degree bound: `≤ 4`, from `rrBasis7`'s largest `bj=0` entry
`(8,4,0)`. Same shape as `Epoly_natDegree_le_three`, `Fin 5 → Fin 7` and
bound `3 → 4`. -/
theorem Epoly4_natDegree_le_four (P1 P2 : F p × F p)
    (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p) :
    (Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).natDegree ≤ 4 := by
  unfold Epoly4
  refine le_trans (Polynomial.natDegree_sum_le _ _) ?_
  refine Finset.sup_le (fun bidx _ => ?_)
  simp only [Function.comp_apply]
  have hbi4 : (rrBasis7.getD bidx.val (0, 0, 0)).2.1 ≤ 4 := by
    -- Same fix as `Ypoly4_natDegree_le_one`'s `hbi1` above: rewrite through
    -- `rrBasis7_eq` first, then it's a literal-list lookup, no `mergeSort`
    -- kernel-irreducibility blocker.
    rw [rrBasis7_eq]
    fin_cases bidx <;> decide
  revert hbi4
  generalize rrBasis7.getD bidx.val (0, 0, 0) = t
  obtain ⟨a, bi, bj⟩ := t
  intro hbi4
  dsimp only at hbi4 ⊢
  split
  · compute_degree!
  · simp

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
noncomputable def Npoly4 (c0 c1 c2 c3 c4 : F p) (P1 P2 : F p × F p)
    (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p) :
    Polynomial (F p) :=
  Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ^ 2 -
    curvePoly p c0 c1 c2 c3 c4 * Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ^ 2

/-- `Npoly4`'s degree bound: `≤ 8`, assembled from `Epoly4_natDegree_le_four`/
`Ypoly4_natDegree_le_one`/`curvePoly_natDegree` (`= 5`, already proved
upstream, no `fAtX`/tower promotion needed here since everything is over
plain `F p` — see this file's own module docstring). Same
`natDegree_sub_le`/`natDegree_mul_le`/`natDegree_pow_le` triangle-inequality
assembly as `Npoly_natDegree_le_six`: `max (2*4) (5 + 2*1) = max 8 7 = 8`. -/
theorem Npoly4_natDegree_le_eight (c0 c1 c2 c3 c4 : F p) (P1 P2 : F p × F p)
    (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p) :
    (Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).natDegree ≤ 8 := by
  unfold Npoly4
  have hE4 := Epoly4_natDegree_le_four p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1
  have hY1 := Ypoly4_natDegree_le_one p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1
  have hf5 : (curvePoly p c0 c1 c2 c3 c4).natDegree = 5 := curvePoly_natDegree p c0 c1 c2 c3 c4
  have hE2 : (Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ^ 2).natDegree ≤ 8 :=
    le_trans (Polynomial.natDegree_pow_le_of_le 2 hE4) (by norm_num)
  have hY2 : (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ^ 2).natDegree ≤ 2 :=
    le_trans (Polynomial.natDegree_pow_le_of_le 2 hY1) (by norm_num)
  have hfY2 : (curvePoly p c0 c1 c2 c3 c4 *
      Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ^ 2).natDegree ≤ 7 := by
    have hstep := Polynomial.natDegree_mul_le (p := curvePoly p c0 c1 c2 c3 c4)
      (q := Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ^ 2)
    omega
  exact le_trans
    (Polynomial.natDegree_sub_le (Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ^ 2)
      (curvePoly p c0 c1 c2 c3 c4 * Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ^ 2))
    (max_le hE2 (le_trans hfY2 (by norm_num)))

/-- `N(x)` for the TANGENT case (`P1=P2`, one point `(px,py)` with
multiplicity 2) — same `E²-fY²` formula as `Npoly4`, substituting
`Epoly4Tangent`/`Ypoly4Tangent`. This is `Npoly4`'s replacement when the
two literal-point anchors collapse into one tangent anchor, per
`ROADMAP-alpha-locus.md`'s tangent-row section. -/
noncomputable def Npoly4Tangent (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p) :
    Polynomial (F p) :=
  Epoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 ^ 2 -
    curvePoly p c0 c1 c2 c3 c4 * Ypoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 ^ 2

/-- The quotient `N(x) / ((x-P1.x)(x-P2.x)(x²+ua1*x+ua0)(x²+u1*x+u0))` —
the K=4 analogue of `curBeforeMonic`, dividing out BOTH known quadratics
(`u_a` and the target `u`) directly rather than by literal roots, per this
file's module docstring ("the `u_a` split-vs-irreducible fork" section).
Stated unconditionally via `/ₘ` (always defined), correctness deferred to
wherever this is used against the analogues of `dvd_N_anchor1`/
`dvd_N_anchor2`/`dvd_N_u` — **none of those three divisibility facts are
proved for this K=4 instance yet**, left for the next pass exactly as
flagged in the module docstring. -/
noncomputable def curBeforeMonic4 (c0 c1 c2 c3 c4 : F p) (P1 P2 : F p × F p)
    (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p) :
    Polynomial (F p) :=
  (((Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 /ₘ (X - C P1.1))
      /ₘ (X - C P2.1))
    /ₘ (X ^ 2 + C ua1 * X + C ua0))
    /ₘ (X ^ 2 + C u1 * X + C u0)

/-- `curBeforeMonic4`'s degree, unconditionally, as a subtraction from
`Npoly4`'s: dividing out two linear factors (`X-P1.1`, `X-P2.1`) and two
monic quadratics (`u_a`, target `u`) in sequence via `/ₘ`. Same shape as
`curBeforeMonic_natDegree_eq_sub`, one more quadratic division (`- 2`
twice, not once) since K=4 has TWO known quadratic factors (`u_a` and the
target `u`) where K=2 only had the target. No tower/`algebraMap`
promotion needed here (unlike the K=2 proof) since everything is already
over plain `F p` — `monicity!`/`compute_degree!` run directly, no
`generalize`-first heartbeat workaround required. -/
theorem curBeforeMonic4_natDegree_eq_sub (c0 c1 c2 c3 c4 : F p) (P1 P2 : F p × F p)
    (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p) :
    (curBeforeMonic4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).natDegree =
      (Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).natDegree
        - 1 - 1 - 2 - 2 := by
  have hmonicUa : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).Monic := by monicity!
  have hdegUa : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).natDegree = 2 := by
    compute_degree!
  have hmonicU : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).Monic := by monicity!
  have hdegU : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).natDegree = 2 := by
    compute_degree!
  have hmonic1 : (X - C P1.1 : Polynomial (F p)).Monic := Polynomial.monic_X_sub_C _
  have hmonic2 : (X - C P2.1 : Polynomial (F p)).Monic := Polynomial.monic_X_sub_C _
  simp only [curBeforeMonic4]
  rw [Polynomial.natDegree_divByMonic _ hmonicU,
      Polynomial.natDegree_divByMonic _ hmonicUa,
      Polynomial.natDegree_divByMonic _ hmonic2,
      Polynomial.natDegree_divByMonic _ hmonic1,
      Polynomial.natDegree_X_sub_C, Polynomial.natDegree_X_sub_C, hdegUa, hdegU]

/-- **Assembly.** `curBeforeMonic4.natDegree ≤ 2`, unconditional — combines
`curBeforeMonic4_natDegree_eq_sub` and `Npoly4_natDegree_le_eight`
(`Npoly4.natDegree - 1 - 1 - 2 - 2 ≤ 8 - 1 - 1 - 2 - 2 = 2`, truncated `ℕ`
subtraction monotone in its first argument). Matches
`curBeforeMonic_natDegree_le_two`'s role for K=2: the honest unconditional
half, correctness of the EXACT degree (`= 2`, not just `≤ 2`) deferred to
a genericity hypothesis at whichever call site needs it, same as K=2. -/
theorem curBeforeMonic4_natDegree_le_two (c0 c1 c2 c3 c4 : F p) (P1 P2 : F p × F p)
    (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p) :
    (curBeforeMonic4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).natDegree ≤ 2 := by
  rw [curBeforeMonic4_natDegree_eq_sub]
  have h8 := Npoly4_natDegree_le_eight p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1
  omega

/-! ## `u_RS`/`v_RS`, K=4 instance — `Reduce`'s actual output

Direct K=4 rescaling of `DataDerivationMumford.lean`'s `uRS`/`uRS_monic`/
`vRS`. No `K2`-tower promotion needed here (unlike the K=2 originals,
which live in `Polynomial (K2 p c0 c1 c2 c3 c4)`): everything in this file
is already over plain `F p = ZMod p`, which is a field directly from
`Fact (Nat.Prime p)` — no extra `Fact (p ≠ 2)` needed, since that fact
was only ever required for `K2`'s field-extension instance
(`factIrreducible_K2`), not for anything in this construction. -/

section URS4

variable (P1 P2 : F p × F p) (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)

/-- `u_RS(x)`, monic-normalized `curBeforeMonic4` — the K=4 instance of
`uRS` (`DataDerivationMumford.lean`), same `leadingCoeff⁻¹`-scaling
construction. Well-defined (as the correct monic associate of
`curBeforeMonic4`) only once `curBeforeMonic4 ≠ 0`, recorded as a
hypothesis on `uRS4_monic` below rather than baked into the definition
itself, matching `uRS`'s own convention. -/
noncomputable def uRS4 : Polynomial (F p) :=
  C (curBeforeMonic4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff⁻¹ *
    curBeforeMonic4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1

/-- `uRS4` really is monic, given `curBeforeMonic4 ≠ 0` — direct rescaling
of `uRS_monic`'s proof, unchanged in substance (same
`natDegree_C_mul_eq_of_mul_eq_one`/`mul_inv_cancel₀`/`inv_mul_cancel₀`
argument; only the underlying quotient polynomial's name differs). -/
theorem uRS4_monic
    (hcur : curBeforeMonic4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0) :
    (uRS4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).Monic := by
  simp only [uRS4]
  set q := curBeforeMonic4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 with hq
  -- Goal now: `(C q.leadingCoeff⁻¹ * q).Monic`.
  have hlc : q.leadingCoeff ≠ 0 := (not_congr Polynomial.leadingCoeff_eq_zero).mpr hcur
  have hau : q.leadingCoeff * q.leadingCoeff⁻¹ = 1 := mul_inv_cancel₀ hlc
  have hdeg : (C q.leadingCoeff⁻¹ * q).natDegree = q.natDegree :=
    Polynomial.natDegree_C_mul_eq_of_mul_eq_one hau
  rw [Polynomial.Monic.def]
  change (C q.leadingCoeff⁻¹ * q).coeff (C q.leadingCoeff⁻¹ * q).natDegree = 1
  rw [hdeg, Polynomial.coeff_C_mul]
  exact inv_mul_cancel₀ hlc

/-- `uRS4`'s degree is `≤ 2`, unconditional — combines `curBeforeMonic4`'s
own `≤ 2` bound with the fact that `C a * q` never raises `natDegree`.
Split on whether `curBeforeMonic4 = 0` rather than reaching for an
unconditional `natDegree_C_mul_le`-style lemma (no such unconditional
statement was confirmed against current Mathlib, only the `≠ 0`-hypothesis
versions `natDegree_C_mul_of_mul_ne_zero` already used by `uRS4_monic`'s
argument): if `curBeforeMonic4 = 0` then `uRS4 = C 0⁻¹ * 0 = 0` (`0⁻¹ = 0`
in a field), degree `0 ≤ 2` trivially; otherwise `uRS4_monic`'s own
`hlc`/`hau` argument applies and gives degree EQUALITY with
`curBeforeMonic4`, which is `≤ 2` by `curBeforeMonic4_natDegree_le_two`. -/
theorem uRS4_natDegree_le_two :
    (uRS4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).natDegree ≤ 2 := by
  simp only [uRS4]
  set q := curBeforeMonic4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 with hq
  have hbound := curBeforeMonic4_natDegree_le_two p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1
  rw [← hq] at hbound
  by_cases hcur : q = 0
  · simp [hcur]
  · have hlc : q.leadingCoeff ≠ 0 := (not_congr Polynomial.leadingCoeff_eq_zero).mpr hcur
    have hau : q.leadingCoeff⁻¹ * q.leadingCoeff ≠ 0 :=
      mul_ne_zero (inv_ne_zero hlc) hlc
    have hdeg : (C q.leadingCoeff⁻¹ * q).natDegree = q.natDegree :=
      Polynomial.natDegree_C_mul_of_mul_ne_zero hau
    rw [hdeg]
    exact hbound

/-- **`v_RS(x) = -E4(x) * Y4(x)⁻¹ mod uRS4(x)`** — the K=4 instance of
`vRS` (`DataDerivationMumford.lean`), same `EuclideanDomain.gcdA`
Bézout-coefficient construction (`Polynomial (F p)` is a Euclidean domain,
being a polynomial ring over a field). As with `vRS`, the coprimality
hypothesis `_hgcd` is only needed to typecheck the statement's INTENDED
reading (`gcdA Ypoly4 uRS4` really is "the" inverse of `Ypoly4` mod
`uRS4`); the bare definition compiles unconditionally, and `_hgcd` is
carried as an unused argument purely so callers are forced to supply it
alongside `uRS4_monic`'s `hcur` wherever `vRS4`'s VALUE is actually used
(e.g. a future `vRS4_sq_eq_f_mod_uRS4` Mumford-identity theorem), matching
`vRS`'s own convention exactly. -/
noncomputable def vRS4
    (_hgcd : IsCoprime (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
      (uRS4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)) :
    Polynomial (F p) :=
  (-(Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) *
      EuclideanDomain.gcdA (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
        (uRS4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)) %ₘ
    uRS4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1

end URS4

/-! ## Root multiplicity ≥ 2 from value+derivative vanishing (general lemma)

Per `ROADMAP-alpha-locus.md`'s tangency-case scoping (step (i)): a
standalone `Polynomial (F p)`-level fact, no `AlphaReduce`-specific
content, needed to turn "phi's value AND derivative-along-the-branch
vanish at `x = px`" (the K=4 tangent-anchor row-block's actual content,
confirmed directly against `phi_general.zip`'s `fill_f_tay!`/
`branch_series!`) into `(X - C px)^2 ∣ N` for the K=4 tangent case,
replacing the `IsCoprime (X - C P1.1) (X - C P2.1)`-based argument
`uRS4_dvd_Npoly4` currently uses for the (still separately needed)
simple-point case.

**Route, confirmed against current Mathlib4 docs before writing anything**
(`Mathlib.Algebra.Polynomial.RingDivision`,
`Mathlib.Algebra.Polynomial.Degree.TrailingDegree`): `rootMultiplicity t p
= (p.comp (X + C t)).natTrailingDegree`
(`Polynomial.rootMultiplicity_eq_natTrailingDegree`), and
`natTrailingDegree` is bounded below by `Polynomial.le_natTrailingDegree`
once enough low coefficients vanish. The two coefficients that matter are
`(p.comp (X + C t)).coeff 0 = p.eval t` (evaluation at the shift point)
and `(p.comp (X + C t)).coeff 1 = (derivative p).eval t` (the standard
"linear coefficient of a Taylor shift is the derivative" fact — confirmed
via `Polynomial.hasseDeriv_one : hasseDeriv 1 f = derivative f` composed
with `Polynomial.taylor_coeff`, rather than assumed). -/

/-- The Taylor-shift `p.comp (X + C t)`'s coefficient-1 is `(derivative
p).eval t` — the general fact `rootMultiplicity_ge_two_of_eval_derivative_eq_zero`
below needs, isolated here so it can be checked/reused independently of
the rest of that proof. Route: `Polynomial.taylor_coeff` gives coefficient
`k` of `taylor t f` as `(hasseDeriv k f).eval t`, and `taylor t f` is
definitionally `f.comp (X + C t)` (`Polynomial.taylor`'s own definition);
`hasseDeriv_one` identifies `hasseDeriv 1` with the ordinary `derivative`. -/
theorem comp_X_add_C_coeff_one (f : Polynomial (F p)) (t : F p) :
    (f.comp (X + C t)).coeff 1 = (derivative f).eval t := by
  have h := Polynomial.taylor_coeff (r := t) (f := f) 1
  rw [Polynomial.taylor_apply] at h
  rw [h, Polynomial.hasseDeriv_one]

/-- The Taylor-shift's coefficient-0 is `f.eval t` — the `n=0` counterpart
of `comp_X_add_C_coeff_one` above, same route (`taylor_coeff` + `taylor_apply`
+ `hasseDeriv_zero : hasseDeriv 0 f = f`), needed for the `m=0` case of
`rootMultiplicity_ge_two_of_eval_derivative_eq_zero`'s `le_natTrailingDegree`
argument below (that case's goal doesn't unify with `h0 : f.eval t = 0`
directly without this bridge). -/
theorem comp_X_add_C_coeff_zero (f : Polynomial (F p)) (t : F p) :
    (f.comp (X + C t)).coeff 0 = f.eval t := by
  have h := Polynomial.taylor_coeff (r := t) (f := f) 0
  rw [Polynomial.taylor_apply] at h
  rw [h, Polynomial.hasseDeriv_zero]
  rfl

/-- **The general lemma** (no `AlphaReduce`-specific content): if a
polynomial `f` and its derivative both vanish at `t`, then `t` is a root
of `f` of multiplicity at least 2 — i.e. `(X - C t)^2 ∣ f`. This is the
tool the K=4 tangent-anchor case needs to turn `phi`'s value+derivative
vanishing (from the `m=2` row-block, confirmed against
`phi_general.zip`) into a squared-factor divisibility of `Npoly4`, in
place of the `IsCoprime`-based argument the simple-point case uses.

`p` is passed explicitly (not left to auto-bound-implicit inference) to
avoid the argument-order confusion an earlier attempt this pass hit at
the call site in `sq_dvd_of_eval_derivative_eq_zero` below (`hf` being
fed into a slot Lean expected a `Nat.Prime` witness for). -/
theorem rootMultiplicity_ge_two_of_eval_derivative_eq_zero
    (p : ℕ) [Fact (Nat.Prime p)] {f : Polynomial (F p)} {t : F p} (hf : f ≠ 0)
    (h0 : f.eval t = 0) (h1 : (derivative f).eval t = 0) :
    2 ≤ f.rootMultiplicity t := by
  rw [Polynomial.rootMultiplicity_eq_natTrailingDegree]
  refine Polynomial.le_natTrailingDegree ?_ ?_
  · -- `f.comp (X + C t) ≠ 0`: `comp` with a degree-1 (hence non-constant,
    -- injective-on-evaluation) polynomial doesn't kill a nonzero `f` —
    -- via `Polynomial.taylor`, an additive equiv, so `taylor_eq_zero`
    -- reduces this to `f ≠ 0` directly.
    have h := (Polynomial.taylor_eq_zero (r := t) (f := f)).not.mpr hf
    rwa [Polynomial.taylor_apply] at h
  · intro m hm
    interval_cases m
    · rw [comp_X_add_C_coeff_zero]; exact h0
    · rw [comp_X_add_C_coeff_one]; exact h1

/-- **Squared-factor form**, the version `uRS4_dvd_Npoly4`'s tangent case
will actually invoke: `(X - C t)^2 ∣ f` follows from value+derivative
vanishing. Route (confirmed against Mathlib4 docs — no
`Polynomial.pow_rootMultiplicity_dvd` lemma exists; the actual name is
`Polynomial.pow_mul_divByMonic_rootMultiplicity_eq`):
`(X - C t) ^ rootMultiplicity t f * (f /ₘ (X - C t) ^ rootMultiplicity t f)
= f` gives `(X - C t) ^ rootMultiplicity t f ∣ f` directly (anonymous-
constructor witness, rather than `Dvd.intro`, whose exact argument order
wasn't confirmed against current docs this pass), then `pow_dvd_pow`
bridges the exponent down from the (possibly larger) actual multiplicity
to the `2` this lemma needs, using the bound above. Same explicit-`p`
convention as the lemma above, for the same reason. -/
theorem sq_dvd_of_eval_derivative_eq_zero
    (p : ℕ) [Fact (Nat.Prime p)] {f : Polynomial (F p)} {t : F p} (hf : f ≠ 0)
    (h0 : f.eval t = 0) (h1 : (derivative f).eval t = 0) :
    (X - C t) ^ 2 ∣ f := by
  have hge := rootMultiplicity_ge_two_of_eval_derivative_eq_zero p (f := f) (t := t) hf h0 h1
  have hmul := Polynomial.pow_mul_divByMonic_rootMultiplicity_eq f t
  -- `a ∣ b` unfolds to `∃ c, b = a * c`; supply the quotient and `hmul`'s
  -- symm directly rather than risk `Dvd.intro`'s exact argument order
  -- (not confirmed against current Mathlib4 docs this pass).
  have hdvd : (X - C t) ^ f.rootMultiplicity t ∣ f :=
    ⟨f /ₘ (X - C t) ^ f.rootMultiplicity t, hmul.symm⟩
  exact (pow_dvd_pow (X - C t) hge).trans hdvd

/-! ## The tangent-case squared-factor divisibility fact — steps (iii)/(iv)

Closes `ROADMAP-alpha-locus.md`'s recommended-scope items (iii) (redo the
`P1=P2` divisibility using the value/derivative lemmas above) using the
row-identity facts `rowTangent0_defining_eq_aux`/`rowTangent1_defining_eq_aux`
built earlier in this file, now that `sq_dvd_of_eval_derivative_eq_zero`
is available to conclude from them. -/

/-- **`(X - C px)² ∣ Npoly4Tangent`** — the tangent-case analogue of
`dvd_N_P1`/`dvd_N_P2`. Route: `Npoly4Tangent.eval px = 0` follows exactly
as in `dvd_N_P1` (from `rowTangent0_defining_eq_aux` + the curve relation
`py²=f(px)`); `(derivative Npoly4Tangent).eval px = 0` needs the
product/chain rule on `E²-fY²` plus `rowTangent1_defining_eq_aux` (the
branch-derivative row) and, crucially, `branchDeriv4`'s own defining
property `2*py*branchDeriv4 = f'(px)` (valid since `py≠0`) to cancel the
`f'(px)*Y(px)²` term against the `2*f(px)*Y(px)*Y'(px)` cross-term. Both
value and derivative vanishing then give `(X-C px)²∣N` via
`sq_dvd_of_eval_derivative_eq_zero`.

**New hypothesis surfaced this pass, not previously flagged anywhere in
this file**: `hp2 : (2:F p)≠0`, i.e. `p ≠ 2`. `branchDeriv4` divides by
`2*py`, so at `p=2` it silently returns `0` (division by zero convention)
and `2*py*branchDeriv4 = f'(px)` becomes the false statement `0=f'(px)`.
This file's module docstring elsewhere claims "no extra `Fact (p≠2)`
needed" for the K=4 construction generally — that claim is still correct
for the SIMPLE-point case (`dvd_N_P1`/`dvd_N_P2`/etc., which never divide
by `2`), but is now known to be false for the TANGENT case specifically:
odd characteristic is a genuine precondition of the branch-derivative
construction (standard — `p=2` hyperelliptic curves need Artin-Schreier
theory instead of `y²=f(x)`'s usual calculus, well outside this project's
scope), not a Lean-engineering artifact. Should be folded into whatever
`Bad`/exceptional-locus bookkeeping this project already does for `p=2`
(if any currently exists), rather than silently assumed away. -/
theorem dvd_N_P1P2_tangent (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (hA : MatrixNondegenerate4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hpy : py ≠ 0) (hp2 : (2 : F p) ≠ 0)
    (hP_curve : py ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval px)
    (hNe : Npoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0) :
    (X - C px) ^ 2 ∣ Npoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 := by
  have hval := rowTangent0_defining_eq_aux p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 hA
  have hder := rowTangent1_defining_eq_aux p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 hA
  have hEeq : (Epoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1).eval px =
      -(py * (Ypoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1).eval px) := by
    exact eq_neg_of_add_eq_zero_left hval
  have h0 : (Npoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1).eval px = 0 := by
    unfold Npoly4Tangent
    rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_mul, Polynomial.eval_pow,
      hEeq, neg_sq, mul_pow, ← hP_curve]
    ring
  have hbranch : 2 * py * branchDeriv4 p c0 c1 c2 c3 c4 px py =
      (derivative (curvePoly p c0 c1 c2 c3 c4)).eval px := by
    unfold branchDeriv4
    have h2py : (2 : F p) * py ≠ 0 := mul_ne_zero hp2 hpy
    field_simp
  have hderE : (derivative (Epoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1)).eval
      px = -(py * (derivative
        (Ypoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1)).eval px) -
      (Ypoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1).eval px *
        branchDeriv4 p c0 c1 c2 c3 c4 px py := by
    rw [add_assoc] at hder
    have h := eq_neg_of_add_eq_zero_left hder
    rw [neg_add] at h
    simpa only [sub_eq_add_neg] using h
  have h1 : (derivative (Npoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1)).eval px
      = 0 := by
    have hNsq : Npoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 =
        Epoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 *
          Epoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 -
        curvePoly p c0 c1 c2 c3 c4 *
          (Ypoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 *
            Ypoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1) := by
      unfold Npoly4Tangent; ring
    rw [hNsq]
    simp only [Polynomial.derivative_sub, Polynomial.derivative_mul, Polynomial.eval_sub,
      Polynomial.eval_add, Polynomial.eval_mul]
    rw [hderE, hEeq, ← hbranch, ← hP_curve]
    ring
  exact sq_dvd_of_eval_derivative_eq_zero p
    (f := Npoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1) (t := px) hNe h0 h1

/-! ## Tangent-case mod-`u_a`/mod-target row identities — closing the
`hUa`/`hU` gap for `Npoly4Tangent`

`curBeforeMonic4Tangent_dvd_Npoly4Tangent`/`uRS4Tangent_dvd_Npoly4Tangent`
(below, in the "Tangent-anchor quotient assembly" section) both took
`hUa`/`hU` (`(X²+ua1*X+ua0) ∣ Npoly4Tangent` and `(X²+u1*X+u0) ∣
Npoly4Tangent`) as raw hypotheses — this section proves them, mirroring
`row23_defining_eq_aux`/`row45_defining_eq_aux`/`dvd_of_row_identity4`/
`dvd_N_ua`/`dvd_N_u4` exactly, substituting the tangent Cramer-rule
objects (`matrixA4Tangent`/`rhsVec4Tangent`/`coeffsOut4Tangent`/
`cramerSolution4Tangent`) for their non-tangent counterparts. Rows 2–5 of
`matrixA4Tangent`/`rhsVec4Tangent` are byte-identical in shape to
`matrixA4`/`rhsVec4`'s (`matrixA4Tangent_row23_eval`/`_row45_eval`,
`rhsVec4Tangent_row23_eval`/`_row45_eval`, proved earlier in this file),
so the same five-step Cramer's-rule argument goes through with no new
mathematical content — only the object names change. -/

section TangentRowIdentity4RowsTwoFour

variable (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)

/-- **The seven-slot defining identity for the mod-`u_a` rows, tangent
case** (rows 2–3) — the tangent analogue of `row23_defining_eq_aux`,
substituting `matrixA4Tangent`/`rhsVec4Tangent`/`coeffsOut4Tangent`/
`cramerSolution4Tangent` for `matrixA4`/`rhsVec4`/`coeffsOut4`/
`cramerSolution4`. -/
private theorem rowTangent23_defining_eq_aux
    (hA : MatrixNondegenerate4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1)
    (a : Fin 2) :
    (∑ bidx : Fin 7,
      let (_, bi, bj) := rrBasis7.getD bidx.val (0, 0, 0)
      coeffsOut4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 bidx *
        (let (r0, r1) := reduceMonomialModU p ua0 ua1 va0 va1 bi bj
         if a.val = 0 then r0 else r1)) = 0 := by
  set A := matrixA4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 with hA_def
  set rhs := rhsVec4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 with hrhs_def
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
      cramerSolution4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 col :=
    fun col => rfl
  simp only [hcramerSolution] at hrow'
  have hApply : ∀ col : Fin 6, A ⟨2 + a.val, haRow⟩ col =
      let (_, bi, bj) := rrBasis7.getD (otherIdx7.getD col.val 0) (0, 0, 0)
      let (r0, r1) := reduceMonomialModU p ua0 ua1 va0 va1 bi bj
      if a.val = 0 then r0 else r1 := fun col =>
    matrixA4Tangent_row23_eval p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 a col
  have hrhsApply : rhs ⟨2 + a.val, haRow⟩ =
      let (_, bi_n, bj_n) := rrBasis7.getD yIdx7 (0, 1, 1)
      let (rn0, rn1) := reduceMonomialModU p ua0 ua1 va0 va1 bi_n bj_n
      (-(if a.val = 0 then rn0 else rn1)) :=
    rhsVec4Tangent_row23_eval p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 a
  clear_value A rhs
  rw [hrhsApply] at hrow'
  have hmoved : (∑ col : Fin 6,
      coeffsOut4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 (otherMap4 col) *
      (let (_, bi, bj) := rrBasis7.getD (otherIdx7.getD col.val 0) (0, 0, 0)
       let (r0, r1) := reduceMonomialModU p ua0 ua1 va0 va1 bi bj
       if a.val = 0 then r0 else r1)) +
      coeffsOut4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1
        ⟨yIdx7, yIdx7_lt_seven⟩ *
        (let (_, bi_n, bj_n) := rrBasis7.getD yIdx7 (0, 1, 1)
         let (rn0, rn1) := reduceMonomialModU p ua0 ua1 va0 va1 bi_n bj_n
         if a.val = 0 then rn0 else rn1) = 0 := by
    have hcoeffsOutY : coeffsOut4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1
        ⟨yIdx7, yIdx7_lt_seven⟩ = 1 := by
      unfold coeffsOut4Tangent; rw [dif_pos rfl]
    rw [hcoeffsOutY, one_mul]
    have hstep : ∑ col : Fin 6,
        coeffsOut4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 (otherMap4 col) *
        (let (_, bi, bj) := rrBasis7.getD (otherIdx7.getD col.val 0) (0, 0, 0)
         let (r0, r1) := reduceMonomialModU p ua0 ua1 va0 va1 bi bj
         if a.val = 0 then r0 else r1) =
        ∑ col : Fin 6,
        cramerSolution4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 col *
        (let (_, bi, bj) := rrBasis7.getD (otherIdx7.getD col.val 0) (0, 0, 0)
         let (r0, r1) := reduceMonomialModU p ua0 ua1 va0 va1 bi bj
         if a.val = 0 then r0 else r1) := by
      apply Finset.sum_congr rfl
      intro col _
      rw [coeffsOut4Tangent_otherMap p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 col]
    have horder : (∑ col : Fin 6,
          cramerSolution4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 col *
          (let (_, bi, bj) := rrBasis7.getD (otherIdx7.getD col.val 0) (0, 0, 0)
           let (r0, r1) := reduceMonomialModU p ua0 ua1 va0 va1 bi bj
           if a.val = 0 then r0 else r1))
        = ∑ col : Fin 6, A ⟨2 + a.val, haRow⟩ col *
            cramerSolution4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 col := by
      apply Finset.sum_congr rfl
      intro col _
      rw [mul_comm (cramerSolution4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1
        u0 u1 v0 v1 col), hApply col]
    rw [hstep, horder, hrow']
    exact neg_add_cancel _
  set Fsum : Fin 7 → F p := fun bidx =>
    coeffsOut4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 bidx *
      (let (_, bi, bj) := rrBasis7.getD bidx.val (0, 0, 0)
       let (r0, r1) := reduceMonomialModU p ua0 ua1 va0 va1 bi bj
       if a.val = 0 then r0 else r1) with hF_def
  have hFcol : ∀ col : Fin 6, Fsum (otherMap4 col) =
      coeffsOut4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 (otherMap4 col) *
      (let (_, bi, bj) := rrBasis7.getD (otherIdx7.getD col.val 0) (0, 0, 0)
       let (r0, r1) := reduceMonomialModU p ua0 ua1 va0 va1 bi bj
       if a.val = 0 then r0 else r1) := by
    intro col
    have hidx : (otherMap4 col).val = otherIdx7.getD col.val 0 := rfl
    simp only [hF_def, hidx]
  have hFy : Fsum (⟨yIdx7, yIdx7_lt_seven⟩ : Fin 7) =
      coeffsOut4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1
        ⟨yIdx7, yIdx7_lt_seven⟩ *
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
          (∑ col : Fin 6,
            coeffsOut4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1
              (otherMap4 col) *
            (let (_, bi, bj) := rrBasis7.getD (otherIdx7.getD col.val 0) (0, 0, 0)
             let (r0, r1) := reduceMonomialModU p ua0 ua1 va0 va1 bi bj
             if a.val = 0 then r0 else r1)) +
            coeffsOut4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1
              ⟨yIdx7, yIdx7_lt_seven⟩ *
              (let (_, bi_n, bj_n) := rrBasis7.getD yIdx7 (0, 1, 1)
               let (rn0, rn1) := reduceMonomialModU p ua0 ua1 va0 va1 bi_n bj_n
               if a.val = 0 then rn0 else rn1) := by
            rw [Finset.sum_congr rfl (fun col _ => hFcol col), hFy]
      _ = 0 := hmoved
  have hsum7' : ∑ bidx : Fin 7, Fsum bidx = 0 := hsum7 ▸ hmoved'
  rw [hF_def] at hsum7'
  exact hsum7'

/-- **The seven-slot defining identity for the mod-target-`u` rows,
tangent case** (rows 4–5) — the tangent analogue of `row45_defining_eq_aux`,
identical argument to `rowTangent23_defining_eq_aux` above with the row
offset shifted from `2+a.val` to `4+a.val` and `matrixA4Tangent_row45_eval`/
`rhsVec4Tangent_row45_eval` supplying the row-unfolding step. -/
private theorem rowTangent45_defining_eq_aux
    (hA : MatrixNondegenerate4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1)
    (a : Fin 2) :
    (∑ bidx : Fin 7,
      let (_, bi, bj) := rrBasis7.getD bidx.val (0, 0, 0)
      coeffsOut4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 bidx *
        (let (r0, r1) := reduceMonomialModU p u0 u1 v0 v1 bi bj
         if a.val = 0 then r0 else r1)) = 0 := by
  set A := matrixA4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 with hA_def
  set rhs := rhsVec4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 with hrhs_def
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
      cramerSolution4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 col :=
    fun col => rfl
  simp only [hcramerSolution] at hrow'
  have hApply : ∀ col : Fin 6, A ⟨4 + a.val, haRow⟩ col =
      let (_, bi, bj) := rrBasis7.getD (otherIdx7.getD col.val 0) (0, 0, 0)
      let (r0, r1) := reduceMonomialModU p u0 u1 v0 v1 bi bj
      if a.val = 0 then r0 else r1 := fun col =>
    matrixA4Tangent_row45_eval p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 a col
  have hrhsApply : rhs ⟨4 + a.val, haRow⟩ =
      let (_, bi_n, bj_n) := rrBasis7.getD yIdx7 (0, 1, 1)
      let (rn0, rn1) := reduceMonomialModU p u0 u1 v0 v1 bi_n bj_n
      (-(if a.val = 0 then rn0 else rn1)) :=
    rhsVec4Tangent_row45_eval p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 a
  clear_value A rhs
  rw [hrhsApply] at hrow'
  have hmoved : (∑ col : Fin 6,
      coeffsOut4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 (otherMap4 col) *
      (let (_, bi, bj) := rrBasis7.getD (otherIdx7.getD col.val 0) (0, 0, 0)
       let (r0, r1) := reduceMonomialModU p u0 u1 v0 v1 bi bj
       if a.val = 0 then r0 else r1)) +
      coeffsOut4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1
        ⟨yIdx7, yIdx7_lt_seven⟩ *
        (let (_, bi_n, bj_n) := rrBasis7.getD yIdx7 (0, 1, 1)
         let (rn0, rn1) := reduceMonomialModU p u0 u1 v0 v1 bi_n bj_n
         if a.val = 0 then rn0 else rn1) = 0 := by
    have hcoeffsOutY : coeffsOut4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1
        ⟨yIdx7, yIdx7_lt_seven⟩ = 1 := by
      unfold coeffsOut4Tangent; rw [dif_pos rfl]
    rw [hcoeffsOutY, one_mul]
    have hstep : ∑ col : Fin 6,
        coeffsOut4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 (otherMap4 col) *
        (let (_, bi, bj) := rrBasis7.getD (otherIdx7.getD col.val 0) (0, 0, 0)
         let (r0, r1) := reduceMonomialModU p u0 u1 v0 v1 bi bj
         if a.val = 0 then r0 else r1) =
        ∑ col : Fin 6,
        cramerSolution4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 col *
        (let (_, bi, bj) := rrBasis7.getD (otherIdx7.getD col.val 0) (0, 0, 0)
         let (r0, r1) := reduceMonomialModU p u0 u1 v0 v1 bi bj
         if a.val = 0 then r0 else r1) := by
      apply Finset.sum_congr rfl
      intro col _
      rw [coeffsOut4Tangent_otherMap p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 col]
    have horder : (∑ col : Fin 6,
          cramerSolution4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 col *
          (let (_, bi, bj) := rrBasis7.getD (otherIdx7.getD col.val 0) (0, 0, 0)
           let (r0, r1) := reduceMonomialModU p u0 u1 v0 v1 bi bj
           if a.val = 0 then r0 else r1))
        = ∑ col : Fin 6, A ⟨4 + a.val, haRow⟩ col *
            cramerSolution4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 col := by
      apply Finset.sum_congr rfl
      intro col _
      rw [mul_comm (cramerSolution4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1
        u0 u1 v0 v1 col), hApply col]
    rw [hstep, horder, hrow']
    exact neg_add_cancel _
  set Fsum : Fin 7 → F p := fun bidx =>
    coeffsOut4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 bidx *
      (let (_, bi, bj) := rrBasis7.getD bidx.val (0, 0, 0)
       let (r0, r1) := reduceMonomialModU p u0 u1 v0 v1 bi bj
       if a.val = 0 then r0 else r1) with hF_def
  have hFcol : ∀ col : Fin 6, Fsum (otherMap4 col) =
      coeffsOut4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 (otherMap4 col) *
      (let (_, bi, bj) := rrBasis7.getD (otherIdx7.getD col.val 0) (0, 0, 0)
       let (r0, r1) := reduceMonomialModU p u0 u1 v0 v1 bi bj
       if a.val = 0 then r0 else r1) := by
    intro col
    have hidx : (otherMap4 col).val = otherIdx7.getD col.val 0 := rfl
    simp only [hF_def, hidx]
  have hFy : Fsum (⟨yIdx7, yIdx7_lt_seven⟩ : Fin 7) =
      coeffsOut4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1
        ⟨yIdx7, yIdx7_lt_seven⟩ *
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
          (∑ col : Fin 6,
            coeffsOut4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1
              (otherMap4 col) *
            (let (_, bi, bj) := rrBasis7.getD (otherIdx7.getD col.val 0) (0, 0, 0)
             let (r0, r1) := reduceMonomialModU p u0 u1 v0 v1 bi bj
             if a.val = 0 then r0 else r1)) +
            coeffsOut4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1
              ⟨yIdx7, yIdx7_lt_seven⟩ *
              (let (_, bi_n, bj_n) := rrBasis7.getD yIdx7 (0, 1, 1)
               let (rn0, rn1) := reduceMonomialModU p u0 u1 v0 v1 bi_n bj_n
               if a.val = 0 then rn0 else rn1) := by
            rw [Finset.sum_congr rfl (fun col _ => hFcol col), hFy]
      _ = 0 := hmoved
  have hsum7' : ∑ bidx : Fin 7, Fsum bidx = 0 := hsum7 ▸ hmoved'
  rw [hF_def] at hsum7'
  exact hsum7'

end TangentRowIdentity4RowsTwoFour

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
theorem dvd_N_P1 (c0 c1 c2 c3 c4 : F p) (P1 P2 : F p × F p) (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
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
theorem dvd_N_P2 (c0 c1 c2 c3 c4 : F p) (P1 P2 : F p × F p) (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
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
def IsMumfordUa (c0 c1 c2 c3 c4 ua0 ua1 va0 va1 : F p) : Prop :=
  (X ^ 2 + C ua1 * X + C ua0) ∣
    ((C va1 * X + C va0) ^ 2 - curvePoly p c0 c1 c2 c3 c4)

/-- **The target Mumford hypothesis, K=4 instance** — mirrors
`IsMumfordTarget` exactly, over plain `F p` (no `K2` promotion needed). -/
def IsMumfordTarget4 (c0 c1 c2 c3 c4 u0 u1 v0 v1 : F p) : Prop :=
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
theorem dvd_N_ua (c0 c1 c2 c3 c4 : F p) (P1 P2 : F p × F p) (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
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
theorem dvd_N_u4 (c0 c1 c2 c3 c4 : F p) (P1 P2 : F p × F p) (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
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

/-! ## The two tangent-case divisibility facts — `hUa`/`hU` for
`Npoly4Tangent`, closing the gap flagged in the "Tangent-anchor quotient
assembly" section's docstring

Direct tangent-case port of `dvd_of_row_identity4`/`dvd_N_ua`/`dvd_N_u4`,
substituting `Epoly4Tangent`/`Ypoly4Tangent`/`coeffsOut4Tangent` for their
non-tangent counterparts and `rowTangent23_defining_eq_aux`/
`rowTangent45_defining_eq_aux` (above) for `row23_defining_eq_aux`/
`row45_defining_eq_aux`. Same `N = (E-Yv)(E+Yv) + (v²-f)Y²` identity
closes both, exactly as in the non-tangent case. -/

/-- **`dvd_of_row_identity4`, tangent case** — the K=4-tangent, plain-`F p`
bridge from the two mod-`(tu0,tu1,tv0,tv1)` row identities to
`(X²+tu1*X+tu0) ∣ (Epoly4Tangent + Ypoly4Tangent*(tv1*X+tv0))`. Identical
argument to `dvd_of_row_identity4`, substituting `coeffsOut4Tangent` for
`coeffsOut4` throughout (the argument never unfolds `Epoly4`/`Ypoly4`
beyond their `coeffsOut4`-indexed sum shape, and `Epoly4Tangent`/
`Ypoly4Tangent` share that exact shape with `coeffsOut4Tangent` in place
of `coeffsOut4`). -/
private theorem dvd_of_row_identity4Tangent (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (tu0 tu1 tv0 tv1 : F p)
    (hrow : ∀ a : Fin 2, (∑ bidx : Fin 7,
        let (_, bi, bj) := rrBasis7.getD bidx.val (0, 0, 0)
        coeffsOut4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 bidx *
          (let (r0, r1) := reduceMonomialModU p tu0 tu1 tv0 tv1 bi bj
           if a.val = 0 then r0 else r1)) = 0) :
    (X ^ 2 + C tu1 * X + C tu0) ∣
      (Epoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 +
        Ypoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 * (C tv1 * X + C tv0)) := by
  set U : Polynomial (F p) := X ^ 2 + C tu1 * X + C tu0 with hU_def
  have hUmonic : U.Monic := by rw [hU_def]; exact uPoly_monic p tu0 tu1
  rw [← Polynomial.modByMonic_eq_zero_iff_dvd hUmonic]
  set R : Polynomial (F p) :=
      Epoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 +
        Ypoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 * (C tv1 * X + C tv0)
      with hR_def
  have hRsum : R = ∑ bidx : Fin 7,
      let (_, bi, bj) := rrBasis7.getD bidx.val (0, 0, 0)
      if bj = 0 then
        C (coeffsOut4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 bidx) * X ^ bi
      else C (coeffsOut4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 bidx) * X ^ bi *
        (C tv1 * X + C tv0) := by
    rw [hR_def]
    unfold Epoly4Tangent Ypoly4Tangent
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
  have hRmod : R %ₘ U = ∑ bidx : Fin 7,
      (let (_, bi, bj) := rrBasis7.getD bidx.val (0, 0, 0)
       if bj = 0 then
         C (coeffsOut4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 bidx) * X ^ bi
       else
         C (coeffsOut4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 bidx) * X ^ bi *
           (C tv1 * X + C tv0)) %ₘ U := by
    rw [hRsum, ← Polynomial.modByMonicHom_apply,
      map_sum U.modByMonicHom
        (fun bidx : Fin 7 =>
          let (_, bi, bj) := rrBasis7.getD bidx.val (0, 0, 0)
          if bj = 0 then
            C (coeffsOut4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 bidx) * X ^ bi
          else
            C (coeffsOut4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 bidx) *
              X ^ bi * (C tv1 * X + C tv0))
        Finset.univ]
    simp only [Polynomial.modByMonicHom_apply]
  have hsmulC : ∀ (c : F p) (q : Polynomial (F p)), c • q = C c * q :=
    fun c _ => Polynomial.smul_eq_C_mul c
  have hmod_add : ∀ q r : Polynomial (F p), (q + r) %ₘ U = q %ₘ U + r %ₘ U := by
    intro q r
    rw [← Polynomial.modByMonicHom_apply, ← Polynomial.modByMonicHom_apply,
      ← Polynomial.modByMonicHom_apply, map_add]
  have hmod_Cmul : ∀ (c : F p) (q : Polynomial (F p)), (C c * q) %ₘ U = C c * (q %ₘ U) := by
    intro c q
    rw [← hsmulC, ← Polynomial.modByMonicHom_apply, ← Polynomial.modByMonicHom_apply, map_smul,
      hsmulC]
  have hterm : ∀ bidx : Fin 7,
      (let (_, bi, bj) := rrBasis7.getD bidx.val (0, 0, 0)
       if bj = 0 then
         C (coeffsOut4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 bidx) * X ^ bi
       else
         C (coeffsOut4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 bidx) * X ^ bi *
            (C tv1 * X + C tv0)) %ₘ U =
       let (_, bi, bj) := rrBasis7.getD bidx.val (0, 0, 0)
       let (r0, r1) := reduceMonomialModU p tu0 tu1 tv0 tv1 bi bj
       C (coeffsOut4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 bidx) *
         (C r0 + C r1 * X) := by
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
    generalize hc_def' : coeffsOut4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1
      u0 u1 v0 v1 bidx = c
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
      coeffsOut4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 bidx *
        (let (r0, _) := reduceMonomialModU p tu0 tu1 tv0 tv1 bi bj; r0)) = 0 := hrow0
  have hrow1' : (∑ bidx : Fin 7,
      let (_, bi, bj) := rrBasis7.getD bidx.val (0, 0, 0)
      coeffsOut4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 bidx *
        (let (_, r1) := reduceMonomialModU p tu0 tu1 tv0 tv1 bi bj; r1)) = 0 := hrow1
  have hRmodsum : R %ₘ U = ∑ bidx : Fin 7,
      let (_, bi, bj) := rrBasis7.getD bidx.val (0, 0, 0)
      let (r0, r1) := reduceMonomialModU p tu0 tu1 tv0 tv1 bi bj
      C (coeffsOut4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 bidx) *
        (C r0 + C r1 * X) := by
    rw [hRmod]; exact Finset.sum_congr rfl (fun bidx _ => hterm bidx)
  rw [hRmodsum]
  have hsplit : (∑ bidx : Fin 7,
      let (_, bi, bj) := rrBasis7.getD bidx.val (0, 0, 0)
      let (r0, r1) := reduceMonomialModU p tu0 tu1 tv0 tv1 bi bj
      C (coeffsOut4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 bidx) *
        (C r0 + C r1 * X)) =
      (∑ bidx : Fin 7,
          let (_, bi, bj) := rrBasis7.getD bidx.val (0, 0, 0)
          C (coeffsOut4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 bidx *
            (let (r0, _) := reduceMonomialModU p tu0 tu1 tv0 tv1 bi bj; r0))) +
      (∑ bidx : Fin 7,
          let (_, bi, bj) := rrBasis7.getD bidx.val (0, 0, 0)
          C (coeffsOut4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 bidx *
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

/-- **`(X²+ua1*X+ua0) ∣ Npoly4Tangent`** — the tangent-case analogue of
`dvd_N_ua`, closing one of the two hypotheses
`curBeforeMonic4Tangent_dvd_Npoly4Tangent`/`uRS4Tangent_dvd_Npoly4Tangent`
previously took as raw assumptions. Same `N = (E-Yv)(E+Yv) + (v²-f)Y²`
combining identity as `dvd_N_ua`. -/
theorem dvd_N_uaTangent (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (hA : MatrixNondegenerate4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hMumfordUa : IsMumfordUa p c0 c1 c2 c3 c4 ua0 ua1 va0 va1) :
    (X ^ 2 + C ua1 * X + C ua0) ∣
      Npoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 := by
  have huY : (X ^ 2 + C ua1 * X + C ua0) ∣
      (Epoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 +
        Ypoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 *
          (C va1 * X + C va0)) :=
    dvd_of_row_identity4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1
      ua0 ua1 va0 va1
      (fun a => rowTangent23_defining_eq_aux p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1
        hA a)
  have hVF : (X ^ 2 + C ua1 * X + C ua0) ∣
      ((C va1 * X + C va0) ^ 2 - curvePoly p c0 c1 c2 c3 c4) := hMumfordUa
  set E := Epoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1
  set Y := Ypoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1
  set V : Polynomial (F p) := C va1 * X + C va0
  set f := curvePoly p c0 c1 c2 c3 c4
  have h1 : (X ^ 2 + C ua1 * X + C ua0) ∣ (E - Y * V) * (E + Y * V) :=
    dvd_mul_of_dvd_right huY (E - Y * V)
  have h2 : (X ^ 2 + C ua1 * X + C ua0) ∣ (V ^ 2 - f) * Y ^ 2 := dvd_mul_of_dvd_left hVF (Y ^ 2)
  have hadd : (X ^ 2 + C ua1 * X + C ua0) ∣
      (E - Y * V) * (E + Y * V) + (V ^ 2 - f) * Y ^ 2 := dvd_add h1 h2
  have hNeq : Npoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 =
      (E - Y * V) * (E + Y * V) + (V ^ 2 - f) * Y ^ 2 := by
    unfold Npoly4Tangent; ring
  rw [hNeq]; exact hadd

/-- **`(X²+u1*X+u0) ∣ Npoly4Tangent`** — the tangent-case analogue of
`dvd_N_u4`, closing the other of the two hypotheses
`curBeforeMonic4Tangent_dvd_Npoly4Tangent`/`uRS4Tangent_dvd_Npoly4Tangent`
previously took as raw assumptions. -/
theorem dvd_N_u4Tangent (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (hA : MatrixNondegenerate4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hMumfordTarget : IsMumfordTarget4 p c0 c1 c2 c3 c4 u0 u1 v0 v1) :
    (X ^ 2 + C u1 * X + C u0) ∣
      Npoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 := by
  have huY : (X ^ 2 + C u1 * X + C u0) ∣
      (Epoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 +
        Ypoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 * (C v1 * X + C v0)) :=
    dvd_of_row_identity4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1
      u0 u1 v0 v1
      (fun a => rowTangent45_defining_eq_aux p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1
        hA a)
  have hVF : (X ^ 2 + C u1 * X + C u0) ∣
      ((C v1 * X + C v0) ^ 2 - curvePoly p c0 c1 c2 c3 c4) := hMumfordTarget
  set E := Epoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1
  set Y := Ypoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1
  set V : Polynomial (F p) := C v1 * X + C v0
  set f := curvePoly p c0 c1 c2 c3 c4
  have h1 : (X ^ 2 + C u1 * X + C u0) ∣ (E - Y * V) * (E + Y * V) :=
    dvd_mul_of_dvd_right huY (E - Y * V)
  have h2 : (X ^ 2 + C u1 * X + C u0) ∣ (V ^ 2 - f) * Y ^ 2 := dvd_mul_of_dvd_left hVF (Y ^ 2)
  have hadd : (X ^ 2 + C u1 * X + C u0) ∣
      (E - Y * V) * (E + Y * V) + (V ^ 2 - f) * Y ^ 2 := dvd_add h1 h2
  have hNeq : Npoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 =
      (E - Y * V) * (E + Y * V) + (V ^ 2 - f) * Y ^ 2 := by
    unfold Npoly4Tangent; ring
  rw [hNeq]; exact hadd

/-! ## The Mumford identity, K=4 instance — `v_RS4² ≡ f (mod u_RS4)`

Direct port of `DataDerivationMumford.lean`'s `vRS_sq_eq_f_mod_uRS` chain.
The four `sq_mod_eq_of_dvd_step*` lemmas and `sq_mod_eq_of_dvd` itself are
completely generic in the ring (`{R : Type*} [CommRing R]`) — they mention
no `K2`/tower content at all, so they port to `Polynomial (F p)` with zero
changes, not a rescaling. Only the wrapper (`vRS_sq_eq_f_mod_uRS` itself,
here `vRS4_sq_eq_f_mod_uRS4`) is K=4-specific, substituting `uRS4`/`vRS4`/
`Epoly4`/`Ypoly4`/`curvePoly`/`Npoly4` for their K=2/tower counterparts
(`curvePoly` plays `fAtX`'s role directly here, exactly as this file's
module docstring already notes — no `algebraMap`/tower promotion needed
since everything already lives in plain `F p`).

**Update (this pass): CLOSED for this file, still open upstream in K=2.**
`DataDerivationSolve.lean`'s K=2 `vRS_sq_eq_f_mod_uRS` still takes `hNu` as
a raw hypothesis — that upstream gap is UNCHANGED, not touched this pass.
But for THIS file, `uRS4_dvd_Npoly4` (below, combining `dvd_N_P1`/
`dvd_N_P2`/`dvd_N_ua`/`dvd_N_u4` via six explicit pairwise-coprimality
hypotheses) now exists and is `sorry`-free, and `vRS4_sq_eq_f_mod_uRS4`
below has been updated to DERIVE `hNu` from it (taking
`uRS4_dvd_Npoly4`'s own hypothesis bundle instead of a bare `hNu`) rather
than assume it separately — `hInv` alone remains a genuine raw hypothesis,
which is correct (it is not implied by the four-factor combining). Porting
this same fix back to `DataDerivationSolve.lean`'s K=2
`vRS_sq_eq_f_mod_uRS` is a natural, symmetric follow-up (the K=2 file has
the identical `dvd_N_anchor1`/`dvd_N_anchor2`/`dvd_N_u` three-factor
version of the same combining lemma available, just never wired in) but
was NOT done this pass — flagged here so it isn't lost, not silently
assumed. -/

section GenericRemainderLemma4
-- Same isolation rationale as `DataDerivationMumford.lean`'s own
-- `GenericRemainderLemma` section: kept free of this file's `p`/`c0..v1`
-- `variable`s so elaboration doesn't carry a large local context through
-- statements that don't mention any of it.

set_option maxHeartbeats 4000000 in
/-- Step 1: `U ∣ (Y*G)^2 - 1` from `U ∣ Y*G - 1`. Ring-generic, identical
to `DataDerivationMumford.lean`'s `sq_mod_eq_of_dvd_step1`. -/
theorem sq_mod_eq_of_dvd_step1_4
    {R : Type*} [CommRing R] {U Y G : Polynomial R}
    (hInv : U ∣ Y * G - 1) :
    U ∣ (Y * G) ^ 2 - 1 := by
  have hsq1 : (Y * G) ^ 2 - 1 = (Y * G - 1) * (Y * G + 1) := by ring
  rw [hsq1]
  exact dvd_mul_of_dvd_left hInv (Y * G + 1)

set_option maxHeartbeats 4000000 in
/-- Step 2: `U ∣ (E*G)^2 - f`. Ring-generic, identical to
`sq_mod_eq_of_dvd_step2`. -/
theorem sq_mod_eq_of_dvd_step2_4
    {R : Type*} [CommRing R] {U E Y G f : Polynomial R}
    (hN : U ∣ E ^ 2 - f * Y ^ 2)
    (hInvSq : U ∣ (Y * G) ^ 2 - 1) :
    U ∣ (E * G) ^ 2 - f := by
  have hNscaled : U ∣ (E ^ 2 - f * Y ^ 2) * G ^ 2 :=
    dvd_mul_of_dvd_left hN (G ^ 2)
  have hInvscaled : U ∣ f * ((Y * G) ^ 2 - 1) :=
    dvd_mul_of_dvd_right hInvSq f
  have hid1 :
      (E ^ 2 - f * Y ^ 2) * G ^ 2 + f * ((Y * G) ^ 2 - 1) = (E * G) ^ 2 - f := by
    ring
  rw [← hid1]
  exact dvd_add hNscaled hInvscaled

set_option maxHeartbeats 4000000 in
/-- Step 3: `U ∣ (X %ₘ U) - X`. Ring-generic, identical to
`sq_mod_eq_of_dvd_step3`. -/
theorem sq_mod_eq_of_dvd_step3_4
    {R : Type*} [CommRing R] (U X : Polynomial R) :
    U ∣ (X %ₘ U) - X :=
  Polynomial.dvd_modByMonic_sub X U

set_option maxHeartbeats 4000000 in
/-- Step 4: `U ∣ (X %ₘ U)^2 - X^2`. Ring-generic, identical to
`sq_mod_eq_of_dvd_step4`. -/
theorem sq_mod_eq_of_dvd_step4_4
    {R : Type*} [CommRing R] {U : Polynomial R} (X : Polynomial R)
    (hrem : U ∣ (X %ₘ U) - X) :
    U ∣ (X %ₘ U) ^ 2 - X ^ 2 := by
  have hsq2 : (X %ₘ U) ^ 2 - X ^ 2 = ((X %ₘ U) + X) * ((X %ₘ U) - X) := by ring
  rw [hsq2]
  exact dvd_mul_of_dvd_right hrem ((X %ₘ U) + X)

set_option maxHeartbeats 4000000 in
/-- Assembled generic remainder lemma, identical to
`DataDerivationMumford.lean`'s `sq_mod_eq_of_dvd`. -/
theorem sq_mod_eq_of_dvd_4
    {R : Type*} [CommRing R]
    {U E Y G f : Polynomial R}
    (hU : U.Monic)
    (hN : U ∣ E ^ 2 - f * Y ^ 2)
    (hInv : U ∣ Y * G - 1) :
    ((-E * G) %ₘ U) ^ 2 %ₘ U = f %ₘ U := by
  have hInvSq := sq_mod_eq_of_dvd_step1_4 hInv
  have hEGf := sq_mod_eq_of_dvd_step2_4 hN hInvSq
  have hrem := sq_mod_eq_of_dvd_step3_4 U (-E * G)
  have hvrem := sq_mod_eq_of_dvd_step4_4 (-E * G) hrem
  have hnegsq : (-E * G) ^ 2 = (E * G) ^ 2 := by ring
  rw [hnegsq] at hvrem
  have hid2 :
      ((-E * G) %ₘ U) ^ 2 - (E * G) ^ 2 + ((E * G) ^ 2 - f) =
        ((-E * G) %ₘ U) ^ 2 - f := by
    ring
  have hvf : U ∣ ((-E * G) %ₘ U) ^ 2 - f := by
    rw [← hid2]; exact dvd_add hvrem hEGf
  exact Polynomial.modByMonic_eq_of_dvd_sub hU hvf

end GenericRemainderLemma4

section FourFactorCombining4
-- Own section, above `MumfordIdentity4`'s `variable`s, same isolation
-- rationale as `GenericRemainderLemma4` — this lemma mentions no
-- `p`/`c0..v1` at all, only four abstract monic polynomials over a
-- generic `R`, so it should not carry a large ambient local context.

/-- **Combine four individually-known divisibility facts into one, given
pairwise coprimality.** Ring-generic (no `F p`/`Npoly4`-specific content) —
built from `IsCoprime.mul_left` (coprimality of a product) and
`IsCoprime.mul_dvd` (coprime factors' product divides a common multiple),
per the ChatGPT consultation's confirmed-against-Mathlib architecture
(`chatgpt_prompt_uRS4_dvd_Npoly4.md`). Six pairwise-coprimality hypotheses
for four factors (`C(4,2) = 6`), matching that consultation's own
`FourPairwiseCoprime`-style interface — deliberately explicit hypotheses,
not derived from root/eval conditions here (that derivation, for the
linear-vs-quadratic and quadratic-vs-quadratic cases, is real further work
not attempted in this pass; see the module docstring). -/
theorem prod_dvd_of_pairwise_coprime_four
    {R : Type*} [CommRing R] {q1 q2 q3 q4 N : R}
    (h12 : IsCoprime q1 q2) (h13 : IsCoprime q1 q3) (h14 : IsCoprime q1 q4)
    (h23 : IsCoprime q2 q3) (h24 : IsCoprime q2 q4) (h34 : IsCoprime q3 q4)
    (hd1 : q1 ∣ N) (hd2 : q2 ∣ N) (hd3 : q3 ∣ N) (hd4 : q4 ∣ N) :
    q1 * q2 * q3 * q4 ∣ N := by
  have h12_3 : IsCoprime (q1 * q2) q3 := IsCoprime.mul_left h13 h23
  have h12_4 : IsCoprime (q1 * q2) q4 := IsCoprime.mul_left h14 h24
  have h12_34 : IsCoprime (q1 * q2) (q3 * q4) := IsCoprime.mul_right h12_3 h12_4
  have hd12 : q1 * q2 ∣ N := IsCoprime.mul_dvd h12 hd1 hd2
  have hd34 : q3 * q4 ∣ N := IsCoprime.mul_dvd h34 hd3 hd4
  have hd1234 : (q1 * q2) * (q3 * q4) ∣ N := IsCoprime.mul_dvd h12_34 hd12 hd34
  have heq : (q1 * q2) * (q3 * q4) = q1 * q2 * q3 * q4 := by ring
  rwa [heq] at hd1234

/-- **Successive `/ₘ` by a monic divisor, given the product already
divides.** If `q.Monic` and `q ∣ N`, then `N /ₘ q` satisfies
`q' * (N /ₘ q) = k` whenever `N = q * q' * k`-shaped — concretely, this
peels ONE monic factor off a product-divisibility fact, reducing the
`k1*k2*k3*k4`-factor combining problem to induction on that peeling.
Built from `Polynomial.modByMonic_eq_zero_iff_dvd` (divisibility ↔ exact
remainder) and `Polynomial.mul_divByMonic_cancel_left` (`q * p /ₘ q = p`
for monic `q`), both confirmed against current Mathlib. -/
theorem divByMonic_eq_of_dvd_mul {R : Type*} [CommRing R]
    {q k N : Polynomial R} (hq : q.Monic) (hN : N = q * k) :
    N /ₘ q = k := by
  rw [hN]
  exact Polynomial.mul_divByMonic_cancel_left k hq

end FourFactorCombining4

/-! ## `uRS4 ∣ Npoly4`, K=4 instance — closing the combining gap

Instantiates `prod_dvd_of_pairwise_coprime_four`/`divByMonic_eq_of_dvd_mul`
against `Npoly4`'s four known factors (`dvd_N_P1`/`dvd_N_P2`/`dvd_N_ua`/
`dvd_N_u4`) and `curBeforeMonic4`'s own four-step `/ₘ` chain. The six
pairwise-coprimality hypotheses are the genericity conditions this file's
module docstring and `ROADMAP-alpha-locus.md`'s Task (B) both flag as the
open "`Bad`" exceptional-locus question — supplied here as explicit
hypotheses (matching this file's convention throughout), not derived. -/

section CombineDvd4

variable (c0 c1 c2 c3 c4 : F p) (P1 P2 : F p × F p) (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)

/-- **`uRS4 ∣ Npoly4`**, given: (a) `curBeforeMonic4 ≠ 0` (needed so `uRS4`'s
leading-coefficient rescaling is a genuine unit, matching `uRS4_monic`'s own
hypothesis), (b) the four individual-factor divisibility facts (via
`MatrixNondegenerate4`/curve-membership/Mumford hypotheses, exactly as
`dvd_N_P1`/`dvd_N_P2`/`dvd_N_ua`/`dvd_N_u4` already require), and (c) six
pairwise-coprimality facts pinning down the genericity locus. This is
exactly `vRS4_sq_eq_f_mod_uRS4`'s `hNu` hypothesis, now proved rather than
assumed (given the coprimality inputs). -/
theorem uRS4_dvd_Npoly4
    (hne : curBeforeMonic4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hA : MatrixNondegenerate4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hP1_curve : P1.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P1.1)
    (hP2_curve : P2.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P2.1)
    (hMumfordUa : IsMumfordUa p c0 c1 c2 c3 c4 ua0 ua1 va0 va1)
    (hMumfordTarget : IsMumfordTarget4 p c0 c1 c2 c3 c4 u0 u1 v0 v1)
    (h12 : IsCoprime (X - C P1.1 : Polynomial (F p)) (X - C P2.1))
    (h13 : IsCoprime (X - C P1.1 : Polynomial (F p))
      (X ^ 2 + C ua1 * X + C ua0))
    (h14 : IsCoprime (X - C P1.1 : Polynomial (F p))
      (X ^ 2 + C u1 * X + C u0))
    (h23 : IsCoprime (X - C P2.1 : Polynomial (F p))
      (X ^ 2 + C ua1 * X + C ua0))
    (h24 : IsCoprime (X - C P2.1 : Polynomial (F p))
      (X ^ 2 + C u1 * X + C u0))
    (h34 : IsCoprime (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
      (X ^ 2 + C u1 * X + C u0)) :
    uRS4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 := by
  have hd1 := dvd_N_P1 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hA hP1_curve
  have hd2 := dvd_N_P2 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hA hP2_curve
  have hd3 := dvd_N_ua p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hA hMumfordUa
  have hd4 := dvd_N_u4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hA hMumfordTarget
  have hprod :
      (X - C P1.1) * (X - C P2.1) * (X ^ 2 + C ua1 * X + C ua0) *
          (X ^ 2 + C u1 * X + C u0) ∣
        Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 :=
    prod_dvd_of_pairwise_coprime_four h12 h13 h14 h23 h24 h34 hd1 hd2 hd3 hd4
  obtain ⟨k, hk⟩ := hprod
  have hm1 : (X - C P1.1 : Polynomial (F p)).Monic := Polynomial.monic_X_sub_C _
  have hm2 : (X - C P2.1 : Polynomial (F p)).Monic := Polynomial.monic_X_sub_C _
  have hm3 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).Monic := by monicity!
  have hm4 : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).Monic := by monicity!
  -- Peel the four factors off `Npoly4` one `/ₘ` at a time, matching
  -- `curBeforeMonic4`'s own left-to-right order exactly.
  have hstep0 :
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 =
        (X - C P1.1) *
          ((X - C P2.1) * (X ^ 2 + C ua1 * X + C ua0) *
            (X ^ 2 + C u1 * X + C u0) * k) := by
    rw [hk]; ring
  have hstep1 :
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 /ₘ (X - C P1.1) =
        (X - C P2.1) * (X ^ 2 + C ua1 * X + C ua0) * (X ^ 2 + C u1 * X + C u0) * k :=
    divByMonic_eq_of_dvd_mul hm1 hstep0
  have hstep1' :
      (X - C P2.1) * (X ^ 2 + C ua1 * X + C ua0) * (X ^ 2 + C u1 * X + C u0) * k =
        (X - C P2.1) *
          ((X ^ 2 + C ua1 * X + C ua0) * (X ^ 2 + C u1 * X + C u0) * k) := by ring
  have hstep2 :
      (Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 /ₘ (X - C P1.1)) /ₘ
          (X - C P2.1) =
        (X ^ 2 + C ua1 * X + C ua0) * (X ^ 2 + C u1 * X + C u0) * k :=
    divByMonic_eq_of_dvd_mul hm2 (hstep1.trans hstep1')
  have hstep2' :
      (X ^ 2 + C ua1 * X + C ua0) * (X ^ 2 + C u1 * X + C u0) * k =
        (X ^ 2 + C ua1 * X + C ua0) * ((X ^ 2 + C u1 * X + C u0) * k) := by ring
  have hstep3 :
      ((Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 /ₘ (X - C P1.1)) /ₘ
          (X - C P2.1)) /ₘ (X ^ 2 + C ua1 * X + C ua0) =
        (X ^ 2 + C u1 * X + C u0) * k :=
    divByMonic_eq_of_dvd_mul hm3 (hstep2.trans hstep2')
  have hstep4 :
      curBeforeMonic4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 = k := by
    unfold curBeforeMonic4
    rw [hstep3]
    exact divByMonic_eq_of_dvd_mul hm4 rfl
  -- `uRS4` is `curBeforeMonic4` scaled by a unit (its leading coefficient's
  -- inverse), so `curBeforeMonic4 ∣ Npoly4` gives `uRS4 ∣ Npoly4` directly:
  -- `curBeforeMonic4 = k` and `k ∣ Npoly4` (from `hk`, reading the divisor
  -- side), and `uRS4` is an associate of `curBeforeMonic4`.
  have hcurdvd :
      curBeforeMonic4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ∣
        Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 := by
    rw [hstep4, hk]
    exact ⟨(X - C P1.1) * (X - C P2.1) * (X ^ 2 + C ua1 * X + C ua0) *
      (X ^ 2 + C u1 * X + C u0), by ring⟩
  -- `uRS4 = C leadingCoeff⁻¹ * curBeforeMonic4`; this scaling is a genuine
  -- unit-rescaling (hence divisibility-preserving both ways) only when
  -- `curBeforeMonic4 ≠ 0` — `hne` is exactly this file's own hypothesis
  -- (matching `uRS4_monic`'s convention), needed for this step even though
  -- the earlier `hcurdvd` derivation didn't need it.
  unfold uRS4
  obtain ⟨m, hm⟩ := hcurdvd
  have hlc : (curBeforeMonic4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff
      ≠ 0 := (not_congr Polynomial.leadingCoeff_eq_zero).mpr hne
  refine ⟨C (curBeforeMonic4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff
    * m, ?_⟩
  rw [hm]
  have : (C (curBeforeMonic4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff⁻¹ *
      curBeforeMonic4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) *
      (C (curBeforeMonic4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff * m) =
      C ((curBeforeMonic4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff⁻¹ *
        (curBeforeMonic4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff) *
      (curBeforeMonic4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 * m) := by
    simp only [map_mul]; ring
  rw [this, inv_mul_cancel₀ hlc, map_one, one_mul]

end CombineDvd4

/-! ## Tangent-anchor quotient assembly

The tangent case replaces the two linear anchor factors by the single
squared factor `(X - C px)^2`.  The theorem `dvd_N_P1P2_tangent` supplies
that squared-factor divisibility.  The following lemmas extend the existing
`/ₘ` quotient bookkeeping through that repeated factor, so the tangent case
has the same quotient/normalization layer as the ordinary four-factor case.
Coprimality remains explicit: establishing the exceptional-locus hypotheses
is separate from this polynomial bookkeeping. -/

section TangentCombine4

variable (c0 c1 c2 c3 c4 : F p) (px py : F p)

/-- Tangent-case quotient after removing the squared literal-point factor and
`u_a`. -/
noncomputable def curBeforeMonic4Tangent
    (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p) : Polynomial (F p) :=
  ((Npoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 /ₘ
      (X - C px) ^ 2) /ₘ
    (X ^ 2 + C ua1 * X + C ua0))

/-- The squared tangent-anchor factor is monic. -/
theorem tangentAnchorPoly4_monic :
    ((X - C px : Polynomial (F p)) ^ 2).Monic := by
  exact (Polynomial.monic_X_sub_C px).pow 2

/-- Three pairwise-coprime divisors combine into their product. -/
theorem prod_dvd_of_pairwise_coprime_three
    {R : Type*} [CommRing R] {q1 q2 q3 N : R}
    (h12 : IsCoprime q1 q2) (h13 : IsCoprime q1 q3)
    (h23 : IsCoprime q2 q3)
    (hd1 : q1 ∣ N) (hd2 : q2 ∣ N) (hd3 : q3 ∣ N) :
    q1 * q2 * q3 ∣ N := by
  have h12_3 : IsCoprime (q1 * q2) q3 := IsCoprime.mul_left h13 h23
  have hd12 : q1 * q2 ∣ N := IsCoprime.mul_dvd h12 hd1 hd2
  have hprod : (q1 * q2) * q3 ∣ N := IsCoprime.mul_dvd h12_3 hd12 hd3
  have heq : (q1 * q2) * q3 = q1 * q2 * q3 := by ring
  rwa [heq] at hprod

/-- The tangent quotient divides `N` once the squared tangent factor, `u_a`,
and the target all divide `N` pairwise-coprimely. -/
theorem curBeforeMonic4Tangent_dvd_Npoly4Tangent
    (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (hTan : ((X - C px : Polynomial (F p)) ^ 2) ∣
      Npoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hUa : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ∣
      Npoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hU : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)) ∣
      Npoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hTUa : IsCoprime ((X - C px : Polynomial (F p)) ^ 2)
      (X ^ 2 + C ua1 * X + C ua0))
    (hTU : IsCoprime ((X - C px : Polynomial (F p)) ^ 2)
      (X ^ 2 + C u1 * X + C u0))
    (hUaU : IsCoprime (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
      (X ^ 2 + C u1 * X + C u0)) :
    curBeforeMonic4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 ∣
      Npoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 := by
  have hprod :
      ((X - C px : Polynomial (F p)) ^ 2) *
          (X ^ 2 + C ua1 * X + C ua0) *
          (X ^ 2 + C u1 * X + C u0) ∣
        Npoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 :=
    prod_dvd_of_pairwise_coprime_three hTUa hTU hUaU hTan hUa hU
  obtain ⟨k, hk⟩ := hprod
  have htMonic : ((X - C px : Polynomial (F p)) ^ 2).Monic :=
    tangentAnchorPoly4_monic p px
  have huaMonic : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).Monic := by
    monicity!
  have hstep0 :
      Npoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 =
        (X - C px) ^ 2 *
          ((X ^ 2 + C ua1 * X + C ua0) *
            ((X ^ 2 + C u1 * X + C u0) * k)) := by
    rw [hk]
    ring
  have hstep1 :
      Npoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 /ₘ
          (X - C px) ^ 2 =
        (X ^ 2 + C ua1 * X + C ua0) *
          ((X ^ 2 + C u1 * X + C u0) * k) :=
    divByMonic_eq_of_dvd_mul htMonic hstep0
  have hstep2 :
      (Npoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 /ₘ
          (X - C px) ^ 2) /ₘ
          (X ^ 2 + C ua1 * X + C ua0) =
        (X ^ 2 + C u1 * X + C u0) * k :=
    divByMonic_eq_of_dvd_mul huaMonic hstep1
  unfold curBeforeMonic4Tangent
  rw [hstep2]
  exact ⟨(X - C px) ^ 2 * (X ^ 2 + C ua1 * X + C ua0), by
    rw [hk]
    ring⟩

/-- Monic normalization of the tangent quotient. -/
noncomputable def uRS4Tangent
    (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p) : Polynomial (F p) :=
  C (curBeforeMonic4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff⁻¹ *
    curBeforeMonic4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1

theorem uRS4Tangent_monic
    (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (hcur : curBeforeMonic4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0) :
    (uRS4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1).Monic := by
  simp only [uRS4Tangent]
  set q := curBeforeMonic4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 with hq
  have hlc : q.leadingCoeff ≠ 0 :=
    (not_congr Polynomial.leadingCoeff_eq_zero).mpr hcur
  have hau : q.leadingCoeff * q.leadingCoeff⁻¹ = 1 := mul_inv_cancel₀ hlc
  have hdeg : (C q.leadingCoeff⁻¹ * q).natDegree = q.natDegree :=
    Polynomial.natDegree_C_mul_eq_of_mul_eq_one hau
  rw [Polynomial.Monic.def]
  change (C q.leadingCoeff⁻¹ * q).coeff (C q.leadingCoeff⁻¹ * q).natDegree = 1
  rw [hdeg, Polynomial.coeff_C_mul]
  exact inv_mul_cancel₀ hlc

/-- The normalized tangent quotient divides the tangent numerator. -/
theorem uRS4Tangent_dvd_Npoly4Tangent
    (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (hcur : curBeforeMonic4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hTan : ((X - C px : Polynomial (F p)) ^ 2) ∣
      Npoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hUa : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ∣
      Npoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hU : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)) ∣
      Npoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hTUa : IsCoprime ((X - C px : Polynomial (F p)) ^ 2)
      (X ^ 2 + C ua1 * X + C ua0))
    (hTU : IsCoprime ((X - C px : Polynomial (F p)) ^ 2)
      (X ^ 2 + C u1 * X + C u0))
    (hUaU : IsCoprime (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
      (X ^ 2 + C u1 * X + C u0)) :
    uRS4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 ∣
      Npoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 := by
  have hq := curBeforeMonic4Tangent_dvd_Npoly4Tangent p c0 c1 c2 c3 c4 px py
    ua0 ua1 va0 va1 u0 u1 v0 v1 hTan hUa hU hTUa hTU hUaU
  unfold uRS4Tangent
  obtain ⟨m, hm⟩ := hq
  have hlc : (curBeforeMonic4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff ≠ 0 :=
    (not_congr Polynomial.leadingCoeff_eq_zero).mpr hcur
  refine ⟨C (curBeforeMonic4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff * m, ?_⟩
  rw [hm]
  have hscale :
      (C (curBeforeMonic4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff⁻¹ *
        curBeforeMonic4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1) *
      (C (curBeforeMonic4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff * m) =
      C ((curBeforeMonic4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff⁻¹ *
        (curBeforeMonic4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff) *
      (curBeforeMonic4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 * m) := by
    simp only [map_mul]
    ring
  rw [hscale, inv_mul_cancel₀ hlc, map_one, one_mul]

/-- **`uRS4Tangent ∣ Npoly4Tangent`, fully derived** — the tangent-case
counterpart of `uRS4_dvd_Npoly4`: takes the same underlying
`MatrixNondegenerate4Tangent`/curve/Mumford/genericity data
`dvd_N_P1P2_tangent`/`dvd_N_uaTangent`/`dvd_N_u4Tangent` need, and derives
`hTan`/`hUa`/`hU` internally (via those three theorems) rather than
assuming them the way `uRS4Tangent_dvd_Npoly4Tangent` above does. This is
`ROADMAP-alpha-locus.md`'s tangent-case combining gap, closed: the
tangent-anchor squared factor no longer has to be assumed to divide
`Npoly4Tangent`, it is proved from the row-identity/curve/branch-derivative
facts exactly as the two ordinary literal-point factors already are in
`uRS4_dvd_Npoly4`. The three pairwise-coprimality hypotheses
(`hTUa`/`hTU`/`hUaU`) remain the genuine open genericity ("`Bad`"
exceptional-locus) content — same status as `uRS4_dvd_Npoly4`'s six
`h12`–`h34` hypotheses, not derived here or anywhere else in this file. -/
theorem uRS4Tangent_dvd_Npoly4Tangent_full
    (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (hcur : curBeforeMonic4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hA : MatrixNondegenerate4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hpy : py ≠ 0) (hp2 : (2 : F p) ≠ 0)
    (hP_curve : py ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval px)
    (hNe : Npoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hMumfordUa : IsMumfordUa p c0 c1 c2 c3 c4 ua0 ua1 va0 va1)
    (hMumfordTarget : IsMumfordTarget4 p c0 c1 c2 c3 c4 u0 u1 v0 v1)
    (hTUa : IsCoprime ((X - C px : Polynomial (F p)) ^ 2)
      (X ^ 2 + C ua1 * X + C ua0))
    (hTU : IsCoprime ((X - C px : Polynomial (F p)) ^ 2)
      (X ^ 2 + C u1 * X + C u0))
    (hUaU : IsCoprime (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
      (X ^ 2 + C u1 * X + C u0)) :
    uRS4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 ∣
      Npoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 := by
  have hTan := dvd_N_P1P2_tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1
    hA hpy hp2 hP_curve hNe
  have hUa := dvd_N_uaTangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1
    hA hMumfordUa
  have hU := dvd_N_u4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1
    hA hMumfordTarget
  exact uRS4Tangent_dvd_Npoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1
    hcur hTan hUa hU hTUa hTU hUaU

/-- Tangent analogue of `vRS4`: the normalized `-E * Y⁻¹ (mod uRS)` remainder. -/
noncomputable def vRS4Tangent
    (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (_hgcd : IsCoprime
      (Ypoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1)
      (uRS4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1)) :
    Polynomial (F p) :=
  (-(Epoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1) *
      EuclideanDomain.gcdA
        (Ypoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1)
        (uRS4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1)) %ₘ
    uRS4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1

/-- Tangent Mumford congruence, conditional on the same Bezout inverse witness
used by the ordinary K=4 construction. -/
theorem vRS4Tangent_sq_eq_f_mod_uRS4Tangent
    (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (hcur : curBeforeMonic4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hgcd : IsCoprime
      (Ypoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1)
      (uRS4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1))
    (hNu :
      uRS4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 ∣
        Npoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hInv :
      uRS4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 ∣
        Ypoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 *
            EuclideanDomain.gcdA
              (Ypoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1)
              (uRS4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1) - 1) :
    (vRS4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 hgcd) ^ 2 %ₘ
        uRS4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 =
      (curvePoly p c0 c1 c2 c3 c4) %ₘ
        uRS4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 := by
  have hU : (uRS4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1).Monic :=
    uRS4Tangent_monic p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 hcur
  have hmod := sq_mod_eq_of_dvd_4 hU hNu hInv
  simpa only [vRS4Tangent] using hmod

/-- **`vRS4Tangent_sq_eq_f_mod_uRS4Tangent`, fully derived** — the tangent
counterpart of `vRS4_sq_eq_f_mod_uRS4`'s "`hNu` no longer a hypothesis"
fix, using `uRS4Tangent_dvd_Npoly4Tangent_full` in place of
`uRS4_dvd_Npoly4` to derive `hNu` from the same underlying
`MatrixNondegenerate4Tangent`/curve/Mumford/genericity data rather than
assuming it. Closes the tangent-case combining gap end to end: this
theorem's only remaining non-`Ypoly4Tangent`-coprimality hypotheses are
`hTUa`/`hTU`/`hUaU` (the tangent genericity/`Bad`-locus data, still
assumed, same status as `uRS4_dvd_Npoly4`'s `h12`–`h34`) and `hInv` (the
Bézout-witness fact, genuinely separate content, same as the non-tangent
case). -/
theorem vRS4Tangent_sq_eq_f_mod_uRS4Tangent_full
    (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (hcur : curBeforeMonic4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hA : MatrixNondegenerate4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hpy : py ≠ 0) (hp2 : (2 : F p) ≠ 0)
    (hP_curve : py ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval px)
    (hNe : Npoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hMumfordUa : IsMumfordUa p c0 c1 c2 c3 c4 ua0 ua1 va0 va1)
    (hMumfordTarget : IsMumfordTarget4 p c0 c1 c2 c3 c4 u0 u1 v0 v1)
    (hTUa : IsCoprime ((X - C px : Polynomial (F p)) ^ 2)
      (X ^ 2 + C ua1 * X + C ua0))
    (hTU : IsCoprime ((X - C px : Polynomial (F p)) ^ 2)
      (X ^ 2 + C u1 * X + C u0))
    (hUaU : IsCoprime (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
      (X ^ 2 + C u1 * X + C u0))
    (hgcd : IsCoprime
      (Ypoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1)
      (uRS4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1))
    (hInv :
      uRS4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 ∣
        Ypoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 *
            EuclideanDomain.gcdA
              (Ypoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1)
              (uRS4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1) - 1) :
    (vRS4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 hgcd) ^ 2 %ₘ
        uRS4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 =
      (curvePoly p c0 c1 c2 c3 c4) %ₘ
        uRS4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 := by
  have hNu :
      uRS4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 ∣
        Npoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 :=
    uRS4Tangent_dvd_Npoly4Tangent_full p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1
      hcur hA hpy hp2 hP_curve hNe hMumfordUa hMumfordTarget hTUa hTU hUaU
  have hU : (uRS4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1).Monic :=
    uRS4Tangent_monic p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 hcur
  have hmod := sq_mod_eq_of_dvd_4 hU hNu hInv
  simpa only [vRS4Tangent] using hmod

end TangentCombine4

section MumfordIdentity4

variable (c0 c1 c2 c3 c4 : F p) (P1 P2 : F p × F p) (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
variable (hcur : curBeforeMonic4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
variable (hgcd : IsCoprime (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
  (uRS4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1))

/-- **The Mumford identity, K=4 instance**: `v_RS4(x)^2 ≡ curvePoly(x)
(mod u_RS4(x))`. Direct K=4 port of `vRS_sq_eq_f_mod_uRS`; same
`hInv` vs `hgcd` distinction applies (see that theorem's docstring) — `hInv`
is real remaining content, not a restatement of `hgcd`. -/
theorem vRS4_sq_eq_f_mod_uRS4
    (hcur :
      curBeforeMonic4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hA : MatrixNondegenerate4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hP1_curve : P1.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P1.1)
    (hP2_curve : P2.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P2.1)
    (hMumfordUa : IsMumfordUa p c0 c1 c2 c3 c4 ua0 ua1 va0 va1)
    (hMumfordTarget : IsMumfordTarget4 p c0 c1 c2 c3 c4 u0 u1 v0 v1)
    (h12 : IsCoprime (X - C P1.1 : Polynomial (F p)) (X - C P2.1))
    (h13 : IsCoprime (X - C P1.1 : Polynomial (F p))
      (X ^ 2 + C ua1 * X + C ua0))
    (h14 : IsCoprime (X - C P1.1 : Polynomial (F p))
      (X ^ 2 + C u1 * X + C u0))
    (h23 : IsCoprime (X - C P2.1 : Polynomial (F p))
      (X ^ 2 + C ua1 * X + C ua0))
    (h24 : IsCoprime (X - C P2.1 : Polynomial (F p))
      (X ^ 2 + C u1 * X + C u0))
    (h34 : IsCoprime (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
      (X ^ 2 + C u1 * X + C u0))
    (hInv :
      uRS4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ∣
        Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 *
            EuclideanDomain.gcdA
              (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
              (uRS4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) - 1) :
    (vRS4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hgcd) ^ 2 %ₘ
        uRS4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 =
      (curvePoly p c0 c1 c2 c3 c4) %ₘ
        uRS4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 := by
  -- `hNu` is no longer taken as a hypothesis: it is now DERIVED from
  -- `uRS4_dvd_Npoly4` (the four-factor combining theorem, proved above from
  -- the same pairwise-coprimality/curve/Mumford data this theorem now also
  -- takes explicitly), closing exactly the gap this file's own module
  -- docstring ("Same open gap as upstream, not a new one") flagged. `Npoly4`
  -- unfolds definitionally to `E^2 - f*Y^2`, so `uRS4_dvd_Npoly4`'s
  -- conclusion is `hNu'` after one `unfold`.
  have hNu :
      uRS4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ∣
        Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 :=
    uRS4_dvd_Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1
      hcur hA hP1_curve hP2_curve hMumfordUa hMumfordTarget h12 h13 h14 h23 h24 h34
  let U := uRS4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1
  let E := Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1
  let Y := Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1
  let G := EuclideanDomain.gcdA Y U
  let f := curvePoly p c0 c1 c2 c3 c4
  have hU : U.Monic :=
    uRS4_monic p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hcur
  have hInv' : U ∣ Y * G - 1 := by exact hInv
  have hNu' : U ∣ E ^ 2 - f * Y ^ 2 := by
    show uRS4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ∣
      (Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) ^ 2 -
        (curvePoly p c0 c1 c2 c3 c4) * (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) ^ 2
    have hNu2 : uRS4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ∣
        (Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) ^ 2 -
          (curvePoly p c0 c1 c2 c3 c4) * (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) ^ 2 := by
      unfold Npoly4 at hNu; exact hNu
    exact hNu2
  have hmod := sq_mod_eq_of_dvd_4 hU hNu' hInv'
  simpa only [vRS4, U, E, Y, G, f] using hmod

end MumfordIdentity4

/-! ## `Reduce`, assembled

Per `AlphaLocusDegreeUniform.lean`'s own "`Reduce`'s actual algorithm, now
on file" section (step 4's note, read closely this pass): the
`(u0,u1,v0,v1)` fed INTO the K=4 linear system (`matrixA4`'s rows 4,5) is
NOT the same thing as `Reduce`'s OUTPUT — it is whichever target this
particular call is reducing against (the other sample's target in the
two-sample matching setup, or "the point at infinity" for a base-case
single reduction). The output — `uRS4`/`vRS4`'s own coefficients — is a
genuinely different `(u0,u1,v0,v1)`-shaped tuple. So `Reduce` below takes
the input target as a parameter (matching `uRS4`/`vRS4`'s own existing
signatures exactly, no new machinery) and reads the OUTPUT off as
`uRS4`/`vRS4`'s coefficients — there is no circularity, just two distinct
uses of the same 4-tuple shape at different points in the pipeline.

**`uRS4`/`vRS4` have `natDegree ≤ 2`** (`uRS4_natDegree_le_two`; `vRS4`'s
bound isn't separately proved here but follows the same way, being a
`%ₘ uRS4` remainder), so `.coeff 0`/`.coeff 1` are exactly the `u0/v0` and
`u1/v1` slots a Mumford pair's degree-≤2 encoding needs (`.coeff 2`, the
leading term, is `1` since `uRS4` is monic by `uRS4_monic` — dropped, same
convention `SampleTarget` already uses throughout).

**Signature note**: takes `hgcd`/`hcur` as explicit hypotheses, matching
this file's "hypotheses instead of proof" convention — `Reduce` does not
prove coprimality or non-degeneracy, it requires them, exactly as
`vRS4`/`uRS4_monic` already do. This is NOT the `uRS4 ∣ Npoly4` combining
gap (routed to `chatgpt_prompt_uRS4_dvd_Npoly4.md`, not yet answered) —
that gap is about CORRECTNESS of `(uRS4,vRS4)` as the true Mumford
reduction, not about whether `Reduce` can be defined; `Reduce` below is
unconditionally well-defined given `hgcd`/`hcur`, and its correctness
(i.e. that it actually computes `alpha•a - P1 - P2`'s reduction) is a
separate, not-yet-attempted theorem. -/

/-- **`Reduce`**: Mumford-reduce `alpha • a - P1 - P2` against a given
target `(u0,u1,v0,v1)` (the divisor class this call's linear system is
solving relative to — see the section docstring above), returning the new
Mumford pair `(u0',u1',v0',v1')` read off `uRS4`/`vRS4`'s coefficients.
`(ua0,ua1,va0,va1)` is `alpha • a`'s own already-reduced Mumford pair,
handed in precomputed per the module docstring's "`alpha • a` is
precomputed, not computed here" finding. -/
noncomputable def Reduce (c0 c1 c2 c3 c4 : F p) (P1 P2 : F p × F p)
    (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (_hcur : curBeforeMonic4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hgcd : IsCoprime (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
      (uRS4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)) :
    F p × F p × F p × F p :=
  ((uRS4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).coeff 0,
   (uRS4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).coeff 1,
   (vRS4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hgcd).coeff 0,
   (vRS4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hgcd).coeff 1)

/-! ## `ReduceTangent` and the `P1 = P2` dispatcher

`Reduce` above is unconditionally computable, but only *correct* when
`P1 ≠ P2` — the ordinary construction's row-01 uses two evaluation
points, and `hgcd`/`hcur` become unsatisfiable (not merely uncorroborated)
once `P1 = P2`, since the corresponding `MatrixNondegenerate4` forces a
det on two linearly-dependent rows. `IsCoprime (X - C P1.1) (X - C P2.1)`
itself is simply false when `P1.1 = P2.1`, so no caller can actually
discharge `Reduce`'s hypotheses in the tangent case using the ordinary
pipeline — that's what the tangent machinery (`Epoly4Tangent` etc.,
`TangentCombine4` above) exists to replace.

`ReduceTangent` mirrors `Reduce` exactly, reading its output off
`uRS4Tangent`/`vRS4Tangent`'s coefficients instead. `ReduceDispatch` case-
splits on `P1 = P2` and calls one or the other, so a caller supplies
*either* the six ordinary coprimality facts (`P1 ≠ P2` branch) *or* the
three tangent ones `hTUa`/`hTU`/`hUaU` (`P1 = P2` branch) — never both, and
never the unusable `h12`-style hypothesis in the tangent branch. This is
purely a wiring layer: it does not prove correctness of either branch (that
is `uRS4_dvd_Npoly4`/`vRS4_sq_eq_f_mod_uRS4` on one side and
`uRS4Tangent_dvd_Npoly4Tangent_full`/`vRS4Tangent_sq_eq_f_mod_uRS4Tangent_full`
on the other, both proved elsewhere in this file already), it only lets a
caller reach the right branch's output without ever stating the wrong
branch's hypotheses. -/

/-- **`ReduceTangent`**: tangent-case counterpart of `Reduce`, for
`alpha • a - 2•(px,py)` (a doubled point rather than two distinct points).
Reads the output Mumford pair off `uRS4Tangent`/`vRS4Tangent`'s
coefficients, exactly as `Reduce` does for `uRS4`/`vRS4`. -/
noncomputable def ReduceTangent (c0 c1 c2 c3 c4 px py : F p)
    (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (_hcur : curBeforeMonic4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hgcd : IsCoprime (Ypoly4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1)
      (uRS4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1)) :
    F p × F p × F p × F p :=
  ((uRS4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1).coeff 0,
   (uRS4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1).coeff 1,
   (vRS4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 hgcd).coeff 0,
   (vRS4Tangent p c0 c1 c2 c3 c4 px py ua0 ua1 va0 va1 u0 u1 v0 v1 hgcd).coeff 1)

/-- **`ReduceDispatch`**: case-splits on `P1 = P2` and routes to `Reduce`
(`P1 ≠ P2` branch) or `ReduceTangent` (`P1 = P2` branch, `(px,py) := P1`).
Unlike a version taking both hypothesis bundles up front, `hcur`/`hgcd` and
`hcurT`/`hgcdT` here are each a *function* out of the corresponding case
(`P1 ≠ P2 → ...` / `P1 = P2 → ...`), so a caller only ever has to produce
the bundle matching the case they are actually in — never
`IsCoprime (X - C P1.1) (X - C P2.1)` when `P1 = P2`, since that fact is
false in that case, not just hard to prove. -/
noncomputable def ReduceDispatch (c0 c1 c2 c3 c4 : F p) (P1 P2 : F p × F p)
    (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (hcur : P1 ≠ P2 →
      curBeforeMonic4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hgcd : P1 ≠ P2 → IsCoprime (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
      (uRS4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1))
    (hcurT : P1 = P2 →
      curBeforeMonic4Tangent p c0 c1 c2 c3 c4 P1.1 P1.2 ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hgcdT : P1 = P2 → IsCoprime
      (Ypoly4Tangent p c0 c1 c2 c3 c4 P1.1 P1.2 ua0 ua1 va0 va1 u0 u1 v0 v1)
      (uRS4Tangent p c0 c1 c2 c3 c4 P1.1 P1.2 ua0 ua1 va0 va1 u0 u1 v0 v1)) :
    F p × F p × F p × F p :=
  if hP : P1 = P2 then
    ReduceTangent p c0 c1 c2 c3 c4 P1.1 P1.2 ua0 ua1 va0 va1 u0 u1 v0 v1
      (hcurT hP) (hgcdT hP)
  else
    Reduce p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 (hcur hP) (hgcd hP)

end TheDataDerivation
end Genus2Lean
