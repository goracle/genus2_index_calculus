import Mathlib
import Genus2Lean.ZeroD.MvPolynomialSharedTargetSolve
import Genus2Lean.ZeroD.IdealOfListNeTopFromEval
import Genus2Lean.ZeroD.DecoupledSystemRegular

/-!
# Composing the four shared-target pairs: `htop_ne_smul`, modulo a curve-side witness

Revision 3: make `DecoupledGenerators` disjointness lemmas generic in `d`, so the concrete resultant-built `theData` value is never unfolded while checking the large chaining proof.

New this pass. `MvPolynomialSharedTargetSolve.lean` solves ONE shared-target
pair (e.g. `U0`'s two generators) given a fixed assignment on the other 8
("curve-side") variables, returning a new assignment agreeing with the old
one everywhere except possibly at that one target variable. This file
chains that lemma across all 4 targets (`U0,U1,V0,V1`) simultaneously,
starting from a single curve-side assignment, and plugs the result into
`IdealOfListNeTopFromEval.lean` to conclude `Ideal.ofList (genList ...) ≠ ⊤`
— i.e. this is the actual `Genus2Lean`-specific composition both of those
files' own closing notes flagged as "not attempted here, future pass."

**The one general-purpose lemma this needed that didn't exist yet**:
`MvPolynomial.eval_eq_eval_of_update_notmem` below — if `assign'` agrees
with `assign` everywhere except possibly at one point `j`, and `j` isn't
one of a polynomial `q`'s variables, then `eval assign' q = eval assign q`.
This is the general form of the "changing a foreign coordinate doesn't
touch `eval`" fact `MvPolynomialSharedTargetSolve.lean`'s own proof already
uses ad hoc twice; naming it once here turns each of the 4 chaining steps
below into a two-line `have`, rather than re-deriving it by hand each time.

**Why chaining 4 single-variable updates is safe.** Each pair's `n,d`
polynomials (`DecoupledGenerators.u1_indep`/etc.) only involve the 8
curve-side variables — never any of `U0,U1,V0,V1`. So after solving the
`U0` pair (which only touches the assignment's `U0` coordinate), every
OTHER pair's `n,d` — none of which mention `U0` — evaluates identically to
before, by the lemma above. Iterating, all 4 pairs solve independently
from the same curve-side data, in any order, with no pair's solution
disturbing another's hypotheses. The curve relations themselves (also
never mentioning `U0,U1,V0,V1`) survive all four updates for the same
reason.

**What this file needs as input, honestly stated**: a curve-side assignment
`assign : Idx → F p` such that (a) all 4 curve relations vanish there, (b)
`theData`'s 8 denominators are nonzero there, and (c) the 4 cross-resultants
(`hu0`/`hu1`/`hv0`/`hv1`'s literal elements) vanish there. **(a) is genuine
elliptic/hyperelliptic-curve point-existence over `F p = ZMod p` — real
number theory, not attempted here or anywhere else in this project so
far.** (b)/(c) are the same per-point conditions `Nondegenerate`/
`CrossNondegenerate` name at the `IsSMulRegular`/structural level, here
needed only as bare evaluations at one point — strictly weaker, but still
open. This file does NOT supply (a)/(b)/(c) — it supplies the (now
nontrivial, previously-unassembled) bridge FROM (a)/(b)/(c) TO
`htop_ne_smul` itself, cleanly isolating exactly what's still missing.

**Status**: `genList_exists_common_zero_of_curve_witness` (the chaining
argument) is REPL-confirmed green. The composition into
`Ideal.ofList (genList ...) ≠ ⊤` promised by this file's title is now
also written, as `ideal_ofList_genList_ne_top_of_curve_witness` below —
not yet REPL-confirmed as of this pass; Claire tests via the REPL.
-/

namespace Genus2Lean

open DecoupledSystem
open TheDataDerivation hiding F
open MvPolynomial Idx

/-- **General-purpose**: if `assign'` and `assign` agree everywhere except
possibly at `j`, and `j` isn't one of `q`'s variables, `eval` sees no
difference. Direct corollary of `MvPolynomial.eval_eq_eval_of_eqOn_vars`
(`MvPolynomialLinearSolve.lean`) — the only work is converting "agrees off
`{j}`" into "agrees on `q.vars`", via `j ∉ q.vars` ruling out the one
coordinate where they might differ. -/
theorem MvPolynomial.eval_eq_eval_of_update_notMem {σ S : Type*} [CommRing S]
    {q : MvPolynomial σ S} {assign assign' : σ → S} {j : σ}
    (hoff : ∀ i ∈ ({j}ᶜ : Set σ), assign' i = assign i) (hj : j ∉ q.vars) :
    MvPolynomial.eval assign' q = MvPolynomial.eval assign q :=
  MvPolynomial.eval_eq_eval_of_eqOn_vars
    (fun i hi => hoff i (fun h => hj (h ▸ hi)))


/-- Carry a solved `eval n - a j * eval d = 0` equation across three
single-coordinate updates.  This is deliberately a separate declaration:
the expensive `eval` invariance rewrites get a fresh heartbeat budget
instead of being elaborated as part of the large headline theorem. -/
theorem carry_eval_sub_mul_three {σ R : Type*} [CommRing R]
    {n d : MvPolynomial σ R} {j : σ}
    {a0 a1 a2 a3 : σ → R}
    {j1 j2 j3 : σ}
    (hoff1 : ∀ i ∈ ({j1}ᶜ : Set σ), a1 i = a0 i)
    (hoff2 : ∀ i ∈ ({j2}ᶜ : Set σ), a2 i = a1 i)
    (hoff3 : ∀ i ∈ ({j3}ᶜ : Set σ), a3 i = a2 i)
    (hn1 : j1 ∉ n.vars) (hd1 : j1 ∉ d.vars)
    (hn2 : j2 ∉ n.vars) (hd2 : j2 ∉ d.vars)
    (hn3 : j3 ∉ n.vars) (hd3 : j3 ∉ d.vars)
    (ht1 : a1 j = a0 j) (ht2 : a2 j = a1 j) (ht3 : a3 j = a2 j)
    (h0 : MvPolynomial.eval a0 n - a0 j * MvPolynomial.eval a0 d = 0) :
    MvPolynomial.eval a3 n - a3 j * MvPolynomial.eval a3 d = 0 := by
  have hn1' : MvPolynomial.eval a1 n = MvPolynomial.eval a0 n :=
    MvPolynomial.eval_eq_eval_of_update_notMem hoff1 hn1
  have hd1' : MvPolynomial.eval a1 d = MvPolynomial.eval a0 d :=
    MvPolynomial.eval_eq_eval_of_update_notMem hoff1 hd1
  have hn2' : MvPolynomial.eval a2 n = MvPolynomial.eval a1 n :=
    MvPolynomial.eval_eq_eval_of_update_notMem hoff2 hn2
  have hd2' : MvPolynomial.eval a2 d = MvPolynomial.eval a1 d :=
    MvPolynomial.eval_eq_eval_of_update_notMem hoff2 hd2
  have hn3' : MvPolynomial.eval a3 n = MvPolynomial.eval a2 n :=
    MvPolynomial.eval_eq_eval_of_update_notMem hoff3 hn3
  have hd3' : MvPolynomial.eval a3 d = MvPolynomial.eval a2 d :=
    MvPolynomial.eval_eq_eval_of_update_notMem hoff3 hd3
  rw [hn3', hd3', ht3, hn2', hd2', ht2, hn1', hd1', ht1]
  exact h0

/-- Carry a solved equation across two single-coordinate updates. -/
theorem carry_eval_sub_mul_two {σ R : Type*} [CommRing R]
    {n d : MvPolynomial σ R} {j : σ}
    {a0 a1 a2 : σ → R}
    {j1 j2 : σ}
    (hoff1 : ∀ i ∈ ({j1}ᶜ : Set σ), a1 i = a0 i)
    (hoff2 : ∀ i ∈ ({j2}ᶜ : Set σ), a2 i = a1 i)
    (hn1 : j1 ∉ n.vars) (hd1 : j1 ∉ d.vars)
    (hn2 : j2 ∉ n.vars) (hd2 : j2 ∉ d.vars)
    (ht1 : a1 j = a0 j) (ht2 : a2 j = a1 j)
    (h0 : MvPolynomial.eval a0 n - a0 j * MvPolynomial.eval a0 d = 0) :
    MvPolynomial.eval a2 n - a2 j * MvPolynomial.eval a2 d = 0 := by
  have hn1' : MvPolynomial.eval a1 n = MvPolynomial.eval a0 n :=
    MvPolynomial.eval_eq_eval_of_update_notMem hoff1 hn1
  have hd1' : MvPolynomial.eval a1 d = MvPolynomial.eval a0 d :=
    MvPolynomial.eval_eq_eval_of_update_notMem hoff1 hd1
  have hn2' : MvPolynomial.eval a2 n = MvPolynomial.eval a1 n :=
    MvPolynomial.eval_eq_eval_of_update_notMem hoff2 hn2
  have hd2' : MvPolynomial.eval a2 d = MvPolynomial.eval a1 d :=
    MvPolynomial.eval_eq_eval_of_update_notMem hoff2 hd2
  rw [hn2', hd2', ht2, hn1', hd1', ht1]
  exact h0

/-- Carry a solved equation across one single-coordinate update. -/
theorem carry_eval_sub_mul_one {σ R : Type*} [CommRing R]
    {n d : MvPolynomial σ R} {j : σ}
    {a0 a1 : σ → R} {j1 : σ}
    (hoff1 : ∀ i ∈ ({j1}ᶜ : Set σ), a1 i = a0 i)
    (hn1 : j1 ∉ n.vars) (hd1 : j1 ∉ d.vars)
    (ht1 : a1 j = a0 j)
    (h0 : MvPolynomial.eval a0 n - a0 j * MvPolynomial.eval a0 d = 0) :
    MvPolynomial.eval a1 n - a1 j * MvPolynomial.eval a1 d = 0 := by
  have hn1' : MvPolynomial.eval a1 n = MvPolynomial.eval a0 n :=
    MvPolynomial.eval_eq_eval_of_update_notMem hoff1 hn1
  have hd1' : MvPolynomial.eval a1 d = MvPolynomial.eval a0 d :=
    MvPolynomial.eval_eq_eval_of_update_notMem hoff1 hd1
  rw [hn1', hd1', ht1]
  exact h0

variable (p : ℕ) [hp : Fact (Nat.Prime p)] [hp2 : Fact (p ≠ 2)]

/-- Extract the target-variable disjointness from the abstract `DecoupledGenerators`
structure.  Crucially, this lemma is parameterized by `d`; it does not mention
`theData` at all.  Thus applying it to the huge `theData` expression does not
force Lean to unfold the resultant-built implementation merely to elaborate
the proposition. -/
theorem target_notmem_u1
    (d : DecoupledGenerators p) (i : Fin 2) (j : Idx)
    (hj : j ∉ ({wa1, wa2, a1, a2} : Finset Idx)) :
    j ∉ (d.u1_num i).vars ∪ (d.u1_den i).vars := by
  intro h
  exact hj (d.u1_indep i j h)

/-- The corresponding fact for the `u2` pair. -/
theorem target_notmem_u2
    (d : DecoupledGenerators p) (i : Fin 2) (j : Idx)
    (hj : j ∉ ({wb1, wb2, b1, b2} : Finset Idx)) :
    j ∉ (d.u2_num i).vars ∪ (d.u2_den i).vars := by
  intro h
  exact hj (d.u2_indep i j h)

/-- The corresponding fact for the `v1` pair. -/
theorem target_notmem_v1
    (d : DecoupledGenerators p) (i : Fin 2) (j : Idx)
    (hj : j ∉ ({wa1, wa2, a1, a2} : Finset Idx)) :
    j ∉ (d.v1_num i).vars ∪ (d.v1_den i).vars := by
  intro h
  exact hj (d.v1_indep i j h)

/-- The corresponding fact for the `v2` pair. -/
theorem target_notmem_v2
    (d : DecoupledGenerators p) (i : Fin 2) (j : Idx)
    (hj : j ∉ ({wb1, wb2, b1, b2} : Finset Idx)) :
    j ∉ (d.v2_num i).vars ∪ (d.v2_den i).vars := by
  intro h
  exact hj (d.v2_indep i j h)

/-- Bundle the six facts needed to carry the `U0` solution forward.  This
statement remains completely generic in `d`, so the expensive implementation
of `theData` is never part of this declaration's elaboration. -/
theorem theData_late_target_notmem
    (d : DecoupledGenerators p) :
    U1 ∉ (d.u1_num 0).vars ∪ (d.u1_den 0).vars ∧
    V0 ∉ (d.u1_num 0).vars ∪ (d.u1_den 0).vars ∧
    V1 ∉ (d.u1_num 0).vars ∪ (d.u1_den 0).vars ∧
    U1 ∉ (d.u2_num 0).vars ∪ (d.u2_den 0).vars ∧
    V0 ∉ (d.u2_num 0).vars ∪ (d.u2_den 0).vars ∧
    V1 ∉ (d.u2_num 0).vars ∪ (d.u2_den 0).vars := by
  refine ⟨target_notmem_u1 p d 0 U1 (by decide),
    target_notmem_u1 p d 0 V0 (by decide),
    target_notmem_u1 p d 0 V1 (by decide),
    target_notmem_u2 p d 0 U1 (by decide),
    target_notmem_u2 p d 0 V0 (by decide),
    target_notmem_u2 p d 0 V1 (by decide)⟩

/-- Bundle the six facts needed to carry the `U1` and `V0` solutions forward,
again without mentioning the concrete `theData` construction. -/
theorem theData_remaining_target_notmem
    (d : DecoupledGenerators p) :
    V0 ∉ (d.u1_num 1).vars ∪ (d.u1_den 1).vars ∧
    V1 ∉ (d.u1_num 1).vars ∪ (d.u1_den 1).vars ∧
    V0 ∉ (d.u2_num 1).vars ∪ (d.u2_den 1).vars ∧
    V1 ∉ (d.u2_num 1).vars ∪ (d.u2_den 1).vars ∧
    V1 ∉ (d.v1_num 0).vars ∪ (d.v1_den 0).vars ∧
    V1 ∉ (d.v2_num 0).vars ∪ (d.v2_den 0).vars := by
  refine ⟨target_notmem_u1 p d 1 V0 (by decide),
    target_notmem_u1 p d 1 V1 (by decide),
    target_notmem_u2 p d 1 V0 (by decide),
    target_notmem_u2 p d 1 V1 (by decide),
    target_notmem_v1 p d 0 V1 (by decide),
    target_notmem_v2 p d 0 V1 (by decide)⟩

set_option maxHeartbeats 20000000 in
/-- **The headline fact.** Given a curve-side assignment `assign : Idx →
F p` satisfying: all 4 curve relations vanish, all 8 `theData` denominators
are nonzero, and all 4 cross-resultants vanish — there is a full
12-variable assignment `assign'` making EVERY element of `genList p c0 c1
c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB` evaluate to `0`. -/
theorem genList_exists_common_zero_of_curve_witness
    (c0 c1 c2 c3 c4 : F p) (sa sb : SampleTarget p)
    (hcurA : curBeforeMonic p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 ≠ 0)
    (hcurB : curBeforeMonic p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 ≠ 0)
    (hgcdA : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1)
      (uRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1))
    (hgcdB : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1)
      (uRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1))
    (assign : Idx → F p)
    (hcurveA1 : MvPolynomial.eval assign (curveA1 p c0 c1 c2 c3 c4) = 0)
    (hcurveA2 : MvPolynomial.eval assign (curveA2 p c0 c1 c2 c3 c4) = 0)
    (hcurveB1 : MvPolynomial.eval assign (curveB1 p c0 c1 c2 c3 c4) = 0)
    (hcurveB2 : MvPolynomial.eval assign (curveB2 p c0 c1 c2 c3 c4) = 0)
    (hu1d0 : MvPolynomial.eval assign
      ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_den 0) ≠ 0)
    (hu2d0 : MvPolynomial.eval assign
      ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_den 0) ≠ 0)
    (hu1d1 : MvPolynomial.eval assign
      ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_den 1) ≠ 0)
    (hu2d1 : MvPolynomial.eval assign
      ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_den 1) ≠ 0)
    (hv1d0 : MvPolynomial.eval assign
      ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_den 0) ≠ 0)
    (hv2d0 : MvPolynomial.eval assign
      ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_den 0) ≠ 0)
    (hv1d1 : MvPolynomial.eval assign
      ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_den 1) ≠ 0)
    (hv2d1 : MvPolynomial.eval assign
      ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_den 1) ≠ 0)
    (hresU0 : MvPolynomial.eval assign
        ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_num 0) *
      MvPolynomial.eval assign
        ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_den 0) =
      MvPolynomial.eval assign
        ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_num 0) *
      MvPolynomial.eval assign
        ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_den 0))
    (hresU1 : MvPolynomial.eval assign
        ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_num 1) *
      MvPolynomial.eval assign
        ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_den 1) =
      MvPolynomial.eval assign
        ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_num 1) *
      MvPolynomial.eval assign
        ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_den 1))
    (hresV0 : MvPolynomial.eval assign
        ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_num 0) *
      MvPolynomial.eval assign
        ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_den 0) =
      MvPolynomial.eval assign
        ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_num 0) *
      MvPolynomial.eval assign
        ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_den 0))
    (hresV1 : MvPolynomial.eval assign
        ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_num 1) *
      MvPolynomial.eval assign
        ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_den 1) =
      MvPolynomial.eval assign
        ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_num 1) *
      MvPolynomial.eval assign
        ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_den 1)) :
    ∃ assign' : Idx → F p,
      ∀ g ∈ genList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB,
        MvPolynomial.eval assign' g = 0 := by
  set d := theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB with hd_def
  -- Each target's `∉ Finset` disjointness, from `u1_indep`/etc.'s `∈ Finset`
  -- membership shape — `Idx`'s 12 constructors are pairwise distinct
  -- (`decide`-checkable), so `U0 ∈ {wa1,wa2,a1,a2}` etc. are all `False`.
  have hU0 : U0 ∉ (d.u1_num 0).vars ∪ (d.u1_den 0).vars :=
    target_notmem_u1 p d 0 U0 (by decide)
  have hU0' : U0 ∉ (d.u2_num 0).vars ∪ (d.u2_den 0).vars :=
    target_notmem_u2 p d 0 U0 (by decide)
  have hU1 : U1 ∉ (d.u1_num 1).vars ∪ (d.u1_den 1).vars :=
    target_notmem_u1 p d 1 U1 (by decide)
  have hU1' : U1 ∉ (d.u2_num 1).vars ∪ (d.u2_den 1).vars :=
    target_notmem_u2 p d 1 U1 (by decide)
  have hV0 : V0 ∉ (d.v1_num 0).vars ∪ (d.v1_den 0).vars :=
    target_notmem_v1 p d 0 V0 (by decide)
  have hV0' : V0 ∉ (d.v2_num 0).vars ∪ (d.v2_den 0).vars :=
    target_notmem_v2 p d 0 V0 (by decide)
  have hV1 : V1 ∉ (d.v1_num 1).vars ∪ (d.v1_den 1).vars :=
    target_notmem_v1 p d 1 V1 (by decide)
  have hV1' : V1 ∉ (d.v2_num 1).vars ∪ (d.v2_den 1).vars :=
    target_notmem_v2 p d 1 V1 (by decide)
  -- Step 1: solve the `U0` pair from `assign` itself.
  obtain ⟨a1, ha1_off, ha1_u0a, ha1_u0b⟩ :=
    MvPolynomial.exists_update_eval_sub_X_mul_eq_zero_pair
      (d.u1_num 0) (d.u1_den 0) (d.u2_num 0) (d.u2_den 0) U0 hU0 hU0'
      assign hu1d0 hu2d0 hresU0
  -- Step 2: solve the `U1` pair from `a1`. `U1 ∉ {U0}`, and none of this
  -- pair's `n,d` mention `U0` (`hU1`/`hU1'` only rule out `U1`, but the
  -- SAME `u1_indep`-style fact shows they don't mention `U0` either, since
  -- both are outside the curve-variable set `u1_indep` restricts to) — so
  -- `a1`'s change at `U0` alone can't perturb them; the general lemma
  -- above needs only `U0 ∉ (this pair's vars)`, exactly `hU0`-shaped
  -- (reusing the SAME independence fact, since `u1_num 1`/`u1_den 1` are
  -- ALSO confined to the curve variables, disjoint from `U0` too).
  have hU0_1 : U0 ∉ (d.u1_num 1).vars ∪ (d.u1_den 1).vars :=
    target_notmem_u1 p d 1 U0 (by decide)
  have hU0_1' : U0 ∉ (d.u2_num 1).vars ∪ (d.u2_den 1).vars :=
    target_notmem_u2 p d 1 U0 (by decide)
  have ha1_u1d1 : MvPolynomial.eval a1 (d.u1_den 1) = MvPolynomial.eval assign (d.u1_den 1) :=
    MvPolynomial.eval_eq_eval_of_update_notMem ha1_off
      (fun h => hU0_1 (Finset.mem_union_right _ h))
  have ha1_u2d1 : MvPolynomial.eval a1 (d.u2_den 1) = MvPolynomial.eval assign (d.u2_den 1) :=
    MvPolynomial.eval_eq_eval_of_update_notMem ha1_off
      (fun h => hU0_1' (Finset.mem_union_right _ h))
  have ha1_u1n1 : MvPolynomial.eval a1 (d.u1_num 1) = MvPolynomial.eval assign (d.u1_num 1) :=
    MvPolynomial.eval_eq_eval_of_update_notMem ha1_off
      (fun h => hU0_1 (Finset.mem_union_left _ h))
  have ha1_u2n1 : MvPolynomial.eval a1 (d.u2_num 1) = MvPolynomial.eval assign (d.u2_num 1) :=
    MvPolynomial.eval_eq_eval_of_update_notMem ha1_off
      (fun h => hU0_1' (Finset.mem_union_left _ h))
  obtain ⟨a2, ha2_off, ha2_u1a, ha2_u1b⟩ :=
    MvPolynomial.exists_update_eval_sub_X_mul_eq_zero_pair
      (d.u1_num 1) (d.u1_den 1) (d.u2_num 1) (d.u2_den 1) U1 hU1 hU1'
      a1 (ha1_u1d1 ▸ hu1d1) (ha1_u2d1 ▸ hu2d1)
      (by rw [ha1_u1n1, ha1_u2d1, ha1_u2n1, ha1_u1d1]; exact hresU1)
  -- Step 3: solve the `V0` pair from `a2`. `V0`'s pair only mentions curve
  -- variables (per `v1_indep`/`v2_indep`), disjoint from BOTH `U0` and
  -- `U1` — so it survives both prior updates.
  have hU0_2 : U0 ∉ (d.v1_num 0).vars ∪ (d.v1_den 0).vars :=
    target_notmem_v1 p d 0 U0 (by decide)
  have hU0_2' : U0 ∉ (d.v2_num 0).vars ∪ (d.v2_den 0).vars :=
    target_notmem_v2 p d 0 U0 (by decide)
  have hU1_2 : U1 ∉ (d.v1_num 0).vars ∪ (d.v1_den 0).vars :=
    target_notmem_v1 p d 0 U1 (by decide)
  have hU1_2' : U1 ∉ (d.v2_num 0).vars ∪ (d.v2_den 0).vars :=
    target_notmem_v2 p d 0 U1 (by decide)
  have ha1_v1d0 : MvPolynomial.eval a1 (d.v1_den 0) = MvPolynomial.eval assign (d.v1_den 0) :=
    MvPolynomial.eval_eq_eval_of_update_notMem ha1_off
      (fun h => hU0_2 (Finset.mem_union_right _ h))
  have ha2_v1d0 : MvPolynomial.eval a2 (d.v1_den 0) = MvPolynomial.eval a1 (d.v1_den 0) :=
    MvPolynomial.eval_eq_eval_of_update_notMem ha2_off
      (fun h => hU1_2 (Finset.mem_union_right _ h))
  have ha1_v2d0 : MvPolynomial.eval a1 (d.v2_den 0) = MvPolynomial.eval assign (d.v2_den 0) :=
    MvPolynomial.eval_eq_eval_of_update_notMem ha1_off
      (fun h => hU0_2' (Finset.mem_union_right _ h))
  have ha2_v2d0 : MvPolynomial.eval a2 (d.v2_den 0) = MvPolynomial.eval a1 (d.v2_den 0) :=
    MvPolynomial.eval_eq_eval_of_update_notMem ha2_off
      (fun h => hU1_2' (Finset.mem_union_right _ h))
  have ha1_v1n0 : MvPolynomial.eval a1 (d.v1_num 0) = MvPolynomial.eval assign (d.v1_num 0) :=
    MvPolynomial.eval_eq_eval_of_update_notMem ha1_off
      (fun h => hU0_2 (Finset.mem_union_left _ h))
  have ha2_v1n0 : MvPolynomial.eval a2 (d.v1_num 0) = MvPolynomial.eval a1 (d.v1_num 0) :=
    MvPolynomial.eval_eq_eval_of_update_notMem ha2_off
      (fun h => hU1_2 (Finset.mem_union_left _ h))
  have ha1_v2n0 : MvPolynomial.eval a1 (d.v2_num 0) = MvPolynomial.eval assign (d.v2_num 0) :=
    MvPolynomial.eval_eq_eval_of_update_notMem ha1_off
      (fun h => hU0_2' (Finset.mem_union_left _ h))
  have ha2_v2n0 : MvPolynomial.eval a2 (d.v2_num 0) = MvPolynomial.eval a1 (d.v2_num 0) :=
    MvPolynomial.eval_eq_eval_of_update_notMem ha2_off
      (fun h => hU1_2' (Finset.mem_union_left _ h))
  have ha2_v1d0' : MvPolynomial.eval a2 (d.v1_den 0) = MvPolynomial.eval assign (d.v1_den 0) := by
    rw [ha2_v1d0, ha1_v1d0]
  have ha2_v2d0' : MvPolynomial.eval a2 (d.v2_den 0) = MvPolynomial.eval assign (d.v2_den 0) := by
    rw [ha2_v2d0, ha1_v2d0]
  have ha2_v1n0' : MvPolynomial.eval a2 (d.v1_num 0) = MvPolynomial.eval assign (d.v1_num 0) := by
    rw [ha2_v1n0, ha1_v1n0]
  have ha2_v2n0' : MvPolynomial.eval a2 (d.v2_num 0) = MvPolynomial.eval assign (d.v2_num 0) := by
    rw [ha2_v2n0, ha1_v2n0]
  obtain ⟨a3, ha3_off, ha3_v0a, ha3_v0b⟩ :=
    MvPolynomial.exists_update_eval_sub_X_mul_eq_zero_pair
      (d.v1_num 0) (d.v1_den 0) (d.v2_num 0) (d.v2_den 0) V0 hV0 hV0'
      a2 (ha2_v1d0' ▸ hv1d0) (ha2_v2d0' ▸ hv2d0)
      (by rw [ha2_v1n0', ha2_v2d0', ha2_v2n0', ha2_v1d0']; exact hresV0)
  -- Step 4: solve the `V1` pair from `a3`, same pattern once more (`V1`'s
  -- pair confined to curve variables, disjoint from `U0,U1,V0` all three).
  have hU0_3 : U0 ∉ (d.v1_num 1).vars ∪ (d.v1_den 1).vars :=
    target_notmem_v1 p d 1 U0 (by decide)
  have hU0_3' : U0 ∉ (d.v2_num 1).vars ∪ (d.v2_den 1).vars :=
    target_notmem_v2 p d 1 U0 (by decide)
  have hU1_3 : U1 ∉ (d.v1_num 1).vars ∪ (d.v1_den 1).vars :=
    target_notmem_v1 p d 1 U1 (by decide)
  have hU1_3' : U1 ∉ (d.v2_num 1).vars ∪ (d.v2_den 1).vars :=
    target_notmem_v2 p d 1 U1 (by decide)
  have hV0_3 : V0 ∉ (d.v1_num 1).vars ∪ (d.v1_den 1).vars := target_notmem_v1 p d 1 V0 (by decide)
  have hV0_3' : V0 ∉ (d.v2_num 1).vars ∪ (d.v2_den 1).vars := target_notmem_v2 p d 1 V0 (by decide)
  have ha1_v1d1 : MvPolynomial.eval a1 (d.v1_den 1) = MvPolynomial.eval assign (d.v1_den 1) :=
    MvPolynomial.eval_eq_eval_of_update_notMem ha1_off (fun h => hU0_3 (Finset.mem_union_right _ h))
  have ha2_v1d1 : MvPolynomial.eval a2 (d.v1_den 1) = MvPolynomial.eval a1 (d.v1_den 1) :=
    MvPolynomial.eval_eq_eval_of_update_notMem ha2_off (fun h => hU1_3 (Finset.mem_union_right _ h))
  have ha3_v1d1 : MvPolynomial.eval a3 (d.v1_den 1) = MvPolynomial.eval a2 (d.v1_den 1) :=
    MvPolynomial.eval_eq_eval_of_update_notMem ha3_off (fun h => hV0_3 (Finset.mem_union_right _ h))
  have ha1_v2d1 : MvPolynomial.eval a1 (d.v2_den 1) = MvPolynomial.eval assign (d.v2_den 1) :=
    MvPolynomial.eval_eq_eval_of_update_notMem ha1_off (fun h => hU0_3' (Finset.mem_union_right _ h))
  have ha2_v2d1 : MvPolynomial.eval a2 (d.v2_den 1) = MvPolynomial.eval a1 (d.v2_den 1) :=
    MvPolynomial.eval_eq_eval_of_update_notMem ha2_off (fun h => hU1_3' (Finset.mem_union_right _ h))
  have ha3_v2d1 : MvPolynomial.eval a3 (d.v2_den 1) = MvPolynomial.eval a2 (d.v2_den 1) :=
    MvPolynomial.eval_eq_eval_of_update_notMem ha3_off (fun h => hV0_3' (Finset.mem_union_right _ h))
  have ha1_v1n1 : MvPolynomial.eval a1 (d.v1_num 1) = MvPolynomial.eval assign (d.v1_num 1) :=
    MvPolynomial.eval_eq_eval_of_update_notMem ha1_off
      (fun h => hU0_3 (Finset.mem_union_left _ h))
  have ha2_v1n1 : MvPolynomial.eval a2 (d.v1_num 1) = MvPolynomial.eval a1 (d.v1_num 1) :=
    MvPolynomial.eval_eq_eval_of_update_notMem ha2_off
      (fun h => hU1_3 (Finset.mem_union_left _ h))
  have ha3_v1n1 : MvPolynomial.eval a3 (d.v1_num 1) = MvPolynomial.eval a2 (d.v1_num 1) :=
    MvPolynomial.eval_eq_eval_of_update_notMem ha3_off
      (fun h => hV0_3 (Finset.mem_union_left _ h))
  have ha1_v2n1 : MvPolynomial.eval a1 (d.v2_num 1) = MvPolynomial.eval assign (d.v2_num 1) :=
    MvPolynomial.eval_eq_eval_of_update_notMem ha1_off
      (fun h => hU0_3' (Finset.mem_union_left _ h))
  have ha2_v2n1 : MvPolynomial.eval a2 (d.v2_num 1) = MvPolynomial.eval a1 (d.v2_num 1) :=
    MvPolynomial.eval_eq_eval_of_update_notMem ha2_off
      (fun h => hU1_3' (Finset.mem_union_left _ h))
  have ha3_v2n1 : MvPolynomial.eval a3 (d.v2_num 1) = MvPolynomial.eval a2 (d.v2_num 1) :=
    MvPolynomial.eval_eq_eval_of_update_notMem ha3_off
      (fun h => hV0_3' (Finset.mem_union_left _ h))
  have ha3_v1d1' : MvPolynomial.eval a3 (d.v1_den 1) = MvPolynomial.eval assign (d.v1_den 1) := by
    rw [ha3_v1d1, ha2_v1d1, ha1_v1d1]
  have ha3_v2d1' : MvPolynomial.eval a3 (d.v2_den 1) = MvPolynomial.eval assign (d.v2_den 1) := by
    rw [ha3_v2d1, ha2_v2d1, ha1_v2d1]
  have ha3_v1n1' : MvPolynomial.eval a3 (d.v1_num 1) = MvPolynomial.eval assign (d.v1_num 1) := by
    rw [ha3_v1n1, ha2_v1n1, ha1_v1n1]
  have ha3_v2n1' : MvPolynomial.eval a3 (d.v2_num 1) = MvPolynomial.eval assign (d.v2_num 1) := by
    rw [ha3_v2n1, ha2_v2n1, ha1_v2n1]
  obtain ⟨a4, ha4_off, ha4_v1a, ha4_v1b⟩ :=
    MvPolynomial.exists_update_eval_sub_X_mul_eq_zero_pair
      (d.v1_num 1) (d.v1_den 1) (d.v2_num 1) (d.v2_den 1) V1 hV1 hV1'
      a3 (ha3_v1d1' ▸ hv1d1) (ha3_v2d1' ▸ hv2d1)
      (by rw [ha3_v1n1', ha3_v2d1', ha3_v2n1', ha3_v1d1']; exact hresV1)
  -- Curve relations never mention `U0,U1,V0,V1` at all (built purely from
  -- `X wa1/wa2/a1/a2/wb1/wb2/b1/b2` and constants `C c0..c4`), so all four
  -- updates leave them evaluating exactly as `assign` already made them: 0.
  --
  -- The previous proof tried to discharge this by repeatedly simplifying a
  -- membership in `vars` after `vars_sub_subset`.  That gets stuck on the
  -- right-hand side of the subtraction: `simp` knows the exact `vars` of `C`
  -- and `X`, but `vars_add_subset` / `vars_mul` / `vars_pow` are only subset
  -- lemmas, not simp equalities.  We therefore prove the needed subset bound
  -- once, structurally, and then the four non-memberships are just `decide`.
  have hC (x : Idx) (c : F p) :
      (MvPolynomial.C c : Rdec p).vars ⊆ ({x} : Finset Idx) := by
    simp
  have hpow (x : Idx) (n : ℕ) :
      ((MvPolynomial.X x : Rdec p) ^ n).vars ⊆ ({x} : Finset Idx) := by
    exact (MvPolynomial.vars_pow (MvPolynomial.X x) n).trans (by simp)
  have hmulPow (x : Idx) (c : F p) (n : ℕ) :
      (MvPolynomial.C c * (MvPolynomial.X x : Rdec p) ^ n).vars
        ⊆ ({x} : Finset Idx) := by
    exact (MvPolynomial.vars_mul _ _).trans
      (Finset.union_subset (hC x c) (hpow x n))
  have hadd (x : Idx) {q r : Rdec p}
      (hq : q.vars ⊆ ({x} : Finset Idx))
      (hr : r.vars ⊆ ({x} : Finset Idx)) :
      (q + r).vars ⊆ ({x} : Finset Idx) := by
    exact (MvPolynomial.vars_add_subset q r).trans (Finset.union_subset hq hr)
  have hright (x : Idx) :
      (MvPolynomial.C c0 + MvPolynomial.C c1 * (MvPolynomial.X x : Rdec p) +
        MvPolynomial.C c2 * (MvPolynomial.X x : Rdec p) ^ 2 +
        MvPolynomial.C c3 * (MvPolynomial.X x : Rdec p) ^ 3 +
        MvPolynomial.C c4 * (MvPolynomial.X x : Rdec p) ^ 4 +
        (MvPolynomial.X x : Rdec p) ^ 5).vars ⊆ ({x} : Finset Idx) := by
    have h1 :
        (MvPolynomial.C c1 * (MvPolynomial.X x : Rdec p)).vars
          ⊆ ({x} : Finset Idx) := by
      simpa using hmulPow x c1 1
    have h01 :
        (MvPolynomial.C c0 + MvPolynomial.C c1 * (MvPolynomial.X x : Rdec p)).vars
          ⊆ ({x} : Finset Idx) :=
      hadd x (hC x c0) h1
    have h012 :
        (MvPolynomial.C c0 + MvPolynomial.C c1 * (MvPolynomial.X x : Rdec p) +
          MvPolynomial.C c2 * (MvPolynomial.X x : Rdec p) ^ 2).vars
          ⊆ ({x} : Finset Idx) :=
      hadd x h01 (hmulPow x c2 2)
    have h0123 :
        (MvPolynomial.C c0 + MvPolynomial.C c1 * (MvPolynomial.X x : Rdec p) +
          MvPolynomial.C c2 * (MvPolynomial.X x : Rdec p) ^ 2 +
          MvPolynomial.C c3 * (MvPolynomial.X x : Rdec p) ^ 3).vars
          ⊆ ({x} : Finset Idx) :=
      hadd x h012 (hmulPow x c3 3)
    have h01234 :
        (MvPolynomial.C c0 + MvPolynomial.C c1 * (MvPolynomial.X x : Rdec p) +
          MvPolynomial.C c2 * (MvPolynomial.X x : Rdec p) ^ 2 +
          MvPolynomial.C c3 * (MvPolynomial.X x : Rdec p) ^ 3 +
          MvPolynomial.C c4 * (MvPolynomial.X x : Rdec p) ^ 4).vars
          ⊆ ({x} : Finset Idx) :=
      hadd x h0123 (hmulPow x c4 4)
    exact hadd x h01234 (hpow x 5)
  have hcurve (w x : Idx) :
      ((MvPolynomial.X w : Rdec p) ^ 2 -
        (MvPolynomial.C c0 + MvPolynomial.C c1 * (MvPolynomial.X x : Rdec p) +
          MvPolynomial.C c2 * (MvPolynomial.X x : Rdec p) ^ 2 +
          MvPolynomial.C c3 * (MvPolynomial.X x : Rdec p) ^ 3 +
          MvPolynomial.C c4 * (MvPolynomial.X x : Rdec p) ^ 4 +
          (MvPolynomial.X x : Rdec p) ^ 5)).vars ⊆ ({w, x} : Finset Idx) := by
    refine (MvPolynomial.vars_sub_subset ((MvPolynomial.X w : Rdec p) ^ 2)).trans ?_
    exact Finset.union_subset
      ((MvPolynomial.vars_pow (MvPolynomial.X w : Rdec p) 2).trans (by simp))
      ((hright x).trans (by simp))
  have hA1 : (curveA1 p c0 c1 c2 c3 c4).vars ⊆ ({Idx.wa1, Idx.a1} : Finset Idx) := by
    simpa [curveA1, wa1', a1'] using hcurve Idx.wa1 Idx.a1
  have hA2 : (curveA2 p c0 c1 c2 c3 c4).vars ⊆ ({Idx.wa2, Idx.a2} : Finset Idx) := by
    simpa [curveA2, wa2', a2'] using hcurve Idx.wa2 Idx.a2
  have hB1 : (curveB1 p c0 c1 c2 c3 c4).vars ⊆ ({Idx.wb1, Idx.b1} : Finset Idx) := by
    simpa [curveB1, wb1', b1'] using hcurve Idx.wb1 Idx.b1
  have hB2 : (curveB2 p c0 c1 c2 c3 c4).vars ⊆ ({Idx.wb2, Idx.b2} : Finset Idx) := by
    simpa [curveB2, wb2', b2'] using hcurve Idx.wb2 Idx.b2
  have hnotmem {q : Rdec p} {s : Finset Idx} {i : Idx}
      (hsub : q.vars ⊆ s) (hi : i ∉ s) : i ∉ q.vars := by
    intro h
    exact hi (hsub h)
  have hcurve_novars : ∀ q ∈ [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
      curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4],
      Idx.U0 ∉ q.vars ∧ Idx.U1 ∉ q.vars ∧ Idx.V0 ∉ q.vars ∧ Idx.V1 ∉ q.vars := by
    intro q hq
    fin_cases hq
    · exact ⟨hnotmem hA1 (by decide), hnotmem hA1 (by decide),
        hnotmem hA1 (by decide), hnotmem hA1 (by decide)⟩
    · exact ⟨hnotmem hA2 (by decide), hnotmem hA2 (by decide),
        hnotmem hA2 (by decide), hnotmem hA2 (by decide)⟩
    · exact ⟨hnotmem hB1 (by decide), hnotmem hB1 (by decide),
        hnotmem hB1 (by decide), hnotmem hB1 (by decide)⟩
    · exact ⟨hnotmem hB2 (by decide), hnotmem hB2 (by decide),
        hnotmem hB2 (by decide), hnotmem hB2 (by decide)⟩
  -- Curve relations survive all four updates: each relation avoids all of
  -- `U0,U1,V0,V1` (by `hcurve_novars` above), so `eval_eq_eval_of_update_notMem`
  -- applies at every step `assign → a1 → a2 → a3 → a4`.
  have hcarry_curve {q : Rdec p} (hq0 : U0 ∉ q.vars) (hq1 : U1 ∉ q.vars)
      (hqV0 : V0 ∉ q.vars) (hqV1 : V1 ∉ q.vars)
      (h0 : MvPolynomial.eval assign q = 0) : MvPolynomial.eval a4 q = 0 := by
    have e1 : MvPolynomial.eval a1 q = MvPolynomial.eval assign q :=
      MvPolynomial.eval_eq_eval_of_update_notMem ha1_off hq0
    have e2 : MvPolynomial.eval a2 q = MvPolynomial.eval a1 q :=
      MvPolynomial.eval_eq_eval_of_update_notMem ha2_off hq1
    have e3 : MvPolynomial.eval a3 q = MvPolynomial.eval a2 q :=
      MvPolynomial.eval_eq_eval_of_update_notMem ha3_off hqV0
    have e4 : MvPolynomial.eval a4 q = MvPolynomial.eval a3 q :=
      MvPolynomial.eval_eq_eval_of_update_notMem ha4_off hqV1
    rw [e4, e3, e2, e1, h0]
  obtain ⟨hcA1_0, hcA1_1, hcA1_V0, hcA1_V1⟩ :=
    hcurve_novars (curveA1 p c0 c1 c2 c3 c4) (by simp)
  obtain ⟨hcA2_0, hcA2_1, hcA2_V0, hcA2_V1⟩ :=
    hcurve_novars (curveA2 p c0 c1 c2 c3 c4) (by simp)
  obtain ⟨hcB1_0, hcB1_1, hcB1_V0, hcB1_V1⟩ :=
    hcurve_novars (curveB1 p c0 c1 c2 c3 c4) (by simp)
  obtain ⟨hcB2_0, hcB2_1, hcB2_V0, hcB2_V1⟩ :=
    hcurve_novars (curveB2 p c0 c1 c2 c3 c4) (by simp)
  have hfinalA1 : MvPolynomial.eval a4 (curveA1 p c0 c1 c2 c3 c4) = 0 :=
    hcarry_curve hcA1_0 hcA1_1 hcA1_V0 hcA1_V1 hcurveA1
  have hfinalA2 : MvPolynomial.eval a4 (curveA2 p c0 c1 c2 c3 c4) = 0 :=
    hcarry_curve hcA2_0 hcA2_1 hcA2_V0 hcA2_V1 hcurveA2
  have hfinalB1 : MvPolynomial.eval a4 (curveB1 p c0 c1 c2 c3 c4) = 0 :=
    hcarry_curve hcB1_0 hcB1_1 hcB1_V0 hcB1_V1 hcurveB1
  have hfinalB2 : MvPolynomial.eval a4 (curveB2 p c0 c1 c2 c3 c4) = 0 :=
    hcarry_curve hcB2_0 hcB2_1 hcB2_V0 hcB2_V1 hcurveB2
  -- Carry the already-solved target pairs forward.  The generic carry lemmas
  -- above isolate the expensive `eval`-invariance rewrites from this large
  -- dependent theorem.
  obtain ⟨hU1_farU0n, hV0_farU0n, hV1_farU0n, hU1_farU0d, hV0_farU0d, hV1_farU0d⟩ :=
    theData_late_target_notmem p d


  have ha2_t_U0 : a2 U0 = a1 U0 := ha2_off U0 (by decide)
  have ha3_t_U0 : a3 U0 = a2 U0 := ha3_off U0 (by decide)
  have ha4_t_U0 : a4 U0 = a3 U0 := ha4_off U0 (by decide)

  have hfinalU0a : MvPolynomial.eval a4 (d.u1_num 0) -
      a4 U0 * MvPolynomial.eval a4 (d.u1_den 0) = 0 :=
    carry_eval_sub_mul_three
      ha2_off ha3_off ha4_off
      (fun h => hU1_farU0n (Finset.mem_union_left _ h))
      (fun h => hU1_farU0n (Finset.mem_union_right _ h))
      (fun h => hV0_farU0n (Finset.mem_union_left _ h))
      (fun h => hV0_farU0n (Finset.mem_union_right _ h))
      (fun h => hV1_farU0n (Finset.mem_union_left _ h))
      (fun h => hV1_farU0n (Finset.mem_union_right _ h))
      ha2_t_U0 ha3_t_U0 ha4_t_U0
      (by rw [map_sub, map_mul, MvPolynomial.eval_X] at ha1_u0a; exact ha1_u0a)

  have hfinalU0b : MvPolynomial.eval a4 (d.u2_num 0) -
      a4 U0 * MvPolynomial.eval a4 (d.u2_den 0) = 0 :=
    carry_eval_sub_mul_three
      ha2_off ha3_off ha4_off
      (fun h => hU1_farU0d (Finset.mem_union_left _ h))
      (fun h => hU1_farU0d (Finset.mem_union_right _ h))
      (fun h => hV0_farU0d (Finset.mem_union_left _ h))
      (fun h => hV0_farU0d (Finset.mem_union_right _ h))
      (fun h => hV1_farU0d (Finset.mem_union_left _ h))
      (fun h => hV1_farU0d (Finset.mem_union_right _ h))
      ha2_t_U0 ha3_t_U0 ha4_t_U0
      (by rw [map_sub, map_mul, MvPolynomial.eval_X] at ha1_u0b; exact ha1_u0b)

  obtain ⟨hV0_farU1n, hV1_farU1n, hV0_farU1d, hV1_farU1d, hV1_farV0n, hV1_farV0d⟩ :=
    theData_remaining_target_notmem p d


  have ha3_t_U1 : a3 U1 = a2 U1 := ha3_off U1 (by decide)
  have ha4_t_U1 : a4 U1 = a3 U1 := ha4_off U1 (by decide)

  have hfinalU1a : MvPolynomial.eval a4 (d.u1_num 1) -
      a4 U1 * MvPolynomial.eval a4 (d.u1_den 1) = 0 :=
    carry_eval_sub_mul_two
      ha3_off ha4_off
      (fun h => hV0_farU1n (Finset.mem_union_left _ h))
      (fun h => hV0_farU1n (Finset.mem_union_right _ h))
      (fun h => hV1_farU1n (Finset.mem_union_left _ h))
      (fun h => hV1_farU1n (Finset.mem_union_right _ h))
      ha3_t_U1 ha4_t_U1
      (by rw [map_sub, map_mul, MvPolynomial.eval_X] at ha2_u1a; exact ha2_u1a)

  have hfinalU1b : MvPolynomial.eval a4 (d.u2_num 1) -
      a4 U1 * MvPolynomial.eval a4 (d.u2_den 1) = 0 :=
    carry_eval_sub_mul_two
      ha3_off ha4_off
      (fun h => hV0_farU1d (Finset.mem_union_left _ h))
      (fun h => hV0_farU1d (Finset.mem_union_right _ h))
      (fun h => hV1_farU1d (Finset.mem_union_left _ h))
      (fun h => hV1_farU1d (Finset.mem_union_right _ h))
      ha3_t_U1 ha4_t_U1
      (by rw [map_sub, map_mul, MvPolynomial.eval_X] at ha2_u1b; exact ha2_u1b)

  have ha4_t_V0 : a4 V0 = a3 V0 := ha4_off V0 (by decide)

  have hfinalV0a : MvPolynomial.eval a4 (d.v1_num 0) -
      a4 V0 * MvPolynomial.eval a4 (d.v1_den 0) = 0 :=
    carry_eval_sub_mul_one ha4_off
      (fun h => hV1_farV0n (Finset.mem_union_left _ h))
      (fun h => hV1_farV0n (Finset.mem_union_right _ h))
      ha4_t_V0
      (by rw [map_sub, map_mul, MvPolynomial.eval_X] at ha3_v0a; exact ha3_v0a)

  have hfinalV0b : MvPolynomial.eval a4 (d.v2_num 0) -
      a4 V0 * MvPolynomial.eval a4 (d.v2_den 0) = 0 :=
    carry_eval_sub_mul_one ha4_off
      (fun h => hV1_farV0d (Finset.mem_union_left _ h))
      (fun h => hV1_farV0d (Finset.mem_union_right _ h))
      ha4_t_V0
      (by rw [map_sub, map_mul, MvPolynomial.eval_X] at ha3_v0b; exact ha3_v0b)

  -- The `V1` pair is already solved AT `a4` (the final assignment) — nothing
  -- to carry forward.
  have hfinalV1a : MvPolynomial.eval a4 (d.v1_num 1) -
      a4 V1 * MvPolynomial.eval a4 (d.v1_den 1) = 0 := by
    rw [map_sub, map_mul, MvPolynomial.eval_X] at ha4_v1a; exact ha4_v1a
  have hfinalV1b : MvPolynomial.eval a4 (d.v2_num 1) -
      a4 V1 * MvPolynomial.eval a4 (d.v2_den 1) = 0 := by
    rw [map_sub, map_mul, MvPolynomial.eval_X] at ha4_v1b; exact ha4_v1b
  refine ⟨a4, ?_⟩
  intro g hg
  simp only [genList, FuList, FvList, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hg
  rcases hg with ((h | h | h | h) | (h | h | h | h)) | (h | h | h | h)
  · rw [h, map_sub, map_mul]; simp only [U0']; rw [MvPolynomial.eval_X]; exact hfinalU0a
  · rw [h, map_sub, map_mul]; simp only [U0']; rw [MvPolynomial.eval_X]; exact hfinalU0b
  · rw [h, map_sub, map_mul]; simp only [U1']; rw [MvPolynomial.eval_X]; exact hfinalU1a
  · rw [h, map_sub, map_mul]; simp only [U1']; rw [MvPolynomial.eval_X]; exact hfinalU1b
  · rw [h, map_sub, map_mul]; simp only [V0']; rw [MvPolynomial.eval_X]; exact hfinalV0a
  · rw [h, map_sub, map_mul]; simp only [V0']; rw [MvPolynomial.eval_X]; exact hfinalV0b
  · rw [h, map_sub, map_mul]; simp only [V1']; rw [MvPolynomial.eval_X]; exact hfinalV1a
  · rw [h, map_sub, map_mul]; simp only [V1']; rw [MvPolynomial.eval_X]; exact hfinalV1b
  · rw [h]; exact hfinalA1
  · rw [h]; exact hfinalA2
  · rw [h]; exact hfinalB1
  · rw [h]; exact hfinalB2

/-- **The actual composition promised by this file's title.** Chains
`genList_exists_common_zero_of_curve_witness` above into
`Ideal.ofList_ne_top_of_forall_eval_eq_zero`
(`IdealOfListNeTopFromEval.lean`): the common zero `assign'` gives a ring
hom `MvPolynomial.eval assign' : Rdec p →+* F p` sending every generator
in `genList ...` to `0`, and `F p = ZMod p` is `Nontrivial` (it's a
field, `Fact (Nat.Prime p)` supplies `ZMod.instField`), so the ideal
those generators span is proper. This is `htop_ne_smul`'s curve-witness
form: everything genuinely `Genus2Lean`-specific is now assembled; only
the curve-side witness `assign` (existence of an actual point satisfying
(a)/(b)/(c), per this file's docstring) remains open, exactly as
disclosed above. -/
theorem ideal_ofList_genList_ne_top_of_curve_witness
    (c0 c1 c2 c3 c4 : F p) (sa sb : SampleTarget p)
    (hcurA : curBeforeMonic p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 ≠ 0)
    (hcurB : curBeforeMonic p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 ≠ 0)
    (hgcdA : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1)
      (uRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1))
    (hgcdB : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1)
      (uRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1))
    (assign : Idx → F p)
    (hcurveA1 : MvPolynomial.eval assign (curveA1 p c0 c1 c2 c3 c4) = 0)
    (hcurveA2 : MvPolynomial.eval assign (curveA2 p c0 c1 c2 c3 c4) = 0)
    (hcurveB1 : MvPolynomial.eval assign (curveB1 p c0 c1 c2 c3 c4) = 0)
    (hcurveB2 : MvPolynomial.eval assign (curveB2 p c0 c1 c2 c3 c4) = 0)
    (hu1d0 : MvPolynomial.eval assign
      ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_den 0) ≠ 0)
    (hu2d0 : MvPolynomial.eval assign
      ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_den 0) ≠ 0)
    (hu1d1 : MvPolynomial.eval assign
      ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_den 1) ≠ 0)
    (hu2d1 : MvPolynomial.eval assign
      ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_den 1) ≠ 0)
    (hv1d0 : MvPolynomial.eval assign
      ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_den 0) ≠ 0)
    (hv2d0 : MvPolynomial.eval assign
      ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_den 0) ≠ 0)
    (hv1d1 : MvPolynomial.eval assign
      ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_den 1) ≠ 0)
    (hv2d1 : MvPolynomial.eval assign
      ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_den 1) ≠ 0)
    (hresU0 : MvPolynomial.eval assign
        ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_num 0) *
      MvPolynomial.eval assign
        ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_den 0) =
      MvPolynomial.eval assign
        ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_num 0) *
      MvPolynomial.eval assign
        ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_den 0))
    (hresU1 : MvPolynomial.eval assign
        ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_num 1) *
      MvPolynomial.eval assign
        ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_den 1) =
      MvPolynomial.eval assign
        ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_num 1) *
      MvPolynomial.eval assign
        ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_den 1))
    (hresV0 : MvPolynomial.eval assign
        ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_num 0) *
      MvPolynomial.eval assign
        ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_den 0) =
      MvPolynomial.eval assign
        ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_num 0) *
      MvPolynomial.eval assign
        ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_den 0))
    (hresV1 : MvPolynomial.eval assign
        ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_num 1) *
      MvPolynomial.eval assign
        ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_den 1) =
      MvPolynomial.eval assign
        ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_num 1) *
      MvPolynomial.eval assign
        ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_den 1)) :
    Ideal.ofList (genList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB) ≠ (⊤ : Ideal (Rdec p)) := by
  obtain ⟨assign', hassign'⟩ :=
    genList_exists_common_zero_of_curve_witness p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB
      assign hcurveA1 hcurveA2 hcurveB1 hcurveB2
      hu1d0 hu2d0 hu1d1 hu2d1 hv1d0 hv2d0 hv1d1 hv2d1
      hresU0 hresU1 hresV0 hresV1
  exact Ideal.ofList_ne_top_of_forall_eval_eq_zero (MvPolynomial.eval assign')
    (genList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB) hassign'

end Genus2Lean
