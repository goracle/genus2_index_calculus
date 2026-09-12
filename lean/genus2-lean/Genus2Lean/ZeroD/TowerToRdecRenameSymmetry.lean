import Mathlib
import Genus2Lean.ZeroD.TheDataDerivation.DataDerivationMumford
import Genus2Lean.ZeroD.DecoupledSystemRegular

/-!
# `towerToRdec`'s rename-equivariance, and a free curve-witness case for Obligation 1

New this pass, toward `ROADMAP-degree-uniform-step3.md`'s Obligation 1
(`htop_ne_smul`). `ZeroD-README.md`'s own tracking (as of the last pass)
says the only thing standing between `GenListNeTopFromCurvePoint.lean`'s
`ideal_ofList_genList_ne_top_of_curve_witness` and an actual closed
`htop_ne_smul` is a concrete witness assignment: a point on all four curve
equations that ALSO makes `theData`'s 8 denominators nonzero and its 4
cross-resultants (`CrossNondegenerate`'s own `hu0`/`hu1`/`hv0`/`hv1`
elements) vanish there.

**The observation this file formalizes**: the cross-resultant condition is
not a generic curve-specific fact to search for — it is FREE whenever the
two samples `sa`/`sb` are equal and the witness assignment mirrors the
a-side variables onto the b-side ones. `theData`'s `u1_num`/`u1_den` (resp.
`u2_num`/`u2_den`) are built by `coeffsToNumDen`/`towerToRdec` applied to
the SAME `uRS`/`vRS` polynomial (a `K2 p c0...c4`-valued element depending
only on `sa`/`sb`'s own target data, per `DataDerivationMumford.lean`'s
`K0`/`K1`/`K2` definitions, which never mention `Vars`/`SideGens` at all)
with only the `SideGens` parameter differing (`aSideGens` vs `bSideGens`).
Since `aSideGens`/`bSideGens` differ only by which four `Idx` names get
used (`{a1,a2,wa1,wa2}` vs `{b1,b2,wb1,wb2}`), and the `Idx` swap pairing
those up (`a1↔b1`, `a2↔b2`, `wa1↔wb1`, `wa2↔wb2`, fixing `U0,U1,V0,V1`) is
a genuine involutive bijection, `towerToRdec p bSideGens v` is *literally*
`towerToRdec p aSideGens v` with its variables renamed along that swap —
`§1` below proves this in general, for any two `SideGens` related by a
bijection intertwining their `tGen`/`wGen` maps, not just this specific
pair. `§2` specializes to `idxSwap`/`aSideGens`/`bSideGens`. `§3` draws the
corollary in full generality (any `poly`/slot `i`, not just `uRS`/`0` as in
an earlier pass): if `sa = sb` and the witness assignment itself is
symmetric under `idxSwap` (i.e. assigns the same value to `wa1`/`wb1`,
`a1`/`b1`, etc.), the cross-resultant vanishes automatically, no curve
computation needed — reducing Obligation 1's remaining gap to finding a
symmetric witness point on `curveA1`/`curveA2` alone (`curveB1`/`curveB2`
then hold for free, being `curveA1`/`curveA2` with variables renamed along
the same swap that fixes the assignment). `§3` closes with the four named
corollaries matching `CrossNondegenerate`'s own `hu0`/`hu1`/`hv0`/`hv1`
fields exactly (`uRS`/slot-0, `uRS`/slot-1, `vRS`/slot-0, `vRS`/slot-1) —
all four slots, not only `U0`, since the general lemma makes the other
three free.

**What this file does NOT do**: exhibit the actual curve-side witness
(a genuine `(a1,a2,wa1,wa2)` satisfying `curveA1`/`curveA2`, plus the 8
denominator-nonvanishing side conditions) — that is `§3`'s own remaining
hypothesis, `hsym`/`hcurve`, left as explicit input. Constructing it (does
a symmetric point always exist? for which `p`/`(c0,...,c4)`?) is future
work, using this file's reduction as the target to hit rather than the
full asymmetric cross-resultant story. This file also does not address
the general `sa ≠ sb` case (the substitute-and-reduce test the roadmap
describes) — the result here is the special-case `sa = sb`, symmetric-
`assign` shortcut only.

**Not yet REPL-confirmed** -- drafted this pass; Claire tests via the REPL.
-/

namespace Genus2Lean
namespace TheDataDerivation

open MvPolynomial

variable (p : ℕ) [hp : Fact (Nat.Prime p)] [hp2 : Fact (p ≠ 2)]

section RenameEquivariance

variable {c0 c1 c2 c3 c4 : F p}

/-! ## §1. General rename-equivariance of `towerToRdec`

The recursion (`baseFracToRing` → `towerToRdecK1` → `towerToRdec`) only
ever reads `sg` through `sg.tGen`/`sg.wGen`'s VALUES, substituted via
`MvPolynomial.X` and combined with `+`/`*`. Composing with
`MvPolynomial.rename ρ` afterwards, for `ρ` intertwining two `SideGens`
records (`ρ ∘ sgA.tGen = sgB.tGen`, `ρ ∘ sgA.wGen = sgB.wGen`), commutes
past every step of the recursion — this is the general fact; no
injectivity of `ρ` is needed anywhere in the proof (only used later, in
§2, to get `idxSwap`'s own involutivity for the corollary). -/

/-- **Base case.** `rename ρ` commutes with `baseFracToRing`'s
`aeval (X ∘ sg.tGen)` substitution, turning `sgA`'s substitution into
`sgB`'s, via `MvPolynomial.aeval_rename` (`aeval g (rename k p) =
aeval (g ∘ k) p`) applied with `k := ρ`, `g := X ∘ sgB.tGen` -- the
composite `g ∘ ρ` unfolds to `X ∘ (ρ ∘ sgA.tGen) = X ∘ sgB.tGen`'s
witnessing equality `htGen`, then back to `X ∘ sgA.tGen` via `hρ`. -/
theorem baseFracToRing_rename {Vars Vars' : Type*} [DecidableEq Vars']
    (sgA : SideGens Vars) (sgB : SideGens Vars') (ρ : Vars → Vars')
    (htGen : ∀ i, ρ (sgA.tGen i) = sgB.tGen i) (w : K0 p) :
    (MvPolynomial.rename ρ (baseFracToRing p sgA w).1,
      MvPolynomial.rename ρ (baseFracToRing p sgA w).2) = baseFracToRing p sgB w := by
  unfold baseFracToRing
  dsimp only
  have key : ∀ q : MvPolynomial (Fin 2) (F p),
      MvPolynomial.rename ρ
        (MvPolynomial.aeval (R := F p) (S₁ := MvPolynomial Vars (F p))
          (fun i : Fin 2 => MvPolynomial.X (sgA.tGen i)) q) =
        MvPolynomial.aeval (R := F p) (S₁ := MvPolynomial Vars' (F p))
          (fun i : Fin 2 => MvPolynomial.X (sgB.tGen i)) q := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C a =>
      simp only [MvPolynomial.aeval_C]
      exact AlgHom.commutes (MvPolynomial.rename ρ) a
    | add q₁ q₂ hq₁ hq₂ => simp only [map_add, hq₁, hq₂]
    | mul_X r i hr => simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.rename_X, hr, htGen i]
  have hnum : MvPolynomial.rename ρ
      (MvPolynomial.aeval (R := F p) (S₁ := MvPolynomial Vars (F p))
        (fun i : Fin 2 => MvPolynomial.X (sgA.tGen i))
        (IsFractionRing.num (MvPolynomial (Fin 2) (F p)) w)) =
      MvPolynomial.aeval (R := F p) (S₁ := MvPolynomial Vars' (F p))
        (fun i : Fin 2 => MvPolynomial.X (sgB.tGen i))
        (IsFractionRing.num (MvPolynomial (Fin 2) (F p)) w) :=
    key _
  have hden : MvPolynomial.rename ρ
      (MvPolynomial.aeval (R := F p) (S₁ := MvPolynomial Vars (F p))
        (fun i : Fin 2 => MvPolynomial.X (sgA.tGen i))
        (↑(IsFractionRing.den (MvPolynomial (Fin 2) (F p)) w) :
          MvPolynomial (Fin 2) (F p))) =
      MvPolynomial.aeval (R := F p) (S₁ := MvPolynomial Vars' (F p))
        (fun i : Fin 2 => MvPolynomial.X (sgB.tGen i))
        (↑(IsFractionRing.den (MvPolynomial (Fin 2) (F p)) w) :
          MvPolynomial (Fin 2) (F p)) :=
    key _
  rw [Prod.mk.injEq]
  exact ⟨hnum, hden⟩

/-- **`K1` step.** `rename ρ` commutes with `towerToRdecK1` the same way,
additionally needing `ρ`'s action on `wGen 0` (`hwGen 0`) to turn the
extra `X (sgA.wGen 0)` factor `towerToRdecK1` multiplies in into
`X (sgB.wGen 0)`. -/
theorem towerToRdecK1_rename {Vars Vars' : Type*} [DecidableEq Vars']
    (sgA : SideGens Vars) (sgB : SideGens Vars') (ρ : Vars → Vars')
    (htGen : ∀ i, ρ (sgA.tGen i) = sgB.tGen i)
    (hwGen : ∀ i, ρ (sgA.wGen i) = sgB.wGen i)
    (v : K1 p c0 c1 c2 c3 c4) :
    (MvPolynomial.rename ρ (towerToRdecK1 p sgA v).1,
      MvPolynomial.rename ρ (towerToRdecK1 p sgA v).2) = towerToRdecK1 p sgB v := by
  unfold towerToRdecK1
  dsimp only
  set d0 := (AdjoinRoot.modByMonicHom (K1_poly_monic p c0 c1 c2 c3 c4) v).coeff 0
  set d1 := (AdjoinRoot.modByMonicHom (K1_poly_monic p c0 c1 c2 c3 c4) v).coeff 1
  have h0 := baseFracToRing_rename p sgA sgB ρ htGen d0
  have h1 := baseFracToRing_rename p sgA sgB ρ htGen d1
  rw [Prod.mk.injEq] at h0 h1
  rw [Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · simp only [map_add, map_mul, MvPolynomial.rename_X]
    rw [h0.1, h1.1, h0.2, h1.2, hwGen 0]
  · simp only [map_mul]
    rw [h0.2, h1.2]


set_option maxHeartbeats 2000000 in
-- the K2-level rename-equivariance proof chains two `baseFracToRing_rename`
-- instances through `towerToRdecK1_rename`'s unfolding; the extra layer of
-- `dsimp`/`simp`/`rw` pushes past the default heartbeat budget.
/-- **`K2` step -- the headline fact.** `rename ρ` commutes with
`towerToRdec` itself, given `ρ` intertwines `sgA`/`sgB`'s `tGen`/`wGen`
maps entirely (all four components, matching `SideGens`' two fields).
Same shape one level up, via `wGen 1` instead of `wGen 0`. -/
theorem towerToRdec_rename {Vars Vars' : Type*} [DecidableEq Vars']
    (sgA : SideGens Vars) (sgB : SideGens Vars') (ρ : Vars → Vars')
    (htGen : ∀ i, ρ (sgA.tGen i) = sgB.tGen i)
    (hwGen : ∀ i, ρ (sgA.wGen i) = sgB.wGen i)
    (v : K2 p c0 c1 c2 c3 c4) :
    (MvPolynomial.rename ρ (towerToRdec p sgA v).1,
      MvPolynomial.rename ρ (towerToRdec p sgA v).2) = towerToRdec p sgB v := by
  unfold towerToRdec
  dsimp only
  set d0 := (AdjoinRoot.modByMonicHom (K2_poly_monic p c0 c1 c2 c3 c4) v).coeff 0
  set d1 := (AdjoinRoot.modByMonicHom (K2_poly_monic p c0 c1 c2 c3 c4) v).coeff 1
  have h0 := towerToRdecK1_rename p sgA sgB ρ htGen hwGen d0
  have h1 := towerToRdecK1_rename p sgA sgB ρ htGen hwGen d1
  rw [Prod.mk.injEq] at h0 h1
  rw [Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · simp only [map_add, map_mul, MvPolynomial.rename_X]
    rw [h0.1, h1.1, h0.2, h1.2, hwGen 1]
  · simp only [map_mul]
    rw [h0.2, h1.2]

end RenameEquivariance

end TheDataDerivation

namespace DecoupledSystem

open TheDataDerivation
open Idx
open MvPolynomial

/-! ## §2. Specializing to `idxSwap`/`aSideGens`/`bSideGens`

`idxSwap` pairs the a-side and b-side variables (`a1↔b1`, `a2↔b2`,
`wa1↔wb1`, `wa2↔wb2`), fixing every other `Idx` (`U0,U1,V0,V1`) -- an
involution, built as a transposition product rather than a bare
pattern-matched function so `Function.Involutive`/injectivity are cheap
`decide`/`Equiv.Perm`-style facts rather than a 12-case `rfl` chase. -/

/-- The `Idx` swap pairing a-side and b-side variables, fixing the four
target variables. Built via `Equiv.swap` composed three times (once per
matched pair) rather than a direct `match`, so involutivity/injectivity
come from `Equiv.swap`'s own API instead of a by-hand 12-way case split. -/
noncomputable def idxSwapEquiv : Equiv.Perm Idx :=
  (Equiv.swap Idx.a1 Idx.b1).trans ((Equiv.swap Idx.a2 Idx.b2).trans
    ((Equiv.swap Idx.wa1 Idx.wb1).trans (Equiv.swap Idx.wa2 Idx.wb2)))

noncomputable abbrev idxSwap : Idx → Idx := idxSwapEquiv

-- **Proof note for Claire's REPL, all four of `idxSwap_a1`/`_a2`/`_wa1`/`_wa2`
-- below**: `idxSwapEquiv` unfolds to a `Equiv.trans` chain of three
-- `Equiv.swap`s; evaluating it at each of the 8 named constructors is, in
-- principle, decidable outright (`Idx` has `DecidableEq`/`Fintype`), so
-- `decide` is tried first as the most robust route (no lemma-name risk at
-- all), with the `simp [idxSwap, idxSwapEquiv, Equiv.swap_apply_def]`
-- unfold-and-compute route (using `Equiv.swap_apply_def`'s `if`-chain
-- characterization directly rather than `_apply_left`/`_of_ne_of_ne`,
-- which need per-call side-condition proofs threaded through three nested
-- `.trans`es) kept as the documented fallback if `decide` times out on
-- `Equiv.Perm`'s `noncomputable`/classical machinery.
theorem idxSwap_a1 : idxSwap a1 = b1 := by
  first
  | decide
  | simp [idxSwap, idxSwapEquiv, Equiv.swap_apply_def]

theorem idxSwap_a2 : idxSwap a2 = b2 := by
  first
  | decide
  | simp [idxSwap, idxSwapEquiv, Equiv.swap_apply_def]

theorem idxSwap_wa1 : idxSwap wa1 = wb1 := by
  first
  | decide
  | simp [idxSwap, idxSwapEquiv, Equiv.swap_apply_def]

theorem idxSwap_wa2 : idxSwap wa2 = wb2 := by
  first
  | decide
  | simp [idxSwap, idxSwapEquiv, Equiv.swap_apply_def]

/-- `idxSwap` sends `aSideGens.tGen`/`.wGen` to `bSideGens.tGen`/`.wGen`
pointwise -- exactly the `htGen`/`hwGen` hypotheses
`towerToRdec_rename` needs, instantiated at this specific pair. -/
theorem idxSwap_aSideGens_tGen (i : Fin 2) :
    idxSwap (aSideGens.tGen i) = bSideGens.tGen i := by
  fin_cases i
  · exact idxSwap_a1
  · exact idxSwap_a2

theorem idxSwap_aSideGens_wGen (i : Fin 2) :
    idxSwap (aSideGens.wGen i) = bSideGens.wGen i := by
  fin_cases i
  · exact idxSwap_wa1
  · exact idxSwap_wa2

/-- **The specialized rename fact.** For any `v : K2 p c0...c4`,
`towerToRdec p bSideGens v` is `towerToRdec p aSideGens v` with `idxSwap`
applied to both components. -/
theorem towerToRdec_bSideGens_eq_rename_idxSwap (p : ℕ) [Fact (Nat.Prime p)]
    [Fact (p ≠ 2)] {c0 c1 c2 c3 c4 : F p} (v : K2 p c0 c1 c2 c3 c4) :
    towerToRdec p bSideGens v =
      (MvPolynomial.rename idxSwap (towerToRdec p aSideGens v).1,
        MvPolynomial.rename idxSwap (towerToRdec p aSideGens v).2) :=
  (towerToRdec_rename p aSideGens bSideGens idxSwap
    idxSwap_aSideGens_tGen idxSwap_aSideGens_wGen v).symm

/-! ## §3. The free cross-resultant corollary

If `sa = sb =: s` (same target on both samples), `uRS p c0...c4 s.u0 ...`
is literally the same `K2`-element fed to both `towerToRdec p aSideGens`
and `towerToRdec p bSideGens` -- so `theData`'s `u2_num i`/`u2_den i` are
`idxSwap`-renamings of `u1_num i`/`u1_den i` (same fact for `v1_*`/`v2_*`
via `vRS`). Evaluating a renamed polynomial at an assignment `assign` is
the same as evaluating the original at `assign ∘ idxSwap`
(`MvPolynomial.eval_rename`-style fact, proved inline below since it is
one line from `aeval_rename` at `g := eval assign`). If `assign` is
`idxSwap`-symmetric (`assign ∘ idxSwap = assign` -- i.e. `assign` gives
the a-side and b-side variables matching values), this makes
`eval assign (u2_num i) = eval assign (u1_num i)` and likewise for the
denominator, so the cross-resultant `u1_num*u2_den - u2_num*u1_den`
vanishes at `assign` for a content-free reason: both terms of the
subtraction become the same product. -/

variable (p : ℕ) [Fact (Nat.Prime p)] [Fact (p ≠ 2)]

/-- Evaluating an `idxSwap`-renamed polynomial at `assign` equals
evaluating the original at `assign ∘ idxSwap`. **Proof note for Claire's
REPL**: `MvPolynomial.eval assign` and `MvPolynomial.aeval assign` (into
`F p` itself, via the canonical `Algebra (F p) (F p)` instance) are
equal as ring homs, so this should follow from `MvPolynomial.aeval_rename`
(`aeval g (rename k p) = aeval (g ∘ k) p`) at `g := assign`, `k := idxSwap`,
modulo unfolding `eval`/`aeval`'s definitional relationship -- attempted
here via `MvPolynomial.eval_eq_eval₂Hom`/`aeval_def`-style unfolding
first, with `simp [MvPolynomial.eval, MvPolynomial.aeval_def,
MvPolynomial.eval₂Hom_eq_bind₂, MvPolynomial.aeval_rename]` as the
documented fallback if the primary route doesn't close it outright --
flagging explicitly rather than asserting a specific lemma name with
false confidence, per this project's "don't guess an API shape from
memory" rule. -/
theorem eval_rename_idxSwap (assign : Idx → F p) (q : Rdec p) :
    MvPolynomial.eval assign (MvPolynomial.rename idxSwap q) =
      MvPolynomial.eval (assign ∘ idxSwap) q :=
  MvPolynomial.eval_rename idxSwap assign q

/- **The headline corollary.** Given a single target `s` used for BOTH
samples, and an `idxSwap`-symmetric assignment (`assign ∘ idxSwap =
assign`), the `U0`-slot cross-resultant vanishes at `assign`
automatically -- no curve-specific computation, purely from the
`aSideGens`/`bSideGens` symmetry. Stated for the `u`-side, slot `0`; the
`U1`/`V0`/`V1` slots and the `v`-side are identical, swapping
`uRS`/`towerToRdec_bSideGens_eq_rename_idxSwap`'s instance or the index
`i` as appropriate -- not restated four more times here since each is a
verbatim copy of this proof at a different `theData` field, per this
project's own "don't repeat a proof shape, name it once" convention
(flagged as the immediate next step once this one instance is
REPL-confirmed, rather than pre-multiplying a possible mistake by four). -/
/-- **The general shape, factored out.** Same statement as
`cross_resultant_u_slot0_eq_zero_of_symmetric` below, but for an
arbitrary `poly : Polynomial (K2 p c0 c1 c2 c3 c4)` and an arbitrary
slot `i : Fin 2` — nothing downstream of `set poly`/`set v` in that
proof actually used `uRS` or `i = 0` specifically, so this is the
literal generalization, proved once. Instantiating `poly := uRS ...`
or `poly := vRS ...` and `i := 0` or `i := 1` gives all four of
`CrossNondegenerate`'s named slots (`U0,U1,V0,V1`) as one-line
corollaries below — this is the infrastructure the roadmap's "next
step (i), generalize to the remaining three slots" asked for. -/
theorem cross_resultant_slot_eq_zero_of_symmetric
    (c0 c1 c2 c3 c4 : F p) (poly : Polynomial (K2 p c0 c1 c2 c3 c4))
    (i : Fin 2) (assign : Idx → F p) (hsym : assign ∘ idxSwap = assign) :
    MvPolynomial.eval assign (coeffsToNumDen p c0 c1 c2 c3 c4 aSideGens poly i).1 *
      MvPolynomial.eval assign (coeffsToNumDen p c0 c1 c2 c3 c4 bSideGens poly i).2 =
      MvPolynomial.eval assign (coeffsToNumDen p c0 c1 c2 c3 c4 bSideGens poly i).1 *
      MvPolynomial.eval assign (coeffsToNumDen p c0 c1 c2 c3 c4 aSideGens poly i).2 := by
  set v := poly.coeff i.val with hv
  have hb : towerToRdec p bSideGens v =
      (MvPolynomial.rename idxSwap (towerToRdec p aSideGens v).1,
        MvPolynomial.rename idxSwap (towerToRdec p aSideGens v).2) :=
    towerToRdec_bSideGens_eq_rename_idxSwap p v
  have hnum2 : (coeffsToNumDen p c0 c1 c2 c3 c4 bSideGens poly i).1 =
      MvPolynomial.rename idxSwap (coeffsToNumDen p c0 c1 c2 c3 c4 aSideGens poly i).1 := by
    unfold coeffsToNumDen
    rw [← hv, hb]
  have hden2 : (coeffsToNumDen p c0 c1 c2 c3 c4 bSideGens poly i).2 =
      MvPolynomial.rename idxSwap (coeffsToNumDen p c0 c1 c2 c3 c4 aSideGens poly i).2 := by
    unfold coeffsToNumDen
    rw [← hv, hb]
  rw [hnum2, hden2, eval_rename_idxSwap, eval_rename_idxSwap, hsym]

/-- **`U0`'s instance** (`poly := uRS ..., i := 0`) — matches
`CrossNondegenerate.hu0`'s own `u1_num 0`/`u2_num 0`/`u1_den 0`/
`u2_den 0` shape exactly, evaluated at `assign` rather than asserted
`IsSMulRegular`; see this file's docstring for the gap between the two. -/
theorem cross_resultant_u0_eq_zero_of_symmetric
    (c0 c1 c2 c3 c4 : F p) (s : SampleTarget p)
    (assign : Idx → F p) (hsym : assign ∘ idxSwap = assign) :
    MvPolynomial.eval assign
        (coeffsToNumDen p c0 c1 c2 c3 c4 aSideGens
          (uRS p c0 c1 c2 c3 c4 s.u0 s.u1 s.v0 s.v1) 0).1 *
      MvPolynomial.eval assign
        (coeffsToNumDen p c0 c1 c2 c3 c4 bSideGens
          (uRS p c0 c1 c2 c3 c4 s.u0 s.u1 s.v0 s.v1) 0).2 =
      MvPolynomial.eval assign
        (coeffsToNumDen p c0 c1 c2 c3 c4 bSideGens
          (uRS p c0 c1 c2 c3 c4 s.u0 s.u1 s.v0 s.v1) 0).1 *
      MvPolynomial.eval assign
        (coeffsToNumDen p c0 c1 c2 c3 c4 aSideGens
          (uRS p c0 c1 c2 c3 c4 s.u0 s.u1 s.v0 s.v1) 0).2 :=
  cross_resultant_slot_eq_zero_of_symmetric p c0 c1 c2 c3 c4
    (uRS p c0 c1 c2 c3 c4 s.u0 s.u1 s.v0 s.v1) 0 assign hsym

/-- **`U1`'s instance** (`poly := uRS ..., i := 1`), matching
`CrossNondegenerate.hu1`. -/
theorem cross_resultant_u1_eq_zero_of_symmetric
    (c0 c1 c2 c3 c4 : F p) (s : SampleTarget p)
    (assign : Idx → F p) (hsym : assign ∘ idxSwap = assign) :
    MvPolynomial.eval assign
        (coeffsToNumDen p c0 c1 c2 c3 c4 aSideGens
          (uRS p c0 c1 c2 c3 c4 s.u0 s.u1 s.v0 s.v1) 1).1 *
      MvPolynomial.eval assign
        (coeffsToNumDen p c0 c1 c2 c3 c4 bSideGens
          (uRS p c0 c1 c2 c3 c4 s.u0 s.u1 s.v0 s.v1) 1).2 =
      MvPolynomial.eval assign
        (coeffsToNumDen p c0 c1 c2 c3 c4 bSideGens
          (uRS p c0 c1 c2 c3 c4 s.u0 s.u1 s.v0 s.v1) 1).1 *
      MvPolynomial.eval assign
        (coeffsToNumDen p c0 c1 c2 c3 c4 aSideGens
          (uRS p c0 c1 c2 c3 c4 s.u0 s.u1 s.v0 s.v1) 1).2 :=
  cross_resultant_slot_eq_zero_of_symmetric p c0 c1 c2 c3 c4
    (uRS p c0 c1 c2 c3 c4 s.u0 s.u1 s.v0 s.v1) 1 assign hsym

/-- **`V0`'s instance** (`poly := vRS ..., i := 0`), matching
`CrossNondegenerate.hv0`. Takes the same `hgcd` coprimality hypothesis
`vRS` itself needs to be well-defined (see `DecoupledSystemRegular.lean`'s
`theData`) — `vRS` is only ever a value once that side condition holds,
same as everywhere else it's used in this project. -/
theorem cross_resultant_v0_eq_zero_of_symmetric
    (c0 c1 c2 c3 c4 : F p) (s : SampleTarget p)
    (hgcd : IsCoprime (Ypoly p c0 c1 c2 c3 c4 s.u0 s.u1 s.v0 s.v1)
      (uRS p c0 c1 c2 c3 c4 s.u0 s.u1 s.v0 s.v1))
    (assign : Idx → F p) (hsym : assign ∘ idxSwap = assign) :
    MvPolynomial.eval assign
        (coeffsToNumDen p c0 c1 c2 c3 c4 aSideGens
          (vRS p c0 c1 c2 c3 c4 s.u0 s.u1 s.v0 s.v1 hgcd) 0).1 *
      MvPolynomial.eval assign
        (coeffsToNumDen p c0 c1 c2 c3 c4 bSideGens
          (vRS p c0 c1 c2 c3 c4 s.u0 s.u1 s.v0 s.v1 hgcd) 0).2 =
      MvPolynomial.eval assign
        (coeffsToNumDen p c0 c1 c2 c3 c4 bSideGens
          (vRS p c0 c1 c2 c3 c4 s.u0 s.u1 s.v0 s.v1 hgcd) 0).1 *
      MvPolynomial.eval assign
        (coeffsToNumDen p c0 c1 c2 c3 c4 aSideGens
          (vRS p c0 c1 c2 c3 c4 s.u0 s.u1 s.v0 s.v1 hgcd) 0).2 :=
  cross_resultant_slot_eq_zero_of_symmetric p c0 c1 c2 c3 c4
    (vRS p c0 c1 c2 c3 c4 s.u0 s.u1 s.v0 s.v1 hgcd) 0 assign hsym

/-- **`V1`'s instance** (`poly := vRS ..., i := 1`), matching
`CrossNondegenerate.hv1`. -/
theorem cross_resultant_v1_eq_zero_of_symmetric
    (c0 c1 c2 c3 c4 : F p) (s : SampleTarget p)
    (hgcd : IsCoprime (Ypoly p c0 c1 c2 c3 c4 s.u0 s.u1 s.v0 s.v1)
      (uRS p c0 c1 c2 c3 c4 s.u0 s.u1 s.v0 s.v1))
    (assign : Idx → F p) (hsym : assign ∘ idxSwap = assign) :
    MvPolynomial.eval assign
        (coeffsToNumDen p c0 c1 c2 c3 c4 aSideGens
          (vRS p c0 c1 c2 c3 c4 s.u0 s.u1 s.v0 s.v1 hgcd) 1).1 *
      MvPolynomial.eval assign
        (coeffsToNumDen p c0 c1 c2 c3 c4 bSideGens
          (vRS p c0 c1 c2 c3 c4 s.u0 s.u1 s.v0 s.v1 hgcd) 1).2 =
      MvPolynomial.eval assign
        (coeffsToNumDen p c0 c1 c2 c3 c4 bSideGens
          (vRS p c0 c1 c2 c3 c4 s.u0 s.u1 s.v0 s.v1 hgcd) 1).1 *
      MvPolynomial.eval assign
        (coeffsToNumDen p c0 c1 c2 c3 c4 aSideGens
          (vRS p c0 c1 c2 c3 c4 s.u0 s.u1 s.v0 s.v1 hgcd) 1).2 :=
  cross_resultant_slot_eq_zero_of_symmetric p c0 c1 c2 c3 c4
    (vRS p c0 c1 c2 c3 c4 s.u0 s.u1 s.v0 s.v1 hgcd) 1 assign hsym

end DecoupledSystem
end Genus2Lean
