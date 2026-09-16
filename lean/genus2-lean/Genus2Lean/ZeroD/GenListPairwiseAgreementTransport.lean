import Mathlib
import Genus2Lean.ZeroD.GenListPairwiseAgreementAssembly
import Genus2Lean.ZeroD.GenListTriangularReorder

/-!
# Transporting pairwise agreement from `genListTriangular` back to `genList`

`ROADMAP-monic-annihilator-degree-uniform.md`'s "Next concrete steps" item
2 built `genListTriangular_pairwise_eq_up_to_sign`, stated for a fully
generic `gens : List (Rdec p)` and only meaningful (as a fact about
`theData`'s actual twelve equations) once specialized to
`gens := genListTriangular ...`. That file's own docstring flags this
transport step as "not yet done"; this file does it.

**Why this is mechanical, not new content.** The pairwise-agreement
theorem never depended on `gens`'s order — it is a bare statement about
`A := Rdec p ⧸ Ideal.ofList gens` for whichever `gens` the caller
supplies (confirmed by direct inspection: `curveFImage`/`linearElimGen`
are evaluated against `Ideal.ofList gens` generically throughout
`PeelChainPairwiseAgreementCurveChain.lean`/`...LinearChain.lean`, with
no reference to `genList`'s or `genListTriangular`'s internal structure).
So specializing at `gens := genListTriangular p c0 c1 c2 c3 c4 sa sb hcurA
hcurB hgcdA hgcdB` already gives the fact for the RIGHT twelve equations,
just presented as a quotient by the reordered list.

**Design choice, revised this pass after a first attempt hit two real
errors: a missing `open TheDataDerivation` (`curBeforeMonic`/`Ypoly`/`uRS`
unresolved) and a `whnf` heartbeat timeout.** The timeout is a separate,
genuine problem from the missing `open` — independent of it, the first
draft's single theorem signature repeated the fully-applied term
`genList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB` 31 times and
`theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB` 21 times. This is
the same elaboration-cost pattern `dvd_N_u`'s own docstring
(`TheDataDerivation/DataDerivationSolve.lean`) already diagnosed and fixed
via `let`/`clear_value` for a proof BODY; here the cost is in the
SIGNATURE itself, before any tactic runs, so the fix has to be structural.
Follows `GenListFinrankFourStageTransport.lean`'s own documented design
choice instead ("this file takes the CONCLUSION as a hypothesis, not its
~200-line hypothesis list... re-typing it by hand here risks a
transcription mismatch invisible until Claire's REPL catches it").

**The fix below**: state the transported theorem generically over an
arbitrary `gens : List (Rdec p)` and `d : DecoupledGenerators p`, tied to
`genList`/`theData` via two `Eq` hypotheses (`hgens`, `hd`) rather than
inlining the applied terms throughout the statement — exactly mirroring
how `genListTriangular_pairwise_eq_up_to_sign` ITSELF already takes
`gens`/`d` generically (`GenListPairwiseAgreementAssembly.lean`). A caller
with concrete `gens := genList ...`/`d := theData ...` supplies `rfl` for
both `hgens`/`hd` at zero extra elaboration cost beyond what defining
`genList`/`theData` already paid.

**Rewrites the IDEAL equality (`Ideal.ofList_perm`), not the quotient-RING
equality (`quot_genListTriangular_eq_quot_genList`)** — matching the fix
`GenListFinrankFourStageTransport.lean`'s own docstring already records
for the identical transport problem one file over: an earlier attempt at
that file used the ring-type equality directly and hit "motive is not
type correct", since `IsDomain`/the ring structure on `A := Rdec p ⧸
Ideal.ofList gens` are derived from that TYPE — rewriting a bare `R ⧸ I₁ =
R ⧸ I₂` type equality underneath asks for a dependent motive `rw` can't
build. Rewriting `Ideal.ofList genList = Ideal.ofList genListTriangular`
(an equality of IDEALS) instead changes only the `Ideal.ofList _`
argument inside `Rdec p ⧸ _` as an ordinary subterm, so every instance is
rebuilt by `congrArg` through a genuine rewrite rather than transported
across an opaque type equality — no dependent-motive issue.

**What this file does NOT do**: discharge the `hdU0`/`hdU1`/`hdV0`/`hdV1`
`IsUnit`-denominator hypotheses (per the roadmap's "Corrections, this
pass" — these are genuine standing per-instance hypotheses, parallel to
`Nondegenerate`/`CrossNondegenerate`/`hd1_U0` in
`GenListFinrankResultantAssembly.lean`, not derivable from `hcurA/hcurB/
hgcdA/hgcdB` and not attempted here), and does NOT yet link `sa,sb` via
`SampleTargetFromAlpha` (roadmap item 3, separate and still open). Purely
the reordering step.

**Still NOT REPL-confirmed (third pass).** Round 1 hit a missing `open`
and a `whnf` timeout. Round 2's `set`-then-`rw [hIeq] at *` fix for the
timeout introduced a NEW type mismatch (`rw ... at *` produces a fresh
elaborated copy of the applied `genListTriangular ...` term at the goal
site, distinct from the one baked into `t1`'s type by that same rewrite)
and, per Claire's REPL, did not actually fix the timeout either (the
expensive step is the rewrite unifying against sixteen-plus independent
hypothesis sites, not the earlier `set`). Round 3 (this pass) replaces
both with `revert` (every `gens`/`d`-typed hypothesis, by name, including
the domain hypothesis — now explicit, see the theorem docstring's "API
note") + a single goal-only `generalize` + `intro`: reverting first
turns all those hypotheses into one goal, so `generalize` need only
abstract the applied term ONCE, out of the goal, and every reverted
premise inherits the same new opaque `gens'` automatically — no
per-hypothesis rewriting, sidestepping both the syntactic-mismatch risk
and the repeated-unification cost. Not yet run in Claire's REPL. Two
concrete risks to watch for if this fails: (1) the `revert` list must
name every hypothesis whose TYPE mentions the applied `genList`/`theData`
terms, in any order (Lean reverts dependencies automatically) — if a
`rw`/`generalize` "motive is not type correct" or "expression contains
metavariables" error appears, some hypothesis was missed; grep the
theorem signature for `gens`/`d` occurrences past `hgens`/`hd` and add it
to the revert list. (2) `haveI := hInst` after the final `intro` must
successfully hand `IsDomain (Rdec p ⧸ Ideal.ofList gens')` to instance
search for the closing `exact` call — if that call reports a missing
`IsDomain` instance, pass `hInst` positionally instead
(`genListTriangular_pairwise_eq_up_to_sign p gens' c0 c1 c2 c3 c4 d
(inst := hInst) ...` — check the exact named-argument syntax the target
theorem's instance-implicit accepts, since Lean's syntax for naming an
instance-implicit argument varies). -/

namespace Genus2Lean
namespace DecoupledSystem

open Idx
open TheDataDerivation

variable (p : ℕ) [Fact (Nat.Prime p)] [Fact (p ≠ 2)]

/-- **`genList`, pairwise agreement up to sign, in `genList`'s own literal
stated order.** Same conclusion as `genListTriangular_pairwise_eq_up_to_
sign`, transported via the ideal-equality rewrite `Ideal.ofList_perm
(genListTriangular_perm_genList ...)`, so the ambient ring in both the
hypotheses and the conclusion is `Rdec p ⧸ Ideal.ofList gens` for
`gens := genList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB` — the
presentation every other `genList`-facing theorem in this project
(`genList_finrank_le`, `decoupledSystem_zeroDimensional`, etc.) already
uses — rather than `genListTriangular`'s reordered one.

**Signature kept generic over `gens : List (Rdec p)` and
`d : DecoupledGenerators p`, tied to `genList`/`theData` via the two
`Eq` hypotheses `hgens`/`hd`** (see the module docstring's "Design
choice" section for why). A caller with concrete `gens := genList ...`/
`d := theData ...` supplies `rfl` for both.

**API note, this pass**: the domain hypothesis is now the EXPLICIT named
argument `hInst : IsDomain (Rdec p ⧸ Ideal.ofList gens)`, not an
instance-implicit `[IsDomain ...]` as in the first draft. Needed so the
proof can `revert`/`generalize`/`intro` it by name alongside the other
`gens`-typed hypotheses (see the proof's own comment for why). A caller
that previously relied on instance search finding this automatically
must now pass it positionally (or via `(hInst := ‹_›)`); this file has
no other callers yet, so no downstream break, but flagging since this
differs from every other `genList`-facing theorem's `[IsDomain ...]`
convention in this project. -/
theorem genList_pairwise_eq_up_to_sign
    (gens : List (Rdec p)) (c0 c1 c2 c3 c4 : F p) (d : DecoupledGenerators p)
    (sa sb : SampleTarget p)
    (hcurA : curBeforeMonic p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 ≠ 0)
    (hcurB : curBeforeMonic p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 ≠ 0)
    (hgcdA : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1)
      (uRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1))
    (hgcdB : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1)
      (uRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1))
    (hgens : gens = genList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB)
    (hd : d = theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB)
    (hInst : IsDomain (Rdec p ⧸ Ideal.ofList gens))
    (t1 t2 t3 t4 t1' t2' t3' t4' U0v U1v V0v V1v U0v' U1v' V0v' V1v' :
      Rdec p ⧸ Ideal.ofList gens)
    (ht1 : (Polynomial.aeval t1)
      (curveRelationPoly (curveFImage p gens c0 c1 c2 c3 c4 a1)) = 0)
    (ht1' : (Polynomial.aeval t1')
      (curveRelationPoly (curveFImage p gens c0 c1 c2 c3 c4 a1)) = 0)
    (ht2 : (Polynomial.aeval t2)
      (curveRelationPoly (curveFImage p gens c0 c1 c2 c3 c4 a2)) = 0)
    (ht2' : (Polynomial.aeval t2')
      (curveRelationPoly (curveFImage p gens c0 c1 c2 c3 c4 a2)) = 0)
    (ht3 : (Polynomial.aeval t3)
      (curveRelationPoly (curveFImage p gens c0 c1 c2 c3 c4 b1)) = 0)
    (ht3' : (Polynomial.aeval t3')
      (curveRelationPoly (curveFImage p gens c0 c1 c2 c3 c4 b1)) = 0)
    (ht4 : (Polynomial.aeval t4)
      (curveRelationPoly (curveFImage p gens c0 c1 c2 c3 c4 b2)) = 0)
    (ht4' : (Polynomial.aeval t4')
      (curveRelationPoly (curveFImage p gens c0 c1 c2 c3 c4 b2)) = 0)
    (hdU0 : IsUnit (Ideal.Quotient.mk (Ideal.ofList gens) (d.u1_den 0)))
    (hdU1 : IsUnit (Ideal.Quotient.mk (Ideal.ofList gens) (d.u1_den 1)))
    (hdV0 : IsUnit (Ideal.Quotient.mk (Ideal.ofList gens) (d.v1_den 0)))
    (hdV1 : IsUnit (Ideal.Quotient.mk (Ideal.ofList gens) (d.v1_den 1)))
    (htU0 : (Polynomial.aeval U0v) (linearElimPoly
      (Ideal.Quotient.mk (Ideal.ofList gens) (d.u1_num 0))
      (Ideal.Quotient.mk (Ideal.ofList gens) (d.u1_den 0))) = 0)
    (htU0' : (Polynomial.aeval U0v') (linearElimPoly
      (Ideal.Quotient.mk (Ideal.ofList gens) (d.u1_num 0))
      (Ideal.Quotient.mk (Ideal.ofList gens) (d.u1_den 0))) = 0)
    (htU1 : (Polynomial.aeval U1v) (linearElimPoly
      (Ideal.Quotient.mk (Ideal.ofList gens) (d.u1_num 1))
      (Ideal.Quotient.mk (Ideal.ofList gens) (d.u1_den 1))) = 0)
    (htU1' : (Polynomial.aeval U1v') (linearElimPoly
      (Ideal.Quotient.mk (Ideal.ofList gens) (d.u1_num 1))
      (Ideal.Quotient.mk (Ideal.ofList gens) (d.u1_den 1))) = 0)
    (htV0 : (Polynomial.aeval V0v) (linearElimPoly
      (Ideal.Quotient.mk (Ideal.ofList gens) (d.v1_num 0))
      (Ideal.Quotient.mk (Ideal.ofList gens) (d.v1_den 0))) = 0)
    (htV0' : (Polynomial.aeval V0v') (linearElimPoly
      (Ideal.Quotient.mk (Ideal.ofList gens) (d.v1_num 0))
      (Ideal.Quotient.mk (Ideal.ofList gens) (d.v1_den 0))) = 0)
    (htV1 : (Polynomial.aeval V1v) (linearElimPoly
      (Ideal.Quotient.mk (Ideal.ofList gens) (d.v1_num 1))
      (Ideal.Quotient.mk (Ideal.ofList gens) (d.v1_den 1))) = 0)
    (htV1' : (Polynomial.aeval V1v') (linearElimPoly
      (Ideal.Quotient.mk (Ideal.ofList gens) (d.v1_num 1))
      (Ideal.Quotient.mk (Ideal.ofList gens) (d.v1_den 1))) = 0) :
    ((t1 = t1' ∨ t1 = -t1') ∧ (t2 = t2' ∨ t2 = -t2') ∧
     (t3 = t3' ∨ t3 = -t3') ∧ (t4 = t4' ∨ t4 = -t4')) ∧
    (U0v = U0v' ∧ U1v = U1v' ∧ V0v = V0v' ∧ V1v = V1v') := by
  -- Once `gens`/`d` are known equal to `genList ...`/`theData ...`, the
  -- rest of the proof only ever needs the ideal-level identity
  -- `Ideal.ofList genList = Ideal.ofList genListTriangular` — never the
  -- full `genList`/`theData` definitions themselves — so `subst` these
  -- two equalities first and then work generically in `gens`/`d`,
  -- exactly the abstraction `genListTriangular_pairwise_eq_up_to_sign`
  -- itself already uses.
  subst hgens
  subst hd
  -- **Diagnosis after three REPL rounds — this is the actual root
  -- cause.** Round 1: missing `open` + heartbeat timeout on a giant
  -- unfolded signature. Round 2 (`set`+`rw ... at *`) and round 3
  -- (`revert`+`generalize`+`intro`) both tried to change the type
  -- `Rdec p ⧸ Ideal.ofList gens` in place, in the GOAL, by rewriting the
  -- ideal argument. Both hit "motive is not type correct": the goal
  -- contains `curveFImage p gens c0 c1 c2 c3 c4 a1`, a TERM (not just a
  -- type annotation) whose return type `Rdec p ⧸ Ideal.ofList gens`
  -- depends on `gens` — so abstracting `gens` (or the ideal built from
  -- it) inside the goal forces `rw`/`generalize` to build a motive
  -- across a dependent function application, which fails exactly the
  -- way `rw`'s own documentation warns about. This is the SAME failure
  -- `GenListFinrankFourStageTransport.lean`'s docstring already diagnosed
  -- for the ring-type-equality route (`quot_genListTriangular_eq_quot_
  -- genList`) — except here it bites even the IDEAL-equality route,
  -- because unlike that file's `Module.finrank (Rdec p ⧸ Ideal.ofList _)`
  -- (one clean occurrence per side), this goal has the ideal argument
  -- showing up ONE LAYER DOWN, inside `curveFImage`'s return type, at
  -- eight different call sites.
  --
  -- **The actual fix: don't rewrite the goal at all.** `Ideal.ofList
  -- genList = Ideal.ofList genListTriangular` means the two RINGS
  -- `Rdec p ⧸ Ideal.ofList genList` and `Rdec p ⧸ Ideal.ofList
  -- genListTriangular` are related by a genuine ring isomorphism,
  -- `Ideal.quotEquivOfEq hIeq : (Rdec p ⧸ Ideal.ofList genList) ≃+*
  -- (Rdec p ⧸ Ideal.ofList genListTriangular)`, together with the simp
  -- lemma `Ideal.quotEquivOfEq_mk : e ((Ideal.Quotient.mk I) x) =
  -- (Ideal.Quotient.mk J) x` for TRANSPORTING TERMS across it — exactly
  -- what's needed, since `curveFImage`/`Ideal.Quotient.mk (d.u1_den _)`
  -- etc. are all literally `Ideal.Quotient.mk (Ideal.ofList gens) (some
  -- gens-INDEPENDENT polynomial)`. So: map each of `t1,...,V1v'` across
  -- `e`, discharge the mapped hypotheses by `simp [e_mk]` (`e_mk` unfolds
  -- both the mapped element's `curveFImage`/`Ideal.Quotient.mk` shape and
  -- the original hypothesis to the SAME literal element of the
  -- `genListTriangular`-side ring, so the hypothesis transfers by
  -- `rfl`/`exact` after rewriting), invoke the target theorem, then map
  -- the conclusion's equalities BACK across `e.symm` (equivalences are
  -- injective, so `e x = e y → x = y` recovers each equality on the
  -- original elements).
  have hIeq : Ideal.ofList (genList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB) =
      Ideal.ofList (genListTriangular p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB) :=
    (Ideal.ofList_perm
      (genListTriangular_perm_genList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB)).symm
  set e := Ideal.quotEquivOfEq hIeq with he_def
  haveI := hInst
  haveI : IsDomain
      (Rdec p ⧸ Ideal.ofList (genListTriangular p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB)) :=
    e.symm.toMulEquiv.isDomain _
  -- **Per ChatGPT's diagnosis**: the earlier `rw [he_def]; simp only
  -- [Ideal.quotEquivOfEq_mk]` boilerplate was backwards — `hdU0` etc.
  -- are stated purely in terms of `Ideal.Quotient.mk (Ideal.ofList
  -- gens) _`, mentioning `e` nowhere, so `rw [he_def]` (which replaces
  -- `e` with its definition) had nothing to fire on. The actual
  -- transport needs `e` applied to the LHS (`e (Ideal.Quotient.mk
  -- (Ideal.ofList gens) x) = Ideal.Quotient.mk (Ideal.ofList
  -- genListTriangular) x`, `Ideal.quotEquivOfEq_mk`) used FORWARD via
  -- `congrArg e` on the original hypothesis, not a `rw` on the goal.
  -- `curveFImage`/`Ideal.Quotient.mk (d.u1_den _)`-style terms are all
  -- literally `Ideal.Quotient.mk (Ideal.ofList gens) (fixed
  -- gens-independent polynomial)`, so `Ideal.quotEquivOfEq_mk` fires by
  -- `simp` directly on `e (curveFImage ...)`/`e (Ideal.Quotient.mk ...)`
  -- once phrased that way.
  have hU0d : e (Ideal.Quotient.mk (Ideal.ofList (genList p c0 c1 c2 c3 c4 sa sb hcurA hcurB
      hgcdA hgcdB)) ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_den 0)) =
      Ideal.Quotient.mk (Ideal.ofList (genListTriangular p c0 c1 c2 c3 c4 sa sb hcurA hcurB
        hgcdA hgcdB)) ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_den 0) := by
    rw [he_def]; exact Ideal.quotEquivOfEq_mk hIeq _
  have hU1d : e (Ideal.Quotient.mk (Ideal.ofList (genList p c0 c1 c2 c3 c4 sa sb hcurA hcurB
      hgcdA hgcdB)) ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_den 1)) =
      Ideal.Quotient.mk (Ideal.ofList (genListTriangular p c0 c1 c2 c3 c4 sa sb hcurA hcurB
        hgcdA hgcdB)) ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_den 1) := by
    rw [he_def]; exact Ideal.quotEquivOfEq_mk hIeq _
  have hV0d : e (Ideal.Quotient.mk (Ideal.ofList (genList p c0 c1 c2 c3 c4 sa sb hcurA hcurB
      hgcdA hgcdB)) ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_den 0)) =
      Ideal.Quotient.mk (Ideal.ofList (genListTriangular p c0 c1 c2 c3 c4 sa sb hcurA hcurB
        hgcdA hgcdB)) ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_den 0) := by
    rw [he_def]; exact Ideal.quotEquivOfEq_mk hIeq _
  have hV1d : e (Ideal.Quotient.mk (Ideal.ofList (genList p c0 c1 c2 c3 c4 sa sb hcurA hcurB
      hgcdA hgcdB)) ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_den 1)) =
      Ideal.Quotient.mk (Ideal.ofList (genListTriangular p c0 c1 c2 c3 c4 sa sb hcurA hcurB
        hgcdA hgcdB)) ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_den 1) := by
    rw [he_def]; exact Ideal.quotEquivOfEq_mk hIeq _
  -- **The `IsUnit`-denominator hypotheses transport via `e`'s ring-hom
  -- structure**: `IsUnit x → IsUnit (e x)` is `IsUnit.map e.toRingHom`
  -- (any ring hom, let alone equiv, sends units to units), and `e x`
  -- literally equals the corresponding `genListTriangular`-side
  -- `Ideal.Quotient.mk` term via `hU0d`/etc. above, so `hU0d ▸
  -- (hdU0.map e.toRingHom)` gives exactly the hypothesis
  -- `genListTriangular_pairwise_eq_up_to_sign` wants.
  have hdU0' := hU0d ▸ (hdU0.map e.toMonoidHom)
  have hdU1' := hU1d ▸ (hdU1.map e.toMonoidHom)
  have hdV0' := hV0d ▸ (hdV0.map e.toMonoidHom)
  have hdV1' := hV1d ▸ (hdV1.map e.toMonoidHom)
  -- **The `aeval`-vanishing hypotheses (`ht1,...,htV1'`) transport via
  -- `Polynomial.eval_map` + a separate `Polynomial.map` identity**: once
  -- corrected against the actual Mathlib API (the earlier
  -- `Polynomial.eval_map_apply`/`Polynomial.coe_aeval_eq_eval` names in
  -- this docstring do not exist — `Polynomial.eval_map (f : R →+* S)
  -- (x : S) : Polynomial.eval x (Polynomial.map f p) = Polynomial.eval₂
  -- f x p` is the real lemma, together with `Polynomial.aeval_def` +
  -- `Polynomial.eval₂_eq_eval_map` to unfold `aeval` on the
  -- ring-acting-on-itself algebra down to plain `eval`), `congrArg
  -- e.toRingHom` applied to the unfolded `ht1` (etc.) transports through
  -- once the corresponding `Polynomial.map` identity (`curveRelationPoly`/
  -- `linearElimPoly` are both built from `X`/`C`/`-`/`*` alone, so
  -- `Polynomial.map` commutes with them via `simp`) is established as
  -- its own `have`. See the generic `aeval_transport` helper below, which
  -- packages this reasoning once and is reused at all 16 call sites.
  have hcurveA1 : Polynomial.map e.toRingHom
      (curveRelationPoly (curveFImage p (genList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB)
        c0 c1 c2 c3 c4 a1)) =
      curveRelationPoly (curveFImage p (genListTriangular p c0 c1 c2 c3 c4 sa sb hcurA hcurB
        hgcdA hgcdB) c0 c1 c2 c3 c4 a1) := by
    unfold curveRelationPoly curveFImage
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
    rw [he_def]
    congr 1
    all_goals exact Ideal.quotEquivOfEq_mk hIeq _
  have hcurveA2 : Polynomial.map e.toRingHom
      (curveRelationPoly (curveFImage p (genList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB)
        c0 c1 c2 c3 c4 a2)) =
      curveRelationPoly (curveFImage p (genListTriangular p c0 c1 c2 c3 c4 sa sb hcurA hcurB
        hgcdA hgcdB) c0 c1 c2 c3 c4 a2) := by
    unfold curveRelationPoly curveFImage
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
    rw [he_def]
    congr 1
    all_goals exact Ideal.quotEquivOfEq_mk hIeq _
  have hcurveB1 : Polynomial.map e.toRingHom
      (curveRelationPoly (curveFImage p (genList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB)
        c0 c1 c2 c3 c4 b1)) =
      curveRelationPoly (curveFImage p (genListTriangular p c0 c1 c2 c3 c4 sa sb hcurA hcurB
        hgcdA hgcdB) c0 c1 c2 c3 c4 b1) := by
    unfold curveRelationPoly curveFImage
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
    rw [he_def]
    congr 1
    all_goals exact Ideal.quotEquivOfEq_mk hIeq _
  have hcurveB2 : Polynomial.map e.toRingHom
      (curveRelationPoly (curveFImage p (genList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB)
        c0 c1 c2 c3 c4 b2)) =
      curveRelationPoly (curveFImage p (genListTriangular p c0 c1 c2 c3 c4 sa sb hcurA hcurB
        hgcdA hgcdB) c0 c1 c2 c3 c4 b2) := by
    unfold curveRelationPoly curveFImage
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
    rw [he_def]
    congr 1
    all_goals exact Ideal.quotEquivOfEq_mk hIeq _
  have hlinU0 : Polynomial.map e.toRingHom
      (linearElimPoly
        (Ideal.Quotient.mk (Ideal.ofList (genList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA
          hgcdB)) ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_num 0))
        (Ideal.Quotient.mk (Ideal.ofList (genList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA
          hgcdB)) ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_den 0))) =
      linearElimPoly
        (Ideal.Quotient.mk (Ideal.ofList (genListTriangular p c0 c1 c2 c3 c4 sa sb hcurA hcurB
          hgcdA hgcdB)) ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_num 0))
        (Ideal.Quotient.mk (Ideal.ofList (genListTriangular p c0 c1 c2 c3 c4 sa sb hcurA hcurB
          hgcdA hgcdB)) ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_den 0)) := by
    unfold linearElimPoly
    simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C]
    rw [he_def]
    congr 2 <;> exact Ideal.quotEquivOfEq_mk hIeq _
  have hlinU1 : Polynomial.map e.toRingHom
      (linearElimPoly
        (Ideal.Quotient.mk (Ideal.ofList (genList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA
          hgcdB)) ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_num 1))
        (Ideal.Quotient.mk (Ideal.ofList (genList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA
          hgcdB)) ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_den 1))) =
      linearElimPoly
        (Ideal.Quotient.mk (Ideal.ofList (genListTriangular p c0 c1 c2 c3 c4 sa sb hcurA hcurB
          hgcdA hgcdB)) ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_num 1))
        (Ideal.Quotient.mk (Ideal.ofList (genListTriangular p c0 c1 c2 c3 c4 sa sb hcurA hcurB
          hgcdA hgcdB)) ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_den 1)) := by
    unfold linearElimPoly
    simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C]
    rw [he_def]
    congr 2 <;> exact Ideal.quotEquivOfEq_mk hIeq _
  have hlinV0 : Polynomial.map e.toRingHom
      (linearElimPoly
        (Ideal.Quotient.mk (Ideal.ofList (genList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA
          hgcdB)) ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_num 0))
        (Ideal.Quotient.mk (Ideal.ofList (genList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA
          hgcdB)) ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_den 0))) =
      linearElimPoly
        (Ideal.Quotient.mk (Ideal.ofList (genListTriangular p c0 c1 c2 c3 c4 sa sb hcurA hcurB
          hgcdA hgcdB)) ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_num 0))
        (Ideal.Quotient.mk (Ideal.ofList (genListTriangular p c0 c1 c2 c3 c4 sa sb hcurA hcurB
          hgcdA hgcdB)) ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_den 0)) := by
    unfold linearElimPoly
    simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C]
    rw [he_def]
    congr 2 <;> exact Ideal.quotEquivOfEq_mk hIeq _
  have hlinV1 : Polynomial.map e.toRingHom
      (linearElimPoly
        (Ideal.Quotient.mk (Ideal.ofList (genList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA
          hgcdB)) ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_num 1))
        (Ideal.Quotient.mk (Ideal.ofList (genList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA
          hgcdB)) ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_den 1))) =
      linearElimPoly
        (Ideal.Quotient.mk (Ideal.ofList (genListTriangular p c0 c1 c2 c3 c4 sa sb hcurA hcurB
          hgcdA hgcdB)) ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_num 1))
        (Ideal.Quotient.mk (Ideal.ofList (genListTriangular p c0 c1 c2 c3 c4 sa sb hcurA hcurB
          hgcdA hgcdB)) ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_den 1)) := by
    unfold linearElimPoly
    simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C]
    rw [he_def]
    congr 2 <;> exact Ideal.quotEquivOfEq_mk hIeq _
  -- **The actual `aeval`-transport, one lemma reused 16 times.** For any
  -- `x` in the `genList`-side ring `A` and `P` a polynomial over `A` with
  -- `Polynomial.aeval x P = 0`, `Polynomial.aeval (e x) (Polynomial.map
  -- e.toRingHom P) = 0` — i.e. the transported element satisfies the
  -- transported polynomial. Proof: `Polynomial.map_aeval_eq_aeval_map`
  -- (found via Loogle, not guessed) is exactly the commuting-square
  -- lemma for this: for `φ : R →+* T`, `ψ : S →+* U` with `S` an
  -- `R`-algebra, `U` a `T`-algebra, and `(algebraMap T U).comp φ =
  -- ψ.comp (algebraMap R S)`, it gives `ψ (aeval a p) = aeval (ψ a)
  -- (map φ p)`. Specialize `R = S := A` (the `genList`-side ring, acting
  -- on itself), `T = U := B` (the `genListTriangular`-side ring, acting
  -- on itself), `φ = ψ := e.toRingHom`. The commuting-square hypothesis
  -- becomes `(algebraMap B B).comp e.toRingHom = e.toRingHom.comp
  -- (algebraMap A A)`, i.e. `RingHom.id B ∘ e.toRingHom = e.toRingHom ∘
  -- RingHom.id A` (both self-`algebraMap`s are `RingHom.id` by `rfl`,
  -- since `Algebra.id`'s `algebraMap` field is literally that ring hom)
  -- — `RingHom.ext fun _ => rfl` discharges it directly, no lemma name
  -- needed for the `RingHom.id` unfolding itself. This REPLACES the
  -- earlier ill-typed generic `transport` attempt AND the subsequent
  -- `simp`-based attempt that hit a `simp` recursion-depth blowup
  -- (`Polynomial.eval_map`/`Polynomial.eval₂_eq_eval_map` are mutual
  -- inverses, so handing both to one `simp` call let it loop rewriting
  -- back and forth instead of terminating) — using the single
  -- purpose-built commuting-square lemma avoids both failure modes.
  have aeval_transport : ∀ (x : Rdec p ⧸ Ideal.ofList (genList p c0 c1 c2 c3 c4 sa sb hcurA
      hcurB hgcdA hgcdB)) (P : Polynomial (Rdec p ⧸ Ideal.ofList
        (genList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB))),
      Polynomial.aeval x P = 0 →
      Polynomial.aeval (e x) (Polynomial.map e.toRingHom P) = 0 := by
    intro x P hP
    have hsq : (algebraMap
        (Rdec p ⧸ Ideal.ofList (genListTriangular p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA
          hgcdB)) (Rdec p ⧸ Ideal.ofList (genListTriangular p c0 c1 c2 c3 c4 sa sb hcurA hcurB
          hgcdA hgcdB))).comp e.toRingHom =
        e.toRingHom.comp (algebraMap
          (Rdec p ⧸ Ideal.ofList (genList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB))
          (Rdec p ⧸ Ideal.ofList (genList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB))) :=
      RingHom.ext fun a => rfl
    have := Polynomial.map_aeval_eq_aeval_map hsq P x
    rw [hP, map_zero] at this
    exact this.symm
  have ht1'' : Polynomial.aeval (e t1) (curveRelationPoly (curveFImage p
      (genListTriangular p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB) c0 c1 c2 c3 c4 a1)) = 0 := by
    rw [← hcurveA1]; exact aeval_transport t1 _ ht1
  have ht1''' : Polynomial.aeval (e t1') (curveRelationPoly (curveFImage p
      (genListTriangular p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB) c0 c1 c2 c3 c4 a1)) = 0 := by
    rw [← hcurveA1]; exact aeval_transport t1' _ ht1'
  have ht2'' : Polynomial.aeval (e t2) (curveRelationPoly (curveFImage p
      (genListTriangular p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB) c0 c1 c2 c3 c4 a2)) = 0 := by
    rw [← hcurveA2]; exact aeval_transport t2 _ ht2
  have ht2''' : Polynomial.aeval (e t2') (curveRelationPoly (curveFImage p
      (genListTriangular p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB) c0 c1 c2 c3 c4 a2)) = 0 := by
    rw [← hcurveA2]; exact aeval_transport t2' _ ht2'
  have ht3'' : Polynomial.aeval (e t3) (curveRelationPoly (curveFImage p
      (genListTriangular p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB) c0 c1 c2 c3 c4 b1)) = 0 := by
    rw [← hcurveB1]; exact aeval_transport t3 _ ht3
  have ht3''' : Polynomial.aeval (e t3') (curveRelationPoly (curveFImage p
      (genListTriangular p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB) c0 c1 c2 c3 c4 b1)) = 0 := by
    rw [← hcurveB1]; exact aeval_transport t3' _ ht3'
  have ht4'' : Polynomial.aeval (e t4) (curveRelationPoly (curveFImage p
      (genListTriangular p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB) c0 c1 c2 c3 c4 b2)) = 0 := by
    rw [← hcurveB2]; exact aeval_transport t4 _ ht4
  have ht4''' : Polynomial.aeval (e t4') (curveRelationPoly (curveFImage p
      (genListTriangular p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB) c0 c1 c2 c3 c4 b2)) = 0 := by
    rw [← hcurveB2]; exact aeval_transport t4' _ ht4'
  have htU0'' : Polynomial.aeval (e U0v) (linearElimPoly
      (Ideal.Quotient.mk (Ideal.ofList (genListTriangular p c0 c1 c2 c3 c4 sa sb hcurA hcurB
        hgcdA hgcdB)) ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_num 0))
      (Ideal.Quotient.mk (Ideal.ofList (genListTriangular p c0 c1 c2 c3 c4 sa sb hcurA hcurB
        hgcdA hgcdB)) ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_den 0))) = 0 := by
    rw [← hlinU0]; exact aeval_transport U0v _ htU0
  have htU0''' : Polynomial.aeval (e U0v') (linearElimPoly
      (Ideal.Quotient.mk (Ideal.ofList (genListTriangular p c0 c1 c2 c3 c4 sa sb hcurA hcurB
        hgcdA hgcdB)) ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_num 0))
      (Ideal.Quotient.mk (Ideal.ofList (genListTriangular p c0 c1 c2 c3 c4 sa sb hcurA hcurB
        hgcdA hgcdB)) ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_den 0))) = 0 := by
    rw [← hlinU0]; exact aeval_transport U0v' _ htU0'
  have htU1'' : Polynomial.aeval (e U1v) (linearElimPoly
      (Ideal.Quotient.mk (Ideal.ofList (genListTriangular p c0 c1 c2 c3 c4 sa sb hcurA hcurB
        hgcdA hgcdB)) ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_num 1))
      (Ideal.Quotient.mk (Ideal.ofList (genListTriangular p c0 c1 c2 c3 c4 sa sb hcurA hcurB
        hgcdA hgcdB)) ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_den 1))) = 0 := by
    rw [← hlinU1]; exact aeval_transport U1v _ htU1
  have htU1''' : Polynomial.aeval (e U1v') (linearElimPoly
      (Ideal.Quotient.mk (Ideal.ofList (genListTriangular p c0 c1 c2 c3 c4 sa sb hcurA hcurB
        hgcdA hgcdB)) ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_num 1))
      (Ideal.Quotient.mk (Ideal.ofList (genListTriangular p c0 c1 c2 c3 c4 sa sb hcurA hcurB
        hgcdA hgcdB)) ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_den 1))) = 0 := by
    rw [← hlinU1]; exact aeval_transport U1v' _ htU1'
  have htV0'' : Polynomial.aeval (e V0v) (linearElimPoly
      (Ideal.Quotient.mk (Ideal.ofList (genListTriangular p c0 c1 c2 c3 c4 sa sb hcurA hcurB
        hgcdA hgcdB)) ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_num 0))
      (Ideal.Quotient.mk (Ideal.ofList (genListTriangular p c0 c1 c2 c3 c4 sa sb hcurA hcurB
        hgcdA hgcdB)) ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_den 0))) = 0 := by
    rw [← hlinV0]; exact aeval_transport V0v _ htV0
  have htV0''' : Polynomial.aeval (e V0v') (linearElimPoly
      (Ideal.Quotient.mk (Ideal.ofList (genListTriangular p c0 c1 c2 c3 c4 sa sb hcurA hcurB
        hgcdA hgcdB)) ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_num 0))
      (Ideal.Quotient.mk (Ideal.ofList (genListTriangular p c0 c1 c2 c3 c4 sa sb hcurA hcurB
        hgcdA hgcdB)) ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_den 0))) = 0 := by
    rw [← hlinV0]; exact aeval_transport V0v' _ htV0'
  have htV1'' : Polynomial.aeval (e V1v) (linearElimPoly
      (Ideal.Quotient.mk (Ideal.ofList (genListTriangular p c0 c1 c2 c3 c4 sa sb hcurA hcurB
        hgcdA hgcdB)) ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_num 1))
      (Ideal.Quotient.mk (Ideal.ofList (genListTriangular p c0 c1 c2 c3 c4 sa sb hcurA hcurB
        hgcdA hgcdB)) ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_den 1))) = 0 := by
    rw [← hlinV1]; exact aeval_transport V1v _ htV1
  have htV1''' : Polynomial.aeval (e V1v') (linearElimPoly
      (Ideal.Quotient.mk (Ideal.ofList (genListTriangular p c0 c1 c2 c3 c4 sa sb hcurA hcurB
        hgcdA hgcdB)) ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_num 1))
      (Ideal.Quotient.mk (Ideal.ofList (genListTriangular p c0 c1 c2 c3 c4 sa sb hcurA hcurB
        hgcdA hgcdB)) ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_den 1))) = 0 := by
    rw [← hlinV1]; exact aeval_transport V1v' _ htV1'
  have key := genListTriangular_pairwise_eq_up_to_sign p
    (genListTriangular p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB)
    c0 c1 c2 c3 c4 (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB)
    (e t1) (e t2) (e t3) (e t4) (e t1') (e t2') (e t3') (e t4')
    (e U0v) (e U1v) (e V0v) (e V1v) (e U0v') (e U1v') (e V0v') (e V1v')
    ht1'' ht1''' ht2'' ht2''' ht3'' ht3''' ht4'' ht4'''
    hdU0' hdU1' hdV0' hdV1'
    htU0'' htU0''' htU1'' htU1''' htV0'' htV0''' htV1'' htV1'''
  obtain ⟨⟨k1, k2, k3, k4⟩, kU0, kU1, kV0, kV1⟩ := key
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rcases k1 with h | h
    · exact Or.inl (e.injective h)
    · exact Or.inr (e.injective (by rw [map_neg]; exact h))
  · rcases k2 with h | h
    · exact Or.inl (e.injective h)
    · exact Or.inr (e.injective (by rw [map_neg]; exact h))
  · rcases k3 with h | h
    · exact Or.inl (e.injective h)
    · exact Or.inr (e.injective (by rw [map_neg]; exact h))
  · rcases k4 with h | h
    · exact Or.inl (e.injective h)
    · exact Or.inr (e.injective (by rw [map_neg]; exact h))
  · exact e.injective kU0
  · exact e.injective kU1
  · exact e.injective kV0
  · exact e.injective kV1

end DecoupledSystem
end Genus2Lean
