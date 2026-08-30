import Mathlib
import Genus2Lean.ZeroD.AlphaLocusDegreeUniform
import Genus2Lean.ZeroD.Reduce.GeneralSharedRoot

/-!
# `isReductionOutputOf`'s first real instance

`ROADMAP-alpha-to-degree-uniform.md` Part A asked for a real witness
that `SampleTargetFromAlpha.isReduction` need not be an unconstrained
`Prop` — some concrete sample really does come out of running `Reduce`.
Tracing the roadmaps this pass (`ROADMAP-reduce-divisor-correctness.md`
Step 1/§16 in particular) to see what `isReduction'`/`isReductionOf`
were FOR concluded they don't fit that job directly: `isReduction'`
(`AlphaLocusDegreeUniform.lean`) is a self-referential FIXED-POINT
condition (it feeds `sa`'s own coordinates back into
`ReduceDispatchGeneral` as input and demands the output equal them),
designed instead as the value that should eventually instantiate
`SampleTargetFromAlpha.isReduction`'s field once a real reduction
pipeline exists — and `reducedClass_eq_of_isReduction'`
(`ReducedClassBundles.lean`, proved, green) never actually unfolds its
`hr : isReduction' ...` hypothesis in its own proof body (confirmed by
direct inspection): `d : SplitAssemblyData sa` already supplies the
Cantor-reduction witnessing data structurally, so `hr` is a real but
currently-inert non-vacuity obligation on that theorem's caller, not
something this file should force a witness for.

**Design decision, this pass (Claire's direction):** rather than patch
`isReduction'` into a bigger monolith, quarantine it and
`reducedClass_eq_of_isReduction'` entirely — untouched, still available
to invoke end-to-end later if/when needed — and build a NEW, narrower,
self-contained predicate `isReductionOutputOf` here instead. It says
only "`sa`'s coordinates equal `ReduceDispatchGeneral`'s output on some
given input data", no self-reference, no connection yet to
`reducedClass`/the divisor class `sa` represents. `mk_sampleTargetFromAlpha_
of_reduceDispatch` builds such a sample directly from
`ReduceDispatchGeneral`'s own output, so `isReductionOutputOf` is
discharged by the output tuple's own `rfl` — genuinely immediate, no
fixed point, no idempotence gap.

Per the roadmap: this does NOT touch `Reduce`'s correctness (whether
`ReduceDispatchGeneral`'s output really is the Mumford reduction of
`alpha • aClass - ([P1]+[P2]-2•[δ₀])` in the divisor-class sense) — that
gap remains `reducedClass_eq_of_isReduction'`'s territory, untouched.
-/

open Polynomial
open Genus2Lean.DecoupledSystem
open Genus2Lean.TheDataDerivation hiding F

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (p ≠ 2)]
variable {H : HyperellipticPolynomial (F p)} {D : HyperellipticPolynomial.PrincipalDivisorData H}

/-- **`SampleTargetFromAlpha` built directly from `ReduceDispatchGeneral`'s
output.** Given curve coefficients `c0..c4`, two points `P1 P2 : H.Point`,
a scalar `alpha : ℤ`, an anchor class `aClass`, a basepoint `δ₀`, an
already-reduced anchor Mumford pair `ua0 ua1 va0 va1` (gap 1 from
`AlphaLocusDegreeUniform.lean`'s own docstring — supplied by the caller,
not derived here), and `ReduceDispatchGeneral`'s four case-split
hypotheses, produces a `SampleTargetFromAlpha` whose `.toSampleTarget` is
literally `ReduceDispatchGeneral`'s output. Pairs with
`isReductionOutputOf` (further below) rather than `isReduction'`/
`isReductionOf` — see this file's module docstring for why.

**Split into two `have`s to keep elaboration/`whnf` costs down**
(the single-theorem version timed out at `whnf` even on the bare
signature, per REPL testing — this project's convention for a
heartbeats-related failure is to unroll first, not just raise the
limit): `mk_sampleTargetFromAlpha_of_reduceDispatch` builds the
`SampleTargetFromAlpha` value alone (no proof obligation in scope yet,
so nothing forces `whnf` on `ReduceDispatchGeneral`'s `if`-branch just
to elaborate the goal); the equation lemmas below (`toSampleTarget_...`/
`alpha_P1_P2_...`) extract its fields via `unseal`, and
`isReductionOutputOf_of_fields_eq` (further below) proves
`isReductionOutputOf` for an ABSTRACT sample target, called at this
def's own output only as a plain opaque argument — never re-mentioning
`mk_sampleTargetFromAlpha_of_reduceDispatch` applied to arguments in any
later theorem STATEMENT, which is what actually triggers the `whnf`
blowup (`isReductionOutputOf` is a plain `def`, not marked
`@[reducible]`, but the same discipline is kept here regardless since
it's cheap insurance and matches the existing `irreducible`-plus-`unseal`
pattern below). -/
noncomputable def mk_sampleTargetFromAlpha_of_reduceDispatch
    (aClass : HyperellipticPolynomial.Jacobian H D) (δ₀ : H.Point)
    (alpha : ℤ) (P1 P2 : H.Point)
    (c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (hcur : (P1.X, P1.Y) ≠ (P2.X, P2.Y) →
      curBeforeMonic4General p c0 c1 c2 c3 c4 (P1.X, P1.Y) (P2.X, P2.Y)
        ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hgcd : (P1.X, P1.Y) ≠ (P2.X, P2.Y) →
      IsCoprime (Ypoly4 p (P1.X, P1.Y) (P2.X, P2.Y) ua0 ua1 va0 va1 u0 u1 v0 v1)
        (uRS4General p c0 c1 c2 c3 c4 (P1.X, P1.Y) (P2.X, P2.Y)
          ua0 ua1 va0 va1 u0 u1 v0 v1))
    (hcurT : (P1.X, P1.Y) = (P2.X, P2.Y) →
      curBeforeMonic4Tangent p c0 c1 c2 c3 c4 P1.X P1.Y
        ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hgcdT : (P1.X, P1.Y) = (P2.X, P2.Y) →
      IsCoprime (Ypoly4Tangent p c0 c1 c2 c3 c4 P1.X P1.Y
          ua0 ua1 va0 va1 u0 u1 v0 v1)
        (uRS4Tangent p c0 c1 c2 c3 c4 P1.X P1.Y
          ua0 ua1 va0 va1 u0 u1 v0 v1)) :
    SampleTargetFromAlpha p H D aClass δ₀ :=
  let out := ReduceDispatchGeneral p c0 c1 c2 c3 c4 (P1.X, P1.Y) (P2.X, P2.Y)
    ua0 ua1 va0 va1 u0 u1 v0 v1 hcur hgcd hcurT hgcdT
  { toSampleTarget := ⟨out.1, out.2.1, out.2.2.1, out.2.2.2⟩
    alpha := alpha
    P1 := P1
    P2 := P2
    isReduction := True }

-- Marked `irreducible` so nothing that mentions
-- `mk_sampleTargetFromAlpha_of_reduceDispatch` applied to arguments,
-- without wanting to actually LOOK INSIDE it, ever triggers `whnf` to
-- unfold this definition just to elaborate a TYPE that mentions it —
-- per REPL testing, that unfolding forces `ReduceDispatchGeneral`'s `if
-- hP : P1 = P2 then ... else ...` to resolve `Decidable (P1 = P2)` over
-- `H.Point`, which times out. The `unseal`-scoped equation lemmas below
-- are the only place that peers inside it; everything else (including
-- `isReductionOutputOf_of_fields_eq` further down) is stated generically
-- and only ever receives this def's OUTPUT as an opaque local variable
-- (via `generalize`), never as the applied term itself.
attribute [irreducible] mk_sampleTargetFromAlpha_of_reduceDispatch

unseal mk_sampleTargetFromAlpha_of_reduceDispatch in
/-- Companion `unseal`ed equation for `mk_sampleTargetFromAlpha_of_reduceDispatch` —
the single place its body is actually inspected, so the `irreducible` attribute
above never gets bypassed accidentally elsewhere. -/
theorem toSampleTarget_mk_sampleTargetFromAlpha_of_reduceDispatch
    (aClass : HyperellipticPolynomial.Jacobian H D) (δ₀ : H.Point)
    (alpha : ℤ) (P1 P2 : H.Point)
    (c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (hcur : (P1.X, P1.Y) ≠ (P2.X, P2.Y) →
      curBeforeMonic4General p c0 c1 c2 c3 c4 (P1.X, P1.Y) (P2.X, P2.Y)
        ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hgcd : (P1.X, P1.Y) ≠ (P2.X, P2.Y) →
      IsCoprime (Ypoly4 p (P1.X, P1.Y) (P2.X, P2.Y) ua0 ua1 va0 va1 u0 u1 v0 v1)
        (uRS4General p c0 c1 c2 c3 c4 (P1.X, P1.Y) (P2.X, P2.Y)
          ua0 ua1 va0 va1 u0 u1 v0 v1))
    (hcurT : (P1.X, P1.Y) = (P2.X, P2.Y) →
      curBeforeMonic4Tangent p c0 c1 c2 c3 c4 P1.X P1.Y
        ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hgcdT : (P1.X, P1.Y) = (P2.X, P2.Y) →
      IsCoprime (Ypoly4Tangent p c0 c1 c2 c3 c4 P1.X P1.Y
          ua0 ua1 va0 va1 u0 u1 v0 v1)
        (uRS4Tangent p c0 c1 c2 c3 c4 P1.X P1.Y
          ua0 ua1 va0 va1 u0 u1 v0 v1)) :
    (mk_sampleTargetFromAlpha_of_reduceDispatch
        aClass δ₀ alpha P1 P2 c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1
        hcur hgcd hcurT hgcdT).toSampleTarget.u0 = (ReduceDispatchGeneral p c0 c1 c2 c3 c4
        (P1.X, P1.Y) (P2.X, P2.Y) ua0 ua1 va0 va1 u0 u1 v0 v1 hcur hgcd hcurT hgcdT).1
    ∧ (mk_sampleTargetFromAlpha_of_reduceDispatch
        aClass δ₀ alpha P1 P2 c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1
        hcur hgcd hcurT hgcdT).toSampleTarget.u1 = (ReduceDispatchGeneral p c0 c1 c2 c3 c4
        (P1.X, P1.Y) (P2.X, P2.Y) ua0 ua1 va0 va1 u0 u1 v0 v1 hcur hgcd hcurT hgcdT).2.1
    ∧ (mk_sampleTargetFromAlpha_of_reduceDispatch
        aClass δ₀ alpha P1 P2 c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1
        hcur hgcd hcurT hgcdT).toSampleTarget.v0 = (ReduceDispatchGeneral p c0 c1 c2 c3 c4
        (P1.X, P1.Y) (P2.X, P2.Y) ua0 ua1 va0 va1 u0 u1 v0 v1 hcur hgcd hcurT hgcdT).2.2.1
    ∧ (mk_sampleTargetFromAlpha_of_reduceDispatch
        aClass δ₀ alpha P1 P2 c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1
        hcur hgcd hcurT hgcdT).toSampleTarget.v1 = (ReduceDispatchGeneral p c0 c1 c2 c3 c4
        (P1.X, P1.Y) (P2.X, P2.Y) ua0 ua1 va0 va1 u0 u1 v0 v1 hcur hgcd hcurT hgcdT).2.2.2 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

unseal mk_sampleTargetFromAlpha_of_reduceDispatch in
/-- Companion `unseal`ed equations for `mk_sampleTargetFromAlpha_of_reduceDispatch`'s
`alpha`/`P1`/`P2` fields — needed because `irreducible` also blocks the
`rfl`s these would otherwise be. Declared BEFORE
`exists_sampleTargetFromAlpha_of_reduceDispatch` since that theorem calls
this one (moved here to fix a forward-reference — this file had it
declared after its first use, which does not compile). -/
theorem alpha_P1_P2_mk_sampleTargetFromAlpha_of_reduceDispatch
    (aClass : HyperellipticPolynomial.Jacobian H D) (δ₀ : H.Point)
    (alpha : ℤ) (P1 P2 : H.Point)
    (c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (hcur : (P1.X, P1.Y) ≠ (P2.X, P2.Y) →
      curBeforeMonic4General p c0 c1 c2 c3 c4 (P1.X, P1.Y) (P2.X, P2.Y)
        ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hgcd : (P1.X, P1.Y) ≠ (P2.X, P2.Y) →
      IsCoprime (Ypoly4 p (P1.X, P1.Y) (P2.X, P2.Y) ua0 ua1 va0 va1 u0 u1 v0 v1)
        (uRS4General p c0 c1 c2 c3 c4 (P1.X, P1.Y) (P2.X, P2.Y)
          ua0 ua1 va0 va1 u0 u1 v0 v1))
    (hcurT : (P1.X, P1.Y) = (P2.X, P2.Y) →
      curBeforeMonic4Tangent p c0 c1 c2 c3 c4 P1.X P1.Y
        ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hgcdT : (P1.X, P1.Y) = (P2.X, P2.Y) →
      IsCoprime (Ypoly4Tangent p c0 c1 c2 c3 c4 P1.X P1.Y
          ua0 ua1 va0 va1 u0 u1 v0 v1)
        (uRS4Tangent p c0 c1 c2 c3 c4 P1.X P1.Y
          ua0 ua1 va0 va1 u0 u1 v0 v1)) :
    (mk_sampleTargetFromAlpha_of_reduceDispatch
        aClass δ₀ alpha P1 P2 c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1
        hcur hgcd hcurT hgcdT).alpha = alpha
    ∧ (mk_sampleTargetFromAlpha_of_reduceDispatch
        aClass δ₀ alpha P1 P2 c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1
        hcur hgcd hcurT hgcdT).P1 = P1
    ∧ (mk_sampleTargetFromAlpha_of_reduceDispatch
        aClass δ₀ alpha P1 P2 c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1
        hcur hgcd hcurT hgcdT).P2 = P2 := by
  exact ⟨rfl, rfl, rfl⟩

-- ============================================================
-- **Quarantine boundary, this pass.** `isReduction'`/`isReductionOf`
-- (`AlphaLocusDegreeUniform.lean`) and `reducedClass_eq_of_isReduction'`
-- (`ReducedClassBundles.lean`, proved, REPL-confirmed green, consumed by
-- `reducedClassDispatch`) are NOT touched here and are not the target of
-- the theorem below. Tracing the roadmaps (`ROADMAP-reduce-divisor-
-- correctness.md` Step 1/§16, `ROADMAP-alpha-to-degree-uniform.md`) this
-- pass surfaced why: `isReduction'` was designed as the value that
-- SHOULD instantiate `SampleTargetFromAlpha.isReduction`'s field
-- (Step 1's own words: "any future `isReduction : Prop` argument/field
-- should be instantiated with this existential"), while
-- `reducedClass_eq_of_isReduction'`'s `hr : isReduction' ...` hypothesis
-- is, by direct inspection of its ~270-line proof body, never once
-- unfolded — `d : SplitAssemblyData sa` already supplies the Cantor-
-- reduction witnessing data (`as_S`/`as_v`/root membership/coprimality)
-- structurally, so the proof never needs to open `hr` to get at that
-- content. `hr` is a genuine, currently-inert non-vacuity obligation on
-- the CALLER (confirming `sa` really is such a reduction, not merely
-- data shaped like one) — real, but a SEPARATE concern from what this
-- file is actually trying to establish, and not something to force a
-- witness for here. Per Claire's direction this pass: keep that whole
-- theorem quarantined/untouched, and build a new, narrower, self-
-- contained predicate below rather than growing `isReduction'` into a
-- bigger monolith. If `reducedClass_eq_of_isReduction'` is ever invoked
-- end-to-end, `hr` becomes that caller's own separate proof obligation.
--
-- **What this file proves instead.** Claire's framing: the target
-- equation is shaped `Reduce(something) = Reduce(something else)`
-- (`P1+P2-alpha•a` vs. its counterpart), and as long as `Reduce` is a
-- well-defined TOTAL operation on `F p`-coordinate data, it doesn't yet
-- matter what the specific coordinates are. So the actually-needed fact
-- at this stage is existential and non-self-referential: "for any curve/
-- point/anchor data satisfying `ReduceDispatchGeneral`'s own case-split
-- hypotheses, there is a real `SampleTargetFromAlpha` whose coordinates
-- ARE that call's output" — i.e. reduction can genuinely be carried out
-- and packaged as a `SampleTargetFromAlpha`, full stop. No fixed point,
-- no connection to `reducedClass` yet.
-- ============================================================

/-- **`isReductionOutputOf`**: `sa`'s Mumford coordinates are literally
`ReduceDispatchGeneral`'s output on some given (caller-supplied) input
data `c0..c4, ua0 ua1 va0 va1, u0 u1 v0 v1` and case-split hypotheses —
NOT `sa`'s own coordinates fed back into themselves (contrast
`isReduction'`, which self-feeds `sa.toSampleTarget`'s fields as the
`u0 u1 v0 v1` argument and is a fixed-point condition; see the
quarantine note above). This is deliberately a NEW, separate, narrower
predicate rather than a patch to `isReduction'` — the point raised this
pass is to keep this existence fact modular rather than growing the
existing monolith. Says nothing yet about `reducedClass`/the divisor
class `sa` is supposed to represent; that connection is
`reducedClass_eq_of_isReduction'`'s job, untouched here. -/
def isReductionOutputOf {p : ℕ} [Fact (Nat.Prime p)] [Fact (p ≠ 2)]
    {H : HyperellipticPolynomial (F p)} {D : HyperellipticPolynomial.PrincipalDivisorData H}
    {aClass : HyperellipticPolynomial.Jacobian H D} {δ₀ : H.Point}
    (sa : SampleTargetFromAlpha p H D aClass δ₀) : Prop :=
  ∃ (c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (hcur : (sa.P1.X, sa.P1.Y) ≠ (sa.P2.X, sa.P2.Y) →
      curBeforeMonic4General p c0 c1 c2 c3 c4
        (sa.P1.X, sa.P1.Y) (sa.P2.X, sa.P2.Y) ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hgcd : (sa.P1.X, sa.P1.Y) ≠ (sa.P2.X, sa.P2.Y) →
      IsCoprime (Ypoly4 p (sa.P1.X, sa.P1.Y) (sa.P2.X, sa.P2.Y) ua0 ua1 va0 va1 u0 u1 v0 v1)
        (uRS4General p c0 c1 c2 c3 c4
          (sa.P1.X, sa.P1.Y) (sa.P2.X, sa.P2.Y) ua0 ua1 va0 va1 u0 u1 v0 v1))
    (hcurT : (sa.P1.X, sa.P1.Y) = (sa.P2.X, sa.P2.Y) →
      curBeforeMonic4Tangent p c0 c1 c2 c3 c4 sa.P1.X sa.P1.Y ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hgcdT : (sa.P1.X, sa.P1.Y) = (sa.P2.X, sa.P2.Y) →
      IsCoprime (Ypoly4Tangent p c0 c1 c2 c3 c4 sa.P1.X sa.P1.Y ua0 ua1 va0 va1 u0 u1 v0 v1)
        (uRS4Tangent p c0 c1 c2 c3 c4 sa.P1.X sa.P1.Y ua0 ua1 va0 va1 u0 u1 v0 v1)),
    (sa.toSampleTarget.u0, sa.toSampleTarget.u1, sa.toSampleTarget.v0, sa.toSampleTarget.v1) =
      ReduceDispatchGeneral p c0 c1 c2 c3 c4 (sa.P1.X, sa.P1.Y) (sa.P2.X, sa.P2.Y)
        ua0 ua1 va0 va1 u0 u1 v0 v1 hcur hgcd hcurT hgcdT

-- **Marked `irreducible`, this pass, after a build failure.** A theorem
-- STATEMENT mentioning `isReductionOutputOf sa` for an abstract `sa`
-- (e.g. `isReductionOutputOf_of_fields_eq`'s conclusion below) timed out
-- at `whnf` on the bare header — the existential's own body nests four
-- higher-order hypothesis binders, each itself invoking
-- `ReduceDispatchGeneral`'s full case-split signature, and elaborating
-- that shape is expensive regardless of whether `sa` is concrete or
-- abstract. `irreducible` stops `whnf` from unfolding
-- `isReductionOutputOf` just to elaborate a goal/statement that merely
-- mentions it; `unseal ... in` (below, at the one equation lemma that
-- actually needs to look inside it) is the sanctioned exception, mirroring
-- `mk_sampleTargetFromAlpha_of_reduceDispatch`'s own existing pattern.
attribute [irreducible] isReductionOutputOf

unseal isReductionOutputOf in
/-- **`isReductionOutputOf`'s introduction rule**, `unseal`ed since
`irreducible` (above) blocks the anonymous-constructor `exact ⟨...⟩` this
would otherwise reduce to directly. The only place in this file that
looks inside `isReductionOutputOf`'s definition. -/
theorem isReductionOutputOf_intro {p : ℕ} [Fact (Nat.Prime p)] [Fact (p ≠ 2)]
    {H : HyperellipticPolynomial (F p)} {D : HyperellipticPolynomial.PrincipalDivisorData H}
    {aClass : HyperellipticPolynomial.Jacobian H D} {δ₀ : H.Point}
    (sa : SampleTargetFromAlpha p H D aClass δ₀)
    (c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (hcur : (sa.P1.X, sa.P1.Y) ≠ (sa.P2.X, sa.P2.Y) →
      curBeforeMonic4General p c0 c1 c2 c3 c4
        (sa.P1.X, sa.P1.Y) (sa.P2.X, sa.P2.Y) ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hgcd : (sa.P1.X, sa.P1.Y) ≠ (sa.P2.X, sa.P2.Y) →
      IsCoprime (Ypoly4 p (sa.P1.X, sa.P1.Y) (sa.P2.X, sa.P2.Y) ua0 ua1 va0 va1 u0 u1 v0 v1)
        (uRS4General p c0 c1 c2 c3 c4
          (sa.P1.X, sa.P1.Y) (sa.P2.X, sa.P2.Y) ua0 ua1 va0 va1 u0 u1 v0 v1))
    (hcurT : (sa.P1.X, sa.P1.Y) = (sa.P2.X, sa.P2.Y) →
      curBeforeMonic4Tangent p c0 c1 c2 c3 c4 sa.P1.X sa.P1.Y ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hgcdT : (sa.P1.X, sa.P1.Y) = (sa.P2.X, sa.P2.Y) →
      IsCoprime (Ypoly4Tangent p c0 c1 c2 c3 c4 sa.P1.X sa.P1.Y ua0 ua1 va0 va1 u0 u1 v0 v1)
        (uRS4Tangent p c0 c1 c2 c3 c4 sa.P1.X sa.P1.Y ua0 ua1 va0 va1 u0 u1 v0 v1))
    (heq : (sa.toSampleTarget.u0, sa.toSampleTarget.u1, sa.toSampleTarget.v0, sa.toSampleTarget.v1) =
      ReduceDispatchGeneral p c0 c1 c2 c3 c4 (sa.P1.X, sa.P1.Y) (sa.P2.X, sa.P2.Y)
        ua0 ua1 va0 va1 u0 u1 v0 v1 hcur hgcd hcurT hgcdT) :
    isReductionOutputOf sa :=
  ⟨c0, c1, c2, c3, c4, ua0, ua1, va0, va1, u0, u1, v0, v1, hcur, hgcd, hcurT, hgcdT, heq⟩

unseal isReductionOutputOf in
/-- **General form, no `mk_sampleTargetFromAlpha_of_reduceDispatch`
mentioned anywhere in the statement.** Same `subst`-not-`rw` discipline
as the file's earlier draft (see git history / chat log for the
`rewrite ... motive is not type correct` failure this avoids): `P1'
P2' u0' u1' v0' v1'` are free local variables, so `subst`ing them
against `sa`'s own fields removes any need to rewrite under a goal that
depends on them dependently. Unlike the old `isReductionOf_of_fields_eq`,
this needs NO extra fixed-point hypothesis — `isReductionOutputOf`'s
existential is precisely "`sa`'s coordinates equal SOME call's output",
which `e0 e1 e2 e3` directly witness once substituted, with no
self-reference to discharge. -/
theorem isReductionOutputOf_of_fields_eq
    {aClass : HyperellipticPolynomial.Jacobian H D} {δ₀ : H.Point}
    (sa : SampleTargetFromAlpha p H D aClass δ₀)
    (P1' P2' : H.Point) (c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0' u1' v0' v1' : F p)
    (uIn0 uIn1 vIn0 vIn1 : F p)
    (hcur : (P1'.X, P1'.Y) ≠ (P2'.X, P2'.Y) →
      curBeforeMonic4General p c0 c1 c2 c3 c4 (P1'.X, P1'.Y) (P2'.X, P2'.Y)
        ua0 ua1 va0 va1 uIn0 uIn1 vIn0 vIn1 ≠ 0)
    (hgcd : (P1'.X, P1'.Y) ≠ (P2'.X, P2'.Y) →
      IsCoprime (Ypoly4 p (P1'.X, P1'.Y) (P2'.X, P2'.Y) ua0 ua1 va0 va1 uIn0 uIn1 vIn0 vIn1)
        (uRS4General p c0 c1 c2 c3 c4 (P1'.X, P1'.Y) (P2'.X, P2'.Y)
          ua0 ua1 va0 va1 uIn0 uIn1 vIn0 vIn1))
    (hcurT : (P1'.X, P1'.Y) = (P2'.X, P2'.Y) →
      curBeforeMonic4Tangent p c0 c1 c2 c3 c4 P1'.X P1'.Y
        ua0 ua1 va0 va1 uIn0 uIn1 vIn0 vIn1 ≠ 0)
    (hgcdT : (P1'.X, P1'.Y) = (P2'.X, P2'.Y) →
      IsCoprime (Ypoly4Tangent p c0 c1 c2 c3 c4 P1'.X P1'.Y
          ua0 ua1 va0 va1 uIn0 uIn1 vIn0 vIn1)
        (uRS4Tangent p c0 c1 c2 c3 c4 P1'.X P1'.Y
          ua0 ua1 va0 va1 uIn0 uIn1 vIn0 vIn1))
    (eP1 : sa.P1 = P1') (eP2 : sa.P2 = P2')
    (e0 : sa.toSampleTarget.u0 = u0') (e1 : sa.toSampleTarget.u1 = u1')
    (e2 : sa.toSampleTarget.v0 = v0') (e3 : sa.toSampleTarget.v1 = v1')
    (eout : (u0', u1', v0', v1') =
      ReduceDispatchGeneral p c0 c1 c2 c3 c4 (P1'.X, P1'.Y) (P2'.X, P2'.Y)
        ua0 ua1 va0 va1 uIn0 uIn1 vIn0 vIn1 hcur hgcd hcurT hgcdT) :
    isReductionOutputOf sa := by
  subst eP1; subst eP2; subst e0; subst e1; subst e2; subst e3
  -- `subst` eliminates `u0' u1' v0' v1'` (and `P1' P2'`) entirely,
  -- replacing them by `sa.toSampleTarget.u0` etc. everywhere including in
  -- `hcur/hgcd/hcurT/hgcdT/eout` — so those primed names no longer exist
  -- as identifiers past this point; `eout` itself is already the
  -- correctly-substituted witness to hand back. `uIn0 uIn1 vIn0 vIn1` are
  -- the INPUT anchor-pair coordinates fed to `ReduceDispatchGeneral`,
  -- kept syntactically distinct from `u0' u1' v0' v1'` (the OUTPUT being
  -- equated) so this witness is never a self-feeding fixed point.
  exact ⟨c0, c1, c2, c3, c4, ua0, ua1, va0, va1,
    uIn0, uIn1, vIn0, vIn1,
    hcur, hgcd, hcurT, hgcdT, eout⟩

/-- **First real instance of `isReductionOutputOf`.** Given curve
coefficients, two points, an anchor Mumford pair, and
`ReduceDispatchGeneral`'s four case-split hypotheses (all caller-
supplied, exactly as `ReduceDispatchGeneral` itself demands them — no
attempt is made to derive them here), produces a real
`SampleTargetFromAlpha` whose `.toSampleTarget` literally IS
`ReduceDispatchGeneral`'s output on that same data, together with the
(now genuinely immediate — no fixed point required) proof that it
satisfies `isReductionOutputOf`. This is `ROADMAP-alpha-to-degree-
uniform.md` Part A's actual content, restated at the right level per
this pass's roadmap re-read: existence of a `SampleTargetFromAlpha`
that really did come out of running `Reduce`, nothing about which
divisor class it represents. -/
theorem exists_sampleTargetFromAlpha_of_reduceDispatch
    (aClass : HyperellipticPolynomial.Jacobian H D) (δ₀ : H.Point)
    (alpha : ℤ) (P1 P2 : H.Point)
    (c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (hcur : (P1.X, P1.Y) ≠ (P2.X, P2.Y) →
      curBeforeMonic4General p c0 c1 c2 c3 c4 (P1.X, P1.Y) (P2.X, P2.Y)
        ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hgcd : (P1.X, P1.Y) ≠ (P2.X, P2.Y) →
      IsCoprime (Ypoly4 p (P1.X, P1.Y) (P2.X, P2.Y) ua0 ua1 va0 va1 u0 u1 v0 v1)
        (uRS4General p c0 c1 c2 c3 c4 (P1.X, P1.Y) (P2.X, P2.Y)
          ua0 ua1 va0 va1 u0 u1 v0 v1))
    (hcurT : (P1.X, P1.Y) = (P2.X, P2.Y) →
      curBeforeMonic4Tangent p c0 c1 c2 c3 c4 P1.X P1.Y
        ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hgcdT : (P1.X, P1.Y) = (P2.X, P2.Y) →
      IsCoprime (Ypoly4Tangent p c0 c1 c2 c3 c4 P1.X P1.Y
          ua0 ua1 va0 va1 u0 u1 v0 v1)
        (uRS4Tangent p c0 c1 c2 c3 c4 P1.X P1.Y
          ua0 ua1 va0 va1 u0 u1 v0 v1)) :
    ∃ sa : SampleTargetFromAlpha p H D aClass δ₀,
      sa.alpha = alpha ∧ sa.P1 = P1 ∧ sa.P2 = P2 ∧ isReductionOutputOf sa := by
  obtain ⟨e0, e1, e2, e3⟩ := toSampleTarget_mk_sampleTargetFromAlpha_of_reduceDispatch
    aClass δ₀ alpha P1 P2 c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1
    hcur hgcd hcurT hgcdT
  obtain ⟨ea, eP1, eP2⟩ := alpha_P1_P2_mk_sampleTargetFromAlpha_of_reduceDispatch
    aClass δ₀ alpha P1 P2 c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1
    hcur hgcd hcurT hgcdT
  -- Introduce the witness as a bound local `sa` via `generalize` BEFORE
  -- `refine`, same discipline as `isReductionOutputOf_of_fields_eq`'s
  -- call site logic below — this keeps
  -- `mk_sampleTargetFromAlpha_of_reduceDispatch` out of the `?_` goal
  -- `refine` would otherwise leave.
  generalize hsa : mk_sampleTargetFromAlpha_of_reduceDispatch
    aClass δ₀ alpha P1 P2 c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1
    hcur hgcd hcurT hgcdT = sa at e0 e1 e2 e3 ea eP1 eP2
  refine ⟨sa, ea, eP1, eP2, ?_⟩
  -- `e0 e1 e2 e3` state `sa.toSampleTarget`'s fields equal `out`'s
  -- projections, where `out := ReduceDispatchGeneral ... u0 u1 v0 v1
  -- hcur hgcd hcurT hgcdT`. So the lemma's output-equation variables
  -- (`u0' u1' v0' v1'`) must be instantiated to `out`'s own projections
  -- below — NOT to the raw input `u0 u1 v0 v1` themselves, which is what
  -- broke the previous attempt (conflating "input fed to Reduce" with
  -- "output Reduce produces"). With that instantiation, `eout` becomes
  -- exactly `out = out`, closed by `rfl`; `uIn0..vIn1` (the genuine
  -- INPUT coordinates) are separately instantiated to `u0 u1 v0 v1`.
  exact isReductionOutputOf_of_fields_eq sa P1 P2 c0 c1 c2 c3 c4 ua0 ua1 va0 va1
    (ReduceDispatchGeneral p c0 c1 c2 c3 c4 (P1.X, P1.Y) (P2.X, P2.Y)
      ua0 ua1 va0 va1 u0 u1 v0 v1 hcur hgcd hcurT hgcdT).1
    (ReduceDispatchGeneral p c0 c1 c2 c3 c4 (P1.X, P1.Y) (P2.X, P2.Y)
      ua0 ua1 va0 va1 u0 u1 v0 v1 hcur hgcd hcurT hgcdT).2.1
    (ReduceDispatchGeneral p c0 c1 c2 c3 c4 (P1.X, P1.Y) (P2.X, P2.Y)
      ua0 ua1 va0 va1 u0 u1 v0 v1 hcur hgcd hcurT hgcdT).2.2.1
    (ReduceDispatchGeneral p c0 c1 c2 c3 c4 (P1.X, P1.Y) (P2.X, P2.Y)
      ua0 ua1 va0 va1 u0 u1 v0 v1 hcur hgcd hcurT hgcdT).2.2.2
    u0 u1 v0 v1 hcur hgcd hcurT hgcdT eP1 eP2 e0 e1 e2 e3 rfl
