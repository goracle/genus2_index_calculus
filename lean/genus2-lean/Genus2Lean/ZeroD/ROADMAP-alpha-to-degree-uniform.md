# Roadmap: from `reducedClassDispatch` to `decoupledSystem_degree_uniform`

## Why this doc exists

`ROADMAP-reducedClass-dispatcher.md` just closed (build green,
REPL-confirmed): `ReducedClassDispatch.lean` gives all seven
`reducedClass_eq_of_isReduction'` variants a real caller for the first
time. That was itself the endpoint of `ROADMAP-reduce-divisor-
correctness.md` (which proved the underlying theorems) and
`ROADMAP-cawitness-tangent-interpolation.md`/`ROADMAP-split-hypothesis-
elimination.md` (which built the tangent/cross cases the dispatcher
routes over).

**None of those roadmaps say what the dispatcher is FOR.** Tracing back
through them (this pass) to `ROADMAP-alpha-locus.md` — the doc that
actually motivated proving `reducedClass_eq_of_isReduction'` in the
first place — recovers the big picture:

- The project's actual target is `decoupledSystem_degree_uniform`
  (`AlphaLocusDegreeUniform.lean` line 886, still `sorry`): a uniform-
  in-`(alpha,alpha')` bound on the solution-variety degree of the
  4-point matching system `[P1]+[P2]-alpha•a = [P3]+[P4]-alpha'•a`.
- Per `ROADMAP-alpha-locus.md`'s corrected picture (its own TL;DR,
  superseding an earlier wrong framing): if this uniform bound holds
  outside a genuinely small exceptional set `Bad`, it closes
  advisory-6/7's Question 4 (the 8th-moment gap) by a two-line counting
  argument — `B^4 = Σ_Delta X(Delta) ≤ d·#{Delta : X(Delta)>0}` — with
  no Sidon-set/Fourier-uniformity machinery needed. This is the
  `p^(4/5)`-complexity closure Claire referenced: resolving Question 4
  this way is what would let the general genus-2 index-calculus
  complexity bound go through.
- Before `decoupledSystem_degree_uniform` can even be STATED
  meaningfully, `SampleTarget` needed an `alpha` field connecting a
  Mumford pair back to the divisor class `alpha•a - P1 - P2` it's
  supposedly the reduction of (task (A), `ROADMAP-alpha-locus.md` Step
  1). `SampleTargetFromAlpha` is that structure. Its `isReduction :
  Prop` field is the actual placeholder task (A) left open — "some
  `Prop`" typechecks as a witness for anything, including nonsense, so
  it doesn't yet mean anything to say "`sa` satisfies `isReduction`."
- `ROADMAP-reduce-divisor-correctness.md` gave `isReduction` real
  content in two pieces: `isReduction'` (a concrete, computable-RHS
  restatement against `ReduceDispatchGeneral`'s actual output) and
  `isReductionOf` (the existential-over-witnessing-coordinates version
  meant to replace the free `isReduction` field everywhere). Then it
  spent ~900 lines proving `reducedClass_eq_of_isReduction'` — that
  `isReduction'` holding really does force `sa.reducedClass` to equal
  the class the Mumford pair geometrically represents. **That's the
  theorem the dispatcher now routes over all seven anchor/target
  configurations of.**

**What this means concretely**: the dispatcher answers "IF some
`SampleTargetFromAlpha` satisfies `isReduction'` (with a given
anchor/target configuration), THEN its `reducedClass` is what it should
be." It does not answer, and nothing in the codebase yet answers,
"DOES any real `SampleTargetFromAlpha` satisfy `isReduction'`" — i.e.
**zero instances of `isReductionOf` have ever been constructed**
(confirmed by grep this pass: `isReductionOf` has no callers anywhere
outside its own definition). The conditional link is proved; the
antecedent has never been discharged. This is the actual next gap,
and it sits directly on the path to `decoupledSystem_degree_uniform`
per task (A)'s own framing — `SampleTargetFromAlpha` isn't really
usable as "the alpha-parametrized sample target" until some concrete
instance of it can be exhibited with a real `isReduction'` proof, not
just declared as a structure with a `Prop` field.

## The actual chain, traced end to end

```
ReduceDispatchGeneral (Reduce/GeneralSharedRoot.lean)
  -- concrete: given curve coeffs + two curve points + an anchor
  -- Mumford pair, COMPUTES the reduced (u0,u1,v0,v1) via Cantor
  -- reduction. Proved correct at the POLYNOMIAL level only
  -- (ReduceGeneral_isMumfordTarget4: v²≡f mod u) — this is
  -- ROADMAP-reduce-to-zerodim.md's "already done" layer.
        |
        | isReduction' packages "sa.toSampleTarget's (u0,u1,v0,v1)
        | literally equals ReduceDispatchGeneral's output"
        v
isReduction'  (AlphaLocusDegreeUniform.lean, coordinate-level, Prop)
        |
        | reducedClass_eq_of_isReduction' + its 6 tangent/cross
        | siblings, NOW DISPATCHED (this session) — proves
        | isReduction' ⟹ sa.reducedClass = <the geometric class>
        v
sa.reducedClass = alpha•aClass - ([P1]+[P2]-2•[δ₀])   (divisor-class
                                                         level, Jacobian H D)
        |
        | *** NOTHING HERE YET ***  — no SampleTargetFromAlpha
        | instance has ever been built with a real isReduction'
        | proof attached (isReductionOf: 0 callers)
        v
SampleTargetFromAlpha, actually usable as "the alpha-parametrized
family the degree-uniform theorem quantifies over"
        |
        | decoupledSystem_degree_uniform's own statement already
        | quantifies over `sa sb : SampleTargetFromAlpha p H D aClass δ₀`
        | (AlphaLocusDegreeUniform.lean line 890) — this part is
        | ALREADY WIRED, no further Lean plumbing needed there
        v
decoupledSystem_degree_uniform  (sorry — task (B)'s Bad + the actual
                                  degree-uniformity argument, both
                                  entirely unstarted)
```

**Two separate gaps remain on this chain, not one**, and they should
not be conflated (same discipline `ROADMAP-cawitness-tangent-
interpolation.md`'s "two independent problems" section used):

1. **Exhibiting a real `isReductionOf` witness** (this doc's Part A) —
   purely mechanical once you have concrete curve/point data:
   instantiate `c0..c4`, `P1,P2`, run `ReduceDispatchGeneral` (or state
   the existence claim abstractly via `ReduceDispatchGeneral`'s own
   correctness lemma), and produce the six existential witnesses
   `isReductionOf` asks for. No new mathematics — this is *using*
   already-proved machinery (`ReduceDispatchGeneral`,
   `reducedClassDispatch`) for the first time, not extending it.
2. **`decoupledSystem_degree_uniform` itself** (task (B) + the actual
   degree argument, `ROADMAP-alpha-locus.md` Steps 2-3) — genuinely
   open, genuinely hard (numerically-informed exceptional-set
   definition, then a real algebraic-geometry degree bound). This is
   the actual `p^(4/5)`-closure content and should not be started until
   Step 2's numerical check (below) has actually been run.

## Part A: give `isReductionOf` its first real instance

**Goal**: prove a lemma of the shape

```lean
theorem exists_sampleTargetFromAlpha_of_reduceDispatch
    {p : ℕ} [Fact (Nat.Prime p)] [Fact (p ≠ 2)]
    {H : HyperellipticPolynomial (F p)} [IsDedekindDomain (CoordinateRing H)]
    {D : PrincipalDivisorData H} {aClass : Jacobian H D} {δ₀ : H.Point}
    (alpha : ℤ) (P1 P2 : H.Point)
    (c0 c1 c2 c3 c4 ua0 ua1 va0 va1 : F p)
    (hcur : ...) (hgcd : ...) (hcurT : ...) (hgcdT : ...) :
    ∃ sa : SampleTargetFromAlpha p H D aClass δ₀,
      sa.alpha = alpha ∧ sa.P1 = P1 ∧ sa.P2 = P2 ∧ isReductionOf sa := by
  -- `sa.toSampleTarget := ⟨ReduceDispatchGeneral p c0 c1 c2 c3 c4
  --   (P1.X,P1.Y) (P2.X,P2.Y) ua0 ua1 va0 va1 ... hcur hgcd hcurT hgcdT⟩`
  -- (unpacking the 4-tuple `ReduceDispatchGeneral` returns into
  -- `u0,u1,v0,v1` fields), then `isReductionOf`'s witness is `rfl` by
  -- construction — `isReduction'` IS the statement that
  -- `sa.toSampleTarget`'s fields equal `ReduceDispatchGeneral`'s output,
  -- and that's exactly how `sa.toSampleTarget` was just built.
  sorry
```

This is the FIRST concrete `SampleTargetFromAlpha` with a genuinely
discharged `isReduction'`, rather than a structure whose `isReduction`
field is asserted rather than proved. Concretely:

1. **Check `ReduceDispatchGeneral`'s exact return type first** — grep
   `Reduce/GeneralSharedRoot.lean` directly rather than assuming a
   4-tuple `(F p × F p × F p × F p)` (the module docstring above uses
   that shape informally; confirm before writing the `sa.toSampleTarget`
   construction).
2. **Build `sa.toSampleTarget`** by projecting `ReduceDispatchGeneral`'s
   output into `SampleTarget`'s four fields.
3. **Build `sa.reducedClass`** — this is already computed
   automatically by `SampleTargetFromAlpha`'s own default-field
   definition (`alpha•aClass - toJacobian D ⟨single P1 + single P2 -
   2•single δ₀, ...⟩`), no new work.
4. **Discharge `sa.isReduction`** with `isReductionOf sa`, itself
   discharged by `⟨c0,c1,c2,c3,c4,ua0,ua1,va0,va1,hcur,hgcd,hcurT,hgcdT,
   rfl⟩` — the `rfl` should go through since `sa.toSampleTarget`'s
   fields were LITERALLY defined as `ReduceDispatchGeneral`'s output in
   step 2; if it doesn't (defeq issues through the tuple-projection),
   that's a real, small bug to fix, not a sign of a deeper problem.
5. **Once this exists, compose it with `reducedClassDispatch`**
   (this session's file) to get a genuinely end-to-end theorem: given
   real curve/point data and a chosen anchor pair `Ra1,Ra2` satisfying
   whichever of the seven configurations applies, produce a real
   `SampleTargetFromAlpha` AND the proof that its `reducedClass` equals
   the concrete geometric divisor class — the first fully-instantiated,
   no-`sorry`, no-free-`Prop` link from "curve + two points + alpha"
   all the way to "divisor class in the Jacobian," anywhere in this
   project.

**Where this belongs**: new file, `SampleTargetFromAlphaWitness.lean`
or similar, importing `AlphaLocusDegreeUniform.lean` (for
`SampleTargetFromAlpha`/`isReduction'`/`isReductionOf`),
`ReducedClassDispatch.lean` (for `reducedClassDispatch`/`CrossCase`),
and `Reduce.GeneralSharedRoot` (for `ReduceDispatchGeneral`) directly.
Small — this is wiring, not new mathematical content, so should stay
well under 200 lines.

**Do this before Part B.** It's cheap, it's the natural next step given
what's already built, and it's a real correctness check on everything
proved so far: if `ReduceDispatchGeneral`'s output can't actually be
packaged into a real `isReductionOf` witness cleanly, that's worth
finding out now rather than after investing in the much harder Part B
work.

## Part B: `decoupledSystem_degree_uniform` itself (the actual
`p^(4/5)` closure) — genuinely open, do the empirical check first

This is `ROADMAP-alpha-locus.md`'s Steps 2-3, restated here only to
keep this doc as the single up-to-date pointer (that roadmap's own
content is not stale and shouldn't be re-derived — read it directly for
the full argument, not just this summary):

1. **Numerical check first (Julia/Oscar, not Lean)**: generate several
   independent `(alpha,alpha')` pairs, run the existing
   `HomotopyContinuation.jl` pipeline, record the witness-point count
   for each. If it's the same small number every time, that's decisive
   evidence the uniform bound is even TRUE before spending Lean effort
   proving it. Separately, check whether `D ~ K_C` (the natural
   candidate for the exceptional locus `Bad`) actually correlates with
   a degree jump, and how large the flagged-bad set is as a *fraction
   of `F ell`* (not just "positive-dimensional over `C`") — this is the
   number that determines whether the eventual counting argument gives
   a useful bound or a vacuous one.
2. **Only once (1) comes back encouraging**: pin down `Bad`'s real
   definition (replacing `IsSmallExceptionalSet`'s current `True` stub,
   `AlphaLocusDegreeUniform.lean` line 838) and attempt
   `decoupledSystem_degree_uniform` itself, via the strategy
   `ROADMAP-alpha-locus.md` Step 3 already lays out: show the
   peel-chain's own nondegeneracy resultants/discriminants
   (`Nondegenerate`, `CrossNondegenerate`, `PeelChainNondegenerate`)
   are bounded-degree polynomials in `alpha,alpha'`, so degree jumps
   are confined to their vanishing locus.

**This part should not be started until Part A is done and (1) above
has actually been run** — per this project's own "settle on paper
first" instinct (used correctly earlier in `ROADMAP-alpha-locus.md`'s
own history), there's no point building Lean machinery for a
uniformity claim nobody has checked is even numerically true yet.

## Suggested order

1. Part A, step 1: confirm `ReduceDispatchGeneral`'s exact signature
   (5 minutes, unblocks everything else).
2. Part A, steps 2-5: write `SampleTargetFromAlphaWitness.lean`,
   REPL-test.
3. Stop and run Part B's numerical check (Claire, outside Lean) before
   writing any more Lean for the degree-uniformity theorem itself.
4. Only after (3) comes back: pin down `Bad`, attempt
   `decoupledSystem_degree_uniform`'s actual proof.
