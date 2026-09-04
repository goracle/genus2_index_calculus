# Roadmap: from `reducedClassDispatch` to `decoupledSystem_degree_uniform`

## Status, this pass (read this first)

**Part A is DONE, build green.** `SampleTargetFromAlphaWitness.lean`
exists and gives `SampleTargetFromAlpha` its first real, non-`sorry`
instance genuinely built from `ReduceDispatchGeneral`'s output
(`isReductionOutputOf`, `exists_sampleTargetFromAlpha_of_reduceDispatch`).
Along the way, a real bug was found and fixed in `isReduction'`/
`isReductionOf` themselves (`AlphaLocusDegreeUniform.lean`) — see
"Bug found and fixed this pass" below — and propagated through all 11
files that carried the broken shape (`AlphaLocusDegreeUniformCross1-4`,
`ReducedClassBundles(Cross1-4)`, `ReducedClassDispatch`), all
REPL-confirmed green.

**Part B's numerical prerequisite is DONE.** Claire ran the
`HomotopyContinuation.jl` pipeline (outside Lean, per this roadmap's own
prior instruction not to start Part B before this): **the system comes
back 0-dimensional, with witness points missing/dropped, consistent
across multiple independent re-runs.** This is the decisive empirical
signal the "Suggested order" step 3 was gating on — see "Numerical
check: result" below for what this means and what it does NOT yet
settle.

**What comes next**: Part B, `decoupledSystem_degree_uniform` itself, is
now unblocked and is the actual next work. See "What comes next,
concretely" at the bottom.

## Bug found and fixed this pass: `isReduction'` was circular

While building `SampleTargetFromAlphaWitness.lean`, a REPL error
(`Application type mismatch` on an `e0 : ... = out.1` vs. `... = u0`
goal) traced back to a real modeling bug in `isReduction'`'s own
definition, not just a wiring issue in the new file.

**The bug**: `ReduceDispatchGeneral` takes curve coefficients, the two
affine points `P1,P2`, an anchor Mumford pair `(ua0,ua1,va0,va1)`
(`alpha•a`'s own known coordinates), and a SEED Mumford pair
`(u0,u1,v0,v1)` that Cantor composition acts on together with `P1,P2`
and the anchor before reducing. `isReduction'`, as originally written,
fed `sa.toSampleTarget`'s own `(u0,u1,v0,v1)` fields into BOTH roles at
once: the thing being asserted equal to `Reduce`'s output, AND the seed
argument to that same call. That's circular — `x = f(..., x)` instead
of `x = f(..., y)` for an independent `y` — not a real "is this already
reduced" condition.

Concretely, this was caught by asking what `isReductionOutputOf sa →
isReduction' sa` (a candidate bridge lemma) would actually require: it
reduces to an idempotence claim `ReduceDispatchGeneral(...,
ReduceDispatchGeneral(..., x)) = ReduceDispatchGeneral(..., x)`, which
is false in general for this function (it composes the anchor into the
seed rather than merely canonicalizing an already-reduced pair — see
chat log for the full ChatGPT-assisted derivation). That falseness was
the signal the definition itself, not just a proof attempt, was wrong.

**The fix**: `isReduction'` (and its existential wrapper `isReductionOf`)
now take `u0 u1 v0 v1 : F p` as genuinely free parameters — the seed is
independent of `sa`'s own coordinates, which appear only on the LHS of
the final equation (`sa.toSampleTarget`'s fields = `Reduce`'s output on
that free seed). This matches `isReductionOutputOf`'s already-correct
shape in `SampleTargetFromAlphaWitness.lean`.

**Propagation, confirmed mechanical**: `reducedClass_eq_of_isReduction'`
and all 6 tangent/cross siblings, plus `reducedClassDispatch`, carry
`hcur/hgcd/hcurT/hgcdT/hr`-style hypotheses whose OLD type had the same
self-feeding bug baked in directly (not just via calling `isReduction'`).
Checked file-by-file before editing: in every one of these theorems,
these hypotheses are declared in the signature and passed to `isReduction'`'s
own application, but never destructured or otherwise inspected anywhere
in the proof body. So this was a signature-only fix — add the same free
`u0 u1 v0 v1` (or `gU0/gU1/gV0/gV1`, `c1U0..c4V1` in the dispatcher,
per-branch) — with zero proof-content changes required. All REPL-
confirmed green after the change.

**Files touched this pass**: `AlphaLocusDegreeUniform.lean` (the fix
itself), `AlphaLocusDegreeUniformCross{1,2,3,4}.lean`,
`ReducedClassBundles.lean`, `ReducedClassBundlesCross{1,2,3,4}.lean`,
`ReducedClassDispatch.lean`, `SampleTargetFromAlphaWitness.lean` (new).
**Untouched, confirmed not needing this fix**: the two tangent-anchor
theorems `reducedClass_eq_of_isReduction'_tangent`/`_tangent_target`
route through `TangentReductionData`/`TangentAssemblyData` instead and
never call `isReduction'` at all.

## Numerical check: result

Per this roadmap's own prior gate ("do not start Part B until this has
been run"): Claire ran two independent checks on several/random
`(alpha,alpha')` pairs on one fixed curve.

1. **Resultant-based check**: solved the system directly down to the
   U,V resultants (not via homotopy continuation), then plugged in two
   random values of `P`. No solution was visible — the expected outcome
   if the solution variety has dimension ≤1, not the naive 2-dimensional
   reading (a genuinely 2D variety would have produced a solution for
   generic `P`'s).
2. **`HomotopyContinuation.jl` check**: run on several independent
   `(alpha,alpha')` pairs.

**Result: 0-dimensional, with witness points missing, consistent across
multiple re-runs** (check 2) — **consistent with** check 1's dimension
≤1 finding. Two independently-run methods on the same regime agree.

What this supports: the uniform degree bound
`decoupledSystem_degree_uniform` is targeting is plausible — the
solution variety is NOT the naive 2-dimensional "plug in two points and
solve" reading; something is genuinely cutting it down to finitely many
points, matching a real uniform-degree phenomenon rather than a
coincidence of one instance or one method.

What this does NOT yet settle (open items Part B still needs, see
below): WHY it's 0D (which nondegeneracy condition is doing the work),
whether the "missing witness points" indicate `Bad`-locus degeneration
specifically (vs. numerical/path-tracking failure unrelated to the
math), whether this holds across *different curves* (both checks used
one fixed curve — curve dependence is untested), and how large the
exceptional set is as a fraction of the whole `F_ell` domain — the
number the eventual counting argument's usefulness depends on. The
"`D ~ K_C` correlates with a degree jump" check mentioned below is still
open and should be looked at together with the missing-witness-point
pattern, since they may be the same phenomenon.

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
  4-point matching system `[P1]+[P2]-alpha•a = [P3]+[P4]-alpha'•a`,
  where `alpha•a` and `alpha'•a` are GIVEN (known Jacobian points) and
  `P1,P2,P3,P4` are the unknowns being solved for.
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
  restatement against `ReduceDispatchGeneral`'s actual output, **fixed
  this pass, see above**) and `isReductionOf` (the existential-over-
  witnessing-coordinates version meant to replace the free `isReduction`
  field everywhere). Then it spent ~900 lines proving
  `reducedClass_eq_of_isReduction'` — that `isReduction'` holding really
  does force `sa.reducedClass` to equal the class the Mumford pair
  geometrically represents. **That's the theorem the dispatcher now
  routes over all seven anchor/target configurations of.**

**What this means concretely, now that Part A is done**: the dispatcher
answers "IF some `SampleTargetFromAlpha` satisfies `isReduction'` (with
a given anchor/target configuration), THEN its `reducedClass` is what it
should be," AND `SampleTargetFromAlphaWitness.lean` now shows a real
instance can be built with `isReductionOutputOf` genuinely discharged.
The one remaining item from the original Part A framing — chaining that
witness through `reducedClassDispatch` itself to get a fully concrete
"curve + two points + alpha → divisor class in the Jacobian" instance
with NO free parameters anywhere — is optional polish, not a blocker;
see "What comes next" below for why Part B doesn't need it first.

## The actual chain, traced end to end

```
ReduceDispatchGeneral (Reduce/GeneralSharedRoot.lean)
  -- concrete: given curve coeffs + two curve points + an anchor
  -- Mumford pair + a free seed pair, COMPUTES the reduced
  -- (u0,u1,v0,v1) via Cantor reduction. Proved correct at the
  -- POLYNOMIAL level only (ReduceGeneral_isMumfordTarget4:
  -- v²≡f mod u) — this is ROADMAP-reduce-to-zerodim.md's
  -- "already done" layer.
        |
        | isReduction' packages "sa.toSampleTarget's (u0,u1,v0,v1)
        | literally equals ReduceDispatchGeneral's output on some
        | FREE seed (u0,u1,v0,v1)" -- fixed this pass, no longer
        | self-referential
        v
isReduction'  (AlphaLocusDegreeUniform.lean, coordinate-level, Prop)
        |
        | reducedClass_eq_of_isReduction' + its 6 tangent/cross
        | siblings, DISPATCHED, proves
        | isReduction' ⟹ sa.reducedClass = <the geometric class>
        v
sa.reducedClass = alpha•aClass - ([P1]+[P2]-2•[δ₀])   (divisor-class
                                                         level, Jacobian H D)
        |
        | isReductionOutputOf / exists_sampleTargetFromAlpha_of_
        | reduceDispatch (SampleTargetFromAlphaWitness.lean, DONE
        | this pass) -- a real SampleTargetFromAlpha, genuinely
        | built from ReduceDispatchGeneral's own output, exists
        v
SampleTargetFromAlpha, actually usable as "the alpha-parametrized
family the degree-uniform theorem quantifies over"
        |
        | decoupledSystem_degree_uniform's own statement already
        | quantifies over `sa sb : SampleTargetFromAlpha p H D aClass δ₀`
        | (AlphaLocusDegreeUniform.lean line 890) — ALREADY WIRED
        v
decoupledSystem_degree_uniform  (sorry — task (B)'s Bad + the actual
                                  degree-uniformity argument;
                                  NUMERICAL PREREQUISITE NOW DONE,
                                  came back 0D -- this is the actual
                                  next work, see below)
```

## Part A: give `isReductionOf`/`isReductionOutputOf` a first real
instance — DONE

`SampleTargetFromAlphaWitness.lean` exists, build green, REPL-confirmed.
It builds `isReductionOutputOf` (a narrower, self-contained sibling of
`isReduction'` — see that file's own module docstring for why it's a
separate predicate rather than a patch to `isReduction'`) with a real,
non-`sorry` witness: `mk_sampleTargetFromAlpha_of_reduceDispatch` +
`exists_sampleTargetFromAlpha_of_reduceDispatch`. Along the way this
surfaced and fixed the `isReduction'` circularity bug described above.

**Not done, and not currently blocking**: composing this witness with
`reducedClassDispatch` itself for a single, fully-closed, no-free-
parameter "curve + two points + alpha → divisor class" instance (the
original Part A step 5). This remains a cheap, mechanical follow-up
whenever it's useful (e.g. as a sanity check while working Part B), but
Part B does not need it as a prerequisite — Part B's own work is at the
level of the general theorem statement (`decoupledSystem_degree_uniform`
quantifies over abstract `sa sb`, not one concrete instance), not a
specific numerical instantiation.

## Part B: `decoupledSystem_degree_uniform` itself (the actual
`p^(4/5)` closure) — genuinely open, NOW THE ACTIVE WORK

This is `ROADMAP-alpha-locus.md`'s Steps 2-3, restated here only to
keep this doc as the single up-to-date pointer (that roadmap's own
content is not stale and shouldn't be re-derived — read it directly for
the full argument, not just this summary):

1. ~~**Numerical check first (Julia/Oscar, not Lean)**~~ **DONE, this
   pass.** Claire ran the `HomotopyContinuation.jl` pipeline on several
   independent `(alpha,alpha')` pairs: **result is 0-dimensional, with
   witness points missing, consistent on multiple re-runs.** See
   "Numerical check: result" above for what this does and doesn't
   settle. Still open, and worth doing before/alongside step 2 below:
   check whether `D ~ K_C` (the natural candidate for the exceptional
   locus `Bad`) correlates with the missing-witness-point pattern, and
   how large the flagged-bad set is as a *fraction of `F_ell`* (not just
   "positive-dimensional over `C`") — this is the number that determines
   whether the eventual counting argument gives a useful bound or a
   vacuous one.
2. **Now unblocked, this is the actual next step**: pin down `Bad`'s
   real definition (replacing `IsSmallExceptionalSet`'s current `True`
   stub, `AlphaLocusDegreeUniform.lean` line 838) and attempt
   `decoupledSystem_degree_uniform` itself, via the strategy
   `ROADMAP-alpha-locus.md` Step 3 already lays out: show the
   peel-chain's own nondegeneracy resultants/discriminants
   (`Nondegenerate`, `CrossNondegenerate`, `PeelChainNondegenerate`)
   are bounded-degree polynomials in `alpha,alpha'`, so degree jumps
   are confined to their vanishing locus.

## What comes next, concretely

1. **Correlate the missing-witness-point pattern with `D ~ K_C`**
   (Claire, Julia/Oscar, not Lean) — same numerical setup as the check
   just run, extended to flag which `(alpha,alpha')` instances show
   missing witnesses and check whether those correlate with the
   candidate `Bad` locus. This directly informs step 2's real
   definition of `Bad` — don't guess the definition in Lean before this
   comes back, per this project's own "settle on paper first"
   discipline.
2. **Measure `Bad`'s size as a fraction of `F_ell`** (Claire,
   Julia/Oscar) — needed regardless of `Bad`'s exact definition, since a
   `Bad` set that's a large fraction of the domain makes the eventual
   counting argument vacuous even if everything else goes through.
3. **Pin down `Bad`'s real Lean definition** (replacing the `True` stub)
   once (1)-(2) give a concrete candidate to formalize — don't attempt
   this from first principles in Lean; transcribe whatever the numerics
   converge on.
4. **Attempt `decoupledSystem_degree_uniform` itself** via
   `ROADMAP-alpha-locus.md` Step 3's strategy (bounded-degree
   nondegeneracy resultants confine degree jumps to `Bad`'s vanishing
   locus) — this is the genuinely hard, open algebraic-geometry content,
   and the actual `p^(4/5)`-closure work. Expect this to be the longest
   remaining phase of the project; break it into sub-lemmas rather than
   attempting the whole theorem in one pass, same discipline used for
   `reducedClass_eq_of_isReduction'` (bundled hypothesis structures,
   `_flat` drafts before bundling, dispatched over cases only once each
   piece is separately proved).
5. **(Low-priority, whenever convenient)**: close out Part A's original
   step 5 — compose `exists_sampleTargetFromAlpha_of_reduceDispatch`
   with `reducedClassDispatch` for one fully-concrete, no-free-parameter
   instance, as a standing sanity check / regression test on the whole
   chain.

