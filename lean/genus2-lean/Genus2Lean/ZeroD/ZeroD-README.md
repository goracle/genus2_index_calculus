# ZeroD: what this directory is for, and where things actually stand

**Written**: this pass, from scratch, by reading every `.lean` file's
imports/line count and every `ROADMAP-*.md`/`CHATGPT-*.md` file in this
directory end to end — not copied from any single existing doc. Purpose:
give a newcomer (including a future Claire/Claude who has lost the
thread) one place to start that doesn't require reconstructing the
story from 17 roadmap files that partially disagree with each other and
with the code.

**If you read nothing else, read this**: the roadmap `.md` files in this
directory are a *session log*, not a spec. Several of them assert a
theorem is `sorry` when the `.lean` file itself has since closed it
(see "Known stale claims" below) — the roadmaps document a sequence of
passes, and later passes often silently overtake earlier claims in
older files without anyone going back to fix the older file. **Treat
`grep`-verified `.lean` content as ground truth and every `.md` claim as
provisional until cross-checked.** `STATUS.md` (this directory) is a
freshly-verified sorry inventory as of this pass — re-run its scan
script rather than trusting either that file or this one blindly, since
both go stale the moment someone edits a `.lean` file.

## The one-sentence goal

Bound the "8th moment" (`E(S,S)`, advisory-6/7's Question 4 / the
`p^(4/5)` complexity claim) for the genus-2 index-calculus attack.
`Genus2Lean/Complexity.lean` (one level up) states this as the actual
top-level theorem and currently proves it via a Sidon-set/Fourier route
*conditional on* an unproved hypothesis (`OffDiagonalBound`). **`ZeroD`
is an entirely separate, independent attempt to prove the same
Question-4 bound a different way** — via a uniform algebraic-geometry
degree bound rather than additive combinatorics — that would need no
Sidon machinery and no `OffDiagonalBound` hypothesis at all if it goes
through. `ZeroD` does not currently import from or export to
`Complexity.lean`; the two are unconnected in Lean today. Whether
`ZeroD`'s route ever actually replaces `Complexity.lean`'s is an open
strategic question, not something this pass decides.

## Why "ZeroD"

Short for "zero-dimensional." The route's core idea (see
`ROADMAP-alpha-locus.md` for the full argument, it's worth reading in
full — this is a summary): the 4-point matching equation

    [P1]+[P2] - alpha•a = [P3]+[P4] - alpha'•a        (eq 1)

cuts out an algebraic variety in `(P1,P2,P3,P4)`-space, for each fixed
pair `(alpha,alpha')`. If that variety is **zero-dimensional** (finitely
many points) with a bound `d` on the point count that's **uniform**
across `(alpha,alpha')` (outside some small exceptional set `Bad`),
then a two-line counting argument bounds `E(S,S)` directly:

    B^4 = Sum_Delta X(Delta) <= d * #{Delta : X(Delta) > 0}
    ==> #{Delta : X(Delta) > 0} = Omega(B^4)

No Cauchy-Schwarz, no Sidon dichotomy, no Fourier uniformity. That
target theorem is `decoupledSystem_degree_uniform`, in
`AlphaLocusDegreeUniform.lean`. Everything else in this directory
exists to state and eventually prove that one theorem honestly.

## The dependency chain, traced from imports (not asserted from memory)

```
TheDataDerivation/DataDerivationBasics.lean
        |
        v
TheDataDerivation/DataDerivationTower.lean
        |
        v
TheDataDerivation/DataDerivationSolve.lean
        |
        v
TheDataDerivation/DataDerivationMumford.lean   -- builds theData: (uRS,vRS),
        |                                          the K=2 symbolic-anchor
        |                                          Mumford-reduction tower
        v
DecoupledSystemRegular.lean   -- SampleTarget := (u0,u1,v0,v1), no `alpha`
        |                         field. Idx = the 12-variable list.
        |                         genList, Nondegenerate, CrossNondegenerate.
        v
PeelChainAssembly.lean        -- regularSeq_of_peel_chain: the 12-stage
        |                         regular-sequence assembly, given
        |                         PeelChainNondegenerate + htop_ne_smul
        v
RegularSequenceFiniteQuotient.lean  -- generic commutative algebra,
        |                              no Genus2Lean content: regular
        |                              sequence of length n in n-variable
        |                              poly ring over a field implies finite
        |                              quotient
        v
AlphaLocusDegreeUniform.lean   -- decoupledSystem_isRegularSequence,
        |                          decoupledSystem_zeroDimensional,
        |                          decoupledSystem_degree_uniform (THE
        |                          target theorem), isReduction',
        |                          SampleTargetFromAlpha, GenericPeelChainHyp
        |
        +--> AlphaLocusDegreeUniformTangent.lean          (Ra1=Ra2 case)
        +--> AlphaLocusDegreeUniformTangentTarget.lean     (T1=T2 case)
        +--> AlphaLocusDegreeUniformCross{1,2,3,4}.lean    (cross-pair cases)
        |
        v
SampleTargetFromAlphaWitness.lean   -- first real (non-sorry) instance of
        |                               SampleTargetFromAlpha, built from
        |                               ReduceDispatchGeneral's own output
        v
ReducedClassBundles.lean, ReducedClassBundlesCross{1,2,3,4}.lean
        |                    -- bundles the 5 non-tangent-axis theorems
        |                       onto shared CoefficientData/ReductionData
        v
ReducedClassDispatch.lean   -- reducedClassDispatch: routes to whichever
                                of the 7 reducedClass_eq_of_isReduction'
                                variants (split / tangent / tangent-target /
                                cross x4) actually applies
```

Separately, feeding into `AlphaLocusDegreeUniform.lean` from the side:

```
Reduce/AlphaReduce.lean  -->  Reduce/GeneralSharedRoot.lean  -->  CAWitness.lean
   (K=4 anchor/tangent          (ReduceDispatchGeneral: the actual       (interpolation-
    row construction,            Cantor-reduction algorithm, general      matrix
    uRS4/vRS4, the                over K anchors -- this is "Reduce",      machinery
    Npoly4/Ypoly4/Epoly4          the thing task (A) in ROADMAP-alpha-    bCA/uCANew,
    machinery)                    locus.md originally called "unstarted") consumed by
                                                                            GeneralSharedRoot)
```

and the `PrincipalWitness*.lean` family (`PrincipalWitness.lean`,
`PrincipalWitnessStep{1,2,3,4}.lean`, `PrincipalWitnessAssembly.lean`,
`PrincipalWitnessFinalAssembly(TangentTarget)?.lean`,
`PrincipalWitnessCAConnection.lean`) is the divisor-class-level
machinery -- connecting a Mumford coordinate pair's *polynomial*
identity to the actual *divisor class* it represents in the Jacobian --
that `reducedClass_eq_of_isReduction'` (in `AlphaLocusDegreeUniform.lean`)
calls on. This is the layer `ROADMAP-reduce-divisor-correctness.md`
built, in an 18-pass sequence, essentially lemma-by-lemma from a
ChatGPT-derived proof sketch (`CHATGPT-REPLY-step3-reduce-correctness.md`).

## Current state, verified this pass (not copied from any roadmap's own claim)

A comment-stripped scan for the literal token `sorry` (not textual
mentions of the word in prose -- those inflate a raw grep hugely) across
**every** `.lean` file in this whole repo, top-level included, found:

**Zero live `sorry`s anywhere under `ZeroD/`.** All 7 remaining live
`sorry`s in the entire project are in the top-level directory
(`RiemannRochGenus2.lean` x2, `RiemannRochCrux.lean` x2,
`LCanonicalElementary.lean` x1, `SidonDichotomyGeneral.lean` x1,
`PrincipalSubgroupCollapse.lean` x1 -- see `STATUS.md` for exactly which
theorems). See `STATUS.md` for the scan script and how to re-run it.

**This contradicts several `ROADMAP-*.md` files in this directory**,
which describe `decoupledSystem_degree_uniform` and
`decoupledSystem_zeroDimensional` as still-open `sorry`s. Checked
directly: `AlphaLocusDegreeUniform.lean`'s own module docstring (its
last dated entry) says both were closed in a later pass, under a new
hypothesis bundle `GenericPeelChainHyp` -- not proved unconditionally,
but not a bare `sorry` either. **That docstring itself flags the result
as "not yet compiled against Claire's REPL"** -- so "zero live `sorry`
tokens" is not the same claim as "confirmed to typecheck." Read
`AlphaLocusDegreeUniform.lean`'s module docstring directly (its last
~150 lines) before trusting either the roadmaps' "still sorry" framing
or this doc's "zero sorry" framing -- both are snapshots, and only a
`lake build` settles which one is live right now.

## Sorry-free is not the same as done

Per this project's own stated practice ("if a theorem is false or too
hard, weaken it to a hypothesis rather than leaving a `sorry` or a
silently-false claim"), a huge amount of the real mathematical content
in this directory now lives in **hypothesis bundles**, not `sorry`s:
`Nondegenerate`, `CrossNondegenerate`, `PeelChainNondegenerate` (16
fields), `GenericPeelChainHyp`, and the various `hcur`/`hgcd`/`hdet`-
style nonvanishing assumptions threaded through the tangent/cross-case
files. A file being "sorry-free" only means its *stated* theorems are
proved from its *stated* hypotheses -- it says nothing about whether
those hypotheses are themselves true, provable, or vacuous. Whether the
hypotheses hold -- for a generic curve, for the actual production curve
this project's Julia pipeline uses, or at all -- is tracked separately;
see "What's actually still open" below.

## What's actually still open (the real remaining work, as of this pass)

Distilled from `ROADMAP-alpha-locus.md`, `ROADMAP-alpha-to-degree-
uniform.md`, and `ROADMAP-degree-uniform-step3.md` -- read those directly
for the full argument, this is a pointer, not a replacement:

1. **`GenericPeelChainHyp` itself is unproved.** The theorem
   `decoupledSystem_degree_uniform` currently gets its uniform bound
   *by assuming* this hypothesis holds outside a finite exceptional set.
   Whether that's true -- for real curves, real `(alpha,alpha')` -- is
   exactly advisory-6/7's Question 4, restated one layer deeper. This is
   the single biggest remaining question in the whole subsystem.
2. **`Reduce` (`ReduceDispatchGeneral`, `Reduce/GeneralSharedRoot.lean`)
   is proved correct only at the polynomial level** (`v^2 = f mod u`,
   the Mumford congruence) -- not yet connected to the actual *group-law*
   semantics (that it computes the literal divisor-class reduction of
   `alpha*a - P1 - P2`). `reducedClass_eq_of_isReduction'` and its six
   siblings are the layer that makes that connection, and per the
   docstring evidence above, at least the base case now typechecks as a
   real theorem (not a bare `sorry`) -- but budget time to re-verify this
   against the actual current file state before relying on it, per the
   "stale claims" warning above.
3. **The exceptional set's actual size is an open empirical question.**
   Claire's `HomotopyContinuation.jl` runs came back 0-dimensional
   (encouraging), but *how small* the bad locus is as a fraction of
   `F_ell` -- the number the eventual counting argument's usefulness
   depends on -- has not been measured. This is Julia/Oscar work, not
   Lean work; see `ROADMAP-degree-uniform-step3.md` Step 3.1.
4. **No dispatcher exists yet above `ReducedClassDispatch.lean`'s own
   level** that would take a bare "these two points collided" fact and
   route to the right one of the 7 theorem variants automatically from
   first principles -- `ReducedClassDispatch.lean` dispatches, but
   something still has to hand it pre-classified case data.

## Directory map (one line each -- see each file's own module docstring for real detail)

- `TheDataDerivation/` -- the K=2 symbolic-anchor tower (`theData`
  construction). Load-bearing, stable, sorry-free.
- `Reduce/` -- `AlphaReduce.lean` (K=4 anchor/tangent-row machinery) and
  `GeneralSharedRoot.lean` (`ReduceDispatchGeneral`, the actual Cantor-
  reduction algorithm -- this **is** "task (A)"/"`Reduce`" from
  `ROADMAP-alpha-locus.md`, not a stub).
- `DecoupledSystemRegular.lean` -- the 12-variable system, `SampleTarget`,
  the nondegeneracy hypothesis bundles.
- `PeelChainAssembly.lean` -- the regular-sequence proof itself.
- `RegularSequenceFiniteQuotient.lean` -- generic commutative algebra
  (regular sequence implies finite quotient), no project-specific content.
- `AlphaLocusDegreeUniform*.lean` (base + Tangent + TangentTarget +
  Cross1-4) -- the seven case-split variants of
  `reducedClass_eq_of_isReduction'`, plus the target theorem
  `decoupledSystem_degree_uniform` itself, in the base file.
- `CAWitness*.lean`, `SanchorMumfordOrdAt.lean`,
  `SanchorEqAlphaPoints.lean`, `TangentMumfordWitness.lean`,
  `CantorAddWitness.lean`, `CantorReductionStep.lean`,
  `OrdAtRootMultiplicityUnified.lean` -- interpolation-matrix and
  root-multiplicity machinery feeding the case-split variants above.
- `PrincipalWitness*.lean` -- the divisor-class-level lemma stack
  (polynomial identity implies actual Jacobian divisor class), built via a
  ChatGPT-assisted 18-pass derivation; see
  `CHATGPT-LOG-principal-witness-assembly.md`/`CHATGPT-REPLY-step3-
  reduce-correctness.md` for that derivation's own record.
- `ReducedClassBundles*.lean`, `ReducedClassDispatch.lean` -- bundling
  and dispatch over the seven case-split variants.
- `SampleTargetFromAlphaWitness.lean` -- the first genuinely concrete,
  non-`sorry` instance of `SampleTargetFromAlpha`.
- `ROADMAP-*.md` -- session logs, one per sub-effort, listed roughly in
  the order they were superseded by the next: `ROADMAP-alpha-locus.md`
  (the master plan, read this one first) then
  `ROADMAP-split-hypothesis-elimination.md` then
  `ROADMAP-cawitness-tangent-interpolation.md` then
  (`ROADMAP-principal-witness-tangent-assembly.md` is referenced by
  other files but was not found as a file in this snapshot -- check
  before assuming it exists) then
  `ROADMAP-reduce-divisor-correctness.md` then
  `ROADMAP-reducedClass-dispatcher.md` then
  `ROADMAP-alpha-to-degree-uniform.md` then
  `ROADMAP-degree-uniform-step3.md`. `ROADMAP-peel-chain-assembly.md`
  and `ROADMAP-regular-sequence.md` cover the earlier, now-closed
  regular-sequence effort. `ROADMAP-reduce-to-zerodim.md` is a
  cross-cutting audit pass that checked the others' claims against the
  code and found `ROADMAP-peel-chain-assembly.md` stale at the time (see
  that file's own "Why this document exists" section) -- read it for a
  second opinion on the others, not as a ninth independent plan.
- `CHATGPT-LOG-*.md`, `CHATGPT-REPLY-*.md` -- records of actual
  ChatGPT consultations used to unblock hard sorries, per this
  project's stated convention. Historical record, not living docs.

## For whoever reads this next

Before writing any new roadmap doc: check whether one of the eight
above already covers your question, and check the target file's own
module docstring (its last dated entry) before trusting any roadmap's
claim about that file's status. If you find another stale claim like
the `decoupledSystem_degree_uniform`/`_zeroDimensional` one above,
prefer fixing it in place (or noting it here) over writing a ninth
roadmap file that also goes stale the moment the next pass edits the
code out from under it. This file and `STATUS.md` are an attempt at a
single stable index; keep them that way rather than letting them
accumulate their own contradictory update-log sections the way the
`ROADMAP-*.md` files did -- if something here goes stale, edit it in
place.
