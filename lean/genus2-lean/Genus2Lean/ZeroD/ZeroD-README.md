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

**This contradicted several `ROADMAP-*.md` files in this directory**
(now fixed, see "Known stale claims" in `STATUS.md` and the correction
notice at the top of `ROADMAP-alpha-locus.md`), which described
`decoupledSystem_degree_uniform` and `decoupledSystem_zeroDimensional`
as still-open `sorry`s. As of this pass, Claire confirms the whole
project builds green. **But "sorry-free and builds green" is not the
same as "proved."** `decoupledSystem_degree_uniform` closes via a
hypothesis bundle, `GenericPeelChainHyp`, whose `hfinrank_le` field
states the uniform degree bound *itself* as an assumption (with
`Bad := ∅`) -- the theorem typechecks by assuming its own conclusion.
This is a genuinely circular closure, not an honest weakening in the
style of this project's other hypothesis bundles (`Nondegenerate`,
which names concrete checkable coefficient conditions, is fine;
`hfinrank_le`, which just restates the goal, is not). See
`ROADMAP-degree-uniform-step3.md` (rewritten this pass) for the
corrected breakdown of what's actually still open, and read on for the
real open risk this surfaced.

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

Distilled from `ROADMAP-alpha-locus.md` (status-corrected this pass) and
`ROADMAP-degree-uniform-step3.md` (rewritten this pass) -- read those
directly for the full argument, this is a pointer, not a replacement.
**Ranked by actual risk, not by document order** -- earlier drafts of
this list ranked `GenericPeelChainHyp` and `Reduce` as comparable
unknowns; they are not. `Reduce` is in good shape. The real open risk is
item 1:

1. **Attempt the degree bound for `CrossNondegenerate`/
   `PeelChainNondegenerate` directly — this is the actual next work, not
   an unmeasured risk requiring more numerics.** This condition's own
   docstring in `DecoupledSystemRegular.lean` says, in Claire's own
   words: "expected to be FALSE for at least some, quite possibly most,
   choices of `(c0,...,c4)`" -- found via a genuine counterexample shape
   during a ChatGPT-assisted debugging session, not a hedge. This is a
   cross-sample resultant regularity condition. **Update, this pass**:
   two independent numerical checks have been run on one fixed curve,
   several `(alpha,alpha')` pairs -- (1) a direct resultant solve down
   to the U,V resultants with two random `P`'s plugged in, no visible
   solution (consistent with dimension ≤1), and (2) a separate
   `HomotopyContinuation.jl` run, 0-dimensional with witness points
   missing/dropped, consistent across re-runs. **These agree.**
   **Corrected framing, this pass**: an earlier version of this
   document treated a further numerical sweep across *multiple curves*
   as the necessary next step before a degree bound could be attempted.
   Per Claire, that's the wrong lens -- the peel-chain construction is a
   fixed, finite sequence of algebraic operations, so this is a
   bounded-degree resultant condition directly amenable to
   Sylvester-matrix-style degree counting on `uRS`/`vRS`'s own known
   degrees (the same style of argument that already fully characterized
   `MatrixNondegenerate`'s `det(A)`), not something requiring
   cross-curve empirical screening to understand. `alpha`/`alpha'`
   draws aren't expected to matter except at `alpha ≡ alpha' (mod
   ell)`, which `Bad` already exists to exclude. **The actual next
   step is to attempt the degree bound directly** -- see
   `ROADMAP-degree-uniform-step3.md`'s rewritten Obligation 2/3 sections
   for the corrected plan (fold Obligation 2 into Obligation 3: prove
   the bound, and let the specific per-stage nonvanishing conditions
   fall out of that proof as named, checkable hypotheses). This is
   still the single highest-priority next action in the whole
   subsystem, higher priority than any further numerical work.

   **Update, later pass**: `CrossNondegenerateDegreeBound.lean` (new file)
   closes the first concrete piece of this -- `crossResultant_totalDegree_le`/
   `crossResultantV_totalDegree_le`, REPL-confirmed green, bound all four of
   `CrossNondegenerate`'s resultants by `4*D+2` given a base-case bound `D`
   on `uRS`/`vRS`'s coefficients, conditional on `D` as a hypothesis.

   **Update, later pass -- the `/ₘ`-chain gap is CLOSED, read this before
   trusting the paragraph above**: `curBeforeMonic_coeff_totalDegree_le`
   (`CurBeforeMonicCoeffTotalDegree.lean`) is REPL-confirmed green and gives
   a concrete `≤315448` bound on `curBeforeMonic.coeff {0,1,2}` -- the three
   nested-`/ₘ` obstacle the paragraph above describes is resolved (via the
   exact-multiplication-identity route, `Npoly = curBeforeMonic * Q`, a
   triangular coefficient system solved top-down, no division-coefficient
   lemma needed after all). **If you are reading this file to figure out
   what to do next, the "pin down `D`" framing above is STALE -- do not
   re-attempt it.** The actual remaining gap is one level higher: that
   bound is stated via `IsRdecWitness` (an existential witness), while
   `crossResultant_totalDegree_le`/`crossResultantV_totalDegree_le` need
   the literal `towerToRdec`-COMPUTED pair bounded -- two different
   strengths (a witness bound never implies a computed-pair bound, since
   witnesses aren't unique). `URSCoeffIsRdecWitness.lean` (new file, later
   pass still) closes half of this -- `uRS.coeff i`'s own `IsRdecWitness`
   bound (`≤630896`), via `IsRdecWitness.div`'s witness-swap trick for the
   `leadingCoeff⁻¹` factor -- but has NOT yet been REPL-confirmed (three
   build errors already found and fixed one round; awaiting a fresh test).
   **The real single next action**: rewrite `crossResultant_totalDegree_le`/
   `crossResultantV_totalDegree_le` themselves to conclude in `IsRdecWitness`
   form (losing nothing real -- `CrossNondegenerate`'s downstream
   `IsSMulRegular` argument only needs the resultant's zero/nonzero status,
   never a canonical representation), then plug in `URSCoeffIsRdecWitness.
   **Update, latest pass -- `URSCoeffIsRdecWitness.lean` REPL-confirmed
   green, but the "rewrite in `IsRdecWitness` form" plan above is WRONG,
   corrected here**: checked `CrossNondegenerate`'s own definition directly
   (`DecoupledSystemRegular.lean` ~line 1992) this pass -- its `hu0`/`hu1`/
   `hv0`/`hv1` fields state `IsSMulRegular` on `theData`'s LITERAL
   `u1_num`/`u1_den`/etc. fields (`= towerToRdec p sg (uRS.coeff i)`'s
   literal `.1`/`.2`), used directly as `MvPolynomial` ring elements inside
   an actual quotient ring `Rdec p ⧸ ⟨Fu0⟩`. `IsRdecWitness`'s existential
   (`∃ nd, evalNd nd.1 = evalNd nd.2 * ι v`) does NOT claim `nd` equals
   `towerToRdec`'s own computed pair -- witnesses for the same value aren't
   unique (`(n*k,d*k)` also witnesses for any `k`) -- so an `IsRdecWitness`-
   shaped bound on "some witness for the resultant" cannot be substituted
   for `IsSMulRegular` on the SPECIFIC `theData`-computed resultant; the
   substitution problem just reappears one level up, on a property
   (`IsSMulRegular`) that's arguably harder to restate generically than
   `totalDegree` was. **The actual right next step, per direct inspection
   this pass, not superseded speculation**: bound `towerToRdec`'s own
   recursive formula directly (it already has exactly this shape of lemma,
   `towerToRdecK1_totalDegree_le`/`towerToRdec_totalDegree_le` in
   `DataDerivationTotalDegree.lean`, for an arbitrary opaque `K2`-element
   input) -- the missing piece is tracing what `totalDegree`-shaped fact
   about `curBeforeMonic.coeff i` (NOT the `IsRdecWitness` existential
   bound already proved) those lemmas' own hypotheses actually need.

   **Update, later pass -- traced precisely, prompt actually written this
   time.** `crossResultant_totalDegree_le`/`crossResultantV_totalDegree_le`
   (`CrossNondegenerateDegreeBound.lean`, the theorem this whole chain feeds)
   ARE already stated against the literal `towerToRdec_coeff_totalDegree_le`
   shape, not `IsRdecWitness` -- their `hA`/`hB` hypotheses want a literal
   bound on `towerToRdecK1`'s output for `uRS.coeff i`'s two `K1`-extracted
   children, exactly what `towerToRdec_coeff_totalDegree_le` needs as input.
   Nothing currently supplies `hA`/`hB`: `uRS_coeff_isRdecWitness`'s
   existential-witness bound is a different, weaker fact, and there is no
   direct route from one to the other without knowing how a witness pair
   relates to `towerToRdec`'s own (possibly differently-reduced) computed
   pair. `chatgpt_prompt_literal_towertordec_bound.md` (`Genus2Lean/` top
   level, written this pass -- the earlier-named `chatgpt_prompt_
   isrdecwitness_to_concrete_bound.md` was never actually written to disk
   despite an earlier pass's claim otherwise; don't go looking for it)
   asks whether `exists_reduced_factors'` can bridge the two. Not yet
   sent/resolved. See `ROADMAP-crossnondegenerate-degree-bound.md`'s final
   two "Update" sections for the full trace.

   **Update, latest pass**: `AlgebraMapFpLiteralTotalDegree.lean` (new file)
   closes the `gu0`/`gu1` half of the literal-`towerToRdec` route the
   previous update above was chasing, but its own closing note correctly
   identifies that route as a dead end for `hA`/`hB` regardless --
   `towerToRdec` is not a ring homomorphism, so no amount of literal
   per-generator bounds composes into a literal bound on `curBeforeMonic.
   coeff i` (an arithmetic combination of those generators). Per that
   file's own redirection, `CrossResultantIsRdecWitness.lean` (new file,
   REPL-confirmed green) instead proves `uResultant_isRdecWitness`/
   `vResultant_isRdecWitness`: the LITERAL `theData`-computed resultant
   element (`u1_den i * u2_num i - u2_den i * u1_num i`, the exact `Rdec p`
   element `CrossNondegenerate`'s `hu0`/etc. state `IsSMulRegular`-ness
   about) is an honest `IsRdecWitness` witness numerator for `uRS_B.coeff i
   - uRS_A.coeff i` (resp. `vRS`), built directly from two
   `towerToRdec_isRdecWitness` applications (already proved,
   unconditional) via `.neg` -- no reshaping of the existing `≤630896`/
   `≤315448` existential bounds, no attempt to bound `towerToRdecK1`'s own
   recursive formula. **Read this precisely, don't over-credit it**: this
   does NOT discharge `hA`/`hB` -- those still want a `totalDegree` bound on
   a strictly deeper quantity (`towerToRdecK1`'s intermediate output) that
   `IsRdecWitness` carries no information about at all (it is a bare
   cross-multiplied equation, no degree content). `hA`/`hB` remain exactly
   as open as the update above left them. What this DOES do: it is the
   concrete witness-shaped resultant statement that `AlgebraMapFpLiteralTotalDegree.lean`'s
   own closing note flagged as needing an `IsSMulRegular`-transfer-between-
   witnesses lemma before it could be used for anything -- that transfer
   question (does `IsSMulRegular` on one witness of a value imply it on
   another witness of the same value?) is now the concrete next thing to
   attempt, against these two theorems specifically, rather than a further
   detour into `hA`/`hB`'s own degree-bound chain.

   **Major update, not yet formalized anywhere -- flagged here first,
   NOT yet reflected in `ROADMAP-alpha-locus.md`/`ROADMAP-degree-uniform-
   step3.md`'s own text (both still describe the plain "0-dimensional"
   picture above; read this note as superseding, not replacing, that
   text until those files are updated in place).** A chain of reasoning
   (outside Lean, not yet written up as its own document) shows the
   solution variety is NOT simply 0-dimensional in the naive sense both
   numerical checks above were reading it as -- it is a **2-dimensional
   space of 0-dimensional fibers**, where the whole 1-dimensional
   sub-family of fibers sharing a fixed `(alpha,alpha')` all carry the
   SAME solution (i.e. that 1D direction is foliated by trivial copies
   of one fiber's solution set, not by genuinely varying solutions).
   Consequence for the actual complexity target: this is **the best-case
   scenario**, not a setback -- the trivial-copy direction collapses to a
   single relation, so the uniform degree bound this whole subsystem is
   chasing (`decoupledSystem_degree_uniform`, closing advisory-6/7's
   `p^(4/5)` Question-4 gap) is still very much alive, and if anything
   this structure is more tractable to formalize than a genuinely
   2-dimensional family would be (one fiber's degree bound, plus "the
   other fibers are copies," rather than a uniform bound needing to hold
   across a truly 2-parameter family). **This has not been elucidated or
   formalized in Lean yet** -- no `.lean` file states or uses this fact,
   and the two numerical checks documented above (resultant solve,
   `HomotopyContinuation.jl`) were run and interpreted before this
   finding, so their "0-dimensional, witness points missing/dropped"
   read is consistent with but does not by itself establish the sharper
   2D-fibers-with-collapsing-copies picture. Formalizing this (stating
   the 2D/1D-collapse structure precisely, then re-deriving the degree
   bound through it) is now part of item 1's real scope, not a separate
   item -- update this note in place once that formalization starts,
   rather than letting this become a ninth stale claim for a future pass
   to untangle.

   **The actual mechanism behind "1D collapses to trivial copies"
   (worked out this pass, chat only, not yet Lean) -- a corollary OF the
   degree bound, not a separate thing to prove first, and downstream of
   it, so it does not compete with item 1 for priority.** The equation,
   un-reduced, is `P1+P2-P3-P4 = (alpha-alpha')*a` (working in the
   `p^2`-size subgroup `⟨a⟩`, so everything IS a multiple of `a` -- this
   is the "1D family" itself, parametrized by the shared value
   `alpha-alpha' = const`). Given any two solutions `(P1,P2,P3,P4)`,
   `(P1',P2',P3',P4')` of the SAME instance (fixed `alpha,alpha'`,
   hence fixed RHS), defining `Delta := (P1+P2)-(P1'+P2')` and
   subtracting the two instances of the equation gives, for free (no
   gap, pure linearity): `(P3+P4)-(P3'+P4') = Delta` too -- i.e.
   `Delta`-translation maps one solution to another solution of the
   SAME instance. Since (once `decoupledSystem_degree_uniform` is
   proved) the solution set `S` for that instance is finite, `O(1)`
   size `d`, `Delta`-translation is an invertible self-map of `S`, i.e.
   `Delta`-translation is a **permutation of a `d`-element set**, for
   EVERY valid `Delta` in the shared-shift family. **The family of valid
   `Delta`'s scales with `p`** (roughly `O(p)`/`O(p^2)`, not literally
   the whole field, but growing with `p`; `d` does NOT grow with `p` --
   that is exactly the "uniform" in `decoupledSystem_degree_uniform`).
   A family of size `~p` mapping into `Sym(S)`, `|Sym(S)| = d!` FIXED,
   cannot inject once `p > d!` -- pigeonhole, not "only finitely many
   permutations exist" (that part of an earlier draft of this note, chat
   only, was for an infinite-field version and is WRONG here; over
   `F_p` the family of `Delta`'s is itself finite, just growing with
   `p`, so the argument has to be pigeonhole-on-a-growing-family-vs-a-
   fixed-target, not counting-permutations-of-an-infinite-family). Once
   `p` is large enough (`p > d!`, or whatever the precise bound works
   out to), MOST `Delta`'s in the family must act as the IDENTITY on
   `S` (two distinct `Delta`'s inducing the same permutation, by
   pigeonhole, and composing -- their difference then fixes `S`
   pointwise, and this can be pushed to show a positive-density/generic
   subfamily fixes `S` entirely) -- that is the actual "1D direction
   foliated by trivial copies" mechanism, made precise. **This is the
   real risk this note exists to flag, in Claire's own words**: the
   `alpha-alpha'=const` family is large and if it acted nontrivially
   AND transitively on the `O(1)` solution set instead of generically
   trivially, the `E(S,S)` counting argument (`B^4 = sum_Delta X(Delta)
   <= d*#{Delta : X(Delta)>0}`, `ZeroD-README.md`'s own summary above)
   would break, since that counting step implicitly needs each `Delta`
   to correspond to essentially one solution-copy, not a nontrivially-
   shuffled orbit. The pigeonhole fix handles this ONLY once `p` is
   large relative to `d` -- `p > d!` (or a sharper bound) needs to
   become an explicit, tracked hypothesis wherever this gets formalized,
   not silently assumed. **Not yet stated or proved in Lean; this is a
   corollary to attempt once `decoupledSystem_degree_uniform` itself is
   proved (needs `d` in hand first), not before.**

2. **`decoupledSystem_degree_uniform`'s current proof is circular and
   needs to be redone, not just re-verified.** It currently closes via
   `GenericPeelChainHyp`, a hypothesis bundle whose `hfinrank_le` field
   states the uniform bound itself as an assumption (`Bad := ∅`
   witnesses the existential). This is not a "weakened but honest"
   hypothesis in the style of `Nondegenerate` -- it's the goal restated
   as its own premise. Item 1's degree-bound work is exactly what
   resolves this: once the bound is proved, `GenericPeelChainHyp` gets
   replaced with the actual proved pieces (or a strictly narrower
   bundle, dropping `hfinrank_le`). See `ROADMAP-degree-uniform-step3.md`'s
   three-obligation breakdown for the full plan, and do not let a future
   pass re-collapse these back into one bundle.
3. **`htop_ne_smul` (solution existence -- the 12-generator ideal is
   proper) is unproved but likely tractable**, and doesn't depend on
   item 1's outcome -- reasonable to attempt in parallel. **Correction,
   later pass**: it depends on item 1's outcome MORE than this line
   suggests -- `MvPolynomialSharedTargetSolve.lean` (new file) found that
   `FuList`/`FvList`'s two generators per target variable can only be
   solved simultaneously at a point where the corresponding
   `CrossNondegenerate` resultant vanishes, so `htop_ne_smul`'s own
   witness point needs the resultant to vanish there specifically (a
   strictly weaker, checkable, per-point fact than full `IsSMulRegular`,
   but a real dependency, not zero). See
   `ROADMAP-degree-uniform-step3.md`'s Obligation 1 section (rewritten
   later pass) for the corrected account.
4. **`Reduce` (`ReduceDispatchGeneral`, `Reduce/GeneralSharedRoot.lean`)
   is in good shape, not a live risk.** Proved correct at the polynomial
   level (`v^2 = f mod u`, the Mumford congruence), and
   `reducedClass_eq_of_isReduction'` plus its six case-split siblings
   (connecting that to the actual divisor-class/group-law semantics) are
   sorry-free. Worth a REPL re-confirmation if you're about to build
   directly on top of it, but this is not where the project's risk sits.
5. **No dispatcher exists yet above `ReducedClassDispatch.lean`'s own
   level** that would take a bare "these two points collided" fact and
   route to the right one of the 7 theorem variants automatically from
   first principles -- `ReducedClassDispatch.lean` dispatches, but
   something still has to hand it pre-classified case data. Low priority
   relative to items 1-3.

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
- `CrossNondegenerateDegreeBound.lean` -- `crossResultant_totalDegree_le`/
  `crossResultantV_totalDegree_le`, conditional on an unmet `hA`/`hB`
  hypothesis; `CrossResultantIsRdecWitness.lean` -- a separate, genuinely
  weaker honest fact (`uResultant_isRdecWitness`/`vResultant_isRdecWitness`,
  `IsRdecWitness` not `totalDegree`) about the same literal resultant
  elements, REPL-confirmed green, does NOT discharge the other file's
  `hA`/`hB` -- see item 1's latest "Update" above before assuming either
  closes the other.
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
