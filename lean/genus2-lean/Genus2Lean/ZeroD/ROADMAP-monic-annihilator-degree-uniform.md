# Roadmap: replacing `GenericPeelChainHyp.hfinrank_le` with a real bound

**Compressed, this pass.** This document had grown to ~1300 lines of
session-by-session narrative, much of it later corrected or superseded
by its own later sections. Rewritten to state only what's currently
true, with superseded reasoning cut rather than kept-and-flagged-stale
— git history has the full narrative if it's ever needed. Cross-check
against `DEGREE-BOUND-FILES-INDEX-README.md` (entries 36–70) before
trusting this document's own file list for anything beyond the
architecture-level summary below; the file index is the file-level
source of truth (per Claire's own instruction: it's updated first, this
document is downstream of it), this document is the strategy/status
layer on top.

## Why this document exists

`AlphaLocusDegreeUniform.lean`'s `decoupledSystem_degree_uniform` is
proved under `GenericPeelChainHyp`, whose `hfinrank_le` field currently
just **assumes** the `finrank` bound the theorem is supposed to
establish (`Bad := ∅` makes the existential trivially true). This
document scopes replacing that assumption with a real proof.

Separate, already-closed question, not reopened here: whether
`crossResultant_totalDegree_le`'s `hA`/`hB` hypothesis could be derived
from witness-existence machinery (`ROADMAP-crossnondegenerate-degree-
bound.md`). Settled as a structural dead end (`towerToRdec` is not a
ring homomorphism) — `hA`/`hB` is correctly a standing hypothesis, and
nothing here depends on revisiting it.

## Core strategy (unchanged since this document's first pass)

Abandon `IsSMulRegular`/witness-existence framing for this specific
goal (the project's separate regularity proof,
`regularSeq_of_peel_chain`, stays as-is — this is an alternative route
to a NUMBER). Build the bound by **iterated monic-annihilator
elimination**:

- **Core reusable fact**: if `G ∈ A[T]` is monic of degree `d` and
  `G(t) = 0` in some `A`-algebra `B`, then `finrank_k B ≤ d *
  finrank_k A` — `A[T]/(G) ↠ B`, and `A[T]/(G)` is spanned over `A` by
  `1, T, ..., T^(d-1)`. Proved: `FinrankLeOfMonicAnnihilator.lean` /
  `FinrankLeOfMonicAnnihilatorFinite.lean` (the latter also exports
  `Module.Finite B`, needed throughout — see below).
- **Per stage**: produce a monic (or normalizable-to-monic) relation
  for the newly-introduced variable over the algebra already built from
  previous stages, apply the core fact, multiply bounds via the tower
  law.
- **Per-stage hypothesis, correctly scoped**: "the eliminant's leading
  coefficient is a unit in the previous stage's algebra" — not bare
  resultant-nonvanishing (too weak to normalize to monic). Meant to
  replace `CrossNondegenerate`'s all-or-nothing framing with named,
  checkable, per-stage conditions.
- Bounds `finrank` (length) directly, so no reducedness/regularity/
  complete-intersection content is needed for the upper-bound
  direction, unlike `RegularSequenceFiniteQuotient.lean`'s existing
  `IsRegular`-based finiteness route (which gives no number).

## The twelve stages

Traced from `genList`'s literal definition (`DecoupledSystemRegular
.lean` §3–4bis) and confirmed against `PeelChainAssembly.lean`'s
12-way case split. Two structurally distinct shapes:

- **Eight matching generators** (`Fu0,Fu1,Fu2,Fu3,Fv0,Fv1,Fv2,Fv3`,
  pivoting `U0,U0,U1,U1,V0,V0,V1,V1` respectively): each is `numerator
  − t·denominator`, linear in the peeled variable `t`, monic after
  dividing by `denominator` whenever `IsUnit denominator` in the
  previous stage's algebra (`d = 1`, `LinearElimDegreeBound.lean`).
  `hv0_ext`–`hv3_ext` (the existing regularity hypotheses,
  `PeelChainAssembly.lean`) do NOT supply this — they assert
  `IsSMulRegular` of the whole evaluated linear form in the further-
  extended ring, not `IsUnit` of the isolated leading coefficient in
  the previous-stage ring. Stages 4–7 therefore need fresh `IsUnit
  (v_den i)`-shaped hypotheses, stated alongside (not replacing) the
  existing `hv_ext` fields (`LinearElimDegreeBoundExt.lean`).
- **Four curve relations** (`curveA1,curveA2,curveB1,curveB2`, e.g.
  `wa1² − f(a1)`): already literally monic, `d = 2`
  (`CurveRelationsDegreeBound.lean`).

**Genuinely NOT a clean one-pivot-per-generator triangular system**:
`U0` is pivoted by BOTH `Fu0` (a-side coefficients) and `Fu1` (b-side
coefficients) — an over-determined pair for one variable — and likewise
`U1`/`Fu2`/`Fu3`, `V0`/`Fv0`/`Fv1`, `V1`/`Fv2`/`Fv3`. Meanwhile
`wa1,wa2,wb1,wb2` are each pivoted once (by their own curve relation),
and `a1,a2,b1,b2` are NEVER a pivot of anything — they only appear as
coefficients. This shared-pivot structure (not the two-shapes
classification above) turned out to be the actual driver of the
Assembly architecture — see below.

## What "Assembly" (chaining all twelve stages into one bound on
## `Rdec p ⧸ Ideal.ofList genList`) actually needs, and why the naive
## version doesn't work

Three architectures were tried, in order; the third is the one that
worked and is being actively extended.

**1. Naive `Ideal.ofList`-prefix induction — dead end.** Chaining the
twelve per-stage lemmas by induction directly on `Ideal.ofList` prefixes
of `Rdec p` needs `Module.Finite (F p) (Rdec p ⧸ Ideal.ofList gens)` at
EVERY prefix, starting from `gens = []`, i.e. `Rdec p` itself — false,
since `Rdec p` is a 12-variable free polynomial ring, infinite-
dimensional over `F p`. `RegularSequenceFiniteQuotient.lean`'s existing
finiteness proof is a GLOBAL Krull-dimension argument needing the FULL
12-generator regular sequence at once; it neither needs nor produces
finiteness at any intermediate prefix, so this route's base case is
unreachable no matter how the twelve stages are ordered.

**2. `Fin n`/`finSuccEquiv`-indexed reindexing — fixes the base case,
but hits a different wall.** Reindex `Idx ≃ Fin 12` (`IdxEquivFin.lean`)
and induct on ARITY instead of on `Ideal.ofList` prefixes, via
`MvPolynomial.finSuccEquiv` (`FinSuccSplitPolynomialEquiv.lean`,
`FinSuccPeelChainFinrank.lean`, `FinSuccPeelChainFold.lean`): at `n = 0`,
`MvPolynomial (Fin 0) K ≃ₐ[K] K` genuinely is finite, giving a real base
case. This resolved the base-case problem but exposed a DIFFERENT one
when actually wiring `genList`'s literal generators against it
(`IdxCurveStage0Wiring.lean`): the interface advances exactly one `Fin`
slot per call, but `curveA1 = X wa1² − f(X a1)` is a relation in TWO
variables (`wa1` AND `a1`), neither separately peeled by any other
generator — there is no valid one-variable-per-step choice at the point
a curve relation needs to fire, for ANY peel order (curves-first leaves
`a1` etc. genuinely free — an infinite affine curve — at the moment the
relation fires; matching-generators-first leaves non-constant
coefficients at the moment `Fu`/`Fv` fire, the same tension the
per-stage hypothesis analysis above already found). This is a real fact
about the mathematics, not an artifact of the reindexing — confirmed
directly against `RegularSequenceFiniteQuotient.lean`'s finiteness proof
(same argument as route 1: finiteness genuinely only holds at the full
12-generator quotient, not at proper prefixes, independent of ordering).
`FinSuccPeelChainFinrank.lean`/`FinSuccPeelChainFold.lean`'s one-`Fin`-
slot-per-call machinery is not wrong, just not sufficient on its own for
this specific 12-generator system's curve-relation stages.

**3. Shared-pivot resultant elimination, over the literal
`Ideal.ofList`-prefix presentation (route 1's presentation, NOT route
2's) — the one currently being extended, and the one that resolves the
tension.** Eliminate `U0,U1,V0,V1` FIRST via their four cross-resultants
(rational functions of the 8-variable coefficient block
`wa1,wa2,wb1,wb2,a1,a2,b1,b2` alone — no `U0..V1` involved), reducing
the real content to finiteness of `F p[wa1,...,b2] ⧸ (curveA1,...,
curveB2, [4 resultant conditions])`. Once the resultants are imposed,
the four curve relations ARE a genuine one-variable-at-a-time
triangular peel (`wa1` over `{a1}`, `wa2` over `{a1,wa1,a2}`, etc.) —
the "two new variables at once" problem that broke route 2 is specific
to route 2's `Fin`-arity interface, not to the underlying mathematics:
route 1's literal-quotient presentation never needed a curve relation's
sample-point variable pre-peeled by anything, since `curveRelationGen`
evaluates `X x` symbolically in whatever ring the prefix already is
(`PeelChainStageFinite.lean`, already built for route 1 before route 2
was tried). **Order matters and is now settled: resultant/coefficient
elimination FIRST, curve relations LAST** — an earlier draft of this
document got this backwards once (`GenListTriangularReorder.lean`'s
`genListTriangular` puts curve relations first; that file is superseded
as an ordering guide, though its `Ideal.ofList_perm` transport machinery
remains independently reusable).

**Files implementing route 3, current state** (see the file index for
full per-file descriptions):

- `SharedPivotResultantElim.lean` / `...Finite.lean` — the core
  two-generator-shared-pivot lemma: given `n1 − X·d1` and `n2 − X·d2`
  both vanishing at the same `X`, bounds (and, in the `Finite` file,
  also concludes `Module.Finite`) via the classical resultant
  `n1·d2 − n2·d1` alone — no `X` involved.
- `SharedPivotStageWiring.lean` / `...Finite.lean` — wires the above to
  a literal `Ideal.ofList (gens ++ [g1, g2])` two-generator extension,
  generic over which pivot/coefficients; not yet specialized to
  `theData`'s actual `U0/U1/V0/V1` values.
- `FinrankLeOfSpanSurjective.lean` — the `finrank`/`Module.Finite`
  transport-along-a-surjection helper both shared-pivot wiring files
  need to bridge an outer resultant quotient's bound down to an
  intermediate ring's.
- `CurveRelationChainFinrank.lean` — the four-stage curve-relation
  chain, generic over an arbitrary starting prefix already known
  `Module.Finite` — meant to be called AFTER the resultant-elimination
  stage above, confirming the corrected ordering.
- **Does not exist yet**: `GenListFinrankResultantAssembly.lean`, the
  file that would chain the four resultant-elimination stages together
  with the curve-relation chain into the actual replacement for
  `GenListFinrankAssembly.lean`'s live `sorry`
  (`genList_finrank_le`, currently the one live sorry under `ZeroD/`).
  This is blocked on the deeper gap below, not on wiring effort.

**Route 2's files are not dead code, but are not the active line**:
`IdxEquivFin.lean`, `FinSuccSplitPolynomialEquiv.lean`,
`FinSuccPeelChainFinrank.lean`, `FinSuccPeelChainFold.lean`,
`RenameEquivOfListFinrankTransport.lean`, `FinSuccStageGenerators.lean`,
`IdxCurveStage0Wiring.lean`, `OptionSplitPolynomialEquiv.lean` all still
build and their content is independently true; route 3 has simply
superseded them as the path to closing `genList_finrank_le`. Don't
resume extending route 2 against curve-relation stages without first
checking whether route 3 has since closed the need.

## The actual remaining blocker: not wiring, but the right theorem
## statement

Even a fully-wired route 3 does not close `genList_finrank_le` as
currently stated, for a reason deeper than architecture. The theorem
is universally quantified over arbitrary `sa sb : SampleTarget p`, with
no `alpha`/`alpha'`/base-point `a` field connecting them. But:

- For FIXED, arbitrary targets `T_A, T_B` (no shared `alpha`/`alpha'`
  structure), the matching condition reduces to a single class-level
  equation `[D_anchorA] + [T_A] = [D_anchorB] + [T_B]` tying two
  independent degree-2-divisor parameters together — pinning only
  their DIFFERENCE, leaving one of the two (2 free parameters) genuinely
  free. **The solution locus is 2-dimensional, not 0-dimensional, for
  arbitrary fixed targets** — `finrank ≤ 16` is therefore false as a
  universal statement over `SampleTarget p × SampleTarget p`, not
  merely unproved.
- The correct statement needs `sa, sb` to come from a shared
  `SampleTargetFromAlpha`-style structure (`AlphaLocusDegreeUniform
  .lean` already has this shape), fixing `alpha`, `alpha'`, and the
  base point `a` explicitly BEFORE any finiteness bound is attempted —
  matching `ROADMAP-alpha-locus.md`'s already-recorded finding that the
  true solution variety is a 2-dimensional space of 0-dimensional
  fibers, with the 2 free dimensions being exactly `(alpha, alpha')`,
  and the 1-dimensional sub-family sharing one fixed `(alpha,alpha')`
  collapsing to a single solution (trivial copies, not genuine extra
  freedom).
- **What is genuinely still missing**: a formalizable account of WHY
  fixing `(alpha,alpha')` collapses the family to a single 0-dimensional
  fiber. `ROADMAP-alpha-locus.md` states this as a finding from
  reasoning done outside Lean, not yet formalized or its mechanism
  elucidated.

**Progress toward that missing account, this session**: a separate,
smaller sub-effort (`MatchingEquationTranslation.lean`,
`MatchingEquationDeltaInvariance.lean`, `OrbitMapConstant.lean` — see
file index entries 68–70) has started formalizing a candidate
mechanism: any two solutions of the matching equation differ by a
common translation `Δ` (entry 68); the equation, and hence its solution
set, depends on `(alpha,alpha')` only through `delta = alpha − alpha'`
(entry 70); and a connected group acting on a 0-dimensional target via
an algebraic orbit map must act trivially, i.e. `Δ = 0` (entry 69's
general-topology core, hypotheses not yet instantiated). **Not yet
wired into this roadmap's actual goal, and entry 70 states its own
caveat plainly**: `alpha • a` for `alpha : ℤ` only sweeps out the
cyclic subgroup `AddSubgroup.zmultiples a`, not all of `Jacobian H D`,
so constructing `G(Δ)` for an ARBITRARY `Δ ∈ Jacobian H D` (needed for
the full argument) is a separate fact about the `Reduce`/Mumford
construction, not established by any of these three files. Until that
account exists in usable form, `genList_finrank_le` cannot be correctly
restated, let alone proved — route 3's resultant-elimination machinery
above is still expected to be the right LOCAL per-fiber tool once the
statement is corrected to fix `(alpha,alpha')` first, but this has not
been re-examined under the corrected statement.

## `Bad`/exceptional-set sizing — still open, blocked on the above

Per-stage unit conditions that depend on `(alpha,alpha')` JOINTLY give
`Bad` of size `O(D·p)` (Schwartz–Zippel); conditions that split into
separate `alpha`-only/`alpha'`-only pieces give the cheaper `O(D)`.
Undecided: depends on what `v_den i` (and the shared-pivot resultants)
actually look like as symbolic expressions in `(c0,...,c4,alpha,
alpha')` — not yet examined, and likely not worth examining before the
statement-correction gap above is resolved, since `Bad`'s definition
itself may need to change once `sa,sb` are properly linked via
`SampleTargetFromAlpha`.

## Next concrete steps, in order

1. Resolve the statement-correction gap: work out (on paper or via a
   ChatGPT consult, then formalize) why fixing `(alpha,alpha')`
   collapses the fiber, building on entries 68–70's partial mechanism
   and its `zmultiples a` caveat.
2. Once resolved, restate `genList_finrank_le` (or its replacement)
   over `SampleTargetFromAlpha`-linked `sa, sb` with fixed
   `alpha, alpha'`.
3. Write `GenListFinrankResultantAssembly.lean`, chaining route 3's
   already-built resultant-elimination + curve-relation stages against
   the corrected per-fiber statement.
4. Revisit `Bad` sizing now that the corrected statement pins down what
   `Bad` actually needs to range over.
5. Replace `GenericPeelChainHyp` in `AlphaLocusDegreeUniform.lean` with
   the proved pieces (delete the hypothesis bundle, or narrow it,
   dropping `hfinrank_le` specifically), per `ROADMAP-degree-uniform-
   step3.md`'s existing instruction.
