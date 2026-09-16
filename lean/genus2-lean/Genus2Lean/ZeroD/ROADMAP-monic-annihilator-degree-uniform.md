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

**1. Naive `Ideal.ofList`-prefix induction — corrected, not abandoned.**
An earlier pass of this document treated this route as a dead end,
reasoning that chaining the twelve per-stage lemmas needs
`Module.Finite (F p) (Rdec p ⧸ Ideal.ofList gens)` re-derived
independently at EVERY prefix, starting from `gens = []`, i.e.
`Rdec p` itself — false, since `Rdec p` is a 12-variable free polynomial
ring, infinite-dimensional over `F p`. **That diagnosis was wrong about
which invariant the induction actually needs, confirmed via a ChatGPT
consult (this pass) and cross-checked directly against this codebase's
own already-correct fix**: `finrank_le_of_monic_annihilator`
(`FinrankLeOfMonicAnnihilator.lean`) does not require its base ring `A`
to be independently re-established finite at each stage from some
global argument — it takes `[Module.Finite k A]` as an ordinary
hypothesis and *produces* `Module.Finite k B` on the extended ring as
part of its own proof (via `Module.Finite.trans A (AdjoinRoot G)`,
documented explicitly in that file). The correct induction invariant is
therefore "`A` is finite over `k` of SOME rank, threaded forward stage
by stage from the genuinely-true base case `Module.Finite k k`
(rank 1)" — never "`A` is finite over `k`" asserted as a standalone fact
about an intermediate polynomial quotient in isolation, and never a
claim that any intermediate prefix has a FIXED, predetermined finrank
before the chain reaches it. `FinrankLeOfMonicAnnihilatorFinite.lean`
and `PeelChainStageFinite.lean` already implement exactly this
forward-threading fix (their docstrings independently reach the same
diagnosis this consult reached). So route 1's ARCHITECTURE — inducting
directly on literal `Ideal.ofList` prefixes, never leaving that
presentation for an `Option`/`Fin`-indexed tower — was always sound;
only the base-case reasoning in this document's earlier pass, and in
one still-unfixed downstream file (see below), stated the wrong
invariant. `RegularSequenceFiniteQuotient.lean`'s existing finiteness
proof (a GLOBAL Krull-dimension argument needing the FULL 12-generator
regular sequence at once) is unrelated to this fix and still gives no
intermediate-prefix finiteness of its own — it simply isn't needed for
this route once the invariant above is used instead.

**Stale file flagged by this correction**: `GenListFinrankAssembly.lean`
(route (a)'s superseded 12-sequential-application attempt at Assembly,
predating route 3's shared-pivot reordering below) still narrates the
OLD, incorrect base-case reasoning in its own docstring — literally
stating `Module.Finite (F p) (Rdec p ⧸ Ideal.ofList [])` reduces to
`Module.Finite (F p) (Rdec p)` and calling this a blocking gap, without
noting that `PeelChainStageFinite.lean`'s forward-threading fix (already
present elsewhere in this same codebase) resolves it. That file's
`genList_finrank_le` is the one live `sorry` under `ZeroD/` and should
either be rewritten to use the corrected invariant directly, or (more in
line with "Next concrete steps" below) left as dead-code-in-place and
superseded outright by route 3's own assembly file once written — do
not treat its docstring's base-case caveat as a still-open problem when
picking this up again.

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

**Progress toward that missing account, this session — CORRECTED, the
orbit/connectedness route is a dead end, not a hard-but-right approach.**
A separate, smaller sub-effort (`MatchingEquationTranslation.lean`,
`MatchingEquationDeltaInvariance.lean`, `OrbitMapConstant.lean` — see
file index entries 68–70) built toward a candidate mechanism: any two
solutions of the matching equation differ by a common translation `Δ`
(entry 68, proved, stays valid); the equation depends on `(alpha,
alpha')` only through `delta = alpha − alpha'` (entry 70, proved, stays
valid); and — this was the candidate closing step — a connected group
acting on a 0-dimensional target via an algebraic orbit map must act
trivially, forcing `Δ = 0` (entry 69's general-topology core).

**A ChatGPT consult this pass identified that the closing step is
mathematically wrong, not merely unformalized, for two independent
reasons — do not pursue it further:**

1. The set `D = {Δ ∈ J : some two solutions differ by Δ}` is NOT shown
   to be a subgroup, and isn't one from what's proved: `0 ∈ D` and
   `D = -D` are free, but `Δ, Γ ∈ D ⟹ Δ + Γ ∈ D` needs an actual group
   action `T_Δ` on the WHOLE solution set with `T_Δ ∘ T_Γ = T_{Δ+Γ}`,
   which a single witnessed pair of solutions does not supply. Worse,
   the raw Jacobian equation `A − B = δ·a` (with `A = [P1]+[P2]`,
   `B = [P3]+[P4]`) is satisfied by a positive-dimensional family of
   `(A,B)` on its own — genus 2 makes the Abel map `Sym²C → Pic²(C)`
   surjective, so for essentially any `A` some `B` exists — meaning
   **the Jacobian equation alone cannot possibly force `Δ = 0`; all of
   the rigidity has to come from the SampleTarget polynomial equations
   themselves**, which the orbit-map framing never used.
2. Separately, no algebraic `J`-action on the fixed-`delta` solution set
   was ever constructed (translating a degree-2 divisor by an arbitrary
   `Δ` doesn't canonically land back in the SampleTarget locus or
   preserve the fiber), so `OrbitMapConstant.lean`'s
   `PreconnectedSpace`/`DiscreteTopology` machinery has nothing to apply
   to even setting the first issue aside — and over a finite base field,
   `J`'s own point group is finite/torsion-heavy, so "constant on a
   finite orbit" would prove nothing useful even if the action existed.

**The corrected target, per that consult, and the one to actually
pursue**: stop trying to prove `Δ = 0` inside the abstract Jacobian.
Instead strengthen the existing 0-dimensional result
(`decoupledSystem_zeroDimensional`, i.e. `finrank ≤ 16` at the ring
level for one fixed `(sa,sb)`) to a **degree-1 / uniqueness** statement
about the polynomial system itself:

- **0-dimensional is not enough** — a 0-dimensional fiber can have
  anywhere from 1 to 16 (or however many) geometric points, and knowing
  a translation relation holds between two of them says nothing about
  whether they coincide. This is a hard logical gap, not a formalization
  gap: `finrank ≤ 16` and `Δ = 0` are different strengths of claim, and
  the former was never going to imply the latter.
- **The right statement**: introduce a SECOND copy of the 12 SampleTarget
  variables `x'`, impose the SAME ideal `I_δ` on both `x` and `x'`
  (i.e. both solve the fixed-`delta` system), and prove `x = x'`
  (coordinatewise) follows — using exactly the triangular/monic
  elimination structure route 3 already builds (shared-pivot resultant
  elimination for `U0,U1,V0,V1`, then the 4 curve relations), just run
  in "pairwise agreement" form rather than "bounded finrank" form: at
  each stage, if `x` and `x'` agree on all previously-eliminated
  coordinates and both satisfy the same monic/linear relation for the
  next coordinate with the same coefficients, the two values of that
  next coordinate agree too (immediate for a linear relation with a
  shared unit leading coefficient; for the degree-2 curve relations,
  needs the curve to not have both square roots coincide — likely an
  easy nondegeneracy side-condition, not yet checked). Once `x = x'`,
  `A(x) = A(x')` and `B(x) = B(x')` follow directly, giving `Δ = 0` via
  the already-proved `matching_solutions_translate_by_delta` — so entry
  68's translation fact is NOT wasted, only entry 69/70's connectedness
  closing step is discarded.
- **Do not build a Zariski topology on `Jacobian H D` or attempt to
  prove it connected** — confirmed by the consult as unnecessary for
  this argument (and would be substantial, out-of-scope work with
  nothing here to actually use it for). `OrbitMapConstant.lean` can stay
  in the codebase as an independently-true, currently-unused general
  topology fact, but is not on the path to closing this gap.
- This pairwise-agreement statement is a strictly better fit for the
  codebase's existing machinery than the abandoned orbit approach: it's
  a direct strengthening of the SAME triangular-elimination stages route
  3 already has (`SharedPivotResultantElim*.lean`,
  `CurveRelationChainFinrank.lean`), rather than a wholly separate
  topological development.

**Restated remaining task**: prove, for two tuples `x, x'` both
satisfying `genList`'s twelve equations at the same `(alpha, alpha')`
(equivalently, both giving valid `SampleTargetFromAlpha p H D aClass
δ₀` structures with the same `alpha, alpha'`), that `x = x'`
coordinatewise, via the same 12-stage elimination order route 3 already
uses. This is likely EASIER to formalize than the `finrank ≤ 16` bound
itself (pairwise agreement per stage is a smaller inductive claim than
counting a full spanning set), and directly gives `genList_finrank_le`
as a corollary once stated over `SampleTargetFromAlpha`-linked `sa, sb`
(a 0-dimensional fiber that's additionally a single point has `finrank`
equal to its own field-extension degree at that point, ≤ the same
per-stage product bound route 3's `finrank` machinery already
establishes at the ring level — so the two threads combine rather than
compete).

## Step 1 (pairwise agreement), current state

`PeelChainPairwiseAgreement.lean` formalizes the abstract per-stage half
of step 1, mirroring `LinearElimDegreeBound.lean`/
`CurveRelationsDegreeBound.lean`'s exact per-stage split:

- **Linear stages (`Fu0`–`Fu3`, `Fv0`–`Fv3`) — DONE, unconditional.**
  `linearElim_forces_eq` (pulled out of `SharedPivotResultantElim.lean`'s
  own inline `htval` computation as a standalone reusable fact — that
  file's proof is untouched, still green, this is purely additive) shows
  a linear-elimination relation forces its variable to a single value
  `d⁻¹ * c`; `linearElim_pairwise_eq` concludes two solutions of the SAME
  relation agree, with no side hypothesis at all.
- **Curve-relation stages (`curveA1`,...,`curveB2`) — genuinely needs a
  side condition, correctly flagged rather than assumed.**
  `curveRelation_sq_sub_sq_eq_zero` shows two roots `t, t'` of the same
  `X² = f` satisfy `(t-t')(t+t') = 0` unconditionally; closing this to
  `t = t'` needs ruling out the `t = -t'` branch, done in
  `curveRelation_forces_eq` via an explicit `t ≠ -t'` hypothesis (plus
  `IsDomain B`, needed for `mul_eq_zero`'s two-branch split).

`PeelChainPairwiseAgreementWiring.lean` (new this pass) specializes both
facts against `genList`'s literal `linearElimGen`/`curveRelationGen`
shapes (`LinearElimStageWiring.lean`/`CurveRelationStageWiring.lean`'s
own conventions), and settles — negatively — the open question the
previous pass left about the curve-relation side condition:

- **Confirmed by direct inspection, not merely still-unresolved: there
  is NO sign convention anywhere in `theData`'s symbolic algebra pinning
  `wa1`/`wa2`/`wb1`/`wb2` to one square root over the other.**
  `SampleTarget` (`DecoupledSystemRegular.lean`) carries only
  `u0,u1,v0,v1` — no `w`-fields at all — and each `curveA1 = wa1'² −
  f(a1')`-shaped relation is the ONLY place `wa1` appears anywhere in
  `Rdec p`'s free-polynomial presentation. So `wa1` and `-wa1` are
  genuinely interchangeable in this symbolic system; the earlier guess
  that a Mumford-coordinate sign convention would resolve this for free
  does not hold at the level this project's `Rdec p` presentation lives
  at. `curveRelation_forces_eq`'s `t ≠ -t'` hypothesis is stated
  explicitly at each of the four curve-relation call sites in the new
  wiring file, not derived — the honest per-stage condition the roadmap's
  Core Strategy always asked for, now confirmed to need an outside input
  rather than being free.
- **Option (a), chased and closed off — no sign convention exists to
  find.** Traced `H.Point` (`AffinePoints.lean`), `SampleTargetFromAlpha`
  (`P1 P2 : H.Point` are genuinely free structure fields, not derived),
  `Reduce`/`ReduceDispatch` (`Reduce/AlphaReduce.lean`, fully built and
  `sorry`-free, but a function OF `P1,P2` — it can't retroactively pin
  which root was "meant"), and `reducedClass_eq_of_isReduction'`
  (`ReducedClassBundles.lean`, also `sorry`-free) end to end. None of
  these fix `wa1`'s sign relative to anything external; the ambiguity is
  real geometry (choice of which of the two points in a fiber `{P, ιP}`
  is "the" point), not a Lean gap. Option (a) is closed: there is
  nothing to find.
- **Option (b), attempted then corrected via ChatGPT consult
  (transcript, this pass) — the naive "16 sign patterns" framing was
  WRONG, not just unproven.** The standard hyperelliptic fact, confirmed
  against Mumford's *Tata Lectures on Theta II* (ch. IIIa §1): for the
  odd-degree model with basepoint `∞`, **`[P] + [ι(P)] = 0` in `J` for
  EVERY `P`** (including Weierstrass points, via `2[W]=0` there — no
  exceptional case), so `[ι(P)] = -[P]`. Consequently, flipping a subset
  `S ⊆ {1,2,3,4}` of the four points to their `ι`-images changes the
  matching-equation LHS by `-2·Σ_{i∈S} ε_i[P_i]` (`ε_i = +1` for
  `i∈{1,2}`, `−1` for `i∈{3,4}`), so the flip preserves `Δ` **iff
  `2·Σ_{i∈S} ε_i[P_i] = 0`** — a genuine arithmetic condition on rational
  2-torsion in `J(𝔽_p)`, not automatic. Most of the naive "16 patterns"
  do NOT satisfy the matching equation in general; asserting "unique up
  to 16 sign patterns [each satisfying the matching equation]" would
  have been false, not merely a weaker true statement. **Option (b) as
  originally framed is dead — do not resurrect the flat 16-pattern
  claim.**
- **What IS true and useful, salvaged from the same consult — the actual
  target now**: the elimination argument already gives
  x-coordinate/fiber-level uniqueness, independent of the 2-torsion
  question above: `P_i' = P_i ∨ P_i' = ι(P_i)` for each `i`, equivalently
  `{x(P1),...,x(P4)} = {x(P1'),...,x(P4')}`. This is real, standalone
  content (proved by `curveRelation_forces_eq_up_to_sign` /
  `curveChain_pairwise_eq_up_to_sign`, already written this pass in
  `PeelChainPairwiseAgreement*.lean` — keep these files, they're correct
  and needed, just retarget their downstream use away from the dead
  16-pattern framing) — it does NOT by itself give `Δ = 0` or resolve
  which of the `2^4` sign patterns actually holds; that needs either (i)
  a separate non-degeneracy input ruling out 2-torsion coincidences among
  `[P1],...,[P4]` under the specific `(alpha,alpha')` targets in play, or
  (ii) restating the ultimate goal at the fiber level (x-coordinates
  only) rather than chasing `Δ = 0` pointwise. Neither (i) nor (ii) is
  chosen yet.
- The linear-stage wiring (`linearElim_ofList_pairwise_eq`) has no such
  gap — it is unconditional, matching the abstract lemma.

**Not yet done, still needed for step 1 to be complete**: decide between
(i)/(ii) above for the curve-relation stages, then chain all twelve
stages' pairwise-agreement facts (now all wired against `genList`'s
literal generators) into one statement at whichever strength (i)/(ii)
lands on — the pairwise-agreement analogue of
`GenListFinrankResultantAssembly.lean`'s own not-yet-finished chaining
(that file, discovered already partially-built this pass, closes the
SEPARATE `finrank ≤ 16` numeric bound via route 3's curve-then-shared-
pivot order; it does not address pairwise agreement and is not modified
by this work).

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

## Corrections, this pass — checked directly against the actual `.lean`
## files (build green, all sorry-free) rather than against this
## document's own prior summary. Read this before touching item 3/4 below.

**1. `toCoords` (item 3's named blocker) is already closed — stale
pointer in this document, not in the code.** `AlphaLocusDegreeUniform
.lean`'s own "Restating `isReduction` against the now-existing `Reduce`"
section resolves it: `AffinePoints.lean`'s `H.Point.X`/`.Y` give the
`H.Point → F p × F p` projection directly, and `isReduction'` already
uses `(sa.P1.X, sa.P1.Y)` etc. This document's item 3 below still
describes `toCoords` as the concrete open gap — it isn't, anymore. What
IS still missing is described in point 3 below, which is a different,
larger gap than `toCoords` ever was.

**2. `GenericPeelChainHyp`/`decoupledSystem_degree_uniform`
(`AlphaLocusDegreeUniform.lean`) already exist, are already stated over
`SampleTargetFromAlpha`, and are already proved — but do NOT resolve
this roadmap's own "actual remaining blocker" section; they route
around it, unlabeled as such.** Checked directly: `GenericPeelChainHyp`
is instantiated on `sa.toSampleTarget sb.toSampleTarget : SampleTarget p`
with no `alpha`/`alpha'` constraint anywhere — `CrossNondegenerate`/
`PeelChainNondegenerate` (`DecoupledSystemRegular.lean`) take `sa sb :
SampleTarget p` as plain, unrelated targets, exactly the shape this
roadmap's own "actual remaining blocker" section already showed gives a
2-dimensional (not 0-dimensional) solution locus for a bare `finrank`
claim. `decoupledSystem_degree_uniform`'s own docstring is candid about
this: `Bad` is defined circularly as "wherever `GenericPeelChainHyp`
fails," and whether that set is actually finite for a real curve family
is exactly this document's still-open Step 3.1/3.2 content — restated
under a different name, not resolved. **Do not read
`decoupledSystem_degree_uniform`'s existing proof as having closed the
alpha-linkage gap** — it hasn't; it isolates the same open content in
`GenericPeelChainHyp.hfinrank_le`, one level further from the surface.

**3. `genList_finrank_le`'s live `sorry` (`GenListFinrankAssembly.lean`)
is stated against `PeelChainFinrankHyp`, a TWELVE-FIELD hypothesis over
`genList`'s LITERAL order (`Fu`s, then `Fv`s, then curves) — not the
`genListTriangular`-order hypotheses (entries 71/77/78,
`DEGREE-BOUND-FILES-INDEX-README.md`) route 3 actually produces.**
`genList_finrank_le` is ALSO already stated over `SampleTargetFromAlpha`
(`sa sb : SampleTargetFromAlpha p H D aClass δ₀`), not bare `SampleTarget
p` as this document's item 3 (below) describes it — another stale
pointer. Its own docstring is explicit and should be trusted over this
document's older framing: even a fully-wired route 3 proof would not
close it, because nothing connects `sa.isReduction`/`sb.isReduction`
sharing `alpha`/`aClass` to `PeelChainFinrankHyp`'s twelve fields
collapsing to something provable. This is the SAME gap as point 2 above,
seen from the other end of the codebase, not a new one — the codebase
currently has this open question written down in two unconnected
places (`GenericPeelChainHyp.hfinrank_le` and `genList_finrank_le`'s own
`PeelChainFinrankHyp` hypothesis) with no theorem tying either to route
3's actual output shape.

**4. A more basic gap than either of the above, not previously flagged
anywhere in this codebase: route 3's own `finrank` chain has never
actually been instantiated at a real base case, for ANY `sa,sb`,
`alpha`-linked or not.** `genList_triangular_finrank_le_of_base`/
`_fourStage` (entries 71/77/78) are generic over an abstract already-
`Module.Finite` starting prefix `gens : List (Rdec p)` — but no file
anywhere supplies such a `gens` with a real proof. `gens := []` is the
natural candidate and is FALSE (`Rdec p ⧸ Ideal.ofList [] ≃ Rdec p`,
infinite-dimensional — the exact obstruction this document's own
"Naive `Ideal.ofList`-prefix induction" section already diagnosed), and
no strict prefix of `genListTriangular` is finite either (`a1,a2,b1,b2`
are never a pivot alone, only jointly via the shared-pivot resultants —
same reason this document's route-1/route-2 sections already give).
`genList_finite_of_regular` (entry 71, `GenListFinrankResultantAssembly
.lean`) is NOT a fix for this — it proves `Module.Finite` for the FULL
twelve-generator `Ideal.ofList genList` via the global regular-sequence
argument, which is an END state, not a starting `gens` the induction can
consume; it was never wired as such, and cannot be (there is no smaller
`gens` it bears on). **Net effect: `genList_triangular_finrank_le_of_base_
fourStage`'s numeric `≤ B` conclusion has never actually been produced
for a real ring — every existing use of it in this codebase is at the
level of "if some finite base existed, here is how the bound would be
built," not "here is the bound."** Confirmed by grep: no file calls
`genList_triangular_finrank_le_of_base` or `..._fourStage` anywhere
except their own defining/adjacent files' docstrings.

**What this means for scope, going forward**: point 4 is the most
concrete and most tractable of the four — it needs a genuinely new
finiteness argument for *some* starting prefix (most plausibly: prove
`Module.Finite` for the curve-relations-alone quotient, `gens := []`
extended by just the four curve relations, directly — this is a
4-variable-over-8-coefficients situation, likely far more tractable than
the full 12-generator regularity argument `genList_finite_of_regular`
uses), not a resolution of the deeper alpha-linkage question (points 2/3,
still exactly as open as this document's pre-existing "actual remaining
blocker" section already says). Doing point 4 does NOT touch points 2/3
and should not be read as progress against them.

**Update, same pass, before any proof of `RouteThreeHasBaseCase` was
attempted — the curve-relations-alone route above is FALSE, not merely
hard, checked directly against `curveA1`'s literal definition.**
`curveA1 = wa1'² − f(a1')` (`DecoupledSystemRegular.lean` §3) constrains
`wa1` given `a1`, but leaves `a1` itself completely free — and nothing
else among the four curve relations, or any proper sublist of `genList`,
pins `a1,a2,b1,b2` down at all: these four variables are NEVER a pivot
of any of the twelve generators (already established earlier in this
document, "The twelve stages" section) — they appear only as
COEFFICIENTS, inside `u1_num i` etc. (`theData`'s concrete values, via
`aSideGens`/`bSideGens`), which are exactly the generators that pin down
`U0,U1,V0,V1`. So `Rdec p ⧸ Ideal.ofList [curveA1,...,curveB2]` is
`(F p)[a1,a2,b1,b2][wa1,wa2,wb1,wb2] ⧸ (4 monic quadratics)` — finite
RANK 16 over `(F p)[a1,a2,b1,b2]`, but `(F p)[a1,a2,b1,b2]` is itself a
4-variable free polynomial ring, infinite-dimensional over `F p`. The
same argument rules out EVERY proper sublist of `genList` (in any
order): `a1,a2,b1,b2` are pinned down only by the joint interaction of
ALL twelve generators together (`U0,U1,V0,V1`'s own defining relations
depend on the curve variables through their coefficients, and the curve
relations depend on `U0,U1,V0,V1` through nothing — the dependency is
one-directional, but finiteness needs the OTHER direction closed too,
which only happens once every generator is in). **Conclusion:
`RouteThreeHasBaseCase` (`GenListFinrankFourStageTransport.lean`) is
unprovable as stated — there is no `gens` strictly smaller than the
full `genList`/`genListTriangular`, in any order, giving a finite
quotient over `F p`.** This is a genuine mathematical fact about this
specific 12-generator system, not a Lean gimmick or an artifact of
choosing the wrong prefix — matching (and now sharpening) this
document's own much earlier "Naive `Ideal.ofList`-prefix induction"
finding, which already suspected no strict prefix works but had not
traced the reason to `a1,a2,b1,b2` specifically being coefficients-only,
never pivots.

**What this actually forces**: route 3's entire "finite-prefix induction"
architecture (entries 71/77/78,
`GenListFinrankFourStageTransport.lean`) can never be given a witness
for its own generic `gens` hypothesis — not "not yet," but structurally,
for this system. The `finrank ≤ 16` NUMBER itself is very likely still
correct (route 3's per-stage multiplier accounting — `×1` per linear
stage, `×2` per curve stage, `16` total — is sound reasoning about how
much EACH stage's own generator constrains things RELATIVE TO the
previous stage), but that reasoning cannot be assembled via an induction
that needs an intermediate finite ring to exist, because none does
before the twelfth generator is added. **The correct fix, not yet
attempted**: prove the `finrank ≤ 16` bound as a property of the FULL
ideal directly (using `genList_finite_of_regular`'s existing finiteness
fact as a start, then bounding the DEGREE/LENGTH of the finite quotient
via a genuinely global argument — e.g. Bézout/degree-multiplicativity for
a genuine 0-dimensional complete intersection, not a stage-by-stage
tower), rather than via any induction that passes through smaller
`Ideal.ofList` prefixes of `Rdec p`. This is a different, and likely
harder, argument than anything route 3 has built — route 3's twelve
per-stage lemmas (entries 36–70 and 71–78) are not wasted (the per-stage
"how much does THIS relation cost, given the ambient ring is already
correctly-shaped" content is genuine and reusable), but the ASSEMBLY
strategy chaining them via `gens := []` upward needs to be abandoned, not
merely finished.

## Next concrete steps, in order

1. **DONE, this pass.** Linear-stage half
   (`PeelChainPairwiseAgreement.lean`, `PeelChainPairwiseAgreementWiring
   .lean`) and curve-relation half (`PeelChainPairwiseAgreementCurveChain
   .lean`, "agree up to sign") both chained per-generator, then combined
   across all twelve of `genListTriangular`'s generators into one
   statement (`GenListPairwiseAgreementAssembly.lean`,
   `genListTriangular_pairwise_eq_up_to_sign` — curve facts up to sign,
   `U0,U1,V0,V1` exact, one flat conjunction, no ring-extension threading
   needed since every stage's claim lives in the same fixed quotient).
2. **(i)/(ii) fork — DECIDED, ChatGPT consult this pass: route (ii),
   with route (i) demoted to an optional later sharpening, not a
   blocker.** Global `J(𝔽_p)[2] = 0` (the strong form of route (i)) is
   NOT generic for this curve family — for an odd-degree genus-2 model
   `y² = f(x)` with `deg f = 5`, `J(𝔽_p)[2] = 0` iff `f` is irreducible
   over `𝔽_p`, and irreducible quintics are only a ~1/5 fraction of
   squarefree quintics, not "most curves." A weaker, construction-local
   route-(i) lemma may still be cheap later (a nondegenerate divisor
   `D = [P1-∞]+[P2-∞]` with nonzero Mumford `v`-polynomial has `2D ≠ 0`
   automatically, without any global Jacobian hypothesis — worth
   revisiting as a sharpening, NOT attempted here, see item 6 below) but
   the main theorem should not be built on it or wait for it. **Route
   (ii) is the one to build now**: keep the 16-bound (really: at most one
   x-coordinate/quotient-level configuration, whose geometric lift has
   size ≤ 16 — the consult flagged "at most 16 fibers" as a
   mis-statement; it is "one configuration, ≤16 point-lifts"), finish the
   degree/finiteness theorem on that basis, defer sharpening 16→1. This
   also answers the DLP-reduction worry the fork was blocking on: a
   16-way sign ambiguity is a constant-size, efficiently-testable branch
   (`[ι(P)] = -[P]` makes each branch a known negation, checkable against
   the matching equation directly), not a dead end — UNLESS a later step
   needs a literal canonical point rather than an efficiently-decidable
   candidate set, which nothing currently on file needs.
2b. **Transport step ("Not yet done" note at the end of the earlier
    "Step 1 (pairwise agreement), current state" section) — ATTEMPTED
    this pass, not yet REPL-confirmed.** `GenListPairwiseAgreementTransport
    .lean`'s `genList_pairwise_eq_up_to_sign` restates
    `genListTriangular_pairwise_eq_up_to_sign` over `Ideal.ofList
    (genList ...)` instead of `genListTriangular`'s reordered list. See
    the "Update, this pass" section below for the full account, including
    the one unverified tactic step (`simp only [← Ideal.ofList_perm ...]
    at *`) and its documented fallback if that step fails in Claire's
    REPL.
3. **Superseded by the "Corrections, this pass" section above — read
   that first.** `toCoords` (this item's originally-named concrete gap)
   is closed; `SampleTargetFromAlpha`-linkage of `sa,sb` is NOT closed by
   `toCoords` being closed, and remains exactly as open as this
   document's own "actual remaining blocker" section describes —
   `GenericPeelChainHyp`/`genList_finrank_le` both currently route around
   it rather than resolve it (Corrections points 2/3). Restating
   `genList_finrank_le` (or a genuinely new replacement theorem) over
   `SampleTargetFromAlpha`-linked `sa,sb` with fixed `alpha,alpha'`, using
   step 1's fiber-level uniqueness result (route (ii): "one quotient-level
   configuration, ≤16 lifts") alongside route 3's `finrank` machinery, is
   still the right target and is still not started — but it is blocked on
   Corrections point 4 (route 3 has no working base case yet) at least as
   much as on the alpha-linkage question itself, so point 4 is the more
   tractable place to start.
4. Write `GenListFinrankResultantAssembly.lean`, chaining route 3's
   already-built resultant-elimination + curve-relation stages against
   the corrected per-fiber statement. **Update: this file already exists
   and already proves the ≤16 `finrank` bound at the ring level for an
   abstract fixed `(sa,sb)`** (this pass discovered it partially built);
   what remains of this step is specifically linking it to
   `SampleTargetFromAlpha` per item 3, not writing the file itself.
5. Revisit `Bad` sizing now that the corrected statement pins down what
   `Bad` actually needs to range over — still open, per route (ii)'s own
   framing this now means sizing `Bad` against "configuration is unique"
   rather than "point is unique", likely no harder than before since
   `Bad`'s role was always to rule out degenerate `(alpha,alpha')`, not
   to control the 16-fold multiplicity.
6. Replace `GenericPeelChainHyp` in `AlphaLocusDegreeUniform.lean` with
   the proved pieces (delete the hypothesis bundle, or narrow it,
   dropping `hfinrank_le` specifically), per `ROADMAP-degree-uniform-
   step3.md`'s existing instruction.
7. **New, from this pass's consult — optional, not blocking.** The
   construction-local route-(i) sharpening: if the actual `(P1,P2)`
   pairs `SampleTargetFromAlpha` produces are provably non-degenerate
   (not `P2 = ι(P1)`, not both Weierstrass) and their Mumford
   `v`-polynomial is provably nonzero, then `2([P1]+[P2]) ≠ 0` follows
   with NO global `J(𝔽_p)[2]=0` assumption, upgrading 16→1 for real
   instances. Worth investigating once items 3–6 are done and there is
   an actual `SampleTargetFromAlpha`/`Reduce` construction on file to
   check this against — premature before then, since it needs concrete
   `(P1,P2)` data this project does not yet construct (`Reduce` is still
   unported, per `AlphaLocusDegreeUniform.lean`'s own status list).

## Item 4 revisited, this pass: route 3's chain confirmed uninvokable
## end-to-end, not just at the `gens := []` base case — the numeric
## bound needs a genuinely global (Bézout-style) argument, which does
## not exist in this codebase or in Mathlib

Direct inspection this pass, checking `GenListFinrankFourStageAssembly.lean`
and `GenListFinrankFourStageTransport.lean` (entries 77/78, both already
sorry-free and REPL-confirmed per the file index) against their own literal
signatures, not against either file's own summary prose:

- `genList_triangular_finrank_le_of_base_fourStage` (entry 78, the true
  terminus of route 3's numeric chain, chaining curves + all four
  shared-pivot pairs `U0,U1,V0,V1`) still takes `hfin : Module.Finite (F p)
  (Rdec p ⧸ Ideal.ofList gens)` as an ordinary hypothesis on an arbitrary
  starting `gens`. It has never been discharged — confirmed by grep, as
  `RouteThreeHasBaseCase`'s own docstring already says, it has zero call
  sites anywhere in this codebase.
- `RouteThreeHasBaseCase` (`GenListFinrankFourStageTransport.lean`) names
  this precisely: `∃ gens, Module.Finite (F p) (Rdec p ⧸ Ideal.ofList gens)
  ∧ ...`. No file proves this `Prop`. `gens := []` is false (`Rdec p ⧸ ⊥ ≃
  Rdec p`, infinite-dimensional); this document's own "Update, same pass"
  section (above) already proved, directly from `curveA1`'s literal
  definition, that NO strict prefix of `genList`/`genListTriangular`, in
  any order, is finite either — `a1,a2,b1,b2` are coefficients-only,
  pinned down only by the joint action of all twelve generators together.
- **New this pass: block-reshuffling does not rescue this.** One might
  hope the tower doesn't need to peel one polynomial at a time — group the
  twelve generators into blocks (e.g. treat `FuList++FvList` as one
  simultaneous 8-generator elimination stage) and look for a smaller block
  that's already finite. This doesn't work either, for the same reason:
  any PROPER sub-block still omits at least one of the twelve generators,
  and the missing-pivot argument above (`a1,a2,b1,b2` never constrained
  except jointly) is about which variables are constrained, not about
  what order or grouping the constraining generators are applied in.
  Finiteness over `F p` for a genuinely proper subset of `genList` is
  false as a fact about this system, independent of how that subset's
  own elements are packaged into "stages."
- **Consequence, confirmed via a ChatGPT consult this pass on what the
  fix would actually require**: `genList_finite_of_regular`
  (`GenListFinrankResultantAssembly.lean`, the theorem that DOES work) is
  finite via a pure Krull-dimension argument
  (`Module.Finite.quotient_of_isRegular_of_length_eq_card`,
  `RegularSequenceFiniteQuotient.lean`) that only ever concludes
  finiteness, never a numeric bound — Krull dimension is insensitive to
  multiplicity/length by design. There is no way to extract `finrank ≤ 16`
  (or any number) from that proof; a length bound for a zero-dimensional
  complete intersection is a **different, strictly stronger** fact, the
  mathematical content of which is essentially Bézout's theorem for
  complete intersections (length of the quotient equals the product of
  the generators' degrees, in the appropriate graded/leading-term sense).
  Standard proofs of that fact go through either (a) Hilbert series /
  graded free resolutions of the associated graded ring, (b) a
  Gröbner-basis/initial-ideal degeneration argument (the length is
  preserved under passing to the initial ideal, which decomposes as a
  monomial count), or (c) a Koszul-complex Euler-characteristic count.
  **None of these three routes' building blocks — Hilbert series,
  standard-monomial/initial-ideal bases, or Koszul complexes — exist
  anywhere in this codebase, and a Mathlib search this pass (web search,
  `leanprover-community.github.io/mathlib4_docs`, multiple query angles)
  turned up nothing for any of them at the generality needed** (Mathlib
  has `IsRegular`/Koszul-adjacent material for depth/Ext-vanishing
  characterizations, and the Krull-dimension route already used, but
  nothing connecting regular-sequence length to a degree/multiplicity
  bound). This is genuinely new infrastructure, not a wiring gap — on the
  order of weeks, not a session, and not attempted this pass.
- **Route 3's twelve per-stage lemmas are NOT wasted by this finding** —
  unchanged from this document's earlier framing: the per-stage
  monic-annihilator accounting (`×1` per linear stage, `×2` per curve
  stage) is genuine, reusable content, and would very likely appear again
  as the "expected" bound inside whichever Hilbert-series/Gröbner argument
  eventually closes this — it just cannot itself be assembled into that
  bound via a finite-prefix induction, because no finite prefix exists.
  Don't discard `GenListFinrankResultantAssembly.lean`/
  `GenListFinrankFourStageAssembly.lean`/`GenListFinrankFourStageTransport
  .lean` — keep them as-is; they are correct, complete answers to a
  narrower question ("given a finite base, what's the bound") that turned
  out not to compose the way route 3 originally hoped.
- **What this means for item 3 (the `SampleTargetFromAlpha` linkage,
  `genList_finrank_le`'s own remaining sorry)**: item 3 cannot currently
  be closed by citing route 3's chain, full stop — there is no path from
  what's on file to a discharged `hfin` for any starting `gens`. Writing
  `SampleTargetFromAlpha`-linked wiring on top of `genList_triangular_
  finrank_le_of_base_fourStage` right now would either fail to typecheck
  (no witness for `gens`) or silently need its own new `sorry`/hypothesis
  restating finiteness of some sub-block, which is false and should not
  be introduced. The honest next step, not yet started, is scoping the
  minimal genuinely-new lemma (see below) rather than more wiring.

**Concrete next step, not yet attempted**: rather than trying to build
full Hilbert-series or Koszul-complex machinery from scratch, the
minimal useful target is likely a SINGLE lemma, specific to this
system's actual shape, that a ChatGPT consult could scope precisely:
given the regular sequence `genList` (or `genListTriangular`) in
`Rdec p = MvPolynomial Idx (F p)`, `Idx` finite of card 12, with
`genList`'s own known per-generator structure (8 linear-in-one-variable
generators, 4 generators quadratic in one variable and otherwise linear
in the rest), derive `Module.finrank (F p) (Rdec p ⧸ Ideal.ofList
genList) ≤ 16` directly from `IsRegular`-ness plus the per-generator
degree data, without needing any intermediate prefix to be finite. This
is likely provable via a Gröbner/initial-ideal argument specific to this
system's simple per-generator shape (each generator's leading term, for
a suitable monomial order, is visibly a single variable's top-degree
term times a constant/unit — the same shape the monic-annihilator route
already exploited stage-by-stage) even if the fully general Bézout
theorem is out of reach.

## ChatGPT consult, this pass — the clean `≤16` prompt as posed was
## answered correctly: it's FALSE as a general theorem, and the reply
## also corrects a mischaracterization in this document's own framing
## of what `GenListFinrankResultantAssembly.lean` already does

**Self-correction first, checked directly against the file before
accepting the consult's framing of the "problem": this document's own
above section overstated what was actually being claimed anywhere in
this codebase.** `genList_triangular_finrank_le_of_base`'s own docstring
(`GenListFinrankResultantAssembly.lean`, unchanged, re-read this pass)
already says explicitly: the bound is `16 * B` **times the product of
the four shared-pivot resultant quotients' own `finrank`s**, "NOT a
clean numeric constant on its own." `finrank_le_of_shared_linear_elim_pair`
(`SharedPivotResultantElim.lean`) bounds each shared-pivot pair's cost by
`Module.finrank k (A ⧸ Ideal.span {resultant})` — the resultant
quotient's OWN dimension — never by a bare `1`, and already requires
`hd1 : IsUnit d1` (one of the pair's two denominators a unit), matching
what the consult below calls "route A," not a bare `IsRegular` hypothesis.
`finrank_le_sixteen_genList_of_finrank_le_sixteen_genListTriangular`
(`GenListFinrankFourStageTransport.lean`) takes `hchain : ... ≤ 16` as an
explicit HYPOTHESIS, not a conclusion it derives. **So no file in this
codebase ever actually asserted "regular sequence + degree-1-shaped
generators ⇒ finrank ≤ 16" as a theorem** — the ChatGPT prompt above
posed that exact (false) claim as the target, which was this document's
own scoping error, not a preexisting bug in the Lean.

**What the consult actually gets right and adds, genuinely new**:

1. **Confirms the four resultant quotients' finranks are NOT free of the
   `d` coefficients — a concrete counterexample** (§2 of the reply,
   `h1 = 1 - U*a^N`, `h2 = a - U`, regular, giving dimension `2(N+1)` not
   `2`) shows that `IsUnit d1` alone (route A's own stated hypothesis)
   is not enough either — `finrank_le_of_shared_linear_elim_pair`'s bound
   via the resultant quotient is CORRECT as stated (it never claimed the
   resultant quotient has dimension 1), but nothing in this codebase yet
   shows `theData`'s actual `u1_den 0`/`u2_den 0` etc. give a resultant
   whose OWN quotient has `finrank` exactly matching what the clean-16
   count needs. This is exactly `GenListFinrankResultantAssembly.lean`'s
   own already-honest caveat ("that bound is `theData`-specific content,
   deferred") — the consult independently confirms via a concrete
   counterexample that this deferral is load-bearing, not a formality.
2. **The Gröbner/initial-ideal/Hilbert-series routes (this document's
   own proposed "next step" above) are confirmed dead ends for the
   general statement, and MORE SPECIFICALLY explained why**: the
   generators' naive leading terms (`U · LT(d)`, not `U` alone, since `d`
   is a non-unit polynomial in general) don't generate the true initial
   ideal, so "take the obvious leading terms and count standard
   monomials" doesn't work without first knowing the twelve generators
   form a Gröbner basis — itself an unproven, and not obviously true,
   extra fact. Mathlib4's `MonomialOrder`/`Groebner` files (checked by
   the consult against current docs) provide `leadingTerm`/division-with-
   invertible-leading-coefficient but no initial-ideal/Hilbert-series
   package — confirming this document's own earlier finding, not
   contradicting it.
3. **The homogeneous-regular-sequence Hilbert-series calculation
   (degrees `2,2,2,2,1,1,1,1,1,1,1,1` ⇒ Hilbert series `(1+t)^4` ⇒ total
   dimension `16`) is exactly right IF the sequence were homogeneous in
   the ordinary grading — but `genList`'s actual generators are not**
   (`c_j - U d_j` isn't homogeneous unless `c_j,d_j` have matching
   constant degree; `w^2 - f(a)` isn't homogeneous in the ordinary
   grading either). A weighted grading might rescue this but needs
   `theData`'s actual `c_j,d_j`/`f` to satisfy specific compatibility
   conditions not yet checked against.
4. **Reframes the actual target theorem, and this is the useful
   redirection**: rather than "prove `finrank ≤ 16` from abstractions,"
   the consult's own recommended path (§9) is to prove a narrower,
   `theData`-specific structural fact — that the four shared-pivot pairs
   admit an explicit triangular elimination (`U_i` solved in terms of one
   new coefficient-side pivot each, not merely "a resultant exists"),
   so the system becomes literally `4 explicit linear eliminations for
   U0,U1,V0,V1` + `4 coefficient-side pivots among a1,a2,b1,b2` (or
   equivalent) + `4 monic quadratics in wa1,wa2,wb1,wb2` — at which point
   `16 = 2^4` falls out as an EXPLICIT spanning set
   (`w_{a1}^{ε1} w_{a2}^{ε2} w_{b1}^{ε3} w_{b2}^{ε4}`, `ε_i ∈ {0,1}`),
   not an abstract dimension count. This is a genuinely different, and
   per the consult, cheaper target than Gröbner/Hilbert machinery.

**Where this actually leaves the project, corrected**: this document's
own "Item 4 revisited" framing above (treating the missing piece as
"prove a general Bézout/Koszul-style theorem") was aimed at the wrong
target — the general theorem is false, so no amount of Hilbert-series
infrastructure would ever close it as originally posed. **The real
remaining task is `theData`-specific, not abstract**: check whether
`u1_den 0, u2_den 0` etc. (`theData`'s actual denominators at each of
the four shared pivots) admit the triangular structure route A/point 4
above describes — i.e. whether one of the two pair's denominators is
provably a unit (`IsUnit`, matching `finrank_le_of_shared_linear_elim_pair`'s
existing hypothesis) AND the resulting single resultant relation is
itself provably degree-1/monic in one of the remaining coefficient
variables (`a1,a2,b1,b2`), which is exactly the fact this document's much
earlier "Correction, this pass" sections (the `hA`/`hB`,
`CrossNondegenerate`-degree-bound chain, now a settled-hypothesis dead
end per that section) already spent significant effort on, from a
different angle, and did NOT resolve. **This connects two threads of
this document that had drifted apart**: the "clean 16" numeric target
and the old `hA`/`hB`/`CrossNondegenerate` degree-bound effort are the
SAME open question, seen from two directions — a triangular-elimination
proof for the shared pivots is precisely what would supply the
resultant-quotient `finrank` bound `GenListFinrankResultantAssembly.lean`
already defers, AND would settle whether `CrossNondegenerate`'s resultant
nonvanishing can ever be upgraded to something checkable. Neither thread
has closed this from either direction; **do not treat "prove a global
degree/Hilbert-series theorem" as live work going forward** — it answers
a question this project doesn't actually need answered, per the
counterexample above, and the genuinely open piece is the concrete
`theData` triangularity check, not yet attempted from this specific
angle (checking `u1_den`/`u2_den`/etc.'s actual symbolic form for a
one-denominator-is-a-unit-and-the-resultant-is-monic property) even
though closely related efforts (`hA`/`hB`) were tried and hit a
different, but related, structural wall.

## Update, this pass: the `theData` triangularity check (the previous
## section's "genuinely open piece") is now a settled dead end, not an
## open TODO — and step 1 (pairwise agreement) is further along

**Part A: the `theData` denominator-triangularity check is closed,
negatively.** The previous section left this as "not yet attempted from
this specific angle." It has now been attempted, by tracing `u1_den`
(and `u2_den`/`v1_den`/`v2_den`) all the way to their literal defining
recursion (`TheDataDerivation/DataDerivationMumford.lean`'s `towerToRdec`
→ `towerToRdecK1` → `baseFracToRing`) rather than reasoning about their
type signature alone. Finding: `u1_den i` is `den0 * den1`, where `den0,
den1` are themselves each a product of TWO further such denominators one
level down, bottoming out at `IsFractionRing.num`/`.den` of an arbitrary
`K0 p` element (`baseFracToRing`) — i.e. `u1_den i` is a product of up to
four independently-arbitrary fraction-field denominators, chained through
three division-clearing steps with NO GCD reduction at any step
(deliberately dropped, per `baseFracToRing`'s own docstring, "Lean's
kernel doesn't care about term-count bloat"). Nothing in this
construction gives `u1_den` any reason to be monic or degree-1 in any of
`a1,a2,b1,b2` — `IsFractionRing.num`/`.den` supply *some* representative
with no shape guarantee, and the compounding through three levels only
makes this worse, not better. **Do not attempt this check again by
looking harder at the definitions** — the conclusion is structural (no
shape guarantee exists to find), not a matter of not having looked hard
enough; confirming it numerically in Julia against a real `(c0,...,c4)`
instance is the only way this could still surprise us, and even a
positive numerical hit would only be evidence for ONE instance, not a
proof. Route 3's numeric `finrank ≤ 16` target is now dead by two
independent findings (this one, and the earlier Hilbert-series/Koszul
one above) — treat it as closed, not "still open, needs checking,"
for any future pass.

**Part B: step 1 (pairwise agreement) does NOT depend on this finding,
and is why the pivot to it (this pass) is sound, not just a fallback.**
`genListTriangular_pairwise_eq_up_to_sign`'s four `hdU0`/`hdU1`/`hdV0`/
`hdV1` hypotheses only need `IsUnit (u1_den i)` etc. as bare EXISTENTIAL
facts (some inverse exists in the quotient ring) — never the polynomial's
degree, shape, or any expansion of the four-deep composite above. This
is exactly the same kind of hypothesis `GenListFinrankResultantAssembly
.lean`'s own `hd1_U0` already is (confirmed by direct inspection: that
file states `hd1_U0` as a bare hypothesis too, not derived from `hcurA/
hcurB/hgcdA/hgcdB`) — the established project pattern (parallel to
`Nondegenerate`/`CrossNondegenerate`) is to name such conditions as
per-instance genericity hypotheses and move on, not to derive them from
first principles. So `IsUnit(u1_den i)` etc. is correctly a standing
hypothesis in `genListTriangular_pairwise_eq_up_to_sign`'s signature
already, not a gap blocking it — nothing to do here, confirmed rather
than assumed.

**Part C: item 2 of "Next concrete steps" (the `genListTriangular` →
`genList` transport for pairwise agreement) is now attempted — REVISED
once already this pass, after Claire's REPL caught two real errors in
the first draft.** New file `GenListPairwiseAgreementTransport.lean`,
theorem `genList_pairwise_eq_up_to_sign` — restates
`genListTriangular_pairwise_eq_up_to_sign`'s conclusion over `Rdec p ⧸
Ideal.ofList gens` for `gens := genList ...` (the presentation every
other `genList`-facing theorem in this project already uses) instead of
the reordered `genListTriangular`'s quotient, by rewriting the IDEAL
equality `Ideal.ofList_perm (genListTriangular_perm_genList ...)` — the
same fix `GenListFinrankFourStageTransport.lean`'s docstring already
records for the sibling `finrank` transport (rewrite the ideal, not the
quotient-ring TYPE equality, to avoid a "motive is not type correct"
failure).

**First draft's two REPL-reported errors, both fixed in the current
file**: (1) missing `open TheDataDerivation` — `curBeforeMonic`/`Ypoly`/
`uRS` live in that namespace and the first draft never opened it,
despite every sibling file (`GenListTriangularReorder.lean`,
`DecoupledSystemRegular.lean`) doing so; (2) a `whnf` heartbeat timeout,
traced to the first draft's signature literally repeating the fully-
applied term `genList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB` 31
times and `theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB` 21
times — an elaboration-cost problem in the SIGNATURE itself, independent
of error (1), of the same kind `dvd_N_u`'s own docstring
(`TheDataDerivation/DataDerivationSolve.lean`) already diagnosed for a
proof body via `let`/`clear_value`. **Fixed by following
`GenListFinrankFourStageTransport.lean`'s own documented design choice**
("takes the conclusion as a hypothesis, not its ~200-line hypothesis
list, to avoid a transcription mismatch"): the current file states
`genList_pairwise_eq_up_to_sign` generically over `gens : List (Rdec p)`
and `d : DecoupledGenerators p`, tied to `genList`/`theData` via two
`Eq` hypotheses (`hgens`, `hd`) that a concrete caller discharges with
`rfl` — mirroring how `genListTriangular_pairwise_eq_up_to_sign` itself
already keeps `gens`/`d` generic rather than inlining `genListTriangular`/
`theData` throughout its own statement.

**NOT REPL-confirmed — flagged honestly in the file itself too, and this
remains true after the revision above.** Errors (1)/(2) are fixed, but
the core tactic step — `subst hgens; subst hd`, then `simp only [←
Ideal.ofList_perm ...] at *` — has never itself been run. Whether `simp
... at *` can rewrite through the `[IsDomain (Rdec p ⧸ Ideal.ofList
gens)]` INSTANCE argument specifically (as opposed to an ordinary
hypothesis) without its own motive/instance-synthesis snag is genuinely
untested — per this project's convention, Claude does not run Lean, so
this is scoped in good faith but unverified. If it fails in Claire's
REPL, the documented fallback (also recorded in the new file) is
`generalize` on `Ideal.ofList gens` to a fresh variable first, rewrite
there, then re-specialize. **Send any further REPL errors back exactly
as reported** (as happened this pass) — that is how errors (1)/(2) got
found and fixed, faster than guessing at what might be wrong.

**Still not done, unchanged from before**: item 2's other half (deciding
whether to actually chain this against a `SampleTargetFromAlpha`-linked
restatement is folded into item 3, not item 2), and items 3–7 below are
otherwise all exactly as open as previously recorded — this update only
closes the `theData`-triangularity distraction and advances item 2.

## Reference fact worth formalizing, if route (i)/(ii) above ends up

## needing it explicitly

`[P] + [ι(P)] = 0` in `J` for every affine `P` on the odd-degree model
(basepoint `∞`), per Mumford's *Tata Lectures on Theta II*, ch. IIIa §1.
Elementary proof, likely formalizable directly from what already exists:
`div(x − x(P)) = P + ι(P) − 2∞` (the `HyperellipticClassProof.lean`
building blocks `divToPair_linX_eq_of_unramified`/`_of_ramified`/
`divToPair_linX_eq` already give this divisor identity, `sorry`-free);
subtracting `2•[∞]`'s own principal-divisor witness (not yet located/
built) turns it into `[P]+[ι(P)] − 2[∞] = 0`, i.e. `[P]+[ι(P)]=0` once
`[∞]` is the basepoint. Not started.
