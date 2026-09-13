# Roadmap: replacing `GenericPeelChainHyp.hfinrank_le` with a real bound

## Why this document exists

`AlphaLocusDegreeUniform.lean`'s `decoupledSystem_degree_uniform` is
currently proved under `GenericPeelChainHyp`, whose `hfinrank_le` field
just **assumes** the `finrank` bound the theorem is supposed to
establish (`Bad := ∅` makes the existential trivially true). That
file's own docstring calls this "circular as a definition of a
genuinely small set," and `ROADMAP-degree-uniform-step3.md`'s "What NOT
to do" section names this exact failure mode explicitly. This document
scopes the actual replacement.

Separately, `ROADMAP-crossnondegenerate-degree-bound.md` already closed
a DIFFERENT question — whether `crossResultant_totalDegree_le`'s
`hA`/`hB` hypothesis could be derived from `IsRdecWitness`/
`HasRdecBound`-style witness-existence machinery. That question is
**settled, not open**: `towerToRdec` is not a ring homomorphism, so no
version of that approach can produce a literal computed-pair bound, and
`hA`/`hB` is correctly a standing hypothesis now. **Nothing in this
document reopens that question or depends on resolving it.** This
document is about a different gap entirely: turning `hfinrank_le` from
an assumption into a proof.

## Strategy, per ChatGPT consult

Full reply on file if needed; summary: abandon the
`IsSMulRegular`/witness-existence framing for this specific goal (the
project's other regularity work, `regularSeq_of_peel_chain` etc.,
stays as-is — this is an alternative route to a NUMBER, not a
replacement for the existing regularity proof). Build the bound by
**iterated monic-annihilator elimination**:

- **Core reusable fact**: if `G ∈ A[T]` is monic of degree `d` and
  `G(t) = 0` in some `A`-algebra `B`, then
  `finrank_k B ≤ d * finrank_k A`. Proof: `A[T]/(G) ↠ B`, and
  `A[T]/(G)` is spanned over `A` by `1, T, ..., T^(d-1)`.
- **Per stage**: produce a monic (or normalizable-to-monic) relation
  for the newly-introduced variable, over the algebra already built
  from the previous stages, then apply the core fact and multiply.
- **Per-stage hypothesis, correctly scoped**: "the eliminant's leading
  coefficient is a unit in the previous stage's algebra" — NOT bare
  nonvanishing of a resultant, which is too weak to normalize to
  monic. This is meant to directly replace `CrossNondegenerate`'s
  current all-or-nothing framing with named, checkable, per-stage
  conditions, in the style `Nondegenerate` already uses.
- This bounds `finrank` (length), not just point-count, so no
  reducedness/regularity/complete-intersection content is needed for
  the *upper bound* direction — a useful simplification versus the
  existing `IsRegular`-based route in `RegularSequenceFiniteQuotient.lean`,
  which proves `Module.Finite` (finiteness) but gives no *number*.

Mathlib already has the pieces the core fact and the stage-chaining
need — confirmed by search before writing this document, not assumed:
`Polynomial.Monic.finite_quotient`/`finite_adjoinRoot`, `AdjoinRoot.finrank`
(finrank of a monic-polynomial quotient equals its degree), and the
tower law `Module.finrank_mul_finrank`/`LinearMap.finrank_range_of_inj`
for composing bounds across a chain of extensions. This is a buildable
plan, not blocked on absent Mathlib theory.

## The peel chain, stage by stage (traced directly from `PeelChainAssembly.lean`, not assumed)

Twelve stages, each peeling exactly one variable, confirmed against
`genList`'s literal definition and `regularSeq_of_peel_chain`'s own
12-way case split:

| Stage | Variable | Generator | Shape |
|---|---|---|---|
| 0 | `U0` | `Fu0 = u1_num(0) − U0·u1_den(0)` | linear in `U0` |
| 1 | `U0` | `Fu1 = u2_num(0) − U0·u2_den(0)` | linear in `U0` |
| 2 | `U1` | `Fu2 = u1_num(1) − U1·u1_den(1)` | linear in `U1`, "Gap A" cross-index |
| 3 | `U1` | `Fu3 = u2_num(1) − U1·u2_den(1)` | linear in `U1`, "Gap A" |
| 4 | `V0` | `Fv0 = v1_num(0) − V0·v1_den(0)` | linear in `V0`, needs `hv0_ext` |
| 5 | `V0` | `Fv1 = v2_num(0) − V0·v2_den(0)` | linear in `V0`, needs `hv1_ext` |
| 6 | `V1` | `Fv2 = v1_num(1) − V1·v1_den(1)` | linear in `V1`, needs `hv2_ext` |
| 7 | `V1` | `Fv3 = v2_num(1) − V1·v2_den(1)` | linear in `V1`, needs `hv3_ext` |
| 8 | `wa1` | `curveA1 = wa1² − f(a1)` | already monic, degree 2 |
| 9 | `wa2` | `curveA2 = wa2² − f(a2)` | already monic, degree 2 |
| 10 | `wb1` | `curveB1 = wb1² − f(b1)` | already monic, degree 2 |
| 11 | `wb2` | `curveB2 = wb2² − f(b2)` | already monic, degree 2 |

Only **two structurally distinct shapes**, not twelve independent
problems:

- **Stages 0–7 (matching generators)**: each is `numerator(x) −
  t·denominator(x)`, literally linear in the peeled variable `t`. The
  regularity version of exactly this shape already has machinery in
  `DecoupledSystemRegular.lean` (`regular_of_linear_elim`,
  `regular_of_peeled_leadingCoeff`) — dividing by `denominator(x)`
  turns it into a monic *linear* relation (`d = 1`) whenever the
  denominator is a unit in the previous stage's algebra, which is
  close to (though not identical to — see Open questions) what the
  existing `hFu*_reg`/`hv*_ext` hypotheses already assert about
  regularity. The task here is bolting a degree number onto an
  argument whose shape is already worked out, not deriving the shape
  from scratch.
- **Stages 8–11 (curve relations)**: each is already literally monic
  as written (`w² − f(a)`, degree exactly 2) — no elimination or
  normalization needed, just a direct application of the core fact
  with `d = 2`.

## Proposed file plan

Numbers are estimates, not commitments — see "How this estimate could
move" below. Rough total: **7–12 new files**, well under the ~35-file
scale of the (separate, already-closed) `hA`/`hB` effort, because the
12 stages collapse to 2 repeated shapes and half the regularity
groundwork already exists.

1. **Core reusable lemma** (1 file, e.g.
   `FinrankLeOfMonicAnnihilator.lean`). Standalone, no peel-chain
   specifics: `finrank_k B ≤ d * finrank_k A` for monic `G` of degree
   `d` with `G(t) = 0` in `B`. Built from `Polynomial.Monic.finite_quotient`/
   `AdjoinRoot.finrank`/`Module.finrank_mul_finrank`. Do this first,
   independent of everything else — it has no dependency on the peel
   chain's specifics and de-risks the whole plan early.
2. **Stages 0–3 degree bound** (1–2 files). The `U0`/`U1` matching
   generators, whose regularity is already fully handled
   (`regular_of_linear_elim` chain, no `_ext` hypotheses needed). Adds
   a degree-1 monic-annihilator bound alongside the existing
   regularity fact at each of these 4 stages.
3. **Stages 4–7 degree bound** (1–2 files). The `V0`/`V1` matching
   generators, which needed the `_ext` hypotheses for regularity
   (`hv0_ext`–`hv3_ext`) because of the shared-matching-variable
   obstruction `PeelChainAssembly.lean` documents at length. Likely
   needs a matching `_ext`-shaped degree hypothesis, not just reused
   regularity — see Open questions.
4. **Stages 8–11 degree bound** (1 file). All four curve relations,
   same shape (`w² − f(a)`, `d = 2`); one file handling all four in
   parallel, mirroring how `curveA1`/`curveA2`/`curveB1`/`curveB2` are
   already grouped elsewhere in this project.
5. **Assembly** (1–2 files). Chain all 12 stages' bounds via the tower
   law into one `finrank` bound on `Rdec p ⧸ Ideal.span(genList...)`,
   producing the actual replacement for
   `GenericPeelChainHyp.hfinrank_le`.
6. **`Bad`/exceptional-set sizing** (1–3 files). Per ChatGPT's point on
   `Bad`'s size: a per-stage unit-condition that depends on
   `(alpha,alpha')` jointly gives `Bad` of size `O(D·p)`
   (Schwartz–Zippel), while one that splits into separate
   `alpha`-only and `alpha'`-only pieces gives `O(D)`. This needs to
   be decided by actually looking at what stages 4–7's `_ext`-shaped
   unit conditions depend on — not yet examined, and the most likely
   place this estimate moves (see below).

## Suggested order

1. Core lemma (item 1) — always first, self-contained.
2. Stages 8–11 (item 4) — do these *before* the matching-generator
   stages, even though they come later in the peel chain: they're
   already monic, so they're the fastest way to confirm the core lemma
   composes correctly through `Module.finrank_mul_finrank` end-to-end,
   on the easiest possible case, before tackling the linear-elimination
   stages' extra "leading coefficient is a unit" bookkeeping.
3. Stages 0–3 (item 2) — the matching generators whose regularity
   argument is already fully worked out; adapt that existing shape to
   also produce a degree bound.
4. Stages 4–7 (item 3) — same shape as 0–3, but first resolve whether
   the existing `_ext` hypotheses already imply what the degree bound
   needs, or whether a new hypothesis is required (see Open questions
   below) — do this diagnosis before writing files, the same way
   `ROADMAP-crossnondegenerate-degree-bound.md`'s own `hA`/`hB`
   investigation was done as a diagnosis pass before committing to
   files.
5. Assembly (item 5).
6. `Bad` sizing (item 6) — informed by what's actually learned about
   the stage conditions' `(alpha,alpha')`-dependence while doing 3–4,
   not decided in advance.
7. **Replace `GenericPeelChainHyp` in `AlphaLocusDegreeUniform.lean`**
   once 1–6 give real content — per
   `ROADMAP-degree-uniform-step3.md`'s own existing instruction, either
   delete the hypothesis bundle in favor of the proved pieces, or keep
   it strictly narrower (dropping `hfinrank_le` specifically) once the
   real bound and its real hypotheses exist.

## Open questions — resolve before or during the file work, not after

- **Do `hv0_ext`–`hv3_ext` already supply what a degree bound needs,
  or only regularity? — RESOLVED (checked directly against
  `PeelChainAssembly.lean`'s literal field definitions, not assumed):
  no, they don't, and the gap is sharper than "related but not
  obviously identical."** `hv0_ext`–`hv3_ext` are `IsSMulRegular
  <the specific difference `v{i}_num j − V·v{i}_den j`> <the extended
  quotient ring>` — i.e. "multiplication by the WHOLE linear-form
  VALUE `v_num − V·v_den` is injective on the further-extended
  quotient," matching `linearElimPoly`'s shape `c − X·d` evaluated at
  the peeled variable, not `linearElimPoly_span_eq`'s antecedent
  `IsUnit d` about the ISOLATED leading coefficient `d = v_den`. Two
  distinct gaps, not one: (1) regularity (injective-on-multiplication)
  is a strictly weaker condition than `IsUnit` in general — a
  nonzerodivisor need not be a unit — so `hv_ext` being `IsSMulRegular`
  rather than `IsUnit`-flavored is real content missing, not a
  relabeling; (2) even granting unit-strength, `hv_ext`'s subject is
  the whole evaluated linear form in the EXTENDED (further-quotiented)
  ring, not the bare leading coefficient `v_den i` in the
  PREVIOUS-STAGE ring `A` that `finrank_le_of_linear_elim`'s `hd :
  IsUnit d` hypothesis is about. Stages 4–7 therefore need a genuinely
  new, separately-supplied `IsUnit (v_den i)`-shaped hypothesis (at
  the previous stage's ring, before the extension) — not a
  restatement or corollary of `hv_ext`, and not automatic from it.
  **Consequence for the file plan**: item 3 (stages 4–7) cannot reuse
  `hv0_ext`–`hv3_ext` as its unit hypothesis; it needs new hypotheses
  of the `IsUnit (v_den i)` shape (mirroring stages 0–3's `IsUnit d`
  in `LinearElimDegreeBound.lean`), stated fresh, likely alongside
  (not replacing) the existing `hv_ext` regularity fields once wired
  into `PeelChainAssembly.lean`'s structure at Assembly time (item 5).
- **Where does `Bad`'s eventual size land?** Now informed by the
  resolution above: since stages 4–7's needed `IsUnit (v_den i)`
  condition is a FRESH hypothesis (not derived from the existing,
  already-`(alpha,alpha')`-entangled `hv_ext` regularity fields), its
  `(alpha,alpha')`-dependence is not yet fixed by anything already
  proved — it depends on what `v_den i` (previous-stage denominator)
  actually looks like as a symbolic expression in `(c0,...,c4)`,
  `alpha`, `alpha'`, which has NOT yet been examined (separate task,
  still open). If the stage-4–7 unit conditions turn out to split
  cleanly per-sample (one depending only on `sa`'s data, the other
  only on `sb`'s), `Bad` lands in the cheap `O(D)` case from ChatGPT's
  own table; if they genuinely entangle `alpha` and `alpha'` together
  the way the *regularity* obstruction did, expect `O(D·p)` instead,
  which may or may not be "small" in the sense
  `IsSmallExceptionalSet` actually needs — check that definition
  before assuming either outcome is acceptable.
- **NEW, discovered while scoping Assembly (item 5's true remainder) —
  NOT YET RESOLVED: does the naive per-stage induction even have a
  valid base case / intermediate steps?** Every one of the 12 wired
  per-stage lemmas (`finrank_le_curveRelation_ofList_cons`,
  `finrank_le_linearElim_ofList_cons`) takes `[Module.Finite (F p)
  (Rdec p ⧸ Ideal.ofList gens)]` (among others) as an EXPLICIT
  hypothesis on the PREFIX ring, meaning a naive Assembly induction
  ("chain stage 0, then stage 1, ..., proving each stage's
  `Module.Finite`/`StrongRankCondition`/`Nontrivial` from the previous
  stage's already-established instance of the same") needs
  `Module.Finite (F p) (Rdec p ⧸ Ideal.ofList gens)` to hold at EVERY
  intermediate prefix, starting from `gens = []`, i.e. `Rdec p` itself.
  But `Rdec p = MvPolynomial Idx (F p)` is NOT finite-dimensional over
  `F p` (`Module.Finite (F p) (Rdec p)` is false — it's a polynomial
  ring, infinite `F p`-dimension), so the induction's base case fails
  outright as naively conceived. Worse, `RegularSequenceFiniteQuotient
  .lean`'s existing `Module.Finite.quotient_of_isRegular_of_length_eq_
  card` (the ONLY existing finiteness fact for any `Rdec p ⧸
  Ideal.ofList (...)` quotient in this project) genuinely needs the
  FULL regular sequence (`hlen : rs.length = Nat.card ι`, i.e. all 12
  generators) to conclude `Ring.KrullDimLE 0` and hence
  `Module.Finite` — its proof goes through `ringKrullDim (MvPolynomial
  ι k) = Nat.card ι` dropping to exactly `0` only once the FULL-length
  regular sequence is quotiented by; a PREFIX of length `i < 12`
  generically leaves Krull dimension `12 - i > 0`, i.e. genuinely NOT
  finite-dimensional in general. **This means finiteness is not an
  incrementally-provable-per-stage fact along this peel chain — it is
  a global fact that only becomes true at the very last step**, so the
  per-stage lemmas' `[Module.Finite (F p) (...)]` hypothesis on the
  PREFIX ring cannot be discharged by a straightforward induction the
  way `StrongRankCondition`/`Nontrivial` plausibly could be (those
  don't have the same "only true at full length" character —
  `Nontrivial`/`StrongRankCondition` likely DO hold at every prefix,
  since they don't need the dimension-drop argument, though this has
  NOT been separately verified either). **This needs to be resolved
  before writing the Assembly chaining file** — options include: (a)
  restating each per-stage lemma to only need `Module.Finite` on the
  EXTENDED ring `B` as a CONCLUSION rather than a hypothesis on the
  prefix (checking whether `finrank_le_of_monic_annihilator`'s own
  proof already establishes `Module.Finite k B` along the way — its
  docstring says it does, via `Module.Finite.trans`, suggesting the
  per-stage lemmas COULD in principle export finiteness forward rather
  than needing it as an input, which would fix the induction's
  direction — but the current wired theorems don't expose this output,
  only consume it as a hypothesis, so this may need a signature change,
  not just a new proof); (b) proving finiteness of every INTERMEDIATE
  prefix quotient by a different argument than the full-length Krull
  dimension one (e.g. if each individual generator, once monic/unit-
  normalized, genuinely makes its one-step extension finite over the
  PREVIOUS stage — which is very plausibly true and is arguably what
  `finrank_le_of_monic_annihilator`'s proof already shows for `B`
  relative to `A`, again suggesting route (a) is more natural); (c)
  something not yet considered. Route (a) looks most promising on
  first read but has not been checked against
  `FinrankLeOfMonicAnnihilator.lean`'s actual proof term — do that
  check before committing to a fix.

  reduction mod a specific `p` — keep this distinction explicit in
  whatever hypothesis each stage ends up stating, the same way
  `ROADMAP-crossnondegenerate-degree-bound.md` already flags it for
  the (separate, closed) `hA`/`hB` question.

## How this estimate could move

- **Down**: if stages 0–3 and 4–7 turn out identical enough in their
  degree-bound argument (not just their regularity argument) to share
  one file each rather than needing separate treatment — plausible,
  since all 8 matching generators share the literal `num − t·den`
  shape.
- **Up**: if the "Open questions" diagnosis above finds that `_ext`'s
  existing hypotheses don't transfer to the unit-condition this plan
  needs, requiring genuinely new hypotheses (and possibly new
  `ChatGPT`-assisted derivations) for stages 4–7 specifically — this
  is exactly the kind of thing that turned the `hA`/`hB` effort from
  an expected quick close into a ~10-file investigation before it was
  understood as structural. If that happens here, expect it to show
  up at stages 4–7, not 0–3 or 8–11, since those are the only stages
  whose regularity argument already needed non-obvious extra
  hypotheses once.
- **Not moved by**: the (separate, already-closed) `hA`/`hB`
  question — nothing here depends on revisiting that.

## Progress (updated as files land)

- **Item 1 (core lemma) — done, REPL-confirmed build-green.**
  `FinrankLeOfMonicAnnihilator.lean`: `finrank_le_of_monic_annihilator`
  (two revisions needed to get the `AdjoinRoot.liftAlgHom`/
  `liftAlgHom_root` API instantiation right — see that file's own
  docstring for the corrected API note).
- **Item 4 / suggested-order step 2 (stages 8–11, curve relations) —
  done, REPL-confirmed build-green.** `CurveRelationsDegreeBound.lean`:
  `finrank_le_of_curve_relation`, a generic per-stage fact (`Module.finrank
  k (AdjoinRoot (X² − C f)) ≤ 2 * Module.finrank k A`) built on item 1's
  lemma. Deliberately abstract — not yet wired to `Rdec p`'s literal
  `curveA1`/`curveA2`/`curveB1`/`curveB2` or their actual quotient rings;
  that identification is item 5's job.
- **Item 2 / suggested-order step 3 (stages 0–3, matching generators) —
  done, REPL-confirmed build-green.** `LinearElimDegreeBound.lean`:
  `linearElimPoly`/`linearElimMonicPoly` (the non-monic `c − X·d` vs.
  its monic unit-rescaling `X − C(d⁻¹c)`), `linearElimPoly_eq_unit_mul`
  + `linearElimPoly_span_eq` (they generate the same ideal, via
  `Ideal.span_singleton_mul_left_unit` — no `IsDomain` needed, unlike
  an earlier draft's `Ideal.span_singleton_eq_span_singleton` attempt),
  `aeval_linearElimPoly_eq_zero_iff` (transports a root across the
  unit-rescaling directly, algebraically — the route actually used by
  the headline theorem, not the `Ideal.span` machinery above, which
  stayed in as independently-true reusable infrastructure), and
  **`finrank_le_of_linear_elim`** (the file's stated deliverable):
  `IsUnit d → aeval t (linearElimPoly c d) = 0 → Algebra.adjoin A {t}
  = ⊤ → finrank k B ≤ finrank k A`. Two REPL-driven fixes worth
  remembering for future files with a similarly heavy ambient
  typeclass stack on `A` (`CommRing`, `Nontrivial`, `StrongRankCondition`,
  `Module.Finite k A`): (1) a `conv_lhs => rw [show d = ↑hd.unit from
  ...]`-style rewrite that touches EVERY occurrence of a variable,
  including one buried inside a hypothesis term that itself depends on
  that variable (here, `d` inside `hd.unit⁻¹`, where `hd : IsUnit d`),
  produces a "motive is not type correct" error — fix by targeting a
  single occurrence (`nth_rewrite 1 [...]`) instead of a blanket `rw`;
  (2) applying a general unit-multiple-ideal lemma DIRECTLY against
  unfolded, project-specific definitions (rather than bare variables)
  can blow the `whnf` heartbeat budget during unification even after
  raising `maxHeartbeats`, purely from the ambient instance search —
  fix by first proving a definition-free helper lemma over plain
  variables, THEN specializing it via `rw` + `exact`, so the heavy
  unification never has to see the project-specific `def`s at all.
- **Open Questions diagnosis (stages 4–7, prerequisite for item 3) —
  resolved.** Checked `hv0_ext`–`hv3_ext`'s literal field definitions
  in `PeelChainAssembly.lean` directly: they are `IsSMulRegular
  <the evaluated linear form v_num − V·v_den> <the further-extended
  quotient ring>`, which is (a) regularity, not `IsUnit`-strength, and
  (b) about the whole evaluated expression in the EXTENDED ring, not
  the isolated leading coefficient `v_den i` in the PREVIOUS-STAGE
  ring that `finrank_le_of_linear_elim`'s `hd : IsUnit d` hypothesis
  needs. Neither gap closes for free — see the Open Questions section
  above for the full writeup.
- **Item 3 / suggested-order step 4 (stages 4–7) — done, REPL-confirmed
  build-green.** `LinearElimDegreeBoundExt.lean`: `finrank_le_of_Fv0`
  through `finrank_le_of_Fv3`, four thin re-exports of item 2's
  `finrank_le_of_linear_elim` under stage-facing names — `Fv0`–`Fv3` are
  literally the same `c − X·d` shape as `Fu0`–`Fu3`, so no new proof
  content was needed, only the fresh `hv_den_unit : IsUnit d` hypothesis
  per stage the Open Questions diagnosis flagged as NOT already supplied
  by `hv_ext`.
- **Item 5 / suggested-order step 5 (Assembly) — part 1 in progress, not
  yet REPL-confirmed.** `QuotOfListChain.lean`: `quotOfListCons_ringEquiv`,
  a generic (any `CommRing R`, `MvPolynomial`/`τ`-free) ring isomorphism
  `(R ⧸ Ideal.ofList gens) ⧸ Ideal.span {mk gens g} ≃+* R ⧸ Ideal.ofList
  (gens ++ [g])`, plus `quotOfListCons_ringEquiv_apply_mk_mk` pinning down
  where it sends the basepoint `mk (mk gens x)`. This is the missing link
  between each per-stage `finrank` lemma's ABSTRACT `B := A ⧸ Ideal.span
  {c}` shape and the LITERAL one-step `Rdec p ⧸ Ideal.ofList (prefix ++
  [newGen])` quotients the 12-stage chain actually produces — needed
  before the twelve per-stage facts can be composed via
  `Module.finrank_mul_finrank` at all. Built on the same
  `DoubleQuot.quotQuotEquivQuotSup` + `Ideal.ofList_append` content
  `PeelChainAssembly.lean`'s own regularity-transport proof already uses
  internally, extracted here without that proof's `MvPolynomial`/`τ`
  machinery (not needed for this file's weaker job — transporting an
  isomorphism's basepoint, not regularity, across it).
- **Item 5 part 2, curve-relation slice (stages 8–11 specifically) —
  done, REPL-confirmed build-green.** `CurveRelationStageWiring.lean`:
  `curveFImage`/`curveRelationGen` (the literal `Rdec p`-valued curve
  relation, generic over which two `Idx` symbols play the `w`/`x`
  roles) and **`finrank_le_curveRelation_ofList_cons`** — the actual
  wiring of `finrank_le_of_monic_annihilator` +
  `finrank_le_ofList_cons` + `QuotOfListChainAdjoinTop.lean`'s free
  `hgen` fact against a literal `Ideal.ofList gens` prefix, giving
  `Module.finrank (F p) (Rdec p ⧸ Ideal.ofList (gens ++ [curveRelationGen
  ...])) ≤ 2 * Module.finrank (F p) (Rdec p ⧸ Ideal.ofList gens)` for
  an arbitrary prefix `gens`. Takes `[StrongRankCondition (Rdec p ⧸
  Ideal.ofList gens)]`, `[Module.Finite (F p) (Rdec p ⧸ Ideal.ofList
  gens)]`, and `[Nontrivial (Rdec p ⧸ Ideal.ofList gens)]` as explicit
  hypotheses (needed by `finrank_le_of_monic_annihilator` and by
  `CurveRelationsDegreeBound.lean`'s `[Nontrivial A]`-scoped section
  respectively) — genuinely undischargeable for an arbitrary prefix,
  left for true Assembly time per this roadmap's own item-5 split.
  Four REPL-driven fixes worth remembering for future stage-wiring
  files: (1) `Rdec p`/`Idx`/`F p` live under the nested
  `Genus2Lean.DecoupledSystem` namespace (`DecoupledSystemRegular.lean`)
  — a file using them needs both the import AND to be nested inside
  `namespace DecoupledSystem`, not just `Genus2Lean`; (2) `F p`'s
  `Field` instance needs `[Fact (Nat.Prime p)]` in scope, easy to
  forget on a bare `variable (p : ℕ)` line; (3) rewriting a `set`-frozen
  local definition's own unfolding (`rw [hg_def, ...]`) fails with
  "motive is not type correct" whenever that definition also appears
  inside a LATER `set`'s type (here, `g` inside `B`'s `Ideal.span {mk_A
  g}`) — `show ... := by ...` sidesteps this by using defeq instead of
  propositional rewriting, since it never touches the frozen type;
  relatedly, closing such a `show`d goal needs `simp only [...]`, not a
  single-pass `rw [...]`, when the target lemmas (`map_sub`/`map_pow`)
  need to fire on a nested ring-hom application, not just the outermost
  one; (4) when a lemma's base field/ring argument (here
  `finrank_le_of_monic_annihilator`'s `{k : Type*}`) appears ONLY in the
  conclusion, never in any explicit argument's type, instance search
  can get stuck on a metavariable before the term is unified against
  its use site — supply it explicitly (`(k := F p)`) rather than
  relying on inference.
- **Item 5 part 2, matching-generator slice (stages 0–7) — done,
  REPL-confirmed build-green.** `LinearElimStageWiring.lean`:
  `linearElimGen` (the literal `Rdec p`-valued matching-generator
  relation `c - X u * d`, generic over the peeled `Idx` symbol `u` and
  already-fixed `c d : Rdec p`) and **`finrank_le_linearElim_ofList_cons`**
  — the counterpart to `CurveRelationStageWiring.lean`'s wiring, this
  time specializing `finrank_le_of_linear_elim`
  (`LinearElimDegreeBound.lean`) instead of
  `finrank_le_of_monic_annihilator` directly. Stated fully generically
  over `c d : Rdec p` and `u : Idx`, so — same reasoning
  `LinearElimDegreeBoundExt.lean`'s own docstring already gives for why
  `finrank_le_of_linear_elim` needs no new per-stage theorem for
  stages 4–7 — **this one file's wiring already covers all eight
  matching-generator stages (0–7), not just 0–3**: nothing in its
  statement or proof is specific to which `Idx` symbol or which
  concrete `c`/`d` expressions are plugged in, so `finrank_le_of_Fv0`
  through `_Fv3`'s stage-4–7 `hv_den_unit` hypothesis is exactly this
  file's `hd_unit` argument, already present. Takes the same three
  `StrongRankCondition`/`Module.Finite`/`Nontrivial` hypotheses as
  `CurveRelationStageWiring.lean` (same undischargeable-until-Assembly
  reasoning) plus `hd_unit : IsUnit (mk_A d)`, the roadmap's own
  correctly-scoped "leading coefficient is a unit" condition (distinct
  from, and not implied by, the existing `hFu*_reg`/`hv*_ext`
  regularity hypotheses per the roadmap's resolved Open Questions).
  Two more REPL-driven fixes worth remembering, beyond the four
  `CurveRelationStageWiring.lean` already logged: (5) when the target
  theorem's conclusion has NO explicit multiplier (degree-1 stages
  conclude bare `finrank B ≤ finrank A`, unlike degree-2's `2 *
  finrank A`) but the chaining lemma `finrank_le_ofList_cons` always
  concludes `... ≤ ?d * finrank A` with an explicit `?d : ℕ`, `apply`
  cannot unify a bare `X` against `?d * X` on its own — bracket the
  goal with `rw [← one_mul X]` before `apply` (turning it into `1 *
  X`, which unifies with `?d := 1`) and `rw [one_mul]` again just
  before the final `exact`, to strip the same `1 *` back off before
  handing the goal to the degree-1 per-stage lemma; (6) `set dA := expr
  with hdA_def` doesn't just introduce a new local name — it rewrites
  every existing occurrence of `expr` everywhere in the current goal
  AND context, including inside hypotheses that were already in scope
  (here, `hd_unit : IsUnit (mk_A d)` was silently already `IsUnit dA`
  the moment `set dA := ...` ran) — a follow-up `rw [← hdA_def] at
  hd_unit` to "catch up" that hypothesis is not just unnecessary but a
  hard error (`rewrite` fails to find the now-absent original pattern).
- **Item 5 (all 12 per-stage wirings) — complete.** Between
  `CurveRelationStageWiring.lean` (stages 8–11) and
  `LinearElimStageWiring.lean` (stages 0–7, covering all eight
  matching-generator stages in one generic file), every one of the 12
  peel-chain stages now has a `finrank` bound wired against a literal
  `Ideal.ofList gens ++ [newGen]` one-step quotient, each still taking
  its own genuinely-undischargeable-for-an-arbitrary-prefix hypotheses
  (`StrongRankCondition`/`Module.Finite`/`Nontrivial`, plus `IsUnit
  d`/`hd_unit` for the eight linear stages) as explicit arguments for
  Assembly to supply.
- **Not yet started**: the final Assembly step (item 5's true
  remainder) — using `QuotOfListChain.lean`'s
  `quotOfListCons_ringEquiv` plus `Module.finrank_mul_finrank` to chain
  all twelve now-proved per-stage bounds against `genList`'s literal
  12-element list (`FuList ++ FvList ++ [curveA1, curveA2, curveB1,
  curveB2]`), discharging each stage's `StrongRankCondition`/
  `Module.Finite`/`Nontrivial`/`IsUnit d` hypotheses along the way by
  induction (each stage's `A` being the previous stage's already-proved
  `B`) — producing the actual replacement for
  `GenericPeelChainHyp.hfinrank_le`; item 6 (`Bad` sizing, still
  blocked on examining `v_den i`'s actual symbolic
  `(c0,...,c4,alpha,alpha')`-dependence per the Open Questions update
  above); and the final `AlphaLocusDegreeUniform.lean` replacement.

## Update, later pass — the "does the naive induction even have a valid
## base case" Open Question is RESOLVED; two new files, not yet REPL-confirmed

The Open Questions section's "NEW, discovered while scoping Assembly"
entry (route (a) vs (b) vs "something not yet considered", for how each
stage's `[Module.Finite (F p) (Rdec p ⧸ Ideal.ofList gens)]` prefix
hypothesis gets discharged along a 12-step induction whose true base
case, `Rdec p` itself, is NOT finite-dimensional) is now resolved in
favor of **route (a)**, checked directly against
`FinrankLeOfMonicAnnihilator.lean`'s actual proof term rather than left
as an unconfirmed guess: that proof already constructs `Module.Finite k
(AdjoinRoot G)` internally via `Module.Finite.trans A (AdjoinRoot G)`,
i.e. it derives the EXTENDED algebra's finiteness from the BASE algebra's
— exactly the direction an induction starting from the genuinely-true
base case `Module.Finite (F p) (F p)` (any field over itself, trivial)
needs. Route (a)'s own docstring in `FinrankLeOfMonicAnnihilator.lean`
(the "`[Module.Finite k A]` is a real hypothesis, not incidental"
paragraph) already flagged this reading; this pass just confirmed it by
reading the proof term line by line rather than trusting the docstring's
own claim uncross-checked.

**Two new files, both untested (no REPL access this pass — see this
project's working agreement; Claire's build is the only real signal)**:

- `FinrankLeOfMonicAnnihilatorFinite.lean`: `finrank_le_of_monic_
  annihilator_of_finite`, a thin repackaging of `finrank_le_of_monic_
  annihilator` taking `Module.Finite k A` as an explicit hypothesis
  argument (not a typeclass assumption an induction can't aim at a
  specific previous stage) and exporting `Module.Finite k B` as an
  explicit second conclusion alongside the same `finrank` bound, via one
  new step (`Module.Finite.of_surjective`, confirmed present in current
  Mathlib4 under `Mathlib.RingTheory.Finiteness.Basic`) applied to the
  same surjection `φ` the existing proof already builds. Also
  `nontrivial_of_span_ne_top`: `B := A ⧸ Ideal.span {g}` is `Nontrivial`
  whenever `g` is not a unit, via `Submodule.Quotient.nontrivial_of_ne_top`
  + `Ideal.span_singleton_ne_top` (both confirmed present in current
  Mathlib4).
- `PeelChainStageFinite.lean`: `finrank_le_and_finite_curveRelation_
  ofList_cons` / `finrank_le_and_finite_linearElim_ofList_cons`, the
  finiteness-exporting counterparts of `finrank_le_curveRelation_ofList_
  cons`/`finrank_le_linearElim_ofList_cons`, each now concluding
  `Module.Finite`/`Nontrivial` on the EXTENDED one-step quotient `Rdec p
  ⧸ Ideal.ofList (gens ++ [g])` (not just the abstract two-step `B`),
  via a new generic transport lemma `finite_and_nontrivial_ofList_cons_
  of_two_step` that pushes both facts across `quotOfListCons_ringEquiv`
  using `Module.Finite.of_surjective` (again) and `Function.Surjective.
  nontrivial` (also confirmed present in current Mathlib4, under
  `Mathlib.Logic.Nontrivial.Defs` — note its direction is "pull back
  nontriviality from the CODOMAIN to the DOMAIN along a surjection",
  i.e. concluding `Nontrivial target` from `Nontrivial (two-step ring)`
  needs the surjection `target → two-step ring`, which is `e'.symm`, NOT
  `e'` — got this backwards in an early draft of this file this same
  pass, caught and fixed before presenting, flagged here as a genuine
  gotcha for whoever touches this lemma next).

**Each of these two finiteness-exporting per-stage theorems adds one
new honest per-stage hypothesis versus its non-finiteness-exporting
counterpart**: `hgu : ¬ IsUnit (mk_A g)` (the newly-appended generator's
image is not itself a unit in the prefix quotient — needed for
`nontrivial_of_span_ne_top` to apply). This is NOT implied by the
existing `hd_unit`/curve-relation hypotheses (see each theorem's own
docstring in `PeelChainStageFinite.lean` for why the two conditions
don't collide) — it is a fresh, honest, per-stage side-condition in the
same spirit as `hd_unit` itself, left for the Assembly file to discharge
against `theData`'s actual values, not asserted here without
justification.

**What is still NOT done, precisely**: these two files supply the
per-stage BUILDING BLOCKS an inductive Assembly proof needs (each stage
now both consumes AND produces `Module.Finite`/`Nontrivial`, so the
induction's base case is genuinely `k` rather than an unreachable prefix
fact) — they do not themselves run the 12-step induction against
`genList`'s literal generators, discharge `hgu`/`hd_unit` against
`theData`'s actual symbolic values, or touch `Bad`/`GenericPeelChainHyp`
at all. The true Assembly file (chaining all 12 stages via `Module.
finrank_mul_finrank` against `FuList ++ FvList ++ [curveA1, curveA2,
curveB1, curveB2]`, using THESE finiteness-exporting theorems rather
than the original non-exporting ones) is still the next concrete step,
and is now actually startable — the base-case obstruction this section
existed to flag is gone, not merely reduced.

## CORRECTION, later pass — the above Progress note's optimism was wrong; the base case is not actually reachable this way

Attempting to actually write `GenListFinrankAssembly.lean`'s
`genList_finrank_le` against `finrank_le_and_finite_of_append`
(`PeelChainAssemblyFinrank.lean`) surfaced that the "base-case
obstruction... is gone" claim above is **false, not merely
optimistic**: `finrank_le_and_finite_of_append`'s own hypothesis
`hfin : Module.Finite k (R ⧸ Ideal.ofList gens)` still has to be
discharged at the TRUE starting point `gens = []`, and `Ideal.ofList []
= ⊥` (`Ideal.ofList_nil`), so that hypothesis unfolds to `Module.Finite
(F p) (Rdec p ⧸ ⊥) ≃ Module.Finite (F p) (Rdec p)` — literally false,
since `Rdec p = MvPolynomial Idx (F p)` is a 12-variable FREE polynomial
ring, infinite-dimensional over `F p`. Route (a) (finiteness flowing
FORWARD via `Module.Finite.trans` inside `finrank_le_of_monic_
annihilator_of_finite`) fixes the induction's DIRECTION, exactly as
diagnosed — but does nothing about the induction's DOMAIN: every ring
in the chain `Rdec p ⧸ Ideal.ofList gens`, for every prefix `gens`
including the empty one, still contains all 12 unpeeled `Idx` variables
free. `OptionSplitPolynomialEquiv.lean`'s own module docstring already
said this outright ("no prefix `gens`... ever makes that ring
finite-dimensional over `F p`") — that file's caveat was the accurate
read; this roadmap's own Progress section above was the stale-optimistic
one, and should be read as superseded by this correction, not as a
completed step.

**Consulted ChatGPT on the right fix — result below, confirmed against
current Mathlib4 (`MvPolynomial.finSuccEquiv` exists exactly as
described, `Mathlib.Algebra.MvPolynomial.Equiv`) before committing to
it.** Verdict: do NOT build a literal `Idx ≃ Option (Option (...))`
chain (twelve bespoke `Option`-nested types, one recognizability lemma
each) even though `optionSplitQuotientAlgEquiv` is stated in exactly
that shape — reindex through `Fin` instead and reuse Mathlib's own
`finSuccEquiv`, which is already built from the same `renameEquiv` +
`optionEquivLeft` machinery `optionSplitQuotientAlgEquiv` re-derives by
hand. Concretely:

1. **Fix the peel order as data, once**: a single explicit equivalence
   `idxEquivFin : Idx ≃ Fin 12` (a 12-line `rfl`-checkable table, e.g.
   `wa1↦0, wa2↦1, wb1↦2, wb2↦3, a1↦4, a2↦5, b1↦6, b2↦7, U0↦8, U1↦9,
   V0↦10, V1↦11` — curve-relation variables first, matching-generator
   variables last, per the ALREADY-RESOLVED Open Questions triangularity
   finding earlier in this document: `FuList`/`FvList`'s coefficients
   depend on the curve variables, so the curve variables must be peeled
   first for each stage's coefficients to already be constants in the
   NOT-YET-peeled ring). `MvPolynomial.renameEquiv (F p) idxEquivFin :
   Rdec p ≃ₐ[F p] MvPolynomial (Fin 12) (F p)` transports the whole
   ambient ring once, up front — no further `Idx`-vs-`Fin`
   bookkeeping needed inside the induction itself.
2. **Generic one-variable peel step, over `Fin (n+1)` not `Idx`**:
   `MvPolynomial.finSuccEquiv (F p) n : MvPolynomial (Fin (n+1)) (F p)
   ≃ₐ[F p] Polynomial (MvPolynomial (Fin n) (F p))`, exactly the object
   `optionSplitQuotientAlgEquiv` already builds by hand for `Option τ` —
   Mathlib's version needs no re-derivation, and its `X 0 ↦ Polynomial.X`
   / `X i.succ ↦ Polynomial.C (X i)` behavior (via `finSuccEquiv_apply`,
   confirmed present) is exactly the recognizability fact each stage's
   generator-matching step needs, supplied once generically rather than
   per-stage.
3. **State the induction generically over `n : ℕ` and `gens : List
   (MvPolynomial (Fin n) K)`, NOT over `Idx` directly** — i.e. write a
   new generic `finrank_peel_fin`-shaped theorem (bounding `Module.
   finrank K (MvPolynomial (Fin n) K ⧸ Ideal.ofList gens)` by induction
   on `n`, base case `n = 0` genuinely trivial: `MvPolynomial (Fin 0) K
   ≃ₐ[K] K` is `Module.Finite K K` for free, unlike the old false
   `Rdec p` base case) and only convert to the literal `Idx`/`Rdec p`/
   `genList` statement at the very end, via `idxEquivFin` from step 1.
   This keeps the twelve `Idx`-specific generator names
   (`Fu0,...,curveB2`) readable in `PeelChainFinrankHyp` and the final
   theorem statement, while the actual induction machinery stays fully
   generic and reusable.
4. **Do NOT reach for `MvPolynomial.pUnitAlgEquiv`/`uniqueAlgEquiv`
   as the main chaining step** — it's the right tool ONLY for the very
   last one-variable-left case (`MvPolynomial (Fin 1) K ≃ₐ[K]
   Polynomial K`, if that shape is ever needed standalone), not for
   iterating the whole 12-step peel; forcing every intermediate stage
   through a `PUnit`/`Option`-flavored presentation is exactly the
   bespoke-bookkeeping overhead this correction is trying to avoid.
   `MvPolynomial.sumAlgEquiv` (splitting `Fin 12` into two blocks at
   once) is a plausible alternative if stages 0–7 vs 8–11 ever need to
   be peeled as two separate batches rather than one generator at a
   time, but is not obviously needed for a straight 12-step induction
   and should only be reached for if the one-at-a-time version proves
   awkward.

**Revised file plan for the true remainder** (supersedes this
document's original item-5 sub-plan; items 1–5's already-landed files
are NOT invalidated — `FinrankLeOfMonicAnnihilator(Finite).lean`,
`CurveRelationStageWiring.lean`/`LinearElimStageWiring.lean`,
`PeelChainStageFinite.lean` all still supply the per-stage `finrank`
BOUND content this new architecture will still call; only the ASSEMBLY
layer changes, from "induct directly on `Ideal.ofList` prefixes of
`Rdec p`" to "induct on `Fin n` via `finSuccEquiv`, converting to the
`Rdec p`/`Ideal.ofList` presentation only per-stage via
`optionSplitQuotientAlgEquiv`-style transport, or possibly bypassing
`optionSplitQuotientAlgEquiv` entirely in favor of `finSuccEquiv`
directly — TBD once the generic peel step is actually attempted, see
Open question below"):

- (a) `idxEquivFin : Idx ≃ Fin 12`, the fixed order table (step 1
  above) — small, standalone, `rfl`-checkable, no dependency on
  anything else in this plan. Do this first.
- (b) The generic `Fin n`-indexed one-step peel lemma (step 2/3 above),
  bounding `finrank` across one `finSuccEquiv` application plus a monic
  annihilator (reusing `finrank_le_of_monic_annihilator_of_finite`,
  already proved) — generic over `K`/`n`/`gens`, no `Idx`/`Rdec p`/
  `theData` content. Self-contained, de-risks the new architecture
  early, same spirit as this roadmap's original item-1 ordering advice.
- (c) The generic `Fin n`-indexed n-stage FOLD (mirroring
  `PeelChainAssemblyFinrank.lean`'s existing `finrank_le_and_finite_of_
  append`, but with the TRUE base case `n = 0` built in rather than
  taken as a hypothesis) — this is where the old false base-case
  assumption gets replaced with a real proof.
- (d) The `Idx`-specific wiring: transporting `genList`'s twelve
  literal generators across `idxEquivFin`/`renameEquiv` to their `Fin
  12`-indexed images, confirming each lands where the peel order
  expects (curve relations at indices 0–3, matching generators at
  4–11), and specializing (c) to conclude the actual `genList_finrank_
  le` statement. Likely the largest single piece of new work in this
  plan — this is where `PeelChainFinrankHyp`'s twelve hypotheses need
  to be restated (or transported) against the `Fin`-indexed generators,
  and where it will become concrete whether `optionSplitQuotientAlgEquiv`
  is still needed at all or whether `finSuccEquiv` directly supersedes
  it for this project's purposes.

**Open question, not yet resolved**: does `OptionSplitPolynomialEquiv
.lean`'s existing `optionSplitQuotientAlgEquiv` become dead code once
(b)/(c)/(d) are built directly on `finSuccEquiv`, or does the `Ideal.
ofList`-quotient presentation (rather than a bare `MvPolynomial`
presentation) still need `optionSplitQuotientAlgEquiv`'s specific
`Ideal.ofList (gens'.map (rename some))`-vs-`Polynomial (... ⧸ Ideal.
ofList gens')` bridge somewhere inside (d)? Likely yes, still needed,
since `genList`'s generators are stated as elements of `Rdec p` being
quotiented by an `Ideal.ofList`, not as an ABSTRACT `Fin`-indexed
polynomial ring with no ideal structure yet — `finSuccEquiv` alone
identifies the RING, `optionSplitQuotientAlgEquiv` is what additionally
carries the IDEAL/GENERATOR-LIST structure across that identification.
Resolve this while attempting (b), not by guessing in advance.

**Not proved, not build-tested — `IdealOfListPerm.lean`'s `Ideal.
ofList_perm`/`Ideal.quotient_ofList_perm_eq` (build-green, REPL-
confirmed by Claire) remain correct and reusable regardless of how this
question resolves — they are order-independent facts about `Ideal.
ofList`, needed either way to transport a bound proved against a
REORDERED/reindexed generator list back onto `genList`'s own literal
stated order.**

## Update, later pass — items (a) and (b) written, not yet REPL-confirmed

**Item (a) — done, not yet REPL-confirmed.** `IdxEquivFin.lean`:
`idxEquivFin : Idx ≃ Fin 12`, the fixed triangular peel-order table —
`0↦wa1, 1↦a1, 2↦wa2, 3↦a2, 4↦wb1, 5↦b1, 6↦wb2, 7↦b2, 8↦U0, 9↦U1, 10↦V0,
11↦V1` (each curve-relation variable immediately followed by its own
sample-point variable, confirmed against `curveA1`/`curveA2`/`curveB1`/
`curveB2`'s actual definitions — `DecoupledSystemRegular.lean` §3 — not
assumed). Both directions closed by `decide` (cheap — finite pattern
match against finite pattern match, no real search).

**Item (b) — done, not yet REPL-confirmed.** `FinSuccSplitPolynomialEquiv
.lean`: the `Fin`-indexed analogue of `OptionSplitPolynomialEquiv.lean`'s
bridge, built directly on Mathlib's `MvPolynomial.finSuccEquiv` (`Fin.succ`
plays the role `some` plays there) instead of re-deriving `renameEquiv`/
`optionEquivLeft` by hand for a bespoke `Option`-nested type per the
ChatGPT-consulted correction above. `finSuccSplitQuotientRingEquiv`/
`finSuccSplitQuotientAlgEquiv` mirror `optionSplitQuotientRingEquiv`/
`optionSplitQuotientAlgEquiv`'s exact statement and proof skeleton
(`Ideal.quotientEquiv` + `Ideal.map_ofList` + `polynomialQuotientEquiv
QuotientPolynomial`, confirmed present and used successfully in the
existing file) with `Fin (n+1)`/`Fin.succ` substituted for `Option τ`/
`some`. **One deliberate proof-safety change versus blindly copying that
file's pattern**: `optionSplitQuotientRingEquiv`'s `hIdealMap` proof
closes its per-generator recognizability fact via `MvPolynomial.
induction_on`, but this file instead proves the underlying RING HOM
equality (`finSuccEquiv K n ∘ (rename Fin.succ) = Polynomial.C`, as
`→+*`s) via `MvPolynomial.ringHom_ext` — checking agreement on `C`/`X`
only — because `induction_on`'s actual Lean 4 case names (`C`/`add`/
`mul_X`, confirmed via direct doc lookup) don't match what a
memory-guess would produce (`h_C`/`h_add`/`h_X`, the Lean-3-flavored
names that seemed initially plausible and were caught and corrected
before presenting), and `ringHom_ext` sidesteps needing those case names
or their exact induction shape at all. Also confirmed via search rather
than assumed: `MvPolynomial.eval₂_X`/`MvPolynomial.coe_eval₂Hom` (the
`eval₂Hom_X'` name floated initially does not appear to exist and was
replaced before presenting) and `MvPolynomial.isEmptyAlgEquiv` (`MvPolynomial
σ R ≃ₐ[R] R` for `[IsEmpty σ]`) — the fact that actually makes `n = 0`
(`Fin 0`, empty) a genuine base case, confirming the whole `Fin`-reindexing
plan actually closes the base-case gap this correction exists to fix,
not just relocates it.

**Not yet done**: item (c) (the generic `Fin n`-indexed n-stage fold with
a real `n=0` base case, using `MvPolynomial.isEmptyAlgEquiv` — mirroring
`PeelChainAssemblyFinrank.lean`'s existing `finrank_le_and_finite_of_
append` but fixing its false-base-case issue) and item (d) (the
`Idx`-specific wiring via `idxEquivFin`, transporting `genList`'s twelve
literal generators and specializing (c) to the real `genList_finrank_le`
statement) are both still open. The Open Question about whether
`optionSplitQuotientAlgEquiv`/its new `finSuccSplit`-named analogue fully
supersedes the old file, or whether both remain needed for different
purposes, is also still unresolved — likely moot in practice since this
pass's `FinSuccSplitPolynomialEquiv.lean` is what item (c)/(d) will
actually use; `OptionSplitPolynomialEquiv.lean` may end up genuinely
unused going forward, a question for whoever does the final cleanup
pass once (c)/(d) are proved.
