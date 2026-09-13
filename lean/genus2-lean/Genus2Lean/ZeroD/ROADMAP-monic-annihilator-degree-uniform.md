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
  or only regularity?** These hypotheses were added to fix a
  regularity gap (`gapA_disjoint_bridge`'s hypotheses being
  unsatisfiable for this project's actual variable-sharing pattern,
  per ChatGPT's own counterexample at the time). Regularity
  (non-zero-divisor) and "leading coefficient is a unit" are related
  but not obviously identical conditions here — check directly rather
  than assuming one implies the other.
- **Where does `Bad`'s eventual size land?** Not decided yet — depends
  on the answer above. If the stage-4–7 unit conditions turn out to
  split cleanly per-sample (one depending only on `sa`'s data, the
  other only on `sb`'s), `Bad` lands in the cheap `O(D)` case from
  ChatGPT's own table; if they genuinely entangle `alpha` and `alpha'`
  together the way the *regularity* obstruction did, expect `O(D·p)`
  instead, which may or may not be "small" in the sense
  `IsSmallExceptionalSet` actually needs — check that definition
  before assuming either outcome is acceptable.
- **Symbolic vs. mod-`p` nonvanishing** (ChatGPT's point 3): the
  project's whole tower is built symbolically over `(c0,...,c4)` before
  specializing to a fixed `p`. A leading-coefficient-is-a-unit
  condition proved symbolically nonzero can still vanish after
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
