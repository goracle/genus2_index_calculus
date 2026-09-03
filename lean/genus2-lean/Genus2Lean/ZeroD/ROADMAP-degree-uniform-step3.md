# Roadmap: `decoupledSystem_degree_uniform` (Step 3 of `ROADMAP-alpha-locus.md`)

## Scope of this document

`ROADMAP-alpha-locus.md`'s Step 3 says, in one paragraph: extend the
existing regular-sequence machinery to track how it varies with
`(alpha,alpha')`, via showing `Nondegenerate`/`CrossNondegenerate`/
`PeelChainNondegenerate`'s resultants are bounded-degree polynomials in
`(alpha,alpha')`, so degree jumps are confined to a small vanishing
locus. This document breaks that paragraph into concrete, ordered,
checkable pieces, using what a separate investigation this pass
actually found about the shape of those resultants (see
`genus2-index-calculus-advisory-6.md` section 12, added this pass) —
so this is Step 3 scoped against real findings, not a restatement of
the one-paragraph sketch.

**Explicitly out of scope here**: connecting the resulting theorem to
`Complexity.lean` (a separate, later bridging task; see that file's own
docstring and this session's discussion — `Complexity.lean` currently
closes the same "Question 4" gap via an unrelated Sidon/Fourier route
and does not import anything from `ZeroD`).

## Where things actually stand, going in

- `decoupledSystem_degree_uniform` (`AlphaLocusDegreeUniform.lean` line
  887) is `sorry`. Its statement already quantifies correctly over
  `sa sb : SampleTargetFromAlpha p H D aClass δ₀` and an existential
  `Bad`/`d`, so the STATEMENT does not need to change — only the proof
  and `IsSmallExceptionalSet`'s definition (currently `:= True`, a
  named stub, `AlphaLocusDegreeUniform.lean` line 839).
- `decoupledSystem_isRegularSequence`/`decoupledSystem_zeroDimensional`
  (the FIXED-target, `alpha`-free case) are the base this generalizes.
  The latter was closed this session (via
  `RegularSequenceFiniteQuotient.lean`'s
  `Module.Finite.quotient_of_isRegular_of_length_eq_card`) but **not
  yet REPL-confirmed** — confirming it should happen before or
  alongside this roadmap's work, since everything below builds on top
  of it.
- `regularSeq_of_peel_chain` itself (which
  `decoupledSystem_isRegularSequence` calls) still has **4 live
  `sorry`s**, in `regularSeq_of_peel_chain_assembly`'s stages 4-7
  (`Fv0`-`Fv3`), per `ROADMAP-peel-chain-assembly.md`'s own current
  status. That doc says the remaining content is wiring
  (`PeelChainNondegenerate.hv0_A/hv1_B/hv2_A/hv3_B` plus
  `gapA_disjoint_bridge`), not open mathematics — but it is still open,
  and this roadmap's Step 3.0 below treats closing it as a genuine
  prerequisite, not something to route around.
- Three nondegeneracy hypothesis bundles gate the whole chain:
  `Nondegenerate` (per-sample), `CrossNondegenerate` (cross-sample,
  repeated-target), `PeelChainNondegenerate` (cross-sample, one
  variable-peel further + curve-relation regularity). This session's
  investigation (advisory section 12) characterized the FIRST
  ingredient feeding all three — `MatrixNondegenerate`, `det(A) ≠ 0`,
  needed just for `uRS`/`vRS` to be well-defined at all — completely:
  `det(A) = -(t1-t2)*u(t1)*u(t2)`, and every zero of that product
  already has its own dedicated, REPL-confirmed, 0-`sorry` theorem
  (the tangent/tangent-target/cross1-4 family, dispatched by
  `ReducedClassDispatch.lean`). `Nondegenerate`/`CrossNondegenerate`/
  `PeelChainNondegenerate` themselves were NOT found to have a clean
  closed form — `CrossNondegenerate` in particular is flagged in its
  own docstring as possibly failing for whole curves, not just a thin
  `(alpha,alpha')` locus, and no closed-form resultant was found (a
  direct symbolic attempt produced an unenlightening, non-factoring
  polynomial — see advisory section 12.2).

## Proposed order

### Step 3.0 — Close `regularSeq_of_peel_chain`'s remaining 4 `sorry`s

Prerequisite, not optional: `decoupledSystem_isRegularSequence` (hence
everything downstream, including the uniform-in-`alpha` version this
roadmap targets) calls `regularSeq_of_peel_chain`, which is not yet
`sorry`-free. Per `ROADMAP-peel-chain-assembly.md`'s own "TL;DR,
current as of the very last section," this is wiring
(`PeelChainNondegenerate`'s already-named fields into
`gapA_disjoint_bridge`, stages 4-7), not new mathematical content — but
should be finished and REPL-confirmed before Step 3.2 below invests
effort in the harder degree-bound question, so that the object being
generalized is itself solid.

**Also do at this step**: get Claire to run `lake build`/REPL on
`decoupledSystem_zeroDimensional`'s new proof (this session's work,
`AlphaLocusDegreeUniform.lean` line ~1016) — flagged in that file's own
"What's left to do" section as "not yet compiled against Claire's
REPL." Cheap to confirm now, before building further on top of it.

### Step 3.1 — Pin down `Bad`'s real definition, in two layers, not one

The single `Bad : Set (ℤ × ℤ)` in `decoupledSystem_degree_uniform`'s
current statement is too coarse for what was actually found this
session. Two structurally different failure modes feed it (advisory
section 12), and they should be named separately before being unioned:

1. **`MatrixNondegenerate`'s locus** — already fully characterized
   (section 12.1): a thin, codimension-≥1 set in `(t1,t2,u0,u1)`-space
   (equivalently, once Step 1's `alpha`-parametrization is used, in
   `(alpha,alpha')`-space for FIXED curve coefficients), and already
   handled case-by-case by existing, dispatched theorems. This layer
   is essentially ready to fold into `Bad`'s definition now — it does
   not need new Lean content, only assembling the existing dispatcher
   machinery's domain-of-applicability into a literal `Set (ℤ × ℤ)`
   term (see Step 3.3 below).
2. **`CrossNondegenerate`/`PeelChainNondegenerate`'s locus** — NOT
   characterized. Per advisory section 12.2, this may depend on the
   curve coefficients `(c0,...,c4)` themselves in a way that isn't
   confined to a small `(alpha,alpha')`-sublocus for bad curves. This
   is the roadmap's genuinely open item, and per this project's own
   "settle on paper/numerically first" discipline, should not be
   guessed at in Lean before Step 3.2's numerical check comes back.

**Concrete action, no Lean yet**: run the check advisory section 12.3
already specifies (Cantor-reduce both samples, cross-multiply the four
`U0,U1,V0,V1` coefficient pairs, check nonzero mod `p`) across (a)
multiple `(alpha,alpha')` pairs on ONE curve, and (b) multiple curves
(varying `c0,...,c4`), to see empirically whether failures cluster on a
thin `(alpha,alpha')` sublocus (good — matches `MatrixNondegenerate`'s
pattern, `Bad` stays a set in `(alpha,alpha')`-space) or spread across
whole curves (bad — `Bad`'s definition needs a curve-coefficient
dependence too, materially changing `decoupledSystem_degree_uniform`'s
statement, likely by adding a curve-genericity hypothesis rather than
folding curves into `Bad` itself). **Do this before Step 3.2** — it is
the cheap check that determines whether Step 3.2's Lean work is even
aimed at a true, useful statement, exactly as `ROADMAP-alpha-locus.md`'s
own Step 2 already argued for the system's dimension as a whole.

### Step 3.2 — The genuinely open mathematics: bounded-degree resultants in `(alpha,alpha')`

This is `ROADMAP-alpha-locus.md`'s own Step 3 paragraph, now scoped by
3.1's split:

- For the `MatrixNondegenerate` layer, the degree bound is already
  implicit in the closed form: `det(A) = -(t1-t2)*u(t1)*u(t2)` is
  degree 1 in `(t1-t2)` and degree 2 in each of `u(t1),u(t2)` — once
  `t1,t2` and `u0,u1` are expressed as functions of `(alpha,alpha')`
  via Step 1's `SampleTargetFromAlpha`/`Reduce` connection, this is a
  concrete, low-degree polynomial in `(alpha,alpha')` to write down and
  bound. This piece looks tractable NOW, independent of 3.1's numerical
  check's outcome.
- For the `CrossNondegenerate`/`PeelChainNondegenerate` layer: blocked
  on Step 3.1's numerical check. If the check shows a thin
  `(alpha,alpha')`-sublocus (per curve), the same style of degree-bound
  argument applies, but the resultant itself has no known closed form
  (advisory 12.2's symbolic attempt produced an unfactored mess) — so
  the degree bound would need to come from general resultant-degree
  bounds (e.g. Sylvester-matrix-style degree counting in the inputs'
  own degrees, which ARE known — `uRS`/`vRS` are bounded-degree
  rational functions of `(t1,t2,u0,u1)`, themselves polynomial in
  `(alpha,alpha')` via Reduce) rather than an explicit factorization.
  If the check instead shows whole-curve failures, this step is
  blocked on a different, harder question (which curves are "good") and
  should be re-scoped before continuing — flag back to Claire rather
  than guessing.

### Step 3.3 — Assemble `IsSmallExceptionalSet`/`Bad` in Lean and attempt the proof

Only after 3.1-3.2 give a concrete, checked candidate: replace
`IsSmallExceptionalSet`'s `:= True` stub with the real predicate (per
`ROADMAP-alpha-locus.md`'s own preference, "better, an explicit small
count" over a purely qualitative notion — the `det(A)` factorization
already gives an exact, small polynomial-vanishing-locus count for
layer 1), and attempt `decoupledSystem_degree_uniform`'s proof itself,
via `decoupledSystem_isRegularSequence`/`_zeroDimensional`'s existing
machinery extended to track degree-in-`(alpha,alpha')` through the peel
chain, per the strategy `ROADMAP-alpha-locus.md` already sketches.
Break into sub-lemmas per peel-chain stage rather than one theorem, per
this project's existing discipline (`_flat` drafts before bundling,
dispatched over cases only once each piece is separately proved) —
matching how `reducedClass_eq_of_isReduction'` itself was built.

## What NOT to do

- Don't attempt Step 3.2's `CrossNondegenerate` degree bound before
  Step 3.1's numerical check comes back — per advisory section 12.2,
  there is a live possibility the needed statement is false as
  currently scoped (whole-curve failure), and proving a degree bound
  for a false statement is wasted work, not merely risky work.
- Don't try to hand-derive `CrossNondegenerate`'s resultant into a
  clean closed form the way `det(A)` factored — this was tried this
  session (advisory section 12.2) and produced no useful structure;
  the productive route for that layer is numerical screening (3.1) and
  general degree-counting (3.2), not another factorization attempt.
- Don't skip Step 3.0 (the peel chain's own remaining 4 `sorry`s) to
  get to the "more interesting" degree-uniform question sooner — the
  degree-uniform proof extends `regularSeq_of_peel_chain`'s machinery,
  so an unclosed prerequisite there is an unclosed prerequisite here.
