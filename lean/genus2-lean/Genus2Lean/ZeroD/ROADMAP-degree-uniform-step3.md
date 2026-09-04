# Roadmap: `decoupledSystem_degree_uniform` (Step 3 of `ROADMAP-alpha-locus.md`)

## Numerical update (this pass) — read this first, then the rewrite notice below

Two independent numerical checks have now been run, outside Lean
(Claire), on one fixed curve with a randomly chosen `(alpha,alpha')`
pair:

1. **Resultant-based check**: the system was solved down to the U,V
   resultants directly (not via homotopy continuation), then two random
   values of `P` were plugged in. No solution was visible. That's the
   expected outcome if the solution variety has dimension ≤ 1 rather
   than the naive 2-dimensional reading.
2. **`HomotopyContinuation.jl` check** (separate run, several
   independent `(alpha,alpha')` pairs): came back 0-dimensional, with
   witness points missing/dropped relative to the expected count,
   consistent across multiple re-runs.

**These two agree**, from independently-run methods. Both are consistent
with the solution variety being finite (0D) rather than the naive 2D
reading.

**Correction to this document's own risk framing (this pass)**: an
earlier version of this document, and of `ROADMAP-alpha-locus.md` and
`ZeroD-README.md`, treated "sweep multiple curves numerically" as a
necessary next empirical step before Obligation 3 could be attempted,
on the theory that `CrossNondegenerate` might fail broadly for some
curve choices in a way that would need to be discovered by trying many
curves. **That framing was wrong.** Per Claire: the peel-chain
operations are a fixed, finite sequence of algebraic steps — there is
no reason to expect qualitatively different behavior curve-to-curve
that a numerical sweep over curves would reveal but a degree-counting
argument wouldn't. `alpha` draws are expected not to matter to the
argument at all, except for the degenerate case `alpha ≡ alpha' (mod
ell)`, which the theorem statement excludes anyway (that's exactly
what `Bad` is for). What actually varies cross-curve is *which specific
values* the fixed resultant expressions take — not the shape of the
argument — so the right next step is to understand the resultant's
**failure modes** directly (i.e. prove degree bounds and characterize
when/why the leading behavior degenerates), not to run more numerical
instances hoping to spot a pattern. See the rewritten Obligation 2/3
sections below — Obligation 2 is now folded into Obligation 3 as "prove
the degree bound, and along the way pin down what makes it fail," not a
separate empirical gate in front of it.

## Rewritten from scratch this pass — read this notice first

The previous version of this document was stale in a way that mattered:
it described `decoupledSystem_degree_uniform` as `sorry`,
`IsSmallExceptionalSet` as a `:= True` stub, and `regularSeq_of_peel_
chain` as having 4 live sorries. **None of that is true anymore.** A
later pass closed all of it — but closed it by introducing a hypothesis
bundle, `GenericPeelChainHyp`, whose own `hfinrank_le` field states the
uniform degree bound *itself*, verbatim, as an assumption:

```
hfinrank_le : Module.finrank (F p) (Rdec p ⧸ Ideal.span (...)) ≤ n
```

and the theorem's own `Bad` is instantiated to `∅` (no exclusions at
all — see `Set.finite_empty` in the current proof). So
`decoupledSystem_degree_uniform` currently typechecks, is sorry-free,
and **proves nothing**: it is "assume the conclusion, thread it through
some bookkeeping, hand the conclusion back" — a circular argument, not
a weakened-but-honest one. This is different in kind from this
project's normal "weaken a false/hard theorem to a named hypothesis"
practice (compare `Nondegenerate`/`CrossNondegenerate`, which name
*specific, checkable, per-instance algebraic facts* — see below):
`hfinrank_le` doesn't name a fact to go check, it just restates the
theorem being proved as its own premise.

**Do not treat "the file builds green" or "no live `sorry`" as evidence
that this step is done.** It isn't. See `STATUS.md` and `README.md` in
this directory for the general version of that warning; this document
is the specific place it bit hardest.

**Explicitly out of scope here**: connecting the resulting theorem to
`Complexity.lean` (a separate, later bridging task — `Complexity.lean`
currently closes the same "Question 4" gap via an unrelated Sidon/
Fourier route and does not import anything from `ZeroD`).

## Where things actually stand, going in (re-verified this pass)

- `decoupledSystem_isRegularSequence`, `decoupledSystem_zeroDimensional`,
  and `regularSeq_of_peel_chain` are all genuinely sorry-free
  (`AlphaLocusDegreeUniform.lean`, `PeelChainAssembly.lean` — confirmed
  by a comment-stripped scan, see `STATUS.md`). Claire confirms the
  whole project currently builds green. Step 3.0 from the previous
  version of this document (close `regularSeq_of_peel_chain`'s 4
  sorries) is done; nothing further needed there.
- `decoupledSystem_degree_uniform` is *stated* correctly — its shape
  (`∃ d Bad, IsSmallExceptionalSet ... ∧ ∀ sa sb, (sa.alpha,sb.alpha)
  ∉ Bad → ...`) is the right target, unchanged from the previous
  version of this document, and does not need to change again. What's
  wrong is entirely in the **proof**, specifically in what got bundled
  into `GenericPeelChainHyp` and how that bundle was then used (assumed
  rather than derived, with `Bad := ∅`).
- The hypothesis chain gating everything is, in increasing order of how
  load-bearing each piece actually is:
  1. **`Nondegenerate`** (×2, one per sample) — 4 fields each, all
     concrete nonvanishing conditions on specific coefficients of
     `uRS`/`vRS`. Narrow, per-instance, plausibly checkable by
     computation for a real curve.
  2. **`CrossNondegenerate`** — 4 `IsSMulRegular` fields. **Its own
     docstring in `DecoupledSystemRegular.lean` states outright**: "this
     is expected to be FALSE for at least some, quite possibly most,
     choices of `(c0,...,c4)`" — Claire's own assessment, made after a
     ChatGPT-assisted debugging session found a genuine counterexample
     shape (`Fu0 = a(1-U)`, `Fu1 = b(1-U)`: both denominators nonzero
     and disjoint, yet `a·Fu1 = b·Fu0` identically — a degeneracy that
     doesn't show up in any per-sample nonvanishing check). This is
     **not a `Reduce`-correctness issue and not obviously a curve-
     geometry issue in the classical sense either** — it's a cross-
     sample resultant regularity condition. **Corrected framing, this
     pass**: an earlier version of this document treated whether this
     fails on a thin `(alpha,alpha')`-sublocus vs. whole curves as an
     open empirical question needing a numerical sweep across curves to
     answer. Per Claire, that's not the right lens: the peel-chain
     operations are fixed and finite, and this is a bounded-degree
     resultant condition amenable to direct degree-counting (Sylvester-
     matrix style, on `uRS`/`vRS`'s known degrees) — a coarse degree
     bound doesn't require a closed form (a symbolic expansion without a
     specific structural target produced an unfactored polynomial, see
     `genus2-index-calculus-advisory-6.md` §12.2, but that's a different,
     harder ask than a degree bound). `alpha`/`alpha'` draws aren't
     expected to matter except at `alpha ≡ alpha' (mod ell)`, which
     `Bad` already exists to exclude. See Obligation 2/3 below for the
     corrected plan: attempt the degree bound directly, and let the
     specific failure-mode conditions fall out of that proof.
  3. **`PeelChainNondegenerate`** — 16 more `IsSMulRegular` fields, one
     variable-peel further into the same cross-sample resultant
     phenomenon `CrossNondegenerate` already flags. Same character,
     same open status, not separately characterized.
  4. **`htop_ne_smul`** — "the 12-generator ideal is proper," i.e. a
     genuine common solution exists. Flagged in-file as real
     existence-of-a-point content, not attempted.
  5. **`hfinrank_le`** — the uniform bound itself, assumed. This is the
     circularity described above, and it's the one item on this list
     that isn't "a specific algebraic fact to go check" — it's the
     theorem restated as its own hypothesis.
- `MatrixNondegenerate` (`det(A) ≠ 0` for the Cantor-reduction
  interpolation matrix) is a *different*, already-fully-characterized
  layer, not part of the above list: `det(A) = -(t1-t2)·u(t1)·u(t2)`,
  factors completely, and every zero of that product already has its
  own dedicated, REPL-confirmed, 0-sorry theorem
  (`AlphaLocusDegreeUniformTangent.lean`,
  `AlphaLocusDegreeUniformTangentTarget.lean`, the four
  `AlphaLocusDegreeUniformCross{1,2,3,4}.lean` files), dispatched by
  `ReducedClassDispatch.lean`. This layer's contribution to `Bad` is
  essentially done. See `genus2-index-calculus-advisory-6.md` §12.1.

## What "done" actually requires — three genuinely separate obligations

Do not try to close these in one pass, and do not let a future pass
collapse them back into one hypothesis bundle the way `GenericPeelChainHyp`
did. Track them separately because they have different risk profiles:

### Obligation 1 — `htop_ne_smul` (solution existence)

Real, but likely the most tractable of the three: showing the
12-generator ideal is proper amounts to exhibiting (or proving the
existence of) an actual common zero — which, for a genuine DLP match,
should exist by construction. Not attempted yet. Low-to-medium risk.

### Obligation 2 — `CrossNondegenerate`/`PeelChainNondegenerate` (cross-sample resultant regularity)

**Corrected framing, this pass**: an earlier version of this document
treated this as something to resolve empirically (numerical sweeps over
curves) before attempting a Lean proof, on the theory that
`CrossNondegenerate` might be false for whole curves in a way only a
sweep would reveal. **That's not the right way to think about this
layer.** The peel-chain construction is a fixed, finite sequence of
algebraic operations — `Fu0..Fv3`'s dependence on `(alpha,alpha')` and
on the curve coefficients is explicit and computable, not something
that needs to be discovered instance-by-instance. The two numerical
checks already run (see "Numerical update" above: direct resultant
solve + `HomotopyContinuation.jl`, one curve, several
`(alpha,alpha')`, both consistent with dimension ≤1/0D) are a useful
sanity check that nothing is grossly wrong, but they are not, and were
never going to be, a substitute for actually deriving the degree bound.

**What the resultant actually is**: `CrossNondegenerate`'s `IsSMulRegular`
conditions come down to a resultant of two polynomials in the peel-chain
variable, each of known, bounded degree in `(alpha,alpha')` (via
`uRS`/`vRS`, themselves `Reduce`'s output — a concretely computable
Cantor-reduction). A resultant of two polynomials of bounded degree is
itself a polynomial of bounded degree in the same variables — that's
Sylvester-matrix degree counting, not open research. The `alpha`/`alpha'`
draws are not expected to matter to *whether this argument goes
through* — only `alpha ≡ alpha' (mod ell)` is a real degeneracy (the two
samples collapsing onto the same target), and that's already exactly
what `Bad` is supposed to exclude. Curve-to-curve variation changes the
*specific numeric value* the resultant polynomial takes at a given
`(alpha,alpha',c0,...,c4)`, not the shape of the degree argument or the
fact that it's a fixed polynomial identity.

**What "failure modes" means here, and why that's proof work, not
sweeping**: the resultant can vanish identically as a polynomial in
`(alpha,alpha')` for special values of `(c0,...,c4)` — that's a genuine
possible degeneracy, and it's exactly the kind of thing Claire's own
in-file counterexample shape (`Fu0 = a(1-U)`, `Fu1 = b(1-U)`) flags.
The right way to find and characterize these is to look directly at the
resultant's structure (when does it factor through a common factor of
`Fu0,Fu1` etc.) — the same kind of analysis that already fully solved
`MatrixNondegenerate`'s `det(A) = -(t1-t2)·u(t1)·u(t2)` factorization,
not a numerical sweep over curve coefficients hoping to spot a pattern.
A general symbolic expansion attempt (advisory §12.2) produced an
unfactored polynomial when tried without a specific structural target;
that doesn't mean the degree bound is hard — a degree bound doesn't
require a closed-form factorization, only a bound on total degree via
Sylvester-matrix-style counting from `uRS`/`vRS`'s own known degrees,
which is directly computable from the construction.

**Revised plan for this obligation**: fold it into Obligation 3 below —
attempt the degree bound directly, and let the specific hypotheses
needed to rule out vanishing (the "failure modes") fall out of that
proof attempt as named, checkable conditions (in the style of
`Nondegenerate`), rather than trying to pre-empt them with numerics.

### Obligation 3 — the actual uniform bound (`hfinrank_le`'s real content)

**Corrected framing, this pass**: this was previously described as
"cannot honestly be attempted until [a numerical sweep] comes back" and
as "comparable in difficulty to anything else in this project." Both of
those overstate the barrier. Per Claire: this is a coarse degree bound
over a fixed, finite sequence of algebraic operations, not open
algebraic geometry — Sylvester-matrix-style degree counting through the
peel chain is a standard, tractable technique, not a research-level
unknown. The uniformity in `(alpha,alpha')` should fall out directly:
`Fu0..Fv3` are polynomial-ish in `(alpha,alpha')` via `Reduce` with
degrees that are fixed and computable from the construction (not
curve-dependent in shape), so a bound on the peel-chain's resultant
degrees gives the uniform bound directly. The one genuine exclusion is
`alpha ≡ alpha' (mod ell)`, which is already what `Bad` exists to
capture — this is not a surprise to be discovered, it's the expected
shape of the theorem.

**This is the actual next work — start now, don't gate it on further
numerics.** Break it into sub-lemmas per peel-chain stage (same
discipline as `reducedClass_eq_of_isReduction'`'s own build: `_flat`
drafts before bundling), and expect the specific nonvanishing conditions
that come out of each stage's degree count to become the honest,
narrow, checkable hypotheses this layer needs (replacing
`CrossNondegenerate`'s current all-or-nothing `IsSMulRegular` framing
with whatever more specific conditions the actual degree-counting proof
requires) — this is where Obligation 2's "failure modes" question gets
answered, as a byproduct of doing the proof, not as a prerequisite to
starting it.

## Proposed order

1. **Attempt the degree bound directly (Obligation 3), broken into
   sub-lemmas per peel-chain stage.** This is now the single
   highest-value next action — do not gate it on further numerical
   sweeping; the two checks already run (see "Numerical update" above)
   are sufficient sanity-check evidence to proceed. Use Sylvester-matrix
   degree counting on `uRS`/`vRS`'s known degrees through the peel
   chain, the same style of argument that already fully solved
   `MatrixNondegenerate`'s factorization. **Scoping for this step's
   first sub-lemma is done** — see
   `ROADMAP-crossnondegenerate-degree-bound.md` (new this pass): the
   `CrossNondegenerate` resultants are polynomials purely in the 8
   sample-local variables (no `(alpha,alpha')`/`(c0,...,c4)` dependence
   as ring variables at all, confirming they're a uniform structural
   bound, not something needing per-instance measurement), built via
   `towerToRdec`'s fixed three-level recursion — that document traces
   the recursion, flags the one genuine technical wrinkle
   (`IsFractionRing.num`/`.den`'s reducedness needs its own small
   degree-monotonicity lemma, not otherwise available off-the-shelf in
   Mathlib), and lays out the concrete next steps.
2. **Let Obligation 2's real content emerge from step 1.** As each
   peel-chain stage's degree bound is proved, note what nonvanishing
   condition it actually needs (the resultant's failure mode at that
   stage) and name it explicitly and narrowly — in the style of
   `Nondegenerate`'s four concrete coefficient conditions — rather than
   inheriting `CrossNondegenerate`'s current broad `IsSMulRegular`
   framing unexamined.
3. **Attempt Obligation 1** (`htop_ne_smul`) in parallel — independent
   of steps 1-2, and likely the cheapest of the three to actually close.
4. **Replace `GenericPeelChainHyp` in `AlphaLocusDegreeUniform.lean`**
   once 1-3 give real content to put in its place — either delete it in
   favor of the actual proved pieces, or keep it strictly narrower
   (dropping `hfinrank_le` specifically, since that field is exactly
   the problem) once the real degree bound and its actual hypotheses
   are established.

## What NOT to do

- **Do not bundle the uniform bound itself into a hypothesis and call
  the theorem "closed."** This already happened once
  (`GenericPeelChainHyp.hfinrank_le`) and is exactly the failure mode
  this rewrite exists to prevent recurring. A hypothesis is honest
  weakening only when it names a *specific, checkable, lower-level
  fact* — compare `Nondegenerate`'s four concrete coefficient
  conditions, which are fine, against `hfinrank_le`, which just
  restates the goal.
- **Don't wait on further numerical sweeps before attempting the degree
  bound.** An earlier version of this document said the opposite; that
  was a misjudgment of how hard this layer actually is (see Obligations
  2-3 above, corrected this pass) — the operations are fixed and finite,
  and a coarse degree bound is standard Sylvester-matrix-style counting,
  not something that needs to wait on empirical screening across curves.
- Don't try to hand-derive `CrossNondegenerate`'s resultant into a
  clean *closed form* the way `det(A)` factored exactly for
  `MatrixNondegenerate` — already tried without a specific structural
  target, produced no useful factorization (advisory §12.2). That's a
  different, harder ask than a *degree bound*, which doesn't need a
  closed form at all — Sylvester-matrix degree counting on the known
  degrees of `uRS`/`vRS` is the right tool and is directly usable
  without any factorization.
- Don't treat "build is green, no sorries" as progress on this specific
  theorem without checking what's inside the hypothesis bundle it
  depends on. Check the bundle's fields against this document's three-
  obligation split before reporting status.
