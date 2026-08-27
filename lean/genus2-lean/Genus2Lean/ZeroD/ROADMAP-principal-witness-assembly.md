# Roadmap: proving `reducedClass_eq_of_isReduction'`

## Goal

`reducedClass_eq_of_isReduction'` (`AlphaLocusDegreeUniform.lean`, ~line
763) is the last un-proved piece of `ROADMAP-reduce-divisor-correctness.md`'s
Step 3: it shows Cantor reduction's output really represents the claimed
Jacobian class. Currently `sorry`. This file tracks only the current state
and the concrete next steps — see `CHATGPT-LOG-principal-witness-assembly.md`
for full consultation transcripts if a past exchange needs re-reading, and
`ROADMAP-principal-witness-assembly-HISTORY.md.bak` for the full pass-by-pass
history this file was compacted from.

## What's already on file (all confirmed 0-`sorry`)

- **`PrincipalWitness.lean`** — 16 lemmas, the general `div(h) = D_old -
  D_new`-style machinery. `eq_of_coeffAt_eq` (`Divisor H` extensionality
  via pointwise `coeffAt`) and `divToPair_eq_of_coeffAt_diff_eq_zero` are
  the two tools the final assembly will call directly. Lemmas 14/15
  (`ordAtFrac_eq_one_of_old_point` / `ordAtFrac_neg_eq_one_of_new_point`)
  are the per-point valuation facts.
- **`AlphaReduce.lean`** (4211 lines — over the 1500-line guideline,
  flagged, not yet split) — `Reduce`/`uRS4`/`vRS4` and the Mumford
  identity for K=4, plus six public point-evaluation wrappers
  (`Epoly4_eval_add_Y_mul_Ypoly4_eval_P1/P2_eq_zero`, and the
  `..._of_root_ua` / `..._of_root_u` forms usable for `Ra1/Ra2/R1/R2`).
- **`GeneralSharedRoot.lean`** — `ReduceGeneral`, `uRS4General`,
  `vRS4General`, and `uRS4General_dvd_Epoly4_add_Ypoly4_mul_vRS4General`
  (the "no named root" divisibility fact for the residual pair).
- **`PrincipalWitnessAssembly.lean`** (3454 lines — over the 1500-line
  guideline, flagged, not yet split) — composes the above into:
  - Six `ordAt_npoly4Lcm4_eq_one_of_{P1,P2,Ra1,Ra2,R1,R2}` theorems
    (fully-split case only, `hRne`/`hRane` required).
  - Six `ordAtFrac_eq_one_of_{P1,P2,Ra1,Ra2,R1,R2}_full` theorems (the
    full old/new-point compositions, same fully-split restriction).
  - Dispatcher lemmas (`ordAtFrac_eq_one_of_four_old_point_cases`,
    `ordAtFrac_neg_eq_one_of_two_new_point_cases`) for the six-way case
    split.
  - `ordAtFrac_eq_neg_one_of_uRS4General_root` — the Mumford-pair
    residual-case theorem (no named root; takes `hsf : Squarefree H.f`
    and `hUfac : ∃ Fco, uRS4General = linX P.X * Fco ∧ Fco.eval P.X ≠ 0`
    as caller-supplied hypotheses).
  - `ordAtFrac_eq_two_of_R1_eq_R2_full`/`ordAt_eq_two_of_R1_eq_R2` (added
    this pass) — the `R1 = R2` repeated-root mirrors of
    `ordAtFrac_eq_one_of_R1_full`/`ordAt_eq_one_of_R1`, for when
    `u_target` is a perfect square. **No `Ra1 = Ra2` mirror exists yet**
    — see the note before "Concrete next steps" below.
- **`OrdAtRootMultiplicityUnified.lean`** (added this pass) — the
  valuation-side generalization behind the `R1 = R2` mirrors above:
  `rootMultiplicity_npoly4Lcm4_eq_add`/`_eq_two_of_R1_eq_R2` and
  `ordAt_npoly4Lcm4_eq_two_of_R1_eq_R2_rootMultiplicity`, none of which
  need `hRne`. See the note before "Concrete next steps" below for how
  this relates to `GeneralSharedRoot.lean` and to step 1.

None of this is yet composed into `reducedClass_eq_of_isReduction'`
itself — that composition is the entire remaining gap.

## BUG FOUND AND FIXED THIS PASS: `u_target`'s roots were silently
## conflated with `uRS4General`'s own roots throughout steps 1-2 below

**The bug.** The previous version of this section's notation defined
`R := [R1]+[R2]` as "the two chosen lifts of `u_new`'s roots" (`u_new :=
uRS4General`, the OUTPUT residual factor). But `PrincipalWitnessAssembly.lean`'s
own `ordAtFrac_eq_one_of_R1_full` — already on file, already proved — has a
docstring stating explicitly and unambiguously: **"`R1, R2` are `u_target`'s
two roots... NOT the residual pair `uRS4General`'s own roots."** `u_target`
is the *input* Mumford quadratic (`X^2+C u1*X+C u0`, fed into the K=4
interpolation as one of `npoly4Lcm4`'s four lcm factors alongside
`(X-P1.x)`, `(X-P2.x)`, `ua`); `uRS4General` is the *output* residual
factor (`Npoly4 /ₘ npoly4Lcm4`, up to a unit) — the whole point of the
"split, no shared root" hypothesis (`hgcd`) is that these two quadratics
are coprime, i.e. have DISJOINT root sets in general. They are not the
same object and do not share roots.

This was caught by re-deriving `deg(div_aff(g))` from first principles
(`deg_div_eq_zero_deg5`: `∑ ordAt = -ordInfOfPair`, giving degree `8` for
`g`, since `ordInfOfPair(Epoly4,Ypoly4) = -8`) and finding it didn't match
the old step 1's claimed `A+C+R` (degree `2+2+2=6`) — a discrepancy of
exactly `2`, which is precisely the degree of the dropped `u_target` term.
`npoly4Lcm4` (degree 6: `1+1+2+2`) is built from FOUR factors, not three —
`(X-P1.x)`, `(X-P2.x)`, `ua`, AND `u_target` — so `g`'s old-point zero
locus (points where `npoly4Lcm4` vanishes to order 1) is genuinely
`A + C + T` where `T := [R1]+[R2]` is `u_target`'s own root-pair (using
Lean's actual `R1,R2` naming), not `A+C+ρ` for `ρ` = `uRS4General`'s roots.
The old step 2 (`div_aff(g)-div_aff(u_new) = A+C-I`) silently dropped `T`
and misidentified `I` (which should be `uRS4General`'s conjugate-root
divisor) with `T`'s conjugate — an unjustified identification of two
different quadratics' root sets.

**Corrected notation** (disambiguating Lean's own `R1,R2` — `u_target`'s
roots — from `uRS4General`'s roots, which no Lean identifier names, per
the Mumford-pair strategy's deliberate choice not to name them):
`g := Epoly4 + Ypoly4·y`, `u_new := uRS4General` (the residual factor).
`A := [P1]+[P2]`, `C := [Ra1]+[Ra2]` (`ua`'s roots), `T := [R1]+[R2]`
(`u_target`'s roots, Lean's own naming — an OLD-support pair, `g` vanishes
here, NOT part of `u_new`'s zero locus). `ρ := [ρ1]+[ρ2]` (`u_new`'s own
two roots, no Lean `H.Point` names them — per the Mumford-pair strategy,
`ordAtFrac_eq_neg_one_of_uRS4General_root` ranges over an abstract `P`
with `P.X` a root of `uRS4General`, not two fixed named points), `I :=
[ι ρ1]+[ι ρ2]` (their hyperelliptic conjugates).

**Do NOT use `divToPairRatio`/`principalSubgroup` for this witness** —
confirmed dead end: `ordInfOfPair(Epoly4,Ypoly4) = -8` vs
`ordInfOfPair(uRS4General,0) = -4` don't match, so `divToPairRatio`'s
exact-pole-order-match requirement can never be satisfied here.

The corrected chain:

1. `div_aff(g) = A + C + T` and `div_aff(u_new) = ρ + I` (both as literal
   `Divisor H` values — `g`'s 6 simple affine zeros, at `npoly4Lcm4`'s
   four-factor root set; `u_new` used bare, with no `y`-dependence,
   vanishes at both lifts of each of its own 2 roots, `ρ1,ρ2` — degree
   4, matching `ordInfOfPair(u_new,0)=-4`). **Not yet proved in Lean** —
   this is where the six `_full` theorems/dispatchers above actually get
   used (for the `A+C+T` side, via `eq_of_coeffAt_eq`), together with
   `ordAtFrac_eq_neg_one_of_uRS4General_root` (for the `ρ+I` side, ranging
   abstractly over `u_new`'s zero locus rather than naming `ρ1,ρ2`).
2. `div_aff(g) - div_aff(u_new) = A + C + T - ρ - I`. **`T` does NOT
   cancel** — `T` (`u_target`'s roots) and `ρ` (`u_new`'s roots) are
   different points in general; nothing here collapses to `A+C-I`. This
   has **no `δ₀` term** — `Divisor H` is affine-only, so nothing here
   should ever carry a `δ₀` correction. `deg = 6 - 4 = 2` — consistent
   with `ordAt_∞ g = -8`, `ordAt_∞ u_new = -4`, net pole-order gap `4`,
   a fact about the point at infinity (not formalized in `Divisor H`,
   and not a `δ₀` fact either).
3. **Re-framing per the caller's own steer, correcting a second error in
   this section's earlier draft.** `T` is not an unwanted residual term to
   be cancelled or absorbed — `T := [R1]+[R2]` (`u_target`'s own two
   roots) IS the theorem's actual target divisor: `isReduction'`'s own
   equation identifies `sa.toSampleTarget.u0,u1` (the `u` fed into
   `curBeforeMonic4General`/`Ypoly4`/`uRS4General` as `u_target`) with the
   goal's own `hu`/`S` data (`u = X^2+C u1*X+C u0`, the same object). So
   `S` (the goal's target support, feeding `divToPair(-v,1,S)`) is
   `T`'s point set or its conjugate — `T`/`ι(T)`, not `ρ`/`I` as the
   earlier draft of this section assumed throughout. `u_new`/`ρ`/`I`
   (`uRS4General`'s own roots) are internal bookkeeping from the Cantor-
   reduction algorithm's factorization identity
   (`Npoly4 = npoly4Lcm4·uRS4General`), not part of the final answer.
   The actual target-divisor-class identity, per the caller's own
   framing: `[P1]+[P2] - alpha·a = [P3]+[P4] - alpha'·a`, i.e.
   `A - alpha·a = (target side) - alpha'·a` for a fixed class `a` (here
   `a` corresponds to `C`/`ua`'s own anchor data, `alpha,alpha'` to
   `sa.alpha`/an implicit reduction factor) — a genuine point-quadruple
   difference, not a single degree-0-on-the-nose intermediate divisor.
   **The pole order at infinity is expected to be nonzero at intermediate
   steps** (`-2` times whatever `a`'s own pole order is, per the caller) —
   chasing `ordInfOfPair`/degree-0-ness of `A+C+T-ρ-I` or similar
   combinations at each intermediate step, as this section's earlier draft
   did, is the wrong test; only the FINAL divisor-class equality
   (`reducedClass = toJacobian D (...)`) needs to hold, and `Divisor0
   H`/`D.P` membership is already handled structurally by `hmem`/
   `hmemAnchor`'s existing `-2•[δ₀]` corrections, not by an independent
   `ordInfOfPair` computation redone here.
4. **Re-derive the `hAlphaRep`-substitution chain (old steps 5-7) from
   scratch with `T` correctly identified as `S`, not as a term needing
   cancellation.** Not attempted in this pass — this needs `Sanchor`/`C`
   on the anchor side related to `A` (via `ρ`/`I`'s role in `g`'s
   factorization) exactly the way `T`/`S` relates to `g` on the target
   side, i.e. the SAME principal-witness argument applied twice (once
   with `(P1,P2,ua)` as the "old" data and `u_target` as unknown-to-be-
   related, once symmetrically) — or possibly a single application
   relating `A` directly to `T` via `g`'s full old-point divisor `A+C+T`,
   with `C`'s own role (anchor) entering through `hAlphaRep` separately.
   This structural question — exactly how `C`/`Sanchor`'s existing role
   in `hAlphaRep` interacts with `T` now being confirmed as the real
   target rather than `ρ`/`I` — is the immediate next thing to work out,
   before any `principalSubgroup`/membership argument is attempted, since
   it determines what actually needs to be shown principal.
5. Once (4) pins down the exact degree-0 divisor that needs
   `toJacobian D (...) = 0`, revisit the membership question
   (`principalSubgroup`/`divToPairRatio` doesn't fit as a single
   generator for `g` vs `u_new` directly, pole orders `-8` vs `-4`
   mismatched — this part of the earlier finding is unaffected by the
   `T`/`S` correction and still stands) against whatever the corrected
   target actually is.

## Concrete next steps, in order

1. **Prove step 1** (`div_aff(g) = A+C+T`, `div_aff(u_new) = ρ+I`) via
   `eq_of_coeffAt_eq`, using the six `_full` theorems/dispatchers and
   `ordAtFrac_eq_neg_one_of_uRS4General_root` already on file — this is
   mechanical composition of existing lemmas already on file, the least
   risky remaining piece. **Read "Note (read before touching step 1)"
   below before starting this** — the six `_full` theorems this step
   depends on are only proved in the `hRne`-requiring (no-repeated-root)
   form today, and `OrdAtRootMultiplicityUnified.lean` (valuation side)
   is the fix for the `R1=R2`/`Ra1=Ra2` case, but it isn't fully wired
   into step 1 yet (only the `R1=R2` half is).
2. **Assemble step 2** (`div_aff(g) - div_aff(u_new) = A+C+T-ρ-I`, no
   `δ₀` term — `Divisor H` is affine-only, see below) directly from (1)
   by `Divisor H`-level subtraction.
3. **Work out step 4** (how `T`'s role as the actual target divisor
   composes with `C`/`Sanchor`'s existing role in `hAlphaRep`) — this is
   the one structural question with no confirmed route yet. Once pinned
   down, the degree-0 divisor that needs `toJacobian D (...) = 0` is
   fully determined and can be discharged directly against `hD :
   principalSubgroup H hdeg ≤ D.P` applied to the `A`-vs-`T` (or
   `C`-vs-`T`) principal-witness identity from (1)/(2) — **no
   `divToPairRatio`/`principalSubgroup`-membership route for `g` vs
   `u_new` itself is needed**: that pairing's pole orders (`-8` vs `-4`)
   are irreconcilable as a single `divToPairRatio` generator (confirmed,
   see "Workflow reminders" below), but the identity this proof actually
   needs is `Divisor H`-level equality between old and new *point*
   divisors (`D_old = D_new`, degree 2 each), not a `divToPairRatio`
   membership claim about `g`/`u_new` at all — `principalSubgroup`
   membership only enters (if at all) one level further out, once (3)
   identifies the genuinely degree-0, principal-divisor-shaped quantity
   `reducedClass_eq_of_isReduction'` needs.
4. **Assemble the rest** into `reducedClass_eq_of_isReduction'`'s proof
   body once (1)-(3) are in hand.
5. Tangent branch (`P1 = P2`) and the Weierstrass sub-case (`P1 = P2 ∧
   Y = 0`, needs lemma 10, `div(x-x0) = 2•[P]`) are separate, smaller
   follow-ups after the general case above is closed.

## Note (read before touching step 1): the affine side (`GeneralSharedRoot.lean`)
## vs. the valuation side (`OrdAtRootMultiplicityUnified.lean`) — how they
## relate to step 1, and what step 1 is NOT yet accounting for

Two files do genuinely different jobs and it's easy to conflate them or
to jump straight to the big `reducedClass_eq_of_isReduction'` assembly
without grounding in either first. Read both before attempting step 1.

**`GeneralSharedRoot.lean` (the affine/quotient side).** This is where
`npoly4Lcm4`, `curBeforeMonic4General`, `uRS4General`, `vRS4General`, and
the flat-product identity `npoly4Lcm4_eq_flat_product` all actually live
(the last three moved here from `PrincipalWitnessAssembly.lean` to break
an import cycle — see its own trailing `/-! ## npoly4Lcm4's flat-product
identity` note). Its whole point: replace the old `P1TargetSharedRoot`/
etc. one-collision-pattern-per-file family with `lcm`-based objects that
divide `Npoly4` and satisfy the Mumford identity UNCONDITIONALLY — no
`h12`–`h34` pairwise-coprimality hypotheses baked into the objects
themselves. `h12`–`h34` (equivalently `hne34`/`hnoroot34`/`hP1ua`/etc.,
the "no two of the six roots coincide" hypotheses) only re-enter later,
as hypotheses on theorems ABOUT these objects (e.g.
`npoly4Lcm4_natDegree_eq_six`, `npoly4Lcm4_eq_flat_product`), not as
constraints on the objects' definitions. This file says nothing about
`ordAt`/valuations at all — it is pure polynomial-ring bookkeeping
(`lcm`, `gcd`, `/ₘ`, `IsCoprime`, `natDegree`).

**`OrdAtRootMultiplicityUnified.lean` (the valuation side).** Takes
`npoly4Lcm4_eq_flat_product` (the affine side's output) and asks: at a
`H.Point` `P` lying over a root `α` of `npoly4Lcm4`, what is `ordAt P
npoly4Lcm4 0`? The existing six `ordAt_npoly4Lcm4_eq_one_of_{P1,P2,Ra1,
Ra2,R1,R2}` theorems (`PrincipalWitnessAssembly.lean`) answer this ONLY
under `hRne : R1 ≠ R2` (resp. `Ra1 ≠ Ra2`) — i.e. only when `ua`/
`u_target` each have two DISTINCT roots — because they route through
`quadratic_eq_mul_X_sub_C`, which needs two named distinct roots to split
a quadratic into linear factors, then Layers 1-3's `linX a * F₁*F₂*F₃`
shape, which needs each `Fᵢ` NONVANISHING at `a` (impossible if `a` is a
double root). `OrdAtRootMultiplicityUnified.lean` bypasses this by
working with `Polynomial.rootMultiplicity` directly (defined for ANY
polynomial, no pre-split needed) composed with `ordAt_eq_rootMultiplicity_
unramified` (`LPairFinrankOneOrdAtFrac.lean`, lemma 6, already 0-`sorry`,
unconditional). Its two "eq_two" theorems —
`rootMultiplicity_npoly4Lcm4_eq_two_of_R1_eq_R2` and
`ordAt_npoly4Lcm4_eq_two_of_R1_eq_R2_rootMultiplicity` — give the
`u_target = (X-C R)^2` repeated-root case's actual `ordAt` value (`2`,
not `1`), which the `hRne`-based six theorems literally cannot state.
`PrincipalWitnessAssembly.lean`'s `PointCompositionR1` section now ALSO
has `ordAtFrac_eq_two_of_R1_eq_R2_full`/`ordAt_eq_two_of_R1_eq_R2` (added
this pass), the `R1=R2` mirrors of `ordAtFrac_eq_one_of_R1_full`/
`ordAt_eq_one_of_R1` — but **only for the `R1`/`u_target` slot**. The
symmetric `Ra1=Ra2`/`ua` repeated-root case has NO mirror yet anywhere —
neither the `rootMultiplicity`-level fact in `OrdAtRootMultiplicityUnified.
lean` nor the assembly-level `_full` theorem in `PrincipalWitnessAssembly.
lean` — this is a real gap, not yet even started.

**Why this matters for step 1, specifically.** Step 1's `A+C+T = div_aff(g)`
claim, proved via the six `_full` theorems, is currently only provable
when EVERY quadratic among `ua`/`u_target` has two distinct roots
(`hRne`/`hRane` both hold) — i.e. step 1 as scoped today silently assumes
the fully-split generic case throughout, the same restriction
`OrdAtRootMultiplicityUnified.lean` exists to lift on the `u_target` side
alone. Concretely:
- If `u_target` is a perfect square (`R1 = R2`), `div_aff(g)`'s `T` term
  is `2•[R1]` (one point, multiplicity `2`), not `[R1]+[R2]` for two
  distinct points — `ordAtFrac_eq_two_of_R1_eq_R2_full`/
  `ordAt_eq_two_of_R1_eq_R2` are the pieces needed for THIS case, already
  on file (this pass).
- If `ua` is a perfect square (`Ra1 = Ra2`), `div_aff(g)`'s `C` term
  needs the same treatment — but nothing exists for this yet. Whoever
  attempts step 1 for the repeated-`ua`-root case needs to FIRST build
  the `Ra1=Ra2` mirror of everything `OrdAtRootMultiplicityUnified.lean`
  + this pass's `PointCompositionR1` additions did for `R1=R2`, before
  attempting the assembly composition itself. Do not try to shortcut this
  by reusing the `R1=R2` theorems with `ua`/`u_target` swapped by hand at
  the call site — the underlying `rootMultiplicity` lemma
  (`rootMultiplicity_npoly4Lcm4_eq_add`) IS already symmetric enough to
  support this (it treats all four flat-product factors uniformly), so
  the mirror should be a comparatively mechanical rewrite of
  `OrdAtRootMultiplicityUnified.lean`'s own repeated-root theorems with
  `ua0,ua1`/`Ra1,Ra2` in `u_target`/`R1,R2`'s slot — but it is NOT yet
  done, and step 1 should not be attempted for this case by assuming it
  already exists.
- The fully-split case (`hRne ∧ hRane` both hold) is unaffected by any of
  this and can proceed with today's six `_full` theorems as-is.

**Practical scoping for step 1, given the above**: either (a) scope step
1's first attempt explicitly to the fully-split case only (`hRne`/
`hRane` as caller hypotheses, matching what the six existing `_full`
theorems already assume) and defer both repeated-root branches as
follow-ups, or (b) if the repeated-`u_target`-root case is specifically
wanted, use this pass's `ordAtFrac_eq_two_of_R1_eq_R2_full`/
`ordAt_eq_two_of_R1_eq_R2` for the `T` term while still assuming `hRane`
(no repeated `ua` root) — a genuine partial case, not the fully general
one. Do NOT attempt the doubly-repeated case (`R1=R2 ∧ Ra1=Ra2`
simultaneously) or the `Ra1=Ra2`-only case until the `Ra1=Ra2` mirror
described above is built first.


## Workflow reminders specific to this file

- Don't reintroduce `Sg`/`Su`/`Starget`/`divToPairRatio` as a membership
  route for `g` vs `u_new` directly — confirmed dead: `ordInfOfPair(Epoly4,
  Ypoly4) = -8` vs `ordInfOfPair(uRS4General, 0) = -4` don't match, so
  `divToPairRatio`'s exact-pole-order-match requirement can never be
  satisfied by this pair. A past pass explored bridging this via a SUM of
  matching-pole-order `divToPairRatio` generators (e.g. via `X^4`/`X^2`
  as pole-order-matched bridges) — never validated, and superseded by the
  direct `eq_of_coeffAt_eq` route (steps 1-2 above), which needs no
  `divToPairRatio` membership claim about `g`/`u_new` at all. Don't
  resurrect the bridging idea without a concrete reason the direct route
  fails.
- **`div_aff(g) - div_aff(u_new)` (steps 1-2) has NO `δ₀` term of any
  kind** — `Divisor H` is affine-only by construction, so nothing here
  should ever carry a `δ₀` correction; `eq_of_coeffAt_eq`'s own docstring
  (`PrincipalWitness.lean`) says so explicitly. Do NOT write `-4•[δ₀]`
  (or any other `k•[δ₀]`) as a correction term on this identity — a past
  pass did, by conflating "pole of order `4` at the point at infinity"
  (`-4∞`, a fact about infinity this project's `Divisor H` deliberately
  doesn't model) with "coefficient `-4` on the affine basepoint `δ₀`"
  (a different, false claim); see
  `CHATGPT-LOG-principal-witness-assembly.md`'s "pass #17" entry for the
  full trace. The ONLY place `δ₀` legitimately appears in this whole
  argument is one level up, in `reducedClass`'s own definition
  (`AlphaLocusDegreeUniform.lean`), which subtracts `2•[δ₀]` once per
  2-point Mumford-pair divisor (`S`, and separately `Sanchor`) to make it
  degree-0 before applying `toJacobian` — that `2•[δ₀]` is unrelated to,
  and not derived from, the `g`/`u_new` pole-order gap.
- `D_new`'s points are `ι(R1), ι(R2)` (hyperelliptic conjugates), not
  `R1, R2` themselves.

## Status update (fresh pass): item 4 re-derived from scratch against the
## CURRENT `reducedClass_eq_of_isReduction'` signature — the exact identity
## still needed, and why it is NOT the same claim Step 1/2 already proved

**Context for this pass.** Re-read `AlphaLocusDegreeUniform.lean`'s actual
current theorem signature directly (not this roadmap's own prose summary of
it, which predates several signature revisions) before doing any algebra.
Confirmed: `hAlphaRep`, `Sanchor`, `va`, `hmemAnchor` are already on file as
hypotheses (not just prose) — the theorem's shape has moved on since this
roadmap's item 4 was last written, and item 4's "structural question" can
now be answered precisely rather than left open-ended.

**The exact identity now needed** (worked out algebraically from the
current signature, using `toJacobian`'s `AddMonoidHom` additivity):

Let `x := ⟨A - 2•[δ₀], _⟩`, `y := ⟨C - 2•[δ₀], hmemAnchor⟩`,
`z := ⟨T - 2•[δ₀], hmem⟩`, all `: Divisor0 H` (`A := [P1]+[P2]`,
`C := [Ra1]+[Ra2]` via `Sanchor`/`va`, `T := [R1]+[R2]` via `S`/`v`, same
`δ₀` throughout).

- `sa.reducedClass = alpha•aClass - toJacobian D x` (definitional, already
  on file).
- `hAlphaRep : alpha•aClass = toJacobian D y` (already a hypothesis).
- Goal: `sa.reducedClass = toJacobian D z`.

Substituting and using additivity, the goal is equivalent to
`toJacobian D (y - x - z) = 0`, i.e.

    (y - x - z) ∈ D.P,  where  y - x - z = C - A - T + 2•[δ₀]  (as Divisor H)

— note **all three `-2•[δ₀]` terms combine to `+2•[δ₀]`**, not to zero;
`δ₀` does NOT cancel away entirely the way it does in `s_add_s_eq_s_add_s_iff`
(`DivisorClassGroup.lean`)'s 2-vs-2-point case, because here it's 3 terms
(`x`,`y`,`z`) each contributing `-2•[δ₀]` combined with a `+`/`-`/`-` sign
pattern, not an even number of terms in matched pairs. **Confirmed via
`hD : principalSubgroup H hdeg ≤ D.P`**: it suffices to show

    C - A - T + 2•[δ₀]  ∈  principalSubgroup H hdeg.

**This is a genuinely different divisor combination from anything Step 1/2
prove.** Step 1/2 give `A+C+T = div_aff(g)` and `ρ+I = div_aff(u_new)` (an
unrelated 6-vs-4-point split, with `ρ,I` — `u_new`'s own roots — not
appearing in `C - A - T + 2δ₀` at all). There is no algebraic manipulation
of `A+C+T-ρ-I` that produces `C-A-T+2δ₀`; these are different linear
combinations of different point sets. **Do not attempt to derive one from
the other by rearranging signs** — a past instinct to do exactly this was
checked and confirmed impossible (they don't even involve the same points:
`ρ,I` vs `δ₀`).

**Checked whether `principalSubgroup` can witness this directly, since it
IS closed under addition (`AddSubgroup.closure`), not just single-generator
membership.** `principalSubgroup H hdeg` (`PrincipalDivisorSubgroup.lean`)
is generated ONLY by `divToPairRatio A₁ B₁ S₁ A₂ B₂ S₂` — differences of two
`toPair`-functions with **matching** `ordInfOfPair` — but a `closure`, so
finite SUMS of such generators are automatically members too, not just
individual matched pairs. This means `C-A-T+2δ₀` being principal does NOT
strictly require `g`/`u_new` (or any single pair) to have matching pole
order — it only requires *some* finite decomposition into matched-pole-order
pieces to exist. This is a strictly weaker (and more plausible) requirement
than the already-confirmed-dead `divToPairRatio(g, u_new)` route, and has
NOT been checked either way — genuinely open, not previously considered in
this form.

**Why this is being handed to ChatGPT rather than attempted directly in
Lean this pass.** Finding the right auxiliary function(s) to build such a
decomposition (if one exists) is real function-field construction work, not
composition of lemmas already on file — the project's own convention is to
ask for help here rather than guess a proof term. A prompt has been drafted
(`CHATGPT-PROMPT-step3-C-A-T-principal.md`, this directory) asking
specifically: (1) whether `C-A-T+2δ₀`'s principality can be exhibited as an
explicit sum of pole-matched `divToPairRatio` generators given what's
already proved (`div_aff(g)=A+C+T`, `div_aff(u_new)=ρ+I`), or (2) whether
this is irreducibly "Cantor reduction's correctness" and needs its own
classical proof (uniqueness of reduced Mumford representatives in a linear
equivalence class), in which case a proof sketch for the K=4→K=2 case
specifically is requested. **Not yet sent.**

**One clarification this pass adds to the earlier "Concrete next steps"
list**: step 3 there ("work out step 4... how T's role composes with
C/Sanchor's role") is now answered structurally (the identity above is the
precise, final target), but proving that identity is NOT the same
remaining-work item as steps 1-2 (which are pure `eq_of_coeffAt_eq`
composition, safe/mechanical) — it is open math, gated on the ChatGPT
consultation above. Do not attempt to close `reducedClass_eq_of_isReduction'`'s
`sorry` by guessing a `principalSubgroup` membership proof for
`C-A-T+2δ₀` without either (a) a decomposition confirmed by the ChatGPT
consultation, or (b) explicit new Lean lemmas establishing it — a plausible-
looking `sorry`-free proof term here that doesn't actually correspond to a
true mathematical fact would be worse than leaving the `sorry` in place.

## Status update (ChatGPT consultation received; SECOND, more serious bug
## found while checking its reply against the actual Lean) — Step 1's own
## claimed identity is incomplete, not just wrongly signed

**ChatGPT's reply (`CHATGPT-REPLY-step3-C-A-T-principal.md`, this
directory — save it there) makes two claims.** First, that no finite sum of
pole-matched `linX`-ratio generators can repair a sign mismatch — a
subtraction-shaped target (`C-A`) cannot be manufactured from an
addition-shaped fact (`A+C+T`) by bridging with fiber-difference-type
generators alone, since those only ever kill already-Jacobian-trivial
fiber relations. This point is accepted: it is a valid general fact about
what `linX`-ratio generators can express, independent of any bug in our
own files. Second, and more consequentially, it flagged that our stated
`div_aff(g)=A+C+T` (degree 6) together with `ord_∞(g)=-8` cannot both be
literally true of a genuine global principal divisor, since global degree
must balance to `0`.

**Checking this against the actual Lean (not the roadmap's prose gloss of
it) found the second claim is right, but for a different, more basic
reason than ChatGPT's own framing (multiple points at infinity) — which
does not apply here at all, see below.**

1. **`divToPair_eq_A_add_C_add_T_of_split` (`PrincipalWitnessStep1.lean`)
   never claims completeness.** Its conclusion is `divToPair E Y
   {six named points} = A+C+T` — literally true, and literally
   `divToPair`'s definition (`∑ P ∈ S, ordAt P E Y • single P`) restricted
   to the given six-point `Finset`. Nothing in the theorem's hypothesis or
   conclusion says `g` vanishes NOWHERE else affine. The roadmap's own
   prose (both the original notation section and this file's status
   notes) has been calling this "`div_aff(g) = A+C+T`" as though it were
   the complete divisor — **that gloss is wrong**, and every downstream
   status note inherited the error uncritically. This is now flagged
   explicitly so it stops propagating.
2. **`g`'s actual complete affine zero-degree is 8, matching
   `ordInfOfPair(E,Y)=-8` via `deg_div_eq_zero_deg5`** (`(∑ affine ordAt) +
   ordInfOfPair = 0`, applied to `g` itself, not to `pairNorm`/`N` — these
   are different applications of the same lemma and should not be
   conflated). So `g` has TWO more affine zeros beyond the six named
   points.
3. **Found the missing two zeros directly, by unfolding `g`/`ḡ`'s
   definitions rather than guessing.** `ḡ(x,y) := E(x)-Y(x)y = g(x,-y) =
   g(ι(x,y))` (immediate from `toPair`'s definition and `Point.iota P =
   (P.X,-P.Y)`, confirmed against `AffinePoints.lean`'s actual `iota_Y`
   lemma, not assumed). `PrincipalWitnessAssembly.lean`'s own residual-case
   proof (`PointCompositionMumfordPairResidualCase` section, the
   `hbar_zero`/`hg_eval` block) already establishes `ḡ(ρ_i)=0` at each of
   `u_new`'s two named roots `ρ1,ρ2` (with the specific lift `P.Y =
   -V(P.X)`) — so by the identity above, `g(ι ρ_i) = ḡ(ρ_i) = 0`. **`g`'s
   complete affine divisor is `A+C+T+[ιρ1]+[ιρ2]`, degree 8** — the two
   missing zeros are the CONJUGATES of `u_new`'s own roots, not anything
   new to construct. Symmetrically, `div(ḡ) = ι(div(g)) = ιA+ιC+ιT+ρ1+ρ2`
   (degree 8), and `N=g·ḡ`'s bare-polynomial 8 roots each lift to 2
   `H.Point`s across the two divisors, consistent with `Npoly4`'s degree 8
   throughout — everything now balances with no contradiction, unlike my
   own first attempt at this same check, which used the wrong comparison
   (`deg(pairNorm)` is a bare-polynomial-degree fact via
   `natDegree_pairNorm_eq_neg_ordInfOfPair`, NOT `ord_∞(g)+ord_∞(ḡ)` added
   together as two independent hyperelliptic pole orders — conflating
   those two is a distinct trap from the one described here, noted so
   nobody re-falls into it).
4. **ChatGPT's own diagnostic framing (possibly-multiple points at
   infinity sharing the pole load) does NOT apply to this project.**
   `H.f.natDegree = 5` (odd-degree model) means a SINGLE ramified point at
   infinity, and `ordInfOfPair`'s `-max(2 deg A, 2 deg B + 5)` formula
   already prices in that ramification (the `+5` term). So the resolution
   here is "Step 1's own theorem was never claiming completeness," not
   "the curve has an extra point at infinity we forgot."
5. **Bigger, structural fact, worth stating plainly: `H.Point` in this
   codebase is PURELY AFFINE.** `DivisorClassGroup.lean`'s own docstring:
   "points at infinity are excluded" — confirmed, there is no
   point-at-infinity type or value anywhere in `AffinePoints.lean` or
   `DivisorClassGroup.lean`. `δ₀ : H.Point` is therefore necessarily an
   AFFINE basepoint — it is not, and cannot be instantiated as, "the point
   at infinity," however natural that would be classically (Mumford
   reduction's usual basepoint). Any future math (ours or ChatGPT's) that
   silently reaches for `δ₀ = ∞`-style reasoning does not typecheck against
   this project's actual types and must be translated into a purely-affine
   argument, or `δ₀` must be treated as a genuinely-abstract affine point
   with no special relationship to infinity assumed.

**Where this leaves `reducedClass_eq_of_isReduction'`.** ChatGPT's
mathematical content (§2-3 of its reply: the real fix is feeding `-A`, i.e.
`ι(A)`, into the interpolation, not `A` itself; the correct construction
uses `C+ι(A)+D_res` shaped divisor identity to get `[C]-[A]=[T]` correctly
signed) still stands and is NOT undone by the completeness bug found this
pass — if anything, the newly-found `g(ιρ_i)=0` fact is a small, concrete
example of exactly the `ι`-conjugation bookkeeping ChatGPT's proof sketch
says is unavoidable. **Do not attempt to patch this by treating the
existing `g` (built via the ORIGINAL `A` orientation, not `ι(A)`) as
already sufficient** — per ChatGPT's §3/§5, this project's current `g` most
likely witnesses the wrong (addition-shaped) relation for what
`hAlphaRep`'s subtraction-shaped target needs, independent of the
completeness bug. A second, corrected function (interpolating through
`C` and `ι(A)`, not `A` directly) is very likely still needed — this pass's
finding only corrects the bookkeeping/degree-accounting bug in the
EXISTING `g`, it does not supply the new function ChatGPT's §5 constructs.

**Concrete next steps, this pass's addition:**
1. Fix this roadmap's own prose (and any downstream file's docstrings that
   copy it) to stop calling `divToPair_eq_A_add_C_add_T_of_split`
   "`div_aff(g) = A+C+T`" outright — it is `g`'s divisor restricted to six
   named points, true and useful, but not complete. Consider proving the
   COMPLETE identity `div(g) = A+C+T+[ιρ1]+[ιρ2]` as a new, separate
   theorem (composing the six existing `_full` theorems with the residual
   case's `hbar_zero`/`ι`-conjugation argument above) — this is likely
   mechanical, using lemmas already on file, and would be honest,
   real Step-1-completing progress regardless of how the ChatGPT
   consultation below resolves.
2. Send a follow-up to ChatGPT (not yet drafted) presenting: (a) the
   corrected complete `div(g)=A+C+T+ιρ` fact from this pass, (b) the
   `H.Point`-is-purely-affine constraint from item 5 above (so `δ₀` cannot
   be `∞`), and (c) ask it to redo its §5 proof sketch entirely within
   this constrained, affine-only, single-ramified-point-at-infinity model
   — its existing §5 sketch freely uses "`2∞`"/"`6∞`"-style terms that may
   not translate directly into a statement about `Divisor H`/`Divisor0 H`
   the way this codebase needs (a principal divisor argument stated with
   an explicit `∞`-coefficient has no home in a type with no
   point-at-infinity slot; the "no `δ₀` term" discipline earlier in this
   roadmap exists for exactly this reason).

## Two-pass Claude audit (this pass): `div(g)` re-derived independently, twice

Requested independently of the ChatGPT consultation above, to check
whether the whole Step-3 difficulty was actually just a misstated
valuation/divisor formula for `g`. Two passes, narrowing each time. Full
transcripts not kept here; findings only.

**Pass 1 (broad audit).** Re-derived, straight from source (not from this
roadmap's own prose): `deg Epoly4 = 4`, `deg Ypoly4 ≤ 1`,
`ordInfOfPair(Epoly4,Ypoly4) = -8` (`ordInfOfPair`'s actual definition,
`PrincipalDivisors.lean:122`), `npoly4Lcm4` has degree 6
(`npoly4Lcm4_natDegree_eq_six`), `uRS4General` has degree 2
(`uRS4General_natDegree_eq_two`), and `Npoly4 = npoly4Lcm4 *
uRS4General` with `deg Npoly4 = 8` (`Npoly4_eq_npoly4Lcm4_mul_uRS4General`,
`Npoly4_natDegree_eq_eight`) — so `6+2=8` exactly, confirming the missing
degree-2 lives in `uRS4General`'s two roots, not in a sign/multiplicity
error on the six named points, and not in a mistranslated `ord∞`. This
matches this file's own "Bigger, structural fact" findings above,
independently re-derived rather than re-quoted. Pass 1 initially described
the residual contribution loosely as "`ρ`"/"`R`" without pinning down
*which* lift (`+v` or `-v`) is `g`'s own zero versus the ratio `g/U`'s
pole — flagged by Claire as the one place the audit moved too fast.

**Pass 2 (narrow follow-up, the ι-labeling question only).** Traced the
sign convention through the actual theorem bodies rather than the
notation:

- `uRS4General_dvd_Epoly4_add_Ypoly4_mul_vRS4General`
  (`GeneralSharedRoot.lean:1171`) proves `U ∣ (E + Y·V)` — literally `g`
  with `y := V := vRS4General` (the `+v` lift) substituted in. So **`g`
  itself vanishes at `(r, +v(r))`** for any root `r` of `U`, unconditionally.
- `ordAtFrac_eq_neg_one_of_uRS4General_root`
  (`PrincipalWitnessAssembly.lean:3247`) is built around the *other* lift:
  its hypothesis `hPY : P.Y = -(vRS4General ...).eval P.X` pins `P` to
  `(r, -v(r))`, and its own proof derives `ḡ(P)=0`/`g(P)≠0` there (comment
  at line 3290: "this is the residual case's actual geometric fact...
  needs `ḡ(P) = 0`/`g(P) ≠ 0`, matching `ordAtFrac_eq_one_of_R1`'s own
  `hbar_zero`-shaped hypothesis, not `g(P) = 0`"). So the ratio `h=g/U`'s
  pole (order `-1`, lemma 13c) sits at the `-v` lift, not the `+v` lift.

Writing `ρ := (r,+v(r))` (`g`'s own zero) and `ι(ρ) = (r,-v(r))` (where
`ḡ` vanishes instead, per `HyperellipticFunctionField.lean`'s
`involution_y`/`AffinePoints.lean`'s `iota_Y : (iota P).Y = -P.Y`, both
confirmed directly): **this exactly reconciles with the "Bigger,
structural fact" finding recorded above in this same file** — that
earlier finding's own `ρ1,ρ2` were defined via the `P.Y = -V(P.X)` lift
(see its point 3: "`u_new`'s two named roots `ρ1,ρ2` (with the specific
lift `P.Y = -V(P.X))`"), i.e. that pass's `ρ` = this pass's `ι(ρ)`, and
that pass's `ι(ρ)` = this pass's `ρ`. **Same underlying fact, opposite
choice of which lift to call the unprimed name** — not a contradiction
between the two passes, once the labeling is made explicit. Recording
both labelings here so neither is mistaken for a live discrepancy later.

**Net, label-independent conclusion (this is the fact to trust, not
either pass's choice of which point to call "`ρ`"):**

```
div_aff(g)      = A + C + T + {the +v-lift pair}          degree 8
div_aff(g/U)    = A + C + T − {the -v-lift pair} − 4·[∞]  (projective; degree 0)
```
with the two lift-pairs being `ι` of each other, `ord∞(g) = -8`,
`ord∞(uRS4General,0) = -4`, hence `ord∞(g/U) = -4` (valuations subtract on
a ratio; verified explicitly, not assumed to cancel to 0 — the *affine*
part `A+C+T−{residual pair}` alone has degree `6-2=4 ≠ 0`, only the full
projective divisor with `−4[∞]` included has degree 0).

**Consequence for the `2[δ₀]` target.** The already-proved lemma-14/15
stack gives `A+C+T = {the -v-lift pair}` only modulo the ratio's own
`4[∞]` pole — it is a genuinely projective identity, not a bare affine
one. This means the original Step-3 target's coefficient `2[δ₀]` cannot
be taken for granted just because the six-point/two-point accounting
degree-matches (`6` vs `2`, needing a "`+4`" of correction one way or
another) — reconciling `reducedClass`'s Abel–Jacobi `[δ₀]` convention
against this `4[∞]`-pole ratio identity (is it `2[δ₀]`, `4[δ₀]`, or does
the fixed-basepoint map absorb the factor differently?) is now the
single concrete open question, and has NOT yet been checked against
`reducedClass`'s literal definition. This is the next narrow thing to
audit, once budget allows — do not re-litigate the `ρ` vs `ι(ρ)` question
above, it is closed and reconciled.

## RESOLVED: the `2[δ₀]` vs `4[∞]` question above — checked directly
## against `reducedClass`'s literal Lean definition, not reasoned about
## in the abstract

The open question above asked whether `reducedClass`'s `2[δ₀]`
coefficient needs to be reconciled with, derived from, or checked
against the `4[∞]` pole order found in the `div(g/U)` computation. It
does not, and cannot — **they are facts about two structurally
unrelated objects, not two accountings of the same quantity.** This was
checked by reading the actual definitions (`AlphaLocusDegreeUniform.lean:
286-330`, `DivisorClassGroup.lean:109-186`), not by re-deriving anything
new.

**Where `2[δ₀]` actually comes from.** `reducedClass` is defined
(`AlphaLocusDegreeUniform.lean:304-314`) as

```
alpha • aClass -
  toJacobian D ⟨single P1 + single P2 - 2•single δ₀, ⟨proof⟩⟩
```

and the `⟨proof⟩` is built by calling `single_sub_single_mem_Divisor0`
**twice** — once for `(P1, δ₀)`, once for `(P2, δ₀)` — and adding:
`(single P1 - single δ₀) + (single P2 - single δ₀) = single P1 + single
P2 - 2•single δ₀`. `single_sub_single_mem_Divisor0`
(`DivisorClassGroup.lean:125-127`) proves `Divisor0 H` membership via
`deg_single_sub_single`, i.e. purely because `deg(single P - single δ₀)
= 1 - 1 = 0` — a counting fact about `Finsupp` degree (`deg` is the
`AddMonoidHom` whose kernel literally defines `Divisor0 H`,
`DivisorClassGroup.lean:119-120`). **There is no `ordAt`, no
`ordInfOfPair`, no pole anywhere in this definition or its proof.** The
`2` is just "two points, individually normalized against a fixed
basepoint `δ₀`, added together" — this is exactly the `s`-map pattern
(`DivisorClassGroup.lean:171-176`, `x ↦ (x)-(δ)`) applied twice and
summed. It would be `2•[δ₀]` for *any* degree-2 affine point divisor
`[P1]+[P2]`, completely independent of what curve, function, or pole
structure produced `P1,P2` — `δ₀` here is not even required to relate
to the curve `H` beyond being one of its points.

**Where `4[∞]` comes from.** It is the literal valuation `ord∞(g/U) =
-4`, i.e. the pole order at infinity of one specific rational function
(`g` divided by `uRS4General`) on this specific curve — a fact that
lives entirely in `ordInfOfPair`'s formula
(`PrincipalDivisors.lean:122`) and has nothing to do with `Finsupp`
degree bookkeeping at all.

**Why no reconciliation is possible or needed.** These aren't two
labelings of one number that happen to both be "4-ish" (`2•2=4`) —
they're outputs of two disjoint computations over two disjoint
universes of objects: `2[δ₀]`'s `2` counts *points in a fixed finite
set* (`{P1,P2}`); `4[∞]`'s `4` measures *the order of vanishing of a
ratio of polynomials at a point that isn't even in this codebase's
point type* (`H.Point` is confirmed affine-only, no infinity
constructor — see "Bigger, structural fact" above, independently
re-confirmed here against `AffinePoints.lean`'s `mk`/`iota`). Nothing
about `ordInfOfPair(g,u_new)` feeds into, constrains, or needs to match
`reducedClass`'s `2•[δ₀]` term. The earlier framing of this as an open
"is it `2[δ₀]` or `4[δ₀]`, does the basepoint map absorb the factor
differently" question was itself still carrying a residue of the
original `4[∞]`-vs-`2[δ₀]` conflation this file diagnosed and fixed
earlier (see "BUG FOUND AND FIXED THIS PASS" above) — restated here so
the file's own ending doesn't relapse into the bug its middle section
already killed.

**What this means for next steps.** `reducedClass`'s `2[δ₀]` is fully
understood and requires no further audit — it's definitional Finsupp
bookkeeping, correct as written, with nothing left to check against the
`g/U` pole-order work. The actual remaining gap is exactly what
"Concrete next steps, this pass's addition" (above) already says:
finish the complete `div(g)=A+C+T+[ιρ1]+[ιρ2]` theorem, then send the
ChatGPT follow-up re-deriving §5 within the affine-only, no-`δ₀`-as-`∞`
constraint. Step 3 (`C-A-T+2δ₀ ∈ principalSubgroup H hdeg`, "Checked
whether `principalSubgroup` can witness this directly" above) is the
live open mathematical question — not this `[δ₀]`/`[∞]` reconciliation,
which is now closed.

## Status update (fresh pass): the `C-A-T+2δ₀` witness question, resolved
## down to a concrete construction target — `-4` is impossible, `-5` with
## one shared residual point `R` is the real target

Three more ChatGPT exchanges this pass (prompts/replies not yet saved as
separate files — summarized here; ask if the raw transcripts are wanted).

**Round 1 finding: the theorem's own `S`/`Sanchor` witnesses (`hv`/`hva`,
i.e. `toPair(-v,1)` for `T`, `toPair(-va,1)` for the anchor `C`) already
have `ordInf = -5` exactly, unconditionally** — `v`/`va` are both
degree-≤1 by construction (`hu`/`hv`/`hva`'s own shape in
`AlphaLocusDegreeUniform.lean`), so `ordInfOfPair(-v,1) =
-(max(2·deg(-v), 2·0+5)) = -5` (the `B`-term `2·deg(1)+5=5` always wins
since `2·deg v ≤ 2 < 5`). This is the CLASSICAL two-point Mumford
`(u,v)`-representation witness (`y - v(x)`), not `g`. `A := [P1]+[P2]`
has the identical-shaped witness via `mumfordB` (`LCanonicalElementary.lean`
— `mumfordB Q₁ Q₂ hne`, degree ≤1 Lagrange interpolation through 2 named
points, with `mumfordB_ordInfOfPair` already proving `ordInfOfPair
(-mumfordB Q₁ Q₂ hne) 1 = -5` exactly, generically, no new work needed for
that fact). So `A`, `C`, `T` are ALL naturally witnessed at `ordInf = -5`,
independent of `g` (which witnesses something different, at `-8`) —
this was a genuinely new fact ChatGPT's earlier replies didn't have.

**Round 1 verdict (checked against ChatGPT): these three `-5` witnesses
alone are NOT sufficient.** Any combination of the pairwise differences
`D_C - D_A`, `D_T - D_A` (the only things `principalSubgroup`'s closure
gives you from 3 pole-matched generators) has coefficients on `D_A, D_C,
D_T` summing to zero — i.e. spans only a rank-≤2 lattice — and expanding
`D_X = X + R_X` (residual degree-3 pieces, since each witness has 5 total
zeros = 2 named + 3 residual), there is no way to isolate `C - A - T +
2δ₀` from that lattice without an EXTRA fact relating the `R_X` residuals
to `2δ₀` — not a formal consequence of the three `-5` facts alone.

**Round 2: asked whether a pole-order-`4` bridge exists instead (`f+`
with `div_aff(f+) = C+2[δ₀]`, `f-` with `div_aff(f-) = A+T`, same `ordInf
= -4`, degree-4 divisors on both sides, no residual term at all — the
"cleanest possible" shape per ChatGPT's own framing).** Verdict:
**impossible in general**, via a clean Riemann-Roch argument, independently
worth recording:

- `L(4∞) = span{1, x, x²}` for this curve shape (`ordInf(x) = -2`,
  `ordInf(y) = -5`; a `y`-term's pole order is always ODD (`2·deg B + 5`)
  while an `x`-only term's is always EVEN (`2·deg A`), so nothing with
  `ordInf = -4` (even) can have a nonzero `y`-part — nothing here is
  specific to this codebase's `Divisor H` model, it's the actual
  classical fact `ℓ(4∞) = 4-2+1 = 3` via Riemann-Roch, genus 2).
- Consequently any `ordInf = -4` function is a bare quadratic `q(x) = ax²
  +bx+c`, and `div_aff(q)` is NECESSARILY of the shape `m₁([P]+[ιP]) +
  m₂([Q]+[ιQ])` — a sum of COMPLETE conjugate fibers with multiplicity,
  since an `x`-only polynomial cannot distinguish a point from its own
  hyperelliptic conjugate (`(x-a)`'s zero locus is always the full fiber
  over `a`). `A = [P1]+[P2]` and `T = [R1]+[R2]` are generic 2-point
  divisors, NOT arranged as conjugate-fiber pairs in general (that's
  exactly what `hR1P1`/`hR1P2`/etc.'s nondegeneracy hypotheses already
  rule out) — so no pole-4 function can have `div_aff = A+T` (or
  `C+2δ₀`) for the generic case this theorem needs to cover.
- At `ordInf = -5` (`ℓ(5∞) = 4`), `L(5∞) = span{1,x,x²,y}` — the extra
  `y` is exactly what permits sheet-separation, matching why the `mumfordB`
  /`(-v,1)` witnesses above first become possible exactly at `-5`, not
  before.

**Round 2 verdict / new target: the realistic bridge is a MATCHED PAIR
of `ordInf = -5` functions sharing ONE common residual point `R`:**

```
div_aff(f+) = C + 2•[δ₀] + [R]      (degree 4 = 2+2, matches ordInf=-5's
                                      "one residual zero beyond degree 4")
div_aff(f-) = A + T + [R]            (same shape, same R)
ordInf(f+) = ordInf(f-) = -5
```

giving `div_aff(f+) - div_aff(f-) = C - A - T + 2•[δ₀]` directly, a single
`divToPairRatio`-shaped principalSubgroup generator — no other
combination needed. `deg(C+2δ₀) = 4` and `deg(A+T) = 4` both being
one short of `5` (the total zero count a genuine `ordInf=-5` function
has, since `(∑ordAt) + ordInf = 0` forces 5 affine zeros) is exactly
why a SINGLE shared residual point `[R]` (not `[R]+[R']` or `0`) is the
right shape — checked via this exact degree arithmetic, not assumed.

**What this needs to actually build in Lean, not yet started:**

1. **`f+`**: a degree-≤2 `b_+(x)` (NOT degree-≤1 like the plain
   `mumfordB`/`(-v,1)`/`(-va,1)` witnesses above — those interpolate
   through only 2 simple points) such that `y - b_+(x)` vanishes
   *simply* at `Ra1, Ra2` (`C`'s two named roots) AND *to order 2* at
   `δ₀` (the `2•[δ₀]` term — a genuine tangency condition: `b_+(δ₀.X) =
   δ₀.Y` AND `b_+`'s derivative at `δ₀.X` matches the curve's own
   implicit-differentiation slope there, `2•δ₀.Y•b_+'(δ₀.X) =
   H.f'.eval δ₀.X`, the standard Mumford/Cantor tangent-row condition).
   Three linear constraints (2 value + 1 derivative) pin down `b_+`'s 3
   coefficients (degree ≤2) via a linear solve — same SHAPE as the
   existing `matrixA4Tangent`/`branchDeriv4`/`tangentRowEntryX4`/
   `tangentRowEntryXY4` machinery in `AlphaReduce.lean` (built for the
   DIFFERENT case of `P1=P2` tangency among the K=4 interpolation's own
   two named points), which is a genuine, reusable PATTERN — same
   derivative-row idea — but not directly callable, since that machinery
   is specific to a 4-points-total interpolation with `P1=P2` as ONE of
   the four, not a 3-points-total (`Ra1,Ra2,δ₀`-doubled) interpolation.
   `R` (the residual point) then falls out as whatever the 5th zero of
   `y-b_+` turns out to be, exactly analogous to how `uRS4General`/`ρ`
   fell out of the K=4 construction as "whatever's left over" — NOT
   separately chosen or constrained in advance.
2. **`f-`**: same shape, interpolating `P1, P2, R1, R2` — wait, that's 4
   points already (degree 4), which would force `ordInf ≤ -8` like `g`
   itself, contradiction. **Re-derive `f-`'s actual shape before coding
   anything** — per the `A+T` target (`A:=[P1]+[P2]`, `T:=[R1]+[R2]`,
   FOUR named points total, not 3), and per Round 2's own degree
   arithmetic (`ordInf=-5` functions have exactly 5 affine zeros, and
   `A+T` alone is already 4 named points), the residual `[R]` here
   would be the ONLY remaining slot — meaning `f-`'s own `b_-(x)` must
   be built by interpolating FOUR named points (`P1,P2,R1,R2`, no
   tangency needed, all simple) via a degree-≤? `b_-`. But `mumfordB`-
   style linear interpolation through `2` points needs `b` degree ≤1;
   through `4` points generically needs `b` degree ≤3 — and `ordInf(y-b)
   = -max(2·deg b, 5)` would need `2·deg b ≤ 4` i.e. `deg b ≤ 2` to stay
   at `-5`, but 4 generic point-constraints need degree ≤3 to solve
   exactly (4 unknowns... a degree-≤3 poly has 4 coefficients, matching
   4 constraints) — **this does NOT obviously fit inside `ordInf=-5`, it
   looks like it wants `ordInf ≤ -7` (`2·3=6 <7`, so `-7`, matching a
   degree-3 `b`), a DIFFERENT parity/order than `f+`'s `-5`.** This
   arithmetic mismatch is NOT yet resolved — before writing any Lean for
   `f-`, re-derive very carefully (by hand, then re-confirm with ChatGPT
   if needed) exactly how many named points `f-` needs to interpolate
   and what `deg b_-` that forces, since the natural first guess
   (`A+T`, 4 named points) does not obviously land at the SAME pole
   order as `f+`'s 3-named-point (`Ra1,Ra2,δ₀`-doubled) construction,
   and `divToPairRatio` needs the two pole orders to match EXACTLY. This
   is the very next thing to work out, before any Lean scaffolding for
   `f-` — `f+`'s construction (item 1 above) is comparatively well-
   scoped and can be started independently in the meantime.

**Not yet attempted in Lean**: neither `f+` nor `f-`'s construction
exists anywhere in the codebase. `AlphaReduce.lean`'s tangent-row
machinery (`branchDeriv4`, `tangentRowEntryX4`, `tangentRowEntryXY4`,
`matrixA4Tangent`) is the closest existing PATTERN for `f+`'s tangency-
at-`δ₀` condition, but is wired for a different (4-points-total,
`P1=P2` tangent) case — reusing the pattern, not the code, is the
plan. No degree-4-anchor-plus-target K=2-style interpolation
(`Epoly`/`Ypoly` in `TheDataDerivation/DataDerivationSolve.lean`) was
found reusable either — checked, it's a K2-tower-abstract construction
for a different downstream purpose (symbolic residual-bound derivation),
degree pattern doesn't match what's needed here (`ordInf=-5` via
`E`-degree-≤2, `Y`-degree-0 — i.e. also NOT what `f+`/`f-` need, since
those need `Y` non-constant to carry the tangency/4-point information).

**Update within this same pass: the `f-` degree question above worked out
by hand (classical CRT Cantor addition), not yet re-confirmed by ChatGPT
(prompt sent, reply pending).** `f-`'s natural construction is the
STANDARD Cantor "addition" step for two degree-2 Mumford pairs
`(u1,v1) := A`, `(u2,v2) := T`: solve `v ≡ v1 (mod u1)`, `v ≡ v2 (mod
u2)` via CRT (`deg u1 = deg u2 = 2` ⟹ `deg v ≤ 3`, one degree higher
than `f+`'s `deg b_+ ≤ 2`), giving `ordInf(y-v) = -max(2·3,5) = -6`, and
`u3 := (f - v²)/(u1·u2)` has degree `max(5, 2·3) - 4 = 6-4 = 2` — **a
DEGREE-2 residual `R` (two points), not the degree-1 single residual
point this section's item 2 originally guessed.** This makes `f-`'s pole
order `-6`, one more than `f+`'s `-5` — **the two sides as scoped do NOT
match**, contradicting `divToPairRatio`'s exact-pole-order-match
requirement, exactly the kind of mismatch ChatGPT's own diagnostic
process has caught twice already in this file (the `g`/`h` `-8`-vs-varies
mismatches above) — flagging immediately rather than building Lean
against unconfirmed arithmetic. **Not yet resolved**: whether `f+` needs
upgrading to also carry a degree-2 residual (matching `-6`), or whether
`f-`'s 4-point target can be reformulated with a smaller residual some
other way. ChatGPT consultation sent this pass, reply pending — check
for it before starting `f-`'s Lean construction. `f+`'s construction
(item 1, previous section) is unaffected by this specific question and
can proceed independently.

**Update within this same pass: found and fixed a real miscount while
starting `f+`'s Lean scaffolding — resolves the `f+`-vs-`f-` pole-order
mismatch above WITHOUT needing the pending ChatGPT reply.**

While drafting `f+`'s 3×3 tangent-interpolation linear system
(`tangentInterpMatrix`/`tangentInterpRHS`, degree-≤2 `b_+`, 3 conditions:
value at `Ra1`, value at `Ra2`, DERIVATIVE-only at `δ₀`), realized the
derivative-only row at `δ₀` is wrong: "vanishes to order `2` at `δ₀`"
for `y - b_+(x)` needs BOTH `δ₀.Y = b_+(δ₀.X)` (value, order ≥1) AND the
branch-derivative condition (order ≥2) — TWO conditions at `δ₀`, not one.
`AlphaReduce.lean`'s own `P1=P2` tangent-row precedent
(`matrixA4Tangent`) confirms this: its own row 0 (ordinary evaluation)
and row 1 (derivative) are BOTH present for the single tangent point —
this file's original draft only ported row 1's idea and dropped row 0's
counterpart for `δ₀`, an asymmetry that was wrong on inspection, not a
subtle new fact.

**Corrected condition count: 4 total** (1 value at `Ra1`, 1 value at
`Ra2`, 1 value + 1 derivative at `δ₀`), needing **`b_+` of degree ≤3**
(four coefficients), not ≤2. This changes `f+`'s own pole order:
`ordInf(y-b_+) = -max(2·3, 5) = -6`, matching `f-`'s independently-
derived `-6` from the Cantor-addition computation above **exactly** —
the two sides now match without needing any further adjustment, and
without needing to wait on the ChatGPT reply already sent (that
consultation is still worth reading when it arrives, as a
cross-check, but is no longer blocking). Residual-degree check: `f+`
has `ordInf=-6` ⟹ 6 affine zeros ⟹ `2 (Ra1,Ra2, simple) + 2 (δ₀, mult.
2) + deg R = 6` ⟹ `deg R = 2`, matching `f-`'s own `deg R = 2` (from
`u3`'s degree in the Cantor-addition computation) exactly as well —
both the pole order AND the residual degree now agree on both sides,
which is the actual requirement for `divToPairRatio`, not just the pole
order alone (the residual `R`s themselves still need to be shown to be
literally the SAME degree-2 divisor on both sides for the final
cancellation `div_aff(f+)-div_aff(f-) = C-A-T+2δ₀` to go through — not
yet checked, is the next thing to verify once both constructions exist
concretely).

**Revised construction target for `f+`:** `b_+` degree ≤3 (four
coefficients), solving a 4×4 linear system: value-rows at `Ra1.X`,
`Ra2.X`, `δ₀.X` (three ordinary evaluation rows, `(1,x,x²,x³)` each) plus
one derivative row at `δ₀.X` (`(0,1,2x,3x²)` evaluated there) — same
`tangentRowEntryX4`-style derivative-coefficient pattern as before, just
sized to degree-3 basis and with the value-row for `δ₀` now correctly
included as its own 4th row. Not yet re-drafted in Lean (previous
3-row/degree-≤2 draft deleted as wrong before being saved anywhere
committed) — the 4×4 version is next.

## Status update (fresh pass): `f-`'s scaffolding started — `CantorAddWitness.lean`

`f+` (item 1 above, `TangentMumfordWitness.lean`) is confirmed 0-`sorry`
and build-green (Claire's REPL). This pass starts `f-` (item 2): a new
file, `CantorAddWitness.lean`, with `bMinus`/`cantorAddMatrix`/
`bMinusCoeff` — the degree-≤3 `b_-` solving `b_- ≡ vC (mod uC)`,
`b_- ≡ -vA (mod uA)` (the `-vA` sign is the `ι(A)` substitution
`CHATGPT-REPLY-step3-reduce-correctness.md` identifies as necessary —
feeding `C + ι(A)` into the Cantor-addition interpolation, not `C+A`,
so the output witnesses the subtraction `C - A` the theorem actually
needs).

**Design choice made this pass, worth recording:** a direct hand-derived
Bezout/CRT closed form was tried first (`s·uC+t·uA=1`, then combine with
`vC,vA`) and abandoned — correct but each of `v`'s 4 coefficients came
out as a ratio of degree-4-in-`(a0,a1,c0,c1)` polynomials over their
shared resultant, unwieldy to encode faithfully in Lean by hand. Used
the same 4×4-Cramer's-rule idiom `bPlus` already established instead:
unfold the two congruences directly into 4 linear equations on `b_-`'s
own 4 coefficients (no Bezout identity, no root-splitting), confirmed
against sympy's `Poly.rem` before writing any Lean. The resulting
matrix's determinant is confirmed (sympy) to equal `Res(uC,uA)` — a
clean, well-understood invariant, nonzero exactly under coprimality.

**This pass's file is scaffolding only — 4 `sorry`s remain**
(`cantorAddMatrix_det_ne_zero`, `bMinus_mod_uC_eq_vC`,
`bMinus_mod_uA_eq_neg_vA`, and implicitly `bMinus_ordInfOfPair` which
isn't even stated yet). Per this project's convention (errors/sorries
are normal, ship the shape first), this was written and left rather
than blocking on closing every proof this pass. Not yet build-tested —
Claire's REPL next.

**Concrete next steps for `f-`:**
1. Close `cantorAddMatrix_det_ne_zero` — likely `Matrix.det_succ_row_zero`
   down to `Matrix.det_fin_three` + `ring` (same recipe as
   `tangentInterpMatrix_det_ne_zero`), landing on the `Res(uC,uA)` closed
   form, then relate `≠ 0` to `hcoprime` via
   `Polynomial.resultant`-family lemmas (search Mathlib4 docs for the
   exact resultant-nonvanishing-iff-coprime statement — not yet looked
   up this pass).
2. Close the two `bMinus_mod_*` row lemmas — same `bPlus_row_eq`-style
   Cramer's-rule unfolding (`Matrix.mulVec_cramer`), then relate the
   resulting coefficient sum back to `%ₘ` via `Polynomial.mod_by_monic`
   lemmas (the quadratics `uC,uA` are monic by construction, needed for
   `%ₘ` to behave as ordinary division).
3. Once (1)-(2) are in hand, add `bMinus_ordInfOfPair` mirroring
   `bPlus_ordInfOfPair` (`hlead`-style hypothesis on `bMinusCoeff ... 3`,
   giving `-6`).
4. **Not yet drafted, genuinely open, ChatGPT-worthy per this project's
   own convention (deep function-field construction, not lemma
   composition):** the actual residual/divisor-level facts —
   `div_aff(y - bMinus) ⊇ A + T` (or the `ι`-conjugated version matching
   whichever sign convention (2) lands on) and the matching degree-2
   residual `[R]`, PLUS confirming this `R` is the SAME `R` as `f+`'s own
   residual (the roadmap's whole point in pairing `f+`/`f-`). This is the
   next thing to hand to ChatGPT once (1)-(3) are closed and the exact
   sign/labeling conventions are pinned down in Lean rather than guessed
   in prose.

## Status update (fresh pass): `f-`'s scaffolding now 0-`sorry`

All 3 remaining `sorry`s in `CantorAddWitness.lean` closed this pass:
- `cantorAddMatrix_det_ne_zero`: closed directly from `IsCoprime`, no
  resultant needed — found `Matrix.exists_mulVec_eq_zero_iff`
  (`Mathlib.LinearAlgebra.Matrix.ToLinearEquiv`) gives a nonzero kernel
  vector `b` from `det = 0`; its 4 rows unfold (via the same
  `modByMonic_uCPoly_eq`/`modByMonic_uAPoly_eq` closed forms used
  elsewhere in the file, at `vC=vA=0`) to `q %ₘ uCPoly = 0` and
  `q %ₘ uAPoly = 0` for `q := ∑ C(b i)*X^i`; coprimality then gives
  `uCPoly*uAPoly ∣ q` (degree 4), contradicting `deg q ≤ 3` unless
  `q = 0`, which forces `b = 0` (`q`'s coefficients ARE `b`'s entries),
  contradicting `b ≠ 0`.
- `bMinus_mod_uC_eq_vC`/`bMinus_mod_uA_eq_neg_vA`: closed via a shared
  `modByMonic_uCPoly_eq`/`modByMonic_uAPoly_eq` pair (explicit
  quotient-remainder identity, sympy-confirmed, plus
  `Polynomial.div_modByMonic_unique`) composed with a `bPlus_row_eq`-style
  Cramer's-rule row extraction.

`CantorAddWitness.lean` is now 507 lines, 0-`sorry`, matching `f+`'s own
status. **Not yet build-tested** — Claire's REPL next, as always.

**Concrete next steps for `f-`, updated:**
1. ~~Close `cantorAddMatrix_det_ne_zero`~~ **Done this pass.**
2. ~~Close the two `bMinus_mod_*` row lemmas~~ **Done this pass.**
3. ~~Add `bMinus_ordInfOfPair` mirroring `bPlus_ordInfOfPair`~~ **Done
   (fresh pass): `bMinus_ordInfOfPair` added to `CantorAddWitness.lean`,
   same weakened `hlead : bMinusCoeff ... 3 ≠ 0` shape as `f+`'s own
   theorem, giving `ordInfOfPair(-bMinus,1) = -6` — matches `f+`'s `-6`
   exactly, confirming both sides of the roadmap's "Round 2 verdict"
   matched-pole-order pairing now exist concretely in Lean, not just in
   the hand-derived arithmetic above. `CantorAddWitness.lean` is now 578
   lines, still 0-`sorry`. Not yet build-tested — Claire's REPL next.**
4. **Still genuinely open, ChatGPT-worthy per this project's own
   convention:** the residual/divisor-level facts — `div_aff(y -
   bMinus) ⊇ C + ι(A)` (matching the sign convention already fixed:
   `bMinus ≡ -vA mod uA`, i.e. the witness vanishes at `A`'s
   HYPERELLIPTIC CONJUGATE, not `A` itself) plus the matching degree-2
   residual `[R]`, and confirming this `R` is the SAME `R` as `f+`'s own
   residual. This is the next thing to hand to ChatGPT — (1)-(3) are now
   fully closed and BOTH pole orders (`f+`'s `-6`, `f-`'s `-6`) are
   pinned down in actual Lean, not guessed in prose, so the prompt can
   state the matched-pole-order fact as an established lemma rather than
   an open arithmetic claim.
