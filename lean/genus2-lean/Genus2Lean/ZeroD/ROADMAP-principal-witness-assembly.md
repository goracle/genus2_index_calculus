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
