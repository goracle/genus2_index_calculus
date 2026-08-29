# Roadmap: eliminating unnecessary split/distinctness hypotheses

## Goal

`reducedClass_eq_of_isReduction'` (`AlphaLocusDegreeUniform.lean`, 1631
lines — **already at the file-size ceiling; any further growth here
should go in a new file, not this one**) currently hard-requires the
"fully split" case (`Ra1 ≠ Ra2`, `T1 ≠ T2`) unconditionally, with no
tangent-case (`Ra1 = Ra2`, i.e. a repeated Mumford root) sibling at all.
This was diagnosed as a **bug, not a genuine restriction** — the actual
`ordAt`/multiplicity machinery this theorem is built from
(`SanchorMumfordOrdAt.lean`, `LPairFinrankOneOrdAtFrac.lean`) is already
unconditional and works identically whether the root is simple or
doubled. The split-only behavior was forced entirely by one lemma
(`Sanchor_eq_of_anchor_roots`, old version) reaching for a helper
(`quadratic_eq_mul_X_sub_C`) that only knows how to factor against two
*named distinct* roots.

This doc tracks every hypothesis in that theorem's signature that is
split/distinctness-flavored, which ones are genuinely the same bug
(fixable now), which are a *different, bigger* instance of the same
underlying mistake (fixable, but real additional work), and which are
genuinely necessary and should survive. **The endpoint, once every
tier below is done: `reducedClass_eq_of_isReduction'`'s signature has
NO bare, unconditional `Ra1 ≠ Ra2`/`T1 ≠ T2`-style hypothesis, and no
bare `IsCoprime` hypothesis, left anywhere.** Every such fact turns out
to be either (a) an artifact of a specific proof strategy that has a
tangent-case alternative, gated behind a genuine case split, or (b) a
distinctness fact between two points that are never the same point in
EITHER branch (e.g. the anchor pair vs. `P1`/`P2`), which is real math
and correctly stays. **Only items in Tier 1 are in scope for a quick
follow-up session; Tier 2 is real, separate work; Tier 3 should not be
touched.**

## Status as of this pass (build green, per Claire's REPL)

Done — `SanchorEqAlphaPoints.lean` and `SanchorMumfordOrdAt.lean` now
each have a genuine tangent-case sibling theorem:

- `Sanchor_eq_of_anchor_roots_tangent` (`SanchorEqAlphaPoints.lean`) —
  `Sanchor = {P1}` when `ua = (X - C P1.X) ^ 2` (caller-supplied, not
  derived — squarefreeness and a genuine double root are mutually
  exclusive, so this is NOT reachable by weakening the split case's own
  hypotheses).
- `ordAt_ua_eq_two_of_mem_Sanchor_tangent` /
  `ordAt_negVa_one_eq_two_of_mem_Sanchor_tangent`
  (`SanchorMumfordOrdAt.lean`) — the `ordAt = 2` mirror of the existing
  `= 1` lemmas, via `Polynomial.rootMultiplicity_X_sub_C_pow` (clean, no
  case split needed) composed with the previously-unused
  `ordAt_eq_two_of_old_point` (`PrincipalWitness.lean` line 1030 — this
  lemma existed already and had no caller anywhere in the codebase
  until now).

These are the two foundational pieces, and this pass consumed them:

- `divToPair_negVa_one_Sanchor_eq_tangent` /
  `divToPair_negV_one_S_eq_tangent` (`PrincipalWitnessCAConnection.lean`)
  — the `Finset.sum_singleton`-collapse consumers of the two lemmas
  above, giving `divToPair (-va) 1 Sanchor = (2:ℤ) • single P1` (resp.
  the `S`/`T1cur` mirror). Item 1a.1 of Tier 1 below, done, build
  green.

**Nothing past this consumes them yet, and — corrected this pass —
the next consumer is a genuinely bigger piece of work than previously
scoped.** See Tier 1's 1a/1b below: splitting the top-level theorem
itself is blocked on a 3-layer-deep assembly chain
(`cAmιTmδmιδ_mem_of_le` → `cIotaAmIotaT_mem_of_le` →
`cIotaAmIotaT_mem_principalSubgroup`/`divToPair_eq_C_add_iotaA_add_T_
of_split`) that has no tangent branch anywhere yet, traced in detail
in 1b.

**Update, later pass — build green (Claire's REPL):** that 3-layer chain
now DOES have a tangent branch, all the way through. Scoped as its own
doc (`ROADMAP-principal-witness-tangent-assembly.md`, spun off from 1b
below) and its Steps 1-4 are done: `CAWitnessTangent.lean`,
`CAWitnessDivisorTangent.lean`, `CAWitnessAssemblyTangent.lean`,
`PrincipalWitnessStep4Tangent.lean`, `PrincipalWitnessFinalAssemblyTangent.
lean`, no sorries. One correction surfaced mid-pass and is now reflected
in those files' signatures: `cIotaAmIotaT_mem_of_le_tangent` and
`cAmιTmδmιδ_mem_of_le_tangent`'s conclusions carry genuine extra
`-single PtT1 - single PtT2` terms that the split case's analogues don't
have (root cause: the tangent case's `f`-divisor support is three points,
not six, so `PtT1,PtT2` never cancel against `divToPair_hT_eq`'s matching
terms the way they do in the split case) — see that roadmap's own Step 4
writeup for the full explanation. **This means Tier 1a's step 2 (splitting
`reducedClass_eq_of_isReduction'` itself, below) is now unblocked in
principle, but the person who does it needs to trace how these two extra
terms interact with `hDP`'s downstream usage first** — not yet done, not
assumed away, see the tangent-assembly roadmap's own Step 5 note.

## Tier 1: same bug, fix is a continuation of what's already started

These are the ONLY hypotheses where the underlying machinery is already
proven unconditional and the fix is "finish wiring the tangent branch
through," not new mathematics.

### 1a. `hRa12Xne : Ra1.X ≠ Ra2.X` (`AlphaLocusDegreeUniform.lean`
line ~1020) and `hT12Xne : T1.X ≠ T2.X` (line ~1028)

Consumed at lines ~1130-1140 (`hSanchorEq`/`hSEq` derivation, calling
`Sanchor_eq_of_anchor_roots`). **Item 1a.1 done, build green** —
`divToPair_negVa_one_Sanchor_eq_tangent`/`divToPair_negV_one_S_eq_tangent`
now exist in `PrincipalWitnessCAConnection.lean`, giving
`divToPair (-va) 1 Sanchor = (2:ℤ) • single P1` (resp. the `S`/`T1cur`
mirror) directly off `Sanchor_eq_of_anchor_roots_tangent` +
`ordAt_negVa_one_eq_two_of_mem_Sanchor_tangent`. (Along the way, found
and fixed a real, pre-existing bug in
`ordAt_ua_eq_two_of_mem_Sanchor_tangent`, `SanchorMumfordOrdAt.lean`:
`ordAt_eq_rootMultiplicity_unramified`'s `α` argument was instantiated
to `Q.X` instead of the fixed root `R`, plus a missing `norm_num` for
the resulting `ℕ→ℤ` cast — unrelated to the split/tangent bug itself,
just a mechanical slip in a lemma nothing had called yet.)

**Still open, and now properly scoped (see 1b below, substantially
revised after tracing the actual call chain this pass): splitting
`reducedClass_eq_of_isReduction'` itself does NOT stop at swapping in
the two lemmas above.** The theorem's proof body calls
`cAmιTmδmιδ_mem_of_le` (`PrincipalWitnessFinalAssembly.lean`) to
produce `hDP`, and *that* theorem's own signature unconditionally
requires `h12 : Ra1X ≠ Ra2X` — independent of, and downstream of,
`hRa12Xne`. So finishing 1a.1's split still leaves the assembly step
itself split-only. That deeper chain is now 1b's actual subject, not a
follow-on afterthought — see there for why this turned out to be much
bigger than "swap two lemma calls."

**Once 1b unblocks `cAmιTmδmιδ_mem_of_le` for the tangent axis, the
remaining edits here are:**

1. In `AlphaLocusDegreeUniform.lean`, split
   `reducedClass_eq_of_isReduction'` itself. Two sub-choices, pick one:
   - **(a) Two top-level theorems** (`_split`/`_tangent` suffix,
     mirroring `hcur`/`hcurT`, `hgcd`/`hgcdT`'s existing convention in
     this same file, lines 834-855) — cleanest, avoids one giant `∨`
     living inside a single 300-line signature, but duplicates ~250
     lines of shared proof body between the two. Given the file is
     already at the 1500-line ceiling, put `_tangent` in a **new**
     file (`AlphaLocusDegreeUniformTangent.lean` or similar) rather
     than growing this one further.
   - **(b) One theorem, hypotheses reshaped as implications** exactly
     like `hcur`/`hcurT` already are (`Ra1 = Ra2 → ...` /
     `Ra1 ≠ Ra2 → ...`), with the proof body `rcases`-ing on
     `Classical.em (Ra1 = Ra2)` near the top and routing to whichever
     branch's lemmas apply. Keeps everything in one place but the
     proof body itself needs restructuring into two sub-cases, which
     is more invasive than (a).

   Given the 50-line-per-theorem guideline and the file already being
   oversized, **(a) is very likely the better default** — but this is
   a judgment call worth revisiting once the actual case-split proof
   is drafted and its real duplication cost is visible.
2. Note `Sanchor`'s tangency (`Ra1 = Ra2`) and `S`'s tangency
   (`T1 = T2`) are **independent axes** — the caller could have a split
   anchor but tangent target, or vice versa. If pursuing (b) above,
   this means a genuine 2×2 case split (four branches), not just 2. If
   pursuing (a), it likely means either 4 top-level theorems, or 2
   theorems each still containing an inner split on the *other* axis —
   worth deciding explicitly before writing rather than discovering it
   mid-proof.

### 1b. The assembly chain beneath `hDP`, REVISED this pass — this is
where the real remaining work is, and it is bigger and deeper than
this doc previously said

**Traced the full call chain this pass** (starting from
`reducedClass_eq_of_isReduction'`'s `hDP := cAmιTmδmιδ_mem_of_le ...`
call, `AlphaLocusDegreeUniform.lean` line ~1204), the way step 1 of
the ordAt-tangent session traced `hRa12Xne` back to its origin before
touching anything. Previous pass's framing — "almost certainly needs
its own tangent version... not yet scoped in detail" — undersold this:
it is not one theorem needing a tangent sibling, it is **four,
stacked**, none of which has a tangent branch anywhere in the codebase
today:

1. `cAmιTmδmιδ_mem_of_le` (`PrincipalWitnessFinalAssembly.lean` line
   213) — takes `h12 : Ra1X ≠ Ra2X` unconditionally (`hPP : P1X ≠ P2X`
   too, i.e. this is ALSO where the `sa.P1 = sa.P2` axis from Tier 2's
   `h1P1,h1P2,h2P1,h2P2,hPP` discussion resurfaces — but `h12`
   specifically is the `Ra1=Ra2` axis this doc tracks). Passes `h12`
   straight through, unused otherwise at this layer.
2. → `cIotaAmIotaT_mem_of_le` (same file, line 108) — same `h12`,
   passed straight through again to both of the next two.
3. → `cIotaAmIotaT_mem_principalSubgroup` (`PrincipalWitnessStep4.lean`
   — the actual theorem this whole chain is built to make generic over
   `D`) **and** `divToPair_eq_C_add_iotaA_add_T_of_split`
   (`PrincipalWitnessStep3.lean` line 104, name literally flags it —
   `_of_split`). **Neither has a tangent-named sibling anywhere in the
   codebase** (checked: `grep -n "_tangent"` against both
   `PrincipalWitnessStep3.lean` and `PrincipalWitnessStep4.lean`
   returns nothing).

So the real blocker is at layer 3, not layer 1 — `cAmιTmδmιδ_mem_of_le`
and `cIotaAmIotaT_mem_of_le` are themselves innocent pass-throughs;
they will fall out for free once layer 3's two theorems have tangent
siblings, mechanically the same way `cAmιTmδmιδ_mem_of_le` itself was
built as a thin composition over `cIotaAmIotaT_mem_of_le`. **This is
genuinely new mathematics, not a wiring job.** Traced one layer
further this pass, past `divToPair_eq_C_add_iotaA_add_T_of_split`
itself, down to its actual root: `CAWitness.lean`'s `caInterpMatrix`,
a plain 4×4 Vandermonde matrix that is genuinely SINGULAR when `Ra1X =
Ra2X` (closed-form determinant has `(Ra2X-Ra1X)` as a literal factor)
— a real linear-algebra fact, not a proof-technique artifact like
`Sanchor_eq_of_anchor_roots`'s `quadratic_eq_mul_X_sub_C` dependency
(the original bug this whole roadmap is about). **Scoped as its own
doc this pass: `ROADMAP-principal-witness-tangent-assembly.md`.**
Good news found there: `TangentMumfordWitness.lean` already solves the
identical shape of problem (confluent Vandermonde replacing a plain
one) and is fully proven — that doc maps its machinery onto this case
step-by-step, and the `bCA` version turns out to be simpler (no
branch-derivative detour needed; `va`'s own polynomial derivative
suffices). **Start there, not from scratch** — it is comparable in
size to this session's `SanchorEqAlphaPoints.lean`/
`SanchorMumfordOrdAt.lean` work, not a quick follow-up, and should not
block 1a.1's already-completed piece from staying merged. Until that
doc's Steps 1-4 are done, 1a's step 2 (the top-level theorem split) is
blocked, not "next."

## Tier 2: same bug as Tier 1, but the codebase already has the right
tool — just not applied here yet

**Revised this pass, after pushback**: I originally put `h1P1, h1P2,
h2P1, h2P2, hPP` (anchor-vs-`sa.P1`/`sa.P2` distinctness, feeding
`hdet`) in "correctly left alone." That was wrong. `hcur`/`hgcd`
(`AlphaLocusDegreeUniform.lean` line 834 onward) already treat
`sa.P1 = sa.P2` as a legitimate case with its own branch
(`hcurT`/`hgcdT`) — and that same file's docstring (line 415-417)
states outright that `ReduceGeneral`/`GeneralSharedRoot.lean` was
BUILT specifically so `Reduce`'s own correctness needs **"NO pairwise
`IsCoprime` facts among `P1,P2,u_a,` target"** — i.e. `sa.P1` colliding
with an anchor root or a target root is *already the exact problem
`GeneralSharedRoot.lean` exists to solve*, at the `Reduce`-dispatch
layer. `CAWitness.lean`'s `hdet`/`dvd_pairNormBCA_full` block is a
SEPARATE, later-written piece of machinery (the CAWitness residual
construction) that never got the same treatment — it still uses the
older, pre-`GeneralSharedRoot.lean` style of gluing four individual
`(X - C _) ∣ g` facts via six pairwise `IsCoprime` hypotheses
(`hc12, hc1P1, hc2P1, hc1P2, hc2P2, hcPP` inside `dvd_pairNormBCA_full`,
`CAWitness.lean` line 338), which is exactly the sequential-coprime-glue
pattern `GeneralSharedRoot.lean`'s own docstring calls out as not
scaling ("`2^6` possible patterns... writing a sixth/seventh/... file
per new collision pattern doesn't scale").

**The tool that already exists and already works for this exact
shape:** `lcm_dvd_of_four_dvd` (`GeneralSharedRoot.lean` line 81) —
`lcm (lcm q1 q2) (lcm q3 q4) ∣ N` for ANY four divisors, **zero
coprimality hypotheses of any kind**, proved once and reused. This is
the direct answer to "shouldn't ALL these collision cases (P1=P2,
P1=an anchor root, P1=a target root, anchor collapsing with itself) be
allowed at once, not enumerated": `lcm` absorbs every one of them
simultaneously, by construction, because `lcm(a,a) = a` regardless of
*why* two inputs happened to coincide. No case split on WHICH pair
collided is needed for divisibility itself.

**What `lcm` gives you immediately, no new proof needed beyond
porting:**
`(X-C Ra1X) ∣ (H.f-bCA²)`, `(X-C Ra2X) ∣ (H.f-bCA²)`,
`(X-C P1X) ∣ (H.f-bCA²)`, `(X-C P2X) ∣ (H.f-bCA²)` — already all four
proved individually (`dvd_pairNormBCA_Ra1/Ra2/P1/P2`, unconditional,
no `h12`/`hPP`/etc. needed for THESE) — feed straight into
`lcm_dvd_of_four_dvd` to get
`lcm(lcm(X-C Ra1X, X-C Ra2X), lcm(X-C P1X, X-C P2X)) ∣ (H.f-bCA²)`
with **zero distinctness hypotheses of any kind**, covering every
collision pattern (`Ra1=Ra2`, `sa.P1=sa.P2`, `Ra1=sa.P1`, all of them
simultaneously if needed) at once. This directly ports
`divToPair_eq_C_add_iotaA_of_split`'s core divisibility step
(`_of_split` in the name should become unnecessary) without touching
`dvd_pairNormBCA_Ra1/Ra2/P1/P2` themselves at all.

**What still needs real work, honestly** — and this is true even
inside `GeneralSharedRoot.lean` itself, not just in `CAWitness.lean`:
`lcm`-divisibility alone is not enough to finish the proof.
`divToPair_eq_C_add_iotaA_of_split`'s actual CONCLUSION is
`divToPair (-bCA) 1 {four points} = single + single + single + single`
— it needs the divisor to assign exactly the right MULTIPLICITY at
each point, which means it needs `npoly4Lcm4`/the `lcm`-combination to
have the exact right DEGREE, not just be "some" divisor. Checked this
directly: `npoly4Lcm4_natDegree_eq_six`
(`GeneralSharedRoot.lean` line 839) — the theorem that pins the exact
degree — **still requires `h12 : P1.1 ≠ P2.1` unconditionally, with no
tangent-case sibling written anywhere in that file.** So
`GeneralSharedRoot.lean` has already solved "divisibility without
enumerating collision patterns" but has NOT yet solved "exact degree/
multiplicity without enumerating collision patterns" — that second
piece is genuinely unwritten, in this file and by extension in
`CAWitness.lean` too.

**Concretely, what's needed, and it directly generalizes**
`OrdAtRootMultiplicityUnified.lean`'s already-proven pattern (this
session's Tier 1 lemmas are a special case of exactly this): when
`Ra1X = Ra2X = R`, `lcm(X-C Ra1X, X-C Ra2X)` DOES simplify to
`(X - C R)` (degree 1, not 2) — `lcm` of two copies of the same monic
linear factor collapses, it does not double. So the exact-degree
theorem's tangent case needs a genuinely separate branch: not
"`lcm_dvd_of_four_dvd` handles it automatically," but "when `Ra1=Ra2`,
the CORRECT divisor to use is `(X-C R)^2` (from `ordAt_ua_eq_two_of_
mem_Sanchor_tangent`-style multiplicity-2 reasoning, this session's
Tier 1 work), not `lcm(X-C Ra1X, X-C Ra2X)` — those are different
polynomials, and only the FIRST one has the correct degree/multiplicity
for the divisor-class statement to come out right." So:
- `lcm_dvd_of_four_dvd` **does** fully solve the split case cleanly
  (all four points genuinely distinct, any collision pattern among
  the OTHER unrelated pairs) — port this in for `h1P1,h1P2,h2P1,h2P2`
  and drop those four bare hypotheses.
- `hPP`/`h12`-shaped anchor-vs-anchor or `sa.P1`-vs-`sa.P2` collisions
  still need their OWN dedicated branch (mirroring this session's
  `Sanchor_eq_of_anchor_roots_tangent`/`ordAt_..._eq_two_...` pair),
  because those are multiplicity-2-at-one-point facts that `lcm`
  cannot produce — not because `lcm` "doesn't apply," but because the
  degree/multiplicity math is genuinely different there.

**Net scope, revised**: smaller than my previous pass claimed for the
"port `lcm_dvd_of_four_dvd` in" half (that part is a fairly direct port
of an already-fully-proven pattern), but the "tangent-case exact-degree
for the anchor pair specifically" half is real new work, roughly
comparable to what was built this session for `Sanchor`/`ordAt`, just
one layer up (at the `bCA`/interpolation level instead of the `ua`/`va`
Mumford-pair level). Recommend splitting into two follow-up passes:
1. Port `lcm_dvd_of_four_dvd` into `CAWitness.lean`'s
   `dvd_pairNormBCA_full`, eliminating `h1P1,h1P2,h2P1,h2P2` (but NOT
   yet `h12`/`hPP`) — mechanical, low-risk, `GeneralSharedRoot.lean`'s
   pattern already proves it works.
2. Write the tangent-case (`Ra1=Ra2` or `sa.P1=sa.P2`) exact-degree/
   multiplicity branch for the CAWitness construction — real work,
   scope as its own roadmap doc if picked up
   (`ROADMAP-cawitness-tangent-interpolation.md`), same as previously
   flagged, but now correctly scoped to just the multiplicity-2 piece,
   not a full Hermite-interpolation matrix redesign — see next
   paragraph for why the redesign claim was likely also overstated.

**One more correction to my previous pass**: I claimed `bCA`/
`caInterpMatrix` would need a full confluent/Hermite-interpolation
redesign for the tangent case. Given `lcm_dvd_of_four_dvd` decouples
"divisibility" from "which points collided," it's plausible the
EXISTING `bCA` (still a 4-named-point interpolant, `Ra2X` allowed to
literally equal `Ra1X` as a VALUE, not requiring the matrix rows to be
distinct in a different sense) continues to work as long as `hdet ≠ 0`
is replaced by whatever nondegeneracy condition the tangent case
actually needs — possibly still `hdet ≠ 0` in a suitable limiting
sense, possibly needing a genuinely different matrix. **Not resolved
this pass — check `caInterpMatrix`'s definition and whether `hdet`
literally becomes `0` when `Ra1X = Ra2X` (two equal rows → singular,
in which case SOME Hermite-style replacement really is needed) before
assuming either way.**

### 2b. `hPtT1X : PtT1.X ≠ PtT2.X` (`AlphaLocusDegreeUniform.lean`
line ~1082) and `hQ1_def`/`hQ2_def`'s factored-shape hypotheses

Traced this session: unlike `hRa12Xne`, this one is **not** an artifact
of a lazy helper call — `hQ1_def`/`hQ2_def` (lines ~1080-1085) directly
assume `uCANew` factors as `(X - C PtT1.X) * (X - C PtT2.X) * Q1`, a
fully-split shape supplied by the CALLER, not derived via
`quadratic_eq_mul_X_sub_C` or anything analogous. Same conclusion as
2a though: `uCANew` is itself the residual of the SAME `bCA`/
interpolation construction 2a is about, so fixing 2a's tangent-case
multiplicity work should make `uCANew`'s own tangent-case factorization
(`(X - C R')^2 * Q` for `PtT1 = PtT2 = R'`) fall out alongside it,
rather than needing a wholly separate fix. Likely folds into the same
follow-up piece of work as 2a's item 2, not a third, independent item.

## Tier 3: correctly left alone — do not touch

**Revised, much shorter than my previous pass** — after tracing 2a
properly, almost nothing survives here. The only genuinely irreducible
distinctness left is between points that structurally cannot ever be
equal in this construction at all (not "happen not to collide in the
cases considered so far," but literally impossible to collide, e.g. an
anchor point and its own hyperelliptic conjugate, or a Weierstrass
exclusion) — nothing in the hypothesis list traced this session
actually meets that bar except the non-Weierstrass conditions. If a
concrete example is needed for this tier, it should be re-derived from
scratch against the ACTUAL geometric meaning of each remaining
hypothesis, not assumed by default the way `h1P1`/etc. wrongly were.
  quadratic).
- `h1δ : PtT1.X ≠ δ₀.X`, `h2δ : PtT2.X ≠ δ₀.X` — non-Weierstrass
  condition (point vs. `δ₀`), a different axis entirely from
  point-vs-point distinctness. Belongs in a `Bad`-locus exclusion set
  per the alpha-locus roadmap, not something to weaken here.
- `hcur`/`hgcd`/`hcurT`/`hgcdT` (lines 834-855) — already correctly
  split via `(sa.P1.X,sa.P1.Y) ≠ (sa.P2.X,sa.P2.Y) → ...` /
  `= ... → ...` implication pairs. This is the existing pattern Tier 1
  item 1a.2's option (b) would mirror. Nothing to do here.
- All plain nonvanishing hypotheses (`hdet`, `hlead`, `hUco_ne`,
  `hUco_evalRa1/Ra2`, `hU_evalRa1/Ra2/P1/P2`, `hU_ne0`, `hQ1T1`,
  `hQ2T2`, `hAeval1/2`, `hRa1Y_ne`/etc., `hP1Y_ne`/`hP2Y_ne`, `hδY`,
  `hchar`, `hufree`, `huafree`) — these assert "this specific quantity
  is nonzero," not "these two points differ." Structurally unrelated to
  the split/tangent bug; leave alone.

## Suggested order if resumed

1. **Done, build green:** Tier 1 item 1a.1's `PrincipalWitnessCAConnection.lean`
   half (`divToPair_negVa_one_Sanchor_eq_tangent`/`divToPair_negV_one_S_eq_tangent`)
   — self-contained, used only machinery already proven the prior
   session, no new Mathlib lemmas needed beyond `Finset.sum_singleton`-
   style unfolding (plus a small pre-existing-bug fix in
   `ordAt_ua_eq_two_of_mem_Sanchor_tangent`, unrelated to the
   split/tangent question itself).
2. **Done, build green:** Tier 1b's 3-layer assembly chain
   (`cAmιTmδmιδ_mem_of_le` → `cIotaAmIotaT_mem_of_le` →
   `cIotaAmIotaT_mem_principalSubgroup`/`divToPair_eq_C_add_iotaA_add_T_
   of_split`) now has a full tangent path — scoped and built in
   `ROADMAP-principal-witness-tangent-assembly.md` (its Steps 1-4), no
   sorries. **Next:** that doc's own Step 5 — actually splitting
   `reducedClass_eq_of_isReduction'` itself (1a's step 2, immediately
   below) — including tracing how the two extra `-[T1]-[T2]` terms found
   during Step 4 (see that doc, and the "Status as of this pass" update
   above) interact with `hDP`'s downstream usage, which has not been
   done yet.
3. Only after that, scope Tier 2 (2a/2b) properly, probably as its own
   roadmap doc — it's a different, bigger piece of work (new
   interpolation construction) and shouldn't block or get tangled with
   Tier 1's completion. Worth noting Tier 1b and Tier 2a turned out to
   be structurally the same kind of gap (a `_of_split`-named theorem
   with no tangent sibling) at two different layers of the same overall
   construction — scoping them together, once both are separately
   understood, may reveal shared machinery worth factoring out rather
   than solving each in isolation.
4. Leave Tier 3 alone throughout.
