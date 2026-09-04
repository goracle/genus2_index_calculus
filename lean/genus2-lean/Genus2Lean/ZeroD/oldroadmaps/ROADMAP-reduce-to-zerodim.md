# Roadmap: `Reduce`'s correctness → wired into alpha locus → connected to
# peel chain → peel chain's hypotheses discharged (or not)

## Why this document exists

Claire's own framing of the remaining work, going in: prove `Reduce`
general's correctness (show `u`'s degree is `≤ 2`), wire that into alpha
locus, connect that to peel chain, then somehow discharge peel chain's
hypotheses. This document checked that framing against the actual files
rather than assuming it. **Verdict: steps 1 and 2 are exactly right and
are the real remaining work. Step 3 ("connect to peel chain") is NOT a
proof obligation — it's already wired, in the sense that both sides
bottom out in explicit hypotheses about the same concrete data and
nothing stops plugging one into the other once step 1 is done. Step 4
("discharge peel chain's hypotheses") is a separate, harder, open-ended
piece of work, already precisely scoped in-file, that doesn't block
steps 1-2 and shouldn't be conflated with them.**

Also found in the course of checking: `ROADMAP-peel-chain-assembly.md`
(the file already in this project) is **stale** — it describes 4 live
`sorry`s in `PeelChainAssembly.lean` that have since been closed by
weakening to 4 more explicit hypotheses. Flagged here, not fixed there,
since correcting that file wasn't this pass's job.

## Sorry inventory, verified fresh this pass (comment-stripped scan, not
## a raw grep of the word "sorry" — the raw grep massively overcounts,
## since most hits are prose *about* sorries in docstrings)

| file | live `sorry` tactic uses |
|---|---|
| `DecoupledSystemRegular.lean` | **0** |
| `PeelChainAssembly.lean` | **0** |
| `RegularSequenceFiniteQuotient.lean` | **0** |
| `Reduce/AlphaReduce.lean` | **0** |
| `Reduce/GeneralSharedRoot.lean` | **0** |
| `TheDataDerivation/*.lean` (all four) | **0** |
| `AlphaLocusDegreeUniform.lean` | **1** (`decoupledSystem_degree_uniform`) |

So: everything in the whole `ZeroD` chain is sorry-free except the one
theorem this project has always known was the actual target —
`decoupledSystem_degree_uniform`, the uniform-in-`(alpha,alpha')` degree
bound. That theorem is not close to provable yet (task (B), the `Bad`
locus, is still an untouched empirical question — see
`ROADMAP-alpha-locus.md` Step 2, unchanged by this document). This
roadmap is about a *different*, more tractable objective: making
`decoupledSystem_isRegularSequence`/`decoupledSystem_zeroDimensional`
(the FIXED-target theorems, already fully proved *modulo hypotheses*)
actually deployable against a real `Reduce`-produced target, rather than
only against an abstractly-quantified `sa sb : SampleTarget p`.

Zero live sorries elsewhere doesn't mean zero open content — most of the
"proved" theorems below take substantial hypothesis bundles
(`Nondegenerate`, `CrossNondegenerate`, `PeelChainNondegenerate`,
`hgcdA`/`hgcdB`, `MatrixNondegenerate4`, `IsMumfordUa`/`IsMumfordTarget4`,
`hdeg2`) that are just as much open mathematical content as a `sorry`
would be, per this project's explicit "weaken to a hypothesis" practice.
The rest of this document is about that content, not about `sorry` count.

## Step 1 (Claire's framing, confirmed correct): `Reduce`'s correctness —
## specifically, `uRS4General.natDegree = 2`

### Where this actually lives

`Reduce.GeneralSharedRoot`, theorem `ReduceGeneral_isMumfordTarget4`
(near the end of the file, `ReduceGeneralCorrectness` section). This
theorem is **already fully proved**, conditional on one hypothesis,
`hdeg2 : uRS4General.natDegree = 2`, which the file's own docstring
names as "the genuinely open piece" in an inline comment directly above
where `hdeg2` is declared. Nothing needs restructuring — this is a
single missing lemma, not a redesign.

Everything downstream of `hdeg2` (the reconstruction of `uRS4General` as
a literal `X²+bX+c`, the `IsMumfordTarget4`-shape divisibility,
`vRS4General`'s degree-≤1 bound via `natDegree_modByMonic_lt`) is
already written and, per the file's own claims, already checked against
the reasoning (not yet against Claire's REPL as of the last pass that
touched this file — reverify that first, see "Before doing anything
else" below).

### What `hdeg2` needs, precisely

`uRS4General := ` the monic normalization of `curBeforeMonic4General :=
Npoly4 /ₘ npoly4Lcm4`. By `Polynomial.natDegree_divByMonic`,

```
curBeforeMonic4General.natDegree = Npoly4.natDegree - npoly4Lcm4.natDegree
```

Two facts currently on file only as **upper bounds**, not exact values:

- `Npoly4_natDegree_le_eight` (`Reduce/AlphaReduce.lean`, already
  proved) — bounds the minuend by `≤ 8`.
- `npoly4Lcm4_natDegree_le_six` (`GeneralSharedRoot.lean`, already
  proved) — bounds the subtrahend by `≤ 6`.

`8 - 6 = 2` only works out if BOTH bounds are sharp (exactly `8` and
exactly `6`), not merely upper bounds — `Nat` subtraction of two upper
bounds gives no lower bound on the difference at all. So `hdeg2` needs
two sharpenings, not one:

**(1a) `npoly4Lcm4.natDegree = 6`, sharp.** This is the more tractable
half — a template already exists in-file:

- `npoly4LcmLinearPair_natDegree_eq_two` (already proved,
  `GeneralSharedRoot.lean`) gives `lcm (X-P1.1) (X-P2.1)` has
  `natDegree = 2` exactly, given `P1.1 ≠ P2.1`. Done, reusable as-is.
- **Missing**: the analogous sharp fact for the OTHER lcm,
  `lcm (u_a-quadratic) (target-quadratic)`. `not_coprime_quadratics_iff`
  (already proved, same file) gives the *dichotomy* — not coprime means
  either a shared root or literal equality — but what's needed here is
  the *positive* direction: **if `u_a ≠ target` as polynomials AND they
  share no root in `F p`, their `lcm` has `natDegree = 4` exactly**
  (mirroring the linear-pair case one degree up: `IsCoprime` ⟹ `gcd` is
  a unit ⟹ `lcm` is a unit multiple of the product ⟹ same `natDegree` as
  the product, `= 2+2 = 4`). This direction of `not_coprime_quadratics_iff`
  already supplies the coprimality-from-non-collision half if phrased
  as its contrapositive; what's missing is the `natDegree`-of-`lcm`
  wrapper, which is a near-verbatim copy of
  `npoly4LcmLinearPair_natDegree_eq_two`'s own proof body (already in
  the file, ~40 lines, `gcd_mul_lcm`/unit-degree-zero argument) with the
  two linear factors swapped for the two quadratics and `natDegree 2`
  swapped for `natDegree 4`. This is genuinely mechanical, not new
  mathematical content — the hard direction (the Galois collapse) is
  already proved in `not_coprime_quadratics_iff`.
- Then `6 = 2 + 4` combines the two sharp lcm-degrees exactly as
  `npoly4Lcm4_natDegree_le_six`'s existing `≤` proof already combines
  the two `≤` bounds — same structure, `omega` closes it once both
  halves are equalities instead of inequalities.

**(1b) `Npoly4.natDegree = 8`, sharp.** Less explored in-file; no
existing sharp-degree lemma or even a documented plan for this half.
`Npoly4 := Epoly4² - curvePoly·Ypoly4²` (the norm construction). The
upper bound `≤ 8` presumably comes from `Epoly4`'s own degree bound
(`≤ 4`, giving `Epoly4².natDegree ≤ 8`) dominating `curvePoly·Ypoly4²`
(degree 5 + `2·(Ypoly4`'s bound`)`, expected smaller). Getting a MATCHING
lower bound needs either:
  - showing the leading term of `Epoly4²` doesn't cancel against
    `curvePoly·Ypoly4²`'s leading term (a genericity condition, likely
    another named hypothesis rather than something provable
    unconditionally — matching this project's established pattern), or
  - showing `curvePoly·Ypoly4²`'s degree is strictly less than 8
    unconditionally (if `Ypoly4`'s bound is tight enough — e.g. if
    `Ypoly4.natDegree ≤ 1` unconditionally, `5 + 2 = 7 < 8`, and then
    `Npoly4.natDegree = 8` follows FOR FREE from `Epoly4.natDegree = 4`
    alone, no genericity condition needed on this half at all). **Check
    `Ypoly4`'s actual proved degree bound in `AlphaReduce.lean`
    (`Ypoly4_natDegree_le_one`, name expected but not confirmed this
    pass) before assuming a new hypothesis is needed here** — there is
    a real chance this half is free.

**Concretely, the next-session task list, easiest first (per project
convention: eliminate errors first, sorry's easiest-first)**:
1. Check `Ypoly4`'s actual degree bound (grep `AlphaReduce.lean` for
   `Ypoly4_natDegree`) and work out whether `Npoly4.natDegree = 8` given
   `Epoly4.natDegree = 4` is free or needs a new genericity hypothesis.
   Do this BEFORE writing any new Lean — it determines whether (1b) is
   a two-line corollary or needs its own named hypothesis.
2. Prove the quadratic-lcm sharp-degree lemma (mirroring
   `npoly4LcmLinearPair_natDegree_eq_two`, swapping in
   `not_coprime_quadratics_iff`'s contrapositive as the coprimality
   source). Name it e.g. `npoly4LcmQuadraticPair_natDegree_eq_four`,
   taking `u_a ≠ target` (as polynomials) and "no shared root in `F p`"
   as its two hypotheses (or a single `IsCoprime` hypothesis directly,
   if that's cleaner — check which shape `not_coprime_quadratics_iff`
   makes easier to discharge at the call site).
3. Combine (1a): `npoly4Lcm4.natDegree = 6` sharp, from step 2 plus the
   already-proved linear-pair sharp lemma.
4. Combine (1b)+(1a) via `Polynomial.natDegree_divByMonic` to get
   `hdeg2` itself, `uRS4General.natDegree = 2`, as an actual theorem
   (not a hypothesis) — conditional on whatever genericity hypotheses
   steps 1-2 needed (expected: `P1.1 ≠ P2.1`, `u_a ≠ target`, `u_a`/
   target share no root in `F p`; possibly nothing more if step 1's
   check comes back favorable).
5. Wire the new `hdeg2` theorem into `ReduceGeneral_isMumfordTarget4`,
   replacing that theorem's `hdeg2` HYPOTHESIS with a proof term calling
   the new theorem — collapsing one hypothesis off `Reduce`'s
   correctness. **Before any of this**: confirm `AlphaReduce.lean` and
   `GeneralSharedRoot.lean` both still compile clean against Claire's
   REPL (per their own docstrings, they were last checked in an earlier
   pass, `AlphaReduce.lean` confirmed 0 errors/0 sorry but
   `GeneralSharedRoot.lean`'s status is less explicitly confirmed —
   verify before building on top of it, not after).

### What this step does NOT need to do

`ReduceGeneral_isMumfordTarget4` already handles everything past
`hdeg2` — the reconstruction lemma `monicQuadratic_eq_reconstruct`, the
`vRS4General` degree bound, the `%ₘ`-to-`∣` conversion, are all done. Do
not re-derive any of that; the only gap is the one hypothesis.

## Step 2 (Claire's framing, confirmed correct): wire into alpha locus

### Where this actually lives, and its current state

`AlphaLocusDegreeUniform.lean`'s `isReduction'` (§ "Restating
`isReduction` against the now-existing `Reduce`") is **already this
wiring** — it states, as a real equation with a computable RHS, that
`sa.toSampleTarget`'s `(u0,u1,v0,v1)` equals `ReduceDispatchGeneral`'s
output. This already exists; there is no additional "wire `Reduce` into
alpha locus" task beyond what's there. What remains is narrower than
"wiring": **`isReduction'` and the original `isReduction` field (an
unconstrained `Prop`) are two separate things, and nothing currently
proves they coincide, or replaces `isReduction` with `isReduction'` as
`SampleTargetFromAlpha`'s actual defining field.**

### The actual remaining task here

1. Once step 1 lands (`hdeg2` closed, `ReduceGeneral_isMumfordTarget4`
   fully unconditional-modulo-genericity), `isReduction'`'s hypothesis
   list (`hcur`/`hgcd`/`hcurT`/`hgcdT`) is exactly `ReduceGeneral`'s own
   precondition list — nothing new is needed to STATE
   `SampleTargetFromAlpha` with `isReduction'` in place of the bare
   `isReduction : Prop` field. Consider making that swap: replace
   `isReduction : Prop` with `isReduction' ...`'s statement directly (or
   keep both and add a theorem `isReduction'_implies_isReduction`/a
   `def` unifying them — whichever reads better once actually looked
   at, not decided here).
2. **The genuinely open piece**: `isReduction'` states a coordinate-level
   fact about `ReduceDispatchGeneral`'s OUTPUT. What it does NOT yet
   connect to is `reducedClass` — `SampleTargetFromAlpha`'s own
   divisor-class-level field, `alpha • aClass - ([P1]+[P2]-2•[δ₀])`. The
   file's own docstring names this precisely: "a theorem (not attempted
   here) that `reducedClass`'s divisor-class-level description and
   `ReduceDispatchGeneral`'s coordinate-level output agree, i.e. that
   `Reduce`'s algorithm is CORRECT (computes the Mumford reduction it
   claims to)". This is a genuinely different, harder theorem than
   step 1's `hdeg2` — step 1 says "`uRS4General`/`vRS4General` satisfy
   the Mumford CONGRUENCE", this says "and that congruence's divisor
   class is the SAME divisor class as `alpha•aClass - [P1]-[P2]+2[δ₀]`"
   — i.e. it needs the actual group-law semantics of the Jacobian
   (`DivisorClassGroup.lean`), not just polynomial algebra. **Not scoped
   in detail by this pass** — flagged as the next open question once
   step 1/2's mechanical parts are done, likely deserving its own
   roadmap section once someone sits down with `DivisorClassGroup.lean`
   directly.

## Step 3 — Claire's framing ("connect to peel chain") is NOT a proof
## obligation; it's already possible, mechanically, once step 1-2 land

This is the one place this document disagrees with the starting framing.
Checked directly: `genList`/`Nondegenerate`/`CrossNondegenerate`/
`PeelChainNondegenerate` (`DecoupledSystemRegular.lean`,
`PeelChainAssembly.lean`) are ALL already stated generically over
`sa sb : SampleTarget p` — a bare `(u0,u1,v0,v1) : F p × F p × F p × F p`
tuple, with NO reference anywhere to how that tuple arose.
`SampleTargetFromAlpha.toSampleTarget` (`AlphaLocusDegreeUniform.lean`)
is exactly this same `SampleTarget p` shape. So once `isReduction'`
holds for a given `SampleTargetFromAlpha` value (step 2), its
`.toSampleTarget` is a completely ordinary `SampleTarget p` value that
`decoupledSystem_isRegularSequence`/`decoupledSystem_zeroDimensional`
already accept — literally the same function application, no new
`Lean` machinery, no bridge theorem, no import even needed beyond
what's already there.

**In other words**: "connecting `Reduce` to peel chain" is not a gap in
the proof architecture, it's a consequence of the architecture already
being decoupled correctly (`Reduce`'s job is producing a
`(u0,u1,v0,v1)`; `genList`'s job is consuming one; neither cares about
the other's internals). The only reason this isn't already "done" in
any stronger sense is that nobody has a concrete `SampleTargetFromAlpha`
value with `isReduction'` actually proved yet (step 2's open piece) —
once one exists, plugging it into
`decoupledSystem_isRegularSequence`/`_zeroDimensional` is immediate.

**Action item, once steps 1-2 land**: write the actual one-line-ish
corollary explicitly (something like `decoupledSystem_isRegularSequence`
applied to `sa.toSampleTarget`/`sb.toSampleTarget` for
`sa sb : SampleTargetFromAlpha ...` satisfying `isReduction'`), so this
connection exists as a real theorem in the file rather than as an
informal claim in a roadmap. Trivial once steps 1-2 are in, genuinely
can't be written before them (there's no `isReduction'`-satisfying value
to apply it to yet).

## Step 4 (Claire's framing, confirmed correct, and genuinely separate
## from steps 1-3): discharging peel chain's hypotheses

### Correcting the stale roadmap first

`ROADMAP-peel-chain-assembly.md` (already in this project) claims 4 live
`sorry`s in `PeelChainAssembly.lean`, stages 4-7 (`Fv0`-`Fv3`), "wiring
not yet done." **This is stale.** Checked directly against the current
file: those 4 sites are closed. `PeelChainNondegenerate` now has 16
fields total (the original 8 the stale roadmap describes, plus
`hv0_A`/`hv1_B`/`hv2_A`/`hv3_B`, plus `hv0_ext`/`hv1_ext`/`hv2_ext`/
`hv3_ext`) and `regularSeq_of_peel_chain` is fully proved, no `sorry`,
taking `PeelChainNondegenerate` and `htop_ne_smul` as its only
hypotheses. The file's OWN top-of-file docstring already says this
("Status as of THIS pass: ... the file is sorry-free") — the stale
roadmap file just wasn't updated to match. Worth a follow-up pass to fix
`ROADMAP-peel-chain-assembly.md` itself so future readers don't get
confused the way this framing question could have; not done here since
it's a separate documentation-only fix.

### What "discharging peel chain's hypotheses" actually means now

Not closing `sorry`s — there are none. It means: **`PeelChainNondegenerate`
(16 fields) + `Nondegenerate` (×2) + `CrossNondegenerate` + `hgcdA`/
`hgcdB` + `hcurA`/`hcurB` + `htop_ne_smul` are ALL currently bare
hypotheses, supplied, never derived from anything more primitive.**
"Discharging" them means either:

(a) proving they hold for a SPECIFIC concrete instance (a specific `p`,
`c0..c4`, and `(sa,sb)` — e.g. the production `p=2371157` curve this
project's Julia pipeline actually uses), by direct computation/`decide`/
`native_decide` once concrete numbers are plugged in, or

(b) proving they hold GENERICALLY (for "enough" `(c0..c4,sa,sb)`,
outside some small exceptional locus) — this is much harder and is
explicitly the same shape of question as `ROADMAP-alpha-locus.md`'s
task (B), the `Bad` locus, one level down (per-fixed-target genericity
rather than uniform-across-`alpha` genericity).

`ROADMAP-peel-chain-assembly.md`'s own "Whether `PeelChainNondegenerate`'s
existing 8 fields are themselves provable" section (unaffected by the
staleness above — this part of that file is still accurate) already
says route (b) is NOT expected to work from `Nondegenerate`/
`CrossNondegenerate`/`hgcdA`/`hgcdB` alone, and that this is unattempted
in the project. Nothing found this pass changes that assessment.

**Recommended scope, in order**:
1. Once a concrete production instance is available (real `p`, real
   `c0..c4`, and — once steps 1-3 above land — a real
   `SampleTargetFromAlpha`-derived `(sa,sb)`), attempt route (a) first:
   plug in the actual numbers and see if `decide`/`native_decide`/direct
   computation discharges each of the ~20 hypothesis fields
   (`Nondegenerate`×2 = 8, `CrossNondegenerate` ≈ 4, `PeelChainNondegenerate`
   = 16, plus `htop_ne_smul`, `hcurA`/`hcurB`, `hgcdA`/`hgcdB` — exact
   count not re-tallied this pass, grep each structure's field count
   directly before starting) — this is "normal engineering," not open
   math, once real numbers exist, and per this project's own"errors are
   not a risk, normal" philosophy is worth just trying rather than
   pre-judging as too hard.
2. Only if (1) turns out to genuinely fail for the production instance
   (not just "hasn't been tried yet") does route (b) — generic
   sufficient conditions — become necessary, and that's ChatGPT-
   consultation-worthy per this project's existing convention for hard
   sorries/hard hypotheses, same as `ROADMAP-alpha-locus.md`'s task (B).
3. Do NOT attempt route (b) before route (a) has actually been tried
   against real numbers — per Claire's "we can always fix it later, but
   don't spend all your time hedging" instruction, checking the concrete
   case is cheap and might make the generic question moot for the actual
   DLP instance this project cares about, even if it doesn't resolve the
   question in general.

## Summary: the four steps, correctly triaged

| step | Claire's framing | actual status this pass | next concrete action |
|---|---|---|---|
| 1. `Reduce` correctness / `u` deg ≤ 2 | correct, real gap | one hypothesis (`hdeg2`) short of a full theorem; template exists | prove `Npoly4.natDegree=8` and the quadratic-lcm sharp-degree lemma (§ above) |
| 2. wire into alpha locus | correct, real gap | already wired as a stated equation (`isReduction'`); genuinely missing piece is `reducedClass ↔ isReduction'` agreement | scope the divisor-class-vs-coordinate correctness theorem once step 1 lands |
| 3. connect to peel chain | **not actually a gap** | architecture already decouples cleanly; nothing to prove beyond function application | write the explicit one-line corollary once 1-2 land, for the record |
| 4. discharge peel chain's hypotheses | correct, real gap, but SEPARATE from 1-3 | ~20 hypothesis fields, all genuinely open, `ROADMAP-peel-chain-assembly.md`'s own analysis (still accurate on this point) says generic discharge is unlikely to be free | try concrete-instance discharge FIRST once real numbers exist; don't chase generic sufficient conditions before that's been tried |

**Also, separately, not part of the four steps but found this pass and
worth fixing**: `ROADMAP-peel-chain-assembly.md` is stale (claims 4 open
sorries that are closed) and `AlphaReduce.lean`'s module docstring has
at least one stale claim too (an earlier passage calls the tangent case
"still fully unstarted," which is no longer true — `ReduceTangent`/
`ReduceDispatch` exist and are wired). Neither blocks any of the four
steps above; both are worth a documentation-cleanup pass so the next
person reading these files isn't misled the way a fresh read this pass
almost was.

## Before doing anything else

None of `AlphaReduce.lean`/`GeneralSharedRoot.lean`/
`AlphaLocusDegreeUniform.lean`'s "0 sorry" claims in this document were
re-verified against Claire's actual REPL this pass — they're taken from
each file's own most recent in-file status claim, cross-checked by a
comment-stripped `sorry`-token scan (robust against docstring mentions
of the word "sorry", not a substitute for `lake build`). Confirm a clean
build of the whole `ZeroD` tree before starting Step 1's work, so any
new work is built on a genuinely-checked foundation rather than a
plausible-sounding but unverified one.
