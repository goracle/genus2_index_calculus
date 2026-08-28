# Roadmap: `Ra1 = Ra2` tangent-case interpolation for `bCA`/`uCANew`,
# and the assembly chain that depends on it

## Where this fits

Spun off from `ROADMAP-split-hypothesis-elimination.md`'s Tier 1b,
after tracing `reducedClass_eq_of_isReduction'`'s `hDP :=
cAmιTmδmιδ_mem_of_le ...` call (`AlphaLocusDegreeUniform.lean`) all
the way to its root. That trace found the blocker is NOT a wiring gap
at the top-level theorem — it's that the entire assembly chain beneath
it is built on a **plain (non-confluent) 4×4 Vandermonde interpolation**
that is genuinely singular when `Ra1.X = Ra2.X`. This doc scopes the
fix: a confluent/Hermite-interpolation replacement for `bCA`, plus
threading its consequences through four downstream theorems.

**This is real, self-contained new mathematics — comparable in size to
the earlier `SanchorEqAlphaPoints.lean`/`SanchorMumfordOrdAt.lean` pass
— not a quick follow-up.** Estimated: one new file (~150-250 lines,
mirroring `TangentMumfordWitness.lean`'s size) plus tangent siblings in
3-4 existing files.

## The chain, traced (earliest link first)

1. **`caInterpMatrix`/`caInterpMatrix_det_ne_zero`** (`CAWitness.lean`
   line 119/137) — the actual root. `bCA` (the `C-A` Cantor witness,
   `y - bCA(x)` vanishing on `{Ra1,Ra2,ιP1,ιP2}`) is defined via
   `Matrix.cramer`/`det⁻¹` against this **plain** 4×4 Vandermonde
   matrix (rows: `1,x,x²,x³` at each of `Ra1.X, Ra2.X, P1.X, P2.X`).
   Its determinant has closed form `(Ra2X-Ra1X)(P1X-Ra1X)(P2X-Ra1X)
   (P1X-Ra2X)(P2X-Ra2X)(P2X-P1X)` — **literally zero when `Ra1X =
   Ra2X`** (first factor vanishes). This is not a proof-technique
   artifact like `Sanchor_eq_of_anchor_roots`'s `quadratic_eq_mul_X_
   sub_C` dependency (this roadmap's original bug) — it is a genuine
   fact about the linear system: two coincident evaluation nodes make
   the plain Vandermonde matrix singular, full stop. `bCA` is simply
   not defined (or rather, `Cramer`/`det⁻¹` silently returns `0` for
   the whole polynomial, which is not the intended interpolant) at
   `Ra1X = Ra2X`.
2. **`denomPolyCA`/`uCANew`/`pairNormBCA_eq_denomPolyCA_mul_uCANew`**
   (`CAWitness.lean` lines 314-446) — built on `bCA`, inherits the
   same restriction. `dvd_pairNormBCA_full`'s six pairwise-`IsCoprime`
   glue (line 338) is ALSO the exact pattern Tier 2 of the main
   roadmap already flags as replaceable by `lcm_dvd_of_four_dvd` — but
   that swap only helps the *divisibility* statement, not `bCA`'s own
   well-definedness, which is the deeper issue here.
3. **`divToPair_eq_C_add_iotaA_add_T_of_split`**
   (`PrincipalWitnessStep3.lean` line 104) — six-point interpolation-
   divisor equality for `f := y - bCA(x)`, takes `h12 : Ra1X ≠ Ra2X`
   unconditionally (along with `h1P1,h1P2,h2P1,h2P2,hPP` — the same
   Tier-2-flagged pairwise set). Its own name flags the bug
   (`_of_split`) — same shape as this roadmap's original
   `Sanchor_eq_of_anchor_roots`/`quadratic_eq_mul_X_sub_C` bug, one
   layer up.
4. **`cIotaAmIotaT_mem_principalSubgroup`** (`PrincipalWitnessStep4.lean`
   line 669) — consumes (3)'s conclusion, same `h12` threaded through
   unconditionally.
5. **`cIotaAmIotaT_mem_of_le`** (`PrincipalWitnessFinalAssembly.lean`
   line 108) — thin `hD`-pushforward wrapper around (4), same `h12`
   passed straight through, itself no new math.
6. **`cAmιTmδmιδ_mem_of_le`** (`PrincipalWitnessFinalAssembly.lean`
   line 213) — `G₁ - G₂ - G₃` composition around (5), same `h12`
   passed straight through, itself no new math.
7. **`reducedClass_eq_of_isReduction'`** (`AlphaLocusDegreeUniform.lean`
   line 808) — the top-level theorem this whole roadmap is ultimately
   about, calls (6) for `hDP`.

**Layers 5/6/7 are innocent pass-throughs** — once (1)-(4) have
tangent siblings, 5/6/7 fall out mechanically the same way they were
originally built as thin compositions. **The real work is entirely in
layers 1-4.**

## The template already exists and is fully proven: `TangentMumfordWitness.lean`

This file (different construction, `b_+` not `bCA`, tangency at `δ₀`
not at an anchor point) already solves the exact same shape of
problem: a plain 4×4 Vandermonde interpolation replaced by a
**confluent** one (three ordinary evaluation rows + one derivative
row at the repeated node), fully proven, "all 7 `sorry`s filled" per
its own status note. Every piece needed for `bCA`'s tangent case has a
direct analogue there:

| `TangentMumfordWitness.lean` (existing) | `bCA` tangent analogue (to build) |
|---|---|
| `tangentInterpMatrix` (rows: `Ra1X`, `Ra2X`, `δ₀X` eval + `δ₀X` deriv) | new matrix: rows `Ra1X` eval+deriv, `P1X` eval, `P2X` eval (tangency at the ANCHOR pair, not at `δ₀`) |
| `tangentInterpMatrix_det_ne_zero` (closed form `-(a-b)(a-d)²(b-d)²`) | new closed-form determinant, nonzero given `Ra1X ≠ P1X`, `Ra1X ≠ P2X`, `P1X ≠ P2X` only (no `Ra2X` — it's gone, replaced by the derivative row) |
| `branchDeriv H px py := (derivative H.f).eval px / (2*py)` | **not needed as-is** — see "Key simplification" below |
| `bPlusCoeff`/`bPlus` (Cramer's rule, 4 coefficients) | `bCATangentCoeff`/`bCATangent`, same shape |
| `bPlus_row_eq` (private Cramer helper) | `bCATangent_row_eq`, same shape |
| `bPlus_eval_Ra1`/`_Ra2`/`_delta0` (row identities) | `bCATangent_eval_Ra1`/`_evalP1`/`_evalP2` |
| `bPlus_deriv_eval_delta0` (the tangency row) | `bCATangent_deriv_eval_Ra1` |
| `sq_dvd_of_eval_derivative_eq_zero'` (generic, reusable as-is) | reuse directly, no changes needed |
| `dvd_pairNormBPlus_Ra1`/`_Ra2` (simple-root divisibility) | `dvd_pairNormBCATangent_P1`/`_P2` |
| `dvd_sq_pairNormBPlus_delta0` (squared-factor divisibility) | `dvd_sq_pairNormBCATangent_Ra1` |
| `dvd_pairNormBPlus_full` (coprimality glue → full divisibility) | `dvd_pairNormBCATangent_full` |
| `denomPoly`/`uANew`/`pairNormBPlus_eq_denomPoly_mul_uANew` | `denomPolyCATangent`/`uCANewTangent`/`pairNormBCATangent_eq_...` |

**Key simplification versus `TangentMumfordWitness.lean`'s own
problem**: `bPlus`'s tangency condition at `δ₀` needs `H.f`'s *implicit*
branch derivative (`branchDeriv`, since `δ₀` is a point on the curve
and there's no separate polynomial giving `y` there). `bCA`'s
tangency condition at `Ra1` (when `Ra1=Ra2`) does NOT need this
detour: `Ra1.Y = va.eval Ra1.X` is already an explicit hypothesis
(`hRa1Y`/`hsaP1Y`-style, matching `Sanchor_eq_of_anchor_roots_tangent`'s
own `hsaP1Y`), and `IsMumfordUa`'s tangent instance (`(X-C R)^2 ∣
(va^2 - H.f)`, `SanchorEqAlphaPoints.lean`'s already-established
tangent-case hypothesis shape) is EXACTLY the value+derivative-vanishing
statement needed: `va(R)² = H.f(R)` (value) and, differentiating
`va²-H.f` and using `(X-C R)² ∣ (va²-H.f)` again,
`va(R)·va'(R) = H.f'(R)/2` (derivative, `char ≠ 2` needed to divide by
2 — already a standing hypothesis, `hchar`, everywhere in this
project). So the tangency row's RHS entry is **`va.derivative.eval
R`** directly — a concrete, already-available polynomial derivative,
not a separately-constructed branch-derivative quotient. This makes
the `bCA` tangent case slightly SIMPLER than `TangentMumfordWitness.
lean`'s own, not harder.

## Concrete plan

### Step 1 — new file `CAWitnessTangent.lean` (or similar), mirroring
`TangentMumfordWitness.lean`'s structure exactly

- `caTangentInterpMatrix (RaX P1X P2X : k) : Matrix (Fin 4) (Fin 4) k`
  — row 0: `1, RaX, RaX², RaX³` (value at the doubled anchor root).
  Row 1: `0, 1, 2·RaX, 3·RaX²` (derivative at the SAME root — the
  confluent row). Row 2: `1, P1X, P1X², P1X³`. Row 3: `1, P2X, P2X²,
  P2X³`.
- `caTangentInterpRHS (RaY vaDerivAtRa P1Y P2Y : k) : Fin 4 → k :=
  ![RaY, vaDerivAtRa, -P1Y, -P2Y]` — note the `ι`-sign flip on `P1Y,
  P2Y` carries over unchanged from `caInterpRHS`'s own convention
  (`bCA` interpolates `C - A`, i.e. `ι(A)`'s Y-values, not `A`'s).
- `caTangentInterpMatrix_det_ne_zero` — compute the closed form (likely
  `± (P1X-RaX)²(P2X-RaX)²(P2X-P1X)`, by analogy with
  `tangentInterpMatrix`'s `-(Ra1X-Ra2X)(Ra1X-δ₀X)²(Ra2X-δ₀X)²` with
  the roles of "doubled node" and "ordinary nodes" swapped — **verify
  by direct expansion or a sympy check before trusting this guess**,
  matching `TangentMumfordWitness.lean`'s own stated practice of
  independently confirming the sign). Needs exactly `RaX ≠ P1X`, `RaX
  ≠ P2X`, `P1X ≠ P2X` — no distinctness fact involving a second
  "Ra2" at all, since it no longer exists as a separate node.
- `bCATangentCoeff`/`bCATangent` — Cramer's rule, same pattern.
- `bCATangent_row_eq` (private helper) + the four public row-identity
  theorems (`bCATangent_eval_Ra`, `bCATangent_deriv_eval_Ra`,
  `bCATangent_eval_P1`, `bCATangent_eval_P2`).
- Divisibility section: `dvd_pairNormBCATangent_P1`/`_P2` (simple
  roots, mirror `dvd_pairNormBPlus_Ra1`/`_Ra2` exactly),
  `dvd_sq_pairNormBCATangent_Ra` (squared root at `RaX`, mirror
  `dvd_sq_pairNormBPlus_delta0`, reusing `sq_dvd_of_eval_derivative_eq_
  zero'` as-is — **check whether this generic lemma needs importing
  from `TangentMumfordWitness.lean` or duplicating**; prefer importing,
  it's already `[Field k]`-generic with no `δ₀`/`bPlus`-specific
  content), `dvd_pairNormBCATangent_full` (coprimality glue — three
  factors this time, `(X-C RaX)²`, `(X-C P1X)`, `(X-C P2X)`, not four).
- `denomPolyCATangent := (X-C RaX)^2 * (X-C P1X) * (X-C P2X)`,
  `uCANewTangent := (H.f - bCATangent²) /ₘ denomPolyCATangent`,
  `pairNormBCATangent_eq_denomPolyCATangent_mul_uCANewTangent` — mirror
  `denomPoly`/`uANew`/`pairNormBPlus_eq_denomPoly_mul_uANew` exactly.

**Estimated size**: `TangentMumfordWitness.lean` is 640 lines for the
same shape of construction (with the extra `branchDeriv` detour this
case doesn't need) — expect this new file to land smaller, maybe
400-500 lines, still needing a fresh 1500-line budget check once
drafted.

### Step 2 — tangent sibling for `CAWitnessDivisor.lean`'s four-point
`ordAt` facts (NOT YET TRACED — do this before starting Step 1's
actual Lean, not after)

`divToPair_eq_C_add_iotaA_add_T_of_split`'s proof body (Step 3's item
3 above) reuses `CAWitnessDivisor.lean`'s per-point `ordAt = 1`
lemmas (`hOrdRa1`/`hOrdRa2`/`hOrdιP1`/`hOrdιP2` in that file, built via
`ordAt_eq_one_of_old_point` + `ordAt_A_eq_one_of_eval_ne_zero`). The
tangent case needs: `ordAt` at the single doubled anchor point `Ra` is
now **`2`**, not two separate `= 1` facts — same
`ordAt_eq_two_of_old_point` (`PrincipalWitness.lean` line ~1030,
already used by this session's `ordAt_negVa_one_eq_two_of_mem_Sanchor_
tangent`) should apply again here, composed with `caTangentInterp
Matrix`'s own multiplicity-2 fact at `RaX` (via `rootMultiplicity_X_
sub_C_pow` applied to `denomPolyCATangent`'s `(X-C RaX)^2` factor,
same pattern as `SanchorMumfordOrdAt.lean`'s `ordAt_ua_eq_two_of_mem_
Sanchor_tangent`, which this doc's Step 1 companion piece already
fixed and can be copied from directly). **Check `CAWitnessDivisor.
lean`'s exact file/theorem names before starting** — not confirmed in
this pass, this doc's chain-trace stopped at `CAWitness.lean` and
`PrincipalWitnessStep3.lean`, `CAWitnessDivisor.lean` itself was not
opened.

### Step 3 — `divToPair_eq_C_add_iotaA_add_T_of_split_tangent`
(`PrincipalWitnessStep3.lean` tangent sibling, new file or appended —
check 1500-line budget first, `PrincipalWitnessStep3.lean` is
currently 447 lines so likely fine to append)

Five-point support now (`{Ra, ιP1, ιP2, PtT1, PtT2}`, one fewer than
the split case's six, `Ra` carrying coefficient `2` not two separate
`Ra1,Ra2` each carrying `1`). Mirrors the split case's `eq_of_coeffAt_
eq` + 5-way `by_cases` structure (one fewer case than the six-way
split does). Conclusion: `divToPair (-bCATangent ...) 1 {Ra, ιP1, ιP2,
PtT1, PtT2} = 2•single Ra + single ιP1 + single ιP2 + single PtT1 +
single PtT2`.

### Step 4 — tangent siblings for layers 4-7 of the chain

Once Step 3 exists, `cIotaAmIotaT_mem_principalSubgroup`,
`cIotaAmIotaT_mem_of_le`, `cAmιTmδmιδ_mem_of_le` (all in
`PrincipalWitnessFinalAssembly.lean`/`PrincipalWitnessStep4.lean`)
each need a `_tangent` sibling — but per the "innocent pass-through"
observation above, these should be genuinely mechanical once Step 3
is in hand (swap the `2•single Ra` shape through the same `abel`-style
composition each of these already uses). **Do not attempt these
before Step 3 is REPL-confirmed** — their proofs are thin compositions
and any error in Step 3 will surface as confusing failures here
instead of at its actual source.

### Step 5 — only then: wire into `reducedClass_eq_of_isReduction'`
itself

This is where `ROADMAP-split-hypothesis-elimination.md`'s Tier 1a step
2 (the `_split`/`_tangent` top-level theorem split, `AlphaLocusDegree
UniformTangent.lean` or similar) finally becomes attemptable — not
before. At that point ALSO revisit `hPtT1X : PtT1.X ≠ PtT2.X` (Tier
1's item 2b, `AlphaLocusDegreeUniform.lean` line ~1076) and the
`hQ1_def`/`hQ2_def` factored-shape hypotheses flagged there — the main
roadmap's own note that these should "fold into the same follow-up
piece of work" as this doc's Step 1 turns out to be correct: `uCANew
Tangent`'s own residual-splitting story is the same shape of problem
one more layer down, and should reuse this doc's Step 1 pattern rather
than being scoped separately.

## What NOT to do

- Do not attempt to weaken `caInterpMatrix_det_ne_zero` itself, or
  patch around its `Ra1X ≠ Ra2X` hypothesis with a case split inside
  the SAME matrix — the plain Vandermonde matrix is genuinely singular
  at that point; there is no proof-engineering trick that avoids
  needing a structurally different matrix.
- Do not try to unify `caTangentInterpMatrix` and `caInterpMatrix`
  into one parameterized construction (e.g. via a `Fin 4 → k × Option
  k` node-with-optional-derivative encoding) — `TangentMumfordWitness.
  lean` didn't do this for its own analogous case (it has both
  `tangentInterpMatrix` and, implicitly via `CantorAddWitness.lean`'s
  `minusInterpMatrix`, a plain sibling, kept as separate definitions),
  and forcing a unification here is speculative extra engineering with
  no evidence it simplifies anything.
- Do not skip Step 2's `CAWitnessDivisor.lean` trace — Step 1 alone
  (a well-defined tangent `bCA`) is necessary but not sufficient; the
  divisor-level `ordAt` facts consuming it need their own tangent
  argument, and skipping ahead to Step 3 without Step 2 in hand will
  hit a wall partway through Step 3's proof.
