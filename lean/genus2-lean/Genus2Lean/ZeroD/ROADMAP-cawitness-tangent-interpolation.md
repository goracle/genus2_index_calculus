# Roadmap: CAWitness tangent-case interpolation (Tier 2, spun off from
# `ROADMAP-split-hypothesis-elimination.md`)

## Goal

`ROADMAP-split-hypothesis-elimination.md`'s Tier 2 is the last
remaining piece of the split-hypothesis-elimination effort, and per
that doc's own step 5/6 it's real, separate work — a genuinely new
interpolation construction, not a wiring job like Tier 1 was. This doc
scopes it on its own, against the CURRENT state of the code (Tier 1
anchor + target tangent cases are both done, build green, as of this
pass), so nothing here should be assumed stale.

**Endpoint**: `CAWitness.lean`'s `dvd_pairNormBCA_full` and its
downstream consumers (`uCANew`, everything built on it) no longer
require `h12,h1P1,h1P2,h2P1,h2P2,hPP` (six pairwise-distinctness
hypotheses among `{Ra1X,Ra2X,P1X,P2X}`) unconditionally — any
collision pattern among those four points is handled, either by a
hypothesis-free `lcm`-based divisibility argument (already available)
or by a genuine tangent-case degree/multiplicity branch (not yet
written).

## Two independent problems, not one

Tracing `dvd_pairNormBCA_full` → `caInterpMatrix` → `uCANew` surfaces
two SEPARATE obstacles that happen to share the same six hypotheses in
their signatures. Conflating them was the mistake the previous pass
corrected; keep them apart here too:

1. **Divisibility** (`dvd_pairNormBCA_full`, line 338): already solved,
   zero new math needed — see "Part A" below. Purely a porting task.
2. **Nondegeneracy of the interpolation matrix itself**
   (`caInterpMatrix_det_ne_zero`, line 137) and, downstream, **exact
   degree** of the combined polynomial (`npoly4Lcm4_natDegree_eq_six`,
   `GeneralSharedRoot.lean` line 839): genuinely unsolved for any
   colliding pair, requires new multiplicity-aware machinery — see
   "Part B" below. This is the actual hard part.

Part A can be ported now, independently of Part B, and doing so
narrows Part B's scope (see "Suggested order").

## Part A: `dvd_pairNormBCA_full` — port `lcm_dvd_of_four_dvd`, no new math

**Current state** (`CAWitness.lean` lines 338-379): six pairwise
`IsCoprime` hypotheses (`hc12,hc1P1,hc2P1,hc1P2,hc2P2,hcPP`), each
built from `hdet`'s six input inequalities, sequentially glued via
`IsCoprime.mul_dvd`/`.mul_left`. This is exactly the
sequential-coprime-glue pattern `GeneralSharedRoot.lean`'s own
docstring (around its `GeneralLcmCombine` section) says doesn't scale.

**The fix**: `lcm_dvd_of_four_dvd` (`GeneralSharedRoot.lean` line 81)
already proves
`lcm(lcm q1 q2, lcm q3 q4) ∣ N` from `q1∣N, q2∣N, q3∣N, q4∣N` alone —
**zero coprimality hypotheses**. `dvd_pairNormBCA_full`'s four
individual divisibility facts (`dvd_pairNormBCA_Ra1/Ra2/P1/P2`,
already unconditional — no `h12`-family hypothesis needed for THESE,
confirmed by reading their signatures) feed directly into it.

**Concretely**:
- New conclusion shape:
  `EuclideanDomain.lcm (EuclideanDomain.lcm (X-C Ra1X) (X-C Ra2X))
    (EuclideanDomain.lcm (X-C P1X) (X-C P2X)) ∣ (H.f - bCA^2)`
  — note this is an `lcm`, not the literal product
  `(X-C Ra1X)*(X-C Ra2X)*(X-C P1X)*(X-C P2X)` the current
  `dvd_pairNormBCA_full` states. The two agree (up to a unit) exactly
  when all four x-coordinates are pairwise distinct; when some
  collide, the `lcm` is the CORRECT (smaller-degree) object and the
  literal product is not even the right divisor to name. Downstream
  callers of `dvd_pairNormBCA_full` that assume the product shape will
  need to either keep a `_of_split` product-shaped corollary (derived
  from the `lcm` version plus the six distinctness facts, trivial) or
  migrate to the `lcm` shape directly — check
  `pairNormBCA_eq_denomPolyCA_mul_uCANew` (line 397, same file) and
  anything past it before deciding which.
- Still needs `hdet ≠ 0` (feeds `dvd_pairNormBCA_Ra1/Ra2/P1/P2`
  themselves, which are unconditional in the six distinctness
  hypotheses but NOT in `hdet`) — `hdet` itself is Part B's problem,
  not Part A's. Part A removes the six pairwise hypotheses from
  `dvd_pairNormBCA_full`'s OWN signature; it does not yet let you call
  it with a genuinely degenerate `caInterpMatrix`, because `hdet` is
  still assumed. That's fine — Part A is scoped as "stop assuming
  distinctness where the proof doesn't structurally need it," not "make
  `hdet` provable in the tangent case."

**Risk**: low. `GeneralSharedRoot.lean`'s own `npoly4Lcm4`-family
theorems already exercise this exact pattern (four inputs, `lcm`
combining, no per-pair coprimality) successfully — this is a direct
port, not new proof technique.

## Part B: nondegeneracy and exact degree in the tangent case — real work

**Where `hdet` actually breaks**: `caInterpMatrix_det_ne_zero` (line
137-156)'s closed-form determinant is
`(Ra2X-Ra1X)*(P1X-Ra1X)*(P2X-Ra1X)*(P1X-Ra2X)*(P2X-Ra2X)*(P2X-P1X)`
— literally the product of the six pairwise differences. ANY collision
among `{Ra1X,Ra2X,P1X,P2X}` zeroes exactly one factor and makes the
whole determinant zero. This is a genuine Vandermonde-style
singularity (four interpolation nodes, one coincides with another),
not a proof-engineering artifact — confirmed by reading the closed
form directly, not assumed.

**Precedent that already solved the identical shape of problem**:
`ROADMAP-principal-witness-tangent-assembly.md` (closed, all 5 steps
done) hit exactly this for the ANCHOR-only case
(`caTangentInterpMatrix`, `TangentMumfordWitness.lean`) — a confluent
Vandermonde replacing a plain one, using the derivative row instead of
a second node. That doc's closing note says the `bCA` version "turned
out to be simpler (no branch-derivative detour needed; `va`'s own
polynomial derivative suffices)" — worth re-reading before starting,
since whatever made it simpler there may or may not carry over to a
4-point (not 2-point) interpolant with potentially TWO of the four
nodes colliding independently (anchor pair, target pair, or a
cross-pair like `Ra1X = P1X`).

**Scope split by collision pattern** — do not assume they're all the
same difficulty; each replaces exactly one row-pair of
`caInterpMatrix` with a confluent (derivative) row, but the derivative
data available differs:

1. **`Ra1X = Ra2X` only** (anchor doubled, target split): **CONFIRMED
   already built and already wired to the top level** —
   `CAWitnessTangent.lean` has `caTangentInterpMatrix`/`bCATangent`/
   `dvd_pairNormBCATangent_full`/`uCANewTangent`, all proven, no
   sorries, and genuinely consumed by
   `AlphaLocusDegreeUniformTangent.lean`'s top-level
   `reducedClass_eq_of_isReduction'_tangent` (checked directly — not
   `TangentMumfordWitness.lean`'s `tangentInterpMatrix`, which is an
   unrelated 3-point `bPlus` construction). No new work needed for this
   case; see "Suggested order" item 3 below for the one caveat that
   does carry over (the determinant closed form is unverified).
2. **`P1X = P2X` only** (target doubled, anchor split): **CONFIRMED
   already built**, this is not an open question —
   `AlphaLocusDegreeUniformTangentTarget.lean` (this pass's item 4)
   already has `caTangentTargetInterpMatrix`, `bCATangentTarget`,
   `uCANewTangentTarget`, `vDerivAtP : F p`, and
   `hPDeriv : 2 * PtP.Y * vDerivAtP = (derivative H.f).eval PtP.X`,
   all fully wired into `hDP_tangent_target_aux`'s signature and
   proven, no sorries. This is EXACTLY case 2's interpolation
   machinery, already done as a byproduct of Tier 1's item 4 — **case
   2 needs no new interpolation-matrix work**, only porting/adapting
   this existing machinery from that file's specific context into
   `CAWitness.lean`'s `dvd_pairNormBCA_full`/`uCANew` if they're not
   already the same construction under different names (check that
   first — `caTangentTargetInterpMatrix` may simply BE the fix for
   `caInterpMatrix`'s `P1X=P2X` collapse, not a separate one-off).
3. **A cross-pair collision** (`Ra1X = P1X`, etc.) — **CONFIRMED
   reachable, and turns out to split into two sub-cases, one genuinely
   new work, one a structural impossibility.** `AlphaLocusDegreeUniform.
   lean`'s top-level `reducedClass_eq_of_isReduction'` currently has
   `h1P1 : Ra1.X ≠ sa.P1.X`, `h1P2 : Ra1.X ≠ sa.P2.X`,
   `h2P1 : Ra2.X ≠ sa.P1.X`, `h2P2 : Ra2.X ≠ sa.P2.X` as live,
   unconditional hypotheses (line 1062-1063), traced all the way
   through to `cAmιTmδmιδ_mem_of_le`'s call (line 1207) — the same
   4-layer chain 1b already traced for `h12`/`hRa12Xne`. (`hPP :
   sa.P1.X ≠ sa.P2.X` itself is case 2's own axis, not new here.)

   **Worked out this pass, from the curve equation directly**: when
   `Ra1.X = sa.P1.X =: x`, both `Ra1.Y` and `sa.P1.Y` are square roots
   of `H.f.eval x` (`hRa1_curve`/`hP1_curve`), so ONLY two things can
   happen — and both are already forced by hypotheses the top-level
   theorem already carries (`hchar : (2:F p)≠0`, `hRa1Y_ne : Ra1.Y≠0`):
   - **`Ra1.Y = sa.P1.Y`** (with `sa.P1.Y ≠ 0`, generic): this would
     require `Ra1.Y = -sa.P1.Y` too (since `bCA`'s RHS row for `sa.P1`
     is `-sa.P1.Y = -Ra1.Y`, and the two rows sharing an x-coordinate
     but wanting DIFFERENT target values makes the interpolation
     problem itself infeasible, not just the matrix singular) — forcing
     `2·Ra1.Y = 0`, contradicting `hchar`/`hRa1Y_ne`. **Genuinely
     impossible under hypotheses already in scope — Tier-3-style, needs
     no interpolation work, just a short lemma deriving `False` from
     `hRa1Y_ne`/`hchar`/the two curve equations.**
   - **`Ra1.Y = -sa.P1.Y`**, i.e. `Ra1 = ι(sa.P1)` as points: the ONLY
     reachable sub-case, and a genuine tangency — `bCA`'s two rows for
     `Ra1` and `ι(sa.P1)` now want the SAME target value at the SAME
     x-coordinate, i.e. the honest confluent case.

   **Cross-pair confluent matrix worked out and verified via
   independent sympy computation** (not the Lean REPL — per Claire's
   instruction, that happens only when there's new Lean code to test;
   this was a symbolic-algebra sanity check on the matrix shape before
   writing any Lean): with the doubled node at the ORIGINAL matrix's
   row-0 (`Ra1`'s slot) and row-2 (`P1`'s slot) — non-adjacent, unlike
   cases 1/2's adjacent-row doubling — replacing row 2 with a derivative
   row `[0,1,2x,3x²]` gives
   `det = -(x-P2X)²(P2X-Ra2X)(x-Ra2X)²`, nonzero exactly when the
   doubled node, `Ra2X`, and `P2X` are pairwise distinct — three
   hypotheses, not five. (As a byproduct, also verified BOTH existing
   "guessed, unverified" closed forms independently:
   `caTangentInterpMatrix_det_ne_zero`'s
   `(P1X-RaX)²(P2X-RaX)²(P2X-P1X)` and
   `caTangentTargetInterpMatrix_det_ne_zero`'s
   `(Ra1X-PX)²(Ra2X-PX)²(Ra2X-Ra1X)` both check out exactly against
   sympy — the "REPL/sympy-check independently" caveat in both
   docstrings can be marked resolved, modulo an actual Lean REPL run
   whenever either theorem's file is next touched.)

   **Not yet written**: the actual Lean (RHS convention for the mixed
   row — needs the SAME sign-flip bookkeeping question cases 1/2 hit,
   i.e. does the derivative row's target value get the `ι`-flip or not
   — checked and it's a free bookkeeping choice, not forced by geometry,
   since `bCATangentTarget_deriv_eval_P`'s docstring confirms the flip
   is baked in via the RHS solve, not derived from curve structure), nor
   the `dvd_..._full`/`uCANew`-shaped consumers, nor the
   impossibility lemma for the other sub-case. **This is the actual
   remaining substance of Part B** — three named-but-unwritten pieces
   (impossibility lemma, cross-pair matrix construction, its `dvd`/
   `uCANew` consumers), plus the three other cross-pair variants by
   symmetry (`Ra1=ι(sa.P2)`, `Ra2=ι(sa.P1)`, `Ra2=ι(sa.P2)` — each
   needs the same treatment, matrix shape differs only in which row
   pair is doubled).
4. **Two simultaneous collisions** (`Ra1X=Ra2X` AND `P1X=P2X`): both
   individually already exist as complete, independent top-level
   theorems (`reducedClass_eq_of_isReduction'_tangent` and
   `reducedClass_eq_of_isReduction'_tangent_target`), so "do they
   compose" is really asking whether a caller ever needs a FIFTH
   top-level theorem for the simultaneous case, or whether every actual
   caller's data only ever hits one axis being tangent at a time. Not
   yet checked — do this check (not the matrix-composition question,
   which is moot until a caller is confirmed to need it) before writing
   anything here.

**`npoly4Lcm4_natDegree_eq_six` mirrors the same problem one layer up**
(`GeneralSharedRoot.lean` line 839): its degree-4 sub-lemma
`npoly4LcmQuadraticPair_natDegree_eq_four` and degree-2 sub-lemma
`npoly4LcmLinearPair_natDegree_eq_two` (line 597) each require their
own pairwise `≠` hypothesis for the same reason —
`npoly4LcmLinearPair_natDegree_eq_two`'s proof is literally
`lcm(a,a) = a` (degree collapses 2→1) when the inputs coincide, read
directly from that lemma's proof (`gcd_mul_lcm`/coprimality-degree
argument breaks the moment `IsCoprime` fails). **This is the exact
same phenomenon Tier 1 solved for `ua`/`va`'s `ordAt`** (`lcm` of two
copies of one factor collapses, doesn't double) — the fix shape is
known (`OrdAtRootMultiplicityUnified.lean`'s pattern, per the original
roadmap's Tier 2 notes), just not yet ported to
`npoly4Lcm4_natDegree_eq_six`'s four-way setting.

## Suggested order

1. **Done, build green:** Part A — ported `lcm_dvd_of_four_dvd`
   (qualified as `Genus2Lean.TheDataDerivation.lcm_dvd_of_four_dvd`,
   its actual namespace) into a new theorem,
   `lcm_dvd_pairNormBCA_full` (`CAWitness.lean`), fully unconditional
   in the six pairwise-distinctness hypotheses (`hdet` still required —
   that's Part B's problem, not Part A's). Needed
   `[DecidableEq k[X]]` as an explicit instance argument (not
   `classical` inside the proof body — that doesn't reach a
   `Decidable` obligation sitting in the theorem's own *statement*),
   mirroring `lcm_dvd_of_four_dvd`'s own signature exactly.
   `dvd_pairNormBCA_full` itself (the product-shaped original) was
   deliberately left untouched, since its only caller
   (`pairNormBCA_eq_denomPolyCA_mul_uCANew`, same file) genuinely needs
   the literal-product shape for `denomPolyCA`'s `%ₘ`/`/ₘ` division —
   `lcm_dvd_pairNormBCA_full` is additive, not a replacement, exactly
   as this doc's Part A section anticipated.
2. **Done, this pass:** confirmed `caTangentTargetInterpMatrix`
   (actually defined in `CAWitnessTangentTarget.lean`, not
   `AlphaLocusDegreeUniformTangentTarget.lean` — that file only reaches
   it transitively via `PrincipalWitnessFinalAssemblyTangentTarget.lean`
   → `CAWitnessAssemblyTangentTarget.lean`) is genuinely the right
   confluent-Vandermonde construction for case 2 (`P1X=P2X`), by direct
   comparison: `caInterpMatrix Ra1X Ra2X P1X P2X`'s rows are
   `[Ra1,Ra2,P1,P2]` (all plain evaluation); `caTangentTargetInterpMatrix
   Ra1X Ra2X PX`'s rows are `[Ra1,Ra2,P,P']` where row 3 is `P`'s
   DERIVATIVE row, replacing the second target-point row — same
   construction, `bCATangentTarget` is `bCA`'s structurally-parallel
   tangent-case sibling (same `caCoeff`/Cramer idiom, same `H.f` role).
   **NOT directly reusable as a drop-in for `CAWitness.lean`'s own
   functions without new wiring**, though — it's parametrized by one
   `PX` (`CAWitness.lean`'s functions take `P1X P2X` as two separate
   arguments), so `CAWitness.lean`'s own `dvd_pairNormBCA_full`/`uCANew`
   need a tangent-case sibling BUILT ON `bCATangentTarget`/
   `caTangentTargetCoeff` (calling them with the shared value
   `PX := P1X = P2X`), not a literal substitution into the existing
   split-case signatures.
   **Caveat found, worth flagging before building on this further**:
   `caTangentTargetInterpMatrix_det_ne_zero`'s closed-form determinant
   (`(Ra1X-PX)^2 * (Ra2X-PX)^2 * (Ra2X-Ra1X)`) is explicitly flagged in
   its own docstring as "guessed... REPL/sympy-check this independently
   before trusting it," and — checked directly — has **zero callers
   anywhere in the codebase**. The item-4 build that went green does
   NOT exercise this lemma: `PrincipalWitnessFinalAssemblyTangentTarget.
   lean` takes `hdet : (caTangentTargetInterpMatrix ...).det ≠ 0` as a
   caller-supplied HYPOTHESIS, never derived from the closed-form
   proof. So "build green" does not mean this determinant claim is
   verified — **REPL-check `caTangentTargetInterpMatrix_det_ne_zero`
   itself (not just its callers) before relying on it** for case 2's
   actual nondegeneracy proof, the same way `caInterpMatrix_det_ne_zero`
   was read directly (not assumed) for Part B's original scoping.
3. **Done — case 1 turns out to already be fully built, not new work.**
   Checked `CAWitnessTangent.lean` directly (not
   `TangentMumfordWitness.lean`, which is a different, 3-point
   `bPlus`/anchor-vs-`delta0` construction unrelated to `bCA`): it
   already has `caTangentInterpMatrix`/`caTangentCoeff`/`bCATangent`
   (row 0-1 confluent at the doubled anchor `RaX`, rows 2-3 plain at
   `P1X,P2X` — exactly case 1's shape) AND, crucially, the full
   `dvd_pairNormBCA_full`/`uCANew` tangent-siblings themselves:
   `dvd_pairNormBCATangent_full` and `uCANewTangent`, both already
   proven, no sorries. Confirmed these are genuinely wired into the
   top-level `reducedClass_eq_of_isReduction'_tangent`
   (`AlphaLocusDegreeUniformTangent.lean`'s `hQ1_def`/`hQ2_def`/`hU_ne0`
   etc. all reference `uCANewTangent` directly), not a disconnected
   parallel construction — this was part of what Tier 1's anchor-axis
   work already closed, just not previously connected in this doc to
   Tier 2's Part-B case breakdown. **Same unverified-determinant caveat
   as case 2 applies here too**: `caTangentInterpMatrix_det_ne_zero`'s
   closed form (`(P1X-RaX)^2*(P2X-RaX)^2*(P2X-P1X)`) is self-flagged
   "guessed... REPL/sympy-check independently" in its own docstring and
   has zero callers — every consumer in the chain takes `hdet` as a
   caller-supplied hypothesis instead. **Net effect on this doc's
   scope: case 1 needs no new proof work**, only the same determinant
   verification case 2 needs, when code changes prompt a REPL check.
4. **Done — case 2 also turns out to already be fully built.** Checked
   `CAWitnessTangentTarget.lean` directly (the actual home of
   `bCATangentTarget`, not just the interpolation matrix mentioned in
   step 2): it already has `dvd_pairNormBCATangentTarget_full` and
   `uCANewTangentTarget`, proven, no sorries — the exact `CAWitness.lean`
   -facing siblings this item originally set out to write. Confirmed
   wired into the top-level `reducedClass_eq_of_isReduction'_tangent_
   target` the same way case 1's were (`hQ1_def`/`hQ2_def`/`hU_ne0` in
   `AlphaLocusDegreeUniformTangentTarget.lean` reference
   `uCANewTangentTarget` directly). **No new proof work needed for case
   2 either** — same unverified-determinant caveat as case 1, nothing
   more.
5. **Case 3 (cross-pair, `Ra1X=P1X`-style): all four symmetric
   variants now built, build pending REPL confirmation on the newest
   two.** `Ra1 = ι(sa.P1)` was already built (`CAWitnessCrossTangent2.lean`
   + `CAWitnessCrossTangent3.lean`, two files) before this session.
   `Ra1 = ι(sa.P2)` was built earlier this session
   (`CAWitnessCrossTangentV2.lean`, single-file, no sorries, REPL-
   confirmed, build green). `Ra2 = ι(sa.P1)`
   (`CAWitnessCrossTangentV3.lean`, single-file, no sorries in source)
   and `Ra2 = ι(sa.P2)` (`CAWitnessCrossTangentV4.lean`, single-file,
   no sorries in source) were both built this pass, completing all
   four. Neither of these last two has been run through Claire's REPL
   yet.

   **Determinant signs, confirmed via independent sympy check for each
   variant separately — do NOT assume a pattern from row-adjacency
   alone:**
   - `Ra1=ι(sa.P1)` (rows 0/2, non-adjacent): `-(x-P2X)^2(P2X-Ra2X)(x-Ra2X)^2`
   - `Ra1=ι(sa.P2)` (rows 0/3, non-adjacent): `-(RaX-Ra2X)^2(Ra2X-P1X)(RaX-P1X)^2`
   - `Ra2=ι(sa.P1)` (rows 1/2, adjacent): `(RaX-P2X)^2(P2X-Ra1X)(RaX-Ra1X)^2`
     — **NO leading minus sign**, the one exception among the four.
   - `Ra2=ι(sa.P2)` (rows 1/3, non-adjacent): `-(x-P1X)^2(P1X-Ra1X)(x-Ra1X)^2`
   So sign does not correlate cleanly with adjacent-vs-non-adjacent row
   position; each variant's sign was checked on its own, and any future
   variant of this shape (should one ever be needed) should be too.

   **Still open, the actual remaining substance of case 3 as a
   whole:** none of the four variants are wired into
   `AlphaLocusDegreeUniform.lean`'s top-level theorem yet (confirmed by
   grep — nothing outside each variant's own file references
   `uCANewCross`/`uCANewCross2`/`uCANewCross3`/`uCANewCross4`). That
   wiring — building the actual `h1P1,h1P2,h2P1,h2P2`-eliminating
   top-level consequence out of these four building blocks, the same
   way Tier 1's anchor/target tangent siblings were wired into their
   own top-level theorems — is the next task, along with the
   impossibility-lemma half of each variant (the `Ra1=sa.P1`-style
   same-point, non-tangent sub-case; already handled in general by
   `CAWitnessCrossTangent.lean`'s `eq_iota_of_X_eq_of_ne`, just needs
   threading through each of the four call sites).

   **Wiring chain traced this pass, before writing anything — genuinely
   FIVE layers deep, not four, for the cross-pair case specifically.**
   `h1P1,h1P2,h2P1,h2P2,hPP` are consumed at exactly one call site in
   `AlphaLocusDegreeUniform.lean` (line ~1207,
   `cAmιTmδmιδ_mem_of_le`'s call), passed straight through unused at
   that layer. Traced the FULL chain beneath it (the same discipline
   Tier 1b used originally):
   1. `cAmιTmδmιδ_mem_of_le` (`PrincipalWitnessFinalAssembly.lean` line
      213) — pass-through, `h1P1` etc. unused here directly.
   2. → `cIotaAmIotaT_mem_of_le` (same file, line 108) — same
      pass-through.
   3. → `cIotaAmIotaT_mem_principalSubgroup` (`PrincipalWitnessStep4.lean`,
      called at line 175 inside `cIotaAmIotaT_mem_of_le`'s proof) AND
      `divToPair_eq_C_add_iotaA_add_T_of_split` (`PrincipalWitnessStep3.lean`,
      called at line 183) — **checked via grep: NEITHER file has any
      `_tangent`- or `_cross`-named sibling anywhere.** This is one
      layer DEEPER than Tier 1b's own chain needed to go for the
      anchor/target axes (those were absorbed at
      `CAWitness.lean`'s `caInterpMatrix` level, layer 3 in THAT
      chain) — the cross-pair collision's actual root, `Ra1X=P1X`
      (say), doesn't just break `caInterpMatrix`'s nondegeneracy (now
      fixed, all four variants), it ALSO breaks `divToPair_eq_C_add_
      iotaA_add_T_of_split`'s own six pairwise-distinctness hypotheses
      (`h12,h1P1,h1P2,h2P1,h2P2,hPP`, same names, same file line 104)
      and `cIotaAmIotaT_mem_principalSubgroup`'s (presumably the same
      shape — not yet read in detail, check before starting).

   **So the real remaining work for case 3 is not just "wire the four
   `uCANewCross*` constructions into the top-level theorem" — it's
   "give `divToPair_eq_C_add_iotaA_add_T_of_split` and
   `cIotaAmIotaT_mem_principalSubgroup` their OWN cross-pair tangent
   siblings first" (comparable in scope to what Tier 1b already did
   once, for a different pair of axes), and only then does the
   `cIotaAmIotaT_mem_of_le`/`cAmιTmδmιδ_mem_of_le` layer's own
   cross-pair siblings become a mechanical wiring exercise the way
   Tier 1b's final step was.** Concretely, before writing any new
   top-level theorem file:
   1. Read `divToPair_eq_C_add_iotaA_add_T_of_split`'s full proof body
      (`PrincipalWitnessStep3.lean`) to see exactly how/where its six
      distinctness hypotheses get used — the same "trace before
      assuming" discipline this whole roadmap has used throughout.
      Likely uses `GeneralSharedRoot.lean`'s machinery (per this doc's
      original Part A/B framing) — confirm which parts are the
      `lcm`-divisibility (already unconditional, Part A) vs. the
      exact-degree/multiplicity argument (Part B, genuinely needs the
      four `bCACross*`/`uCANewCross*` constructions this pass built).
   2. Do the same for `cIotaAmIotaT_mem_principalSubgroup`
      (`PrincipalWitnessStep4.lean`).
   3. Only once both of those have cross-pair-tangent siblings (four
      variants each, or a shared generic-collision-point argument if
      one cleanly covers all four — check before assuming four
      separate proofs are needed) does writing
      `cIotaAmIotaT_mem_of_le_cross`/`cAmιTmδmιδ_mem_of_le_cross`
      become the mechanical composition Tier 1b's own final step was.
   4. Only after that does the actual top-level
      `reducedClass_eq_of_isReduction'_cross_tangent`-style theorem
      (or four of them, or a shared one parametrized by which pair
      collided — same "check before assuming four are needed"
      caution) become buildable — expect this to be comparable in
      line count to `AlphaLocusDegreeUniformTangent.lean` (612 lines)
      per variant, so budget file-count accordingly against the
      1500-line ceiling; likely wants its own new file(s) per variant,
      following Tier 1's own established convention rather than
      growing an existing file.

   **Update, later pass**: steps 1-2 above (`divToPair_eq_C_add_iotaA_add_T_of_split_crossN`
   and `cIotaAmIotaT_mem_principalSubgroup_crossN` for all four variants,
   `N = 1,2,3,4`) are now DONE and sorry-free — confirmed directly by
   reading `CAWitnessCrossTangent{1,2,3,4}Assembly.lean`, not assumed
   from this doc's own prior "not started" note, which was stale by the
   time this was checked. Step 3 (the `cIotaAmIotaT_mem_of_le`/
   `cAmιTmδmιδ_mem_of_le`-layer composition, i.e. Tier 1b's own final
   step, mirrored) is now PARTIALLY done: `CAWitnessCrossTangentMemOfLe.lean`
   (new file) has `cIotaAmIotaT_mem_of_le_cross{1,2,3,4}`, the direct
   `hD`-pushforward/`single`-sum-rewrite mirror of
   `PrincipalWitnessFinalAssembly.lean`'s `cIotaAmIotaT_mem_of_le`, for
   all four variants — **drafted this pass, NOT YET REPL-confirmed**
   (per Claire's own instruction, REPL-testing is done by her, not
   assumed green here). Two things to check first if this comes back
   with errors: (1) the `rw [← hPtT1X, ← hPtT2X] at hmem` step, present
   in the original `cIotaAmIotaT_mem_of_le` to align `hraw`'s raw
   `linX T1X`/`linX T2X` term with `divToPair_hT_eq`'s `PtT1.X`/`PtT2.X`-
   named conclusion before the `rw [hLHS, hRHS]` step — ported here
   identically, but worth double-checking against each variant's actual
   elaborated term shape, since `simp`/`rw` motive issues in this
   codebase have previously been naming-shape-sensitive (see this
   file's own Tier-1-derived cautions in the parent roadmap); (2) the
   final `abel`-proved `heq` step's LHS/RHS shapes were written by hand
   to mirror each variant's own `divToPair_eq_C_add_iotaA_add_T_of_split_crossN`
   conclusion shape (cross1/cross2: `(2:ℤ)•single PtRa + single PtRa2/PtRa1
   + ...`; cross3/cross4: `single PtRa1 + (2:ℤ)•single PtRa + ...`, doubled
   term in the SECOND position, matching each variant's own asymmetric
   conclusion — not a copy-paste of one shape across all four) — worth a
   second look if `abel` fails to close any of the four.

   **Still not done**: `cAmιTmδmιδ_mem_of_le_crossN`'s own `G₁-G₂-G₃`
   composition (needs `fiber_diff_mem_of_le`, `PrincipalWitnessFinalAssembly.lean`,
   called against the correct un-doubled anchor/target points per
   variant — e.g. cross1's `fiber_diff_mem_of_le` calls would need
   `PtRa2`/something and `δ₀`, `PtιP2`/something and `δ₀`, mirroring the
   split case's `G₂,G₃` but against the THREE surviving un-doubled
   points per variant, not four — not yet worked out per-variant, left
   for a follow-up pass to keep `CAWitnessCrossTangentMemOfLe.lean`'s
   diff reviewable on its own), nor the eventual top-level
   `reducedClass_eq_of_isReduction'_cross_tangentN`-style theorem. Budget
   this as the next piece once the REPL confirms the current file is
   green.
6. **Case 4** (double collision) — checked: both single-axis top-level
   theorems already exist independently
   (`reducedClass_eq_of_isReduction'_tangent`/`_tangent_target`), so
   this reduces to "does any actual caller need both axes tangent at
   once" rather than a matrix-composition question. Not yet checked —
   do that check first if this is ever picked up; don't assume the
   need exists.
7. **`npoly4Lcm4_natDegree_eq_six`'s own tangent branches** — port the
   `OrdAtRootMultiplicityUnified.lean`-style degree-collapse argument
   into `npoly4LcmLinearPair_natDegree_eq_two`/
   `npoly4LcmQuadraticPair_natDegree_eq_four`'s tangent siblings. Can
   happen in parallel with 3-6 since it's a different file
   (`GeneralSharedRoot.lean`) with its own hypothesis surface, not
   downstream of `CAWitness.lean`. Not yet started.
8. Once all of 1-7 land: revisit `dvd_pairNormBCA_full`'s callers
   (traced from `uCANew` up through `AlphaLocusDegreeUniform.lean`'s
   `hQ1_def`/`hQ2_def`, per the original roadmap's Tier 2 item 2b) to
   confirm the six-hypothesis removal actually reaches the top-level
   `reducedClass_eq_of_isReduction'` variants, not just `CAWitness.lean`
   in isolation.

## Explicitly out of scope for this doc

- Anything already closed by Tier 1 (anchor-axis and target-axis
  `Ra1=Ra2`/`T1=T2` tangent cases at the TOP level, i.e.
  `AlphaLocusDegreeUniformTangent.lean` and
  `AlphaLocusDegreeUniformTangentTarget.lean`) — those theorems'
  OWN internal machinery doesn't touch `CAWitness.lean`'s
  `caInterpMatrix` at all; they're a different interpolation
  construction one layer up (`ROADMAP-principal-witness-tangent-
  assembly.md`'s `caTangentTargetInterpMatrix`-family, already done).
  Don't conflate "the top-level split is done" with "`CAWitness.lean`'s
  own 4-point interpolant now handles collisions" — they're unrelated
  matrices solving different sub-problems, confirmed by reading both
  files' definitions.
- Tier 3 (genuinely structurally-impossible distinctness facts, e.g.
  a point vs. its own hyperelliptic conjugate) — correctly out of
  scope per the parent roadmap, not revisited here.
