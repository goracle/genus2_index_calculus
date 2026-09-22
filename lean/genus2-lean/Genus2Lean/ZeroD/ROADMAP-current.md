# ZeroD / index-calculus model: where things actually stand

Written 2026-09-21 from the module docstrings of the 13 most recent files
(listed at the bottom) plus Claire's stated hit-rate logic. It replaces every
roadmap/README that used to live at the top of `ZeroD/`; those are now in
`oldroadmaps/` as session logs. **The `.lean` docstrings are ground truth;
this file is a map, not a spec.** Lines marked *(read)* are my reading of
the files and should be corrected if wrong.

## Correction, this pass: the `HitRate`/`hbad` branch is superseded, not open

**`IndexCalculusHitRate.lean` and everything built on it —
`HitRateSumsetReduction`'s `good`/`goodMatch`/`DirectRelation`/`hbad`
machinery (Parts 2 and 4–5) included — solves a problem the project's own
`IndexCalculusComplexity.lean` already declared unnecessary, for an
independent reason.** `IndexCalculusComplexity.lean`'s own docstring:
`matchCount`'s fiber *multiplicity* (how many quadruples land on a given
`Δ`) is the wrong quantity to bound at all, because
`IndexCalculusRelations.lean`'s `translate_of_same_diff` +
`dedup_by_rhsElt_loses_no_rhs` prove that any two solves sharing a `Δ` are
gauge-related, so a big fiber is worth exactly ONE relation regardless of
its size. The complexity claim goes through `expectedRelations` /
`matchCount_distinct_hits_ge_unconditional` (a coupon-collector /
distinct-count argument, unconditional, no Sidon) and
`IndexCalculusReachability`'s `SolverReaches` (also unconditional, "pure
double counting" per its own docstring) instead. Neither of those imports
or calls `hitRate_of_good_overlap`, `hitRate_of_goodMatch`, or
`hitRate_of_good_mass` — grepped this pass, confirmed zero live callers
outside `IndexCalculusHitRate.lean`/`HitRateSumsetReduction.lean`
themselves. (`IndexCalculusReachability` imports `IndexCalculusHitRate`
only for the bare `HitRate` type/def, not for anything `good`-related.)

So the `T+T`/Fourier gap surfaced this session (bounding `hbad`'s `T+T`
piece needs Plancherel on the finite-abelian dual, nothing else in the
project uses that Mathlib area) is **not a hole to fill** — it's a
symptom of continuing to build out a branch the project moved past. Same
shape as the already-flagged-dead gauge-shift branch (open item 5 below):
built for a target (`matchCount ≤ K` pointwise, then `good`/`hbad`
accounting) that a later, better argument made unnecessary, but nobody
went back to prune or flag it at the time.

**Confirmed this pass:** `expectedRelations_le_of_hitRate` and
`expected_successes_at_balance` — `IndexCalculusHitRate.lean`'s only
bridge-to-the-model theorems — are also uncalled anywhere outside their
own file. `IndexCalculusComplexity.lean`'s actual headline result
(`index_calculus_complexity`) is built entirely from
`expectedRelations_at_balance`/`balance_forces_fifth_power`/
`total_cost_eq_rpow`, none of which touch `HitRate`. So the whole
`IndexCalculusHitRate.lean` file — not just its `good`/`hbad` corner — is
disconnected from the live proof graph.

**Downgraded this pass:** `IndexCalculusHitRate.lean` and
`HitRateSumsetReduction.lean` Parts 2, 4, 5 (the `good`/`goodMatch`/
`DirectRelation`/`hbad` material) are superseded, kept for reference,
same status as the gauge-shift branch (item 5 below) — not further open
work. `HitRateSumsetReduction` Part 1 (negative pointwise-cap result) and
Part 3 (`overlap_le_sidon_energy`, `matchCount_le_two_card_sq`) are also
only reachable via this now-superseded branch — checked, nothing live
imports `HitRateSumsetReduction` outside `IndexCalculusReachability`'s
bare-type import chain traced above, so the whole file is downstream of
the superseded branch, not just Parts 2/4/5.

## Correction, this pass (2): `SidonRepBound T` for the real `T = s(F)` is
already proved, `sorry`-free — but stranded, same pattern as above

**`SidonDichotomyGeneral.lean` already proves `SidonRepBound (sidonSet
(principalDivisorData H hdeg) δ₀ F)` for the actual `T = s(F)`, over the
real field, unconditionally — no `sorry`, no unproved `SidonDichotomy`
needed.** The degree-2 argument (`P1+P2` and its collisions are governed
by `H.Point`'s degree-2-map-to-`ℙ¹` structure, per Riemann–Roch) is exactly
right and is what
`isOnlyEffectiveInClass_of_uniqueDegree2MapToP1_general`
(`LPairFinrankOneOrdAtFracSpec.lean`) already formalizes. Chain:
`sidonRepBound_of_sidonDichotomy_nonInvolution_general` needs only
`hchar`, `hsf`, and two checkable-by-construction side conditions on `F`
— `AvoidsInvolutionPairs F` and `NoWeierstrassPoints F` (`SidonBridge.lean`;
costs at most `2g+2=6` points out of `~p` available, per that file's own
docstring) — and sidesteps the one genuinely-open piece
(`sidonDichotomy_general`'s involution-branch `sorry`, `x₂ = ι x₁`, needing
`IsOnlyFibersInCanonicalClass` general-`k`, proved nowhere in the
codebase) entirely, by construction, rather than needing it discharged.

**But: same stranding pattern as `HitRate`/`hbad` above.** `SidonRepBound`
is called only from `Complexity.lean` (in prose, and by
`UniformFiberBoundOffDiagonal.lean`, neither in the live 13-file import
closure) — `IndexCalculusComplexity.lean`'s own correction already says
the whole Sidon/second-moment apparatus `SidonRepBound` feeds is
unnecessary for the live model (fiber multiplicity is irrelevant, see
correction (1) above). So former item 1 (`SidonRepBound T` open) is now:
proved, but for a branch (`Complexity.lean`/`SidonDichotomyGeneral.lean`
→ `HitRateSumsetReduction`'s Sidon-fed parts) that the live proof graph
doesn't currently call into. Not renumbered off the open list below by
deletion (per "don't touch completed proofs, just note and move on") —
removed as a numbered open item since there's nothing left to prove here,
kept as a note in case the live model ever needs `SidonRepBound` again
(e.g. if `HitRateSumsetReduction`'s branch gets revisited).

## The model in one paragraph

A solve at fixed `(α, α')` looks for points with `P1+P2-P3-P4 = (α-α')·a`
(eq 1). Schematically `reduce(P1+P2-α·a) = (U,V) = reduce(P3+P4-α'·a)`, so
one draws the Mumford divisor `(U,V)` from `~p²` choices, and that divisor
determines all four `P`'s (up to the swaps in each pair). Success needs the
`P`'s to land in the factor base `F`, `|F| = B`, which has probability
`~B⁴/p²` per `(α,α')` (ignoring the trivial `b-b` family). With `~B` distinct
relations needed and sparse linear algebra `~B²`, the balance is
`B ~ p^(2/5)`, total cost `p^(4/5)`.

Direct-relation rule: if `Δ = (α-α')·a` already splits with both `u`-roots in
`F` (i.e. `Δ ∈ T-T`, `T`, or `T+T`), that is accepted as the relation and
no draw is made on the reduce equation. So the matching regime only ever sees
`Δ` outside those sets, and the trivial quadruples `(x,b,b,y)` (which force
`Δ = x-y ∈ T-T`) do not occur there.

## Proved (each REPL-tested per Claire)

| File | What it gives |
|---|---|
| `ZeroD/FixedTargetBoundCanonical` | `≤ 4` fixed-target bound for the canonical `D`, with `hbridge` and `IsOnlyEffectiveInClass` discharged. Needs `hchar`, `hsf`, and non-involution pairs (`P2 ≠ ι P1`); FALSE without the last. **This pass:** the non-involution fact is now a required field (`.hne`) of `SampleTargetFromAlpha` itself (`AlphaLocusDegreeUniform.lean`) rather than a separately-threaded caller hypothesis — no `SampleTargetFromAlpha` can be built without it. Resolves open item 2 below. |
| `ZeroD/InvolutionPairsCount` | involution pairs are exactly `#H.Point` of `#H.Point²`: rejecting them costs a factor `1 - 1/#Points`. (`#Points ~ p` is Hasse–Weil, not on file.) |
| `IndexCalculusRelations` | a solve's relation has `rhs = (α-α')·a`; two solves are gauge-related iff same `rhs`; `DistinctRHS` excludes all gauge duplicates. |
| `IndexCalculusComplexity` | balance `B ~ p^(2/5)`, cost `p^(4/5)` from a named per-solve rate `hRate = B⁴/p²`. |
| `IndexCalculusHitRate` | **Superseded, this pass** — see correction (1) above. `hRate` made explicit as `HitRate F c` with sufficient conditions, but disconnected from the live proof graph: `IndexCalculusComplexity`'s actual result doesn't route through it. |
| `HitRateSumsetReduction` | **Downstream of the superseded branch, this pass** — see correction (1) above. Content kept for reference: (1) NEGATIVE: no constant cap `matchCount T Δ ≤ K` at `Δ ≠ 0`. (2) POSITIVE: `matchCount ≤ 4·overlap(T+T)` under `SidonRepBound`. (3) `overlap(Δ) ≤ 2B²` unconditionally. (4)–(5) `goodMatch`/`DirectRelation`/`hbad` 3-piece split, `T`-piece proved, `T-T`/`T+T` pieces open — moot per the correction, not pursued further. |
| `SidonDichotomyGeneral` | **Proved, `sorry`-free.** `sidonRepBound_of_sidonDichotomy_nonInvolution_general`: `SidonRepBound (sidonSet (principalDivisorData H hdeg) δ₀ F)` for the real `T = s(F)`, general `k`, from `hchar`/`hsf`/`AvoidsInvolutionPairs F`/`NoWeierstrassPoints F` only. Also carries `hitCount_ge_of_sidonDichotomy_nonInvolution_general`: `≥ B²/2` distinct relations, unconditional, real curve. **No longer purely stranded — this pass**, see `IndexCalculusComplexityRealHitCount` below. |
| `IndexCalculusComplexityRealHitCount` | Chains `SidonDichotomyGeneral`'s `hitCount_ge_of_sidonDichotomy_nonInvolution_general` (`≥ B²/2` distinct relations, real curve, unconditional) into `IndexCalculusComplexity`'s balance point `B⁵=p²`: at that balance, the real curve's existence guarantee (`B²/2`) already covers the `~B` relations the model calls for, with room to spare. Settles, for the actual curve, the "which fiber-cap instantiation" question `IndexCalculusComplexity`'s own docstring had left as an unmade modeling choice. Does NOT close the reachability gap — this is a static existence fact over the whole `B⁴`-quadruple space, not a statement about `N` solve attempts. |
| `FiniteCouponCollector` | **`PMF`-free, generic finite-combinatorics coupon-collector bound** (ChatGPT consult this pass; corrected mid-pass after a pigeonhole conflict the consult caught — rate hypothesis is `k/d ≥ 1/(C·B²)`, not the pigeonhole-incompatible `1/(C·B)`). `sum_card_hit_ge`/`avg_seenCount_ge`: exact `𝔼[X_N] ≥ M(1-(1-k/d)^N)`-style bound over a literal `Fin N → R` seed space, no `PMF`/`MeasureTheory`. `pow_one_sub_le_one_div_one_add_mul`: elementary Bernoulli-style bound, proved by induction. `avg_seenCount_ge_half_sq_of_rate`: closed-form `B²/4` conclusion at `N ≥ C·B²`. Curve-independent, generic in label type `G`/seed type `R` — wiring to `H.Point`/`matchCount` NOT attempted here (that is item 1). |
| `IndexCalculusReachabilityCouponCollector` | Connects `SolverReaches` to a coupon-collector bound directly at the `q`-level (per Claire: reuse `FiniteCouponCollector`'s Bernoulli *technique*, not its literal seed-space model — no second seed coordinate reifying the solver's internal randomness). Defines `avgSuccessProb`/`successProb` (crediting `¬goodMatch` free hits at probability `1`, sound since this can only inflate the bound). `expected_successes_at_least`/`solverReaches_coupon_collector_bound`: the `1 - 1/(1+N·avgQ)` asymptotic floor, REPL-tested. `occupancy_ge_half_of_rate`/`solverReaches_half_success_of_rate`: a clean fixed `≥ 1/2` threshold once `N` clears a rate floor `avgQ ≥ 1/(C·N)`. **Now has a genuine `SolverReaches` instance to apply to** (`SolverReachesFactorBaseCap`, below) — `avgQ`'s value at that instance is the loose `q ≡ 1` ceiling, not a tight real-solver rate; see item 1. |
| `ZeroD/MatchCountFactorBaseBridge` | Closes open item 1's sub-gap (1a): connects `matchCount`/`SolverReaches`'s abstract `G := Jacobian H D` model to a REAL `H.Point` factor base. `pointMatchCount D δ₀ F₀ Δ` is the direct `H.Point`-level analogue of `matchCount`, stated against `GaugeOrbitSolutions`'s own defining equation (`GaugeOrbitMatchCountBound.lean`) restricted to a finite factor base. `matchCount_sidonSet_le_pointMatchCount`: `matchCount (sidonSet D δ₀ F₀) Δ ≤ pointMatchCount D δ₀ F₀ Δ`, proved by exhibiting `matchCount`'s counted set as literally the `.image` of `pointMatchCount`'s counted set under coordinatewise `s`, then `Finset.card_image_le` — deliberately an INEQUALITY, not an equality, since `s` is not claimed injective on a factor base (that is what `SidonBridge.lean`'s whole `AvoidsInvolutionPairs`/`NoWeierstrassPoints`/`SidonDichotomy` apparatus exists to control, not assumed here). Right-shaped for `SolverReaches`'s own use of `matchCount` as a lower bound on reachable mass. **REPL-confirmed green.** `d`/`q` themselves now wired, see `PointMatchCountFactorBaseCap`/`SolverReachesFactorBaseCap` below. |
| `ZeroD/GaugeOrbitMatchCountBound` | earlier "gauge orbit = swapImages" claim was false; honest replacement: the `Δ`-fiber is a union over pair-sum classes of `≤4` fibers. |
| `ZeroD/AlphaUnionGaugeCollapse` | any second sample with the same `α-α'` is gauge-accounted for by the reference `≤4` fiber. |
| `PointMatchCountFactorBaseCap` | **(top-level `Genus2Lean/`, not `ZeroD/`.)** Closes item 1 sub-gap (1b)'s `d`-side: `pointMatchCount_le_four_mul_card_sq` gives `pointMatchCount D δ₀ F₀ Δ ≤ 4 * F₀.card ^ 2`, unconditional in `Δ`, canonical `D`, `F₀` satisfying `AvoidsInvolutionPairs`/`NoWeierstrassPoints`. NOT via `decoupledSystem_degree_uniform` (stays conditional on `GenericPeelChainHyp`) — a direct pigeonhole argument instead: group `pointMatchCount`'s quadruples by first pair `(P1,P2)` (`Finset.card_eq_sum_card_fiberwise`), bound each `≤4`-element fiber via `pointMatchCount_fiber_le_four`, itself chaining `fixedTargetSolutions_ncard_le_four` (`MatchingSolutionSwapSymmetry.lean`) through `isOnlyEffectiveInClass_of_uniqueDegree2MapToP1_general` (`sorry`-free). **REPL-confirmed green, no `sorry`.** |
| `SolverReachesFactorBaseCap` | **(top-level `Genus2Lean/`.)** Chains the above with `ZeroD/MatchCountFactorBaseBridge`'s (1a) bridge into a concrete `SolverReaches (sidonSet D δ₀ F₀) (4 * F₀.card ^ 2) (fun _ => 1)` — the first genuine (non-abstract) instance of `SolverReaches` anywhere on file, for the canonical `D`. `q ≡ 1` is the loosest sound witness, not a placeholder: see item 1's updated text on why a tighter `q` is a modeling boundary, not open proof work. **REPL-confirmed green, no `sorry`.** |

## Open, in order of importance

1. **`IndexCalculusReachability`'s `SolverReaches` takes `|Sol Δ| ≤ d`, and
   `avgQ`/`d` needed wiring to `H.Point`/`Jacobian H D`.**
   *(Renamed from "not yet wired" — this pass closes the provable part.)*
   Two sub-gaps:
   * (1a) **`matchCount`-side, bridged, REPL-confirmed green.**
     See `ZeroD/MatchCountFactorBaseBridge.lean` in the `Proved` table:
     `sidonSet D δ₀ F₀` connects to a genuine `H.Point`-level quadruple
     count (`pointMatchCount`), unconditional inequality `matchCount
     (sidonSet D δ₀ F₀) Δ ≤ pointMatchCount D δ₀ F₀ Δ`.
   * (1b) **`d`-side closed this pass, `q`-side is a modeling boundary,
     not a formalizable gap.** `PointMatchCountFactorBaseCap.lean` (new)
     gives an unconditional `pointMatchCount D δ₀ F₀ Δ ≤ 4 * F₀.card ^ 2`
     for the canonical `D` — NOT via `decoupledSystem_degree_uniform`
     (that route stays conditional on `GenericPeelChainHyp`/an unpinned
     placeholder exponent `n`; this is a direct pigeonhole argument on
     `pointMatchCount`'s own fiber structure instead, sidestepping that
     whole conditional chain). `SolverReachesFactorBaseCap.lean` (new)
     chains (1a) and this `d`-bound into a concrete
     `SolverReaches (sidonSet D δ₀ F₀) (4 * F₀.card ^ 2) (fun _ => 1)`.
     **The `q ≡ 1` witness is the loosest sound choice, deliberately, not
     a placeholder awaiting improvement**: re-examined this pass whether a
     tighter `q` is provable, and it is not — `IndexCalculusReachability.lean`'s
     own docstring is explicit that `q` encodes a claim about the real
     solver's sampling behavior ("not adversarially biased away from
     `F⁴`"), which this codebase does not implement or model
     computationally. `SolverReaches` is, and was always meant to be, a
     HYPOTHESIS about an external algorithm, not a theorem to prove from
     combinatorics alone. Tightening `q` further would require either an
     actual solver implementation (out of scope) or bounding
     `∑_{goodMatch F} matchCount F Δ` restricted to `goodMatch`, which is
     the same superseded `hbad`-adjacent question flagged in the
     corrections at the top of this file — not new open work.
2. **Reachability/sampling gap: turning "relations exist" into "a solver
   finds them."** **Resolved at the modeling-threshold level**
   (see "Proved" table): `IndexCalculusComplexityRealHitCount` established
   the `~B²` existence guarantee; `FiniteCouponCollector` and
   `IndexCalculusReachabilityCouponCollector` turn that into a `PMF`-free,
   finite-combinatorics coupon-collector bound, landing on a clean `≥ 1/2`
   success-floor threshold (`solverReaches_half_success_of_rate`) at a
   sufficient attempt budget `N`. **This pass**: item 1's `d`-side closure
   means `avgQ_mem_Icc`/`solverReaches_coupon_collector_bound` now have a
   genuine (if loose, `q ≡ 1`) `SolverReaches` instance to apply to —
   feeding `SolverReachesFactorBaseCap`'s theorem through those gives a
   concrete, if not tight, `avgQ = 1` instantiation for the real curve.
   The probability machinery itself was already settled (no
   `PMF`/`MeasureTheory` needed); what would still improve this is a
   tighter `avgQ` from a less trivial `q` — same modeling-boundary
   situation as item 1 (1b), not new open work.

*(Former item 2, "sampler must reject `P2 = ι P1`": resolved —
`SampleTargetFromAlpha` now carries the non-involution fact as a required
field, see the `Proved` table above.)*

*(Former gauge-shift-branch item: dropped from this list per Claire's
instruction — worth noting, not worth archiving. No longer tracked here.)*

*(Former item 1, `SidonRepBound T` for the real `T = s(F)`: resolved, see
correction (2) above — proved, not open, just stranded off the live path.)*

## Where the live proof graph now actually terminates

Every gap in the `matchCount`/`pointMatchCount`/`SolverReaches` chain that
was provable FROM COMBINATORICS ALONE is now closed:
`pointMatchCount ≤ 4B²` → bridged to `matchCount` → wired into a concrete
`SolverReaches` instance → feeds the coupon-collector success-floor bound.
What's left standing between here and a full end-to-end complexity theorem
for the real curve is not a missing lemma but two independent, genuinely
external inputs: (i) a real per-attempt success rate `q` for the actual
12-equation solver (a claim about an algorithm this codebase doesn't
implement), and (ii) the 8 live `sorry`s in the Riemann–Roch/
`IsOnlyFibersInCanonicalClass` layer (deep algebraic-geometry content,
already correctly triaged in this file's own "hard sorry → ChatGPT
prompt" convention — see the live `sorry` inventory below). Neither is
"the next small step"; both are the actual remaining mathematical or
modeling content the project set out to formalize.


## Deprecated branch (kept, not extended)

The degree-uniform 0-dimensional-system route (`decoupledSystem_degree_uniform`,
`GenericPeelChainHyp`, peel-chain finrank assembly, `CrossNondegenerate`
degree-bound files). The one live `sorry` under `ZeroD/` is here:
`GenListFinrankAssembly.lean : genList_finrank_le`. Only 29 of 154 `ZeroD/`
modules are in the import closure of the 13 files below.

## Live `sorry` inventory (comment-stripped scan, 2026-09-21): 8

`RiemannRochGenus2` (`finrank_L_pair`, `finrank_L_canonical`),
`RiemannRochCrux` (`uniqueDegree2MapToP1`,
`isOnlyEffectiveInClass_of_uniqueDegree2MapToP1`), `PrincipalSubgroupCollapse`
(`isOnlyEffectiveInClass_of_uniqueDegree2MapToP1'`), `SidonDichotomyGeneral`
(`sidonDichotomy_general`), `LCanonicalElementary`
(`isOnlyFibersInCanonicalClass_of_elementary`), `ZeroD/GenListFinrankAssembly`
(`genList_finrank_le`). The scan script is in `oldroadmaps/ZeroD-STATUS.md`.
Importing a file with a `sorry` is not depending on it: to check the headline
result, run `#print axioms` on `fixedTargetSolutions_ncard_le_four_canonical`
and look for `sorryAx`. (`hitRate_of_good_overlap` dropped from this check —
superseded, see correction above; not a headline result.) Same check is
worth running on `index_calculus_complexity_real_hitCount`
(`IndexCalculusComplexityRealHitCount.lean`, new this pass) — it imports
`SidonDichotomyGeneral`, which carries `sidonDichotomy_general`'s live
`sorry` in an unrelated declaration; the theorems it actually calls
(`hitCount_ge_of_sidonDichotomy_nonInvolution_general` and its dependents)
were already `sorry`-free per the inventory above, so this should come back
clean, but hasn't been explicitly `#print axioms`-checked yet.

## Files this map is built from (oldest to newest)

`ZeroD/AlphaUnionGaugeCollapse`, `ZeroD/GaugeOrbitMatchCountBound`,
`IndexCalculusRelations`, `IndexCalculusComplexity`, `CantorCompositionStep`,
`AlphaReducedClassShift`, `CantorMulMumford`, `GaugeShiftAssembly`,
`IndexCalculusHitRate`, `IndexCalculusReachability`,
`ZeroD/FixedTargetBoundCanonical`, `ZeroD/InvolutionPairsCount`,
`HitRateSumsetReduction`. Plus, read a previous pass while chasing item 1
(resolved, correction (2) above): `SidonDichotomyGeneral`,
`SidonBridge`, `FFKSidon`, `DivisorClassGroup`.

**Updated 2026-09-22**: `ZeroD/AlphaLocusDegreeUniform`
(`SampleTargetFromAlpha`'s new `.hne` field),
`ZeroD/SampleTargetFromAlphaWitness` (threading `.hne` through the one real
constructor) — both REPL-confirmed green. Plus the new file
`IndexCalculusComplexityRealHitCount` (chaining `SidonDichotomyGeneral`'s
hit-count bound into `IndexCalculusComplexity`'s balance point),
REPL-confirmed green.

**Updated 2026-09-22 (2)**: `FiniteCouponCollector` (new, generic
`PMF`-free coupon-collector bound) and `IndexCalculusReachabilityCouponCollector`
(new, connects `SolverReaches` to that bound at the `q`-level) — both
REPL-confirmed green except `occupancy_ge_half_of_rate`/
`solverReaches_half_success_of_rate` in the latter, drafted this pass and
not yet REPL-checked. Read together with `ROADMAP-current.md`'s own open
item 2 (now folded into item 1, see above): the probability/expectation
machinery is done; what remains is wiring `avgQ`/`d` to `H.Point`/
`Jacobian H D`.

**Updated 2026-09-22 (3)**: `ZeroD/MatchCountFactorBaseBridge` (closes open
item 1's sub-gap (1a) — see the `Proved` table). **REPL-confirmed green**,
one fix by hand (a trailing `rfl` in `sum_pointMatchCount_eq_card_pow_four`
was unnecessary after the preceding `rw` already closed the goal — deleted).
No new `sorry` introduced (the live-`sorry` inventory below is unaffected).
Sub-gap (1b) — wiring `d`/`q` themselves to
`decoupledSystem_degree_uniform`/an actual solver model — remains open, per
item 1's updated text above.

**Updated 2026-09-22 (4)**: `PointMatchCountFactorBaseCap.lean` (new,
top-level `Genus2Lean/`, not under `ZeroD/`) and `SolverReachesFactorBaseCap.lean`
(new, same location) — **both REPL-confirmed green**, no `sorry` in either.
This closes item 1's sub-gap (1b) on the `d`-side, and chains it together
with (1a)'s bridge into a genuine, concrete `SolverReaches` instance:

* `PointMatchCountFactorBaseCap.pointMatchCount_le_four_mul_card_sq` —
  `pointMatchCount D δ₀ F₀ Δ ≤ 4 * F₀.card ^ 2`, unconditional in `Δ`, for
  `D := principalDivisorData H hdeg`, `F₀` satisfying
  `AvoidsInvolutionPairs`/`NoWeierstrassPoints`. Proved by grouping
  `pointMatchCount`'s counted quadruples by their first pair `(P1,P2)`
  (`Finset.card_eq_sum_card_fiberwise`) and bounding each fiber by 4, via
  a new `pointMatchCount_fiber_le_four` that chains
  `fixedTargetSolutions_ncard_le_four` (`MatchingSolutionSwapSymmetry.lean`)
  through `isOnlyEffectiveInClass_of_uniqueDegree2MapToP1_general`
  (`LPairFinrankOneOrdAtFracSpec.lean`, itself `sorry`-free per that file's
  own docstring) — same non-involution-witness pattern
  `FixedTargetBoundCanonical.lean` already uses, just re-derived at the
  `H.Point`-pair level instead of the `Jacobian` level. Note: `Set.toFinite`
  does NOT work here (no `Finite H.Point` instance project-wide, see
  `MatchingSolutionSwapSymmetry.lean`'s own docstring on `swapImages_finite`)
  — finiteness is obtained by embedding into `swapImages P1 P2 P3 P4`
  instead, mirroring `fixedTargetSolutions_ncard_le_four`'s own internal
  proof.
* `SolverReachesFactorBaseCap.solverReaches_sidonSet_of_avoidsInvolutionPairs`
  — chains the above with `MatchCountFactorBaseBridge`'s
  `matchCount_sidonSet_le_pointMatchCount` into
  `SolverReaches (sidonSet D δ₀ F₀) (4 * F₀.card ^ 2) (fun _ => 1)`, a
  genuine (if loose) instance of the `SolverReaches` hypothesis
  `IndexCalculusReachability.lean` otherwise leaves entirely abstract. Uses
  the trivial witness `q ≡ 1` — sound since the chained bound holds for
  every `Δ` unconditionally, not just `goodMatch`-restricted ones, so no
  case-split on `goodMatch` is needed.

**What this does NOT close, and why it's not a formalizable gap**: `q ≡ 1`
is a ceiling, not a model of the real 12-equation solver's success rate.
Re-examined this pass whether a less trivial `q` is available to prove: it
is not — `IndexCalculusReachability.lean`'s own docstring is explicit that
`q` encodes "(ii) the returned element is not adversarially biased away
from `F⁴` (a uniform-pick heuristic)", a claim about an external
algorithm's sampling behavior that this codebase does not implement or
model computationally. There is no missing lemma here; `q` is deliberately
left abstract by design, the same way `SolverReaches` itself is a
hypothesis about the solver, not a theorem. `avgQ`/`d` (open item 1's
framing) are therefore now: `d` fully wired (this update), `q` wired only
at its loosest possible sound value — further tightening `q` would require
either a concrete algorithm specification (out of scope for this proof
graph) or bounding `∑_{goodMatch F} matchCount F Δ` itself, which per
`IndexCalculusReachability.lean`'s own docstring is "exactly the still-open
`hbad`-adjacent question" — i.e. the same superseded-branch question
already flagged in the corrections at the top of this file, not a new gap.

**Open item 1 status after this update**: sub-gaps (1a) and (1b)'s
provable content are both closed. What remains under item 1's heading is
not a gap in the proof graph but a modeling boundary — the same kind of
line `SolverReaches` itself was always drawn at.
