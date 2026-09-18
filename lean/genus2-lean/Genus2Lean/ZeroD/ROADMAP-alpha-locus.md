# Roadmap: proving eq 1 is 0-dimensional *uniformly in `(alpha,alpha')`* —
# why this is the real target, and how it closes the 8th-moment gap

**SUPERSEDED (2026-09-18) — the entire `matchCount T Δ ≤ K` target this
roadmap chases is stale. Read this block first; it overrides every
"actual gap"/"Next steps" section below that talks about bounding
`matchCount`, `Δ`-fibers, or wiring into
`UniformFiberBoundOffDiagonal.lean`.**

`IndexCalculusRelations.lean` (new, sorry-free) reframes what a
"relation" the attack actually collects even is, and the reframing
dissolves this roadmap's target rather than closing it:

- **CORRECTED (2026-09-18, Claire) — a relation's right-hand side is
  `(alpha - alpha')·a`, NOT `alpha·a`.** A matching solve produces
  `P1+P2-P3-P4 = (alpha-alpha')·a` (eq 1), so its relation has terms
  `[P1,P2,-P3,-P4]` and `rhs = alpha - alpha'`
  (`MatchingSolve.toRelation`). An earlier version of this block and of
  `IndexCalculusRelations.lean` keyed everything on `alpha` alone; that was
  wrong. `DistinctRHS` is keyed on the group element `rhs • a`, not on
  `alpha` and not even on the integer `alpha - alpha'` (integers differing
  by a multiple of `ord a` are the same element of `G`).
- **Both kinds of gauge redundancy are "same right-hand side".**
  (Write `A = P1+P2`, `B = P3+P4`.)
  1. *Common shift* `(alpha,alpha') ↦ (alpha+c,alpha'+c)`: same points (the
     shift lands on the auxiliary target `D`), same terms, same `rhs`
     (`MatchingSolve.shift_toRelation_terms`, `shift_toRelation_rhs`). It is
     the identical relation re-derived, but `alpha` differs
     (`shift_alpha_ne`) — which is exactly why `alpha`-keying accepted the
     duplicate.
  2. *Translation* (`matching_solutions_translate_by_delta`): two solves
     with the same `rhs` have `A = A'+Δ`, `B = B'+Δ`. Over the columns
     `(A,B,A',B',Δ)`, `row1 - row2 = (A-B)-(A'-B') = (1,-1,-1,1,0) =
     t₁ - t₂` with `t₁ = A-A'-Δ`, `t₂ = B-B'-Δ` the translation
     relations (`translation_rows_differ_by_translation_relations`;
     equivalently substitute `A'=A-Δ`, `B'=B-Δ` into row 2: the `Δ`
     coefficient is `-1+1 = 0`). The right-hand sides agree too, so the
     difference is a pure `sum = 0` row with no `a`-component
     (`relation_sub_zero_of_same_rhsElt`). At the level of the POINT factor
     base the two rows are different vectors; they differ by translation
     relations only after the pair-sum classes and `Δ` are adjoined as
     columns.
  These are exhaustive: `gaugeRelated_iff_same_rhsElt` — two solves are
  translation-related iff their right-hand-side elements are equal — so
  `DistinctRHS` (`not_gaugeRelated_of_distinctRHS`) excludes every gauge
  duplicate at once, and there is no third kind. That such rows hurt the
  solver's kernel is a claim about the linear algebra the attack runs; it is
  not formalized, only its algebraic content (difference row has rhs `0`).
- Consequently: `matchCount T Δ ≤ 4` (this roadmap's whole target),
  `UniformFiberBoundOffDiagonal.lean`'s
  `offDiagonalBound_of_uniform_matchCount_bound_four`, and the Sidon/
  second-moment apparatus in `Complexity.lean`/advisory-7 §7 this was all
  built to feed are OBSOLETE — `IndexCalculusComplexity.lean` (new,
  sorry-free) derives the attack's complexity (`B ~ p^(2/5)`, total cost
  `p^(4/5)`) directly from a per-solve success-rate hypothesis (`hRate`,
  `B⁴/p²`) and `DistinctRHS`-style bookkeeping, with NO dependence on any
  `matchCount`/off-diagonal/Sidon bound. Nothing in that file imports or
  needs this roadmap's target.

  **CAVEAT on the "OBSOLETE" verdict (2026-09-18) — not re-verified under
  the corrected model.** That verdict was argued from the `alpha`-keyed
  picture. Under the corrected one, two solves share a right-hand-side
  element iff they are translation-related, i.e. iff they lie in the same
  `Δ`-fiber; a relation set with distinct RHS can use at most one solve per
  `Δ`, so the yield lost to discarding is governed by how many quadruples
  share a `Δ` — the `matchCount` / off-diagonal quantity. Under a
  random-RHS heuristic that loss is negligible at `B ~ p^(2/5)` (about
  `B²/p²` colliding pairs among `~B` relations), so nothing here breaks
  `IndexCalculusComplexity.lean`; but a worst-case guarantee is what the
  `OffDiagonalBound` machinery was for, and `hRate` silently assumes the
  loss is small. Treat "matchCount is irrelevant" as heuristic, not proved.

**What is still real and worth keeping** (do not delete): `swapImages`/
`fixedTargetSolutions_ncard_le_four`
(`MatchingSolutionSwapSymmetry.lean`) — the ≤4-solutions-per-fixed-
`(alpha,alpha')` fact — is unaffected and still true; it was never
wrong, just aimed at a target (`matchCount`) that turned out not to be
the thing the attack needs. `GaugeShiftAssembly.lean`
(`gaugeShift_fixedTargetSolutions_ncard_le_four`) is likewise correct as
stated but was solving the wrong problem — built in service of exactly
this now-superseded target — and should not be extended further for
that purpose. `AlphaReducedClassShift.lean`'s transport lemmas are pure
algebra, harmless, and may still be useful elsewhere, but are no longer
"Next steps" for THIS roadmap's stated goal, because that goal is gone.

**What to actually work on instead**: `IndexCalculusComplexity.lean`'s
`hRate` (the per-solve success probability `B⁴/p²`) is the real
remaining assumed hypothesis feeding the complexity derivation — see
that file's own "What is assumed, and what is not." If further Lean
work on this thread is wanted, that is the honest next target, not
anything below this block.

---

## Current status (condensed this pass — see "History" at the end for how
## we got here; nothing below is new content, this is a rewrite for
## clarity, not a new pass of investigation)

**The open problem.** Advisory-6/7's §7 second-moment split needs
`OffDiagonalBound` (`Complexity.lean`) — a bound on
`∑_{Δ≠0} matchCount T Δ ²` for the factor-base image `T := s(F) ⊆ G :=
Jacobian H D`. The cleanest way to get it: a uniform pointwise cap
`matchCount T Δ ≤ K` for every `Δ ≠ 0`, `K` independent of `p`. If that
exists, `UniformFiberBoundOffDiagonal.lean`'s
`offDiagonalBound_of_uniform_matchCount_bound_four` (proved, sorry-free)
closes `OffDiagonalBound` immediately at `K=4`, and the whole
Sidon/Fourier apparatus in advisory-7 §7 becomes unnecessary.

**What eq 1 is.** For fixed `alpha,alpha' : ℤ`,

    [P1]+[P2] - alpha·a = [P3]+[P4] - alpha'·a      (eq 1)

i.e. `[P1]+[P2]-[P3]-[P4] = (alpha-alpha')·a`. The equation only ever sees
the difference `Δ := alpha-alpha'`, never `alpha,alpha'` individually
(`eq1_gauge_invariant`, `MatchingEquationTranslation.lean`, proved). So
`matchCount T Δ`, for `Δ := (alpha-alpha')•a`, is *literally* the count of
`H.Point`-quadruples `(P1,P2,P3,P4) ∈ F⁴` solving eq 1 — this is
`deg(alpha,alpha')` in advisory-6/7's own notation, no reformulation
needed. **The question this roadmap is actually about is just: is
`matchCount T Δ` bounded by a `p`-independent constant, for (nearly) every
`Δ`?**

**What's proved, unconditionally, no `sorry`:**

- `fixedTargetSolutions_ncard_le_four` (`MatchingSolutionSwapSymmetry.lean`):
  for **fixed, separately-pinned** classes `A := [P1]+[P2]`,
  `B := [P3]+[P4] : Jacobian H D`, the set `FixedTargetSolutions δ₀ A B` of
  point-quadruples realizing exactly that `(A,B)` pair has at most 4
  elements — via `pairFiber_ncard_le_two` (≤2 ordered representations per
  class, given `IsOnlyEffectiveInClass` for that pair), applied once to
  `A` and once to `B`.
- `matching_solutions_translate_by_delta` /
  `matching_solutions_translate_by_delta_gauge_orbit`
  (`MatchingEquationTranslation.lean`): any two **class pairs** `(A,B)`,
  `(A',B')` sharing the same difference `A-B = A'-B' = Δ` are related by a
  single `Δ' := A-A'` with `A = A'+Δ'`, `B = B'+Δ'` — pure `AddCommGroup`
  algebra, no hypothesis beyond the two equations.
- `AlphaUnionGaugeCollapse.lean`'s `sameDifference_gauge_orbit` /
  `fixedTargetSolutions_ncard_le_four_of_sameDifference`: the same
  class-level translation fact, restated over `SampleTargetFromAlpha`.
  **Its actual content, stripped of framing: any two class pairs sharing a
  difference are translates of each other, and each individual
  `(A,B)`-fiber is ≤4 (by the theorem above, applied directly to that
  pair — not derived from the reference fiber).** It does NOT show the two
  fibers coincide, only that they're equinumerous via a *class-level*
  translation.

**CONFIRMED (this pass, Claire): for one fixed `(alpha,alpha')`, the
solution set really is `≤4`, two independent ways — this part is
settled and should not be re-litigated.** Two genuinely separate
arguments land on the same fixed-`(alpha,alpha')` object and agree:

  1. **Counting route** (`fixedTargetSolutions_ncard_le_four`,
     `MatchingSolutionSwapSymmetry.lean`): for the classes `A,B` that
     ONE specific `(alpha,alpha')` pins (`A := alpha·aClass`,
     `B := alpha'·aClass`, in this file's terms — a single, fixed target,
     not ranging over anything), the ≤2-per-class swap-counting argument
     gives ≤4 directly and unconditionally (module the standing
     `hbridge`/`IsOnlyEffectiveInClass` hypotheses it always carried).
  2. **Regular-sequence route** (`decoupledSystem_zeroDimensional`,
     `AlphaLocusDegreeUniform.lean`, via `regularSeq_of_peel_chain`): the
     12-variable system (`Idx`'s 8 point-coordinate variables
     `wa1,wa2,wb1,wb2,a1,a2,b1,b2` for `P1,P2,P3,P4`'s coordinates, plus
     `U0,U1,V0,V1` for the target Mumford coefficients) is built from
     `sa sb : SampleTarget p` — **numeric constants, with no `alpha` as a
     variable or parameter of the system itself**: a specific `alpha`
     determines what the constants `(sa.u0,...,sa.v1)` numerically ARE,
     *before* the 12-equation system is ever written down, so each
     `alpha` gives a wholly separate system. For that one system, the
     generators form a regular sequence (`decoupledSystem_isRegularSequence`),
     giving `Module.Finite` — finiteness, not by itself a numeric bound
     (that would need `GenericPeelChainHyp.hfinrank_le`, still an assumed
     hypothesis, see below) — but corroborates route 1's finiteness
     independently.

**Both routes are PER-`(alpha,alpha')`.** Neither one, by itself or
together, says anything about a *different* `(alpha'',alpha''')` pair
sharing the same difference `Δ`. That's still open — see below.

**The actual gap — why `matchCount T Δ ≤ 4` is NOT yet established, even
though each fixed-`(alpha,alpha')` fiber is.**
`matchCount T Δ` is the size of the WHOLE `Δ`-fiber:
`{(P1,P2,P3,P4) ∈ F⁴ : [P1]+[P2]-[P3]-[P4] = Δ}`. This fiber decomposes
as a disjoint union, over every class `A` that some `F`-pair realizes, of
`FixedTargetSolutions(A, A-Δ)` — equivalently, over every `(alpha,alpha')`
pair with `alpha-alpha' = Δ/a` (mod whatever's needed to make that
division sensible), of that pair's own ≤4-bounded, separately-0-dimensional
solution set (both senses just confirmed above). The translation facts
show different pieces are all the *same size* and related by class-level
shifts — but a class-level equality `A = A'+Δ'` is a fact about
`Jacobian H D` elements, not a map on `H.Point`-quadruples: it does NOT
identify the point-quadruples in one fiber with those in another, and
does not bound how many *distinct* `(alpha,alpha')` pairs (equivalently,
distinct classes `A`) a finite factor base `F` realizes for a given `Δ`.
Two solutions from two different `(alpha,alpha')` pairs sharing the same
`Δ` are two genuinely different elements of `matchCount`'s fiber; nothing
proved so far rules this out. The only bound on the *number of realized
classes* currently available is the trivial one, `|F|² = B²` (distinct
ordered pairs from `F`), giving `matchCount T Δ ≤ 4·B²` at best — matching
`matchCount_le_two_card_sq` (`MatchCountAutocorr.lean`)'s existing,
weaker, already-proved bound, not the `O(1)` bound this roadmap wants.

**CORRECTION (2026-09-18) — the "RESOLVED" block below does NOT reach the
whole `Δ`-fiber; `GaugeOrbitMatchCountBound.lean`'s old main theorem was
false, not merely unproved.** Step 4 below shows the same four points persist
in each `(alpha+c,alpha'+c)` 0D system *with the transported target*
`D - Delta(c)`. Transported targets leave the pair-sums `(A,B)` UNCHANGED
(`Reduce(P1+P2-(alpha+c)a) = D - Delta(c)` is the same class equation as at
`c=0`), so every one of those systems is the single fiber
`FixedTargetSolutions A B` (≤4, already known). A `Δ`-fiber solution whose own
pair-sums are `(A',A'-Δ)` with `A' ≠ A` lies in none of them; e.g. any
quadruple with pair-sums `(A+a, B+a)` has the same difference and is not a
swap of the reference unless `a = 0`. Formally: `GaugeOrbitSolutions`'s `c` is
vacuous (`(alpha+c)-(alpha'+c) = alpha-alpha'`), so it is the difference-only
set, which `MatchingSolutionSwapSymmetry.lean` already records as unbounded.
What IS proved (see the new file): the `Δ`-fiber is the union over pair-sum
classes of fixed-target fibers (`gaugeOrbit_eq_iUnion_fixedTarget`), and the
gauge orbit intersected with the reference's own pair-sum fiber is exactly
`swapImages` (`gaugeOrbit_inter_fixedTarget_eq_swapImages`). So the "actual
gap" paragraph above stands: bounding the number of realized classes `A'`
is still open, and `matchCount T Δ ≤ 4` is NOT closed by this argument.

**RESOLVED (this pass, Claire — via the gauge-shift-on-`D`-not-`P`
argument; verified step by step, not just asserted): `matchCount T Δ ≤ 4`
after all, for any `Δ` realized by some non-degenerate base quadruple.**

The argument, precisely (record this so it isn't re-derived or
re-doubted from scratch):

1. Write the 0D system as `Reduce(P1+P2 - alpha·a) = D = Reduce(P3+P4 -
   alpha'·a)`, `D = (U,V)` the shared reduced-divisor target.
2. Shift `alpha ↦ alpha+c`, `alpha' ↦ alpha'+c` — same `c` both sides, so
   `alpha-alpha'` (hence `Δ`) is unchanged, staying in the same gauge
   orbit. **Key move: keep `P1,P2,P3,P4` fixed and let the shift land on
   `D` instead.**

   **CORRECTED (this pass) — get the order of operations right: shift
   FIRST, then call `Reduce`/invoke `isReduction` fresh on the
   already-shifted class. Do NOT try to derive the shifted target from
   the ORIGINAL `Reduce` output via an equivariance law on `Reduce`
   itself.** An earlier draft of this step wrote
   `Reduce((P1+P2-alpha·a)-c·a) = Reduce(P1+P2-alpha·a) - Delta(c)`, i.e.
   reduce once at `alpha`, then try to move the *answer* by some
   `Delta(c)` depending on how `Reduce` interacts with a shift — that
   framing needs a real equivariance theorem about `Reduce` as a
   function, which doesn't exist and can't even be checked yet (`Reduce`
   isn't assembled as a callable function anywhere in this project — see
   `AlphaReduce.lean`'s own "not yet built" note). That was the wrong
   order and the real source of the "flagged as needing confirmation"
   caveat below — not a genuine gap in the *math*.

   The right order needs no equivariance law at all, because
   `SampleTargetFromAlpha.reducedClass` is a **plain algebraic
   definition** in `alpha`, `aClass`, `P1`, `P2` (see
   `AlphaLocusDegreeUniform.lean`) — NOT something computed by calling
   `Reduce`. So: first form `reducedClass_c := (alpha+c)•aClass -
   toJacobian D (single P1+single P2-2•single δ₀)`, which by pure
   `AddCommGroup`/`zsmul` algebra equals `reducedClass + c•aClass` (no
   `Reduce` involved at all in this step — provable outright, today).
   THEN separately instantiate a fresh `SampleTargetFromAlpha` at
   `alpha+c` whose `reducedClass` field is (by construction)
   `reducedClass_c`, and assume `isReduction` for THAT instance the same
   way every other instance in this project already assumes it (it's a
   standing per-instance hypothesis, not something derived from a single
   global `Reduce` equivariance fact). Do this identically on the other
   side (`alpha'+c`), same `c`. Given both fresh `isReduction`
   assumptions, the same four points solve the `(alpha+c,alpha'+c)`
   system too — no existence question, no "does some other pair realize
   this class," it's literally the same quadruple, now paired with a
   freshly-asserted (not derived) reduced target.

   **Consequence for what's actually provable right now:** the transport
   step itself (`reducedClass_c = reducedClass + c•aClass`) is pure
   algebra and can be proved today, `sorry`-free, independent of
   `Reduce`. But turning that into "the same 4 points solve every
   `(alpha+c,alpha'+c)` system, for every `c`" still requires a
   fresh `isReduction` witness per `c` — currently an assumed `Prop`
   field with no constructed witness anywhere in the project (see
   `SampleTargetFromAlpha`'s docstring). So the assembled theorem (Next
   steps item 1) will honestly still need to quantify over "for every
   `c` such that a `SampleTargetFromAlpha` at `alpha+c` with this shifted
   `reducedClass` and `isReduction` exists" — not a hypothesis-free
   closure. This is a real, provable, useful theorem (and removes the
   need for any equivariance claim about `Reduce`), but it is not the
   unconditional "`matchCount T Δ ≤ 4`, full stop" line 132's heading
   suggests until `Reduce` itself is assembled as a callable, and
   `isReduction` is upgraded from an assumed field to a proved one (see
   `AlphaReduce.lean`, "not yet built").
3. This applies individually to all 4 elements of
   `swapImages(P1,P2,P3,P4)` (`MatchingSolutionSwapSymmetry.lean`), not
   just the base quadruple — swapping `P1,P2` (or `P3,P4`) doesn't change
   the pair-sum `P1+P2`, so step 2's equation is unaffected and the same
   shift argument applies to each swap independently.
4. So: start from an `(alpha,alpha')` pair whose 0D solution set achieves
   the max (all 4 `swapImages` elements distinct — i.e. `P1≠P2`, `P3≠P4`,
   `{P1,P2}≠{P3,P4}`). By 2-3, all 4 persist, as the SAME 4 elements,
   inside every `(alpha+c,alpha'+c)`'s own 0D set. Since every such set
   has size ≤4 (`fixedTargetSolutions_ncard_le_four`, already proved) and
   already contains these same 4 distinct elements, there is no room left
   for a genuinely different solution at any `c` — the whole gauge orbit
   (hence the whole `Δ`-fiber, i.e. `matchCount T Δ`) is exactly these 4,
   no more. Degenerate starting quadruples (fewer than 4 distinct swaps)
   are still fine: swaps ⊆ solutions ≤ 4 regardless, the "no room left"
   step just isn't needed to state the bound (only to show it's tight).

**CORRECTED A THIRD TIME (this pass) — the earlier "not yet attempted"
claim was itself stale; real work exists, but the precise theorem the
argument needs is still open, now under its actual name.** Checked
`Reduce/GeneralSharedRoot.lean` directly: `ReduceGeneral_isMumfordTarget4`
IS proved — `ReduceGeneral`'s output is a genuine, valid Mumford pair
(satisfies `IsMumfordTarget4`, the polynomial congruence `v²≡f mod u`),
given a list of genericity hypotheses. That's real, and is NOT what the
old `AlphaReduce.lean` docstring's "not yet attempted" referred to —
that docstring predates this file and is stale.

**RESOLVED, CONFIRMED (this pass) — `reducedClass_eq_of_isReduction'` IS
proved, no `sorry`.** Checked directly: it lives in
`ReducedClassBundles.lean` (not `AlphaLocusDegreeUniform.lean`, which
only carries a stale forward-reference — that's what misled the previous
note in this roadmap into calling it open twice; `grep sorry
ReducedClassBundles.lean` returns zero hits, and the proof body is real,
not a stub). Its conclusion — `sa.reducedClass + d.as_q = toJacobian D
(...)` — is genuinely the divisor-class-level statement the gauge-shift
argument needs, discharged from `base : ReductionData sa`/
`d : SplitAssemblyData sa` bundles plus `hr : isReduction' ...` and the
usual `hdeg`/`hD` bridge hypotheses (all pre-existing, standing
hypotheses this project always carries, not new gaps). Siblings
(`_tangent`, `_cross1`–`_cross4`, `_tangent_target`) cover the other
geometric cases and are dispatched via `ReducedClassDispatch.lean`.

**So: the gauge-shift/transport argument — shift `alpha` FIRST (pure
algebra on `reducedClass`, no `Reduce` needed for this part), THEN
invoke `Reduce`'s correctness/`isReduction` fresh at each `c` (a new
standing per-instance hypothesis each time, same as every other use of
`isReduction` in this project) — has every piece it needs to be written
as a real, `sorry`-free theorem, for real, checked against the actual
files rather than stale docstrings or forward-references. What that
theorem concludes is NOT an unconditional `matchCount T Δ ≤ 4` for the
whole gauge orbit — see the "Consequence for what's actually provable
right now" note under step 2 above — it's the same bound conditional on
an `isReduction` witness existing at each `c` in the orbit, which is
real, useful progress but is honestly still "modulo standing hypotheses
this project already carries" in a stronger sense than `hbridge`/
`IsOnlyEffectiveInClass` (those are per-quadruple; this is per-`c`, i.e.
per-element-of-a-`p`-size orbit). Formally writing it is: mechanical
assembly of already-proved pieces — `reducedClass_eq_of_isReduction'` +
`swapImages`/`fixedTargetSolutions_ncard_le_four` + basic
`AddCommGroup`/`Jacobian` algebra for the `reducedClass_c := reducedClass
+ c•aClass` transport step (this part fully provable today) — plus the
per-`c` `isReduction` hypothesis threaded through explicitly rather than
hidden.**

**Where the confusion came from, worth recording so it doesn't recur.**
A "RESOLUTION" pass (superseded by this rewrite) argued the union
"collapses for free," reading the `Δ'`-translation fact as literally
re-identifying `(P1',P2',P3',P4')` with `(P1,P2,P3,P4)` "under relabeled
points" — i.e. treating a class-level algebraic identity as if it
produced a point-quadruple bijection. It doesn't: nothing in
`matching_solutions_translate_by_delta`'s statement or proof constructs
or asserts a map on `H.Point`-quadruples, only an existential `Δ` at the
`Jacobian H D` level. `SampleTargetFromAlphaPairMemA.lean`'s own earlier,
more cautious diagnosis — that composing the `Δ`-membership fact with a
stabilizer-triviality argument is "NOT a one-line corollary, because
`FixedTargetSolutions`'s pair-sum is constant across a single fiber" —
was correct, and should be trusted over the later "RESOLUTION" framing
that dismissed it.

**Also worth recording**: the `Stab(S)` argument (steps 1-6 of an earlier
pass, preserved in `StabOfSmallSetTrivial.lean`) is a genuinely different,
correct piece of abstract group theory (`[AddCommGroup G] (a : G)`
prime-order, small-set stabilizer-triviality) that WOULD close this gap
*if* two further standing hypotheses were formalized: (a) a formal home
for "all four points across a comparison lie in `⟨a⟩`," and (b) a
`Fintype`/prime-order instance for `AddSubgroup.zmultiples aClass`.
Neither is derivable from this project's abstract `Jacobian H D`
construction — both would need to be added as new, explicit hypotheses.
This route was set aside (not disproved) in favor of the "gauge collapses
for free" argument above, which turned out not to work. **It may be worth
returning to `Stab(S)` now that the free-collapse route is confirmed not
to close the gap** — see "Next steps" below.

## Next steps

**STALE — see the "SUPERSEDED (2026-09-18)" block at the top of this
file. The items below are the old `matchCount`-bounding plan; do not
resume them. Kept for archaeology only.**

**CORRECTED (this pass) — not fully closed; see step 2's "Consequence"
note above.** The transport half is real and provable today; the overall
conclusion still honestly carries a per-`c` `isReduction` hypothesis
until `Reduce` is assembled as a callable function. What remains:

1. Write the Lean proof assembling, in the CORRECT order (shift `alpha`
   before invoking `isReduction`, not after — see step 2 above for why
   the reverse order was wrong):
   (a) the `reducedClass_c := reducedClass + c•aClass` transport step —
   pure `AddCommGroup`/`zsmul` algebra, provable today, no `Reduce`
   dependency;
   (b) `reducedClass_eq_of_isReduction'` (`ReducedClassBundles.lean`,
   proved) applied twice — once to the original `sa`, once to a fresh
   `SampleTargetFromAlpha` instance at `alpha+c` built from (a)'s shifted
   class, carrying its OWN `isReduction` hypothesis (don't try to derive
   it from the first instance's);
   (c) `swapImages`/`fixedTargetSolutions_ncard_le_four`
   (`MatchingSolutionSwapSymmetry.lean`, proved) applied to both.
   The resulting theorem's conclusion should honestly state its
   hypothesis as "for every `c` in [whatever range matters] such that a
   `SampleTargetFromAlpha` at `alpha+c` with the transported
   `reducedClass` and its own `isReduction` witness exists" — carrying
   forward the standing hypotheses each piece already needs (`hbridge`,
   `IsOnlyEffectiveInClass`, `ReductionData`/`SplitAssemblyData`
   witnesses, `hdeg`/`hD`) rather than re-deriving them, and rather than
   silently dropping the per-`c` `isReduction` requirement to make the
   statement look unconditional.
2. Wire the result into `UniformFiberBoundOffDiagonal.lean`'s
   `offDiagonalBound_of_uniform_matchCount_bound_four` (already proved,
   waiting for exactly this hypothesis) to close `OffDiagonalBound`.
3. Whichever route closes it, the eventual output should be a theorem
   `matchCount (s D δ₀ '' F) Δ ≤ K` for a `p`-independent `K` and every
   `Δ ≠ 0` (or with a well-characterized, provably-small exceptional set
   of `Δ`'s excluded) — feeding directly into
   `UniformFiberBoundOffDiagonal.lean`'s
   `offDiagonalBound_of_uniform_matchCount_bound_four`, already built and
   waiting for exactly this hypothesis. That file, plus
   `AlphaLocusDegreeUniform.lean`'s task (B) (`Bad`, the exceptional-set
   accounting — see below), are the only pieces still missing once this
   gap closes.

**Not needed regardless of which route above is taken**: Obligation 3's
old `hfinrank_le` route via `GenericPeelChainHyp`/`Rdec p ⧸
Ideal.span(genList ...)` is confirmed dead — it assumed its own
conclusion (`decoupledSystem_degree_uniform`'s existing statement is
circular, see "What's actually in the files" below) and should not be
resumed as-is.

**CHECKED (2026-09-18) — `CantorMulMumford.lean` does NOT yet let us
*construct* a per-`c` `isReduction` witness; item 1's "Consequence"
caveat above still stands exactly as written.** `CantorMulMumford.lean`
(companion `CantorCompositionStep.lean`, both new this pass, both
sorry-free) was written to supply `isReduction'`'s "gap 1" — `alpha •
aClass`'s own Mumford pair `(ua0,ua1,va0,va1)`, which `isReduction'`'s
docstring (`AlphaLocusDegreeUniform.lean`) already flags as
"supplied by the caller, not derived." Checked directly whether it
closes that gap (and hence lets item 1's per-`c` `isReduction`
hypothesis be discharged rather than assumed): it doesn't, for three
compounding reasons `CantorMulMumford.lean`'s own "still open" section
already names precisely:

1. `cantorMulPair_isMumfordPair` (the file's main theorem) is proved
   *given* a `CantorMulWitness` — the Bézout coefficients and reduction
   quotients at every level of `alpha`'s binary expansion. Nobody has
   produced one; it's existence data, exactly the same *kind* of
   standing hypothesis as `isReduction` itself, not a discharge of it.
   Swapping "`(ua0,ua1,va0,va1)` exists and is correct" for
   "`CantorMulWitness` exists" is not a reduction in what's assumed.
2. `CantorAddWitness` models exactly one reduction step, not
   `cantor_add`'s full `while` loop — so even given a full
   `CantorMulWitness`, nothing here guarantees the output actually
   reaches `natDegree ≤ 2` after finitely many applications.
3. `CantorMulMumford.lean` works over abstract `Polynomial K`/`f`;
   `Reduce`/`ReduceDispatchGeneral` want four `F p` field elements
   (`.coeff 0`/`.coeff 1` of a degree-≤2 pair, specialized at
   `K := F p`). Neither the specialization nor the degree bound is
   established in this file.

And that's only gap 1 of `isReduction'`. Even a fully-discharged
`CantorMulWitness` would only hand `ReduceDispatchGeneral` its input —
it says nothing about `Reduce`'s *correctness* (that its output equals
`reducedClass`'s divisor-class-level description), which
`isReduction'`'s own docstring already calls "a fully open,
not-yet-attempted theorem." **Conclusion: `CantorMulMumford.lean` is
real, useful progress — the concrete recipe for what kind of witness
gap 1 needs, and an unconditional proof of the structural half (`cantorAdd`
preserves the Mumford identity, given any witness) — but it adds a new
named open item (`CantorMulWitness`, for a concrete `base`/`n`) to the
stack rather than closing the existing one. Item 1's assembled theorem,
when written, should still honestly carry the per-`c` `isReduction`
hypothesis (or, if built via this route, a `CantorMulWitness` hypothesis
plus `Reduce`'s correctness) rather than presenting either as
discharged.**

## What's actually in the files

- **`DataDerivationBasics/Tower/Solve/Mumford.lean`**: builds `theData`,
  i.e. `(uRS, vRS)`, as a tower construction over symbolic anchors, for
  one sample. Curve-and-anchor data only; no `alpha` anywhere. Sorry-free.
- **`DecoupledSystemRegular.lean`**: `Idx` is the 12-variable list.
  `SampleTarget` is `(u0,u1,v0,v1)`, no `alpha` field — agnostic to how
  the target arose. `theData`'s assembly here is fully wired, sorry-free.
  `decoupledSystem_isRegularSequence`/`decoupledSystem_zeroDimensional`
  have moved to `AlphaLocusDegreeUniform.lean` (pointer docstring left in
  place).
- **`AlphaLocusDegreeUniform.lean`**: home of
  `decoupledSystem_isRegularSequence` (fixed-target case — **proved, no
  `sorry`**, delegates to `PeelChainAssembly.lean`'s
  `regularSeq_of_peel_chain`) and `decoupledSystem_zeroDimensional`
  (**proved, no `sorry`**, via
  `Module.Finite.quotient_of_isRegular_of_length_eq_card`). Also home of
  `decoupledSystem_degree_uniform`, the OLD target theorem — **stated but
  circular**: it typechecks only because a later pass introduced
  `GenericPeelChainHyp.hfinrank_le`, which assumes the uniform degree
  bound as a hypothesis and hands it straight back as the conclusion.
  Treat this as still open despite "building green." Also home of
  `SampleTargetFromAlpha` (task (A)'s `alpha`-parametrized extension of
  `SampleTarget`), with `isReduction` still an assumed `Prop` field rather
  than a constructed witness pointing at a real `Reduce` function.
- **`AlphaReduce.lean`**: the K=4 concrete-point port of `Reduce`
  (task (A)'s hard part). Confirmed building clean, 0 errors, 0 `sorry`,
  through `uRS4_dvd_Npoly4`/`vRS4_sq_eq_f_mod_uRS4` (the Mumford identity
  for the reduced quotient). **Not yet built**: `Reduce` itself as a
  callable function returning `(u0,u1,v0,v1)` (the divisibility/Mumford
  machinery is all in place, but nothing assembles it into the function),
  and the tangent/multiplicity-2 case (`P1=P2` or any other pairwise
  point-coincidence) — the general `rootMultiplicity ≥ 2` lemmas are
  proved and sorry-free, but nothing downstream invokes them yet. `m≥3`
  (triple coincidence) is out of scope by design, matching the reference
  Julia pipeline's own limits — fold into `Bad` rather than build further
  machinery for it.
- **`MatchingSolutionSwapSymmetry.lean`**,
  **`MatchingEquationTranslation.lean`**, **`AlphaUnionGaugeCollapse.lean`**:
  described above under "What's proved." All sorry-free.
- **`UniformFiberBoundOffDiagonal.lean`** (parent `Genus2Lean/` folder,
  not `ZeroD/`): the `matchCount`-side consumer half of the bridge.
  Sorry-free, proved, waiting for the hypothesis described in "Next
  steps" above.
- **`StabOfSmallSetTrivial.lean`**: correct, sorry-free, reusable abstract
  group theory (`[AddCommGroup G]`, prime-order small-set
  stabilizer-triviality) — not currently wired into anything, but see
  "Next steps" item 1.
- **Task (B), `Bad` (the exceptional-set accounting)**: still fully open.
  Nothing in the codebase constructs `Bad` or bounds its size. Two
  concrete candidate contributions are on record: (i) `D ~ K_C` (advisory
  §6.2's locus, for single-instance finiteness) — whether this coincides
  with wherever the degree genuinely jumps has never been checked;
  (ii) `alpha`-values whose `alpha•a`'s support collides with the factor
  base being drawn from (a concrete, checkable, mechanical exclusion
  criterion, identified but not yet formalized). Needs its own
  definition and a genuine `F_p`-point-count size bound, not just
  "positive-dimensional over `C`" — a measure-zero-over-`C` set can still
  be a large fraction of `F_p`-points.

## Translation-layer notes (for whoever picks up "Next steps" item 4)

`matchCount`'s `G` is `Jacobian H D` (or its cryptographic subgroup); the
factor base `T : Finset G` is `s D δ₀ '' F` for a chosen `F : Finset
H.Point`. This is exactly the same object `SidonBridge.lean` calls
`sidonSet` — a `matchCountSet`-style definition following that file's
pattern (`F.image (s D δ₀)`) is the right shape, and
`repCount (s D δ₀ '' F) A ≤ 2` (transporting `pairFiber_ncard_le_two`
from `Set.ncard` to `Finset.card`, given an explicit `FactorBaseGeneric`
hypothesis — "every pair `F` realizes satisfies `IsOnlyEffectiveInClass`,"
i.e. avoids task (B)'s exceptional locus) is a genuine, provable
standalone lemma, already sketched, not yet written to a file. It is NOT
by itself sufficient to close `matchCount T Δ ≤ 4` — see "the actual gap"
above — but it is real partial progress and should be kept regardless of
which "Next steps" route closes the rest.

## What NOT to do

Don't restart `DataDerivationBasics.lean`/`DataDerivationTower.lean`/
`DataDerivationSolve.lean`/`DataDerivationMumford.lean`/
`DecoupledSystemRegular.lean` from scratch in favor of a "cleaner"
birationality-only argument — that machinery is the toolkit any remaining
work extends, not a detour from it. Don't treat "generate one more
numerical instance and eyeball the degree" as a substitute for an actual
proof that the union/orbit-count is bounded — it's a cheap sanity check,
not a closing argument. Don't resume the old `hfinrank_le`/
`GenericPeelChainHyp` route believing it finishes
`decoupledSystem_degree_uniform` — it's circular, see above.

---

## History (condensed; for archaeology only — "Current status" above is
## authoritative)

This roadmap went through several passes that each partially corrected
the previous one, worth summarizing so nobody re-treads them:

1. **Original TL;DR**: claimed a uniform degree bound `deg(alpha,alpha')
   = O(1)` closes advisory-6/7's Question 4 (the 8th-moment gap) via a
   two-line counting argument, and that `decoupledSystem_isRegularSequence`
   (proved for one fixed `(sa,sb)`) was most of the way there.
2. **CRITICAL CORRECTION**: fixing `(alpha,alpha')` only pins the
   *difference* `A-B`, not `A` and `B` individually — so the TL;DR's
   `O(1)` claim was false as argued; the true solution variety for fixed
   `(alpha,alpha')` is a union over every class `A ∈ ⟨a⟩` (order `~p²`),
   each fiber ≤4, naively giving `O(p²)` not `O(1)`.
3. **`Stab(S)` argument** (Newest status update, at the time): proposed
   closing the gap via a prime-order-subgroup stabilizer-triviality
   argument, contingent on two new, not-yet-formalized standing
   hypotheses (`P1..P4 ∈ ⟨a⟩`, a `Fintype`/prime-order instance). Correctly
   identified as "necessary but not sufficient" without those hypotheses
   landing. `StabOfSmallSetTrivial.lean` was written as the reusable
   abstract-group-theory core of this argument, sorry-free but unwired.
4. **"RESOLUTION" pass**: argued the `Stab(S)` machinery was unnecessary
   — that the union "collapses for free" via the class-level translation
   fact (`matching_solutions_translate_by_delta_gauge_orbit`), reading a
   `Jacobian H D`-level equality as if it re-identified point-quadruples
   across fibers. `AlphaUnionGaugeCollapse.lean` was written to formalize
   this composition.
5. **This pass**: attempting to actually wire `AlphaUnionGaugeCollapse`'s
   conclusion into `matchCount`-language (for
   `UniformFiberBoundOffDiagonal.lean`) surfaced that step 4's "collapses
   for free" argument does not go through — the class-level translation
   never produces a point-quadruple-level identification or injection,
   only equal fiber *sizes*. `SampleTargetFromAlphaPairMemA.lean`'s
   original, more cautious diagnosis (predating step 4) was right all
   along. The gap identified in step 2 is confirmed still open; see
   "Current status" and "Next steps" above for where that leaves things.
   `AlphaUnionGaugeCollapse.lean` and `MatchingEquationTranslation.lean`
   remain correct, sorry-free files — their content (equal fiber sizes,
   class-level translation) is real, just not sufficient on its own.

Numerical side-notes preserved from the investigation-note/status-update
layers, still accurate and potentially useful for "Next steps" item 3's
ChatGPT consult or a future numerical check: two independent numerical
checks (a direct resultant solve, and a separate `HomotopyContinuation.jl`
run, both on one fixed curve) found 0-dimensional/near-empty behavior for
random `(P1,P2)` — in tension with a naive fiber-product dimension count
(which predicts a 2-dimensional variety), via the sum map `C⁽²⁾ → J`
being generically bijective for genus 2. Two candidate reconciliations
were proposed, neither checked: (i) the numerical solver's "missing
witnesses" may be a false negative for dimension rather than evidence of
a truly 0D variety — worth rerunning as a numerical irreducible
decomposition rather than a plain witness-point solve; (ii)
`CrossNondegenerate`'s `hv0`/`hv1` resultant conditions (flagged
elsewhere as "expected to be FALSE for at least some, quite possibly
most, choices of `(c0,...,c4)`") may be the ring-theoretic symptom of a
genuinely positive-dimensional component, which would explain the
tension directly. Neither has been re-examined since being proposed.
