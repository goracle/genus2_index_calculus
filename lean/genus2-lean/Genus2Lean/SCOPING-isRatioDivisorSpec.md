# Scoping note: `IsRatioDivisorSpec` — threading `hspec` through `IsRatioDivisor`
to close the `hreduced` gap for good, general `k`

## TL;DR

`RiemannRochCrux.lean`'s `isOnlyEffectiveInClass_of_uniqueDegree2MapToP1` (closed
field) and its general-`k` analogue (not yet written, planned in
`LPairFinrankOneOrdAtFracSpec.lean` §5) both stall on the same `hreduced`-shaped
gap: given the witness `(A,B,A',B')` that `IsRatioDivisor` hands you for a
principal divisor `(x₁)+(x₂)-(x₃)-(x₄)`, you need to know the ratio `toPair A B /
toPair A' B'` has **no pole hiding at a non-rational closed point** — and nothing
in `IsRatioDivisor`'s own data proves that, because the fact that would prove it
is thrown away one step upstream.

**The fact exists and is already in the codebase.** `principalSubgroup`'s
generators (`PrincipalDivisorSubgroup.lean:166-185`) carry an explicit
`hspec₁`/`hspec₂` hypothesis:

```lean
hspec₁ : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
  (Associates.mk v.asIdeal).count
    (Associates.mk (Ideal.span ({toPair H A₁ B₁} : Set (CoordinateRing H)))).factors ≠ 0 →
  ∃ P, v.asIdeal = pointIdeal P
```

i.e. "every closed point with nonzero multiplicity in `toPair H A₁ B₁`'s
factorization is rational" — exactly the divisor-theoretic fact that rules out a
non-rational pole. But `isRatioDivisor_of_mem_principalSubgroup`
(`RatioDivisorCollapse.lean:313-345`) destructures a generator and **discards**
this hypothesis:

```lean
rintro D ⟨A₁, B₁, S₁, hAB₁, hsupp₁, _hspec₁, _hfin₁, A₂, B₂, S₂, hAB₂, hsupp₂,
  _hspec₂, _hfin₂, hmatch, rfl⟩
```

(`_hspec₁`, `_hspec₂` — underscore-bound, thrown away). `IsRatioDivisor` itself
(`RatioDivisorCollapse.lean:115-120`) has no field for it at all. This is why
`hreduced` looks unprovable from inside `mem_LPairCarrier_of_isRatioDivisor` or
any consumer downstream of `IsRatioDivisor` — the information needed to prove it
was dropped before `IsRatioDivisor` was even constructed. Over an algebraically
closed field this was invisible: `hspec` is vacuously true there (every closed
point is rational), so discarding it cost nothing and the closed-field file
(`RiemannRochCrux.lean`) never noticed. Over general `k` it's fatal.

**This is a confirmed mathematical fact, not a hunch** — see "Why `hcoef` +
`hgu` + infinity alone cannot work" below for the counterexample that rules out
every softer alternative that was tried first.

## Why `hcoef` + `hgu` + infinity alone cannot work

(Recorded here so a future session doesn't re-attempt the softer routes that
were already tried and ruled out this session — all of them are dead ends for
the same underlying reason.)

Given only:
- `hcoef : ∀ P : H.Point, ordAt P A B - ordAt P A' B' = <rational indicator>`
  (`IsRatioDivisor`'s derived consequence, rational points only),
- `hgu : IsUnit (gcd (gcd a₀ b₀) c₀)` (the rationalized-and-gcd-reduced triple is
  genuinely coprime, no shared irreducible factor of *any* degree), and
- the infinity/degree bound `ordInfOfPair a₀ b₀ ≥ ordInfOfPair c₀ 0`,

the closed-point bound `hzsuppSpec₀` (needed for `LPairCarrierSpec'`/
`IsPoleBoundedAtPairSpec'` membership) **does not follow**. Counterexample
(confirmed by consultation, see below): fix any situation where the rational
data holds, then replace `c₀` by `c₀ · qᴺ` for `q` irreducible, coprime to
`a₀,b₀,c₀`, with **no rational root** (so `hcoef` is untouched — `ordAt` at every
rational point is unchanged) but with a genuine non-rational closed-point factor
`v₀ ∣ q`. `hgu` is preserved (`q` was chosen coprime to the original data). The
infinity inequality only gets *easier* to satisfy as `N → ∞` if `q` is affine
(more negative order at infinity on the denominator side only helps). But at
`v₀`, `ordAtSpec v₀ c₀qᴺ = ordAtSpec v₀ c₀ + N·ordAtSpec v₀ q` grows without
bound while the numerator's value at `v₀` is untouched — so for large `N` the
closed-point bound fails at `v₀`, even though every rational-point hypothesis,
the gcd/reducedness hypothesis, and the infinity inequality all still hold.
**A degree-sum identity over all closed points doesn't rescue this either**:
knowing rational-point values plus one global inequality only pins down a
*weighted total*, not that each individual non-rational term is nonnegative —
and the counterexample is exactly a case where the non-rational term is what
absorbs the slack.

Conclusion: **only genuinely divisor-theoretic data** (the `hspec` fact: which
closed points can appear in `toPair H A B`'s factorization at all) rules this
out. There is no way to get `hzsuppSpec₀`/`hreduced` from rational-point data
alone, however it's massaged. Do not re-attempt this; thread `hspec` instead.

## What already exists and doesn't need to change

- `principalSubgroup`'s definition, and its `hspec₁`/`hspec₂` fields
  (`PrincipalDivisorSubgroup.lean:166-185`) — the fact is already there, already
  proved to hold for every generator (it's baked into the `AddSubgroup.closure`
  set itself), nothing to add here.
- `deg_divToPairRatio_eq_zero` (`PrincipalDivisorSubgroup.lean:128-150`) — already
  consumes `hspec₁`/`hspec₂` correctly (via `deg_div_eq_zero_deg5`, not shown in
  this file but upstream) to prove degree-0. Not part of the gap; unaffected by
  anything below.
- `ordAtSpec`, `ordAtSpec'`, `pointHeightOne'`, the whole closed-point apparatus
  (`RiemannRochGenus2.lean` §1c, `LPairFinrankOneOrdAtFracSpec.lean`) — already
  built, already used successfully by `uniqueDegree2MapToP1Spec` /
  `natDegree_le_two_of_gcdUnit_closed_point`. What's missing is only the bridge
  from `hspec`-shaped data to this apparatus, not the apparatus itself.
- `heightOneSpectrum_over_irreducible` (`LPairFinrankOneOrdAtFracSpec.lean:1150`)
  — "every irreducible `q : k[X]` determines a height-one prime `v` lying over
  it" — likely the right tool for converting an `hspec`-style "every closed
  point dividing this is rational" statement into "every irreducible factor `q`
  of the underlying `k[X]` polynomial has a `k`-rational root", or vice versa,
  if that reformulation turns out to be the cleanest one to carry through the
  closure induction (see "Open design question" below).
- `uniqueDegree2MapToP1_general` and `finrank_LPairSpec'_eq_one`
  (`LPairFinrankOneOrdAtFracSpec.lean`) — fully proved, general `k`, no
  `IsAlgClosed`. This is the theorem the new work below needs to feed into; it
  does not itself need touching.

## What needs to change

### 1. `IsRatioDivisorSpec`: a new predicate carrying `hspec`

Add a field to `IsRatioDivisor`'s existential (or define a new predicate
`IsRatioDivisorSpec`, parallel-not-replacing `IsRatioDivisor` — recommended, to
avoid rippling into the closed-field consumers listed below) requiring:

```lean
∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
  (Associates.mk v.asIdeal).count
    (Associates.mk (Ideal.span ({toPair H A} : Set (CoordinateRing H)))).factors ≠ 0 →
  ∃ P, v.asIdeal = pointIdeal P
```

for *both* the numerator pair `(A,B)` and denominator pair `(A',B')` (i.e. two
such clauses, mirroring `hspec₁`/`hspec₂`). Naming: `IsRatioDivisorSpec` to match
the project's existing `...Spec` convention for the general-`k` sibling of an
`H.Point`-only predicate (`IsPoleBoundedAtPairSpec'` vs `IsPoleBoundedAtPair'`,
`LPairCarrierSpec'` vs `LPairCarrier'`).

### 2. Re-derive the closure lemmas, retaining `hspec`

Three lemmas to port, in increasing difficulty (**do the easy ones first**, per
project convention):

- **`isRatioDivisorSpec_zero`** — trivial. `A=A'=1, B=B'=0`; `toPair H 1 0 = 1`
  is a unit, `Ideal.span {1} = ⊤`, its factorization is empty, `hspec` holds
  vacuously (the `count ≠ 0` hypothesis is never satisfiable). Should be a
  one-liner once the right `simp` set is found.

- **`isRatioDivisorSpec_neg`** — trivial. Pure swap of numerator/denominator
  (mirrors `isRatioDivisor_neg` exactly, `RatioDivisorCollapse.lean:137-141`);
  `hspec` for `(A,B)` and `(A',B')` just swap roles, no new content.

- **`isRatioDivisorSpec_add`** — the real work, mirrors `isRatioDivisor_add`
  (`RatioDivisorCollapse.lean:161-291`, ~130 lines). Needs one new lemma this
  file doesn't yet have: **`toPair H A B`'s factorization is rational-supported,
  and `toPair H A₁ B₁ * toPair H A₂ B₂`'s factorization is rational-supported,
  given both factors' are.** This should be easy in substance — a product's
  irreducible factors are exactly the union (with multiplicity) of each
  factor's irreducible factors (`UniqueFactorizationMonoid`/`Associates.count`
  API — likely `Associates.count_mul` or similar, converting `count ≠ 0` on a
  product into `count ≠ 0` on one of the two factors, then applying `hspec₁`/
  `hspec₂` to whichever one it lands on). Isolate this as its own top-level
  lemma (e.g. `hspec_mul_of_hspec`) before touching `isRatioDivisorSpec_add`
  itself, so the ~130-line port only needs to insert two calls to it (numerator
  and denominator) rather than reproving it inline.

### 3. `isRatioDivisorSpec_of_mem_principalSubgroup`

Mirrors `isRatioDivisor_of_mem_principalSubgroup`
(`RatioDivisorCollapse.lean:313-345`) exactly, but keeps `hspec₁`/`hspec₂` in the
`rintro` pattern instead of discarding them, feeding `isRatioDivisorSpec_add`
where the old proof fed `isRatioDivisor_add`. The `AddSubgroup.closure_induction`
call itself is unchanged.

### 4. `mem_LPairCarrierSpec'_of_isRatioDivisor`

New theorem, `LPairFinrankOneOrdAtFracSpec.lean` §5 (the docstring is already
there, at the top of §5 — line ~3102 as of this session — the body was never
written). Mirrors `mem_LPairCarrier_of_isRatioDivisor`
(`RatioDivisorCollapse.lean:392-571`) in overall shape (same `hcoef`
construction, same swapped-witness `polePairToFraction A' B' A B` output,
same non-constancy argument), but:

- Takes `IsRatioDivisorSpec`'s witness (with `hspec`) instead of
  `IsRatioDivisor`'s.
- Instead of taking `hreduced` as an explicit unprovable hypothesis (the way
  `mem_LPairCarrier_of_isRatioDivisor` does, forcing the `sorry` one level up in
  every consumer), **derives** the closed-point pointwise bound directly from
  `hspec` + `hcoef`: at a closed point `v` NOT of the form `pointHeightOne' P`
  for rational `P`, `hspec` on the relevant side (numerator or denominator, per
  which one actually has `v` as a factor) forces `ordAtSpec v _ = 0` — apply to
  whichever side `v` could divide, contradiction or zero either way. At a
  rational `v = pointHeightOne' P`, fall back to `hcoef P` via
  `ordAt_eq_ordAtSpec` (already `rfl`-level per the roadmap). This is the
  actual mathematical content that makes the bound provable — `hspec` doesn't
  just patch the counterexample above, it removes the need for `hreduced` (the
  gcd-reduction step) entirely, since `hspec` already says "no non-rational
  closed point sees a pole", full stop.
- Output shape should match `mem_LPairCarrier_of_isRatioDivisor`'s (a witness
  quadruple plus `IsPoleBoundedAtPairSpec'` and non-constancy), so it slots
  directly into an `isOnlyEffectiveInClass_of_uniqueDegree2MapToP1_general`
  built the same way `RiemannRochCrux.lean`'s closed-field version is built
  (`RiemannRochCrux.lean:203-222`), just swapping in
  `uniqueDegree2MapToP1_general` for `uniqueDegree2MapToP1` and no longer
  needing a `hreduced := sorry` line at all.

### 5. Assembly

Once (4) exists, `isOnlyEffectiveInClass_of_uniqueDegree2MapToP1_general` is a
direct port of `RiemannRochCrux.lean:203-222` with the `sorry` simply gone (no
replacement needed — see point 4's third bullet). Combined with the already-
proved `finrank_LPairSpec'_eq_one`, this gives the general-`k`
`IsOnlyEffectiveInClass`/`ℓ(D)=1` pair — i.e. the actual Forey–Fresán–Kowalski
Sidon-set uniqueness fact, formalized over `F_p`, not just over a closed field.
That is the deliverable this whole multi-session thread has been working
toward.

## Open design question: does `IsRatioDivisor` need to change at all?

Recommended above: leave `IsRatioDivisor` and its three closed-field consumers
(`LPairFinrankOne.lean`, `RiemannRochCrux.lean`, and `RatioDivisorCollapse.lean`
§3's `mem_LPairCarrier_of_isRatioDivisor` itself) completely untouched, and add
`IsRatioDivisorSpec` as a parallel, stronger predicate used only by the new
general-`k` track. This avoids any risk of breaking the closed-field proofs
(`finrank_L_pair'` etc., all currently fully proved with no `sorry`) while this
work is in progress.

Alternative (not recommended for this pass, flagged in case a future session
disagrees): make `IsRatioDivisorSpec` *imply* `IsRatioDivisor` (drop the
`hspec` fields via a projection lemma) so that closed-field consumers could in
principle be re-derived from the stronger predicate too, unifying the two
tracks. This would be a bigger, riskier refactor (touching working, sorry-free
proofs) for no immediate benefit — the closed-field track doesn't need
`hspec`, and keeping it separate is exactly the pattern the project already
uses everywhere else (`LPairCarrier` vs `LPairCarrierSpec'`,
`IsPoleBoundedAtPair` vs `IsPoleBoundedAtPairSpec'`). Don't do this unless a
concrete need for the unification shows up later.

## What is explicitly out of scope for this pass

- Modifying `IsRatioDivisor`, `isRatioDivisor_zero/_neg/_add`,
  `isRatioDivisor_of_mem_principalSubgroup`, or `mem_LPairCarrier_of_isRatioDivisor`
  themselves (the closed-field originals) — all correct and fully proved as-is
  for the closed-field track; only new, parallel `...Spec` siblings are needed.
- `RiemannRochCrux.lean`'s own `sorry` at `hreduced`
  (`isOnlyEffectiveInClass_of_uniqueDegree2MapToP1`, line ~217-218) — this is
  the closed-field version and is out of scope; it's a different (also real,
  also currently open) gap in the closed-field file, not fixed by anything
  above. Could in principle now be closed the same way (closed points are
  automatically rational when `k` is algebraically closed, so `hspec` would be
  trivially derivable there too) but that's a separate, smaller follow-up, not
  part of this task.
- The already-deprecated `IsNormCoprime`/`pairNorm`-coprimality route
  (`LPairFinrankOneOrdAtFracSpec.lean` §2 and the now-removed §6) — confirmed
  dead this session, do not resurrect.
- `finrank_L_canonical`/`IsOnlyFibersInCanonicalClass` (the `x₂ = ιx₁` branch)
  — untouched, separate hard theorem, same as prior scoping notes have already
  flagged.

## Suggested order of attack

1. `hspec_mul_of_hspec` (or whatever it ends up named) — the
   `Associates.count`-on-a-product lemma. Small, self-contained, unblocks
   everything else. Search Mathlib for `Associates.count_mul` /
   `UniqueFactorizationMonoid` factorization-of-product lemmas before
   reproving from scratch.
2. `IsRatioDivisorSpec` (the predicate) + `isRatioDivisorSpec_zero`,
   `isRatioDivisorSpec_neg` — trivial once the predicate is stated.
3. `isRatioDivisorSpec_add` — port `isRatioDivisor_add`'s ~130 lines, inserting
   two calls to step 1's lemma.
4. `isRatioDivisorSpec_of_mem_principalSubgroup` — port
   `isRatioDivisor_of_mem_principalSubgroup`, keep `hspec` instead of
   discarding it.
5. `mem_LPairCarrierSpec'_of_isRatioDivisor` — the actual payoff, in
   `LPairFinrankOneOrdAtFracSpec.lean` §5 (docstring already present). This is
   where the closed-point-vs-rational-point case split described in point 4
   above happens.
6. `isOnlyEffectiveInClass_of_uniqueDegree2MapToP1_general` — direct port of
   `RiemannRochCrux.lean:203-222`, `sorry`-free by construction once step 5 is
   done.

Steps 1-2 are quick; step 3 is mechanical but long; steps 4-6 are where the
actual mathematical payoff lands. If tokens run out mid-session, stopping after
step 3 (with steps 4-6 stubbed as named `sorry`s, not attempted) is a clean
place to pause — the hard mathematical question (this note's whole point) is
already resolved, only bookkeeping remains.
