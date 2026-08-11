# Roadmap: making `LPairCarrier`/`IsPoleBoundedAtPair` correct over `k = ZMod p`

## TL;DR

`natDegree_le_two_of_isCoprimeAtRoots` (`LPairFinrankOneOrdAtFrac.lean`) is not
the bug. It is a symptom. The actual defect is upstream, in
`RiemannRochGenus2.lean`:

```lean
def IsPoleBoundedAtPair (x₁ x₂ : H.Point) (A B A' B' : k[X]) : Prop :=
  ¬ (A' = 0 ∧ B' = 0) ∧
  ordInfOfPair A B ≥ ordInfOfPair A' B' ∧
  (∀ P : H.Point, ordAt P A B ≥ ordAt P A' B' - (indicator sum))
```

and its `ordAtFrac` twin `IsPoleBoundedAtPair'`. The pointwise clause
quantifies over `P : H.Point` — i.e. only **`k`-rational** points. Over an
algebraically closed field this is harmless, because every closed point of
the curve *is* `k`-rational. Over `k = ZMod p` it is not: a closed point can
have residue field a proper extension of `k` (any point lying over a root of
an irreducible factor of `H.f`, or more generally any point whose
coordinates aren't in `k`), and `IsPoleBoundedAtPair`'s pointwise clause is
structurally blind to poles located there.

**Concrete, fully-checked counterexample** (see "Certified counterexample"
below): with `H.f` irreducible over `k` (no `k`-rational roots at all), the
witness `A=1, B=0, A'=0, B'=1` satisfies *every* clause of
`IsPoleBoundedAtPair'` for **any** `x₁, x₂ : H.Point` — the pointwise clause
is vacuous because there are zero Weierstrass `k`-points to check, and the
infinity clause holds because `ordInfOfPair 1 0 = 0 ≥ ordInfOfPair 0 1 = -5`.
This gives `z = 1/y ∈ LPairCarrier' x₁ x₂`, but `z` is manifestly not a
constant fraction (`y` generates a genuine degree-2 extension of `k(x)`), so
`uniqueDegree2MapToP1_ordAtFrac`'s conclusion `IsConstantFraction z` fails
for it. The theorem, as currently stated, is **false** over `ZMod p`.

Do not spend more time on `natDegree_le_two_of_isCoprimeAtRoots` in
isolation — its hypotheses (`hzsupp`, `IsCoprimeAtRoots`) are honest
statements about the wrong geometric object (rational places only), and no
amount of internal repair makes them see the hidden non-rational pole in the
counterexample above.

## Why this didn't surface earlier

The whole file (`LPairFinrankOneOrdAtFrac.lean`) is written under an ambient
`variable [IsAlgClosed k]`, stated as deliberate project policy in its own
preamble ("`k` is algebraically closed — a standing hypothesis threaded
throughout this project"). Under that hypothesis `H.Point` really does
enumerate every closed point (every maximal ideal of `CoordinateRing H` has
residue field `k`), so `IsPoleBoundedAtPair`'s `H.Point`-indexed clause is
complete, and the file compiles cleanly. The mismatch only appears when the
project's *actual* target field, `k = ZMod p`, is substituted in — which
nothing in the file currently forces anyone to try, since `IsAlgClosed k` is
assumed from the first `variable` line down.

The same gap already has a name inside the codebase, one layer deeper:
`PrincipalDivisors.lean`'s `sum_ordAt_eq_natDegree_pairNorm` has a hypothesis

```lean
(hspec : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
  (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {toPair H A B})).factors ≠ 0 →
  ∃ P, v.asIdeal = pointIdeal P)
```

i.e. "every closed point with nonzero multiplicity in this divisor is
`k`-rational" — assumed, not proved, exactly because it's false in general
over `ZMod p`. This is the same fact `IsPoleBoundedAtPair` implicitly
depends on. Both issues have one root cause and should get one fix.

## What already exists and doesn't need to change

The Dedekind-domain valuation-theoretic machinery this redesign needs is
**already built and in use** — this is not a from-scratch project:

- `IsDedekindDomain.HeightOneSpectrum (CoordinateRing H)` — the full space of
  height-one primes, i.e. all closed points of the (affine) curve, rational
  or not. Already imported and used (`PrincipalDivisors.lean:655` onward).
- `pointHeightOne'/pointHeightOne : H.Point → HeightOneSpectrum (CoordinateRing H)`
  (`PrincipalDivisors.lean:332,341`) — the existing embedding of rational
  points into the full spectrum, via `pointIdeal P = ker(evalAtPoint P)`. This
  is already an *embedding*, not a bijection: `pointIdeal P`'s residue field
  is `k` by construction (`evalAtPoint` surjects onto `k`), so it only ever
  reaches degree-1 primes.
- `ordAt P A B` (`PrincipalDivisors.lean:358`) is **already defined through**
  `pointHeightOne P h_bot`, i.e. through `WithZero.log ∘ intValuation` at a
  general height-one prime — it is already, internally, a special case of a
  more general valuation, just pre-composed with `P ↦ pointHeightOne' P`
  before anything downstream sees it.
- `natDegree_pairNorm_eq_neg_ordInfOfPair` (`PrincipalDivisors.lean:192`):
  `(pairNorm H A B).natDegree = -ordInfOfPair A B` **unconditionally**, pure
  `k[X]`-degree arithmetic, no closedness hypothesis. This is the fact that
  makes the counterexample's degree-5 denominator visible in the first
  place, and it's exactly the fact a correct global pole-bound argument
  needs to reuse.
- `sum_ordAt_eq_natDegree_pairNorm`'s overall shape (sum of local orders over
  a `Finset S : Finset H.Point` equals total degree) is the right *template*
  for a genus-2 Riemann–Roch-style global degree bound — it just needs `S`
  replaced by (or supplemented with) a sum over `HeightOneSpectrum`.

None of this needs to be invented. The redesign is a re-indexing of
existing definitions, not a new valuation theory.

## What does need to change

### 1. New primitive: `ordAtSpec`

```lean
noncomputable def ordAtSpec [IsDedekindDomain (CoordinateRing H)]
    (v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H)) (A B : k[X]) : ℤ :=
  if toPair H A B = 0 then 0
  else -WithZero.log (v.intValuation (toPair H A B))
```

(No `pointIdeal P ≠ ⊥` side-condition to thread — every `HeightOneSpectrum`
element already carries `ne_bot` in its structure.) Then:

```lean
theorem ordAt_eq_ordAtSpec (P : H.Point) (A B : k[X]) :
    ordAt P A B = ordAtSpec (pointHeightOne' P) A B := rfl  -- or close to it
```

recovering `ordAt` as the rational-point specialization. This step should be
almost entirely refactor-and-rename; every existing lemma about `ordAt` (the
`ordAt_eq_rootMultiplicity_ramified`/`_unramified` pair,
`ordAt_eq_zero_of_notMem`, etc.) either transports automatically along this
identity or needs only a `rfl`-level restatement.

### 2. `IsPoleBoundedAtPair`/`IsPoleBoundedAtPair'`, requantified

```lean
def IsPoleBoundedAtPairSpec (x₁ x₂ : H.Point) (A B A' B' : k[X]) : Prop :=
  ¬ (A' = 0 ∧ B' = 0) ∧
  ordInfOfPair A B ≥ ordInfOfPair A' B' ∧
  (∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
    ordAtSpec v A B ≥ ordAtSpec v A' B' -
      ((if v = pointHeightOne' x₁ then 1 else 0) + (if v = pointHeightOne' x₂ then 1 else 0)))
```

with `LPairCarrierSpec`/`LPairCarrierSpec'` defined the same way as today but
against this predicate. This is the actual fix: the pointwise clause now
sees *every* closed point, rational or not, so the `1/y`-style hidden pole
is caught (some `v` cutting out a zero/pole of `y` away from `{x₁,x₂}`'s
images forces a violation).

**This is the definition change that matters.** Everything else in this
roadmap is in service of making this definition provable-with and
usable-with the rest of the existing file.

### 3. `H.Point`-boundedness becomes a derived corollary, not the definition

```lean
theorem isPoleBoundedAtPair_of_spec (x₁ x₂ : H.Point) (A B A' B' : k[X]) :
    IsPoleBoundedAtPairSpec x₁ x₂ A B A' B' → IsPoleBoundedAtPair x₁ x₂ A B A' B' := by
  rintro ⟨h1, h2, h3⟩
  exact ⟨h1, h2, fun P => (ordAt_eq_ordAtSpec ..) ▸ h3 (pointHeightOne' P)⟩
```

i.e. specialize the universal `v` quantifier to `v = pointHeightOne' P`. This
direction is free (just instantiate). The whole existing rational-root /
factor-base argument in `LPairFinrankOneOrdAtFrac.lean` — `IsCoprimeAtRoots`,
`hzsupp`, `exists_pole_of_isCoprimeAtRoots`, `hcard_le`, `hnodup` — continues
to consume `IsPoleBoundedAtPair` (the `H.Point`-only predicate) exactly as
today, now reached via this derived specialization instead of being the
primary definition. **No changes needed to that machinery** beyond swapping
which theorem hands it its input.

### 4. The genuinely new mathematical content: a global degree bound

This is the piece that was previously (wrongly) attempted via
`natDegree_le_two_of_isCoprimeAtRoots`, and is the real Riemann–Roch content
the project needs. Shape:

```lean
theorem natDegree_le_two_of_isPoleBoundedAtPairSpec
    (x₁ x₂ : H.Point) (A' B' : k[X]) (hA'B' : ¬(A' = 0 ∧ B' = 0))
    (hspec : ∀ v : HeightOneSpectrum (CoordinateRing H),
      -- pole bound at every place, from IsPoleBoundedAtPairSpec's pointwise clause,
      -- specialized to the denominator's own zero/pole structure
      ...) :
    (pairNorm H A' B').natDegree ≤ 2 := ...
```

Proof sketch (standard degree-of-a-divisor argument, made precise against
this codebase's actual API): `natDegree_pairNorm_eq_neg_ordInfOfPair` gives
`(pairNorm H A' B').natDegree = -ordInfOfPair A' B'` directly — so it
suffices to bound `-ordInfOfPair A' B'` (the pole order of `toPair H A' B'`
at infinity) by 2. This should follow from a *degree-of-divisor-is-zero*
style fact for the coordinate ring's function field: the total degree of
zeros of `toPair H A' B'` (summed over all closed points, weighted by
residue-field degree, à la `sum_ordAt_eq_natDegree_pairNorm`'s intended
generalization) equals its total pole degree (at infinity), and the pole
bound `≤ (x₁)+(x₂)` on the *reciprocal* direction caps the zero-side sum at
2 in exactly the way this file's existing `hcard_le`/`hnodup` argument
already establishes for the rational-point-only sub-case. The rational-only
argument is the right template; it just needs the sum extended over
`HeightOneSpectrum` with residue-degree weights instead of over
`c.roots.toFinset`.

This is real, not-yet-formalized mathematics — flag it for a ChatGPT
consultation once the definitions in steps 1–3 are in place and compiling,
rather than attempting it blind. It is the direct Lean analogue of "the
degree of a principal divisor is zero" / Riemann–Roch's `ℓ(D) ≤ deg D + 1`
for `deg D = 2`, phrased for this specific coordinate ring.

## Suggested order of attack

1. **`ordAtSpec` + `ordAt_eq_ordAtSpec`.** Pure refactor, low risk, unlocks
   everything else. Confirm every existing `ordAt`-consuming theorem still
   applies via the identity (should be near-free — `ordAt` already computes
   through `pointHeightOne`).
2. **`IsPoleBoundedAtPairSpec`/`LPairCarrierSpec` + the derived
   `isPoleBoundedAtPair_of_spec` direction.** Also low risk — purely a
   restatement plus one specialization lemma.
3. **Re-certify the counterexample is now excluded.** Before touching
   anything else, confirm concretely that `A=1,B=0,A'=0,B'=1` (with `H.f`
   irreducible over `k`) fails `IsPoleBoundedAtPairSpec`'s pointwise clause
   at some `v` — i.e. that some non-rational closed point genuinely
   witnesses the violation. This should be checkable directly: `H.f`
   irreducible over `k` means `k[X]/(H.f)` is a field extension of `k` of
   degree 5, giving a height-one prime of `CoordinateRing H` above it with
   residue field of degree > 1, at which `toPair H 0 1 = y` vanishes (`y² =
   H.f(x) = 0` in that residue field) — this `v` is not `pointHeightOne' x₁`
   or `x₂` for any `k`-rational `x₁,x₂`, so it violates the pointwise clause
   unless already excluded by the indicator, closing the counterexample.
   Worth nailing down as a standalone sanity-check theorem before step 4.
4. **The global degree bound (§4 above).** The one genuinely hard piece.
   Scope it as its own file/session, likely with a ChatGPT consultation
   prompt mirroring this project's existing style
   (`chatgpt_prompt_coprimality.md`), once 1–3 compile.
5. **Rewire `LPairFinrankOneOrdAtFrac.lean`'s assembly theorem** to consume
   `LPairCarrierSpec'` instead of `LPairCarrier'`, feeding
   `isPoleBoundedAtPair_of_spec` to reach the existing `H.Point`-only
   argument for the "at most 2 factor-base poles" half, and the new §4
   theorem for the "hence `c.natDegree ≤ 2`" half — replacing
   `natDegree_le_two_of_isCoprimeAtRoots`'s call site with a call to §4's
   theorem instead. `b_eq_zero_of_rationalized_pole_bounded` and everything
   after it in the file needs **no changes** — it only ever consumed a bare
   `c.natDegree ≤ 2` fact, agnostic to how it was derived.

## What's explicitly out of scope for this pass

- Rewriting `IsCoprimeAtRoots`, `hzsupp`, `exists_pole_of_isCoprimeAtRoots`,
  or any of the rational-root/factor-base bookkeeping in
  `LPairFinrankOneOrdAtFrac.lean` §4/§5. These are correct statements about
  the correct object (`H.Point`, the actual factor base) and should survive
  this redesign untouched, consumed via `isPoleBoundedAtPair_of_spec` rather
  than rewritten.
- The non-Weierstrass square-root step in `exists_pole_of_isCoprimeAtRoots`
  (currently `IsAlgClosed.exists_pow_nat_eq`) — separately fixable by
  deriving `f(α) = (A'(α)/B'(α))²` algebraically from `c(α) = A'(α)² -
  B'(α)²f(α) = 0` and coprimality (`B'(α) ≠ 0` follows from coprimality once
  `f(α) ≠ 0`), per the ChatGPT correction on this thread. Small, local,
  independent of the `HeightOneSpectrum` redesign — can be done in parallel
  or first, since it doesn't touch `IsPoleBoundedAtPair`.
- Removing `[IsAlgClosed k]` from the rest of the file wholesale. Once
  `LPairCarrierSpec'` is correct for general `k`, the ambient `variable
  [IsAlgClosed k]` blocks can be relaxed section-by-section, but that's
  cleanup, not part of the core fix — don't block on it.
- Any change to `H.Point`, `pointIdeal`, `Equation`, or the factor-base
  definition itself. The factor base is, correctly, `H(𝔽_p)` — this
  redesign only changes what *pole-boundedness* means, not what counts as a
  factor-base point.

## Certified counterexample (for reference / re-verification)

Concrete numeric instance, checked directly: `p = 7`, `H.f = X^5 + X + 3`.
`H.f` has no roots in `𝔽_7` (checked by exhaustion: `f(0..6) mod 7` all
nonzero), so zero Weierstrass `𝔽_7`-points exist, and `H.Point` is still
nonempty (e.g. `f(2) = 2` is a nonzero QR mod 7, giving genuine affine
points `(2, ±2)` etc. — five such `x`-values exist for `p=7`). With
`A=1,B=0,A'=0,B'=1`:

- `¬(A'=0 ∧ B'=0)`: `¬(0=0∧1=0)` — true.
- `ordInfOfPair A B = ordInfOfPair 1 0 = 0`.
- `ordInfOfPair A' B' = ordInfOfPair 0 1 = -(2·0+5) = -5`. `0 ≥ -5` — holds.
- Pointwise: `toPair H 1 0 = 1` is a unit, `ordAt P 1 0 = 0` for all
  `P`. `toPair H 0 1 = y`; `y`'s zero locus among `H.Point` is exactly the
  Weierstrass points, of which there are none — so `ordAt P 0 1 = 0` for
  every `P : H.Point` too. Clause `0 ≥ 0 - indicator(P)` holds for all `P`,
  for any `x₁,x₂`.

`z = polePairToFraction 1 0 0 1 = 1/y ∈ LPairCarrier' x₁ x₂` for any
`x₁,x₂ : H.Point`, but `z` is not a constant fraction. Re-verify this
numerically/structurally before relying on it further — this doc's step 3
above is exactly that re-verification, done against `IsPoleBoundedAtPairSpec`
instead.
