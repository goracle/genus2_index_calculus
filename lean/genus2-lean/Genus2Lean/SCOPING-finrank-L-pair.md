# Scoping note: `finrank_L_pair` / "P1+P2 irreducible" vs. full Riemann–Hurwitz

## TL;DR

`UniqueDegree2MapRiemannHurwitz.lean` is **more machine than the task needs**.
It builds a first-class "degree-2 map to P¹" type, a general ramification-point
notion, a full Riemann–Hurwitz ramification count (`= 6`), and a
Möbius-transform uniqueness argument, in order to prove one narrow fact. That
file has real, hard `sorry`s in it (`h_coprime`, `card_ramification_eq_six`,
the whole Möbius-transform existence argument in
`pole_pair_eq_fiber_of_degree2_weierstrass_ramified`) and is not the shortest
path to what `finrank_L_pair` actually consumes.

**What `finrank_L_pair` actually needs, tracing the dependency graph
precisely:**

```
finrank_L_pair (RiemannRochGenus2.lean, sorry)
  ⟸ finrank_L_pair' (RiemannRochCrux.lean, fully proved)
       = ⟨finrank_LPair_eq_one_of_uniqueDegree2MapToP1,     -- fully proved, from uniqueDegree2MapToP1
          isOnlyEffectiveInClass_of_uniqueDegree2MapToP1⟩   -- fully proved, from uniqueDegree2MapToP1
                                                              --   + RatioDivisorCollapse.lean (fully proved)
  ⟸ uniqueDegree2MapToP1 (RiemannRochCrux.lean, THE ONLY sorry)
```

Everything downstream of `uniqueDegree2MapToP1` — `finrank_LPair_eq_one_...`,
`isOnlyEffectiveInClass_of_...`, all of `RatioDivisorCollapse.lean`, all of
`PrincipalSubgroupCollapse.lean`, all of `HyperellipticClassProof.lean`
(`ordAt_linX_eq` and its three cases) — is **already fully proved, zero real
`sorry` tokens** (checked by grep; only prose mentions of "sorry" remain in
docstrings). So the *entire* remaining gap for "P1+P2 irreducible" is one
theorem:

```lean
theorem uniqueDegree2MapToP1 (hdeg : H.f.natDegree = 5) (x₁ x₂ : H.Point)
    (hne : x₂ ≠ Point.iota x₁) (z : FractionRing (CoordinateRing H))
    (hz : z ∈ LPairCarrier x₁ x₂) : IsConstantFraction z
```

i.e. *"a rational function with poles bounded by `(x₁)+(x₂)`, `x₂ ≠ ιx₁`, is
constant."* This is Riemann–Roch's `ℓ((x₁)+(x₂)) = 1` in disguise, restricted
to exactly the divisors we need (not a general dimension formula).

## Why we don't need the general Riemann–Hurwitz machine

`UniqueDegree2MapRiemannHurwitz.lean`'s strategy is the textbook one: build a
first-class "degree-2 map" object, define ramification abstractly, invoke
Riemann–Hurwitz to count 6 ramification points, then argue any two degree-2
maps with the same ramification agree up to Möbius transform. This proves a
*much stronger* statement than we need (full classification of degree-2 maps
up to Möbius) and requires inventing machinery (`IsDegree2Map`,
`IsRamificationPointOf`, the ramification-count formula, the
Möbius-transform-existence argument) that doesn't exist anywhere else in the
project. Several of its steps are flagged in its own docstrings as "genuinely
hard, not bookkeeping" (`h_coprime`, `card_ramification_eq_six`,
`h_mobius_eq_x`), i.e. real unformalized mathematics, not just plumbing.

We don't need the classification. We only need: **for the two *specific*
divisor shapes that ever arise in the FFK dichotomy — `(x₁)+(x₂)` with
`x₂ ≠ ιx₁`, and `(x)+(ιx)` — the space of pole-bounded rational functions is
exactly `k·1`.** That's a much smaller target, provable directly from the
coordinate ring's `A(x) + B(x)y` shape and elementary polynomial-degree
counting — no ramification indices, no Möbius transforms, no "uniqueness of
the degree-2 map" as an abstract classification.

## The elementary route

Every element of `CoordinateRing H` is `toPair H A B = A(x) + B(x)·y`
(`y² = f(x)`, `deg f = 5`). The pole-order convention already in the project
(`ordInfOfPair`, `PrincipalDivisors.lean:122`) is

```
ordInfOfPair A B = - max(2·deg A, 2·deg B + 5)      (when (A,B) ≠ (0,0), B ≠ 0)
                  = - 2·deg A                          (when B = 0)
```

reflecting the standard hyperelliptic weighting `deg(y) "=" 5/2` at the point
at infinity. `IsPoleBoundedAtPair x₁ x₂ A B A' B'` requires (among other
things) `ordInfOfPair A B ≥ ordInfOfPair A' B'`, i.e. the numerator's pole at
infinity is no worse than the denominator's.

For `z = toPair H A B / toPair H A' B' ∈ LPairCarrier x₁ x₂`, non-constant,
the pole bound at each affine point caps the total affine pole degree of `z`
at exactly 2 (one at `x₁`, one at `x₂`, or a double pole if `x₁ = x₂`). Two
routes from here, in increasing order of "already available in this repo":

### Route A (recommended): direct degree-counting on `A(x) + B(x)y`

1. **`B' = 0` is forced.** If `B' ≠ 0`, the denominator `toPair H A' B'` has a
   pole at infinity of order (in the `ordInfOfPair` convention)
   `2·deg B' + 5 ≥ 5` — an *odd* multiple of the "half-integer" unit, which
   cannot be cancelled by any affine pole pattern that is a sum of two
   *order-≤1* contributions (`x₁`, `x₂` contribute total affine pole degree
   `≤ 2`, an even, small number in the same units — this needs the precise
   parity/degree bookkeeping made precise, see Lemma 1 below). This is the
   scoped-down replacement for "z has degree exactly 2 as a map to P¹, so a
   pole at infinity of order ≥ 5 is impossible" — proved by direct degree
   arithmetic on `ordInfOfPair`, not by an abstract ramification count.
2. **With `B' = 0`,** `z = (A(x) + B(x)y) / A'(x)` for some `A(x), B(x),
   A'(x) ∈ k[X]`. `z`'s pole divisor is bounded by `(x₁)+(x₂)`; comparing
   `y`'s own pole/zero structure (`y² = f(x)`, `f` squarefree of degree 5)
   against `B(x)y/A'(x)`'s contribution forces `B = 0` too (a similar
   parity/degree argument: `y` contributes "half-integer" pole orders at
   infinity that can't be cancelled or matched by the low-degree affine
   bound), reducing `z` to a **pure rational function of `x` alone**,
   `z = A(x)/A'(x)`.
3. **`z = A(x)/A'(x)` with total pole degree `≤ 2` forces `deg A, deg A' ≤
   1`** directly from `ordInfOfPair`'s formula (`2·deg A' ≤ 2` when `B'=0`,
   after step 1's argument pins the *only* pole contribution to be at
   infinity-plus-affine in a controlled way — precise statement in Lemma 3
   below). A degree-≤1-over-degree-≤1 rational function of `x` is constant
   unless it has a genuine simple pole; matching its pole set against
   `{x₁,x₂}` (both affine, both order-≤1) directly, via the *already-proved*
   `ordAt_linX_eq` (three-way case split on `Q.X = a` and `Q.Y = 0`,
   `HyperellipticClassProof.lean:1031`), shows: **the only way `A(x)/A'(x)` (a
   Möbius transform of `x` itself) has pole divisor `{x₁,x₂}` supported on two
   distinct affine points rather than a double pole at one Weierstrass point is
   if `x₁, x₂` are *both* preimages of the same value under `x`**, i.e.
   `{x₁,x₂}` is a fiber of the coordinate function `x`. But `x`'s fibers are
   exactly `{Q, ιQ}` pairs (`ordAt_linX_eq`'s case split: `Q.Y=0` gives a
   double pole at one Weierstrass point, `Q.Y≠0` gives a simple pole shared
   with `ιQ`) — so `x₂ = ι x₁`, contradicting `hne`.

This whole argument stays inside `k[X]`-degree bookkeeping plus the
*already-proved* `ordAt_linX_eq`. No new "ramification" notion, no Möbius
existence argument, no Riemann–Hurwitz citation — genus 2 enters only through
`deg f = 5` (`hdeg`), exactly as everywhere else in this project.

### Route B (fallback, more work, avoid unless Route A stalls)

Reuse `UniqueDegree2MapRiemannHurwitz.lean`'s `IsDegree2Map`/ramification
scaffolding but *only* for the specific pair `(x₁, x₂)` at hand, never
generalizing to "every degree-2 map". This still needs
`card_ramification_eq_six`-style counting or an equivalent, and is why it's
listed as fallback: it inherits more of that file's hard `sorry`s than Route A
does. Not attempted in the new file below; flagged here only so a future
session doesn't have to rediscover it's the worse option.

## What is explicitly *not* being proved (correctly out of scope)

* **`finrank_L_canonical`** (`ℓ(K) = 2` and its qualitative half,
  `IsOnlyFibersInCanonicalClass`) is a *second*, separate hard theorem in
  `RiemannRochGenus2.lean`, also `sorry`'d, needed for the `x₂ = ιx₁` branch of
  `sidonDichotomy_of_riemannRoch`. It is **not** addressed by this scoping
  pass or the new file below — a genuinely different computation (a
  2-dimensional space spanned by `{1, x}`, not a 1-dimensional
  "collapse to constant" argument), left for a future session. Don't confuse
  "P1+P2 irreducible" (this note's target) with "ℓ(K)=2" (untouched).
* **General classification of degree-2 maps up to Möbius transform** — not
  proved, not needed. `UniqueDegree2MapRiemannHurwitz.lean` can stay as
  unfinished scaffolding; nothing in the new file depends on it.
* **The upstream Dedekind-domain `sorry`s** already flagged in
  `PrincipalDivisors.lean`/`PrincipalDivisorsDedekind.lean` are untouched, as
  always — `finrank_L_pair`'s statement is conditional on
  `[IsDedekindDomain (CoordinateRing H)]`, same ambient hypothesis as
  everywhere else.

## Recommended next step

Attack Route A's three lemmas in `LPairFinrankOne.lean` (new file, drafted
alongside this note), in order of expected difficulty (easiest first, per
project convention):

1. **Lemma 1** (`B' = 0` forced) — pure `ordInfOfPair`-arithmetic, no new
   concepts; probably the easiest of the three once the exact inequality
   chain is written out.
2. **Lemma 2** (`B = 0` forced, given `B' = 0`) — same flavor, one level up
   (comparing `y`'s contribution against the bound).
3. **Lemma 3** (pure-rational-function pole matching via `ordAt_linX_eq`) —
   the one genuinely new piece of reasoning, but it reuses `ordAt_linX_eq`
   rather than inventing ramification theory, so it should be a `k[X]`-level
   argument about when `A(x)/A'(x)` (degree ≤ 1 numerator/denominator) has a
   prescribed two-point pole divisor.

Each is stated as its own named theorem in the new file with a `sorry`, not
folded into one monolithic proof, per your stated preference — easiest first,
skeleton for the hard one.
