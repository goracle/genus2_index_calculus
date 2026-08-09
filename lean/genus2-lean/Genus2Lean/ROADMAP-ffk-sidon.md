# Closing `SidonDichotomy`: a genus-2 Riemann–Roch roadmap

## Where things stand today

`FFKSidon.lean` states the FFK dichotomy for `s : C(k) → J` in two pieces:

* **Easy direction** (`sum_eq_of_dichotomy`): dichotomy ⟹ sum equation. Fully
  proved, unconditionally, gated only on `D.HyperellipticClass`.
* **`D.HyperellipticClass`** itself, for the concrete `D :=
  principalDivisorData H hdeg`: fully proved with no `sorry`, in
  `HyperellipticClassProof.lean`'s `hyperellipticClass_principalDivisorData`,
  by exhibiting `(x₁)+(ιx₁)-(x₃)-(ιx₃)` as a `divToPairRatio` generator of
  the (correctly widened, matching-`ordInfOfPair`) `principalSubgroup`. This
  was previously believed to be gated on a further `sorry`; it is not — the
  widening in `PrincipalDivisorSubgroup.lean` already closes it, modulo
  `lake build` verification and the upstream Dedekind-domain `sorry`s in
  `PrincipalDivisors.lean` / `PrincipalDivisorsDedekind.lean`.
* **Hard direction** (`D.SidonDichotomy`, forward: sum equation ⟹
  dichotomy): entirely unstarted. This is the actual Forey–Fresán–Kowalski
  content and is a genus-2-specific Riemann–Roch fact. Nothing in the repo
  builds `L(D)` for a divisor `D` supported at two *affine* points (only
  `RiemannRochSpaceInf`, for divisors at infinity, exists), and nothing
  builds a canonical divisor. This file is that gap, made precise.

## The mathematical content

**Target.** For `D := principalDivisorData H hdeg` (deg-5 case), prove
`D.SidonDichotomy`: if `s x₁ + s x₂ = s x₃ + s x₄` then
`{x₁,x₂}={x₃,x₄} ∨ (x₂ = ιx₁ ∧ x₄ = ιx₃)`.

Equivalently (via `s_add_s_eq_s_add_s_iff`): `(x₁)+(x₂) ~ (x₃)+(x₄)` (their
difference lies in `principalSubgroup H hdeg`) forces the same dichotomy.

**Proof, standard for hyperelliptic genus 2:**

1. `ℓ(D) - ℓ(K-D) = deg D + 1 - g = 1` (Riemann–Roch), `D := (x₁)+(x₂)`,
   `K` a canonical divisor (`deg K = 2g-2 = 2`).
2. On a hyperelliptic curve `|K|` is exactly the set of fibers of the
   degree-2 map to `P¹`: every effective canonical divisor is `(x)+(ιx)`
   for a unique `x` up to the swap, and conversely. (`ℓ(K) = g = 2` here.)
3. **Case `x₂ ≠ ιx₁`:** `K ≠ D` as divisor classes' effective
   representatives don't coincide at `D`, so `ℓ(K-D) = 0`
   (`K-D` has no effective divisor in its class — degree 0, and the only
   degree-0 effective divisor is `0`, which would need `D` itself to be `K`),
   giving `ℓ(D) = 1`: `D` is the *only* effective divisor in its own linear
   equivalence class. So `(x₃)+(x₄) ~ D` and both effective forces
   `(x₃)+(x₄) = (x₁)+(x₂)` as divisors, i.e. `{x₁,x₂}={x₃,x₄}`.
4. **Case `x₂ = ιx₁`:** `D ~ K` and `|K|`'s effective divisors are exactly
   the fibers (step 2), so `(x₃)+(x₄) ~ D ~ K` forces `(x₃)+(x₄)` to be a
   fiber too: `x₄ = ιx₃`.

Steps 1 and 2 are the two genuinely hard pieces. Step 2 in particular is
*not* a generic Riemann–Roch corollary — it is the specific fact that makes
a curve hyperelliptic in the first place (the canonical map factors through
the degree-2 map to `P¹`), and for genus 2 it degenerates further: **every**
canonical divisor is hyperelliptic, because `deg K = 2` already forces it
(there is no room for a "non-fiber" effective canonical divisor once
`ℓ(K)=2` pins the dimension). This is genus-2-specific: for `g ≥ 3`
hyperelliptic curves, `|K|` still consists only of hyperelliptic fibers,
but `deg K = 2g-2 > 2`, so an effective canonical divisor is a *sum* of
several fibers, not a single one — the FFK dichotomy's two-term shape is
special to `g = 2`.

## Concrete construction needed: `L(D)` for `D = (x₁)+(x₂)`, deg-5 model

Mirrors `RiemannRochSpaceInf`'s existing pole-order convention but at finite
points instead of infinity, and must still bound the pole at infinity since
elements of `Frac(CoordinateRing H)` are otherwise unconstrained there.

```
L(x₁ + x₂) := { toPair H A B / toPair H A' B' | ... } ⊆ Frac(CoordinateRing H)
```
stated via numerator/denominator pairs `(A,B,A',B')` with:
* `ordInfOfPair A B = ordInfOfPair A' B'` (no pole at infinity — reuses
  the exact `divToPairRatio` matching condition already built),
* `ordAt P A B - ordAt P A' B' ≥ 0` for `P ∉ {x₁, x₂}`,
* `ordAt x₁ A B - ordAt x₁ A' B' ≥ -1`, likewise at `x₂`.

This is a `k`-submodule of `Frac(CoordinateRing H)` (sums of such ratios
need a common-denominator argument — mechanical but not `rfl`, similar in
shape to `RiemannRochSpaceInf.add_mem'`). Its dimension is `ℓ(D)`.

Two theorems to prove about it, at genus-2-specific dimension values:

* **`ℓ((x₁)+(x₂)) = 1` when `x₂ ≠ ιx₁`.** The "only constants" case:
  `L(D)` collapses to the constant functions `k · 1`. Proof shape:
  suppose `h ∈ L(D)` non-constant; `h` has a pole (order ≤1) at `x₁` and/or
  `x₂` and no other poles (including infinity) — but a nonconstant rational
  function of pole-degree ≤ 2 on `C` gives a degree-≤2 map `C → P¹`, and a
  genus-2 curve's only degree-2 map to `P¹` (up to `PGL₂`) is the
  hyperelliptic one — forcing `h`'s pole divisor to be `x + ιx` for some
  `x`, degree exactly 2 with *both* points appearing, contradicting
  `x₂ ≠ ιx₁` unless `h`'s poles are literally `{x₁,x₂}` with `x₂=ιx₁`. This
  is the step that most needs the curve's hyperelliptic structure, not
  generic Riemann–Roch, and is the crux of the whole file.

* **`ℓ(K) = 2` and effective canonical divisors are exactly the fibers.**
  Needs an explicit canonical divisor. For the deg-5 affine model the
  standard differential is `dx/(2y)` (holomorphic everywhere finite,
  vanishing to the right order at infinity for `g=2`); `K := div(dx/(2y))`.
  `L(K)` should be spanned by `{1, x}` (the two holomorphic differentials
  `dx/(2y)`, `x·dx/(2y)` correspond to `1, x ∈ L(K)` under the standard
  identification) — this is the concrete genus-2 fact that needs checking
  against the deg-5 pole-order convention already fixed by `inLInf`.

## Sequencing recommendation

1. Build `L(x₁+x₂)` as a `Submodule k (FractionRing (CoordinateRing H))`
   (needs `[IsDomain (CoordinateRing H)]`, already assumed elsewhere).
   Mechanical, similar cost to `RiemannRochSpaceInf`.
2. State (do not yet prove) `finrank_L_pair` and `finrank_L_canonical` as
   named `sorry`s, exactly as `PrincipalDivisors.lean` does for its own
   hard steps — get the *statement* of `SidonDichotomy`'s proof assembled
   and typechecking against these two sorries first, so the dependency
   shape is locked in before spending effort on the hard steps themselves.
3. Prove `finrank_L_canonical` first — it's a single fixed divisor `K`,
   not a family over `x₁,x₂`, so there's less to quantify over.
4. Prove `finrank_L_pair`'s `≤ 1` direction (harder: `≥ 1` is free, `1` is
   always in `L(D)`) — this is where the "genus 2 ⟹ only one degree-2 map
   to P¹" fact has to be pinned down precisely, likely via the norm/trace
   machinery already in `HyperellipticFunctionField.lean`
   (`toPair_satisfies_charpoly`) applied to the hypothetical extra function.
5. Assemble `sidonDichotomy_of_riemannRoch` from steps 1–4 following the
   4-step case split above; wire into `FFKSidon.lean` as the new proof of
   `(principalDivisorData H hdeg).SidonDichotomy`, replacing the current
   axiom-style packaging.

Steps 1–2 are a session's work. Step 3 is comparable in difficulty to the
already-completed `ordAt_linX_eq` (a genuine local computation, but a
single one). Step 4 is the hardest step in the whole project remaining
after the Dedekind-domain sorries — comparable to or harder than
`finrank_quotient_pointIdeal_pow` (§4.2 in `PrincipalDivisors.lean`).
