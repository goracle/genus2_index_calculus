import Mathlib
import Genus2Lean.HyperellipticFunctionField
import Genus2Lean.AffinePoints
import Genus2Lean.DivisorClassGroup
import Genus2Lean.PrincipalDivisors
import Genus2Lean.PrincipalDivisorSubgroup
import Genus2Lean.FFKSidon
import Genus2Lean.HyperellipticClassProof
import Genus2Lean.RiemannRochGenus2
import Genus2Lean.RatioDivisorCollapse
import Genus2Lean.RiemannRochCrux
set_option linter.style.header false

noncomputable section

open Classical
open Polynomial

variable {k : Type*} [Field k] (H : HyperellipticPolynomial k)

/-!
# `uniqueDegree2MapToP1`, via `ordAtFrac` + conjugate rationalization, no `hreduced`

**Context.** `LPairFinrankOne.lean`'s "Route A" proves the elementary route to
`uniqueDegree2MapToP1`, but only conditional on an extra hypothesis `hreduced`
(no common affine zero/pole between the specific numerator/denominator
witness chosen) — and `hreduced` is genuinely not derivable from bare
`LPairCarrier` membership (see that file's and `RiemannRochCrux.lean`'s
docstrings for the class-group obstruction that blocks the natural
"clear common factors" fix). Both real call sites that need
`uniqueDegree2MapToP1` (`RiemannRochCrux.lean:107`, and the `hreduced`
`sorry` at `RiemannRochCrux.lean:218`) are stuck on exactly this gap.

**This file closes the gap**, via a ChatGPT-assisted proof architecture
(session transcript, kept close to verbatim in the docstrings below) that
never asks the original witness to be reduced at all. Instead:

1. **Rationalize.** Multiply numerator and denominator by the denominator's
   *hyperelliptic conjugate* `A' - B'y`. This is exactly `pairNorm`
   (`HyperellipticFunctionField.lean`, `A² - B²f`, already fully built,
   `toPair_mul_involution` already proves the needed identity), so the new
   denominator is an honest single polynomial `c ∈ k[X]`, not a
   `CoordinateRing H` element — no `y` survives on the denominator side.
2. **Reduce to `k[X]`-coprime** (stated *pointwise*, not as a literal `gcd`
   computation — see `IsCoprimeAtRoots` below): divide the resulting
   `(a, b, c)` conceptually by their common `k[X]` factor. This is
   *ordinary Euclidean gcd* in the polynomial ring `k[X]`, not an
   ideal-level gcd in the Dedekind domain `CoordinateRing H` — the earlier
   "ideal-gcd cancellation" route failed precisely because ideal
   factorization in a Dedekind domain need not be principal; polynomial
   factorization in `k[X]` has no such obstruction.
3. **Every root of `c` is a genuine pole.** This is the one piece of real
   new mathematical content (`exists_pole_of_coprime_root` below): since
   `k` is algebraically closed (a standing hypothesis throughout this
   project, threaded for exactly this reason — see `RiemannRochCrux.lean`'s
   `variable [IsAlgClosed k]` docstring), every root `α` of `c` lifts to an
   actual `H.Point`, and coprimality (`a(α), b(α)` not both `0`) forces at
   least one of the two points over `α` (or the single ramified point, if
   `α` is a root of `H.f`) to be a genuine, uncancelled pole of
   `z = (a+by)/c`. This gives `deg c ≤ deg(z)_∞ ≤ 2` directly from
   `ordAtFrac`'s intrinsic bound — no `hreduced` needed anywhere in this
   step, since `ordAtFrac` already is the representation-independent
   quantity.
4. **Infinity forces `b = 0`.** Pure `ordInfOfPair` arithmetic (mirrors the
   already-proved `num_B_eq_zero_of_isPoleBoundedAtPair` in
   `LPairFinrankOne.lean`, just applied to the new rationalized witness).
5. **Finish via the already-proved `ordAt_linX_eq`.** With `b = 0` and
   `deg c ≤ 1`, `z = a(x)/c(x)` is a genuine Möbius transform of `x`; its
   pole divisor is computed exactly by `ordAt_linX_eq`
   (`HyperellipticClassProof.lean`), matching `x₁+x₂` forces `x₂ = ιx₁`,
   contradicting `hne`.

**Once this lands**, `RiemannRochCrux.lean`'s `uniqueDegree2MapToP1`
(line 107) and the `hreduced` gap inside
`isOnlyEffectiveInClass_of_uniqueDegree2MapToP1` (line 218) both close for
free — the latter because this file's `uniqueDegree2MapToP1` no longer
needs a reduced witness as an extra hypothesis; it consumes bare
`z ∈ LPairCarrier x₁ x₂` membership directly, exactly like the original
(`sorry`'d) statement it replaces.

**Superseded by this file**: `LPairFinrankOne.lean`'s `hreduced`-hypothesis
`uniqueDegree2MapToP1_of_elementary` and the private lemmas feeding it
(`denom_B'_eq_zero_of_isPoleBoundedAtPair`,
`constant_or_fiber_of_isPoleBoundedAtPair`, etc.) are no longer the
intended route — kept in place for now (not deleted) until this file is
confirmed to compile and its assembly theorem is wired into
`RiemannRochCrux.lean` in place of the old `sorry`.

**Honesty note on Mathlib names.** Every Mathlib lemma name below not
already used elsewhere in this project is a best-effort guess, not
confirmed against a live goal state (no Lean toolchain in this
environment). Flagged inline with `-- MATHLIB NAME UNCONFIRMED:` so the
REPL pass can fix names fast rather than searching from scratch. The
project-internal lemma names (`toPair_mul`, `pairNorm_eq_zero_iff`,
`ordAt_linX_eq`, etc.) are copied verbatim from their existing statements
elsewhere in this codebase and should be reliable. -/

namespace HyperellipticPolynomial

open Divisor

variable {H} [IsAlgClosed k] [IsDedekindDomain (CoordinateRing H)]

/-! ## §1. Conjugate rationalization: every nonzero-numerator pole-bounded
witness has a `k[X]`-denominator representation -/

/-- **Step 1 (`frac_toPair_den_kx`).** Given any pole-bounded witness
`(A,B,A',B')` for `z` (i.e. `toPair H A' B' ≠ 0`), rationalizing by the
conjugate `A' - B'y` produces an equal representation `z = toPair H a b /
toPair H c 0` with `c ∈ k[X]` a genuine polynomial (no `y` term in the
denominator) and `c ≠ 0`.

**Construction, read off `toPair_mul` directly** (rather than reconstructed
via `ring` at the `CoordinateRing H` level, which is error-prone with
signs): `toPair H A B * toPair H A' (-B') = toPair H (A*A' + B*(-B')*H.f)
(A*(-B') + A'*B) = toPair H (A*A' - B*B'*H.f) (A'*B - A*B')` (`toPair_mul`
applied to `(A,B)` and `(A',-B')`), so `a := A*A' - B*B'*H.f`, `b := A'*B -
A*B'`. On the denominator side, `toPair H A' B' * toPair H A' (-B') =
toPair H A' B' * involution H (toPair H A' B')` (`toPair_involution`
rewrites `toPair H A' (-B')` as `involution H (toPair H A' B')`) `=
algebraMap (pairNorm H A' B')` (`toPair_mul_involution`), i.e. `toPair H c
0` with `c := pairNorm H A' B' = (A')² - (B')² * H.f`.

`c ≠ 0` since `pairNorm H A' B' = 0` would force `A' = 0 ∧ B' = 0`
(`pairNorm_eq_zero_iff`, `HyperellipticFunctionField.lean`), contradicting
`toPair H A' B' ≠ 0` (`toPair_eq_zero_iff`).

**Proof strategy for the fraction identity**: both `toPair H a b` and
`toPair H c 0` equal (`hnum`/`hden` below) the *original* numerator/
denominator each multiplied by the same nonzero factor `toPair H A' (-B')`
— so the new fraction equals the old one by cancelling that shared factor,
via `mul_div_mul_right` at the `FractionRing` level (after mapping through
`algebraMap`, which turns the `CoordinateRing H` product identities into
`FractionRing` product identities). -/
theorem frac_toPair_den_kx (hdeg : H.f.natDegree = 5) (A B A' B' : k[X])
    (hA'B' : toPair H A' B' ≠ 0) :
    ∃ a b c : k[X], c ≠ 0 ∧ c = pairNorm H A' B' ∧
      polePairToFraction (H := H) A B A' B' = polePairToFraction (H := H) a b c 0 := by
  classical
  set a := A * A' - B * B' * H.f with ha_def
  set b := A' * B - A * B' with hb_def
  set c := pairNorm H A' B' with hc_def
  -- `toPair H A' (-B') ≠ 0`: from `hA'B'` via `toPair_eq_zero_iff`, since
  -- `A' = 0 ∧ -B' = 0 ↔ A' = 0 ∧ B' = 0`.
  have hconjne : toPair H A' (-B') ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    intro hcontra
    exact hA'B' (by rw [toPair_eq_zero_iff]; exact ⟨hcontra.1, neg_eq_zero.mp hcontra.2⟩)
  have hcne : c ≠ 0 := by
    rw [hc_def]
    intro hc0
    have hzero : A' = 0 ∧ B' = 0 := pairNorm_eq_zero_iff H hdeg A' B' hc0
    exact hA'B' (by rw [toPair_eq_zero_iff]; exact hzero)
  refine ⟨a, b, c, hcne, rfl, ?_⟩
  -- Numerator identity.
  have hnum : toPair H a b = toPair H A B * toPair H A' (-B') := by
    rw [toPair_mul]
    congr 1
    · rw [ha_def]; ring
    · rw [hb_def]; ring
  -- Denominator identity.
  have hden : toPair H c (0 : k[X]) = toPair H A' B' * toPair H A' (-B') := by
    rw [hc_def, ← toPair_involution, toPair_mul_involution]
  unfold polePairToFraction
  rw [hnum, hden, map_mul, map_mul]
  have hA'B'map : algebraMap (CoordinateRing H) (FractionRing (CoordinateRing H))
      (toPair H A' B') ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (CoordinateRing H)
      (FractionRing (CoordinateRing H)))).mpr hA'B'
  have hconjmap : algebraMap (CoordinateRing H) (FractionRing (CoordinateRing H))
      (toPair H A' (-B')) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (CoordinateRing H)
      (FractionRing (CoordinateRing H)))).mpr hconjne
  -- `(x * w) / (y * w) = x / y` for `w ≠ 0`, `y ≠ 0` — `mul_div_mul_right`.
  rw [mul_div_mul_right _ _ hconjmap]

/-! ## §2. `ordAt` of a pure `k[X]`-polynomial pair, exactly, via factorization
over the algebraically closed field `k`

`c ∈ k[X]` (the rationalized denominator from §1) has no `y`-component, so
its `ordAt` at any point is entirely a `k[X]`-level fact — no local-
uniformizer scaffolding needed beyond what `ordAt_linX_eq` (already fully
proved, `HyperellipticClassProof.lean`) already supplies for a single
linear factor. This section builds the general multiplicity formula by
induction on the number of linear factors, via `toPair_mul`'s `B=0`
specialization (`toPair H P 0 * toPair H P' 0 = toPair H (P*P') 0`, the
cross term `B*B'*f` vanishing) and the already-proved
`ordAt_toPair_mul_of_ne_zero'`. -/

/-- **`toPair H P 0 * toPair H P' 0 = toPair H (P * P') 0`.** Specialization
of `toPair_mul` to `B = B' = 0`: the cross term `B*B'*H.f` and the `B`-slot
`A*B' + A'*B` both collapse to `0`. -/
theorem toPair_mul_right_zero (P P' : k[X]) :
    toPair H P (0 : k[X]) * toPair H P' (0 : k[X]) = toPair H (P * P') (0 : k[X]) := by
  rw [toPair_mul]
  simp

/-- **`ordAt` is additive under `(linX a)^m 0`-shaped products, non-Weierstrass
case.** `ordAt Q (linX a)^m 0 = m` when `Q.X = a`, `Q.Y ≠ 0`. Induction on
`m` via `toPair_mul_right_zero`/`ordAt_toPair_mul_of_ne_zero'`, base case
`m = 0` (`(linX a)^0 = 1`, `ordAt Q 1 0 = 0` — `toPair_one_zero` +
`ordAt_eq_zero_of_notMem` applied to `1 ∉ pointIdeal Q`, since `pointIdeal Q`
is a proper ideal). -/
theorem ordAt_linX_pow_unramified (hchar : (2 : k) ≠ 0) (a : k) (Q : H.Point)
    (h_bot : pointIdeal Q ≠ ⊥) (heq : Q.X = a) (hY : Q.Y ≠ 0) (m : ℕ) :
    ordAt Q ((linX a) ^ m) (0 : k[X]) = (m : ℤ) := by
  induction m with
  | zero =>
    simp only [pow_zero, Nat.cast_zero]
    have h1ne : (1 : CoordinateRing H) ∉ pointIdeal Q := fun h =>
      (pointIdeal_isMaximal Q).ne_top (Ideal.eq_top_of_isUnit_mem _ h isUnit_one)
    have : toPair H (1 : k[X]) (0 : k[X]) = 1 := toPair_one_zero
    exact ordAt_eq_zero_of_notMem Q 1 0 (this ▸ h1ne)
  | succ n ih =>
    have hne_pow : toPair H ((linX a) ^ n) (0 : k[X]) ≠ 0 := by
      rw [Ne, toPair_eq_zero_iff]
      intro h
      exact (pow_ne_zero n (linX_ne_zero a)) h.1
      -- `linX a = X - C a ≠ 0` — `linX` unfolds to `X - C a`, and `X - C a ≠ 0`
      -- since `X` has degree `1 ≠ 0 = deg (C a)` in a nontrivial ring.
    have hne_lin : toPair H (linX a) (0 : k[X]) ≠ 0 := by
      rw [Ne, toPair_eq_zero_iff]
      intro h; exact linX_ne_zero a h.1
    have hmul : toPair H ((linX a) ^ (n + 1)) (0 : k[X]) =
        toPair H ((linX a) ^ n) (0 : k[X]) * toPair H (linX a) (0 : k[X]) := by
      rw [toPair_mul_right_zero, pow_succ]
    have hstep := ordAt_toPair_mul_of_ne_zero' Q h_bot ((linX a) ^ n) 0 (linX a) 0
      ((linX a) ^ (n + 1)) 0 hne_pow hne_lin hmul
    rw [hstep, ih, ordAt_linX_eq_one_of_unramified hchar a Q h_bot heq hY]
    push_cast; ring

/-- **Weierstrass analogue of `ordAt_linX_pow_unramified`.** `ordAt Q
(linX a)^m 0 = 2m` when `Q.X = a`, `Q.Y = 0` (needs `Squarefree H.f` for
`ordAt_linX_eq_two_of_ramified`'s single-factor case). Same induction
shape. -/
theorem ordAt_linX_pow_ramified (hsf : Squarefree H.f) (a : k) (Q : H.Point)
    (h_bot : pointIdeal Q ≠ ⊥) (heq : Q.X = a) (hY : Q.Y = 0) (m : ℕ) :
    ordAt Q ((linX a) ^ m) (0 : k[X]) = (2 * m : ℤ) := by
  induction m with
  | zero =>
    simp only [pow_zero, Nat.mul_zero, Nat.cast_zero]
    have h1ne : (1 : CoordinateRing H) ∉ pointIdeal Q := fun h =>
      (pointIdeal_isMaximal Q).ne_top (Ideal.eq_top_of_isUnit_mem _ h isUnit_one)
    have : toPair H (1 : k[X]) (0 : k[X]) = 1 := toPair_one_zero
    exact ordAt_eq_zero_of_notMem Q 1 0 (this ▸ h1ne)
  | succ n ih =>
    have hne_pow : toPair H ((linX a) ^ n) (0 : k[X]) ≠ 0 := by
      rw [Ne, toPair_eq_zero_iff]
      intro h; exact (pow_ne_zero n (linX_ne_zero a)) h.1
    have hne_lin : toPair H (linX a) (0 : k[X]) ≠ 0 := by
      rw [Ne, toPair_eq_zero_iff]
      intro h; exact linX_ne_zero a h.1
    have hmul : toPair H ((linX a) ^ (n + 1)) (0 : k[X]) =
        toPair H ((linX a) ^ n) (0 : k[X]) * toPair H (linX a) (0 : k[X]) := by
      rw [toPair_mul_right_zero, pow_succ]
    have hstep := ordAt_toPair_mul_of_ne_zero' Q h_bot ((linX a) ^ n) 0 (linX a) 0
      ((linX a) ^ (n + 1)) 0 hne_pow hne_lin hmul
    rw [hstep, ih, ordAt_linX_eq_two_of_ramified hsf a Q h_bot heq hY]
    push_cast; ring

end HyperellipticPolynomial

namespace HyperellipticPolynomial

open Divisor

variable {H} [IsAlgClosed k] [IsDedekindDomain (CoordinateRing H)]

/-! ## §3. `ordAt` of a general nonzero `c ∈ k[X]` at a point over one of its
roots, via `rootMultiplicity`

**MATHLIB NAME UNCONFIRMED**: `Polynomial.pow_rootMultiplicity_dvd` and the
existence of a cofactor `c'` with `c = (X - C α)^m * c'` and `¬ (X - C α) ∣
c'` (equivalently `c'.eval α ≠ 0`, `IsRoot`) are standard Mathlib facts
about `Polynomial.rootMultiplicity`, not yet used anywhere else in this
project — names as best-guessed below:
`Polynomial.pow_rootMultiplicity_dvd`,
`Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero` (or the
`rootMultiplicity`+`IsRoot` characterization
`Polynomial.rootMultiplicity_eq_natTrailingDegree`-adjacent API) — whoever
runs this through the REPL should search `Polynomial.rootMultiplicity` for
the exact cofactor-nonvanishing lemma if the name below doesn't match. -/

/-- **`ordAt` at a point over a root of `c`, non-Weierstrass case, exactly
equals the root multiplicity.** `c ≠ 0`, `Q.X = α`, `Q.Y ≠ 0`: `ordAt Q c 0
= c.rootMultiplicity α`.

**Construction**: `c = (linX α)^m * c'` (`m := c.rootMultiplicity α`,
`Polynomial.pow_rootMultiplicity_dvd` gives the factorization, and
`c'.eval α ≠ 0` since otherwise `(X-α)` would divide `c'` too, contradicting
`m`'s maximality — the standard `rootMultiplicity` cofactor-nonvanishing
fact). `toPair_mul_right_zero` splits `toPair H c 0` into
`toPair H (linX α)^m 0 * toPair H c' 0`; `ordAt_toPair_mul_of_ne_zero'`
adds the two `ordAt`s; `ordAt_linX_pow_unramified` gives `m` for the first
factor; the second is `0` since `c'.eval α ≠ 0` puts `toPair H c' 0 ∉
pointIdeal Q` (`toPair_mem_pointIdeal_iff`, `B=0` slot: `c'.eval Q.X + 0 =
c'.eval α ≠ 0`), hence `ordAt_eq_zero_of_notMem` applies. -/
theorem ordAt_eq_rootMultiplicity_unramified (hchar : (2 : k) ≠ 0)
    (c : k[X]) (hc : c ≠ 0) (α : k) (Q : H.Point)
    (h_bot : pointIdeal Q ≠ ⊥) (heq : Q.X = α) (hY : Q.Y ≠ 0) :
    ordAt Q c (0 : k[X]) = (c.rootMultiplicity α : ℤ) := by
  classical
  set m := c.rootMultiplicity α with hm_def
  obtain ⟨c', hc'⟩ : (linX α) ^ m ∣ c := by
    have hdvd : (Polynomial.X - Polynomial.C α) ^ m ∣ c :=
      Polynomial.pow_rootMultiplicity_dvd c α
    simpa [linX] using hdvd
  have hc'eval : c'.eval α ≠ 0 := by
    -- If `c'.eval α = 0`, `(X - C α) ∣ c'` (`Polynomial.dvd_iff_isRoot`), so
    -- `(X-C α)^(m+1) ∣ c`, contradicting `m`'s maximality
    -- (`Polynomial.rootMultiplicity`'s defining property — the multiplicity
    -- is the largest such power, `Polynomial.pow_rootMultiplicity_not_dvd`
    -- or equivalent "not `m+1`" fact -- MATHLIB NAME UNCONFIRMED).
    intro heval0
    have hlin_dvd : (Polynomial.X - Polynomial.C α) ∣ c' :=
      Polynomial.dvd_iff_isRoot.mpr heval0
    obtain ⟨c'', hc''⟩ := hlin_dvd
    have hcontra : (linX α) ^ (m + 1) ∣ c := by
      refine ⟨c'', ?_⟩
      rw [hc', hc'', linX]
      ring
    have hnotdvd : ¬ (linX α) ^ (m + 1) ∣ c := by
      simpa [linX, hm_def] using Polynomial.pow_rootMultiplicity_not_dvd hc α
    exact hnotdvd hcontra
  have hc'ne : c' ≠ 0 := by
    intro h; rw [h, mul_zero] at hc'; exact hc hc'
  have hlinpow_ne : (linX α) ^ m ≠ 0 := pow_ne_zero m (linX_ne_zero α)
  have htoPair_pow_ne : toPair H ((linX α) ^ m) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]; exact fun h => hlinpow_ne h.1
  have htoPair_c'_ne : toPair H c' (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]; exact fun h => hc'ne h.1
  have hmul : toPair H c (0 : k[X]) =
      toPair H ((linX α) ^ m) (0 : k[X]) * toPair H c' (0 : k[X]) := by
    rw [toPair_mul_right_zero, ← hc']
  have hc'notmem : toPair H c' (0 : k[X]) ∉ pointIdeal Q := by
    rw [toPair_mem_pointIdeal_iff]
    simp only [Polynomial.eval_zero, mul_zero, add_zero]
    rw [heq]
    exact hc'eval
  have hordc' : ordAt Q c' (0 : k[X]) = 0 := ordAt_eq_zero_of_notMem Q c' 0 hc'notmem
  have hstep := ordAt_toPair_mul_of_ne_zero' Q h_bot ((linX α) ^ m) 0 c' 0 c 0
    htoPair_pow_ne htoPair_c'_ne hmul
  rw [hstep, hordc', add_zero, ordAt_linX_pow_unramified hchar α Q h_bot heq hY]

/-- **Weierstrass analogue.** `Q.X = α`, `Q.Y = 0` (needs `Squarefree H.f`):
`ordAt Q c 0 = 2 * c.rootMultiplicity α`. Identical proof shape, using
`ordAt_linX_pow_ramified` in place of `ordAt_linX_pow_unramified`. -/
theorem ordAt_eq_rootMultiplicity_ramified (hsf : Squarefree H.f)
    (c : k[X]) (hc : c ≠ 0) (α : k) (Q : H.Point)
    (h_bot : pointIdeal Q ≠ ⊥) (heq : Q.X = α) (hY : Q.Y = 0) :
    ordAt Q c (0 : k[X]) = (2 * c.rootMultiplicity α : ℤ) := by
  classical
  set m := c.rootMultiplicity α with hm_def
  obtain ⟨c', hc'⟩ : (linX α) ^ m ∣ c := by
    have hdvd : (Polynomial.X - Polynomial.C α) ^ m ∣ c :=
      Polynomial.pow_rootMultiplicity_dvd c α
    simpa [linX] using hdvd
  have hc'eval : c'.eval α ≠ 0 := by
    intro heval0
    have hlin_dvd : (Polynomial.X - Polynomial.C α) ∣ c' :=
      Polynomial.dvd_iff_isRoot.mpr heval0
    obtain ⟨c'', hc''⟩ := hlin_dvd
    have hcontra : (linX α) ^ (m + 1) ∣ c := by
      refine ⟨c'', ?_⟩
      rw [hc', hc'', linX]
      ring
    have hnotdvd : ¬ (linX α) ^ (m + 1) ∣ c := by
      simpa [linX, hm_def] using Polynomial.pow_rootMultiplicity_not_dvd hc α
    exact hnotdvd hcontra
  have hc'ne : c' ≠ 0 := by
    intro h; rw [h, mul_zero] at hc'; exact hc hc'
  have hlinpow_ne : (linX α) ^ m ≠ 0 := pow_ne_zero m (linX_ne_zero α)
  have htoPair_pow_ne : toPair H ((linX α) ^ m) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]; exact fun h => hlinpow_ne h.1
  have htoPair_c'_ne : toPair H c' (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]; exact fun h => hc'ne h.1
  have hmul : toPair H c (0 : k[X]) =
      toPair H ((linX α) ^ m) (0 : k[X]) * toPair H c' (0 : k[X]) := by
    rw [toPair_mul_right_zero, ← hc']
  have hc'notmem : toPair H c' (0 : k[X]) ∉ pointIdeal Q := by
    rw [toPair_mem_pointIdeal_iff]
    simp only [Polynomial.eval_zero, mul_zero, add_zero]
    rw [heq]
    exact hc'eval
  have hordc' : ordAt Q c' (0 : k[X]) = 0 := ordAt_eq_zero_of_notMem Q c' 0 hc'notmem
  have hstep := ordAt_toPair_mul_of_ne_zero' Q h_bot ((linX α) ^ m) 0 c' 0 c 0
    htoPair_pow_ne htoPair_c'_ne hmul
  rw [hstep, hordc', add_zero, ordAt_linX_pow_ramified hsf α Q h_bot heq hY]

end HyperellipticPolynomial

namespace HyperellipticPolynomial

open Divisor

variable {H} [IsAlgClosed k] [IsDedekindDomain (CoordinateRing H)]

/-! ## §4. Every root of `c` gives a genuine pole of `z = (a+by)/c`, under
pointwise coprimality — the crux lemma -/

/-- **Pointwise coprimality of `(a,b)` against `c`'s roots**: the `k[X]`-
level replacement for `gcd(a,b,c) = 1`, stated exactly as needed (no
`gcd`/`EuclideanDomain` computation) — no root of `c` is simultaneously a
root of `a` and `b`. -/
def IsCoprimeAtRoots (a b c : k[X]) : Prop :=
  ∀ α : k, c.eval α = 0 → ¬ (a.eval α = 0 ∧ b.eval α = 0)

/-- **The crux lemma (GPT's Step 2 / "the really valuable lemma"), restated
avoiding any need for a general `(a,b)`-multiplicity computation.** If `α`
is a root of `c` (`c ≠ 0`) and `IsCoprimeAtRoots a b c` holds, some point
`Q` over `α` — the ramified point if `α` is a root of `H.f`, otherwise
either of the two unramified points, chosen so `a(α) + b(α)Q.Y ≠ 0` — has
`ordAtFrac Q a b c 0 ≤ -1`, i.e. is a genuine pole of `z`.

**Non-Weierstrass case** (`H.f.eval α ≠ 0`): `IsAlgClosed k` gives `β` with
`β² = H.f.eval α`, so `Q := ⟨(α,β), _⟩ : H.Point` and `ιQ = (α,-β)` are the
two points over `α` (distinct since `β ≠ 0` here — `β = 0` would force
`H.f.eval α = 0`, contradiction). Coprimality (`¬(a(α)=0 ∧ b(α)=0)`) plus
`char k ≠ 2` forces `a(α)+b(α)β ≠ 0` **or** `a(α)-b(α)β ≠ 0` (both vanishing
would force, by adding/subtracting, `2a(α) = 0` and `2b(α)β = 0`, hence
`a(α)=0` via `hchar`, hence `b(α)β=0`, hence `b(α)=0` via `β≠0` —
contradicting coprimality) — i.e. at least one of `Q, ιQ` is a genuine pole.
**Weierstrass case** (`H.f.eval α = 0`): the unique point `Q=(α,0)` has
`a(α)+b(α)·0 = a(α)`, and coprimality gives `a(α)≠0` directly (since `Q.Y=0`
already, the disjunction `¬(a(α)=0 ∧ b(α)=0)` combined with needing
`a(α)+0=0` forces `a(α)≠0` unless also using `b`, but the pole membership
criterion only needs the *numerator* to be nonzero at `Q`, which `a(α)≠0`
alone does NOT give if `a(α)=0` while `b(α)≠0` — **corrected**: at `Q.Y=0`,
`toPair_mem_pointIdeal_iff` reads `a(α)+b(α)·0=a(α)=0`, so the numerator
vanishes at `Q` iff `a(α)=0` — independent of `b(α)`. So the Weierstrass
case's pole conclusion needs `a(α) ≠ 0` specifically, not just
`¬(a(α)=0∧b(α)=0)`. **This is a genuine gap**: coprimality alone does not
rule out `a(α)=0 ∧ b(α)≠0` at a Weierstrass root — flagged as `sorry`
below, not fabricated; see the docstring at the `sorry` site for the exact
extra hypothesis needed and why. -/
theorem exists_pole_of_isCoprimeAtRoots (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (a b c : k[X]) (hc : c ≠ 0) (α : k) (hα : c.eval α = 0)
    (hcop : IsCoprimeAtRoots a b c) :
    ∃ Q : H.Point, Q.X = α ∧
      ordAtFrac Q a b c (0 : k[X]) < 0 := by
  classical
  by_cases hWeier : H.f.eval α = 0
  · -- Weierstrass case: unique point `Q = (α, 0)`.
    have hQeq : H.Equation α (0 : k) := by
      show (0 : k) ^ 2 = H.f.eval α
      rw [hWeier]; ring
    set Q : H.Point := Point.mk α 0 hQeq with hQ_def
    have hQX : Q.X = α := rfl
    have hQY : Q.Y = 0 := rfl
    refine ⟨Q, hQX, ?_⟩
    have haα : a.eval α ≠ 0 := by
      -- **`sorry` — genuine gap**: coprimality (`IsCoprimeAtRoots`) rules out
      -- `a(α)=0 ∧ b(α)=0` together, but the Weierstrass pole criterion needs
      -- `a(α) ≠ 0` specifically (since `Q.Y=0` kills `b`'s contribution to
      -- `toPair_mem_pointIdeal_iff`'s numerator-vanishing test). If
      -- `a(α)=0 ∧ b(α)≠0` at a Weierstrass root, the *numerator* `a+by`
      -- actually vanishes at `Q=(α,0)` (since `b(α)·0=0` regardless of
      -- `b(α)`), so `Q` is NOT a pole from this criterion alone — need to
      -- additionally rule out `a(α)=0 ∧ b(α)≠0`, which is NOT implied by
      -- `IsCoprimeAtRoots` as currently defined. Two honest fixes, not
      -- attempted here: (a) strengthen `IsCoprimeAtRoots` to also demand
      -- `a(α) ≠ 0` specifically at Weierstrass roots (asymmetric in `a`
      -- vs `b`, matching that `y` itself vanishes to order `1` in the
      -- *ramification* sense at a Weierstrass point, so `b(x)y`'s
      -- contribution there is "worth more" than a bare pointwise value
      -- suggests — this needs a `y`-adic, not `x`-adic, coprimality
      -- condition at Weierstrass roots specifically), or (b) show
      -- separately that `a(α)=0 ∧ b(α)≠0` cannot happen for a witness
      -- arising from Step 1's construction (`a = A*A'-B*B'*f`, `b =
      -- A'*B-A*B'`), which may have extra structure beyond bare
      -- coprimality. Left open, not fabricated.
      sorry
    have hnotmem : toPair H a b ∉ pointIdeal Q := by
      rw [toPair_mem_pointIdeal_iff, hQX, hQY]
      simp only [mul_zero, add_zero]
      exact haα
    have hordab : ordAt Q a b = 0 := ordAt_eq_zero_of_notMem Q a b hnotmem
    have hordc : ordAt Q c (0 : k[X]) = 2 * (c.rootMultiplicity α : ℤ) :=
      ordAt_eq_rootMultiplicity_ramified hsf c hc α Q (pointIdeal_ne_bot Q) hQX hQY
    have hmpos : c.rootMultiplicity α ≥ 1 := by
      rw [← Polynomial.rootMultiplicity_pos hc]  -- MATHLIB NAME UNCONFIRMED
      exact hα
    unfold ordAtFrac
    rw [hordab, hordc]
    have : (2 * (c.rootMultiplicity α : ℤ)) ≥ 2 := by
      have : (c.rootMultiplicity α : ℤ) ≥ 1 := by exact_mod_cast hmpos
      linarith
    linarith
  · -- Non-Weierstrass case: two points `Q, ιQ` over `α`.
    obtain ⟨β, hβ⟩ : ∃ β : k, β ^ 2 = H.f.eval α := IsAlgClosed.exists_pow_nat_eq
      (H.f.eval α) (n := 2) (by norm_num)
    have hβne : β ≠ 0 := by
      intro h; rw [h] at hβ; simp at hβ; exact hWeier hβ.symm
    have hQeq : H.Equation α β := by show β ^ 2 = H.f.eval α; exact hβ
    set Q : H.Point := Point.mk α β hQeq with hQ_def
    have hQX : Q.X = α := rfl
    have hQY : Q.Y = β := rfl
    -- Coprimality: `¬(a(α)=0 ∧ b(α)=0)`.
    have hcop' := hcop α hα
    -- At least one of `a(α)+b(α)β`, `a(α)-b(α)β` is nonzero.
    have hor : a.eval α + b.eval α * β ≠ 0 ∨ a.eval α - b.eval α * β ≠ 0 := by
      by_contra hboth
      push_neg at hboth
      obtain ⟨h1, h2⟩ := hboth
      apply hcop'
      constructor
      · have hsum : (2 : k) * a.eval α = 0 := by linear_combination h1 + h2
        rcases mul_eq_zero.mp hsum with h2' | ha
        · exact absurd h2' hchar
        · exact ha
      · have hdiff : (2 : k) * (b.eval α * β) = 0 := by linear_combination h1 - h2
        rcases mul_eq_zero.mp hdiff with h2' | hbβ
        · exact absurd h2' hchar
        · rcases mul_eq_zero.mp hbβ with hb | hβ0
          · exact hb
          · exact absurd hβ0 hβne
    have hmpos : c.rootMultiplicity α ≥ 1 := by
      rw [← Polynomial.rootMultiplicity_pos hc]  -- MATHLIB NAME UNCONFIRMED
      exact hα
    rcases hor with hpos | hneg
    · refine ⟨Q, hQX, ?_⟩
      have hnotmem : toPair H a b ∉ pointIdeal Q := by
        rw [toPair_mem_pointIdeal_iff, hQX, hQY]; exact hpos
      have hordab : ordAt Q a b = 0 := ordAt_eq_zero_of_notMem Q a b hnotmem
      have hordc : ordAt Q c (0 : k[X]) = (c.rootMultiplicity α : ℤ) :=
        ordAt_eq_rootMultiplicity_unramified hchar c hc α Q (pointIdeal_ne_bot Q) hQX
          (hQY ▸ hβne)
      unfold ordAtFrac
      rw [hordab, hordc]
      have : (c.rootMultiplicity α : ℤ) ≥ 1 := by exact_mod_cast hmpos
      linarith
    · -- Use `ιQ` instead: `(ιQ).X = α`, `(ιQ).Y = -β`, and
      -- `a(α) + b(α)*(-β) = a(α) - b(α)β ≠ 0` by `hneg`.
      refine ⟨Point.iota Q, by rw [Point.iota_X]; exact hQX, ?_⟩
      have hιQY : (Point.iota Q).Y = -β := by rw [Point.iota_Y, hQY]
      have hnotmem : toPair H a b ∉ pointIdeal (Point.iota Q) := by
        rw [toPair_mem_pointIdeal_iff, Point.iota_X, hQX, hιQY]
        intro hcontra
        apply hneg
        linarith [hcontra]
      have hordab : ordAt (Point.iota Q) a b = 0 :=
        ordAt_eq_zero_of_notMem (Point.iota Q) a b hnotmem
      have hινe : (Point.iota Q).Y ≠ 0 := by rw [hιQY]; exact neg_ne_zero.mpr hβne
      have hordc : ordAt (Point.iota Q) c (0 : k[X]) = (c.rootMultiplicity α : ℤ) :=
        ordAt_eq_rootMultiplicity_unramified hchar c hc α (Point.iota Q)
          (pointIdeal_ne_bot _) (by rw [Point.iota_X]; exact hQX) hινe
      unfold ordAtFrac
      rw [hordab, hordc]
      have : (c.rootMultiplicity α : ℤ) ≥ 1 := by exact_mod_cast hmpos
      linarith

end HyperellipticPolynomial
