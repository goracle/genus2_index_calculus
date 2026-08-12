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
import Genus2Lean.LCanonicalElementary
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

variable {H} [IsDedekindDomain (CoordinateRing H)]

/-! ## §1. Conjugate rationalization: every nonzero-numerator pole-bounded
witness has a `k[X]`-denominator representation

**Non-closed-field note (rewiring pass):** this section's `[IsAlgClosed k]`
has been dropped — nothing here uses it. `frac_toPair_den_kx` is pure
`toPair`/`FractionRing` algebra: rationalizing by the conjugate `A' - B'y`
and cancelling the shared nonzero factor `toPair H A' (-B')` works over any
field `k`. -/

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
      a = A * A' - B * B' * H.f ∧ b = A' * B - A * B' ∧
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
  refine ⟨a, b, c, hcne, rfl, ha_def, hb_def, ?_⟩
  -- Numerator identity.
  have hnum : toPair H a b = toPair H A B * toPair H A' (-B') := by
    rw [toPair_mul]
    congr 1
    · rw [ha_def]; ring
    · rw [hb_def]; ring
  -- Denominator identity.
  have htoPair_right_zero : ∀ P : k[X],
      toPair H P (0 : k[X]) = algebraMap k[X] (CoordinateRing H) P := by
    intro P
    unfold toPair
    simp
  have hden : toPair H c (0 : k[X]) = toPair H A' B' * toPair H A' (-B') := by
    rw [hc_def, htoPair_right_zero, ← toPair_involution, toPair_mul_involution]
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
    simp only [pow_zero, Nat.cast_zero]
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

variable {H} [IsDedekindDomain (CoordinateRing H)]

/-! ## §3. `ordAt` of a general nonzero `c ∈ k[X]` at a point over one of its
roots, via `rootMultiplicity`

**Non-closed-field note (rewiring pass):** `[IsAlgClosed k]` dropped here
too — every theorem below takes the point `Q` (and the fact `Q.X = α`) as
an explicit hypothesis rather than manufacturing it from closedness, so
nothing in this section needs `k` algebraically closed.

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
    simp only [Polynomial.eval_zero, zero_mul, add_zero]
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
    simp only [Polynomial.eval_zero, zero_mul, add_zero]
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

/-! ## §4. Every root of `c` gives pole mass ≥ its multiplicity, under
pointwise coprimality — the crux lemma

**Resolved via ChatGPT consultation (this session).** The original "existence
of a pole" version of this lemma had a genuine gap in the Weierstrass case:
`IsCoprimeAtRoots` only rules out `a(α)=0 ∧ b(α)=0` together, and
`a(α)=0 ∧ b(α)≠0` at a Weierstrass root looked like it might not be a pole
(since `Q.Y=0` kills `b`'s contribution to the *pointwise value* test). The
resolution: it's still a pole, just of a different, still-uniform order. At a
Weierstrass point `Q=(α,0)`, `y` is the local uniformizer (`ordQ(y)=1`,
`ordQ(x-α)=2`, since `f` is squarefree so `α` is a simple root). If
`a(α)=0` (so `ordQ(a(x)) ≥ 2`, `a` a polynomial in `x`) and `b(α)≠0` (so
`ordQ(b(x)y) = ordQ(y) = 1` exactly), the two terms of `a+by` can't cancel at
their minimum order, giving `ordQ(a+by) = 1` — NOT `≥ 2`, hence NOT
swallowed by `c`'s order `2m ≥ 2` at that root. So `Q` is still a genuine
pole, with `ordAtFrac Q a b c 0 = ordQ(a+by) - 2m ≤ 1 - 2m ≤ -m` (using
`m ≥ 1`).

**Uniform quantitative statement** (strictly stronger than mere pole
existence, and — per the same consultation — exactly what's needed to drop
the squarefreeness hypothesis on `c` entirely in §5 below): at any point `Q`
over a root `α` of multiplicity `m := c.rootMultiplicity α`,

- non-Weierstrass: `ordQ(a+by) = 0` for at least one of the two points over
  `α` (the numerator can't vanish at both, by the `char ≠ 2` argument
  already proved below), giving `ordAtFrac ≤ -m`;
- Weierstrass: `ordQ(a+by) ≤ 1` always (either `0`, if `a(α)≠0`; or exactly
  `1`, if `a(α)=0` — which under coprimality forces `b(α)≠0`), giving
  `ordAtFrac ≤ 1 - 2m ≤ -m` whenever `m ≥ 1` (always true at a root).

Both cases give `ordAtFrac Q a b c 0 ≤ -m` at some point `Q` over `α` — the
statement proved below, `exists_pole_of_isCoprimeAtRoots`. This also lets
§5 sum pole mass *with multiplicity* directly (`deg c = ∑ m_α ≤ deg(z)_∞`),
rather than needing `c` squarefree to bound a *distinct*-root count — per
the consultation, `c` is genuinely not squarefree in general (explicit
counterexample: `A'=X, B'=1, f=X^5-3X+3` gives `c = pairNorm = X²-f` with a
double root at `X=1`), so this multiplicity-aware route is the one that
actually closes. -/

/-- **Pointwise coprimality of `(a,b)` against `c`'s roots**: the `k[X]`-
level replacement for `gcd(a,b,c) = 1`, stated exactly as needed (no
`gcd`/`EuclideanDomain` computation) — no root of `c` is simultaneously a
root of `a` and `b`. -/
def IsCoprimeAtRoots (a b c : k[X]) : Prop :=
  ∀ α : k, c.eval α = 0 → ¬ (a.eval α = 0 ∧ b.eval α = 0)

/-- **Local order of `a+by` at a ramified point is `≤ 1` when `a(α)=0`,
`b(α)≠0`.** ChatGPT-assisted (see project convention: hard `sorry`s get a
prompt, not a guess). Strategy, verified against this file's existing
`ordAt_linX_eq_two_of_ramified` idiom rather than a general "order of a sum
is the min" theorem: prove the CONTRAPOSITIVE. If `ordAt Q a b ≥ 2`, then
`pointIdeal Q ^ 2 ∣ span {toPair H a b}`. Since `a(α) = 0` gives `(X - α) ∣
a`, hence `pointIdeal Q ^ 2 ∣ span {toPair H a 0}` too (via
`pointIdeal_sq_dvd_span_linX_of_ramified`, transported along the pure-`X`
factorization). Subtracting, `pointIdeal Q ^ 2 ∣ span {toPair H 0 b}` (the
"`by`" term). But `b(α) ≠ 0` gives `pointIdeal`-count `0` for `b`'s image,
and `y H` has count exactly `1` (`pointIdeal_y_not_sq_dvd_of_ramified` for
`≤ 1`, `y H ∈ pointIdeal Q` — proved inline, matching
`pointIdeal_sq_dvd_span_linX_of_ramified`'s pattern — for `≥ 1`), so `by`'s
count is exactly `1` via `Associates.count` additivity over `*` — contradicting
`≥ 2`. No `char k ≠ 2` needed (unlike the `y ± C Q.Y` unit argument
elsewhere in this file): this only separates `a` from `b` at `α`, never
touches `±y`.

**One correction from the ChatGPT draft**: it proposed a `toPair_mul`
identity for splitting `toPair H (linX α * a₁) 0` into
`toPair H (linX α) 0 * toPair H a₁ 0` — no such lemma exists in this
codebase (the closest, `toPairEquiv_mulByToPairLin`, is itself flagged
UNVERIFIED and covers the general two-variable case, not needed here).
Replaced with a direct one-line unfold of `toPair` at `B = 0`, where the
identity is immediate (`algebraMap` is a ring hom, no `y²=f` reduction
needed since both `B`-parts are `0`). Also replaced its fabricated
`H.f_ne_zero` with this file's own already-proved `y H ≠ 0` argument
(`ordAt_linX_eq_two_of_ramified`'s `hy_ne` block, reused verbatim), and
tightened `hb_notmem` to match `algebraMap_r_notMem_pointIdeal_of_ramified`'s
established `evalAtPoint`-first idiom rather than an ad hoc `change`. -/
theorem ordAt_le_one_of_ramified_num_vanish (hsf : Squarefree H.f)
    (a b : k[X]) (α : k) (Q : H.Point)
    (h_bot : pointIdeal Q ≠ ⊥) (heq : Q.X = α) (hY : Q.Y = 0)
    (ha : a.eval α = 0) (hb : b.eval α ≠ 0) :
    ordAt Q a b ≤ 1 := by
  classical
  set p : Ideal (CoordinateRing H) := pointIdeal Q with hp_def
  set g : CoordinateRing H := toPair H a b with hg_def

  have hprime : Prime p := (Ideal.prime_iff_isPrime h_bot).mpr (pointIdeal_isMaximal Q).isPrime
  have hirr : Irreducible (Associates.mk p) := Associates.irreducible_mk.mpr hprime.irreducible

  -- `g ≠ 0`: if `toPair H a b = 0` then `b = 0` (via `toPair_eq_zero_iff`), contradicting
  -- `b.eval α ≠ 0` (a zero polynomial evaluates to `0` everywhere).
  have hg_ne : g ≠ 0 := by
    rw [hg_def, Ne, toPair_eq_zero_iff]
    rintro ⟨-, hb0⟩
    exact hb (by rw [hb0]; simp)
  have hgspan_ne : Associates.mk (Ideal.span ({g} : Set (CoordinateRing H))) ≠ 0 :=
    Associates.mk_ne_zero.mpr (Ideal.span_singleton_eq_bot.not.mpr hg_ne)

  -- `a`'s image lies in `p ^ 2`: `a(α) = 0` gives `linX α ∣ a` (`a = linX α * a₁`), and
  -- `toPair H a 0 = toPair H (linX α) 0 * toPair H a₁ 0` (direct `toPair`-unfold at `B = 0`,
  -- no need for the codebase's UNVERIFIED general `toPair` product identity), so `p ^ 2` divides
  -- it via `pointIdeal_sq_dvd_span_linX_of_ramified` (applied at `Q.X = α`, using `heq`).
  obtain ⟨a₁, ha₁⟩ : linX α ∣ a := (Polynomial.dvd_iff_isRoot).mpr ha
  have hpair_a : toPair H a 0 = toPair H (linX α) 0 * toPair H a₁ 0 := by
    rw [ha₁]
    unfold HyperellipticPolynomial.toPair
    simp only [map_mul, map_zero, zero_mul, add_zero]
  have hdvd_lin : p ^ 2 ∣ Ideal.span ({toPair H (linX α) 0} : Set (CoordinateRing H)) := by
    rw [hp_def, ← heq]
    exact pointIdeal_sq_dvd_span_linX_of_ramified hsf Q hY
  have hdvd_a : p ^ 2 ∣ Ideal.span ({toPair H a 0} : Set (CoordinateRing H)) := by
    rw [hpair_a, ← Ideal.span_singleton_mul_span_singleton]
    exact hdvd_lin.mul_right _
  have ha_mem : toPair H a 0 ∈ p ^ 2 := Ideal.dvd_span_singleton.mp hdvd_a

  -- `y H`'s image is in `p` (evaluates to `Q.Y = 0`) and NOT in `p ^ 2`
  -- (`pointIdeal_y_not_sq_dvd_of_ramified`), so its `p`-adic count is exactly `1`.
  have hy_mem : y H ∈ p := by
    have heval : evalAtPoint Q (y H) = 0 := by
      have hy : evalAtPoint Q (y H) = Q.Y := by
        unfold evalAtPoint y
        change Polynomial.eval₂ (Polynomial.evalRingHom Q.val.1) Q.val.2 X = Q.Y
        simp [Point.Y]
      rw [hy, hY]
    rw [hp_def]; unfold pointIdeal
    rw [RingHom.mem_ker]
    exact heval
  have hnot_sq_dvd_y : ¬ p ^ 2 ∣ Ideal.span ({y H} : Set (CoordinateRing H)) := by
    rw [hp_def]; exact pointIdeal_y_not_sq_dvd_of_ramified hsf Q hY
  have hy_ne : y H ≠ 0 := by
    intro hy0
    have hf0 : H.f = 0 := by
      have h2 := y_sq_eq H
      rw [hy0, sq, mul_zero] at h2
      have h2' : algebraMap k[X] (CoordinateRing H) H.f = 0 := h2.symm
      have hdeg : (Polynomial.X ^ 2 - Polynomial.C H.f).degree ≠ 0 := by
        have hlt : (Polynomial.C H.f : Polynomial k[X]).degree <
            (Polynomial.X ^ 2 : Polynomial k[X]).degree := by
          have h2 : (Polynomial.X ^ 2 : Polynomial k[X]).degree = (2 : ℕ) := by
            rw [Polynomial.degree_pow, Polynomial.degree_X]; rfl
          rw [h2]
          exact lt_of_le_of_lt (Polynomial.degree_C_le (a := H.f))
            (WithBot.coe_lt_coe.mpr (by decide))
        rw [Polynomial.degree_sub_eq_left_of_degree_lt hlt, Polynomial.degree_pow,
          Polynomial.degree_X]
        intro h; revert h; decide
      have hinj : Function.Injective (algebraMap k[X] (CoordinateRing H)) :=
        AdjoinRoot.of.injective_of_degree_ne_zero hdeg
      have h2'' : algebraMap k[X] (CoordinateRing H) H.f =
          algebraMap k[X] (CoordinateRing H) 0 := by rw [map_zero, h2']
      exact hinj h2''
    have hnd := H.natDegree_eq
    rw [hf0, natDegree_zero] at hnd
    rcases hnd with h5 | h6 <;> omega
  have hyspan_ne : Associates.mk (Ideal.span ({y H} : Set (CoordinateRing H))) ≠ 0 :=
    Associates.mk_ne_zero.mpr (Ideal.span_singleton_eq_bot.not.mpr hy_ne)
  have hy_count_lt2 : (Associates.mk p).count
      (Associates.mk (Ideal.span ({y H} : Set (CoordinateRing H)))).factors < 2 := by
    by_contra hge
    push Not at hge
    rw [← Associates.prime_pow_dvd_iff_le hyspan_ne hirr] at hge
    exact hnot_sq_dvd_y (by simpa [pow_two] using (Associates.mk_le_mk_iff_dvd.mp hge))
  have hy_count_ge1 : 1 ≤ (Associates.mk p).count
      (Associates.mk (Ideal.span ({y H} : Set (CoordinateRing H)))).factors := by
    rw [← Associates.prime_pow_dvd_iff_le hyspan_ne hirr, pow_one]
    exact (Associates.mk_dvd_mk).mpr (Ideal.dvd_span_singleton.mpr hy_mem)
  have hy_count_eq1 : (Associates.mk p).count
      (Associates.mk (Ideal.span ({y H} : Set (CoordinateRing H)))).factors = 1 := by omega

  -- `b`'s image is a UNIT mod `p` (`b(α) ≠ 0`, `heq : Q.X = α`), matching the established
  -- `evalAtPoint`-first idiom from `algebraMap_r_notMem_pointIdeal_of_ramified`.
  have hb_notmem : algebraMap k[X] (CoordinateRing H) b ∉ p := by
    have heval : evalAtPoint Q (algebraMap k[X] (CoordinateRing H) b) = b.eval Q.X := by
      change Polynomial.eval₂ (Polynomial.evalRingHom Q.val.1) Q.val.2 (Polynomial.C b) = b.eval Q.X
      simp [Point.X]
    rw [hp_def]; unfold pointIdeal
    rw [RingHom.mem_ker, heval, heq]
    exact hb
  have hbR_ne : algebraMap k[X] (CoordinateRing H) b ≠ 0 := by
    intro hb0; apply hb_notmem; rw [hb0]; exact Submodule.zero_mem _
  have hbspan_ne : Associates.mk
      (Ideal.span ({algebraMap k[X] (CoordinateRing H) b} : Set (CoordinateRing H))) ≠ 0 :=
    Associates.mk_ne_zero.mpr (Ideal.span_singleton_eq_bot.not.mpr hbR_ne)
  have hb_count_eq0 : (Associates.mk p).count (Associates.mk (Ideal.span
      ({algebraMap k[X] (CoordinateRing H) b} : Set (CoordinateRing H)))).factors = 0 := by
    by_contra hne0
    have hge1 : 1 ≤ (Associates.mk p).count (Associates.mk (Ideal.span
        ({algebraMap k[X] (CoordinateRing H) b} : Set (CoordinateRing H)))).factors :=
      Nat.one_le_iff_ne_zero.mpr hne0
    rw [← Associates.prime_pow_dvd_iff_le hbspan_ne hirr, pow_one] at hge1
    exact hb_notmem (Ideal.dvd_span_singleton.mp (Associates.mk_le_mk_iff_dvd.mp hge1))

  -- `Associates.count` additivity over `*` (same reusable block as
  -- `ordAt_linX_eq_two_of_ramified`), applied to `by := algebraMap b * y H`.
  have hcount_add : ∀ x y : CoordinateRing H, x ≠ 0 → y ≠ 0 →
      (Associates.mk p).count (Associates.mk (Ideal.span ({x} : Set (CoordinateRing H)) *
        Ideal.span ({y} : Set (CoordinateRing H)))).factors =
      (Associates.mk p).count (Associates.mk (Ideal.span ({x} : Set (CoordinateRing H)))).factors +
      (Associates.mk p).count (Associates.mk (Ideal.span ({y} : Set (CoordinateRing H)))).factors := by
    intro x y hx hy
    have hxne : Associates.mk (Ideal.span ({x} : Set (CoordinateRing H))) ≠ 0 :=
      Associates.mk_ne_zero.mpr (Ideal.span_singleton_eq_bot.not.mpr hx)
    have hyne : Associates.mk (Ideal.span ({y} : Set (CoordinateRing H))) ≠ 0 :=
      Associates.mk_ne_zero.mpr (Ideal.span_singleton_eq_bot.not.mpr hy)
    rw [← Associates.mk_mul_mk, Associates.factors_mul]
    obtain ⟨sx, hsx⟩ := Associates.factors_eq_some_iff_ne_zero.mpr hxne
    obtain ⟨sy, hsy⟩ := Associates.factors_eq_some_iff_ne_zero.mpr hyne
    rw [hsx, hsy, ← Associates.FactorSet.coe_add]
    simp only [Associates.count, dif_pos hirr, Associates.bcount]
    exact Multiset.count_add _ sx sy

  have hby_ne : algebraMap k[X] (CoordinateRing H) b * y H ≠ 0 := mul_ne_zero hbR_ne hy_ne
  have hbyspan_ne : Associates.mk (Ideal.span
      ({algebraMap k[X] (CoordinateRing H) b * y H} : Set (CoordinateRing H))) ≠ 0 :=
    Associates.mk_ne_zero.mpr (Ideal.span_singleton_eq_bot.not.mpr hby_ne)
  have hcount_by : (Associates.mk p).count (Associates.mk (Ideal.span
      ({algebraMap k[X] (CoordinateRing H) b * y H} : Set (CoordinateRing H)))).factors = 1 := by
    rw [← Ideal.span_singleton_mul_span_singleton,
      hcount_add (algebraMap k[X] (CoordinateRing H) b) (y H) hbR_ne hy_ne,
      hb_count_eq0, hy_count_eq1]

  -- Assembly: contrapositive. Assume `1 < ordAt Q a b`, i.e. `ordAt Q a b ≥ 2`; derive
  -- `g ∈ p ^ 2` (via `ordAt_eq_count` + `prime_pow_dvd_iff_le`), subtract `ha_mem` (`toPair H a
  -- 0 ∈ p ^ 2`) to get `algebraMap b * y H ∈ p ^ 2` (since `toPair H a b - toPair H a 0 =
  -- toPair H 0 b = algebraMap b * y H`, direct from `toPair`'s definition), then
  -- `prime_pow_dvd_iff_le` again gives `count(by) ≥ 2`, contradicting `hcount_by = 1`.
  by_contra hcon
  push Not at hcon
  have hcount_ge2 : 2 ≤ (Associates.mk p).count
      (Associates.mk (Ideal.span ({g} : Set (CoordinateRing H)))).factors := by
    have hval : ordAt Q a b = ((Associates.mk p).count
        (Associates.mk (Ideal.span ({g} : Set (CoordinateRing H)))).factors : ℤ) := by
      rw [hp_def, hg_def]; exact ordAt_eq_count Q a b hg_ne h_bot
    have : (2 : ℤ) ≤ ((Associates.mk p).count
        (Associates.mk (Ideal.span ({g} : Set (CoordinateRing H)))).factors : ℤ) := by omega
    exact_mod_cast this
  have hg_mem : g ∈ p ^ 2 := by
    have hdvd : p ^ 2 ∣ Ideal.span ({g} : Set (CoordinateRing H)) := by
      rw [← Associates.prime_pow_dvd_iff_le hgspan_ne hirr] at hcount_ge2
      exact (Associates.mk_le_mk_iff_dvd).mp hcount_ge2
    exact Ideal.dvd_span_singleton.mp hdvd
  -- `toPair H a b - toPair H a 0 = toPair H 0 b = algebraMap b * y H` (direct unfold, `toPair`
  -- additive in its first argument).
  have hsplit : g - toPair H a 0 = algebraMap k[X] (CoordinateRing H) b * y H := by
    rw [hg_def]
    unfold HyperellipticPolynomial.toPair
    simp only [map_zero, zero_mul, add_zero]
    abel
  have hby_mem : algebraMap k[X] (CoordinateRing H) b * y H ∈ p ^ 2 := by
    rw [← hsplit]
    exact sub_mem hg_mem ha_mem
  have hp2_by : p ^ 2 ∣
      Ideal.span ({algebraMap k[X] (CoordinateRing H) b * y H} : Set (CoordinateRing H)) :=
    Ideal.dvd_span_singleton.mpr hby_mem
  have hassoc : (Associates.mk p) ^ 2 ∣ Associates.mk (Ideal.span
      ({algebraMap k[X] (CoordinateRing H) b * y H} : Set (CoordinateRing H))) :=
    (Associates.mk_dvd_mk).mpr hp2_by
  have hge2 : 2 ≤ (Associates.mk p).count (Associates.mk (Ideal.span
      ({algebraMap k[X] (CoordinateRing H) b * y H} : Set (CoordinateRing H)))).factors :=
    (Associates.prime_pow_dvd_iff_le hbyspan_ne hirr).mp hassoc
  omega



/-- **The crux lemma, quantitative form.** If `α` is a root of `c` (`c ≠ 0`)
of multiplicity `m := c.rootMultiplicity α`, and `IsCoprimeAtRoots a b c`
holds, some point `Q` over `α` has `ordAtFrac Q a b c 0 ≤ -m` — i.e. `Q`
absorbs at least the full multiplicity `m` as pole order, regardless of
whether `c` is squarefree at `α`. Strictly stronger than (and supersedes)
the earlier existence-only version. -/
theorem exists_pole_of_isCoprimeAtRoots (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (a b c : k[X]) (hc : c ≠ 0) (α : k) (hα : c.eval α = 0)
    (hcop : IsCoprimeAtRoots a b c) :
    ∃ Q : H.Point, Q.X = α ∧
      ordAtFrac Q a b c (0 : k[X]) ≤ -(c.rootMultiplicity α : ℤ) := by
  classical
  set m := c.rootMultiplicity α with hm_def
  have hmpos : m ≥ 1 := by
    have hroot : c.IsRoot α := hα
    have hpos : 0 < m := by rw [hm_def]; exact (Polynomial.rootMultiplicity_pos hc).mpr hroot
    omega
  by_cases hWeier : H.f.eval α = 0
  · -- Weierstrass case: unique point `Q = (α, 0)`.
    have hQeq : H.Equation α (0 : k) := by
      show (0 : k) ^ 2 = H.f.eval α
      rw [hWeier]; ring
    set Q : H.Point := Point.mk α 0 hQeq with hQ_def
    have hQX : Q.X = α := rfl
    have hQY : Q.Y = 0 := rfl
    refine ⟨Q, hQX, ?_⟩
    have hordc : ordAt Q c (0 : k[X]) = 2 * (m : ℤ) :=
      ordAt_eq_rootMultiplicity_ramified hsf c hc α Q (pointIdeal_ne_bot Q) hQX hQY
    unfold ordAtFrac
    rw [hordc]
    by_cases haα : a.eval α = 0
    · -- `a(α)=0` forces `b(α)≠0` (coprimality), giving `ordAt Q a b ≤ 1`
      -- via the local-uniformizer lemma above.
      have hbα : b.eval α ≠ 0 := fun hb0 => hcop α hα ⟨haα, hb0⟩
      have hle1 := ordAt_le_one_of_ramified_num_vanish hsf a b α Q (pointIdeal_ne_bot Q)
        hQX hQY haα hbα
      linarith
    · -- `a(α)≠0` gives `ordAt Q a b = 0` directly (numerator doesn't vanish
      -- at `Q` at all, since `Q.Y = 0` kills `b`'s contribution).
      have hnotmem : toPair H a b ∉ pointIdeal Q := by
        rw [toPair_mem_pointIdeal_iff, hQX, hQY]
        simp only [mul_zero, add_zero]
        exact haα
      have hordab : ordAt Q a b = 0 := ordAt_eq_zero_of_notMem Q a b hnotmem
      rw [hordab]
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
    rcases hor with hpos | hneg
    · refine ⟨Q, hQX, ?_⟩
      have hnotmem : toPair H a b ∉ pointIdeal Q := by
        rw [toPair_mem_pointIdeal_iff, hQX, hQY]; exact hpos
      have hordab : ordAt Q a b = 0 := ordAt_eq_zero_of_notMem Q a b hnotmem
      have hordc : ordAt Q c (0 : k[X]) = (m : ℤ) :=
        ordAt_eq_rootMultiplicity_unramified hchar c hc α Q (pointIdeal_ne_bot Q) hQX
          (hQY ▸ hβne)
      unfold ordAtFrac
      rw [hordab, hordc]
      linarith
    · -- Use `ιQ` instead: `(ιQ).X = α`, `(ιQ).Y = -β`, and
      -- `a(α) + b(α)*(-β) = a(α) - b(α)β ≠ 0` by `hneg`.
      refine ⟨Point.iota Q, by rw [Point.iota_X]; exact hQX, ?_⟩
      have hιQY : (Point.iota Q).Y = -β := by rw [Point.iota_Y, hQY]
      have hnotmem : toPair H a b ∉ pointIdeal (Point.iota Q) := by
        rw [toPair_mem_pointIdeal_iff, Point.iota_X, hQX, hιQY]
        intro hcontra
        apply hneg
        have heq : a.eval α + b.eval α * (-β) = a.eval α - b.eval α * β := by ring
        rw [← heq]
        exact hcontra
      have hordab : ordAt (Point.iota Q) a b = 0 :=
        ordAt_eq_zero_of_notMem (Point.iota Q) a b hnotmem
      have hινe : (Point.iota Q).Y ≠ 0 := by rw [hιQY]; exact neg_ne_zero.mpr hβne
      have hordc : ordAt (Point.iota Q) c (0 : k[X]) = (m : ℤ) :=
        ordAt_eq_rootMultiplicity_unramified hchar c hc α (Point.iota Q)
          (pointIdeal_ne_bot _) (by rw [Point.iota_X]; exact hQX) hινe
      unfold ordAtFrac
      rw [hordab, hordc]
      linarith

end HyperellipticPolynomial

namespace HyperellipticPolynomial

open Divisor

variable {H} [IsAlgClosed k] [IsDedekindDomain (CoordinateRing H)]

/-! ## §5. `deg c ≤ 2`, via pole mass with multiplicity — no squarefreeness needed

**Resolved via ChatGPT consultation (this session), superseding the original
distinct-root-counting approach.** The original plan bounded the number of
*distinct* roots of `c` by 2, which only gives `deg c ≤ 2` if `c` is
squarefree — and per the consultation, `c = pairNorm H A' B' = (A')² -
(B')²f` is **not** squarefree in general, even with `A', B'` coprime and `f`
squarefree (explicit counterexample in the consultation transcript:
`A'=X, B'=1, f=X⁵-3X+3` gives a double root of `c` at `X=1`).

**The fix**: §4's crux lemma (`exists_pole_of_isCoprimeAtRoots`) was
strengthened to a *quantitative* form — every root `α` of multiplicity `m`
supplies pole mass **at least `m`**, not just "some pole". So instead of
counting distinct roots, we bound the **sum of pole orders (with
multiplicity) at `x₁` and `x₂` together**, which `IsPoleBoundedAtPair'`
already caps at `2` directly (order `≤ 1` at each of the two points, by the
pointwise clause with singleton indicators) — no `Finset.sum`-over-roots
machinery needed at all, since every root's witness point `Q_α` is forced
into `{x₁,x₂}` and contributes to a bound already available pointwise. -/

/-- **Bridge: `IsPoleBoundedAtPair`'s pointwise `ordAt` clause restates as the
`ordAtFrac`-shaped bound, for the same witness pair.** Pure unfolding —
`ordAtFrac P A B A' B' := ordAt P A B - ordAt P A' B'` by definition, so this
needs no representation-independence machinery, unlike
`ordAtFrac_eq_of_polePairToFraction_eq` (which compares *different*
witnesses of the same fraction). This is exactly what's needed to feed the
`(A,B,A',B')` witness pulled out of `LPairCarrier` membership into §5/§6's
`ordAtFrac`-based lemmas without first rationalizing. -/
theorem ordAtFrac_ge_of_isPoleBoundedAtPair_pointwise (x₁ x₂ : H.Point) (A B A' B' : k[X])
    (hptwise : ∀ P : H.Point, ordAt P A B ≥ ordAt P A' B' -
      ((if P = x₁ then 1 else 0) + (if P = x₂ then 1 else 0)))
    (P : H.Point) :
    ordAtFrac P A B A' B' ≥ -((if P = x₁ then 1 else 0) + (if P = x₂ then 1 else 0)) := by
  unfold ordAtFrac
  have := hptwise P
  omega

/-- **Every root of `c` forces its witness point into `{x₁,x₂}`, with the
root's full multiplicity absorbed there.** Direct combination of §4's
quantitative crux lemma with the pointwise `{x₁,x₂}` pole cap: if `Q` is
`α`'s witness point (`ordAtFrac Q a b c 0 ≤ -m`) and `Q ∉ {x₁,x₂}`, the
pointwise bound forces `ordAtFrac Q a b c 0 ≥ 0`, an immediate contradiction
once `m ≥ 1`. So `Q ∈ {x₁,x₂}`, and moreover `m ≤ 1` (the pointwise bound
at `Q ∈ {x₁,x₂}` is `≥ -1`, matching a single indicator).

**Requires `x₁ ≠ x₂`** (added after the original hypothesis-free statement was
found false): when `x₁ = x₂`, a witness `Q` equal to both collapses the two
indicators onto the same point, weakening the pointwise bound to `≥ -2`
instead of `≥ -1`, which only forces `m ≤ 2`, not `m ≤ 1`. -/
theorem rootMultiplicity_le_one_and_mem_pair_of_isCoprimeAtRoots
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (x₁ x₂ : H.Point) (hne : x₁ ≠ x₂) (a b c : k[X]) (hc : c ≠ 0) (α : k) (hα : c.eval α = 0)
    (hcop : IsCoprimeAtRoots a b c)
    (hzsupp : ∀ P : H.Point, ordAtFrac P a b c 0 ≥
      -((if P = x₁ then 1 else 0) + (if P = x₂ then 1 else 0))) :
    ∃ Q : H.Point, (Q = x₁ ∨ Q = x₂) ∧ Q.X = α ∧ (c.rootMultiplicity α : ℤ) ≤ 1 := by
  classical
  obtain ⟨Q, hQX, hQpole⟩ := exists_pole_of_isCoprimeAtRoots hchar hsf a b c hc α hα hcop
  have hbound := hzsupp Q
  by_cases hQ1 : Q = x₁
  · refine ⟨Q, Or.inl hQ1, hQX, ?_⟩
    rw [if_pos hQ1] at hbound
    have hQ2 : Q ≠ x₂ := hQ1 ▸ hne
    rw [if_neg hQ2] at hbound; omega
  · by_cases hQ2 : Q = x₂
    · refine ⟨Q, Or.inr hQ2, hQX, ?_⟩
      rw [if_neg hQ1, if_pos hQ2] at hbound
      omega
    · exfalso
      rw [if_neg hQ1, if_neg hQ2] at hbound
      simp only [add_zero] at hbound
      have hmpos : (c.rootMultiplicity α : ℤ) ≥ 1 := by
        have hroot : c.IsRoot α := hα
        have hpos : 0 < c.rootMultiplicity α := (Polynomial.rootMultiplicity_pos hc).mpr hroot
        exact_mod_cast hpos
      omega

/-- **`c` has at most two roots (each of multiplicity exactly `1`, forced
above), one absorbed at `x₁`, one at `x₂` — hence `deg c ≤ 2`.**

**Construction.** Every root `α` of `c` maps (via the lemma above) to a
witness point `Q_α ∈ {x₁,x₂}` with `c.rootMultiplicity α ≤ 1`. Two distinct
roots `α ≠ α'` give witness points with `Q_α.X = α ≠ α' = Q_{α'}.X`, hence
`Q_α ≠ Q_{α'}` — so at most one root can map to `x₁` and at most one to
`x₂`, i.e. `c` has at most `2` distinct roots, **each of multiplicity `1`**.
Since multiplicity-`1` roots contribute exactly their count to `c.natDegree`
(no "missing" multiplicity to worry about, unlike the squarefree-counting
route this replaces), `c.natDegree ≤ 2` follows directly — **this is the
key simplification**: because every root is forced to multiplicity exactly
`1` (not merely bounded), summing degree contributions needs no
`Squarefree c` hypothesis at all, matching the consultation's diagnosis
that the multiplicity-quantitative crux lemma is what actually removes the
squarefreeness dependency. -/
theorem natDegree_le_two_of_isCoprimeAtRoots (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (x₁ x₂ : H.Point) (hne : x₁ ≠ x₂) (a b c : k[X]) (hc : c ≠ 0)
    (hcop : IsCoprimeAtRoots a b c)
    (hzsupp : ∀ P : H.Point, ordAtFrac P a b c 0 ≥
      -((if P = x₁ then 1 else 0) + (if P = x₂ then 1 else 0))) :
    c.natDegree ≤ 2 := by
  classical
  -- Every root `α` of `c` maps to a witness point `Q_α ∈ {x₁,x₂}` with
  -- `Q_α.X = α`, via the previous lemma. Package this as an injective map
  -- from `c`'s (finite) root set into `{x₁,x₂}` — injective because `Q_α.X = α`
  -- recovers `α` from `Q_α`, so distinct roots give distinct witness points.
  have hroot_to_pair : ∀ α ∈ c.roots.toFinset,
      ∃ Q : H.Point, (Q = x₁ ∨ Q = x₂) ∧ Q.X = α ∧ (c.rootMultiplicity α : ℤ) ≤ 1 := by
    intro α hα
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hc] at hα
    exact rootMultiplicity_le_one_and_mem_pair_of_isCoprimeAtRoots hchar hsf x₁ x₂ hne a b c hc
      α hα hcop hzsupp
  -- Choice function `α ↦ Q_α`, packaged via `Classical.choice` on the above.
  choose Qf hQf_mem hQf_X hQf_mult using hroot_to_pair
  -- `Qf` is injective on `c.roots.toFinset`: if `Qf α = Qf β` then
  -- `α = (Qf α).X = (Qf β).X = β`.
  have hQf_inj : ∀ α (hα : α ∈ c.roots.toFinset) β (hβ : β ∈ c.roots.toFinset),
      Qf α hα = Qf β hβ → α = β := by
    intro α hα β hβ heq
    rw [← hQf_X α hα, ← hQf_X β hβ, heq]
  -- Hence `c.roots.toFinset` injects into the 2-element set `{x₁, x₂}`,
  -- bounding its cardinality by `2`.
  have hcard_le : c.roots.toFinset.card ≤ 2 := by
    have hmaps : ∀ α (hα : α ∈ c.roots.toFinset), Qf α hα ∈ ({x₁, x₂} : Finset H.Point) := by
      intro α hα
      rcases hQf_mem α hα with h | h <;> simp [h]
    -- `Qf` is dependently typed (`∀ α, α ∈ c.roots.toFinset → H.Point`), so it
    -- can't feed `Finset.card_le_card_of_injOn` directly (that wants a plain
    -- function on a `Finset`). Route through `c.roots.toFinset.attach`, whose
    -- elements are `⟨α, hα⟩ : {α // α ∈ c.roots.toFinset}` — the membership
    -- proof travels with the element, so `Qf a.1 a.2` is a genuine
    -- non-dependent function `{α // α ∈ c.roots.toFinset} → H.Point`.
    have hcard_attach : c.roots.toFinset.attach.card ≤ ({x₁, x₂} : Finset H.Point).card := by
      apply Finset.card_le_card_of_injOn (fun a => Qf a.1 a.2)
      · intro a _
        exact hmaps a.1 a.2
      · intro a _ b _ heq
        exact Subtype.ext (hQf_inj a.1 a.2 b.1 b.2 heq)
    rw [Finset.card_attach] at hcard_attach
    refine hcard_attach.trans ?_
    -- `{x₁, x₂} = insert x₁ {x₂}`, so `card {x₁,x₂} ≤ card {x₂} + 1 = 2` via
    -- `Finset.card_insert_le`. NAME UNCONFIRMED — please check in the REPL;
    -- if it doesn't match, `decide`/`Finset.card_le_card ... ` or
    -- `Finset.card_pair`-style lemmas are the likely alternates.
    have : ({x₁, x₂} : Finset H.Point).card ≤ ({x₂} : Finset H.Point).card + 1 :=
      Finset.card_insert_le x₁ ({x₂} : Finset H.Point)
    simpa using this
  -- Every root has multiplicity exactly `1` (`≥ 1` since it's a root of `c ≠ 0`,
  -- `≤ 1` from `hQf_mult`), so the roots-with-multiplicity multiset `c.roots`
  -- has no repeats, i.e. `c.roots.Nodup` — hence `c.roots.card =
  -- c.roots.toFinset.card ≤ 2` (just proved above). Combined with `c` splitting
  -- over `k` (below, using the ambient `[IsAlgClosed k]`), `c.roots.card =
  -- c.natDegree` exactly, closing the goal.
  have hnodup : c.roots.Nodup := by
    rw [Multiset.nodup_iff_count_le_one]
    intro α
    by_cases hα : α ∈ c.roots
    · have hα' : α ∈ c.roots.toFinset := Multiset.mem_toFinset.mpr hα
      have hm1 : c.rootMultiplicity α ≤ 1 := by exact_mod_cast hQf_mult α hα'
      rw [Polynomial.count_roots]
      exact hm1
    · simp [Multiset.count_eq_zero.mpr hα]
  have hroots_card : c.roots.card = c.roots.toFinset.card := (Multiset.toFinset_card_of_nodup hnodup).symm
  -- `IsAlgClosed k` *is* in scope here (the ambient `variable [IsAlgClosed k]`
  -- block at the top of this section covers this theorem, confirmed by the
  -- REPL error context listing `inst✝¹ : IsAlgClosed k`). Confirmed via
  -- Mathlib docs (web search): in the current version, `Polynomial.Splits` is
  -- a UNARY predicate (`f.Splits`, no ring-hom argument — the old binary
  -- `Splits i f` API is gone), and `IsAlgClosed.splits (p : Polynomial k) :
  -- p.Splits` gives it directly. `Polynomial.Splits.natDegree_eq_card_roots`
  -- is exactly the fact wanted, in exactly this direction:
  -- `f.Splits → f.natDegree = f.roots.card`.
  have hsplits : c.Splits := IsAlgClosed.splits c
  have heq_natDegree : c.natDegree = c.roots.card := hsplits.natDegree_eq_card_roots
  rw [heq_natDegree]
  omega

/-! ## §5b. `x₁ = x₂` companion: `deg c ≤ 2` still holds, with all pole mass
absorbed at the single point `x₁`

`natDegree_le_two_of_isCoprimeAtRoots` above needs `x₁ ≠ x₂` (its own
docstring explains why: the pointwise bound at a single shared witness point
only weakens to `≥ -2` when `x₁ = x₂`, not the `≥ -1` the `hne`-using proof
needs to force multiplicity exactly `1` per root). But the assembly theorem
`uniqueDegree2MapToP1_ordAtFrac` only has `hne : x₂ ≠ Point.iota x₁`, which
does **not** exclude `x₁ = x₂` (that's the `2•x₁` / doubled-Weierstrass-style
divisor case). This section supplies the missing companion: when `x₁ = x₂`,
`c` still has `natDegree ≤ 2`, now via a *single* root of multiplicity `≤ 2`
(rather than two roots of multiplicity `1` each) — the direct analogue,
proved the same way as §5 but merging the two `{x₁,x₂}` slots into one. -/

/-- **`x₁ = x₂` analogue of `rootMultiplicity_le_one_and_mem_pair_of_isCoprimeAtRoots`.**
Every root `α` of `c` has its witness point (from `exists_pole_of_isCoprimeAtRoots`)
forced to equal `x₁`, with multiplicity `≤ 2` (matching the doubled indicator
`-2` slack at the single point, instead of `-1`). -/
theorem rootMultiplicity_le_two_of_isCoprimeAtRoots_eq
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (x₁ : H.Point) (a b c : k[X]) (hc : c ≠ 0) (α : k) (hα : c.eval α = 0)
    (hcop : IsCoprimeAtRoots a b c)
    (hzsupp : ∀ P : H.Point, ordAtFrac P a b c 0 ≥ -(2 * (if P = x₁ then 1 else 0))) :
    x₁.X = α ∧ (c.rootMultiplicity α : ℤ) ≤ 2 := by
  classical
  obtain ⟨Q, hQX, hQpole⟩ := exists_pole_of_isCoprimeAtRoots hchar hsf a b c hc α hα hcop
  have hbound := hzsupp Q
  by_cases hQ1 : Q = x₁
  · refine ⟨hQ1 ▸ hQX, ?_⟩
    rw [if_pos hQ1] at hbound
    omega
  · exfalso
    rw [if_neg hQ1] at hbound
    simp only [mul_zero] at hbound
    have hmpos : (c.rootMultiplicity α : ℤ) ≥ 1 := by
      have hroot : c.IsRoot α := hα
      have hpos : 0 < c.rootMultiplicity α := (Polynomial.rootMultiplicity_pos hc).mpr hroot
      exact_mod_cast hpos
    omega

/-- **`x₁ = x₂` analogue of `natDegree_le_two_of_isCoprimeAtRoots`.** All of
`c`'s roots are forced to the single point `x₁` (by the previous lemma's
`.X`-recovery injectivity argument, now trivial since there is only one
target point rather than two), so `c.roots.toFinset.card ≤ 1`; combined with
the same lemma's multiplicity bound `≤ 2` per root, `c.natDegree ≤ 2`
follows — this time NOT because every root has multiplicity exactly `1`
(that's false here in general: `c` could genuinely be `(X-α)²` up to a unit,
a single double root), but because there is at most **one** root, of
multiplicity **at most `2`**, giving the same total bound `≤ 2` by a
different route (`1 root × mult ≤ 2` instead of `≤2 roots × mult ≤ 1`). -/
theorem natDegree_le_two_of_isCoprimeAtRoots_eq (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (x₁ : H.Point) (a b c : k[X]) (hc : c ≠ 0)
    (hcop : IsCoprimeAtRoots a b c)
    (hzsupp : ∀ P : H.Point, ordAtFrac P a b c 0 ≥ -(2 * (if P = x₁ then 1 else 0))) :
    c.natDegree ≤ 2 := by
  classical
  -- Every root `α` of `c` equals `x₁.X` (via the previous lemma), so
  -- `c.roots.toFinset ⊆ {x₁.X}`, i.e. has cardinality `≤ 1`.
  have hroot_eq : ∀ α ∈ c.roots.toFinset, x₁.X = α ∧ (c.rootMultiplicity α : ℤ) ≤ 2 := by
    intro α hα
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hc] at hα
    exact rootMultiplicity_le_two_of_isCoprimeAtRoots_eq hchar hsf x₁ a b c hc α hα hcop hzsupp
  have hsub : c.roots.toFinset ⊆ ({x₁.X} : Finset k) := by
    intro α hα
    rw [Finset.mem_singleton]
    exact (hroot_eq α hα).1.symm
  have hcard_le : c.roots.toFinset.card ≤ 1 := by
    calc c.roots.toFinset.card ≤ ({x₁.X} : Finset k).card := Finset.card_le_card hsub
      _ = 1 := Finset.card_singleton x₁.X
  -- Every root has multiplicity `≤ 2` by the previous lemma, so
  -- `c.roots.card = ∑_{α ∈ toFinset} count α ≤ ∑_{α ∈ toFinset} 2 ≤ 2 * 1`.
  have hcount_le : ∀ α ∈ c.roots.toFinset, c.roots.count α ≤ 2 := by
    intro α hα
    rw [Polynomial.count_roots]
    have := (hroot_eq α hα).2
    exact_mod_cast this
  have hroots_card_le : c.roots.card ≤ 2 * c.roots.toFinset.card := by
    -- `Multiset.toFinset_sum_count_eq : s.toFinset.sum (fun a => s.count a) = s.card` —
    -- MATHLIB NAME UNCONFIRMED (this exact orientation/name), standard multiset fact
    -- relating total card to the sum of per-element counts over the support `Finset`.
    have hsum : c.roots.card = ∑ α ∈ c.roots.toFinset, c.roots.count α := by
      rw [Multiset.toFinset_sum_count_eq]
    rw [hsum]
    calc ∑ α ∈ c.roots.toFinset, c.roots.count α
        ≤ ∑ _α ∈ c.roots.toFinset, 2 :=
          Finset.sum_le_sum hcount_le
      _ = 2 * c.roots.toFinset.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hsplits : c.Splits := IsAlgClosed.splits c
  have heq_natDegree : c.natDegree = c.roots.card := hsplits.natDegree_eq_card_roots
  rw [heq_natDegree]
  calc c.roots.card ≤ 2 * c.roots.toFinset.card := hroots_card_le
    _ ≤ 2 * 1 := by omega
    _ = 2 := by norm_num


/-! ## §5c. `ordInfOfPair` transport across §1's rationalization

Pure `k[X]`-degree arithmetic, no dependence on `H.Point`/`CoordinateRing H`
beyond `H.f.natDegree = 5`: given the original witness's infinity bound
`ordInfOfPair A B ≥ ordInfOfPair A' B'`, the rationalized witness
`a = A A' - B B' f, b = A' B - A B', c = A'² - B'² f` (§1's construction)
again satisfies `ordInfOfPair a b ≥ ordInfOfPair c 0`. No representation-
independence machinery for `ordInfOfPair` exists in this codebase, so this
has to be proved from scratch from the explicit polynomial formulas.

**Hand-verified proof sketch (correct, but not yet successfully turned into
a clean tactic proof — an earlier attempt below this docstring produced
unreliable `nlinarith`/`omega` case-work with at least one outright bad step,
so it's been replaced with an honest `sorry` rather than left broken).**
Write `dA = A.natDegree`, etc., all as integers, `M := max(2dA, 2dB+5)` (with
the convention `2dB+5` is replaced by `0` when `B=0`, matching
`ordInfOfPair`'s own `if`), `M' := max(2dA', 2dB'+5)` similarly. `hinfle`
unfolds to `M ≤ M'`. Since `M = max(2dA, ...)` and `M = max(..., 2dB+5)` (when
`B≠0`), always `2dA ≤ M ≤ M'` and (when `B≠0`) `2dB+5 ≤ M ≤ M'` — these two
facts hold regardless of which branch of `M`'s own max is realized, and don't
need to know which one is active. Symmetrically `2dA' ≤ M'` and (`B'≠0`)
`2dB'+5 ≤ M'` trivially. From these:

- `c = A'² - B'²f`: `deg c ≤ max(2dA', 2dB'+5) = M'` directly
  (`natDegree_sub_le`, `natDegree_pow`, `natDegree_mul_le`, `hdeg`).
- `a = AA' - BB'f`: `deg a ≤ max(dA+dA', dB+dB'+5)`. Bound each summand
  against `M'` using `2dA≤M'`, `2dA'≤M'` (so `dA+dA' ≤ M'` via
  `2(dA+dA') ≤ 2M'`, i.e. `dA+dA' ≤ M'` needs `2dA≤M'` AND `2dA'≤M'` added
  and halved — careful: this only gives `dA+dA' ≤ M'` when `M'` is even or
  the halving is done in `ℤ` with the right rounding; since all quantities
  here are `2×`(degree) or `2×`(degree)`+5`, everything should be tracked as
  `2×` the actual degree throughout rather than halving, to avoid parity
  issues — i.e. bound `2 deg a ≤ 2M'` directly: `2 deg a ≤
  2 max(dA+dA', dB+dB'+5) = max(2dA+2dA', 2dB+2dB'+10)`, and `2dA+2dA' ≤
  M'+M' = 2M'` (from `2dA≤M'`, `2dA'≤M'`), similarly
  `2dB+2dB'+10 = (2dB+5)+(2dB'+5) ≤ M'+M' = 2M'`. So `2 deg a ≤ 2M'`.
- `b = A'B - AB'`: `deg b ≤ max(dA'+dB, dA+dB')`, so `2 deg b + 5 ≤
  2max(dA'+dB,dA+dB')+5 = max(2dA'+2dB+5, 2dA+2dB'+5)`, and each branch is
  `≤ M'+M' = 2M'` similarly (`2dA'≤M'` and `2dB+5≤M'` sum to `≤2M'`; likewise
  `2dA≤M'` and `2dB'+5≤M'`). So `2 deg b + 5 ≤ 2M'` too.
- Conclusion: `max(2 deg a, 2 deg b+5) ≤ 2M'`, and `2 deg c ≤ 2M'` (from the
  `c`-bound above, doubled) — but `ordInfOfPair a b = -max(2 deg a, 2 deg
  b+5) ≥ -2M'` and `ordInfOfPair c 0 = -2 deg c ≥ -2M'` don't directly
  compare (both bounded below by `-2M'`, not against each other) — **this
  sketch establishes `ordInfOfPair a b ≥ -2M'` and needs the SHARPER fact
  `2 deg c ≥ 2 deg a` and `2 deg c ≥ 2 deg b + 5` (i.e. `deg c` itself, not
  just `M'`, dominates), or equivalently that `deg c` actually **equals**
  `M'` up to the cancellation caveat below, not merely `≤ M'`** — the
  degree-6 term of `c = A'²-B'²f` cancels only in genuinely degenerate cases
  (needs `A'`'s leading coefficient² = `B'`'s leading coefficient² ×
  (leading coeff of `f`) AND same total degree on both sides, i.e. only when
  `2dA' = 2dB'+5` exactly, impossible for parity reasons since `2dA'` is even
  and `2dB'+5` is odd) — **so `deg c = M'` exactly, no cancellation is
  possible**, and the chain above (`2 deg a ≤ 2M' = 2 deg c`,
  `2 deg b + 5 ≤ 2M' = 2 deg c`) gives exactly `ordInfOfPair a b ≥
  ordInfOfPair c 0`. This parity observation (`2dA'` even, `2dB'+5` odd, so
  the two terms of `c` can never have equal degree and cancel) is the one
  piece of real content beyond routine `natDegree_add_le`/`natDegree_mul_le`
  bookkeeping, and is the reason `deg c` is exactly `M'` rather than merely
  `≤ M'` — worth double-checking carefully against a live goal state. -/
theorem ordInfOfPair_rationalized_ge (hdeg : H.f.natDegree = 5) (A B A' B' : k[X])
    (hABne : ¬ (A = 0 ∧ B = 0)) (hA'B'ne : ¬ (A' = 0 ∧ B' = 0))
    (hinfle : ordInfOfPair A B ≥ ordInfOfPair A' B')
    (a b c : k[X]) (ha : a = A * A' - B * B' * H.f) (hb : b = A' * B - A * B')
    (hc : c = A' ^ 2 - B' ^ 2 * H.f) (habne : ¬ (a = 0 ∧ b = 0)) (hcne : c ≠ 0) :
    ordInfOfPair a b ≥ ordInfOfPair c (0 : k[X]) := by

  have hABord := ordInfOfPair_eq_of_ne A B hABne
  have hA'B'ord := ordInfOfPair_eq_of_ne A' B' hA'B'ne

  -- `M' := max(2 deg A', if B'=0 then 0 else 2 deg B'+5)`. Everything below
  -- is stated directly against this quantity via the two *plain* (no `ite`)
  -- bounds `hA_M'` / `hB'_bound`, so no `omega` call downstream ever has to
  -- look inside a bare `max`/`ite` itself.
  have hmax :
      max
          (2 * (A.natDegree : ℤ))
          (if B = 0 then 0 else 2 * (B.natDegree : ℤ) + 5)
      ≤
      max
          (2 * (A'.natDegree : ℤ))
          (if B' = 0 then 0 else 2 * (B'.natDegree : ℤ) + 5) := by
    rw [← neg_le_neg_iff]
    rw [← hABord, ← hA'B'ord]
    exact hinfle

  have hf : H.f ≠ 0 := by
    intro hf
    rw [hf] at hdeg
    norm_num at hdeg

  -- Plain (ite-free) bound: `2 deg A ≤ M'`.
  have hA_M' : (2 : ℤ) * (A.natDegree : ℤ) ≤
      max (2 * (A'.natDegree : ℤ))
        (if B' = 0 then 0 else 2 * (B'.natDegree : ℤ) + 5) :=
    (le_max_left _ _).trans hmax

  -- Plain bound: `2 deg A' ≤ M'`.
  have hA'_M' : (2 : ℤ) * (A'.natDegree : ℤ) ≤
      max (2 * (A'.natDegree : ℤ))
        (if B' = 0 then 0 else 2 * (B'.natDegree : ℤ) + 5) :=
    le_max_left _ _

  -- Plain bound: if `B ≠ 0`, `2 deg B + 5 ≤ M'`.
  have hB_bound : B ≠ 0 → (2 : ℤ) * (B.natDegree : ℤ) + 5 ≤
      max (2 * (A'.natDegree : ℤ))
        (if B' = 0 then 0 else 2 * (B'.natDegree : ℤ) + 5) := by
    intro hB0
    have h := (le_max_right
        (2 * (A.natDegree : ℤ)) (if B = 0 then 0 else 2 * (B.natDegree : ℤ) + 5)).trans hmax
    rwa [if_neg hB0] at h

  -- Plain bound: if `B' ≠ 0`, `2 deg B' + 5 ≤ M'`.
  have hB'_bound : B' ≠ 0 → (2 : ℤ) * (B'.natDegree : ℤ) + 5 ≤
      max (2 * (A'.natDegree : ℤ))
        (if B' = 0 then 0 else 2 * (B'.natDegree : ℤ) + 5) := by
    intro hB'0
    rw [if_neg hB'0]
    exact le_max_right (2 * (A'.natDegree : ℤ)) (2 * (B'.natDegree : ℤ) + 5)

  -- Raw degree bounds for the products/differences making up `a`, `b`, `c`.
  have hAA' : (A * A').natDegree ≤ A.natDegree + A'.natDegree :=
    natDegree_mul_le

  have hBB'f : (B * B' * H.f).natDegree ≤
      B.natDegree + B'.natDegree + H.f.natDegree := by
    have h1 : (B * B').natDegree ≤ B.natDegree + B'.natDegree :=
      natDegree_mul_le
    have h2 : (B * B' * H.f).natDegree ≤ (B * B').natDegree + H.f.natDegree :=
      natDegree_mul_le
    omega

  have ha_le : a.natDegree ≤ max (A * A').natDegree (B * B' * H.f).natDegree := by
    rw [ha]; exact natDegree_sub_le (A * A') (B * B' * H.f)

  have hb_le : b.natDegree ≤ max (A' * B).natDegree (A * B').natDegree := by
    rw [hb]; exact natDegree_sub_le (A' * B) (A * B')

  -- `(A*A').natDegree ≤ M'`: from `hAA'` (`deg(AA') ≤ deg A + deg A'`) and
  -- `2 deg A ≤ M'`, `2 deg A' ≤ M'` (both plain, always available).
  have haa'_M : ((A * A').natDegree : ℤ) ≤
      max (2 * (A'.natDegree : ℤ))
        (if B' = 0 then 0 else 2 * (B'.natDegree : ℤ) + 5) := by
    have hcast : ((A * A').natDegree : ℤ) ≤
        (A.natDegree : ℤ) + (A'.natDegree : ℤ) := by
      exact_mod_cast hAA'
    by_cases hB'0 : B' = 0
    · rw [if_pos hB'0] at hA_M' hA'_M' ⊢; omega
    · rw [if_neg hB'0] at hA_M' hA'_M' ⊢; omega

  -- `(B*B'*f).natDegree ≤ M'`. Case split on `B = 0` and `B' = 0`
  -- separately since `hB_bound`/`hB'_bound` are conditional facts.
  have hbbf_M : ((B * B' * H.f).natDegree : ℤ) ≤
      max (2 * (A'.natDegree : ℤ))
        (if B' = 0 then 0 else 2 * (B'.natDegree : ℤ) + 5) := by
    by_cases hB0 : B = 0
    · subst hB0
      simp only [zero_mul, natDegree_zero, Nat.cast_zero]
      by_cases hB'0 : B' = 0
      · have h := hA'_M'; rw [if_pos hB'0] at h ⊢; omega
      · have h := hA'_M'; rw [if_neg hB'0] at h ⊢; omega
    · by_cases hB'0 : B' = 0
      · subst hB'0
        simp only [mul_zero, zero_mul, natDegree_zero, Nat.cast_zero]
        simp
      · have hcast : ((B * B' * H.f).natDegree : ℤ) ≤
            (B.natDegree : ℤ) + (B'.natDegree : ℤ) + (H.f.natDegree : ℤ) := by
          exact_mod_cast hBB'f
        rw [hdeg] at hcast
        have h1 := hB_bound hB0
        have h2 := hB'_bound hB'0
        rw [if_neg hB'0] at h1 h2 ⊢
        omega

  have ha_M : (a.natDegree : ℤ) ≤
      max (2 * (A'.natDegree : ℤ))
        (if B' = 0 then 0 else 2 * (B'.natDegree : ℤ) + 5) := by
    have hab_le' : (a.natDegree : ℤ) ≤
        max ((A * A').natDegree : ℤ) ((B * B' * H.f).natDegree : ℤ) := by
      exact_mod_cast ha_le
    exact le_trans hab_le' (max_le haa'_M hbbf_M)

  -- `(A'*B).natDegree ≤ M'`: from `deg(A'B) ≤ deg A' + deg B`, `2 deg A' ≤ M'`
  -- always, and (if `B ≠ 0`) `2 deg B + 5 ≤ M'`.
  have hA'B_M : ((A' * B).natDegree : ℤ) ≤
      max (2 * (A'.natDegree : ℤ))
        (if B' = 0 then 0 else 2 * (B'.natDegree : ℤ) + 5) := by
    have hcast : ((A' * B).natDegree : ℤ) ≤
        (A'.natDegree : ℤ) + (B.natDegree : ℤ) := by
      exact_mod_cast (show (A' * B).natDegree ≤
        A'.natDegree + B.natDegree from natDegree_mul_le)
    by_cases hB0 : B = 0
    · subst hB0
      simp only [mul_zero, natDegree_zero, Nat.cast_zero]
      by_cases hB'0 : B' = 0
      · have h := hA'_M'; rw [if_pos hB'0] at h ⊢; omega
      · have h := hA'_M'; rw [if_neg hB'0] at h ⊢; omega
    · have h := hB_bound hB0
      by_cases hB'0 : B' = 0
      · rw [if_pos hB'0] at h ⊢; omega
      · rw [if_neg hB'0] at h ⊢; omega

  -- `(A*B').natDegree ≤ M'`: from `deg(AB') ≤ deg A + deg B'`, `2 deg A ≤ M'`
  -- always, and (if `B' ≠ 0`) `2 deg B' + 5 ≤ M'`.
  have hAB'_M : ((A * B').natDegree : ℤ) ≤
      max (2 * (A'.natDegree : ℤ))
        (if B' = 0 then 0 else 2 * (B'.natDegree : ℤ) + 5) := by
    have hcast : ((A * B').natDegree : ℤ) ≤
        (A.natDegree : ℤ) + (B'.natDegree : ℤ) := by
      exact_mod_cast (show (A * B').natDegree ≤
        A.natDegree + B'.natDegree from natDegree_mul_le)
    by_cases hB'0 : B' = 0
    · subst hB'0
      simp only [mul_zero, natDegree_zero, Nat.cast_zero]
      simp
    · have h := hB'_bound hB'0
      rw [if_neg hB'0] at h ⊢
      omega

  have hb_M : (b.natDegree : ℤ) ≤
      max (2 * (A'.natDegree : ℤ))
        (if B' = 0 then 0 else 2 * (B'.natDegree : ℤ) + 5) := by
    have hb_le' : (b.natDegree : ℤ) ≤
        max ((A' * B).natDegree : ℤ) ((A * B').natDegree : ℤ) := by
      exact_mod_cast hb_le
    exact le_trans hb_le' (max_le hA'B_M hAB'_M)

  -- `hcdeg`: `c.natDegree` EQUALS `M'`, not just `≤ M'`. Needed because
  -- `ha_M`/`hb_M` only give `≤ M'`, and we need the *sharper* comparison
  -- against `c.natDegree` itself. The two terms of `c = A'^2 - B'^2*f` have
  -- degrees `2 dA'` (even) and `2 dB'+5` (odd) respectively when `B' ≠ 0`,
  -- so they can never be equal and cancel — the larger one always survives
  -- as `c`'s degree exactly.
  have hcdeg : (c.natDegree : ℤ) =
      max (2 * (A'.natDegree : ℤ))
        (if B' = 0 then 0 else 2 * (B'.natDegree : ℤ) + 5) := by
    by_cases hB'0 : B' = 0
    · have hcval : c = A' ^ 2 := by
        rw [hc, hB'0, zero_pow two_ne_zero, zero_mul, sub_zero]
      have hcdeg' : c.natDegree = 2 * A'.natDegree := by
        rw [hcval]; exact natDegree_pow A' 2
      rw [hcdeg', if_pos hB'0]
      have hnonneg : (0 : ℤ) ≤ 2 * (A'.natDegree : ℤ) := by positivity
      push_cast
      rw [max_eq_left hnonneg]
    · have hA'2 : (A' ^ 2).natDegree = 2 * A'.natDegree := natDegree_pow A' 2
      have hB'2f : (B' ^ 2 * H.f).natDegree = 2 * B'.natDegree + 5 := by
        rw [natDegree_mul (pow_ne_zero 2 hB'0) hf, natDegree_pow B' 2, hdeg]
      have hdeg_ne : (A' ^ 2).natDegree ≠ (B' ^ 2 * H.f).natDegree := by
        rw [hA'2, hB'2f]; omega
      rw [if_neg hB'0]
      rcases lt_or_gt_of_ne hdeg_ne with hlt | hgt
      · have hcdeg' : c.natDegree = (B' ^ 2 * H.f).natDegree := by
          rw [hc]; exact natDegree_sub_eq_right_of_natDegree_lt hlt
        rw [hcdeg', hB'2f]; push_cast; omega
      · have hcdeg' : c.natDegree = (A' ^ 2).natDegree := by
          rw [hc]; exact natDegree_sub_eq_left_of_natDegree_lt hgt
        rw [hcdeg', hA'2]; push_cast; omega

  rw [ordInfOfPair_eq_of_ne a b habne]
  have hc_zero_pair : ¬ (c = 0 ∧ (0 : k[X]) = 0) := by simp [hcne]
  rw [ordInfOfPair_eq_of_ne c 0 hc_zero_pair]

  have ha_c : (2 : ℤ) * a.natDegree ≤ 2 * c.natDegree := by
    rw [hcdeg]
    have h := ha_M
    omega

  rw [if_pos (rfl : (0 : k[X]) = 0)]
  have hrhs : max (2 * (c.natDegree : ℤ)) (0 : ℤ) = 2 * c.natDegree :=
    max_eq_left (by positivity)
  rw [hrhs]

  by_cases hb0 : b = 0
  · subst hb0
    rw [if_pos (rfl : (0 : k[X]) = 0)]
    have hlhs : max (2 * (a.natDegree : ℤ)) (0 : ℤ) = 2 * a.natDegree :=
      max_eq_left (by positivity)
    rw [hlhs, ge_iff_le, neg_le_neg_iff]
    exact ha_c
  · have hb_c : 2 * (b.natDegree : ℤ) + 5 ≤ 2 * c.natDegree := by
      rw [hcdeg]
      by_cases hB0 : B = 0
      · -- `B = 0`: `b = A'*0 - A*B' = -A*B'`, so `b.natDegree = (A*B').natDegree`
        -- exactly (up to the `neg`, which `natDegree` ignores).
        subst hB0
        have hbval : b.natDegree = (A * B').natDegree := by
          rw [hb]; simp
        rw [hbval]
        by_cases hB'0 : B' = 0
        · -- Then `b = -(A*0) = 0`, contradicting `hb0`.
          exfalso; apply hb0; rw [hb]; simp [hB'0]
        · have hAB'deg : (A * B').natDegree = A.natDegree + B'.natDegree := by
            rcases eq_or_ne A 0 with hA0 | hA0
            · exfalso; apply hb0; rw [hb, hA0]; simp
            · exact natDegree_mul hA0 hB'0
          rw [hAB'deg]
          have h2 := hB'_bound hB'0
          have h4 := hA_M'
          rw [if_neg hB'0] at h2 h4 ⊢
          omega
      · by_cases hB'0 : B' = 0
        · -- `B' = 0`: `b = A'*B - A*0 = A'*B`, so `b.natDegree = (A'*B).natDegree`
          -- exactly.
          subst hB'0
          have hbval : b.natDegree = (A' * B).natDegree := by
            rw [hb]; simp
          rw [hbval]
          have hA'Bdeg : (A' * B).natDegree = A'.natDegree + B.natDegree := by
            rcases eq_or_ne A' 0 with hA'0 | hA'0
            · exfalso; apply hb0; rw [hb, hA'0]; simp
            · exact natDegree_mul hA'0 hB0
          rw [hA'Bdeg]
          have h1 := hB_bound hB0
          have h3 := hA'_M'
          simp at h1 h3 ⊢
          omega
        · -- Both `B ≠ 0` and `B' ≠ 0`: fall back to the subadditive bound
          -- `b.natDegree ≤ max(dA'+dB, dA+dB')`, each branch closed by the
          -- matching pair of conditional bounds.
          have hb_le' : (b.natDegree : ℤ) ≤
              max ((A' * B).natDegree : ℤ) ((A * B').natDegree : ℤ) := by
            exact_mod_cast hb_le
          have hA'B_cast : ((A' * B).natDegree : ℤ) ≤
              (A'.natDegree : ℤ) + (B.natDegree : ℤ) := by
            exact_mod_cast (show (A' * B).natDegree ≤ A'.natDegree + B.natDegree
              from natDegree_mul_le)
          have hAB'_cast : ((A * B').natDegree : ℤ) ≤
              (A.natDegree : ℤ) + (B'.natDegree : ℤ) := by
            exact_mod_cast (show (A * B').natDegree ≤ A.natDegree + B'.natDegree
              from natDegree_mul_le)
          have h1 := hB_bound hB0
          have h2 := hB'_bound hB'0
          have h3 := hA'_M'
          have h4 := hA_M'
          rw [if_neg hB'0] at h1 h2 h3 h4 ⊢
          omega
    rw [if_neg hb0]
    have hab_le : max (2 * (a.natDegree : ℤ)) (2 * (b.natDegree : ℤ) + 5) ≤
        2 * c.natDegree := max_le ha_c hb_c
    rw [ge_iff_le, neg_le_neg_iff]
    exact hab_le






end HyperellipticPolynomial

namespace HyperellipticPolynomial

open Divisor

variable {H} [IsAlgClosed k] [IsDedekindDomain (CoordinateRing H)]

/-! ## §6. `b = 0`, via the `ordInfOfPair`/infinity route

Mirrors `LPairFinrankOne.lean`'s `num_B_eq_zero_of_isPoleBoundedAtPair`
exactly, specialized to the rationalized witness `(a,b,c,0)`: the
denominator's `B'`-slot is already `0` here (by §1's construction), so
`ordInfOfPair c 0 = -2 * c.natDegree ≥ -4` (from §5's `c.natDegree ≤ 2`)
directly supplies the `≥ -2`-shaped hypothesis... except §5 only gives
`≥ -4`, one notch too weak for `num_B_eq_zero_of_isPoleBoundedAtPair`'s exact
`-2` threshold as stated there. Re-examining: that lemma's hypothesis
`h_denom_ord : ordInfOfPair A' B' ≥ -2` was tuned to the *original*
(unrationalized) `A'` before §1's conjugate multiplication — post-
rationalization, `c`'s degree bound is looser (≤ 2 vs whatever `A'` had
before), so the numeric threshold genuinely needs rederiving here rather
than reused verbatim. Redone below directly from `ordInfOfPair`'s
definition and the *same* `IsPoleBoundedAtPair'`-style infinity inequality,
using the correct (weaker, `≥ -4`) bound and re-deriving what's actually
needed: if `b ≠ 0`, `ordInfOfPair a b ≤ -5` (2·deg b + 5 term dominates the
max, exactly as in the original lemma's proof), which combined with
`ordInfOfPair a b ≥ ordInfOfPair c 0 ≥ -4` (infinity clause of
`IsPoleBoundedAtPair'` for `(a,b,c,0)`, chained through §5) is already a
contradiction (`-5 ≥ -4` is false) — so the weaker `≤ 2` bound on `c` is
in fact already enough, no retightening to `≤ 1` needed. -/

/-- **`b = 0` for the rationalized, degree-bounded witness.** Direct
analogue of `num_B_eq_zero_of_isPoleBoundedAtPair`, redone with the
threshold that actually matches §5's `c.natDegree ≤ 2` bound (`-4`, not
`-2`) — see the section docstring above for why `-4` already suffices. -/
theorem b_eq_zero_of_rationalized_pole_bounded (a b c : k[X])
    (hinf : ordInfOfPair a b ≥ ordInfOfPair c (0 : k[X]))
    (hcdeg : c.natDegree ≤ 2) :
    b = 0 := by
  by_contra hbne
  have hcinf : ordInfOfPair c (0 : k[X]) ≥ -4 := by
    dsimp [ordInfOfPair]
    by_cases hc0 : c = 0
    · simp [hc0]
    · rw [if_neg (fun h => hc0 h.1), if_pos rfl]
      have : (c.natDegree : ℤ) ≤ 2 := by exact_mod_cast hcdeg
      omega
  have hableneg5 : ordInfOfPair a b ≤ -5 := by
    dsimp [ordInfOfPair]
    have hab : ¬ (a = 0 ∧ b = 0) := fun h => hbne h.2
    rw [if_neg hab, if_neg hbne]
    have hbnn : (0 : ℤ) ≤ 2 * (b.natDegree : ℤ) := by positivity
    have hmaxge : (2 * (b.natDegree : ℤ) + 5) ≤
        max (2 * (a.natDegree : ℤ)) (2 * (b.natDegree : ℤ) + 5) := le_max_right _ _
    linarith
  linarith [hinf, hcinf, hableneg5]

end HyperellipticPolynomial

namespace HyperellipticPolynomial

open Divisor

variable {H} [IsAlgClosed k] [IsDedekindDomain (CoordinateRing H)]

/-- **Bridge: `LPairCarrier ⊆ LPairCarrier'`.** Every witness pair satisfying
the weak, separate-clause `IsPoleBoundedAtPair` also satisfies the
`ordAtFrac`-based `IsPoleBoundedAtPair'` — no reducedness/lowest-terms fact
about the witness is needed for this direction, only for the (unrelated)
coprimality step downstream. Two ingredients, both already proved: the
pointwise clause rewrites via `ordAtFrac_ge_of_isPoleBoundedAtPair_pointwise`
(pure `ordAt` subtraction, `omega`-level), and the extra
`toPair H A B ≠ 0` field of `IsPoleBoundedAtPair'` is supplied by case-splitting
on whether the numerator vanishes: if it does, `z = 0 ∈ LPairCarrier'` via the
carrier's own `Or.inl` clause (no witness pair needed at all); otherwise the
same `(A,B,A',B')` witness transports directly. -/
theorem LPairCarrier_subset_LPairCarrier' (x₁ x₂ : H.Point) :
    LPairCarrier x₁ x₂ ⊆ LPairCarrier' x₁ x₂ := by
  rintro z ⟨A, B, A', B', ⟨hA'B'ne, hinfle, hptwise⟩, hz_eq⟩
  by_cases hAB0 : toPair H A B = 0
  · refine Or.inl ?_
    rw [hz_eq]
    unfold polePairToFraction
    rw [hAB0, map_zero, zero_div]
  · refine Or.inr ⟨A, B, A', B', ⟨hAB0, hA'B'ne, hinfle, ?_⟩, hz_eq⟩
    exact ordAtFrac_ge_of_isPoleBoundedAtPair_pointwise x₁ x₂ A B A' B' hptwise
    



omit [IsAlgClosed k] in
/-- **`ordAtSpec`-analogue of `ordAtFrac_ge_of_isPoleBoundedAtPair_pointwise`.**
Same pure-unfolding argument (`ordAtSpec v A B - ordAtSpec v A' B'` is
literally the LHS of `IsPoleBoundedAtPairSpec'`'s pointwise clause, matching
`IsPoleBoundedAtPairSpec`'s pointwise clause rearranged), transcribed from
`P : H.Point` to `v : HeightOneSpectrum (CoordinateRing H)`. Needed to feed
the witness pulled out of `LPairCarrierSpec` membership into
`IsPoleBoundedAtPairSpec'`'s shape without first rationalizing. -/
theorem ordAtSpec_sub_ge_of_isPoleBoundedAtPairSpec_pointwise (x₁ x₂ : H.Point)
    (A B A' B' : k[X])
    (hptwise : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      ordAtSpec v A B ≥ ordAtSpec v A' B' -
        ((if v = pointHeightOne' x₁ then 1 else 0) + (if v = pointHeightOne' x₂ then 1 else 0)))
    (v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H)) :
    ordAtSpec v A B - ordAtSpec v A' B' ≥
      -((if v = pointHeightOne' x₁ then 1 else 0) + (if v = pointHeightOne' x₂ then 1 else 0)) := by
  have := hptwise v
  omega

omit [IsAlgClosed k] in
/-- **Bridge: `LPairCarrierSpec ⊆ LPairCarrierSpec'`.** The general-`k`
analogue of `LPairCarrier_subset_LPairCarrier'` — same proof shape (case-split
on whether the numerator vanishes, otherwise transport the witness pair
directly), using `IsPoleBoundedAtPairSpec`'s `HeightOneSpectrum`-indexed
pointwise clause and `ordAtSpec_sub_ge_of_isPoleBoundedAtPairSpec_pointwise`
in place of the `H.Point`-only originals. This is the real fix this file's
`uniqueDegree2MapToP1_ordAtFrac` needs: callers holding a `LPairCarrierSpec`
witness (the general-`k`-correct carrier, `RiemannRochGenus2.lean` §1b) can
now reach `LPairCarrierSpec'` without first funneling through the lossy
`H.Point`-only `LPairCarrier`/`LPairCarrier'` pair. -/
theorem LPairCarrierSpec_subset_LPairCarrierSpec' (x₁ x₂ : H.Point) :
    LPairCarrierSpec x₁ x₂ ⊆ LPairCarrierSpec' x₁ x₂ := by
  rintro z ⟨A, B, A', B', ⟨hA'B'ne, hinfle, hptwise⟩, hz_eq⟩
  by_cases hAB0 : toPair H A B = 0
  · refine Or.inl ?_
    rw [hz_eq]
    unfold polePairToFraction
    rw [hAB0, map_zero, zero_div]
  · refine Or.inr ⟨A, B, A', B', ⟨hAB0, hA'B'ne, hinfle, ?_⟩, hz_eq⟩
    exact ordAtSpec_sub_ge_of_isPoleBoundedAtPairSpec_pointwise x₁ x₂ A B A' B' hptwise

/-! ## §7. Assembly: `uniqueDegree2MapToP1`, no `hreduced` needed

Chains §1 (rationalize) → §5/§6 (`b = 0`, `deg c ≤ 2`) → `ordAt_linX_eq`
(already-proved Möbius-transform pole computation) → contradiction with
`hne : x₂ ≠ Point.iota x₁`, exactly as sketched in this file's module
docstring. Only handles the genuinely nonconstant case; `z`'s constancy is
the theorem's own conclusion, reached here by deriving a contradiction from
`z` nonconstant (i.e. `a` not a constant multiple of `c`) together with the
fiber-matching argument, mirroring `fiber_eq_of_pure_rational_pole_match`'s
shape one level up. **Left as `sorry`** — this last step is the one still
requiring the actual `x₁+x₂` divisor-matching case analysis (the "4-way
split on where the rationalized numerator's root lands" mentioned in the
top-level project notes), not yet carried out here.

**Status of §4/§5, post-ChatGPT-consultation.** The original Weierstrass gap
in §4 is now resolved (no `sorry` in the main crux lemma
`exists_pole_of_isCoprimeAtRoots` itself — only in the one supporting local-
uniformizer fact `ordAt_le_one_of_ramified_num_vanish` it calls, which is
real remaining formalization work, not a mathematical gap). §5 no longer
needs a squarefreeness hypothesis on `c` at all (superseded the distinct-
root-counting approach with a multiplicity-aware one), and has one
remaining bookkeeping `sorry` wiring `c.natDegree` to its root-multiplicity
sum via standard Mathlib `Polynomial.roots` API. So everything upstream of
this theorem is now either fully proved or has an isolated, clearly-scoped
`sorry` — this assembly step is the one remaining piece of genuinely new
case-analysis work for a future session (or a ChatGPT-assisted pass, per
this project's standard escalation path for hard sorries) to close.

**Wired to `LPairCarrier'`, not the bare `LPairCarrier`** (post-ChatGPT-
consultation on the coprimality gap below): `LPairCarrier`'s witness pairs
carry no reducedness/lowest-terms guarantee, which is exactly the missing
ingredient the coprimality step needs (confirmed via an explicit
counterexample — see `chatgpt_prompt_coprimality.md` — showing
`IsCoprimeAtRoots a b c` is false for a witness with a common numerator/
denominator zero). `LPairCarrier'`'s `ordAtFrac`-based pointwise clause is
representation-independent and cancels shared factors automatically, so it
is the honest hypothesis for this theorem. Callers holding only
`z ∈ LPairCarrier x₁ x₂` (e.g. `RiemannRochCrux.lean`) reach this via
`LPairCarrier_subset_LPairCarrier'` — that inclusion needs no reducedness at
all, only the pure `ordAt`-subtraction identity, so it is not blocked by the
same gap.

**Second ChatGPT consultation, on `hcop` itself.** `ordAtFrac`'s pointwise
bound (used for `hzsupp`/`hbound`) is a statement about a *difference* of
`ordAt`s, which is blind to a shared factor's size — it does NOT give
"no common zero of numerator and denominator", only a bound on the net pole
order. Concrete counterexample confirming this (ChatGPT, verified against
this file's own definitions): `f = X^5+1`, `A=B=A'=B'=1` gives
`toPair H A' B' = 1+y ≠ 0` (satisfying `IsPoleBoundedAtPair'`'s nonzero
hypothesis) yet the rationalized triple is `a=c=-X^5, b=0` — all three
vanish at `α=0`, so `IsCoprimeAtRoots a b c` is false for this witness. So
`hcop` genuinely cannot be proved from `hzsupp`/`hbound` alone; the fix is a
**reduction step**, not a cleverer direct proof.

**Resolution, `reduce_ordAtFrac_triple` below.** Rather than reducing the
original `(A,B,A',B')` (which would need Dedekind-domain ideal theory in
`CoordinateRing H`, per ChatGPT's explicit caution against that route), the
reduction is done on the *already-rationalized* triple `(a,b,c) ∈ k[X]^3`
(post `frac_toPair_den_kx`), using ordinary `k[X]`-gcd (`k[X]` is a
Euclidean/GCD domain since `k` is a field) — dividing `(a,b,c)` by
`g := gcd (gcd a b) c` kills every common root at once, since a value `α` is
a common root of `(a,b,c)` iff it's a common root of the quotient triple's
gcd, and dividing by the *full* gcd forces that quotient-gcd to be a unit
(root-free, as a nonzero constant). This is cheap precisely because it acts
after rationalization: `(a,b,c)` are plain `k[X]` polynomials, so no
`CoordinateRing`-level factorization is needed, matching ChatGPT's
"rank-2 `k[X]` representation" suggestion. Verified against the counter-
example above: `g = X^5` there, reducing to `a₀=b₀... ` — actually
`a₀=c₀=-1, b₀=0`, genuinely coprime, correctly identifying `z=1` (constant)
as the true value of `(1+y)/(1+y)`. -/

/-- **`ordInfOfPair` shifts by `-2·deg g` under multiplying both slots by a
common nonzero factor `g`.** Pure `k[X]`-degree arithmetic: `natDegree`
is additive under multiplication in a domain (`Polynomial.natDegree_mul`),
so `ordInfOfPair (g*A) (g*B) = -max(2 deg(g*A), 2 deg(g*B)+5) =
-(2 deg g) - max(2 deg A, 2 deg B + 5) = ordInfOfPair A B - 2 deg g` (the
`(0,0)` case is excluded by `hAB`, and needs `g ≠ 0` throughout so
`g*A = 0 ↔ A = 0` etc.). Two-sided (`A,B` and `A',B'` sharing the same `g`)
so callers get the exact shift cancellation needed to transfer an
`ordInfOfPair` *inequality* across common-factor division. -/
theorem ordInfOfPair_mul_left (g A B : k[X]) (hg : g ≠ 0) (hAB : ¬ (A = 0 ∧ B = 0)) :
    ordInfOfPair (g * A) (g * B) = ordInfOfPair A B - 2 * (g.natDegree : ℤ) := by
  have hgAB : ¬ (g * A = 0 ∧ g * B = 0) := by
    rintro ⟨hA0, hB0⟩
    exact hAB ⟨(mul_eq_zero.mp hA0).resolve_left hg, (mul_eq_zero.mp hB0).resolve_left hg⟩
  unfold ordInfOfPair
  rw [if_neg hAB, if_neg hgAB]
  by_cases hB : B = 0
  · -- `B = 0` (so `A ≠ 0` from `hAB`), and hence `g * B = 0` too: both
    -- `if`-branches collapse to the `2 * deg` term, no `+5` on either side.
    have hA0 : A ≠ 0 := fun h => hAB ⟨h, hB⟩
    have hgB : g * B = 0 := by rw [hB, mul_zero]
    have hgA0 : g * A ≠ 0 := mul_ne_zero hg hA0
    rw [if_pos hB, if_pos hgB, Polynomial.natDegree_mul hg hA0]
    push_cast
    omega
  · -- `B ≠ 0` (hence `g * B ≠ 0`): both `if`-branches take the `+5` term,
    -- and `natDegree_mul` applies to both slots of the `max`.
    have hgB0 : g * B ≠ 0 := mul_ne_zero hg hB
    rw [if_neg hB, if_neg hgB0, Polynomial.natDegree_mul hg hB]
    by_cases hA0 : A = 0
    · simp only [hA0, mul_zero, Polynomial.natDegree_zero]
      push_cast
      omega
    · rw [Polynomial.natDegree_mul hg hA0]
      push_cast
      omega

set_option maxHeartbeats 2000000 in
-- Reduction by the triple gcd causes substantial polynomial normalization.
/-- **Reduction lemma: every nonzero-`c` rationalized triple `(a,b,c)`
reduces to a coprime-at-roots triple representing the same fraction, with
the same `ordAtFrac` pole bound at every point and the same `ordInfOfPair`
bound relation.** The `k[X]`-analogue of "put a fraction in lowest terms":
`g := gcd (gcd a b) c`; since `g ∣ c` and `c ≠ 0`, `g ≠ 0`, so
`a = g*a₀, b = g*b₀, c = g*c₀` for a unique `(a₀,b₀,c₀)` (division exact by
`gcd_dvd_*`). `polePairToFraction a b c 0 = polePairToFraction a₀ b₀ c₀ 0`
by the same shared-factor cancellation `frac_toPair_den_kx` already uses
(`toPair` is `k[X]`-linear in each slot, so `toPair H a b = algebraMap g *
toPair H a₀ b₀`, and likewise `toPair H c 0 = algebraMap g * toPair H c₀ 0`;
cancel `algebraMap g ≠ 0` via `mul_div_mul_left`, `k[X]`'s bare `gcd`/
`gcd_dvd_left`/`gcd_dvd_right` API, same as `PrincipalDivisorsDedekind.lean`'s
`isCoprime_of_irreducible_not_dvd` — MATHLIB NAME UNCONFIRMED for the exact
instance path). `ordAtFrac` then transfers for free via
`ordAtFrac_eq_of_polePairToFraction_eq` (already proved, representation-
independent for nonzero numerators); `ordInfOfPair` transfers via
`ordInfOfPair_mul_left` applied on both sides (the `-2 deg g` shift cancels
in the inequality). `IsCoprimeAtRoots a₀ b₀ c₀` is proved directly rather
than via a "quotient-gcd-is-unit" Mathlib lemma: if `α` were a shared root of
`(a₀,b₀,c₀)`, `linX α ∣ a₀,b₀,c₀` (`dvd_iff_isRoot`), so `g*(linX α) ∣ a,b,c`
(scaling by `g`), hence `g*(linX α) ∣ gcd (gcd a b) c = g` (`dvd_gcd` twice);
cancelling the nonzero `g` (`mul_dvd_mul_iff_left`) gives `linX α ∣ 1`, i.e.
`linX α` is a unit — impossible since `natDegree (linX α) = 1 ≠ 0`. This
avoids needing to name the "dividing by the full gcd leaves the quotient-gcd
a unit" lemma at all. -/
theorem reduce_ordAtFrac_triple (x₁ x₂ : H.Point) (a b c : k[X]) (hcne : c ≠ 0)
    (hab_ne : toPair H a b ≠ 0)
    (hzsupp : ∀ P : H.Point, ordAtFrac P a b c 0 ≥
      -((if P = x₁ then 1 else 0) + (if P = x₂ then 1 else 0)))
    (hinf : ordInfOfPair a b ≥ ordInfOfPair c (0 : k[X])) :
    ∃ a₀ b₀ c₀ : k[X], c₀ ≠ 0 ∧ toPair H a₀ b₀ ≠ 0 ∧
      polePairToFraction (H := H) a b c 0 = polePairToFraction (H := H) a₀ b₀ c₀ 0 ∧
      (∀ P : H.Point, ordAtFrac P a₀ b₀ c₀ 0 ≥
        -((if P = x₁ then 1 else 0) + (if P = x₂ then 1 else 0))) ∧
      ordInfOfPair a₀ b₀ ≥ ordInfOfPair c₀ (0 : k[X]) ∧
      IsCoprimeAtRoots a₀ b₀ c₀ := by
  classical
  -- `g := gcd (gcd a b) c`: the joint `k[X]`-gcd of the whole triple.
  -- `k[X]` is a `GCDMonoid` (field-coefficient polynomial ring), so the bare
  -- `gcd`/`gcd_dvd_left`/`gcd_dvd_right`/`dvd_gcd` API applies directly —
  -- MATHLIB NAME UNCONFIRMED for the exact instance path, but this is the
  -- same `gcd` used elsewhere in the project (`PrincipalDivisorsDedekind.lean`,
  -- `isCoprime_of_irreducible_not_dvd`).
  set g := gcd (gcd a b) c with hg_def
  have hg_dvd_ab : g ∣ gcd a b := gcd_dvd_left _ _
  have hg_dvd_a : g ∣ a := hg_dvd_ab.trans (gcd_dvd_left _ _)
  have hg_dvd_b : g ∣ b := hg_dvd_ab.trans (gcd_dvd_right _ _)
  have hg_dvd_c : g ∣ c := gcd_dvd_right _ _
  have hgne : g ≠ 0 := fun h => hcne (eq_zero_of_zero_dvd (h ▸ hg_dvd_c))
  -- Explicit quotient witnesses.
  obtain ⟨a₀, ha_eq⟩ := hg_dvd_a
  obtain ⟨b₀, hb_eq⟩ := hg_dvd_b
  obtain ⟨c₀, hc_eq⟩ := hg_dvd_c
  have hc₀ne : c₀ ≠ 0 := by
    intro h; apply hcne; rw [hc_eq, h, mul_zero]
  have hab₀ne : ¬ (a₀ = 0 ∧ b₀ = 0) := by
    rintro ⟨ha0, hb0⟩
    apply hab_ne
    apply toPair_eq_zero_iff H a b |>.mpr
    exact ⟨by rw [ha_eq, ha0, mul_zero], by rw [hb_eq, hb0, mul_zero]⟩
  have ha0₀ne : toPair H a₀ b₀ ≠ 0 := fun h => hab₀ne (toPair_eq_zero_iff H a₀ b₀ |>.mp h)
  -- **Numerator/denominator factorization through `toPair H g 0`.**
  have htoPair_right_zero : ∀ P : k[X],
      toPair H P (0 : k[X]) = algebraMap k[X] (CoordinateRing H) P := by
    intro P; unfold toPair; simp
  have hg_toPair_ne : toPair H g (0 : k[X]) ≠ 0 :=
    fun h => hgne (toPair_eq_zero_iff H g 0 |>.mp h).1
  have hnum : toPair H a b = toPair H g (0 : k[X]) * toPair H a₀ b₀ := by
    have hmul := toPair_mul (H := H) g 0 a₀ b₀
    have harg1 : g * a₀ + 0 * b₀ * H.f = a := by rw [← ha_eq]; ring
    have harg2 : g * b₀ + a₀ * 0 = b := by rw [← hb_eq]; ring
    rw [harg1, harg2] at hmul
    exact hmul.symm
  have hden : toPair H c (0 : k[X]) = toPair H g (0 : k[X]) * toPair H c₀ (0 : k[X]) := by
    have hmul := toPair_mul (H := H) g 0 c₀ 0
    have harg1 : g * c₀ + 0 * 0 * H.f = c := by rw [← hc_eq]; ring
    have harg2 : g * 0 + c₀ * 0 = (0 : k[X]) := by ring
    rw [harg1, harg2] at hmul
    exact hmul.symm
  -- **Fraction equality**, by cancelling `algebraMap (toPair H g 0) ≠ 0`.
  have hfrac_eq : polePairToFraction (H := H) a b c 0 =
      polePairToFraction (H := H) a₀ b₀ c₀ 0 := by
    unfold polePairToFraction
    rw [hnum, hden, map_mul, map_mul]
    have hgmap_ne : algebraMap (CoordinateRing H) (FractionRing (CoordinateRing H))
        (toPair H g (0 : k[X])) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (CoordinateRing H)
        (FractionRing (CoordinateRing H)))).mpr hg_toPair_ne
    rw [mul_div_mul_left _ _ hgmap_ne]
  -- **`ordAtFrac` transfer**, via representation-independence.
  have hc0_ne : toPair H c (0 : k[X]) ≠ 0 :=
    fun h => hcne (toPair_eq_zero_iff H c 0 |>.mp h).1
  have hc₀0_ne : toPair H c₀ (0 : k[X]) ≠ 0 :=
    fun h => hc₀ne (toPair_eq_zero_iff H c₀ 0 |>.mp h).1
  have hzsupp' : ∀ P : H.Point, ordAtFrac P a₀ b₀ c₀ 0 ≥
      -((if P = x₁ then 1 else 0) + (if P = x₂ then 1 else 0)) := by
    intro P
    rw [← ordAtFrac_eq_of_polePairToFraction_eq P a b c 0 a₀ b₀ c₀ 0
      hab_ne hc0_ne hc₀0_ne hfrac_eq]
    exact hzsupp P
  -- **`ordInfOfPair` transfer**, via the common-factor shift lemma applied to
  -- both `(a,b)` and `(c,0)` with the same `g` — the `-2 deg g` shift cancels.
  have hinf' : ordInfOfPair a₀ b₀ ≥ ordInfOfPair c₀ (0 : k[X]) := by
    have hc₀0ne : ¬ (c₀ = 0 ∧ (0 : k[X]) = 0) := by
      simpa using hc₀ne
    have hshift_ab : ordInfOfPair a b = ordInfOfPair a₀ b₀ - 2 * (g.natDegree : ℤ) := by
      rw [ha_eq, hb_eq]
      exact ordInfOfPair_mul_left g a₀ b₀ hgne hab₀ne
    have hshift_c : ordInfOfPair c (0 : k[X]) =
        ordInfOfPair c₀ (0 : k[X]) - 2 * (g.natDegree : ℤ) := by
      rw [hc_eq]
      have h := ordInfOfPair_mul_left g c₀ (0 : k[X]) hgne hc₀0ne
      simpa only [mul_zero] using h
    rw [hshift_ab, hshift_c] at hinf
    linarith
  -- **Coprimality**: no root `α` can be shared by `(a₀,b₀,c₀)`, since a
  -- shared linear factor `(X-α)` would divide `g`'s quotient triple, hence
  -- `(X-α)*g ∣ gcd (gcd a b) c = g`, forcing `X - α ∣ 1` after cancelling
  -- the nonzero `g` — impossible since `X - α` is non-unit.
  have hcop : IsCoprimeAtRoots a₀ b₀ c₀ := by
    intro α hα
    rintro ⟨hαa, hαb⟩
    have hlin_dvd_a₀ : linX α ∣ a₀ := Polynomial.dvd_iff_isRoot.mpr hαa
    have hlin_dvd_b₀ : linX α ∣ b₀ := Polynomial.dvd_iff_isRoot.mpr hαb
    have hlin_dvd_c₀ : linX α ∣ c₀ := Polynomial.dvd_iff_isRoot.mpr hα
    have hga_dvd : g * linX α ∣ a := by
      rw [ha_eq]; exact mul_dvd_mul_left g hlin_dvd_a₀
    have hgb_dvd : g * linX α ∣ b := by
      rw [hb_eq]; exact mul_dvd_mul_left g hlin_dvd_b₀
    have hgc_dvd : g * linX α ∣ c := by
      rw [hc_eq]; exact mul_dvd_mul_left g hlin_dvd_c₀
    have hgab_dvd : g * linX α ∣ gcd a b := dvd_gcd hga_dvd hgb_dvd
    have hg2_dvd : g * linX α ∣ g := dvd_gcd hgab_dvd hgc_dvd
    have hlin_dvd_one : linX α ∣ (1 : k[X]) := by
      have hg_dvd_g1 : g ∣ g * 1 := by rw [mul_one]
      have := (mul_dvd_mul_iff_left hgne).mp (hg2_dvd.trans hg_dvd_g1)
      simpa using this
    have hlin_unit : IsUnit (linX α : k[X]) := isUnit_of_dvd_one hlin_dvd_one
    have hlin_deg : (linX α : k[X]).natDegree = 1 := by
      unfold linX
      compute_degree!
    have hlin_deg0 : (linX α : k[X]).natDegree = 0 :=
      Polynomial.natDegree_eq_zero_of_isUnit hlin_unit
    omega
  exact ⟨a₀, b₀, c₀, hc₀ne, ha0₀ne, hfrac_eq, hzsupp', hinf', hcop⟩
/-! ## §7. Finishing step: `b₀ = 0`, `c₀.natDegree ≤ 2` forces `c₀` constant

**The genuinely new piece of reasoning flagged in this file's own docstring**
(`uniqueDegree2MapToP1_ordAtFrac`'s final step). With `b₀ = 0`, `z =
a₀(x)/c₀(x)` is a Möbius transform of the coordinate function `x` alone. If
`c₀` were non-constant it would have a root `α` (`k` algebraically closed);
every point `Q` with `Q.X = α` gives `ordAt Q a₀ 0 = 0` (coprimality: `a₀(α)
≠ 0` since `c₀(α) = 0`) and `ordAt Q c₀ 0 ≥ 1` (`ordAt_eq_rootMultiplicity_
unramified`/`_ramified`, root multiplicity `≥ 1`), so `Q` is a genuine pole
of `z`. Crucially, since `a₀, c₀ ∈ k[X]` don't involve `y`, this *same*
computation holds at both points of the fiber over `α` (`toPair_mem_
pointIdeal_iff` for a `B = 0`-slot pair only ever sees `Q.X`, never `Q.Y`) —
so in the unramified case (`Q.Y ≠ 0`) **both** `Q` and `ι Q` are poles,
forcing `{Q, ι Q} ⊆ {x₁, x₂}` by the pointwise pole-cap; since `Q ≠ ι Q`,
this pins `{Q, ι Q} = {x₁, x₂}` exactly, giving `x₂ = ι x₁` either way the
two points land — contradicting `hne`. In the ramified case (`Q.Y = 0`,
`ι Q = Q`) the pole order at `Q` is `≥ 2`, which already exceeds every
pointwise cap available (`≥ -1` when `x₁ ≠ x₂`, and `≥ -2` only at the
single point `x₁` when `x₁ = x₂` — but that forces `Q = x₁ = x₂`, so
`ι x₁ = ι Q = Q = x₁ = x₂`, contradicting `hne` directly without even using
the multiplicity bound). Either way `c₀` non-constant is impossible. -/

/-- **Fiber-matching contradiction lemma.** If `α` is a root of `c₀` (via a
witness point `Q` with `Q.X = α`), coprimality plus the pointwise `{x₁,x₂}`
pole cap on `(a₀,b₀,c₀,0)` (with `b₀ = 0`) forces `x₂ = Point.iota x₁` —
contradicting `hne`. Packaged as `False` directly (rather than proving the
positive `x₂ = ι x₁` fact and separately applying `hne`) since every call
site immediately wants the contradiction. -/
theorem false_of_root_of_coprimeAtRoots_zero_snd
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f) (x₁ x₂ : H.Point)
    (hne : x₂ ≠ Point.iota x₁) (a₀ c₀ : k[X]) (hc₀ne : c₀ ≠ 0)
    (hcop : IsCoprimeAtRoots a₀ 0 c₀)
    (hzsupp₀ : ∀ P : H.Point, ordAtFrac P a₀ 0 c₀ 0 ≥
      -((if P = x₁ then 1 else 0) + (if P = x₂ then 1 else 0)))
    (α : k) (hα : c₀.eval α = 0) : False := by
  classical
  -- `a₀(α) ≠ 0` by coprimality (`c₀(α) = 0`, and `(a₀,0)` can't both vanish at `α`).
  have haα : a₀.eval α ≠ 0 := fun h => hcop α hα ⟨h, by simp⟩
  -- Produce a witness point `Q` with `Q.X = α` (Weierstrass or not).
  by_cases hWeier : H.f.eval α = 0
  · -- Ramified case: unique point `Q = (α,0)`, `ι Q = Q`.
    have hQeq : H.Equation α (0 : k) := by
      show (0 : k) ^ 2 = H.f.eval α; rw [hWeier]; ring
    set Q : H.Point := Point.mk α 0 hQeq with hQ_def
    have hQX : Q.X = α := rfl
    have hQY : Q.Y = 0 := rfl
    have hordc : ordAt Q c₀ (0 : k[X]) = 2 * (c₀.rootMultiplicity α : ℤ) :=
      ordAt_eq_rootMultiplicity_ramified hsf c₀ hc₀ne α Q (pointIdeal_ne_bot Q) hQX hQY
    have hmpos : (c₀.rootMultiplicity α : ℤ) ≥ 1 := by
      have hroot : c₀.IsRoot α := hα
      have hpos : 0 < c₀.rootMultiplicity α := (Polynomial.rootMultiplicity_pos hc₀ne).mpr hroot
      exact_mod_cast hpos
    have hnotmem : toPair H a₀ (0 : k[X]) ∉ pointIdeal Q := by
      rw [toPair_mem_pointIdeal_iff]; simp only [hQX, hQY, mul_zero, add_zero]; exact haα
    have hordab : ordAt Q a₀ (0 : k[X]) = 0 := ordAt_eq_zero_of_notMem Q a₀ 0 hnotmem
    have hboundQ := hzsupp₀ Q
    unfold ordAtFrac at hboundQ
    rw [hordab, hordc] at hboundQ
    -- `hboundQ : 0 - 2*m ≥ -(ind x₁ + ind x₂)`, with `m ≥ 1`, so the RHS
    -- indicator sum is `≥ 2`, forcing `Q = x₁` (and, if `x₁ ≠ x₂`, also
    -- `Q = x₂`, which would force `x₁ = x₂` — either way `Q = x₁ = x₂`
    -- whenever both indicators are needed, since a single indicator only
    -- contributes `1`).
    have hsum_ge : (2 : ℤ) ≤
        (if Q = x₁ then 1 else 0) + (if Q = x₂ then 1 else 0) := by
      linarith [hboundQ, hmpos]
    have hQ1 : Q = x₁ := by
      by_contra hQ1
      by_cases hQ2 : Q = x₂
      · have h := hsum_ge
        simp only [if_neg hQ1, if_pos hQ2] at h
        omega
      · have h := hsum_ge
        simp only [if_neg hQ1, if_neg hQ2] at h
        omega
    have hQ2 : Q = x₂ := by
      by_contra hQ2
      by_cases hQ1 : Q = x₁
      · have h := hsum_ge
        simp only [if_pos hQ1, if_neg hQ2] at h
        omega
      · have h := hsum_ge
        simp only [if_neg hQ1, if_neg hQ2] at h
        omega
    have hιQeq : Point.iota Q = Q := by
      apply Subtype.ext
      apply Prod.ext
      · exact Point.iota_X Q
      · calc
          (Point.iota Q).Y = -Q.Y := Point.iota_Y Q
          _ = Q.Y := by rw [hQY]; simp
    apply hne
    calc
      x₂ = Q := hQ2.symm
      _ = Point.iota Q := hιQeq.symm
      _ = Point.iota x₁ := congrArg Point.iota hQ1
  · -- Unramified case: two points `Q, ι Q` over `α`, both genuine poles.
    obtain ⟨β, hβ⟩ : ∃ β : k, β ^ 2 = H.f.eval α := IsAlgClosed.exists_pow_nat_eq
      (H.f.eval α) (n := 2) (by norm_num)
    have hβne : β ≠ 0 := by
      intro h
      rw [h] at hβ
      simp at hβ
      exact hWeier hβ.symm
    have hQeq : H.Equation α β := by
      show β ^ 2 = H.f.eval α
      exact hβ
    set Q : H.Point := Point.mk α β hQeq with hQ_def
    have hQX : Q.X = α := rfl
    have hQY : Q.Y = β := rfl
    have hQYne : Q.Y ≠ 0 := hQY ▸ hβne
    have hιQX : (Point.iota Q).X = α := by
      rw [Point.iota_X]
      exact hQX
    have hιQYne : (Point.iota Q).Y ≠ 0 := by
      rw [Point.iota_Y]
      exact neg_ne_zero.mpr hQYne
    have hQIneQ : Point.iota Q ≠ Q :=
      Point.iota_ne_self_of_Y_ne_zero hchar hQYne
    have hordabQ : ordAt Q a₀ (0 : k[X]) = 0 := by
      apply ordAt_eq_zero_of_notMem
      rw [toPair_mem_pointIdeal_iff]
      simpa [hQX] using haα
    have hordabιQ : ordAt (Point.iota Q) a₀ (0 : k[X]) = 0 := by
      apply ordAt_eq_zero_of_notMem
      rw [toPair_mem_pointIdeal_iff]
      simpa [hιQX] using haα
    have hmpos : (c₀.rootMultiplicity α : ℤ) ≥ 1 := by
      have hroot : c₀.IsRoot α := hα
      have hpos : 0 < c₀.rootMultiplicity α :=
        (Polynomial.rootMultiplicity_pos hc₀ne).mpr hroot
      exact_mod_cast hpos
    have hordcQ : ordAt Q c₀ (0 : k[X]) = (c₀.rootMultiplicity α : ℤ) :=
      ordAt_eq_rootMultiplicity_unramified hchar c₀ hc₀ne α Q
        (pointIdeal_ne_bot Q) hQX hQYne
    have hordcιQ : ordAt (Point.iota Q) c₀ (0 : k[X]) =
        (c₀.rootMultiplicity α : ℤ) :=
      ordAt_eq_rootMultiplicity_unramified hchar c₀ hc₀ne α (Point.iota Q)
        (pointIdeal_ne_bot _) hιQX hιQYne
    have hboundQ := hzsupp₀ Q
    have hboundιQ := hzsupp₀ (Point.iota Q)
    unfold ordAtFrac at hboundQ hboundιQ
    rw [hordabQ, hordcQ] at hboundQ
    rw [hordabιQ, hordcιQ] at hboundιQ
    have hQmem : Q = x₁ ∨ Q = x₂ := by
      by_cases hQ1 : Q = x₁
      · exact Or.inl hQ1
      by_cases hQ2 : Q = x₂
      · exact Or.inr hQ2
      exfalso
      have h : -(c₀.rootMultiplicity α : ℤ) ≥ 0 := by
        simpa only [if_neg hQ1, if_neg hQ2, sub_eq_add_neg, zero_add,
          neg_zero, add_zero] using hboundQ
      linarith
    have hιQmem : Point.iota Q = x₁ ∨ Point.iota Q = x₂ := by
      by_cases hQ1 : Point.iota Q = x₁
      · exact Or.inl hQ1
      by_cases hQ2 : Point.iota Q = x₂
      · exact Or.inr hQ2
      exfalso
      have h : -(c₀.rootMultiplicity α : ℤ) ≥ 0 := by
        simpa only [if_neg hQ1, if_neg hQ2, sub_eq_add_neg, zero_add,
          neg_zero, add_zero] using hboundιQ
      linarith
    apply hne
    rcases hQmem with hQ1 | hQ2
    · rcases hιQmem with hιQ1 | hιQ2
      · exact False.elim (hQIneQ (hιQ1.trans hQ1.symm))
      · exact hιQ2.symm.trans (congrArg Point.iota hQ1)
    · rcases hιQmem with hιQ1 | hιQ2
      · calc
          x₂ = Q := hQ2.symm
          _ = Point.iota (Point.iota Q) := (Point.iota_iota Q).symm
          _ = Point.iota x₁ := congrArg Point.iota hιQ1
      · exact False.elim (hQIneQ (hιQ2.trans hQ2.symm))
set_option maxHeartbeats 5000000 in
-- The proof performs substantial dependent-polynomial normalization.
theorem uniqueDegree2MapToP1_ordAtFrac (hdeg : H.f.natDegree = 5) (hchar : (2 : k) ≠ 0)
    (hsf : Squarefree H.f) (x₁ x₂ : H.Point) (hne : x₂ ≠ Point.iota x₁)
    (z : FractionRing (CoordinateRing H)) (hz : z ∈ LPairCarrier' x₁ x₂) :
    IsConstantFraction z := by
  classical
  rcases hz with hz0 | ⟨A, B, A', B', hbound, hz_eq⟩
  · -- `z = 0`, trivially constant (`c = 0`).
    exact ⟨0, by rw [hz0]; simp⟩
  · obtain ⟨hAB0ne, hA'B'ne, hinfle, hptwise'⟩ := hbound
    -- Rationalize via §1, then run §5/§6/`ordAt_linX_eq`.
    have hA'B'toPairne : toPair H A' B' ≠ 0 := by
      rw [Ne, toPair_eq_zero_iff]; exact hA'B'ne
    obtain ⟨a, b, c, hcne, hc_def, ha_def, hb_def, hfrac_eq⟩ :=
      frac_toPair_den_kx hdeg A B A' B' hA'B'toPairne
    -- The original witness's pointwise bound is already `ordAtFrac`-shaped
    -- (`hptwise'`, from `IsPoleBoundedAtPair'` membership) — no separate
    -- bridge step needed here, unlike the old `LPairCarrier`-based proof.
    -- **Step (1): transport `hptwise'` to the rationalized witness
    -- `(a,b,c,0)`.** Needs `toPair H a b ≠ 0` (i.e. `z ≠ 0` in the new
    -- representation) as the side condition for
    -- `ordAtFrac_eq_of_polePairToFraction_eq`.
    have hab_ne : toPair H a b ≠ 0 := by
      intro hab0
      apply hAB0ne
      have hzero_frac : polePairToFraction (H := H) a b c 0 = 0 := by
           unfold polePairToFraction
           rw [hab0, map_zero, zero_div]
      rw [hzero_frac] at hfrac_eq
      unfold polePairToFraction at hfrac_eq
      have hA'B'map_ne :
           algebraMap (CoordinateRing H) (FractionRing (CoordinateRing H))
             (toPair H A' B') ≠ 0 :=
           (map_ne_zero_iff _ (IsFractionRing.injective (CoordinateRing H)
           (FractionRing (CoordinateRing H)))).mpr hA'B'toPairne
      have hABmap0 :
           algebraMap (CoordinateRing H) (FractionRing (CoordinateRing H))
             (toPair H A B) = 0 := by
           rcases div_eq_zero_iff.mp hfrac_eq with h | h
           · exact h
           · exact absurd h hA'B'map_ne
      exact
        (map_eq_zero_iff _ (IsFractionRing.injective (CoordinateRing H)
          (FractionRing (CoordinateRing H)))).mp hABmap0
    have hc0_ne : toPair H c (0 : k[X]) ≠ 0 := by
      rw [Ne, toPair_eq_zero_iff]; exact fun h => hcne h.1
    have hzsupp : ∀ P : H.Point, ordAtFrac P a b c 0 ≥
        -((if P = x₁ then 1 else 0) + (if P = x₂ then 1 else 0)) := by
      intro P
      rw [← ordAtFrac_eq_of_polePairToFraction_eq P A B A' B' a b c 0
        hAB0ne hA'B'toPairne hc0_ne hfrac_eq]
      exact hptwise' P
    -- **`ordInfOfPair` bound for `(a,b,c)`**, via the pure-`k[X]`-degree-
    -- arithmetic bridge lemma `ordInfOfPair_rationalized_ge` (§5c), fed
    -- `hinfle` (the original witness's infinity bound) and the explicit
    -- polynomial identities `ha_def`/`hb_def`/`hc_def` — computed *before*
    -- the coprimality reduction below, since this identity-based route only
    -- applies to `(a,b,c)` themselves (tied to `A,B,A',B'` via `ha_def` etc.),
    -- not to any reduced witness that no longer satisfies those identities.
    have hinf : ordInfOfPair a b ≥ ordInfOfPair c (0 : k[X]) := by
      have hABne : ¬ (A = 0 ∧ B = 0) := fun h => hAB0ne (by rw [toPair_eq_zero_iff]; exact h)
      have habne : ¬ (a = 0 ∧ b = 0) := fun h => hab_ne (by rw [toPair_eq_zero_iff]; exact h)
      have hc_def' : c = A' ^ 2 - B' ^ 2 * H.f := by rw [hc_def]; rfl
      exact ordInfOfPair_rationalized_ge hdeg A B A' B' hABne hA'B'ne hinfle a b c
        ha_def hb_def hc_def' habne hcne
    -- **Step (2): coprimality.** Genuinely new content, not derivable from
    -- `hzsupp`/`hbound` alone (see this file's §4/§5 docstrings and the
    -- accompanying `chatgpt_prompt_coprimality.md` consultation prompt for why
    -- a shared root of `(a,b,c)` isn't immediately ruled out by pole-
    -- boundedness). Resolved via `reduce_ordAtFrac_triple`: reduce `(a,b,c)`
    -- to a coprime-at-roots `(a₀,b₀,c₀)` representing the same fraction, with
    -- `hzsupp`/`hinf` transported automatically. Steps (3) onward now run on
    -- `(a₀,b₀,c₀)` instead of `(a,b,c)`.
    have hred : ∃ a₀ b₀ c₀ : k[X],
        c₀ ≠ 0 ∧ toPair H a₀ b₀ ≠ 0 ∧
        polePairToFraction (H := H) a b c 0 =
          polePairToFraction (H := H) a₀ b₀ c₀ 0 ∧
        (∀ P : H.Point, ordAtFrac P a₀ b₀ c₀ 0 ≥
          -((if P = x₁ then 1 else 0) + (if P = x₂ then 1 else 0))) ∧
        ordInfOfPair a₀ b₀ ≥ ordInfOfPair c₀ (0 : k[X]) ∧
        IsCoprimeAtRoots a₀ b₀ c₀ := by
      exact reduce_ordAtFrac_triple (H := H) x₁ x₂ a b c hcne hab_ne hzsupp hinf
    obtain ⟨a₀, b₀, c₀, hc₀ne, hab₀_ne, hfrac_eq₀, hzsupp₀, hinf₀, hcop⟩ := hred
    -- **Step (3): finish.** Case-split on `x₁ = x₂` (needed since
    -- `natDegree_le_two_of_isCoprimeAtRoots` requires `x₁ ≠ x₂`; §5b supplies
    -- the missing `x₁ = x₂` companion bound). Either way, `c₀.natDegree ≤ 2`,
    -- feeding `b_eq_zero_of_rationalized_pole_bounded` to get `b₀ = 0`, then
    -- `ordAt_linX_eq`-driven fiber matching to reach `x₂ = ιx₁`, contradicting
    -- `hne`.
    have hcdeg : c₀.natDegree ≤ 2 := by
      by_cases hx12 : x₁ = x₂
      · subst hx12
        apply natDegree_le_two_of_isCoprimeAtRoots_eq hchar hsf x₁ a₀ b₀ c₀ hc₀ne hcop
        intro P
        have h := hzsupp₀ P
        by_cases hPx : P = x₁
        · norm_num [hPx] at h ⊢
          exact h
        · norm_num [hPx] at h ⊢
          exact h
      · exact
        natDegree_le_two_of_isCoprimeAtRoots
          hchar hsf x₁ x₂ hx12 a₀ b₀ c₀ hc₀ne hcop hzsupp₀
          
    have hbeq0 : b₀ = 0 := b_eq_zero_of_rationalized_pole_bounded a₀ b₀ c₀ hinf₀ hcdeg
    subst hbeq0

    have hcdeg0 : c₀.natDegree = 0 := by
      by_contra hcdeg0
      obtain ⟨α, hα⟩ := IsAlgClosed.exists_root c₀ (by
        rw [Polynomial.degree_eq_natDegree hc₀ne]
        exact_mod_cast hcdeg0)
      exact false_of_root_of_coprimeAtRoots_zero_snd
        (H := H) hchar hsf x₁ x₂ hne a₀ c₀ hc₀ne hcop hzsupp₀ α hα

    have hadeg0 : a₀.natDegree = 0 := by
      have habne0 : a₀ ≠ 0 := by
        intro ha0
        apply hab₀_ne
        simp [ha0, toPair_eq_zero_iff]
      have horda := hinf₀
      rw [ordInfOfPair_eq_of_ne a₀ 0 (fun h => habne0 h.1)] at horda
      rw [ordInfOfPair_eq_of_ne c₀ 0 (fun h => hc₀ne h.1)] at horda
      rw [hcdeg0] at horda
      simp at horda
      omega

    obtain ⟨ka, hka⟩ := Polynomial.natDegree_eq_zero.mp hadeg0
    obtain ⟨kc, hkc⟩ := Polynomial.natDegree_eq_zero.mp hcdeg0
    refine ⟨ka / kc, ?_⟩

    have hkc_ne : kc ≠ 0 := by
      rintro rfl
      simp at hkc
      exact hc₀ne hkc.symm

    have h_inv : (algebraMap H.CoordinateRing (FractionRing H.CoordinateRing))
        ((algebraMap k[X] H.CoordinateRing) (C kc⁻¹)) =
      ((algebraMap H.CoordinateRing (FractionRing H.CoordinateRing))
        ((algebraMap k[X] H.CoordinateRing) (C kc)))⁻¹ := by
      symm
      apply inv_eq_of_mul_eq_one_right
      rw [← map_mul, ← map_mul, ← map_mul]
      rw [mul_inv_cancel₀ hkc_ne]
      simp

    rw [hz_eq, hfrac_eq, hfrac_eq₀, ← hka, ← hkc]
    unfold polePairToFraction
    simp [HyperellipticPolynomial.toPair, toPair]
    rw [div_eq_mul_inv]
    rw [div_eq_mul_inv ka kc]
    rw [map_mul, map_mul, map_mul]
    rw [h_inv]

end HyperellipticPolynomial
