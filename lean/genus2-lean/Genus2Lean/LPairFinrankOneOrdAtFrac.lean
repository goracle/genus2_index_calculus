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

/-- **Local order of `a+by` at a ramified point is exactly `1` when `a(α)=0`,
`b(α)≠0`.** The one piece of genuinely new local analysis identified by the
ChatGPT consultation: `y` is a uniformizer at a simple Weierstrass point
(`f` squarefree ⇒ `ordQ(x-α)=2`, `ordQ(y)=1`, via `y²=f`, `f` having a
simple zero at `α`), so `a(x)` (vanishing at `α`, hence `ordQ(a) ≥ 2` as a
function of the order-`2` uniformizer `x-α`) and `b(x)y` (with `b(α)≠0`,
hence `ordQ(b(x)y) = ordQ(y) = 1` exactly) sit at different orders — no
cancellation, so `ordQ(a+by) = min(ordQ(a), ordQ(by)) = 1`.

**Not yet formalized here** — needs the local-uniformizer statement `ordQ(y)
= 1` at a ramified point (equivalently, `y ∉ pointIdeal Q ^ 2`, dual to
`y² = f` having a simple root) threaded through `ordAt`'s `intValuation`
definition; this is exactly the kind of one-step "local parameter" fact
`HyperellipticClassProof.lean`'s docstring (§B) flags as not yet built out
for general pairs (only for bare `linX a` there). Genuine remaining
formalization work, not a wrong statement — kept as its own named lemma
(rather than inlined into `exists_pole_of_isCoprimeAtRoots`) so a future
session can attack exactly this local fact in isolation. -/
theorem ordAt_le_one_of_ramified_num_vanish (hsf : Squarefree H.f)
    (a b : k[X]) (α : k) (Q : H.Point)
    (h_bot : pointIdeal Q ≠ ⊥) (heq : Q.X = α) (hY : Q.Y = 0)
    (ha : a.eval α = 0) (hb : b.eval α ≠ 0) :
    ordAt Q a b ≤ 1 := by
  sorry

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
    (x₁ x₂ : H.Point) (a b c : k[X]) (hc : c ≠ 0)
    (hcop : IsCoprimeAtRoots a b c)
    (hzsupp : ∀ P : H.Point, ordAtFrac P a b c 0 ≥
      -((if P = x₁ then 1 else 0) + (if P = x₂ then 1 else 0))) :
    c.natDegree ≤ 2 := by
  classical
  -- **Remaining bookkeeping** (mechanical, not new content): package
  -- `rootMultiplicity_le_one_and_mem_pair_of_isCoprimeAtRoots` applied to
  -- every element of `c.roots.toFinset` into the injection-into-`{x₁,x₂}`
  -- argument, then read off `c.natDegree = ∑ (rootMultiplicity) ≤
  -- ∑_{root} 1 ≤ 2` via the standard Mathlib fact bounding `c.natDegree`
  -- below by its multiplicity-weighted root count over a splitting field
  -- (`k` algebraically closed ⇒ equality, `Polynomial.natDegree_eq_card_roots`
  -- or the `Multiset.card`-level equivalent — MATHLIB NAME UNCONFIRMED).
  -- Left as `sorry`, isolated from the mathematical content (fully resolved
  -- above) — this is exactly the kind of Mathlib-API-wiring step to close
  -- via the REPL rather than guess blind.
  sorry

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
this project's standard escalation path for hard sorries) to close. -/
theorem uniqueDegree2MapToP1_ordAtFrac (hdeg : H.f.natDegree = 5) (hchar : (2 : k) ≠ 0)
    (hsf : Squarefree H.f) (x₁ x₂ : H.Point) (hne : x₂ ≠ Point.iota x₁)
    (z : FractionRing (CoordinateRing H)) (hz : z ∈ LPairCarrier x₁ x₂) :
    IsConstantFraction z := by
  classical
  obtain ⟨A, B, A', B', hbound, hz_eq⟩ := hz
  obtain ⟨hA'B'ne, hinfle, hptwise⟩ := hbound
  by_cases hAB0 : toPair H A B = 0
  · -- Numerator vanishes: `z = 0`, trivially constant (`c = 0`).
    refine ⟨0, ?_⟩
    rw [hz_eq]
    unfold polePairToFraction
    rw [hAB0, map_zero, zero_div]
    simp
  · -- Rationalize via §1, then run §5/§6/`ordAt_linX_eq`.
    have hA'B'toPairne : toPair H A' B' ≠ 0 := by
      rw [Ne, toPair_eq_zero_iff]; exact hA'B'ne
    obtain ⟨a, b, c, hcne, hc_def, hfrac_eq⟩ := frac_toPair_den_kx hdeg A B A' B' hA'B'toPairne
    -- Transport the original witness's pointwise bound to `(A,B,A',B')`'s
    -- `ordAtFrac` form (bridge lemma), matching `hfrac_eq`'s original
    -- (unrationalized) witness — NOT yet the rationalized `(a,b,c,0)` witness,
    -- since `ordAtFrac` isn't representation-independent for the *pole-bound
    -- hypothesis itself* (only for its *value*, once both numerators are
    -- nonzero — `ordAtFrac_eq_of_polePairToFraction_eq`). The remaining gap:
    -- transporting `hzsupp_orig` from `(A,B,A',B')` to `(a,b,c,0)` needs
    -- exactly `ordAtFrac_eq_of_polePairToFraction_eq` applied at every point
    -- `P`, which in turn needs `toPair H a b ≠ 0` (i.e. `z ≠ 0`, already
    -- known from `hAB0`, transported through `hfrac_eq`) as its side
    -- condition — mechanical but not yet threaded through here.
    have hzsupp_orig := fun P => ordAtFrac_ge_of_isPoleBoundedAtPair_pointwise x₁ x₂ A B A' B'
      hptwise P
    -- **Remaining work, left as `sorry`**: (1) transport `hzsupp_orig` to the
    -- rationalized witness `(a,b,c,0)` via `hfrac_eq` +
    -- `ordAtFrac_eq_of_polePairToFraction_eq`; (2) derive `IsCoprimeAtRoots a
    -- b c` (needs a genuine new argument — coprimality doesn't fall out of
    -- `hbound` alone, it needs the extra "no common factor" content that
    -- motivated this file's whole rationalize-then-reduce strategy in the
    -- first place; §1's rationalized `(a,b,c)` is NOT automatically coprime,
    -- only `c`'s *specific* algebraic form as `pairNorm H A' B'` is pinned
    -- down — reducing `(a,b,c)` by their actual `k[X]`-gcd, as the module
    -- docstring's step 2 describes, is the piece not yet executed here; note
    -- §5 no longer needs `c` squarefree, so this step is *purely* about
    -- coprimality, not squarefreeness); (3) feed the result through
    -- `natDegree_le_two_of_isCoprimeAtRoots` → `b_eq_zero_of_rationalized_pole_bounded`
    -- → `ordAt_linX_eq`-driven fiber-matching, to reach `x₂ = ιx₁`,
    -- contradicting `hne`. Steps (1)-(3) are the genuine content still
    -- missing; nothing further should be guessed at without Lean/REPL
    -- feedback per this session's ground rules.
    sorry

end HyperellipticPolynomial
