import Mathlib
import Genus2Lean.HyperellipticFunctionField
import Genus2Lean.AffinePoints
import Genus2Lean.PrincipalDivisors
import Genus2Lean.RiemannRochGenus2
import Genus2Lean.GlobalDegreeBoundSpec
import Genus2Lean.LPairFinrankOneOrdAtFrac
import Genus2Lean.CoprimeAtRootsClosed
import Genus2Lean.NonSquareFiberPoint

/-!
# `uniqueDegree2MapToP1`, general `k` (no `[IsAlgClosed k]`)

This file closes the gap traced in `LPairFinrankOneOrdAtFrac.lean` and
`CoprimeAtRootsClosed.lean`: `uniqueDegree2MapToP1_ordAtFrac` assumed
`[IsAlgClosed k]` at exactly two call sites (`IsAlgClosed.exists_root` and
`IsAlgClosed.exists_pow_nat_eq`), which is false for `k = ZMod p`.

**The fix, in outline:**

1. `reduce_ordAtFrac_triple` (`LPairFinrankOneOrdAtFrac.lean`) already reduces
   a pole-bounded triple `(a,b,c)` by their joint `k[X]`-gcd `g := gcd (gcd a
   b) c`, and its proof of `IsCoprimeAtRoots a₀ b₀ c₀` in fact shows something
   stronger in passing: *any* common divisor `d ∣ a₀, b₀, c₀` must be a unit
   (not just linear ones). `gcd_unit_of_reduce_ordAtFrac_triple` below states
   this directly: `IsUnit (gcd (gcd a₀ b₀) c₀)`.
2. Once the existing `b_eq_zero_of_rationalized_pole_bounded` gives `b₀ = 0`,
   `IsUnit (gcd (gcd a₀ b₀) c₀) = IsUnit (gcd a₀ c₀)` collapses to ordinary
   `IsCoprime a₀ c₀` (`gcd_isUnit_iff`), and `pairNorm H a₀ 0 = a₀ ^ 2`, so
   `IsNormCoprime H a₀ 0 c₀ = IsCoprime (a₀^2) c₀` follows from
   `IsCoprime.pow_left`. No new hard math — bookkeeping only.
3. Feeding `IsNormCoprime` plus `IsPoleBoundedAtPairSpec` (available directly
   from `LPairCarrierSpec'` membership, unlike the old `H.Point`-only
   `LPairCarrier'`) into `CoprimeAtRootsClosed.lean`'s
   `natDegree_le_one_of_isPoleBoundedAtPairSpec_isNormCoprime` gives
   `c₀.natDegree ≤ 1` directly — stronger than the old `≤ 2`, and with no
   algebraic closedness anywhere.
4. Since `c₀.natDegree ≤ 1`, if `c₀` is nonconstant it is `C k * X + C m`
   with `k ≠ 0`, which **always has a root over any field** (`α = -m/k`) — no
   closedness needed to find it. Feed that root into the *existing*
   `false_of_root_of_coprimeAtRoots_zero_snd` (which is already field-general
   once it has a root in hand — its own two `IsAlgClosed` calls only concerned
   finding a root and finding a square root of `H.f.eval α`, and the
   unramified branch's square-root step is no longer needed at all, since we
   only ever need `c₀.natDegree = 0` — see the note at that call site below;
   we do not reach the unramified branch's `IsAlgClosed.exists_pow_nat_eq`
   because we only call it to rule out a root existing, not to construct a
   point over it).

This means step 4 only needs the *existence* of a root at nonconstant `c₀`,
which is where `false_of_root_of_coprimeAtRoots_zero_snd` is invoked. That
theorem's own proof still calls `IsAlgClosed.exists_pow_nat_eq` internally
(unramified branch, `H.f.eval α` a non-square) — so it is not itself
closedness-free. We avoid this by never needing degree ≤ 2 with possible
non-rational roots; instead §4 below directly derives `False` from a root of
a genuinely *linear* `c₀`, without going through that lemma, using only the
ramified/unramified split against the two given points `x₁, x₂` (no
"produce a point over `α`" step needed at all — see `false_of_linear_root`).
-/

set_option maxHeartbeats 1000000

noncomputable section

open Classical
open Polynomial

variable {k : Type*} [Field k] {H : HyperellipticPolynomial k}

namespace HyperellipticPolynomial

open Divisor

variable [IsDedekindDomain (CoordinateRing H)]

/-! ## §1. Strengthening `reduce_ordAtFrac_triple`: the reduced triple's joint
gcd is a unit, not merely root-coprime.

Mirrors the last part of `reduce_ordAtFrac_triple`'s own proof
(`LPairFinrankOneOrdAtFrac.lean`) verbatim, with the specific divisor `linX α`
generalized to an arbitrary common divisor `d`. -/

omit [IsDedekindDomain (CoordinateRing H)] in
/-- **The reduced triple from `reduce_ordAtFrac_triple` has unit joint gcd.**
If `d ∣ a₀`, `d ∣ b₀`, `d ∣ c₀` where `a₀ = a/g`, `b₀ = b/g`, `c₀ = c/g` for
`g := gcd (gcd a b) c`, then `d * g ∣ a, b, c`, hence `d * g ∣ g` (`dvd_gcd`
twice), so cancelling the nonzero `g` gives `d ∣ 1`, i.e. `d` is a unit. This
is the same cancellation `reduce_ordAtFrac_triple` already performs for
`d = linX α`; stated here for an arbitrary common divisor, which is exactly
`gcd (gcd a₀ b₀) c₀`. -/
theorem gcd_unit_of_joint_reduce (a b c : k[X]) (hcne : c ≠ 0) :
    IsUnit (gcd (gcd (a / gcd (gcd a b) c) (b / gcd (gcd a b) c))
      (c / gcd (gcd a b) c)) := by
  set g := gcd (gcd a b) c with hg_def
  have hg_dvd_ab : g ∣ gcd a b := gcd_dvd_left _ _
  have hg_dvd_a : g ∣ a := hg_dvd_ab.trans (gcd_dvd_left _ _)
  have hg_dvd_b : g ∣ b := hg_dvd_ab.trans (gcd_dvd_right _ _)
  have hg_dvd_c : g ∣ c := gcd_dvd_right _ _
  have hgne : g ≠ 0 := fun h => hcne (eq_zero_of_zero_dvd (h ▸ hg_dvd_c))
  obtain ⟨a₀, ha_eq⟩ := hg_dvd_a
  obtain ⟨b₀, hb_eq⟩ := hg_dvd_b
  obtain ⟨c₀, hc_eq⟩ := hg_dvd_c
  have ha₀_eq : a / g = a₀ := by rw [ha_eq, mul_comm, mul_div_cancel_right₀ _ hgne]
  have hb₀_eq : b / g = b₀ := by rw [hb_eq, mul_comm, mul_div_cancel_right₀ _ hgne]
  have hc₀_eq : c / g = c₀ := by rw [hc_eq, mul_comm, mul_div_cancel_right₀ _ hgne]
  rw [ha₀_eq, hb₀_eq, hc₀_eq]
  set d := gcd (gcd a₀ b₀) c₀ with hd_def
  have hd_dvd_a₀ : d ∣ a₀ := (gcd_dvd_left _ _).trans (gcd_dvd_left _ _)
  have hd_dvd_b₀ : d ∣ b₀ := (gcd_dvd_left _ _).trans (gcd_dvd_right _ _)
  have hd_dvd_c₀ : d ∣ c₀ := gcd_dvd_right _ _
  have hgd_dvd_a : g * d ∣ a := by rw [ha_eq]; exact mul_dvd_mul_left g hd_dvd_a₀
  have hgd_dvd_b : g * d ∣ b := by rw [hb_eq]; exact mul_dvd_mul_left g hd_dvd_b₀
  have hgd_dvd_c : g * d ∣ c := by rw [hc_eq]; exact mul_dvd_mul_left g hd_dvd_c₀
  have hgd_dvd_gab : g * d ∣ gcd a b := dvd_gcd hgd_dvd_a hgd_dvd_b
  have hgd_dvd_g : g * d ∣ g := dvd_gcd hgd_dvd_gab hgd_dvd_c
  have hd_dvd_one : d ∣ (1 : k[X]) := by
    have hg_dvd_g1 : g ∣ g * 1 := by rw [mul_one]
    have := (mul_dvd_mul_iff_left hgne).mp (hgd_dvd_g.trans hg_dvd_g1)
    simpa using this
  exact isUnit_of_dvd_one hd_dvd_one

omit [IsDedekindDomain (CoordinateRing H)] in
/-- **Restated against `reduce_ordAtFrac_triple`'s actual output witnesses.**
Given the explicit quotient decomposition `a = g * a₀`, `b = g * b₀`,
`c = g * c₀` with `g := gcd (gcd a b) c ≠ 0` (exactly what
`reduce_ordAtFrac_triple`'s proof constructs internally), `gcd (gcd a₀ b₀) c₀`
is a unit. -/
theorem gcd_unit_of_reduce_ordAtFrac_triple (a b c a₀ b₀ c₀ : k[X])
    (hcne : c ≠ 0) (hg_def : gcd (gcd a b) c ≠ 0)
    (ha_eq : a = gcd (gcd a b) c * a₀) (hb_eq : b = gcd (gcd a b) c * b₀)
    (hc_eq : c = gcd (gcd a b) c * c₀) :
    IsUnit (gcd (gcd a₀ b₀) c₀) := by
  have key := gcd_unit_of_joint_reduce a b c hcne
  set g := gcd (gcd a b) c with hg_def'
  have ha₀_eq : a / g = a₀ := by rw [ha_eq, mul_comm, mul_div_cancel_right₀ _ hg_def]
  have hb₀_eq : b / g = b₀ := by rw [hb_eq, mul_comm, mul_div_cancel_right₀ _ hg_def]
  have hc₀_eq : c / g = c₀ := by rw [hc_eq, mul_comm, mul_div_cancel_right₀ _ hg_def]
  rwa [ha₀_eq, hb₀_eq, hc₀_eq] at key

/-! ## §2. [DEPRECATED] `IsNormCoprime` after `b = 0`.

**DEPRECATED — do not use.** The `IsNormCoprime` route (this section and its
consumer `natDegree_le_one_of_isPoleBoundedAtPairSpec_isNormCoprime` in
`CoprimeAtRootsClosed.lean`) has been superseded by the `IsCoprimeAtRoots` /
`ordAtSpec` closed-point route (§0, §3f, `natDegree_le_two_of_gcdUnit_closed_point`,
`false_of_root_of_isCoprimeAtRoots_zero_snd_general`). That is now the good,
maintained strategy; `IsNormCoprime` is not. Kept here only as historical
reference — not called from the live assembly theorem
(`uniqueDegree2MapToP1Spec`) anymore. Do not build on this.

Once `b₀ = 0`, `pairNorm H a₀ 0 = a₀ ^ 2 - 0 ^ 2 * H.f = a₀ ^ 2`, so
`IsNormCoprime H a₀ 0 c₀` (`IsCoprime (pairNorm H a₀ 0) c₀`) is exactly
`IsCoprime (a₀ ^ 2) c₀`, which follows from ordinary `IsCoprime a₀ c₀` via
`IsCoprime.pow_left`. -/

omit [IsDedekindDomain (CoordinateRing H)] in
/-- **[DEPRECATED] `IsNormCoprime` from a unit joint gcd, at `b = 0`.**
Superseded by the `IsCoprimeAtRoots` route — see section header. -/
theorem isNormCoprime_of_gcd_unit_snd_zero (a c : k[X])
    (hgu : IsUnit (gcd (gcd a (0 : k[X])) c)) :
    IsNormCoprime H a 0 c := by
  have hagcd : Associated (gcd (gcd a (0 : k[X])) c) (gcd a c) := by
    exact (gcd_zero_right' a).gcd (Associated.refl c)

  have hgu' : IsUnit (gcd a c) := by
    exact hagcd.isUnit_iff.mp hgu

  have hcop : IsCoprime a c := (gcd_isUnit_iff a c).1 hgu'
  have hpn : pairNorm H a (0 : k[X]) = a ^ 2 := by
    unfold pairNorm
    ring
  unfold IsNormCoprime
  rw [hpn]
  exact hcop.pow_left

/-! ## §3. The `IsAlgClosed`-free degree bound and finishing step. -/

omit [IsDedekindDomain (CoordinateRing H)] in
/-- **`c.natDegree = 1` normal form: `c = C (c.coeff 1) * X + C (c.coeff 0)`.**
Every coefficient of `c` beyond degree 1 vanishes (`natDegree_le_iff_coeff_eq_zero`
at `n = 1`, since `c.natDegree ≤ 1`), so `c` agrees with its own degree-1 Taylor
expansion at every coefficient, hence (`Polynomial.ext`) as a polynomial. -/
theorem eq_C_mul_X_add_C_of_natDegree_eq_one (c : k[X]) (hc : c.natDegree = 1) :
    c = C (c.coeff 1) * X + C (c.coeff 0) := by
  apply Polynomial.ext
  intro n
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X,
    Polynomial.coeff_C]
  match n with
  | 0 => simp
  | 1 => simp
  | (m + 2) =>
    have hzero : c.coeff (m + 2) = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      omega
    simp [hzero]

omit [IsDedekindDomain (CoordinateRing H)] in
/-- **A polynomial of `natDegree = 1` over any field has a root.** Direct
construction, since `Polynomial.exists_root`-style lemmas in Mathlib
generally assume algebraic closure; this is elementary for degree exactly 1
and needs no such hypothesis. With `c = C (c.coeff 1) * X + C (c.coeff 0)` and
`c.coeff 1 ≠ 0` (else `c.natDegree ≤ 0`, contradicting `hc`), the root is
`-(c.coeff 0) / (c.coeff 1)`. -/
theorem exists_root_of_natDegree_eq_one (c : k[X]) (hc : c.natDegree = 1) :
    ∃ α : k, c.eval α = 0 := by
  have hc1ne : c.coeff 1 ≠ 0 := by
    intro h
    have hle0 : c.natDegree ≤ 0 := by
      apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
      intro N hN
      rcases N with _ | _ | m
      · omega
      · exact h
      · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    omega

  refine ⟨-(c.coeff 0) / c.coeff 1, ?_⟩

  have hceq := eq_C_mul_X_add_C_of_natDegree_eq_one c hc

  have heval :
      c.eval (-(c.coeff 0) / c.coeff 1) =
        (C (c.coeff 1) * X + C (c.coeff 0)).eval
          (-(c.coeff 0) / c.coeff 1) := by
    exact congrArg
      (fun p : k[X] => p.eval (-(c.coeff 0) / c.coeff 1)) hceq

  rw [heval]
  simp [hc1ne]
  field_simp
  ring

/-! ## §3b. `ordAtSpec` transport across a `polePairToFraction` equality.

`ordAt_sub_ordAt_eq_of_polePairToFraction_eq` (`RiemannRochGenus2.lean`)
proves the `H.Point`/`ordAt` version of this fact via `ordAt'`
(`pointIdeal`-based) machinery. Here we need the `HeightOneSpectrum`/
`ordAtSpec` analogue. Rather than re-deriving the whole `ordAt'` apparatus
generically, we go directly through `Associates.count` additivity over `*`
(the same idiom already used at `LPairFinrankOneOrdAtFrac.lean:609-624` and
`HyperellipticClassProof.lean:962`), since `ordAtSpec = ordAtSpec_eq_count`
reduces everything to a statement about `Associates.count`, which is
manifestly additive over products — no point-rationality involved anywhere
in this argument. -/

omit [IsDedekindDomain (CoordinateRing H)] in
/-- **`Associates.count` is additive over `*`, at a prime, for nonzero
elements of `CoordinateRing H`.** Extracted as its own lemma (the same
computation is inlined in several places in this project); stated for a
`HeightOneSpectrum` ideal (automatically prime + nonzero) rather than a bare
`Prime` element, matching this file's needs directly. -/
theorem count_mul_eq_add [IsDedekindDomain (CoordinateRing H)]
    (v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H))
    (x y : CoordinateRing H)
    (hx : x ≠ 0) (hy : y ≠ 0) :
    (Associates.mk v.asIdeal).count
        (Associates.mk (Ideal.span ({x * y} : Set (CoordinateRing H)))).factors =
      (Associates.mk v.asIdeal).count
        (Associates.mk (Ideal.span ({x} : Set (CoordinateRing H)))).factors +
      (Associates.mk v.asIdeal).count
        (Associates.mk (Ideal.span ({y} : Set (CoordinateRing H)))).factors := by
  have hxne :
      Associates.mk (Ideal.span ({x} : Set (CoordinateRing H))) ≠ 0 :=
    Associates.mk_ne_zero.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hx)

  have hyne :
      Associates.mk (Ideal.span ({y} : Set (CoordinateRing H))) ≠ 0 :=
    Associates.mk_ne_zero.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hy)

  have hspan :
      Ideal.span ({x * y} : Set (CoordinateRing H)) =
        Ideal.span ({x} : Set (CoordinateRing H)) *
          Ideal.span ({y} : Set (CoordinateRing H)) := by
    symm
    exact Ideal.span_singleton_mul_span_singleton x y

  rw [hspan]
  rw [← Associates.mk_mul_mk]
  rw [Associates.factors_mul]

  obtain ⟨sx, hsx⟩ :=
    Associates.factors_eq_some_iff_ne_zero.mpr hxne
  obtain ⟨sy, hsy⟩ :=
    Associates.factors_eq_some_iff_ne_zero.mpr hyne

  rw [hsx, hsy, ← Associates.FactorSet.coe_add]
  simpa [Associates.count, Associates.bcount, v.irreducible] using
    (Multiset.count_add (Associates.mk v.asIdeal) sx sy)


omit [IsDedekindDomain (CoordinateRing H)] in
/-- **`ordAtSpec` is additive over `toPair`-multiplication**, at nonzero
factors — the `ordAtSpec` analogue of `ordAt'_toPair_mul`. -/
theorem ordAtSpec_add_of_toPair_mul [IsDedekindDomain (CoordinateRing H)]
    (v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H))
    (A B C D E F : k[X])
    (hAB : toPair H A B ≠ 0) (hCD : toPair H C D ≠ 0)
    (hmul : toPair H E F = toPair H A B * toPair H C D) :
    ordAtSpec v E F = ordAtSpec v A B + ordAtSpec v C D := by
  have hEF : toPair H E F ≠ 0 := by rw [hmul]; exact mul_ne_zero hAB hCD
  rw [ordAtSpec_eq_count v A B hAB, ordAtSpec_eq_count v C D hCD,
    ordAtSpec_eq_count v E F hEF, hmul]
  have := count_mul_eq_add v (toPair H A B) (toPair H C D) hAB hCD
  exact_mod_cast this

omit [IsDedekindDomain (CoordinateRing H)] in
/-- **Nonarchimedean "strict order gives order of the sum" law for `ordAtSpec`.**
If `toPair H A B` and `toPair H C D` have distinct `ordAtSpec v` values, the sum
`toPair H (A+C) (B+D)` has `ordAtSpec` equal to the *smaller* of the two — the
usual ultrametric fact, proved directly via `Associates.count` (matching this
file's existing idiom, e.g. the `hge1`/`Associates.prime_pow_dvd_iff_le` pattern
used throughout `ordAtSpec_eq_zero_of_notMem_four_of_dvd`), rather than through
`Valuation.map_add_eq_of_lt_right`/`WithZero.log` monotonicity directly, to avoid
depending on an unconfirmed `WithZero.log` order-API name. Only the `A B` ≺ `C D`
direction is stated (`hlt : ordAtSpec v A B < ordAtSpec v C D`); the symmetric
case is obtained by swapping the two calls at use sites (`add_comm`). -/
theorem ordAtSpec_add_eq_of_lt [IsDedekindDomain (CoordinateRing H)]
    (v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H))
    (A B C D : k[X])
    (hAB : toPair H A B ≠ 0) (hCD : toPair H C D ≠ 0)
    (hlt : ordAtSpec v A B < ordAtSpec v C D) :
    ordAtSpec v (A + C) (B + D) = ordAtSpec v A B := by
  classical
  have hsum_eq : toPair H (A + C) (B + D) = toPair H A B + toPair H C D := toPair_add A B C D
  set n : ℕ := (ordAtSpec v A B).toNat with hn_def
  have hn_eq : ordAtSpec v A B = (n : ℤ) := (Int.toNat_of_nonneg (ordAtSpec_nonneg v A B hAB)).symm
  
  have hsumne : toPair H (A + C) (B + D) ≠ 0 := by
    intro hsum0
    have hCDeq : toPair H C D = -toPair H A B := by
      have heq0 : toPair H A B + toPair H C D = 0 := by rw [← hsum_eq]; exact hsum0
      linear_combination heq0
    have hspaneq : Ideal.span {toPair H C D} = Ideal.span {toPair H A B} := by
      rw [hCDeq, Ideal.span_singleton_neg]
    have heq : ordAtSpec v A B = ordAtSpec v C D := by
      rw [ordAtSpec_eq_count v A B hAB, ordAtSpec_eq_count v C D hCD, hspaneq]
    rw [heq] at hlt
    exact absurd hlt (lt_irrefl _)
    
  have hIAB : Ideal.span {toPair H A B} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hAB
  have hICD : Ideal.span {toPair H C D} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hCD
  have hIsum : Ideal.span {toPair H (A + C) (B + D)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hsumne

  -- Replace omega with explicit Nat.cast_inj
  have h_count_AB : (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {toPair H A B})).factors = n := by
    have h_eq := ordAtSpec_eq_count v A B hAB
    rw [hn_eq] at h_eq
    exact Nat.cast_inj.mp h_eq.symm

  have hn_le_AB : n ≤ (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {toPair H A B})).factors :=
    h_count_AB.symm.le

  -- Replace omega with explicit Nat.cast_lt
  have hn_lt_CD : n < (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {toPair H C D})).factors := by
    have hcCD := ordAtSpec_eq_count v C D hCD
    have hlt' := hlt
    rw [hn_eq, hcCD] at hlt'
    exact Nat.cast_lt.mp hlt'

  have hn_le_CD : n ≤ (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {toPair H C D})).factors :=
    hn_lt_CD.le
    
  have hdvd_AB : v.asIdeal ^ n ∣ Ideal.span {toPair H A B} := by
    have h_pow := (Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hIAB) v.associates_irreducible).mpr hn_le_AB
    rw [← Associates.mk_pow] at h_pow
    exact Associates.mk_le_mk_iff_dvd.mp h_pow
    
  have hdvd_CD : v.asIdeal ^ n ∣ Ideal.span {toPair H C D} := by
    have h_pow := (Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hICD) v.associates_irreducible).mpr hn_le_CD
    rw [← Associates.mk_pow] at h_pow
    exact Associates.mk_le_mk_iff_dvd.mp h_pow
    
  have hAB_mem : toPair H A B ∈ v.asIdeal ^ n := Ideal.dvd_span_singleton.mp hdvd_AB
  have hCD_mem : toPair H C D ∈ v.asIdeal ^ n := Ideal.dvd_span_singleton.mp hdvd_CD
  have hsum_mem : toPair H (A + C) (B + D) ∈ v.asIdeal ^ n := by
    rw [hsum_eq]; exact (v.asIdeal ^ n).add_mem hAB_mem hCD_mem
    
  have hn_le_sum : n ≤ (Associates.mk v.asIdeal).count
      (Associates.mk (Ideal.span {toPair H (A + C) (B + D)})).factors := by
    rw [← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hIsum) v.associates_irreducible]
    have h_mk_le := Associates.mk_le_mk_iff_dvd.mpr (Ideal.dvd_span_singleton.mpr hsum_mem)
    rw [Associates.mk_pow] at h_mk_le
    exact h_mk_le
    
  have hn1_not_dvd_AB : ¬ v.asIdeal ^ (n + 1) ∣ Ideal.span {toPair H A B} := by
    intro hdvd
    have h_mk_le := Associates.mk_le_mk_iff_dvd.mpr hdvd
    rw [Associates.mk_pow] at h_mk_le
    have hc := (Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hIAB) v.associates_irreducible).mp h_mk_le
    -- Replace omega with explicit not_succ_le_self
    rw [h_count_AB] at hc
    exact Nat.not_succ_le_self n hc
    
  have hn1_dvd_CD : v.asIdeal ^ (n + 1) ∣ Ideal.span {toPair H C D} := by
    have h_pow := (Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hICD) v.associates_irreducible).mpr hn_lt_CD
    rw [← Associates.mk_pow] at h_pow
    exact Associates.mk_le_mk_iff_dvd.mp h_pow
    
  have hn1_not_dvd_sum : ¬ v.asIdeal ^ (n + 1) ∣ Ideal.span {toPair H (A + C) (B + D)} := by
    intro hdvd
    apply hn1_not_dvd_AB
    have hCD_mem' : toPair H C D ∈ v.asIdeal ^ (n + 1) := Ideal.dvd_span_singleton.mp hn1_dvd_CD
    have hsum_mem' : toPair H (A + C) (B + D) ∈ v.asIdeal ^ (n + 1) := Ideal.dvd_span_singleton.mp hdvd
    have hAB_mem' : toPair H A B ∈ v.asIdeal ^ (n + 1) := by
      have : toPair H A B = toPair H (A + C) (B + D) - toPair H C D := by rw [hsum_eq]; ring
      rw [this]; exact (v.asIdeal ^ (n + 1)).sub_mem hsum_mem' hCD_mem'
    exact Ideal.dvd_span_singleton.mpr hAB_mem'
    
  have hn_ge_sum : (Associates.mk v.asIdeal).count
      (Associates.mk (Ideal.span {toPair H (A + C) (B + D)})).factors < n + 1 := by
    by_contra hge
    push Not at hge
    apply hn1_not_dvd_sum
    have h_pow := (Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hIsum) v.associates_irreducible).mpr hge
    rw [← Associates.mk_pow] at h_pow
    exact Associates.mk_le_mk_iff_dvd.mp h_pow

  -- Replace final omega with le_antisymm bridged via Nat.le_of_lt_succ
  have h_count_eq : (Associates.mk v.asIdeal).count 
      (Associates.mk (Ideal.span {toPair H (A + C) (B + D)})).factors = n :=
    le_antisymm (Nat.le_of_lt_succ hn_ge_sum) hn_le_sum

  rw [ordAtSpec_eq_count v (A + C) (B + D) hsumne, hn_eq, h_count_eq]

omit [IsDedekindDomain (CoordinateRing H)] in
/-- **`ordAtSpec` transport across a `polePairToFraction` equality**, the
`HeightOneSpectrum` analogue of `ordAt_sub_ordAt_eq_of_polePairToFraction_eq`.
Same cross-multiplication argument, with `ordAt'`/`ordAt` replaced by
`ordAtSpec` and `ordAtSpec_add_of_toPair_mul` in place of `ordAt'_toPair_mul`. -/
theorem ordAtSpec_sub_ordAtSpec_eq_of_polePairToFraction_eq
    [IsDedekindDomain (CoordinateRing H)]
    (v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H))
    (A B A' B' C D C' D' : k[X])
    (hz : toPair H A B ≠ 0)
    (hA'B' : toPair H A' B' ≠ 0) (hC'D' : toPair H C' D' ≠ 0)
    (heq : polePairToFraction (H := H) A B A' B' = polePairToFraction (H := H) C D C' D') :
    ordAtSpec v A B - ordAtSpec v A' B' = ordAtSpec v C D - ordAtSpec v C' D' := by
  have hmul := toPair_mul_eq_of_polePairToFraction_eq A B A' B' C D C' D' hA'B' hC'D' heq
  haveI : IsDomain (CoordinateRing H) := IsDedekindDomain.toIsDomain
  have hCD : toPair H C D ≠ 0 := by
    intro hCD0
    have hRHS0 : toPair H C D * toPair H A' B' = 0 := by rw [hCD0]; ring
    have hLHSne : toPair H A B * toPair H C' D' ≠ 0 := mul_ne_zero hz hC'D'
    exact hLHSne (hmul.trans hRHS0)
  have h1 := ordAtSpec_add_of_toPair_mul (H := H) v A B C' D'
    (A * C' + B * D' * H.f) (A * D' + C' * B) hz hC'D'
    (toPair_mul A B C' D').symm
  have h2 := ordAtSpec_add_of_toPair_mul (H := H) v C D A' B'
    (A * C' + B * D' * H.f) (A * D' + C' * B) hCD hA'B'
    ((toPair_mul A B C' D').symm.trans hmul)
  have hleft : ordAtSpec v A B + ordAtSpec v C' D' =
      ordAtSpec v C D + ordAtSpec v A' B' := by
    rw [← h1, ← h2]
  omega

/-! ## §3c. Residue degree of the non-square-fiber closed point.

Needed to distinguish `nonSquareFiberHeightOne α hns` from every rational
point `pointHeightOne' P` (which always has residue degree `1`,
`residueDeg_pointHeightOne'`) in the finishing indicator-sum argument below. -/

omit [IsDedekindDomain (CoordinateRing H)] in
/-- **`SqrtExt c` has `k`-dimension `2`.** `SqrtExt c = AdjoinRoot (X^2 - C c)`,
and `X^2 - C c ≠ 0` (degree `2`), so `AdjoinRoot.finrank` gives
`Module.finrank k (SqrtExt c) = (X^2 - C c).natDegree = 2`. -/
theorem finrank_sqrtExt (c : k) : Module.finrank k (SqrtExt c) = 2 := by
  have hne : (X ^ 2 - C c : k[X]) ≠ 0 := by
    intro h
    have hd : (X ^ 2 - C c : k[X]).natDegree = 2 := by
      compute_degree!
    rw [h] at hd
    simp at hd
  rw [Module.finrank_eq_card_basis (AdjoinRoot.powerBasisAux hne)]
  simp




omit [IsDedekindDomain (CoordinateRing H)] in
/-- **Residue degree of the non-square-fiber closed point is `2`.** Via the
surjective `evalAtNonSquareFiber α : CoordinateRing H →+* SqrtExt (H.f.eval α)`
(kernel = `nonSquareFiberIdeal α`) and the first isomorphism theorem, mirroring
`finrank_quotient_pointIdeal`'s proof shape exactly, target field
`SqrtExt (H.f.eval α)` (dimension `2`, `finrank_sqrtExt`) instead of `k`
(dimension `1`). -/
theorem residueDeg_nonSquareFiberHeightOne
    [IsDedekindDomain (CoordinateRing H)]
    (α : k) (hns : ¬ IsSquare (H.f.eval α)) :
    residueDeg (nonSquareFiberHeightOne (H := H) α hns) = 2 := by
  unfold residueDeg nonSquareFiberHeightOne nonSquareFiberIdeal
  simp only

  let hequiv :
      (CoordinateRing H ⧸
          RingHom.ker (evalAtNonSquareFiber (H := H) α))
        ≃+* SqrtExt (H.f.eval α) :=
    RingHom.quotientKerEquivOfSurjective
      (evalAtNonSquareFiber_surjective (H := H) α)

  have hlinequiv :
      Module.finrank k
          (CoordinateRing H ⧸
            RingHom.ker (evalAtNonSquareFiber (H := H) α)) =
        Module.finrank k (SqrtExt (H.f.eval α)) := by
    let e :
        (CoordinateRing H ⧸
            RingHom.ker (evalAtNonSquareFiber (H := H) α))
          ≃ₗ[k] SqrtExt (H.f.eval α) :=
      { hequiv.toAddEquiv with
        map_smul' := by
          intro r x
          change hequiv (r • x) = r • hequiv x
          rw [Algebra.smul_def, Algebra.smul_def]
          rw [map_mul]
          congr 1

          change
            hequiv
                ((algebraMap k
                  (CoordinateRing H ⧸
                    RingHom.ker
                      (evalAtNonSquareFiber (H := H) α))) r) =
              (algebraMap k (SqrtExt (H.f.eval α))) r

          change
            hequiv
                (Ideal.Quotient.mk
                  (RingHom.ker
                    (evalAtNonSquareFiber (H := H) α))
                  ((algebraMap k (CoordinateRing H)) r)) =
              (algebraMap k (SqrtExt (H.f.eval α))) r

          rw [show hequiv =
              RingHom.quotientKerEquivOfSurjective
                (evalAtNonSquareFiber_surjective (H := H) α) from rfl]

          rw [RingHom.quotientKerEquivOfSurjective_apply_mk]

          simp only [evalAtNonSquareFiber]

          change
            (AdjoinRoot.lift
                ((AdjoinRoot.of (X ^ 2 - C (H.f.eval α))).comp
                  (Polynomial.evalRingHom α))
                (sqrtExtRoot (H.f.eval α)) _)
              ((AdjoinRoot.of (X ^ 2 - C H.f)) (C r)) =
              (AdjoinRoot.of (X ^ 2 - C (H.f.eval α))) r

          rw [AdjoinRoot.lift_of]
          simp }

    exact e.finrank_eq

  rw [hlinequiv]
  exact finrank_sqrtExt (H.f.eval α)



omit [IsDedekindDomain (CoordinateRing H)] in
/-- **The non-square-fiber closed point is never a rational point.** Immediate
from the residue degree mismatch (`2 ≠ 1`). -/
theorem nonSquareFiberHeightOne_ne_pointHeightOne' [IsDedekindDomain (CoordinateRing H)]
    (α : k) (hns : ¬ IsSquare (H.f.eval α)) (P : H.Point) :
    nonSquareFiberHeightOne (H := H) α hns ≠ pointHeightOne' P := by
  intro h
  have h1 := residueDeg_nonSquareFiberHeightOne (H := H) α hns
  have h2 := residueDeg_pointHeightOne' (H := H) P
  rw [h] at h1
  omega

/-! ## §3d. The `IsAlgClosed`-free finish: a root of a linear `c₀` forces
`x₂ = ι x₁`, contradicting `hne`.

Direct replacement for `false_of_root_of_coprimeAtRoots_zero_snd` (which is
gated behind `[IsAlgClosed k]` in its section, and internally still calls
`IsAlgClosed.exists_pow_nat_eq`). Same ramified/unramified split for the
rational case; the non-square fiber case is new, using
`nonSquareFiberHeightOne`/`hzsuppSpec₀` (closed-point-native) directly instead
of trying to name a witness `H.Point`. -/

/-- **No closed point lying over a coprime-at-roots-guaranteed root can be
anything but `x₁`/`x₂` — impossible when both `H.f.eval α = 0` is false and
`H.f.eval α` is a non-square.** The non-square-fiber case of the finishing
argument: `v := nonSquareFiberHeightOne α hns` has `ordAtSpec v c₀ 0 ≥ 1`
(`α` a root of `c₀`, so `toPair H c₀ 0 = algebraMap c₀ ∈ nonSquareFiberIdeal
α` via `toPair_mem_nonSquareFiberIdeal_iff`, giving strictly positive
`v.intValuation`, hence `Associates.count ≥ 1`), `ordAtSpec v a₀ 0 = 0`
(`a₀.eval α ≠ 0`, same membership characterization), and `v ≠ pointHeightOne'
x₁, x₂` (`nonSquareFiberHeightOne_ne_pointHeightOne'`) forces the indicator
in `hzsuppSpec₀ v` to be `0` — contradicting `ordAtSpec v a₀ 0 - ordAtSpec v
c₀ 0 ≥ -0`, i.e. `0 - (≥1) ≥ 0`. -/
theorem false_of_nonSquareFiber_root [IsDedekindDomain (CoordinateRing H)]
    (x₁ x₂ : H.Point) (a₀ c₀ : k[X]) (hc₀ne : c₀ ≠ 0)
    (haα : a₀.eval (α : k) ≠ 0) (hα : c₀.eval α = 0)
    (hns : ¬ IsSquare (H.f.eval α))
    (hzsuppSpec₀ : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      ordAtSpec v a₀ 0 - ordAtSpec v c₀ (0 : k[X]) ≥
        -((if v = pointHeightOne' x₁ then 1 else 0) +
          (if v = pointHeightOne' x₂ then 1 else 0))) : False := by
  set v := nonSquareFiberHeightOne (H := H) α hns with hv_def
  have hc₀mem : toPair H c₀ (0 : k[X]) ∈ v.asIdeal := by
    show toPair H c₀ (0 : k[X]) ∈ nonSquareFiberIdeal (H := H) α
    rw [toPair_mem_nonSquareFiberIdeal_iff]
    have hc0eval : algebraMap k (SqrtExt (H.f.eval α)) (c₀.eval α) = 0 := by
      rw [hα]; simp
    simpa using hc0eval
  have ha₀notmem : toPair H a₀ (0 : k[X]) ∉ v.asIdeal := by
    show toPair H a₀ (0 : k[X]) ∉ nonSquareFiberIdeal (H := H) α
    rw [toPair_mem_nonSquareFiberIdeal_iff]
    simp only [Polynomial.eval_zero, map_zero, zero_mul, add_zero]
    intro hcontra
    apply haα
    haveI : Nontrivial (SqrtExt (H.f.eval α)) :=
      (sqrtExt_isField (H.f.eval α) hns).toField.toNontrivial
    have := (algebraMap k (SqrtExt (H.f.eval α))).injective
    exact this (by simpa using hcontra)
  have hc₀ne' : toPair H c₀ (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]; exact fun h => hc₀ne h.1
  have hordc_pos : ordAtSpec v c₀ (0 : k[X]) ≥ 1 := by
    rw [ordAtSpec_eq_count v c₀ 0 hc₀ne']
    have hdvd : v.asIdeal ∣ Ideal.span ({toPair H c₀ (0 : k[X])} : Set (CoordinateRing H)) :=
      Ideal.dvd_span_singleton.mpr hc₀mem
    have hspan_ne : Associates.mk
        (Ideal.span ({toPair H c₀ (0 : k[X])} : Set (CoordinateRing H))) ≠ 0 :=
      Associates.mk_ne_zero.mpr (Ideal.span_singleton_eq_bot.not.mpr hc₀ne')
    have hge1 : 1 ≤ (Associates.mk v.asIdeal).count (Associates.mk
        (Ideal.span ({toPair H c₀ (0 : k[X])} : Set (CoordinateRing H)))).factors := by
      have hdvd' : Associates.mk v.asIdeal ^ 1 ∣
          Associates.mk (Ideal.span ({toPair H c₀ (0 : k[X])} : Set (CoordinateRing H))) := by
        rw [pow_one, Associates.mk_dvd_mk]
        exact hdvd
      exact (Associates.prime_pow_dvd_iff_le hspan_ne
        (Associates.irreducible_mk.mpr v.irreducible)).mp hdvd'
    exact_mod_cast hge1
  have horda0 : ordAtSpec v a₀ (0 : k[X]) = 0 := ordAtSpec_eq_zero_of_notMem v a₀ 0 ha₀notmem
  have hbound := hzsuppSpec₀ v
  rw [horda0] at hbound
  have hvne1 : v ≠ pointHeightOne' x₁ :=
    nonSquareFiberHeightOne_ne_pointHeightOne' (H := H) α hns x₁
  have hvne2 : v ≠ pointHeightOne' x₂ :=
    nonSquareFiberHeightOne_ne_pointHeightOne' (H := H) α hns x₂
  simp only [if_neg hvne1, if_neg hvne2, add_zero] at hbound
  omega

/-- **The ramified rational case, without `[IsAlgClosed k]`.** Verbatim
extraction of `false_of_root_of_coprimeAtRoots_zero_snd`'s ramified branch
(`H.f.eval α = 0`): it never invokes closedness, only the unramified branch
of that theorem does (via `IsAlgClosed.exists_pow_nat_eq`), so this half is a
direct, unconditional replacement — no `hsq`/`hns` case split needed here. -/
theorem false_of_root_ramified
    [IsDedekindDomain (CoordinateRing H)]
    (hsf : Squarefree H.f) (x₁ x₂ : H.Point)
    (hne : x₂ ≠ Point.iota x₁) (a₀ c₀ : k[X]) (hc₀ne : c₀ ≠ 0)
    (haα : a₀.eval (α : k) ≠ 0)
    (hzsupp₀ : ∀ P : H.Point, ordAtFrac P a₀ 0 c₀ 0 ≥
      -((if P = x₁ then 1 else 0) + (if P = x₂ then 1 else 0)))
    (hWeier : H.f.eval α = 0) (hα : c₀.eval α = 0) : False := by
  classical
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

/-- **The unramified rational case, without `[IsAlgClosed k]`.** Same
argument as `false_of_root_of_coprimeAtRoots_zero_snd`'s unramified branch,
except the square root `β` with `β ^ 2 = H.f.eval α` is taken directly from
the hypothesis `hsq : IsSquare (H.f.eval α)` (`IsSquare c ↔ ∃ r, c = r * r`)
instead of from `IsAlgClosed.exists_pow_nat_eq`. Everything downstream is
identical to the closed-field proof, since nothing else in that branch uses
closedness. -/
theorem false_of_root_unramified_of_isSquare
    [IsDedekindDomain (CoordinateRing H)]
    (hchar : (2 : k) ≠ 0) (x₁ x₂ : H.Point)
    (hne : x₂ ≠ Point.iota x₁) (a₀ c₀ : k[X]) (hc₀ne : c₀ ≠ 0)
    (haα : a₀.eval (α : k) ≠ 0)
    (hzsupp₀ : ∀ P : H.Point, ordAtFrac P a₀ 0 c₀ 0 ≥
      -((if P = x₁ then 1 else 0) + (if P = x₂ then 1 else 0)))
    (hWeier : H.f.eval α ≠ 0) (hα : c₀.eval α = 0)
    (hsq : IsSquare (H.f.eval α)) : False := by
  classical
  obtain ⟨β, hβ⟩ := hsq
  have hβ' : β ^ 2 = H.f.eval α := by rw [sq]; exact hβ.symm
  have hβne : β ≠ 0 := by
    intro h
    rw [h] at hβ'
    simp at hβ'
    exact hWeier hβ'.symm
  have hQeq : H.Equation α β := by
    show β ^ 2 = H.f.eval α
    exact hβ'
  set Q : H.Point := Point.mk α β hQeq with hQ_def
  have hQX : Q.X = α := rfl
  have hQY : Q.Y = β := rfl
  have hQYne : Q.Y ≠ 0 := hQY ▸ hβne
  have hιQX : (Point.iota Q).X = α := by
    rw [Point.iota_X]; exact hQX
  have hιQYne : (Point.iota Q).Y ≠ 0 := by
    rw [Point.iota_Y]; exact neg_ne_zero.mpr hQYne
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

/-- **The `IsAlgClosed`-free finish.** Direct replacement for
`false_of_root_of_coprimeAtRoots_zero_snd`. The ramified rational case uses
`false_of_root_ramified` (an extraction of that lemma's ramified branch,
which never needed closedness); the unramified rational case uses
`false_of_root_unramified_of_isSquare` (square root taken from `hsq`
directly, not from `IsAlgClosed`); the `H.f.eval α` non-square case uses
`false_of_nonSquareFiber_root`. -/
theorem false_of_root_of_isCoprimeAtRoots_zero_snd_general
    [IsDedekindDomain (CoordinateRing H)] [DecidableEq k]
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f) (x₁ x₂ : H.Point)
    (hne : x₂ ≠ Point.iota x₁) (a₀ c₀ : k[X]) (hc₀ne : c₀ ≠ 0)
    (hcop : IsCoprimeAtRoots a₀ 0 c₀)
    (hzsupp₀ : ∀ P : H.Point, ordAtFrac P a₀ 0 c₀ 0 ≥
      -((if P = x₁ then 1 else 0) + (if P = x₂ then 1 else 0)))
    (hzsuppSpec₀ : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      ordAtSpec v a₀ 0 - ordAtSpec v c₀ (0 : k[X]) ≥
        -((if v = pointHeightOne' x₁ then 1 else 0) +
          (if v = pointHeightOne' x₂ then 1 else 0)))
    (α : k) (hα : c₀.eval α = 0) : False := by
  have haα : a₀.eval α ≠ 0 := fun h => hcop α hα ⟨h, by simp⟩
  by_cases hWeier : H.f.eval α = 0
  · exact false_of_root_ramified
      (H := H) hsf x₁ x₂ hne a₀ c₀ hc₀ne haα hzsupp₀ hWeier hα
  · by_cases hsq : IsSquare (H.f.eval α)
    · exact false_of_root_unramified_of_isSquare
        (H := H) hchar x₁ x₂ hne a₀ c₀ hc₀ne haα hzsupp₀ hWeier hα hsq
    · exact false_of_nonSquareFiber_root (H := H) x₁ x₂ a₀ c₀ hc₀ne haα hα hsq hzsuppSpec₀

/-! ## §3e. `IsNormCoprime H a₀ b₀ c₀` directly, for general `b₀` (no `hbeq0`
prerequisite).

**The actual remaining gap, per the bad-factor plan.** Take any irreducible `q`
dividing `gcd (pairNorm H a₀ b₀) c₀`. `hgu` (unit joint `k[X]`-gcd of `a₀,b₀,c₀`)
forces `q ∤ b₀` (`notDvd_snd_of_dvd_gcd_pairNorm_of_gcdUnit` below — pure `k[X]`
algebra, no closedness). Then case-split `q ∣ H.f` (ramified) vs `q ∤ H.f`
(split/inert): each case forces a closed point `v` lying over `q` into
`{pointHeightOne' x₁, pointHeightOne' x₂}` via `hzsuppSpec₀`, and since `q` is a
common factor of `pairNorm a₀ b₀` and `c₀`, `v` witnesses both `toPair H a₀ b₀ ∈
v.asIdeal` and `toPair H c₀ 0 ∈ v.asIdeal` — but genuinely new closed-point
infrastructure (a `HeightOneSpectrum`-level construction for the *ramified* fiber at
an arbitrary-degree irreducible `q ∣ H.f`, generalizing the existing rational-`α`-only
ramified machinery in `LPairFinrankOneOrdAtFrac.lean`) is needed for the ramified
case, and the `nonSquareFiberHeightOne`/`SqrtExt` pattern needs regeneralizing from
`α : k` to `q : k[X]` for the split case. Built incrementally below. -/

/-- **`q ∤ b₀`, from the unit joint gcd.** If `q ∣ pairNorm H a₀ b₀`, `q ∣ c₀`, and
`q ∣ b₀`, then since `pairNorm H a₀ b₀ = a₀^2 - b₀^2 * H.f`, `q ∣ b₀^2 * H.f` too, so
`q ∣ a₀^2`; `q` irreducible (hence prime, `k[X]` a UFD) gives `q ∣ a₀`. Then `q`
divides `a₀`, `b₀`, and `c₀`, hence `q ∣ gcd (gcd a₀ b₀) c₀`, forcing `q` to be a
unit (`hgu`) — contradicting `q` irreducible. -/
theorem notDvd_snd_of_dvd_gcd_pairNorm_of_gcdUnit
    (a₀ b₀ c₀ q : k[X]) (hq : Irreducible q)
    (hgu : IsUnit (gcd (gcd a₀ b₀) c₀))
    (hqc : q ∣ c₀) (hqn : q ∣ pairNorm H a₀ b₀) : ¬ q ∣ b₀ := by
  intro hqb
  have hqa2 : q ∣ a₀ ^ 2 := by
    have hqb2f : q ∣ b₀ ^ 2 * H.f := Dvd.dvd.mul_right (hqb.pow (two_ne_zero)) H.f
    have : q ∣ a₀ ^ 2 - b₀ ^ 2 * H.f + b₀ ^ 2 * H.f := by
      have hsub : a₀ ^ 2 - b₀ ^ 2 * H.f = pairNorm H a₀ b₀ := rfl
      rw [hsub]
      exact hqn.add hqb2f
    simpa using this
  have hqa : q ∣ a₀ := hq.prime.dvd_of_dvd_pow hqa2
  have hq_dvd_gcd : q ∣ gcd (gcd a₀ b₀) c₀ := dvd_gcd (dvd_gcd hqa hqb) hqc
  exact hq.not_isUnit (isUnit_of_dvd_unit hq_dvd_gcd hgu)

/-! ### The split (non-Weierstrass) bad-factor case, `q.natDegree ≥ 2`, `q ∤ H.f`.

**Per the residue-field argument (confirmed correct, no exact-order computation
needed):** at any `v` over `q` (going-up, `heightOneSpectrum_of_irreducible_ne_
pointIdeal`), work in the field `L := CoordinateRing H ⧸ v.asIdeal`. Write `ȳ := mk (y
H)`, so `ȳ² = mk H.f` in `L`. If `toPair H a₀ b₀ ∈ v.asIdeal` (i.e. `mk (toPair H a₀
b₀) = 0`), consider the *conjugate* ideal `v' := ` the image of `v` under `involution
H` (a ring automorphism, so `v'` is again height-one prime). Since `involution H
(toPair H a₀ b₀) = toPair H a₀ (-b₀)`, membership transports: `toPair H a₀ b₀ ∈
v.asIdeal ↔ toPair H a₀ (-b₀) ∈ v'.asIdeal`. The *sum* `toPair H a₀ b₀ + toPair H a₀
(-b₀) = 2 • algebraMap a₀`(the `y`-terms cancel), so if **both** `toPair H a₀ b₀ ∈
v.asIdeal` and its conjugate fact forced `a₀`'s image to vanish at `v` too — but we
show directly below that at least one of `v`, `v'` fails to contain the numerator,
using `q ∤ a₀` (from `q ∤ b₀`, `q ∣ pairNorm`, `q ∤ H.f`) and `hchar`. -/

/-- **The conjugate `HeightOneSpectrum` under the hyperelliptic involution.**
`involution H` is a ring automorphism (self-inverse, `involution_involution` below), so
pushing a height-one prime through it stays height-one. -/
theorem involution_involution (H : HyperellipticPolynomial k) (w : CoordinateRing H) :
    involution H (involution H w) = w := by
  obtain ⟨E, F, hw⟩ := toPair_surjective_local H w
  rw [hw, toPair_involution, toPair_involution, neg_neg]

theorem involution_bijective (H : HyperellipticPolynomial k) :
    Function.Bijective (involution H) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨involution H, involution_involution H, involution_involution H⟩

/-- `involution H`, packaged as a `RingEquiv` (self-inverse ring automorphism). -/
noncomputable def involutionEquiv (H : HyperellipticPolynomial k) :
    CoordinateRing H ≃+* CoordinateRing H :=
  RingEquiv.ofBijective (involution H) (involution_bijective H)

/-- The conjugate closed point `v' := involution "of" v`, i.e. the height-one prime
`(involutionEquiv H) '' v.asIdeal` (equivalently `Ideal.comap (involutionEquiv H).symm
v.asIdeal`, since `involutionEquiv H` is self-inverse). -/
def conjHeightOne [IsDedekindDomain (CoordinateRing H)]
    (v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H)) :
    IsDedekindDomain.HeightOneSpectrum (CoordinateRing H) where
  asIdeal := Ideal.comap (involutionEquiv H).symm.toRingHom v.asIdeal
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    intro hbot
    apply v.ne_bot
    have hcomap : Ideal.comap (involutionEquiv H).symm.toRingHom v.asIdeal = (⊥ : Ideal _) :=
      hbot
    have hmap := congrArg (Ideal.map (involutionEquiv H).symm.toRingHom) hcomap
    rw [Ideal.map_bot] at hmap
    rwa [Ideal.map_comap_of_surjective (involutionEquiv H).symm.toRingHom
      (involutionEquiv H).symm.surjective v.asIdeal] at hmap

/-- **Membership transports across `conjHeightOne`.** `w ∈ (conjHeightOne v).asIdeal ↔
involution H w ∈ v.asIdeal`. Direct unfolding: `(conjHeightOne v).asIdeal` is the
comap of `v.asIdeal` along `(involutionEquiv H).symm`, i.e. exactly `{w | (involutionEquiv
H).symm w ∈ v.asIdeal}`; since `involution H` is its own inverse,
`(involutionEquiv H).symm w = involution H w`. -/
theorem mem_conjHeightOne_iff [IsDedekindDomain (CoordinateRing H)]
    (v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H)) (w : CoordinateRing H) :
    w ∈ (conjHeightOne (H := H) v).asIdeal ↔ involution H w ∈ v.asIdeal := by
  show (involutionEquiv H).symm w ∈ v.asIdeal ↔ involution H w ∈ v.asIdeal
  have : (involutionEquiv H).symm w = involution H w := by
    have hfwd : involutionEquiv H (involution H w) = w := involution_involution H w
    have := congrArg (involutionEquiv H).symm hfwd
    simpa using this.symm
  rw [this]

/-- **`conjHeightOne` is an involution.** Follows directly from `mem_conjHeightOne_iff`
(applied twice) and `involution_involution`: `w ∈ (conjHeightOne (conjHeightOne v)).asIdeal
↔ involution H w ∈ (conjHeightOne v).asIdeal ↔ involution H (involution H w) ∈ v.asIdeal ↔
w ∈ v.asIdeal`. -/
theorem conjHeightOne_conjHeightOne [IsDedekindDomain (CoordinateRing H)]
    (v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H)) :
    conjHeightOne (H := H) (conjHeightOne (H := H) v) = v := by
  ext w
  rw [mem_conjHeightOne_iff, mem_conjHeightOne_iff, involution_involution]

/-- **`pointHeightOne'` is injective.** `pointHeightOne' P`'s underlying ideal is
`pointIdeal P` by definition, and distinct points have distinct point ideals
(`pointIdeal_ne_of_ne`). -/
theorem pointHeightOne'_injective [IsDedekindDomain (CoordinateRing H)] :
    Function.Injective (pointHeightOne' (H := H)) := by
  intro P Q heq
  by_contra hne
  exact pointIdeal_ne_of_ne P Q hne (congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal heq)

/-- **`residueDeg` is `conjHeightOne`-invariant.** `involutionEquiv H` is a `k`-algebra
automorphism of `CoordinateRing H` (fixes `k` pointwise, via `involution_algebraMap` and
`IsScalarTower k k[X] (CoordinateRing H)`) carrying `v.asIdeal` to `(conjHeightOne
v).asIdeal` (that's exactly `conjHeightOne`'s definition: comap along the symm map), so it
descends to a `k`-algebra iso of the two residue fields, giving equal `finrank`. -/
theorem residueDeg_conjHeightOne [IsDedekindDomain (CoordinateRing H)]
    (v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H)) :
    residueDeg (conjHeightOne (H := H) v) = residueDeg v := by
  unfold residueDeg
  have hmap : Ideal.map (involutionEquiv H).symm.toRingHom (conjHeightOne (H := H) v).asIdeal
      = v.asIdeal := by
    show Ideal.map (involutionEquiv H).symm.toRingHom
      (Ideal.comap (involutionEquiv H).symm.toRingHom v.asIdeal) = v.asIdeal
    exact Ideal.map_comap_of_surjective _ (involutionEquiv H).symm.surjective v.asIdeal
    
  have halg : ∀ c : k, (involutionEquiv H).symm (algebraMap k (CoordinateRing H) c)
      = algebraMap k (CoordinateRing H) c := by
    intro c
    have h_hom : (algebraMap k (CoordinateRing H) c) = 
        (algebraMap k[X] (CoordinateRing H)) (algebraMap k k[X] c) := rfl
    apply (involutionEquiv H).injective
    rw [(involutionEquiv H).apply_symm_apply, h_hom]
    exact (involution_algebraMap H (algebraMap k k[X] c)).symm
    
  have e : (CoordinateRing H ⧸ (conjHeightOne (H := H) v).asIdeal) ≃ₐ[k]
      (CoordinateRing H ⧸ v.asIdeal) :=
    AlgEquiv.ofRingEquiv (f := Ideal.quotientEquiv _ _ (involutionEquiv H).symm hmap.symm)
      (fun c => by
        rw [show algebraMap k (CoordinateRing H ⧸ (conjHeightOne (H := H) v).asIdeal) c
              = Ideal.Quotient.mk _ (algebraMap k (CoordinateRing H) c) from rfl,
            Ideal.quotientEquiv_mk, halg]
        rfl)
        
  exact LinearEquiv.finrank_eq e.toLinearEquiv


/-- **`ordAtSpec` at a "B=0" pair is `conjHeightOne`-invariant.** `toPair H A 0 =
algebraMap A` is fixed by `involution H`, so membership (hence the whole `Associates.count`
multiplicity) transports identically between `v` and `conjHeightOne v` — not just the
`> 0 ↔ > 0` fact `Case A` uses, but exact equality, since the ideal `Ideal.span
{algebraMap A}` is itself `involutionEquiv`-invariant and `conjHeightOne v`'s ideal is the
`involutionEquiv.symm`-comap of `v`'s. -/
theorem ordAtSpec_conjHeightOne_fst [IsDedekindDomain (CoordinateRing H)]
    (v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H)) (A : k[X]) :
    ordAtSpec (conjHeightOne (H := H) v) A (0 : k[X]) = ordAtSpec v A (0 : k[X]) := by
  by_cases hA : A = 0
  · subst hA
    unfold ordAtSpec
    have h0 : toPair H 0 (0 : k[X]) = 0 := by simp [HyperellipticPolynomial.toPair]
    simp [h0]
  have hne : toPair H A (0 : k[X]) ≠ 0 := by rw [Ne, toPair_eq_zero_iff]; exact fun h => hA h.1
  have hcalg : toPair H A (0 : k[X]) = algebraMap k[X] (CoordinateRing H) A := by
    unfold HyperellipticPolynomial.toPair; simp

  set alg := algebraMap k[X] (CoordinateRing H) A with halg_def
  have halg_fix : involution H alg = alg := involution_algebraMap H A
  have hsymm_eq : ∀ w : CoordinateRing H, (involutionEquiv H).symm w = involution H w := by
    intro w
    have hfwd : involutionEquiv H (involution H w) = w := involution_involution H w
    have := congrArg (involutionEquiv H).symm hfwd
    simpa using this.symm

  have hI : Ideal.comap (involutionEquiv H).symm.toRingHom (Ideal.span {alg}) = Ideal.span {alg} := by
    ext c
    simp only [Ideal.mem_comap, Ideal.mem_span_singleton]
    have h_coe : (involutionEquiv H).symm.toRingHom c = involution H c := hsymm_eq c
    rw [h_coe]
    constructor
    · rintro ⟨d, hd⟩
      refine ⟨involution H d, ?_⟩
      have happ := congrArg (involution H) hd
      rw [map_mul, halg_fix] at happ
      rw [involution_involution H c] at happ
      exact happ
    · rintro ⟨d, hd⟩
      refine ⟨involution H d, ?_⟩
      have happ := congrArg (involution H) hd
      rw [map_mul, halg_fix] at happ
      exact happ

  rw [ordAtSpec_eq_count _ A 0 hne, ordAtSpec_eq_count _ A 0 hne, hcalg]
  have h_comap_ideal : (conjHeightOne (H := H) v).asIdeal =
      Ideal.comap (involutionEquiv H).symm.toRingHom v.asIdeal := rfl
  rw [h_comap_ideal]
  congr 1
  -- `Ideal.span {alg}` is invariant under `(involutionEquiv H).symm` (via `hI`), so counting
  -- `comap v.asIdeal` against it agrees with counting `v.asIdeal` against it directly. No
  -- Mathlib lemma packages this for a bare ring equiv, so we prove it here directly, matching
  -- this file's existing `Associates.prime_pow_dvd_iff_le`/`Associates.mk_le_mk_iff_dvd` idiom
  -- (e.g. `ordAtSpec_add_eq_of_lt` above): `n ≤ count P I ↔ P^n ∣ I`, and divisibility
  -- transports along `Ideal.map f` for `f := (involutionEquiv H).toRingHom`, which is
  -- multiplicative (`Ideal.mapHom`, `Ideal.map_pow`). Crucially, `Ideal.comap
  -- (involutionEquiv H).symm.toRingHom = Ideal.map (involutionEquiv H).toRingHom`
  -- (`Ideal.comap_symm`), so `w := (conjHeightOne v).asIdeal` is *itself* `map f v.asIdeal`,
  -- and `hI` (rewritten the same way) says `map f alg' = alg'` — everything below is then a
  -- single multiplicative hom `f` applied to two ideals, no inverse map needed at all.
  classical
  set f := (involutionEquiv H).toRingHom with hf_def
  set alg' := Ideal.span ({alg} : Set (CoordinateRing H)) with halg'_def
  have halg'ne : Associates.mk alg' ≠ 0 :=
    Associates.mk_ne_zero.mpr (Ideal.span_singleton_eq_bot.not.mpr (hcalg ▸ hne))
  have hcomap_eq_map : ∀ I : Ideal (CoordinateRing H),
      Ideal.comap (involutionEquiv H).symm.toRingHom I = Ideal.map f I := fun I =>
    Ideal.comap_symm (f := involutionEquiv H) (I := I)
  have hw_eq : (conjHeightOne (H := H) v).asIdeal = Ideal.map f v.asIdeal := by
    rw [h_comap_ideal, hcomap_eq_map]
  have hmap_alg' : Ideal.map f alg' = alg' := by
    have := hI; rw [hcomap_eq_map] at this; exact this
  -- `map f v.asIdeal ^ n ∣ alg' ↔ v.asIdeal ^ n ∣ alg'`, one direction via the multiplicative
  -- `map f` directly, the other via `map f.symm` (using `Ideal.map_of_equiv` to undo `map f`).
  have hdvd_fwd : ∀ n : ℕ, v.asIdeal ^ n ∣ alg' → (Ideal.map f v.asIdeal) ^ n ∣ alg' := by
    intro n ⟨c, hc⟩
    refine ⟨Ideal.map f c, ?_⟩
    have hmap := congrArg (Ideal.map f) hc
    rwa [Ideal.map_mul, Ideal.map_pow, hmap_alg'] at hmap
  have hdvd_bwd : ∀ n : ℕ, (Ideal.map f v.asIdeal) ^ n ∣ alg' → v.asIdeal ^ n ∣ alg' := by
    intro n ⟨c, hc⟩
    refine ⟨Ideal.map (involutionEquiv H).symm.toRingHom c, ?_⟩
    have hmap := congrArg (Ideal.map (involutionEquiv H).symm.toRingHom) hc
    rw [Ideal.map_mul, Ideal.map_pow] at hmap
    -- `map f.symm (map f I) = I` for a `RingEquiv f` (`Ideal.map_of_equiv`), applied both to
    -- `I = v.asIdeal` and, via `hmap_alg'` (`map f alg' = alg'`), to pin down that `alg'` is
    -- also fixed by `map f.symm`.
    have hmap_alg'_symm : Ideal.map (involutionEquiv H).symm.toRingHom alg' = alg' := by
      have heq : Ideal.map (involutionEquiv H).symm.toRingHom (Ideal.map f alg') = alg' := by
        rw [hf_def]; exact Ideal.map_of_equiv (f := involutionEquiv H) (I := alg')
      rwa [hmap_alg'] at heq
    have hmap_v : Ideal.map (involutionEquiv H).symm.toRingHom (Ideal.map f v.asIdeal) =
        v.asIdeal := by
      rw [hf_def]; exact Ideal.map_of_equiv (f := involutionEquiv H) (I := v.asIdeal)
    rwa [hmap_v, hmap_alg'_symm] at hmap
  have hcount_iff_w : ∀ n : ℕ,
      n ≤ (Associates.mk (Ideal.map f v.asIdeal)).count (Associates.mk alg').factors ↔
        (Ideal.map f v.asIdeal) ^ n ∣ alg' := by
    intro n
    rw [← Associates.mk_le_mk_iff_dvd, Associates.mk_pow]
    rw [← hw_eq]
    exact (Associates.prime_pow_dvd_iff_le halg'ne
      (conjHeightOne (H := H) v).associates_irreducible).symm
  have hcount_iff_v : ∀ n : ℕ,
      n ≤ (Associates.mk v.asIdeal).count (Associates.mk alg').factors ↔ v.asIdeal ^ n ∣ alg' := by
    intro n
    rw [← Associates.mk_le_mk_iff_dvd, Associates.mk_pow]
    exact (Associates.prime_pow_dvd_iff_le halg'ne v.associates_irreducible).symm
  rw [hcomap_eq_map]
  apply le_antisymm
  · by_contra hcon
    push_neg at hcon
    have hge : (Associates.mk v.asIdeal).count (Associates.mk alg').factors + 1 ≤
        (Associates.mk (Ideal.map f v.asIdeal)).count (Associates.mk alg').factors := hcon
    have hdvd_w := (hcount_iff_w _).mp hge
    have hdvd_v := hdvd_bwd _ hdvd_w
    have := (hcount_iff_v _).mpr hdvd_v
    omega
  · by_contra hcon
    push_neg at hcon
    have hge : (Associates.mk (Ideal.map f v.asIdeal)).count (Associates.mk alg').factors + 1 ≤
        (Associates.mk v.asIdeal).count (Associates.mk alg').factors := hcon
    have hdvd_v := (hcount_iff_v _).mp hge
    have hdvd_w := hdvd_fwd _ hdvd_v
    have := (hcount_iff_w _).mpr hdvd_w
    omega





/-! ## §3f. `c₀.natDegree ≤ 2`, closed-point-native, avoiding the `pairNorm`
circularity entirely.

**ChatGPT-suggested route (confirmed non-circular).** Rather than bound
`c₀.natDegree` via `deg(pairNorm a₀ b₀)` (which `hinf₀` only bounds back in
terms of `c₀.natDegree` itself — vacuous), work directly with ideal membership
in `CoordinateRing H`: for irreducible `q ∣ c₀`, `hgu` forces
`toPair H a₀ b₀ ∉ v.asIdeal` for *some* `v` lying over `q` (else `q` would
divide `gcd (gcd a₀ b₀) c₀`), and `hzsuppSpec₀` then forces that `v` to be
`pointHeightOne' x₁` or `pointHeightOne' x₂` — pinning `q` to be linear,
rational, and multiplicity-one, with at most two such factors total. `hinf₀`
never enters this argument. -/

/-- **General going-up, with exact comap (no degree restriction).** Every
irreducible `q : k[X]` determines a height-one prime `v` of `CoordinateRing H`
lying exactly over `Ideal.span {q}` (`v.asIdeal.comap (algebraMap k[X]
(CoordinateRing H)) = Ideal.span {q}`, not just `≤`). Extracted from
`heightOneSpectrum_of_irreducible_ne_pointIdeal`'s proof: the going-up step
(`Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain`) and the exact
comap equality it produces never used `2 ≤ q.natDegree` — that hypothesis was
only needed for the `≠ pointHeightOne' P` conclusion, dropped here since this
version is applied to *every* factor of `c₀`, including linear ones. -/
theorem heightOneSpectrum_over_irreducible
    (q : k[X]) (hq : Irreducible q) :
    ∃ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      Ideal.comap (algebraMap k[X] (CoordinateRing H)) v.asIdeal =
        Ideal.span ({q} : Set k[X]) := by
  have hmonic : (X ^ 2 - C H.f : (k[X])[X]).Monic :=
    Polynomial.monic_X_pow_sub_C H.f two_ne_zero
  haveI hfin : Module.Finite k[X] (CoordinateRing H) := Polynomial.Monic.finite_adjoinRoot hmonic
  haveI hint : Algebra.IsIntegral k[X] (CoordinateRing H) :=
    Algebra.IsIntegral.of_finite k[X] (CoordinateRing H)
  haveI : IsDomain (CoordinateRing H) := IsDedekindDomain.toIsDomain
  have hqne0 : q ≠ 0 := hq.ne_zero
  have hspanq_prime : (Ideal.span ({q} : Set k[X])).IsPrime :=
    (Ideal.span_singleton_prime hqne0).mpr hq.prime
  haveI : (Ideal.span ({q} : Set k[X])).IsPrime := hspanq_prime
  have hker_inj : Function.Injective (algebraMap k[X] (CoordinateRing H)) := by
    show Function.Injective (AdjoinRoot.of (X ^ 2 - C H.f))
    exact AdjoinRoot.of.injective_of_degree_ne_zero degree_X_sq_sub_C_H_f_ne_zero
  have hker_bot : RingHom.ker (algebraMap k[X] (CoordinateRing H)) = ⊥ :=
    RingHom.ker_eq_bot_iff_eq_zero _ |>.mpr (fun a ha => hker_inj (by simpa using ha))
  obtain ⟨Q, hQprime, hQcomap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain
      (R := k[X]) (S := CoordinateRing H) (Ideal.span ({q} : Set k[X]))
      (hP := hker_bot ▸ bot_le)
  haveI : Q.IsPrime := hQprime
  have hQ_ne_bot : Q ≠ ⊥ := by
    intro hQbot
    rw [hQbot] at hQcomap
    have : Ideal.span ({q} : Set k[X]) = ⊥ :=
      hQcomap.symm.trans (Ideal.comap_bot_of_injective _ hker_inj)
    rw [Ideal.span_singleton_eq_bot] at this
    exact hqne0 this
  exact ⟨⟨Q, hQprime, hQ_ne_bot⟩, hQcomap⟩

/-- **`toPair H A B ∈ v.asIdeal → q ∣ A`**, for `v` lying exactly over `q`
(via `heightOneSpectrum_over_irreducible`'s comap equality). Only the `A`-part
transfers cleanly through `comap` (the `B·y` term isn't `algebraMap` of a
`k[X]` element), but that's already enough: combined with the same fact
applied to a second combination, we can detect `q ∣ A ∧ q ∣ B` termwise. -/
theorem dvd_of_algebraMap_mem_of_comap_eq
    (q A : k[X]) (v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H))
    (hv : Ideal.comap (algebraMap k[X] (CoordinateRing H)) v.asIdeal =
      Ideal.span ({q} : Set k[X]))
    (hA : algebraMap k[X] (CoordinateRing H) A ∈ v.asIdeal) : q ∣ A := by
  have : A ∈ Ideal.comap (algebraMap k[X] (CoordinateRing H)) v.asIdeal := hA
  rw [hv, Ideal.mem_span_singleton] at this
  exact this

/-- **The membership half of ChatGPT's key lemma.** `q ∣ A → q ∣ B →
toPair H A B ∈ Ideal.span {algebraMap q}` (hence `∈ v.asIdeal` for any `v`
lying over `q`, since `Ideal.span {algebraMap q} ≤ v.asIdeal` there). Trivial:
`toPair H A B = algebraMap A + algebraMap B * y`, and both summands are
divisible by `algebraMap q` once `A, B` are. -/
theorem toPair_mem_span_algebraMap_of_dvd
    (q A B : k[X]) (hqA : q ∣ A) (hqB : q ∣ B) :
    toPair H A B ∈ Ideal.span ({algebraMap k[X] (CoordinateRing H) q} : Set (CoordinateRing H)) := by
  rw [Ideal.mem_span_singleton]
  unfold HyperellipticPolynomial.toPair
  obtain ⟨A', rfl⟩ := hqA
  obtain ⟨B', rfl⟩ := hqB
  refine ⟨algebraMap k[X] (CoordinateRing H) A' +
    algebraMap k[X] (CoordinateRing H) B' * y H, ?_⟩
  simp only [map_mul]
  ring

/-- **The full membership iff.** `toPair H A B ∈ Ideal.span {algebraMap q} ↔
q ∣ A ∧ q ∣ B`. The reverse direction is `toPair_mem_span_algebraMap_of_dvd`
(trivial). Forward: membership gives `toPair H A B = algebraMap q * w` for
some `w`; write `w = toPair H E F` (`toPair_surjective_local`), so `toPair H A
B = toPair H (q*E) (q*F)` (`toPair_mul`, `algebraMap q = toPair H q 0`); then
`toPair_injective` (needs `H.f.natDegree = 5`, threaded as `hdeg`) forces
`A = q*E`, `B = q*F` directly, no coefficient/AdjoinRoot bookkeeping needed. -/
theorem toPair_mem_span_algebraMap_iff
    (hdeg : H.f.natDegree = 5) (q A B : k[X]) :
    toPair H A B ∈ Ideal.span ({algebraMap k[X] (CoordinateRing H) q} : Set (CoordinateRing H)) ↔
      q ∣ A ∧ q ∣ B := by
  constructor
  · intro hmem
    rw [Ideal.mem_span_singleton] at hmem
    obtain ⟨w, hw⟩ := hmem
    obtain ⟨E, F, hEF⟩ := toPair_surjective_local H w
    rw [hEF] at hw
    have hqpair : algebraMap k[X] (CoordinateRing H) q = toPair H q 0 := by
      unfold HyperellipticPolynomial.toPair; simp
    have hprod : toPair H A B = toPair H (q * E) (q * F) := by
      rw [hw, hqpair]
      have := toPair_mul (H := H) q 0 E F
      simpa using this
    obtain ⟨hAeq, hBeq⟩ := toPair_injective H hdeg A B (q * E) (q * F) hprod
    exact ⟨⟨E, hAeq⟩, ⟨F, hBeq⟩⟩
  · rintro ⟨hqA, hqB⟩
    exact toPair_mem_span_algebraMap_of_dvd (H := H) q A B hqA hqB

/-- **The witness `v`.** If `toPair H a₀ b₀ ∉ Ideal.span {algebraMap q}`, there is a
height-one prime `v` with `algebraMap q ∈ v.asIdeal` (i.e. `v` "lies over `q`") and
`ordAtSpec v a₀ b₀ < ordAtSpec v q 0`. Proved by comparing `Associates.count` at every
`v` in the (finite) union of the two factorizations' supports: if no such `v` existed,
every count of `span{toPair a₀ b₀}` would be `≥` the matching count of
`span{algebraMap q}`, giving `span{algebraMap q} ∣ span{toPair a₀ b₀}` (`Multiset.le`
on `normalizedFactors`, `UniqueFactorizationMonoid.dvd_iff_normalized_factors_le_
normalized_factors`) — i.e. `toPair a₀ b₀ ∈ span{algebraMap q}` (`Ideal.dvd_iff_le` +
`Ideal.mem_span_singleton`), contradicting the hypothesis. -/
theorem exists_ordAtSpec_lt_of_notMem_span_algebraMap
    [IsDedekindDomain (CoordinateRing H)]
    (q a₀ b₀ : k[X]) (hq : Irreducible q) (hab₀ne : toPair H a₀ b₀ ≠ 0)
    (hnotmem : toPair H a₀ b₀ ∉
      Ideal.span ({algebraMap k[X] (CoordinateRing H) q} : Set (CoordinateRing H))) :
    ∃ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      algebraMap k[X] (CoordinateRing H) q ∈ v.asIdeal ∧
      ordAtSpec v a₀ b₀ < ordAtSpec v q 0 := by
  classical
  haveI : IsDomain (CoordinateRing H) := IsDedekindDomain.toIsDomain
  have hqpair : algebraMap k[X] (CoordinateRing H) q = toPair H q 0 := by
    unfold HyperellipticPolynomial.toPair; simp
  have hqne : toPair H q (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]; exact fun h => hq.ne_zero h.1
  by_contra hcon
  push_neg at hcon
  apply hnotmem
  rw [Ideal.mem_span_singleton, hqpair]
  -- Every `v` satisfies `ordAtSpec v q 0 ≤ ordAtSpec v a₀ b₀`, whenever `algebraMap q ∈
  -- v.asIdeal` (`hcon`, rearranged); when `algebraMap q ∉ v.asIdeal`, `ordAtSpec v q 0 = 0
  -- ≤ ordAtSpec v a₀ b₀` too (`ordAtSpec_nonneg`). So the inequality holds at *every* `v`,
  -- unconditionally — giving `count v (span{algebraMap q}) ≤ count v (span{toPair a₀ b₀})`
  -- everywhere, hence `span{algebraMap q} ∣ span{toPair a₀ b₀}`.
  have hcount_le : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk v.asIdeal).count
        (Associates.mk (Ideal.span ({toPair H q 0} : Set (CoordinateRing H)))).factors ≤
      (Associates.mk v.asIdeal).count
        (Associates.mk (Ideal.span ({toPair H a₀ b₀} : Set (CoordinateRing H)))).factors := by
    intro v
    have hordv_le : ordAtSpec v q 0 ≤ ordAtSpec v a₀ b₀ := by
      by_cases hvmem : toPair H q 0 ∈ v.asIdeal
      · exact hcon v (by rwa [← hqpair] at hvmem)
      · rw [ordAtSpec_eq_zero_of_notMem v q 0 hvmem]
        exact ordAtSpec_nonneg v a₀ b₀ hab₀ne
    have hcAB := ordAtSpec_eq_count v q 0 hqne
    have hcA'B' := ordAtSpec_eq_count v a₀ b₀ hab₀ne
    rw [hcAB, hcA'B'] at hordv_le
    exact_mod_cast hordv_le
  have hle : Ideal.span ({toPair H q 0} : Set (CoordinateRing H)) ∣
      Ideal.span ({toPair H a₀ b₀} : Set (CoordinateRing H)) := by
    haveI hqIne : Ideal.span ({toPair H q 0} : Set (CoordinateRing H)) ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hqne
    haveI habIne : Ideal.span ({toPair H a₀ b₀} : Set (CoordinateRing H)) ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hab₀ne
    have hMultiset_le :
        UniqueFactorizationMonoid.normalizedFactors
          (Ideal.span ({toPair H q 0} : Set (CoordinateRing H))) ≤
        UniqueFactorizationMonoid.normalizedFactors
          (Ideal.span ({toPair H a₀ b₀} : Set (CoordinateRing H))) := by
      rw [Multiset.le_iff_count]
      intro J
      by_cases hJprime : J.IsPrime ∧ J ≠ ⊥
      · set v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H) :=
          ⟨J, hJprime.1, hJprime.2⟩ with hv_def
        have hvJ : v.asIdeal = J := rfl
        have hq_count := Ideal.count_associates_factors_eq hqIne v.isPrime v.ne_bot
        have hab_count := Ideal.count_associates_factors_eq habIne v.isPrime v.ne_bot
        calc
          Multiset.count J (UniqueFactorizationMonoid.normalizedFactors
              (Ideal.span ({toPair H q 0} : Set (CoordinateRing H))))
              = (Associates.mk v.asIdeal).count
                  (Associates.mk (Ideal.span ({toPair H q 0} : Set (CoordinateRing H)))).factors := by
                simpa [hvJ] using hq_count.symm
          _ ≤ (Associates.mk v.asIdeal).count
                (Associates.mk (Ideal.span ({toPair H a₀ b₀} : Set (CoordinateRing H)))).factors :=
                hcount_le v
          _ = Multiset.count J (UniqueFactorizationMonoid.normalizedFactors
                (Ideal.span ({toPair H a₀ b₀} : Set (CoordinateRing H)))) := by
                simpa [hvJ] using hab_count
      · push Not at hJprime
        by_cases hJ0 : J = 0
        · have h1 : Multiset.count J (UniqueFactorizationMonoid.normalizedFactors
              (Ideal.span ({toPair H q 0} : Set (CoordinateRing H)))) = 0 := by
            rw [Multiset.count_eq_zero]
            intro hmem
            have hle := ((Ideal.mem_normalizedFactors_iff hqIne).mp hmem).2
            rw [hJ0, Ideal.zero_eq_bot, le_bot_iff] at hle
            exact hqIne hle
          have h2 : Multiset.count J (UniqueFactorizationMonoid.normalizedFactors
              (Ideal.span ({toPair H a₀ b₀} : Set (CoordinateRing H)))) = 0 := by
            rw [Multiset.count_eq_zero]
            intro hmem
            have hle := ((Ideal.mem_normalizedFactors_iff habIne).mp hmem).2
            rw [hJ0, Ideal.zero_eq_bot, le_bot_iff] at hle
            exact habIne hle
          rw [h1, h2]
        · have hJprime' : ¬ J.IsPrime := by
            intro hprime
            apply hJ0
            rw [Ideal.zero_eq_bot]
            exact hJprime hprime
          have h1 : Multiset.count J (UniqueFactorizationMonoid.normalizedFactors
              (Ideal.span ({toPair H q 0} : Set (CoordinateRing H)))) = 0 := by
            rw [Multiset.count_eq_zero]
            intro hmem
            exact hJprime' ((Ideal.mem_normalizedFactors_iff hqIne).mp hmem).1
          have h2 : Multiset.count J (UniqueFactorizationMonoid.normalizedFactors
              (Ideal.span ({toPair H a₀ b₀} : Set (CoordinateRing H)))) = 0 := by
            rw [Multiset.count_eq_zero]
            intro hmem
            exact hJprime' ((Ideal.mem_normalizedFactors_iff habIne).mp hmem).1
          rw [h1, h2]
    calc Ideal.span ({toPair H q 0} : Set (CoordinateRing H))
        = (UniqueFactorizationMonoid.normalizedFactors
            (Ideal.span ({toPair H q 0} : Set (CoordinateRing H)))).prod :=
          (Ideal.prod_normalizedFactors_eq_self hqIne).symm
      _ ∣ (UniqueFactorizationMonoid.normalizedFactors
            (Ideal.span ({toPair H a₀ b₀} : Set (CoordinateRing H)))).prod :=
          Multiset.prod_dvd_prod_of_le hMultiset_le
      _ = Ideal.span ({toPair H a₀ b₀} : Set (CoordinateRing H)) :=
          Ideal.prod_normalizedFactors_eq_self habIne
  -- `hle : span{toPair q 0} ∣ span{toPair a₀ b₀}` gives the required element membership.
  have hmemb : toPair H a₀ b₀ ∈ Ideal.span ({toPair H q 0} : Set (CoordinateRing H)) :=
    Ideal.dvd_span_singleton.mp hle
  rw [Ideal.mem_span_singleton] at hmemb
  exact hmemb

/-- **Case A (fully closed): at `v` with `conjHeightOne v` also outside
`{x₁,x₂}`, `ordAtSpec v c₀ 0 = 0`.** Uses `hzsuppSpec₀` at *both* `v` and
`conjHeightOne v` (legitimate: `hzsuppSpec₀` is a hypothesis at every closed
point). Since `c₀` has `B = 0`, `algebraMap c₀` is `involution`-fixed
(`involution_algebraMap`), so `ordAtSpec v c₀ 0 > 0` transports to
`ordAtSpec (conjHeightOne v) c₀ 0 > 0` too (`mem_conjHeightOne_iff`). Both
instances of `hzsuppSpec₀` (indicator `0` at both, by hypothesis) then force
`toPair H a₀ b₀ ∈ v.asIdeal` **and** `toPair H a₀ (-b₀) ∈ v.asIdeal` (the
second via `mem_conjHeightOne_iff` applied to the *involution* of `toPair H a₀
b₀`, which lands in `v.asIdeal` iff `toPair H a₀ b₀ ∈ (conjHeightOne
v).asIdeal`). Adding gives `algebraMap (2a₀) ∈ v.asIdeal`, hence (via `q :=`
the generator of `v`'s comap, `hchar`) `q ∣ a₀`. Subtracting gives `algebraMap
(2b₀) * y H ∈ v.asIdeal`; if `q ∤ H.f` then `y H ∉ v.asIdeal` (else `y H ^ 2 =
algebraMap H.f ∈ v.asIdeal` forces `q ∣ H.f` via the comap), giving `q ∣ b₀`
directly. If `q ∣ H.f`, use the *exact* order computation instead: since `H.f`
squarefree, `ordAtSpec v q 0 = 2` and `ordAtSpec v (y H) 0`-shaped reasoning
(via `y H ^ 2 = algebraMap H.f`) forces the whole argument through a
valuation-comparison rather than a bare unit/nonunit split — this sub-case is
proved via `hzsuppSpec₀ v` directly with the sharper multiplicity bound
`ordAtSpec v c₀ 0 ≥ 2` from `q^2 ∣ c₀` (using `q ∣ c₀`, `ordAtSpec v q 0 = 2`)
against `ordAtSpec v (toPair H a₀ b₀) ≤ 1` (itself from the `q ∣ H.f` valuation
argument at `v`), giving `hzsuppSpec₀`'s inequality `-1 ≤ 1 - ordAtSpec v c₀ 0`
i.e. `ordAtSpec v c₀ 0 ≤ 2` — contradicting `≥ 4` if `q^2 ∣ c₀` fails to be
excluded first; see `irreducible_sq_not_dvd_c0` below, which packages this
whole ramified sub-argument at the `H.Point` level instead (cleaner: uses
`ordAt_linX_eq`/`pointIdeal_sq_dvd_span_linX_of_ramified` directly, no
abstract-`q` valuation bookkeeping needed). This theorem only proves the
**support** half (Case A elimination); multiplicity is handled separately. -/
theorem ordAtSpec_eq_zero_of_notMem_four_of_dvd
    [IsDedekindDomain (CoordinateRing H)] [DecidableEq k]
    (x₁ x₂ : H.Point) (a₀ b₀ c₀ : k[X]) (hc₀ne : c₀ ≠ 0)
    (hab₀ne : toPair H a₀ b₀ ≠ 0)
    (hgu : IsUnit (gcd (gcd a₀ b₀) c₀))
    (hzsuppSpec₀ : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      ordAtSpec v a₀ b₀ - ordAtSpec v c₀ (0 : k[X]) ≥
        -((if v = pointHeightOne' x₁ then 1 else 0) +
          (if v = pointHeightOne' x₂ then 1 else 0)))
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H))
    (hv1 : v ≠ pointHeightOne' x₁) (hv2 : v ≠ pointHeightOne' x₂)
    (hw1 : conjHeightOne (H := H) v ≠ pointHeightOne' x₁)
    (hw2 : conjHeightOne (H := H) v ≠ pointHeightOne' x₂) :
    ordAtSpec v c₀ (0 : k[X]) = 0 := by
  haveI : IsDomain (CoordinateRing H) := IsDedekindDomain.toIsDomain
  by_contra hne0
  have hc₀'ne : toPair H c₀ (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]; exact fun h => hc₀ne h.1
  have hpos : 0 < ordAtSpec v c₀ (0 : k[X]) :=
    lt_of_le_of_ne (ordAtSpec_nonneg v c₀ 0 hc₀'ne) (Ne.symm hne0)
  have hvmem : toPair H c₀ (0 : k[X]) ∈ v.asIdeal := by
    by_contra hnotmem
    have := ordAtSpec_eq_zero_of_notMem v c₀ 0 hnotmem
    omega
  set w : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H) := conjHeightOne (H := H) v
    with hw_def
  -- `algebraMap c₀` is `involution`-fixed (`B = 0`), so membership transports to `w`.
  have hcalg : algebraMap k[X] (CoordinateRing H) c₀ = toPair H c₀ (0 : k[X]) := by
    unfold HyperellipticPolynomial.toPair; simp
  have hwmem : toPair H c₀ (0 : k[X]) ∈ w.asIdeal := by
    rw [hw_def, mem_conjHeightOne_iff, ← hcalg, involution_algebraMap, hcalg]
    exact hvmem
  have hwpos : 0 < ordAtSpec w c₀ (0 : k[X]) := by
    by_contra hle
    push_neg at hle
    have hle0 : ordAtSpec w c₀ (0 : k[X]) = 0 := le_antisymm hle (ordAtSpec_nonneg w c₀ 0 hc₀'ne)
    have := ordAtSpec_eq_zero_of_notMem w c₀ 0
    -- `hle0` contradicts `hwmem` via `ordAtSpec_eq_zero_of_notMem`'s converse direction:
    -- if `ordAtSpec = 0` were forced only by non-membership, membership would force `> 0`.
    -- Direct route: `ordAtSpec_eq_count` plus `hwmem` gives a nonzero count.
    have hcount := ordAtSpec_eq_count w c₀ 0 hc₀'ne
    rw [hle0] at hcount
    have hcount0 : (Associates.mk w.asIdeal).count
        (Associates.mk (Ideal.span ({toPair H c₀ (0:k[X])} : Set (CoordinateRing H)))).factors
        = 0 := by exact_mod_cast hcount.symm
    have hdvd : w.asIdeal ∣ Ideal.span ({toPair H c₀ (0:k[X])} : Set (CoordinateRing H)) :=
      Ideal.dvd_span_singleton.mpr hwmem
    have hIne : Ideal.span ({toPair H c₀ (0:k[X])} : Set (CoordinateRing H)) ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hc₀'ne
    have hge1 : 1 ≤ (Associates.mk w.asIdeal).count
        (Associates.mk (Ideal.span ({toPair H c₀ (0:k[X])} : Set (CoordinateRing H)))).factors := by
      have hIne' : Associates.mk
          (Ideal.span ({toPair H c₀ (0:k[X])} : Set (CoordinateRing H))) ≠ 0 :=
        Associates.mk_ne_zero.mpr hIne
      rw [← Associates.prime_pow_dvd_iff_le hIne' w.associates_irreducible, pow_one]
      exact Associates.mk_le_mk_iff_dvd.mpr hdvd
    omega
  -- `hzsuppSpec₀` at `v` and `w` (both indicators `0`) force membership of `toPair H a₀ b₀`
  -- at both.
  have hbv := hzsuppSpec₀ v
  simp only [hv1, hv2, if_neg, if_false] at hbv
  have habv_pos : 0 < ordAtSpec v a₀ b₀ := by omega
  have habvmem : toPair H a₀ b₀ ∈ v.asIdeal := by
    by_contra hnotmem
    have := ordAtSpec_eq_zero_of_notMem v a₀ b₀ hnotmem
    omega
  have hbw := hzsuppSpec₀ w
  simp only [hw1, hw2, if_neg, if_false] at hbw
  have habw_pos : 0 < ordAtSpec w a₀ b₀ := by omega
  have habwmem : toPair H a₀ b₀ ∈ w.asIdeal := by
    by_contra hnotmem
    have := ordAtSpec_eq_zero_of_notMem w a₀ b₀ hnotmem
    omega
  -- `habwmem` transports back to `v` via `involution`: `toPair H a₀ (-b₀) ∈ v.asIdeal`.
  have habvmem' : toPair H a₀ (-b₀) ∈ v.asIdeal := by
    rw [hw_def, mem_conjHeightOne_iff] at habwmem
    rwa [toPair_involution] at habwmem
  -- Add and subtract: `algebraMap (2a₀) ∈ v.asIdeal`, `algebraMap (2b₀) * y H ∈ v.asIdeal`.
  have hadd : toPair H a₀ b₀ + toPair H a₀ (-b₀) = algebraMap k[X] (CoordinateRing H) (2 * a₀) := by
    unfold HyperellipticPolynomial.toPair
    rw [map_mul, map_ofNat, map_neg]
    ring
  have hsub : toPair H a₀ b₀ - toPair H a₀ (-b₀) =
      algebraMap k[X] (CoordinateRing H) (2 * b₀) * y H := by
    unfold HyperellipticPolynomial.toPair
    rw [map_mul, map_ofNat, map_neg]
    ring
  have h2a_mem : algebraMap k[X] (CoordinateRing H) (2 * a₀) ∈ v.asIdeal := by
    rw [← hadd]; exact v.asIdeal.add_mem habvmem habvmem'
  have h2by_mem : algebraMap k[X] (CoordinateRing H) (2 * b₀) * y H ∈ v.asIdeal := by
    rw [← hsub]; exact v.asIdeal.sub_mem habvmem habvmem'
  -- Set up `P := v.asIdeal.comap = span {q}` for irreducible `q` (PID argument, as before).
  set P : Ideal k[X] := Ideal.comap (algebraMap k[X] (CoordinateRing H)) v.asIdeal with hP_def
  have hPprime : P.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨q, hq_gen⟩ := (IsPrincipalIdealRing.principal P).principal
  rw [Ideal.submodule_span_eq] at hq_gen
  have hc₀P : c₀ ∈ P := by
    show algebraMap k[X] (CoordinateRing H) c₀ ∈ v.asIdeal
    rw [hcalg]; exact hvmem
  have hqne0 : q ≠ 0 := by
    intro hq0
    rw [hq0, Ideal.span_singleton_zero] at hq_gen
    exact hc₀ne (by rw [← Ideal.mem_bot (R := k[X]), ← hq_gen]; exact hc₀P)
  have hq_irred : Irreducible q := by
    have hPprime' : (Ideal.span ({q} : Set k[X])).IsPrime := hq_gen ▸ hPprime
    exact (Ideal.span_singleton_prime hqne0).mp hPprime' |>.irreducible
  have hqc₀ : q ∣ c₀ := by
    have : c₀ ∈ Ideal.span ({q} : Set k[X]) := hq_gen ▸ hc₀P
    rwa [Ideal.mem_span_singleton] at this
  -- `2a₀ ∈ v.asIdeal → q ∣ 2*a₀ → q ∣ a₀` (`hchar`, `2` a unit).
  have hq2a : q ∣ 2 * a₀ := by
    have : 2 * a₀ ∈ P := h2a_mem
    rwa [hq_gen, Ideal.mem_span_singleton] at this
  have h2unit : IsUnit (2 : k[X]) := by
    rw [show (2 : k[X]) = Polynomial.C (2:k) from (map_ofNat Polynomial.C 2).symm]
    exact (Polynomial.isUnit_C).mpr (IsUnit.mk0 (2:k) hchar)
  have hq_prime : Prime q := hq_irred.prime
  have hqa₀ : q ∣ a₀ := by
    rcases (hq_prime.dvd_mul).mp hq2a with h | h
    · exact absurd h (hq_irred.not_dvd_isUnit h2unit)
    · exact h
  -- `2b₀ * y H ∈ v.asIdeal`: split on `q ∣ H.f` or not.
  by_cases hqf : q ∣ H.f
  · -- Ramified case is actually **impossible** here: `H.f` squarefree (`hsf`) means
    -- `q^2 ∤ H.f` (`q` irreducible, not a unit); combined with `q ∣ H.f` and
    -- `y H ^ 2 = algebraMap H.f`, a parity argument on `ordAtSpec v` at `q^2` vs
    -- `y H` gives a direct contradiction — no need to separate `q ∣ b₀` at all.
    exfalso
    have hyf : y H ^ 2 = algebraMap k[X] (CoordinateRing H) H.f := y_sq_eq H
    have hyToPair : y H = toPair H 0 1 := by unfold HyperellipticPolynomial.toPair; simp
    have hyne : toPair H 0 1 ≠ (0 : CoordinateRing H) := by
      rw [← hyToPair]
      -- `y H ≠ 0`: else `H.f = y H ^ 2 = 0`, contradicting `H.f` squarefree/nonzero
      -- implicitly (a squarefree `0` is impossible in a nontrivial ring since `0 = u*u`
      -- for any `u`, e.g. `u` non-unit if such exists; simplest: `H.f`'s `natDegree`
      -- context elsewhere in the file always assumes `H.f ≠ 0`, and `hqf : q ∣ H.f`
      -- with `q` irreducible forces `H.f ≠ 0`, since `q ∣ 0` is fine but then `H.f = 0`
      -- would make `Squarefree H.f` force `IsUnit q` for every `q` with `q*q ∣ 0`,
      -- i.e. every `q`, contradicting `hq_irred.not_isUnit` directly below via `hsf`.
      intro hy0
      rw [hy0] at hyf
      have halg0 : algebraMap k[X] (CoordinateRing H) H.f = 0 := by rw [← hyf]; ring
      have hf0 : H.f = 0 := by
        have htp0 : toPair H H.f (0:k[X]) = 0 := by
          unfold HyperellipticPolynomial.toPair; simpa using halg0
        exact ((toPair_eq_zero_iff H H.f 0).mp htp0).1
      have : IsUnit q := hsf q (by rw [hf0]; exact dvd_zero _)
      exact hq_irred.not_isUnit this
    have hordy_ge0 : 0 ≤ ordAtSpec v (0:k[X]) 1 := ordAtSpec_nonneg v 0 1 hyne
    have hordf : ordAtSpec v H.f (0:k[X]) = 2 * ordAtSpec v (0:k[X]) 1 := by
      have hprod : toPair H H.f 0 = toPair H 0 1 * toPair H 0 1 := by
        have hmul := toPair_mul (H := H) 0 1 0 1
        norm_num at hmul
        exact hmul.symm
      have := ordAtSpec_add_of_toPair_mul (H := H) v 0 1 0 1 H.f 0 hyne hyne hprod
      rw [this]; ring
    have hq2ndvd : ¬ q ^ 2 ∣ H.f := fun h => hq_irred.not_isUnit (hsf q (by rwa [pow_two] at h))
    -- `hordf : ordAtSpec v H.f 0 = 2 * ordAtSpec v (0) 1` is **even**. `q ∣ H.f` gives
    -- `ordAtSpec v H.f 0 ≥ 1` (cheap, membership via `ordAtSpec_eq_zero_of_notMem`'s
    -- contrapositive), so evenness forces `ordAtSpec v H.f 0 ≥ 2`. The genuine remaining
    -- gap: turning `ordAtSpec v H.f 0 ≥ 2` into `q ^ 2 ∣ H.f` in `k[X]` (contradicting
    -- `hq2ndvd`) needs comparing `v`'s multiplicity (in `CoordinateRing H`) against `q`'s
    -- own multiplicity in `k[X]` at `P = v.asIdeal.comap = span {q}` — i.e. a
    -- ramification-index fact (`ordAtSpec v (algebraMap q) 0` vs. `k[X]`-multiplicity of
    -- `q` in `q` itself, `= 1`), not yet established in this file for a general
    -- going-up prime (this is exactly the same class of gap flagged in this file's
    -- earlier history around `heightOneSpectrum_over_irreducible`/ramification).
    -- Isolating rather than forcing: see `chatgpt_prompt_ramified_squarefree.txt`.
    have hfpos : 0 < ordAtSpec v H.f (0:k[X]) := by
      have hfne : toPair H H.f (0:k[X]) ≠ 0 := by
        rw [Ne, toPair_eq_zero_iff]; exact fun h => hsf.ne_zero h.1
      have hfmem : toPair H H.f (0:k[X]) ∈ v.asIdeal := by
        have halgf : toPair H H.f (0:k[X]) = algebraMap k[X] (CoordinateRing H) H.f := by
          unfold HyperellipticPolynomial.toPair; simp
        rw [halgf]; show H.f ∈ P; rw [hq_gen, Ideal.mem_span_singleton]; exact hqf
      by_contra hle
      push_neg at hle
      have hle0 : ordAtSpec v H.f (0:k[X]) = 0 := le_antisymm hle (ordAtSpec_nonneg v H.f 0 hfne)
      have hcount := ordAtSpec_eq_count v H.f 0 hfne
      rw [hle0] at hcount
      have hIne : Ideal.span ({toPair H H.f (0:k[X])} : Set (CoordinateRing H)) ≠ 0 := by
        rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hfne
      have hge1 : 1 ≤ (Associates.mk v.asIdeal).count
          (Associates.mk (Ideal.span ({toPair H H.f (0:k[X])} : Set (CoordinateRing H)))).factors := by
        have hIne' : Associates.mk
            (Ideal.span ({toPair H H.f (0:k[X])} : Set (CoordinateRing H))) ≠ 0 :=
          Associates.mk_ne_zero.mpr hIne
        rw [← Associates.prime_pow_dvd_iff_le hIne' v.associates_irreducible, pow_one]
        exact Associates.mk_le_mk_iff_dvd.mpr (Ideal.dvd_span_singleton.mpr hfmem)
      omega
    have hordf_ge2 : ordAtSpec v H.f (0:k[X]) ≥ 2 := by omega
    -- **Corrected route (ChatGPT consultation, `chatgpt_prompt_ramified_sorry.txt`):
    -- the ramified case is NOT vacuous — `ordAtSpec v H.f 0 ≥ 2` is exactly what
    -- ramification predicts, not a contradiction. The actual argument compares the
    -- *relative* orders of `a₀` and `(2b₀)·y` inside `toPair a₀ b₀`; it never needs
    -- the exact ramification index `ordAtSpec v q 0`, only that it equals
    -- `ordAtSpec v H.f 0` (via `H.f = q*r`, `q ∤ r`, squarefreeness), which is
    -- `2 * ordAtSpec v (0) 1` (`hordf`) and hence `≥ 2`.
    obtain ⟨r, hfr⟩ := hqf
    have hq_not_dvd_r : ¬ q ∣ r := by
      intro hqr
      apply hq_irred.not_isUnit
      apply hsf q
      rw [hfr]
      exact mul_dvd_mul_left q hqr
    have hrne : toPair H r (0:k[X]) ≠ 0 := by
      rw [Ne, toPair_eq_zero_iff]
      exact fun h => hq_not_dvd_r (h.1 ▸ dvd_zero q)
    have hr_notmem : algebraMap k[X] (CoordinateRing H) r ∉ v.asIdeal := by
      intro hrmem
      apply hq_not_dvd_r
      have : r ∈ P := hrmem
      rwa [hq_gen, Ideal.mem_span_singleton] at this
    have hord_r : ordAtSpec v r (0:k[X]) = 0 := by
      apply ordAtSpec_eq_zero_of_notMem v r 0
      rwa [show toPair H r (0:k[X]) = algebraMap k[X] (CoordinateRing H) r by
        unfold HyperellipticPolynomial.toPair; simp]
    have hqne_toPair : toPair H q (0:k[X]) ≠ 0 := by
      rw [Ne, toPair_eq_zero_iff]; exact fun h => hqne0 h.1
    have hHf_prod : toPair H H.f (0:k[X]) = toPair H q (0:k[X]) * toPair H r (0:k[X]) := by
      have := toPair_mul (H := H) q 0 r 0
      simpa [hfr] using this.symm
    have hord_q_eq_f : ordAtSpec v q (0:k[X]) = ordAtSpec v H.f (0:k[X]) := by
      have := ordAtSpec_add_of_toPair_mul (H := H) v q 0 r 0 H.f 0 hqne_toPair hrne hHf_prod
      rw [this, hord_r, add_zero]
    -- `ordAtSpec v q 0 = 2 * ordAtSpec v (0) 1` (`m`, the order of `y`), and `m ≥ 1`.
    have hord_q_eq_2m : ordAtSpec v q (0:k[X]) = 2 * ordAtSpec v (0:k[X]) 1 := by
      rw [hord_q_eq_f]; exact hordf
    have hm_pos : 0 < ordAtSpec v (0:k[X]) 1 := by omega
    -- `toPair H a₀ b₀ ≠ 0` (from `habv_pos`), and its decomposition
    -- `toPair a₀ b₀ = toPair a₀ 0 + toPair 0 b₀`.
    have hab₀_ne : toPair H a₀ b₀ ≠ (0 : CoordinateRing H) := by
      intro h0
      rw [show ordAtSpec v a₀ b₀ = 0 from by unfold ordAtSpec; rw [if_pos h0]] at habv_pos
      exact lt_irrefl 0 habv_pos
    have hdecomp : toPair H a₀ b₀ = toPair H a₀ (0:k[X]) + toPair H (0:k[X]) b₀ := by
      have := toPair_add (H := H) a₀ 0 0 b₀
      simpa using this
    -- We're already inside `exfalso` (goal `False`), so derive it by cases on
    -- `q ∣ b₀`: get `ordAtSpec v (0) b₀ = ordAtSpec v (0) 1 = m`, via
    -- `toPair 0 b₀ = toPair b₀ 0 * toPair 0 1` and `ordAtSpec v b₀ 0 = 0`
    -- (nonmembership, since `q ∤ b₀`) in the non-divisibility case.
    by_cases hqb₀ : q ∣ b₀
    · -- `q ∣ a₀` (`hqa₀`), `q ∣ b₀`, `q ∣ c₀` (`hqc₀`) together contradict `hgu`.
      have hq_dvd_gcd : q ∣ gcd (gcd a₀ b₀) c₀ := dvd_gcd (dvd_gcd hqa₀ hqb₀) hqc₀
      exact absurd (isUnit_of_dvd_unit hq_dvd_gcd hgu) hq_irred.not_isUnit
    have hb₀_notmem : algebraMap k[X] (CoordinateRing H) b₀ ∉ v.asIdeal := by
      intro hb0mem
      apply hqb₀
      have : b₀ ∈ P := hb0mem
      rwa [hq_gen, Ideal.mem_span_singleton] at this
    have hb₀ne_toPair : toPair H b₀ (0:k[X]) ≠ 0 := by
      rw [Ne, toPair_eq_zero_iff]
      intro h
      exact hb₀_notmem (by
        rw [h.1, map_zero]; exact Submodule.zero_mem _)
    have hord_b₀ : ordAtSpec v b₀ (0:k[X]) = 0 := by
      apply ordAtSpec_eq_zero_of_notMem v b₀ 0
      rwa [show toPair H b₀ (0:k[X]) = algebraMap k[X] (CoordinateRing H) b₀ by
        unfold HyperellipticPolynomial.toPair; simp]
    -- `hyne : toPair H 0 1 ≠ 0` is already in scope (established earlier in this
    -- `by_cases hqf` branch, via `hyToPair`).
    have h0b₀_prod : toPair H (0:k[X]) b₀ = toPair H b₀ (0:k[X]) * toPair H (0:k[X]) 1 := by
      have := toPair_mul (H := H) b₀ 0 0 1
      simpa using this.symm
    have hord_0b₀ : ordAtSpec v (0:k[X]) b₀ = ordAtSpec v (0:k[X]) 1 := by
      have := ordAtSpec_add_of_toPair_mul (H := H) v b₀ 0 0 1 0 b₀ hb₀ne_toPair hyne h0b₀_prod
      rw [this, hord_b₀, zero_add]
    -- Case split on `a₀ = 0`.
    by_cases ha₀0 : a₀ = 0
    · -- `toPair a₀ b₀ = toPair 0 b₀` directly: `ordAtSpec v a₀ b₀ = m`.
      have habeq : ordAtSpec v a₀ b₀ = ordAtSpec v (0:k[X]) 1 := by
        rw [ha₀0, ← hord_0b₀]
      -- `hbv : ordAtSpec v a₀ b₀ ≥ ordAtSpec v c₀ 0 ≥ ordAtSpec v q 0 = 2m` (via
      -- `q ∣ c₀`), contradicting `habeq : ordAtSpec v a₀ b₀ = m` and `m > 0`.
      obtain ⟨s, hcs⟩ := hqc₀
      have hs_ne : toPair H s (0:k[X]) ≠ 0 := by
        rw [Ne, toPair_eq_zero_iff]
        intro h
        exact hc₀ne (by rw [hcs, h.1, mul_zero])
      have hcs_prod : toPair H c₀ (0:k[X]) = toPair H q (0:k[X]) * toPair H s (0:k[X]) := by
        have := toPair_mul (H := H) q 0 s 0
        simpa [hcs] using this.symm
      have hordc₀_ge : ordAtSpec v c₀ (0:k[X]) ≥ ordAtSpec v q (0:k[X]) := by
        have heq := ordAtSpec_add_of_toPair_mul (H := H) v q 0 s 0 c₀ 0 hqne_toPair hs_ne hcs_prod
        have hsnn : 0 ≤ ordAtSpec v s (0:k[X]) := ordAtSpec_nonneg v s 0 hs_ne
        omega
      omega
    · -- `a₀ ≠ 0`: decompose `toPair a₀ b₀ = toPair a₀ 0 + toPair 0 b₀`, with
      -- `ordAtSpec v a₀ 0 ≥ ordAtSpec v q 0 = 2m > m = ordAtSpec v 0 b₀`, so the sum's
      -- order is exactly `m` (`ordAtSpec_add_eq_of_lt`, smaller term wins).
      have ha₀ne_toPair : toPair H a₀ (0:k[X]) ≠ 0 := by
        rw [Ne, toPair_eq_zero_iff]; exact fun h => ha₀0 h.1
      obtain ⟨s, has⟩ := hqa₀
      have hs_ne_or_a₀0 : toPair H s (0:k[X]) ≠ 0 := by
        rw [Ne, toPair_eq_zero_iff]
        intro h
        exact ha₀0 (by rw [has, h.1, mul_zero])
      have has_prod : toPair H a₀ (0:k[X]) = toPair H q (0:k[X]) * toPair H s (0:k[X]) := by
        have := toPair_mul (H := H) q 0 s 0
        simpa [has] using this.symm
      have hord_a₀_ge : ordAtSpec v a₀ (0:k[X]) ≥ ordAtSpec v q (0:k[X]) := by
        have heq := ordAtSpec_add_of_toPair_mul (H := H) v q 0 s 0 a₀ 0
          hqne_toPair hs_ne_or_a₀0 has_prod
        have hsnn : 0 ≤ ordAtSpec v s (0:k[X]) := ordAtSpec_nonneg v s 0 hs_ne_or_a₀0
        omega
      have hlt : ordAtSpec v (0:k[X]) b₀ < ordAtSpec v a₀ (0:k[X]) := by
        rw [hord_0b₀]; omega
      -- `ordAtSpec_add_eq_of_lt` with `(A,B) := (0,b₀)` (the smaller term) and
      -- `(C,D) := (a₀,0)`: `ord v (0+a₀) (b₀+0) = ord v 0 b₀`.
      have hzero_ne : toPair H (0:k[X]) b₀ ≠ 0 := by
        rw [h0b₀_prod]; exact mul_ne_zero hb₀ne_toPair hyne
      have hsum_eq : ordAtSpec v ((0:k[X]) + a₀) (b₀ + (0:k[X])) = ordAtSpec v (0:k[X]) b₀ :=
        ordAtSpec_add_eq_of_lt (H := H) v (0:k[X]) b₀ a₀ (0:k[X])
          hzero_ne ha₀ne_toPair hlt
      have hsum_simp : ordAtSpec v a₀ b₀ = ordAtSpec v (0:k[X]) b₀ := by
        rw [zero_add, add_zero] at hsum_eq; exact hsum_eq
      rw [hsum_simp, hord_0b₀] at hbv
      -- `hbv : m ≥ ordAtSpec v c₀ 0 ≥ ordAtSpec v q 0 = 2m` (via `q ∣ c₀`, same as
      -- the `a₀ = 0` case above), contradicting `m > 0`.
      obtain ⟨s, hcs⟩ := hqc₀
      have hs_ne : toPair H s (0:k[X]) ≠ 0 := by
        rw [Ne, toPair_eq_zero_iff]
        intro h
        exact hc₀ne (by rw [hcs, h.1, mul_zero])
      have hcs_prod : toPair H c₀ (0:k[X]) = toPair H q (0:k[X]) * toPair H s (0:k[X]) := by
        have := toPair_mul (H := H) q 0 s 0
        simpa [hcs] using this.symm
      have hordc₀_ge : ordAtSpec v c₀ (0:k[X]) ≥ ordAtSpec v q (0:k[X]) := by
        have heq := ordAtSpec_add_of_toPair_mul (H := H) v q 0 s 0 c₀ 0 hqne_toPair hs_ne hcs_prod
        have hsnn : 0 ≤ ordAtSpec v s (0:k[X]) := ordAtSpec_nonneg v s 0 hs_ne
        omega
      omega
  · -- Unramified: `q ∤ H.f` means `y H ∉ v.asIdeal` (else `y H^2 = algebraMap H.f ∈
    -- v.asIdeal` forces `q ∣ H.f`), so `v.asIdeal` prime + `2b₀*y ∈ v.asIdeal` + `y ∉
    -- v.asIdeal` gives `algebraMap (2b₀) ∈ v.asIdeal`, hence `q ∣ 2b₀`, hence `q ∣ b₀`.
    have hynotmem : y H ∉ v.asIdeal := by
      intro hymem
      apply hqf
      have hy2mem : y H ^ 2 ∈ v.asIdeal := by
        rw [pow_two]; exact Ideal.mul_mem_left v.asIdeal (y H) hymem
      have hyf : y H ^ 2 = algebraMap k[X] (CoordinateRing H) H.f := y_sq_eq H
      rw [hyf] at hy2mem
      have : H.f ∈ P := hy2mem
      rwa [hq_gen, Ideal.mem_span_singleton] at this
    have h2b_mem : algebraMap k[X] (CoordinateRing H) (2 * b₀) ∈ v.asIdeal := by
      rcases v.isPrime.mem_or_mem h2by_mem with h | h
      · exact h
      · exact absurd h hynotmem
    have hq2b : q ∣ 2 * b₀ := by
      have : (2:k[X]) * b₀ ∈ P := h2b_mem
      rwa [hq_gen, Ideal.mem_span_singleton] at this
    have hqb₀ : q ∣ b₀ := by
      rcases (hq_prime.dvd_mul).mp hq2b with h | h
      · exact absurd h (hq_irred.not_dvd_isUnit h2unit)
      · exact h
    have hq_dvd_gcd : q ∣ gcd (gcd a₀ b₀) c₀ := dvd_gcd (dvd_gcd hqa₀ hqb₀) hqc₀
    exact absurd (isUnit_of_dvd_unit hq_dvd_gcd hgu) hq_irred.not_isUnit

/-! **STATUS: `false_of_bad_factor_split_deg_ge_two` — abandoned, dead scaffold
removed.** This was an earlier, superseded attempt at the same fact now proved (up to
Gap 1/Gap 2, see `chatgpt_prompt_final_two_gaps.txt`) by
`ordAtSpec_eq_zero_of_notMem_four_of_dvd` / `natDegree_le_two_of_gcdUnit_closed_point`
above. The abandoned draft is deleted rather than kept as a dangling, unclosed comment
block (it previously left ~100 lines of live, headerless tactic code after an
unterminated `!`, which does not parse). 

 **Final assembly: `c₀.natDegree ≤ 2`, closed-point-native, no `IsAlgClosed`.**
`ordAtSpec v c₀ 0 = 0` away from `{x₁, x₂}` (`ordAtSpec_eq_zero_of_notMem_pair_of_dvd`)
means the norm-degree identity `2·c₀.natDegree = ∑_{v∈T} residueDeg(v)·ordAtSpec(v,c₀,0)`
(`natDegree_pairNorm_eq_sum_residueDeg_ordAtSpec` applied to `(c₀,0)`, `pairNorm H c₀ 0 =
c₀^2`) collapses to (at most) the two terms at `pointHeightOne' x₁, pointHeightOne' x₂`,
each contributing `residueDeg = 1` (`residueDeg_pointHeightOne'`) times `ordAtSpec ≤
1` (from `hzsuppSpec₀`'s own indicator bound at those two points, mirroring
`ordAtSpec_le_indicator_of_isPoleBoundedAtPairSpec`'s style) — giving `2·c₀.natDegree
≤ 1 + 1 = 2`, i.e. `c₀.natDegree ≤ 1` (stronger than needed, matches `hcdeg1`'s later
bound, consistent since this is really the same fact reached earlier). -/
set_option maxHeartbeats 100000000 in
theorem natDegree_le_two_of_gcdUnit_closed_point
    [DecidableEq k]
    (hdeg : H.f.natDegree = 5)
    (x₁ x₂ : H.Point) (a₀ b₀ c₀ : k[X]) (hc₀ne : c₀ ≠ 0)
    (hab₀ne : toPair H a₀ b₀ ≠ 0)
    (hgu : IsUnit (gcd (gcd a₀ b₀) c₀))
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (hzsuppSpec₀ : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      ordAtSpec v a₀ b₀ - ordAtSpec v c₀ (0 : k[X]) ≥
        -((if v = pointHeightOne' x₁ then 1 else 0) +
          (if v = pointHeightOne' x₂ then 1 else 0))) :
    c₀.natDegree ≤ 2 := by
  haveI : IsDomain (CoordinateRing H) := IsDedekindDomain.toIsDomain

  /- An irreducible factor of `c₀` has a zero at the `X`-coordinate of one of
  the two distinguished rational points.  The important point is that the
  witness supplied by `exists_ordAtSpec_lt_of_notMem_span_algebraMap` is a
  closed point over the factor `q`; the pole bound then forces that witness
  to be one of `x₁,x₂`. -/
  have hq_root_location : ∀ {q : k[X]}, Irreducible q → q ∣ c₀ →
      q.IsRoot x₁.X ∨ q.IsRoot x₂.X := by
    intro q hq hqc
    have hqne : q ≠ 0 := hq.ne_zero
    have hnotmem : toPair H a₀ b₀ ∉
        Ideal.span ({algebraMap k[X] (CoordinateRing H) q} : Set (CoordinateRing H)) := by
      intro hmem
      obtain ⟨hqa, hqb⟩ :=
        (toPair_mem_span_algebraMap_iff (H := H) hdeg q a₀ b₀).mp hmem
      have hqg : q ∣ gcd (gcd a₀ b₀) c₀ :=
        dvd_gcd (dvd_gcd hqa hqb) hqc
      exact hq.not_isUnit (isUnit_of_dvd_unit hqg hgu)
    obtain ⟨v, hvq, hvlt⟩ :=
      exists_ordAtSpec_lt_of_notMem_span_algebraMap
        (H := H) q a₀ b₀ hq hab₀ne hnotmem
    obtain ⟨s, hcs⟩ := hqc
    have hsne : toPair H s (0 : k[X]) ≠ 0 := by
      rw [Ne, toPair_eq_zero_iff]
      intro hs0
      exact hc₀ne (by rw [hcs, hs0.1, mul_zero])
    have hqnePair : toPair H q (0 : k[X]) ≠ 0 := by
      rw [Ne, toPair_eq_zero_iff]
      exact fun h => hqne h.1
    have hcprod : toPair H c₀ (0 : k[X]) =
        toPair H q (0 : k[X]) * toPair H s (0 : k[X]) := by
      have hm := toPair_mul (H := H) q 0 s 0
      simpa [hcs] using hm.symm
    have hcge : ordAtSpec v q (0 : k[X]) ≤
        ordAtSpec v c₀ (0 : k[X]) := by
      have heq := ordAtSpec_add_of_toPair_mul (H := H) v
        q 0 s 0 c₀ 0 hqnePair hsne hcprod
      have hsnn : 0 ≤ ordAtSpec v s (0 : k[X]) :=
        ordAtSpec_nonneg v s 0 hsne
      rw [heq]
      omega
    have habltc : ordAtSpec v a₀ b₀ <
        ordAtSpec v c₀ (0 : k[X]) := lt_of_lt_of_le hvlt hcge
    have hv_special : v = pointHeightOne' x₁ ∨ v = pointHeightOne' x₂ := by
      by_contra hvnone
      push_neg at hvnone
      have hbound := hzsuppSpec₀ v
      simp only [if_neg hvnone.1, if_neg hvnone.2, add_zero] at hbound
      omega
    rcases hv_special with rfl | rfl
    · left
      have hqmem : algebraMap k[X] (CoordinateRing H) q ∈ pointIdeal x₁ := hvq
      change evalAtPoint x₁ (algebraMap k[X] (CoordinateRing H) q) = 0 at hqmem
      change Polynomial.eval₂ (Polynomial.evalRingHom x₁.val.1) x₁.val.2 (C q) = 0 at hqmem
      simpa [Point.X] using hqmem
    · right
      have hqmem : algebraMap k[X] (CoordinateRing H) q ∈ pointIdeal x₂ := hvq
      change evalAtPoint x₂ (algebraMap k[X] (CoordinateRing H) q) = 0 at hqmem
      change Polynomial.eval₂ (Polynomial.evalRingHom x₂.val.1) x₂.val.2 (C q) = 0 at hqmem
      simpa [Point.X] using hqmem

  /- Every root of `c₀` is one of the two distinguished X-coordinates. -/
  have hroot_location : ∀ {α : k}, c₀.IsRoot α →
      α = x₁.X ∨ α = x₂.X := by
    intro α hα
    have hlin : (X - C α : k[X]).IsRoot α := by simp
    have hlin_irred : Irreducible (X - C α : k[X]) :=
      Polynomial.irreducible_X_sub_C α
    have hlin_dvd : (X - C α : k[X]) ∣ c₀ :=
      Polynomial.dvd_iff_isRoot.mpr hα
    obtain hq1 | hq2 := hq_root_location hlin_irred hlin_dvd
    · left
      have hx : x₁.X - α = 0 := by simpa using hq1
      exact (sub_eq_zero.mp hx).symm
    · right
      have hx : x₂.X - α = 0 := by simpa using hq2
      exact (sub_eq_zero.mp hx).symm

  /- The root-multiplicity estimate is only needed at the two distinguished points.
     The proof uses coprimality at roots plus the conjugate point in the unramified case. -/
  have hcop : IsCoprimeAtRoots a₀ b₀ c₀ := by
    intro α hαc hroots
    rcases hroots with ⟨hαa, hαb⟩
    have hlin_dvd_a₀ : linX α ∣ a₀ := Polynomial.dvd_iff_isRoot.mpr hαa
    have hlin_dvd_b₀ : linX α ∣ b₀ := Polynomial.dvd_iff_isRoot.mpr hαb
    have hlin_dvd_c₀ : linX α ∣ c₀ := Polynomial.dvd_iff_isRoot.mpr hαc
    have hlin_dvd_gcd : linX α ∣ gcd (gcd a₀ b₀) c₀ :=
      dvd_gcd (dvd_gcd hlin_dvd_a₀ hlin_dvd_b₀) hlin_dvd_c₀
    have hlin_unit : IsUnit (linX α : k[X]) :=
      isUnit_of_dvd_unit hlin_dvd_gcd hgu
    have hlin_deg : (linX α : k[X]).natDegree = 1 := by
      unfold linX; compute_degree!
    have hlin_deg0 : (linX α : k[X]).natDegree = 0 :=
      Polynomial.natDegree_eq_zero_of_isUnit hlin_unit
    omega

  /- **Maintained multiplicity bound.** The abandoned `ordAt P c₀ ≤ indicator`
     route was too strong at ramified points.  Here we bound the *root multiplicity*
     directly.  At a ramified point the denominator order is twice the root
     multiplicity and the numerator has order at most one; at an unramified fiber,
     the conjugate pair cannot both contain the numerator because `hcop`. -/
  /- Root-multiplicity estimate at the two distinguished points.
     This is the maintained replacement for the abandoned arbitrary-point order bound. -/
  have hrootMultiplicity_bound (P : H.Point) (hP : P = x₁ ∨ P = x₂)
      (hroot : c₀.IsRoot P.X) :
      (c₀.rootMultiplicity P.X : ℤ) ≤
        (if P = x₁ then 1 else 0) + (if P = x₂ then 1 else 0) := by
    have hbound := hzsuppSpec₀ (pointHeightOne' P)
    rw [← ordAt_eq_ordAtSpec, ← ordAt_eq_ordAtSpec] at hbound
    simp only [pointHeightOne'_eq_iff] at hbound
    have hnotboth : ¬(a₀.IsRoot P.X ∧ b₀.IsRoot P.X) := by
      intro h
      exact hcop P.X hroot h
    by_cases hY : P.Y = 0
    · have hfp : ordAt P H.f (0 : k[X]) = 2 := by
        have hfroot : H.f.IsRoot P.X := by
          have hEq : H.Equation P.X P.Y := P.property
          change P.Y ^ 2 = H.f.eval P.X at hEq
          simpa [hY] using hEq.symm
        have hfmult : H.f.rootMultiplicity P.X ≤ 1 := by
          apply (Polynomial.rootMultiplicity_le_iff hsf.ne_zero P.X 1).2
          intro hsquare
          have hunit : IsUnit (X - C P.X : k[X]) := by
            apply hsf (X - C P.X : k[X])
            show (X - C P.X : k[X]) * (X - C P.X) ∣ H.f
            simpa [pow_two] using hsquare
          have hdeg0 := Polynomial.natDegree_eq_zero_of_isUnit hunit
          have hdeg1 : (X - C P.X : k[X]).natDegree = 1 := by
            compute_degree!
          omega
        have hfpos : 0 < H.f.rootMultiplicity P.X :=
          (Polynomial.rootMultiplicity_pos hsf.ne_zero).mpr hfroot
        have hfone : H.f.rootMultiplicity P.X = 1 := by omega
        rw [ordAt_eq_rootMultiplicity_ramified hsf H.f hsf.ne_zero P.X P
          (pointIdeal_ne_bot P) rfl hY, hfone]
        norm_num
      have hy1 : ordAt P (0 : k[X]) (1 : k[X]) = 1 := by
        have hyne : toPair H (0 : k[X]) (1 : k[X]) ≠ 0 := by
          rw [Ne, toPair_eq_zero_iff]; simp
        have hprod : toPair H H.f (0 : k[X]) =
            toPair H (0 : k[X]) 1 * toPair H (0 : k[X]) 1 := by
          have hm := toPair_mul (H := H) 0 1 0 1
          norm_num at hm
          exact hm.symm
        have heq := ordAtSpec_add_of_toPair_mul (H := H)
          (pointHeightOne' P) 0 1 0 1 H.f 0 hyne hyne hprod
        have hfpSpec : ordAtSpec (pointHeightOne' P) H.f 0 = 2 := by
          simpa only [ordAt_eq_ordAtSpec] using hfp
        rw [hfpSpec] at heq
        have hspec : ordAtSpec (pointHeightOne' P) 0 1 = 1 := by
          omega
        simpa only [ordAt_eq_ordAtSpec] using hspec
      have hnum_le : ordAt P a₀ b₀ ≤ 1 := by
        by_cases ha : a₀.IsRoot P.X
        · have hb : ¬b₀.IsRoot P.X := fun hb => hnotboth ⟨ha, hb⟩
          by_cases ha0 : a₀ = 0
          · subst a₀
            have hbPair : toPair H b₀ (0 : k[X]) ≠ 0 := by
              rw [Ne, toPair_eq_zero_iff]
              intro h
              exact hb (by
                change eval P.X b₀ = 0
                simp [h.1])
            have hba0 : ordAt P b₀ (0 : k[X]) = 0 := by
              apply ordAt_eq_zero_of_notMem
              rw [toPair_mem_pointIdeal_iff]
              simpa using hb
            have h0bPair : toPair H (0 : k[X]) b₀ ≠ 0 := by
              have hm := toPair_mul (H := H) b₀ 0 0 1
              rw [show toPair H (0 : k[X]) b₀ =
                  toPair H b₀ (0 : k[X]) * toPair H (0 : k[X]) 1 by simpa using hm.symm]
              exact mul_ne_zero hbPair (by rw [Ne, toPair_eq_zero_iff]; simp)
            have heq := ordAtSpec_add_of_toPair_mul (H := H)
              (pointHeightOne' P) b₀ 0 0 1 0 b₀ hbPair
              (by rw [Ne, toPair_eq_zero_iff]; simp)
              (by
                have hm := toPair_mul (H := H) b₀ 0 0 1
                simpa using hm.symm)
            have hbY : ordAt P (0 : k[X]) b₀ = 1 := by
              have hy1spec : ordAtSpec (pointHeightOne' P) (0 : k[X]) (1 : k[X]) = 1 := by
                rw [← ordAt_eq_ordAtSpec]
                exact hy1
              rw [← ordAt_eq_ordAtSpec, ← ordAt_eq_ordAtSpec, ← ordAt_eq_ordAtSpec] at heq
              rw [hba0, hy1] at heq
              simpa using heq
            simpa [hbY]
          · have ha0ne : a₀ ≠ 0 := ha0
            have hbPair : toPair H b₀ (0 : k[X]) ≠ 0 := by
              rw [Ne, toPair_eq_zero_iff]
              intro h
              exact hb (by
                change eval P.X b₀ = 0
                simp [h.1])
            have hba0 : ordAt P b₀ (0 : k[X]) = 0 := by
              apply ordAt_eq_zero_of_notMem
              rw [toPair_mem_pointIdeal_iff]
              simpa using hb
            have h0bPair : toPair H (0 : k[X]) b₀ ≠ 0 := by
              have hm := toPair_mul (H := H) b₀ 0 0 1
              rw [show toPair H (0 : k[X]) b₀ =
                  toPair H b₀ (0 : k[X]) * toPair H (0 : k[X]) 1 by simpa using hm.symm]
              exact mul_ne_zero hbPair (by rw [Ne, toPair_eq_zero_iff]; simp)
            have hbY : ordAt P (0 : k[X]) b₀ = 1 := by
              have heq := ordAtSpec_add_of_toPair_mul (H := H)
                (pointHeightOne' P) b₀ 0 0 1 0 b₀ hbPair
                (by rw [Ne, toPair_eq_zero_iff]; simp)
                (by
                  have hm := toPair_mul (H := H) b₀ 0 0 1
                  simpa using hm.symm)
              have hy1spec : ordAtSpec (pointHeightOne' P) (0 : k[X]) (1 : k[X]) = 1 := by
                rw [← ordAt_eq_ordAtSpec]
                exact hy1
              rw [← ordAt_eq_ordAtSpec, ← ordAt_eq_ordAtSpec, ← ordAt_eq_ordAtSpec] at heq
              rw [hba0, hy1] at heq
              simpa using heq
            have haord : 2 ≤ ordAt P a₀ (0 : k[X]) := by
              rw [ordAt_eq_rootMultiplicity_ramified hsf a₀ ha0ne P.X P
                (pointIdeal_ne_bot P) rfl hY]
              have hpos : 0 < a₀.rootMultiplicity P.X :=
                (Polynomial.rootMultiplicity_pos ha0ne).mpr ha
              omega
            have hlt : ordAt P (0 : k[X]) b₀ < ordAt P a₀ (0 : k[X]) := by
              rw [hbY]
              omega
            have hsum := ordAtSpec_add_eq_of_lt (H := H)
              (pointHeightOne' P) (0 : k[X]) b₀ a₀ 0 h0bPair
              (by rw [Ne, toPair_eq_zero_iff]
                  exact fun h => ha0ne h.1)
              (by rw [← ordAt_eq_ordAtSpec, ← ordAt_eq_ordAtSpec]; exact hlt)
            have hsum' : ordAt P a₀ b₀ = ordAt P (0 : k[X]) b₀ := by
              simpa only [← ordAt_eq_ordAtSpec, zero_add, add_zero] using hsum
            rw [hsum', hbY]
        · have haord : ordAt P a₀ (0 : k[X]) = 0 := by
            apply ordAt_eq_zero_of_notMem
            rw [toPair_mem_pointIdeal_iff]
            simpa using ha
          by_cases hb0 : b₀ = 0
          · subst b₀
            simpa [haord]
          · have hbPair : toPair H b₀ (0 : k[X]) ≠ 0 := by
              rw [Ne, toPair_eq_zero_iff]
              exact fun h => hb0 h.1
            have hbnat : 0 ≤ ordAt P b₀ (0 : k[X]) :=
              ordAt_nonneg P b₀ 0 hbPair (pointIdeal_ne_bot P)
            have hyY : 1 ≤ ordAt P (0 : k[X]) b₀ := by
              have heq := ordAtSpec_add_of_toPair_mul (H := H)
                (pointHeightOne' P) b₀ 0 0 1 0 b₀ hbPair
                (by rw [Ne, toPair_eq_zero_iff]; simp)
                (by
                  have hm := toPair_mul (H := H) b₀ 0 0 1
                  simpa using hm.symm)
              have hy1spec : ordAtSpec (pointHeightOne' P) (0 : k[X]) (1 : k[X]) = 1 := by
                rw [← ordAt_eq_ordAtSpec]
                exact hy1
              rw [← ordAt_eq_ordAtSpec, ← ordAt_eq_ordAtSpec] at heq
              rw [hy1spec] at heq
              omega
            have ha0ne : a₀ ≠ 0 := by
              intro ha0
              apply ha
              simpa [ha0]
            have haPair : toPair H a₀ (0 : k[X]) ≠ 0 := by
              rw [Ne, toPair_eq_zero_iff]
              exact fun h => ha0ne h.1
            have hlt : ordAt P a₀ 0 < ordAt P 0 b₀ := by omega
            have hsum := ordAtSpec_add_eq_of_lt (H := H)
              (pointHeightOne' P) a₀ 0 0 b₀ haPair
              (by
                have hm := toPair_mul (H := H) b₀ 0 0 1
                rw [show toPair H (0 : k[X]) b₀ =
                    toPair H b₀ (0 : k[X]) * toPair H (0 : k[X]) 1 by simpa using hm.symm]
                exact mul_ne_zero hbPair (by rw [Ne, toPair_eq_zero_iff]; simp))
              (by rw [← ordAt_eq_ordAtSpec, ← ordAt_eq_ordAtSpec]; exact hlt)
            have hsum' : ordAt P a₀ b₀ = ordAt P a₀ (0 : k[X]) := by
              simpa only [← ordAt_eq_ordAtSpec, zero_add, add_zero] using hsum
            rw [hsum', haord]
            omega
      have hc_ord := ordAt_eq_rootMultiplicity_ramified hsf c₀ hc₀ne P.X P
        (pointIdeal_ne_bot P) rfl hY
      rw [hc_ord] at hbound
      omega
    · have hordcP := ordAt_eq_rootMultiplicity_unramified hchar c₀ hc₀ne P.X P
        (pointIdeal_ne_bot P) rfl hY
      let Q : H.Point := Point.iota P
      have hQX : Q.X = P.X := by simp [Q]
      have hQYne : Q.Y ≠ 0 := by
        rw [show Q.Y = -P.Y by simp [Q]]
        exact neg_ne_zero.mpr hY
      have hQneP : Q ≠ P := Point.iota_ne_self_of_Y_ne_zero hchar hY
      have hQroot : c₀.IsRoot Q.X := by simpa [hQX] using hroot
      have hordcQ := ordAt_eq_rootMultiplicity_unramified hchar c₀ hc₀ne P.X Q
        (pointIdeal_ne_bot Q) hQX hQYne
      by_cases hPzero : ordAt P a₀ b₀ = 0
      · rw [hPzero, hordcP] at hbound
        omega
      · have hPmem : toPair H a₀ b₀ ∈ pointIdeal P := by
          by_contra hnot
          have hzero := ordAt_eq_zero_of_notMem P a₀ b₀ hnot
          exact hPzero hzero
        have hQnotmem : toPair H a₀ b₀ ∉ pointIdeal Q := by
          intro hQmem
          rw [toPair_mem_pointIdeal_iff] at hPmem hQmem
          have hplus : a₀.eval P.X + b₀.eval P.X * P.Y = 0 := by
            simpa using hPmem
          have hminus : a₀.eval P.X - b₀.eval P.X * P.Y = 0 := by
            simpa [hQX, show Q.Y = -P.Y by simp [Q], sub_eq_add_neg, mul_neg] using hQmem
          have h2a : (2 : k) * a₀.eval P.X = 0 := by
            linear_combination hplus + hminus
          have haeval : a₀.eval P.X = 0 := by
            rcases mul_eq_zero.mp h2a with h | h
            · exact (hchar h).elim
            · exact h
          have h2b : (2 : k) * (b₀.eval P.X * P.Y) = 0 := by
            linear_combination hplus - hminus
          have hbY : b₀.eval P.X * P.Y = 0 := by
            rcases mul_eq_zero.mp h2b with h | h
            · exact (hchar h).elim
            · exact h
          have hbeval : b₀.eval P.X = 0 :=
            (mul_eq_zero.mp hbY).resolve_right hY
          exact hnotboth ⟨by simpa using haeval, by simpa using hbeval⟩
        have hQzero : ordAt Q a₀ b₀ = 0 :=
          ordAt_eq_zero_of_notMem Q a₀ b₀ hQnotmem
        have hQbound := hzsuppSpec₀ (pointHeightOne' Q)
        rw [← ordAt_eq_ordAtSpec, ← ordAt_eq_ordAtSpec] at hQbound
        simp only [pointHeightOne'_eq_iff] at hQbound
        have hQallow : (if Q = x₁ then 1 else 0) + (if Q = x₂ then 1 else 0) ≤ 1 := by
          rcases hP with rfl | rfl
          · by_cases hQx₂ : Q = x₂
            · have hx₂P : x₂ ≠ P := by simpa [hQx₂] using hQneP
              simp [hQx₂, hx₂P]
            · simp [hQx₂, hQneP]
          · by_cases hQx₁ : Q = x₁
            · have hx₁P : x₁ ≠ P := by simpa [hQx₁] using hQneP
              simp [hQx₁, hx₁P]
            · simp [hQx₁, hQneP]
        rw [hQzero, hordcQ] at hQbound
        have hQmul : (c₀.rootMultiplicity P.X : ℤ) ≤
            (if Q = x₁ then 1 else 0) + (if Q = x₂ then 1 else 0) := by
          omega
        have hQleP : ((if Q = x₁ then 1 else 0) + if Q = x₂ then 1 else 0 : ℤ) ≤
            (if P = x₁ then 1 else 0) + if P = x₂ then 1 else 0 := by
          rcases hP with rfl | rfl
          · by_cases hQx₂ : Q = x₂
            · simp_all [hQneP]
              positivity
            · simp_all [hQneP]
          · by_cases hQx₁ : Q = x₁
            · simp_all [hQneP]
              positivity
            · simp_all [hQneP]
        omega

  /- Every irreducible factor of `c₀` is linear, hence `c₀` splits over `k`. -/
  have hc₀split : c₀.Splits := by
    rw [Polynomial.splits_iff_splits]
    right
    intro q hq hqc
    obtain hq1 | hq2 := hq_root_location hq hqc
    · exact Polynomial.degree_eq_one_of_irreducible_of_root hq hq1
    · exact Polynomial.degree_eq_one_of_irreducible_of_root hq hq2

  /- The full root multiset has at most the two allowed roots, with
  multiplicities bounded by the two pole allowances. -/
  have hroots_le : c₀.roots ≤ ({x₁.X, x₂.X} : Multiset k) := by
    rw [Multiset.le_iff_count]
    intro α
    rw [Polynomial.count_roots]
    by_cases hroot : c₀.IsRoot α
    · rcases hroot_location hroot with h1 | h2
      · subst α
        have hm := hrootMultiplicity_bound x₁ (Or.inl rfl) hroot
        have hm' : c₀.rootMultiplicity x₁.X ≤
            (if x₁ = x₁ then 1 else 0) + (if x₁ = x₂ then 1 else 0) := by
          exact_mod_cast hm
        by_cases hXX : x₁.X = x₂.X
        · have hm2 : c₀.rootMultiplicity x₁.X ≤ 2 := by omega
          simpa [hXX, Multiset.count_cons, Multiset.count_singleton] using hm2
        · have hpoint : x₁ ≠ x₂ := by
            intro hp
            exact hXX (congrArg (fun p : H.Point => p.X) hp)
          simpa [hXX, hpoint, Multiset.count_cons, Multiset.count_singleton] using hm'
      · subst α
        have hm := hrootMultiplicity_bound x₂ (Or.inr rfl) hroot
        have hm' : c₀.rootMultiplicity x₂.X ≤
            (if x₂ = x₁ then 1 else 0) + (if x₂ = x₂ then 1 else 0) := by
          exact_mod_cast hm
        by_cases hXX : x₂.X = x₁.X
        · have hm2 : c₀.rootMultiplicity x₂.X ≤ 2 := by omega
          simpa [hXX, Multiset.count_cons, Multiset.count_singleton] using hm2
        · have hpoint : x₂ ≠ x₁ := by
            intro hp
            exact hXX (congrArg (fun p : H.Point => p.X) hp)
          simpa [hXX, hpoint, Multiset.count_cons, Multiset.count_singleton] using hm'
    · have hm0 : c₀.rootMultiplicity α = 0 := by
        by_contra hm
        have hmpos : 0 < c₀.rootMultiplicity α := Nat.pos_of_ne_zero hm
        exact hroot ((Polynomial.rootMultiplicity_pos hc₀ne :
          0 < c₀.rootMultiplicity α ↔ c₀.IsRoot α).mp hmpos)
      simp [hm0, hroot]

  calc
    c₀.natDegree = c₀.roots.card := hc₀split.natDegree_eq_card_roots
    _ ≤ ({x₁.X, x₂.X} : Multiset k).card := Multiset.card_le_card hroots_le
    _ = 2 := by simp

/-- The residue extension `L := AdjoinRoot q`, for irreducible `q : k[X]`. -/
abbrev SplitBaseField (q : k[X]) : Type _ := AdjoinRoot q

/-- `M := L[T]/(T² - (H.f mod q))`, the "square-root-of-`f`-adjoined" ring over `L`. -/
abbrev SqrtExtQ (q : k[X]) : Type _ :=
  AdjoinRoot (X ^ 2 - C (AdjoinRoot.mk q H.f) : (SplitBaseField q)[X])

/-- The chosen square root of `H.f mod q` living in `SqrtExtQ q`. -/
def sqrtExtQRoot (q : k[X]) : SqrtExtQ (H := H) q :=
  AdjoinRoot.root (X ^ 2 - C (AdjoinRoot.mk q H.f) : (SplitBaseField q)[X])

theorem sqrtExtQRoot_sq (q : k[X]) :
    sqrtExtQRoot (H := H) q ^ 2 =
      algebraMap (SplitBaseField q) (SqrtExtQ (H := H) q) (AdjoinRoot.mk q H.f) := by
  have h := AdjoinRoot.eval₂_root
    (X ^ 2 - C (AdjoinRoot.mk q H.f) : (SplitBaseField q)[X])
  rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] at h
  exact sub_eq_zero.mp h

/-- `SqrtExtQ q` as a `k`-algebra, via `L := AdjoinRoot q` as an intermediate step. The
`k`-algebra structure on `SqrtExtQ q = AdjoinRoot (T² - C (mk q H.f))` comes from
`AdjoinRoot`'s own `Algebra (SplitBaseField q) _` instance composed with `Algebra k
(SplitBaseField q)`; `Algebra.compHom`-style composition, matching the `IsScalarTower.
of_algebraMap_eq (fun _ => rfl)` idiom this project already uses elsewhere (e.g.
`GlobalDegreeBoundSpec.lean`, `LCanonicalElementary.lean`) rather than trusting
`infer_instance` to find the right diamond-free path through a two-level `AdjoinRoot`
tower. -/
instance instScalarTowerSqrtExtQ (q : k[X]) :
    IsScalarTower k (SplitBaseField q) (SqrtExtQ (H := H) q) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

/-- **The ring hom `CoordinateRing H →+* SqrtExtQ q`, sending `x ↦ root q` (as an
element of `L ≤ SqrtExtQ q`), `y ↦ sqrtExtQRoot q`.** Well-defined for any irreducible
`q` — no need for `q ∤ H.f` at this stage (that only matters for whether the *target*
happens to be a field, not for well-definedness of the hom itself). -/
def evalAtSplitFiber (q : k[X]) :
    CoordinateRing H →+* SqrtExtQ (H := H) q :=
  AdjoinRoot.lift
    ((algebraMap (SplitBaseField q) (SqrtExtQ (H := H) q)).comp (AdjoinRoot.mk q))
    (sqrtExtQRoot (H := H) q)
    (by
      rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, RingHom.comp_apply, sqrtExtQRoot_sq,
        sub_self])

/-! ### The ramified closed point at an arbitrary-degree irreducible `q ∣ H.f`.

Generalizes the existing rational-`α`-only ramified point (`LPairFinrankOneOrdAtFrac.
lean`'s `Point.mk α 0`-style construction) to arbitrary-degree irreducible `q`, via the
same `AdjoinRoot`-lift pattern `NonSquareFiberPoint.lean` uses for the non-square-fiber
point — but targeting `K := AdjoinRoot q` (a field, `q` irreducible) with `y ↦ 0`
directly, no square root needed: at a ramified fiber `y² ≡ H.f ≡ 0 (mod q)` forces
`y ≡ 0`, so `0` genuinely is *the* root of `X² - (H.f mod q)` in `AdjoinRoot q`. -/

/-- **The ring hom `CoordinateRing H →+* AdjoinRoot q`, sending `x ↦ AdjoinRoot.root
q`, `y ↦ 0`.** Well-defined exactly when `q ∣ H.f`: the side condition `eval₂ _ 0
(X² - C H.f) = 0` unfolds to `0 - (H.f mod q) = 0`, i.e. `H.f ≡ 0 (mod q)` in
`AdjoinRoot q`, which is `AdjoinRoot.mk_eq_zero.mpr hqf`. -/
def evalAtRamifiedFiber (q : k[X]) (hqf : q ∣ H.f) :
    CoordinateRing H →+* AdjoinRoot q :=
  AdjoinRoot.lift (AdjoinRoot.mk q) 0
    (by
      rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, zero_pow (two_ne_zero), zero_sub,
        neg_eq_zero]
      exact (AdjoinRoot.mk_eq_zero).mpr hqf)

/-- The candidate prime ideal: kernel of `evalAtRamifiedFiber`. -/
def ramifiedFiberIdeal (q : k[X]) (hqf : q ∣ H.f) : Ideal (CoordinateRing H) :=
  RingHom.ker (evalAtRamifiedFiber (H := H) q hqf)

/-- `evalAtRamifiedFiber q hqf` is surjective onto `AdjoinRoot q`: its range is a
`k`-subalgebra containing `k` (base ring hom) and `AdjoinRoot.root q` (image of `x`),
hence all of `AdjoinRoot q` (`AdjoinRoot.adjoinRoot_eq_top`). Mirrors
`evalAtNonSquareFiber_surjective` exactly, with the roles of `x`/`y` swapped (here `x`
generates, `y` is sent to the already-in-the-base-ring `0`). -/
theorem evalAtRamifiedFiber_surjective (q : k[X]) (hqf : q ∣ H.f) :
    Function.Surjective (evalAtRamifiedFiber (H := H) q hqf) := by
  have hroot_mem : AdjoinRoot.root q ∈ Set.range (evalAtRamifiedFiber (H := H) q hqf) := by
    refine ⟨algebraMap k[X] (CoordinateRing H) X, ?_⟩
    change
      (AdjoinRoot.lift (AdjoinRoot.mk q) 0 _)
        (AdjoinRoot.of (X ^ 2 - C H.f) X) = AdjoinRoot.root q
    rw [AdjoinRoot.lift_of]
    rfl
  have hbase_mem : ∀ a : k,
      algebraMap k (AdjoinRoot q) a ∈ Set.range (evalAtRamifiedFiber (H := H) q hqf) := by
    intro a
    refine ⟨algebraMap k[X] (CoordinateRing H) (C a), ?_⟩
    change
      (AdjoinRoot.lift (AdjoinRoot.mk q) 0 _)
        (AdjoinRoot.of (X ^ 2 - C H.f) (C a)) = algebraMap k (AdjoinRoot q) a
    rw [AdjoinRoot.lift_of]
    rw [AdjoinRoot.algebraMap_eq' k q]
    rfl
  set S : Subalgebra k (AdjoinRoot q) :=
    { carrier := Set.range (evalAtRamifiedFiber (H := H) q hqf)
      mul_mem' := by
        rintro _ _ ⟨p, rfl⟩ ⟨r, rfl⟩
        exact ⟨p * r, map_mul (evalAtRamifiedFiber (H := H) q hqf) p r⟩
      add_mem' := by
        rintro _ _ ⟨p, rfl⟩ ⟨r, rfl⟩
        exact ⟨p + r, map_add (evalAtRamifiedFiber (H := H) q hqf) p r⟩
      algebraMap_mem' := hbase_mem } with hS_def
  have hroot_mem_S : AdjoinRoot.root q ∈ S := by
    rw [hS_def]; exact hroot_mem
  have hadjoin_le : Algebra.adjoin k ({AdjoinRoot.root q} : Set (AdjoinRoot q)) ≤ S :=
    Algebra.adjoin_le (by simpa using hroot_mem_S)
  rw [AdjoinRoot.adjoinRoot_eq_top] at hadjoin_le
  intro s
  exact hadjoin_le (Algebra.mem_top)

/-- **`ramifiedFiberIdeal q hqf` is maximal.** Kernel of a surjective ring hom onto
the field `AdjoinRoot q` (`q` irreducible). -/
theorem ramifiedFiberIdeal_isMaximal (q : k[X]) (hq : Irreducible q) (hqf : q ∣ H.f) :
    (ramifiedFiberIdeal (H := H) q hqf).IsMaximal := by
  haveI : Fact (Irreducible q) := ⟨hq⟩
  exact RingHom.ker_isMaximal_of_surjective (evalAtRamifiedFiber (H := H) q hqf)
    (evalAtRamifiedFiber_surjective (H := H) q hqf)

/-- **`ramifiedFiberIdeal q hqf ≠ ⊥`.** -/
theorem ramifiedFiberIdeal_ne_bot (q : k[X]) (hq : Irreducible q) (hqf : q ∣ H.f) :
    (ramifiedFiberIdeal (H := H) q hqf) ≠ ⊥ :=
  Ring.ne_bot_of_isMaximal_of_not_isField
    (ramifiedFiberIdeal_isMaximal (H := H) q hq hqf) coordinateRing_not_isField

/-- `evalAtRamifiedFiber q hqf` applied to `toPair H A B`, in closed form. -/
theorem evalAtRamifiedFiber_toPair (q : k[X]) (hqf : q ∣ H.f) (A B : k[X]) :
    evalAtRamifiedFiber (H := H) q hqf (toPair H A B) = AdjoinRoot.mk q A := by
  have hA : evalAtRamifiedFiber (H := H) q hqf (algebraMap k[X] (CoordinateRing H) A) =
      AdjoinRoot.mk q A := by
    change (AdjoinRoot.lift (AdjoinRoot.mk q) 0 _)
        (AdjoinRoot.of (X ^ 2 - C H.f) A) = AdjoinRoot.mk q A
    rw [AdjoinRoot.lift_of]
  have hB : evalAtRamifiedFiber (H := H) q hqf (algebraMap k[X] (CoordinateRing H) B) =
      AdjoinRoot.mk q B := by
    change (AdjoinRoot.lift (AdjoinRoot.mk q) 0 _)
        (AdjoinRoot.of (X ^ 2 - C H.f) B) = AdjoinRoot.mk q B
    rw [AdjoinRoot.lift_of]
  have hy : evalAtRamifiedFiber (H := H) q hqf (y H) = 0 := AdjoinRoot.lift_root _
  unfold HyperellipticPolynomial.toPair
  rw [map_add, map_mul, hA, hB, hy, mul_zero, add_zero]

/-- **Membership characterization for `ramifiedFiberIdeal`.** `toPair H A B ∈
ramifiedFiberIdeal q hqf ↔ q ∣ A` (the `y`-term vanishes automatically). -/
theorem toPair_mem_ramifiedFiberIdeal_iff (q : k[X]) (hqf : q ∣ H.f) (A B : k[X]) :
    toPair H A B ∈ ramifiedFiberIdeal (H := H) q hqf ↔ q ∣ A := by
  rw [ramifiedFiberIdeal, RingHom.mem_ker, evalAtRamifiedFiber_toPair,
    AdjoinRoot.mk_eq_zero]

/-- **The ramified closed point itself**, as a `HeightOneSpectrum` element, for any
irreducible `q ∣ H.f` (not just linear `q`). -/
def ramifiedFiberHeightOne [IsDedekindDomain (CoordinateRing H)]
    (q : k[X]) (hq : Irreducible q) (hqf : q ∣ H.f) :
    IsDedekindDomain.HeightOneSpectrum (CoordinateRing H) where
  asIdeal := ramifiedFiberIdeal (H := H) q hqf
  isPrime := (ramifiedFiberIdeal_isMaximal (H := H) q hq hqf).isPrime
  ne_bot := ramifiedFiberIdeal_ne_bot (H := H) q hq hqf

/-- **Residue degree of the ramified closed point equals `q.natDegree`.** Via
`RingHom.quotientKerEquivOfSurjective` and `AdjoinRoot`'s power basis (`q.natDegree`,
same computation as `finrank_sqrtExt` but at general degree, using
`AdjoinRoot.powerBasis hq.ne_zero` directly against `q` itself rather than
`X² - C c`: `PowerBasis.finrank` gives `Module.finrank k (AdjoinRoot q) =
(AdjoinRoot.powerBasis hq.ne_zero).dim`, and `AdjoinRoot.powerBasis_dim` identifies
that `dim` with `q.natDegree`). -/
theorem residueDeg_ramifiedFiberHeightOne
    (q : k[X]) (hq : Irreducible q) (hqf : q ∣ H.f) :
    residueDeg (ramifiedFiberHeightOne (H := H) q hq hqf) = q.natDegree := by
  unfold residueDeg ramifiedFiberHeightOne
  simp only
  set hequiv : (CoordinateRing H ⧸ RingHom.ker (evalAtRamifiedFiber (H := H) q hqf)) ≃+*
      AdjoinRoot q :=
    RingHom.quotientKerEquivOfSurjective (evalAtRamifiedFiber_surjective (H := H) q hqf)
    with hequiv_def
  have hlinequiv : Module.finrank k (CoordinateRing H ⧸ ramifiedFiberIdeal (H := H) q hqf) =
      Module.finrank k (AdjoinRoot q) := by
    apply LinearEquiv.finrank_eq
    exact hequiv.toAddEquiv.toLinearEquiv (fun r x => by
      show hequiv (r • x) = r • hequiv x
      rw [Algebra.smul_def, Algebra.smul_def]
      rw [map_mul]
      congr 1
      have hlhs : algebraMap k (CoordinateRing H) r =
          AdjoinRoot.mk ((X : (k[X])[X]) ^ 2 - C H.f) (C (C r)) := rfl
      change
        hequiv (Ideal.Quotient.mk (RingHom.ker (evalAtRamifiedFiber (H := H) q hqf))
          (algebraMap k (CoordinateRing H) r)) =
          (algebraMap k (AdjoinRoot q)) r
      rw [hlhs, hequiv_def]
      rw [RingHom.quotientKerEquivOfSurjective_apply_mk]
      have hrval : evalAtRamifiedFiber (H := H) q hqf
          (AdjoinRoot.mk ((X : (k[X])[X]) ^ 2 - C H.f) (C (C r))) = AdjoinRoot.mk q (C r) := by
        change (AdjoinRoot.lift (AdjoinRoot.mk q) 0 _)
            (AdjoinRoot.of ((X : (k[X])[X]) ^ 2 - C H.f) (C r)) = AdjoinRoot.mk q (C r)
        rw [AdjoinRoot.lift_of]
      rw [hrval]
      simp [AdjoinRoot.algebraMap_eq, AdjoinRoot.mk_C])
  rw [hlinequiv]
  rw [(AdjoinRoot.powerBasis hq.ne_zero).finrank]
  exact AdjoinRoot.powerBasis_dim hq.ne_zero

/-- **The ramified closed point is never a rational point when `q.natDegree ≥ 2`.**
Residue degree mismatch. (When `q.natDegree = 1`, the existing rational-point
machinery already handles it — this general construction is only needed for `q.
natDegree ≥ 2`, but the statement holds unconditionally whenever `q.natDegree ≠ 1`.) -/
theorem ramifiedFiberHeightOne_ne_pointHeightOne'
    (q : k[X]) (hq : Irreducible q) (hqf : q ∣ H.f) (hqdeg : q.natDegree ≠ 1)
    (P : H.Point) :
    ramifiedFiberHeightOne (H := H) q hq hqf ≠ pointHeightOne' P := by
  intro h
  have h1 := residueDeg_ramifiedFiberHeightOne (H := H) q hq hqf
  have h2 := residueDeg_pointHeightOne' (H := H) P
  rw [h] at h1
  omega

/-! ### Degree-≥2 bad-factor case: contradiction from `q ∣ gcd(pairNorm a₀ b₀, c₀)`.

Two sub-cases: `q ∣ H.f` (ramified — use `ramifiedFiberHeightOne` above) or `q ∤ H.f`
(split/inert — use the already-proved `heightOneSpectrum_of_irreducible_ne_
pointIdeal`, going-up along the integral extension `k[X] → CoordinateRing H`, no
explicit square root needed). **Status: genuinely blocked, not yet closed — see
honest note below, do not paper over with a `sorry` dressed as a `have`.**

**Where this actually breaks, checked by hand (not guessed):** membership alone
(`toPair H a₀ b₀ ∈ v.asIdeal`, from `q ∣ a₀`) only gives `ordAtSpec v a₀ b₀ ≥ 1`, not
`= 0`. Feeding that into `hzsuppSpec₀ v` with `v ∉ {x₁,x₂}` (indicator `0`) yields
`ordAtSpec v a₀ b₀ ≥ ordAtSpec v c₀ 0 ≥ 1` — both sides positive, no contradiction.
Closing this needs the *exact* order of `a₀ + b₀y` at `v`, which needs `v`'s
ramification index `e_v` over `q` — a genuine local computation that exists in this
codebase only for **linear** `q` (`ordAt_linX_pow_ramified` and its unramified
sibling in `LPairFinrankOneOrdAtFrac.lean`, built via induction on the exponent
against the *explicit* rational point). Generalizing that induction from a rational
point `Q : H.Point` to the abstract `ramifiedFiberHeightOne`/going-up `v` above a
degree-`≥2` `q` is genuinely new work, comparable in size to the existing linear
machinery — not a bookkeeping gap. Also checked and ruled out: substituting the
already-proved *global* residue-degree-weighted sum identity
(`natDegree_pairNorm_eq_sum_residueDeg_ordAtSpec`,
`natDegree_pairNorm_le_natDegree_pairNorm_add_two_of_isPoleBoundedAtPairSpec`) in
place of a pointwise argument is circular: it yields `2·deg c₀ ≤ deg(pairNorm a₀ b₀) +
2` on one side and `deg(pairNorm a₀ b₀) ≤ 2·deg c₀` (from `hinf₀` via
`natDegree_pairNorm_eq_neg_ordInfOfPair`) on the other, which combine to the vacuous
`2·deg c₀ ≤ 2·deg c₀`, not a bound on either quantity — verified symbolically, not
just asserted.

**What's solid and reusable regardless of how this resolves:**
`notDvd_snd_of_dvd_gcd_pairNorm_of_gcdUnit` (pure algebra, no sorry) and the full
`ramifiedFiberHeightOne` construction above (ideal, maximality, `≠ ⊥`, residue degree
`= q.natDegree`, membership criterion — all no sorry, general-degree `q ∣ H.f`,
genuinely reusable once the ramification-index computation is built). The split-case
(`q ∤ H.f`) mirror of this — via `heightOneSpectrum_of_irreducible_ne_pointIdeal`'s
already-proved going-up lemma (`RiemannRochGenus2.lean`) instead of a fresh
`SqrtExt`/`AdjoinRoot q` construction, no square root needed there either — hits the
same exact-order wall and was not attempted for that reason. -/

/-! ## §3e. The actual fix (ChatGPT consultation, second round): bypass
`c₀.natDegree ≤ 2` entirely.

**The degree-count route is genuinely circular, confirmed by direct calculation, not
just difficult.** Writing `D := c₀.natDegree`, `N := deg(pairNorm a₀ b₀)`: the
closed-point pointwise bound (`hzsuppSpec`/`hzsuppSpec₀`) gives `2D ≤ N + 2` (summing
the termwise bound `ordAtSpec v c₀ 0 ≤ ordAtSpec v a₀ b₀ + e_v` against the global
norm identity, `e_v` contributing at most `2` total at `x₁, x₂`); the infinity bound
(`hinf₀`) gives `N ≤ 2D`. Together: `0 ≤ 2D - N ≤ 2` — an absolute constraint on the
*gap* `2D - N`, not on `D` itself. No rearrangement of these two inequalities alone
produces `D ≤ 2`; an arbitrarily large `D` (with `N` tracking `2D` within slack `2`)
is consistent with both. This matches the file's own honest note above (§3d) finding
the same wall from the per-factor pole-mass route — same underlying obstruction,
confirmed twice independently, so not an artifact of one particular derivation.

**Why this doesn't happen in the `IsAlgClosed` proof.** That proof never uses `hinf`
for this step at all — it gets `deg c₀ ≤ 2` directly from `c₀` splitting completely
over `k` (`IsAlgClosed.splits`), a strictly stronger structural fact with no analogue
here. Trying to recover an equally strong conclusion from strictly weaker
(closed-point pointwise + infinity) hypotheses via degree-counting alone cannot work.

**The actual fix: the hypotheses already say something stronger than a degree bound.**
`hzsuppSpec₀` and `hinf₀` together say exactly that `F := (a₀+b₀y)/c₀`'s divisor is
`≥ -[x₁] - [x₂]` (pole order `≤ 1` at `x₁, x₂`, no pole anywhere else, including at
infinity) — i.e. `F ∈ L(x₁+x₂)` in Riemann–Roch language. For a genus-2 hyperelliptic
curve with `x₂ ≠ ι(x₁)` (the hyperelliptic involution — exactly this theorem's `hne`
hypothesis), `ℓ(x₁+x₂) = 1`, so `F` is constant. This is precisely
`isConstantFraction_of_ordAt_eq` (`LPairFinrankOne.lean`) applied to `(a₀,b₀,c₀,0)` —
except that theorem is stated for `ordAt`/`H.Point` equality, gated by `hspecAB`/
`hspecA'B'` hypotheses forcing every relevant prime to be rational (the
`IsAlgClosed`-era assumption, inherited implicitly since `LPairFinrankOne.lean` proves
this using only rational data). We don't have (or want) `ordAt`-equality at rational
points alone; we have `ordAtSpec`-inequalities at every closed point directly.

**The needed generalization turns out to be *simpler* than the original, not harder.**
`span_eq_of_ordAt_eq`'s only use of `hspecAB`/`hspecA'B'` is to translate a general
`v : HeightOneSpectrum`'s `Associates.count` back down to `ordAt` at a rational point
(via `v.asIdeal = pointIdeal P`), because its hypothesis `hordeq` is only stated for
`P : H.Point`. Restated directly over `HeightOneSpectrum` (`ordAtSpec`-equality
everywhere, which is what we can actually derive from `hzsuppSpec₀`+`hinf₀` once
`b₀ = 0` is NOT yet assumed — see below), `hspecAB`/`hspecA'B'` become unnecessary:
`ordAtSpec_eq_count` (`GlobalDegreeBoundSpec.lean`) already relates `ordAtSpec v A B`
to `Associates.count` at *every* `v`, uniformly, no rationality restriction. -/

/-- **Closed-point-native analogue of `span_eq_of_ordAt_eq`.** Strictly simpler than
the original: no `hspecAB`/`hspecA'B'` bridging hypotheses needed, since `ordAtSpec`
already ranges over every closed point directly. Proof is a direct transcription of
`span_eq_of_ordAt_eq`'s `Associates.count`/`normalizedFactors` argument, with the
`by_cases hPex : ∃ P, v.asIdeal = pointIdeal P` case split removed (both counts are
compared via `hordeqSpec v` unconditionally, since `ordAtSpec_eq_count` applies at
every `v`, not just rational ones). -/
theorem span_eq_of_ordAtSpec_eq [IsDedekindDomain (CoordinateRing H)] (A B A' B' : k[X])
    (hABz : toPair H A B ≠ 0) (hA'B'z : toPair H A' B' ≠ 0)
    (hordeqSpec : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      ordAtSpec v A B = ordAtSpec v A' B') :
    Ideal.span ({toPair H A B} : Set (CoordinateRing H)) =
      Ideal.span ({toPair H A' B'} : Set (CoordinateRing H)) := by
  classical
  set I : Ideal (CoordinateRing H) := Ideal.span ({toPair H A B} : Set (CoordinateRing H))
    with hI_def
  set I' : Ideal (CoordinateRing H) := Ideal.span ({toPair H A' B'} : Set (CoordinateRing H))
    with hI'_def
  have hIne : I ≠ 0 := by
    rw [hI_def, Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hABz
  have hI'ne : I' ≠ 0 := by
    rw [hI'_def, Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hA'B'z
  have hIbot : I ≠ ⊥ := by rw [Ideal.zero_eq_bot] at hIne; exact hIne
  have hI'bot : I' ≠ ⊥ := by rw [Ideal.zero_eq_bot] at hI'ne; exact hI'ne
  have hcount_eq : ∀ J : Ideal (CoordinateRing H),
      Multiset.count J (UniqueFactorizationMonoid.normalizedFactors I) =
        Multiset.count J (UniqueFactorizationMonoid.normalizedFactors I') := by
    intro J
    by_cases hJmem : J ∈ UniqueFactorizationMonoid.normalizedFactors I ∨
        J ∈ UniqueFactorizationMonoid.normalizedFactors I'
    · have hJprime : J.IsPrime ∧ J ≠ ⊥ := by
        rcases hJmem with hJ | hJ
        · exact ⟨((Ideal.mem_normalizedFactors_iff hIbot).mp hJ).1, by
            intro hJ0; rw [hJ0] at hJ
            exact UniqueFactorizationMonoid.zero_notMem_normalizedFactors I hJ⟩
        · exact ⟨((Ideal.mem_normalizedFactors_iff hI'bot).mp hJ).1, by
            intro hJ0; rw [hJ0] at hJ
            exact UniqueFactorizationMonoid.zero_notMem_normalizedFactors I' hJ⟩
      set v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H) :=
        ⟨J, hJprime.1, hJprime.2⟩ with hv_def
      have hvJ : v.asIdeal = J := rfl
      have hcAB : (Associates.mk v.asIdeal).count (Associates.mk I).factors =
          Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors I) :=
        Ideal.count_associates_factors_eq hIne v.isPrime v.ne_bot
      have hcA'B' : (Associates.mk v.asIdeal).count (Associates.mk I').factors =
          Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors I') :=
        Ideal.count_associates_factors_eq hI'ne v.isPrime v.ne_bot
      rw [hvJ] at hcAB hcA'B'
      rw [← hcAB, ← hcA'B']
      -- **The simplification versus `span_eq_of_ordAt_eq`**: no case split on
      -- whether `v` is rational — `ordAtSpec_eq_count` applies uniformly.
      have hordv : ordAtSpec v A B = ordAtSpec v A' B' := hordeqSpec v
      have hcountAB : ordAtSpec v A B =
          ((Associates.mk v.asIdeal).count (Associates.mk I).factors : ℤ) := by
        rw [hI_def]; exact ordAtSpec_eq_count v A B hABz
      have hcountA'B' : ordAtSpec v A' B' =
          ((Associates.mk v.asIdeal).count (Associates.mk I').factors : ℤ) := by
        rw [hI'_def]; exact ordAtSpec_eq_count v A' B' hA'B'z
      rw [hcountAB, hcountA'B'] at hordv
      exact_mod_cast hordv
    · push Not at hJmem
      rw [Multiset.count_eq_zero.mpr hJmem.1, Multiset.count_eq_zero.mpr hJmem.2]
  have hfactors_eq : UniqueFactorizationMonoid.normalizedFactors I =
      UniqueFactorizationMonoid.normalizedFactors I' := Multiset.ext'_iff.mpr hcount_eq
  calc I = (UniqueFactorizationMonoid.normalizedFactors I).prod :=
        (Ideal.prod_normalizedFactors_eq_self hIbot).symm
    _ = (UniqueFactorizationMonoid.normalizedFactors I').prod := by rw [hfactors_eq]
    _ = I' := Ideal.prod_normalizedFactors_eq_self hI'bot

/-- **Closed-point-native analogue of `isConstantFraction_of_ordAt_eq`.** Same proof
shape (Dedekind-domain unique factorization ⟹ associated elements ⟹ unit ⟹
`CoordinateRing H`'s unit group is `k^×` ⟹ constant fraction), verbatim except for
routing through `span_eq_of_ordAtSpec_eq` instead of `span_eq_of_ordAt_eq`. -/
theorem isConstantFraction_of_ordAtSpec_eq [IsDedekindDomain (CoordinateRing H)]
    (hdeg : H.f.natDegree = 5) (A B A' B' : k[X])
    (hordeqSpec : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      ordAtSpec v A B = ordAtSpec v A' B') :
    IsConstantFraction (polePairToFraction (H := H) A B A' B') := by
  by_cases hABz : toPair H A B = 0
  · refine ⟨0, ?_⟩
    unfold polePairToFraction
    rw [hABz, map_zero, zero_div]
    have : (algebraMap k[X] (CoordinateRing H) (C (0:k))) = 0 := by simp
    rw [this, map_zero]
  · by_cases hA'B'z : toPair H A' B' = 0
    · refine ⟨0, ?_⟩
      unfold polePairToFraction
      rw [hA'B'z, map_zero, div_zero]
      have : (algebraMap k[X] (CoordinateRing H) (C (0:k))) = 0 := by simp
      rw [this, map_zero]
    · have hspan : Ideal.span ({toPair H A B} : Set (CoordinateRing H)) =
          Ideal.span ({toPair H A' B'} : Set (CoordinateRing H)) :=
        span_eq_of_ordAtSpec_eq (H := H) A B A' B' hABz hA'B'z hordeqSpec
      have hassoc : Associated (toPair H A B) (toPair H A' B') :=
        Ideal.span_singleton_eq_span_singleton.mp hspan
      obtain ⟨u, hu⟩ := hassoc
      have hu_unit : IsUnit (u : CoordinateRing H) := u.isUnit
      obtain ⟨c, hc, hcu⟩ := (isUnit_coordinateRing_iff (H := H) hdeg (u : CoordinateRing H)).mp
        hu_unit
      refine ⟨c⁻¹, ?_⟩
      unfold polePairToFraction
      set F := FractionRing (CoordinateRing H)
      set φ : CoordinateRing H →+* F := algebraMap (CoordinateRing H) F with hφ_def
      have hcz : (C c : k[X]) ≠ 0 := fun h => hc (by simpa using congrArg (Polynomial.eval 0) h)
      have hCcpair_ne : toPair H (C c) 0 ≠ 0 := by
        rw [Ne, toPair_eq_zero_iff]; exact fun h => hcz h.1
      have hCc_alg : toPair H (C c) 0 = algebraMap k[X] (CoordinateRing H) (C c) := by
        unfold toPair; simp
      have hCc_ne_ring : (algebraMap k[X] (CoordinateRing H) (C c) : CoordinateRing H) ≠ 0 := by
        rw [← hCc_alg]; exact hCcpair_ne
      have hABz' : φ (toPair H A B) ≠ 0 :=
        fun h => hABz (IsFractionRing.injective (CoordinateRing H) F
          (by rw [hφ_def] at h; rw [h, map_zero]))
      have hCc_ne_frac : φ (algebraMap k[X] (CoordinateRing H) (C c)) ≠ 0 :=
        fun h => hCc_ne_ring (IsFractionRing.injective (CoordinateRing H) F
          (by rw [hφ_def] at h; rw [h, map_zero]))
      have hring_eq : toPair H A B =
          algebraMap k[X] (CoordinateRing H) (C c⁻¹) * toPair H A' B' := by
        have h1 : toPair H A' B' = algebraMap k[X] (CoordinateRing H) (C c) * toPair H A B := by
          rw [← hu, hcu, mul_comm]
        rw [h1, ← mul_assoc, ← map_mul, ← Polynomial.C_mul, inv_mul_cancel₀ hc,
          Polynomial.C_1, map_one, one_mul]
      have hden_ne : φ (toPair H A' B') ≠ 0 := by
        rw [← hu, hcu, map_mul]; exact mul_ne_zero hABz' hCc_ne_frac
      rw [div_eq_iff hden_ne, hring_eq, map_mul]

/-! ## §4. Main theorem: `uniqueDegree2MapToP1`, general `k`, no
`[IsAlgClosed k]`.

Consumes `LPairCarrierSpec'` (closed-point-native) instead of `LPairCarrier'`
(rational-points-only), which is what makes `IsPoleBoundedAtPairSpec`
available at the rationalized triple, and hence the whole
`CoprimeAtRootsClosed.lean` route usable. -/

variable [DecidableEq k]

/-- **Uniqueness of the degree-2 map to `P¹` glued at `{x₁, x₂}`, general `k`.**
The `[IsAlgClosed k]`-free replacement for `uniqueDegree2MapToP1_ordAtFrac`. -/
theorem uniqueDegree2MapToP1Spec (hdeg : H.f.natDegree = 5) (hchar : (2 : k) ≠ 0)
    (hsf : Squarefree H.f) (x₁ x₂ : H.Point) (hne : x₂ ≠ Point.iota x₁)
    (z : FractionRing (CoordinateRing H)) (hz : z ∈ LPairCarrierSpec' x₁ x₂) :
    IsConstantFraction z := by
  classical
  rcases hz with hz0 | ⟨A, B, A', B', hbound, hz_eq⟩
  · exact ⟨0, by rw [hz0]; simp⟩
  · obtain ⟨hAB0ne, hA'B'ne, hinfle, hptwise'⟩ := hbound
    have hA'B'toPairne : toPair H A' B' ≠ 0 := by
      rw [Ne, toPair_eq_zero_iff]; exact hA'B'ne
    obtain ⟨a, b, c, hcne, hc_def, ha_def, hb_def, hfrac_eq⟩ :=
      frac_toPair_den_kx hdeg A B A' B' hA'B'toPairne
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
      exact (map_eq_zero_iff _ (IsFractionRing.injective (CoordinateRing H)
        (FractionRing (CoordinateRing H)))).mp hABmap0
    have hc0_ne : toPair H c (0 : k[X]) ≠ 0 := by
      rw [Ne, toPair_eq_zero_iff]; exact fun h => hcne h.1
    -- **Closed-point-native pointwise bound transported to `(a,b,c,0)`.**
    have hzsuppSpec : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
        ordAtSpec v a b - ordAtSpec v c (0 : k[X]) ≥
          -((if v = pointHeightOne' x₁ then 1 else 0) +
            (if v = pointHeightOne' x₂ then 1 else 0)) := by
      intro v
      -- Transport `hptwise'` (stated for `(A,B,A',B')`) to `(a,b,c,0)` via the
      -- fraction equality `hfrac_eq`, exactly as `ordAtFrac_eq_of_polePairToFraction_eq`
      -- does at the `H.Point`-only level — here at the level of `ordAtSpec`
      -- differences, using the same representation-independence fact
      -- (`ordAtSpec` of a fraction depends only on the fraction, not the
      -- witness), specialized pointwise. We reuse the existing `H.Point`-level
      -- transport lemma at `pointHeightOne'`-images via `ordAt_eq_ordAtSpec`
      -- where `v` is rational, and directly via the closed-point identity
      -- `polePairToFraction`-invariance otherwise; since `hptwise'` is already
      -- stated for *every* `v`, no case split is needed at all — the same
      -- fraction-equality argument that proves `ordAtFrac_eq_of_polePairToFraction_eq`
      -- for `H.Point` applies verbatim with `ordAt` replaced by `ordAtSpec`
      -- throughout (that lemma's proof never uses rationality of the point).
      have hv := hptwise' v
      rwa [ordAtSpec_sub_ordAtSpec_eq_of_polePairToFraction_eq (H := H) v A B A' B' a b c 0
        hAB0ne hA'B'toPairne hc0_ne hfrac_eq] at hv
    have hinf : ordInfOfPair a b ≥ ordInfOfPair c (0 : k[X]) := by
      have hABne : ¬ (A = 0 ∧ B = 0) := fun h => hAB0ne (by rw [toPair_eq_zero_iff]; exact h)
      have habne : ¬ (a = 0 ∧ b = 0) := fun h => hab_ne (by rw [toPair_eq_zero_iff]; exact h)
      have hc_def' : c = A' ^ 2 - B' ^ 2 * H.f := by rw [hc_def]; rfl
      exact ordInfOfPair_rationalized_ge hdeg A B A' B' hABne hA'B'ne hinfle a b c
        ha_def hb_def hc_def' habne hcne
    -- **Reduce `(a,b,c)` by the joint `k[X]`-gcd**, using the `H.Point`-only
    -- `reduce_ordAtFrac_triple` (its `ordAtFrac`-shaped conclusion is exactly
    -- what we need downstream for `b₀ = 0`, and its internal construction is
    -- exactly what §1 above re-derives the unit-gcd fact from). First bridge
    -- `hzsuppSpec` down to the `ordAtFrac`/`H.Point`-shaped hypothesis
    -- `reduce_ordAtFrac_triple` expects.
    have hzsupp : ∀ P : H.Point, ordAtFrac P a b c 0 ≥
        -((if P = x₁ then 1 else 0) + (if P = x₂ then 1 else 0)) := by
      intro P
      have hv := hzsuppSpec (pointHeightOne' P)
      rw [← ordAt_eq_ordAtSpec, ← ordAt_eq_ordAtSpec, pointHeightOne'_eq_iff,
        pointHeightOne'_eq_iff] at hv
      unfold ordAtFrac
      exact hv
    -- **Reduce by the explicit joint gcd `g := gcd (gcd a b) c` directly**
    -- (inline, rather than via `reduce_ordAtFrac_triple`'s opaque existential),
    -- so the quotient witnesses `a₀ = a/g, b₀ = b/g, c₀ = c/g` are available
    -- by name for §1's `gcd_unit_of_reduce_ordAtFrac_triple`.
    set g := gcd (gcd a b) c with hg_def
    have hg_dvd_ab : g ∣ gcd a b := gcd_dvd_left _ _
    have hg_dvd_a : g ∣ a := hg_dvd_ab.trans (gcd_dvd_left _ _)
    have hg_dvd_b : g ∣ b := hg_dvd_ab.trans (gcd_dvd_right _ _)
    have hg_dvd_c : g ∣ c := gcd_dvd_right _ _
    have hgne : g ≠ 0 := fun h => hcne (eq_zero_of_zero_dvd (h ▸ hg_dvd_c))
    obtain ⟨a₀, ha_eq⟩ := hg_dvd_a
    obtain ⟨b₀, hb_eq⟩ := hg_dvd_b
    obtain ⟨c₀, hc_eq⟩ := hg_dvd_c
    have hc₀ne : c₀ ≠ 0 := by intro h; apply hcne; rw [hc_eq, h, mul_zero]
    have hab₀ne : ¬ (a₀ = 0 ∧ b₀ = 0) := by
      rintro ⟨ha0, hb0⟩
      apply hab_ne
      apply toPair_eq_zero_iff H a b |>.mpr
      exact ⟨by rw [ha_eq, ha0, mul_zero], by rw [hb_eq, hb0, mul_zero]⟩
    have hab₀_ne : toPair H a₀ b₀ ≠ 0 := fun h => hab₀ne (toPair_eq_zero_iff H a₀ b₀ |>.mp h)
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
    have hfrac_eq₀ : polePairToFraction (H := H) a b c 0 =
        polePairToFraction (H := H) a₀ b₀ c₀ 0 := by
      unfold polePairToFraction
      rw [hnum, hden, map_mul, map_mul]
      have hgmap_ne : algebraMap (CoordinateRing H) (FractionRing (CoordinateRing H))
          (toPair H g (0 : k[X])) ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective (CoordinateRing H)
          (FractionRing (CoordinateRing H)))).mpr hg_toPair_ne
      rw [mul_div_mul_left _ _ hgmap_ne]
    have hc0_ne' : toPair H c (0 : k[X]) ≠ 0 := fun h => hcne (toPair_eq_zero_iff H c 0 |>.mp h).1
    have hc₀0_ne : toPair H c₀ (0 : k[X]) ≠ 0 :=
      fun h => hc₀ne (toPair_eq_zero_iff H c₀ 0 |>.mp h).1
    -- **General closed-point-native pointwise bound at `(a₀,b₀,c₀,0)`, before
    -- `b₀ = 0` is known** — transported from `hzsuppSpec` (pre-reduction, at
    -- `(a,b,c,0)`) exactly as the post-`hbeq0` version below does, just moved earlier
    -- so `natDegree_le_two_of_gcdUnit_closed_point` can consume it for `hcdeg`.
    have hzsuppSpec₀ : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
        ordAtSpec v a₀ b₀ - ordAtSpec v c₀ (0 : k[X]) ≥
          -((if v = pointHeightOne' x₁ then 1 else 0) +
            (if v = pointHeightOne' x₂ then 1 else 0)) := by
      intro v
      have hv := hzsuppSpec v
      rwa [ordAtSpec_sub_ordAtSpec_eq_of_polePairToFraction_eq (H := H) v a b c 0 a₀ b₀ c₀ 0
        hab_ne hc0_ne' hc₀0_ne hfrac_eq₀] at hv
    have hzsupp₀ : ∀ P : H.Point, ordAtFrac P a₀ b₀ c₀ 0 ≥
        -((if P = x₁ then 1 else 0) + (if P = x₂ then 1 else 0)) := by
      intro P
      rw [← ordAtFrac_eq_of_polePairToFraction_eq P a b c 0 a₀ b₀ c₀ 0
        hab_ne hc0_ne' hc₀0_ne hfrac_eq₀]
      exact hzsupp P
    have hinf₀ : ordInfOfPair a₀ b₀ ≥ ordInfOfPair c₀ (0 : k[X]) := by
      have hc₀0ne : ¬ (c₀ = 0 ∧ (0 : k[X]) = 0) := by simpa using hc₀ne
      have hshift_ab : ordInfOfPair a b = ordInfOfPair a₀ b₀ - 2 * (g.natDegree : ℤ) := by
        rw [ha_eq, hb_eq]; exact ordInfOfPair_mul_left g a₀ b₀ hgne hab₀ne
      have hshift_c : ordInfOfPair c (0 : k[X]) =
          ordInfOfPair c₀ (0 : k[X]) - 2 * (g.natDegree : ℤ) := by
        rw [hc_eq]
        have h := ordInfOfPair_mul_left g c₀ (0 : k[X]) hgne hc₀0ne
        simpa only [mul_zero] using h
      -- Chain the three facts as bare `≤`/`≥`/`=` values via `calc`, never
      -- asking a tactic (`rw ... at`, `generalize ... at`, `set`) to search
      -- for `ordInfOfPair` occurrences inside an already-elaborated
      -- hypothesis — that search itself is what timed out twice before, since
      -- `ordInfOfPair`'s `max`/`if` definition is expensive to match against.
      -- `calc` only ever unifies each step's own stated end points, which are
      -- written out plainly here, so no such search is triggered.
      calc ordInfOfPair a₀ b₀ = ordInfOfPair a b + 2 * (g.natDegree : ℤ) := by
            rw [hshift_ab]; ring
        _ ≥ ordInfOfPair c (0 : k[X]) + 2 * (g.natDegree : ℤ) := by
            gcongr <;> exact hinf
        _ = ordInfOfPair c₀ (0 : k[X]) := by
            rw [hshift_c]; ring
    -- **§1's unit-gcd fact**, proved directly for the already-named
    -- quotient witnesses. Avoid passing the `set g := ...` abstraction through
    -- `gcd_unit_of_reduce_ordAtFrac_triple`: that forces elaboration to unfold
    -- the gcd expression while matching several dependent hypotheses, which is
    -- exactly where `whnf` was hitting the heartbeat limit.
    have hgu : IsUnit (gcd (gcd a₀ b₀) c₀) := by
      set d := gcd (gcd a₀ b₀) c₀ with hd_def
      have hd_dvd_a₀ : d ∣ a₀ :=
        (gcd_dvd_left _ _).trans (gcd_dvd_left _ _)
      have hd_dvd_b₀ : d ∣ b₀ :=
        (gcd_dvd_left _ _).trans (gcd_dvd_right _ _)
      have hd_dvd_c₀ : d ∣ c₀ := gcd_dvd_right _ _
      have hgd_dvd_a : g * d ∣ a := by
        rw [ha_eq]
        exact mul_dvd_mul_left g hd_dvd_a₀
      have hgd_dvd_b : g * d ∣ b := by
        rw [hb_eq]
        exact mul_dvd_mul_left g hd_dvd_b₀
      have hgd_dvd_c : g * d ∣ c := by
        rw [hc_eq]
        exact mul_dvd_mul_left g hd_dvd_c₀
      have hgd_dvd_gab : g * d ∣ gcd a b :=
        dvd_gcd hgd_dvd_a hgd_dvd_b
      have hgd_dvd_g : g * d ∣ g :=
        dvd_gcd hgd_dvd_gab hgd_dvd_c
      have hd_dvd_one : d ∣ (1 : k[X]) := by
        have hg_dvd_g1 : g ∣ g * 1 := by rw [mul_one]
        have h := (mul_dvd_mul_iff_left hgne).mp
          (hgd_dvd_g.trans hg_dvd_g1)
        simpa using h
      exact isUnit_of_dvd_one hd_dvd_one
    -- **§0: `c₀.natDegree ≤ 2`** — reuse the existing `IsCoprimeAtRoots`-based
    -- route for this bound (unaffected by closedness: it only needs `H.Point`-
    -- rational roots to bound the *rational* root count, and the *degree*
    -- bound itself, at this stage, is only used to get `b₀ = 0`, not to force
    -- `c₀` constant — that finish uses the new §3 route instead). We still
    -- need `IsCoprimeAtRoots a₀ b₀ c₀`, which follows from the unit-gcd fact.
    have hcop : IsCoprimeAtRoots a₀ b₀ c₀ := by
      intro α hα
      rintro ⟨hαa, hαb⟩
      have hlin_dvd_a₀ : linX α ∣ a₀ := Polynomial.dvd_iff_isRoot.mpr hαa
      have hlin_dvd_b₀ : linX α ∣ b₀ := Polynomial.dvd_iff_isRoot.mpr hαb
      have hlin_dvd_c₀ : linX α ∣ c₀ := Polynomial.dvd_iff_isRoot.mpr hα
      have hlin_dvd_gcd : linX α ∣ gcd (gcd a₀ b₀) c₀ :=
        dvd_gcd (dvd_gcd hlin_dvd_a₀ hlin_dvd_b₀) hlin_dvd_c₀
      have hlin_unit : IsUnit (linX α : k[X]) := isUnit_of_dvd_unit hlin_dvd_gcd hgu
      have hlin_deg : (linX α : k[X]).natDegree = 1 := by unfold linX; compute_degree!
      have hlin_deg0 : (linX α : k[X]).natDegree = 0 :=
        Polynomial.natDegree_eq_zero_of_isUnit hlin_unit
      omega
    -- **`c₀.natDegree ≤ 2`**, closed-point-native (§3f), no `IsAlgClosed` anywhere:
    -- `natDegree_le_two_of_gcdUnit_closed_point` consumes `hgu` and the general
    -- `hzsuppSpec₀` (built above, pre-`b₀=0`) directly — replaces the old
    -- `natDegree_le_two_of_isCoprimeAtRoots[_eq]` route, which silently required
    -- `[IsAlgClosed k]` via `IsAlgClosed.splits` in its own proof.
    -- The `whnf` timeout at this call site is not caused by the callee (which
    -- elaborates fine on its own, see its `set_option maxHeartbeats 100000000`
    -- above) — it's caused by unifying the call against ~65 accumulated local
    -- hypotheses (`hzsuppSpec`, `hzsupp`, `hnum`, `hden`, `hfrac_eq₀`, `hgu`'s
    -- own internal `d`, etc.) still sitting in context here, none of which the
    -- callee needs. `clear` them first so the `exact` elaborates against a
    -- small, cheap-to-`whnf` context instead of raising heartbeats.
    have hcdeg : c₀.natDegree ≤ 2 := by
      clear hA'B'toPairne hab_ne hc0_ne hzsuppSpec hinf hzsupp
        hg_dvd_ab hgne
        htoPair_right_zero hg_toPair_ne hnum hden hfrac_eq₀ hc0_ne' hc₀0_ne
        hzsupp₀ hinf₀ hcop hfrac_eq ha_def hb_def hc_def hcne
        hAB0ne hA'B'ne hinfle hptwise' hz_eq hne
        ha_eq hb_eq hc_eq hg_def g
      exact natDegree_le_two_of_gcdUnit_closed_point (H := H) hdeg x₁ x₂ a₀ b₀ c₀
        hc₀ne hab₀_ne hgu hchar hsf hzsuppSpec₀
    have hbeq0 : b₀ = 0 := by
      by_contra hb0
      have hInfb : ordInfOfPair a₀ b₀ ≤ -5 := by
        rw [ordInfOfPair_eq_of_ne a₀ b₀ hab₀ne]
        simp only [if_neg hb0]
        have hmax : (5 : ℤ) ≤
            max (2 * (a₀.natDegree : ℤ)) (2 * (b₀.natDegree : ℤ) + 5) := by
          exact le_trans (by omega) (le_max_right _ _)
        linarith
      have hInfc : -(4 : ℤ) ≤ ordInfOfPair c₀ (0 : k[X]) := by
        rw [ordInfOfPair_eq_of_ne c₀ 0 (fun h => hc₀ne h.1)]
        have hmax : max (2 * (c₀.natDegree : ℤ)) 0 ≤ 4 := by
          apply max_le
          · omega
          · omega
        simpa only [if_true, Nat.cast_zero, mul_zero, add_zero] using
          (neg_le_neg hmax)
      linarith [hinf₀, hInfb, hInfc]
    subst b₀
    -- **[DEPRECATED ROUTE REMOVED]** This used to go through `IsNormCoprime`
    -- (`isNormCoprime_of_gcd_unit_snd_zero` +
    -- `natDegree_le_one_of_isPoleBoundedAtPairSpec_isNormCoprime`) to get
    -- `c₀.natDegree ≤ 1`. That route is deprecated — see §2's header above.
    -- The `IsCoprimeAtRoots`-based route is the maintained strategy, but
    -- nothing currently derives `c₀.natDegree ≤ 1` (as opposed to `≤ 2`,
    -- already in hand as `hcdeg`) from it. Left as an honest gap for the
    -- next pass rather than papered over with the deprecated bridge.
    have hcdeg1 : c₀.natDegree ≤ 1 := by
      by_contra hnot
      -- Every irreducible factor is impossible: a linear one gives a rational
      -- root, while a non-linear one gives a closed point away from both the
      -- distinguished rational points (and away from their conjugates).
      obtain ⟨q, hq, hqc⟩ :=
        Polynomial.exists_irreducible_of_natDegree_pos (show 0 < c₀.natDegree by omega)
      have hqdeg_ne_one : q.natDegree ≠ 1 := by
        intro hqdeg1
        obtain ⟨α, hαq⟩ := exists_root_of_natDegree_eq_one q hqdeg1
        have hαc : c₀.IsRoot α := by
          obtain ⟨s, hs⟩ := hqc
          rw [hs]
          simp [hαq]
        have haα : a₀.eval α ≠ 0 := by
          intro haα
          exact (hcop α hαc) ⟨haα, by simp⟩
        exact false_of_root_of_isCoprimeAtRoots_zero_snd_general
          (H := H) hchar hsf x₁ x₂ hne a₀ c₀ hc₀ne hcop
            hzsupp₀ hzsuppSpec₀ α hαc
      obtain ⟨v, hvq⟩ := heightOneSpectrum_over_irreducible (H := H) q hq
      have hqmem : algebraMap k[X] (CoordinateRing H) q ∈ v.asIdeal := by
        have hmem : q ∈ Ideal.comap (algebraMap k[X] (CoordinateRing H)) v.asIdeal := by
          rw [hvq]
          exact Ideal.mem_span_singleton_self q
        exact hmem
      have hv1 : v ≠ pointHeightOne' x₁ := by
        intro hv
        subst v
        have hqmem' : algebraMap k[X] (CoordinateRing H) q ∈ pointIdeal x₁ := hqmem
        change evalAtPoint x₁ (algebraMap k[X] (CoordinateRing H) q) = 0 at hqmem'
        change Polynomial.eval₂ (Polynomial.evalRingHom x₁.val.1) x₁.val.2 (C q) = 0 at hqmem'
        have hqroot : q.IsRoot x₁.X := by
          simpa [Point.X] using hqmem'
        exact hq.not_isRoot_of_natDegree_ne_one hqdeg_ne_one hqroot
      have hv2 : v ≠ pointHeightOne' x₂ := by
        intro hv
        subst v
        have hqmem' : algebraMap k[X] (CoordinateRing H) q ∈ pointIdeal x₂ := hqmem
        change evalAtPoint x₂ (algebraMap k[X] (CoordinateRing H) q) = 0 at hqmem'
        change Polynomial.eval₂ (Polynomial.evalRingHom x₂.val.1) x₂.val.2 (C q) = 0 at hqmem'
        have hqroot : q.IsRoot x₂.X := by
          simpa [Point.X] using hqmem'
        exact hq.not_isRoot_of_natDegree_ne_one hqdeg_ne_one hqroot
      have hwmem : algebraMap k[X] (CoordinateRing H) q ∈
          (conjHeightOne (H := H) v).asIdeal := by
        rw [mem_conjHeightOne_iff]
        simpa [involution_algebraMap] using hqmem
      have hw1 : conjHeightOne (H := H) v ≠ pointHeightOne' x₁ := by
        intro hw
        have hwmem' := hwmem
        rw [hw] at hwmem'
        change evalAtPoint x₁ (algebraMap k[X] (CoordinateRing H) q) = 0 at hwmem'
        change Polynomial.eval₂ (Polynomial.evalRingHom x₁.val.1) x₁.val.2 (C q) = 0 at hwmem'
        have hqroot : q.IsRoot x₁.X := by
          simpa [Point.X] using hwmem'
        exact hq.not_isRoot_of_natDegree_ne_one hqdeg_ne_one hqroot
      have hw2 : conjHeightOne (H := H) v ≠ pointHeightOne' x₂ := by
        intro hw
        have hwmem' := hwmem
        rw [hw] at hwmem'
        change evalAtPoint x₂ (algebraMap k[X] (CoordinateRing H) q) = 0 at hwmem'
        change Polynomial.eval₂ (Polynomial.evalRingHom x₂.val.1) x₂.val.2 (C q) = 0 at hwmem'
        have hqroot : q.IsRoot x₂.X := by
          simpa [Point.X] using hwmem'
        exact hq.not_isRoot_of_natDegree_ne_one hqdeg_ne_one hqroot
      have hc0ne_pair : toPair H c₀ (0 : k[X]) ≠ 0 := by
        rw [Ne, toPair_eq_zero_iff]
        exact fun h => hc₀ne h.1
      have hvzero : ordAtSpec v c₀ (0 : k[X]) = 0 := by
        clear hqdeg_ne_one hqmem hwmem hc0ne_pair hAB0ne hA'B'ne hinfle hptwise'
          hz_eq hne hcne ha_def hb_def hc_def hfrac_eq hab_ne hc0_ne hzsuppSpec
          hinf hzsupp hg_dvd_ab hgne htoPair_right_zero
          hg_toPair_ne hnum hden hfrac_eq₀ hc0_ne' hc₀0_ne hzsupp₀ hinf₀ hcop
          hab₀ne hA'B'toPairne hq hqc ha_eq hb_eq hc_eq hg_def g
        exact ordAtSpec_eq_zero_of_notMem_four_of_dvd
          (H := H) x₁ x₂ a₀ 0 c₀ hc₀ne hab₀_ne hgu hzsuppSpec₀ hchar hsf
          v hv1 hv2 hw1 hw2
      have hc0mem : toPair H c₀ (0 : k[X]) ∈ v.asIdeal := by
        obtain ⟨s, hs⟩ := hqc
        rw [hs]
        unfold HyperellipticPolynomial.toPair
        rw [map_mul, map_zero, zero_mul, add_zero]
        exact Ideal.mul_mem_right _ v.asIdeal hqmem
      have hc0pos : 0 < ordAtSpec v c₀ (0 : k[X]) := by
        set_option maxHeartbeats 100000000 in
          rw [ordAtSpec_eq_count v c₀ 0 hc0ne_pair]
          have hIne : Ideal.span ({toPair H c₀ (0 : k[X])} : Set (CoordinateRing H)) ≠ 0 := by
            rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
            exact hc0ne_pair
          have hdvd := Ideal.dvd_span_singleton.mpr hc0mem
          have hge1 : 1 ≤ (Associates.mk v.asIdeal).count
              (Associates.mk (Ideal.span ({toPair H c₀ (0 : k[X])} : Set (CoordinateRing H)))).factors := by
            have hIne' : Associates.mk
                (Ideal.span ({toPair H c₀ (0 : k[X])} : Set (CoordinateRing H))) ≠ 0 :=
              Associates.mk_ne_zero.mpr hIne
            rw [← Associates.prime_pow_dvd_iff_le hIne' v.associates_irreducible, pow_one]
            exact Associates.mk_le_mk_iff_dvd.mpr hdvd
          exact_mod_cast hge1
      omega
    -- **§4: finish.** `c₀.natDegree ≤ 1` — if `= 1`, it has a genuine root
    -- (`exists_root_of_natDegree_eq_one`), contradicting pole-boundedness via
    -- the `[IsAlgClosed k]`-free `false_of_root_of_isCoprimeAtRoots_zero_snd_general`
    -- (§3d above), which case-splits on whether `H.f.eval α` is `0`, a square,
    -- or a non-square, using `hzsuppSpec₀` (closed-point-native) for the
    -- non-square branch instead of `IsAlgClosed.exists_pow_nat_eq`.
    have hcdeg0 : c₀.natDegree = 0 := by
      by_contra hcdeg0
      have hc₀deg1 : c₀.natDegree = 1 := by omega
      obtain ⟨α, hα⟩ := exists_root_of_natDegree_eq_one c₀ hc₀deg1
      clear hcdeg0 hcdeg1 hAB0ne hA'B'ne hinfle hptwise' hz_eq hcne ha_def
        hb_def hc_def hfrac_eq hab_ne hc0_ne hzsuppSpec hinf hzsupp hg_dvd_ab
        hgne htoPair_right_zero hg_toPair_ne hnum hden
        hfrac_eq₀ hc0_ne' hc₀0_ne hab₀ne hA'B'toPairne hgu hc₀deg1
        ha_eq hb_eq hc_eq hg_def g
      exact false_of_root_of_isCoprimeAtRoots_zero_snd_general
        (H := H) hchar hsf x₁ x₂ hne a₀ c₀ hc₀ne hcop hzsupp₀ hzsuppSpec₀ α hα
    have hadeg0 : a₀.natDegree = 0 := by
      have habne0 : a₀ ≠ 0 := by
        intro ha0
        apply hab₀_ne
        simp [ha0, toPair_eq_zero_iff]
      have haInf : ordInfOfPair a₀ (0 : k[X]) = -2 * (a₀.natDegree : ℤ) := by
        rw [ordInfOfPair_eq_of_ne a₀ 0 (fun h => habne0 h.1)]
        simp
      have hcInf : ordInfOfPair c₀ (0 : k[X]) = -2 * (c₀.natDegree : ℤ) := by
        rw [ordInfOfPair_eq_of_ne c₀ 0 (fun h => hc₀ne h.1)]
        simp
      have horda : -2 * (a₀.natDegree : ℤ) ≥
          -2 * (c₀.natDegree : ℤ) := by
        calc
          -2 * (a₀.natDegree : ℤ) = ordInfOfPair a₀ (0 : k[X]) := haInf.symm
          _ ≥ ordInfOfPair c₀ (0 : k[X]) := hinf₀
          _ = -2 * (c₀.natDegree : ℤ) := hcInf
      rw [hcdeg0] at horda
      simp at horda
      omega
    obtain ⟨ka, hka⟩ := Polynomial.natDegree_eq_zero.mp hadeg0
    obtain ⟨kc, hkc⟩ := Polynomial.natDegree_eq_zero.mp hcdeg0
    refine ⟨ka / kc, ?_⟩
    have hkc_ne : kc ≠ 0 := by
      rintro rfl; simp at hkc; exact hc₀ne hkc.symm
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

end
