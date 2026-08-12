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

/-! ## §2. `IsNormCoprime` after `b = 0`.

Once `b₀ = 0`, `pairNorm H a₀ 0 = a₀ ^ 2 - 0 ^ 2 * H.f = a₀ ^ 2`, so
`IsNormCoprime H a₀ 0 c₀` (`IsCoprime (pairNorm H a₀ 0) c₀`) is exactly
`IsCoprime (a₀ ^ 2) c₀`, which follows from ordinary `IsCoprime a₀ c₀` via
`IsCoprime.pow_left`. -/

omit [IsDedekindDomain (CoordinateRing H)] in
/-- **`IsNormCoprime` from a unit joint gcd, at `b = 0`.** -/
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
`false_of_root_of_coprimeAtRoots_zero_snd`. The ramified rational case
reuses that lemma's exact argument (no closedness there); the unramified
rational case uses `false_of_root_unramified_of_isSquare` (square root taken
from `hsq` directly, not from `IsAlgClosed`); the `H.f.eval α` non-square
case uses `false_of_nonSquareFiber_root`. -/
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
  classical
  have haα : a₀.eval α ≠ 0 := fun h => hcop α hα ⟨h, by simp⟩
  by_cases hWeier : H.f.eval α = 0
  · exact false_of_root_of_coprimeAtRoots_zero_snd
      (H := H) hchar hsf x₁ x₂ hne a₀ c₀ hc₀ne hcop hzsupp₀ α hα
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

/-- **STATUS: `false_of_bad_factor_split_deg_ge_two` — attempted, not closed.**
Built `SplitBaseField q := AdjoinRoot q`, `SqrtExtQ q := L[T]/(T² - mk q H.f)`, and
`evalAtSplitFiber : CoordinateRing H →+* SqrtExtQ q` (well-defined, `x ↦ root q`, `y ↦`
the adjoined square root) — the ring-hom layer of the construction, directly analogous
to `evalAtRamifiedFiber` above. **Not yet built on top of it:** surjectivity, primality
of the kernel, and the residue-degree lower bound. Unlike the ramified case, `SqrtExtQ
q` is not automatically a field (`T² - mk q H.f` may split in `L` already, giving
`SqrtExtQ q ≅ L × L`), so `RingHom.ker_isMaximal_of_surjective` doesn't apply directly
— the kernel is prime (pulled back from a field factor of `SqrtExtQ q`, e.g. via
`Ideal.primeCompl`/factoring through one coordinate of the product decomposition when
reducible, or the whole ring when `T² - mk q H.f` stays irreducible over `L`) but
establishing that split, and the resulting `residueDeg = q.natDegree` (reducible case)
or `2 * q.natDegree` (irreducible case) either way `≥ q.natDegree ≥ 2`, is genuinely
unfinished work, comparable in remaining size to what `ramifiedFiberHeightOne` needed
end-to-end.

**What IS solid and complete below, reusable regardless:** `notDvd_snd_of_dvd_gcd_pairNorm_of_gcdUnit`
(`q ∤ b₀` from `hgu`), `involution_involution` / `involution_bijective` /
`involutionEquiv` / `conjHeightOne` / `mem_conjHeightOne_iff` (the conjugate-closed-point
machinery under the hyperelliptic involution — fully general, not specific to this case
split), and the `SplitBaseField`/`SqrtExtQ`/`evalAtSplitFiber` ring-hom layer just
above. The case-split argument itself (GPT's residue-field computation, confirmed
correct in the abstract: nonmembership at the split point gives *exact* order `0` for
free via `ordAtSpec_eq_zero_of_notMem`, no induction needed, unlike the ramified case)
is ready to write once the prime-ideal/residue-degree package on top of
`evalAtSplitFiber` is finished.

### The split closed point at an arbitrary-degree irreducible `q ∤ H.f`, built
explicitly (not via the opaque going-up lemma, so residue degree is computable).

Mirrors `NonSquareFiberPoint.lean`'s `SqrtExt`/`evalAtNonSquareFiber` pattern exactly,
with the scalar `α : k` generalized to the root of an arbitrary irreducible `q : k[X]`:
base field `L := AdjoinRoot q` (`[L:k] = q.natDegree`), then `M := SqrtExtQ q := L[T]/(T² -
(H.f mod q))` (`[M:L] ≤ 2`, always `≥ 1`), giving `evalAtSplitFiber : CoordinateRing H →+*
M` sending `x ↦ root q`, `y ↦ ` the chosen square root of `H.f mod q` in `M`. Unlike the
ramified construction, `M` need not itself be a field when `H.f mod q` happens to be a
square in `L` (then `M ≅ L × L`) — but `ker (evalAtSplitFiber)` is still prime: it's the
kernel of `CoordinateRing H →+* M ↠ M / (one factor)`, landing in one of the two field
factors, each of `k`-dimension exactly `[L:k] = q.natDegree` (not `2·q.natDegree`) in that
split sub-case — either way `residueDeg ≥ q.natDegree ≥ 2`, all that's actually needed. -/

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
`RingHom.quotientKerEquivOfSurjective` and `AdjoinRoot`'s `finrank` (`q.natDegree`,
same computation as `finrank_sqrtExt` but at general degree, using `AdjoinRoot.finrank`
directly against `q` itself rather than `X² - C c`). -/
theorem residueDeg_ramifiedFiberHeightOne [IsDedekindDomain (CoordinateRing H)]
    (q : k[X]) (hq : Irreducible q) (hqf : q ∣ H.f) :
    residueDeg (ramifiedFiberHeightOne (H := H) q hq hqf) = q.natDegree := by
  unfold residueDeg ramifiedFiberHeightOne
  simp only
  have hequiv : (CoordinateRing H ⧸ RingHom.ker (evalAtRamifiedFiber (H := H) q hqf)) ≃+*
      AdjoinRoot q :=
    RingHom.quotientKerEquivOfSurjective (evalAtRamifiedFiber_surjective (H := H) q hqf)
  have hlinequiv : Module.finrank k (CoordinateRing H ⧸ ramifiedFiberIdeal (H := H) q hqf) =
      Module.finrank k (AdjoinRoot q) := by
    apply LinearEquiv.finrank_eq
    exact hequiv.toAddEquiv.toLinearEquiv (fun r x => by
      show hequiv (r • x) = r • hequiv x
      simp [Algebra.smul_def, map_mul])
  rw [hlinequiv]
  exact AdjoinRoot.finrank hq.ne_zero

/-- **The ramified closed point is never a rational point when `q.natDegree ≥ 2`.**
Residue degree mismatch. (When `q.natDegree = 1`, the existing rational-point
machinery already handles it — this general construction is only needed for `q.
natDegree ≥ 2`, but the statement holds unconditionally whenever `q.natDegree ≠ 1`.) -/
theorem ramifiedFiberHeightOne_ne_pointHeightOne' [IsDedekindDomain (CoordinateRing H)]
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
      rw [hshift_ab, hshift_c] at hinf
      linarith
    -- **§1's unit-gcd fact**, for this specific witness triple.
    have hgu : IsUnit (gcd (gcd a₀ b₀) c₀) :=
      gcd_unit_of_reduce_ordAtFrac_triple a b c a₀ b₀ c₀ hcne hgne ha_eq hb_eq hc_eq
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
    have hbeq0 : b₀ = 0 := by
      exact b_eq_zero_of_rationalized_pole_bounded
        a₀ b₀ c₀ hinf₀ hcdeg
    subst b₀
    -- **§2: `IsNormCoprime`**, now that `b₀ = 0`.
    have hnc : IsNormCoprime H a₀ 0 c₀ := isNormCoprime_of_gcd_unit_snd_zero a₀ c₀ hgu
    -- **§3: `IsPoleBoundedAtPairSpec x₁ x₂ a₀ 0 c₀ 0`**, transported from
    -- `hzsuppSpec` (closed-point-native, for `(a,b,c,0)`) down to `(a₀,0,c₀,0)`
    -- via the same `g`-cancellation identity used for `hzsupp₀` above, redone
    -- at the `ordAtSpec` level.
    have hzsuppSpec₀ : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
        ordAtSpec v a₀ 0 - ordAtSpec v c₀ (0 : k[X]) ≥
          -((if v = pointHeightOne' x₁ then 1 else 0) +
            (if v = pointHeightOne' x₂ then 1 else 0)) := by
      intro v
      have hv := hzsuppSpec v
      rwa [ordAtSpec_sub_ordAtSpec_eq_of_polePairToFraction_eq (H := H) v a b c 0 a₀ 0 c₀ 0
        hab_ne hc0_ne' hc₀0_ne hfrac_eq₀] at hv
    have habpb : IsPoleBoundedAtPairSpec x₁ x₂ a₀ 0 c₀ (0 : k[X]) :=
      ⟨fun h => hc₀ne h.1, hinf₀, hzsuppSpec₀⟩
    have hcdeg1 : c₀.natDegree ≤ 1 :=
      natDegree_le_one_of_isPoleBoundedAtPairSpec_isNormCoprime
        (H := H) x₁ x₂ a₀ 0 c₀ hc₀ne hnc habpb
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
      exact false_of_root_of_isCoprimeAtRoots_zero_snd_general
        (H := H) hchar hsf x₁ x₂ hne a₀ c₀ hc₀ne hcop hzsupp₀ hzsuppSpec₀ α hα
    have hadeg0 : a₀.natDegree = 0 := by
      have habne0 : a₀ ≠ 0 := by
        intro ha0; apply hab₀_ne; simp [ha0, toPair_eq_zero_iff]
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
