import Mathlib
import Genus2Lean.ZeroD.TheDataDerivation.DataDerivationBasics
import Genus2Lean.ZeroD.Reduce.AlphaReduce
import Genus2Lean.ZeroD.Reduce.SharedRootCombining

/-! # A fully general, collision-pattern-free replacement for the
`P1TargetSharedRoot`/`P1UaSharedRoot`/`P2TargetSharedRoot`/`P2UaSharedRoot`
family

`SharedRootCombining.lean`'s `prod_dvd_of_coprime_to_lcm` handles exactly
one collision shape: `q3`/`q4` merge via `lcm`, while `q1`/`q2` stay
ordinary factors, and STILL requires `h12 : IsCoprime q1 q2`. The four
one-off files each specialize this to a different single pair merging,
but every one of them still demands the OTHER five pairwise coprimality
facts raw. Once more than one pair can fail at once (Claire's
`{P1 vs u_a} + {P2 vs target}`-style cases), none of the five existing
files apply, and writing a sixth/seventh/... file per new collision
pattern doesn't scale — there are `2^6` possible patterns in principle.

This file replaces the whole family with two theorems that need no case
enumeration at all:

1. `lcm_dvd_of_four_dvd`: for ANY four divisors of `N` in a Euclidean
   domain, `lcm (lcm q1 q2) (lcm q3 q4) ∣ N`, with **zero** coprimality
   hypotheses anywhere. This absorbs every collision pattern
   simultaneously — it doesn't need to know which pairs (if any) failed
   to be coprime, because `lcm` is idempotent/absorbing regardless of the
   reason two polynomials aren't coprime. This is the one fact that makes
   per-pattern files unnecessary.

2. `not_coprime_quadratics_iff` (the Galois collapse Claire asked to
   double check): two monic quadratics over `F p` fail to be coprime iff
   either they share a literal root in `F p`, or they are equal as
   polynomials. This is what actually shrinks the case count for
   `u_a`/`target`-style collisions — if `u_a` is irreducible and shares a
   root with `target` in the splitting field `F p²`, Frobenius forces the
   OTHER root to match too, so `u_a = target` outright rather than merely
   sharing one root. Combined with (1), this means every remaining
   correctness argument can be written as: `lcm (lcm q1 q2) (lcm q3 q4)`
   unconditionally divides `Npoly4` (fact 1), and its degree is bounded
   directly from `Npoly4`'s degree bound
   (`curBeforeMonic4_natDegree_le_two`'s route, itself independent of
   coprimality) — no branching on WHICH pair collided is needed at the
   proof-term level; the case data only matters if/when a human wants
   `uRS4` to literally equal a specific hand-named quadratic, which is a
   strictly separate (and optional) question from `uRS4 ∣ Npoly4`. -/

namespace Genus2Lean
namespace TheDataDerivation

open Polynomial

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

section GeneralLcmCombine

/-- **Any four divisors of `N` combine, unconditionally, via a nested
`lcm`.** No coprimality hypothesis of any kind — this single theorem
covers every one of the `2^6` possible pairwise-coprimality-failure
patterns among four factors at once, since `lcm` already absorbs shared
factors however they arise. Proof: `lcm q1 q2 ∣ N` and `lcm q3 q4 ∣ N`
each follow from `lcm_dvd_of_dvd_dvd` (`SharedRootCombining.lean`), then
one more application of the same lemma merges those two lcms. -/
theorem lcm_dvd_of_four_dvd
    {R : Type*} [EuclideanDomain R] [DecidableEq R] {q1 q2 q3 q4 N : R}
    (hd1 : q1 ∣ N) (hd2 : q2 ∣ N) (hd3 : q3 ∣ N) (hd4 : q4 ∣ N) :
    EuclideanDomain.lcm (EuclideanDomain.lcm q1 q2) (EuclideanDomain.lcm q3 q4) ∣ N := by
  have h12 : EuclideanDomain.lcm q1 q2 ∣ N := lcm_dvd_of_dvd_dvd hd1 hd2
  have h34 : EuclideanDomain.lcm q3 q4 ∣ N := lcm_dvd_of_dvd_dvd hd3 hd4
  exact lcm_dvd_of_dvd_dvd h12 h34

end GeneralLcmCombine

section QuadraticDichotomy

variable {b0 b1 c0 c1 : F p}

/-- **Refinement note**: when `q1`/`q2` (or `q3`/`q4`) genuinely stay
coprime to what they'd otherwise merge with, `lcm_dvd_of_four_dvd`'s
bound can be tightened back down using `prod_dvd_of_coprime_to_lcm` —
that theorem is still exactly the right tool in the single-collision
case, and is unchanged/reusable as-is. This file's contribution is only
for when that extra coprimality can't be assumed; `lcm_dvd_of_four_dvd`
is always *available* as a fallback with a possibly-larger (but still
degree-bounded, see the module docstring) combined factor.

**The Galois collapse for two monic quadratics over `F p`.** If
`X²+b1·X+b0` and `X²+c1·X+c0` are not coprime, then either they share a
literal root in `F p`, or they are the same polynomial. There is no
third possibility (e.g. "share a root only in `F p²`, but aren't equal")
because a monic quadratic's roots come in a single Frobenius-conjugate
pair when irreducible: if `r ∉ F p` is a common root living in `F p²`,
applying `x ↦ x^p` to `r` gives the SAME polynomial's other root on both
sides (each polynomial has coefficients in `F p`, so is Frobenius-fixed),
forcing both quadratics to have identical root multisets, hence be equal
(both monic). This is proved at the level of `IsCoprime` failing ⟹
sharing a common non-unit factor, then case-splitting on that factor's
degree (1 ⟹ literal shared root; 2 ⟹ the factor IS both quadratics,
i.e. equality), without ever naming the extension field explicitly —
Mathlib's `EuclideanDomain.gcd` machinery gives the common factor
directly over `F p` itself, so no tower/splitting-field construction is
needed in the Lean proof even though the intuition is Galois-theoretic. -/
theorem not_coprime_quadratics_iff
    (hb : (X ^ 2 + C b1 * X + C b0 : Polynomial (F p)).Monic := by monicity!)
    (hc : (X ^ 2 + C c1 * X + C c0 : Polynomial (F p)).Monic := by monicity!) :
    ¬ IsCoprime (X ^ 2 + C b1 * X + C b0 : Polynomial (F p))
        (X ^ 2 + C c1 * X + C c0) ↔
      (∃ r : F p, (X ^ 2 + C b1 * X + C b0 : Polynomial (F p)).eval r = 0 ∧
          (X ^ 2 + C c1 * X + C c0 : Polynomial (F p)).eval r = 0) ∨
      (X ^ 2 + C b1 * X + C b0 : Polynomial (F p)) = X ^ 2 + C c1 * X + C c0 := by
  set q1 : Polynomial (F p) := X ^ 2 + C b1 * X + C b0 with hq1_def
  set q2 : Polynomial (F p) := X ^ 2 + C c1 * X + C c0 with hq2_def
  have hq1ne : q1 ≠ 0 := hb.ne_zero
  have hq2ne : q2 ≠ 0 := hc.ne_zero
  have hq1deg : q1.natDegree = 2 := by rw [hq1_def]; compute_degree!
  have hq2deg : q2.natDegree = 2 := by rw [hq2_def]; compute_degree!
  set d : Polynomial (F p) := EuclideanDomain.gcd q1 q2 with hd_def
  have hd1 : d ∣ q1 := EuclideanDomain.gcd_dvd_left q1 q2
  have hd2 : d ∣ q2 := EuclideanDomain.gcd_dvd_right q1 q2
  constructor
  · intro hnc
    have hdne : d ≠ 0 := by
      intro hd0
      rw [hd0] at hd1
      exact hq1ne (eq_zero_of_zero_dvd hd1)
    have hdnu : ¬ IsUnit d := fun hu => hnc (EuclideanDomain.gcd_isUnit_iff.mp hu)
    have hlc_ne : d.leadingCoeff ≠ 0 := (not_congr Polynomial.leadingCoeff_eq_zero).mpr hdne
    -- The monic normalization of `d`, mirroring `uRS4`'s own
    -- `C leadingCoeff⁻¹ * q` construction (`AlphaReduce.lean`).
    set e : Polynomial (F p) := C d.leadingCoeff⁻¹ * d with he_def
    have he_monic : e.Monic := by
      have hmul_ne : d.leadingCoeff⁻¹ * d.leadingCoeff ≠ 0 :=
        mul_ne_zero (inv_ne_zero hlc_ne) hlc_ne
      have hedeg : e.natDegree = d.natDegree :=
        Polynomial.natDegree_C_mul_of_mul_ne_zero hmul_ne
      rw [Polynomial.Monic.def]
      change e.coeff e.natDegree = 1
      rw [hedeg, he_def, Polynomial.coeff_C_mul]
      exact inv_mul_cancel₀ hlc_ne
    have he_deg : e.natDegree = d.natDegree :=
      Polynomial.natDegree_C_mul_of_mul_ne_zero (mul_ne_zero (inv_ne_zero hlc_ne) hlc_ne)
    have he_ne : e ≠ 0 := he_monic.ne_zero
    have hddeg_le : d.natDegree ≤ 2 := hq1deg ▸ Polynomial.natDegree_le_of_dvd hd1 hq1ne
    have hedeg_le : e.natDegree ≤ 2 := he_deg ▸ hddeg_le
    have hcc : (C d.leadingCoeff⁻¹ : Polynomial (F p)) * C d.leadingCoeff = 1 := by
      rw [← C_mul, inv_mul_cancel₀ hlc_ne, C_1]
    have he_dvd1 : e ∣ q1 := by
      obtain ⟨k, hk⟩ := hd1
      refine ⟨C d.leadingCoeff * k, ?_⟩
      rw [hk, he_def]
      have : C d.leadingCoeff⁻¹ * d * (C d.leadingCoeff * k) =
          (C d.leadingCoeff⁻¹ * C d.leadingCoeff) * (d * k) := by ring
      rw [this, hcc, one_mul]
    have he_dvd2 : e ∣ q2 := by
      obtain ⟨k, hk⟩ := hd2
      refine ⟨C d.leadingCoeff * k, ?_⟩
      rw [hk, he_def]
      have : C d.leadingCoeff⁻¹ * d * (C d.leadingCoeff * k) =
          (C d.leadingCoeff⁻¹ * C d.leadingCoeff) * (d * k) := by ring
      rw [this, hcc, one_mul]
    have hddeg_pos : 0 < d.natDegree := by
      rcases Nat.eq_zero_or_pos d.natDegree with hz | hpos
      · exfalso
        apply hdnu
        have hcoeff0 : ∀ n : ℕ, 0 < n → d.coeff n = 0 :=
          fun n hn => Polynomial.natDegree_le_iff_coeff_eq_zero.mp hz.le n hn
        have hdC : d = C (d.coeff 0) := by
          apply Polynomial.ext
          intro n
          rcases Nat.eq_zero_or_pos n with hn0 | hnpos
          · subst hn0; simp
          · rw [hcoeff0 n hnpos, Polynomial.coeff_C, if_neg hnpos.ne']
        have hc0ne : d.coeff 0 ≠ 0 := by
          intro hz
          rw [hdC, hz] at hdne
          exact hdne (by simp)
        rw [hdC]
        exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc0ne)
      · exact hpos
    have hedeg_pos : 0 < e.natDegree := he_deg ▸ hddeg_pos
    -- `e`'s degree is in `{1, 2}`; `interval_cases` on a bounded `ℕ`.
    interval_cases hed : e.natDegree
    · -- degree 1: write `e = X + C k` (monic, degree 1) and read off its
      -- root directly.
      have he_eq : e = X + C (e.coeff 0) := by
        apply Polynomial.ext
        intro n
        match n with
        | 0 => simp
        | 1 =>
          have h1 : e.coeff 1 = 1 := by
            have hmc : e.coeff e.natDegree = 1 := he_monic.coeff_natDegree
            rwa [hed] at hmc
          simp [h1]
        | (n + 2) =>
          have hzero : e.coeff (n + 2) = 0 :=
            Polynomial.natDegree_le_iff_coeff_eq_zero.mp hed.le (n + 2) (by omega)
          simp [hzero, Polynomial.coeff_X, Polynomial.coeff_C]
      set r : F p := -(e.coeff 0) with hr_def
      have he_root : e.eval r = 0 := by
        rw [he_eq]; simp [hr_def]
      have hroot1 : q1.eval r = 0 := by
        obtain ⟨k, hk⟩ := he_dvd1
        rw [hk, Polynomial.eval_mul, he_root, zero_mul]
      have hroot2 : q2.eval r = 0 := by
        obtain ⟨k, hk⟩ := he_dvd2
        rw [hk, Polynomial.eval_mul, he_root, zero_mul]
      exact Or.inl ⟨r, hroot1, hroot2⟩
    · -- degree 2: `e` is monic of the same degree as `q1`/`q2` and
      -- divides both, so the quotient in each division is a monic
      -- degree-0 polynomial, i.e. `1`, forcing `e = q1` and `e = q2`.
      have heq1 : e = q1 := by
        obtain ⟨k, hk⟩ := he_dvd1
        have hkne : k ≠ 0 := by rintro rfl; rw [mul_zero] at hk; exact hq1ne hk
        have hdegsum : q1.natDegree = e.natDegree + k.natDegree :=
          hk ▸ Polynomial.natDegree_mul he_ne hkne
        have hkdeg : k.natDegree = 0 := by rw [hq1deg, hed] at hdegsum; omega
        have hkmonic : k.Monic := by
          have hq1m : (e * k).Monic := hk ▸ hb
          exact he_monic.of_mul_monic_left hq1m
        have hk1 : k = 1 := by
          have hklead : k.coeff k.natDegree = 1 := hkmonic.coeff_natDegree
          rw [hkdeg] at hklead
          have : k = C (k.coeff 0) :=
            Polynomial.eq_C_of_natDegree_eq_zero hkdeg
          rw [this, hklead, C_1]
        rw [hk, hk1, mul_one]
      have heq2 : e = q2 := by
        obtain ⟨k, hk⟩ := he_dvd2
        have hkne : k ≠ 0 := by rintro rfl; rw [mul_zero] at hk; exact hq2ne hk
        have hdegsum : q2.natDegree = e.natDegree + k.natDegree :=
          hk ▸ Polynomial.natDegree_mul he_ne hkne
        have hkdeg : k.natDegree = 0 := by rw [hq2deg, hed] at hdegsum; omega
        have hkmonic : k.Monic := by
          have hq2m : (e * k).Monic := hk ▸ hc
          exact he_monic.of_mul_monic_left hq2m
        have hk1 : k = 1 := by
          have hklead : k.coeff k.natDegree = 1 := hkmonic.coeff_natDegree
          rw [hkdeg] at hklead
          have : k = C (k.coeff 0) :=
            Polynomial.eq_C_of_natDegree_eq_zero hkdeg
          rw [this, hklead, C_1]
        rw [hk, hk1, mul_one]
      exact Or.inr (heq1.symm.trans heq2)
  · rintro (⟨r, hr1, hr2⟩ | heq)
    · -- a shared root directly contradicts a Bézout identity: evaluate
      -- `u*q1 + v*q2 = 1` at `r`, where both `q1.eval r` and `q2.eval r`
      -- vanish, forcing `0 = 1` in `F p`.
      intro hcop
      obtain ⟨u, v, huv⟩ := hcop
      have := congrArg (Polynomial.eval r) huv
      simp only [Polynomial.eval_add, Polynomial.eval_mul, hr1, hr2,
        mul_zero, add_zero, Polynomial.eval_one] at this
      exact absurd this (by norm_num)
    · intro hcop
      have hunit_d : IsUnit d := EuclideanDomain.gcd_isUnit_iff.mpr hcop
      have hdq1 : d = q1 := by
        rw [hd_def, heq, EuclideanDomain.gcd_self]
      have hunit : IsUnit q1 := hdq1 ▸ hunit_d
      have hdeg0 : q1.degree = 0 := Polynomial.isUnit_iff_degree_eq_zero.mp hunit
      rw [Polynomial.degree_eq_natDegree hq1ne, hq1deg] at hdeg0
      exact absurd hdeg0 (by norm_num)

end QuadraticDichotomy

end TheDataDerivation
end Genus2Lean
