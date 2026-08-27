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
   sharing one root.

The rest of the file (`GeneralQuotient`/`GeneralOutput`/
`MumfordIdentity4General`/`ReduceGeneral4`) is the actual wiring that uses
fact (1) to eliminate `h12`–`h34` as blockers on `AlphaReduce.lean`'s
correctness/output pipeline, without touching `AlphaReduce.lean` itself:

- `npoly4Lcm4` (`GeneralQuotient`): the four raw `Npoly4` factors combined
  via monic-normalized `lcm` instead of sequential `/ₘ` — divides `Npoly4`
  UNCONDITIONALLY (`npoly4Lcm4_dvd_Npoly4`, zero `IsCoprime` hypotheses).
- `curBeforeMonic4General`/`uRS4General`/`vRS4General` (`GeneralOutput`):
  ports of `curBeforeMonic4`/`uRS4`/`vRS4`, built on `npoly4Lcm4` instead
  of the four-step `/ₘ` chain, so `uRS4General ∣ Npoly4` holds
  unconditionally too (`uRS4General_dvd_Npoly4`) — this is the genuine fix,
  not a repackaging: `uRS4`/`curBeforeMonic4` themselves are silently
  WRONG (drop a remainder) whenever any of `h12`–`h34` fails, since their
  `/ₘ`-chain only computes the true quotient under pairwise coprimality;
  `uRS4General` sidesteps this by construction rather than by assumption.
- `vRS4General_sq_eq_f_mod_uRS4General` (`MumfordIdentity4General`): the
  Mumford identity for the general objects, `h12`–`h34`-free.
- `ReduceGeneral` (`ReduceGeneral4`): `Reduce`'s output read off the
  general objects. Note `Reduce` itself never took `h12`–`h34` directly
  (confirmed by inspection — only `hcur`/`hgcd`, a different, still-needed
  pair of hypotheses unrelated to the six); what was missing was a
  correctness proof for that output that didn't secretly need them, which
  `uRS4General_dvd_Npoly4`/`vRS4General_sq_eq_f_mod_uRS4General` supply. -/

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

/-! ## `uRS4General`/`vRS4General`: infrastructure for zero-blocking-
hypothesis correctness

This section is the actual wiring `AlphaReduce.lean`'s `uRS4`/`vRS4` are
missing. `uRS4` is `curBeforeMonic4` monic-normalized, and
`curBeforeMonic4` is a SEQUENTIAL `/ₘ` chain by the four raw factors
`(X-P1.1)`, `(X-P2.1)`, `u_a`, `target` — that chain only computes the
true quotient (i.e. only has zero remainder at every step) when the four
factors are pairwise coprime, which is exactly what `h12`–`h34` assert.
If any pair fails, `curBeforeMonic4` as currently defined silently drops
a remainder and becomes the WRONG polynomial — not a false theorem
anywhere, just a quotient that no longer satisfies `uRS4 ∣ Npoly4`.

The fix here does not touch `curBeforeMonic4`/`uRS4` (both left exactly
as `AlphaReduce.lean` defines them, so nothing existing changes). Instead:
combine the four factors via their (monic-normalized) `lcm` rather than
their product/sequential `/ₘ` chain. `lcm_dvd_of_four_dvd` (above) already
proves `lcm(lcm(q1,q2),lcm(q3,q4)) ∣ N` completely unconditionally — no
`h12`–`h34` anywhere — because `EuclideanDomain.lcm` absorbs shared roots
regardless of why two polynomials fail to be coprime. The one piece that
section didn't need but this one does: `EuclideanDomain.lcm` is only
defined up to a unit (Mathlib has no monic-normalization guarantee for
it, confirmed against `Polynomial.divByMonic_eq_of_not_monic`'s existence
— dividing by a non-monic polynomial is NOT genuine Euclidean division,
so a further `/ₘ` step needs actual monicity, not just "an lcm"). This
section normalizes the lcm by the same `leadingCoeff⁻¹`-rescaling trick
`uRS4` already uses on `curBeforeMonic4`, applied to the lcm itself. -/

section GeneralQuotient

variable (c0 c1 c2 c3 c4 : F p) (P1 P2 : F p × F p) (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)

/-- The four raw factors' `lcm`, nested exactly as `lcm_dvd_of_four_dvd`
combines them (`lcm (lcm q1 q2) (lcm q3 q4)`), NOT yet monic-normalized —
`EuclideanDomain.lcm`'s output is only an associate of the "true" monic
lcm. `npoly4Lcm4` (below) is the normalized version callers should
actually use; this raw form is kept separate purely so
`npoly4Lcm4_dvd_Npoly4`'s proof can cite `lcm_dvd_of_four_dvd` directly
without re-deriving the nested-lcm shape inline. -/
noncomputable def npoly4LcmRaw : Polynomial (F p) :=
  EuclideanDomain.lcm
    (EuclideanDomain.lcm (X - C P1.1 : Polynomial (F p)) (X - C P2.1))
    (EuclideanDomain.lcm (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
      (X ^ 2 + C u1 * X + C u0))

/-- `npoly4LcmRaw ≠ 0` — all four base factors are monic, hence nonzero,
and `EuclideanDomain.lcm_eq_zero_iff` propagates that through both nested
`lcm`s. Needed so the `leadingCoeff⁻¹` rescaling below is a genuine unit
scaling (mirrors `uRS4_monic`'s own `hcur`/`hne`-style precondition, but
proved outright here rather than assumed, since none of the four base
factors can ever be zero — they're monic by construction). -/
theorem npoly4LcmRaw_ne_zero :
    npoly4LcmRaw p P1 P2 ua0 ua1 u0 u1 ≠ 0 := by
  have hm1 : (X - C P1.1 : Polynomial (F p)).Monic := Polynomial.monic_X_sub_C _
  have hm2 : (X - C P2.1 : Polynomial (F p)).Monic := Polynomial.monic_X_sub_C _
  have hm3 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).Monic := by monicity!
  have hm4 : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).Monic := by monicity!
  intro hz
  unfold npoly4LcmRaw at hz
  rw [EuclideanDomain.lcm_eq_zero_iff] at hz
  rcases hz with hz | hz
  · rw [EuclideanDomain.lcm_eq_zero_iff] at hz
    rcases hz with hz | hz
    · exact hm1.ne_zero hz
    · exact hm2.ne_zero hz
  · rw [EuclideanDomain.lcm_eq_zero_iff] at hz
    rcases hz with hz | hz
    · exact hm3.ne_zero hz
    · exact hm4.ne_zero hz

/-- **The normalized (monic) combined-lcm quotient.** Same
`leadingCoeff⁻¹`-rescaling `uRS4`/`uRS4Tangent`/`uRS4LcmShared` all already
use, applied to `npoly4LcmRaw` instead of a `/ₘ`-chain quotient — this is
the object that plays `curBeforeMonic4`'s role but is defined
unconditionally (no coprimality anywhere in its own definition). -/
noncomputable def npoly4Lcm4 : Polynomial (F p) :=
  C (npoly4LcmRaw p P1 P2 ua0 ua1 u0 u1).leadingCoeff⁻¹ * npoly4LcmRaw p P1 P2 ua0 ua1 u0 u1

/-- `npoly4Lcm4` is monic — direct port of `uRS4_monic`'s proof, unchanged
in substance, applied to `npoly4LcmRaw` instead of `curBeforeMonic4`. -/
theorem npoly4Lcm4_monic :
    (npoly4Lcm4 p P1 P2 ua0 ua1 u0 u1).Monic := by
  simp only [npoly4Lcm4]
  set q := npoly4LcmRaw p P1 P2 ua0 ua1 u0 u1 with hq
  have hne : q ≠ 0 := npoly4LcmRaw_ne_zero p P1 P2 ua0 ua1 u0 u1
  have hlc : q.leadingCoeff ≠ 0 := (not_congr Polynomial.leadingCoeff_eq_zero).mpr hne
  have hau : q.leadingCoeff * q.leadingCoeff⁻¹ = 1 := mul_inv_cancel₀ hlc
  have hdeg : (C q.leadingCoeff⁻¹ * q).natDegree = q.natDegree :=
    Polynomial.natDegree_C_mul_eq_of_mul_eq_one hau
  rw [Polynomial.Monic.def]
  change (C q.leadingCoeff⁻¹ * q).coeff (C q.leadingCoeff⁻¹ * q).natDegree = 1
  rw [hdeg, Polynomial.coeff_C_mul]
  exact inv_mul_cancel₀ hlc

/-- **`npoly4Lcm4 ∣ Npoly4`, with NO coprimality hypotheses whatsoever** —
only the curve-membership/nondegeneracy/Mumford data `dvd_N_P1`/
`dvd_N_P2`/`dvd_N_ua`/`dvd_N_u4` already need on their own (all four are
unconditional given that data — confirmed by inspection, neither takes
any `IsCoprime` hypothesis). This is the theorem that actually removes
`h12`–`h34` as blockers on the DIVISIBILITY question — `lcm_dvd_of_four_dvd`
absorbs whichever pairs (if any) fail coprimality, since `lcm` doesn't
care why one polynomial divides another. Combined with `npoly4Lcm4_monic`,
this is the unconditional replacement for `uRS4_dvd_Npoly4`. -/
theorem npoly4Lcm4_dvd_Npoly4
    (hA : MatrixNondegenerate4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hP1_curve : P1.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P1.1)
    (hP2_curve : P2.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P2.1)
    (hMumfordUa : IsMumfordUa p c0 c1 c2 c3 c4 ua0 ua1 va0 va1)
    (hMumfordTarget : IsMumfordTarget4 p c0 c1 c2 c3 c4 u0 u1 v0 v1) :
    npoly4Lcm4 p P1 P2 ua0 ua1 u0 u1 ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 := by
  have hd1 := dvd_N_P1 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hA hP1_curve
  have hd2 := dvd_N_P2 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hA hP2_curve
  have hd3 := dvd_N_ua p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hA hMumfordUa
  have hd4 := dvd_N_u4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hA hMumfordTarget
  have hraw : npoly4LcmRaw p P1 P2 ua0 ua1 u0 u1 ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 := by
    simpa only [npoly4LcmRaw] using
      lcm_dvd_of_four_dvd (R := Polynomial (F p)) hd1 hd2 hd3 hd4
  -- `npoly4Lcm4` is `npoly4LcmRaw` scaled by a unit (its leading
  -- coefficient's inverse, valid since `npoly4LcmRaw ≠ 0`), so
  -- divisibility transfers directly.
  obtain ⟨m, hm⟩ := hraw
  simp only [npoly4Lcm4]
  refine ⟨C (npoly4LcmRaw p P1 P2 ua0 ua1 u0 u1).leadingCoeff * m, ?_⟩
  rw [hm]
  have hlc : (npoly4LcmRaw p P1 P2 ua0 ua1 u0 u1).leadingCoeff ≠ 0 :=
    (not_congr Polynomial.leadingCoeff_eq_zero).mpr (npoly4LcmRaw_ne_zero p P1 P2 ua0 ua1 u0 u1)
  have hscale :
      (C (npoly4LcmRaw p P1 P2 ua0 ua1 u0 u1).leadingCoeff⁻¹ *
        npoly4LcmRaw p P1 P2 ua0 ua1 u0 u1) *
      (C (npoly4LcmRaw p P1 P2 ua0 ua1 u0 u1).leadingCoeff * m) =
      C ((npoly4LcmRaw p P1 P2 ua0 ua1 u0 u1).leadingCoeff⁻¹ *
        (npoly4LcmRaw p P1 P2 ua0 ua1 u0 u1).leadingCoeff) *
      (npoly4LcmRaw p P1 P2 ua0 ua1 u0 u1 * m) := by
    simp only [map_mul]; ring
  rw [hscale, inv_mul_cancel₀ hlc, map_one, one_mul]

/-- `npoly4Lcm4`'s degree is `≤ 6`: each nested `lcm` divides the product
of its two monic arguments (`EuclideanDomain.lcm_dvd` applied to
`dvd_mul_right`/`dvd_mul_left` witnesses), so its degree is `≤` that
product's, and monic `natDegree_le_of_dvd` bounds it from there — `≤ 2`
for `lcm q1 q2` (two linear factors) and `≤ 4` for `lcm q3 q4` (two
quadratics), giving `≤ 6` overall. Mirrors `curBeforeMonic4_natDegree_le_two`'s
role, but bounding `npoly4Lcm4` (degree ≤ 6, since nothing here divides
that lcm further by the two known quadratics the way `curBeforeMonic4`
does) rather than a fully-quotiented `≤ 2` object — this is the honest
degree bound for the object that's actually unconditional. -/
theorem npoly4Lcm4_natDegree_le_six :
    (npoly4Lcm4 p P1 P2 ua0 ua1 u0 u1).natDegree ≤ 6 := by
  have hm1 : (X - C P1.1 : Polynomial (F p)).Monic := Polynomial.monic_X_sub_C _
  have hm2 : (X - C P2.1 : Polynomial (F p)).Monic := Polynomial.monic_X_sub_C _
  have hm3 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).Monic := by monicity!
  have hm4 : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).Monic := by monicity!
  have h12dvd : EuclideanDomain.lcm (X - C P1.1 : Polynomial (F p)) (X - C P2.1) ∣
      (X - C P1.1) * (X - C P2.1) :=
    EuclideanDomain.lcm_dvd (dvd_mul_right _ _) (dvd_mul_left _ _)
  have h34dvd : EuclideanDomain.lcm (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
      (X ^ 2 + C u1 * X + C u0) ∣
      (X ^ 2 + C ua1 * X + C ua0) * (X ^ 2 + C u1 * X + C u0) :=
    EuclideanDomain.lcm_dvd (dvd_mul_right _ _) (dvd_mul_left _ _)
  have h12ne : ((X - C P1.1 : Polynomial (F p)) * (X - C P2.1)) ≠ 0 :=
    mul_ne_zero hm1.ne_zero hm2.ne_zero
  have h34ne : ((X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) * (X ^ 2 + C u1 * X + C u0)) ≠ 0 :=
    mul_ne_zero hm3.ne_zero hm4.ne_zero
  have hdeg12 : (EuclideanDomain.lcm (X - C P1.1 : Polynomial (F p)) (X - C P2.1)).natDegree ≤ 2 := by
    have := Polynomial.natDegree_le_of_dvd h12dvd h12ne
    have heq : ((X - C P1.1 : Polynomial (F p)) * (X - C P2.1)).natDegree = 2 := by
      rw [Polynomial.natDegree_mul hm1.ne_zero hm2.ne_zero,
        Polynomial.natDegree_X_sub_C, Polynomial.natDegree_X_sub_C]
    omega
  have hdeg34 : (EuclideanDomain.lcm (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
      (X ^ 2 + C u1 * X + C u0)).natDegree ≤ 4 := by
    have := Polynomial.natDegree_le_of_dvd h34dvd h34ne
    have heq : ((X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) *
        (X ^ 2 + C u1 * X + C u0)).natDegree = 4 := by
      rw [Polynomial.natDegree_mul hm3.ne_zero hm4.ne_zero]
      have e3 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).natDegree = 2 := by compute_degree!
      have e4 : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).natDegree = 2 := by compute_degree!
      rw [e3, e4]
    omega
  have hrawdeg : (npoly4LcmRaw p P1 P2 ua0 ua1 u0 u1).natDegree ≤ 6 := by
    have hlcmdvd : EuclideanDomain.lcm
        (EuclideanDomain.lcm (X - C P1.1 : Polynomial (F p)) (X - C P2.1))
        (EuclideanDomain.lcm (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
          (X ^ 2 + C u1 * X + C u0)) ∣
        (EuclideanDomain.lcm (X - C P1.1 : Polynomial (F p)) (X - C P2.1)) *
          (EuclideanDomain.lcm (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
            (X ^ 2 + C u1 * X + C u0)) :=
      EuclideanDomain.lcm_dvd (dvd_mul_right _ _) (dvd_mul_left _ _)
    have hne12 : EuclideanDomain.lcm (X - C P1.1 : Polynomial (F p)) (X - C P2.1) ≠ 0 := by
      intro hz
      rw [EuclideanDomain.lcm_eq_zero_iff] at hz
      rcases hz with hz | hz
      · exact hm1.ne_zero hz
      · exact hm2.ne_zero hz
    have hne34 : EuclideanDomain.lcm (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
        (X ^ 2 + C u1 * X + C u0) ≠ 0 := by
      intro hz
      rw [EuclideanDomain.lcm_eq_zero_iff] at hz
      rcases hz with hz | hz
      · exact hm3.ne_zero hz
      · exact hm4.ne_zero hz
    have hprodne : (EuclideanDomain.lcm (X - C P1.1 : Polynomial (F p)) (X - C P2.1)) *
        (EuclideanDomain.lcm (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
          (X ^ 2 + C u1 * X + C u0)) ≠ 0 := mul_ne_zero hne12 hne34
    have hb := Polynomial.natDegree_le_of_dvd hlcmdvd hprodne
    have heq : ((EuclideanDomain.lcm (X - C P1.1 : Polynomial (F p)) (X - C P2.1)) *
        (EuclideanDomain.lcm (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
          (X ^ 2 + C u1 * X + C u0))).natDegree ≤ 6 := by
      have := Polynomial.natDegree_mul_le (p := EuclideanDomain.lcm
        (X - C P1.1 : Polynomial (F p)) (X - C P2.1))
        (q := EuclideanDomain.lcm (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
          (X ^ 2 + C u1 * X + C u0))
      omega
    simp only [npoly4LcmRaw]
    omega
  simp only [npoly4Lcm4]
  set q := npoly4LcmRaw p P1 P2 ua0 ua1 u0 u1 with hq
  have hne : q ≠ 0 := npoly4LcmRaw_ne_zero p P1 P2 ua0 ua1 u0 u1
  have hlc : q.leadingCoeff ≠ 0 := (not_congr Polynomial.leadingCoeff_eq_zero).mpr hne
  have hau : q.leadingCoeff⁻¹ * q.leadingCoeff ≠ 0 := mul_ne_zero (inv_ne_zero hlc) hlc
  have hdeg : (C q.leadingCoeff⁻¹ * q).natDegree = q.natDegree :=
    Polynomial.natDegree_C_mul_of_mul_ne_zero hau
  rw [hdeg]
  exact hrawdeg

end GeneralQuotient

/-! ## `curBeforeMonic4General`/`uRS4General`/`vRS4General`: the actual
degree-`≤2` output, unconditional

`npoly4Lcm4` (degree `≤ 6`) is already an unconditional divisor of
`Npoly4`, but it's the WRONG shape for `Reduce`'s output — `uRS4`/`vRS4`
need to be `Npoly4`'s reduction, degree `≤ 2` (one more `/ₘ` step, exactly
mirroring `curBeforeMonic4`'s relationship to `Npoly4`, just dividing by
`npoly4Lcm4` in one step instead of by the four raw factors in sequence).
Since `npoly4Lcm4_monic` is unconditional, this single `/ₘ` step is
always genuine Euclidean division — no coprimality needed anywhere. -/

section GeneralOutput

variable (c0 c1 c2 c3 c4 : F p) (P1 P2 : F p × F p) (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)

/-- `Npoly4` divided by the normalized combined lcm — the unconditional
replacement for `curBeforeMonic4`. Always genuine Euclidean division
(`npoly4Lcm4` is monic unconditionally, `npoly4Lcm4_monic`), unlike
`curBeforeMonic4`'s four-step chain, which silently degrades if any pair
among `h12`–`h34` fails. -/
noncomputable def curBeforeMonic4General : Polynomial (F p) :=
  Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 /ₘ
    npoly4Lcm4 p P1 P2 ua0 ua1 u0 u1

/-- `curBeforeMonic4General`'s degree is `≤ 8`, unconditionally.

**Honest weaker bound than `curBeforeMonic4`'s `≤ 2`, not a typo.**
`Polynomial.natDegree_divByMonic` gives the EXACT formula
`(N /ₘ q).natDegree = N.natDegree - q.natDegree` for any monic `q`
(no divisibility of `q` into `N` needed for the formula itself), so
`curBeforeMonic4General.natDegree = Npoly4.natDegree - npoly4Lcm4.natDegree`.
`Npoly4_natDegree_le_eight` bounds the minuend; `npoly4Lcm4.natDegree`
needs a MATCHING LOWER bound (not the upper bound
`npoly4Lcm4_natDegree_le_six` proves) to get a tight `≤ 2` result via `ℕ`
subtraction, and no unconditional lower bound holds — e.g. `u_a = target`
exactly collapses `npoly4Lcm4` to degree 2, giving `curBeforeMonic4General`
degree up to `8 - 2 = 6` in that fully-degenerate case. So `≤ 2` is only
true generically (the same genericity `h12`–`h34` used to encode), while
`≤ 8` (just `Npoly4_natDegree_le_eight` plus `ℕ` subtraction never
increasing) is the honest unconditional bound. This is expected, not a
regression: `uRS4General` trades `uRS4`'s sharp-but-conditional `≤ 2`
bound for an unconditional-but-looser one, exactly mirroring how
`npoly4Lcm4` itself trades `curBeforeMonic4`'s implicit degree-6 product
for a possibly-smaller degree-≤6 lcm. -/
theorem curBeforeMonic4General_natDegree_le_eight :
    (curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).natDegree ≤ 8 := by
  have hmonic := npoly4Lcm4_monic p P1 P2 ua0 ua1 u0 u1
  have heq :
      (curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).natDegree =
        (Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).natDegree -
          (npoly4Lcm4 p P1 P2 ua0 ua1 u0 u1).natDegree := by
    simp only [curBeforeMonic4General]
    exact Polynomial.natDegree_divByMonic _ hmonic
  have h8 := Npoly4_natDegree_le_eight p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1
  omega

/-! ### Sharpening under `P1.1 ≠ P2.1`

`P1.1 ≠ P2.1` is not part of `curBeforeMonic4General`'s own definition
(matching `curBeforeMonic4`/`Reduce`, both unconditional in `P1`/`P2`),
but it IS always true on the path that actually reaches `Reduce`/
`ReduceGeneral`: `ReduceDispatch` routes `P1 = P2` to `ReduceTangent`
entirely, so `Reduce`/`ReduceGeneral` are only ever called with
`P1 ≠ P2` (hence `P1.1 ≠ P2.1`, since `P1 ≠ P2` for points ON A CURVE with
distinct `x`-coordinates — matching how `IsCoprime (X-C P1.1) (X-C P2.1)`,
i.e. `h12`, was always implicitly the "not the tangent case" condition
elsewhere in this file). Given that, the degree-6 slack in `npoly4Lcm4`
collapses to AT MOST the `u_a`-vs-`target` uncertainty alone — the linear
pair's `lcm` is always exactly degree 2 once `P1.1 ≠ P2.1`, since two
distinct-root monic linear polynomials are always coprime
(`Polynomial.isCoprime_X_sub_C_of_isUnit_sub`), so their `lcm` is (up to a
unit) their product, degree `1+1=2`, never less. -/

/-- The linear pair `(X-C P1.1)`/`(X-C P2.1)` is coprime whenever
`P1.1 ≠ P2.1` — direct application of `Polynomial.isCoprime_X_sub_C_of_isUnit_sub`,
using that `F p` is a field so `a - b ≠ 0 → IsUnit (a - b)`. -/
theorem isCoprime_linear_pair_of_ne (h : P1.1 ≠ P2.1) :
    IsCoprime (X - C P1.1 : Polynomial (F p)) (X - C P2.1) :=
  Polynomial.isCoprime_X_sub_C_of_isUnit_sub (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr h))

/-- `lcm(X-C P1.1, X-C P2.1)` has EXACT degree 2 whenever `P1.1 ≠ P2.1` —
coprime monic-linear factors' `lcm` is (up to a unit) their product, and
`EuclideanDomain.gcd_mul_lcm` plus coprimality (`gcd` a unit) pins the
`lcm` as an associate of the product `(X-C P1.1)*(X-C P2.1)`, degree
`1+1=2`; associates share `natDegree`. -/
theorem npoly4LcmLinearPair_natDegree_eq_two (P1 P2 : F p × F p) (h : P1.1 ≠ P2.1) :
    (EuclideanDomain.lcm (X - C P1.1 : Polynomial (F p)) (X - C P2.1)).natDegree = 2 := by
  have hm1 : (X - C P1.1 : Polynomial (F p)).Monic := Polynomial.monic_X_sub_C _
  have hm2 : (X - C P2.1 : Polynomial (F p)).Monic := Polynomial.monic_X_sub_C _
  have hcop := isCoprime_linear_pair_of_ne p P1 P2 h
  -- `IsCoprime` gives `gcd = 1` up to unit, and `gcd * lcm = q1 * q2`
  -- (`EuclideanDomain.gcd_mul_lcm`), so `lcm` is a unit multiple of
  -- `q1 * q2`, hence shares its `natDegree`.
  have hgcdunit : IsUnit (EuclideanDomain.gcd (X - C P1.1 : Polynomial (F p)) (X - C P2.1)) :=
    EuclideanDomain.gcd_isUnit_iff.mpr hcop
  have hprod := EuclideanDomain.gcd_mul_lcm (X - C P1.1 : Polynomial (F p)) (X - C P2.1)
  obtain ⟨u, hu⟩ := hgcdunit
  have hne1 : (X - C P1.1 : Polynomial (F p)) ≠ 0 := hm1.ne_zero
  have hne2 : (X - C P2.1 : Polynomial (F p)) ≠ 0 := hm2.ne_zero
  have hlcmne : (EuclideanDomain.lcm (X - C P1.1 : Polynomial (F p)) (X - C P2.1)) ≠ 0 := by
    rw [Ne, EuclideanDomain.lcm_eq_zero_iff]
    intro hz; rcases hz with hz | hz
    · exact hne1 hz
    · exact hne2 hz
  have hdeg : ((X - C P1.1 : Polynomial (F p)) * (X - C P2.1)).natDegree = 2 := by
    rw [Polynomial.natDegree_mul hne1 hne2, Polynomial.natDegree_X_sub_C, Polynomial.natDegree_X_sub_C]
  -- `u` (the unit realizing `gcd`) has `natDegree 0`: it divides `1`,
  -- so `natDegree_le_of_dvd` bounds it above by `natDegree 1 = 0`.
  have hune : (u : Polynomial (F p)) ≠ 0 := u.ne_zero
  have hudvd1 : (u : Polynomial (F p)) ∣ (1 : Polynomial (F p)) := u.isUnit.dvd
  have hudeg0 : (u : Polynomial (F p)).natDegree = 0 := by
    have hle := Polynomial.natDegree_le_of_dvd hudvd1 one_ne_zero
    simpa using hle
  -- `gcd * lcm = q1 * q2`, `gcd = ↑u`, both sides nonzero, so `natDegree_mul`
  -- on each side plus `hudeg0` pins down `lcm.natDegree`.
  have hlhs : (EuclideanDomain.gcd (X - C P1.1 : Polynomial (F p)) (X - C P2.1) *
      EuclideanDomain.lcm (X - C P1.1 : Polynomial (F p)) (X - C P2.1)).natDegree =
      (EuclideanDomain.lcm (X - C P1.1 : Polynomial (F p)) (X - C P2.1)).natDegree := by
    rw [← hu, Polynomial.natDegree_mul hune hlcmne, hudeg0, zero_add]
  rw [hprod, hdeg] at hlhs
  exact hlhs.symm

/-- The quadratic pair `u_a(X) = X²+ua1·X+ua0` / `target(X) = X²+u1·X+u0`
is coprime whenever they're not equal as polynomials AND share no root in
`F p` — the positive direction of `not_coprime_quadratics_iff`'s
dichotomy, phrased as its contrapositive. -/
theorem isCoprime_quadratic_pair_of_ne_of_no_shared_root
    (hne : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ≠ X ^ 2 + C u1 * X + C u0)
    (hnoroot : ¬ ∃ r : F p, (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval r = 0 ∧
        (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval r = 0) :
    IsCoprime (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) (X ^ 2 + C u1 * X + C u0) := by
  by_contra hnc
  rw [not_coprime_quadratics_iff p] at hnc
  rcases hnc with hroot | heq
  · exact hnoroot hroot
  · exact hne heq

/-- `lcm(u_a, target)` (the quadratic pair) has EXACT degree 4 whenever
`u_a ≠ target` as polynomials AND they share no root in `F p` — mirrors
`npoly4LcmLinearPair_natDegree_eq_two`'s proof one degree up (coprime
monic factors' `lcm` is a unit multiple of their product, degree `2+2=4`),
using `isCoprime_quadratic_pair_of_ne_of_no_shared_root` for the
coprimality half instead of `isCoprime_linear_pair_of_ne`. -/
theorem npoly4LcmQuadraticPair_natDegree_eq_four
    (hne : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ≠ X ^ 2 + C u1 * X + C u0)
    (hnoroot : ¬ ∃ r : F p, (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval r = 0 ∧
        (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval r = 0) :
    (EuclideanDomain.lcm (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
        (X ^ 2 + C u1 * X + C u0)).natDegree = 4 := by
  have hm3 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).Monic := by monicity!
  have hm4 : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).Monic := by monicity!
  have hcop := isCoprime_quadratic_pair_of_ne_of_no_shared_root p ua0 ua1 u0 u1 hne hnoroot
  have hgcdunit : IsUnit (EuclideanDomain.gcd (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
      (X ^ 2 + C u1 * X + C u0)) :=
    EuclideanDomain.gcd_isUnit_iff.mpr hcop
  have hprod := EuclideanDomain.gcd_mul_lcm (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
    (X ^ 2 + C u1 * X + C u0)
  obtain ⟨u, hu⟩ := hgcdunit
  have hne3 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ≠ 0 := hm3.ne_zero
  have hne4 : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)) ≠ 0 := hm4.ne_zero
  have hlcmne : (EuclideanDomain.lcm (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
      (X ^ 2 + C u1 * X + C u0)) ≠ 0 := by
    rw [Ne, EuclideanDomain.lcm_eq_zero_iff]
    intro hz; rcases hz with hz | hz
    · exact hne3 hz
    · exact hne4 hz
  have hdeg : ((X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) *
      (X ^ 2 + C u1 * X + C u0)).natDegree = 4 := by
    rw [Polynomial.natDegree_mul hne3 hne4]
    have e3 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).natDegree = 2 := by compute_degree!
    have e4 : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).natDegree = 2 := by compute_degree!
    rw [e3, e4]
  have hune : (u : Polynomial (F p)) ≠ 0 := u.ne_zero
  have hudvd1 : (u : Polynomial (F p)) ∣ (1 : Polynomial (F p)) := u.isUnit.dvd
  have hudeg0 : (u : Polynomial (F p)).natDegree = 0 := by
    have hle := Polynomial.natDegree_le_of_dvd hudvd1 one_ne_zero
    simpa using hle
  have hlhs : (EuclideanDomain.gcd (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
      (X ^ 2 + C u1 * X + C u0) *
      EuclideanDomain.lcm (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
        (X ^ 2 + C u1 * X + C u0)).natDegree =
      (EuclideanDomain.lcm (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
        (X ^ 2 + C u1 * X + C u0)).natDegree := by
    rw [← hu, Polynomial.natDegree_mul hune hlcmne, hudeg0, zero_add]
  rw [hprod, hdeg] at hlhs
  exact hlhs.symm

/-- `IsCoprime (X - C r) q` whenever `r` is not a root of `q` — the
linear-factor case of coprimality-from-no-shared-root, strictly simpler
than `not_coprime_quadratics_iff`'s quadratic-vs-quadratic dichotomy
(no Galois-collapse case to rule out: a linear factor's only possible
non-unit divisor is an associate of itself, so "not coprime" collapses
directly to "shares its unique root"). Any common divisor `d` of
`X - C r` and `q` divides the degree-1 polynomial `X - C r`, so
`d.natDegree ≤ 1`; if `d` is a non-unit, `d.natDegree = 1` exactly (a
nonzero degree-0 polynomial over a field is always a unit), forcing `d`
to be a unit multiple of `X - C r` itself (matching leading behavior via
`Polynomial.eq_of_dvd_of_natDegree_le_of_leadingCoeff`-style reasoning),
hence `r` is a root of `d`, hence of `q` (since `d ∣ q`) — contradicting
`hnoroot`. -/
theorem isCoprime_X_sub_C_of_not_isRoot {r : F p} {q : Polynomial (F p)}
    (hnoroot : q.eval r ≠ 0) :
    IsCoprime (X - C r : Polynomial (F p)) q := by
  set d : Polynomial (F p) := EuclideanDomain.gcd (X - C r) q with hd_def
  have hd1 : d ∣ (X - C r : Polynomial (F p)) := EuclideanDomain.gcd_dvd_left _ _
  have hd2 : d ∣ q := EuclideanDomain.gcd_dvd_right _ _
  rw [← EuclideanDomain.gcd_isUnit_iff, ← hd_def]
  by_contra hdnu
  have hlne : (X - C r : Polynomial (F p)) ≠ 0 := Polynomial.X_sub_C_ne_zero r
  have hddeg_le : d.natDegree ≤ 1 := by
    have := Polynomial.natDegree_le_of_dvd hd1 hlne
    rwa [Polynomial.natDegree_X_sub_C] at this
  have hdne : d ≠ 0 := by
    intro hd0; rw [hd0] at hd1; exact hlne (eq_zero_of_zero_dvd hd1)
  have hddeg1 : d.natDegree = 1 := by
    rcases Nat.lt_or_ge d.natDegree 1 with hlt | hge
    · exfalso; apply hdnu
      have hd0 : d.natDegree = 0 := by omega
      have hdC : d = C (d.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hd0
      have hc0ne : d.coeff 0 ≠ 0 := by
        intro hz; rw [hdC, hz] at hdne; exact hdne (by simp)
      rw [hdC]; exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc0ne)
    · omega
  -- `d` has the same degree as `X - C r` and divides it, so `d` is
  -- an associate of `X - C r` (up to a unit scalar): the quotient in
  -- `hd1` is degree-0, hence a nonzero constant, hence a unit.
  obtain ⟨k, hk⟩ := hd1
  have hkne : k ≠ 0 := by rintro rfl; rw [mul_zero] at hk; exact hlne hk
  have hkdeg : k.natDegree = 0 := by
    have hdegsum : (X - C r : Polynomial (F p)).natDegree = d.natDegree + k.natDegree :=
      hk ▸ Polynomial.natDegree_mul hdne hkne
    rw [Polynomial.natDegree_X_sub_C, hddeg1] at hdegsum
    omega
  have hkC : k = C (k.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hkdeg
  have hk0ne : k.coeff 0 ≠ 0 := by
    intro hz; rw [hkC, hz] at hkne; exact hkne (by simp)
  -- `r` is a root of `X - C r`, hence of `d * k = X - C r`; since
  -- `k.eval r ≠ 0` (a nonzero constant), `r` must be a root of `d`.
  have hroot_lin : (X - C r : Polynomial (F p)).eval r = 0 := by simp
  have hkeval_ne : k.eval r ≠ 0 := by rw [hkC]; simpa using hk0ne
  have hroot_d : d.eval r = 0 := by
    have := hroot_lin
    rw [hk, Polynomial.eval_mul] at this
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h hkeval_ne
  have hroot_q : q.eval r = 0 := by
    obtain ⟨m, hm⟩ := hd2
    rw [hm, Polynomial.eval_mul, hroot_d, zero_mul]
  exact hnoroot hroot_q

/-- `IsCoprime (lcm(X-C P1.1, X-C P2.1)) (lcm(u_a, target))` follows
from `P1.1 ≠ P2.1` (so the linear-pair lcm is an associate of the
product `(X-C P1.1)*(X-C P2.1)`, `npoly4LcmLinearPair_natDegree_eq_two`'s
own proof already builds this) together with `P1.1`/`P2.1` each not
being a root of `u_a` or `target` — this is `hcop1234`'s promised "natural
sufficient condition", discharged rather than left as a bare hypothesis.
No coprimality of the quadratic pair with itself is needed here (unlike
`hcop1234`'s original statement, this doesn't even mention `hne34`/
`hnoroot34`) — coprimality of a LINEAR factor with anything reduces
directly to "not a root" via `isCoprime_X_sub_C_of_not_isRoot`, then
`IsCoprime.mul_left`/`.mul_right` combine the two linear factors, and
`IsCoprime.of_isCoprime_of_dvd_left`/`_right` transport along each `lcm`'s
divisibility from its underlying pair. -/
theorem isCoprime_lcm12_lcm34_of_no_shared_root (h12 : P1.1 ≠ P2.1)
    (hP1ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P1.1 = 0)
    (hP1target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P1.1 = 0)
    (hP2ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P2.1 = 0)
    (hP2target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P2.1 = 0) :
    IsCoprime (EuclideanDomain.lcm (X - C P1.1 : Polynomial (F p)) (X - C P2.1))
        (EuclideanDomain.lcm (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
          (X ^ 2 + C u1 * X + C u0)) := by
  set lcm34 : Polynomial (F p) := EuclideanDomain.lcm
    (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) (X ^ 2 + C u1 * X + C u0) with hlcm34_def
  -- Coprimality of each individual linear factor with `lcm34`: go
  -- through `IsCoprime` with the PRODUCT `q3*q4` (via `mul_right`
  -- combining the two separate root-nonmembership facts), then
  -- transport DOWN to `lcm34` since `lcm34 ∣ q3 * q4`.
  have hcop1_3 : IsCoprime (X - C P1.1 : Polynomial (F p))
      (X ^ 2 + C ua1 * X + C ua0) := isCoprime_X_sub_C_of_not_isRoot p hP1ua
  have hcop1_4 : IsCoprime (X - C P1.1 : Polynomial (F p))
      (X ^ 2 + C u1 * X + C u0) := isCoprime_X_sub_C_of_not_isRoot p hP1target
  have hcop2_3 : IsCoprime (X - C P2.1 : Polynomial (F p))
      (X ^ 2 + C ua1 * X + C ua0) := isCoprime_X_sub_C_of_not_isRoot p hP2ua
  have hcop2_4 : IsCoprime (X - C P2.1 : Polynomial (F p))
      (X ^ 2 + C u1 * X + C u0) := isCoprime_X_sub_C_of_not_isRoot p hP2target
  have hcopP1 : IsCoprime (X - C P1.1 : Polynomial (F p))
      ((X ^ 2 + C ua1 * X + C ua0) * (X ^ 2 + C u1 * X + C u0)) :=
    hcop1_3.mul_right hcop1_4
  have hcopP2 : IsCoprime (X - C P2.1 : Polynomial (F p))
      ((X ^ 2 + C ua1 * X + C ua0) * (X ^ 2 + C u1 * X + C u0)) :=
    hcop2_3.mul_right hcop2_4
  have hlcm34dvd : lcm34 ∣ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) *
      (X ^ 2 + C u1 * X + C u0) := by
    rw [hlcm34_def]
    -- `a ∣ a*b` and `b ∣ a*b` via anonymous-constructor witnesses,
    -- avoiding `Dvd.intro`'s argument-order pitfall (flagged already in
    -- `AlphaReduce.lean`'s `sq_dvd_of_eval_derivative_eq_zero`).
    exact EuclideanDomain.lcm_dvd ⟨_, rfl⟩ ⟨_, mul_comm _ _⟩
  have hcopP1' : IsCoprime (X - C P1.1 : Polynomial (F p)) lcm34 :=
    IsCoprime.of_isCoprime_of_dvd_right hcopP1 hlcm34dvd
  have hcopP2' : IsCoprime (X - C P2.1 : Polynomial (F p)) lcm34 :=
    IsCoprime.of_isCoprime_of_dvd_right hcopP2 hlcm34dvd
  have hcop12 : IsCoprime ((X - C P1.1 : Polynomial (F p)) * (X - C P2.1)) lcm34 :=
    hcopP1'.mul_left hcopP2'
  have hlcm12dvd : (EuclideanDomain.lcm (X - C P1.1 : Polynomial (F p)) (X - C P2.1)) ∣
      (X - C P1.1 : Polynomial (F p)) * (X - C P2.1) := by
    have h1 : (X - C P1.1 : Polynomial (F p)) ∣ (X - C P1.1 : Polynomial (F p)) * (X - C P2.1) :=
      ⟨_, rfl⟩
    have h2 : (X - C P2.1 : Polynomial (F p)) ∣ (X - C P1.1 : Polynomial (F p)) * (X - C P2.1) :=
      ⟨_, mul_comm _ _⟩
    exact EuclideanDomain.lcm_dvd h1 h2
  exact IsCoprime.of_isCoprime_of_dvd_left hcop12 hlcm12dvd

/-- `npoly4Lcm4`'s degree is EXACTLY 6, given `P1.1 ≠ P2.1` (linear pair
sharpening, `npoly4LcmLinearPair_natDegree_eq_two`), `u_a ≠ target` with
no shared root (quadratic pair sharpening,
`npoly4LcmQuadraticPair_natDegree_eq_four`), AND that `P1.1`/`P2.1` are
each not a root of `u_a` or `target` — this last block of four hypotheses
replaces what used to be a single bare `hcop1234 : IsCoprime (lcm12)
(lcm34)` hypothesis; `isCoprime_lcm12_lcm34_of_no_shared_root` derives
that `IsCoprime` fact from these four simpler root-nonmembership facts,
matching Mumford reduction's own case analysis (reduction only needs a
DIFFERENT combining step when a specific point actually collides with a
specific root — these four hypotheses are exactly "no such collision"),
rather than assuming coprimality of the combined lcms as an unreduced
black box. -/
theorem npoly4Lcm4_natDegree_eq_six (h12 : P1.1 ≠ P2.1)
    (hne34 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ≠ X ^ 2 + C u1 * X + C u0)
    (hnoroot34 : ¬ ∃ r : F p, (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval r = 0 ∧
        (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval r = 0)
    (hP1ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P1.1 = 0)
    (hP1target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P1.1 = 0)
    (hP2ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P2.1 = 0)
    (hP2target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P2.1 = 0) :
    (npoly4Lcm4 p P1 P2 ua0 ua1 u0 u1).natDegree = 6 := by
  have hcop1234 : IsCoprime (EuclideanDomain.lcm (X - C P1.1 : Polynomial (F p)) (X - C P2.1))
      (EuclideanDomain.lcm (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
        (X ^ 2 + C u1 * X + C u0)) :=
    isCoprime_lcm12_lcm34_of_no_shared_root p P1 P2 ua0 ua1 u0 u1 h12
      hP1ua hP1target hP2ua hP2target
  have hm1 : (X - C P1.1 : Polynomial (F p)).Monic := Polynomial.monic_X_sub_C _
  have hm2 : (X - C P2.1 : Polynomial (F p)).Monic := Polynomial.monic_X_sub_C _
  have hm3 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).Monic := by monicity!
  have hm4 : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).Monic := by monicity!
  have hdeg12 : (EuclideanDomain.lcm (X - C P1.1 : Polynomial (F p)) (X - C P2.1)).natDegree
      = 2 := npoly4LcmLinearPair_natDegree_eq_two p P1 P2 h12
  have hdeg34 : (EuclideanDomain.lcm (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
      (X ^ 2 + C u1 * X + C u0)).natDegree = 4 :=
    npoly4LcmQuadraticPair_natDegree_eq_four p ua0 ua1 u0 u1 hne34 hnoroot34
  have hne12 : EuclideanDomain.lcm (X - C P1.1 : Polynomial (F p)) (X - C P2.1) ≠ 0 := by
    intro hz
    rw [EuclideanDomain.lcm_eq_zero_iff] at hz
    rcases hz with hz | hz
    · exact hm1.ne_zero hz
    · exact hm2.ne_zero hz
  have hne34' : EuclideanDomain.lcm (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
      (X ^ 2 + C u1 * X + C u0) ≠ 0 := by
    intro hz
    rw [EuclideanDomain.lcm_eq_zero_iff] at hz
    rcases hz with hz | hz
    · exact hm3.ne_zero hz
    · exact hm4.ne_zero hz
  -- Same `gcd_mul_lcm`-associate argument as `npoly4LcmLinearPair_natDegree_eq_two`/
  -- `npoly4LcmQuadraticPair_natDegree_eq_four`, one level up: `hcop1234`
  -- gives `gcd q12 q34` a unit, so `lcm q12 q34` is a unit multiple of
  -- `q12 * q34`, degree `2+4=6`.
  have hgcdunit : IsUnit (EuclideanDomain.gcd
      (EuclideanDomain.lcm (X - C P1.1 : Polynomial (F p)) (X - C P2.1))
      (EuclideanDomain.lcm (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
        (X ^ 2 + C u1 * X + C u0))) :=
    EuclideanDomain.gcd_isUnit_iff.mpr hcop1234
  have hprod := EuclideanDomain.gcd_mul_lcm
    (EuclideanDomain.lcm (X - C P1.1 : Polynomial (F p)) (X - C P2.1))
    (EuclideanDomain.lcm (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
      (X ^ 2 + C u1 * X + C u0))
  obtain ⟨u, hu⟩ := hgcdunit
  have hrawne : npoly4LcmRaw p P1 P2 ua0 ua1 u0 u1 ≠ 0 := npoly4LcmRaw_ne_zero p P1 P2 ua0 ua1 u0 u1
  have hprodne : (EuclideanDomain.lcm (X - C P1.1 : Polynomial (F p)) (X - C P2.1)) *
      (EuclideanDomain.lcm (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
        (X ^ 2 + C u1 * X + C u0)) ≠ 0 := mul_ne_zero hne12 hne34'
  have hproddeg : ((EuclideanDomain.lcm (X - C P1.1 : Polynomial (F p)) (X - C P2.1)) *
      (EuclideanDomain.lcm (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
        (X ^ 2 + C u1 * X + C u0))).natDegree = 6 := by
    rw [Polynomial.natDegree_mul hne12 hne34', hdeg12, hdeg34]
  have hune : (u : Polynomial (F p)) ≠ 0 := u.ne_zero
  have hudvd1 : (u : Polynomial (F p)) ∣ (1 : Polynomial (F p)) := u.isUnit.dvd
  have hudeg0 : (u : Polynomial (F p)).natDegree = 0 := by
    have hle := Polynomial.natDegree_le_of_dvd hudvd1 one_ne_zero
    simpa using hle
  have hlhs : (EuclideanDomain.gcd
      (EuclideanDomain.lcm (X - C P1.1 : Polynomial (F p)) (X - C P2.1))
      (EuclideanDomain.lcm (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
        (X ^ 2 + C u1 * X + C u0)) *
      npoly4LcmRaw p P1 P2 ua0 ua1 u0 u1).natDegree =
      (npoly4LcmRaw p P1 P2 ua0 ua1 u0 u1).natDegree := by
    rw [← hu, Polynomial.natDegree_mul hune hrawne, hudeg0, zero_add]
  rw [show EuclideanDomain.gcd
      (EuclideanDomain.lcm (X - C P1.1 : Polynomial (F p)) (X - C P2.1))
      (EuclideanDomain.lcm (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
        (X ^ 2 + C u1 * X + C u0)) *
      npoly4LcmRaw p P1 P2 ua0 ua1 u0 u1 =
      (EuclideanDomain.lcm (X - C P1.1 : Polynomial (F p)) (X - C P2.1)) *
      (EuclideanDomain.lcm (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
        (X ^ 2 + C u1 * X + C u0)) from hprod, hproddeg] at hlhs
  simp only [npoly4Lcm4]
  set q := npoly4LcmRaw p P1 P2 ua0 ua1 u0 u1 with hq
  have hlc : q.leadingCoeff ≠ 0 := (not_congr Polynomial.leadingCoeff_eq_zero).mpr hrawne
  have hau : q.leadingCoeff⁻¹ * q.leadingCoeff ≠ 0 := mul_ne_zero (inv_ne_zero hlc) hlc
  have hscaledeg : (C q.leadingCoeff⁻¹ * q).natDegree = q.natDegree :=
    Polynomial.natDegree_C_mul_of_mul_ne_zero hau
  rw [hscaledeg]
  exact hlhs.symm

/-- `u_RS,general(x)`, monic-normalized `curBeforeMonic4General` — same
`leadingCoeff⁻¹`-scaling construction as `uRS4`/`uRS4LcmShared`/
`uRS4Tangent`, applied to `curBeforeMonic4General` instead. Well-defined
(as the correct monic associate) only once `curBeforeMonic4General ≠ 0`,
recorded as a hypothesis exactly as `uRS4_monic` does for `uRS4`. -/
noncomputable def uRS4General : Polynomial (F p) :=
  C (curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff⁻¹ *
    curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1

theorem uRS4General_monic
    (hcur : curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0) :
    (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).Monic := by
  simp only [uRS4General]
  set q := curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 with hq
  have hlc : q.leadingCoeff ≠ 0 := (not_congr Polynomial.leadingCoeff_eq_zero).mpr hcur
  have hau : q.leadingCoeff * q.leadingCoeff⁻¹ = 1 := mul_inv_cancel₀ hlc
  have hdeg : (C q.leadingCoeff⁻¹ * q).natDegree = q.natDegree :=
    Polynomial.natDegree_C_mul_eq_of_mul_eq_one hau
  rw [Polynomial.Monic.def]
  change (C q.leadingCoeff⁻¹ * q).coeff (C q.leadingCoeff⁻¹ * q).natDegree = 1
  rw [hdeg, Polynomial.coeff_C_mul]
  exact inv_mul_cancel₀ hlc

/-- **`uRS4General ∣ Npoly4`, completely unconditional** — the actual
target of this file: no `IsCoprime` hypothesis of any kind, only the
curve-membership/nondegeneracy/Mumford data every other divisibility fact
in `AlphaReduce.lean` already needs on its own, plus `curBeforeMonic4General
≠ 0` (matching `uRS4_dvd_Npoly4`'s own `hne` precondition). Direct port of
`uRS4_dvd_Npoly4`'s final scaling argument, replacing the `hprod`/four-step
peel with `npoly4Lcm4_dvd_Npoly4` and a single `divByMonic_eq_of_dvd_mul`
step (using `npoly4Lcm4_monic`, itself unconditional). -/
theorem uRS4General_dvd_Npoly4
    (hne : curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hA : MatrixNondegenerate4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hP1_curve : P1.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P1.1)
    (hP2_curve : P2.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P2.1)
    (hMumfordUa : IsMumfordUa p c0 c1 c2 c3 c4 ua0 ua1 va0 va1)
    (hMumfordTarget : IsMumfordTarget4 p c0 c1 c2 c3 c4 u0 u1 v0 v1) :
    uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 := by
  have hLdvd := npoly4Lcm4_dvd_Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1
    hA hP1_curve hP2_curve hMumfordUa hMumfordTarget
  have hLmonic := npoly4Lcm4_monic p P1 P2 ua0 ua1 u0 u1
  obtain ⟨k, hk⟩ := hLdvd
  have hstep :
      curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 = k := by
    simp only [curBeforeMonic4General]
    exact divByMonic_eq_of_dvd_mul hLmonic hk
  have hcurdvd :
      curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ∣
        Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 := by
    rw [hstep, hk]; exact ⟨npoly4Lcm4 p P1 P2 ua0 ua1 u0 u1, by ring⟩
  unfold uRS4General
  obtain ⟨m, hm⟩ := hcurdvd
  have hlc :
      (curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff
        ≠ 0 := (not_congr Polynomial.leadingCoeff_eq_zero).mpr hne
  refine ⟨C (curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff
    * m, ?_⟩
  rw [hm]
  have hscale :
      (C (curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff⁻¹ *
        curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) *
      (C (curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff * m) =
      C ((curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff⁻¹ *
        (curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff) *
      (curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 * m) := by
    simp only [map_mul]; ring
  rw [hscale, inv_mul_cancel₀ hlc, map_one, one_mul]

/-- `v_RS,general(x) = -E4(x) * Y4(x)⁻¹ mod uRS4General(x)` — the
unconditional counterpart of `vRS4`, same `EuclideanDomain.gcdA`
Bézout-coefficient construction. `_hgcd` is carried unused, matching
`vRS4`'s own convention (forcing callers to supply it alongside
`uRS4General_monic`'s `hcur` wherever the VALUE is used). -/
noncomputable def vRS4General
    (_hgcd : IsCoprime (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
      (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)) :
    Polynomial (F p) :=
  (-(Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) *
      EuclideanDomain.gcdA (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
        (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)) %ₘ
    uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1

/-- **`hdeg2` itself, as an actual theorem** — `curBeforeMonic4General`'s
degree is EXACTLY 2, combining `Npoly4_natDegree_eq_eight` (`AlphaReduce.lean`,
needing only `hlead`, the `bi=4` Cramer coefficient nonvanishing) and
`npoly4Lcm4_natDegree_eq_six` (needing `h12`/`hne34`/`hnoroot34` plus the
four root-nonmembership facts `hP1ua`/`hP1target`/`hP2ua`/`hP2target`
above). `8 - 6 = 2` via `Polynomial.natDegree_divByMonic`, exactly as
`ROADMAP-reduce-to-zerodim.md`'s step-4 combination predicted, now with
BOTH halves sharp instead of merely bounded. This closes step 1 of that
roadmap modulo these named genericity hypotheses — the same class of
"weaken to a hypothesis" object as `Nondegenerate`/`CrossNondegenerate`
elsewhere in this project, not a `sorry`. Note this is now STRICTLY
WEAKER than the file's earlier form: the old bare `hcop1234 : IsCoprime
(lcm12) (lcm34)` hypothesis is gone, replaced by the four simpler
root-nonmembership facts it actually reduces to
(`isCoprime_lcm12_lcm34_of_no_shared_root`), matching how Mumford
reduction itself only needs a different combining step exactly when a
specific point collides with a specific root — not an unreduced
coprimality black box. -/
theorem curBeforeMonic4General_natDegree_eq_two
    (hlead : coeffsOut4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ⟨6, by norm_num⟩ ≠ 0)
    (h12 : P1.1 ≠ P2.1)
    (hne34 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ≠ X ^ 2 + C u1 * X + C u0)
    (hnoroot34 : ¬ ∃ r : F p, (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval r = 0 ∧
        (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval r = 0)
    (hP1ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P1.1 = 0)
    (hP1target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P1.1 = 0)
    (hP2ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P2.1 = 0)
    (hP2target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P2.1 = 0) :
    (curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).natDegree = 2 := by
  have hmonic := npoly4Lcm4_monic p P1 P2 ua0 ua1 u0 u1
  have heq :
      (curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).natDegree =
        (Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).natDegree -
          (npoly4Lcm4 p P1 P2 ua0 ua1 u0 u1).natDegree := by
    simp only [curBeforeMonic4General]
    exact Polynomial.natDegree_divByMonic _ hmonic
  have h8 : (Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).natDegree = 8 :=
    Npoly4_natDegree_eq_eight p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hlead
  have h6 : (npoly4Lcm4 p P1 P2 ua0 ua1 u0 u1).natDegree = 6 :=
    npoly4Lcm4_natDegree_eq_six p P1 P2 ua0 ua1 u0 u1 h12 hne34 hnoroot34
      hP1ua hP1target hP2ua hP2target
  omega

/-- **`hdeg2`, the shape `ReduceGeneral_isMumfordTarget4` needs
directly** — `uRS4General.natDegree = 2` (monic-normalization preserves
`natDegree`), obtained from `curBeforeMonic4General_natDegree_eq_two`
plus `curBeforeMonic4General ≠ 0` (immediate from `natDegree = 2 ≠ 0`,
via `Polynomial.natDegree_eq_zero_iff_...`-style contrapositive: a
polynomial with a nonzero `natDegree` cannot itself be the zero
polynomial, since `(0 : Polynomial _).natDegree = 0`). Wired into
`ReduceGeneral_isMumfordTarget4`'s call site below (`ReduceGeneralCorrectness`
section) — that theorem's bare `hdeg2` hypothesis is replaced by a `have`
calling this theorem, per `ROADMAP-reduce-to-zerodim.md`'s step-1 action
item 5. -/
theorem uRS4General_natDegree_eq_two
    (hlead : coeffsOut4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ⟨6, by norm_num⟩ ≠ 0)
    (h12 : P1.1 ≠ P2.1)
    (hne34 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ≠ X ^ 2 + C u1 * X + C u0)
    (hnoroot34 : ¬ ∃ r : F p, (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval r = 0 ∧
        (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval r = 0)
    (hP1ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P1.1 = 0)
    (hP1target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P1.1 = 0)
    (hP2ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P2.1 = 0)
    (hP2target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P2.1 = 0) :
    (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).natDegree = 2 := by
  have hdeg2 := curBeforeMonic4General_natDegree_eq_two p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1
    u0 u1 v0 v1 hlead h12 hne34 hnoroot34 hP1ua hP1target hP2ua hP2target
  have hcurne : curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0 := by
    intro hz; rw [hz] at hdeg2; simp at hdeg2
  simp only [uRS4General]
  set q := curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 with hq
  have hlc : q.leadingCoeff ≠ 0 := (not_congr Polynomial.leadingCoeff_eq_zero).mpr hcurne
  have hau : q.leadingCoeff⁻¹ * q.leadingCoeff ≠ 0 := mul_ne_zero (inv_ne_zero hlc) hlc
  rw [Polynomial.natDegree_C_mul_of_mul_ne_zero hau]
  exact hdeg2

end GeneralOutput

/-! ## The Mumford identity, unconditional -/

section MumfordIdentity4General

variable (c0 c1 c2 c3 c4 : F p) (P1 P2 : F p × F p) (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
variable (hcur : curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
variable (hgcd : IsCoprime (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
  (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1))

/-- **The Mumford identity, unconditional K=4 instance**: `v_RS,general(x)^2
≡ curvePoly(x) (mod u_RS,general(x))` — the zero-blocking-hypothesis
replacement for `vRS4_sq_eq_f_mod_uRS4`. `hNu` is derived from
`uRS4General_dvd_Npoly4` (no `h12`–`h34` anywhere) rather than assumed;
`hInv` (the Bézout-invertibility content) is real remaining content, same
status as `vRS4_sq_eq_f_mod_uRS4`'s own `hInv`, not derivable from `hgcd`
alone (see that theorem's docstring in `AlphaReduce.lean` for why). -/
theorem vRS4General_sq_eq_f_mod_uRS4General
    (hcur :
      curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hA : MatrixNondegenerate4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hP1_curve : P1.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P1.1)
    (hP2_curve : P2.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P2.1)
    (hMumfordUa : IsMumfordUa p c0 c1 c2 c3 c4 ua0 ua1 va0 va1)
    (hMumfordTarget : IsMumfordTarget4 p c0 c1 c2 c3 c4 u0 u1 v0 v1)
    (hInv :
      uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ∣
        Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 *
            EuclideanDomain.gcdA
              (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
              (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) - 1) :
    (vRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hgcd) ^ 2 %ₘ
        uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 =
      (curvePoly p c0 c1 c2 c3 c4) %ₘ
        uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 := by
  have hNu :
      uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ∣
        Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 :=
    uRS4General_dvd_Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1
      hcur hA hP1_curve hP2_curve hMumfordUa hMumfordTarget
  let U := uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1
  let E := Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1
  let Y := Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1
  let G := EuclideanDomain.gcdA Y U
  let f := curvePoly p c0 c1 c2 c3 c4
  have hU : U.Monic :=
    uRS4General_monic p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hcur
  have hInv' : U ∣ Y * G - 1 := by exact hInv
  have hNu' : U ∣ E ^ 2 - f * Y ^ 2 := by
    show uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ∣
      (Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) ^ 2 -
        (curvePoly p c0 c1 c2 c3 c4) * (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) ^ 2
    have hNu2 : uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ∣
        (Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) ^ 2 -
          (curvePoly p c0 c1 c2 c3 c4) * (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) ^ 2 := by
      unfold Npoly4 at hNu; exact hNu
    exact hNu2
  have hmod := sq_mod_eq_of_dvd_4 hU hNu' hInv'
  simpa only [vRS4General, U, E, Y, G, f] using hmod

set_option maxHeartbeats 4000000 in
/-- **`uRS4General ∣ (Epoly4 + Ypoly4 * vRS4General)`, unconditional given
`hInv` — the residual-pair analogue of `ua_dvd_Epoly4_add_Ypoly4_mul_va`/
`u_dvd_Epoly4_add_Ypoly4_mul_v` (`AlphaReduce.lean`), but for
`uRS4General`/`vRS4General` (the genuinely FRESH residual pair) instead of
the INPUT `u_a`/`u_target` pairs those two lemmas cover.** This is the
"Mumford pair, not named roots" bridge fact the "package as `(U,V)`"
strategy (`ROADMAP-principal-witness-assembly.md`, "Status update, this
pass, #11") needs: it lets a caller conclude `g(P) = 0` or `ḡ(P) = 0`
directly from `P.X` being ANY root of `uRS4General`, without ever
constructing that root as a named field element the way
`Epoly4_eval_add_v_eval_mul_Ypoly4_eval_eq_zero_of_root_u` does for `u`.

Proof, linear (not squared) analogue of `vRS4General_sq_eq_f_mod_uRS4General`'s
own derivation: writing `U := uRS4General`, `E := Epoly4`, `Y := Ypoly4`,
`G := EuclideanDomain.gcdA Y U`, `vRS4General` unfolds to `(-E*G) %ₘ U`.
`Polynomial.dvd_modByMonic_sub` gives `U ∣ ((-E*G) %ₘ U) - (-E*G)`, i.e.
`U ∣ V - (-E*G)` where `V := vRS4General`. Then
`E + Y*V = E + Y*(-E*G) + Y*(V - (-E*G)) = E*(1 - Y*G) + Y*(V-(-E*G))`
— the first summand is divisible by `U` via `hInv : U ∣ Y*G - 1` (negate
and scale by `E`), the second directly via the remainder fact just
derived (scale by `Y`) — so `U` divides the sum. This is the SAME `hInv`
hypothesis `vRS4General_sq_eq_f_mod_uRS4General` already takes (Bézout
invertibility of `Y` mod `U`), not a new assumption. -/
theorem uRS4General_dvd_Epoly4_add_Ypoly4_mul_vRS4General
    (hInv :
      uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ∣
        Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 *
            EuclideanDomain.gcdA
              (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
              (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) - 1) :
    uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ∣
      (Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 +
        Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 *
          vRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hgcd) := by
  let U := uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1
  let E := Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1
  let Y := Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1
  let G := EuclideanDomain.gcdA Y U
  have hV_def : vRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hgcd =
      (-E * G) %ₘ U := rfl
  have hInv' : U ∣ Y * G - 1 := hInv
  have hrem : U ∣ ((-E * G) %ₘ U) - (-E * G) := Polynomial.dvd_modByMonic_sub (-E * G) U
  have hpart1 : U ∣ (Y * G - 1) * (-E) := dvd_mul_of_dvd_left hInv' (-E)
  have hpart2 : U ∣ Y * (((-E * G) %ₘ U) - (-E * G)) := dvd_mul_of_dvd_right hrem Y
  have hid : (Y * G - 1) * (-E) + Y * (((-E * G) %ₘ U) - (-E * G)) =
      E + Y * ((-E * G) %ₘ U) := by ring
  have hfinal : U ∣ (E + Y * ((-E * G) %ₘ U)) := by
    rw [← hid]
    exact dvd_add hpart1 hpart2
  rw [hV_def]
  exact hfinal

end MumfordIdentity4General

/-! ## `ReduceGeneral`: `Reduce`'s output, with `h12`–`h34` gone

Direct port of `Reduce` (`AlphaReduce.lean`), reading its output off
`uRS4General`/`vRS4General` instead of `uRS4`/`vRS4`. Takes the exact same
TWO hypotheses `Reduce` itself already takes (`hcur : curBeforeMonic4General
≠ 0`, `hgcd : IsCoprime Ypoly4 uRS4General`) — those two are NOT among
`h12`–`h34` (they concern `Ypoly4` vs the OUTPUT quotient, a different
pair than any of the six `P1`/`P2`/`u_a`/`target` combinations), so they
are genuinely separate content this file does not attempt to remove,
exactly as `Reduce` itself never took `h12`–`h34` directly (confirmed by
inspection: `Reduce`'s only hypotheses were always `hcur`/`hgcd`, never
the six pairwise facts — those only ever lived in `uRS4_dvd_Npoly4`'s
CORRECTNESS proof, not in `Reduce`'s own definition). What
`ReduceGeneral` adds over plain `Reduce` is that its correctness theorem
(`uRS4General_dvd_Npoly4`/`vRS4General_sq_eq_f_mod_uRS4General`, both
above) no longer needs `h12`–`h34` either — so the full pipeline
(`Reduce`'s output + a proof it's actually correct) is now blocker-free,
not just `Reduce`'s bare definedness (which was already blocker-free
before this file, per the earlier investigation this pass confirmed). -/

section ReduceGeneral4

/-- **`ReduceGeneral`**: `Reduce`'s zero-`h12`–`h34`-blocker counterpart.
Same two hypotheses `Reduce` itself takes (`hcur`/`hgcd`, now stated
against `curBeforeMonic4General`/`uRS4General`), same output shape (the
Mumford pair's coefficients). A caller who has `hcur`/`hgcd` for the
GENERAL objects gets a `Reduce` whose correctness (`uRS4General_dvd_Npoly4`
above) holds regardless of whether `P1`/`P2`/`u_a`/`target` happen to be
pairwise coprime. -/
noncomputable def ReduceGeneral (c0 c1 c2 c3 c4 : F p) (P1 P2 : F p × F p)
    (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (_hcur : curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hgcd : IsCoprime (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
      (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)) :
    F p × F p × F p × F p :=
  ((uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).coeff 0,
   (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).coeff 1,
   (vRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hgcd).coeff 0,
   (vRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hgcd).coeff 1)

end ReduceGeneral4

/-! ## `ReduceDispatchGeneral`: the `h12`–`h34`-free full dispatcher

Direct port of `AlphaReduce.lean`'s `ReduceDispatch`, swapping the
`P1 ≠ P2` branch's call from `Reduce` to `ReduceGeneral`. The `P1 = P2`
branch is UNCHANGED — still `ReduceTangent` on `Epoly4Tangent`/
`Ypoly4Tangent`, genuinely different objects (built from
`coeffsOut4Tangent`'s own tangent-row Cramer solution, not `Epoly4`/
`Ypoly4` with `P1 = P2` substituted; confirmed by inspection, see
`Epoly4Tangent`'s definition in `AlphaReduce.lean` and its docstring on
`Ypoly4`'s "genuinely different" K=4 shape). `npoly4Lcm4`/
`curBeforeMonic4General`/`uRS4General` ARE all well-defined at `P1 = P2`
(`EuclideanDomain.lcm (X - C P1.1) (X - C P2.1)` degenerates harmlessly to
a single linear factor there, no falsity anywhere in their construction —
confirmed by inspection, none of `GeneralQuotient`/`GeneralOutput`'s
definitions or proofs use `h : P1.1 ≠ P2.1` except
`npoly4LcmLinearPair_natDegree_eq_two`, which is not on `ReduceGeneral`'s
call path), but the tangent-row linear system is still the mathematically
correct model of `alpha • a - 2•P1` (a doubled point), not `alpha • a - P1
- P2` with `P1 = P2` plugged into the two-DISTINCT-points system — so this
dispatcher keeps the same two-way case split as `ReduceDispatch`, just
with the `P1 ≠ P2` branch's six raw `h12`–`h34` obligations replaced by
zero. -/

section ReduceDispatchGeneral

/-- **`ReduceDispatchGeneral`**: case-splits on `P1 = P2` exactly as
`ReduceDispatch` does, routing to `ReduceTangent` (`P1 = P2`, unchanged)
or `ReduceGeneral` (`P1 ≠ P2`, the `h12`–`h34`-free replacement for
`Reduce`). A caller in the `P1 ≠ P2` branch now only ever has to supply
`hcur`/`hgcd` against the GENERAL objects — never any of the six pairwise
`IsCoprime` facts, and never a false hypothesis (unlike `ReduceDispatch`'s
`P1 ≠ P2` branch, which is well-typed but requires `h12`–`h34` that may
not hold when `P1`/`P2`/`u_a`/`target` collide). -/
noncomputable def ReduceDispatchGeneral (c0 c1 c2 c3 c4 : F p) (P1 P2 : F p × F p)
    (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (hcur : P1 ≠ P2 →
      curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hgcd : P1 ≠ P2 → IsCoprime (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
      (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1))
    (hcurT : P1 = P2 →
      curBeforeMonic4Tangent p c0 c1 c2 c3 c4 P1.1 P1.2 ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hgcdT : P1 = P2 → IsCoprime
      (Ypoly4Tangent p c0 c1 c2 c3 c4 P1.1 P1.2 ua0 ua1 va0 va1 u0 u1 v0 v1)
      (uRS4Tangent p c0 c1 c2 c3 c4 P1.1 P1.2 ua0 ua1 va0 va1 u0 u1 v0 v1)) :
    F p × F p × F p × F p :=
  if hP : P1 = P2 then
    ReduceTangent p c0 c1 c2 c3 c4 P1.1 P1.2 ua0 ua1 va0 va1 u0 u1 v0 v1
      (hcurT hP) (hgcdT hP)
  else
    ReduceGeneral p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 (hcur hP) (hgcd hP)

end ReduceDispatchGeneral

/-! ## `ReduceGeneral`'s correctness: its output is a genuine Mumford pair

**What "correctness" means here, precisely.** `IsMumfordUa`/`IsMumfordTarget4`
(`AlphaReduce.lean`) already fix this project's working definition of "is a
valid Mumford representative": `(u0,u1,v0,v1)` is one iff
`(X²+C u1*X+C u0) ∣ ((C v1*X+C v0)² - f)` — the polynomial-level Mumford
congruence `v(x)² ≡ f(x) (mod u(x))`, `f = curvePoly`. This is the same
notion Cantor's algorithm's correctness is classically stated against, and
it's the notion `SampleTargetFromAlpha.isReduction'`
(`AlphaLocusDegreeUniform.lean`) ultimately needs discharged for
`Reduce`/`ReduceGeneral`'s output to be usable as a genuine sample target.

**What's actually provable right now, and what isn't.**
`vRS4General_sq_eq_f_mod_uRS4General` above already IS the polynomial
Mumford identity, `vRS4General² %ₘ uRS4General = curvePoly %ₘ uRS4General`,
for the *polynomials* `uRS4General`/`vRS4General` themselves — that part
needs no new work, it's proved. What's missing is repackaging that fact in
`IsMumfordTarget4`'s literal coefficient shape, `(X²+C u1'*X+C u0') ∣ (...)`,
which requires knowing `uRS4General` (as a polynomial) actually EQUALS
`X² + C uRS4General.coeff 1 * X + C uRS4General.coeff 0` — true for any
monic polynomial of `natDegree = 2` (NOT merely `≤ 2`: a monic polynomial
of `natDegree 0` or `1`, e.g. `q = 1`, is not literally `X² + ...`, whose
own `natDegree` is always exactly `2` by construction — this was caught
and fixed after an earlier draft of this section wrongly stated the `≤ 2`
version as "unconditionally true").

**Updated status**: the sharp `natDegree = 2` bound is now CLOSED —
`uRS4General_natDegree_eq_two` (`GeneralOutput` section above) proves it,
modulo the same genericity hypotheses (`hlead`/`h12`/`hne34`/`hnoroot34`/
`hP1ua`/`hP1target`/`hP2ua`/`hP2target`) `npoly4Lcm4_natDegree_eq_six`
needed. `ReduceGeneral_isMumfordTarget4` below now takes those hypotheses
directly and derives `hdeg2` internally via a `have`, rather than taking
`hdeg2` as a bare hypothesis — `ROADMAP-reduce-to-zerodim.md`'s step-1
action item 5, now done. -/

section ReduceGeneralCorrectness

variable (c0 c1 c2 c3 c4 : F p) (P1 P2 : F p × F p) (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)

/-- **A monic polynomial of `natDegree ≤ 2` is literally `X² + C(coeff 1)*X +
C(coeff 0)`.** General fact, proved directly from the coefficients (no
`compute_degree!`/`monicity!` shortcuts, since `q` is a hypothesis here, not
a literal): every coefficient past degree 2 vanishes
(`natDegree_le_iff_coeff_eq_zero`), the degree-2 coefficient is `1` (monic),
and `Polynomial.ext` assembles these into the claimed equality
coefficient-by-coefficient. Same idiom as `not_coprime_quadratics_iff`'s
`he_eq : e = X + C (e.coeff 0)` step above, one degree higher. -/
theorem monicQuadratic_eq_reconstruct {q : Polynomial (F p)} (hmonic : q.Monic)
    (hdeg : q.natDegree = 2) :
    q = X ^ 2 + C (q.coeff 1) * X + C (q.coeff 0) := by
  apply Polynomial.ext
  intro n
  match n with
  | 0 => simp [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C,
      Polynomial.coeff_C_mul, Polynomial.coeff_X]
  | 1 => simp [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C,
      Polynomial.coeff_C_mul, Polynomial.coeff_X]
  | 2 =>
    have hlead : q.coeff q.natDegree = 1 := hmonic.coeff_natDegree
    rw [hdeg] at hlead
    simp [hlead, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C,
      Polynomial.coeff_C_mul, Polynomial.coeff_X]
  | (n + 3) =>
    have hzero : q.coeff (n + 3) = 0 :=
      (Polynomial.natDegree_le_iff_coeff_eq_zero (n := 2)).mp (by omega) (n + 3) (by omega)
    simp [hzero, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C,
      Polynomial.coeff_C_mul, Polynomial.coeff_X]

/-- **`ReduceGeneral`'s output is a genuine Mumford pair — fully proved,
`hdeg2` now derived rather than assumed.** Unfolds `ReduceGeneral` to its
`uRS4General`/`vRS4General` coefficients, rewrites both polynomials via
`monicQuadratic_eq_reconstruct` (using `uRS4General_monic`/`hdeg2` for `u`;
`vRS4General` needs no monicity or degree bound at all here, since
`IsMumfordTarget4`'s shape only pins down `v`'s degree-≤1 PART via its own
literal `C v1*X+C v0` form, which is exactly the reconstruction target —
but `vRS4General` is a `%ₘ uRS4General` remainder, so `vRS4General.natDegree
< uRS4General.natDegree ≤ 2` from `Polynomial.natDegree_modByMonic_lt`
already gives `≤ 1`, no separate hypothesis needed there, resolving the
"vRS4/vRS4General's degree bound isn't separately proved" gap
`AlphaReduce.lean`'s own docstring flags — at least for this call), then
converts `vRS4General_sq_eq_f_mod_uRS4General`'s `%ₘ` equation to the `∣`
form `IsMumfordTarget4` needs via `Polynomial.modByMonic_eq_zero_iff_dvd`. -/
theorem ReduceGeneral_isMumfordTarget4
    (hcur : curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hgcd : IsCoprime (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
      (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1))
    (hA : MatrixNondegenerate4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hP1_curve : P1.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P1.1)
    (hP2_curve : P2.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P2.1)
    (hMumfordUa : IsMumfordUa p c0 c1 c2 c3 c4 ua0 ua1 va0 va1)
    (hMumfordTarget : IsMumfordTarget4 p c0 c1 c2 c3 c4 u0 u1 v0 v1)
    (hInv :
      uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ∣
        Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 *
            EuclideanDomain.gcdA
              (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
              (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) - 1)
    -- **Closed** — `uRS4General_natDegree_eq_two` (`GeneralOutput` section
    -- above) proves this sharp bound unconditionally-modulo-genericity;
    -- the hypotheses below are its exact preconditions, replacing what
    -- used to be a bare `hdeg2` hypothesis here. `ROADMAP-reduce-to-
    -- zerodim.md`'s step-1 action item 5.
    (hlead : coeffsOut4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ⟨6, by norm_num⟩ ≠ 0)
    (h12 : P1.1 ≠ P2.1)
    (hne34 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ≠ X ^ 2 + C u1 * X + C u0)
    (hnoroot34 : ¬ ∃ r : F p, (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval r = 0 ∧
        (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval r = 0)
    (hP1ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P1.1 = 0)
    (hP1target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P1.1 = 0)
    (hP2ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P2.1 = 0)
    (hP2target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P2.1 = 0) :
    IsMumfordTarget4 p c0 c1 c2 c3 c4
      (ReduceGeneral p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hcur hgcd).1
      (ReduceGeneral p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hcur hgcd).2.1
      (ReduceGeneral p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hcur hgcd).2.2.1
      (ReduceGeneral p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hcur hgcd).2.2.2 := by
  have hdeg2 : (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).natDegree = 2 :=
    uRS4General_natDegree_eq_two p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1
      hlead h12 hne34 hnoroot34 hP1ua hP1target hP2ua hP2target
  set U := uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 with hU_def
  set V := vRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hgcd with hV_def
  have hUmonic : U.Monic :=
    uRS4General_monic p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hcur
  have hUrecon : U = X ^ 2 + C (U.coeff 1) * X + C (U.coeff 0) :=
    monicQuadratic_eq_reconstruct p hUmonic hdeg2
  have hVdeg : V.natDegree ≤ 1 := by
    have hdeglt : V.degree < U.degree := by
      rw [hV_def]
      exact Polynomial.degree_modByMonic_lt _ hUmonic
    rcases eq_or_ne V 0 with hV0 | hV0
    · simp [hV0]
    · have hlt : V.natDegree < U.natDegree := Polynomial.natDegree_lt_natDegree hV0 hdeglt
      omega
  have hVrecon : V = C (V.coeff 1) * X + C (V.coeff 0) := by
    apply Polynomial.ext
    intro n
    match n with
    | 0 => simp [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul,
        Polynomial.coeff_X]
    | 1 => simp [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul,
        Polynomial.coeff_X]
    | (n + 2) =>
      have hzero : V.coeff (n + 2) = 0 :=
        Polynomial.natDegree_le_iff_coeff_eq_zero.mp hVdeg (n + 2) (by omega)
      simp [hzero, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul,
        Polynomial.coeff_X]
  have hmod := vRS4General_sq_eq_f_mod_uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1
    u0 u1 v0 v1 hgcd hcur hA hP1_curve hP2_curve hMumfordUa hMumfordTarget hInv
  rw [← hU_def, ← hV_def] at hmod
  have hdvd : U ∣ (V ^ 2 - curvePoly p c0 c1 c2 c3 c4) := by
    rw [← Polynomial.modByMonic_eq_zero_iff_dvd hUmonic, Polynomial.sub_modByMonic, hmod, sub_self]
  unfold IsMumfordTarget4 ReduceGeneral
  dsimp only
  simp only [← hU_def, ← hV_def]
  rw [← hUrecon, ← hVrecon]
  exact hdvd

end ReduceGeneralCorrectness

/-! ## `npoly4Lcm4`'s flat-product identity (moved from
`PrincipalWitnessAssembly.lean`)

Relocated here, verbatim, to break an import cycle:
`OrdAtRootMultiplicityUnified.lean` needs `npoly4Lcm4_eq_flat_product` (it
was originally only available via `PrincipalWitnessAssembly.lean`), but
`PrincipalWitnessAssembly.lean`'s own `R1 = R2` repeated-root assembly
theorems need `OrdAtRootMultiplicityUnified.lean`'s
`ordAt_npoly4Lcm4_eq_two_of_R1_eq_R2_rootMultiplicity` — so the two files
can't import each other. `npoly4Lcm4` and all of `quadratic_eq_mul_X_sub_C`/
`npoly4Lcm4_eq_flat_product`'s own dependencies
(`isCoprime_linear_pair_of_ne`, `isCoprime_quadratic_pair_of_ne_of_no_shared_root`,
`isCoprime_lcm12_lcm34_of_no_shared_root`) already live in THIS file, so
moving the two theorems here (unqualified names unchanged, since every
call site across the project refers to them unqualified and both files
`open`/sit inside `TheDataDerivation`) resolves the cycle with no other
file needing to change. -/

section FlatProduct

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-- **`lcm f g = C u * (f * g)` for monic coprime `f g`, for the specific
unit `u := (gcd f g).leadingCoeff⁻¹`** — i.e. `lcm f g` IS an exact unit
multiple of the product, with the unit pinned down concretely (not left
existential), by reusing this project's own established scaling idiom
(`npoly4Lcm4`/`uRS4General`'s `C leadingCoeff⁻¹ * ·` normalization,
already used four times over in `GeneralSharedRoot.lean`). This is the
version actually needed downstream (`npoly4Lcm4_eq_flat_product`), since
`npoly4Lcm4` is ITSELF built via exactly this `C leadingCoeff⁻¹ * ·`
normalization applied to `npoly4LcmRaw` — composing two normalizations
telescopes cleanly, whereas asserting the bare `lcm f g = f * g` (no unit)
would additionally require proving `EuclideanDomain.lcm` returns the
monic representative outright, which is false in general (flagged
already in this file's own `npoly4Lcm4` construction: the whole reason
`npoly4Lcm4` needs its own rescaling step is that the raw
`EuclideanDomain.lcm`/`npoly4LcmRaw` is NOT automatically monic). -/
theorem lcm_eq_C_leadingCoeff_inv_mul_of_monic_coprime {f g : Polynomial (F p)}
    (hf : f.Monic) (hg : g.Monic) (hcop : IsCoprime f g) :
    EuclideanDomain.lcm f g =
      C (EuclideanDomain.gcd f g).leadingCoeff⁻¹ * (f * g) := by
  have hgcdunit : IsUnit (EuclideanDomain.gcd f g) := EuclideanDomain.gcd_isUnit_iff.mpr hcop
  have hprod := EuclideanDomain.gcd_mul_lcm f g
  have hfne : f ≠ 0 := hf.ne_zero
  have hgne : g ≠ 0 := hg.ne_zero
  have hgcdne : EuclideanDomain.gcd f g ≠ 0 := by
    intro hz
    have := EuclideanDomain.gcd_dvd_left f g
    rw [hz] at this
    exact hfne (eq_zero_of_zero_dvd this)
  have hlc_ne : (EuclideanDomain.gcd f g).leadingCoeff ≠ 0 :=
    (not_congr Polynomial.leadingCoeff_eq_zero).mpr hgcdne
  -- `hprod : gcd f g * lcm f g = f * g`. Multiply both sides by
  -- `C (gcd f g).leadingCoeff⁻¹` and use that `gcd f g` is a unit (hence
  -- `C leadingCoeff⁻¹ * gcd f g` is `1` exactly — same
  -- `inv_mul_cancel₀`-on-`leadingCoeff` idiom `uRS4General_monic`'s own
  -- proof already uses for a monic-normalization step) to isolate `lcm f g`.
  have hcancel : C (EuclideanDomain.gcd f g).leadingCoeff⁻¹ * EuclideanDomain.gcd f g = 1 := by
    -- A UNIT polynomial over a field has `natDegree = 0` (it divides `1`),
    -- hence is `C` of its own constant coefficient
    -- (`Polynomial.eq_C_of_natDegree_eq_zero`), which IS its leading
    -- coefficient (`Polynomial.leadingCoeff_C`) — no `IsUnit.exists`
    -- destructuring needed, avoiding the `c.val : (F p)[X]`/`C : F p → (F p)[X]`
    -- type mismatch that destructuring runs into.
    have hcdeg0 : (EuclideanDomain.gcd f g).natDegree = 0 := by
      have hdvd1 : (EuclideanDomain.gcd f g) ∣ (1 : Polynomial (F p)) := hgcdunit.dvd
      have hle := Polynomial.natDegree_le_of_dvd hdvd1 one_ne_zero
      simpa using hle
    have hcC : (EuclideanDomain.gcd f g) = C ((EuclideanDomain.gcd f g).coeff 0) :=
      Polynomial.eq_C_of_natDegree_eq_zero hcdeg0
    have hlcC : (EuclideanDomain.gcd f g).leadingCoeff = (EuclideanDomain.gcd f g).coeff 0 := by
      conv_lhs => rw [Polynomial.leadingCoeff, hcdeg0]
    have hcoeff : (EuclideanDomain.gcd f g).coeff 0 ≠ 0 := by
      simpa [← hlcC] using hlc_ne
    rw [hlcC]
    nth_rewrite 2 [hcC]
    rw [← map_mul, inv_mul_cancel₀ hcoeff, map_one]
  calc EuclideanDomain.lcm f g
      = 1 * EuclideanDomain.lcm f g := (one_mul _).symm
    _ = (C (EuclideanDomain.gcd f g).leadingCoeff⁻¹ * EuclideanDomain.gcd f g) *
          EuclideanDomain.lcm f g := by rw [hcancel]
    _ = C (EuclideanDomain.gcd f g).leadingCoeff⁻¹ *
          (EuclideanDomain.gcd f g * EuclideanDomain.lcm f g) := by ring
    _ = C (EuclideanDomain.gcd f g).leadingCoeff⁻¹ * (f * g) := by rw [hprod]

/-- **A monic quadratic with two known distinct roots equals the product
of its two linear factors** — the symmetric splitting lemma the ChatGPT
reply recommended (deliberately NOT privileging either root, since `F p`
has no useful order for this purpose; both `ua`'s two roots and
`u_target`'s two roots reuse this ONE lemma, 4 call sites total, rather
than a bespoke argument per point). Proof follows the reply's recommended
route exactly: each root gives a linear-factor divisor
(`Polynomial.dvd_iff_isRoot`), the two linear factors are coprime
(`r1 ≠ r2`, `isCoprime_linear_pair_of_ne`-style —
`Polynomial.isCoprime_X_sub_C_of_isUnit_sub` directly, since this lemma
is stated for a general monic quadratic `q`, not literally
`ua`/`u_target`, so it can't call the project-specific
`isCoprime_linear_pair_of_ne` which is hardcoded to `P1.1`/`P2.1`), hence
`IsCoprime.mul_dvd` gives `(X-C r1)*(X-C r2) ∣ q`; both sides are monic of
degree 2 (`hdeg` supplies `q`'s degree so this works for any degree-2
monic `q`, not hardcoding "quadratic" via a literal `X^2+...` shape), so
`Polynomial.eq_of_monic_of_dvd_of_natDegree_le` (with the natDegree
inequality direction flipped, since the divisor here is the DEGREE-2
side and the dividend is `q` itself) closes it. -/
theorem quadratic_eq_mul_X_sub_C {q : Polynomial (F p)} (hq : q.Monic)
    (hdeg : q.natDegree = 2) {r1 r2 : F p} (hr1 : q.IsRoot r1) (hr2 : q.IsRoot r2)
    (hne : r1 ≠ r2) :
    q = (X - C r1) * (X - C r2) := by
  have hd1 : (X - C r1 : Polynomial (F p)) ∣ q := Polynomial.dvd_iff_isRoot.mpr hr1
  have hd2 : (X - C r2 : Polynomial (F p)) ∣ q := Polynomial.dvd_iff_isRoot.mpr hr2
  have hcop : IsCoprime (X - C r1 : Polynomial (F p)) (X - C r2) :=
    Polynomial.isCoprime_X_sub_C_of_isUnit_sub (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hne))
  have hdvd : (X - C r1 : Polynomial (F p)) * (X - C r2) ∣ q := hcop.mul_dvd hd1 hd2
  have hm1 : (X - C r1 : Polynomial (F p)).Monic := Polynomial.monic_X_sub_C _
  have hm2 : (X - C r2 : Polynomial (F p)).Monic := Polynomial.monic_X_sub_C _
  have hprodmonic : ((X - C r1 : Polynomial (F p)) * (X - C r2)).Monic := hm1.mul hm2
  have hproddeg : ((X - C r1 : Polynomial (F p)) * (X - C r2)).natDegree = 2 := by
    rw [Polynomial.natDegree_mul hm1.ne_zero hm2.ne_zero,
      Polynomial.natDegree_X_sub_C, Polynomial.natDegree_X_sub_C]
  have hle22 : q.natDegree ≤ ((X - C r1 : Polynomial (F p)) * (X - C r2)).natDegree :=
    le_of_eq (hdeg.trans hproddeg.symm)
  have hqeq : q = (X - C r1 : Polynomial (F p)) * (X - C r2) :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le
      (p := (X - C r1 : Polynomial (F p)) * (X - C r2))
      (q := q) hprodmonic hq hdvd hle22
  exact hqeq

/-- **`npoly4Lcm4` equals the flat product `(X-C P1.x)*(X-C P2.x)*ua*u_target`
up to an explicit, named unit, in the fully-split/no-shared-root generic
case** — the actual target of roadmap step 3's "flat-product bridge",
assembled in the SAME binary-tree shape as `npoly4Lcm4`'s own definition
(`lcm(lcm q1 q2, lcm q3 q4)`, then re-normalized by ONE more
`leadingCoeff⁻¹`-rescaling to match `npoly4Lcm4`'s own outer
normalization), per the ChatGPT reply's explicit recommendation ("prove
it in the same tree shape as the definition... rather than trying to
prove the fully flattened statement in one shot"). Composes
`lcm_eq_C_leadingCoeff_inv_mul_of_monic_coprime` (inner-left, inner-right)
plus a direct `EuclideanDomain.gcd_mul_lcm` step at the outer level
(sidesteps needing `L12`/`L34` themselves monic, which they are not) —
against the coprimality facts ALREADY proved in `GeneralSharedRoot.lean`
(`isCoprime_linear_pair_of_ne`, `isCoprime_quadratic_pair_of_ne_of_no_shared_root`,
`isCoprime_lcm12_lcm34_of_no_shared_root`) — confirmed by the reply that
these three hypotheses are exactly "all six pairwise roots distinct"
repackaged to match the tree shape, not a separate/stronger condition.

The unit is named concretely (`unitConst`, a `Polynomial (F p)`, together
with `hunit : IsUnit unitConst`) rather than left existential, so the
call sites in step 4 (Layer 3 instantiation at each of the 6 named
points) can `rw` the flat-product identity directly without first
destructuring an anonymous existential witness. -/
theorem npoly4Lcm4_eq_flat_product
    (P1 P2 : F p × F p) (ua0 ua1 u0 u1 : F p)
    (h12 : P1.1 ≠ P2.1)
    (hne34 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ≠ X ^ 2 + C u1 * X + C u0)
    (hnoroot34 : ¬ ∃ r : F p, (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval r = 0 ∧
        (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval r = 0)
    (hP1ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P1.1 = 0)
    (hP1target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P1.1 = 0)
    (hP2ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P2.1 = 0)
    (hP2target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P2.1 = 0) :
    npoly4Lcm4 p P1 P2 ua0 ua1 u0 u1 =
      C ((npoly4LcmRaw p P1 P2 ua0 ua1 u0 u1).leadingCoeff⁻¹ *
        (EuclideanDomain.gcd
          (EuclideanDomain.lcm (X - C P1.1 : Polynomial (F p)) (X - C P2.1))
          (EuclideanDomain.lcm (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
            (X ^ 2 + C u1 * X + C u0))).leadingCoeff⁻¹ *
        (EuclideanDomain.gcd (X - C P1.1 : Polynomial (F p)) (X - C P2.1)).leadingCoeff⁻¹ *
        (EuclideanDomain.gcd (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
          (X ^ 2 + C u1 * X + C u0)).leadingCoeff⁻¹) *
      (((X - C P1.1 : Polynomial (F p)) * (X - C P2.1)) *
        ((X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) * (X ^ 2 + C u1 * X + C u0))) := by
  have hm1 : (X - C P1.1 : Polynomial (F p)).Monic := Polynomial.monic_X_sub_C _
  have hm2 : (X - C P2.1 : Polynomial (F p)).Monic := Polynomial.monic_X_sub_C _
  have hm3 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).Monic := by monicity!
  have hm4 : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).Monic := by monicity!
  have hcop12 : IsCoprime (X - C P1.1 : Polynomial (F p)) (X - C P2.1) :=
    isCoprime_linear_pair_of_ne p P1 P2 h12
  have hcop34 : IsCoprime (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
      (X ^ 2 + C u1 * X + C u0) :=
    isCoprime_quadratic_pair_of_ne_of_no_shared_root p ua0 ua1 u0 u1 hne34 hnoroot34
  -- Name the two inner lcms so the outer step's algebra stays short and
  -- avoids re-typing (hence re-risking parenthesization typos on) these
  -- long expressions repeatedly.
  set L12 : Polynomial (F p) := EuclideanDomain.lcm (X - C P1.1 : Polynomial (F p)) (X - C P2.1)
    with hL12def
  set L34 : Polynomial (F p) := EuclideanDomain.lcm
      (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) (X ^ 2 + C u1 * X + C u0) with hL34def
  have hcopOuter : IsCoprime L12 L34 :=
    isCoprime_lcm12_lcm34_of_no_shared_root p P1 P2 ua0 ua1 u0 u1 h12 hP1ua hP1target hP2ua
      hP2target
  have hL12 :
      L12 = C (EuclideanDomain.gcd (X - C P1.1 : Polynomial (F p)) (X - C P2.1)).leadingCoeff⁻¹ *
      ((X - C P1.1 : Polynomial (F p)) * (X - C P2.1)) :=
    lcm_eq_C_leadingCoeff_inv_mul_of_monic_coprime p hm1 hm2 hcop12
  have hL34 : L34 = C (EuclideanDomain.gcd (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
        (X ^ 2 + C u1 * X + C u0)).leadingCoeff⁻¹ *
      ((X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) * (X ^ 2 + C u1 * X + C u0)) :=
    lcm_eq_C_leadingCoeff_inv_mul_of_monic_coprime p hm3 hm4 hcop34
  -- Outer step: `gcd L12 L34 * lcm L12 L34 = L12 * L34` directly
  -- (`EuclideanDomain.gcd_mul_lcm`), no monicity of `L12`/`L34` needed —
  -- only `IsCoprime`'s gcd-is-a-unit consequence, isolating `lcm L12 L34`
  -- by the same `inv_mul_cancel₀`-on-`leadingCoeff` idiom as
  -- `lcm_eq_C_leadingCoeff_inv_mul_of_monic_coprime`'s own proof.
  set G : Polynomial (F p) := EuclideanDomain.gcd L12 L34 with hGdef
  have hprodOuter : G * EuclideanDomain.lcm L12 L34 = L12 * L34 :=
    EuclideanDomain.gcd_mul_lcm L12 L34
  have hgcdOuterUnit : IsUnit G := EuclideanDomain.gcd_isUnit_iff.mpr hcopOuter
  have hgcdOuterne : G ≠ 0 := hgcdOuterUnit.ne_zero
  have hlcOuterne : G.leadingCoeff ≠ 0 :=
    (not_congr Polynomial.leadingCoeff_eq_zero).mpr hgcdOuterne
  have hcdeg0 : G.natDegree = 0 := by
    have hdvd1 : G ∣ (1 : Polynomial (F p)) := hgcdOuterUnit.dvd
    have hle := Polynomial.natDegree_le_of_dvd hdvd1 one_ne_zero
    simpa using hle
  have hcOuterC : G = C (G.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hcdeg0
  have hlcOuterC : G.leadingCoeff = G.coeff 0 := by
    conv_lhs => rw [Polynomial.leadingCoeff, hcdeg0]
  have hcancelOuter : C G.leadingCoeff⁻¹ * G = 1 := by
    have hcoeff : G.coeff 0 ≠ 0 := by
      simpa [← hlcOuterC] using hlcOuterne
    rw [hlcOuterC]
    nth_rewrite 2 [hcOuterC]
    rw [← map_mul, inv_mul_cancel₀ hcoeff, map_one]
  have houterLcm : EuclideanDomain.lcm L12 L34 = C G.leadingCoeff⁻¹ * (L12 * L34) := by
    calc EuclideanDomain.lcm L12 L34
        = 1 * EuclideanDomain.lcm L12 L34 := (one_mul _).symm
      _ = (C G.leadingCoeff⁻¹ * G) * EuclideanDomain.lcm L12 L34 := by rw [hcancelOuter]
      _ = C G.leadingCoeff⁻¹ * (G * EuclideanDomain.lcm L12 L34) := by ring
      _ = C G.leadingCoeff⁻¹ * (L12 * L34) := by rw [hprodOuter]
  simp only [npoly4Lcm4, npoly4LcmRaw, ← hL12def, ← hL34def]
  rw [houterLcm, hL12, hL34]
  simp only [map_mul]
  ring_nf

end FlatProduct

end TheDataDerivation
end Genus2Lean
