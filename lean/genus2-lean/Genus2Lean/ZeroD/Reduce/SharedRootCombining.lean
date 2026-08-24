import Mathlib
import Genus2Lean.ZeroD.TheDataDerivation.DataDerivationBasics
import Genus2Lean.ZeroD.Reduce.AlphaReduce

/-! # Combining `Npoly4`'s four factors when `u_a` and `target` share a root

`uRS4_dvd_Npoly4` (`AlphaReduce.lean`) combines the four known-divides-`N`
facts (`dvd_N_P1`, `dvd_N_P2`, `dvd_N_ua`, `dvd_N_u4`) via
`prod_dvd_of_pairwise_coprime_four`, which needs all six pairwise
coprimality facts among the four factors. One of those,
`IsCoprime (X²+ua1·X+ua0) (X²+u1·X+u0)` (`u_a` vs `target`), is FALSE
whenever `alpha•a` and the target divisor share a Jacobian-point root —
which is not an excludable measure-zero coincidence for a generic genus-2
curve (nothing in the group law forbids `u_a` and `target` sharing a root;
concretely `P1+P2-u_a1-u_a2 = u_a1+u2` is a perfectly ordinary instance).

This file's fix is purely at the *combining* step, not the row/matrix
construction: `dvd_N_ua`/`dvd_N_u4` (and their tangent-case twins) already
prove `u_a ∣ N` / `target ∣ N` directly and algebraically, with no
coprimality assumed anywhere in their own proofs — `u_a`/`target` are
always treated as opaque quadratics, never split into roots, so a shared
root changes nothing about those two theorems. Coprimality was only ever
needed by `prod_dvd_of_pairwise_coprime_four`'s specific proof strategy
(independent divisibilities × pairwise coprimality ⟹ product divides).

The fix: replace the `u_a`-vs-`target` factor pair by their `lcm` instead
of assuming they're coprime. `EuclideanDomain.lcm_dvd` gives
`lcm u_a target ∣ N` UNCONDITIONALLY from `u_a ∣ N` and `target ∣ N` — no
coprimality needed for that step at all. What remains is combining
`lcm u_a target` (degree ≤ 4, degree exactly 3 in the one-shared-root case)
with the two `P1`/`P2` factors, which only needs THOSE to be coprime to
`lcm u_a target` — two hypotheses, not four, since the `u_a`-vs-`target`
pairwise fact is no longer needed at all (subsumed by the unconditional
`lcm_dvd` step). -/

namespace Genus2Lean
namespace TheDataDerivation

open Polynomial

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

section LcmCombine4

/-- **Two divisors combine via their lcm, unconditionally** — no
coprimality needed. Direct restatement of `EuclideanDomain.lcm_dvd`
specialized to `Polynomial (F p)` (via `[DecidableEq R]`, which
`Polynomial (F p)` gets automatically since `F p := ZMod p` already has
decidable equality), named locally so call sites read the same way
`prod_dvd_of_pairwise_coprime_four` does. -/
theorem lcm_dvd_of_dvd_dvd {R : Type*} [EuclideanDomain R] [DecidableEq R]
    {q1 q2 N : R} (hd1 : q1 ∣ N) (hd2 : q2 ∣ N) :
    EuclideanDomain.lcm q1 q2 ∣ N :=
  EuclideanDomain.lcm_dvd hd1 hd2

/-- **Three factors combine when two of them are only known to jointly
divide via their lcm.** `q1`/`q2` (the `P1`/`P2`-style linear/tangent
factors) must each be coprime to `lcm q3 q4` (the merged `u_a`/`target`
factor) — but `q3`/`q4` need NOT be coprime to each other, unlike
`prod_dvd_of_pairwise_coprime_four`. Four hypotheses total (`h1L`, `h2L`,
`h12`, plus the two individual divisibilities folded in via
`lcm_dvd_of_dvd_dvd`), down from six. -/
theorem prod_dvd_of_coprime_to_lcm
    {R : Type*} [EuclideanDomain R] [DecidableEq R] {q1 q2 q3 q4 N : R}
    (h12 : IsCoprime q1 q2)
    (h1L : IsCoprime q1 (EuclideanDomain.lcm q3 q4))
    (h2L : IsCoprime q2 (EuclideanDomain.lcm q3 q4))
    (hd1 : q1 ∣ N) (hd2 : q2 ∣ N) (hd3 : q3 ∣ N) (hd4 : q4 ∣ N) :
    q1 * q2 * (EuclideanDomain.lcm q3 q4) ∣ N := by
  have hd34 : EuclideanDomain.lcm q3 q4 ∣ N := lcm_dvd_of_dvd_dvd hd3 hd4
  have h12_L : IsCoprime (q1 * q2) (EuclideanDomain.lcm q3 q4) :=
    IsCoprime.mul_left h1L h2L
  have hd12 : q1 * q2 ∣ N := IsCoprime.mul_dvd h12 hd1 hd2
  have hprod : (q1 * q2) * (EuclideanDomain.lcm q3 q4) ∣ N :=
    IsCoprime.mul_dvd h12_L hd12 hd34
  have heq : (q1 * q2) * (EuclideanDomain.lcm q3 q4) =
      q1 * q2 * (EuclideanDomain.lcm q3 q4) := by ring
  rwa [heq] at hprod

end LcmCombine4

/-! ## Instantiation against `Npoly4`

Mirrors `uRS4_dvd_Npoly4` (`AlphaReduce.lean`'s `CombineDvd4` section)
exactly, substituting `prod_dvd_of_coprime_to_lcm` for
`prod_dvd_of_pairwise_coprime_four`. Unlike `curBeforeMonic4`, there is no
single new definition for "the quotient after removing all four factors"
here: `EuclideanDomain.lcm` is only defined up to a unit
(`a*b/gcd a b`, no normalization guarantee), so a third `/ₘ` step against
it can't be justified without first separately establishing its
monicity — `npoly4_quotient_eq_lcm_mul_of_shared_root` below stops after
the two `(X-C P1.1)`/`(X-C P2.1)` steps and exposes the remaining factor
`uaTargetLcm4 * k` directly, leaving any further monic-normalization to
the call site. -/

section SharedRootCombine4

variable (c0 c1 c2 c3 c4 : F p) (P1 P2 : F p × F p)
variable (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)

/-- The merged `u_a`/`target` factor, via `lcm` rather than product —
degree ≤ 4, degree exactly 3 when `u_a` and `target` share exactly one
root (the generic shared-root case), degree 2 when `u_a = target`
outright (a different, more degenerate case, not handled by this file —
see the module docstring's case-classification discussion). -/
noncomputable def uaTargetLcm4 : Polynomial (F p) :=
  EuclideanDomain.lcm (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
    (X ^ 2 + C u1 * X + C u0)

/-- **The shared-root-safe combining theorem.** Only needs `P1`/`P2`'s
factors to be coprime to each other and to the MERGED `u_a`/`target`
factor — `IsCoprime u_a target` is never assumed, so this covers exactly
the case `uRS4_dvd_Npoly4` cannot: `u_a` and `target` sharing a root. -/
theorem npoly4_dvd_of_shared_root
    (h12 : IsCoprime (X - C P1.1 : Polynomial (F p)) (X - C P2.1))
    (h1L : IsCoprime (X - C P1.1 : Polynomial (F p)) (uaTargetLcm4 p ua0 ua1 u0 u1))
    (h2L : IsCoprime (X - C P2.1 : Polynomial (F p)) (uaTargetLcm4 p ua0 ua1 u0 u1))
    (hd1 : (X - C P1.1 : Polynomial (F p)) ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hd2 : (X - C P2.1 : Polynomial (F p)) ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hUa : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hU : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)) ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) :
    (X - C P1.1) * (X - C P2.1) * (uaTargetLcm4 p ua0 ua1 u0 u1) ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 :=
  prod_dvd_of_coprime_to_lcm h12 h1L h2L hd1 hd2 hUa hU

/-- **`(Npoly4 /ₘ (X-P1.1)) /ₘ (X-P2.1) = uaTargetLcm4 * k` for some `k`**
— the shared-root-safe counterpart of `curBeforeMonic4_dvd_Npoly4`-style
reasoning, stopping one step earlier than a `curBeforeMonic4`-style
def would: `EuclideanDomain.lcm` is only defined up to a unit (`a*b/gcd
a b`, no normalization guarantee), so it is NOT assumed monic here — this
theorem exposes the witness `k` directly instead of trying to `/ₘ` by
`uaTargetLcm4` a third time, which would need `uaTargetLcm4.Monic` as an
extra unproven hypothesis. A caller who needs the monic `uRS`-style
quotient can normalize `uaTargetLcm4 * k`'s leading coefficient themselves
(exactly as `uRS4`/`uRS4Tangent` already do to `curBeforeMonic4`/
`curBeforeMonic4Tangent` in `AlphaReduce.lean`), or first establish
`uaTargetLcm4`'s monicity by hand from `u_a`/`target`'s known monic forms
before taking this further — left to the call site, not assumed here. -/
theorem npoly4_quotient_eq_lcm_mul_of_shared_root
    (h12 : IsCoprime (X - C P1.1 : Polynomial (F p)) (X - C P2.1))
    (h1L : IsCoprime (X - C P1.1 : Polynomial (F p)) (uaTargetLcm4 p ua0 ua1 u0 u1))
    (h2L : IsCoprime (X - C P2.1 : Polynomial (F p)) (uaTargetLcm4 p ua0 ua1 u0 u1))
    (hd1 : (X - C P1.1 : Polynomial (F p)) ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hd2 : (X - C P2.1 : Polynomial (F p)) ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hUa : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hU : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)) ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) :
    ∃ k : Polynomial (F p),
      (Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 /ₘ (X - C P1.1)) /ₘ
          (X - C P2.1) =
        uaTargetLcm4 p ua0 ua1 u0 u1 * k := by
  have hprod := npoly4_dvd_of_shared_root p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1
    h12 h1L h2L hd1 hd2 hUa hU
  obtain ⟨k, hk⟩ := hprod
  have hm1 : (X - C P1.1 : Polynomial (F p)).Monic := Polynomial.monic_X_sub_C _
  have hm2 : (X - C P2.1 : Polynomial (F p)).Monic := Polynomial.monic_X_sub_C _
  have hstep0 :
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 =
        (X - C P1.1) * ((X - C P2.1) * (uaTargetLcm4 p ua0 ua1 u0 u1 * k)) := by
    rw [hk]; ring
  have hstep1 :
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 /ₘ (X - C P1.1) =
        (X - C P2.1) * (uaTargetLcm4 p ua0 ua1 u0 u1 * k) :=
    divByMonic_eq_of_dvd_mul hm1 hstep0
  have hstep2 :
      (Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 /ₘ (X - C P1.1)) /ₘ
          (X - C P2.1) =
        uaTargetLcm4 p ua0 ua1 u0 u1 * k :=
    divByMonic_eq_of_dvd_mul hm2 hstep1
  exact ⟨k, hstep2⟩

end SharedRootCombine4

/-! ## `uRS4LcmShared` / `vRS4LcmShared`: monic-normalized output for the
shared-root branch

`curBeforeMonic4LcmShared` is the two-step quotient
`(Npoly4 /ₘ (X-P1.1)) /ₘ (X-P2.1)` — well-defined unconditionally, exactly
like `curBeforeMonic4`'s own first two steps, and NOT a third `/ₘ` division
by `uaTargetLcm4` (see the previous section's docstring for why that step
is not available in general). `npoly4_quotient_eq_lcm_mul_of_shared_root`
already shows this quotient equals `uaTargetLcm4 * k` for a witness `k`
under the same hypotheses `uRS4_dvd_Npoly4` needs, minus `IsCoprime u_a
target` — so `curBeforeMonic4LcmShared` really is a degree-≤4 polynomial
divisible only by `u_a`'s and `target`'s combined root set, same role
`curBeforeMonic4` plays for the non-shared-root branch, just reached by a
two-step rather than four-step quotient chain. `uRS4LcmShared`/
`vRS4LcmShared` monic-normalize / Bézout-invert it exactly as `uRS4`/`vRS4`
do for `curBeforeMonic4`. -/

section URS4LcmShared

variable (c0 c1 c2 c3 c4 : F p) (P1 P2 : F p × F p)
variable (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)

/-- Two-step quotient of `Npoly4` by `(X-P1.1)` then `(X-P2.1)` only —
the shared-root-branch analogue of `curBeforeMonic4`'s first two steps. -/
noncomputable def curBeforeMonic4LcmShared : Polynomial (F p) :=
  (Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 /ₘ (X - C P1.1)) /ₘ
    (X - C P2.1)

/-- `u_RS,shared(x)`, monic-normalized `curBeforeMonic4LcmShared` — same
`leadingCoeff⁻¹`-scaling construction as `uRS4`. -/
noncomputable def uRS4LcmShared : Polynomial (F p) :=
  C (curBeforeMonic4LcmShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff⁻¹ *
    curBeforeMonic4LcmShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1

/-- `uRS4LcmShared` is monic, given `curBeforeMonic4LcmShared ≠ 0` — byte-
for-byte the same argument as `uRS4_monic`, only the quotient's name
differs. -/
theorem uRS4LcmShared_monic
    (hcur : curBeforeMonic4LcmShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0) :
    (uRS4LcmShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).Monic := by
  simp only [uRS4LcmShared]
  set q := curBeforeMonic4LcmShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 with hq
  have hlc : q.leadingCoeff ≠ 0 := (not_congr Polynomial.leadingCoeff_eq_zero).mpr hcur
  have hau : q.leadingCoeff * q.leadingCoeff⁻¹ = 1 := mul_inv_cancel₀ hlc
  have hdeg : (C q.leadingCoeff⁻¹ * q).natDegree = q.natDegree :=
    Polynomial.natDegree_C_mul_eq_of_mul_eq_one hau
  rw [Polynomial.Monic.def]
  change (C q.leadingCoeff⁻¹ * q).coeff (C q.leadingCoeff⁻¹ * q).natDegree = 1
  rw [hdeg, Polynomial.coeff_C_mul]
  exact inv_mul_cancel₀ hlc

/-- **`v_RS,shared(x) = -E4(x) * Y4(x)⁻¹ mod uRS4LcmShared(x)`** — same
`EuclideanDomain.gcdA` Bézout-coefficient construction as `vRS4`. -/
noncomputable def vRS4LcmShared
    (_hgcd : IsCoprime (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
      (uRS4LcmShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)) :
    Polynomial (F p) :=
  (-(Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) *
      EuclideanDomain.gcdA (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
        (uRS4LcmShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)) %ₘ
    uRS4LcmShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1

end URS4LcmShared

/-! ## Mumford identity, shared-root branch

Mirrors `vRS4_sq_eq_f_mod_uRS4` exactly, substituting
`npoly4_quotient_eq_lcm_mul_of_shared_root`'s weaker hypothesis set
(`h12`, `h1L`, `h2L` — no `IsCoprime u_a target`) for the six pairwise
facts, and re-deriving `uRS4LcmShared ∣ Npoly4` from that existential
witness rather than from `uRS4_dvd_Npoly4` directly. `sq_mod_eq_of_dvd_4`
itself is reused completely unchanged (it is already fully ring-generic,
proved once in `AlphaReduce.lean` for any `CommRing R`). -/

section MumfordIdentity4LcmShared

variable (c0 c1 c2 c3 c4 : F p) (P1 P2 : F p × F p) (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)

/-- **The Mumford identity, shared-root branch**: `v_RS,shared(x)^2 ≡
curvePoly(x) (mod u_RS,shared(x))`, valid when `u_a` and `target` share a
root (so `IsCoprime u_a target` — used by `vRS4_sq_eq_f_mod_uRS4` — is
false), replacing it with the `lcm`-based combining route. -/
theorem vRS4LcmShared_sq_eq_f_mod_uRS4LcmShared
    (hcur : curBeforeMonic4LcmShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hgcd : IsCoprime (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
      (uRS4LcmShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1))
    (h12 : IsCoprime (X - C P1.1 : Polynomial (F p)) (X - C P2.1))
    (h1L : IsCoprime (X - C P1.1 : Polynomial (F p)) (uaTargetLcm4 p ua0 ua1 u0 u1))
    (h2L : IsCoprime (X - C P2.1 : Polynomial (F p)) (uaTargetLcm4 p ua0 ua1 u0 u1))
    (hd1 : (X - C P1.1 : Polynomial (F p)) ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hd2 : (X - C P2.1 : Polynomial (F p)) ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hUa : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hU : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)) ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hInv :
      uRS4LcmShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ∣
        Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 *
            EuclideanDomain.gcdA
              (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
              (uRS4LcmShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) - 1) :
    (vRS4LcmShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hgcd) ^ 2 %ₘ
        uRS4LcmShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 =
      (curvePoly p c0 c1 c2 c3 c4) %ₘ
        uRS4LcmShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 := by
  have hprod := npoly4_dvd_of_shared_root
    p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 h12 h1L h2L hd1 hd2 hUa hU
  obtain ⟨k, hk⟩ := hprod
  have hm1 : (X - C P1.1 : Polynomial (F p)).Monic := Polynomial.monic_X_sub_C _
  have hm2 : (X - C P2.1 : Polynomial (F p)).Monic := Polynomial.monic_X_sub_C _
  have hstep0 :
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 =
        (X - C P1.1) * ((X - C P2.1) * (uaTargetLcm4 p ua0 ua1 u0 u1 * k)) := by
    rw [hk]
    ring
  have hstep1 :
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 /ₘ (X - C P1.1) =
        (X - C P2.1) * (uaTargetLcm4 p ua0 ua1 u0 u1 * k) :=
    divByMonic_eq_of_dvd_mul hm1 hstep0
  have hstep2 :
      (Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 /ₘ (X - C P1.1)) /ₘ
          (X - C P2.1) =
        uaTargetLcm4 p ua0 ua1 u0 u1 * k :=
    divByMonic_eq_of_dvd_mul hm2 hstep1
  have hNu : curBeforeMonic4LcmShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 := by
    unfold curBeforeMonic4LcmShared
    refine ⟨(X - C P1.1) * (X - C P2.1), ?_⟩
    rw [hstep2, hstep0]
    ring
  let U := uRS4LcmShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1
  let E := Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1
  let Y := Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1
  let G := EuclideanDomain.gcdA Y U
  let f := curvePoly p c0 c1 c2 c3 c4
  have hU : U.Monic :=
    uRS4LcmShared_monic p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hcur
  have hInv' : U ∣ Y * G - 1 := by exact hInv
  have hNu' : U ∣ E ^ 2 - f * Y ^ 2 := by
    show uRS4LcmShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ∣
      (Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) ^ 2 -
        (curvePoly p c0 c1 c2 c3 c4) * (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) ^ 2
    have huRS : uRS4LcmShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ∣
        curBeforeMonic4LcmShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 := by
      simp only [uRS4LcmShared]
      set q := curBeforeMonic4LcmShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1
      have hq : q.leadingCoeff ≠ 0 :=
        (not_congr Polynomial.leadingCoeff_eq_zero).mpr hcur
      refine ⟨C q.leadingCoeff, ?_⟩
      have hC : C q.leadingCoeff⁻¹ * C q.leadingCoeff = 1 := by
        rw [← C_mul, inv_mul_cancel₀ hq, C_1]
      calc
        q = q * 1 := by simp
        _ = q * (C q.leadingCoeff⁻¹ * C q.leadingCoeff) := by rw [hC]
        _ = (q * C q.leadingCoeff⁻¹) * C q.leadingCoeff := by rw [mul_assoc]
        _ = (C q.leadingCoeff⁻¹ * q) * C q.leadingCoeff := by rw [mul_comm q]
    have hNu2 : uRS4LcmShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ∣
        Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 :=
      huRS.trans hNu
    unfold Npoly4 at hNu2
    exact hNu2
  have hmod := sq_mod_eq_of_dvd_4 hU hNu' hInv'
  simpa only [vRS4LcmShared, U, E, Y, G, f] using hmod

end MumfordIdentity4LcmShared

/-! ## Dispatcher: `h34`-free combining, case-split on whether `u_a`/`target`
share a root

`uRS4_dvd_Npoly4` (`AlphaReduce.lean`) and `npoly4_dvd_of_shared_root`
(above) are genuinely different theorems about genuinely different
polynomials — `uRS4` (product-based, needs `h34`) vs `uaTargetLcm4`
(`lcm`-based, does not). Neither subsumes the other, so a caller who does
NOT want to assume `h34` up front cannot get a single uniform divisor
polynomial back — it depends on which branch they're in, and that's real
mathematical content, not a proof gap. This dispatcher packages that case
split explicitly: it takes every hypothesis EXCEPT `h34` (in particular
`h13`/`h14`/`h23`/`h24`/`h1L`/`h2L`, since those are near-identical-looking
but distinct coprimality facts required by each branch respectively —
`h13`/`h23` are P1/P2-vs-`u_a` in raw quadratic form, `h1L`/`h2L` are the
same P1/P2 vs the MERGED `lcm` factor, needed only in the shared-root
branch) and returns a disjunction: either `h34` holds and `uRS4 ∣ Npoly4`
(the ordinary, already-proved case), or it doesn't and
`uaTargetLcm4 ∣ curBeforeMonic4LcmShared`-shaped divisibility holds via the
shared-root branch instead. `Classical.em` on `h34` supplies the case
split; each branch is closed by the theorem that branch already has —
no new mathematical content here, purely dispatch. -/

section Dispatcher4

variable (c0 c1 c2 c3 c4 : F p) (P1 P2 : F p × F p)
variable (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)

/-- **`uRS4 ∣ Npoly4` OR the shared-root `lcm`-combine goes through** —
`h34`-free dispatcher. `Classical.em` on `h34` supplies the case split;
each branch closes directly by the theorem that branch already has
(`uRS4_dvd_Npoly4` for the coprime case, `npoly4_dvd_of_shared_root` for
the shared-root case) — no new mathematical content, purely dispatch. -/
theorem uRS4_dvd_Npoly4_or_shared_root
    (hne : curBeforeMonic4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hA : MatrixNondegenerate4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hP1_curve : P1.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P1.1)
    (hP2_curve : P2.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P2.1)
    (hMumfordUa : IsMumfordUa p c0 c1 c2 c3 c4 ua0 ua1 va0 va1)
    (hMumfordTarget : IsMumfordTarget4 p c0 c1 c2 c3 c4 u0 u1 v0 v1)
    (h12 : IsCoprime (X - C P1.1 : Polynomial (F p)) (X - C P2.1))
    (h13 : IsCoprime (X - C P1.1 : Polynomial (F p))
      (X ^ 2 + C ua1 * X + C ua0))
    (h14 : IsCoprime (X - C P1.1 : Polynomial (F p))
      (X ^ 2 + C u1 * X + C u0))
    (h23 : IsCoprime (X - C P2.1 : Polynomial (F p))
      (X ^ 2 + C ua1 * X + C ua0))
    (h24 : IsCoprime (X - C P2.1 : Polynomial (F p))
      (X ^ 2 + C u1 * X + C u0))
    (h1L : IsCoprime (X - C P1.1 : Polynomial (F p))
      (uaTargetLcm4 p ua0 ua1 u0 u1))
    (h2L : IsCoprime (X - C P2.1 : Polynomial (F p))
      (uaTargetLcm4 p ua0 ua1 u0 u1)) :
    (IsCoprime (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
        (X ^ 2 + C u1 * X + C u0) ∧
      uRS4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ∣
        Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) ∨
    (¬ IsCoprime (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
        (X ^ 2 + C u1 * X + C u0) ∧
      (X - C P1.1) * (X - C P2.1) * (uaTargetLcm4 p ua0 ua1 u0 u1) ∣
        Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) := by
  rcases Classical.em
      (IsCoprime (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
        (X ^ 2 + C u1 * X + C u0)) with h34 | h34
  · exact Or.inl ⟨h34,
      uRS4_dvd_Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1
        hne hA hP1_curve hP2_curve hMumfordUa hMumfordTarget h12 h13 h14 h23 h24 h34⟩
  · have hd1 := dvd_N_P1 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hA hP1_curve
    have hd2 := dvd_N_P2 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hA hP2_curve
    have hd3 := dvd_N_ua p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hA hMumfordUa
    have hd4 := dvd_N_u4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hA hMumfordTarget
    exact Or.inr ⟨h34,
      npoly4_dvd_of_shared_root p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1
        h12 h1L h2L hd1 hd2 hd3 hd4⟩

end Dispatcher4

end TheDataDerivation
end Genus2Lean
