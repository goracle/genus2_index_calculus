import Mathlib
import Genus2Lean.TheDataDerivation.DataDerivationBasics
import Genus2Lean.AlphaReduce
import Genus2Lean.SharedRootCombining
import Genus2Lean.P1TargetSharedRoot

/-! # Combining `Npoly4`'s four factors when `P2` and `target` share a root

Mirrors `P1TargetSharedRoot.lean` exactly, with the roles of `P1` and
`P2` swapped: this file removes `h24` (`IsCoprime (X - C P2.1) target`)
as a blocker instead of `h14`. `h24` is FALSE exactly when `P2.1` is a
root of `target = X²+u1·X+u0` — i.e. `P2` is one of the two Jacobian
points making up the target divisor. As with `h14`, nothing in the
group law forbids this.

`isCoprime_X_sub_C_iff_eval_ne_zero` is reused unchanged from
`P1TargetSharedRoot.lean` (it is already stated for a generic `a`, not
specifically `P1.1`). The combining step reuses
`prod_dvd_of_coprime_to_lcm`/`lcm_dvd_of_dvd_dvd` unchanged, merging
`(X - C P2.1)` and `target` into `p2TargetLcm4` instead of `p1TargetLcm4`.
`P1` and `u_a` remain ordinary product factors, still assumed coprime to
everything else — only `h24` is removed as a blocker here. -/

namespace Genus2Lean
namespace TheDataDerivation

open Polynomial

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

section P2TargetLcmShared

variable (c0 c1 c2 c3 c4 : F p) (P1 P2 : F p × F p)
variable (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)

/-- The merged `P2`/`target` factor via `lcm` — degree ≤ 3, degree
exactly 2 when `P2.1` is one of `target`'s two roots (the generic
shared-root case). -/
noncomputable def p2TargetLcm4 : Polynomial (F p) :=
  EuclideanDomain.lcm (X - C P2.1 : Polynomial (F p))
    (X ^ 2 + C u1 * X + C u0)

/-- **The `h24`-free combining theorem.** Only needs `P1` and `u_a`'s
factors to be coprime to each other and to the MERGED `P2`/`target`
factor — `IsCoprime (X - C P2.1) target` is never assumed, so this
covers exactly the case ordinary `h24` cannot: `P2` sharing a root with
`target`. -/
theorem npoly4_dvd_of_p2_target_shared_root
    (h1a : IsCoprime (X - C P1.1 : Polynomial (F p))
      (X ^ 2 + C ua1 * X + C ua0))
    (h1L : IsCoprime (X - C P1.1 : Polynomial (F p))
      (p2TargetLcm4 p P2 u0 u1))
    (haL : IsCoprime (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
      (p2TargetLcm4 p P2 u0 u1))
    (hd1 : (X - C P1.1 : Polynomial (F p)) ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hd3 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hd2 : (X - C P2.1 : Polynomial (F p)) ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hd4 : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)) ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) :
    (X - C P1.1) * (X ^ 2 + C ua1 * X + C ua0) * (p2TargetLcm4 p P2 u0 u1) ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 :=
  prod_dvd_of_coprime_to_lcm h1a h1L haL hd1 hd3 hd2 hd4

/-- **`(Npoly4 /ₘ (X-P1.1)) /ₘ (u_a) = p2TargetLcm4 * k` for some `k`** —
h24-branch counterpart of `npoly4_quotient_eq_p1_target_lcm_mul_of_shared_root`.
Divides out `P1`'s and `u_a`'s factors first (both ordinary, unmerged
factors in this branch — the merge here is `P2`/`target`), leaving the
merged `p2TargetLcm4` times a witness `k`. As with the `h14` case,
`p2TargetLcm4` is only defined up to a unit (`EuclideanDomain.lcm`), so
its monicity is established separately (`uRS4P2TargetShared_monic`
below) rather than folded into a third `/ₘ` step here. -/
theorem npoly4_quotient_eq_p2_target_lcm_mul_of_shared_root
    (h1a : IsCoprime (X - C P1.1 : Polynomial (F p))
      (X ^ 2 + C ua1 * X + C ua0))
    (h1L : IsCoprime (X - C P1.1 : Polynomial (F p))
      (p2TargetLcm4 p P2 u0 u1))
    (haL : IsCoprime (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
      (p2TargetLcm4 p P2 u0 u1))
    (hd1 : (X - C P1.1 : Polynomial (F p)) ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hd3 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hd2 : (X - C P2.1 : Polynomial (F p)) ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hd4 : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)) ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) :
    ∃ k : Polynomial (F p),
      (Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 /ₘ (X - C P1.1)) /ₘ
          (X ^ 2 + C ua1 * X + C ua0) =
        p2TargetLcm4 p P2 u0 u1 * k := by
  obtain ⟨k, hk⟩ := npoly4_dvd_of_p2_target_shared_root
    p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 h1a h1L haL hd1 hd3 hd2 hd4
  refine ⟨k, ?_⟩
  have hm1 : (X - C P1.1 : Polynomial (F p)).Monic := Polynomial.monic_X_sub_C _
  have hma : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).Monic := by monicity!
  have hstep0 :
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 =
        (X - C P1.1) * ((X ^ 2 + C ua1 * X + C ua0) * (p2TargetLcm4 p P2 u0 u1 * k)) := by
    rw [hk]; ring
  have hstep1 :
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 /ₘ (X - C P1.1) =
        (X ^ 2 + C ua1 * X + C ua0) * (p2TargetLcm4 p P2 u0 u1 * k) :=
    divByMonic_eq_of_dvd_mul hm1 hstep0
  exact divByMonic_eq_of_dvd_mul hma hstep1

end P2TargetLcmShared

section URS4P2TargetShared

variable (c0 c1 c2 c3 c4 : F p) (P1 P2 : F p × F p)
variable (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)

/-- Two-step quotient of `Npoly4` by `(X-P1.1)` then `u_a` only — the
h24-branch analogue of `curBeforeMonic4P1TargetShared`, dividing out the
two ordinary (unmerged) factors in this branch. -/
noncomputable def curBeforeMonic4P2TargetShared : Polynomial (F p) :=
  (Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 /ₘ (X - C P1.1)) /ₘ
    (X ^ 2 + C ua1 * X + C ua0)

/-- `u_RS,P2target(x)`, monic-normalized `curBeforeMonic4P2TargetShared` —
same `leadingCoeff⁻¹`-scaling construction as `uRS4`/`uRS4P1TargetShared`. -/
noncomputable def uRS4P2TargetShared : Polynomial (F p) :=
  C (curBeforeMonic4P2TargetShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff⁻¹ *
    curBeforeMonic4P2TargetShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1

/-- `uRS4P2TargetShared` is monic, given `curBeforeMonic4P2TargetShared ≠
0` — byte-for-byte `uRS4P1TargetShared_monic`'s argument. -/
theorem uRS4P2TargetShared_monic
    (hcur : curBeforeMonic4P2TargetShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0) :
    (uRS4P2TargetShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).Monic := by
  simp only [uRS4P2TargetShared]
  set q := curBeforeMonic4P2TargetShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 with hq
  have hlc : q.leadingCoeff ≠ 0 := (not_congr Polynomial.leadingCoeff_eq_zero).mpr hcur
  have hau : q.leadingCoeff * q.leadingCoeff⁻¹ = 1 := mul_inv_cancel₀ hlc
  have hdeg : (C q.leadingCoeff⁻¹ * q).natDegree = q.natDegree :=
    Polynomial.natDegree_C_mul_eq_of_mul_eq_one hau
  rw [Polynomial.Monic.def]
  change (C q.leadingCoeff⁻¹ * q).coeff (C q.leadingCoeff⁻¹ * q).natDegree = 1
  rw [hdeg, Polynomial.coeff_C_mul]
  exact inv_mul_cancel₀ hlc

/-- **`v_RS,P2target(x) = -E4(x) * Y4(x)⁻¹ mod uRS4P2TargetShared(x)`** —
same `EuclideanDomain.gcdA` Bézout-coefficient construction as
`vRS4`/`vRS4P1TargetShared`. -/
noncomputable def vRS4P2TargetShared
    (_hgcd : IsCoprime (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
      (uRS4P2TargetShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)) :
    Polynomial (F p) :=
  (-(Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) *
      EuclideanDomain.gcdA (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
        (uRS4P2TargetShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)) %ₘ
    uRS4P2TargetShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1

end URS4P2TargetShared

/-! ## Mumford identity, `P2`/`target` shared-root branch

Mirrors `vRS4P1TargetShared_sq_eq_f_mod_uRS4P1TargetShared` exactly,
substituting `npoly4_quotient_eq_p2_target_lcm_mul_of_shared_root`'s
hypothesis set (`h1a`, `h1L`, `haL` — no `IsCoprime (X - C P2.1)
target`). `sq_mod_eq_of_dvd_4` is reused completely unchanged. -/

section MumfordIdentity4P2TargetShared

variable (c0 c1 c2 c3 c4 : F p) (P1 P2 : F p × F p) (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)

/-- **The Mumford identity, `P2`/`target` shared-root branch**:
`v_RS,P2target(x)^2 ≡ curvePoly(x) (mod u_RS,P2target(x))`, valid when
`P2` and `target` share a root (so `IsCoprime (X - C P2.1) target` —
used by `vRS4_sq_eq_f_mod_uRS4` — is false), replacing it with the
`lcm`-based combining route. -/
theorem vRS4P2TargetShared_sq_eq_f_mod_uRS4P2TargetShared
    (hcur : curBeforeMonic4P2TargetShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hgcd : IsCoprime (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
      (uRS4P2TargetShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1))
    (h1a : IsCoprime (X - C P1.1 : Polynomial (F p))
      (X ^ 2 + C ua1 * X + C ua0))
    (h1L : IsCoprime (X - C P1.1 : Polynomial (F p)) (p2TargetLcm4 p P2 u0 u1))
    (haL : IsCoprime (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
      (p2TargetLcm4 p P2 u0 u1))
    (hd1 : (X - C P1.1 : Polynomial (F p)) ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hd2 : (X - C P2.1 : Polynomial (F p)) ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hUa : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hU : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)) ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hInv :
      uRS4P2TargetShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ∣
        Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 *
            EuclideanDomain.gcdA
              (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
              (uRS4P2TargetShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) - 1) :
    (vRS4P2TargetShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hgcd) ^ 2 %ₘ
        uRS4P2TargetShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 =
      (curvePoly p c0 c1 c2 c3 c4) %ₘ
        uRS4P2TargetShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 := by
  obtain ⟨k, hk⟩ := npoly4_dvd_of_p2_target_shared_root
    p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 h1a h1L haL hd1 hUa hd2 hU
  have hm1 : (X - C P1.1 : Polynomial (F p)).Monic := Polynomial.monic_X_sub_C _
  have hma : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).Monic := by monicity!
  have hstep0 :
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 =
        (X - C P1.1) * ((X ^ 2 + C ua1 * X + C ua0) * (p2TargetLcm4 p P2 u0 u1 * k)) := by
    rw [hk]; ring
  have hstep1 :
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 /ₘ (X - C P1.1) =
        (X ^ 2 + C ua1 * X + C ua0) * (p2TargetLcm4 p P2 u0 u1 * k) :=
    divByMonic_eq_of_dvd_mul hm1 hstep0
  have hstep2 :
      curBeforeMonic4P2TargetShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 =
        p2TargetLcm4 p P2 u0 u1 * k :=
    divByMonic_eq_of_dvd_mul hma hstep1
  set cur := curBeforeMonic4P2TargetShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1
  set U := uRS4P2TargetShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1
  have hlc : cur.leadingCoeff ≠ 0 := (not_congr Polynomial.leadingCoeff_eq_zero).mpr hcur
  have hNpoly_eq :
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 =
        cur * ((X - C P1.1) * (X ^ 2 + C ua1 * X + C ua0)) := by
    rw [hstep0, hstep2]
    ring
  have hU_cur : U ∣ cur := by
    refine ⟨C cur.leadingCoeff, ?_⟩
    dsimp [U, uRS4P2TargetShared]
    rw [mul_right_comm, ← C_mul, inv_mul_cancel₀ hlc, map_one, one_mul]
  have hcur_Npoly : cur ∣ Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 :=
    ⟨(X - C P1.1) * (X ^ 2 + C ua1 * X + C ua0), hNpoly_eq⟩
  have hNu_Npoly : U ∣ Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 :=
    dvd_trans hU_cur hcur_Npoly
  let E := Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1
  let Y := Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1
  let G := EuclideanDomain.gcdA Y U
  let f := curvePoly p c0 c1 c2 c3 c4
  have hU : U.Monic :=
    uRS4P2TargetShared_monic p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hcur
  have hInv' : U ∣ Y * G - 1 := hInv
  have hmod := sq_mod_eq_of_dvd_4 hU hNu_Npoly hInv'
  simpa only [vRS4P2TargetShared, U, E, Y, G, f] using hmod

end MumfordIdentity4P2TargetShared

section Dispatcher24

variable (c0 c1 c2 c3 c4 : F p) (P1 P2 : F p × F p)
variable (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)

/-- **`uRS4 ∣ Npoly4` OR the `P2`/`target` shared-root `lcm`-combine goes
through** — `h24`-free dispatcher, same shape as
`uRS4_dvd_Npoly4_or_p1_target_shared_root` with the roles of `h14`/`P1`-
`target` replaced by `h24`/`P2`-`target`. `Classical.em` on `h24`
supplies the case split; each branch closes directly by the theorem that
branch already has (`uRS4_dvd_Npoly4` for the coprime case,
`npoly4_dvd_of_p2_target_shared_root` for the shared-root case). -/
theorem uRS4_dvd_Npoly4_or_p2_target_shared_root
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
    (h34 : IsCoprime (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
      (X ^ 2 + C u1 * X + C u0))
    (h1L : IsCoprime (X - C P1.1 : Polynomial (F p))
      (p2TargetLcm4 p P2 u0 u1))
    (haL : IsCoprime (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
      (p2TargetLcm4 p P2 u0 u1)) :
    (P2.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P2.1 ∧
      IsCoprime (X - C P2.1 : Polynomial (F p)) (X ^ 2 + C u1 * X + C u0) ∧
      uRS4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ∣
        Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) ∨
    (¬ IsCoprime (X - C P2.1 : Polynomial (F p)) (X ^ 2 + C u1 * X + C u0) ∧
      (X - C P1.1) * (X ^ 2 + C ua1 * X + C ua0) * (p2TargetLcm4 p P2 u0 u1) ∣
        Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) := by
  rcases Classical.em
      (IsCoprime (X - C P2.1 : Polynomial (F p)) (X ^ 2 + C u1 * X + C u0)) with h24 | h24
  · exact Or.inl ⟨hP2_curve, h24,
      uRS4_dvd_Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1
        hne hA hP1_curve hP2_curve hMumfordUa hMumfordTarget h12 h13 h14 h23 h24 h34⟩
  · have hd1 := dvd_N_P1 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hA hP1_curve
    have hd2 := dvd_N_P2 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hA hP2_curve
    have hd3 := dvd_N_ua p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hA hMumfordUa
    have hd4 := dvd_N_u4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hA hMumfordTarget
    exact Or.inr ⟨h24,
      npoly4_dvd_of_p2_target_shared_root p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1
        h13 h1L haL hd1 hd3 hd2 hd4⟩

end Dispatcher24

/-! ## `h24`-free Mumford-identity dispatcher

Mirrors `vRS4_sq_eq_f_mod_uRS4_or_p1_target_shared_root` exactly,
dispatching on `h24` instead of `h14`, producing
`vRS4P2TargetShared_sq_eq_f_mod_uRS4P2TargetShared` in the shared-root
branch. -/

section Dispatcher24MumfordIdentity

variable (c0 c1 c2 c3 c4 : F p) (P1 P2 : F p × F p)
variable (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)

/-- **The Mumford identity, `h24`-free**: either the ordinary
`vRS4²≡f mod uRS4` (when `h24` holds), or the shared-root
`vRS4P2TargetShared²≡f mod uRS4P2TargetShared` (when it fails) — no
caller ever has to assume `IsCoprime (X - C P2.1) target`. -/
theorem vRS4_sq_eq_f_mod_uRS4_or_p2_target_shared_root
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
    (h34 : IsCoprime (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
      (X ^ 2 + C u1 * X + C u0))
    (h1L : IsCoprime (X - C P1.1 : Polynomial (F p)) (p2TargetLcm4 p P2 u0 u1))
    (haL : IsCoprime (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
      (p2TargetLcm4 p P2 u0 u1))
    (hcurShared :
      curBeforeMonic4P2TargetShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hgcd : (hcop : IsCoprime (X - C P2.1 : Polynomial (F p)) (X ^ 2 + C u1 * X + C u0)) →
      IsCoprime (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
        (uRS4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1))
    (hgcdShared :
      IsCoprime (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
        (uRS4P2TargetShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1))
    (hInvShared :
      uRS4P2TargetShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ∣
        Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 *
            EuclideanDomain.gcdA
              (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
              (uRS4P2TargetShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) - 1)
    (hInv : (hcop : IsCoprime (X - C P2.1 : Polynomial (F p)) (X ^ 2 + C u1 * X + C u0)) →
      uRS4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ∣
        Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 *
            EuclideanDomain.gcdA
              (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
              (uRS4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) - 1) :
    (∃ hcop : IsCoprime (X - C P2.1 : Polynomial (F p)) (X ^ 2 + C u1 * X + C u0),
      (vRS4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 (hgcd hcop)) ^ 2 %ₘ
          uRS4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 =
        (curvePoly p c0 c1 c2 c3 c4) %ₘ
          uRS4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) ∨
    (¬ IsCoprime (X - C P2.1 : Polynomial (F p)) (X ^ 2 + C u1 * X + C u0) ∧
      (vRS4P2TargetShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hgcdShared) ^ 2 %ₘ
          uRS4P2TargetShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 =
        (curvePoly p c0 c1 c2 c3 c4) %ₘ
          uRS4P2TargetShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) := by
  rcases Classical.em
      (IsCoprime (X - C P2.1 : Polynomial (F p)) (X ^ 2 + C u1 * X + C u0)) with h24 | h24
  · exact Or.inl ⟨h24,
      vRS4_sq_eq_f_mod_uRS4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1
        (hgcd h24) hne hA hP1_curve hP2_curve hMumfordUa hMumfordTarget h12 h13 h14 h23 h24 h34
        (hInv h24)⟩
  · have hd1 := dvd_N_P1 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hA hP1_curve
    have hd2 := dvd_N_P2 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hA hP2_curve
    have hd3 := dvd_N_ua p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hA hMumfordUa
    have hd4 := dvd_N_u4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hA hMumfordTarget
    exact Or.inr ⟨h24,
      vRS4P2TargetShared_sq_eq_f_mod_uRS4P2TargetShared
        p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1
        hcurShared hgcdShared h13 h1L haL hd1 hd2 hd3 hd4 hInvShared⟩

end Dispatcher24MumfordIdentity

end TheDataDerivation
end Genus2Lean
