import Mathlib
import Genus2Lean.ZeroD.TheDataDerivation.DataDerivationBasics
import Genus2Lean.ZeroD.Reduce.AlphaReduce
import Genus2Lean.ZeroD.Reduce.SharedRootCombining
import Genus2Lean.ZeroD.Reduce.P1TargetSharedRoot

/-! # Combining `Npoly4`'s four factors when `P2` and `u_a` share a root

Same fix as `P1UaSharedRoot.lean`, for `h23` (`IsCoprime (X - C P2.1)
u_a`) instead of `h13`. `h23` is FALSE exactly when `P2.1` is a root of
`u_a = X²+ua1·X+ua0` — `P2` is one of the two Jacobian points making up
`alpha•a`'s already-reduced Mumford pair. Nothing in the group law
forbids this either.

Reuses `isCoprime_X_sub_C_iff_eval_ne_zero` (`P1TargetSharedRoot.lean`)
and `lcm_dvd_of_dvd_dvd`/`prod_dvd_of_coprime_to_lcm`
(`SharedRootCombining.lean`) completely unchanged, merging
`(X - C P2.1)` and `u_a` into `lcm (X - C P2.1) u_a` instead of
`(X - C P2.1)`/`target`. `P1` and `target` remain ordinary product
factors, still assumed coprime to everything else — only `h23` is
removed as a blocker here. -/

namespace Genus2Lean
namespace TheDataDerivation

open Polynomial

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

section P2UaLcmShared

variable (c0 c1 c2 c3 c4 : F p) (P1 P2 : F p × F p)
variable (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)

/-- The merged `P2`/`u_a` factor via `lcm` — degree ≤ 3, degree exactly 2
when `P2.1` is one of `u_a`'s two roots (the generic shared-root case). -/
noncomputable def p2UaLcm4 : Polynomial (F p) :=
  EuclideanDomain.lcm (X - C P2.1 : Polynomial (F p))
    (X ^ 2 + C ua1 * X + C ua0)

/-- **The `h23`-free combining theorem.** Only needs `P1` and `target`'s
factors to be coprime to each other and to the MERGED `P2`/`u_a` factor —
`IsCoprime (X - C P2.1) u_a` is never assumed, so this covers exactly the
case ordinary `h23` cannot: `P2` sharing a root with `u_a`. -/
theorem npoly4_dvd_of_p2_ua_shared_root
    (h24 : IsCoprime (X - C P1.1 : Polynomial (F p))
      (X ^ 2 + C u1 * X + C u0))
    (h2L : IsCoprime (X - C P1.1 : Polynomial (F p))
      (p2UaLcm4 p P2 ua0 ua1))
    (hUL : IsCoprime (X ^ 2 + C u1 * X + C u0 : Polynomial (F p))
      (p2UaLcm4 p P2 ua0 ua1))
    (hd2 : (X - C P1.1 : Polynomial (F p)) ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hd4 : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)) ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hd1 : (X - C P2.1 : Polynomial (F p)) ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hd3 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) :
    (X - C P1.1) * (X ^ 2 + C u1 * X + C u0) * (p2UaLcm4 p P2 ua0 ua1) ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 :=
  prod_dvd_of_coprime_to_lcm h24 h2L hUL hd2 hd4 hd1 hd3

/-- **`(Npoly4 /ₘ (X-P1.1)) /ₘ target = p2UaLcm4 * k` for some `k`** —
`h23`-branch counterpart of `npoly4_quotient_eq_p1_target_lcm_mul_of_shared_root`.
Divides out `P1`'s and `target`'s factors first (both ordinary, unmerged
factors in this branch — the merge here is `P2`/`u_a`, not `P2`/`target`),
leaving the merged `p2UaLcm4` times a witness `k`. -/
theorem npoly4_quotient_eq_p2_ua_lcm_mul_of_shared_root
    (h24 : IsCoprime (X - C P1.1 : Polynomial (F p))
      (X ^ 2 + C u1 * X + C u0))
    (h2L : IsCoprime (X - C P1.1 : Polynomial (F p))
      (p2UaLcm4 p P2 ua0 ua1))
    (hUL : IsCoprime (X ^ 2 + C u1 * X + C u0 : Polynomial (F p))
      (p2UaLcm4 p P2 ua0 ua1))
    (hd2 : (X - C P1.1 : Polynomial (F p)) ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hd4 : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)) ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hd1 : (X - C P2.1 : Polynomial (F p)) ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hd3 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) :
    ∃ k : Polynomial (F p),
      (Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 /ₘ (X - C P1.1)) /ₘ
          (X ^ 2 + C u1 * X + C u0) =
        p2UaLcm4 p P2 ua0 ua1 * k := by
  obtain ⟨k, hk⟩ := npoly4_dvd_of_p2_ua_shared_root
    p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 h24 h2L hUL hd2 hd4 hd1 hd3
  refine ⟨k, ?_⟩
  have hm2 : (X - C P1.1 : Polynomial (F p)).Monic := Polynomial.monic_X_sub_C _
  have hmu : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).Monic := by monicity!
  have hstep0 :
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 =
        (X - C P1.1) * ((X ^ 2 + C u1 * X + C u0) * (p2UaLcm4 p P2 ua0 ua1 * k)) := by
    rw [hk]; ring
  have hstep1 :
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 /ₘ (X - C P1.1) =
        (X ^ 2 + C u1 * X + C u0) * (p2UaLcm4 p P2 ua0 ua1 * k) :=
    divByMonic_eq_of_dvd_mul hm2 hstep0
  exact divByMonic_eq_of_dvd_mul hmu hstep1

end P2UaLcmShared

section URS4P2UaShared

variable (c0 c1 c2 c3 c4 : F p) (P1 P2 : F p × F p)
variable (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)

/-- Two-step quotient of `Npoly4` by `(X-P1.1)` then `target` only — the
`h23`-branch analogue of `curBeforeMonic4P1TargetShared`, dividing out
the two ordinary (unmerged) factors in this branch. -/
noncomputable def curBeforeMonic4P2UaShared : Polynomial (F p) :=
  (Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 /ₘ (X - C P1.1)) /ₘ
    (X ^ 2 + C u1 * X + C u0)

/-- `u_RS,P2ua(x)`, monic-normalized `curBeforeMonic4P2UaShared` — same
`leadingCoeff⁻¹`-scaling construction as `uRS4`/`uRS4P1TargetShared`. -/
noncomputable def uRS4P2UaShared : Polynomial (F p) :=
  C (curBeforeMonic4P2UaShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff⁻¹ *
    curBeforeMonic4P2UaShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1

/-- `uRS4P2UaShared` is monic, given `curBeforeMonic4P2UaShared ≠ 0` —
byte-for-byte `uRS4P1TargetShared_monic`'s argument. -/
theorem uRS4P2UaShared_monic
    (hcur : curBeforeMonic4P2UaShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0) :
    (uRS4P2UaShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).Monic := by
  simp only [uRS4P2UaShared]
  set q := curBeforeMonic4P2UaShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 with hq
  have hlc : q.leadingCoeff ≠ 0 := (not_congr Polynomial.leadingCoeff_eq_zero).mpr hcur
  have hau : q.leadingCoeff * q.leadingCoeff⁻¹ = 1 := mul_inv_cancel₀ hlc
  have hdeg : (C q.leadingCoeff⁻¹ * q).natDegree = q.natDegree :=
    Polynomial.natDegree_C_mul_eq_of_mul_eq_one hau
  rw [Polynomial.Monic.def]
  change (C q.leadingCoeff⁻¹ * q).coeff (C q.leadingCoeff⁻¹ * q).natDegree = 1
  rw [hdeg, Polynomial.coeff_C_mul]
  exact inv_mul_cancel₀ hlc

/-- **`v_RS,P2ua(x) = -E4(x) * Y4(x)⁻¹ mod uRS4P2UaShared(x)`** — same
`EuclideanDomain.gcdA` Bézout-coefficient construction as
`vRS4`/`vRS4P1TargetShared`. -/
noncomputable def vRS4P2UaShared
    (_hgcd : IsCoprime (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
      (uRS4P2UaShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)) :
    Polynomial (F p) :=
  (-(Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) *
      EuclideanDomain.gcdA (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
        (uRS4P2UaShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)) %ₘ
    uRS4P2UaShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1

end URS4P2UaShared

/-! ## Mumford identity, `P2`/`u_a` shared-root branch

Mirrors `vRS4P1TargetShared_sq_eq_f_mod_uRS4P1TargetShared` exactly,
substituting `npoly4_quotient_eq_p2_ua_lcm_mul_of_shared_root`'s
hypothesis set (`h24`, `h2L`, `hUL` — no `IsCoprime (X - C P2.1) u_a`)
for the six pairwise facts. `sq_mod_eq_of_dvd_4` is reused completely
unchanged. -/

section MumfordIdentity4P2UaShared

variable (c0 c1 c2 c3 c4 : F p) (P1 P2 : F p × F p) (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)

/-- **The Mumford identity, `P2`/`u_a` shared-root branch**:
`v_RS,P2ua(x)^2 ≡ curvePoly(x) (mod u_RS,P2ua(x))`, valid when `P2` and
`u_a` share a root (so `IsCoprime (X - C P2.1) u_a` — used by
`vRS4_sq_eq_f_mod_uRS4` — is false), replacing it with the `lcm`-based
combining route. -/
theorem vRS4P2UaShared_sq_eq_f_mod_uRS4P2UaShared
    (hcur : curBeforeMonic4P2UaShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hgcd : IsCoprime (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
      (uRS4P2UaShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1))
    (h24 : IsCoprime (X - C P1.1 : Polynomial (F p))
      (X ^ 2 + C u1 * X + C u0))
    (h2L : IsCoprime (X - C P1.1 : Polynomial (F p)) (p2UaLcm4 p P2 ua0 ua1))
    (hUL : IsCoprime (X ^ 2 + C u1 * X + C u0 : Polynomial (F p))
      (p2UaLcm4 p P2 ua0 ua1))
    (hd1 : (X - C P2.1 : Polynomial (F p)) ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hd2 : (X - C P1.1 : Polynomial (F p)) ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hUa : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hU : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)) ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hInv :
      uRS4P2UaShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ∣
        Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 *
            EuclideanDomain.gcdA
              (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
              (uRS4P2UaShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) - 1) :
    (vRS4P2UaShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hgcd) ^ 2 %ₘ
        uRS4P2UaShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 =
      (curvePoly p c0 c1 c2 c3 c4) %ₘ
        uRS4P2UaShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 := by
  obtain ⟨k, hk⟩ := npoly4_dvd_of_p2_ua_shared_root
    p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 h24 h2L hUL hd2 hU hd1 hUa
  have hm2 : (X - C P1.1 : Polynomial (F p)).Monic := Polynomial.monic_X_sub_C _
  have hmu : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).Monic := by monicity!
  have hstep0 :
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 =
        (X - C P1.1) * ((X ^ 2 + C u1 * X + C u0) * (p2UaLcm4 p P2 ua0 ua1 * k)) := by
    rw [hk]; ring
  have hstep1 :
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 /ₘ (X - C P1.1) =
        (X ^ 2 + C u1 * X + C u0) * (p2UaLcm4 p P2 ua0 ua1 * k) :=
    divByMonic_eq_of_dvd_mul hm2 hstep0
  have hstep2 :
      curBeforeMonic4P2UaShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 =
        p2UaLcm4 p P2 ua0 ua1 * k :=
    divByMonic_eq_of_dvd_mul hmu hstep1
  set cur := curBeforeMonic4P2UaShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1
  set U := uRS4P2UaShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1
  have hlc : cur.leadingCoeff ≠ 0 := (not_congr Polynomial.leadingCoeff_eq_zero).mpr hcur
  have hNpoly_eq :
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 =
        cur * ((X - C P1.1) * (X ^ 2 + C u1 * X + C u0)) := by
    rw [hstep0, hstep2]
    ring
  have hU_cur : U ∣ cur := by
    refine ⟨C cur.leadingCoeff, ?_⟩
    dsimp [U, uRS4P2UaShared]
    rw [mul_right_comm, ← C_mul, inv_mul_cancel₀ hlc, map_one, one_mul]
  have hcur_Npoly : cur ∣ Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 :=
    ⟨(X - C P1.1) * (X ^ 2 + C u1 * X + C u0), hNpoly_eq⟩
  have hNu_Npoly : U ∣ Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 :=
    dvd_trans hU_cur hcur_Npoly
  let E := Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1
  let Y := Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1
  let G := EuclideanDomain.gcdA Y U
  let f := curvePoly p c0 c1 c2 c3 c4
  have hU : U.Monic :=
    uRS4P2UaShared_monic p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hcur
  have hInv' : U ∣ Y * G - 1 := hInv
  have hmod := sq_mod_eq_of_dvd_4 hU hNu_Npoly hInv'
  simpa only [vRS4P2UaShared, U, E, Y, G, f] using hmod

end MumfordIdentity4P2UaShared

section Dispatcher23

variable (c0 c1 c2 c3 c4 : F p) (P1 P2 : F p × F p)
variable (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)

/-- **`uRS4 ∣ Npoly4` OR the `P2`/`u_a` shared-root `lcm`-combine goes
through** — `h23`-free dispatcher, same shape as
`uRS4_dvd_Npoly4_or_p1_target_shared_root` (`P1TargetSharedRoot.lean`)
with the roles of `h14`/`P1`-`target` replaced by `h23`/`P2`-`u_a`.
`Classical.em` on `h23` supplies the case split; each branch closes
directly by the theorem that branch already has (`uRS4_dvd_Npoly4` for
the coprime case, `npoly4_dvd_of_p2_ua_shared_root` for the shared-root
case). -/
theorem uRS4_dvd_Npoly4_or_p2_ua_shared_root
    (hne : curBeforeMonic4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hA : MatrixNondegenerate4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hP1_curve : P1.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P1.1)
    (hP2_curve : P2.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P2.1)
    (hMumfordUa : IsMumfordUa p c0 c1 c2 c3 c4 ua0 ua1 va0 va1)
    (hMumfordTarget : IsMumfordTarget4 p c0 c1 c2 c3 c4 u0 u1 v0 v1)
    (h12 : IsCoprime (X - C P1.1 : Polynomial (F p)) (X - C P2.1))
    (h14 : IsCoprime (X - C P1.1 : Polynomial (F p))
      (X ^ 2 + C u1 * X + C u0))
    (h13 : IsCoprime (X - C P1.1 : Polynomial (F p))
      (X ^ 2 + C ua1 * X + C ua0))
    (h24 : IsCoprime (X - C P2.1 : Polynomial (F p))
      (X ^ 2 + C u1 * X + C u0))
    (h34 : IsCoprime (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
      (X ^ 2 + C u1 * X + C u0))
    (h2L : IsCoprime (X - C P1.1 : Polynomial (F p))
      (p2UaLcm4 p P2 ua0 ua1))
    (hUL : IsCoprime (X ^ 2 + C u1 * X + C u0 : Polynomial (F p))
      (p2UaLcm4 p P2 ua0 ua1)) :
    (P1.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P1.1 ∧
      IsCoprime (X - C P2.1 : Polynomial (F p)) (X ^ 2 + C ua1 * X + C ua0) ∧
      uRS4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ∣
        Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) ∨
    (¬ IsCoprime (X - C P2.1 : Polynomial (F p)) (X ^ 2 + C ua1 * X + C ua0) ∧
      (X - C P1.1) * (X ^ 2 + C u1 * X + C u0) * (p2UaLcm4 p P2 ua0 ua1) ∣
        Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) := by
  rcases Classical.em
      (IsCoprime (X - C P2.1 : Polynomial (F p)) (X ^ 2 + C ua1 * X + C ua0)) with h23 | h23
  · exact Or.inl ⟨hP1_curve, h23,
      uRS4_dvd_Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1
        hne hA hP1_curve hP2_curve hMumfordUa hMumfordTarget h12 h13 h14 h23 h24 h34⟩
  · have hd1 := dvd_N_P1 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hA hP1_curve
    have hd2 := dvd_N_P2 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hA hP2_curve
    have hd3 := dvd_N_ua p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hA hMumfordUa
    have hd4 := dvd_N_u4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hA hMumfordTarget
    exact Or.inr ⟨h23,
      npoly4_dvd_of_p2_ua_shared_root p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1
        h14 h2L hUL hd1 hd4 hd2 hd3⟩

end Dispatcher23

/-! ## `h23`-free Mumford-identity dispatcher

Mirrors `vRS4_sq_eq_f_mod_uRS4_or_p1_target_shared_root`
(`P1TargetSharedRoot.lean`) exactly, dispatching on `h23` instead of
`h14`. -/

section Dispatcher23MumfordIdentity

variable (c0 c1 c2 c3 c4 : F p) (P1 P2 : F p × F p)
variable (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)

/-- **The Mumford identity, `h23`-free**: either the ordinary
`vRS4²≡f mod uRS4` (when `h23` holds), or the shared-root
`vRS4P2UaShared²≡f mod uRS4P2UaShared` (when it fails) — no caller ever
has to assume `IsCoprime (X - C P2.1) u_a`. -/
theorem vRS4_sq_eq_f_mod_uRS4_or_p2_ua_shared_root
    (hne : curBeforeMonic4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hA : MatrixNondegenerate4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hP1_curve : P1.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P1.1)
    (hP2_curve : P2.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P2.1)
    (hMumfordUa : IsMumfordUa p c0 c1 c2 c3 c4 ua0 ua1 va0 va1)
    (hMumfordTarget : IsMumfordTarget4 p c0 c1 c2 c3 c4 u0 u1 v0 v1)
    (h12 : IsCoprime (X - C P1.1 : Polynomial (F p)) (X - C P2.1))
    (h14 : IsCoprime (X - C P1.1 : Polynomial (F p))
      (X ^ 2 + C u1 * X + C u0))
    (h13 : IsCoprime (X - C P1.1 : Polynomial (F p))
      (X ^ 2 + C ua1 * X + C ua0))
    (h24 : IsCoprime (X - C P2.1 : Polynomial (F p))
      (X ^ 2 + C u1 * X + C u0))
    (h34 : IsCoprime (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
      (X ^ 2 + C u1 * X + C u0))
    (h2L : IsCoprime (X - C P1.1 : Polynomial (F p)) (p2UaLcm4 p P2 ua0 ua1))
    (hUL : IsCoprime (X ^ 2 + C u1 * X + C u0 : Polynomial (F p))
      (p2UaLcm4 p P2 ua0 ua1))
    (hcurShared :
      curBeforeMonic4P2UaShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hgcd : (hcop : IsCoprime (X - C P2.1 : Polynomial (F p))
        (X ^ 2 + C ua1 * X + C ua0)) →
      IsCoprime (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
        (uRS4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1))
    (hgcdShared :
      IsCoprime (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
        (uRS4P2UaShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1))
    (hInvShared :
      uRS4P2UaShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ∣
        Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 *
            EuclideanDomain.gcdA
              (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
              (uRS4P2UaShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) - 1)
    (hInv : (hcop : IsCoprime (X - C P2.1 : Polynomial (F p))
        (X ^ 2 + C ua1 * X + C ua0)) →
      uRS4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ∣
        Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 *
            EuclideanDomain.gcdA
              (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
              (uRS4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) - 1) :
    (∃ hcop : IsCoprime (X - C P2.1 : Polynomial (F p)) (X ^ 2 + C ua1 * X + C ua0),
      (vRS4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 (hgcd hcop)) ^ 2 %ₘ
          uRS4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 =
        (curvePoly p c0 c1 c2 c3 c4) %ₘ
          uRS4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) ∨
    (¬ IsCoprime (X - C P2.1 : Polynomial (F p)) (X ^ 2 + C ua1 * X + C ua0) ∧
      (vRS4P2UaShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hgcdShared) ^ 2 %ₘ
          uRS4P2UaShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 =
        (curvePoly p c0 c1 c2 c3 c4) %ₘ
          uRS4P2UaShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) := by
  rcases Classical.em
      (IsCoprime (X - C P2.1 : Polynomial (F p)) (X ^ 2 + C ua1 * X + C ua0)) with h23 | h23
  · exact Or.inl ⟨h23,
      vRS4_sq_eq_f_mod_uRS4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1
        (hgcd h23) hne hA hP1_curve hP2_curve hMumfordUa hMumfordTarget h12 h13 h14 h23 h24 h34
        (hInv h23)⟩
  · have hd1 := dvd_N_P1 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hA hP1_curve
    have hd2 := dvd_N_P2 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hA hP2_curve
    have hd3 := dvd_N_ua p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hA hMumfordUa
    have hd4 := dvd_N_u4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hA hMumfordTarget
    exact Or.inr ⟨h23,
      vRS4P2UaShared_sq_eq_f_mod_uRS4P2UaShared
        p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1
        hcurShared hgcdShared h14 h2L hUL hd2 hd1 hd3 hd4 hInvShared⟩

end Dispatcher23MumfordIdentity

end TheDataDerivation
end Genus2Lean
