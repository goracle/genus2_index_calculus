import Mathlib
import Genus2Lean.ZeroD.TheDataDerivation.DataDerivationBasics
import Genus2Lean.ZeroD.Reduce.AlphaReduce
import Genus2Lean.ZeroD.Reduce.SharedRootCombining

/-! # Combining `Npoly4`'s four factors when `P1` and `target` share a root

`SharedRootCombining.lean` removed `h34` (`IsCoprime u_a target`) as a
blocker by replacing the `u_a`/`target` factor pair with their `lcm`,
which `EuclideanDomain.lcm_dvd` supplies unconditionally. This file does
the same for `h14` (`IsCoprime (X - C P1.1) target`), which is FALSE
exactly when `P1.1` is a root of `target = X²+u1·X+u0` — i.e. `P1` is one
of the two Jacobian points making up the target divisor. Nothing in the
group law forbids this either (it is the linear-vs-quadratic analogue of
the same phenomenon `h34`'s docstring already flags for `u_a`/`target`).

Unlike `h34` (quadratic vs quadratic), `h14` is linear vs quadratic, so
"coprimality fails" has a sharper characterization: `IsCoprime
(X - C a) q ↔ q.eval a ≠ 0` for any `q` over a field, proved below
(`isCoprime_X_sub_C_iff_eval_ne_zero`) via `Polynomial.dvd_iff_isRoot` and
`EuclideanDomain.isCoprime_of_dvd`-style reasoning — no low-level Bézout
computation needed. The combining step itself reuses
`SharedRootCombining.lean`'s `lcm_dvd_of_dvd_dvd`/`prod_dvd_of_coprime_to_lcm`
completely unchanged (both are already stated generically over any
`EuclideanDomain`, not specifically for `u_a`/`target`), merging
`(X - C P1.1)` and `target` into `lcm (X - C P1.1) target` instead of
`u_a`/`target`. `P2` and `u_a` remain ordinary product factors, still
assumed coprime to everything else — only `h14` is removed as a blocker
here, matching the scope `SharedRootCombining.lean` set for `h34`. -/

namespace Genus2Lean
namespace TheDataDerivation

open Polynomial

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

section EvalCoprimality

/-- **`IsCoprime (X - C a) q ↔ q.eval a ≠ 0`**, over any field. The
forward direction: if `q.eval a = 0` then `(X - C a) ∣ q`
(`dvd_iff_isRoot`), so `X - C a` divides both itself and `q`; since
`X - C a` is not a unit (it has degree 1), `IsCoprime.isUnit_of_dvd'`
rules this out. The backward direction uses
`X_sub_C_mul_divByMonic_eq_sub_modByMonic` (field-only) together with
`modByMonic_X_sub_C_eq_C_eval`: `(X - C a) * (q /ₘ (X - C a)) =
q - C (q.eval a)`, so dividing through by the unit `C (q.eval a)`
exhibits the Bézout identity directly. -/
theorem isCoprime_X_sub_C_iff_eval_ne_zero {a : F p} {q : Polynomial (F p)} :
    IsCoprime (X - C a : Polynomial (F p)) q ↔ q.eval a ≠ 0 := by
  constructor
  · intro hcop heval
    have hnu : ¬ IsUnit (X - C a : Polynomial (F p)) := by
      intro hu
      have h1 : (X - C a : Polynomial (F p)) = 1 :=
        (Polynomial.monic_X_sub_C a).eq_one_of_isUnit hu
      have hdeg : (X - C a : Polynomial (F p)).degree = 1 := Polynomial.degree_X_sub_C a
      rw [h1, Polynomial.degree_one] at hdeg
      exact absurd hdeg (by norm_num)
    exact hnu (hcop.isUnit_of_dvd' dvd_rfl (Polynomial.dvd_iff_isRoot.mpr heval))
  · intro heval
    have hkey : (X - C a) * (q /ₘ (X - C a)) = q - C (q.eval a) := by
      rw [Polynomial.X_sub_C_mul_divByMonic_eq_sub_modByMonic,
        Polynomial.modByMonic_X_sub_C_eq_C_eval]
    refine ⟨-C ((q.eval a)⁻¹) * (q /ₘ (X - C a)),
      C ((q.eval a)⁻¹), ?_⟩
    calc
      -C ((q.eval a)⁻¹) * (q /ₘ (X - C a)) * (X - C a) +
          C ((q.eval a)⁻¹) * q
          =
          C ((q.eval a)⁻¹) *
            (q - (X - C a) * (q /ₘ (X - C a))) := by
              ring
      _ = C ((q.eval a)⁻¹) * C (q.eval a) := by
            rw [hkey]
            ring
      _ = 1 := by
            rw [← C_mul]
            simp [heval]
end EvalCoprimality

section P1TargetLcmShared

variable (c0 c1 c2 c3 c4 : F p) (P1 P2 : F p × F p)
variable (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)

/-- The merged `P1`/`target` factor via `lcm` — degree ≤ 3, degree
exactly 2 when `P1.1` is one of `target`'s two roots (the generic
shared-root case). -/
noncomputable def p1TargetLcm4 : Polynomial (F p) :=
  EuclideanDomain.lcm (X - C P1.1 : Polynomial (F p))
    (X ^ 2 + C u1 * X + C u0)

/-- **The `h14`-free combining theorem.** Only needs `P2` and `u_a`'s
factors to be coprime to each other and to the MERGED `P1`/`target`
factor — `IsCoprime (X - C P1.1) target` is never assumed, so this
covers exactly the case ordinary `h14` cannot: `P1` sharing a root with
`target`. -/
theorem npoly4_dvd_of_p1_target_shared_root
    (h2a : IsCoprime (X - C P2.1 : Polynomial (F p))
      (X ^ 2 + C ua1 * X + C ua0))
    (h2L : IsCoprime (X - C P2.1 : Polynomial (F p))
      (p1TargetLcm4 p P1 u0 u1))
    (haL : IsCoprime (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
      (p1TargetLcm4 p P1 u0 u1))
    (hd2 : (X - C P2.1 : Polynomial (F p)) ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hd3 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hd1 : (X - C P1.1 : Polynomial (F p)) ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hd4 : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)) ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) :
    (X - C P2.1) * (X ^ 2 + C ua1 * X + C ua0) * (p1TargetLcm4 p P1 u0 u1) ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 :=
  prod_dvd_of_coprime_to_lcm h2a h2L haL hd2 hd3 hd1 hd4

/-- **`(Npoly4 /ₘ (X-P2.1)) /ₘ (u_a) = p1TargetLcm4 * k` for some `k`** —
h14-branch counterpart of `npoly4_quotient_eq_lcm_mul_of_shared_root`.
Divides out `P2`'s and `u_a`'s factors first (both ordinary, unmerged
factors in this branch — the merge here is `P1`/`target`, not `u_a`/
`target`), leaving the merged `p1TargetLcm4` times a witness `k`. As with
the h34 case, `p1TargetLcm4` is only defined up to a unit
(`EuclideanDomain.lcm`), so its monicity is established separately
(`uRS4P1TargetShared_monic` below) rather than folded into a third `/ₘ`
step here. -/
theorem npoly4_quotient_eq_p1_target_lcm_mul_of_shared_root
    (h2a : IsCoprime (X - C P2.1 : Polynomial (F p))
      (X ^ 2 + C ua1 * X + C ua0))
    (h2L : IsCoprime (X - C P2.1 : Polynomial (F p))
      (p1TargetLcm4 p P1 u0 u1))
    (haL : IsCoprime (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
      (p1TargetLcm4 p P1 u0 u1))
    (hd2 : (X - C P2.1 : Polynomial (F p)) ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hd3 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hd1 : (X - C P1.1 : Polynomial (F p)) ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hd4 : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)) ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) :
    ∃ k : Polynomial (F p),
      (Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 /ₘ (X - C P2.1)) /ₘ
          (X ^ 2 + C ua1 * X + C ua0) =
        p1TargetLcm4 p P1 u0 u1 * k := by
  obtain ⟨k, hk⟩ := npoly4_dvd_of_p1_target_shared_root
    p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 h2a h2L haL hd2 hd3 hd1 hd4
  refine ⟨k, ?_⟩
  have hm2 : (X - C P2.1 : Polynomial (F p)).Monic := Polynomial.monic_X_sub_C _
  have hma : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).Monic := by monicity!
  have hstep0 :
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 =
        (X - C P2.1) * ((X ^ 2 + C ua1 * X + C ua0) * (p1TargetLcm4 p P1 u0 u1 * k)) := by
    rw [hk]; ring
  have hstep1 :
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 /ₘ (X - C P2.1) =
        (X ^ 2 + C ua1 * X + C ua0) * (p1TargetLcm4 p P1 u0 u1 * k) :=
    divByMonic_eq_of_dvd_mul hm2 hstep0
  exact divByMonic_eq_of_dvd_mul hma hstep1

end P1TargetLcmShared

section URS4P1TargetShared

variable (c0 c1 c2 c3 c4 : F p) (P1 P2 : F p × F p)
variable (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)

/-- Two-step quotient of `Npoly4` by `(X-P2.1)` then `u_a` only — the
h14-branch analogue of `curBeforeMonic4LcmShared`, dividing out the two
ordinary (unmerged) factors in this branch. -/
noncomputable def curBeforeMonic4P1TargetShared : Polynomial (F p) :=
  (Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 /ₘ (X - C P2.1)) /ₘ
    (X ^ 2 + C ua1 * X + C ua0)

/-- `u_RS,P1target(x)`, monic-normalized `curBeforeMonic4P1TargetShared` —
same `leadingCoeff⁻¹`-scaling construction as `uRS4`/`uRS4LcmShared`. -/
noncomputable def uRS4P1TargetShared : Polynomial (F p) :=
  C (curBeforeMonic4P1TargetShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff⁻¹ *
    curBeforeMonic4P1TargetShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1

/-- `uRS4P1TargetShared` is monic, given `curBeforeMonic4P1TargetShared ≠
0` — byte-for-byte `uRS4LcmShared_monic`'s argument. -/
theorem uRS4P1TargetShared_monic
    (hcur : curBeforeMonic4P1TargetShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0) :
    (uRS4P1TargetShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).Monic := by
  simp only [uRS4P1TargetShared]
  set q := curBeforeMonic4P1TargetShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 with hq
  have hlc : q.leadingCoeff ≠ 0 := (not_congr Polynomial.leadingCoeff_eq_zero).mpr hcur
  have hau : q.leadingCoeff * q.leadingCoeff⁻¹ = 1 := mul_inv_cancel₀ hlc
  have hdeg : (C q.leadingCoeff⁻¹ * q).natDegree = q.natDegree :=
    Polynomial.natDegree_C_mul_eq_of_mul_eq_one hau
  rw [Polynomial.Monic.def]
  change (C q.leadingCoeff⁻¹ * q).coeff (C q.leadingCoeff⁻¹ * q).natDegree = 1
  rw [hdeg, Polynomial.coeff_C_mul]
  exact inv_mul_cancel₀ hlc

/-- **`v_RS,P1target(x) = -E4(x) * Y4(x)⁻¹ mod uRS4P1TargetShared(x)`** —
same `EuclideanDomain.gcdA` Bézout-coefficient construction as
`vRS4`/`vRS4LcmShared`. -/
noncomputable def vRS4P1TargetShared
    (_hgcd : IsCoprime (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
      (uRS4P1TargetShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)) :
    Polynomial (F p) :=
  (-(Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) *
      EuclideanDomain.gcdA (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
        (uRS4P1TargetShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)) %ₘ
    uRS4P1TargetShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1

end URS4P1TargetShared

/-! ## Mumford identity, `P1`/`target` shared-root branch

Mirrors `vRS4LcmShared_sq_eq_f_mod_uRS4LcmShared` exactly, substituting
`npoly4_quotient_eq_p1_target_lcm_mul_of_shared_root`'s hypothesis set
(`h2a`, `h2L`, `haL` — no `IsCoprime (X - C P1.1) target`) for the six
pairwise facts. `sq_mod_eq_of_dvd_4` is reused completely unchanged. -/

section MumfordIdentity4P1TargetShared

variable (c0 c1 c2 c3 c4 : F p) (P1 P2 : F p × F p) (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)

/-- **The Mumford identity, `P1`/`target` shared-root branch**:
`v_RS,P1target(x)^2 ≡ curvePoly(x) (mod u_RS,P1target(x))`, valid when
`P1` and `target` share a root (so `IsCoprime (X - C P1.1) target` — used
by `vRS4_sq_eq_f_mod_uRS4` — is false), replacing it with the `lcm`-based
combining route. -/
theorem vRS4P1TargetShared_sq_eq_f_mod_uRS4P1TargetShared
    (hcur : curBeforeMonic4P1TargetShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hgcd : IsCoprime (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
      (uRS4P1TargetShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1))
    (h2a : IsCoprime (X - C P2.1 : Polynomial (F p))
      (X ^ 2 + C ua1 * X + C ua0))
    (h2L : IsCoprime (X - C P2.1 : Polynomial (F p)) (p1TargetLcm4 p P1 u0 u1))
    (haL : IsCoprime (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
      (p1TargetLcm4 p P1 u0 u1))
    (hd1 : (X - C P1.1 : Polynomial (F p)) ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hd2 : (X - C P2.1 : Polynomial (F p)) ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hUa : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hU : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)) ∣
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hInv :
      uRS4P1TargetShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ∣
        Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 *
            EuclideanDomain.gcdA
              (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
              (uRS4P1TargetShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) - 1) :
    (vRS4P1TargetShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hgcd) ^ 2 %ₘ
        uRS4P1TargetShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 =
      (curvePoly p c0 c1 c2 c3 c4) %ₘ
        uRS4P1TargetShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 := by
  obtain ⟨k, hk⟩ := npoly4_dvd_of_p1_target_shared_root
    p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 h2a h2L haL hd2 hUa hd1 hU
  have hm2 : (X - C P2.1 : Polynomial (F p)).Monic := Polynomial.monic_X_sub_C _
  have hma : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).Monic := by monicity!
  have hstep0 :
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 =
        (X - C P2.1) * ((X ^ 2 + C ua1 * X + C ua0) * (p1TargetLcm4 p P1 u0 u1 * k)) := by
    rw [hk]; ring
  have hstep1 :
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 /ₘ (X - C P2.1) =
        (X ^ 2 + C ua1 * X + C ua0) * (p1TargetLcm4 p P1 u0 u1 * k) :=
    divByMonic_eq_of_dvd_mul hm2 hstep0
  have hstep2 :
      curBeforeMonic4P1TargetShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 =
        p1TargetLcm4 p P1 u0 u1 * k :=
    divByMonic_eq_of_dvd_mul hma hstep1
  set cur := curBeforeMonic4P1TargetShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1
  set U := uRS4P1TargetShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1
  have hlc : cur.leadingCoeff ≠ 0 := (not_congr Polynomial.leadingCoeff_eq_zero).mpr hcur
  have hNpoly_eq :
      Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 =
        cur * ((X - C P2.1) * (X ^ 2 + C ua1 * X + C ua0)) := by
    rw [hstep0, hstep2]
    ring
  have hU_cur : U ∣ cur := by
    refine ⟨C cur.leadingCoeff, ?_⟩
    dsimp [U, uRS4P1TargetShared]
    rw [mul_right_comm, ← C_mul, inv_mul_cancel₀ hlc, map_one, one_mul]
  have hcur_Npoly : cur ∣ Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 :=
    ⟨(X - C P2.1) * (X ^ 2 + C ua1 * X + C ua0), hNpoly_eq⟩
  have hNu_Npoly : U ∣ Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 :=
    dvd_trans hU_cur hcur_Npoly
  let E := Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1
  let Y := Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1
  let G := EuclideanDomain.gcdA Y U
  let f := curvePoly p c0 c1 c2 c3 c4
  have hU : U.Monic :=
    uRS4P1TargetShared_monic p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hcur
  have hInv' : U ∣ Y * G - 1 := hInv
  have hmod := sq_mod_eq_of_dvd_4 hU hNu_Npoly hInv'
  simpa only [vRS4P1TargetShared, U, E, Y, G, f] using hmod

end MumfordIdentity4P1TargetShared

section Dispatcher14

variable (c0 c1 c2 c3 c4 : F p) (P1 P2 : F p × F p)
variable (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)

/-- **`uRS4 ∣ Npoly4` OR the `P1`/`target` shared-root `lcm`-combine goes
through** — `h14`-free dispatcher, same shape as
`uRS4_dvd_Npoly4_or_shared_root` (`SharedRootCombining.lean`) with the
roles of `h34`/`u_a`-`target` replaced by `h14`/`P1`-`target`.
`Classical.em` on `h14` supplies the case split; each branch closes
directly by the theorem that branch already has (`uRS4_dvd_Npoly4` for
the coprime case, `npoly4_dvd_of_p1_target_shared_root` for the
shared-root case). -/
theorem uRS4_dvd_Npoly4_or_p1_target_shared_root
    (hne : curBeforeMonic4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hA : MatrixNondegenerate4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hP1_curve : P1.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P1.1)
    (hP2_curve : P2.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P2.1)
    (hMumfordUa : IsMumfordUa p c0 c1 c2 c3 c4 ua0 ua1 va0 va1)
    (hMumfordTarget : IsMumfordTarget4 p c0 c1 c2 c3 c4 u0 u1 v0 v1)
    (h12 : IsCoprime (X - C P1.1 : Polynomial (F p)) (X - C P2.1))
    (h13 : IsCoprime (X - C P1.1 : Polynomial (F p))
      (X ^ 2 + C ua1 * X + C ua0))
    (h23 : IsCoprime (X - C P2.1 : Polynomial (F p))
      (X ^ 2 + C ua1 * X + C ua0))
    (h24 : IsCoprime (X - C P2.1 : Polynomial (F p))
      (X ^ 2 + C u1 * X + C u0))
    (h34 : IsCoprime (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
      (X ^ 2 + C u1 * X + C u0))
    (h2L : IsCoprime (X - C P2.1 : Polynomial (F p))
      (p1TargetLcm4 p P1 u0 u1))
    (haL : IsCoprime (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
      (p1TargetLcm4 p P1 u0 u1)) :
    (P1.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P1.1 ∧
      IsCoprime (X - C P1.1 : Polynomial (F p)) (X ^ 2 + C u1 * X + C u0) ∧
      uRS4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ∣
        Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) ∨
    (¬ IsCoprime (X - C P1.1 : Polynomial (F p)) (X ^ 2 + C u1 * X + C u0) ∧
      (X - C P2.1) * (X ^ 2 + C ua1 * X + C ua0) * (p1TargetLcm4 p P1 u0 u1) ∣
        Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) := by
  rcases Classical.em
      (IsCoprime (X - C P1.1 : Polynomial (F p)) (X ^ 2 + C u1 * X + C u0)) with h14 | h14
  · exact Or.inl ⟨hP1_curve, h14,
      uRS4_dvd_Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1
        hne hA hP1_curve hP2_curve hMumfordUa hMumfordTarget h12 h13 h14 h23 h24 h34⟩
  · have hd1 := dvd_N_P1 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hA hP1_curve
    have hd2 := dvd_N_P2 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hA hP2_curve
    have hd3 := dvd_N_ua p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hA hMumfordUa
    have hd4 := dvd_N_u4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hA hMumfordTarget
    exact Or.inr ⟨h14,
      npoly4_dvd_of_p1_target_shared_root p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1
        h23 h2L haL hd2 hd3 hd1 hd4⟩

end Dispatcher14

/-! ## `h14`-free Mumford-identity dispatcher

The divisibility dispatcher above (`uRS4_dvd_Npoly4_or_p1_target_shared_root`)
only reaches `uRS4 ∣ Npoly4`, not the actual Mumford identity
`v² ≡ f (mod u)` that `Reduce`'s correctness ultimately needs
(`vRS4_sq_eq_f_mod_uRS4` in the ordinary case). This section closes that
gap for the `h14` branch specifically: dispatches on `h14`, and in the
shared-root case produces `vRS4P1TargetShared_sq_eq_f_mod_uRS4P1TargetShared`
rather than stopping at divisibility. Each branch needs its own `hgcd`
(coprimality of `Ypoly4` with that branch's own `u`-polynomial — `uRS4` vs
`uRS4P1TargetShared` are different polynomials, so this cannot be a single
shared hypothesis), matching `ReduceDispatch`'s existing convention of
taking each branch's inputs as `P1≠P2/P1=P2`-style implications rather
than assuming both up front. -/

section Dispatcher14MumfordIdentity

variable (c0 c1 c2 c3 c4 : F p) (P1 P2 : F p × F p)
variable (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)

/-- **The Mumford identity, `h14`-free**: either the ordinary
`vRS4²≡f mod uRS4` (when `h14` holds), or the shared-root
`vRS4P1TargetShared²≡f mod uRS4P1TargetShared` (when it fails) — no
caller ever has to assume `IsCoprime (X - C P1.1) target`. -/
theorem vRS4_sq_eq_f_mod_uRS4_or_p1_target_shared_root
    (hne : curBeforeMonic4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hA : MatrixNondegenerate4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hP1_curve : P1.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P1.1)
    (hP2_curve : P2.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P2.1)
    (hMumfordUa : IsMumfordUa p c0 c1 c2 c3 c4 ua0 ua1 va0 va1)
    (hMumfordTarget : IsMumfordTarget4 p c0 c1 c2 c3 c4 u0 u1 v0 v1)
    (h12 : IsCoprime (X - C P1.1 : Polynomial (F p)) (X - C P2.1))
    (h13 : IsCoprime (X - C P1.1 : Polynomial (F p))
      (X ^ 2 + C ua1 * X + C ua0))
    (h23 : IsCoprime (X - C P2.1 : Polynomial (F p))
      (X ^ 2 + C ua1 * X + C ua0))
    (h24 : IsCoprime (X - C P2.1 : Polynomial (F p))
      (X ^ 2 + C u1 * X + C u0))
    (h34 : IsCoprime (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
      (X ^ 2 + C u1 * X + C u0))
    (h2L : IsCoprime (X - C P2.1 : Polynomial (F p)) (p1TargetLcm4 p P1 u0 u1))
    (haL : IsCoprime (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
      (p1TargetLcm4 p P1 u0 u1))
    (hcurShared :
      curBeforeMonic4P1TargetShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hgcd : (hcop : IsCoprime (X - C P1.1 : Polynomial (F p)) (X ^ 2 + C u1 * X + C u0)) →
      IsCoprime (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
        (uRS4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1))
    (hgcdShared :
      IsCoprime (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
        (uRS4P1TargetShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1))
    (hInvShared :
      uRS4P1TargetShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ∣
        Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 *
            EuclideanDomain.gcdA
              (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
              (uRS4P1TargetShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) - 1)
    (hInv : (hcop : IsCoprime (X - C P1.1 : Polynomial (F p)) (X ^ 2 + C u1 * X + C u0)) →
      uRS4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ∣
        Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 *
            EuclideanDomain.gcdA
              (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
              (uRS4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) - 1) :
    (∃ hcop : IsCoprime (X - C P1.1 : Polynomial (F p)) (X ^ 2 + C u1 * X + C u0),
      (vRS4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 (hgcd hcop)) ^ 2 %ₘ
          uRS4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 =
        (curvePoly p c0 c1 c2 c3 c4) %ₘ
          uRS4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) ∨
    (¬ IsCoprime (X - C P1.1 : Polynomial (F p)) (X ^ 2 + C u1 * X + C u0) ∧
      (vRS4P1TargetShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hgcdShared) ^ 2 %ₘ
          uRS4P1TargetShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 =
        (curvePoly p c0 c1 c2 c3 c4) %ₘ
          uRS4P1TargetShared p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) := by
  rcases Classical.em
      (IsCoprime (X - C P1.1 : Polynomial (F p)) (X ^ 2 + C u1 * X + C u0)) with h14 | h14
  · exact Or.inl ⟨h14,
      vRS4_sq_eq_f_mod_uRS4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1
        (hgcd h14) hne hA hP1_curve hP2_curve hMumfordUa hMumfordTarget h12 h13 h14 h23 h24 h34
        (hInv h14)⟩
  · have hd1 := dvd_N_P1 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hA hP1_curve
    have hd2 := dvd_N_P2 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hA hP2_curve
    have hd3 := dvd_N_ua p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hA hMumfordUa
    have hd4 := dvd_N_u4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hA hMumfordTarget
    exact Or.inr ⟨h14,
      vRS4P1TargetShared_sq_eq_f_mod_uRS4P1TargetShared
        p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1
        hcurShared hgcdShared h23 h2L haL hd1 hd2 hd3 hd4 hInvShared⟩
          
end Dispatcher14MumfordIdentity

end TheDataDerivation
end Genus2Lean
