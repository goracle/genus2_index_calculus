import Mathlib
import Genus2Lean.ZeroD.PrincipalWitness
import Genus2Lean.ZeroD.AlphaLocusDegreeUniform

/-!
# Assembling `reducedClass_eq_of_isReduction'` from `PrincipalWitness.lean`'s
# lemma stack

Per `ROADMAP-principal-witness-assembly.md`'s "Recommended order for the
next pass". This file does the wiring the roadmap scoped precisely:

1. The exact factorization equation `Npoly4 = npoly4Lcm4 * uRS4General`
   (up to the leading-coefficient unit already tracked by `uRS4General`'s
   own definition) — needed as an actual EQUATION (`hAU` in the
   `PrincipalWitness.lean` lemma-stack sense), not just the divisibility
   facts `npoly4Lcm4_dvd_Npoly4`/`uRS4General_dvd_Npoly4` already on file.
2. The geometric-classification bridge: connecting "`P` is a root of one
   of `npoly4Lcm4`'s four sub-factors" to `Finset H.Point`-membership in
   `Sold := Sanchor ∪ {sa.P1, sa.P2}` with `ordAt P (-va-or-similar) 1 = 1`
   (roadmap step 3, "the one piece of genuinely new Lean content").
3. Assembly into `reducedClass_eq_of_isReduction'` itself.

Scoped, per the roadmap's explicit recommendation, to the SPLIT case only
(both `ua`/`uRS4General` have two rational roots) — the irreducible case
is a documented non-goal here, not attempted.
-/

noncomputable section

open HyperellipticPolynomial
open HyperellipticPolynomial.Divisor
open Polynomial

namespace Genus2Lean
namespace DecoupledSystem

open TheDataDerivation

/-! ## Step 1: the exact factorization equation

`npoly4Lcm4_dvd_Npoly4` only gives divisibility; the `PrincipalWitness.lean`
lemma stack (lemma 7/8/13/13c) needs the actual equation `pairNorm H E Y =
A * U`. This section derives it from `curBeforeMonic4General`'s definition
(`Npoly4 /ₘ npoly4Lcm4`) via `divByMonic_eq_of_dvd_mul` (already used for
exactly this purpose inside `uRS4General_dvd_Npoly4`'s own proof — this
section just names the intermediate fact as its own reusable lemma, since
`uRS4General_dvd_Npoly4`'s proof only produces `curBeforeMonic4General ∣
Npoly4`-flavored intermediate `have`s, not the plain product equation with
`npoly4Lcm4` on the other side). -/

section ExactFactorization

variable (p : ℕ) [hp : Fact (Nat.Prime p)]
variable (c0 c1 c2 c3 c4 : F p) (P1 P2 : F p × F p)
variable (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)

/-- **`Npoly4 = npoly4Lcm4 * curBeforeMonic4General`, exactly** (no unit
slack yet — that's absorbed in the next lemma once `uRS4General`'s
`leadingCoeff⁻¹`-rescaling is folded in). Direct read-off of
`npoly4Lcm4_dvd_Npoly4`'s witness (`⟨k,hk⟩`) composed with
`divByMonic_eq_of_dvd_mul` — this is the same pair of facts
`uRS4General_dvd_Npoly4`'s own proof already derives internally as
`hstep`/`hk`, just extracted here as its own named, reusable lemma instead
of staying buried inside that proof. -/
theorem Npoly4_eq_npoly4Lcm4_mul_curBeforeMonic4General
    (hA : MatrixNondegenerate4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hP1_curve : P1.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P1.1)
    (hP2_curve : P2.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P2.1)
    (hMumfordUa : IsMumfordUa p c0 c1 c2 c3 c4 ua0 ua1 va0 va1)
    (hMumfordTarget : IsMumfordTarget4 p c0 c1 c2 c3 c4 u0 u1 v0 v1) :
    Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 =
      npoly4Lcm4 p P1 P2 ua0 ua1 u0 u1 *
        curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 := by
  have hLdvd := npoly4Lcm4_dvd_Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1
    hA hP1_curve hP2_curve hMumfordUa hMumfordTarget
  have hLmonic := npoly4Lcm4_monic p P1 P2 ua0 ua1 u0 u1
  obtain ⟨k, hk⟩ := hLdvd
  have hstep :
      curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 = k := by
    simp only [curBeforeMonic4General]
    exact divByMonic_eq_of_dvd_mul hLmonic hk
  rw [hk, hstep]

/-- **`Npoly4 = npoly4Lcm4 * uRS4General`, exactly** — the equation the
`PrincipalWitness.lean` lemma stack's `hAU`-shaped hypotheses need. Folds
in `uRS4General`'s `leadingCoeff⁻¹`-rescaling relative to
`curBeforeMonic4General`: `curBeforeMonic4General = leadingCoeff •
uRS4General` (since `uRS4General := C leadingCoeff⁻¹ *
curBeforeMonic4General` and `leadingCoeff ≠ 0`), so multiplying
`Npoly4_eq_npoly4Lcm4_mul_curBeforeMonic4General`'s RHS by
`leadingCoeff⁻¹`/`leadingCoeff` and re-associating gives this unit-free
form directly, with `npoly4Lcm4` (not `npoly4Lcm4` scaled) as the exact
left factor. -/
theorem Npoly4_eq_npoly4Lcm4_mul_uRS4General
    (hne : curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hA : MatrixNondegenerate4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hP1_curve : P1.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P1.1)
    (hP2_curve : P2.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P2.1)
    (hMumfordUa : IsMumfordUa p c0 c1 c2 c3 c4 ua0 ua1 va0 va1)
    (hMumfordTarget : IsMumfordTarget4 p c0 c1 c2 c3 c4 u0 u1 v0 v1) :
    Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 =
      npoly4Lcm4 p P1 P2 ua0 ua1 u0 u1 *
        (C (curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff *
          uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) := by
  have hbase := Npoly4_eq_npoly4Lcm4_mul_curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2
    ua0 ua1 va0 va1 u0 u1 v0 v1 hA hP1_curve hP2_curve hMumfordUa hMumfordTarget
  set q := curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 with hq
  have hlc : q.leadingCoeff ≠ 0 := (not_congr Polynomial.leadingCoeff_eq_zero).mpr hne
  have hunfold : uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 =
      C q.leadingCoeff⁻¹ * q := rfl
  rw [hbase, hunfold]
  -- Goal is now `npoly4Lcm4 * q = npoly4Lcm4 * (C leadingCoeff * (C leadingCoeff⁻¹ * q))`;
  -- reduce the RHS's scalar pair to `1` and cancel.
  have hscale : C q.leadingCoeff * (C q.leadingCoeff⁻¹ * q) = q := by
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hlc, map_one, one_mul]
  rw [hscale]

end ExactFactorization

/-! ## Step 2 (roadmap step 3, part 1): the flat-product identity for
`npoly4Lcm4`

Per the ChatGPT reply: prove `lcm f g = f * g` as a literal equation
(not just an associate) for monic coprime `f g`, then apply it in the
same binary-tree shape as `npoly4Lcm4`'s own definition
(`lcm(lcm q1 q2, lcm q3 q4)`) — inner-then-outer, matching the reply's
explicit recommendation not to try to flatten in one shot. All three
coprimality facts this needs (`isCoprime_linear_pair_of_ne`,
`isCoprime_quadratic_pair_of_ne_of_no_shared_root`,
`isCoprime_lcm12_lcm34_of_no_shared_root`) are already proved in
`GeneralSharedRoot.lean` — this section only adds the "coprime ⟹ literal
product" step (previously only "coprime ⟹ associate, hence same degree"
was on file) and the final 3-step assembly. -/

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

/-! ## Step 3: the geometric-classification bridge (roadmap step 3 proper)

The genuinely new content this roadmap flags: connect "`P` is a simple
root of one of `npoly4Lcm4`'s four flat sub-factors" to `ordAt P
npoly4Lcm4 0 = 1` at the K=4/`H.Point` level, so that `PrincipalWitness.
lean`'s lemmas 14/15 (`ordAtFrac_eq_one_of_old_point`/
`ordAtFrac_neg_eq_one_of_new_point`, both of which take `ordAt P A 0 = 1`
as a literal hypothesis) can actually be invoked at each of the 6 named
points (`sa.P1`, `sa.P2`, `ua`'s two roots, `u_target`'s two roots).

Step 1/Step 2 above supply the two facts (`Npoly4 = npoly4Lcm4 *
uRS4General` exactly; `npoly4Lcm4 = unit * flat product` in the split
case) that make this step MECHANICAL once composed with `PrincipalWitness.
lean`'s `ordAt_A_eq_one_of_eval_ne_zero` (Layer 3) — but "mechanical" here
still means instantiating Layer 3 once per point, threading `H.Point`
membership in `Sanchor ∪ {sa.P1,sa.P2}` vs `S` through each case, and
handling the `IsUnit`-scalar on `npoly4Lcm4`'s flat-product identity
(Layer 3's own `ordAt`-of-a-product lemmas are stated for exact products,
not up-to-unit ones, so `ordAt P (unit • flat) 0 = ordAt P flat 0` needed
its own one-line justification — this was the "one care point" the
roadmap's own resolution flagged and deferred, and Part C below closes it).

ChatGPT's reply confirmed the architecture and closed both
open sub-questions:

- **Part A (outer lcm step)**: no hidden interaction between the two
  inner `lcm`s — the outer coprimality is the ONLY extra ingredient
  needed, already exactly what `npoly4Lcm4_eq_flat_product` (Step 2
  above) uses. Nothing further to do here.
- **Part B (quadratic splitting)**: the coefficient-expansion route
  (`quadratic_eq_mul_X_sub_C`, already proved above) is confirmed as the
  right choice for this local assembly, over the general `Polynomial.
  roots`-product route.
- **Part C (unit-scaling invariance of `ordAt`)**: confirmed the
  `ordAt (C c * A) (C c * B) = ordAt A B`-style lemma is the right idiom
  — and it's ALREADY ON FILE, not something to prove fresh:
  `ordAt_C_zero`/`ordAt_C_mul_eq` (`RiemannRochGenus2.lean`). No new
  lemma needed; Step 3 just composes these with Layer 3.
- **Part D (six-point case split)**: recommended NOT six nested
  `by_cases`, but a two-stage approach — a `support_cases` lemma turning
  `P ∈ S` into a 6-way named disjunction, called from a `by_cases P ∈ S`
  split, with the "elsewhere" branch closed by `simp` from the two
  `hsuppAnchor`/`hsupp`-style non-membership facts. Deferred to the
  actual assembly at `reducedClass_eq_of_isReduction'`'s call site
  (`AlphaLocusDegreeUniform.lean`), matching the roadmap's own scoping
  (this file stays about the `E,Y,A,U`-level bridge, not the
  `SampleTargetFromAlpha`-specific wiring).

This section writes Part C (the unit-scaled Layer 3, generalized per
ChatGPT's recommendation around a single designated factor rather than
`P1`-specific), the one piece of new Lean content Steps A-C leave to
write. Part D (the `Sold`/`Snew` case-split assembly) is left for
`AlphaLocusDegreeUniform.lean`'s own proof body, per the roadmap's
explicit scoping (`PrincipalWitness.lean`/`PrincipalWitnessAssembly.lean`
stay ignorant of `SampleTargetFromAlpha`). -/

section GeometricBridge

variable {k : Type*} [Field k]
variable {H : HyperellipticPolynomial k}

/-- **Generalized Layer 3, unit-scaled, around a single designated linear
factor `X - C a`** — per ChatGPT's explicit recommendation, this
supersedes needing four separately hand-written re-associations of the
flat product: the caller reshapes whichever of the four sub-factors is
`X - C a` to the front via `ring`/`mul_comm`-style rewriting (cheap, since
`Polynomial (F p)` is commutative) BEFORE calling this lemma, so this
lemma itself only ever sees the shape `((linX a * F₁) * F₂) * F₃`
directly — no index parameter needed. Adds exactly one new ingredient
relative to `PrincipalWitness.lean`'s own `ordAt_A_eq_one_of_eval_ne_zero`
(Layer 3): the leading `C u` unit scalar coming from
`npoly4Lcm4_eq_flat_product`'s RHS, discharged via `ordAt_C_zero`/
`ordAt_C_mul_eq` (`RiemannRochGenus2.lean`, already proved, confirmed by
ChatGPT as the right idiom — no fresh valuation-theoretic argument
needed). -/
theorem ordAt_unit_mul_A_eq_one_of_eval_ne_zero
    [IsDedekindDomain (CoordinateRing H)] [DecidableEq k]
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (P : H.Point) (h_bot : pointIdeal P ≠ ⊥) (a u : k) (hu : u ≠ 0)
    (hPX : P.X = a) (hPY : P.Y ≠ 0)
    (F₁ F₂ F₃ : k[X])
    (hF₁_eval : F₁.eval a ≠ 0) (hF₂_eval : F₂.eval a ≠ 0) (hF₃_eval : F₃.eval a ≠ 0) :
    ordAt P (Polynomial.C u * (((linX a * F₁) * F₂) * F₃)) (0 : k[X]) = 1 := by
  have hflat : ordAt P (((linX a * F₁) * F₂) * F₃) (0 : k[X]) = 1 :=
    ordAt_A_eq_one_of_eval_ne_zero hchar hsf P h_bot a hPX hPY F₁ F₂ F₃
      hF₁_eval hF₂_eval hF₃_eval
  have hF₁ne : F₁ ≠ 0 := fun h => hF₁_eval (by rw [h]; simp)
  have hF₂ne : F₂ ≠ 0 := fun h => hF₂_eval (by rw [h]; simp)
  have hF₃ne : F₃ ≠ 0 := fun h => hF₃_eval (by rw [h]; simp)
  have hflatne : (((linX a * F₁) * F₂) * F₃ : k[X]) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (linX_ne_zero a) hF₁ne) hF₂ne) hF₃ne
  have hPQ : ¬ (((linX a * F₁) * F₂) * F₃ = 0 ∧ (0 : k[X]) = 0) :=
    fun h => hflatne h.1
  have hstep := ordAt_C_mul_eq u hu (((linX a * F₁) * F₂) * F₃) 0 hPQ P
  simpa using hstep.trans hflat

/-! ## Step 4 (Part D, partial): instantiating the geometric bridge at each
of the four `npoly4Lcm4` roots that live on a linear sub-factor
(`sa.P1`/`sa.P2`) — the two quadratic-factor roots (`ua`'s two roots,
`u_target`'s two roots) additionally need `quadratic_eq_mul_X_sub_C` (Step
2 above) to split the quadratic into its two linear factors first, and are
NOT attempted in this section; see the trailing status note below for why.

This section composes `npoly4Lcm4_eq_flat_product` (Step 2) with
`ordAt_unit_mul_A_eq_one_of_eval_ne_zero` (Part C) to get `ordAt P
npoly4Lcm4 0 = 1` at `P := H.Point.mk P1.1 P1.2 h1` (the point built from
`sa.P1`'s own coordinates), given the four coprimality-flavored
eval-nonvanishing hypotheses `npoly4Lcm4_eq_flat_product` already needs.
This is genuinely new Lean content (not previously on file anywhere) — the
first concrete instantiation of the flat-product bridge at a real point,
rather than left at the polynomial level. -/

section GeometricInstantiation

variable (p : ℕ) [hp : Fact (Nat.Prime p)] [Fact (p ≠ 2)]
variable {H : HyperellipticPolynomial (F p)} [IsDedekindDomain (CoordinateRing H)]

/-- **`ordAt` of `npoly4Lcm4` at the point built from `P1`'s own coordinates
is `1`**, in the fully-split/no-shared-root case. Composes
`npoly4Lcm4_eq_flat_product` (the flat-product identity, up to an explicit
unit) with `ordAt_unit_mul_A_eq_one_of_eval_ne_zero` (the unit-scaled Layer
3) — the caller supplies the point itself (`P`, with `hPX`/`hPY` pinning
its coordinates to `P1`) rather than this lemma constructing `H.Point.mk`
internally, since `H.Equation`'s own proof obligation is exactly
`P1_on_curve`-shaped data this lemma has no way to manufacture on its own. -/
theorem ordAt_npoly4Lcm4_eq_one_of_P1
    (hchar : (2 : F p) ≠ 0) (hsf : Squarefree H.f)
    (P1 P2 : F p × F p) (ua0 ua1 u0 u1 : F p)
    (P : H.Point) (h_bot : pointIdeal P ≠ ⊥) (hPX : P.X = P1.1) (hPY : P.Y ≠ 0)
    (h12 : P1.1 ≠ P2.1)
    (hne34 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ≠ X ^ 2 + C u1 * X + C u0)
    (hnoroot34 : ¬ ∃ r : F p, (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval r = 0 ∧
        (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval r = 0)
    (hP1ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P1.1 = 0)
    (hP1target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P1.1 = 0)
    (hP2ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P2.1 = 0)
    (hP2target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P2.1 = 0) :
    ordAt P (npoly4Lcm4 p P1 P2 ua0 ua1 u0 u1) (0 : Polynomial (F p)) = 1 := by
  rw [npoly4Lcm4_eq_flat_product p P1 P2 ua0 ua1 u0 u1 h12 hne34 hnoroot34
    hP1ua hP1target hP2ua hP2target]
  -- Reshape the flat product so `linX P1.1 = X - C P1.1` sits at the front,
  -- matching `ordAt_unit_mul_A_eq_one_of_eval_ne_zero`'s expected shape
  -- `C u * (((linX a * F₁) * F₂) * F₃)`.
  have hshape :
      (((X - C P1.1 : Polynomial (F p)) * (X - C P2.1)) *
        ((X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) * (X ^ 2 + C u1 * X + C u0))) =
      ((linX P1.1 * (X - C P2.1 : Polynomial (F p))) *
        (X ^ 2 + C ua1 * X + C ua0)) * (X ^ 2 + C u1 * X + C u0) := by
    simp only [linX]; ring
  rw [hshape]
  -- The unit `npoly4Lcm4_eq_flat_product` names is a product of four
  -- `leadingCoeff⁻¹` terms; each is nonzero because each underlying
  -- polynomial (`npoly4LcmRaw`, the two inner gcds) is itself nonzero, being
  -- built from products/gcds of nonzero monics (`X - C _`/quadratics with
  -- leading coefficient `1 ≠ 0`) — hence each `leadingCoeff` is nonzero, so
  -- each `leadingCoeff⁻¹` is nonzero, so the product of the four is nonzero.
  have hune : ∀ q : Polynomial (F p), q.Monic → q ≠ 0 → q.leadingCoeff⁻¹ ≠ 0 := by
    intro q _ hq0
    exact inv_ne_zero ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hq0)
  have hm1 : (X - C P1.1 : Polynomial (F p)).Monic := Polynomial.monic_X_sub_C _
  have hm2 : (X - C P2.1 : Polynomial (F p)).Monic := Polynomial.monic_X_sub_C _
  have hm3 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).Monic := by monicity!
  have hm4 : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).Monic := by monicity!
  have hL12ne : (EuclideanDomain.lcm (X - C P1.1 : Polynomial (F p)) (X - C P2.1)) ≠ 0 :=
    fun h => (EuclideanDomain.lcm_eq_zero_iff.mp h).elim hm1.ne_zero hm2.ne_zero
  have hL34ne :
      (EuclideanDomain.lcm (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
        (X ^ 2 + C u1 * X + C u0)) ≠ 0 :=
    fun h => (EuclideanDomain.lcm_eq_zero_iff.mp h).elim hm3.ne_zero hm4.ne_zero
  have hGne :
      (EuclideanDomain.gcd
        (EuclideanDomain.lcm (X - C P1.1 : Polynomial (F p)) (X - C P2.1))
        (EuclideanDomain.lcm (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
          (X ^ 2 + C u1 * X + C u0))) ≠ 0 :=
    fun h => hL12ne (EuclideanDomain.gcd_eq_zero_iff.mp h).1
  have hgcd12ne : (EuclideanDomain.gcd (X - C P1.1 : Polynomial (F p)) (X - C P2.1)) ≠ 0 :=
    fun h => hm1.ne_zero (EuclideanDomain.gcd_eq_zero_iff.mp h).1
  have hgcd34ne :
      (EuclideanDomain.gcd (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
        (X ^ 2 + C u1 * X + C u0)) ≠ 0 :=
    fun h => hm3.ne_zero (EuclideanDomain.gcd_eq_zero_iff.mp h).1
  have hrawne : (npoly4LcmRaw p P1 P2 ua0 ua1 u0 u1) ≠ 0 :=
    npoly4LcmRaw_ne_zero p P1 P2 ua0 ua1 u0 u1
  exact ordAt_unit_mul_A_eq_one_of_eval_ne_zero hchar hsf P h_bot _ _
    (mul_ne_zero (mul_ne_zero (mul_ne_zero
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hrawne |> inv_ne_zero)
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hGne |> inv_ne_zero))
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hgcd12ne |> inv_ne_zero))
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hgcd34ne |> inv_ne_zero))
    hPX hPY (X - C P2.1) (X ^ 2 + C ua1 * X + C ua0) (X ^ 2 + C u1 * X + C u0)
    (by rw [hPX] at *; simpa using sub_ne_zero.mpr h12)
    (by rw [hPX] at *; exact hP1ua)
    (by rw [hPX] at *; exact hP1target)

end GeometricInstantiation

section GeometricInstantiation

variable (p : ℕ) [hp : Fact (Nat.Prime p)] [Fact (p ≠ 2)]
variable {H : HyperellipticPolynomial (F p)} [IsDedekindDomain (CoordinateRing H)]

/-- **`ordAt` of `npoly4Lcm4` at the point built from `P2`'s own coordinates
is `1`** — the exact mirror of `ordAt_npoly4Lcm4_eq_one_of_P1`, reshaping
the flat product so `linX P2.1` sits at the front instead of `linX P1.1`
(via `mul_comm`/`ring`, same as the `P1` case but with the two linear
factors swapped). Same composition (`npoly4Lcm4_eq_flat_product` +
`ordAt_unit_mul_A_eq_one_of_eval_ne_zero`), same four `leadingCoeff⁻¹`
nonzero-unit argument, only the designated linear factor and the
correspondingly-reordered `eval`-nonvanishing hypotheses change. -/
theorem ordAt_npoly4Lcm4_eq_one_of_P2
    (hchar : (2 : F p) ≠ 0) (hsf : Squarefree H.f)
    (P1 P2 : F p × F p) (ua0 ua1 u0 u1 : F p)
    (P : H.Point) (h_bot : pointIdeal P ≠ ⊥) (hPX : P.X = P2.1) (hPY : P.Y ≠ 0)
    (h12 : P1.1 ≠ P2.1)
    (hne34 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ≠ X ^ 2 + C u1 * X + C u0)
    (hnoroot34 : ¬ ∃ r : F p, (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval r = 0 ∧
        (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval r = 0)
    (hP1ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P1.1 = 0)
    (hP1target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P1.1 = 0)
    (hP2ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P2.1 = 0)
    (hP2target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P2.1 = 0) :
    ordAt P (npoly4Lcm4 p P1 P2 ua0 ua1 u0 u1) (0 : Polynomial (F p)) = 1 := by
  rw [npoly4Lcm4_eq_flat_product p P1 P2 ua0 ua1 u0 u1 h12 hne34 hnoroot34
    hP1ua hP1target hP2ua hP2target]
  -- Reshape the flat product so `linX P2.1 = X - C P2.1` sits at the front,
  -- matching `ordAt_unit_mul_A_eq_one_of_eval_ne_zero`'s expected shape
  -- `C u * (((linX a * F₁) * F₂) * F₃)`.
  have hshape :
      (((X - C P1.1 : Polynomial (F p)) * (X - C P2.1)) *
        ((X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) * (X ^ 2 + C u1 * X + C u0))) =
      ((linX P2.1 * (X - C P1.1 : Polynomial (F p))) *
        (X ^ 2 + C ua1 * X + C ua0)) * (X ^ 2 + C u1 * X + C u0) := by
    simp only [linX]; ring
  rw [hshape]
  have hune : ∀ q : Polynomial (F p), q.Monic → q ≠ 0 → q.leadingCoeff⁻¹ ≠ 0 := by
    intro q _ hq0
    exact inv_ne_zero ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hq0)
  have hm1 : (X - C P1.1 : Polynomial (F p)).Monic := Polynomial.monic_X_sub_C _
  have hm2 : (X - C P2.1 : Polynomial (F p)).Monic := Polynomial.monic_X_sub_C _
  have hm3 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).Monic := by monicity!
  have hm4 : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).Monic := by monicity!
  have hL12ne : (EuclideanDomain.lcm (X - C P1.1 : Polynomial (F p)) (X - C P2.1)) ≠ 0 :=
    fun h => (EuclideanDomain.lcm_eq_zero_iff.mp h).elim hm1.ne_zero hm2.ne_zero
  have hL34ne :
      (EuclideanDomain.lcm (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
        (X ^ 2 + C u1 * X + C u0)) ≠ 0 :=
    fun h => (EuclideanDomain.lcm_eq_zero_iff.mp h).elim hm3.ne_zero hm4.ne_zero
  have hGne :
      (EuclideanDomain.gcd
        (EuclideanDomain.lcm (X - C P1.1 : Polynomial (F p)) (X - C P2.1))
        (EuclideanDomain.lcm (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
          (X ^ 2 + C u1 * X + C u0))) ≠ 0 :=
    fun h => hL12ne (EuclideanDomain.gcd_eq_zero_iff.mp h).1
  have hgcd12ne : (EuclideanDomain.gcd (X - C P1.1 : Polynomial (F p)) (X - C P2.1)) ≠ 0 :=
    fun h => hm1.ne_zero (EuclideanDomain.gcd_eq_zero_iff.mp h).1
  have hgcd34ne :
      (EuclideanDomain.gcd (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
        (X ^ 2 + C u1 * X + C u0)) ≠ 0 :=
    fun h => hm3.ne_zero (EuclideanDomain.gcd_eq_zero_iff.mp h).1
  have hrawne : (npoly4LcmRaw p P1 P2 ua0 ua1 u0 u1) ≠ 0 :=
    npoly4LcmRaw_ne_zero p P1 P2 ua0 ua1 u0 u1
  exact ordAt_unit_mul_A_eq_one_of_eval_ne_zero hchar hsf P h_bot _ _
    (mul_ne_zero (mul_ne_zero (mul_ne_zero
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hrawne |> inv_ne_zero)
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hGne |> inv_ne_zero))
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hgcd12ne |> inv_ne_zero))
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hgcd34ne |> inv_ne_zero))
    hPX hPY (X - C P1.1) (X ^ 2 + C ua1 * X + C ua0) (X ^ 2 + C u1 * X + C u0)
    (by rw [hPX] at *; simpa using sub_ne_zero.mpr h12.symm)
    (by rw [hPX] at *; exact hP2ua)
    (by rw [hPX] at *; exact hP2target)

end GeometricInstantiation

end GeometricBridge

/-! ## Status note (this pass): Part D is genuinely started, not finished

`ordAt_npoly4Lcm4_eq_one_of_P1` is ONE of the six point-instantiations Part
D needs (the `P1` case; `P2` is the exact mirror via `mul_comm`-style
reshaping; `ua`'s two roots and `u_target`'s two roots additionally need
`quadratic_eq_mul_X_sub_C` to split the quadratic factor into linear
factors before this same technique applies, NOT attempted this pass). Not
yet build-tested — Claire's REPL to confirm, in particular the `hshape`
`ring` step and the final unit-nonzero assembly's associativity against
`ordAt_unit_mul_A_eq_one_of_eval_ne_zero`'s expected argument order.

**What is still missing, honestly, before `reducedClass_eq_of_isReduction'`
can lose its `sorry`** (do not attempt to fake past this list):

1. The five remaining point-instantiations (`P2`, `ua`'s two roots,
   `u_target`'s two roots) — mechanical repeats of this section's pattern,
   not new content, but not yet written.
2. Composing `ordAt P npoly4Lcm4 0 = 1` (this section) with `Npoly4 =
   npoly4Lcm4 * uRS4General` (Step 1) to get `ordAt P A 0 = 1` in
   `PrincipalWitness.lean`'s lemma-14/15 sense (`A := npoly4Lcm4` there),
   then applying lemmas 14/15 themselves at each of the 6 points — not
   attempted this pass.
3. **The `Sg`/`Su`/`divToPairRatio`/`principalSubgroup`-membership half of
   the roadmap's corrected two-step plan (its "Status update, pass #4/#5"
   sections) — SUPERSEDED, not just unstarted.** `ordInfOfPair` was found
   (`PrincipalDivisors.lean`) and computed directly: `ordInfOfPair(Epoly4,
   Ypoly4) = -8`, `ordInfOfPair(uRS4General, 0) = -4` — these do NOT match,
   so `divToPairRatio`/`principalSubgroup` (which demands an exact match)
   is confirmed the wrong tool for this witness. The correct route
   (confirmed via ChatGPT consultation, see
   `ROADMAP-principal-witness-assembly.md`'s "Status update, pass #7"
   and `CHATGPT-LOG-principal-witness-assembly.md` for the exact exchange):
   prove `div(g) - div(uRS4General) = D_old - D_new - 4 • [δ₀]` directly
   via `eq_of_coeffAt_eq` (already on file), bypassing `principalSubgroup`
   membership entirely, then separately check how `reducedClass`/
   `toJacobian` absorb the leftover `4•[δ₀]` term. **Not yet written as
   Lean** — this is the next pass's actual target for this piece.

`reducedClass_eq_of_isReduction'` itself is NOT touched this pass and stays
`sorry` — the gap above is too large to close with a guessed proof term,
and this project's own convention (search/ask rather than guess) applies
doubly hard to a correction-term computation not yet checked against
`reducedClass`'s actual definition. -/

end DecoupledSystem
end Genus2Lean

