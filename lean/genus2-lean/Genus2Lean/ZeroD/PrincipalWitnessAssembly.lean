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

/-!
The following three wrappers are deliberately opaque (`def`, not `abbrev`).
The P1 point-composition theorem has an unusually large declaration type:
`ordAtFrac` is fed three large polynomial expressions, and elaborating the
same expressions repeatedly was enough to hit the default 200k heartbeat
limit at the theorem declaration itself, before the proof body was entered.
Keeping the constructions behind named constants makes the declaration cheap;
the definitions unfold where the proof explicitly asks for them.
-/

def witnessE4 (p : ℕ) [Fact (Nat.Prime p)]
    (P1 P2 : F p × F p) (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p) : Polynomial (F p) :=
  Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1

def witnessY4 (p : ℕ) [Fact (Nat.Prime p)]
    (P1 P2 : F p × F p) (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p) : Polynomial (F p) :=
  Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1

def witnessA4 (p : ℕ) [Fact (Nat.Prime p)]
    (P1 P2 : F p × F p) (ua0 ua1 u0 u1 : F p) : Polynomial (F p) :=
  npoly4Lcm4 p P1 P2 ua0 ua1 u0 u1

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

section GeometricInstantiationQuadratic

variable (p : ℕ) [hp : Fact (Nat.Prime p)] [Fact (p ≠ 2)]
variable {H : HyperellipticPolynomial (F p)} [IsDedekindDomain (CoordinateRing H)]

/-- **`ordAt` of `npoly4Lcm4` at the point built from `Ra1`'s own
coordinates is `1`**, where `Ra1, Ra2` are `ua`'s two distinct roots over
`F p` (the split case; the irreducible-quadratic fork is out of scope,
per the roadmap's "scope to the split case first" decision). Same overall
composition as the `P1`/`P2` cases (`npoly4Lcm4_eq_flat_product` +
`ordAt_unit_mul_A_eq_one_of_eval_ne_zero`), but with one extra step
first: `quadratic_eq_mul_X_sub_C` rewrites `ua` itself into
`(X-C Ra1)*(X-C Ra2)` before the flat product is reshaped. Since Layer
3's underlying lemma only has 3 "other-factor" slots (`F₁ F₂ F₃`) and
splitting `ua` leaves 4 remaining flat factors (`Ra2`, `P1`, `P2`,
`u_target`), `P2` and `u_target` are merged into a single `F₃ := (X-C
P2.1) * u_target`, discharged via `Polynomial.eval_mul`/`mul_ne_zero` —
`F₁`/`F₂`/`F₃` carry no shape restriction in Layer 3's statement, only
`eval a ≠ 0`, so this merge is free. -/
theorem ordAt_npoly4Lcm4_eq_one_of_Ra1
    (hchar : (2 : F p) ≠ 0) (hsf : Squarefree H.f)
    (P1 P2 : F p × F p) (ua0 ua1 u0 u1 : F p)
    (Ra1 Ra2 : F p)
    (huaRoot1 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).IsRoot Ra1)
    (huaRoot2 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).IsRoot Ra2)
    (hRane : Ra1 ≠ Ra2)
    (P : H.Point) (h_bot : pointIdeal P ≠ ⊥) (hPX : P.X = Ra1) (hPY : P.Y ≠ 0)
    (h12 : P1.1 ≠ P2.1)
    (hne34 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ≠ X ^ 2 + C u1 * X + C u0)
    (hnoroot34 : ¬ ∃ r : F p, (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval r = 0 ∧
        (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval r = 0)
    (hP1ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P1.1 = 0)
    (hP1target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P1.1 = 0)
    (hP2ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P2.1 = 0)
    (hP2target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P2.1 = 0)
    (hRa1P1 : Ra1 ≠ P1.1) (hRa1P2 : Ra1 ≠ P2.1)
    (hRa1target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval Ra1 = 0) :
    ordAt P (npoly4Lcm4 p P1 P2 ua0 ua1 u0 u1) (0 : Polynomial (F p)) = 1 := by
  rw [npoly4Lcm4_eq_flat_product p P1 P2 ua0 ua1 u0 u1 h12 hne34 hnoroot34
    hP1ua hP1target hP2ua hP2target]
  -- Split `ua` into its two named linear factors, then reshape so
  -- `linX Ra1` sits at the front and `(X-C P2.1) * u_target` is merged
  -- into a single `F₃` slot.
  have huaSplit : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) =
      (X - C Ra1) * (X - C Ra2) := by
    have hmonic : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).Monic := by monicity!
    have hdeg : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).natDegree = 2 := by
      compute_degree!
    exact quadratic_eq_mul_X_sub_C p hmonic hdeg huaRoot1 huaRoot2 hRane
  have hshape :
      (((X - C P1.1 : Polynomial (F p)) * (X - C P2.1)) *
        ((X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) * (X ^ 2 + C u1 * X + C u0))) =
      ((linX Ra1 * (X - C Ra2 : Polynomial (F p))) *
        (X - C P1.1)) * ((X - C P2.1) * (X ^ 2 + C u1 * X + C u0)) := by
    simp only [linX]; rw [huaSplit]; ring
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
  have hF3_eval :
      ((X - C P2.1 : Polynomial (F p)) * (X ^ 2 + C u1 * X + C u0)).eval Ra1 ≠ 0 := by
    rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact mul_ne_zero (sub_ne_zero.mpr hRa1P2) hRa1target
  exact ordAt_unit_mul_A_eq_one_of_eval_ne_zero hchar hsf P h_bot _ _
    (mul_ne_zero (mul_ne_zero (mul_ne_zero
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hrawne |> inv_ne_zero)
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hGne |> inv_ne_zero))
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hgcd12ne |> inv_ne_zero))
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hgcd34ne |> inv_ne_zero))
    hPX hPY (X - C Ra2) (X - C P1.1) ((X - C P2.1) * (X ^ 2 + C u1 * X + C u0))
    (by rw [hPX] at *; simpa using sub_ne_zero.mpr hRane)
    (by rw [hPX] at *; simpa using sub_ne_zero.mpr hRa1P1)
    (by rw [hPX] at *; exact hF3_eval)

end GeometricInstantiationQuadratic

section GeometricInstantiationQuadratic2

variable (p : ℕ) [hp : Fact (Nat.Prime p)] [Fact (p ≠ 2)]
variable {H : HyperellipticPolynomial (F p)} [IsDedekindDomain (CoordinateRing H)]

/-- **`ordAt` of `npoly4Lcm4` at the point built from `Ra2`'s own
coordinates is `1`** — the exact mirror of `ordAt_npoly4Lcm4_eq_one_of_Ra1`,
with `Ra1`/`Ra2` swapped throughout: `linX Ra2` sits at the front, `(X-C
Ra1)` is the designated-factor's companion, and the "no shared root"
hypotheses are `Ra2`'s own versions. Same composition and same
`P2`/`u_target` merge-into-`F₃` trick as the `Ra1` case. -/
theorem ordAt_npoly4Lcm4_eq_one_of_Ra2
    (hchar : (2 : F p) ≠ 0) (hsf : Squarefree H.f)
    (P1 P2 : F p × F p) (ua0 ua1 u0 u1 : F p)
    (Ra1 Ra2 : F p)
    (huaRoot1 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).IsRoot Ra1)
    (huaRoot2 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).IsRoot Ra2)
    (hRane : Ra1 ≠ Ra2)
    (P : H.Point) (h_bot : pointIdeal P ≠ ⊥) (hPX : P.X = Ra2) (hPY : P.Y ≠ 0)
    (h12 : P1.1 ≠ P2.1)
    (hne34 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ≠ X ^ 2 + C u1 * X + C u0)
    (hnoroot34 : ¬ ∃ r : F p, (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval r = 0 ∧
        (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval r = 0)
    (hP1ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P1.1 = 0)
    (hP1target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P1.1 = 0)
    (hP2ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P2.1 = 0)
    (hP2target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P2.1 = 0)
    (hRa2P1 : Ra2 ≠ P1.1) (hRa2P2 : Ra2 ≠ P2.1)
    (hRa2target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval Ra2 = 0) :
    ordAt P (npoly4Lcm4 p P1 P2 ua0 ua1 u0 u1) (0 : Polynomial (F p)) = 1 := by
  rw [npoly4Lcm4_eq_flat_product p P1 P2 ua0 ua1 u0 u1 h12 hne34 hnoroot34
    hP1ua hP1target hP2ua hP2target]
  -- Split `ua` into its two named linear factors, then reshape so
  -- `linX Ra2` sits at the front and `(X-C P2.1) * u_target` is merged
  -- into a single `F₃` slot.
  have huaSplit : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) =
      (X - C Ra1) * (X - C Ra2) := by
    have hmonic : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).Monic := by monicity!
    have hdeg : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).natDegree = 2 := by
      compute_degree!
    exact quadratic_eq_mul_X_sub_C p hmonic hdeg huaRoot1 huaRoot2 hRane
  have hshape :
      (((X - C P1.1 : Polynomial (F p)) * (X - C P2.1)) *
        ((X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) * (X ^ 2 + C u1 * X + C u0))) =
      ((linX Ra2 * (X - C Ra1 : Polynomial (F p))) *
        (X - C P1.1)) * ((X - C P2.1) * (X ^ 2 + C u1 * X + C u0)) := by
    simp only [linX]; rw [huaSplit]; ring
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
  have hF3_eval :
      ((X - C P2.1 : Polynomial (F p)) * (X ^ 2 + C u1 * X + C u0)).eval Ra2 ≠ 0 := by
    rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact mul_ne_zero (sub_ne_zero.mpr hRa2P2) hRa2target
  exact ordAt_unit_mul_A_eq_one_of_eval_ne_zero hchar hsf P h_bot _ _
    (mul_ne_zero (mul_ne_zero (mul_ne_zero
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hrawne |> inv_ne_zero)
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hGne |> inv_ne_zero))
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hgcd12ne |> inv_ne_zero))
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hgcd34ne |> inv_ne_zero))
    hPX hPY (X - C Ra1) (X - C P1.1) ((X - C P2.1) * (X ^ 2 + C u1 * X + C u0))
    (by rw [hPX] at *; simpa using sub_ne_zero.mpr hRane.symm)
    (by rw [hPX] at *; simpa using sub_ne_zero.mpr hRa2P1)
    (by rw [hPX] at *; exact hF3_eval)

end GeometricInstantiationQuadratic2

section GeometricInstantiationQuadratic3

variable (p : ℕ) [hp : Fact (Nat.Prime p)] [Fact (p ≠ 2)]
variable {H : HyperellipticPolynomial (F p)} [IsDedekindDomain (CoordinateRing H)]

/-- **`ordAt` of `npoly4Lcm4` at the point built from `R1`'s own
coordinates is `1`**, where `R1, R2` are `u_target`'s two distinct roots
over `F p` (split case, per the same scoping as `Ra1`/`Ra2`). Mirrors
`ordAt_npoly4Lcm4_eq_one_of_Ra1` with the roles of `ua` and `u_target`
swapped: `u_target` is the quadratic that gets split via
`quadratic_eq_mul_X_sub_C`, `linX R1` is the designated factor, `(X-C R2)`
its companion, and `ua`/`P2` are merged into `F₃` this time (the mirror
of `Ra1`'s `P2`/`u_target` merge). -/
theorem ordAt_npoly4Lcm4_eq_one_of_R1
    (hchar : (2 : F p) ≠ 0) (hsf : Squarefree H.f)
    (P1 P2 : F p × F p) (ua0 ua1 u0 u1 : F p)
    (R1 R2 : F p)
    (htargetRoot1 : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).IsRoot R1)
    (htargetRoot2 : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).IsRoot R2)
    (hRne : R1 ≠ R2)
    (P : H.Point) (h_bot : pointIdeal P ≠ ⊥) (hPX : P.X = R1) (hPY : P.Y ≠ 0)
    (h12 : P1.1 ≠ P2.1)
    (hne34 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ≠ X ^ 2 + C u1 * X + C u0)
    (hnoroot34 : ¬ ∃ r : F p, (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval r = 0 ∧
        (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval r = 0)
    (hP1ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P1.1 = 0)
    (hP1target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P1.1 = 0)
    (hP2ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P2.1 = 0)
    (hP2target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P2.1 = 0)
    (hR1P1 : R1 ≠ P1.1) (hR1P2 : R1 ≠ P2.1)
    (hR1ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval R1 = 0) :
    ordAt P (npoly4Lcm4 p P1 P2 ua0 ua1 u0 u1) (0 : Polynomial (F p)) = 1 := by
  rw [npoly4Lcm4_eq_flat_product p P1 P2 ua0 ua1 u0 u1 h12 hne34 hnoroot34
    hP1ua hP1target hP2ua hP2target]
  -- Split `u_target` into its two named linear factors, then reshape so
  -- `linX R1` sits at the front and `(X-C P2.1) * ua` is merged into a
  -- single `F₃` slot.
  have htargetSplit : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)) =
      (X - C R1) * (X - C R2) := by
    have hmonic : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).Monic := by monicity!
    have hdeg : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).natDegree = 2 := by
      compute_degree!
    exact quadratic_eq_mul_X_sub_C p hmonic hdeg htargetRoot1 htargetRoot2 hRne
  have hshape :
      (((X - C P1.1 : Polynomial (F p)) * (X - C P2.1)) *
        ((X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) * (X ^ 2 + C u1 * X + C u0))) =
      ((linX R1 * (X - C R2 : Polynomial (F p))) *
        (X - C P1.1)) * ((X - C P2.1) * (X ^ 2 + C ua1 * X + C ua0)) := by
    simp only [linX]; rw [htargetSplit]; ring
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
  have hF3_eval :
      ((X - C P2.1 : Polynomial (F p)) * (X ^ 2 + C ua1 * X + C ua0)).eval R1 ≠ 0 := by
    rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact mul_ne_zero (sub_ne_zero.mpr hR1P2) hR1ua
  exact ordAt_unit_mul_A_eq_one_of_eval_ne_zero hchar hsf P h_bot _ _
    (mul_ne_zero (mul_ne_zero (mul_ne_zero
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hrawne |> inv_ne_zero)
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hGne |> inv_ne_zero))
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hgcd12ne |> inv_ne_zero))
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hgcd34ne |> inv_ne_zero))
    hPX hPY (X - C R2) (X - C P1.1) ((X - C P2.1) * (X ^ 2 + C ua1 * X + C ua0))
    (by rw [hPX] at *; simpa using sub_ne_zero.mpr hRne)
    (by rw [hPX] at *; simpa using sub_ne_zero.mpr hR1P1)
    (by rw [hPX] at *; exact hF3_eval)

end GeometricInstantiationQuadratic3

section GeometricInstantiationQuadratic4

variable (p : ℕ) [hp : Fact (Nat.Prime p)] [Fact (p ≠ 2)]
variable {H : HyperellipticPolynomial (F p)} [IsDedekindDomain (CoordinateRing H)]

/-- **`ordAt` of `npoly4Lcm4` at the point built from `R2`'s own
coordinates is `1`** — the exact mirror of `ordAt_npoly4Lcm4_eq_one_of_R1`,
with `R1`/`R2` swapped throughout: `linX R2` sits at the front, `(X-C R1)`
is the designated-factor's companion, and the "no shared root" hypotheses
are `R2`'s own versions. Same composition and same `P2`/`ua`
merge-into-`F₃` trick as the `R1` case. **This is the sixth and final
point-instantiation Part D needs** — completes the `P1`/`P2`/`Ra1`/`Ra2`/
`R1`/`R2` set. -/
theorem ordAt_npoly4Lcm4_eq_one_of_R2
    (hchar : (2 : F p) ≠ 0) (hsf : Squarefree H.f)
    (P1 P2 : F p × F p) (ua0 ua1 u0 u1 : F p)
    (R1 R2 : F p)
    (htargetRoot1 : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).IsRoot R1)
    (htargetRoot2 : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).IsRoot R2)
    (hRne : R1 ≠ R2)
    (P : H.Point) (h_bot : pointIdeal P ≠ ⊥) (hPX : P.X = R2) (hPY : P.Y ≠ 0)
    (h12 : P1.1 ≠ P2.1)
    (hne34 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ≠ X ^ 2 + C u1 * X + C u0)
    (hnoroot34 : ¬ ∃ r : F p, (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval r = 0 ∧
        (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval r = 0)
    (hP1ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P1.1 = 0)
    (hP1target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P1.1 = 0)
    (hP2ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P2.1 = 0)
    (hP2target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P2.1 = 0)
    (hR2P1 : R2 ≠ P1.1) (hR2P2 : R2 ≠ P2.1)
    (hR2ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval R2 = 0) :
    ordAt P (npoly4Lcm4 p P1 P2 ua0 ua1 u0 u1) (0 : Polynomial (F p)) = 1 := by
  rw [npoly4Lcm4_eq_flat_product p P1 P2 ua0 ua1 u0 u1 h12 hne34 hnoroot34
    hP1ua hP1target hP2ua hP2target]
  -- Split `u_target` into its two named linear factors, then reshape so
  -- `linX R2` sits at the front and `(X-C P2.1) * ua` is merged into a
  -- single `F₃` slot.
  have htargetSplit : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)) =
      (X - C R1) * (X - C R2) := by
    have hmonic : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).Monic := by monicity!
    have hdeg : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).natDegree = 2 := by
      compute_degree!
    exact quadratic_eq_mul_X_sub_C p hmonic hdeg htargetRoot1 htargetRoot2 hRne
  have hshape :
      (((X - C P1.1 : Polynomial (F p)) * (X - C P2.1)) *
        ((X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) * (X ^ 2 + C u1 * X + C u0))) =
      ((linX R2 * (X - C R1 : Polynomial (F p))) *
        (X - C P1.1)) * ((X - C P2.1) * (X ^ 2 + C ua1 * X + C ua0)) := by
    simp only [linX]; rw [htargetSplit]; ring
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
  have hF3_eval :
      ((X - C P2.1 : Polynomial (F p)) * (X ^ 2 + C ua1 * X + C ua0)).eval R2 ≠ 0 := by
    rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact mul_ne_zero (sub_ne_zero.mpr hR2P2) hR2ua
  exact ordAt_unit_mul_A_eq_one_of_eval_ne_zero hchar hsf P h_bot _ _
    (mul_ne_zero (mul_ne_zero (mul_ne_zero
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hrawne |> inv_ne_zero)
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hGne |> inv_ne_zero))
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hgcd12ne |> inv_ne_zero))
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hgcd34ne |> inv_ne_zero))
    hPX hPY (X - C R1) (X - C P1.1) ((X - C P2.1) * (X ^ 2 + C ua1 * X + C ua0))
    (by rw [hPX] at *; simpa using sub_ne_zero.mpr hRne.symm)
    (by rw [hPX] at *; simpa using sub_ne_zero.mpr hR2P1)
    (by rw [hPX] at *; exact hF3_eval)

end GeometricInstantiationQuadratic4

/-! ## Step 4 (roadmap item 1): composing the `P1` case — the first of six
point compositions

This is the actual assembly the roadmap's "what is still missing" list
(item 1) asks for, done here for `P1` as a template for the remaining
five points (`P2`, `Ra1`, `Ra2`, `R1`, `R2`). Composes:
- Step 1's exact factorization (`Npoly4_eq_npoly4Lcm4_mul_uRS4General`),
  reshaped into `pairNorm H Epoly4 Ypoly4 = A * U` form (`hAU` in
  `PrincipalWitness.lean`'s sense) via `pairNorm_eq_of_eq_curvePoly` and
  `Npoly4`'s own definition;
- Part D's `ordAt_npoly4Lcm4_eq_one_of_P1` (`ordAt P npoly4Lcm4 0 = 1`);
- `AlphaReduce.lean`'s `Epoly4_eval_add_Y_mul_Ypoly4_eval_P1_eq_zero`
  (`g(P1) = 0`, added this project — see `ROADMAP-principal-witness-
  assembly.md`'s pass #8);
- `PrincipalWitness.lean`'s lemma 14 (`ordAtFrac_eq_one_of_old_point`).

**One new hypothesis, not on file anywhere before this pass, added
honestly rather than derived or hidden**: `hYP1_ne : (Ypoly4 ...).eval
P1.1 ≠ 0`. Lemma 14's `hg_ne_eval` (misleadingly named — it is actually
the `ḡ(P) ≠ 0` hypothesis, per that lemma's own docstring/proof) needs
`ḡ(P1) ≠ 0`. Since `g(P1) = 0` gives `E.eval P1.1 = -P1.2 * Y.eval P1.1`,
`ḡ(P1) = E.eval P1.1 - P1.2 * Y.eval P1.1 = -2 * P1.2 * Y.eval P1.1`,
which is nonzero (given `hchar : (2:F p) ≠ 0`) iff `P1.2 ≠ 0` (already
`hPY` in `ordAt_npoly4Lcm4_eq_one_of_P1`'s hypothesis list) AND
`Y.eval P1.1 ≠ 0`. The latter is NOT derivable from any hypothesis
currently on file (checked: `hgcd`'s coprimality is between `Ypoly4` and
`uRS4General`, the RESIDUAL quadratic — not `npoly4Lcm4`/`A`, the OLD
factor `P1` is a root of; no lemma anywhere states or implies `Ypoly4`
doesn't vanish at `P1.X`). This is a genuine mathematical gap, not a
notational one — stating it as an explicit hypothesis here (rather than
guessing a derivation) matches this project's "don't over-assume, but
state what's actually needed" discipline, same as `hP1ua`/`hP1target`
etc. already do for the geometric-distinctness side. **Flagged for a
ChatGPT consult or direct check**: is `Ypoly4.eval P1.1 ≠ 0` actually true
unconditionally (geometrically: does the interpolating `Y`-component ever
vanish at one of the two points it's built to pass through, for generic
input data)?  or does it need a further nondegeneracy hypothesis on
`(P1,P2,ua,u)` beyond `MatrixNondegenerate4`? Not resolved this pass. -/

section PointCompositionP1

variable (p : ℕ) [hp : Fact (Nat.Prime p)] [Fact (p ≠ 2)]
variable {H : HyperellipticPolynomial (F p)} [IsDedekindDomain (CoordinateRing H)]

set_option maxHeartbeats 400000 in
-- Large polynomial whnf from `set`-introduced abbreviations in the proof body.
/-- **The `P1` case of the pointwise `ordAtFrac`-assembly:** the old-point
factor `A = npoly4Lcm4` has order one at `P1`, and the residual factor
`U` is therefore the denominator in `ordAtFrac P E Y U`. This is the exact
conclusion provided by `ordAtFrac_eq_one_of_old_point`. First of six point
compositions the assembly needs (see module-level status note above for the
other five, not yet done). -/
theorem ordAtFrac_eq_one_of_P1
    (hchar : (2 : F p) ≠ 0) (hsf : Squarefree H.f)
    (c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (hf : H.f = curvePoly p c0 c1 c2 c3 c4)
    (P1 P2 : F p × F p)
    (P : H.Point) (hPX : P.X = P1.1) (hPY : P.Y = P1.2) (hPY_ne : P.Y ≠ 0)
    (h12 : P1.1 ≠ P2.1)
    (hne34 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ≠ X ^ 2 + C u1 * X + C u0)
    (hnoroot34 : ¬ ∃ r : F p, (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval r = 0 ∧
        (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval r = 0)
    (hP1ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P1.1 = 0)
    (hP1target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P1.1 = 0)
    (hP2ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P2.1 = 0)
    (hP2target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P2.1 = 0)
    (hA : MatrixNondegenerate4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hP1_curve : P1.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P1.1)
    (hP2_curve : P2.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P2.1)
    (hMumfordUa : IsMumfordUa p c0 c1 c2 c3 c4 ua0 ua1 va0 va1)
    (hMumfordTarget : IsMumfordTarget4 p c0 c1 c2 c3 c4 u0 u1 v0 v1)
    (hcurne : curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hYP1_ne : (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval P1.1 ≠ 0)
    (E Y A : Polynomial (F p))
    (hE_def : E = Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hY_def : Y = Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hA_def : A = npoly4Lcm4 p P1 P2 ua0 ua1 u0 u1) :
    ordAtFrac P E Y
      (C ((curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff) *
        uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
      (0 : Polynomial (F p)) = 1 := by
  have h_bot : pointIdeal P ≠ ⊥ := pointIdeal_ne_bot P
  -- `hNpoly4_eq₀`: proved BEFORE the `set`s above are introduced, and by
  -- `rfl` alone (this is definitional — `Npoly4`'s `def` body IS
  -- `Epoly4^2 - curvePoly*Ypoly4^2`, verbatim) rather than `unfold ...;
  -- ring`, which was timing out: with `E,Y,A,lc,U` all sitting in context
  -- as `set`-local-defs, `unfold`/`ring`'s `whnf` calls had to thread
  -- through all of them, not just `Npoly4`, to normalize a degree-≤8
  -- polynomial identity. Proving this cheap fact in terms of the plain
  -- `Epoly4 p ...`/`Ypoly4 p ...` names (no `E`/`Y` abbreviations yet)
  -- keeps the `rfl` local to `Npoly4`'s own unfolding.
  have hNpoly4_eq₀ : Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 =
      Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ^ 2 -
        curvePoly p c0 c1 c2 c3 c4 * Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ^ 2 := rfl
  set lc := (curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff
    with hlc_def
  set U := C lc * uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 with hU_def
  -- `hAU`: `pairNorm H E Y = A * U`, from Step 1's factorization plus
  -- `Npoly4`'s definition and `hf`.
  have hAU : pairNorm H E Y = A * U := by
    -- `hfact : Npoly4 = npoly4Lcm4 * (C leadingCoeff * uRS4General)`, and
    -- `Npoly4` unfolds (definitionally) to `E^2 - curvePoly*Y^2`; `pairNorm
    -- H E Y` unfolds (via `hf`) to `E^2 - Y^2*curvePoly` — the same value,
    -- differing only by `mul_comm`, so `linear_combination` (not `rw`,
    -- which would need exact syntactic matches on both sides) closes the
    -- gap directly from the two component facts.
    have hfact := Npoly4_eq_npoly4Lcm4_mul_uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1
      u0 u1 v0 v1 hcurne hA hP1_curve hP2_curve hMumfordUa hMumfordTarget
    have hpn := pairNorm_eq_of_eq_curvePoly hf E Y
    have hNpoly4_eq : Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 = E ^ 2 -
        curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := hE_def ▸ hY_def ▸ hNpoly4_eq₀
    -- Orient the local set-equalities backwards.  `hfact` already contains
    -- the fully expanded definitions on its right-hand side, so rewriting
    -- forwards cannot see `A`, while rewriting backwards exposes `A * U`
    -- without unfolding any of the large polynomial definitions.
    rw [← hlc_def, ← hU_def, ← hA_def] at hfact
    have hpn' : pairNorm H E Y = E ^ 2 - curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := by
      calc
        pairNorm H E Y = E ^ 2 - Y ^ 2 * curvePoly p c0 c1 c2 c3 c4 := hpn
        _ = E ^ 2 - curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := by
          rw [mul_comm (Y ^ 2) (curvePoly p c0 c1 c2 c3 c4)]
    calc
      pairNorm H E Y = E ^ 2 - curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := hpn'
      _ = Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 := hNpoly4_eq.symm
      _ = A * U := hfact
  -- `A ≠ 0`, `U ≠ 0` as ring elements (`toPair H · 0`).
  have hAmonic : A.Monic := by
    rw [hA_def]
    exact npoly4Lcm4_monic p P1 P2 ua0 ua1 u0 u1
  have hA_ne0 : A ≠ 0 := hAmonic.ne_zero
  have hA_ne : toPair H A (0 : Polynomial (F p)) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]; exact fun h => hA_ne0 h.1
  have hUmonic : (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).Monic :=
    uRS4General_monic p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hcurne
  have hU_ne0 : U ≠ 0 := by
    rw [hU_def]
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hcurne)) hUmonic.ne_zero
  have hU_ne : toPair H U (0 : Polynomial (F p)) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]; exact fun h => hU_ne0 h.1
  -- `ordAt P A 0 = 1`, from Part D.
  have hA_ord : ordAt P A (0 : Polynomial (F p)) = 1 := by
    rw [hA_def]
    exact ordAt_npoly4Lcm4_eq_one_of_P1 p hchar hsf P1 P2 ua0 ua1 u0 u1
      P h_bot hPX hPY_ne h12 hne34 hnoroot34 hP1ua hP1target hP2ua hP2target
  -- `g(P1) = 0`, giving both `hg_ne` (as a ring element) and (combined
  -- with `hYP1_ne`) `hg_ne_eval` (really `ḡ(P1) ≠ 0`).
  have hgP1_eval : E.eval P1.1 + P1.2 * Y.eval P1.1 = 0 := by
    simpa [hE_def, hY_def] using
      (Epoly4_eval_add_Y_mul_Ypoly4_eval_P1_eq_zero p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hA)
  -- `ḡ(P1) ≠ 0`: since `g(P1) = 0` gives `E(P1) = -P1.2 * Y(P1)`,
  -- we have `ḡ(P1) = E(P1) - Y(P1)*P1.2 = -2*Y(P1)*P1.2 ≠ 0`.
  have hgbar_eval : E.eval P.X + (-Y).eval P.X * P.Y ≠ 0 := by
    rw [hPX, hPY, Polynomial.eval_neg]
    have hYZ : Y.eval P1.1 * P1.2 ≠ 0 :=
      mul_ne_zero (by simpa [hY_def] using hYP1_ne) (hPY ▸ hPY_ne)
    have hgP1_eval' : E.eval P1.1 + Y.eval P1.1 * P1.2 = 0 := by
      linear_combination hgP1_eval
    intro hcontra
    have h2 : (2 : F p) * (Y.eval P1.1 * P1.2) = 0 := by
      linear_combination hgP1_eval' - hcontra
    rcases mul_eq_zero.mp h2 with h2c | h2yz
    · exact absurd h2c hchar
    · exact absurd h2yz hYZ

  have hg_ne : toPair H E Y ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    rintro ⟨-, hY0⟩
    apply hYP1_ne
    rw [← hY_def, hY0]
    simp

  exact ordAtFrac_eq_one_of_old_point P h_bot E Y A U
    hg_ne hgbar_eval hAU hA_ne hU_ne hA_ord
end PointCompositionP1

section PointCompositionP2

variable (p : ℕ) [hp : Fact (Nat.Prime p)] [Fact (p ≠ 2)]
variable {H : HyperellipticPolynomial (F p)} [IsDedekindDomain (CoordinateRing H)]

set_option maxHeartbeats 400000 in
-- Large polynomial whnf from `set`-introduced abbreviations in the proof body.
/-- **The `P2` case of the pointwise `ordAtFrac`-assembly**, the exact mirror
of `ordAtFrac_eq_one_of_P1` with `P1`/`P2` swapped throughout: same
derivation of `hAU`/`hA_ne`/`hU_ne`/`hA_ord`/`hg_ne`/`hgbar_eval`, only the
designated point's own coordinates and `Epoly4_eval_add_Y_mul_Ypoly4_eval_
P2_eq_zero` (in place of the `_P1_` version) change. Second of six point
compositions the assembly needs. Named `_full` to avoid clashing with the
abstract `ordAtFrac_eq_one_of_P2` wrapper below (`PointwiseOrdAtFracAssembly`
section), which takes `hA_ord`/`hzero` as bare hypotheses instead of
deriving them from the raw interpolation data as this theorem does. -/
theorem ordAtFrac_eq_one_of_P2_full
    (hchar : (2 : F p) ≠ 0) (hsf : Squarefree H.f)
    (c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (hf : H.f = curvePoly p c0 c1 c2 c3 c4)
    (P1 P2 : F p × F p)
    (P : H.Point) (hPX : P.X = P2.1) (hPY : P.Y = P2.2) (hPY_ne : P.Y ≠ 0)
    (h12 : P1.1 ≠ P2.1)
    (hne34 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ≠ X ^ 2 + C u1 * X + C u0)
    (hnoroot34 : ¬ ∃ r : F p, (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval r = 0 ∧
        (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval r = 0)
    (hP1ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P1.1 = 0)
    (hP1target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P1.1 = 0)
    (hP2ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P2.1 = 0)
    (hP2target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P2.1 = 0)
    (hA : MatrixNondegenerate4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hP1_curve : P1.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P1.1)
    (hP2_curve : P2.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P2.1)
    (hMumfordUa : IsMumfordUa p c0 c1 c2 c3 c4 ua0 ua1 va0 va1)
    (hMumfordTarget : IsMumfordTarget4 p c0 c1 c2 c3 c4 u0 u1 v0 v1)
    (hcurne : curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hYP2_ne : (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval P2.1 ≠ 0)
    (E Y A : Polynomial (F p))
    (hE_def : E = Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hY_def : Y = Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hA_def : A = npoly4Lcm4 p P1 P2 ua0 ua1 u0 u1) :
    ordAtFrac P E Y
      (C ((curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff) *
        uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
      (0 : Polynomial (F p)) = 1 := by
  have h_bot : pointIdeal P ≠ ⊥ := pointIdeal_ne_bot P
  have hNpoly4_eq₀ : Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 =
      Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ^ 2 -
        curvePoly p c0 c1 c2 c3 c4 * Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ^ 2 := rfl
  set lc := (curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff
    with hlc_def
  set U := C lc * uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 with hU_def
  have hAU : pairNorm H E Y = A * U := by
    have hfact := Npoly4_eq_npoly4Lcm4_mul_uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1
      u0 u1 v0 v1 hcurne hA hP1_curve hP2_curve hMumfordUa hMumfordTarget
    have hpn := pairNorm_eq_of_eq_curvePoly hf E Y
    have hNpoly4_eq : Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 = E ^ 2 -
        curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := hE_def ▸ hY_def ▸ hNpoly4_eq₀
    rw [← hlc_def, ← hU_def, ← hA_def] at hfact
    have hpn' : pairNorm H E Y = E ^ 2 - curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := by
      calc
        pairNorm H E Y = E ^ 2 - Y ^ 2 * curvePoly p c0 c1 c2 c3 c4 := hpn
        _ = E ^ 2 - curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := by
          rw [mul_comm (Y ^ 2) (curvePoly p c0 c1 c2 c3 c4)]
    calc
      pairNorm H E Y = E ^ 2 - curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := hpn'
      _ = Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 := hNpoly4_eq.symm
      _ = A * U := hfact
  have hAmonic : A.Monic := by
    rw [hA_def]
    exact npoly4Lcm4_monic p P1 P2 ua0 ua1 u0 u1
  have hA_ne0 : A ≠ 0 := hAmonic.ne_zero
  have hA_ne : toPair H A (0 : Polynomial (F p)) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]; exact fun h => hA_ne0 h.1
  have hUmonic : (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).Monic :=
    uRS4General_monic p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hcurne
  have hU_ne0 : U ≠ 0 := by
    rw [hU_def]
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hcurne)) hUmonic.ne_zero
  have hU_ne : toPair H U (0 : Polynomial (F p)) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]; exact fun h => hU_ne0 h.1
  -- `ordAt P A 0 = 1`, from Part D — the `P2` geometric instantiation.
  have hA_ord : ordAt P A (0 : Polynomial (F p)) = 1 := by
    rw [hA_def]
    exact ordAt_npoly4Lcm4_eq_one_of_P2 p hchar hsf P1 P2 ua0 ua1 u0 u1
      P h_bot hPX hPY_ne h12 hne34 hnoroot34 hP1ua hP1target hP2ua hP2target
  -- `g(P2) = 0`, giving both `hg_ne` (as a ring element) and (combined
  -- with `hYP2_ne`) `hg_ne_eval` (really `ḡ(P2) ≠ 0`).
  have hgP2_eval : E.eval P2.1 + P2.2 * Y.eval P2.1 = 0 := by
    simpa [hE_def, hY_def] using
      (Epoly4_eval_add_Y_mul_Ypoly4_eval_P2_eq_zero p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hA)
  -- `ḡ(P2) ≠ 0`: since `g(P2) = 0` gives `E(P2) = -P2.2 * Y(P2)`,
  -- we have `ḡ(P2) = E(P2) - Y(P2)*P2.2 = -2*Y(P2)*P2.2 ≠ 0`.
  have hgbar_eval : E.eval P.X + (-Y).eval P.X * P.Y ≠ 0 := by
    rw [hPX, hPY, Polynomial.eval_neg]
    have hYZ : Y.eval P2.1 * P2.2 ≠ 0 :=
      mul_ne_zero (by simpa [hY_def] using hYP2_ne) (hPY ▸ hPY_ne)
    have hgP2_eval' : E.eval P2.1 + Y.eval P2.1 * P2.2 = 0 := by
      linear_combination hgP2_eval
    intro hcontra
    have h2 : (2 : F p) * (Y.eval P2.1 * P2.2) = 0 := by
      linear_combination hgP2_eval' - hcontra
    rcases mul_eq_zero.mp h2 with h2c | h2yz
    · exact absurd h2c hchar
    · exact absurd h2yz hYZ

  have hg_ne : toPair H E Y ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    rintro ⟨-, hY0⟩
    apply hYP2_ne
    rw [← hY_def, hY0]
    simp

  exact ordAtFrac_eq_one_of_old_point P h_bot E Y A U
    hg_ne hgbar_eval hAU hA_ne hU_ne hA_ord
end PointCompositionP2

/-! ## Step 4a: a reusable PrincipalWitness assembly interface

The `P1` proof above contains an important bit of logic that is independent of
how the order-one fact was obtained.  Once the geometric side has supplied
`ordAt P A 0 = 1`, the remaining input to `ordAtFrac_eq_one_of_old_point` is
exactly the pair-norm factorization together with the two nonvanishing facts.
Making that interface explicit is useful for the other five points: each
geometric instantiation should now only have to produce the point-specific
`g = 0` / `bar g ≠ 0` facts and the common factorization data.

This theorem is intentionally just an interface theorem.  In particular, it
does not manufacture any of the point-specific hypotheses; doing so here would
hide precisely the nondegeneracy obligations that still need to be checked at
`P2`, `Ra1`, `Ra2`, `R1`, and `R2`.
-/
section PointCompositionInterface

variable (p : ℕ) [hp : Fact (Nat.Prime p)] [Fact (p ≠ 2)]
variable {H : HyperellipticPolynomial (F p)} [IsDedekindDomain (CoordinateRing H)]

/--
Generic old-point assembly for the `PrincipalWitness` lemma 14.

The geometric part of the proof is completely abstracted into
`hA_ord`.  The algebraic part is the equality
`pairNorm H E Y = A * U`; once that and the two evaluations distinguishing
`g := toPair H E Y` from `ḡ := toPair H E (-Y)` are available, the conclusion is
exactly the desired order-one statement for the fraction with denominator `U`.
-/
omit [Fact (p ≠ 2)] in
theorem ordAtFrac_eq_one_of_old_point_of_pairNorm
    (P : H.Point) (h_bot : pointIdeal P ≠ ⊥)
    (E Y A U : Polynomial (F p))
    (hAU : pairNorm H E Y = A * U)
    (hg_ne : toPair H E Y ≠ 0)
    (hgbar_eval : E.eval P.X + (-Y).eval P.X * P.Y ≠ 0)
    (hA_ne : toPair H A (0 : Polynomial (F p)) ≠ 0)
    (hU_ne : toPair H U (0 : Polynomial (F p)) ≠ 0)
    (hA_ord : ordAt P A (0 : Polynomial (F p)) = 1) :
    ordAtFrac P E Y U (0 : Polynomial (F p)) = 1 := by
  exact ordAtFrac_eq_one_of_old_point P h_bot E Y A U
    hg_ne hgbar_eval hAU hA_ne hU_ne hA_ord

/-- A zero-coefficient witness cannot vanish as a pair at `P` when its `Y`
coefficient is nonzero at `P.X`.  This is the small bridge needed repeatedly
when feeding the PrincipalWitness lemmas: `toPair_eq_zero_iff` is global,
whereas the pointwise hypotheses are stated using polynomial evaluation. -/
omit [Fact (p ≠ 2)] [IsDedekindDomain (CoordinateRing H)] in
lemma toPair_ne_zero_of_eval_snd_ne
    (P : H.Point) (E Y : Polynomial (F p))
    (hY_eval : Y.eval P.X ≠ 0) :
    toPair H E Y ≠ 0 := by
  rw [Ne, toPair_eq_zero_iff]
  intro hzero
  exact hY_eval (by simp [hzero.2])

/-- Characteristic-`≠ 2` algebraic bridge for conjugating the `Y`-coefficient.
If `E + Y*y = 0` at a point, but `Y*y` is nonzero, then the conjugate
expression `E - Y*y` cannot also vanish.  This packages the recurring
`linear_combination`/`mul_eq_zero` argument from the point instantiations. -/
lemma eval_conj_ne_of_eval_add_mul_eq_zero
    {K : Type*} [Field K] (hchar : (2 : K) ≠ 0)
    {e y z : K} (hyz : y * z ≠ 0)
    (h : e + y * z = 0) :
    e + (-y) * z ≠ 0 := by
  intro h'
  have h2 : (2 : K) * (y * z) = 0 := by
    linear_combination h - h'
  exact hyz (by
    rcases mul_eq_zero.mp h2 with h2c | h2yz
    · exact absurd h2c hchar
    · exact h2yz)

end PointCompositionInterface


/-! ## Step 4 (continued): all six pointwise `ordAtFrac` assemblies

The remaining work in this step is deliberately separated from the geometric
root bookkeeping.  Step 3 supplies, at a given named point, the order-one fact
for `npoly4Lcm4` together with the interpolation identity saying that either
`g := E + Y*y` or its conjugate `bar g := E - Y*y` vanishes there.  The only
extra nondegeneracy needed to invoke the corresponding PrincipalWitness lemma
is the explicit pointwise hypothesis
`(Ypoly4 ...).eval P.X ≠ 0`.

This section packages the two algebraic patterns and then gives the five named
wrappers requested for P2/Ra1/Ra2/R1/R2.  The wrappers intentionally take the
pointwise interpolation identity and the Step-3 `ordAt` fact as hypotheses:
those are the completed geometric bridge inputs, while this section is only
responsible for the `ordAtFrac` assembly itself.
-/

section PointwiseOrdAtFracAssembly

variable (p : ℕ) [hp : Fact (Nat.Prime p)] [Fact (p ≠ 2)]
variable {H : HyperellipticPolynomial (F p)} [IsDedekindDomain (CoordinateRing H)]

/-- `P2` specialization of the old-point assembly.  The Step-3 geometry is
represented by `hA_ord` and `hzero`; the `hY` nonvanishing remains explicit.
-/
omit [Fact (p ≠ 2)] in
theorem ordAtFrac_eq_one_of_P2
    (hchar : (2 : F p) ≠ 0)
    (P : H.Point) (h_bot : pointIdeal P ≠ ⊥)
    (E Y A U : Polynomial (F p))
    (hAU : pairNorm H E Y = A * U)
    (hA_ord : ordAt P A (0 : Polynomial (F p)) = 1)
    (hzero : E.eval P.X + P.Y * Y.eval P.X = 0)
    (hY : Y.eval P.X ≠ 0)
    (hPY : P.Y ≠ 0)
    (hA_ne : toPair H A (0 : Polynomial (F p)) ≠ 0)
    (hU_ne : toPair H U (0 : Polynomial (F p)) ≠ 0) :
    ordAtFrac P E Y U (0 : Polynomial (F p)) = 1 := by
  have hYZ : Y.eval P.X * P.Y ≠ 0 := mul_ne_zero hY hPY
  have hzero' : E.eval P.X + Y.eval P.X * P.Y = 0 := by
    simpa [mul_comm] using hzero
  have hbar_eval : E.eval P.X + (-Y).eval P.X * P.Y ≠ 0 := by
    rw [Polynomial.eval_neg]
    exact eval_conj_ne_of_eval_add_mul_eq_zero hchar hYZ hzero'
  have hg_ne : toPair H E Y ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    rintro ⟨hE0, hY0⟩
    apply hY
    rw [hY0]
    simp
  exact ordAtFrac_eq_one_of_old_point P h_bot E Y A U
    hg_ne hbar_eval hAU hA_ne hU_ne hA_ord

/-- `Ra1` specialization of the old-point assembly. -/
omit [Fact (p ≠ 2)] in
theorem ordAtFrac_eq_one_of_Ra1
    (hchar : (2 : F p) ≠ 0)
    (P : H.Point) (h_bot : pointIdeal P ≠ ⊥)
    (E Y A U : Polynomial (F p))
    (hAU : pairNorm H E Y = A * U)
    (hA_ord : ordAt P A (0 : Polynomial (F p)) = 1)
    (hzero : E.eval P.X + P.Y * Y.eval P.X = 0)
    (hY : Y.eval P.X ≠ 0)
    (hPY : P.Y ≠ 0)
    (hA_ne : toPair H A (0 : Polynomial (F p)) ≠ 0)
    (hU_ne : toPair H U (0 : Polynomial (F p)) ≠ 0) :
    ordAtFrac P E Y U (0 : Polynomial (F p)) = 1 := by
  have hYZ : Y.eval P.X * P.Y ≠ 0 := mul_ne_zero hY hPY
  have hzero' : E.eval P.X + Y.eval P.X * P.Y = 0 := by
    simpa [mul_comm] using hzero
  have hbar_eval : E.eval P.X + (-Y).eval P.X * P.Y ≠ 0 := by
    rw [Polynomial.eval_neg]
    exact eval_conj_ne_of_eval_add_mul_eq_zero hchar hYZ hzero'
  have hg_ne : toPair H E Y ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    rintro ⟨hE0, hY0⟩
    apply hY
    rw [hY0]
    simp
  exact ordAtFrac_eq_one_of_old_point P h_bot E Y A U
    hg_ne hbar_eval hAU hA_ne hU_ne hA_ord

set_option maxHeartbeats 400000 in
-- Accumulated elaboration context in PointwiseOrdAtFracAssembly section.
/-- `Ra2` specialization of the old-point assembly. -/
omit [Fact (p ≠ 2)] in
theorem ordAtFrac_eq_one_of_Ra2
    (hchar : (2 : F p) ≠ 0)
    (P : H.Point) (h_bot : pointIdeal P ≠ ⊥)
    (E Y A U : Polynomial (F p))
    (hAU : pairNorm H E Y = A * U)
    (hA_ord : ordAt P A (0 : Polynomial (F p)) = 1)
    (hzero : E.eval P.X + P.Y * Y.eval P.X = 0)
    (hY : Y.eval P.X ≠ 0)
    (hPY : P.Y ≠ 0)
    (hA_ne : toPair H A (0 : Polynomial (F p)) ≠ 0)
    (hU_ne : toPair H U (0 : Polynomial (F p)) ≠ 0) :
    ordAtFrac P E Y U (0 : Polynomial (F p)) = 1 := by
  have hYZ : Y.eval P.X * P.Y ≠ 0 := mul_ne_zero hY hPY
  have hzero' : E.eval P.X + Y.eval P.X * P.Y = 0 := by
    simpa [mul_comm] using hzero
  have hbar_eval : E.eval P.X + (-Y).eval P.X * P.Y ≠ 0 := by
    rw [Polynomial.eval_neg]
    exact eval_conj_ne_of_eval_add_mul_eq_zero hchar hYZ hzero'
  have hg_ne : toPair H E Y ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    rintro ⟨hE0, hY0⟩
    apply hY
    rw [hY0]
    simp
  exact ordAtFrac_eq_one_of_old_point P h_bot E Y A U
    hg_ne hbar_eval hAU hA_ne hU_ne hA_ord

set_option maxHeartbeats 400000 in
-- new-point (residual) case: P is a root of U, not A; uses lemma 13c.
theorem ordAtFrac_eq_one_of_R1
    (hchar : (2 : F p) ≠ 0)
    (P : H.Point) (h_bot : pointIdeal P ≠ ⊥)
    (E Y A U : Polynomial (F p))
    (hAU : pairNorm H E Y = A * U)
    (hA_ord : ordAt P A (0 : Polynomial (F p)) = 0)
    (hU_ord : ordAt P U (0 : Polynomial (F p)) = 1)
    (hbar_zero : E.eval P.X + (-Y).eval P.X * P.Y = 0)
    (hY : Y.eval P.X ≠ 0)
    (hPY : P.Y ≠ 0)
    (hA_ne : toPair H A (0 : Polynomial (F p)) ≠ 0)
    (hU_ne : toPair H U (0 : Polynomial (F p)) ≠ 0) :
    ordAtFrac P E Y U (0 : Polynomial (F p)) = -1 := by
  have hYZbar : (-Y).eval P.X * P.Y ≠ 0 :=
    mul_ne_zero (by simp [hY]) hPY
  have hg_ne : toPair H E Y ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]; rintro ⟨-, hY0⟩; simp [hY0] at hY
  have hbar_global_ne : toPair H E (-Y) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    rintro ⟨-, hY0⟩; apply hY
    have : Y = 0 := neg_eq_zero.mp hY0
    simp [this]
  have hg_eval : E.eval P.X + (-(-Y)).eval P.X * P.Y ≠ 0 := by
    simp only [neg_neg]
    have h := eval_conj_ne_of_eval_add_mul_eq_zero hchar hYZbar hbar_zero
    simpa [Polynomial.eval_neg] using h
  exact ordAtFrac_eq_neg_one_of_residual_point P h_bot E Y A U
    hg_ne hbar_global_ne hg_eval hAU hA_ne hU_ne hA_ord hU_ord

set_option maxHeartbeats 400000 in
-- new-point (residual) case: same as R1.
/-- `R2` specialization of the new-point assembly. -/
theorem ordAtFrac_eq_one_of_R2
    (hchar : (2 : F p) ≠ 0)
    (P : H.Point) (h_bot : pointIdeal P ≠ ⊥)
    (E Y A U : Polynomial (F p))
    (hAU : pairNorm H E Y = A * U)
    (hA_ord : ordAt P A (0 : Polynomial (F p)) = 0)
    (hU_ord : ordAt P U (0 : Polynomial (F p)) = 1)
    (hbar_zero : E.eval P.X + (-Y).eval P.X * P.Y = 0)
    (hY : Y.eval P.X ≠ 0)
    (hPY : P.Y ≠ 0)
    (hA_ne : toPair H A (0 : Polynomial (F p)) ≠ 0)
    (hU_ne : toPair H U (0 : Polynomial (F p)) ≠ 0) :
    ordAtFrac P E Y U (0 : Polynomial (F p)) = -1 := by
  have hYZbar : (-Y).eval P.X * P.Y ≠ 0 :=
    mul_ne_zero (by simp [hY]) hPY
  have hg_ne : toPair H E Y ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]; rintro ⟨-, hY0⟩; simp [hY0] at hY
  have hbar_global_ne : toPair H E (-Y) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    rintro ⟨-, hY0⟩; apply hY
    have : Y = 0 := neg_eq_zero.mp hY0
    simp [this]
  have hg_eval : E.eval P.X + (-(-Y)).eval P.X * P.Y ≠ 0 := by
    simp only [Polynomial.eval_neg, neg_neg]
    have h := eval_conj_ne_of_eval_add_mul_eq_zero hchar hYZbar hbar_zero
    simpa [Polynomial.eval_neg] using h
  exact ordAtFrac_eq_neg_one_of_residual_point P h_bot E Y A U
    hg_ne hbar_global_ne hg_eval hAU hA_ne hU_ne hA_ord hU_ord

/-- Two explicit old-point cases can be wired directly to the old-point
PrincipalWitness theorem without manufacturing any hidden nondegeneracy.
This is the reusable case-split shape used by the eventual six-point caller.
-/
theorem ordAtFrac_eq_one_of_old_point_cases
    (P Q₁ Q₂ : H.Point)
    (hPcase : P = Q₁ ∨ P = Q₂)
    (hQ₁ : ordAtFrac Q₁ E Y U (0 : Polynomial (F p)) = 1)
    (hQ₂ : ordAtFrac Q₂ E Y U (0 : Polynomial (F p)) = 1) :
    ordAtFrac P E Y U (0 : Polynomial (F p)) = 1 := by
  rcases hPcase with rfl | rfl
  · exact hQ₁
  · exact hQ₂

/-- Four-way old-point dispatcher for `P1`, `P2`, `Ra1`, `Ra2`.  Each
branch is already the fully assembled pointwise valuation theorem, so the
case split itself introduces no additional nondegeneracy assumptions. -/
theorem ordAtFrac_eq_one_of_four_old_point_cases
    (P P1 P2 Ra1 Ra2 : H.Point)
    (hPcase : P = P1 ∨ P = P2 ∨ P = Ra1 ∨ P = Ra2)
    (hP1 : ordAtFrac P1 E Y U (0 : Polynomial (F p)) = 1)
    (hP2 : ordAtFrac P2 E Y U (0 : Polynomial (F p)) = 1)
    (hRa1 : ordAtFrac Ra1 E Y U (0 : Polynomial (F p)) = 1)
    (hRa2 : ordAtFrac Ra2 E Y U (0 : Polynomial (F p)) = 1) :
    ordAtFrac P E Y U (0 : Polynomial (F p)) = 1 := by
  rcases hPcase with rfl | rfl | rfl | rfl
  · exact hP1
  · exact hP2
  · exact hRa1
  · exact hRa2

/-- Two-way new-point dispatcher for `R1`/`R2`.  The two branches carry the
negative valuation furnished by `ordAtFrac_neg_eq_one_of_new_point`. -/
theorem ordAtFrac_neg_eq_one_of_two_new_point_cases
    (P R1 R2 : H.Point)
    (hPcase : P = R1 ∨ P = R2)
    (hR1 : ordAtFrac R1 E Y U (0 : Polynomial (F p)) = -1)
    (hR2 : ordAtFrac R2 E Y U (0 : Polynomial (F p)) = -1) :
    ordAtFrac P E Y U (0 : Polynomial (F p)) = -1 := by
  rcases hPcase with rfl | rfl
  · exact hR1
  · exact hR2

end PointwiseOrdAtFracAssembly

/-! ## Status note (this pass): the generic PrincipalWitness assembly layer is now
## explicit; P1 is the first concrete instantiation, and the `R_i`/`ι(R_i)`
## orientation is resolved for the eventual new-point cases.

**Current concrete Step-4 status:** P1 was already assembled end-to-end;
this pass adds the five remaining pointwise wrappers `P2`, `Ra1`, `Ra2`,
`R1`, and `R2`, plus the old/new case-split dispatchers.  Each wrapper
consumes the completed Step-3 inputs as explicit hypotheses: the order-one
fact for `A := npoly4Lcm4`, the appropriate interpolation zero (`g(P)=0`
for old points or `bar g(P)=0` for new points), and the pointwise
`Y.eval P.X ≠ 0` condition.  Thus the nondegeneracy condition is never
silently inferred.  The root-specific Step-3 theorems remain responsible
for producing those hypotheses from the named `P2`/`Ra1`/`Ra2`/`R1`/`R2`
geometry; this file's Step-4 layer now performs the complete `ordAtFrac`
assembly once they are supplied.  `ordAt_npoly4Lcm4_eq_one_of_P1`/`_P2`/
`_Ra1`/`_Ra2`/`_R1`/`_R2`. The
`ua`/`u_target`-root cases each needed one extra step
(`quadratic_eq_mul_X_sub_C` splitting the relevant quadratic into its two
named linear factors) plus a 3-slot/5-factor merge trick (Layer 3's
underlying lemma only has `F₁ F₂ F₃` slots, but splitting a quadratic
leaves 5 flat factors total — the "other" linear/quadratic pair not
containing the designated root is merged into a single `F₃`, which is
free since Layer 3 only needs `Fᵢ.eval a ≠ 0`, no shape constraint). Not
yet build-tested past `Ra2`/`R1`/`R2` as of writing this note — Claire's
REPL to confirm.

**Resolved this pass: the `R_i` vs `ι(R_i)` orientation question flagged
by the roadmap's "Status update, pass #7" section.** Traced directly
against two already-proved facts, not assumed either way:

- `vRS4General := -Epoly4 * gcdA(Ypoly4, uRS4General) mod uRS4General`
  (`GeneralSharedRoot.lean`, confirmed by direct read) — the standard
  Cantor/Mumford sign convention `v ≡ -E/Y mod U`. This means `g := toPair
  H Epoly4 Ypoly4`'s OWN zero at a root `r` of `uRS4General` is the point
  `(r, v(r))` — `g`'s interpolation was built to vanish there, by
  construction.
- Lemma 15 (`ordAtFrac_neg_eq_one_of_new_point`, `PrincipalWitness.lean`)
  identifies a "residual/new" point via `hgbar_ne : toPair H E (-Y) ≠ 0`
  becoming the VANISHING side at the call site (the lemma's own docstring:
  *"at a point where `ḡ(P) = 0`... `g(P) ≠ 0`"*) — i.e. the point that
  actually contributes to `D_new` in the assembly is where `ḡ := toPair H
  E (-Y)` vanishes, NOT where `g` itself vanishes.

Since `toPair H E (-Y)` vanishing at `(x_0,y_0)` means `E(x_0) -
Y(x_0)·y_0 = 0`, i.e. `y_0 = E(x_0)/Y(x_0) = -v(x_0)` (using
`vRS4General`'s confirmed minus sign), the point lemma 15 actually
selects at a root `r` of `uRS4General` is `(r, -v(r))` — the
HYPERELLIPTIC CONJUGATE of `g`'s own zero `(r, v(r))`.

**Conclusion: `D_new`'s two points are `ι(R1), ι(R2)` — the conjugates of
`R1`/`R2` as `g`'s own Mumford-selected points — NOT `R1, R2` directly.**
This is a real orientation fact the call-site assembly (composing lemmas
14/15 at each of the 6 named points, item 2 below) must get right: at
each of `R1`/`R2`, the "new point" case (lemma 15) is the one that
applies, and the `H.Point` it concludes about is `⟨R_i, -v(R_i)⟩`, not
`⟨R_i, v(R_i)⟩`. The 6 `ordAt_npoly4Lcm4_eq_one_of_*` theorems above are
unaffected by this (they only pin down `P.X`, taking `P.Y ≠ 0` and
`h_bot` as hypotheses rather than constructing `H.Point.mk` internally —
per each theorem's own docstring) — the orientation only matters once a
caller instantiates `P` concretely at the assembly call site.

**What is still missing, honestly, before `reducedClass_eq_of_isReduction'`
can lose its `sorry`** (do not attempt to fake past this list):

1. Composing each `ordAt P npoly4Lcm4 0 = 1` fact (the six theorems above)
   with `Npoly4 = npoly4Lcm4 * uRS4General` (Step 1, already proved) to
   get `ordAt P A 0 = 1` in `PrincipalWitness.lean`'s lemma-14/15 sense
   (`A := npoly4Lcm4` there), then applying lemmas 14/15 themselves at
   each of the 6 points — using the NOW-RESOLVED orientation above for the
   `R1`/`R2` cases (lemma 15, point `⟨R_i, -v(R_i)⟩`) versus `P1`/`P2`/
   `Ra1`/`Ra2` (lemma 14, point as constructed). Not attempted this pass.
2. **The `Sg`/`Su`/`divToPairRatio`/`principalSubgroup`-membership half of
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
   `toJacobian` absorb the leftover `4•[δ₀]` term — `D_new`'s point labels
   in this identity use the now-resolved `ι(R1), ι(R2)` orientation above,
   not `R1, R2`. **Not yet written as Lean** — this is the next pass's
   actual target for this piece.

`reducedClass_eq_of_isReduction'` itself is NOT touched this pass and stays
`sorry` — the gap above is too large to close with a guessed proof term,
and this project's own convention (search/ask rather than guess) applies
doubly hard to a correction-term computation not yet checked against
`reducedClass`'s actual definition. -/

/-! ## Status note (this pass, #11): `P2`'s full concrete composition
## (item 1's pattern, second of six) is now on file, alongside `P1`'s

**What this pass adds**: `ordAtFrac_eq_one_of_P2_full`, in a new
`PointCompositionP2` section immediately after `PointCompositionP1`. This
is `ordAtFrac_eq_one_of_P1`'s exact mirror — same derivation of `hAU`
(via `Npoly4_eq_npoly4Lcm4_mul_uRS4General`), `hA_ne`/`hU_ne` (monic
non-zero-ness of `A := npoly4Lcm4` and `U := C leadingCoeff * uRS4General`),
`hA_ord` (via `ordAt_npoly4Lcm4_eq_one_of_P2`, already on file), and
`hg_ne`/`hgbar_eval` (via `Epoly4_eval_add_Y_mul_Ypoly4_eval_P2_eq_zero`,
already on file, confirmed present in `AlphaReduce.lean`) — with every
`P1`-specific occurrence (coordinates, hypothesis names) swapped for `P2`'s
own. No new mathematical content: this is the literal "item 1" composition
step the roadmap's own status notes describe, applied to the second of the
six named points, using only theorems already confirmed on file (this
pass added no new lemmas to `AlphaReduce.lean` or elsewhere — everything
`P2`'s composition needs was already present, just not yet wired together
into one end-to-end theorem the way `P1`'s was).

**Naming note**: called `ordAtFrac_eq_one_of_P2_full`, not bare
`ordAtFrac_eq_one_of_P2`, because that name is already taken by the
abstract wrapper in the `PointwiseOrdAtFracAssembly` section above (which
takes `hA_ord`/`hzero` as bare hypotheses rather than deriving them from
raw interpolation data). `P1`'s theorem never collided with anything
because no abstract `ordAtFrac_eq_one_of_P1` wrapper exists elsewhere in
this file — only `P2` (and, if fully composed in a future pass, `Ra1`/
`Ra2`/`R1`/`R2`) needs the `_full` suffix to disambiguate from its
already-existing abstract counterpart.

**Not yet build-tested — Claire's REPL to confirm**, though risk is
assessed as low: every step is a mechanical re-derivation of `P1`'s
already-confirmed-build-clean proof, swapping named constants only; no new
tactic sequence, no new lemma composition shape.

**Still not done**: the analogous full compositions for `Ra1`, `Ra2`,
`R1`, `R2` (four more of the six). The `Ra1`/`Ra2` cases will need
`Epoly4_eval_add_va_eval_mul_Ypoly4_eval_eq_zero_of_root_ua` (pass #10,
already on file in `AlphaReduce.lean`) in place of the direct `P1`/`P2`
`g(point)=0` theorems, taking the relevant root of `u_a` as an explicit
hypothesis rather than reading off a named point's own coordinate — and
will need `hgbar_eval` re-derived at that root rather than at a `P.Y`-typed
point coordinate directly, since `Ra1`/`Ra2`'s own curve-point `y`-value is
`va.eval Ra1`/`va.eval Ra2` (via `IsMumfordUa`), not a free `P.2` the
caller supplies. The `R1`/`R2` cases are structurally different again —
they use `ordAtFrac_eq_neg_one_of_residual_point` (lemma 13c), not
`ordAtFrac_eq_one_of_old_point` (lemma 14), and that lemma's `hA_ord`/
`hU_ord` roles are swapped relative to the old-point cases (`ordAt P A 0 =
0`, `ordAt P U 0 = 1` — i.e. the *residual* factor, not `npoly4Lcm4`, is
what needs the order-one fact at `R1`/`R2`; `Npoly4 = npoly4Lcm4 *
uRS4General` still supplies `hAU`, but the roles of the two factors in the
lemma's hypothesis list are reversed relative to `P1`/`P2`/`Ra1`/`Ra2` and
the `ι(R_i)` orientation resolved above must be threaded through). None of
this is attempted yet; recommend `Ra1`/`Ra2` as the next pass's target
before `R1`/`R2`, since they reuse lemma 14 (same shape as `P1`/`P2`, just
with a root-hypothesis instead of a named-point hypothesis) rather than
introducing lemma 13c's swapped-roles complication. -/

end DecoupledSystem
end Genus2Lean

