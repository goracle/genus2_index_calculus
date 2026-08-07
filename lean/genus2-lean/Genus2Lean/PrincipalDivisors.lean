import Mathlib
import Genus2Lean.HyperellipticFunctionField
import Genus2Lean.AffinePoints
import Genus2Lean.DivisorClassGroup

set_option linter.style.header false

/-!
# Genus-2 index calculus: principal divisors, points at infinity, and toward the FFK dichotomy

`DivisorClassGroup.lean` built `J` as a quotient of `Divisor0 H` by an *abstract*
subgroup `P` satisfying only `P ≤ Divisor0 H`, flagging as the remaining gap that `P`
is not actually derived from `CoordinateRing H`. This file starts closing that gap.

## Scope of this file, stated up front

Deriving genuine principal divisors requires (1) a point-at-infinity type completing
the affine model to a smooth projective model, (2) a Dedekind-domain / valuation-theoretic
notion of order of vanishing at every point (affine and infinite), (3) the theorem that
`deg(div g) = 0` for every nonzero rational function `g`. Per this project's scoping
discussion: the natDegree = 6 case's points at infinity require a smooth model
(blow-up/normalization) that is out of reach of the *affine* coordinate ring alone, so
it is captured here only as an axiomatized/parametrized stand-in
(`PointsAtInfinityData`, §1 below) that a later session can fill in properly. The
natDegree = 5 case (one point at infinity, fixed by `ι`) is built concretely, reusing
`RiemannRochSpaceInf`'s pole-order convention (§2). The Dedekind-domain proof for
`CoordinateRing H` (needed to even define affine orders of vanishing rigorously, §3)
and the `deg(div g) = 0` theorem (§4) are the two hardest remaining steps in this
project and are recorded here as explicit, clearly-labelled `sorry`s — NOT filled in,
NOT worked around, and NOT silently assumed elsewhere. Every downstream construction
that depends on them is named so the dependency is auditable.

Nothing in this file is wired back into `DivisorClassGroup.lean`'s `Jacobian`/`s`
yet — that integration (instantiating a `PrincipalDivisorData` from the results here)
is left for once §3–§4 are actually closed, since `PrincipalDivisorData.le_Divisor0`
requires exactly the `deg(div g) = 0` fact that is `sorry`'d in §4.
-/

noncomputable section

open Polynomial

namespace HyperellipticPolynomial

open Divisor
variable {k : Type*} [Field k]
variable {H : HyperellipticPolynomial k}

/-! ## §1. Points at infinity -/

/-- Data package for the points at infinity of `C`, parametrized rather than
constructed, for the `natDegree = 6` case. A genuine construction needs the smooth
projective model of `C` (the naive affine chart is singular at infinity when
`H.f.natDegree = 6`, since both branches of `y² = f(x)` meet there); building that
model from `CoordinateRing H` alone is out of scope for this file (see module
docstring) and is left as this structure's obligation. Advisory-7's Sidon-theorem
application does not depend on the deg-6 case being resolved before the deg-5 case
is usable, so this is deliberately kept separate rather than blocking on it. -/
structure PointsAtInfinityData (H : HyperellipticPolynomial k)
    (hdeg6 : H.f.natDegree = 6) where
  /-- The (as yet unconstructed) type of points at infinity: two points, swapped by
  the hyperelliptic involution, when `H.f.natDegree = 6`. -/
  PtsAtInf : Type*
  /-- There are exactly two points at infinity in the deg-6 case (this is a
  standard fact about the smooth model, not proved here — see module docstring). -/
  card_eq_two : Nat.card PtsAtInf = 2
  /-- The involution acts on the points at infinity, swapping the two. -/
  involutionInf : Equiv.Perm PtsAtInf
  /-- The involution at infinity has no fixed points (the two points at infinity
  are distinct and swapped, unlike the deg-5 case's single fixed point at
  infinity) — this is what makes the deg-6 case genuinely different from deg-5
  for the FFK dichotomy's exceptional-pair clause. -/
  involutionInf_ne : ∀ p, involutionInf p ≠ p

/-- The point-at-infinity for the `natDegree = 5` case: there is exactly one, and it
is fixed by the hyperelliptic involution (`y` has a pole of odd order there, so
`y ↦ -y` cannot swap it with a second point — there is no second point in this
case). Represented as `Unit` since the construction needs no further data: unlike
the deg-6 case, the deg-5 point at infinity is the unique point of the smooth model
lying over `x = ∞`, and every fact about it used downstream (its role in
`RiemannRochSpaceInf`'s pole-order convention) is already pinned down by
`HyperellipticFunctionField.lean`'s `inLInf`. -/
abbrev PointAtInfinityDeg5 : Type := Unit

/-- The full point type of `C` in the `natDegree = 5` case: affine points, plus the
single point at infinity. This is the type `Divisor` should really be built on
(`DivisorClassGroup.lean`'s `Divisor H := H.Point →₀ ℤ` is, in this light, the
restriction of the true divisor group to divisors supported away from infinity —
consistent with that file's own documented affine-only scope). -/
def FullPointDeg5 (H : HyperellipticPolynomial k) : Type _ :=
  H.Point ⊕ PointAtInfinityDeg5

/-- The point at infinity, as an element of `FullPointDeg5`. -/
def infPoint (H : HyperellipticPolynomial k) : FullPointDeg5 H :=
  Sum.inr ()

/-- The point-level involution extended to `FullPointDeg5`: acts as `Point.iota` on
affine points, and fixes the point at infinity (per the deg-5 case's defining
property, documented above). -/
def FullPointDeg5.iota (H : HyperellipticPolynomial k) : FullPointDeg5 H → FullPointDeg5 H
  | Sum.inl P => Sum.inl (Point.iota P)
  | Sum.inr u => Sum.inr u

@[simp] theorem FullPointDeg5.iota_inr (H : HyperellipticPolynomial k) (u : PointAtInfinityDeg5) :
    FullPointDeg5.iota H (Sum.inr u) = Sum.inr u := rfl

@[simp] theorem FullPointDeg5.iota_inl (H : HyperellipticPolynomial k) (P : H.Point) :
    FullPointDeg5.iota H (Sum.inl P) = Sum.inl (Point.iota P) := rfl

theorem FullPointDeg5.iota_iota (H : HyperellipticPolynomial k) (Q : FullPointDeg5 H) :
    FullPointDeg5.iota H (FullPointDeg5.iota H Q) = Q := by
  cases Q with
  | inl P => simp [FullPointDeg5.iota, Point.iota_iota]
  | inr u => simp [FullPointDeg5.iota]

/-! ## §2. The order of `A(x) + B(x)y` at the point at infinity, deg-5 case -/

/-- The order of vanishing of `A(x) + B(x)y` at the point at infinity (deg-5 case),
as a pole order: `ordInf (A + By) = -max(2 deg A, 2 deg B + 5)` when `A + By ≠ 0` (in
`CoordinateRing H`, equivalently `(A, B) ≠ (0, 0)`), matching `inLInf`'s convention
that this quantity bounded above by `n` characterizes membership in `L(n P∞)`. -/
def ordInfOfPair (A B : k[X]) : ℤ :=
  haveI := Classical.propDecidable (A = 0 ∧ B = 0)
  haveI := Classical.propDecidable (B = 0)
  if A = 0 ∧ B = 0 then 0
  else - (max (2 * A.natDegree : ℤ) (if B = 0 then 0 else 2 * B.natDegree + 5))

/-- `toPair_injective`'s proof, isolated: `toPair H A B = 0` in `CoordinateRing H`
forces `A = 0 ∧ B = 0`. -/
theorem toPair_eq_zero_iff (H : HyperellipticPolynomial k) (A B : k[X]) :
    toPair H A B = 0 ↔ A = 0 ∧ B = 0 := by
  constructor
  · intro heq
    have heq' : AdjoinRoot.mk ((X : (k[X])[X]) ^ 2 - C H.f) (C A + C B * X) = 0 := by
      have : toPair H A B =
          AdjoinRoot.mk ((X : (k[X])[X]) ^ 2 - C H.f) (C A + C B * X) := rfl
      rw [this] at heq
      exact heq
    rw [AdjoinRoot.mk_eq_zero] at heq'
    set f : (k[X])[X] := (X : (k[X])[X]) ^ 2 - C H.f with hf_def
    set g : (k[X])[X] := C A + C B * X with hg_def
    have hg_eq_zero : g = 0 := by
      by_contra hg_ne
      have hg_deg : g.natDegree ≤ 1 := by rw [hg_def]; compute_degree
      have hf_deg : f.natDegree = 2 := by
        rw [hf_def]
        compute_degree!
      have hcontra := Polynomial.natDegree_le_of_dvd heq' hg_ne
      rw [hf_deg] at hcontra
      omega
    have hcoeff0 : g.coeff 0 = A := by rw [hg_def]; simp
    have hcoeff1 : g.coeff 1 = B := by rw [hg_def]; simp
    rw [hg_eq_zero] at hcoeff0 hcoeff1
    simp only [coeff_zero] at hcoeff0 hcoeff1
    exact ⟨hcoeff0.symm, hcoeff1.symm⟩
  · rintro ⟨rfl, rfl⟩
    simp [toPair]

/-- `ordInfOfPair` is well-defined on the ring element `A + By`. -/
theorem toPair_injective (H : HyperellipticPolynomial k) (_hdeg : H.f.natDegree = 5)
    (A₁ B₁ A₂ B₂ : k[X]) (heq : toPair H A₁ B₁ = toPair H A₂ B₂) :
    A₁ = A₂ ∧ B₁ = B₂ := by
  have hsub : toPair H (A₁ - A₂) (B₁ - B₂) = 0 := by
    have : toPair H (A₁ - A₂) (B₁ - B₂) = toPair H A₁ B₁ - toPair H A₂ B₂ := by
      unfold toPair
      rw [map_sub, map_sub]
      ring
    rw [this, heq, sub_self]
  obtain ⟨hA, hB⟩ := (toPair_eq_zero_iff H (A₁ - A₂) (B₁ - B₂)).mp hsub
  exact ⟨sub_eq_zero.mp hA, sub_eq_zero.mp hB⟩

/-- The degree of `A^2` is always even. -/
theorem natDegree_sq (p : k[X]) : (p ^ 2).natDegree = 2 * p.natDegree := by
  by_cases hp : p = 0
  · subst hp; simp
  · rw [sq, Polynomial.natDegree_mul hp hp]
    ring

/-- The degree of `B^2 * H.f` is always odd when `H.f.natDegree = 5` and `B ≠ 0`. -/
theorem natDegree_sq_mul_f (H : HyperellipticPolynomial k) (hdeg : H.f.natDegree = 5)
    {B : k[X]} (hb : B ≠ 0) : (B ^ 2 * H.f).natDegree = 2 * B.natDegree + 5 := by
  have hf0 : H.f ≠ 0 := by
    intro h
    rw [h] at hdeg
    simp at hdeg
  have hb2 : B ^ 2 ≠ 0 := pow_ne_zero 2 hb
  rw [Polynomial.natDegree_mul hb2 hf0, natDegree_sq, hdeg]

/-- The main degree formula: for `(A, B) ≠ (0, 0)`, the degree of `pairNorm H A B`
in `k[X]` equals `-ordInfOfPair A B`. Parity prevents degree cancellation between
`A^2` (even degree) and `B^2 * H.f` (odd degree). -/
theorem natDegree_pairNorm_eq_neg_ordInfOfPair (H : HyperellipticPolynomial k)
    (hdeg : H.f.natDegree = 5) (A B : k[X]) (hAB : ¬(A = 0 ∧ B = 0)) :
    ((pairNorm H A B).natDegree : ℤ) = - ordInfOfPair A B := by
  dsimp [ordInfOfPair]
  rw [if_neg hAB, neg_neg]
  by_cases hb : B = 0
  · -- Case B = 0: pairNorm H A 0 = A^2
    subst hb
    have ha : A ≠ 0 := by
      rintro rfl
      exact hAB ⟨rfl, rfl⟩
    have hnorm : pairNorm H A 0 = A ^ 2 := by
      unfold pairNorm
      simp
    rw [hnorm, natDegree_sq]
    simp only [if_true]
    have hpos : (0 : ℤ) ≤ 2 * (A.natDegree : ℤ) := by positivity
    rw [max_eq_left hpos]
    push_cast
    rfl
  · -- Case B ≠ 0: parity forces natDegree (A^2 - B^2 * H.f) = max deg(A^2) deg(B^2 * H.f)
    rw [if_neg hb]
    unfold pairNorm
    have hdegA : (A ^ 2).natDegree = 2 * A.natDegree := natDegree_sq A
    have hdegB : (B ^ 2 * H.f).natDegree = 2 * B.natDegree + 5 := natDegree_sq_mul_f H hdeg hb
    have hne : (A ^ 2).natDegree ≠ (B ^ 2 * H.f).natDegree := by
      rw [hdegA, hdegB]
      omega
    have hmax : (A ^ 2 - B ^ 2 * H.f).natDegree =
        max (A ^ 2).natDegree (B ^ 2 * H.f).natDegree := by
      rw [sub_eq_add_neg]
      have hneg : (- (B ^ 2 * H.f)).natDegree = (B ^ 2 * H.f).natDegree :=
        Polynomial.natDegree_neg (B ^ 2 * H.f)
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hlt' : (A ^ 2).natDegree < (- (B ^ 2 * H.f)).natDegree := by rwa [hneg]
        rw [Polynomial.natDegree_add_eq_right_of_natDegree_lt hlt', hneg, max_eq_right_of_lt hlt]
      · have hgt' : (- (B ^ 2 * H.f)).natDegree < (A ^ 2).natDegree := by rwa [hneg]
        rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt hgt', max_eq_left_of_lt hgt]
    rw [hmax, hdegA, hdegB]
    push_cast
    rfl

/-! ## §3. Affine orders of vanishing via Dedekind-domain machinery -/

/-- The hypotheses needed for `CoordinateRing H` to be a Dedekind domain. -/
structure NonsingularData (H : HyperellipticPolynomial k) where
  irreducible_defining_poly :
    Irreducible ((X : (k[X])[X]) ^ 2 - C H.f)
  squarefree_f : Squarefree H.f
  char_ne_two : (2 : k) ≠ 0

/-- Given `NonsingularData`, `CoordinateRing H` is an integral domain. -/
theorem coordinateRingIsDomain (H : HyperellipticPolynomial k)
    (nd : NonsingularData H) : IsDomain (CoordinateRing H) := by
  haveI : IsDomain (k[X]) := inferInstance
  exact AdjoinRoot.isDomain_of_prime nd.irreducible_defining_poly.prime

/-- `CoordinateRing H` is Noetherian as a quotient of the polynomial ring `k[X][X]`. -/
instance coordinateRing_isNoetherian (H : HyperellipticPolynomial k) :
    IsNoetherianRing (CoordinateRing H) := by
  haveI : IsNoetherianRing (k[X]) := inferInstance
  haveI : IsNoetherianRing ((k[X])[X]) := Polynomial.isNoetherianRing
  exact Ideal.Quotient.isNoetherianRing _

-- `coordinateRing_isIntegrallyClosed` and `coordinateRingIsDedekindDomain` now live in
-- `PrincipalDivisorsIntegralClosure.lean`, which imports both this file and
-- `DedekindClosure5` (the latter transitively imports this file via
-- `PrincipalDivisorsDedekind.lean`, so those two theorems can't live here without
-- creating an import cycle).

/-! ## §3.5. Concrete affine valuations -/

set_option linter.style.openClassical false
open Classical

/-- Evaluation map on `CoordinateRing H` at an affine point `P = (x₀, y₀)`,
mapping $X \mapsto P.val.1$ and $Y \mapsto P.val.2$. -/
def evalAtPoint (P : H.Point) : CoordinateRing H →+* k :=
  AdjoinRoot.lift (Polynomial.evalRingHom P.val.1) P.val.2 (by
    have hP : P.val.2 ^ 2 - eval P.val.1 H.f = 0 :=
      sub_eq_zero.mpr P.property
    simpa [HyperellipticPolynomial.Equation] using hP)

/-- `evalAtPoint P` is surjective onto $k$ because constant scalars $c \in k$ map to themselves. -/
theorem evalAtPoint_surjective (P : H.Point) :
    Function.Surjective (evalAtPoint P) := by
  intro c
  refine ⟨AdjoinRoot.mk ((X : (k[X])[X]) ^ 2 - C H.f) (C (C c)), ?_⟩
  change Polynomial.eval₂ (Polynomial.evalRingHom P.val.1) P.val.2 (C (C c)) = c
  simp

/-- The maximal ideal $\mathfrak{m}_P \subset \text{CoordinateRing } H$ vanishing at $P$. -/
def pointIdeal (P : H.Point) : Ideal (CoordinateRing H) :=
  RingHom.ker (evalAtPoint P)

/-- $\mathfrak{m}_P$ is a maximal ideal since `evalAtPoint P` is surjective onto the field `k`. -/
theorem pointIdeal_isMaximal (P : H.Point) : (pointIdeal P).IsMaximal := by
  have hsurj := evalAtPoint_surjective P
  exact RingHom.ker_isMaximal_of_surjective (evalAtPoint P) hsurj

/-- `pointIdeal P` as a height-one prime ideal in `CoordinateRing H`. -/
def pointHeightOne [IsDedekindDomain (CoordinateRing H)]
    (P : H.Point) (h_bot : pointIdeal P ≠ ⊥) :
    IsDedekindDomain.HeightOneSpectrum (CoordinateRing H) where
  asIdeal := pointIdeal P
  isPrime := (pointIdeal_isMaximal P).isPrime
  ne_bot := h_bot

/-- Concrete order of vanishing of $A(x) + B(x)y$ at an affine point $P$,
defined via the local valuation at $\mathfrak{m}_P$. -/
noncomputable def ordAt [IsDedekindDomain (CoordinateRing H)]
    (P : H.Point) (A B : k[X]) : ℤ :=
  if toPair H A B = 0 then
    0
  else if h_bot : pointIdeal P = ⊥ then
    0
  else
    WithZero.log ((pointHeightOne P h_bot).intValuation (toPair H A B))
    

/-! ## §4. `deg(div g) = 0` — the target theorem -/

/-- The norm bridge lemma: the sum of the affine orders of vanishing of $A(x) + B(x)y$
equals the degree of its norm $N(A + By) = A^2 - B^2 f$. -/
theorem sum_ordAt_eq_natDegree_pairNorm [IsDedekindDomain (CoordinateRing H)]
    (S : Finset H.Point) (A B : k[X]) (hAB : ¬(A = 0 ∧ B = 0))
    (hsupp : ∀ P, P ∉ S → ordAt P A B = 0) :
    (∑ P ∈ S, ordAt P A B) = ((pairNorm H A B).natDegree : ℤ) := by
  sorry

/-- Target statement: the affine orders plus the order at infinity sum to zero. -/
theorem deg_div_eq_zero_deg5 (H : HyperellipticPolynomial k) (hdeg : H.f.natDegree = 5)
    [IsDedekindDomain (CoordinateRing H)]
    (S : Finset H.Point) (A B : k[X]) (hAB : ¬(A = 0 ∧ B = 0))
    (hsupp : ∀ P, P ∉ S → ordAt P A B = 0) :
    (∑ P ∈ S, ordAt P A B) + ordInfOfPair A B = 0 := by
  rw [sum_ordAt_eq_natDegree_pairNorm S A B hAB hsupp]
  have hdeg_norm := natDegree_pairNorm_eq_neg_ordInfOfPair H hdeg A B hAB
  rw [hdeg_norm]
  omega

end HyperellipticPolynomial
