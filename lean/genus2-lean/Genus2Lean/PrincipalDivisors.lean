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
defined via the local valuation at $\mathfrak{m}_P$.

**Sign convention, fixed this session**: `WithZero.log ∘ intValuation` alone computes
`-(membership multiplicity)` (confirmed by direct proof in `ordAt_eq_count` below — see
that theorem's proof for the derivation via `WithZero.exp_log`/`WithZero.exp_injective`),
since `intValuationDef`'s defining equation uses the "absolute value" sign convention
standard for valuations (`ofAdd (-(count))`), the *opposite* of the "order of vanishing"
convention this file's naming (`ordAt`, `ordAt_nonneg`) assumes throughout. The explicit
`-` below corrects for that, so `ordAt P A B ≥ 0` for points actually on the zero locus,
matching every downstream use in this file (§4.2/§4.4's "local multiplicities
`(ordAt P A B).toNat`" phrasing, `ordAt_nonneg`, `sum_ordAt_eq_natDegree_pairNorm`'s
bookkeeping) at face value. -/
noncomputable def ordAt [IsDedekindDomain (CoordinateRing H)]
    (P : H.Point) (A B : k[X]) : ℤ :=
  if toPair H A B = 0 then
    0
  else if h_bot : pointIdeal P = ⊥ then
    0
  else
    -WithZero.log ((pointHeightOne P h_bot).intValuation (toPair H A B))

/-! ## §4. `deg(div g) = 0` — the target theorem

**Scaffold, not a complete proof.** `sum_ordAt_eq_natDegree_pairNorm` decomposes into four
steps below (§4.1–§4.4), each stated as its own theorem, plus a final assembly. §4.1 and §4.3
look mechanical (unfolding definitions / the first isomorphism theorem) but their exact closing
tactics were not checked against a live goal state, so they are `sorry`'d too rather than
asserted solid; §4.2 and §4.4 are the genuinely hard steps (CRT/associated-graded dimension
counting, and a rank-2-free-module determinant computation, respectively). Only the final
assembly (`sum_ordAt_eq_natDegree_pairNorm` itself) is fully proved, and it is pure bookkeeping
conditional on the four lemmas above it. This mirrors the file's own stated policy (see the
top-of-file docstring): genuinely hard or unverified steps are recorded as named, individually
auditable `sorry`s, not worked around or silently assumed.

The four steps, informally:

1. (§4.1, `sorry`'d — plausible/mechanical) `ordAt P A B` is (via `intValuationDef`'s
   definition, `Associates.count`
   of `pointHeightOne P`'s ideal in the factorization of `Ideal.span {toPair H A B}`) exactly
   the multiplicity of the prime `pointIdeal P` dividing `Ideal.span {toPair H A B}` — and in
   particular is `≥ 0` (so the `ℤ`-valued `ordAt` is secretly an `ℕ`-count), since
   `intValuation_le_one` bounds it above by `1` in `WithZero (Multiplicative ℤ)`.

2. (§4.2, `sorry`, **the genuinely hard step**) `Module.finrank k (CoordinateRing H ⧸
   Ideal.span {toPair H A B})` equals `∑ P ∈ S, (ordAt P A B).toNat`. This needs: (a) CRT for
   Dedekind domains (`IsDedekindDomain.quotientEquivPiOfFinsetProdEq` or similar) to split the
   quotient by the factored ideal into a product over `S` of `CoordinateRing H ⧸ 𝔪_P ^ nP`
   pieces, and (b) for each such piece, `finrank k (CoordinateRing H ⧸ 𝔪_P ^ n) = n` (uses
   §4.3's residue-field-is-`k` fact, plus the standard associated-graded computation
   `𝔪^i / 𝔪^(i+1) ≅ 𝔪^0/𝔪^1` as `R/𝔪`-modules for a DVR-local Dedekind domain).

3. (§4.3, `sorry`'d — plausible/mechanical) The residue field `CoordinateRing H ⧸ pointIdeal P`
   is `k`-isomorphic to `k`
   itself — hence 1-dimensional — via `evalAtPoint P`'s surjectivity and the first isomorphism
   theorem.

4. (§4.4, `sorry`, **the other genuinely hard step**) `Module.finrank k (CoordinateRing H ⧸
   Ideal.span {toPair H A B}) = (pairNorm H A B).natDegree`. This is a concrete linear-algebra
   fact, *not* Dedekind-domain norm theory: `CoordinateRing H` is `k[X]`-free of rank 2 with
   basis `{1, y}` (`toPair_surjective` + `toPair`'s injectivity elsewhere in this file), so
   "multiplication by `g := toPair H A B`" is a `k[X]`-linear endomorphism of `k[X]²`; its
   matrix in the `{1,y}` basis has determinant exactly `pairNorm H A B` (since
   `g * involution H g = algebraMap (pairNorm H A B)` is literally the norm/determinant
   identity for a rank-2 free extension with `ι` as the nontrivial automorphism — matches
   `toPair_mul_involution`). `CoordinateRing H ⧸ (g)` as a `k[X]`-module then has `k[X]`-length
   `= natDegree(det) = natDegree(pairNorm H A B)` by Smith normal form / elementary divisors of
   that matrix over the PID `k[X]`; converting `k[X]`-length to `k`-`finrank` recovers the
   stated equality once matched against `pairNorm H A B`'s own `natDegree` directly (no
   intermediate `k[X]`-length concept needs to actually appear if this is done via a direct
   `k`-basis of `CoordinateRing H ⧸ (g)` built from the division algorithm against `g`, in the
   style of `toPair_surjective`'s "reduce mod `X² - C H.f`" argument, but adapted to reducing
   mod `g` itself — this is the part most likely to need real new infrastructure rather than
   an existing Mathlib lemma). -/

/-- §4.1: `ordAt P A B` (when `toPair H A B ≠ 0` and `pointIdeal P ≠ ⊥`) equals the
`Associates.count` multiplicity of `pointIdeal P` in the factorization of
`Ideal.span {toPair H A B}`, viewed in `ℤ` — in particular it is `≥ 0`. Unfolds `ordAt` and
`IsDedekindDomain.HeightOneSpectrum.intValuation`/`intValuationDef`, whose defining equation
(per the docstring on `intValuationDef`) is literally
`v.intValuationDef r = if r = 0 then 0 else ofAdd (-(Associates.mk v.asIdeal).count
(Associates.mk (span {r})).factors)` — so this should reduce to unfolding that `if` (`r ≠ 0`
here) and computing `WithZero.log` of an `ofAdd (-(n : ℤ))` term. **PLAUSIBLE, not checked
against a live goal state**: the exact accessor name for that defining equation
(`intValuationDef` may unfold directly via `unfold`/`show`, or may need a named simp lemma not
identified here — e.g. something in the `intValuationDef_if_pos`/`_if_neg` family, whose
existence and exact name were not verified) and the exact `WithZero.log`/`ofAdd` simp lemma
needed to cancel the outer `Multiplicative.ofAdd`/`WithZero.log` round-trip were not confirmed.
-/
theorem ordAt_eq_count [IsDedekindDomain (CoordinateRing H)]
    (P : H.Point) (A B : k[X]) (hne : toPair H A B ≠ 0) (h_bot : pointIdeal P ≠ ⊥) :
    ordAt P A B =
      ((Associates.mk (pointHeightOne P h_bot).asIdeal).count
        (Associates.mk (Ideal.span ({toPair H A B} : Set (CoordinateRing H)))).factors : ℤ) := by
  unfold ordAt
  rw [if_neg hne, dif_neg h_bot]
  set n : ℕ := (Associates.mk (pointHeightOne P h_bot).asIdeal).count
    (Associates.mk (Ideal.span ({toPair H A B} : Set (CoordinateRing H)))).factors with hn_def
  -- Goal (after the sign fix to `ordAt`'s definition above):
  -- `-WithZero.log ((pointHeightOne P h_bot).intValuation (toPair H A B)) = (n : ℤ)`.
  -- `intValuation_apply` unfolds `intValuation` to `intValuationDef`; the `r ≠ 0` branch
  -- of `intValuationDef` (`intValuationDef_if_neg`, confirmed to exist with exactly this
  -- name and shape) then gives `intValuationDef (toPair H A B)
  --   = ↑(Multiplicative.ofAdd (-(n:ℤ)))`, which is `WithZero.exp (-(n:ℤ))` by definition
  -- of `WithZero.exp a := ↑(Multiplicative.ofAdd a)`.
  have hval : (pointHeightOne P h_bot).intValuation (toPair H A B) =
      WithZero.exp (-(n : ℤ)) := by
    rw [IsDedekindDomain.HeightOneSpectrum.intValuation_apply,
        IsDedekindDomain.HeightOneSpectrum.intValuationDef_if_neg _ hne]
    try rfl
  rw [hval]
  -- Derive `WithZero.log (WithZero.exp m) = m` from the *confirmed* `WithZero.exp_log`
  -- (exp ∘ log = id on nonzero elements) plus `WithZero.exp_injective`, rather than
  -- relying on an unconfirmed separate `log_exp` lemma name: `exp_log` applied to
  -- `exp m ≠ 0` gives `exp (log (exp m)) = exp m`, and injectivity of `exp` cancels
  -- the outer `exp` on both sides, leaving `log (exp m) = m` directly. This step was
  -- confirmed by direct proof (not guessed) in the prior session, and is what surfaced
  -- the sign convention fix now applied to `ordAt`'s definition above: `WithZero.log`
  -- alone computes `-(n:ℤ)`, the "absolute value" valuation-theoretic sign, so `ordAt`'s
  -- definition negates it to recover the "order of vanishing" convention this file's
  -- naming assumes throughout (`ordAt_nonneg`, §4.2/§4.4's `.toNat`, etc.).
  have hlog_exp : WithZero.log (WithZero.exp (-(n : ℤ))) = -(n : ℤ) :=
    WithZero.exp_injective (WithZero.exp_log WithZero.exp_ne_zero)
  rw [hlog_exp, neg_neg]

/-- §4.1 corollary: every `ordAt P A B` (in the nonzero, non-`⊥`-ideal case) is `≥ 0` — an
`Associates.count` is a natural number cast into `ℤ`. -/
theorem ordAt_nonneg [IsDedekindDomain (CoordinateRing H)]
    (P : H.Point) (A B : k[X]) (hne : toPair H A B ≠ 0) (h_bot : pointIdeal P ≠ ⊥) :
    0 ≤ ordAt P A B := by
  rw [ordAt_eq_count P A B hne h_bot]
  exact Int.natCast_nonneg _

/-- `evalAtPoint P`, repackaged as a `k`-algebra map. `evalAtPoint P` is built as a
plain `RingHom` (via `AdjoinRoot.lift`), but `CoordinateRing H` carries a `k`-algebra
structure via `Algebra.compHom` composing `algebraMap k[X] (CoordinateRing H)` with
`algebraMap k k[X]` (see the instance in `HyperellipticFunctionField.lean`), and
`evalAtPoint P` fixes that composed `k`-action. The `commutes'` proof mirrors
`evalAtPoint_surjective`'s computation above verbatim: both reduce
`evalAtPoint P (AdjoinRoot.mk _ (C (C c)))` to `c` by `simp` after unfolding to
`Polynomial.eval₂`, since `algebraMap k[X] (CoordinateRing H) (algebraMap k k[X] c)`
is definitionally `AdjoinRoot.mk (X² - C H.f) (C (C c))` (the same `rfl`-unfolding
`toPair_eq_zero_iff` above relies on for `algebraMap k[X] (CoordinateRing H) A`). -/
def evalAtPointAlg (P : H.Point) : CoordinateRing H →ₐ[k] k where
  toFun := evalAtPoint P
  map_one' := map_one _
  map_mul' := map_mul _
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' := fun c => by
    change evalAtPoint P (algebraMap k (CoordinateRing H) c) = algebraMap k k c
    have hlhs : algebraMap k (CoordinateRing H) c =
        AdjoinRoot.mk ((X : (k[X])[X]) ^ 2 - C H.f) (C (C c)) := rfl
    rw [hlhs]
    change Polynomial.eval₂ (Polynomial.evalRingHom P.val.1) P.val.2 (C (C c)) = c
    simp

/-- `evalAtPointAlg P` is surjective (it agrees with `evalAtPoint P` as a function;
stated via `change` + the `RingHom`-level lemma rather than direct term-mode reuse, in
case the `AlgHom`/`RingHom` `FunLike` coercions for `Function.Surjective`'s target
aren't syntactically identical). -/
theorem evalAtPointAlg_surjective (P : H.Point) :
    Function.Surjective (evalAtPointAlg P) := by
  change Function.Surjective (evalAtPoint P)
  exact evalAtPoint_surjective P

/-- `pointIdeal P` is the kernel of `evalAtPointAlg P`'s underlying ring hom (same
underlying function as `evalAtPoint P`, so same kernel by definition). -/
theorem pointIdeal_eq_ker_evalAtPointAlg (P : H.Point) :
    pointIdeal P = RingHom.ker (evalAtPointAlg P).toRingHom := rfl

/-- §4.3: the residue field `CoordinateRing H ⧸ pointIdeal P` is `k`-algebra-isomorphic to `k`
itself, via `evalAtPointAlg P` (the `k`-algebra repackaging of `evalAtPoint P` above) and
`Ideal.quotientKerAlgEquivOfSurjective` (Mathlib's first isomorphism theorem for algebras,
surjective case), hence `1`-dimensional over `k` via `LinearEquiv.finrank_eq` and
`Module.finrank_self`. -/
theorem finrank_quotient_pointIdeal (P : H.Point) :
    Module.finrank k (CoordinateRing H ⧸ pointIdeal P) = 1 := by
  have hequiv : (CoordinateRing H ⧸ RingHom.ker (evalAtPointAlg P).toRingHom) ≃ₐ[k] k :=
    Ideal.quotientKerAlgEquivOfSurjective (evalAtPointAlg_surjective P)
  rw [pointIdeal_eq_ker_evalAtPointAlg]
  rw [LinearEquiv.finrank_eq hequiv.toLinearEquiv]
  exact Module.finrank_self k

/-! ### §4.2 scaffolding: CRT + associated-graded dimension count

**UNVERIFIED — drafted without a Lean toolchain, same caveat as the §4.4 scaffold below:
lemma names are best-effort guesses, not confirmed lookups.**

Plan, decomposed so each piece is independently checkable/replaceable:
1. `span_toPair_eq_prod_pointIdeal_pow`: `Ideal.span {toPair H A B} = ∏ P ∈ S, pointIdeal P ^
   (ordAt P A B).toNat`, as ideals of `CoordinateRing H`. This is where `hsupp` (every point
   outside `S` has multiplicity `0`) and unique factorization of ideals in a Dedekind domain
   actually get used — it says `S` is exactly (a superset closed under zero-multiplicity of)
   the support of the factorization of `(g)`. Candidate route:
   `UniqueFactorizationMonoid`/`Ideal.finprod_heightOneSpectrum_factorization`-style lemmas,
   or building it directly from `Associates.factors` and `ordAt_eq_count` (§4.1) applied
   pointwise. Not looked up against a live Mathlib.
2. `pointIdeal_pairwise_coprime`: for `P ≠ Q` in `S`, `pointIdeal P ^ nP` and `pointIdeal Q ^
   nQ` are coprime ideals (`IsCoprime`/`Ideal.IsCoprime` — exact name and `^`-compatibility
   lemma, e.g. `IsCoprime.pow` or `Ideal.isCoprime_iff_sup_eq` composed with
   `Ideal.IsMaximal`-distinctness of `pointIdeal P` vs `pointIdeal Q`, not confirmed).
3. `crt_equiv`: **CRT proper** — `CoordinateRing H ⧸ ∏ P ∈ S, pointIdeal P ^ nP ≃+*
   Π P ∈ S, CoordinateRing H ⧸ pointIdeal P ^ nP` (candidate:
   `Ideal.quotientInfRingEquivPiQuotient` for pairwise coprime ideals, composed with
   `Ideal.IsCoprime`-implies-`inf = prod` to match the `∏` in step 1 — the exact Mathlib
   CRT entry point for a *finite family indexed by a `Finset`* rather than two ideals at a
   time was not confirmed; may need `Finset.induction` to build up from the pairwise case).
4. `finrank_quotient_pointIdeal_pow`: for a single point `P` with `nP := (ordAt P A B).toNat`,
   `finrank k (CoordinateRing H ⧸ pointIdeal P ^ nP) = nP`. The genuinely mathematical
   sub-step: filtration `pointIdeal P ^ i` for `i = 0, …, nP` gives short exact sequences
   `0 → 𝔪^i/𝔪^{i+1} → R/𝔪^{i+1} → R/𝔪^i → 0`, and `𝔪^i/𝔪^{i+1} ≅ R/𝔪` as `R/𝔪`-modules
   (hence `k`-modules, 1-dimensional by §4.3's `finrank_quotient_pointIdeal`) for a DVR-local
   Dedekind domain — `𝔪` principal locally, so `𝔪^i/𝔪^{i+1} ≅ 𝔪^i ⊗ (R/𝔪)`-type argument, or
   directly `Ideal.factorPow`/`Ideal.quotientEquivQuotientMulSpanSingleton`-style API. Proved
   by induction on `nP` using `Module.finrank`-additivity across the exact sequence
   (`LinearMap.finrank_range_add_finrank_ker` / a submodule-quotient dimension-addition
   lemma — exact name not confirmed). This is the step most likely to actually need new
   infrastructure rather than a single citation.
5. Assembly: chain 1→3 for the ring iso, take `k`-finrank of both sides (finrank of a finite
   product of `k`-modules is the sum of finranks — `Module.finrank_pi`-style lemma, exact
   name not confirmed for a `Π P ∈ S, _` dependent-on-`Finset` product rather than a plain
   `Fin n →`-indexed one), then apply step 4 to each factor and match against
   `(ordAt P A B).toNat` via `ordAt_nonneg`/`ordAt_eq_count` from §4.1.
-/

/-- Step 1: the ideal `Ideal.span {toPair H A B}` factors as the product, over `P ∈ S`, of
`pointIdeal P` raised to its local multiplicity `(ordAt P A B).toNat`. **UNVERIFIED, no
citation confirmed** — see the module comment above §4.2, item 1. -/
theorem span_toPair_eq_prod_pointIdeal_pow [IsDedekindDomain (CoordinateRing H)]
    (S : Finset H.Point) (A B : k[X]) (hAB : ¬(A = 0 ∧ B = 0))
    (hsupp : ∀ P, P ∉ S → ordAt P A B = 0) :
    Ideal.span ({toPair H A B} : Set (CoordinateRing H)) =
      ∏ P ∈ S, pointIdeal P ^ (ordAt P A B).toNat := by
  sorry

/-- Distinct affine points give distinct point-ideals. Proved via the coordinate functions:
`X - C P.X ∈ pointIdeal P` (since `evalAtPoint P` sends `X ↦ P.X`), so if `pointIdeal P =
pointIdeal Q` then evaluating at `Q` forces `Q.X = P.X`; symmetrically `Q.Y = P.Y`, so
`P = Q` (as a subtype of `k × k`), contradicting `hne`. -/
theorem pointIdeal_ne_of_ne (P Q : H.Point) (hne : P ≠ Q) :
    pointIdeal P ≠ pointIdeal Q := by
  intro heq
  apply hne
  have hXmem : (algebraMap k[X] (CoordinateRing H) X - algebraMap k[X] (CoordinateRing H) (C P.X))
      ∈ pointIdeal P := by
    change evalAtPoint P (algebraMap k[X] (CoordinateRing H) X -
      algebraMap k[X] (CoordinateRing H) (C P.X)) = 0
    have hXeval : evalAtPoint P (algebraMap k[X] (CoordinateRing H) X) = P.X := by
      change Polynomial.eval₂ (Polynomial.evalRingHom P.val.1) P.val.2 (C X) = P.X
      simp [Point.X]
    have hCeval : evalAtPoint P (algebraMap k[X] (CoordinateRing H) (C P.X)) = P.X := by
      change Polynomial.eval₂ (Polynomial.evalRingHom P.val.1) P.val.2 (C (C P.X)) = P.X
      simp
    rw [map_sub, hXeval, hCeval, sub_self]
  rw [heq] at hXmem
  have hQX : evalAtPoint Q (algebraMap k[X] (CoordinateRing H) X -
      algebraMap k[X] (CoordinateRing H) (C P.X)) = 0 := hXmem
  have hXevalQ : evalAtPoint Q (algebraMap k[X] (CoordinateRing H) X) = Q.X := by
    change Polynomial.eval₂ (Polynomial.evalRingHom Q.val.1) Q.val.2 (C X) = Q.X
    simp [Point.X]
  have hCevalQ : evalAtPoint Q (algebraMap k[X] (CoordinateRing H) (C P.X)) = P.X := by
    change Polynomial.eval₂ (Polynomial.evalRingHom Q.val.1) Q.val.2 (C (C P.X)) = P.X
    simp
  rw [map_sub, hXevalQ, hCevalQ, sub_eq_zero] at hQX
  have hYmem : (algebraMap k[X] (CoordinateRing H) (C P.Y) - y H) ∈ pointIdeal P := by
    change evalAtPoint P (algebraMap k[X] (CoordinateRing H) (C P.Y) - y H) = 0
    have hCYeval : evalAtPoint P (algebraMap k[X] (CoordinateRing H) (C P.Y)) = P.Y := by
      change Polynomial.eval₂ (Polynomial.evalRingHom P.val.1) P.val.2 (C (C P.Y)) = P.Y
      simp
    have hyeval : evalAtPoint P (y H) = P.Y := by
      change Polynomial.eval₂ (Polynomial.evalRingHom P.val.1) P.val.2 X = P.Y
      simp [Point.Y]
    rw [map_sub, hCYeval, hyeval, sub_self]
  rw [heq] at hYmem
  have hQY : evalAtPoint Q (algebraMap k[X] (CoordinateRing H) (C P.Y) - y H) = 0 := hYmem
  have hCYevalQ : evalAtPoint Q (algebraMap k[X] (CoordinateRing H) (C P.Y)) = P.Y := by
    change Polynomial.eval₂ (Polynomial.evalRingHom Q.val.1) Q.val.2 (C (C P.Y)) = P.Y
    simp
  have hyevalQ : evalAtPoint Q (y H) = Q.Y := by
    change Polynomial.eval₂ (Polynomial.evalRingHom Q.val.1) Q.val.2 X = Q.Y
    simp [Point.Y]
  rw [map_sub, hCYevalQ, hyevalQ, sub_eq_zero] at hQY
  exact Subtype.ext (Prod.ext hQX.symm hQY)

/-- Step 2: distinct points give coprime (prime-power) ideals — needed to invoke CRT in
step 3. Built from `pointIdeal_ne_of_ne` (distinct points ⟹ distinct maximal ideals) plus
the standard fact that two distinct maximal ideals are coprime, then `IsCoprime.pow` to lift
to prime powers. **UNVERIFIED naming**: the "two distinct maximal ideals are coprime" step
is written via `Ideal.isCoprime_iff_sup_eq` + `Ideal.IsMaximal`-distinctness forcing
`M ⊔ N = ⊤` (a maximal ideal `M ⊊ M ⊔ N` forces `M ⊔ N = ⊤` since `M` has no proper
superideal but `⊤`), but the exact Mathlib lemma name for "two distinct maximal ideals
generate the whole ring" (candidates: `Ideal.IsMaximal.coprime_of_ne`,
`Ideal.sup_eq_top_of_isMaximal_of_ne`) was not confirmed — the proof below spells out the
`sup`-is-`⊤` argument by hand via `Ideal.IsMaximal.eq_of_le` instead of citing a single named
lemma, so it should be more robust to that uncertainty even if slightly verbose.
**UNVERIFIED**: `Ideal.IsMaximal.eq_of_le`'s exact argument order/signature (does it take
`(I.IsMaximal) (hne_top : J ≠ ⊤) (hle : I ≤ J) : I = J`, or a different order/hypothesis
shape?) was not checked against a live goal — this is the one genuinely uncertain piece of
the `hsup` proof below; everything else in this theorem (the `pointIdeal_ne_of_ne` call,
`Ideal.isCoprime_iff_sup_eq`, `IsCoprime.pow`) is a more standard/confident guess. -/
theorem pointIdeal_pow_pairwise_coprime [IsDedekindDomain (CoordinateRing H)]
    (S : Finset H.Point) (A B : k[X]) :
    ∀ P ∈ S, ∀ Q ∈ S, P ≠ Q →
      IsCoprime (pointIdeal P ^ (ordAt P A B).toNat) (pointIdeal Q ^ (ordAt Q A B).toNat) := by
  intro P _ Q _ hPQ
  have hne : pointIdeal P ≠ pointIdeal Q := pointIdeal_ne_of_ne P Q hPQ
  have hsup : pointIdeal P ⊔ pointIdeal Q = ⊤ := by
    by_contra hlt
    have hle : pointIdeal P ≤ pointIdeal P ⊔ pointIdeal Q := le_sup_left
    have hne_top : pointIdeal P ⊔ pointIdeal Q ≠ ⊤ := hlt
    have heq1 : pointIdeal P = pointIdeal P ⊔ pointIdeal Q :=
      (pointIdeal_isMaximal P).eq_of_le hne_top hle
    have hle2 : pointIdeal Q ≤ pointIdeal P ⊔ pointIdeal Q := le_sup_right
    rw [← heq1] at hle2
    have heq2 : pointIdeal Q = pointIdeal P :=
      (pointIdeal_isMaximal Q).eq_of_le (pointIdeal_isMaximal P).ne_top hle2
    exact hne heq2.symm
  have hcoprime : IsCoprime (pointIdeal P) (pointIdeal Q) :=
    Ideal.isCoprime_iff_sup_eq.mpr hsup
  exact hcoprime.pow

/-- Step 3: the Chinese Remainder Theorem, specialized to this factored ideal — the quotient
by the product ideal is ring-isomorphic to the product of the individual prime-power
quotients. **UNVERIFIED, no citation confirmed** — candidate is
`Ideal.quotientInfRingEquivPiQuotient` (for pairwise coprime ideals, `Finset`-indexed) or an
iterated two-ideal CRT built up by `Finset.induction`; not looked up against a live Mathlib. -/
noncomputable def crt_equiv_prod_pointIdeal_pow [IsDedekindDomain (CoordinateRing H)]
    (S : Finset H.Point) (A B : k[X]) :
    (CoordinateRing H ⧸ ∏ P ∈ S, pointIdeal P ^ (ordAt P A B).toNat) ≃+*
      (Π P : S, CoordinateRing H ⧸ pointIdeal P.1 ^ (ordAt P.1 A B).toNat) := by
  have hcoprime : ∀ P ∈ S, ∀ Q ∈ S, P ≠ Q →
      IsCoprime (pointIdeal P ^ (ordAt P A B).toNat) (pointIdeal Q ^ (ordAt Q A B).toNat) :=
    pointIdeal_pow_pairwise_coprime S A B
  let I : S → Ideal (CoordinateRing H) := fun P => pointIdeal P.1 ^ (ordAt P.1 A B).toNat
  have h_pairwise : ∀ (P Q : S), P ≠ Q → IsCoprime (I P) (I Q) := by
    intro ⟨P, hP⟩ ⟨Q, hQ⟩ hneq
    exact hcoprime P hP Q hQ (fun h => hneq (Subtype.ext h))
  have heq : (∏ P ∈ S, pointIdeal P ^ (ordAt P A B).toNat) = ⨅ P : S, I P := by
    sorry
  rw [heq]
  exact Ideal.quotientInfRingEquivPiQuotient I h_pairwise


/-- Step 4: the `k`-dimension of a single prime-power quotient `R ⧸ 𝔪_P^{n}` equals `n`.
The genuinely mathematical content of §4.2 — the associated-graded computation
`𝔪^i/𝔪^{i+1} ≅ R/𝔪` for a Dedekind domain localized at a height-one prime, combined with
§4.3's `finrank_quotient_pointIdeal` (each graded piece is `1`-dimensional over `k`) and
induction on `n` via dimension-additivity across the filtration's exact sequences.
**UNVERIFIED, no citation confirmed** — this is the sub-step most likely to need genuinely
new infrastructure (an explicit filtration/associated-graded argument) rather than a single
Mathlib lemma; see the module comment above §4.2, item 4. -/
theorem finrank_quotient_pointIdeal_pow [IsDedekindDomain (CoordinateRing H)]
    (P : H.Point) (n : ℕ) :
    Module.finrank k (CoordinateRing H ⧸ pointIdeal P ^ n) = n := by
  sorry

/-- §4.2 assembly: the `k`-dimension of `CoordinateRing H ⧸ Ideal.span {toPair H A B}` is the
sum, over `P ∈ S`, of the local multiplicities `(ordAt P A B).toNat`. **The genuinely hard
step** — needs CRT for the factored ideal (steps 1–3 above) plus the associated-graded
dimension count for prime-power quotients (step 4 above). See the §4.2 module comment for the
full decomposition; none of steps 1–4 have been checked against a live goal, so treat this
assembly (which chains them via `Module.finrank`-of-a-ring-iso and finrank-of-a-finite-product)
as unverified too — in particular the exact lemma taking "`R ≃+* Π i, Sᵢ`" to "`finrank k R =
∑ i, finrank k (Sᵢ)`" was not looked up. -/
theorem finrank_quotient_span_eq_sum_ordAt [IsDedekindDomain (CoordinateRing H)]
    (S : Finset H.Point) (A B : k[X]) (hAB : ¬(A = 0 ∧ B = 0))
    (hsupp : ∀ P, P ∉ S → ordAt P A B = 0) :
    Module.finrank k (CoordinateRing H ⧸ Ideal.span ({toPair H A B} : Set (CoordinateRing H))) =
      ∑ P ∈ S, (ordAt P A B).toNat := by
  rw [span_toPair_eq_prod_pointIdeal_pow S A B hAB hsupp]
  have hcrt := crt_equiv_prod_pointIdeal_pow S A B
  -- Remaining step: `finrank k` of `crt_equiv_prod_pointIdeal_pow`'s ring iso, then
  -- `finrank` of the `Finset`-indexed product `Π P : S, _` equals `∑ P ∈ S, finrank (_)`,
  -- then apply `finrank_quotient_pointIdeal_pow` to each factor and reindex the `Subtype`
  -- sum `∑ P : S, _` back to `∑ P ∈ S, _`. **UNVERIFIED** — not checked against a live goal.
  sorry

/-! ### §4.4 scaffolding: `CoordinateRing H` as a rank-2 free `k[X]`-module

**UNVERIFIED — drafted without a Lean toolchain available. Every lemma name below is a
best-effort guess at Mathlib's current API shape, not a confirmed lookup. Expect several
wrong names, wrong argument orders, or missing `simp`/`convert` glue. This is a worked plan
to fix up against a live REPL, not a finished proof — matching the file's own stated policy
of flagging unverified steps explicitly rather than passing them off as solid.**

Plan:
1. `toPairLin`/`toPairEquiv`: package `toPair H` as a `k[X]`-linear equivalence
   `k[X] × k[X] ≃ₗ[k[X]] CoordinateRing H`, using `toPair_surjective` (surjectivity, from
   `PrincipalDivisorsIntegralClosure.lean`) and `toPair_eq_zero_iff` (injectivity, via the
   kernel — this is exactly `toPair_injective`'s argument, but unconditional since
   `toPair_eq_zero_iff` itself carries no `natDegree = 5` hypothesis).
2. Transport "multiply by `g := toPair H A B`" across that equivalence to a `k[X]`-linear
   endomorphism of `k[X] × k[X]`; identify its matrix (in the standard basis of
   `k[X] × k[X]`, which corresponds to the `{1, y}`-basis of `CoordinateRing H` under
   `toPairEquiv`) as `!![A, B * H.f; B, A]`. This is `(A + By)(a + by) = (Aa + Bbf) + (Ab +
   Ba)y` via `y² = f`, i.e. `toPair_mul_involution`'s underlying computation with `(a, b)`
   playing the role of a second, independent pair rather than `(A, -B)`.
3. `Ideal.span {g}` (as a `k[X]`-submodule of `CoordinateRing H`) corresponds, under
   `toPairEquiv`, to the range of that matrix's linear map on `k[X] × k[X]`.
4. So `CoordinateRing H ⧸ Ideal.span {g} ≃ₗ[k[X]] (k[X] × k[X]) ⧸ range(mul-by-M)` — and in
   particular the two sides have equal `k`-finrank.
5. The genuinely new fact, isolated as
   `finrank_quotient_range_mulByToPairLin_eq_natDegree_pairNorm` below: for `A B : k[X]`
   with `pairNorm H A B ≠ 0`, `finrank k ((k[X] × k[X]) ⧸ range (mulByToPairLin H A B)) =
   (pairNorm H A B).natDegree`. (Note: `mulByToPairLin` is written directly as a `Prod`-level
   linear map — `(a,b) ↦ (Aa + Bfb, Ba + Ab)` — rather than via `Matrix.toLin'` on
   `Fin 2 → k[X]`, to avoid needing the exact name of the `k[X]×k[X] ≃ₗ (Fin 2 → k[X])`
   conversion lemma. Its "determinant" in the classical 2×2 sense, `A*A - (B*H.f)*B`, is
   literally `pairNorm H A B` — this is where that quantity re-enters after step 2 packaged
   it into the endomorphism's coefficients.) Candidate routes, *neither confirmed against a
   live Mathlib*:
   - **Smith normal form**: `Mathlib.LinearAlgebra.Matrix.SmithNormalForm` gives unit
     matrices `L, R` and diagonal `D` with `!![A, B*H.f; B, A] = L * D * R` over the PID
     `k[X]`; the cokernel is then (up to the units, which don't change the cokernel's iso
     type) the direct sum `⨁ i, k[X] ⧸ (D i i)`, each summand's `k`-finrank equal to
     `(D i i).natDegree` by the *same* argument as `AdjoinRoot.powerBasis`-style reasoning
     (`k[X] ⧸ (p) ≅ AdjoinRoot p` has a power basis of size `p.natDegree` when `p ≠ 0`), and
     `∑ (D i i).natDegree = (pairNorm H A B).natDegree` since the product of the diagonal is,
     up to a unit of `k[X]`, the determinant `pairNorm H A B`.
   - **Direct division-algorithm basis** (more self-contained, more new content to write):
     construct an explicit `k`-basis of `CoordinateRing H ⧸ (g)` directly by "reducing mod
     `g`" — using `g * ḡ = algebraMap (pairNorm H A B)` (`toPair_mul_involution`) to turn
     "divide by `g`" into "divide by `pairNorm H A B` after multiplying by `ḡ`", mirroring how
     one computes with quadratic-field norms by rationalizing, in the style of
     `toPair_surjective_local`'s `%ₘ` reduction against the monic quadratic
     `X² - C H.f`. This avoids Smith normal form entirely but needs its own care
     (multiplying by `ḡ` is only reversible when `g` is a non-zero-divisor, which holds once
     `CoordinateRing H` is a domain).
   Given the uncertainty, `finrank_quotient_range_mulByToPairLin_eq_natDegree_pairNorm` is
   left as its own named `sorry` rather than guessed at length; whichever route works, only
   that one lemma needs to change, keeping the rest of this chain (steps 1–4, and the final
   assembly) independent of which proof strategy for step 5 is used.
-/

/-- Step 1: `toPair H` packaged as a `k[X]`-linear map `k[X] × k[X] →ₗ[k[X]] CoordinateRing H`.
**UNVERIFIED**: the `map_smul'` proof's final `ring` call assumes `Algebra.smul_def` rewrites
the *whole* RHS `c • (toPair H A B)` into `algebraMap c * toPair H A B` in one step; if
`Algebra.smul_def` only fires on a sub-term, this needs an extra `rw`/`simp only` before
`ring` closes it. Not checked against a live goal. -/
def toPairLin (H : HyperellipticPolynomial k) : (k[X] × k[X]) →ₗ[k[X]] CoordinateRing H where
  toFun p := toPair H p.1 p.2
  map_add' p q := by
    change toPair H (p.1 + q.1) (p.2 + q.2) = toPair H p.1 p.2 + toPair H q.1 q.2
    unfold toPair
    simp only [map_add]
    ring
  map_smul' c p := by
    change toPair H (c * p.1) (c * p.2) = c • toPair H p.1 p.2
    unfold toPair
    rw [Algebra.smul_def]
    simp only [map_mul]
    ring

/-- Local copy of `toPair_surjective` (originally in `PrincipalDivisorsIntegralClosure.lean`,
which *imports* this file — so it can't be cited from here without an import cycle). Inlined
verbatim rather than re-derived, since that file's version is not itself `sorry`'d. If the two
files are ever merged or reordered, this copy should be deleted in favor of the original. -/
theorem toPair_surjective_local (H : HyperellipticPolynomial k) (z : CoordinateRing H) :
    ∃ A B : k[X], z = toPair H A B := by
  have hmonic : (X ^ 2 - C H.f : (k[X])[X]).Monic :=
    Polynomial.monic_X_pow_sub_C H.f two_ne_zero
  induction z using AdjoinRoot.induction_on with
  | ih p =>
    have hmod : AdjoinRoot.mk (X ^ 2 - C H.f) p =
        AdjoinRoot.mk (X ^ 2 - C H.f) (p %ₘ (X ^ 2 - C H.f)) := by
      have hdvd : (X ^ 2 - C H.f : (k[X])[X]) ∣ (p %ₘ (X ^ 2 - C H.f)) - p :=
        Polynomial.dvd_modByMonic_sub p (X ^ 2 - C H.f)
      have hker : AdjoinRoot.mk (X ^ 2 - C H.f) ((p %ₘ (X ^ 2 - C H.f)) - p) = 0 :=
        AdjoinRoot.mk_eq_zero.mpr hdvd
      rw [map_sub, sub_eq_zero] at hker
      exact hker.symm
    set r := p %ₘ (X ^ 2 - C H.f) with hr_def
    have hnd2 : (X ^ 2 - C H.f : (k[X])[X]).natDegree = 2 := by compute_degree!
    have hrdeg : r.natDegree < 2 := by
      have hne1 : (X ^ 2 - C H.f : (k[X])[X]) ≠ 1 := by
        intro heq1
        rw [heq1, Polynomial.natDegree_one] at hnd2
        exact absurd hnd2 (by norm_num)
      have hlt := Polynomial.natDegree_modByMonic_lt p hmonic hne1
      rw [hnd2] at hlt
      rw [hr_def]
      exact hlt
    have hr_eq : r = C (r.coeff 0) + C (r.coeff 1) * X := by
      ext n
      match n with
      | 0 => simp
      | 1 => simp
      | (m + 2) =>
        have hc0 : r.coeff (m + 2) = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
        simp [hc0]
    refine ⟨r.coeff 0, r.coeff 1, ?_⟩
    change AdjoinRoot.mk (X ^ 2 - C H.f) p = toPair H (r.coeff 0) (r.coeff 1)
    have hmk : ∀ A B : k[X], AdjoinRoot.mk (X ^ 2 - C H.f) (C A + C B * X) = toPair H A B := by
      intro A B
      unfold toPair HyperellipticPolynomial.y
      rw [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
      rfl
    rw [hmod]
    conv_lhs => rw [hr_eq]
    exact hmk (r.coeff 0) (r.coeff 1)

/-- Step 1, continued: `toPairLin H` is bijective — surjectivity is
`toPair_surjective_local`, injectivity is `toPair_eq_zero_iff` applied to the difference of
two preimages (mirroring `toPair_injective`'s proof, but unconditional since
`toPair_eq_zero_iff` carries no `natDegree = 5` hypothesis). -/
theorem toPairLin_bijective (H : HyperellipticPolynomial k) :
    Function.Bijective (toPairLin H) := by
  constructor
  · intro p q hpq
    have hsub : toPair H (p.1 - q.1) (p.2 - q.2) = 0 := by
      have hrw : toPair H (p.1 - q.1) (p.2 - q.2) = toPairLin H p - toPairLin H q := by
        change toPair H (p.1 - q.1) (p.2 - q.2) = toPair H p.1 p.2 - toPair H q.1 q.2
        unfold toPair
        rw [map_sub, map_sub]
        ring
      rw [hrw, hpq, sub_self]
    obtain ⟨hA, hB⟩ := (toPair_eq_zero_iff H (p.1 - q.1) (p.2 - q.2)).mp hsub
    exact Prod.ext (sub_eq_zero.mp hA) (sub_eq_zero.mp hB)
  · intro z
    obtain ⟨A, B, hz⟩ := toPair_surjective_local H z
    exact ⟨(A, B), hz.symm⟩

/-- Step 1, packaged as an equivalence: `k[X] × k[X]` and `CoordinateRing H` are
isomorphic as `k[X]`-modules, via `toPair`. -/
noncomputable def toPairEquiv (H : HyperellipticPolynomial k) :
    (k[X] × k[X]) ≃ₗ[k[X]] CoordinateRing H :=
  LinearEquiv.ofBijective (toPairLin H) (toPairLin_bijective H)

/-- The `k[X]`-linear endomorphism of `k[X] × k[X]` corresponding, under `toPairEquiv`, to
multiplication by `g := toPair H A B` — i.e. the "matrix `!![A, B*H.f; B, A]`" from the
module comment above, written out directly on `Prod` instead of routing through
`Matrix`/`Fin 2 → k[X]` (avoiding needing to name the `k[X] × k[X] ≃ₗ (Fin 2 → k[X])`
conversion lemma, whose exact Mathlib name wasn't confirmed). Entrywise, this is
`(a, b) ↦ (A*a + B*H.f*b, B*a + A*b)`, matching `(A + By)(a + by) = (Aa + Bbf) + (Ab + Ba)y`
via `y² = f`. -/
def mulByToPairLin (H : HyperellipticPolynomial k) (A B : k[X]) :
    (k[X] × k[X]) →ₗ[k[X]] (k[X] × k[X]) where
  toFun p := (A * p.1 + B * H.f * p.2, B * p.1 + A * p.2)
  map_add' p q := by
    apply Prod.ext
    · change A * (p.1 + q.1) + B * H.f * (p.2 + q.2) =
        A * p.1 + B * H.f * p.2 + (A * q.1 + B * H.f * q.2)
      ring
    · change B * (p.1 + q.1) + A * (p.2 + q.2) = B * p.1 + A * p.2 + (B * q.1 + A * q.2)
      ring
  map_smul' c p := by
    apply Prod.ext
    · change A * (c * p.1) + B * H.f * (c * p.2) = c * (A * p.1 + B * H.f * p.2)
      ring
    · change B * (c * p.1) + A * (c * p.2) = c * (B * p.1 + A * p.2)
      ring

/-- `mulByToPairLin H A B` really does correspond to multiplication by `toPair H A B`
across `toPairEquiv`, i.e. the following square commutes:
`toPairEquiv (mulByToPairLin p) = toPair H A B * toPairEquiv p`. **UNVERIFIED**: the
`unfold`/`simp`/`ring` combination closing the final equation in `CoordinateRing H` (using
`y_sq_eq` to rewrite `y H ^ 2`) was not checked against a live goal, though the underlying
algebra `(A + By)(a + by) = (Aa + Bbf) + (Ab + Ba)y` is the same identity
`toPair_mul_involution` already establishes (with `(a, b)` in the role that
`toPair_involution` gives `(A, -B)`), so this should be a comparatively safe adaptation of
an existing proof. -/
theorem toPairEquiv_mulByToPairLin (A B : k[X]) (p : k[X] × k[X]) :
    toPairEquiv H (mulByToPairLin H A B p) = toPair H A B * toPairEquiv H p := by
  change toPair H (A * p.1 + B * H.f * p.2) (B * p.1 + A * p.2) = toPair H A B * toPair H p.1 p.2
  unfold toPair
  have hy2 : y H ^ 2 = algebraMap k[X] (CoordinateRing H) H.f := y_sq_eq H
  simp only [map_add, map_mul]
  set a := algebraMap k[X] (CoordinateRing H) A
  set b := algebraMap k[X] (CoordinateRing H) B
  set p1 := algebraMap k[X] (CoordinateRing H) p.1
  set p2 := algebraMap k[X] (CoordinateRing H) p.2
  set f' := algebraMap k[X] (CoordinateRing H) H.f
  set w := y H
  have hexpand : (a + b * w) * (p1 + p2 * w) = a * p1 + b * p2 * w ^ 2 + (a * p2 + b * p1) * w := by
    ring
  rw [hexpand, hy2]
  ring

/-- Step 2/3 combined: transported through `toPairEquiv`, `Ideal.span {toPair H A B}`
(as a `k[X]`-submodule of `CoordinateRing H`) equals the range of `mulByToPairLin H A B`,
mapped forward into `CoordinateRing H`. **UNVERIFIED**: the `Ideal.span {g}` ↦ "range of
mult-by-`g`" identification (`Ideal.span_singleton_eq_range` or built by hand from
`Ideal.mem_span_singleton`) was not checked against a live goal, nor was the
`Submodule.map`/`LinearMap.range` bookkeeping connecting it to
`toPairEquiv_mulByToPairLin` above. -/
theorem span_toPair_eq_range_mulByToPairLin (A B : k[X]) :
    (Ideal.span ({toPair H A B} : Set (CoordinateRing H))).restrictScalars k[X] =
      Submodule.map (toPairEquiv H).toLinearMap (LinearMap.range (mulByToPairLin H A B)) := by
  ext z
  constructor
  · intro hz
    change z ∈ Ideal.span ({toPair H A B} : Set _) at hz
    rw [Ideal.mem_span_singleton] at hz
    rcases hz with ⟨w, rfl⟩
    obtain ⟨q, hq⟩ := (toPairEquiv H).surjective w
    refine Submodule.mem_map.mpr ⟨mulByToPairLin H A B q, LinearMap.mem_range.mpr ⟨q, rfl⟩, ?_⟩
    rw [LinearEquiv.coe_toLinearMap, toPairEquiv_mulByToPairLin, hq]
  · intro hz
    rcases Submodule.mem_map.mp hz with ⟨p, hp, rfl⟩
    rcases LinearMap.mem_range.mp hp with ⟨q, rfl⟩
    change toPairEquiv H (mulByToPairLin H A B q) ∈ Ideal.span ({toPair H A B} : Set _)
    rw [Ideal.mem_span_singleton]
    rw [toPairEquiv_mulByToPairLin]
    exact dvd_mul_right (toPair H A B) (toPairEquiv H q)


/-- Step 5 (the actually-hard fact, isolated so the two candidate proof routes — Smith
normal form, or a direct division-algorithm basis via the norm/rationalization trick — can
be tried independently without touching the rest of the §4.4 chain): for `A B : k[X]` with
`pairNorm H A B ≠ 0`, the `k`-dimension of `(k[X] × k[X]) ⧸ range (mulByToPairLin H A B)`
equals `(pairNorm H A B).natDegree`. **UNVERIFIED, no citation confirmed** — see the module
comment above §4.4 for the two candidate routes (the "determinant" of `mulByToPairLin H A B`
in the Smith-normal-form / classical sense is exactly `A^2 - B^2*H.f = pairNorm H A B`, by
the same computation as `Matrix.det_fin_two` applied to `!![A, B*H.f; B, A]`, so this
statement's `pairNorm H A B` plays the role `M.det` played in the earlier `Matrix`-based
draft of this lemma). -/
theorem finrank_quotient_range_mulByToPairLin_eq_natDegree_pairNorm
    (A B : k[X]) (hne : pairNorm H A B ≠ 0) :
    Module.finrank k ((k[X] × k[X]) ⧸ LinearMap.range (mulByToPairLin H A B)) =
      (pairNorm H A B).natDegree := by
  sorry

/-- `pairNorm H A B ≠ 0` whenever `(A, B) ≠ (0, 0)`, given `CoordinateRing H` is a domain.
Needed as a side fact for §4.4 (`mulByToPairLin H A B` is invertible over the fraction field
of `k[X]` iff its "determinant" `pairNorm H A B` is nonzero, which is what makes the
quotient finite-dimensional in the first place). Proved via
`toPair_mul_involution`: `g * ḡ = algebraMap (pairNorm H A B)`, and `g ≠ 0` (from `hAB` via
`toPair_eq_zero_iff`) forces the product `g * ḡ` nonzero in a domain, hence its preimage
`pairNorm H A B` nonzero since `algebraMap k[X] (CoordinateRing H)` is injective (domain,
nonzero ring). -/
theorem pairNorm_ne_zero_of_ne [IsDomain (CoordinateRing H)] (A B : k[X])
    (hAB : ¬(A = 0 ∧ B = 0)) : pairNorm H A B ≠ 0 := by
  have hg_ne : toPair H A B ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]; exact hAB
  have hgbar_ne : involution H (toPair H A B) ≠ 0 := by
    intro hz
    apply hg_ne
    have hrw : toPair H A B = involution H (involution H (toPair H A B)) := by
      rw [toPair_involution, toPair_involution, neg_neg]
    rw [hrw, hz, map_zero]
  have hprod_ne : toPair H A B * involution H (toPair H A B) ≠ 0 :=
    mul_ne_zero hg_ne hgbar_ne
  rw [toPair_mul_involution] at hprod_ne
  intro hcontra
  apply hprod_ne
  rw [hcontra, map_zero]

/-- §4.4: the `k`-dimension of `CoordinateRing H ⧸ Ideal.span {toPair H A B}` equals
`natDegree (pairNorm H A B)`. **The other genuinely hard step** — a concrete linear-algebra
fact about the rank-2 free `k[X]`-module `CoordinateRing H`, not Dedekind-domain norm theory;
see the §4 module comment above for the full shape.

Takes `[IsDedekindDomain (CoordinateRing H)]` (which implies `[IsDomain (CoordinateRing H)]`)
as an added hypothesis relative to the original stub — needed for `pairNorm_ne_zero_of_ne`
above, and available at this theorem's only call site (`sum_ordAt_eq_natDegree_pairNorm`
already carries the same instance), so this should not break anything downstream.

**UNVERIFIED chain**: the final assembly below is meant to be mechanical *given*
`toPairEquiv`, `span_toPair_eq_range_mulByToPairLin`, and
`finrank_quotient_range_mulByToPairLin_eq_natDegree_pairNorm` — but none of those three (nor
the `LinearEquiv.finrank_eq`/`Submodule.Quotient.equiv`-style chaining used here) have been
checked against a live goal. -/
theorem finrank_quotient_span_eq_natDegree_pairNorm [IsDedekindDomain (CoordinateRing H)]
    (A B : k[X]) (hAB : ¬(A = 0 ∧ B = 0)) :
    Module.finrank k (CoordinateRing H ⧸ Ideal.span ({toPair H A B} : Set (CoordinateRing H))) =
      (pairNorm H A B).natDegree := by
  have hne : pairNorm H A B ≠ 0 := pairNorm_ne_zero_of_ne A B hAB
  have hfinrank := finrank_quotient_range_mulByToPairLin_eq_natDegree_pairNorm (H := H) A B hne
  haveI : IsScalarTower k k[X] (CoordinateRing H) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let e_k : (k[X] × k[X]) ≃ₗ[k] CoordinateRing H :=
    LinearEquiv.restrictScalars k (toPairEquiv H)
  have hmap : Submodule.map e_k.toLinearMap ((LinearMap.range (mulByToPairLin H A B)).restrictScalars k) =
      (Ideal.span ({toPair H A B} : Set (CoordinateRing H))).restrictScalars k := by
    ext z
    constructor
    · intro hz
      rcases Submodule.mem_map.mp hz with ⟨p, hp, rfl⟩
      rcases LinearMap.mem_range.mp hp with ⟨q, rfl⟩
      change toPairEquiv H (mulByToPairLin H A B q) ∈ Ideal.span ({toPair H A B} : Set _)
      rw [Ideal.mem_span_singleton, toPairEquiv_mulByToPairLin]
      exact dvd_mul_right (toPair H A B) (toPairEquiv H q)
    · intro hz
      change z ∈ Ideal.span ({toPair H A B} : Set _) at hz
      rw [Ideal.mem_span_singleton] at hz
      rcases hz with ⟨w, rfl⟩
      obtain ⟨q, hq⟩ := (toPairEquiv H).surjective w
      refine Submodule.mem_map.mpr ⟨mulByToPairLin H A B q, ?_, ?_⟩
      · exact LinearMap.mem_range.mpr ⟨q, rfl⟩
      · change toPairEquiv H (mulByToPairLin H A B q) = toPair H A B * w
        rw [toPairEquiv_mulByToPairLin, hq]
  have e_quot := Submodule.Quotient.equiv
    ((LinearMap.range (mulByToPairLin H A B)).restrictScalars k)
    ((Ideal.span ({toPair H A B} : Set (CoordinateRing H))).restrictScalars k)
    e_k
    hmap
  exact (LinearEquiv.finrank_eq e_quot).symm.trans hfinrank


/-- The norm bridge lemma: the sum of the affine orders of vanishing of $A(x) + B(x)y$
equals the degree of its norm $N(A + By) = A^2 - B^2 f$.

Assembled from §4.1–§4.4 above: `sum_ordAt_eq_natDegree_pairNorm` itself is now pure
bookkeeping (cast `ℕ`-sums to `ℤ`, chain the two `finrank` computations) — the actual
mathematical content lives in `finrank_quotient_span_eq_sum_ordAt` and
`finrank_quotient_span_eq_natDegree_pairNorm`, both still `sorry`'d above. -/
theorem sum_ordAt_eq_natDegree_pairNorm [IsDedekindDomain (CoordinateRing H)]
    (S : Finset H.Point) (A B : k[X]) (hAB : ¬(A = 0 ∧ B = 0))
    (hsupp : ∀ P, P ∉ S → ordAt P A B = 0) :
    (∑ P ∈ S, ordAt P A B) = ((pairNorm H A B).natDegree : ℤ) := by
  have hne : toPair H A B ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact hAB
  have hnonneg : ∀ P ∈ S, 0 ≤ ordAt P A B := by
    intro P _
    by_cases h_bot : pointIdeal P = ⊥
    · simp only [ordAt, if_neg hne, dif_pos h_bot, le_refl]
    · exact ordAt_nonneg P A B hne h_bot
  have hsum_toNat : (∑ P ∈ S, ordAt P A B) = ((∑ P ∈ S, (ordAt P A B).toNat : ℕ) : ℤ) := by
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl (fun P hP => (Int.toNat_of_nonneg (hnonneg P hP)).symm)
  rw [hsum_toNat, ← finrank_quotient_span_eq_sum_ordAt S A B hAB hsupp,
    finrank_quotient_span_eq_natDegree_pairNorm A B hAB]

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
