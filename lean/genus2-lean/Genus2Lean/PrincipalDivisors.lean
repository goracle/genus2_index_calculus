import Mathlib
import Genus2Lean.HyperellipticFunctionField
import Genus2Lean.AffinePoints
import Genus2Lean.DivisorClassGroup
noncomputable section

set_option linter.style.header false

open Polynomial

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

/-! ## §2. The order of `A(x) + B(x)y` at the point at infinity, deg-5 case

Reuses `HyperellipticFunctionField.lean`'s `inLInf` pole-order convention
(`2 · deg A` for the `A`-part, `2 · deg B + 5` for the `B`-part) rather than
re-deriving it, since `RiemannRochSpaceInf` already encodes exactly this
convention as the definition of "bounded pole order at `P∞`" and
`pairNorm_eq_zero_iff`/`two_mul_ne_two_mul_add_five` already establish the parity
split between the two parts is genuine (an `A`-part contribution can never
cancel a `B`-part contribution, since one is always even and the other always
odd) — the fact this file's `ordInf` needs.
-/

/-- The order of vanishing of `A(x) + B(x)y` at the point at infinity (deg-5 case),
as a pole order: `ordInf (A + By) = -max(2 deg A, 2 deg B + 5)` when `A + By ≠ 0` (in
`CoordinateRing H`, equivalently `(A, B) ≠ (0, 0)`), matching `inLInf`'s convention
that this quantity bounded above by `n` characterizes membership in `L(n P∞)`.
Packaged as an `ℤ`-valued function on the pair `(A, B) : k[X] × k[X]` rather than on
`CoordinateRing H` directly, since `toPair` uniqueness of representation (needed to
descend this to a well-defined function of the ring element) is exactly
`pairNorm_eq_zero_iff`'s content and is invoked at the point of use below rather
than baked into the definition. Decidability of the equalities in the `if`s below
is supplied via `Classical.propDecidable` at each site (`haveI := Classical.dec _`)
rather than `open Classical in`, since the latter's line-joining interacted badly
with this project's header linter. -/
def ordInfOfPair (A B : k[X]) : ℤ :=
  haveI := Classical.propDecidable (A = 0 ∧ B = 0)
  haveI := Classical.propDecidable (B = 0)
  if A = 0 ∧ B = 0 then 0
  else - (max (2 * A.natDegree : ℤ) (if B = 0 then 0 else 2 * B.natDegree + 5))

/-- `toPair_injective`'s proof, isolated: `toPair H A B = 0` in `CoordinateRing H`
forces `A = 0 ∧ B = 0`. Proved by unfolding `CoordinateRing H = AdjoinRoot f` (with
`f := X² - C H.f`) down to `AdjoinRoot.mk f (C A + C B * X) = 0`, then
`AdjoinRoot.mk_eq_zero : mk f g = 0 ↔ f ∣ g` reduces this to `f ∣ (C A + C B * X)`.
Since `f` is monic of degree 2, a nonzero dividend of a degree-2 monic divisor must
itself have degree ≥ 2 (`Polynomial.natDegree_le_of_dvd`), but `C A + C B * X` has
degree ≤ 1 whenever it is nonzero — so it must be zero, and equating coefficients of
`C A + C B * X = 0` gives `A = 0 ∧ B = 0` directly (no `pairNorm`, no domain
structure, no `hdeg` hypothesis needed — this holds for any `H`). This is a cleaner
route than the norm/involution approach originally sketched in `toPair_injective`'s
docstring: that route still needs `algebraMap : k[X] → CoordinateRing H` injective
to get from `algebraMap (pairNorm ...) = 0` back down to `pairNorm ... = 0` in
`k[X]`, which is itself unproven (would need `CoordinateRing H` a domain, i.e.
`NonsingularData`) — this lemma avoids that dependency entirely by working with
`AdjoinRoot.mk_eq_zero` directly instead of going through `pairNorm`. -/
theorem toPair_eq_zero_iff (H : HyperellipticPolynomial k) (A B : k[X]) :
    toPair H A B = 0 ↔ A = 0 ∧ B = 0 := by
  constructor
  · intro heq
    -- `heq : toPair H A B = 0` lives in `CoordinateRing H`'s own instances
    -- (`H.instCommRingCoordinateRing` etc., from `HyperellipticFunctionField.lean`).
    -- Those instances are *defeq* to `AdjoinRoot`'s native ones (built via
    -- `inferInstanceAs`) but not *syntactically* identical terms, so `rw`/`unfold`
    -- cannot bridge `CoordinateRing H`-phrased facts to `AdjoinRoot`-phrased
    -- lemmas (`mk_eq_zero`, `mk_C`, `mk_X`, ...) no matter how they're combined —
    -- confirmed the hard way across several failed attempts here. The robust fix:
    -- state `heq' : AdjoinRoot.mk f (C A + C B * X) = 0` as an independent claim
    -- and prove it by `exact heq` under a `show`, relying on the kernel's defeq
    -- check (which sees through `inferInstanceAs`) rather than `rw`'s syntactic
    -- matcher (which doesn't). This is the same idea as before, but applied via
    -- `exact`/kernel typechecking instead of `rw`, since defeq-checking is
    -- exactly the tool that's actually needed here.
    have heq' : AdjoinRoot.mk ((X : (k[X])[X]) ^ 2 - C H.f) (C A + C B * X) = 0 := by
      have : toPair H A B =
          AdjoinRoot.mk ((X : (k[X])[X]) ^ 2 - C H.f) (C A + C B * X) := rfl
      rw [this] at heq
      exact heq
    rw [AdjoinRoot.mk_eq_zero] at heq'
    -- `f := X² - C H.f` is monic of natDegree 2; the dividend `C A + C B * X`
    -- has natDegree ≤ 1, so divisibility forces it to be the zero polynomial.
    -- Degree bookkeeping is via `compute_degree` (Mathlib.Tactic.ComputeDegree)
    -- rather than hand-picked lemma names, since those are exactly the kind of
    -- API names that are easy to get subtly wrong without a live goal state.
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
    -- Equating coefficients of `C A + C B * X = 0` at degrees 0 and 1.
    have hcoeff0 : g.coeff 0 = A := by rw [hg_def]; simp
    have hcoeff1 : g.coeff 1 = B := by rw [hg_def]; simp
    rw [hg_eq_zero] at hcoeff0 hcoeff1
    simp only [coeff_zero] at hcoeff0 hcoeff1
    exact ⟨hcoeff0.symm, hcoeff1.symm⟩
  · rintro ⟨rfl, rfl⟩
    simp [toPair]

/-- `ordInfOfPair` is well-defined on the ring element `A + By`: if `(A₁, B₁)` and
`(A₂, B₂)` give the same coordinate-ring element `toPair H A₁ B₁ = toPair H A₂ B₂`,
then `A₁ = A₂` and `B₁ = B₂`. Follows immediately from `toPair_eq_zero_iff` applied
to the difference, using that `toPair H` is additive in `(A, B)` (both `algebraMap`
and multiplication-by-`y H` are additive) so
`toPair H A₁ B₁ - toPair H A₂ B₂ = toPair H (A₁ - A₂) (B₁ - B₂)`. -/
theorem toPair_injective (H : HyperellipticPolynomial k) (hdeg : H.f.natDegree = 5)
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

/-! ## §3. Affine orders of vanishing via Dedekind-domain machinery — SCOPED OUT THIS SESSION

The affine part of `ord_P(g)` for `P : H.Point` and `g` a nonzero element of the
fraction field of `CoordinateRing H` needs:

1. `CoordinateRing H` is a domain: needs `X ^ 2 - C H.f` irreducible over `k`, which
   needs `H.f` to not be a square in `k[X]` (weaker than but implied by squarefree +
   odd-ish degree considerations) — NOT currently a hypothesis anywhere in
   `HyperellipticPolynomial`, by this project's explicit choice (kept local to this
   file rather than retrofitted onto the shared structure).
2. `CoordinateRing H` is a Dedekind domain: needs `H.f` squarefree (nonsingularity of
   `C`) on top of (1), then a genuine proof that the resulting ring is Noetherian,
   integrally closed, and of Krull dimension 1 — e.g. via exhibiting it as (an open
   subscheme's coordinate ring of) the integral closure of `k[X]` in its fraction
   field, using `IsIntegrallyClosed`/`IsDedekindDomain` instances for integral
   closures of Dedekind domains in finite separable extensions.
3. Identifying `H.Point` (or the relevant subset of it) with
   `IsDedekindDomain.HeightOneSpectrum (CoordinateRing H)`, to define
   `ordAt (v : HeightOneSpectrum (CoordinateRing H)) (r : CoordinateRing H) : ℤ`
   via `(Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {r})).factors`
   (cast to `ℤ`, `0` when `r = 0`) — deliberately not going through
   `intValuationDef`'s `WithZero (Multiplicative ℤ)` packaging, to keep this
   additive and directly summable for §4's degree computation.

None of steps 1–3 is attempted in this file. This is a genuine, acknowledged gap:
the hypotheses package below (`NonsingularData`) exists only to *name* what step 1–2
need, so that later files/sessions have a fixed target rather than having to
rediscover the requirements. -/

/-- The hypotheses needed to even start §3: `H.f` is not a square in `k[X]` (giving
`CoordinateRing H` a domain structure via irreducibility of `X² - C H.f`), and `H.f`
is squarefree (nonsingularity, needed for the Dedekind-domain property). Neither
consequence (`IsDomain (CoordinateRing H)`, `IsDedekindDomain (CoordinateRing H)`) is
derived from this structure in this file — it only records the hypotheses a later
file's derivation would take as input. -/
structure NonsingularData (H : HyperellipticPolynomial k) where
  /-- `X² - C H.f` is irreducible over `k` — the hypothesis `CoordinateRing H` being
  a domain (indeed a field-extension-shaped `AdjoinRoot`) rests on. Stated directly
  in this form, rather than via a `¬ IsSquare` reformulation, since irreducibility is
  exactly what Mathlib's `AdjoinRoot` API (see module docstring) consumes. The
  ambient ring is spelled out as `(k[X])[X]` (via the explicit type ascription on
  `X`) rather than left to be inferred from the final `: k[X]` result-type
  ascription alone, since elaboration of `X`/`C` themselves needs the coefficient
  ring `k[X]` pinned down before that point is reached. -/
  irreducible_defining_poly :
    Irreducible ((X : (k[X])[X]) ^ 2 - C H.f)
  /-- `H.f` is squarefree — the nonsingularity hypothesis, needed (on top of
  irreducibility above) for `CoordinateRing H` to be a Dedekind domain rather than
  merely a domain. -/
  squarefree_f : Squarefree H.f
  /-- `char k ≠ 2`, needed for `X² - C H.f` to be *separable* (not just
  irreducible): in characteristic 2, `X² - c = (X - √c)²` has a repeated root
  even when irreducible-as-a-polynomial-shaped-check might otherwise seem to
  apply, so separability genuinely needs this excluded. Required by
  `integralClosure.isDedekindDomain_fractionRing`'s `Algebra.IsSeparable`
  hypothesis (via `Polynomial.separable_X_sq_sub_C`-style reasoning: the
  derivative of `X² - c` is `2X`, which is the zero polynomial exactly when
  `2 = 0` in `k`, and a nonzero-derivative argument is the standard route to
  separability for this shape of polynomial). Matches the char-≠-2 caveat
  already flagged in `AffinePoints.lean`'s docstring for the point-level
  involution `iota_ne_self_of_Y_ne_zero`. -/
  char_ne_two : (2 : k) ≠ 0

/-- Given `NonsingularData`, `CoordinateRing H` is a domain. This is the one
consequence of §3's setup this file does derive — a short step from
`AdjoinRoot`'s field-when-irreducible machinery, since a field is in particular a
domain, and unlike the full Dedekind-domain property it does not need
`squarefree_f`. Recorded because `DivisorClassGroup.lean`'s embedding `s` and this
file's `toPair_injective` both implicitly want an ambient domain for the fraction
field of `CoordinateRing H` to make sense of "rational function" at all.

Deliberately stated as a `def` producing an `IsDomain` term, not a global
`instance`: `nd : NonsingularData H` is ordinary data, not itself typeclass-
inferable, so registering this as an `instance` is rejected by Lean (an instance's
non-instance-implicit arguments must be recoverable from the return type, which
`nd` is not). Callers who have a `NonsingularData H` in hand should bring this
into scope locally, e.g. `haveI := coordinateRingIsDomain H nd`, at the point they
need `IsDomain (CoordinateRing H)`. Named without the `inst`-prefix deliberately:
that naming convention triggers Lean's "this looks like an instance declaration"
heuristics even on a plain `def`. -/
def coordinateRingIsDomain (H : HyperellipticPolynomial k)
    (nd : NonsingularData H) : IsDomain (CoordinateRing H) :=
  -- `letI` (rather than `have`/`haveI`) makes `hfact` available to instance
  -- search across the *entire* remaining term. `CoordinateRing H` unfolds to
  -- exactly `AdjoinRoot (X ^ 2 - C H.f)` (`HyperellipticFunctionField.lean`).
  --
  -- NB: this does *not* go through `AdjoinRoot.instField` / `Field.toIsDomain`
  -- as an old comment here claimed. `AdjoinRoot.instField` requires the *base*
  -- ring of the `AdjoinRoot` — here `k[X]`, since the ambient polynomial ring
  -- is `(k[X])[X]` — to itself be a `Field`, which `k[X]` never is (`X` has no
  -- inverse). That's why the old `inferInstanceAs (IsDomain _)` failed: with
  -- no `Field k[X]` instance available, `AdjoinRoot.instField` wasn't found.
  --
  -- What actually applies is `AdjoinRoot.isDomain_of_prime`:
  --   theorem AdjoinRoot.isDomain_of_prime {R} [CommRing R] {f : R[X]}
  --     (hf : Prime f) : IsDomain (AdjoinRoot f)
  -- confirmed against current Mathlib docs (Mathlib.RingTheory.AdjoinRoot).
  -- Two things distinguish it from the previous (wrong) `inferInstanceAs`
  -- attempt: (1) it's a plain `theorem`, not a registered instance, so it must
  -- be applied directly rather than found by typeclass search — no `Fact`
  -- wrapper needed or consumed, unlike the old `hfact` approach; (2) it wants
  -- `Prime f`, not `Irreducible f` — so `nd.irreducible_defining_poly` needs
  -- converting via `Irreducible → Prime` (`.prime`), valid here since `k[X]`
  -- is a UFD (in fact PID, `k` a field), where irreducible = prime.
  -- Stage-boundary check: confirm `k[X]` itself is a domain — needed for
  -- `Irreducible.prime` below to fire (that lemma requires a UFD/GCD-type
  -- structure on the ambient ring `k[X]`, which itself needs `IsDomain k[X]`).
  -- If *this* line fails, the bug is upstream of the final `exact`.
  haveI : IsDomain (k[X]) := inferInstance
  AdjoinRoot.isDomain_of_prime nd.irreducible_defining_poly.prime

/-- Given `NonsingularData`, `CoordinateRing H` is a Dedekind domain. **Not proved
here** — this is the central §3 gap. See `Genus2Lean/PrincipalDivisorsScratch.lean`
for an in-progress draft attempt (built via Mathlib's
`integralClosure.isDedekindDomain_fractionRing`: `k[X]` is Dedekind (PID), and
`FractionRing (CoordinateRing H)` is a finite separable extension of
`FractionRing (k[X])`, so the integral closure of `k[X]` in that fraction field is
Dedekind; transporting that down to `CoordinateRing H` itself needs
`CoordinateRing H` to equal that integral closure, which genuinely uses
`squarefree_f`). That scratch file is NOT wired into the build or into anything
downstream — kept separate until the chain actually compiles, so an in-progress
draft never silently becomes load-bearing for other files. -/
theorem coordinateRingIsDedekindDomain (H : HyperellipticPolynomial k)
    (nd : NonsingularData H) : IsDedekindDomain (CoordinateRing H) := by
  sorry

/-! ## §4. `deg(div g) = 0` — the target theorem, stated but not proved

This is the theorem that would let `DivisorClassGroup.lean`'s `PrincipalDivisorData`
actually be instantiated from `CoordinateRing H` (its `le_Divisor0` field is exactly
this fact, once `div` is built). Stated here against a fully abstract signature
(`ordAt`/`ordInfOfPair` as free variables satisfying the properties they should have,
rather than against the not-yet-built concrete `ordAt` of §3) so the *shape* of the
target is fixed even though the construction behind it is not.

**This theorem is not proved in this file — it is the central remaining gap.** A
genuine proof combines: (a) the affine product formula
`∏_v v(g)^{ord_v(g)}` type factorization-of-`(g)`-as-an-ideal argument (standard for
Dedekind domains, via `Ideal.span {g} = ∏ v.asIdeal ^ ord_v(g)` and comparing norms
down to `k[X]`), with (b) the pole order at infinity from §2, matching them via a
degree-of-the-norm-polynomial computation (the norm `pairNorm H A B` of the
numerator/denominator controls both). This is the kind of argument that genuinely
needs a Lean environment with a working `#check`/goal-state loop to get right;
writing it blind risks silently encoding a false statement, which is worse than
leaving it as `sorry`. -/

/-- Target statement: the affine orders (`ordAt`, abstracted here since §3's
concrete construction is not built) plus the order at infinity (`ordInfOfPair`, §2)
of any nonzero `A + By` sum to zero. `ordAt` is taken as a hypothesis-level function
here, not `HeightOneSpectrum`-derived, precisely to isolate "what §4 needs from §3"
from "what §3 needs to construct" — once §3 exists, this signature is what its
`ordAt` should be checked against before this theorem is attempted. -/
theorem deg_div_eq_zero_deg5 (H : HyperellipticPolynomial k) (hdeg : H.f.natDegree = 5)
    (ordAt : H.Point → k[X] → k[X] → ℤ)
    -- ordAt should satisfy: ordAt P A B = 0 for all but finitely many P, so the sum
    -- below is well-defined. Not stated as a hypothesis here (would need a Finset /
    -- Finsupp-shaped `ordAt` to even typecheck a finite sum) — another design
    -- decision deferred to when §3 is actually built.
    (S : Finset H.Point) (A B : k[X]) (hAB : ¬(A = 0 ∧ B = 0))
    (hsupp : ∀ P, P ∉ S → ordAt P A B = 0) :
    (∑ P ∈ S, ordAt P A B) + ordInfOfPair A B = 0 := by
  sorry

end HyperellipticPolynomial
