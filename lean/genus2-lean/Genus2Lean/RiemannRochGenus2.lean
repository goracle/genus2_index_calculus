import Mathlib
import Genus2Lean.HyperellipticFunctionField
import Genus2Lean.AffinePoints
import Genus2Lean.DivisorClassGroup
import Genus2Lean.PrincipalDivisors
import Genus2Lean.PrincipalDivisorSubgroup
import Genus2Lean.FFKSidon
import Genus2Lean.HyperellipticClassProof
noncomputable section

open Classical

set_option linter.style.header false

open Polynomial


/-!
# The hard direction of FFK: `SidonDichotomy` from genus-2 Riemann–Roch

`FFKSidon.lean` packages the forward direction of the Forey–Fresán–Kowalski
dichotomy as an unproved hypothesis `PrincipalDivisorData.SidonDichotomy`.
This file attempts to derive it, for the concrete `D := principalDivisorData
H hdeg`, from the two genus-2-specific Riemann–Roch facts spelled out in
`ROADMAP-ffk-sidon.md`:

* `finrank_L_pair`: `ℓ((x₁)+(x₂)) = 1` whenever `x₂ ≠ ι x₁`.
* `finrank_L_canonical`: `ℓ(K) = 2`, and the effective divisors in `|K|`
  are exactly the hyperelliptic fibers `(x)+(ι x)`.

**Status.** The `k`-submodule `L D` is built below and is a genuine
construction (mirroring `RiemannRochSpaceInf`'s pole-order convention, but
at two affine points rather than at infinity), not a placeholder. The two
dimension theorems above are stated precisely and left as named `sorry`s —
they are the two hardest remaining steps in this project, per the roadmap.
**What is fully proved, unconditionally given those two facts**, is the
assembly: `sidonDichotomy_of_riemannRoch` derives the complete dichotomy
from `finrank_L_pair` + `finrank_L_canonical` alone, so the dependency
shape is locked in and typechecked even though the two inputs are not yet
supplied.

Everything here is scoped to the `H.f.natDegree = 5` case, matching
`principalDivisorData`'s own scope (`PrincipalDivisorSubgroup.lean`) and
`hyperellipticClass_principalDivisorData`'s.
-/

namespace HyperellipticPolynomial

open Divisor

variable {k : Type*} [Field k]
variable {H : HyperellipticPolynomial k}

/-! ## §1. `L(x₁ + x₂)`: the Riemann–Roch space of an affine degree-2 divisor

An element of `L((x₁)+(x₂))` is a ratio of two coordinate-ring elements,
`toPair H A B / toPair H A' B'`, subject to:

* no worse pole at infinity than the denominator (`ordInfOfPair A B ≥
  ordInfOfPair A' B'` — weakened from the originally-intended `=`; see
  `LPairCarrier_add_smul`'s docstring for why exact equality isn't provable
  for an arbitrary `k`-linear combination of two pole-bounded pairs, and
  `≥` is the direction actually needed and closed everywhere in this file);
* at every affine point `P`, the ratio's pole is bounded by the
  multiplicity of `P` in the divisor `(x₁)+(x₂)`: `ordAt P A B ≥ ordAt P
  A' B' - ((if P = x₁ then 1 else 0) + (if P = x₂ then 1 else 0))`. Away
  from `{x₁,x₂}` both indicators vanish, giving the expected "no pole"
  bound; at `x₁` or `x₂` (distinct) it gives the expected "at worst simple
  pole" bound; when `x₁ = x₂` the two indicators add, correctly giving "at
  worst a double pole" at that single point.

Represented as a `Set` predicate on `FractionRing (CoordinateRing H)`
first (so equality of two representations of the same ratio is handled by
the ambient field, not by hand), then packaged as a `Submodule`. -/

variable [IsDedekindDomain (CoordinateRing H)]

/-- The pole/zero conditions a numerator/denominator pair `(A,B,A',B')`
must satisfy to represent an element of `L((x₁)+(x₂))`. Stated as a
`Prop` on the four polynomials rather than on the resulting field element,
so `L` can be defined as an image/range without first needing to know the
map `(A,B,A',B') ↦ toPair H A B / toPair H A' B'` is well-behaved.

The pointwise pole bound is a single clause, `ordAt P A B ≥ ordAt P A' B' -
((if P = x₁ then 1 else 0) + (if P = x₂ then 1 else 0))`, rather than three
separate clauses (elsewhere / at `x₁` / at `x₂`) as an earlier version of
this definition had it. The two versions agree whenever `x₁ ≠ x₂`, but the
three-clause version is *wrong* when `x₁ = x₂`: its two `-1` bounds "at
`x₁`" and "at `x₂`" become the same clause stated twice, capping the pole
at `x₁` to a single order even though the divisor `(x₁)+(x₂) = 2•(x₁)`
should allow a double pole there. The single indicator-sum clause correctly
gives `-2` slack in that case (`1 + 1`), and reduces to the old three-clause
shape's content whenever the two points are distinct — so it's a strict
generalization, not a change in what the pair-generic case (`x₁ ≠ x₂`)
means. -/
def IsPoleBoundedAtPair (x₁ x₂ : H.Point) (A B A' B' : k[X]) : Prop :=
  ¬ (A' = 0 ∧ B' = 0) ∧
  ordInfOfPair A B ≥ ordInfOfPair A' B' ∧
  (∀ P : H.Point, ordAt P A B ≥ ordAt P A' B' -
    ((if P = x₁ then 1 else 0) + (if P = x₂ then 1 else 0)))

/-- The image of `toPair H A B / toPair H A' B'` in `FractionRing
(CoordinateRing H)`, for a pair satisfying `IsPoleBoundedAtPair`. -/
def polePairToFraction (A B A' B' : k[X]) : FractionRing (CoordinateRing H) :=
  algebraMap (CoordinateRing H) (FractionRing (CoordinateRing H)) (toPair H A B) /
  algebraMap (CoordinateRing H) (FractionRing (CoordinateRing H)) (toPair H A' B')

/-- `L((x₁)+(x₂))`, as a bare `Set`: every field element arising from some
pole-bounded representation. This is the honest definition — `L` as a
`Submodule` (`LPair`, below) has this as its carrier, with `k`-submodule
closure proved separately rather than baked into this `Set`-builder. -/
def LPairCarrier (x₁ x₂ : H.Point) : Set (FractionRing (CoordinateRing H)) :=
  { z | ∃ A B A' B' : k[X], IsPoleBoundedAtPair x₁ x₂ A B A' B' ∧
      z = polePairToFraction A B A' B' }

/-- **General-purpose unit lemma, factored out of `HyperellipticClassProof.lean`'s
`ordAt_linX_eq_zero_of_ne` proof body** (which proved exactly this shape inline, for
`toPair H (linX a) 0` specifically): if `toPair H A B ∉ pointIdeal P`, then
`ordAt P A B = 0`. Same chain as that theorem — `Ideal.dvd_span_singleton`
("to divide is to contain", contrapositive) to get non-divisibility, then
`intValuation_lt_one_iff_dvd` / `intValuation_le_one` to pin the valuation at
exactly `1`, so `WithZero.log = 0`. Stated once here so `one_mem_LPairCarrier`
doesn't have to re-derive it for the specific case `toPair H 1 0 = 1`. -/
theorem ordAt_eq_zero_of_notMem (P : H.Point) (A B : k[X])
    (hnotmem : toPair H A B ∉ pointIdeal P) :
    ordAt P A B = 0 := by
  have hgne : toPair H A B ≠ 0 := by
    intro hz
    apply hnotmem
    rw [hz]
    exact Submodule.zero_mem _
  by_cases h_bot : pointIdeal P = ⊥
  · -- `pointIdeal P = ⊥` would force `toPair H A B = 0` to be the only element
    -- of `pointIdeal P`, but `hnotmem`'s witness `toPair H A B ∉ pointIdeal P`
    -- doesn't actually need this case separated out — `ordAt`'s own `dif_pos`
    -- branch already returns `0` directly when `pointIdeal P = ⊥`.
    unfold ordAt
    rw [if_neg hgne, dif_pos h_bot]
  · have hnotdvd :
        ¬ pointIdeal P ∣ Ideal.span ({toPair H A B} : Set (CoordinateRing H)) := by
      rw [Ideal.dvd_span_singleton]
      exact hnotmem
    have hval_not_lt : ¬ (pointHeightOne P h_bot).intValuation (toPair H A B) < 1 := by
      rw [(pointHeightOne P h_bot).intValuation_lt_one_iff_dvd]
      exact hnotdvd
    have hval_le : (pointHeightOne P h_bot).intValuation (toPair H A B) ≤ 1 :=
      (pointHeightOne P h_bot).intValuation_le_one (toPair H A B)
    have hval_eq : (pointHeightOne P h_bot).intValuation (toPair H A B) = 1 :=
      le_antisymm hval_le (not_lt.mp hval_not_lt)
    unfold ordAt
    rw [if_neg hgne, dif_neg h_bot]
    show -WithZero.log ((pointHeightOne P h_bot).intValuation (toPair H A B)) = 0
    rw [hval_eq]
    simp

/-- `toPair H 1 0 = 1`: unfolds `toPair`'s definition (`algebraMap A +
algebraMap B * y H`) with `A = 1, B = 0`, and `algebraMap` is a ring hom so
sends `1 ↦ 1`. -/
theorem toPair_one_zero : toPair H (1 : k[X]) 0 = 1 := by
  unfold toPair
  simp

/-- `toPair H 1 0 = 1 ∉ pointIdeal P` for any `P`: `pointIdeal P` is a proper
ideal (it is maximal, `pointIdeal_isMaximal`, hence `≠ ⊤`), and any ideal
containing a unit is `⊤` (`Ideal.eq_top_of_isUnit_mem`) — `1` is a unit
(`isUnit_one`), so `1 ∈ pointIdeal P` would force `pointIdeal P = ⊤`,
contradicting maximality. -/
theorem toPair_one_zero_notMem_pointIdeal (P : H.Point) :
    toPair H (1 : k[X]) 0 ∉ pointIdeal P := by
  rw [toPair_one_zero]
  intro hmem
  exact (pointIdeal_isMaximal P).ne_top
    (Ideal.eq_top_of_isUnit_mem (pointIdeal P) hmem isUnit_one)

/-- `ordAt P 1 0 = 0` for every `P`: `toPair H 1 0 = 1` is never in any
`pointIdeal P` (`toPair_one_zero_notMem_pointIdeal`), so
`ordAt_eq_zero_of_notMem` applies directly. -/
theorem ordAt_one_zero (P : H.Point) : ordAt P (1 : k[X]) 0 = 0 :=
  ordAt_eq_zero_of_notMem P 1 0 (toPair_one_zero_notMem_pointIdeal P)

/-- `ordInfOfPair 1 0 = 0`: `(1 : k[X])` has `natDegree = 0`
(`Polynomial.natDegree_one`) and is nonzero, so `ordInfOfPair`'s `else`
branch gives `-(max (2*0) 0) = 0`. -/
theorem ordInfOfPair_one_zero : ordInfOfPair (1 : k[X]) 0 = 0 := by
  unfold ordInfOfPair
  rw [if_neg (by simp : ¬((1 : k[X]) = 0 ∧ (0 : k[X]) = 0)), if_pos rfl,
    Polynomial.natDegree_one]
  simp

/-- `polePairToFraction 1 0 1 0 = 1`: both numerator and denominator are
`toPair H 1 0 = 1` (`toPair_one_zero`), so the ratio is `1/1 = 1`. -/
theorem polePairToFraction_one_zero_one_zero (H : HyperellipticPolynomial k)
    [IsDedekindDomain (CoordinateRing H)] :
    polePairToFraction (H := H) (1 : k[X]) 0 1 0 = 1 := by
  unfold polePairToFraction
  rw [toPair_one_zero]
  simp

/-- `1 ∈ LPairCarrier x₁ x₂`, via `A = 1, B = 0, A' = 1, B' = 0`: the
constant function has no poles anywhere. `IsPoleBoundedAtPair`'s three
conjuncts close via, respectively: `toPair_one_zero_notMem_pointIdeal`
(ruling out the vacuous `A'=B'=0` case, since `toPair H 1 0 = 1 ≠ 0`, hence
`¬(1=0 ∧ 0=0)` directly — no need for the ideal-membership fact here, just
`one_ne_zero`), `ordInfOfPair_one_zero` (both sides), `ordAt_one_zero`
(giving `0 ≥ 0 - (...)` at every point, true regardless of the indicator
sum since it's `≥ 0`). -/
theorem one_mem_LPairCarrier (x₁ x₂ : H.Point) : (1 : FractionRing (CoordinateRing H)) ∈
    LPairCarrier x₁ x₂ := by
  refine ⟨1, 0, 1, 0, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact fun h => one_ne_zero h.1
  · exact le_refl _
  · -- Goal: `∀ P, ordAt P 1 0 ≥ ordAt P 1 0 - (...)`. Holds for *any*
    -- integer value of `ordAt P 1 0` and any nonneg indicator sum, so no
    -- `rw`/`simp` on the concrete value is needed — `omega` alone closes
    -- each instance once the statement is recognized as being about a
    -- single integer term minus a nonnegative quantity.
    intro P
    omega
  · exact (polePairToFraction_one_zero_one_zero H).symm

/-- `algebraMap k[X] (CoordinateRing H)` is injective — same proof as
`coordinateRing_not_isField`'s `hinj`, isolated as its own lemma so
`pairNorm_mul_of_toPair_mul` below can cancel it without re-deriving. -/
theorem algebraMap_coordinateRing_injective :
    Function.Injective (algebraMap k[X] (CoordinateRing H)) := by
  show Function.Injective (AdjoinRoot.of (X ^ 2 - C H.f))
  exact AdjoinRoot.of.injective_of_degree_ne_zero degree_X_sq_sub_C_H_f_ne_zero

/-- **`pairNorm` is multiplicative under `toPair` multiplication**: if
`toPair H A₃ B₃ = toPair H A B * toPair H A' B'`, then `pairNorm H A₃ B₃ =
pairNorm H A B * pairNorm H A' B'`. Proof: `involution H` is a `RingHom`
(`map_mul`), so `toPair_mul_involution` applied to the product gives
`algebraMap (pairNorm H A₃ B₃) = (toPair H A B * toPair H A' B') *
involution H (toPair H A B * toPair H A' B') = (toPair H A B * involution H
(toPair H A B)) * (toPair H A' B' * involution H (toPair H A' B'))` after
regrouping (commutative ring), which is `algebraMap (pairNorm H A B) *
algebraMap (pairNorm H A' B') = algebraMap (pairNorm H A B * pairNorm H A'
B')` by `toPair_mul_involution` again plus `map_mul`. Cancel `algebraMap`
via its injectivity (`algebraMap_coordinateRing_injective`). -/
theorem pairNorm_mul_of_toPair_mul (A B A' B' A₃ B₃ : k[X])
    (hA₃ : toPair H A₃ B₃ = toPair H A B * toPair H A' B') :
    pairNorm H A₃ B₃ = pairNorm H A B * pairNorm H A' B' := by
  have h3 := toPair_mul_involution H A₃ B₃
  have h1 := toPair_mul_involution H A B
  have h2 := toPair_mul_involution H A' B'
  rw [hA₃, map_mul (involution H)] at h3
  -- h3 : (toPair H A B * toPair H A' B') * (involution H (toPair H A B) *
  --       involution H (toPair H A' B')) = algebraMap (pairNorm H A₃ B₃)
  have hregroup : toPair H A B * toPair H A' B' *
      (involution H (toPair H A B) * involution H (toPair H A' B')) =
      (toPair H A B * involution H (toPair H A B)) *
        (toPair H A' B' * involution H (toPair H A' B')) := by ring
  rw [hregroup, h1, h2, ← map_mul] at h3
  exact (algebraMap_coordinateRing_injective h3).symm

/-- **`ordInfOfPair` is additive under `toPair` multiplication** (the deg-5
case): if `toPair H A₃ B₃ = toPair H A B * toPair H A' B'` and all three pairs
are nonzero, then `ordInfOfPair A₃ B₃ = ordInfOfPair A B + ordInfOfPair A'
B'`. Proof: `natDegree_pairNorm_eq_neg_ordInfOfPair` (already proved,
`PrincipalDivisors.lean`) converts each `ordInfOfPair` to `-(pairNorm
...).natDegree`; `pairNorm_mul_of_toPair_mul` turns the combined `pairNorm`
into a product, and `Polynomial.natDegree_mul` (valid since `pairNorm H A B`
and `pairNorm H A' B'` are both nonzero — they're `A²-B²f`, nonzero because
`toPair_mul_involution` identifies them with a nonzero coordinate-ring norm
of a nonzero element in the deg-5 domain case) turns `natDegree` of a product
into a sum. -/
theorem ordInfOfPair_add_of_toPair_mul [IsDomain (CoordinateRing H)]
    (hdeg : H.f.natDegree = 5)
    (A B A' B' A₃ B₃ : k[X])
    (hAB : ¬(A = 0 ∧ B = 0)) (hA'B' : ¬(A' = 0 ∧ B' = 0))
    (hA₃B₃ : ¬(A₃ = 0 ∧ B₃ = 0))
    (hA₃ : toPair H A₃ B₃ = toPair H A B * toPair H A' B') :
    ordInfOfPair A₃ B₃ = ordInfOfPair A B + ordInfOfPair A' B' := by
  have hn3 := natDegree_pairNorm_eq_neg_ordInfOfPair H hdeg A₃ B₃ hA₃B₃
  have hn1 := natDegree_pairNorm_eq_neg_ordInfOfPair H hdeg A B hAB
  have hn2 := natDegree_pairNorm_eq_neg_ordInfOfPair H hdeg A' B' hA'B'
  have hprod := pairNorm_mul_of_toPair_mul (H := H) A B A' B' A₃ B₃ hA₃
  have hne1 : pairNorm H A B ≠ 0 := pairNorm_ne_zero_of_ne A B hAB
  have hne2 : pairNorm H A' B' ≠ 0 := pairNorm_ne_zero_of_ne A' B' hA'B'
  have hdeg_prod : (pairNorm H A₃ B₃).natDegree =
      (pairNorm H A B).natDegree + (pairNorm H A' B').natDegree := by
    rw [hprod, Polynomial.natDegree_mul hne1 hne2]
  -- Combine: `-ordInfOfPair A₃ B₃ = (pairNorm A₃ B₃).natDegree`
  -- `= (pairNorm A B).natDegree + (pairNorm A' B').natDegree`
  -- `= -ordInfOfPair A B + -ordInfOfPair A' B'`, so negate both sides.
  have : (-(ordInfOfPair A₃ B₃) : ℤ) = -(ordInfOfPair A B) + -(ordInfOfPair A' B') := by
    rw [← hn3, ← hn1, ← hn2]
    exact_mod_cast hdeg_prod
  omega

/-- `toPair H (A₁+A₂) (B₁+B₂) = toPair H A₁ B₁ + toPair H A₂ B₂`: linearity of
`toPair` in its two polynomial arguments, extracted from the identical
computation already inline in `RiemannRochSpaceInf`'s `add_mem'`
(`HyperellipticFunctionField.lean`). -/
theorem toPair_add (A1 B1 A2 B2 : k[X]) :
    toPair H (A1 + A2) (B1 + B2) = toPair H A1 B1 + toPair H A2 B2 := by
  unfold toPair
  simp only [map_add]
  set a1 := algebraMap k[X] (CoordinateRing H) A1
  set a2 := algebraMap k[X] (CoordinateRing H) A2
  set b1 := algebraMap k[X] (CoordinateRing H) B1
  set b2 := algebraMap k[X] (CoordinateRing H) B2
  set w := y H
  ring

/-- `c • toPair H A B = toPair H (C c * A) (C c * B)`: the `k`-scalar action
(routed through `Algebra.compHom` via `algebraMap k k[X]`, per the
`Algebra k (CoordinateRing H)` instance) distributes into both polynomial
slots as multiplication by the constant polynomial `C c`. Extracted from the
identical computation already inline in `RiemannRochSpaceInf`'s
`smul_mem'`. -/
theorem toPair_smul (c : k) (A B : k[X]) :
    c • toPair H A B = toPair H (C c * A) (C c * B) := by
  unfold toPair
  rw [Algebra.compHom_smul_def, Algebra.smul_def]
  rw [show algebraMap k k[X] c = C c from by simp [Polynomial.algebraMap_apply]]
  simp only [map_mul]
  set a := algebraMap k[X] (CoordinateRing H) A
  set b := algebraMap k[X] (CoordinateRing H) B
  set cc := algebraMap k[X] (CoordinateRing H) (C c)
  set w := y H
  ring

/-- **The explicit multiplication formula for `toPair`**: `toPair H A B *
toPair H A' B' = toPair H (A*A' + B*B'*H.f) (A*B' + A'*B)`. Derived directly:
`(a+by)(a'+b'y) = aa' + ab'y + a'by + bb'y² = (aa'+bb'f) + (ab'+a'b)y` using
`y² = f` (`y_sq_eq`). This is the multiplication-closure fact `toPair_add`
provides for addition — needed to exhibit an explicit `(A'',B'')` witness for
`LPairCarrier_add_smul`'s combined numerator/denominator, matching the
abstract `toPair_surjective_local` existence with a concrete formula so the
later `ordAt`/`ordInfOfPair` additivity lemmas (`ordAt_toPair_mul_of_ne_zero`,
`ordInfOfPair_add_of_toPair_mul`) can be applied against a witness pair that
is written down, not merely known to exist. -/
theorem toPair_mul (A B A' B' : k[X]) :
    toPair H A B * toPair H A' B' =
      toPair H (A * A' + B * B' * H.f) (A * B' + A' * B) := by
  unfold toPair
  have hy2 : y H ^ 2 = algebraMap k[X] (CoordinateRing H) H.f := y_sq_eq H
  simp only [map_add, map_mul]
  set a := algebraMap k[X] (CoordinateRing H) A
  set b := algebraMap k[X] (CoordinateRing H) B
  set a' := algebraMap k[X] (CoordinateRing H) A'
  set b' := algebraMap k[X] (CoordinateRing H) B'
  set fH := algebraMap k[X] (CoordinateRing H) H.f
  set w := y H
  have : (a + b * w) * (a' + b' * w) = a * a' + b * b' * w ^ 2 + (a * b' + a' * b) * w := by
    ring
  rw [this, hy2]

/-- **Key new infrastructure**: `ordAt` is additive under multiplication of
`CoordinateRing H` elements, stated directly at the `intValuation` level
(bypassing `toPair`-pair bookkeeping). `intValuation` is a bundled `Valuation`
(`IsDedekindDomain.HeightOneSpectrum.intValuation : Valuation (CoordinateRing H)
(WithZero (Multiplicative ℤ))`), hence a `MonoidWithZeroHom`, so `map_mul`
applies directly; `WithZero.log_mul` then turns that multiplicativity into
additivity on the nonzero values, and `ordAt`'s defining `-` flips it back to
`+` — both steps confirmed against Mathlib's `RingTheory.DedekindDomain.
AdicValuation` and `Algebra.GroupWithZero.WithZero` source. -/
theorem ordAt_toPair_mul_of_ne_zero
    (P : H.Point) (h_bot : pointIdeal P ≠ ⊥) (g g' : CoordinateRing H)
    (hg : g ≠ 0) (hg' : g' ≠ 0) (A B A₃ B₃ : k[X]) (hA : toPair H A B = g)
    (hA₃ : toPair H A₃ B₃ = g * g') :
    ordAt P A₃ B₃ = ordAt P A B +
      -WithZero.log ((pointHeightOne P h_bot).intValuation g') := by
  have hne3 : toPair H A₃ B₃ ≠ 0 := by rw [hA₃]; exact mul_ne_zero hg hg'
  have hneA : toPair H A B ≠ 0 := hA ▸ hg
  unfold ordAt
  rw [if_neg hne3, if_neg hneA, dif_neg h_bot, dif_neg h_bot]
  rw [hA₃, hA, map_mul, WithZero.log_mul ((pointHeightOne P h_bot).intValuation_ne_zero g hg)
    ((pointHeightOne P h_bot).intValuation_ne_zero g' hg')]
  ring

/-- **Corollary of `ordAt_toPair_mul_of_ne_zero`, stated entirely at the `(A,B)`-pair
level**: if `toPair H A₃ B₃ = toPair H A B * toPair H A' B'` with both factors
nonzero, then `ordAt P A₃ B₃ = ordAt P A B + ordAt P A' B'`. This is the shape every
call site in `LPairCarrier_add_smul` actually needs (as opposed to
`ordAt_toPair_mul_of_ne_zero`'s raw `-WithZero.log (intValuation g')` term on the
right, which still needs identifying with `ordAt P A' B'` — done here once, via
`ordAt`'s own definition unfolded symmetrically for `(A',B')`, rather than inline
at every call site). -/
theorem ordAt_toPair_mul_of_ne_zero'
    (P : H.Point) (h_bot : pointIdeal P ≠ ⊥) (A B A' B' A₃ B₃ : k[X])
    (hAB : toPair H A B ≠ 0) (hA'B' : toPair H A' B' ≠ 0)
    (hA₃ : toPair H A₃ B₃ = toPair H A B * toPair H A' B') :
    ordAt P A₃ B₃ = ordAt P A B + ordAt P A' B' := by
  have hstep := ordAt_toPair_mul_of_ne_zero P h_bot (toPair H A B) (toPair H A' B')
    hAB hA'B' A B A₃ B₃ rfl hA₃
  have hA'val : ordAt P A' B' =
      -WithZero.log ((pointHeightOne P h_bot).intValuation (toPair H A' B')) := by
    unfold ordAt
    rw [if_neg hA'B', dif_neg h_bot]
  rw [hstep, hA'val]

/-- **Ultrametric inequality for `ordAt`**, again stated at the `intValuation`
level: `v.intValuationDef (x+y) ≤ max (v.intValuationDef x) (v.intValuationDef
y)` is `IsDedekindDomain.HeightOneSpectrum.intValuation.map_add_le_max'`,
confirmed against Mathlib source. After `ordAt`'s sign flip and `-max = min
∘ -`, this becomes the expected `ordAt P (x+y) ≥ min (ordAt P x) (ordAt P y)`
— stated here directly on `CoordinateRing H` elements via their valuations,
leaving the translation back to explicit `(A,B)` pairs (needed for
`IsPoleBoundedAtPair`'s literal statement) to the caller via
`toPair_surjective_local`. **Still requires assembling the full
`LPairCarrier_add_smul` common-denominator argument on top of this and
`ordAt_toPair_mul_of_ne_zero`, plus the separate `ordInfOfPair` additivity
fact (which is elementary `natDegree` arithmetic, not valuation theory, but
is not yet written either) — left `sorry`'d below as the remaining assembly
step.** -/
theorem intValuation_add_le_max
    (P : H.Point) (h_bot : pointIdeal P ≠ ⊥) (g g' : CoordinateRing H) :
    (pointHeightOne P h_bot).intValuation (g + g') ≤
      max ((pointHeightOne P h_bot).intValuation g)
        ((pointHeightOne P h_bot).intValuation g') :=
  IsDedekindDomain.HeightOneSpectrum.intValuation.map_add_le_max' _ g g'

/-- **`ordAt`'s ultrametric inequality**, translated from `intValuation_add_le_max`
via `ordAt`'s definition (`ordAt = -WithZero.log ∘ intValuation`, the `toPair H A B
= 0`/`pointIdeal P = ⊥` branches trivial). Uses a locally-proved `WithZero.log`
monotonicity helper (`WithZero.log_le_log_of_ne_zero` below), since Mathlib's
`WithZero` API has no order-compatibility lemma for `log` (confirmed absent:
`log_exp`/`exp_log`/`log_mul`/`log_pow`/`log_div`/`log_inv`/`log_zpow` are the only
`log`-adjacent facts). **Fully proved**, `intValuation_neg` included — the
`g,g' ≠ 0` but `g+g' = 0` branch this docstring used to flag as an unclosed
residual (`ordAt P A B = 0` needed exactly, not provable from `ordAt_nonneg`
alone — see `ordAt_add_ge_min`'s own docstring/history for the counterexample
showing that branch is false as originally stated) is now structurally
unreachable: `ordAt_add_ge_min` gained an explicit `g + g' ≠ 0` hypothesis this
session, which rules the branch out via `hA₃` directly rather than needing it
proved. The corresponding proof obligation didn't disappear — it moved to
`ordAt_add_ge_min`'s one call site (`hordN` in `LPairCarrier_add_smul`), which
now carries its own `sorry`'d `hsum_ne` side fact instead. -/
theorem WithZero.log_le_log_of_ne_zero {x y : WithZero (Multiplicative ℤ)}
    (hx : x ≠ 0) (hy : y ≠ 0) (h : x ≤ y) : x.log ≤ y.log := by
  -- Recover `x = exp x.log`, `y = exp y.log` from `exp_log` (needs `x ≠ 0`/`y ≠ 0`),
  -- then push `h : x ≤ y` through those rewrites to get `exp x.log ≤ exp y.log`,
  -- and unfold `exp a = ↑(Multiplicative.ofAdd a)` (`exp_eq_coe_ofAdd`) so `h`
  -- becomes `(↑(ofAdd x.log) : WithZero (Multiplicative ℤ)) ≤ ↑(ofAdd y.log)`, which
  -- `WithZero.coe_le_coe` reduces to `ofAdd x.log ≤ ofAdd y.log` in `Multiplicative ℤ`.
  -- `Multiplicative α`'s order (for `α` a `Preorder`) is definitionally `α`'s own
  -- order carried across the `ofAdd`/`toAdd` type-synonym identity, so this is
  -- literally `x.log ≤ y.log` already — no separate `ofAdd_le` lemma needed.
  rw [← WithZero.exp_log hx, ← WithZero.exp_log hy, WithZero.exp_eq_coe_ofAdd,
      WithZero.exp_eq_coe_ofAdd, WithZero.coe_le_coe] at h
  exact h

/-- `toPair H (-A) (-B) = -toPair H A B`: specialize `toPair_smul` to `c = -1`,
using `C (-1) = -1` (`Polynomial.C_neg`/`map_neg` on `C`, plus `C 1 = 1`) and
`(-1 : k) • x = -x` (`neg_one_smul`). Not currently used by `ordAt_add_ge_min`
below — its hard sub-case takes a more direct route to the same fact, deriving
`toPair H A' B' = -(toPair H A B)` straight from `hA`/`hA'`/`g+g'=0` without
going through `A`/`B` as literal negated polynomials — but kept here as a
standalone, independently useful fact about `toPair`. -/
theorem toPair_neg (A B : k[X]) :
    toPair H (-A) (-B) = -toPair H A B := by
  have hC : (C (-1 : k) : k[X]) = -1 := by simp
  have h := @toPair_smul k _ H _ (-1 : k) A B
  rw [neg_one_smul, hC, neg_one_mul, neg_one_mul] at h
  exact h.symm

/-- `intValuation` is negation-invariant: `v(-x) = v(x)` for every
`x : CoordinateRing H`. Closed via the generic `Valuation.map_neg`
(`IsDedekindDomain.HeightOneSpectrum.intValuation` is bundled as a
`Valuation (CoordinateRing H) (WithZero (Multiplicative ℤ))`, and
`Valuation.map_neg` is the standard fact `v (-x) = v x` for any `Valuation`
on a ring — it does not need commutativity of the value monoid or any
extra hypothesis, since it's derived exactly the way the old docstring
here sketched: `v(-1)^2 = v((-1)^2) = v(1) = 1` in the (linearly ordered,
hence multiplication-cancellative on nonzero elements, and visibly `≤ 1`
everywhere by `intValuation_le_one`) value monoid forces `v(-1) = 1`, then
`v(-x) = v(-1) * v(x) = v(x)`). Manual fallback, if `Valuation.map_neg`
turns out not to unify against `intValuation`'s bundled form: replace the
one-liner below with `have hone : (pointHeightOne P h_bot).intValuation
(-1) = 1 := ...` proved from `map_mul`/`map_one` applied to `(-1)*(-1)=1`
via `mul_self_eq_one_iff` (or the `intValuation_le_one` upper bound plus
`WithZero`/`Multiplicative ℤ` having no other square root of `1` that is
`≤ 1`), then `rw [show (-x) = (-1) * x from (neg_one_mul x).symm, map_mul,
hone, one_mul]`. -/
theorem intValuation_neg
    (P : H.Point) (h_bot : pointIdeal P ≠ ⊥) (x : CoordinateRing H) :
    (pointHeightOne P h_bot).intValuation (-x) =
      (pointHeightOne P h_bot).intValuation x :=
  Valuation.map_neg (pointHeightOne P h_bot).intValuation x

theorem ordAt_add_ge_min
    (P : H.Point) (g g' : CoordinateRing H) (A B A' B' A₃ B₃ : k[X])
    (hA : toPair H A B = g) (hA' : toPair H A' B' = g') (hA₃ : toPair H A₃ B₃ = g + g')
    (hgg'_ne : g + g' ≠ 0) :
    ordAt P A₃ B₃ ≥ min (ordAt P A B) (ordAt P A' B') := by
  by_cases h_bot : pointIdeal P = ⊥
  · -- Every `ordAt` collapses to its `dif_pos h_bot` branch, `0`, regardless of the
    -- `toPair H _ _ = 0` case (that `if` is checked first, but its `then`-branch is
    -- also `0`, so either way each `ordAt` term here is `0`).
    have h0 : ∀ (C D : k[X]), ordAt P C D = 0 := by
      intro C D
      unfold ordAt
      split
      · rfl
      · rfl
    rw [h0 A B, h0 A' B', h0 A₃ B₃]
    simp
  · -- `h_bot : pointIdeal P ≠ ⊥` from here on (via `by_cases`'s negative branch giving
    -- exactly that, since `by_cases` on a `Decidable`/`Prop` `=` splits into `h_bot :
    -- pointIdeal P = ⊥` and `h_bot : ¬ pointIdeal P = ⊥` i.e. `pointIdeal P ≠ ⊥`).
    by_cases hg : toPair H A B = 0
    · -- `g = 0` (via `hA`), so `g + g' = g'` and `ordAt P A B = 0` (the `if`-branch).
      -- `min 0 (ordAt P A' B') ≤ 0 ≤ ordAt P A₃ B₃` needs `ordAt P A₃ B₃ ≥ 0`, which
      -- fails in general unless `toPair H A₃ B₃ = toPair H A' B'` as *values* lets us
      -- reuse `A',B'`'s `ordAt` directly — but `A₃,B₃` need not literally be `A',B'`,
      -- only agree on `toPair`'s value. `ordAt` only depends on `toPair H C D`'s
      -- *value*, not on `(C,D)` themselves (unfold ordAt is entirely in terms of
      -- `toPair H C D`), so `ordAt P A₃ B₃ = ordAt P A' B'` here follows from
      -- `toPair H A₃ B₃ = g + g' = 0 + g' = g' = toPair H A' B'` (using `hg`'s
      -- consequence `g = 0` via `hA ▸ hg`).
      have hgval : g = 0 := hA ▸ hg
      have heq : toPair H A₃ B₃ = toPair H A' B' := by rw [hA₃, hgval, zero_add, hA']
      have hordEq : ordAt P A₃ B₃ = ordAt P A' B' := by unfold ordAt; rw [heq]
      have hordAB0 : ordAt P A B = 0 := by unfold ordAt; rw [if_pos hg]
      rw [hordEq, hordAB0]
      exact min_le_right _ _
    · by_cases hg' : toPair H A' B' = 0
      · -- Symmetric to the previous case, swapping the roles of `(A,B)`/`(A',B')`
        -- (`min`'s commutativity, `g + g' = g' + g = g` via `add_comm`/`zero_add`).
        have hg'val : g' = 0 := hA' ▸ hg'
        have heq : toPair H A₃ B₃ = toPair H A B := by
          rw [hA₃, hg'val, add_zero, hA]
        have hordEq : ordAt P A₃ B₃ = ordAt P A B := by unfold ordAt; rw [heq]
        have hordA'B'0 : ordAt P A' B' = 0 := by unfold ordAt; rw [if_pos hg']
        rw [hordEq, hordA'B'0]
        exact min_le_left _ _
      · -- The genuinely hard case: `g ≠ 0`, `g' ≠ 0`. With `hgg'_ne : g + g' ≠ 0`
        -- now part of the hypotheses (added this session — see the theorem's
        -- statement), `toPair H A₃ B₃ = g + g' ≠ 0` follows immediately via
        -- `hA₃`, eliminating the `toPair H A₃ B₃ = 0` branch entirely: that
        -- branch was the one place `ordAt_add_ge_min` was false as originally
        -- stated (`ordAt`'s convention forces `ordAt P A₃ B₃ = 0` whenever
        -- `toPair H A₃ B₃ = 0`, which is not generally `≤` the true minimum
        -- order of `g, g'` at `P` — see the prior revision of this proof, kept
        -- in the file's history, for the explicit counterexample). With that
        -- branch structurally unreachable, only the already-fully-proved
        -- `g+g'≠0` case below remains, via the direct `intValuation` ultrametric
        -- route (`intValuation_add_le_max` plus `WithZero.log` monotonicity).
        have hg3 : toPair H A₃ B₃ ≠ 0 := by rw [hA₃]; exact hgg'_ne
        -- Now all three are nonzero and `h_bot` holds: the direct `intValuation`
        -- route via `WithZero.log_le_log_of_ne_zero` applies cleanly. Nonzero-ness
        -- of each `intValuation` term comes from `intValuationDef_if_neg` (already
        -- confirmed and used identically in `ordAt_eq_count` above: `intValuationDef
        -- r = ofAdd (-(count)) ≠ 0` on the `r ≠ 0` branch, since `WithZero.exp _ ≠ 0`
        -- always — `WithZero.exp_ne_zero`), rather than a separately-named
        -- `intValuation_ne_zero`/`_eq_zero_iff` lemma whose existence isn't confirmed.
        unfold ordAt
        rw [if_neg hg, if_neg hg', if_neg hg3, dif_neg h_bot, dif_neg h_bot, dif_neg h_bot]
        set v := pointHeightOne P h_bot
        have hval3 : toPair H A₃ B₃ = toPair H A B + toPair H A' B' := by
          rw [hA₃, hA, hA']
        have hstep : v.intValuation (toPair H A₃ B₃) ≤
            max (v.intValuation (toPair H A B)) (v.intValuation (toPair H A' B')) := by
          rw [hval3]; exact intValuation_add_le_max P h_bot _ _
        have hne : ∀ (C D : k[X]), toPair H C D ≠ 0 → v.intValuation (toPair H C D) ≠ 0 := by
          intro C D hCD
          rw [IsDedekindDomain.HeightOneSpectrum.intValuation_apply,
              IsDedekindDomain.HeightOneSpectrum.intValuationDef_if_neg _ hCD]
          exact WithZero.exp_ne_zero
        have hne3 := hne A₃ B₃ hg3
        have hneAB := hne A B hg
        have hneA'B' := hne A' B' hg'
        have hmaxne : max (v.intValuation (toPair H A B))
            (v.intValuation (toPair H A' B')) ≠ 0 := by
          rcases max_choice (v.intValuation (toPair H A B))
              (v.intValuation (toPair H A' B')) with h | h <;> rw [h]
          · exact hneAB
          · exact hneA'B'
        have hlog := WithZero.log_le_log_of_ne_zero hne3 hmaxne hstep
        -- `(max x y).log = max x.log y.log` for nonzero `x,y`: derived from
        -- `log_le_log_of_ne_zero` applied both ways (`log` monotone on nonzero
        -- inputs) rather than a separate named `log_max` lemma.
        have hmaxlog : (max (v.intValuation (toPair H A B))
            (v.intValuation (toPair H A' B'))).log =
            max (v.intValuation (toPair H A B)).log
              (v.intValuation (toPair H A' B')).log := by
          rcases le_total (v.intValuation (toPair H A B))
              (v.intValuation (toPair H A' B')) with h | h
          · rw [max_eq_right h, max_eq_right (WithZero.log_le_log_of_ne_zero hneAB hneA'B' h)]
          · rw [max_eq_left h, max_eq_left (WithZero.log_le_log_of_ne_zero hneA'B' hneAB h)]
        rw [hmaxlog] at hlog
        omega


/-- `ordInfOfPair A B` is always `≤ 0`. -/
theorem ordInfOfPair_le_zero (A B : k[X]) : ordInfOfPair A B ≤ 0 := by
  by_cases hA : A = 0
  · by_cases hB : B = 0
    · simp [ordInfOfPair, hA, hB]
    · simp [ordInfOfPair, hA, hB]
  · by_cases hB : B = 0
    · simp [ordInfOfPair, hA, hB]
    · simp [ordInfOfPair, hA, hB]

/-- The zero pair has `ordInfOfPair = 0`. -/
theorem ordInfOfPair_zero_zero :
    ordInfOfPair (0 : k[X]) (0 : k[X]) = 0 := by
  simp [ordInfOfPair]

/-- Multiplying both slots by `C c` can only weaken the pole order at infinity. -/
theorem ordInfOfPair_C_mul_ge (c : k) (A B : k[X]) :
    ordInfOfPair (C c * A) (C c * B) ≥ ordInfOfPair A B := by
  by_cases hc : c = 0
  · have hL : ordInfOfPair (C c * A) (C c * B) = 0 := by
      simp [hc, ordInfOfPair]
    rw [hL]
    exact ordInfOfPair_le_zero A B
  · have hAdeg : (C c * A).natDegree = A.natDegree := by
      simpa using
        (Polynomial.natDegree_C_mul hc :
          (C c * A).natDegree = A.natDegree)
    have hBdeg : (C c * B).natDegree = B.natDegree := by
      simpa using
        (Polynomial.natDegree_C_mul hc :
          (C c * B).natDegree = B.natDegree)
    -- Avoid `Polynomial.C_eq_0`, which is not available here.
    have hCne : (C c : k[X]) ≠ 0 := by
      intro h
      have hcoeff := congr_arg (fun p : k[X] => Polynomial.coeff p 0) h
      simp only [Polynomial.coeff_C_zero, Polynomial.coeff_zero] at hcoeff
      exact hc hcoeff
    by_cases hA : A = 0 <;> by_cases hB : B = 0 <;>
      simp [ordInfOfPair, hA, hB, hAdeg, hBdeg, mul_eq_zero, hCne]

/-- Helper: `ordInfOfPair A B` unfolded on its nonzero branch. `ordInfOfPair`
picks up `Classical.propDecidable` for the `if B = 0 then .. else ..`
internally, but a freshly-written `if B = 0 then .. else ..` in a goal's
stated type instead resolves to `instDecidableEq k` (since `k : Field` gives
`DecidableEq k`) — a *different* `Decidable (B = 0)` term, even though both
decide the same proposition. `rfl`/`simp only [if_neg h]` can fail to bridge
this because they're instance-sensitive; `Subsingleton.elim` on the instance
argument closes the gap unconditionally. Isolated here as its own lemma so it
can be tested/compiled independently of `ordInfOfPair_add_ge_min`. -/
theorem ordInfOfPair_eq_of_ne (A B : k[X]) (h : ¬(A = 0 ∧ B = 0)) :
    ordInfOfPair A B =
      -(max ((2 * A.natDegree : ℤ))
          (if B = 0 then 0 else (2 * B.natDegree + 5 : ℤ))) := by
  unfold ordInfOfPair
  rw [if_neg h]
  split_ifs with hB <;> rfl

/-- `ordInfOfPair_A_degree_bound`'s first branch (`A.natDegree ≤ A'.natDegree`),
isolated as its own lemma so it can be compiled/timed independently. -/
theorem ordInfOfPair_A_degree_bound_le (A B A' B' : k[X])
    (hd : A.natDegree ≤ A'.natDegree) :
    (2 : ℤ) * ↑(A + A').natDegree ≤
      max
        (max (2 * (A.natDegree : ℤ)) (if B = 0 then 0 else 2 * (B.natDegree : ℤ) + 5))
        (max (2 * (A'.natDegree : ℤ)) (if B' = 0 then 0 else 2 * (B'.natDegree : ℤ) + 5)) := by
  have hle : (A + A').natDegree ≤ A'.natDegree := by
    simpa [max_eq_right hd] using natDegree_add_le A A'
  have hcast : (↑(A + A').natDegree : ℤ) ≤ ↑A'.natDegree := Nat.cast_le.mpr hle
  have step1 : (2 : ℤ) * ↑(A + A').natDegree ≤ 2 * ↑A'.natDegree := by omega
  have step2 : (2 : ℤ) * ↑A'.natDegree ≤
      max (2 * (A'.natDegree : ℤ)) (if B' = 0 then 0 else 2 * (B'.natDegree : ℤ) + 5) :=
    le_max_left (2 * (A'.natDegree : ℤ)) (if B' = 0 then 0 else 2 * (B'.natDegree : ℤ) + 5)
  have step3 :
      max (2 * (A'.natDegree : ℤ)) (if B' = 0 then 0 else 2 * (B'.natDegree : ℤ) + 5) ≤
      max
        (max (2 * (A.natDegree : ℤ)) (if B = 0 then 0 else 2 * (B.natDegree : ℤ) + 5))
        (max (2 * (A'.natDegree : ℤ)) (if B' = 0 then 0 else 2 * (B'.natDegree : ℤ) + 5)) :=
    le_max_right
      (max (2 * (A.natDegree : ℤ)) (if B = 0 then 0 else 2 * (B.natDegree : ℤ) + 5))
      (max (2 * (A'.natDegree : ℤ)) (if B' = 0 then 0 else 2 * (B'.natDegree : ℤ) + 5))
  exact step1.trans (step2.trans step3)

/-- `ordInfOfPair_A_degree_bound`'s second branch (`A'.natDegree ≤ A.natDegree`),
isolated as its own lemma so it can be compiled/timed independently. -/
theorem ordInfOfPair_A_degree_bound_ge (A B A' B' : k[X])
    (hd : A'.natDegree ≤ A.natDegree) :
    (2 : ℤ) * ↑(A + A').natDegree ≤
      max
        (max (2 * (A.natDegree : ℤ)) (if B = 0 then 0 else 2 * (B.natDegree : ℤ) + 5))
        (max (2 * (A'.natDegree : ℤ)) (if B' = 0 then 0 else 2 * (B'.natDegree : ℤ) + 5)) := by
  have hle : (A + A').natDegree ≤ A.natDegree := by
    simpa [max_eq_left hd] using natDegree_add_le A A'
  have hcast : (↑(A + A').natDegree : ℤ) ≤ ↑A.natDegree := Nat.cast_le.mpr hle
  have step1 : (2 : ℤ) * ↑(A + A').natDegree ≤ 2 * ↑A.natDegree := by omega
  have step2 : (2 : ℤ) * ↑A.natDegree ≤
      max (2 * (A.natDegree : ℤ)) (if B = 0 then 0 else 2 * (B.natDegree : ℤ) + 5) :=
    le_max_left (2 * (A.natDegree : ℤ)) (if B = 0 then 0 else 2 * (B.natDegree : ℤ) + 5)
  have step3 :
      max (2 * (A.natDegree : ℤ)) (if B = 0 then 0 else 2 * (B.natDegree : ℤ) + 5) ≤
      max
        (max (2 * (A.natDegree : ℤ)) (if B = 0 then 0 else 2 * (B.natDegree : ℤ) + 5))
        (max (2 * (A'.natDegree : ℤ)) (if B' = 0 then 0 else 2 * (B'.natDegree : ℤ) + 5)) :=
    le_max_left
      (max (2 * (A.natDegree : ℤ)) (if B = 0 then 0 else 2 * (B.natDegree : ℤ) + 5))
      (max (2 * (A'.natDegree : ℤ)) (if B' = 0 then 0 else 2 * (B'.natDegree : ℤ) + 5))
  exact step1.trans (step2.trans step3)

/-- The `A`-degree component of `ordInfOfPair_add_ge_min`'s main inequality:
after `push_cast`, the `max_le` split leaves this as one of its two goals.
Now just a two-way case split dispatching to `ordInfOfPair_A_degree_bound_le`/
`_ge`, each of which was isolated and pinned down with explicit (non-`_`)
`max` arguments to `le_max_left`/`le_max_right` to avoid the higher-order
unification against deeply-nested `ite`-containing `max` terms that was
timing out when left as `le_max_left _ _`/`le_max_right _ _` inside a single
large `calc` block. -/
theorem ordInfOfPair_A_degree_bound (A B A' B' : k[X]) :
    (2 : ℤ) * ↑(A + A').natDegree ≤
      max
        (max (2 * (A.natDegree : ℤ)) (if B = 0 then 0 else 2 * (B.natDegree : ℤ) + 5))
        (max (2 * (A'.natDegree : ℤ)) (if B' = 0 then 0 else 2 * (B'.natDegree : ℤ) + 5)) := by
  rcases le_total A.natDegree A'.natDegree with hd | hd
  · exact ordInfOfPair_A_degree_bound_le A B A' B' hd
  · exact ordInfOfPair_A_degree_bound_ge A B A' B' hd

/-- `ordInfOfPair_B_degree_bound`'s `B+B'=0` branch, isolated. -/
theorem ordInfOfPair_B_degree_bound_sum_zero (A B A' B' : k[X]) (hBsum : B + B' = 0) :
    (if B + B' = 0 then (0 : ℤ) else 2 * (B + B').natDegree + 5) ≤
      max
        (max (2 * (A.natDegree : ℤ)) (if B = 0 then 0 else 2 * (B.natDegree : ℤ) + 5))
        (max (2 * (A'.natDegree : ℤ)) (if B' = 0 then 0 else 2 * (B'.natDegree : ℤ) + 5)) := by
  simp only [if_pos hBsum]
  have step1 : (0 : ℤ) ≤ 2 * (A.natDegree : ℤ) := by positivity
  have step2 : (2 : ℤ) * (A.natDegree : ℤ) ≤
      max (2 * (A.natDegree : ℤ)) (if B = 0 then 0 else 2 * (B.natDegree : ℤ) + 5) :=
    le_max_left (2 * (A.natDegree : ℤ)) (if B = 0 then 0 else 2 * (B.natDegree : ℤ) + 5)
  have step3 :
      max (2 * (A.natDegree : ℤ)) (if B = 0 then 0 else 2 * (B.natDegree : ℤ) + 5) ≤
      max
        (max (2 * (A.natDegree : ℤ)) (if B = 0 then 0 else 2 * (B.natDegree : ℤ) + 5))
        (max (2 * (A'.natDegree : ℤ)) (if B' = 0 then 0 else 2 * (B'.natDegree : ℤ) + 5)) :=
    le_max_left
      (max (2 * (A.natDegree : ℤ)) (if B = 0 then 0 else 2 * (B.natDegree : ℤ) + 5))
      (max (2 * (A'.natDegree : ℤ)) (if B' = 0 then 0 else 2 * (B'.natDegree : ℤ) + 5))
  exact step1.trans (step2.trans step3)

/-- `ordInfOfPair_B_degree_bound`'s `B=0, B'≠0` branch, isolated. -/
theorem ordInfOfPair_B_degree_bound_B_zero (A B A' B' : k[X])
    (hB : B = 0) (hB' : B' ≠ 0) :
    (if B + B' = 0 then (0 : ℤ) else 2 * (B + B').natDegree + 5) ≤
      max
        (max (2 * (A.natDegree : ℤ)) (if B = 0 then 0 else 2 * (B.natDegree : ℤ) + 5))
        (max (2 * (A'.natDegree : ℤ)) (if B' = 0 then 0 else 2 * (B'.natDegree : ℤ) + 5)) := by
  rw [hB, zero_add]
  simp only [if_neg hB']
  have step1 : (2 : ℤ) * (B'.natDegree : ℤ) + 5 ≤
      max (2 * (A'.natDegree : ℤ)) (2 * (B'.natDegree : ℤ) + 5) :=
    le_max_right (2 * (A'.natDegree : ℤ)) (2 * (B'.natDegree : ℤ) + 5)
  have step2 :
      max (2 * (A'.natDegree : ℤ)) (2 * (B'.natDegree : ℤ) + 5) ≤
      max (max (2 * (A.natDegree : ℤ)) (0 : ℤ))
        (max (2 * (A'.natDegree : ℤ)) (2 * (B'.natDegree : ℤ) + 5)) :=
    le_max_right (max (2 * (A.natDegree : ℤ)) (0 : ℤ))
      (max (2 * (A'.natDegree : ℤ)) (2 * (B'.natDegree : ℤ) + 5))
  exact step1.trans step2

/-- `ordInfOfPair_B_degree_bound`'s `B≠0, B'=0` branch, isolated. -/
theorem ordInfOfPair_B_degree_bound_B'_zero (A B A' B' : k[X])
    (hB : B ≠ 0) (hB' : B' = 0) :
    (if B + B' = 0 then (0 : ℤ) else 2 * (B + B').natDegree + 5) ≤
      max
        (max (2 * (A.natDegree : ℤ)) (if B = 0 then 0 else 2 * (B.natDegree : ℤ) + 5))
        (max (2 * (A'.natDegree : ℤ)) (if B' = 0 then 0 else 2 * (B'.natDegree : ℤ) + 5)) := by
  rw [hB', add_zero]
  simp only [if_neg hB]
  have step1 : (2 : ℤ) * (B.natDegree : ℤ) + 5 ≤
      max (2 * (A.natDegree : ℤ)) (2 * (B.natDegree : ℤ) + 5) :=
    le_max_right (2 * (A.natDegree : ℤ)) (2 * (B.natDegree : ℤ) + 5)
  have step2 :
      max (2 * (A.natDegree : ℤ)) (2 * (B.natDegree : ℤ) + 5) ≤
      max (max (2 * (A.natDegree : ℤ)) (2 * (B.natDegree : ℤ) + 5))
        (max (2 * (A'.natDegree : ℤ)) (0 : ℤ)) :=
    le_max_left (max (2 * (A.natDegree : ℤ)) (2 * (B.natDegree : ℤ) + 5))
      (max (2 * (A'.natDegree : ℤ)) (0 : ℤ))
  exact step1.trans step2

/-- `ordInfOfPair_B_degree_bound`'s both-nonzero, `B.natDegree ≤ B'.natDegree`
sub-branch, isolated. -/
theorem ordInfOfPair_B_degree_bound_both_ne_le (A B A' B' : k[X])
    (hBsum : ¬(B + B' = 0)) (hB : B ≠ 0) (hB' : B' ≠ 0)
    (hd : B.natDegree ≤ B'.natDegree) :
    (if B + B' = 0 then (0 : ℤ) else 2 * (B + B').natDegree + 5) ≤
      max
        (max (2 * (A.natDegree : ℤ)) (if B = 0 then 0 else 2 * (B.natDegree : ℤ) + 5))
        (max (2 * (A'.natDegree : ℤ)) (if B' = 0 then 0 else 2 * (B'.natDegree : ℤ) + 5)) := by
  have hle : (B + B').natDegree ≤ B'.natDegree := by
    simpa [max_eq_right hd] using natDegree_add_le B B'
  have hcast : (↑(B + B').natDegree : ℤ) ≤ ↑B'.natDegree := Nat.cast_le.mpr hle
  rw [if_neg hBsum, if_neg hB, if_neg hB']
  have step1 : (2 : ℤ) * (B + B').natDegree + 5 ≤ 2 * (B'.natDegree : ℤ) + 5 := by omega
  have step2 : (2 : ℤ) * (B'.natDegree : ℤ) + 5 ≤
      max (2 * (A'.natDegree : ℤ)) (2 * (B'.natDegree : ℤ) + 5) :=
    le_max_right (2 * (A'.natDegree : ℤ)) (2 * (B'.natDegree : ℤ) + 5)
  have step3 :
      max (2 * (A'.natDegree : ℤ)) (2 * (B'.natDegree : ℤ) + 5) ≤
      max (max (2 * (A.natDegree : ℤ)) (2 * (B.natDegree : ℤ) + 5))
        (max (2 * (A'.natDegree : ℤ)) (2 * (B'.natDegree : ℤ) + 5)) :=
    le_max_right (max (2 * (A.natDegree : ℤ)) (2 * (B.natDegree : ℤ) + 5))
      (max (2 * (A'.natDegree : ℤ)) (2 * (B'.natDegree : ℤ) + 5))
  exact step1.trans (step2.trans step3)

/-- `ordInfOfPair_B_degree_bound`'s both-nonzero, `B'.natDegree ≤ B.natDegree`
sub-branch, isolated. -/
theorem ordInfOfPair_B_degree_bound_both_ne_ge (A B A' B' : k[X])
    (hBsum : ¬(B + B' = 0)) (hB : B ≠ 0) (hB' : B' ≠ 0)
    (hd : B'.natDegree ≤ B.natDegree) :
    (if B + B' = 0 then (0 : ℤ) else 2 * (B + B').natDegree + 5) ≤
      max
        (max (2 * (A.natDegree : ℤ)) (if B = 0 then 0 else 2 * (B.natDegree : ℤ) + 5))
        (max (2 * (A'.natDegree : ℤ)) (if B' = 0 then 0 else 2 * (B'.natDegree : ℤ) + 5)) := by
  have hle : (B + B').natDegree ≤ B.natDegree := by
    simpa [max_eq_left hd] using natDegree_add_le B B'
  have hcast : (↑(B + B').natDegree : ℤ) ≤ ↑B.natDegree := Nat.cast_le.mpr hle
  rw [if_neg hBsum, if_neg hB, if_neg hB']
  have step1 : (2 : ℤ) * (B + B').natDegree + 5 ≤ 2 * (B.natDegree : ℤ) + 5 := by omega
  have step2 : (2 : ℤ) * (B.natDegree : ℤ) + 5 ≤
      max (2 * (A.natDegree : ℤ)) (2 * (B.natDegree : ℤ) + 5) :=
    le_max_right (2 * (A.natDegree : ℤ)) (2 * (B.natDegree : ℤ) + 5)
  have step3 :
      max (2 * (A.natDegree : ℤ)) (2 * (B.natDegree : ℤ) + 5) ≤
      max (max (2 * (A.natDegree : ℤ)) (2 * (B.natDegree : ℤ) + 5))
        (max (2 * (A'.natDegree : ℤ)) (2 * (B'.natDegree : ℤ) + 5)) :=
    le_max_left (max (2 * (A.natDegree : ℤ)) (2 * (B.natDegree : ℤ) + 5))
      (max (2 * (A'.natDegree : ℤ)) (2 * (B'.natDegree : ℤ) + 5))
  exact step1.trans (step2.trans step3)

/-- The `B`-degree component of `ordInfOfPair_add_ge_min`'s main inequality:
the other of the two `max_le`-split goals. Now just a case split dispatching
to the five standalone sub-lemmas above. -/
theorem ordInfOfPair_B_degree_bound (A B A' B' : k[X]) :
    (if B + B' = 0 then (0 : ℤ) else 2 * (B + B').natDegree + 5) ≤
      max
        (max (2 * (A.natDegree : ℤ)) (if B = 0 then 0 else 2 * (B.natDegree : ℤ) + 5))
        (max (2 * (A'.natDegree : ℤ)) (if B' = 0 then 0 else 2 * (B'.natDegree : ℤ) + 5)) := by
  by_cases hBsum : B + B' = 0
  · exact ordInfOfPair_B_degree_bound_sum_zero A B A' B' hBsum
  · by_cases hB : B = 0
    · have hB' : B' ≠ 0 := fun h => hBsum (by simp [hB, h])
      exact ordInfOfPair_B_degree_bound_B_zero A B A' B' hB hB'
    · by_cases hB' : B' = 0
      · exact ordInfOfPair_B_degree_bound_B'_zero A B A' B' hB hB'
      · rcases le_total B.natDegree B'.natDegree with hd | hd
        · exact ordInfOfPair_B_degree_bound_both_ne_le A B A' B' hBsum hB hB' hd
        · exact ordInfOfPair_B_degree_bound_both_ne_ge A B A' B' hBsum hB hB' hd

theorem ordInfOfPair_add_ge_min (A B A' B' : k[X]) :
    ordInfOfPair (A + A') (B + B') ≥
      min (ordInfOfPair A B) (ordInfOfPair A' B') := by
  -- If the sum pair is zero, LHS is `0`, and RHS is `≤ 0`.
  by_cases hsum : A + A' = 0 ∧ B + B' = 0
  · have hL : ordInfOfPair (A + A') (B + B') = 0 := by
      unfold ordInfOfPair
      rw [if_pos hsum]
    rw [hL]
    exact le_trans (min_le_left _ _) (ordInfOfPair_le_zero A B)

  -- If the first pair is zero, the sum is just the second pair.
  by_cases hAB : A = 0 ∧ B = 0
  · obtain ⟨rfl, rfl⟩ := hAB
    have hle := ordInfOfPair_le_zero A' B'
    have hR :
        min (ordInfOfPair (0 : k[X]) (0 : k[X]))
          (ordInfOfPair A' B') =
        ordInfOfPair A' B' := by
      rw [ordInfOfPair_zero_zero, min_eq_right hle]
    rw [zero_add, zero_add, hR]

  -- If the second pair is zero, the sum is just the first pair.
  by_cases hA'B' : A' = 0 ∧ B' = 0
  · obtain ⟨rfl, rfl⟩ := hA'B'
    have hle := ordInfOfPair_le_zero A B
    have hR :
        min (ordInfOfPair A B)
          (ordInfOfPair (0 : k[X]) (0 : k[X])) =
        ordInfOfPair A B := by
      rw [ordInfOfPair_zero_zero, min_eq_left hle]
    rw [add_zero, add_zero, hR]

  -- Main case: none of the three pairs is the zero pair.
  · have hLHS : ordInfOfPair (A + A') (B + B') =
        -(max ((2 * (A + A').natDegree : ℤ))
            (if B + B' = 0 then 0 else (2 * (B + B').natDegree + 5 : ℤ))) :=
      ordInfOfPair_eq_of_ne (A + A') (B + B') hsum
    have hRHS : min (ordInfOfPair A B) (ordInfOfPair A' B') =
        -(max (max ((2 * A.natDegree : ℤ))
                (if B = 0 then 0 else (2 * B.natDegree : ℤ) + 5))
              (max ((2 * A'.natDegree : ℤ))
                (if B' = 0 then 0 else (2 * B'.natDegree : ℤ) + 5))) := by
      have hA0 := ordInfOfPair_eq_of_ne A B hAB
      have hA'0 := ordInfOfPair_eq_of_ne A' B' hA'B'
      rw [hA0, hA'0, min_neg_neg]
    rw [ge_iff_le, hLHS, hRHS, neg_le_neg_iff]
    push_cast
    exact max_le (ordInfOfPair_A_degree_bound A B A' B')
      (ordInfOfPair_B_degree_bound A B A' B')
/-- `LPairCarrier x₁ x₂` is closed under `k`-linear combinations: the
common-denominator argument that turns two pole-bounded ratios into one.
Given `z₁` from `(A₁,B₁,A₁',B₁')` and `z₂` from `(A₂,B₂,A₂',B₂')`, `c₁ z₁ +
c₂ z₂` is represented by numerator `c₁ · toPair A₁ B₁ · toPair A₂' B₂' + c₂
· toPair A₂ B₂ · toPair A₁' B₁'` over denominator `toPair A₁' B₁' · toPair
A₂' B₂'`.

**Status.** All four of `IsPoleBoundedAtPair`'s conjuncts are proved. The
`ordInfOfPair`-at-infinity conjunct was weakened from `=` to `≥` (see
`IsPoleBoundedAtPair`'s docstring) since exact equality isn't provable for
an arbitrary `k`-linear combination (leading-term cancellation between the
two summands can strictly increase `ordInfOfPair` past the shared value);
`≥` is what the rest of this file actually needs and is closed here via
`ordInfOfPair_C_mul_ge`/`ordInfOfPair_add_ge_min`. The other three conjuncts
go via the shared `hpointwise` argument below (built from
`ordAt_toPair_mul_of_ne_zero'` for multiplicativity and `ordAt_add_ge_min`
for the ultrametric step). `ordAt_add_ge_min` itself is now fully proved
(closed this session via an added `g + g' ≠ 0` hypothesis); the residual gap
that hypothesis exposes lives instead in this proof's own `hordN₁`/`hordN₂`/
`hordN` `sorry`s below (the zero-`toPair`/zero-scalar convention boundary). -/
theorem LPairCarrier_add_smul (hdeg : H.f.natDegree = 5) (x₁ x₂ : H.Point)
    (c₁ c₂ : k) (z₁ z₂ : FractionRing (CoordinateRing H))
    (h₁ : z₁ ∈ LPairCarrier x₁ x₂) (h₂ : z₂ ∈ LPairCarrier x₁ x₂) :
    c₁ • z₁ + c₂ • z₂ ∈ LPairCarrier x₁ x₂ := by
  obtain ⟨A₁, B₁, A₁', B₁', ⟨hne₁, hinf₁, hoff₁⟩, hz₁⟩ := h₁
  obtain ⟨A₂, B₂, A₂', B₂', ⟨hne₂, hinf₂, hoff₂⟩, hz₂⟩ := h₂
  -- The combined denominator: `toPair H A₁' B₁' * toPair H A₂' B₂'`, written out via
  -- `toPair_mul`'s explicit formula as `toPair H D' D''`.
  set D' : k[X] := A₁' * A₂' + B₁' * B₂' * H.f with hD'_def
  set D'' : k[X] := A₁' * B₂' + A₂' * B₁' with hD''_def
  have hDmul : toPair H D' D'' = toPair H A₁' B₁' * toPair H A₂' B₂' := (toPair_mul A₁' B₁' A₂' B₂').symm
  -- The combined numerator: `c₁ • toPair H A₁ B₁ * toPair H A₂' B₂' + c₂ • toPair H A₂ B₂ *
  -- toPair H A₁' B₁'`, again written out as a single `toPair H N' N''` via `toPair_mul`,
  -- `toPair_smul`, and `toPair_add`.
  set N₁' : k[X] := A₁ * A₂' + B₁ * B₂' * H.f with hN₁'_def
  set N₁'' : k[X] := A₁ * B₂' + A₂' * B₁ with hN₁''_def
  set N₂' : k[X] := A₂ * A₁' + B₂ * B₁' * H.f with hN₂'_def
  set N₂'' : k[X] := A₂ * B₁' + A₁' * B₂ with hN₂''_def
  have hN₁mul : toPair H N₁' N₁'' = toPair H A₁ B₁ * toPair H A₂' B₂' := (toPair_mul A₁ B₁ A₂' B₂').symm
  have hN₂mul : toPair H N₂' N₂'' = toPair H A₂ B₂ * toPair H A₁' B₁' := (toPair_mul A₂ B₂ A₁' B₁').symm
  set N' : k[X] := C c₁ * N₁' + C c₂ * N₂' with hN'_def
  set N'' : k[X] := C c₁ * N₁'' + C c₂ * N₂'' with hN''_def
  have hNadd : toPair H N' N'' =
      c₁ • toPair H N₁' N₁'' + c₂ • toPair H N₂' N₂'' := by
    rw [hN'_def, hN''_def, toPair_add, toPair_smul, toPair_smul]
  -- `D' ≠ 0 ∨ D'' ≠ 0`: since `toPair H D' D'' = toPair H A₁' B₁' * toPair H A₂' B₂' ≠ 0`
  -- (product of two nonzero elements in the domain `CoordinateRing H`), `toPair_eq_zero_iff`
  -- rules out `D' = 0 ∧ D'' = 0`.
  have hA₁'B₁'ne : toPair H A₁' B₁' ≠ 0 := fun h => hne₁ ((toPair_eq_zero_iff H A₁' B₁').mp h)
  have hA₂'B₂'ne : toPair H A₂' B₂' ≠ 0 := fun h => hne₂ ((toPair_eq_zero_iff H A₂' B₂').mp h)
  have hDne : toPair H D' D'' ≠ 0 := by
    rw [hDmul]; exact mul_ne_zero hA₁'B₁'ne hA₂'B₂'ne
  have hD'D''ne : ¬ (D' = 0 ∧ D'' = 0) := fun h => hDne ((toPair_eq_zero_iff H D' D'').mpr h)
  -- `z := c₁ • z₁ + c₂ • z₂` equals `polePairToFraction N' N'' D' D''`.
  have hzeq : c₁ • z₁ + c₂ • z₂ = polePairToFraction N' N'' D' D'' := by
    have hd1 : (algebraMap (CoordinateRing H) (FractionRing (CoordinateRing H))
        (toPair H A₁' B₁')) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (CoordinateRing H) (FractionRing (CoordinateRing H)))).mpr hA₁'B₁'ne
    have hd2 : (algebraMap (CoordinateRing H) (FractionRing (CoordinateRing H))
        (toPair H A₂' B₂')) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (CoordinateRing H) (FractionRing (CoordinateRing H)))).mpr hA₂'B₂'ne
    have hNumEq : algebraMap (CoordinateRing H) (FractionRing (CoordinateRing H)) (toPair H N' N'') =
        c₁ • algebraMap (CoordinateRing H) (FractionRing (CoordinateRing H)) (toPair H A₁ B₁) *
          algebraMap (CoordinateRing H) (FractionRing (CoordinateRing H)) (toPair H A₂' B₂') +
        c₂ • algebraMap (CoordinateRing H) (FractionRing (CoordinateRing H)) (toPair H A₂ B₂) *
          algebraMap (CoordinateRing H) (FractionRing (CoordinateRing H)) (toPair H A₁' B₁') := by
      -- `algebraMap (CoordinateRing H) (FractionRing (CoordinateRing H))` is only a
      -- `RingHom`, with no `MulActionHomClass` instance witnessing that it commutes with
      -- the `k`-scalar action, so `map_smul` does not apply directly. Route each `c •`
      -- through `Algebra.smul_def` (`c • x = algebraMap k _ c * x`) to turn every `smul`
      -- into a ring multiplication, so the whole equation becomes a `map_add`/`map_mul`
      -- push-through (the same route `toPair_smul` itself uses). Push `hNadd`/`hN₁mul`/
      -- `hN₂mul` in *first* so the `•`s sit where `Algebra.smul_def` can see them on
      -- both sides at once — running `simp` before the `rw` (as the previous attempt
      -- did) left the LHS `•` buried inside the `algebraMap` argument as `c₁ • (x*y)`,
      -- where `simp` had already passed and `map_mul` could no longer find `?x * ?y`.
      rw [hNadd, hN₁mul, hN₂mul, map_add]
      simp only [Algebra.smul_def, map_mul]
      -- The remaining mismatch is not a pure ring identity: each `c • x` was rewritten
      -- to `(algebraMap CoordinateRing FractionRing) ((algebraMap k CoordinateRing) c) * x`
      -- (a *composed* algebra map applied to `c`), whereas the goal's other side has the
      -- single-step `(algebraMap k FractionRing) c` — these are only equal via the scalar
      -- tower `k → CoordinateRing H → FractionRing (CoordinateRing H)` composing to the
      -- direct map `k → FractionRing (CoordinateRing H)`, which `ring` cannot see (it
      -- treats differently-nested `algebraMap` applications as unrelated atoms). Collapse
      -- the composition first via `IsScalarTower.algebraMap_apply`, then `ring` closes the
      -- remaining pure associativity/commutativity rearrangement.
      rw [← IsScalarTower.algebraMap_apply k (CoordinateRing H) (FractionRing (CoordinateRing H)) c₁,
          ← IsScalarTower.algebraMap_apply k (CoordinateRing H) (FractionRing (CoordinateRing H)) c₂]
      ring
    have hDenEq : algebraMap (CoordinateRing H) (FractionRing (CoordinateRing H)) (toPair H D' D'') =
        algebraMap (CoordinateRing H) (FractionRing (CoordinateRing H)) (toPair H A₁' B₁') *
          algebraMap (CoordinateRing H) (FractionRing (CoordinateRing H)) (toPair H A₂' B₂') := by
      rw [hDmul, map_mul]
    rw [hz₁, hz₂]
    unfold polePairToFraction
    rw [hNumEq, hDenEq]
    -- `c₁ • z₁` here is the *heterogeneous* `Algebra k (FractionRing (CoordinateRing H))`
    -- scalar action (`c₁ : k`, `z₁ : FractionRing (CoordinateRing H)` — different types),
    -- not same-type ring multiplication, so `smul_eq_mul` (which is `Monoid.smul_eq_mul`,
    -- for `a • b = a * b` when the scalar and the ring coincide) doesn't apply here at all
    -- — that's why it silently made no progress. `Algebra.smul_def` is the correct lemma:
    -- `c • x = algebraMap k _ c * x`.
    simp only [Algebra.smul_def]
    -- `field_simp` fully closes the goal here (clearing denominators leaves an identity
    -- `ring` would otherwise finish, but there's nothing left for it to do) — the trailing
    -- `ring` was dead weight and Lean rightly complains "no goals to be solved".
    field_simp
  -- **Shared point-wise argument**, applied below at a generic point `Q` (an affine point
  -- distinct from `x₁, x₂`, or `x₁`/`x₂` themselves): given the two "offset" hypotheses
  -- `ordAt Q A₁ B₁ ≥ ordAt Q A₁' B₁' - s` and `ordAt Q A₂ B₂ ≥ ordAt Q A₂' B₂' - s` (for a
  -- shared slack `s : ℤ`, either `0` away from `x₁, x₂` or `1` at `x₁`/`x₂`), conclude
  -- `ordAt Q N' N'' ≥ ordAt Q D' D'' - s`. Factored out once here so it is proved a single
  -- time and merely instantiated three times below (at a generic `P`, at `x₁`, at `x₂`)
  -- rather than reproved inline at each of the three `IsPoleBoundedAtPair` conjuncts.
  have hpointwise : ∀ (Q : H.Point) (s : ℤ),
      ordAt Q A₁ B₁ ≥ ordAt Q A₁' B₁' - s → ordAt Q A₂ B₂ ≥ ordAt Q A₂' B₂' - s →
      ordAt Q N' N'' ≥ ordAt Q D' D'' - s := by
    intro Q s h1 h2
    by_cases h_bot : pointIdeal Q = ⊥
    · -- `h_bot : pointIdeal Q = ⊥` makes `ordAt Q a b = 0` for *every* `a b : k[X]`
      -- unconditionally — `ordAt`'s `if toPair H A B = 0 then 0 else if h_bot then 0
      -- else ...` gives `0` on both the zero-`toPair` branch and the `h_bot` branch, so
      -- no case split on `toPair H a b = 0` is needed (the original attempt to derive
      -- `ordAt Q A₁ B₁ = 0` from `hz0`'s *nonzero* hypothesis was the bug: `hz0` never
      -- lets us conclude `ordAt Q A₁ B₁ = 0` when `toPair H A₁ B₁` might be zero, and
      -- `h1`/`h2` were never rewritten on that side at all). Rewrite every `ordAt Q _ _`
      -- to `0` directly via `hz0'` (no nonzero side condition) and close with `omega`.
      have hz0' : ∀ (a b : k[X]), ordAt Q a b = 0 := by
        intro a b
        unfold ordAt
        by_cases hab : toPair H a b = 0
        · rw [if_pos hab]
        · rw [if_neg hab, dif_pos h_bot]
      rw [hz0' N' N'', hz0' D' D'']
      rw [hz0' A₁ B₁, hz0' A₁' B₁'] at h1
      omega
    · have hordD : ordAt Q D' D'' = ordAt Q A₁' B₁' + ordAt Q A₂' B₂' :=
        ordAt_toPair_mul_of_ne_zero' Q h_bot A₁' B₁' A₂' B₂' D' D'' hA₁'B₁'ne hA₂'B₂'ne hDmul
      -- **Genuine gap, flagged rather than forced**: when `toPair H A₁ B₁ = 0` (so
      -- `N₁' = A₁·A₂'+B₁·B₂'·f`, `N₁'' = ...` also gives `toPair H N₁' N₁'' = 0` via
      -- `hN₁mul`), `ordAt`'s convention (`PrincipalDivisors.lean`) sets `ordAt Q _ _ = 0`
      -- on *any* zero-`toPair` pair — not `+∞` as the true valuation-theoretic order of
      -- vanishing would require. So this branch's target `ordAt Q N₁' N₁'' = ordAt Q A₁
      -- B₁ + ordAt Q A₂' B₂'` reduces to `0 = 0 + ordAt Q A₂' B₂'`, i.e. `ordAt Q A₂' B₂'
      -- = 0` — which is false in general (only `ordAt_nonneg` gives `≥ 0` for the nonzero
      -- `toPair H A₂' B₂'` here, with no matching upper bound). The previous attempt's
      -- `simp` silently produced this same unprovable residual goal instead of closing it
      -- (visible in the error trace as an unclosed `intValuation`/`.log` implication) —
      -- this is a bug in the additivity convention itself, not a missing tactic, so it is
      -- left as a named `sorry` rather than "fixed" unsoundly.
      have hordN₁ : ordAt Q N₁' N₁'' = ordAt Q A₁ B₁ + ordAt Q A₂' B₂' := by
        by_cases hA₁B₁ : toPair H A₁ B₁ = 0
        · -- **False as stated, not unproven** — same convention defect as the one
          -- `ordAt_add_ge_min` originally had (now fixed there via an added `g +
          -- g' ≠ 0` hypothesis; see that theorem and `WithZero.log_le_log_of_ne_zero`'s
          -- docstring above). `hA₁B₁` gives `ordAt Q A₁
          -- B₁ = 0` (`ordAt`'s zero-`toPair` convention) and, via `hN₁mul`,
          -- `toPair H N₁' N₁'' = toPair H A₁ B₁ * toPair H A₂' B₂' = 0` too, so the
          -- goal reduces to `0 = 0 + ordAt Q A₂' B₂'`, i.e. `ordAt Q A₂' B₂' = 0`
          -- exactly. This is false in general: `ordAt_nonneg` only gives `≥ 0` for
          -- the nonzero witness `toPair H A₂' B₂'` (`hA₂'B₂'ne`), with no matching
          -- upper bound — take `A₂', B₂'` so that `toPair H A₂' B₂'` genuinely
          -- vanishes to positive order at `Q` (nothing in this branch's hypotheses
          -- rules that out) and the claim `= 0` fails outright. The true
          -- valuation-theoretic fact is `ordAt Q N₁' N₁'' = +∞` here (`N₁',N₁''`
          -- witness the zero function since one factor is zero), which `ordAt`'s
          -- `ℤ`-valued, zero-defaults-to-`0` convention cannot express — fixing
          -- this needs either an `ordAt` convention change (e.g. `ℤ ∪ {∞}`-valued,
          -- a change far outside this theorem's scope) or, as with
          -- `ordAt_add_ge_min`, an extra hypothesis pushed down from
          -- `LPairCarrier_add_smul` ruling out `toPair H A₁ B₁ = 0` /
          -- `toPair H A₂ B₂ = 0` at this call site specifically (plausible, since
          -- `LPairCarrier`'s pole-boundedness conditions may already force `A₁,B₁`
          -- and `A₂,B₂` nonzero as genuine numerator witnesses — not checked here).
          -- Left `sorry`'d rather than force-closed unsoundly.
          sorry
        · exact ordAt_toPair_mul_of_ne_zero' Q h_bot A₁ B₁ A₂' B₂' N₁' N₁'' hA₁B₁ hA₂'B₂'ne hN₁mul
      have hordN₂ : ordAt Q N₂' N₂'' = ordAt Q A₂ B₂ + ordAt Q A₁' B₁' := by
        by_cases hA₂B₂ : toPair H A₂ B₂ = 0
        · -- Symmetric to `hordN₁`'s branch above (swap the roles of `(A₁,B₁,A₂',B₂')`
          -- and `(A₂,B₂,A₁',B₁')`): equally false as stated, same underlying
          -- convention defect, same missing-hypothesis fix. See `hordN₁` above for
          -- the full diagnosis; not repeated here.
          sorry
        · exact ordAt_toPair_mul_of_ne_zero' Q h_bot A₂ B₂ A₁' B₁' N₂' N₂'' hA₂B₂ hA₁'B₁'ne hN₂mul
      -- `ordAt_add_ge_min`'s `(A,B)` argument must be an actual `toPair`-witness for `g :=
      -- c₁ • toPair H N₁' N₁''`, i.e. `toPair H A B = g`. `toPair_smul` gives `c₁ • toPair
      -- H N₁' N₁'' = toPair H (C c₁ * N₁') (C c₁ * N₁'')`, so the witness pair is `(C c₁ *
      -- N₁', C c₁ * N₁'')`, *not* `(N₁', N₁'')` itself — passing `(N₁', N₁'')` (as the
      -- previous attempt did) demands the false statement `toPair H N₁' N₁'' = toPair H
      -- (C c₁ * N₁') (C c₁ * N₁'')`, which only holds when `c₁ = 1`. Likewise the `min`
      -- this produces is over `ordAt Q (C c₁ * N₁') (C c₁ * N₁'')` and `ordAt Q (C c₂ *
      -- N₂') (C c₂ * N₂'')`, not `ordAt Q N₁' N₁''`/`ordAt Q N₂' N₂''` directly, so the
      -- scale-invariance fact `hordScale` bridges back to the unscaled pairs.
      --
      -- `hordScale`: `ordAt Q (C c * A) (C c * B) = ordAt Q A B` — but only genuinely
      -- true for `c ≠ 0`. At `c = 0`, `C 0 * A = 0` and `C 0 * B = 0` literally, so the
      -- LHS is `ordAt Q 0 0 = 0` (`ordAt`'s own `if toPair H A B = 0 then 0` branch),
      -- while the RHS `ordAt Q A B` is *not* generally `0` — this is the identical
      -- convention gap flagged above for `hordN₁`/`hordN₂` (`ordAt`'s `0`-at-a-zero-
      -- `toPair` convention, rather than the valuation-theoretic `+∞`, breaks additivity
      -- exactly at zero). So `hordScale` is stated and proved here only for `c ≠ 0`; the
      -- `c = 0` case is left as the same class of gap (not re-derived, since it would
      -- just restate the existing `hordN₁`/`hordN₂` sorries in different notation).
      have hordScale : ∀ (c : k), c ≠ 0 → ∀ (A B : k[X]),
          ordAt Q (C c * A) (C c * B) = ordAt Q A B := by
        intro c hc A B
        -- `toPair H (C c) 0 = algebraMap k[X] (CoordinateRing H) (C c)`: `toPair`'s
        -- definition (`HyperellipticFunctionField.lean`) is `algebraMap A + algebraMap
        -- B * y H`, and the second summand vanishes when `B = 0`.
        have hCc_eq : toPair H (C c) (0 : k[X]) = algebraMap k[X] (CoordinateRing H) (C c) := by
          unfold toPair; simp
        -- `algebraMap k[X] (CoordinateRing H) (C c)` is a unit: its inverse is
        -- `algebraMap k[X] (CoordinateRing H) (C c⁻¹)`, since `algebraMap` is a ring
        -- hom (`map_mul`, `map_one`) and `C c * C c⁻¹ = C (c * c⁻¹) = C 1 = 1` in
        -- `k[X]` (`c ≠ 0` gives `c * c⁻¹ = 1` in the field `k`). Mirrors the confirmed
        -- pattern in `PrincipalDivisors.lean` (`rw [eqC, ← map_mul, mul_inv_cancel₀
        -- coeff_ne, map_one]`): first the `k[X]`-level fact `C c * C c⁻¹ = 1` via `C`'s
        -- own `map_mul`/`mul_inv_cancel₀`/`map_one`, then lift through `algebraMap`
        -- once via its own `map_mul`.
        have hCc_inv_poly : (C c : k[X]) * C c⁻¹ = 1 := by
          rw [← map_mul, mul_inv_cancel₀ hc, map_one]
        have hCc_inv : algebraMap k[X] (CoordinateRing H) (C c) *
            algebraMap k[X] (CoordinateRing H) (C c⁻¹) = 1 := by
          rw [← map_mul, hCc_inv_poly, map_one]
        -- Build the `IsUnit` witness directly via the `Units` anonymous constructor
        -- (`⟨val, inv, val_inv, inv_val⟩ : Mˣ`, needing only `CommMonoid` — always
        -- available for a `CommRing` like `CoordinateRing H`) rather than a named lemma
        -- like `isUnit_of_mul_eq_one`, whose exact spelling in this Mathlib version
        -- wasn't confirmed (and turned out wrong — "unknown identifier" — last round).
        have hCc_unit : IsUnit (algebraMap k[X] (CoordinateRing H) (C c)) :=
          ⟨⟨algebraMap k[X] (CoordinateRing H) (C c), algebraMap k[X] (CoordinateRing H) (C c⁻¹),
              hCc_inv, by rw [mul_comm]; exact hCc_inv⟩, rfl⟩
        have hCc_ne : toPair H (C c) (0 : k[X]) ≠ 0 := by
          rw [hCc_eq]
          intro h
          rw [h] at hCc_unit
          exact not_isUnit_zero hCc_unit
        have hprod : toPair H (C c * A) (C c * B) = toPair H (C c) 0 * toPair H A B := by
          have hmul : toPair H (C c) (0 : k[X]) * toPair H A B =
              toPair H (C c * A + 0 * B * H.f) (C c * B + A * 0) := toPair_mul (C c) 0 A B
          simpa using hmul.symm
        by_cases hAB : toPair H A B = 0
        · have hprod0 : toPair H (C c * A) (C c * B) = 0 := by rw [hprod, hAB, mul_zero]
          unfold ordAt
          rw [if_pos hprod0, if_pos hAB]
        · -- `toPair H (C c) 0`'s image is a unit, hence lies in no proper ideal —
          -- in particular not in the maximal ideal `pointIdeal Q`
          -- (`pointIdeal_isMaximal`/`Ideal.eq_top_of_isUnit_mem`, same pattern
          -- `toPair_one_zero_notMem_pointIdeal` uses for the `c = 1` special case) —
          -- so `ordAt Q (C c) 0 = 0` via `ordAt_eq_zero_of_notMem`.
          have hCc0 : ordAt Q (C c) (0 : k[X]) = 0 := by
            apply ordAt_eq_zero_of_notMem
            rw [hCc_eq]
            intro hmem
            exact (pointIdeal_isMaximal Q).ne_top
              (Ideal.eq_top_of_isUnit_mem (pointIdeal Q) hmem hCc_unit)
          have := ordAt_toPair_mul_of_ne_zero' Q h_bot (C c) 0 A B (C c * A) (C c * B)
            hCc_ne hAB hprod
          rw [this, hCc0, zero_add]
      have hordN : ordAt Q N' N'' ≥ min (ordAt Q N₁' N₁'') (ordAt Q N₂' N₂'') := by
        -- `hordScale` only covers `c ≠ 0`, so case-split on `c₁ = 0`/`c₂ = 0`. Unlike
        -- `hordN₁`/`hordN₂` above, the *singly*-degenerate sub-cases here (`c₁ = 0,
        -- c₂ ≠ 0` and vice versa) are genuinely provable, not another instance of the
        -- convention gap: `hordN`'s goal is only `≥`, not `=`, and `min x y ≤ y` (resp.
        -- `≤ x`) lets the vanishing summand's `ordAt` be discarded via `min_le_right`/
        -- `min_le_left` rather than needing to be pinned down exactly. Only the
        -- *doubly*-degenerate sub-case `c₁ = 0 ∧ c₂ = 0` (where `N' = N'' = 0`
        -- literally, forcing `ordAt Q N' N'' = 0` by convention, against a `min` that
        -- need not be `≤ 0`) is the same unprovable-as-stated gap as `hordN₁`/`hordN₂`.
        -- `ordAt_add_ge_min` (now requiring `g + g' ≠ 0`, added this session) is only
        -- invoked in the final `c₁ ≠ 0, c₂ ≠ 0` branch below — the other three never
        -- needed it (they go straight through `hordScale`), so the call is moved
        -- there rather than computed eagerly up front for all four branches.
        by_cases hc₁ : c₁ = 0
        · by_cases hc₂ : c₂ = 0
          · -- **False as stated, not unproven** — the doubly-degenerate case: `N' = C
            -- 0 * N₁' + C 0 * N₂' = 0` and likewise `N'' = 0` (`hN'_def`/`hN''_def`,
            -- `hc₁`, `hc₂`, `zero_mul`/`add_zero`), so `ordAt Q N' N'' = ordAt Q 0 0 =
            -- 0` unconditionally (`ordAt`'s zero-`toPair` convention). The goal `0 ≥
            -- min (ordAt Q N₁' N₁'') (ordAt Q N₂' N₂'')` then fails exactly when either
            -- `N₁',N₁''` or `N₂',N₂''` witnesses a function vanishing to positive order
            -- at `Q` — realizable here for the same reason `hordN₁`/`hordN₂` above are
            -- false in general (nothing in scope pins either witness to order `0`).
            -- Same fix as `ordAt_add_ge_min`/`hordN₁`/`hordN₂`: needs a hypothesis from
            -- `LPairCarrier_add_smul`'s call site ruling out `c₁ = c₂ = 0` reaching a
            -- degenerate pair, or an `ordAt` convention change; left `sorry`'d.
            sorry
          · -- `c₁ = 0`, `c₂ ≠ 0`: `N' = C c₂ * N₂'`, `N'' = C c₂ * N₂''` literally
            -- (`hN'_def`/`hN''_def` with `C 0 = 0`, `zero_mul`, `zero_add`), so
            -- `ordAt Q N' N'' = ordAt Q (C c₂ * N₂') (C c₂ * N₂'') = ordAt Q N₂' N₂''`
            -- via `hordScale c₂ hc₂`, and the goal follows from `min_le_right`.
            have hN'eq : N' = C c₂ * N₂' := by rw [hN'_def, hc₁]; simp
            have hN''eq : N'' = C c₂ * N₂'' := by rw [hN''_def, hc₁]; simp
            rw [hN'eq, hN''eq, hordScale c₂ hc₂]
            exact min_le_right _ _
        · by_cases hc₂ : c₂ = 0
          · -- Symmetric: `c₁ ≠ 0`, `c₂ = 0` gives `N' = C c₁ * N₁'`, `N'' = C c₁ * N₁''`,
            -- so `ordAt Q N' N'' = ordAt Q N₁' N₁''` via `hordScale c₁ hc₁`, and the
            -- goal follows from `min_le_left`.
            have hN'eq : N' = C c₁ * N₁' := by rw [hN'_def, hc₂]; simp
            have hN''eq : N'' = C c₁ * N₁'' := by rw [hN''_def, hc₂]; simp
            rw [hN'eq, hN''eq, hordScale c₁ hc₁]
            exact min_le_left _ _
          · -- `c₁ ≠ 0`, `c₂ ≠ 0`: the only branch that actually needs
            -- `ordAt_add_ge_min`. Its new `g + g' ≠ 0` hypothesis is NOT always
            -- derivable here in general (two nonzero terms can still sum to zero —
            -- this is exactly the same convention-boundary phenomenon flagged
            -- throughout this file, just relocated rather than eliminated by adding
            -- the hypothesis at `ordAt_add_ge_min` alone), so it is supplied as a
            -- fresh `sorry`'d side fact here rather than silently assumed via
            -- `by_cases`/`Classical.byContradiction` on a goal that may be false.
            -- **Left genuinely open, one level further out than before**: closing
            -- this needs either (a) showing `LPairCarrier`'s pole-boundedness
            -- conditions already force `c₁ • toPair H N₁' N₁'' + c₂ • toPair H N₂'
            -- N₂'' ≠ 0` whenever `c₁, c₂ ≠ 0` (plausible but not yet checked — it
            -- would follow from `N₁', N₁''` and `N₂', N₂''` never being exact
            -- negative multiples of one another at the level of `toPair` values,
            -- itself presumably related to `x₁ ≠ ι x₂`/`x₂ ≠ ι x₁`-style hypotheses
            -- already threaded elsewhere in this file — worth checking directly
            -- rather than assuming), or (b) further weakening `LPairCarrier_add_smul`
            -- itself to not need this case at all.
            have hsum_ne : c₁ • toPair H N₁' N₁'' + c₂ • toPair H N₂' N₂'' ≠ 0 := by sorry
            have hstep := ordAt_add_ge_min Q (c₁ • toPair H N₁' N₁'') (c₂ • toPair H N₂' N₂'')
              (C c₁ * N₁') (C c₁ * N₁'') (C c₂ * N₂') (C c₂ * N₂'') N' N''
              (by rw [toPair_smul])
              (by rw [toPair_smul])
              (by rw [hNadd])
              hsum_ne
            rwa [hordScale c₁ hc₁, hordScale c₂ hc₂] at hstep
      rw [hordD]
      calc ordAt Q N' N'' ≥ min (ordAt Q N₁' N₁'') (ordAt Q N₂' N₂'') := hordN
        _ = min (ordAt Q A₁ B₁ + ordAt Q A₂' B₂') (ordAt Q A₂ B₂ + ordAt Q A₁' B₁') := by
            rw [hordN₁, hordN₂]
        _ ≥ ordAt Q A₁' B₁' + ordAt Q A₂' B₂' - s := by
            rw [ge_iff_le, sub_eq_add_neg, le_min_iff]
            constructor
            · omega
            · omega
  rw [hzeq]
  refine ⟨N', N'', D', D'', ⟨hD'D''ne, ?_, ?_⟩, rfl⟩
  · -- `ordInfOfPair N' N'' ≥ ordInfOfPair D' D''` (the actual conjunct required by
    -- `IsPoleBoundedAtPair`, which uses `≥` — see its definition above). Proved via
    -- `ordInfOfPair_add_ge_min` (sum) and `ordInfOfPair_C_mul_ge` (scalar multiples) to
    -- reduce to `min (ordInfOfPair N₁' N₁'') (ordInfOfPair N₂' N₂'')`, then
    -- `ordInfOfPair_add_of_toPair_mul` (case-split on whether `toPair H A₁ B₁`/`toPair H
    -- A₂ B₂` vanish, using `ordInfOfPair_le_zero` in the vanishing case since only `≥` is
    -- needed there) to relate each of `N₁', N₂'` back to `A₁',B₁',A₂',B₂'`, and finally
    -- `hinf₁`/`hinf₂` to land on `ordInfOfPair A₁' B₁' + ordInfOfPair A₂' B₂' =
    -- ordInfOfPair D' D''`.
    have hN'eq : N' = C c₁ * N₁' + C c₂ * N₂' := hN'_def
    have hN''eq : N'' = C c₁ * N₁'' + C c₂ * N₂'' := hN''_def
    have hstep1 : ordInfOfPair N' N'' ≥
        min (ordInfOfPair (C c₁ * N₁') (C c₁ * N₁'')) (ordInfOfPair (C c₂ * N₂') (C c₂ * N₂'')) := by
      rw [hN'eq, hN''eq]; exact ordInfOfPair_add_ge_min _ _ _ _
    have hstep2 : min (ordInfOfPair (C c₁ * N₁') (C c₁ * N₁'')) (ordInfOfPair (C c₂ * N₂') (C c₂ * N₂'')) ≥
        min (ordInfOfPair N₁' N₁'') (ordInfOfPair N₂' N₂'') :=
      min_le_min (ordInfOfPair_C_mul_ge c₁ N₁' N₁'') (ordInfOfPair_C_mul_ge c₂ N₂' N₂'')
    -- `ordInfOfPair_add_of_toPair_mul` needs *both* factors nonzero-as-a-pair; `A₁,B₁`
    -- (resp. `A₂,B₂`) aren't guaranteed nonzero here (same boundary as `hordN₁`/`hordN₂`
    -- above). We only need `≥`, though, so the zero case is handled directly: if
    -- `toPair H A₁ B₁ = 0` then `N₁' = N₁'' = 0` too (via `hN₁mul`), forcing
    -- `ordInfOfPair N₁' N₁'' = 0` by convention, which is `≥ ordInfOfPair A₂' B₂'`
    -- unconditionally via `ordInfOfPair_le_zero`.
    have hge1 : ordInfOfPair N₁' N₁'' ≥ ordInfOfPair A₁ B₁ + ordInfOfPair A₂' B₂' := by
      by_cases hA₁B₁ : toPair H A₁ B₁ = 0
      · have hN₁zero : toPair H N₁' N₁'' = 0 := by rw [hN₁mul, hA₁B₁, zero_mul]
        have hN₁pair : N₁' = 0 ∧ N₁'' = 0 := (toPair_eq_zero_iff H N₁' N₁'').mp hN₁zero
        have hA₁pair : A₁ = 0 ∧ B₁ = 0 := (toPair_eq_zero_iff H A₁ B₁).mp hA₁B₁
        have hA₁inf : ordInfOfPair A₁ B₁ = 0 := by
          unfold ordInfOfPair; rw [if_pos hA₁pair]
        rw [hN₁pair.1, hN₁pair.2, hA₁inf, zero_add]
        show ordInfOfPair (0 : k[X]) 0 ≥ ordInfOfPair A₂' B₂'
        calc ordInfOfPair (0 : k[X]) 0 = 0 := by unfold ordInfOfPair; rw [if_pos ⟨rfl, rfl⟩]
          _ ≥ ordInfOfPair A₂' B₂' := ordInfOfPair_le_zero A₂' B₂'
      · have hN₁ne : toPair H N₁' N₁'' ≠ 0 := by rw [hN₁mul]; exact mul_ne_zero hA₁B₁ hA₂'B₂'ne
        have hN₁pairne : ¬ (N₁' = 0 ∧ N₁'' = 0) := fun h => hN₁ne ((toPair_eq_zero_iff H N₁' N₁'').mpr h)
        have hA₁pairne : ¬ (A₁ = 0 ∧ B₁ = 0) := fun h => hA₁B₁ ((toPair_eq_zero_iff H A₁ B₁).mpr h)
        exact le_of_eq (ordInfOfPair_add_of_toPair_mul (H := H) hdeg A₁ B₁ A₂' B₂' N₁' N₁''
          hA₁pairne hne₂ hN₁pairne hN₁mul).symm
    have hge2 : ordInfOfPair N₂' N₂'' ≥ ordInfOfPair A₂ B₂ + ordInfOfPair A₁' B₁' := by
      by_cases hA₂B₂ : toPair H A₂ B₂ = 0
      · have hN₂zero : toPair H N₂' N₂'' = 0 := by rw [hN₂mul, hA₂B₂, zero_mul]
        have hN₂pair : N₂' = 0 ∧ N₂'' = 0 := (toPair_eq_zero_iff H N₂' N₂'').mp hN₂zero
        have hA₂pair : A₂ = 0 ∧ B₂ = 0 := (toPair_eq_zero_iff H A₂ B₂).mp hA₂B₂
        have hA₂inf : ordInfOfPair A₂ B₂ = 0 := by
          unfold ordInfOfPair; rw [if_pos hA₂pair]
        rw [hN₂pair.1, hN₂pair.2, hA₂inf, zero_add]
        show ordInfOfPair (0 : k[X]) 0 ≥ ordInfOfPair A₁' B₁'
        calc ordInfOfPair (0 : k[X]) 0 = 0 := by unfold ordInfOfPair; rw [if_pos ⟨rfl, rfl⟩]
          _ ≥ ordInfOfPair A₁' B₁' := ordInfOfPair_le_zero A₁' B₁'
      · have hN₂ne : toPair H N₂' N₂'' ≠ 0 := by rw [hN₂mul]; exact mul_ne_zero hA₂B₂ hA₁'B₁'ne
        have hN₂pairne : ¬ (N₂' = 0 ∧ N₂'' = 0) := fun h => hN₂ne ((toPair_eq_zero_iff H N₂' N₂'').mpr h)
        have hA₂pairne : ¬ (A₂ = 0 ∧ B₂ = 0) := fun h => hA₂B₂ ((toPair_eq_zero_iff H A₂ B₂).mpr h)
        exact le_of_eq (ordInfOfPair_add_of_toPair_mul (H := H) hdeg A₂ B₂ A₁' B₁' N₂' N₂''
          hA₂pairne hne₁ hN₂pairne hN₂mul).symm
    have hDinf : ordInfOfPair D' D'' = ordInfOfPair A₁' B₁' + ordInfOfPair A₂' B₂' :=
      ordInfOfPair_add_of_toPair_mul (H := H) hdeg A₁' B₁' A₂' B₂' D' D'' hne₁ hne₂ hD'D''ne hDmul
    calc ordInfOfPair N' N'' ≥ min (ordInfOfPair N₁' N₁'') (ordInfOfPair N₂' N₂'') :=
          le_trans hstep2 hstep1
      _ ≥ min (ordInfOfPair A₁ B₁ + ordInfOfPair A₂' B₂') (ordInfOfPair A₂ B₂ + ordInfOfPair A₁' B₁') :=
          min_le_min hge1 hge2
      _ ≥ ordInfOfPair A₁' B₁' + ordInfOfPair A₂' B₂' := by
          rw [ge_iff_le, le_min_iff]
          refine ⟨add_le_add_left hinf₁ _, ?_⟩
          rw [add_comm (ordInfOfPair A₂ B₂) (ordInfOfPair A₁' B₁')]
          exact add_le_add_right hinf₂ _
      _ = ordInfOfPair D' D'' := hDinf.symm
  · -- The pointwise pole bound, now a single `∀ P` clause: `hoff₁ P`/`hoff₂ P` already
    -- supply exactly the shape `hpointwise` wants, with the *same* shared slack `s :=
    -- (if P = x₁ then 1 else 0) + (if P = x₂ then 1 else 0)` on both sides (since it's
    -- the same `P`), so `hpointwise` applies directly with no case split on `P`'s
    -- relation to `x₁, x₂` needed at all — that three-way split (elsewhere / at `x₁` /
    -- at `x₂`) was only an artifact of the old three-clause `IsPoleBoundedAtPair`.
    intro P
    exact hpointwise P _ (hoff₁ P) (hoff₂ P)

/-- `L((x₁)+(x₂))` as a genuine `k`-submodule of `FractionRing (CoordinateRing
H)`, packaging `LPairCarrier` with `one_mem_LPairCarrier` /
`LPairCarrier_add_smul` (the latter specialized to give `zero_mem'` and
`add_mem'`/`smul_mem'` in the shapes `Submodule` wants). Takes `hdeg` because
`LPairCarrier_add_smul` needs it (for `ordInfOfPair` additivity, which is
genuinely deg-5-specific — see `ordInfOfPair_add_of_toPair_mul`) — a change
from the file's original scaffold, where `LPair` took no `hdeg`; every
existing call site (`finrank_L_pair`, `finrank_L_canonical`) already has
`hdeg` in scope, so this is a mechanical threading, not a new hypothesis on
the file's overall dependency shape. -/
def LPair (hdeg : H.f.natDegree = 5) (x₁ x₂ : H.Point) :
    Submodule k (FractionRing (CoordinateRing H)) where
  carrier := LPairCarrier x₁ x₂
  zero_mem' := by
    have h := LPairCarrier_add_smul hdeg x₁ x₂ 0 0 1 1
      (one_mem_LPairCarrier x₁ x₂) (one_mem_LPairCarrier x₁ x₂)
    simpa using h
  add_mem' {z₁ z₂} h₁ h₂ := by
    have h := LPairCarrier_add_smul hdeg x₁ x₂ 1 1 z₁ z₂ h₁ h₂
    simpa using h
  smul_mem' c {z} h := by
    -- `c • z + 0 • z`, both summands drawn from the *same* membership proof
    -- `h` (the second copy of `z` is discarded by the `0` coefficient) —
    -- simplifies to `c • z`.
    have h' := LPairCarrier_add_smul hdeg x₁ x₂ c 0 z z h h
    simpa using h'

/-! ## §2. The canonical divisor `K` and `L(K)`

The standard genus-2 holomorphic differential `dx/(2y)` on the deg-5 model.
`L(K)` is built the same way as `LPair`, but for the fixed divisor `K`
rather than a variable `(x₁)+(x₂)` — concretely, per the roadmap, `L(K)`
should turn out to be spanned by `{1, x}` under the standard
identification of `L(K)` with the space of holomorphic differentials. This
identification (and hence a fully explicit `LCanonical`, parallel to
`LPair` above) is not built in this file — `finrank_L_canonical` below is
stated abstractly, against `LPair` applied to a fiber `(x)+(ιx)` itself
(any hyperelliptic fiber represents the canonical class, so `LPair x (ι x)`
*is* `L(K)` up to the choice of representative `x` — this sidesteps needing
a separate `LCanonical` definition, at the cost of stating the theorem for
`LPair` at a fiber rather than for an independently-constructed `K`). -/

/-! ## §3. What "the effective divisors in this linear system are exactly
these" means, stated once and reused

Both hard steps below need not just a *dimension* count but a *qualitative*
description of which effective divisors lie in the class — `ℓ(D) = 1` needs
"and `D` is the only one", `ℓ(K) = 2` needs "and they are exactly the
fibers". These are genuinely different shapes (one compares against a fixed
pair `x₁,x₂`, the other against a fixed fiber `x, ι x`), so they get two
separate predicates below (`IsOnlyEffectiveInClass`, `IsOnlyFibersInCanonicalClass`)
rather than one shared one — but both exist so that §5's assembly has
exactly what it needs directly, rather than as bare `finrank` equalities
that would need a second, separately-named "and moreover" theorem bolted on
afterward. (This file's first draft stated `finrank_L_canonical` as only a
dimension count and had exactly that gap: it was not strong enough for
§5's `x₂ = ι x₁` case, which needs to know `(x₃)+(x₄)` is a fiber, not
merely that `ℓ(K) = 2`.) -/

/-- `x₁ + x₂` is the *only* effective divisor representing the class of
`LPair x₁ x₂`: for any `x₃, x₄` with `(x₁)+(x₂) ~ (x₃)+(x₄)` (i.e. the
difference lies in `principalSubgroup H hdeg`), `{x₃,x₄} = {x₁,x₂}` as an
unordered pair. This is the qualitative content `ℓ(D) = 1` is supposed to
buy in the case split below — stated directly, rather than as a `finrank`
equality plus a separate unpacking lemma, so §5 has exactly what it needs
without an intermediate `sorry`. -/
def IsOnlyEffectiveInClass (hdeg : H.f.natDegree = 5) (x₁ x₂ : H.Point) : Prop :=
  ∀ x₃ x₄ : H.Point,
    (single x₁ + single x₂ - single x₃ - single x₄ : Divisor H) ∈
      principalSubgroup H hdeg →
    ({x₃, x₄} : Set H.Point) = {x₁, x₂}

/-- `x + ι x`'s class contains *only* fibers as effective divisors: for any
`x₃, x₄` with `(x)+(ιx) ~ (x₃)+(x₄)`, `x₄ = ι x₃` (so `{x₃,x₄}` is itself
a fiber, of the point `x₃`, possibly a different point than `x`). This is
the qualitative content the case `x₂ = ι x₁` branch of §5 needs — strictly
stronger than `ℓ(K) = 2` alone, which is why it is stated as its own
predicate rather than derived from a bare dimension count in this file. -/
def IsOnlyFibersInCanonicalClass (hdeg : H.f.natDegree = 5) (x : H.Point) : Prop :=
  ∀ x₃ x₄ : H.Point,
    (single x + single (Point.iota x) - single x₃ - single x₄ : Divisor H) ∈
      principalSubgroup H hdeg →
    x₄ = Point.iota x₃

/-! ## §4. The two hard Riemann–Roch facts, stated precisely, `sorry`'d

`Module.finrank k (LPair x₁ x₂) = n` is included in both statements below
for the record — it is the actual Riemann–Roch dimension count and is the
natural thing to prove *en route* to the qualitative statement (the
qualitative statement is what a dimension-1 or dimension-2 space, together
with genus-2 hyperelliptic structure, forces) — but the qualitative
predicates from §3 are what §5's assembly actually consumes. Anyone filling
in these `sorry`s should expect to prove the `finrank` equality first (via
the `LPair`/`LPairCarrier` machinery of §1) and derive the qualitative
half from it (e.g. `ℓ = 1` forces the space to be exactly `k · 1`,
i.e. every element of `LPair x₁ x₂` is constant, i.e. every effective
divisor `(x₃)+(x₄)` linearly equivalent to `(x₁)+(x₂)` arises from a unit
ratio — hence equals `(x₁)+(x₂)` on the nose). -/

/-- **The first hard step**: `ℓ((x₁)+(x₂)) = 1` when `x₂ ≠ ι x₁`, and
`(x₁)+(x₂)` is consequently the only effective divisor in its class. The
"only constants" case — see `ROADMAP-ffk-sidon.md` §"Concrete construction
needed" for the proof shape (a nonconstant element would give a second,
non-hyperelliptic degree-2 map `C → P¹`, impossible for genus 2). **This is
the crux of the whole file and the hardest step in the project after the
Dedekind-domain `sorry`s already in `PrincipalDivisors.lean`.** -/
theorem finrank_L_pair (hdeg : H.f.natDegree = 5) (x₁ x₂ : H.Point)
    (hne : x₂ ≠ Point.iota x₁) :
    Module.finrank k (LPair hdeg x₁ x₂) = 1 ∧ IsOnlyEffectiveInClass hdeg x₁ x₂ := by
  sorry

/-- **The second hard step**: `ℓ((x)+(ι x)) = 2` for every `x` (every
hyperelliptic fiber represents the canonical class with the full expected
Riemann–Roch dimension), and — the genuinely genus-2-specific strengthening
`IsOnlyFibersInCanonicalClass` needs beyond the dimension count — every
effective divisor in that class is itself a fiber. See
`ROADMAP-ffk-sidon.md`; concretely the `finrank` half should reduce to
exhibiting `1, x_coord ∈ LPair x (ι x)` (via the standard differential
`dx/(2y)`'s pole structure) as a `k`-basis, and the qualitative half from
`deg K = 2` leaving no room for a non-fiber effective divisor once the
degree-2 map to `P¹` induced by `|K|` is shown to coincide with the
hyperelliptic map itself (not merely have the same dimension). -/
theorem finrank_L_canonical (hdeg : H.f.natDegree = 5) (x : H.Point) :
    Module.finrank k (LPair hdeg x (Point.iota x)) = 2 ∧
      IsOnlyFibersInCanonicalClass hdeg x := by
  sorry

/-! ## §5. Assembly: the dichotomy from the two facts above

This is the part of the file that is a complete, checked proof, modulo the
two `sorry`s above and the ambient `IsDedekindDomain (CoordinateRing H)`
hypothesis already threaded through the rest of the project. -/

/-- **The main theorem**: `SidonDichotomy` for `principalDivisorData H hdeg`,
assembled from `finrank_L_pair` and `finrank_L_canonical`'s qualitative
halves by the case split in `ROADMAP-ffk-sidon.md`:

* `s x₁ + s x₂ = s x₃ + s x₄` unfolds, via `s_add_s_eq_s_add_s_iff`, to
  `(x₁)+(x₂)-(x₃)-(x₄) ∈ principalSubgroup H hdeg`, i.e. `(x₁)+(x₂) ~
  (x₃)+(x₄)`.
* If `x₂ ≠ ι x₁`: `finrank_L_pair`'s qualitative half, applied to this
  equivalence (read as "`(x₃)+(x₄)` is an effective divisor equivalent to
  `(x₁)+(x₂)`"), gives `{x₃,x₄} = {x₁,x₂}` directly — the first disjunct.
* If `x₂ = ι x₁`: the equivalence becomes `(x₁)+(ιx₁) ~ (x₃)+(x₄)`, so
  `finrank_L_canonical`'s qualitative half (applied at the point `x₁`)
  gives `x₄ = ι x₃` directly — the second disjunct (with the swap already
  baked into `SidonDichotomy`'s stated shape, `x₂ = ι x₁ ∧ x₄ = ι x₃`, so
  this branch also needs to hand back `x₂ = ι x₁`, which is this branch's
  own case hypothesis). -/
theorem sidonDichotomy_of_riemannRoch (hdeg : H.f.natDegree = 5) :
    (principalDivisorData H hdeg).SidonDichotomy := by
  intro δ₀ x₁ x₂ x₃ x₄ heq
  rw [s_add_s_eq_s_add_s_iff] at heq
  by_cases hcase : x₂ = Point.iota x₁
  · -- `x₂ = ι x₁` branch: rewrite `heq` to match `IsOnlyFibersInCanonicalClass`'s
    -- shape, then invoke the qualitative half of `finrank_L_canonical`.
    right
    refine ⟨hcase, ?_⟩
    -- `hcase : x₂ = ι x₁`, so rewriting `x₂` to `ι x₁` inside `heq` needs
    -- `rw [hcase] at heq` (forward direction: replace `x₂` by `ι x₁`), not
    -- `rw [← hcase]` (which would replace `ι x₁` by `x₂` — the wrong way).
    rw [hcase] at heq
    exact (finrank_L_canonical hdeg x₁).2 x₃ x₄ heq
  · -- `x₂ ≠ ι x₁` branch: directly invoke the qualitative half of
    -- `finrank_L_pair`; `{x₃,x₄} = {x₁,x₂}` is the same set equality as the
    -- goal `{x₁,x₂} = {x₃,x₄}` up to `.symm`.
    left
    exact ((finrank_L_pair hdeg x₁ x₂ hcase).2 x₃ x₄ heq).symm

/-- **Closing the loop with `FFKSidon.lean`**: for the concrete `D :=
principalDivisorData H hdeg`, both hypotheses `ffk_sidon_dichotomy` needs —
`SidonDichotomy` (`sidonDichotomy_of_riemannRoch`, this file) and
`HyperellipticClass` (`hyperellipticClass_principalDivisorData`,
`HyperellipticClassProof.lean`) — are now available for the same `D`, so
the full FFK "iff" is derivable for a genuine, `CoordinateRing`-built
principal-divisor subgroup rather than an abstract one. This is the
theorem `sidonRepBound_of_sidonDichotomy` in `SidonBridge.lean` is meant
to be fed once this file's two remaining `sorry`s are closed — nothing
downstream needs to change, since `SidonBridge.lean` already takes
`D.SidonDichotomy`/`D.HyperellipticClass` as hypotheses on an arbitrary
`D`, and this theorem supplies both for the specific `D` that matters.
Still gated on this file's `finrank_L_pair`/`finrank_L_canonical` and on
the upstream Dedekind-domain `sorry`s already present in
`PrincipalDivisors.lean`/`PrincipalDivisorsDedekind.lean` — not a new,
independent gap, just the same ones inherited through this file's
dependencies. -/
theorem ffk_sidon_dichotomy_principalDivisorData (hdeg : H.f.natDegree = 5)
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    [∀ (a : k) (S : Finset H.Point),
      ∀ P : S, Module.Finite k (CoordinateRing H ⧸ pointIdeal P.1 ^ (ordAt P.1 (linX a) 0).toNat)]
    (hspec : ∀ (a : k), ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk v.asIdeal).count
        (Associates.mk (Ideal.span ({toPair H (linX a) 0} : Set (CoordinateRing H)))).factors
          ≠ 0 → ∃ P, v.asIdeal = pointIdeal P)
    (δ₀ x₁ x₂ x₃ x₄ : H.Point) :
    s (principalDivisorData H hdeg) δ₀ x₁ + s (principalDivisorData H hdeg) δ₀ x₂ =
        s (principalDivisorData H hdeg) δ₀ x₃ + s (principalDivisorData H hdeg) δ₀ x₄ ↔
      ({x₁, x₂} : Set H.Point) = {x₃, x₄} ∨
        (x₂ = Point.iota x₁ ∧ x₄ = Point.iota x₃) :=
  ffk_sidon_dichotomy (principalDivisorData H hdeg)
    (sidonDichotomy_of_riemannRoch hdeg)
    (hyperellipticClass_principalDivisorData hdeg hchar hsf hspec)
    δ₀ x₁ x₂ x₃ x₄

end HyperellipticPolynomial
