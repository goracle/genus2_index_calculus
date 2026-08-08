import Mathlib
import Genus2Lean.HyperellipticFunctionField
import Genus2Lean.AffinePoints
import Genus2Lean.DivisorClassGroup
import Genus2Lean.PrincipalDivisors
import Genus2Lean.PrincipalDivisorSubgroup
import Genus2Lean.FFKSidon
import Genus2Lean.HyperellipticClassProof
noncomputable section

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

* no pole at infinity (`ordInfOfPair A B = ordInfOfPair A' B'`, reusing
  exactly `PrincipalDivisorSubgroup.lean`'s `divToPairRatio` matching
  condition — this is the same "ratio of two `toPair`s with matching pole
  order at infinity" shape, just now also tracking poles at `x₁, x₂`);
* at every affine point other than `x₁, x₂`, the ratio has no pole
  (`ordAt P A B ≥ ordAt P A' B'`);
* at `x₁` and at `x₂`, the ratio has at worst a simple pole
  (`ordAt P A B ≥ ordAt P A' B' - 1`).

Represented as a `Set` predicate on `FractionRing (CoordinateRing H)`
first (so equality of two representations of the same ratio is handled by
the ambient field, not by hand), then packaged as a `Submodule`. -/

variable [IsDedekindDomain (CoordinateRing H)]

/-- The pole/zero conditions a numerator/denominator pair `(A,B,A',B')`
must satisfy to represent an element of `L((x₁)+(x₂))`. Stated as a
`Prop` on the four polynomials rather than on the resulting field element,
so `L` can be defined as an image/range without first needing to know the
map `(A,B,A',B') ↦ toPair H A B / toPair H A' B'` is well-behaved. -/
def IsPoleBoundedAtPair (x₁ x₂ : H.Point) (A B A' B' : k[X]) : Prop :=
  ¬ (A' = 0 ∧ B' = 0) ∧
  ordInfOfPair A B = ordInfOfPair A' B' ∧
  (∀ P : H.Point, P ≠ x₁ → P ≠ x₂ → ordAt P A B ≥ ordAt P A' B') ∧
  ordAt x₁ A B ≥ ordAt x₁ A' B' - 1 ∧
  ordAt x₂ A B ≥ ordAt x₂ A' B' - 1

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
constant function has no poles anywhere. `IsPoleBoundedAtPair`'s four
conjuncts close via, respectively: `toPair_one_zero_notMem_pointIdeal`
(ruling out the vacuous `A'=B'=0` case, since `toPair H 1 0 = 1 ≠ 0`, hence
`¬(1=0 ∧ 0=0)` directly — no need for the ideal-membership fact here, just
`one_ne_zero`), `ordInfOfPair_one_zero` (both sides), `ordAt_one_zero`
(giving `0 ≥ 0` in every branch). -/
theorem one_mem_LPairCarrier (x₁ x₂ : H.Point) : (1 : FractionRing (CoordinateRing H)) ∈
    LPairCarrier x₁ x₂ := by
  refine ⟨1, 0, 1, 0, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact fun h => one_ne_zero h.1
  · rfl
  · intro P _ _
    exact le_refl _
  · -- Goal: `ordAt x₁ 1 0 ≥ ordAt x₁ 1 0 - 1`. This holds for *any* integer
    -- value of `ordAt x₁ 1 0` (`n ≥ n - 1` always), so no `rw`/`simp` on the
    -- concrete value is even needed — `omega` alone closes it once the
    -- statement is recognized as being about a single integer term.
    omega
  · omega
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
theorem ordAt_toPair_mul_of_ne_zero [IsDedekindDomain (CoordinateRing H)]
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
theorem intValuation_add_le_max [IsDedekindDomain (CoordinateRing H)]
    (P : H.Point) (h_bot : pointIdeal P ≠ ⊥) (g g' : CoordinateRing H) :
    (pointHeightOne P h_bot).intValuation (g + g') ≤
      max ((pointHeightOne P h_bot).intValuation g)
        ((pointHeightOne P h_bot).intValuation g') :=
  IsDedekindDomain.HeightOneSpectrum.intValuation.map_add_le_max' _ g g'

/-- `LPairCarrier x₁ x₂` is closed under `k`-linear combinations: the
common-denominator argument that turns two pole-bounded ratios into one.
Given `z₁` from `(A₁,B₁,A₁',B₁')` and `z₂` from `(A₂,B₂,A₂',B₂')`, `c₁ z₁ +
c₂ z₂` is represented by numerator `c₁ · toPair A₁ B₁ · toPair A₂' B₂' + c₂
· toPair A₂ B₂ · toPair A₁' B₁'` over denominator `toPair A₁' B₁' · toPair
A₂' B₂'`. The two valuation-theoretic facts this needs —
`ordAt_toPair_mul_of_ne_zero` (multiplicativity) and `intValuation_add_le_max`
(the ultrametric inequality) — are now proved above (confirmed against
Mathlib's `AdicValuation`/`WithZero` source, not guessed). What remains
`sorry`'d is pure assembly: (1) `ordInfOfPair` additivity under the same
combination (elementary `natDegree` bookkeeping, no valuation theory, not yet
written); (2) threading `toPair_surjective_local` witnesses for the combined
numerator/denominator through `ordAt_toPair_mul_of_ne_zero`/
`intValuation_add_le_max` to land exactly on `IsPoleBoundedAtPair`'s four
`(A,B,A',B')`-level conjuncts; (3) the several `A'=B'=0`-style degenerate
cases (`c₁=0`, `c₂=0`, denominators colliding) that the clean multiplicativity
statement above doesn't cover on its own. -/
theorem LPairCarrier_add_smul (hdeg : H.f.natDegree = 5) (x₁ x₂ : H.Point)
    (c₁ c₂ : k) (z₁ z₂ : FractionRing (CoordinateRing H))
    (h₁ : z₁ ∈ LPairCarrier x₁ x₂) (h₂ : z₂ ∈ LPairCarrier x₁ x₂) :
    c₁ • z₁ + c₂ • z₂ ∈ LPairCarrier x₁ x₂ := by
  sorry

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
