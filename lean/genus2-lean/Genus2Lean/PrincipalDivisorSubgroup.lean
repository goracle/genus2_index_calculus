import Mathlib
import Genus2Lean.HyperellipticFunctionField
import Genus2Lean.AffinePoints
import Genus2Lean.DivisorClassGroup
import Genus2Lean.PrincipalDivisors
noncomputable section

set_option linter.style.header false

open Polynomial

/-!
# A genuine (partial) principal-divisor subgroup, built from `CoordinateRing H`

`DivisorClassGroup.lean` leaves `PrincipalDivisorData.P` abstract: any subgroup of
`Divisor0 H` satisfying only `P ≤ Divisor0 H`, not derived from `CoordinateRing H`. This
file closes part of that gap by constructing a genuine subgroup of divisors of actual
elements of the coordinate ring, proving it lands in `Divisor0 H` via
`PrincipalDivisors.lean`'s `deg_div_eq_zero_deg5`.

**Scope, stated honestly:**

* `Divisor H` (per `DivisorClassGroup.lean`'s own docstring) only covers the *affine* part
  of `C` — points at infinity are excluded by design. Consequently the affine divisor of a
  single function, `∑_{P ∈ S} ordAt P A B • (P)`, has degree `-ordInfOfPair A B` in general
  (`deg_div_eq_zero_deg5`), **not** `0` — it is only degree-0 when the function has no
  zero/pole at the point at infinity. This is not a bug to work around: it is the actual
  mathematical content of "principal divisors have degree 0" *for the compactified curve*,
  which this file's affine-only `Divisor H` cannot fully see on its own.
* **Generators are differences, not single functions — this is the key design point, and the
  reason for a revision to this file's first version.** A first version generated
  `principalSubgroup` only by single `divToPair A B S` with `ordInfOfPair A B = 0` on the nose.
  That is too narrow: it misses exactly the case that matters for `FFKSidon.lean`'s
  `HyperellipticClass` — the divisor of a genuine *ratio* `g/h` of two coordinate-ring elements
  each individually having a nonzero (but *matching*) pole/zero order at infinity, e.g.
  `g = toPair H (X - C a) 0`, `h = toPair H (X - C c) 0`, both degree-1-in-`X` so both
  `ordInfOfPair = -2`, whose ratio `g/h` has no pole/zero at infinity at all (the order-2
  contributions cancel) even though neither factor alone does. `CoordinateRing H` is a domain,
  not a field, so "the divisor of `g/h`" is not literally `divToPair` of any single element —
  it is `div(g) - div(h)` computed on the affine part directly. The generating set below is
  therefore built from *pairs* `((A₁,B₁,S₁), (A₂,B₂,S₂))` with **matching** `ordInfOfPair`
  (`ordInfOfPair A₁ B₁ = ordInfOfPair A₂ B₂`, not both `= 0`), generating
  `divToPair A₁ B₁ S₁ - divToPair A₂ B₂ S₂`. Taking `(A₂, B₂, S₂) = (1, 0, ∅)` (so `h = 1`,
  `ordInfOfPair 1 0 = 0`, `divToPair 1 0 ∅ = 0`) recovers the old single-function generators
  as a special case, so this is a strict widening, not a different construction.
* `ordAt`'s finite support is, as in `PrincipalDivisors.lean`, threaded through as explicit
  `(S, hsupp)` data per function rather than derived to exist in general; likewise the
  Nullstellensatz-type `hspec` hypothesis is carried through unchanged, for each of the two
  functions in a generating pair.
* Only the `H.f.natDegree = 5` case is covered (`deg_div_eq_zero_deg5`'s own hypothesis); the
  degree-6 case (two points at infinity) is not addressed here.

So: this file supplies a real, non-vacuous, honestly-scoped instance of
`PrincipalDivisorData` — strictly smaller than "the" principal divisors of `C` (it only
captures divisors of *ratios* expressible via two `toPair`s with matching pole order at
infinity, not the fully general principal-divisor group), but genuinely built from
`CoordinateRing H` rather than assumed, and wide enough to be the actual target
`HyperellipticClassProof.lean` needs. `FFKSidon.lean`'s `SidonDichotomy` is not addressed
here at all.

**Verification status: drafted without a live Lean toolchain, same caveat as this project's
other `PLAUSIBLE`-tier scaffolding — NOT yet `lake build`-checked.** `divToPair`/`deg_divToPair`
below are carried over unchanged from the previous (now-superseded) version of this file,
which did build successfully up through those two definitions; what's new here
(`divToPairRatio`, `deg_divToPairRatio_eq_zero`, the widened `principalSubgroup`) has not been
checked against a live goal.
-/

namespace HyperellipticPolynomial

open Divisor

variable {k : Type*} [Field k]
variable {H : HyperellipticPolynomial k}

/-- The affine divisor of the coordinate-ring element `toPair H A B`, restricted to a finite
set `S` of points: `∑ P ∈ S, ordAt P A B • (P)`. Note this definition alone does not assert
`S` actually captures every point where `ordAt P A B ≠ 0` — that `hsupp` fact (matching
`PrincipalDivisors.lean`'s `sum_ordAt_eq_natDegree_pairNorm`/`deg_div_eq_zero_deg5`) is only
needed, and only supplied, at the point of use below (`deg_divToPair_eq_zero`), not baked
into this definition's type.

Built as `∑ P ∈ S, ordAt P A B • single P` rather than via `Finsupp.onFinset`: `Divisor
H` is a plain `def`, not `abbrev`, over `H.Point →₀ ℤ`, so it does not unfold to expose
`Finsupp`'s `DFunLike` application or `.support`/`.sum` projections at ordinary transparency
(confirmed by a build error on an earlier `Finsupp.onFinset`-based attempt) — exactly the same
reason `DivisorClassGroup.lean` itself only ever builds/inspects `Divisor H` values through the
`single`/`deg` `AddMonoidHom`s and the ambient `AddCommGroup` structure, never through raw
`Finsupp` field access. This definition follows that same discipline: `Finset.sum` and `zsmul`
are already available on any `AddCommGroup`, so no `Finsupp`-specific API is needed at all. -/
def divToPair [IsDedekindDomain (CoordinateRing H)] (A B : k[X]) (S : Finset H.Point) : Divisor H :=
  ∑ P ∈ S, (ordAt P A B) • single P

/-- `deg (divToPair A B S) = ∑ P ∈ S, ordAt P A B`. Pure `AddMonoidHom` bookkeeping via
`deg`'s additivity (`map_sum`) and `deg_single` — no `Finsupp` internals touched, matching
`DivisorClassGroup.lean`'s own idiom for interacting with `Divisor H` values.
**UNVERIFIED step**: `map_zsmul (f : M →+ N) (n : ℤ) (x : M) : f (n • x) = n • f x` lands in
`N`'s own `zsmul`, here `ℤ`'s — the exact simp lemma to collapse `n • (1 : ℤ)` down to `n * 1`
(candidates: `zsmul_eq_mul`, `smul_eq_mul`, or it may already be `rfl`/handled by `zsmul_one`)
was not checked against a live goal; if `zsmul_eq_mul` is the wrong name, replace that one
`rw` with `simp` as a fallback. -/
theorem deg_divToPair [IsDedekindDomain (CoordinateRing H)] (A B : k[X]) (S : Finset H.Point) :
    deg (divToPair A B S) = ∑ P ∈ S, ordAt P A B := by
  unfold divToPair
  rw [map_sum]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  rw [map_zsmul, deg_single]
  simp

/-- **The genuine generator shape.** The affine divisor of a *ratio* `g/h` of two
coordinate-ring elements, `g = toPair H A₁ B₁` and `h = toPair H A₂ B₂`, as
`divToPair A₁ B₁ S₁ - divToPair A₂ B₂ S₂`. This is not itself claimed to be `deg`-zero for
arbitrary `(A₁,B₁,S₁), (A₂,B₂,S₂)` — see `deg_divToPairRatio_eq_zero` below for the actual
condition (matching `ordInfOfPair`, not each individually zero). -/
def divToPairRatio [IsDedekindDomain (CoordinateRing H)]
    (A₁ B₁ : k[X]) (S₁ : Finset H.Point) (A₂ B₂ : k[X]) (S₂ : Finset H.Point) : Divisor H :=
  divToPair A₁ B₁ S₁ - divToPair A₂ B₂ S₂

/-- **The degree-0 containment for ratios: matching `ordInfOfPair`, not each individually
zero.** With `ordInfOfPair A₁ B₁ = ordInfOfPair A₂ B₂`, `deg_div_eq_zero_deg5` applied to each
half gives `(∑_{S₁} ordAt) = -ordInfOfPair A₁ B₁` and `(∑_{S₂} ordAt) = -ordInfOfPair A₂ B₂`;
subtracting, the (possibly nonzero) `ordInfOfPair` terms cancel exactly because they're equal,
leaving `deg (divToPairRatio ...) = 0` even though neither half alone is `deg`-zero unless
`ordInfOfPair = 0`. This is the actual mechanism that makes `HyperellipticClassProof.lean`'s
target expressible: taking `(A₂,B₂,S₂) := ((X - C a), 0, S)` twice with different centers `a`
recovers exactly the fiber-difference divisor, since both centers give the same
`ordInfOfPair = -2` (`ordInfOfPair` depends only on `natDegree`, not on the specific center). -/
theorem deg_divToPairRatio_eq_zero (hdeg : H.f.natDegree = 5)
    [IsDedekindDomain (CoordinateRing H)]
    (A₁ B₁ : k[X]) (hAB₁ : ¬(A₁ = 0 ∧ B₁ = 0)) (S₁ : Finset H.Point)
    (hsupp₁ : ∀ P, P ∉ S₁ → ordAt P A₁ B₁ = 0)
    (hspec₁ : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk v.asIdeal).count
        (Associates.mk (Ideal.span ({toPair H A₁ B₁} : Set (CoordinateRing H)))).factors ≠ 0 →
      ∃ P, v.asIdeal = pointIdeal P)
    [∀ P : S₁, Module.Finite k (CoordinateRing H ⧸ pointIdeal P.1 ^ (ordAt P.1 A₁ B₁).toNat)]
    (A₂ B₂ : k[X]) (hAB₂ : ¬(A₂ = 0 ∧ B₂ = 0)) (S₂ : Finset H.Point)
    (hsupp₂ : ∀ P, P ∉ S₂ → ordAt P A₂ B₂ = 0)
    (hspec₂ : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk v.asIdeal).count
        (Associates.mk (Ideal.span ({toPair H A₂ B₂} : Set (CoordinateRing H)))).factors ≠ 0 →
      ∃ P, v.asIdeal = pointIdeal P)
    [∀ P : S₂, Module.Finite k (CoordinateRing H ⧸ pointIdeal P.1 ^ (ordAt P.1 A₂ B₂).toNat)]
    (hmatch : ordInfOfPair A₁ B₁ = ordInfOfPair A₂ B₂) :
    deg (divToPairRatio A₁ B₁ S₁ A₂ B₂ S₂) = 0 := by
  unfold divToPairRatio
  rw [deg_sub, deg_divToPair, deg_divToPair]
  have h₁ := deg_div_eq_zero_deg5 H hdeg S₁ A₁ B₁ hAB₁ hsupp₁ hspec₁
  have h₂ := deg_div_eq_zero_deg5 H hdeg S₂ A₂ B₂ hAB₂ hsupp₂ hspec₂
  omega



/-- The genuine principal-divisor subgroup: generated by every `divToPairRatio A₁ B₁ S₁ A₂ B₂
S₂` arising from a pair of functions with **matching** `ordInfOfPair` (not each individually
zero — see the module docstring for why this is the actual condition, and
`deg_divToPairRatio_eq_zero` for the proof), for a fixed degree-5 `H`. Built via
`AddSubgroup.closure` rather than a `Set`-carrier structure, so `≤ Divisor0 H` can be proved
once via `AddSubgroup.closure_le` instead of per-generator.

Strictly widens the previous (single-function) version of this subgroup: taking
`(A₂,B₂,S₂) := (1, 0, ∅)` gives `divToPairRatio A B S 1 0 ∅ = divToPair A B S - 0 = divToPair
A B S` (since `divToPair 1 0 ∅` is an empty `Finset.sum`, hence `0`) with `ordInfOfPair 1 0 =
0` matching `ordInfOfPair A B = 0` exactly when the old condition held — so every old
generator is still a generator here, via that special case. -/
def principalSubgroup (H : HyperellipticPolynomial k) (hdeg : H.f.natDegree = 5)
    [IsDedekindDomain (CoordinateRing H)] : AddSubgroup (Divisor H) :=
  AddSubgroup.closure
    { D : Divisor H | ∃ (A₁ B₁ : k[X]) (S₁ : Finset H.Point)
        (_hAB₁ : ¬(A₁ = 0 ∧ B₁ = 0)) (hsupp₁ : ∀ P, P ∉ S₁ → ordAt P A₁ B₁ = 0)
        (_hspec₁ : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
          (Associates.mk v.asIdeal).count
            (Associates.mk (Ideal.span ({toPair H A₁ B₁} : Set (CoordinateRing H)))).factors
              ≠ 0 → ∃ P, v.asIdeal = pointIdeal P)
        (_hfin₁ : ∀ P : S₁, Module.Finite k (CoordinateRing H ⧸
          pointIdeal P.1 ^ (ordAt P.1 A₁ B₁).toNat))
        (A₂ B₂ : k[X]) (S₂ : Finset H.Point)
        (_hAB₂ : ¬(A₂ = 0 ∧ B₂ = 0)) (hsupp₂ : ∀ P, P ∉ S₂ → ordAt P A₂ B₂ = 0)
        (_hspec₂ : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
          (Associates.mk v.asIdeal).count
            (Associates.mk (Ideal.span ({toPair H A₂ B₂} : Set (CoordinateRing H)))).factors
              ≠ 0 → ∃ P, v.asIdeal = pointIdeal P)
        (_hfin₂ : ∀ P : S₂, Module.Finite k (CoordinateRing H ⧸
          pointIdeal P.1 ^ (ordAt P.1 A₂ B₂).toNat)),
        ordInfOfPair A₁ B₁ = ordInfOfPair A₂ B₂ ∧ D = divToPairRatio A₁ B₁ S₁ A₂ B₂ S₂ }

/-- **`principalSubgroup H hdeg ≤ Divisor0 H`.** The one fact `PrincipalDivisorData` needs.
Reduces, via `AddSubgroup.closure_le`, to checking every *generator* lands in `Divisor0 H`
— exactly `deg_divToPairRatio_eq_zero` above. -/
theorem principalSubgroup_le_Divisor0 (H : HyperellipticPolynomial k) (hdeg : H.f.natDegree = 5)
    [IsDedekindDomain (CoordinateRing H)] :
    principalSubgroup H hdeg ≤ Divisor0 H := by
  rw [principalSubgroup, AddSubgroup.closure_le]
  rintro D ⟨A₁, B₁, S₁, hAB₁, hsupp₁, hspec₁, hfin₁, A₂, B₂, S₂, hAB₂, hsupp₂, hspec₂, hfin₂,
    hmatch, rfl⟩
  rw [SetLike.mem_coe, mem_Divisor0_iff]
  exact deg_divToPairRatio_eq_zero hdeg A₁ B₁ hAB₁ S₁ hsupp₁ hspec₁ A₂ B₂ hAB₂ S₂ hsupp₂ hspec₂
    hmatch

/-- The genuine, honestly-partial `PrincipalDivisorData` instance for a degree-5 `H`,
packaging `principalSubgroup`/`principalSubgroup_le_Divisor0`. Downstream (`FFKSidon.lean`)
consumers can now instantiate against this concrete `D` instead of an arbitrary abstract
one — though `HyperellipticClass`/`SidonDichotomy` for *this* `D` are separate, unproved
facts, not automatic consequences of this construction. -/
def principalDivisorData (H : HyperellipticPolynomial k) (hdeg : H.f.natDegree = 5)
    [IsDedekindDomain (CoordinateRing H)] : PrincipalDivisorData H where
  P := principalSubgroup H hdeg
  le_Divisor0 := principalSubgroup_le_Divisor0 H hdeg

end HyperellipticPolynomial
