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
elements of the coordinate ring — `∑ P ∈ S, ordAt P A B • (P)` for `toPair H A B` — and
proving it lands in `Divisor0 H`, using `PrincipalDivisors.lean`'s `deg_div_eq_zero_deg5`.

**Scope, stated honestly:**

* `Divisor H` (per `DivisorClassGroup.lean`'s own docstring) only covers the *affine* part
  of `C` — points at infinity are excluded by design. Consequently the affine divisor of a
  function, `∑_{P ∈ S} ordAt P A B • (P)`, has degree `-ordInfOfPair A B` in general
  (`deg_div_eq_zero_deg5`), **not** `0` — it is only degree-0 when the function has no
  zero/pole at the point at infinity. This is not a bug to work around here: it is the
  actual mathematical content of "principal divisors have degree 0" *for the compactified
  curve*, which this file's affine-only `Divisor H` cannot fully see. Rather than construct
  a subgroup and give it an unsound `le_Divisor0` proof, the subgroup built below is
  generated *only* by the divisors of pairs `(A, B)` with `ordInfOfPair A B = 0` — a
  genuinely smaller subgroup than the full principal divisors, but one whose degree-0
  containment is actually true and actually proved.
* `ordAt`'s finite support (needed to write the sum `∑ P ∈ S, ordAt P A B • (P)` as a
  `Divisor H := H.Point →₀ ℤ` at all) is not derived here either — as in
  `PrincipalDivisors.lean`, it is threaded through as an explicit `(S, hsupp)` pair rather
  than proved to exist for arbitrary `(A, B)`. The Nullstellensatz-type `hspec` hypothesis
  (every height-one prime with nonzero multiplicity in `(toPair H A B)`'s factorization is
  `pointIdeal P` for some affine point `P`) is likewise carried through unchanged from
  `PrincipalDivisors.lean`, for the same reason documented there.
* Only the `H.f.natDegree = 5` case is covered (`deg_div_eq_zero_deg5`'s own hypothesis);
  the degree-6 case (two points at infinity) is not addressed here.

So: this file supplies a real, non-vacuous, honestly-scoped instance of
`PrincipalDivisorData` — strictly smaller than "the" principal divisors of `C`, but
genuinely built from `CoordinateRing H` rather than assumed — closing part, not all, of the
gap `DivisorClassGroup.lean` flags. `FFKSidon.lean`'s `HyperellipticClass`/`SidonDichotomy`
are not addressed here; they would need this subgroup (or its completion once points at
infinity are modeled) checked against those specific hypotheses separately.

**Verification status: drafted without a live Lean toolchain, same caveat as this project's
other `PLAUSIBLE`-tier scaffolding.** A first draft used `Finsupp.onFinset` directly and
failed to build (`Divisor H` doesn't unfold to `Finsupp`'s `DFunLike`/`.support`/`.sum` API
at ordinary transparency); the version below instead builds `divToPair` as a `Finset.sum` of
`zsmul`s of `single`, and computes its `deg` via plain `AddMonoidHom` lemmas
(`map_sum`, `map_zsmul`, `deg_single`) — the same idiom `DivisorClassGroup.lean` itself uses
throughout, so this is lower-risk than the original attempt, but has still not been
`lake build`-checked against a live goal.
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

/-- **The degree-0 containment, for functions with no zero/pole at infinity.** This is where
`PrincipalDivisors.lean`'s `deg_div_eq_zero_deg5` actually gets used: with
`ordInfOfPair A B = 0`, the affine sum `∑ P ∈ S, ordAt P A B` alone is forced to `0`. -/
theorem deg_divToPair_eq_zero (hdeg : H.f.natDegree = 5)
    [IsDedekindDomain (CoordinateRing H)]
    (A B : k[X]) (hAB : ¬(A = 0 ∧ B = 0)) (S : Finset H.Point)
    (hsupp : ∀ P, P ∉ S → ordAt P A B = 0)
    (hspec : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk v.asIdeal).count
        (Associates.mk (Ideal.span ({toPair H A B} : Set (CoordinateRing H)))).factors ≠ 0 →
      ∃ P, v.asIdeal = pointIdeal P)
    [∀ P : S, Module.Finite k (CoordinateRing H ⧸ pointIdeal P.1 ^ (ordAt P.1 A B).toNat)]
    (hinf : ordInfOfPair A B = 0) :
    deg (divToPair A B S) = 0 := by
  rw [deg_divToPair]
  have h := deg_div_eq_zero_deg5 H hdeg S A B hAB hsupp hspec
  omega

/-- The genuine, honestly-partial principal-divisor subgroup: generated by every
`divToPair A B S` arising from a pair `(A, B)` with no zero/pole at infinity
(`ordInfOfPair A B = 0`), for a fixed degree-5 `H`. Built via `AddSubgroup.closure` rather
than a `Set`-carrier structure, so `≤ Divisor0 H` can be proved once via
`AddSubgroup.closure_le` instead of per-generator. -/
def principalSubgroup (H : HyperellipticPolynomial k) (hdeg : H.f.natDegree = 5)
    [IsDedekindDomain (CoordinateRing H)] : AddSubgroup (Divisor H) :=
  AddSubgroup.closure
    { D : Divisor H | ∃ (A B : k[X]) (S : Finset H.Point)
        (_hAB : ¬(A = 0 ∧ B = 0)) (hsupp : ∀ P, P ∉ S → ordAt P A B = 0)
        (_hspec : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
          (Associates.mk v.asIdeal).count
            (Associates.mk (Ideal.span ({toPair H A B} : Set (CoordinateRing H)))).factors
              ≠ 0 → ∃ P, v.asIdeal = pointIdeal P)
        (_hfin : ∀ P : S, Module.Finite k (CoordinateRing H ⧸
          pointIdeal P.1 ^ (ordAt P.1 A B).toNat)),
        ordInfOfPair A B = 0 ∧ D = divToPair A B S }

/-- **`principalSubgroup H hdeg ≤ Divisor0 H`.** The one fact `PrincipalDivisorData` needs.
Reduces, via `AddSubgroup.closure_le`, to checking every *generator* lands in `Divisor0 H`
— exactly `deg_divToPair_eq_zero` above. -/
theorem principalSubgroup_le_Divisor0 (H : HyperellipticPolynomial k) (hdeg : H.f.natDegree = 5)
    [IsDedekindDomain (CoordinateRing H)] :
    principalSubgroup H hdeg ≤ Divisor0 H := by
  rw [principalSubgroup, AddSubgroup.closure_le]
  rintro D ⟨A, B, S, hAB, hsupp, hspec, hfin, hinf, rfl⟩
  rw [SetLike.mem_coe, mem_Divisor0_iff]
  exact deg_divToPair_eq_zero hdeg A B hAB S hsupp hspec hinf

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
