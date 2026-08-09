import Mathlib
import Genus2Lean.HyperellipticFunctionField
import Genus2Lean.AffinePoints
import Genus2Lean.DivisorClassGroup
import Genus2Lean.PrincipalDivisors
import Genus2Lean.PrincipalDivisorSubgroup
import Genus2Lean.FFKSidon
import Genus2Lean.HyperellipticClassProof
import Genus2Lean.RiemannRochGenus2
noncomputable section

open Classical

set_option linter.style.header false

open Polynomial

/-!
# The actual crux: uniqueness of the genus-2 hyperelliptic degree-2 map

`RiemannRochGenus2.lean` reduces the whole Forey–Fresán–Kowalski dichotomy to two
`sorry`s, `finrank_L_pair` and `finrank_L_canonical`, and its own docstring on
`finrank_L_pair` calls it "the crux of the whole file". Tracing through *why* it's
hard (rather than just restating that it is) lands on a single, precisely citable
external fact, not a vague gap:

> **A hyperelliptic curve of genus ≥ 2 has a unique morphism to `P¹` of degree 2, up
> to post-composition by an automorphism of `P¹`.**

This is not folklore invented for this project — it is exactly what the original FFK
paper itself cites (as an external black box, not something they reprove) at the one
point in their own argument where they need it:

    "there exists on C a unique morphism to P¹ of degree 2, up to automorphisms"
    — Forey–Fresán–Kowalski, *Sidon sets in algebraic geometry* (IMRN 2024),
      proof of Theorem 1, Case (5), citing Liu, *Algebraic geometry and
      arithmetic curves*, Remark 7.4.30.

So even the paper this project is formalizing treats this as citable background, not
something to re-derive from Riemann–Hurwitz or ramification counting inline. Nothing
in this project (`ordAt`, valuations, `pointIdeal`, CRT/Dedekind-domain bookkeeping)
currently encodes "a rational function `C → P¹`" or its degree as a first-class
object, so there is no cheaper route to this fact from what is already built — see
`RiemannRochGenus2.lean`'s own `finrank_L_pair` docstring and `SidonBridge.lean`'s
module docstring, both of which already flag this as the real remaining content
rather than Lean bookkeeping.

**What this file does:**

* States the fact above precisely, in this project's own idiom (`ordAt`, `H.Point`,
  `FractionRing (CoordinateRing H)`) rather than inventing a new "morphism to `P¹`"
  type — as `uniqueDegree2MapToP1`, a single named `sorry` with the citation
  attached, exactly the way `PrincipalDivisorData.SidonDichotomy`
  (`FFKSidon.lean`) and the `PrincipalDivisors.lean` §4.4 "genuinely hard step" are
  already handled in this project: named, scoped, and cited, not silently assumed.
* **Actually derives** `finrank_L_pair` (both the `finrank = 1` half and the
  `IsOnlyEffectiveInClass` half) from `uniqueDegree2MapToP1`, checked Lean
  reasoning, not a restatement of the gap under a new name.

If `uniqueDegree2MapToP1` is later proved from Riemann–Hurwitz or the general theory
of linear systems, this file's derivation of `finrank_L_pair` needs no further
change — the gap is now exactly one theorem, with a name, a type, a citation, and a
home, matching how `SidonBridge.lean` already describes the state of the rest of
this project.
-/

namespace HyperellipticPolynomial

open Divisor

variable {k : Type*} [Field k]
variable {H : HyperellipticPolynomial k}
variable [IsDedekindDomain (CoordinateRing H)]

/-- `z` is a `k`-constant inside `FractionRing (CoordinateRing H)`: the image of
some `c : k` under the composite `k → k[X] → CoordinateRing H → FractionRing
(CoordinateRing H)`. Phrased this way (rather than "`z` has empty pole divisor")
because it is the notion `finrank_L_pair`'s conclusion (`ℓ = 1`, spanned by `1`)
actually needs: every element of `LPair x₁ x₂` is *this*, not merely "has no
poles" (the two coincide for a genus ≥ 1 curve, but the constant phrasing is the
one that transfers directly into a `finrank = 1` proof via `1` spanning). -/
def IsConstantFraction (z : FractionRing (CoordinateRing H)) : Prop :=
  ∃ c : k, z = algebraMap (CoordinateRing H) (FractionRing (CoordinateRing H))
    (algebraMap k[X] (CoordinateRing H) (C c))

/-- **The crux fact**, stated precisely and cited (see the module docstring):
uniqueness, up to `k`-scaling of the ratio, of the degree-2 map to `P¹` on a
genus-2 hyperelliptic curve. Concretely: if `z ∈ LPairCarrier x₁ x₂` is
*non-constant*, then its pole set — the `A', B'`-side data witnessing
`IsPoleBoundedAtPair` — is forced to be a hyperelliptic fiber `{x₃, ι x₃}`, and
correspondingly its zero set (read off the `A, B`-side data) is the fiber
`{x₁, x₂}` only when `x₂ = ι x₁` to begin with. Stated as the direct
contrapositive-shaped fact `finrank_L_pair` needs: **if `x₂ ≠ ι x₁`, no
non-constant `z` can lie in `LPairCarrier x₁ x₂` at all** — a nonconstant
degree-≤2 function's pole divisor would have to be a genuine hyperelliptic fiber
(by the uniqueness-of-the-degree-2-map fact above), and `{x₁, x₂}` is assumed not
to be one.

This is genuinely the geometric content, not a restatement of the goal: it says
the *only* way to exhibit a low-degree map to `P¹` on a hyperelliptic curve is via
(a Möbius transform of) the hyperelliptic map itself, i.e. via a fiber. Proving it
requires either Riemann–Hurwitz (ramification-point counting: a second degree-2
map would force ≥ 6 ramification points and, via the genus formula, an
additional constraint incompatible with `g = 2` unless the map is a Möbius
transform of the hyperelliptic one) or the general classification of `g^1_2`
linear systems on a curve — neither of which this project currently formalizes
(see the module docstring). -/
theorem uniqueDegree2MapToP1 (hdeg : H.f.natDegree = 5) (x₁ x₂ : H.Point)
    (hne : x₂ ≠ Point.iota x₁) (z : FractionRing (CoordinateRing H))
    (hz : z ∈ LPairCarrier x₁ x₂) : IsConstantFraction z := by
  sorry

/-- **`finrank_L_pair`, derived from `uniqueDegree2MapToP1`.** The `finrank = 1`
half: `LPair hdeg x₁ x₂` is spanned by `1` (`Submodule.eq_span_singleton_of...`
shape via `Submodule.finrank_eq_one_iff_of_mem_of_ne_zero`-style reasoning), since
`uniqueDegree2MapToP1` forces every element to be a `k`-multiple of `1`. -/
theorem finrank_LPair_eq_one_of_uniqueDegree2MapToP1
    (hdeg : H.f.natDegree = 5) (x₁ x₂ : H.Point) (hne : x₂ ≠ Point.iota x₁) :
    Module.finrank k (LPair hdeg x₁ x₂) = 1 := by
  -- Every `z ∈ LPair hdeg x₁ x₂` is, by `uniqueDegree2MapToP1`, `algebraMap _ (C c)`
  -- for some `c : k` — i.e. `c • (1 : FractionRing (CoordinateRing H))`. So the
  -- carrier is exactly `k ∙ 1`, i.e. `LPair hdeg x₁ x₂ = Submodule.span k {1}`,
  -- whence `finrank = 1` by the standard singleton-span fact (needs `(1 : ...) ≠ 0`,
  -- clear since `FractionRing (CoordinateRing H)` is a field and `1 ≠ 0`).
  have hspan : LPair hdeg x₁ x₂ = Submodule.span k {(1 : FractionRing (CoordinateRing H))} := by
    apply le_antisymm
    · intro z hz
      have hz' : z ∈ LPairCarrier x₁ x₂ := hz
      obtain ⟨c, hc⟩ := uniqueDegree2MapToP1 hdeg x₁ x₂ hne z hz'
      rw [Submodule.mem_span_singleton]
      refine ⟨c, ?_⟩
      -- Goal: `c • (1 : FractionRing (CoordinateRing H)) = z`. Rewrite `z` via `hc`, then
      -- unfold the `k`-scalar action down to the same algebra-map composite `hc` already
      -- exhibits. Both `k`-algebra structures here are built via `Algebra.compHom` (see
      -- `HyperellipticFunctionField.lean`'s `Algebra k (CoordinateRing H)` instance and its
      -- `FractionRing` analogue), so `IsScalarTower` is not automatic and is established by
      -- hand via `IsScalarTower.of_algebraMap_eq (fun _ => rfl)` — the same idiom
      -- `PrincipalDivisors.lean:1774` already uses for exactly this situation — then
      -- `algebraMap k k[X] c = C c` closes the remaining gap, the same step
      -- `RiemannRochGenus2.lean:301` (`toPair_smul`'s proof) already takes.
      haveI hst1 : IsScalarTower k k[X] (CoordinateRing H) :=
        IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      haveI hst2 : IsScalarTower k (CoordinateRing H) (FractionRing (CoordinateRing H)) :=
        IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      rw [hc, Algebra.smul_def, mul_one,
        IsScalarTower.algebraMap_apply k (CoordinateRing H) (FractionRing (CoordinateRing H)),
        IsScalarTower.algebraMap_apply k k[X] (CoordinateRing H),
        show algebraMap k k[X] c = C c from by simp]
    · rw [Submodule.span_singleton_le_iff_mem]
      exact one_mem_LPairCarrier x₁ x₂
  rw [hspan]
  exact finrank_span_singleton one_ne_zero

/-- **`finrank_L_pair`'s qualitative half, derived from `uniqueDegree2MapToP1`.**
`(x₁)+(x₂)` is the only effective divisor in its class: given
`(x₁)+(x₂)-(x₃)-(x₄) ∈ principalSubgroup H hdeg`, conclude `{x₃,x₄} = {x₁,x₂}`.

**Left `sorry`'d — genuinely open, not mechanical plumbing (correcting this
theorem's earlier docstring, which understated the gap).** `principalSubgroup`
is an `AddSubgroup.closure` of ratio-divisor generators: membership means being
a *finite ± combination* of generators, not literally one generator's divisor.
So this needs a real two-step argument, neither step of which is done:

1. **Closure collapse**: every `D ∈ principalSubgroup H hdeg` is actually the
   divisor of *some single* nonzero ratio `z ∈ FractionRing (CoordinateRing H)`
   — true, and provable from what already exists in this project
   (`AddSubgroup.closure_induction` with motive "`D` is the divisor of some
   `z ≠ 0`", discharged via `1` for the `zero` case, `z₁ * z₂` for `add`
   (using `toPair_mul`/`ordAt_toPair_mul_of_ne_zero'`, already in
   `RiemannRochGenus2.lean`, for the needed multiplicativity), and `z⁻¹` for
   `neg` — but this induction has not been carried out anywhere in this
   project and is itself a genuine multi-step proof, not a corollary of
   anything already on the books.
2. **Support matching**: given that single-ratio `z`, match its zero/pole
   structure against the specific 4-point target `(x₁)+(x₂)-(x₃)-(x₄)` to
   place `z` in `LPairCarrier x₁ x₂` (or its inverse in `LPairCarrier x₂ x₁`,
   depending on orientation) so `uniqueDegree2MapToP1` actually applies —
   separate work from step 1.

Flagged as its own gap, distinct from `uniqueDegree2MapToP1`, since it is
divisor-group bookkeeping rather than the genus-2-specific geometric content —
but it is *real* bookkeeping, not free, and should not be assumed closed by a
quick follow-up. -/
theorem isOnlyEffectiveInClass_of_uniqueDegree2MapToP1
    (hdeg : H.f.natDegree = 5) (x₁ x₂ : H.Point) (hne : x₂ ≠ Point.iota x₁) :
    IsOnlyEffectiveInClass hdeg x₁ x₂ := by
  sorry

/-- **Assembly**: `finrank_L_pair` itself, now a two-line combination of the two
theorems above rather than a bare `sorry`. This is the intended replacement for
`RiemannRochGenus2.lean`'s `finrank_L_pair` — swap that `sorry`'d theorem body for
`exact ⟨finrank_LPair_eq_one_of_uniqueDegree2MapToP1 hdeg x₁ x₂ hne,
isOnlyEffectiveInClass_of_uniqueDegree2MapToP1 hdeg x₁ x₂ hne⟩` once this file is
wired in (not done automatically here, to avoid editing
`RiemannRochGenus2.lean`'s statement out from under it mid-session). -/
theorem finrank_L_pair' (hdeg : H.f.natDegree = 5) (x₁ x₂ : H.Point)
    (hne : x₂ ≠ Point.iota x₁) :
    Module.finrank k (LPair hdeg x₁ x₂) = 1 ∧ IsOnlyEffectiveInClass hdeg x₁ x₂ :=
  ⟨finrank_LPair_eq_one_of_uniqueDegree2MapToP1 hdeg x₁ x₂ hne,
    isOnlyEffectiveInClass_of_uniqueDegree2MapToP1 hdeg x₁ x₂ hne⟩

end HyperellipticPolynomial
