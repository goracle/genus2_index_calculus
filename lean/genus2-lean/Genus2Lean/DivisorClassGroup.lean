import Mathlib
import Genus2Lean.HyperellipticFunctionField
import Genus2Lean.AffinePoints
noncomputable section

set_option linter.style.header false

open Polynomial
open Classical

/-!
# Genus-2 index calculus: the divisor group, principal divisors, and `J` as a divisor-class group

`AffinePoints.lean` supplies the affine point type `H.Point` and the point-level
involution `ι`, and flags as the next gap: "the Jacobian `J` (or a degree-0-divisor-
class stand-in for it) and the embedding map `s : C → J`." This file supplies that
layer.

Design choices, made explicit rather than silently assumed:

* **Divisors.** `Divisor H := H.Point →₀ ℤ`, the free abelian group on affine points.
  This is the standard model of the divisor group `Div(C)` restricted to the affine
  part of `C` — see the same restriction-to-affine-points design note already made in
  `AffinePoints.lean` (points at infinity are a flagged, not silently assumed, gap).
* **Degree.** `deg : Divisor H →+ ℤ`, the sum of coefficients — well-defined on
  `Finsupp` since only finitely many coefficients are nonzero.
* **Principal divisors.** Advisory-7 §4's Sidon theorem is a statement purely about
  the map `s : C(k) → J`, `x ↦ (x) - δ`, and does not require the full function-field
  machinery of "divisor of a function." Building the genuine principal-divisor
  subgroup (zeros minus poles of rational functions on `C`) is a substantial
  additional layer on top of `HyperellipticFunctionField.lean`'s coordinate ring, and
  is *not* built here — flagged as an explicit gap below (`PrincipalDivisors`,
  currently a hypothesis-level placeholder subgroup, not derived from `CoordinateRing`).
  What *is* proved unconditionally here (`sub_ne_principal_of_...` style lemmas are
  deferred; see below) is the part advisory-7 actually uses: the map
  `s(x) = (x) - δ` composed with the quotient by principal divisors, and its raw,
  divisor-level injectivity/additivity properties before quotienting.
* **`J`.** The quotient `Divisor H ⧸ (degree-0 part ⊓ principal divisors)` is the
  genuine Jacobian model, `Pic⁰(C)`. Since principal divisors are left abstract here
  (see above), `J` is built as a quotient by an *arbitrary* subgroup `P` of
  `Divisor0 H` satisfying the properties principal divisors are known to have
  (in particular: every principal divisor has degree 0, this is `P`'s defining
  containment `P ≤ Divisor0 H`), rather than committing to `P` being exactly the
  principal divisors of `CoordinateRing H`. This keeps the file honest about what is
  and is not derived from the earlier function-field construction.
-/

namespace HyperellipticPolynomial

variable {k : Type*} [Field k]
variable {H : HyperellipticPolynomial k}

/-- The divisor group of the affine part of `C`: the free abelian group on
affine points, `H.Point →₀ ℤ`. Points at infinity are excluded, matching the
affine-only scope already fixed by `AffinePoints.lean`. -/
def Divisor (H : HyperellipticPolynomial k) : Type _ :=
  H.Point →₀ ℤ

noncomputable instance : AddCommGroup (Divisor H) :=
  inferInstanceAs (AddCommGroup (H.Point →₀ ℤ))

namespace Divisor

/-- The divisor `(P)` of a single point `P`, with coefficient `1`. -/
noncomputable def single (P : H.Point) : Divisor H :=
  Finsupp.single P 1

/-- The degree homomorphism `Div(C) → ℤ`, summing coefficients. Built via
`Finsupp.liftAddHom` (lifting the constant family of identity homomorphisms
`ℤ →+ ℤ` at each point) rather than `Finsupp.sumAddHom`, so that `deg_single`
below reduces via the directly-documented `Finsupp.liftAddHom_apply_single`. -/
noncomputable def deg : Divisor H →+ ℤ :=
  Finsupp.liftAddHom (fun (_ : H.Point) => AddMonoidHom.id ℤ)

@[simp] theorem deg_single (P : H.Point) : deg (single P) = 1 := by
  show (Finsupp.liftAddHom (fun (_ : H.Point) => AddMonoidHom.id ℤ)) (Finsupp.single P 1) = 1
  rw [Finsupp.liftAddHom_apply_single]
  rfl

/-- The coefficient-at-`P` homomorphism `Div(C) → ℤ`. Callers elsewhere
(`PrincipalSubgroupCollapse.lean`) need to extract the `ℤ`-coefficient of a
`Divisor H` at a chosen point via the `AddMonoidHom` API, exactly as `deg` does
above, rather than through raw `Finsupp` application: `Divisor H` is a plain
`def`, not `abbrev`, over `H.Point →₀ ℤ`, so it does not unfold to expose
`Finsupp`'s `DFunLike` application at ordinary transparency (see the discussion
in `PrincipalDivisorSubgroup.lean`'s `divToPair`). Built via
`Finsupp.applyAddHom`, the library's own `AddMonoidHom` version of evaluation
at a point, mirroring `deg`'s use of `Finsupp.liftAddHom`. -/
noncomputable def coeffAt (P : H.Point) : Divisor H →+ ℤ :=
  Finsupp.applyAddHom P

-- **UNVERIFIED step** (no local Lean install to check against a live goal):
-- `Finsupp.applyAddHom_apply` is assumed to be the simp-normal-form lemma
-- unfolding `Finsupp.applyAddHom P f` to `f P`; if that name is wrong, the
-- `simp` fallback should still close the goal — worst case replace the whole
-- proof body with `simp [Finsupp.applyAddHom_apply]` or `simp [coeffAt]`.
-- Condition stated as `if P = Q` (not `if Q = P`) to match how
-- `PrincipalSubgroupCollapse.lean` consumes this lemma: it derives a
-- `hQP : Q ≠ P` hypothesis and passes `Ne.symm hQP : P ≠ Q` to `if_neg`,
-- which only typechecks against this orientation.
@[simp] theorem coeffAt_single (P Q : H.Point) :
    coeffAt P (single Q) = if P = Q then 1 else 0 := by
  show Finsupp.applyAddHom P (Finsupp.single Q 1) = if P = Q then 1 else 0
  simp [Finsupp.applyAddHom_apply, Finsupp.single_apply, eq_comm]

@[simp] theorem coeffAt_single_self (P : H.Point) : coeffAt P (single P) = 1 := by
  rw [coeffAt_single, if_pos rfl]

@[simp] theorem deg_sub (D₁ D₂ : Divisor H) : deg (D₁ - D₂) = deg D₁ - deg D₂ :=
  map_sub deg D₁ D₂

@[simp] theorem deg_single_sub_single (P Q : H.Point) :
    deg (single P - single Q) = 0 := by
  simp

/-- The degree-0 divisors, as a subgroup of `Divisor H`. `AddMonoidHom.ker` on an
`AddCommGroup` target already returns an `AddSubgroup` in this Mathlib version
(no separate `.toAddSubgroup` projection needed). -/
def Divisor0 (H : HyperellipticPolynomial k) : AddSubgroup (Divisor H) :=
  (deg : Divisor H →+ ℤ).ker

theorem mem_Divisor0_iff {D : Divisor H} : D ∈ Divisor0 H ↔ deg D = 0 :=
  AddMonoidHom.mem_ker

theorem single_sub_single_mem_Divisor0 (P Q : H.Point) :
    single P - single Q ∈ Divisor0 H :=
  mem_Divisor0_iff.mpr (deg_single_sub_single P Q)

end Divisor

open Divisor

/-!
## Principal divisors, and `J` as a divisor-class group

Principal divisors are taken here as an arbitrary subgroup `P` of `Divisor0 H`
satisfying only the one property advisory-7's argument structurally needs and that
genuine principal divisors are known to have: containment in the degree-0 divisors.
This is a deliberate weakening relative to deriving `P` from `CoordinateRing H`
directly (flagged in the module docstring above as the remaining gap). Every lemma
proved against this abstract `P` therefore holds a fortiori for the true principal
divisor subgroup, once/if that is built.
-/

/-- A candidate "principal divisor" subgroup: any subgroup of the degree-0
divisors. The genuine principal divisors of `C` (zeros-minus-poles of elements of
`CoordinateRing H`, or more precisely of the function field) form one such
subgroup; that identification is *not* made here (see module docstring) — this
structure packages only the containment fact downstream arguments use. -/
structure PrincipalDivisorData (H : HyperellipticPolynomial k) where
  /-- The subgroup of principal (or principal-like) divisors. -/
  P : AddSubgroup (Divisor H)
  /-- Principal divisors have degree 0 — the one fact about principal divisors
  that the Jacobian quotient construction below actually uses. -/
  le_Divisor0 : P ≤ Divisor0 H

variable (D : PrincipalDivisorData H)

/-- `J`, the Jacobian stand-in: degree-0 divisors modulo (candidate) principal
divisors, `Pic⁰(C) = Div⁰(C) / P`. This is the object advisory-7 §4 calls `J`. -/
def Jacobian (H : HyperellipticPolynomial k) (D : PrincipalDivisorData H) : Type _ :=
  (Divisor0 H) ⧸ D.P.addSubgroupOf (Divisor0 H)

noncomputable instance : AddCommGroup (Jacobian H D) :=
  inferInstanceAs (AddCommGroup ((Divisor0 H) ⧸ D.P.addSubgroupOf (Divisor0 H)))

/-- The quotient map `Div⁰(C) → J`. -/
noncomputable def toJacobian : Divisor0 H →+ Jacobian H D :=
  QuotientAddGroup.mk' (D.P.addSubgroupOf (Divisor0 H))

/-- **The embedding `s : C(k) → J`**, `x ↦ (x) - δ`, for a fixed base point `δ`
of degree 1 (here: a fixed affine point `δ₀ : H.Point`, giving `δ := (δ₀)`,
matching advisory-7 §4's phrasing "let `δ` be a `k`-rational divisor of degree 1").
This is exactly the map the Forey–Fresán–Kowalski Sidon theorem is stated about. -/
noncomputable def s (δ₀ : H.Point) (P : H.Point) : Jacobian H D :=
  toJacobian D ⟨single P - single δ₀, single_sub_single_mem_Divisor0 P δ₀⟩

/-- Unfolding `s`: it factors through the divisor `(x) - (δ)` and the quotient map,
as claimed. Stated as its own lemma since downstream Sidon-set arguments (the
additive-energy computation of §4, already formalized against abstract `G` in
`SidonEnergy.lean`) will want to reason about `s x₁ + s x₂ = s x₃ + s x₄` purely at
the level of `Divisor0 H`/`toJacobian`, not by re-unfolding `single`/`Finsupp`. -/
theorem s_eq_toJacobian_sub (δ₀ P : H.Point) :
    s D δ₀ P = toJacobian D ⟨single P - single δ₀, single_sub_single_mem_Divisor0 P δ₀⟩ :=
  rfl

/-- `s x₁ + s x₂ = s x₃ + s x₄` is equivalent, purely as a fact about divisors
composed with `toJacobian`, to `(x₁) + (x₂) - (x₃) - (x₄)` lying in `P` — the
divisor-level form of the matching condition that a genuine proof of the FFK
theorem (still not attempted here) would need to unpack via principal-divisor /
function-field arguments to recover the point-level dichotomy
`{x₁,x₂} = {x₃,x₄} ∨ (x₂ = ι x₁ ∧ x₄ = ι x₃)`. -/
theorem s_add_s_eq_s_add_s_iff (δ₀ x₁ x₂ x₃ x₄ : H.Point) :
    s D δ₀ x₁ + s D δ₀ x₂ = s D δ₀ x₃ + s D δ₀ x₄ ↔
      (single x₁ + single x₂ - single x₃ - single x₄ : Divisor H) ∈ D.P := by
  have hmem : ∀ y z : H.Point,
      single y - single z ∈ Divisor0 H := single_sub_single_mem_Divisor0
  -- Name the four degree-0 divisors `(xᵢ) - (δ₀)` as elements of the subtype
  -- `Divisor0 H`, so that both directions can be proved via one coercion
  -- computation (`hcoe`) instead of duplicating it.
  set a₁ : Divisor0 H := ⟨single x₁ - single δ₀, hmem x₁ δ₀⟩
  set a₂ : Divisor0 H := ⟨single x₂ - single δ₀, hmem x₂ δ₀⟩
  set a₃ : Divisor0 H := ⟨single x₃ - single δ₀, hmem x₃ δ₀⟩
  set a₄ : Divisor0 H := ⟨single x₄ - single δ₀, hmem x₄ δ₀⟩
  -- The coercion of `(a₁ + a₂) - (a₃ + a₄) : Divisor0 H` back down to
  -- `Divisor H` is exactly `(x₁) + (x₂) - (x₃) - (x₄)`: the `δ₀` terms cancel
  -- in pairs. Proved by unfolding the `AddSubgroup`/`Subtype` coercion to
  -- `Subtype.val` and closing with `abel` in the ambient group `Divisor H`,
  -- rather than via `simp`, to keep this step auditable.
  have hcoe : (((a₁ + a₂) - (a₃ + a₄) : Divisor0 H) : Divisor H) =
      (single x₁ + single x₂ - single x₃ - single x₄ : Divisor H) := by
    show a₁.1 + a₂.1 - (a₃.1 + a₄.1) = single x₁ + single x₂ - single x₃ - single x₄
    show (single x₁ - single δ₀) + (single x₂ - single δ₀)
        - ((single x₃ - single δ₀) + (single x₄ - single δ₀))
        = single x₁ + single x₂ - single x₃ - single x₄
    abel
  constructor
  · intro h
    have h' : toJacobian D a₁ + toJacobian D a₂ = toJacobian D a₃ + toJacobian D a₄ := h
    rw [← map_add, ← map_add] at h'
    have h'' := (QuotientAddGroup.eq_iff_sub_mem
      (N := D.P.addSubgroupOf (Divisor0 H))).mp h'
    rw [AddSubgroup.mem_addSubgroupOf] at h''
    rwa [hcoe] at h''
  · intro h
    have h' : ((a₁ + a₂) - (a₃ + a₄) : Divisor0 H) ∈ D.P.addSubgroupOf (Divisor0 H) := by
      rw [AddSubgroup.mem_addSubgroupOf, hcoe]; exact h
    have h'' := (QuotientAddGroup.eq_iff_sub_mem
      (N := D.P.addSubgroupOf (Divisor0 H))).mpr h'
    -- `h''` is stated via the raw quotient-mk coercion `↑(a₁ + a₂) = ↑(a₃ + a₄)`,
    -- which is defeq to but not syntactically `map_add`-shaped against
    -- `toJacobian`, so bridge it with `show`/`QuotientAddGroup.mk'_apply` instead
    -- of trying to `rw [map_add]` into it directly.
    have h''' : toJacobian D (a₁ + a₂) = toJacobian D (a₃ + a₄) := h''
    rwa [map_add, map_add] at h'''

end HyperellipticPolynomial
