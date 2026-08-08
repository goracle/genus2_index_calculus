import Mathlib
import Genus2Lean.HyperellipticFunctionField
import Genus2Lean.AffinePoints
import Genus2Lean.DivisorClassGroup
import Genus2Lean.PrincipalDivisors
import Genus2Lean.PrincipalDivisorSubgroup
import Genus2Lean.FFKSidon

set_option linter.style.header false
set_option linter.style.show false
set_option linter.unusedVariables false

noncomputable section

set_option linter.style.header false

open Polynomial

/-!
# `HyperellipticClass` for `principalDivisorData`

`FFKSidon.lean` packages, as an explicit hypothesis on an abstract `D : PrincipalDivisorData
H`, the fact that the fiber-difference divisor `(x₁) + (ι x₁) - (x₃) - (ι x₃)` is principal
(`D.HyperellipticClass`) — needed for the easy direction of the FFK dichotomy
(`sum_eq_of_involution_swap`/`sum_eq_of_dichotomy`). `PrincipalDivisorSubgroup.lean` supplies
a genuine, non-abstract `D := principalDivisorData H hdeg`. This file attempts to prove
`(principalDivisorData H hdeg).HyperellipticClass`, i.e. to actually exhibit that divisor as
principal for the concrete `D`, rather than leave it a further abstract hypothesis.

**The function.** For `a : k`, `linX a := X - C a ∈ k[X]`, and `g a := toPair H (linX a) 0 =
algebraMap k[X] (CoordinateRing H) (linX a)` — the coordinate-ring element corresponding to
"the polynomial function `x ↦ x - a`". Its zero set is exactly the fiber of the `x`-coordinate
map over `a`: `{(a, b) : b² = f(a)}`, i.e. `{Q : Q.X = a}`. For `a` with `f(a) ≠ 0` this fiber
is the two-point set `{P, ι P}` where `P = (a, b)`, `b² = f(a)`, `b ≠ 0`; for `a` a root of `f`
(a Weierstrass point) it is the single fixed point `(a, 0) = ι (a, 0)`, and `g a` should vanish
there to order `2` (matching `single P + single (ι P) = 2 • single P` in that degenerate case).

**What `ordInfOfPair` says.** `linX a` has degree `1`, so `ordInfOfPair (linX a) 0 = -2`
(`PrincipalDivisors.lean`'s formula: `-(max (2·1) 0)`) — `g a` alone has a pole of order `2` at
infinity and is *not* itself in `principalSubgroup`'s generating set (which requires
`ordInfOfPair = 0`). This matches the geometry: `g a`'s affine divisor `(P) + (ι P)` has affine
degree `2`, not `0` — the missing degree is the order-2 pole at the (unmodeled) point at
infinity. What *is* in `principalSubgroup`, and is exactly what `HyperellipticClass` needs, is
the difference `g x₁.X / g x₃.X` for two points `x₁, x₃` — its poles at infinity cancel
(`ordInfOfPair`'s formula depends only on `natDegree`, and both `linX` are degree `1`), leaving
affine divisor exactly `(x₁) + (ι x₁) - (x₃) - (ι x₃)`, degree `0`, with no help needed from a
point at infinity.

**A genuine gap in `principalSubgroup` itself, not just a hard proof step.** `principalSubgroup`
is `AddSubgroup.closure` of the set `{D | ∃ A B S ..., ordInfOfPair A B = 0 ∧ D = divToPair A B
S}`. `AddSubgroup.closure S` contains sums/differences *of elements of `S`* — it does not
automatically contain every difference of two things that individually fail to be in `S` but
whose difference "happens to be nice". Since `divToPair (linX x₁.X) 0 S₁` and
`divToPair (linX x₃.X) 0 S₃` each individually have `ordInfOfPair = -2 ≠ 0` (shown above), *neither
is itself a member of `principalSubgroup`'s generating set*, and nothing proved so far shows
their difference is in the closure either. This is not resolved by a harder proof of the same
containment claim — it means `principalSubgroup`'s generating set, as currently defined, is
too narrow to witness this specific fact, and either needs widening (e.g. to allow generators
built from *pairs* `(A₁,B₁,S₁), (A₂,B₂,S₂)` whose `ordInfOfPair`s merely agree, not both being
zero — the genuinely correct principal-divisor condition is "the function has a well-defined
divisor", i.e. finite pole/zero locus, with degree-0-on-the-compactified-curve following from
`deg_div_eq_zero_deg5` applied to the *quotient* `g₁/g₃` rather than each numerator/denominator
separately) or the fiber-difference fact needs to be established by some other route entirely
(e.g. directly verifying `AddSubgroup.closure_le`-style containment against a redefined
subgroup). **This file does not resolve that; `hyperellipticClass_diff_mem`/the final theorem
below are left `sorry`'d for this reason, not merely because `ordAt_linX_eq` was open (it is now
fully proved — see below).** Fixing
this properly means revisiting `PrincipalDivisorSubgroup.lean`'s `principalSubgroup` definition
before this file's final theorem can be completed, not just filling in more Lean here.

## Summary of what's proved vs. open in this file
-/

/-!
* `linX_mem_pointIdeal_iff` (proved): `g a ∈ pointIdeal Q ↔ Q.X = a` — vanishing-locus
  membership, a direct corollary of `pointIdeal_ne_of_ne`'s own computation (`evalAtPoint Q`
  applied to `algebraMap (X - C a)` is `Q.X - a`). This is real and mechanical.
* **`ordAt_linX_eq` (now fully proved, no `sorry`).** The *exact multiplicity* of vanishing:
  `ordAt Q (linX a) 0 = 1` when `Q.X = a` and `Q.Y ≠ 0` (the generic, unramified case), vs
  `= 2` when `Q.X = a` and `Q.Y = 0` (the Weierstrass/ramification case, now requiring
  `Squarefree H.f` as an explicit hypothesis — needed for the simple-root argument at a
  Weierstrass point), vs `= 0` when `Q.X ≠ a`. Closed via a genuine local-uniformizer argument
  at `pointIdeal Q`: `linX a` (unramified case) or `y H` (ramified case) is shown to be a
  uniformizer of the DVR-localization at `pointIdeal Q` by direct Nakayama-style ideal
  arguments, with the ramified case's final multiplicity-2 count closed via
  `Associates.count` additivity over the factorization `(y H)^2 = g * algebraMap r`.
* Everything downstream of `ordAt_linX_eq` in this file (`divToPair_linX_eq_of_unramified`/
  `_ramified`) is conditional on it and is otherwise mechanical bookkeeping (matching
  `PrincipalDivisors.lean`'s own stated policy: hard steps get isolated, named `sorry`s, not
  silently assumed or worked around).
* **The final theorem, `hyperellipticClass_principalDivisorData`, has a second, separate open
  gap beyond `ordAt_linX_eq`**: it needs `principalSubgroup H hdeg` to contain a *difference*
  of two `divToPair` values, neither of which individually satisfies `principalSubgroup`'s own
  membership condition (`ordInfOfPair = 0`) — see that theorem's own docstring below for why
  this is a gap in `principalSubgroup`'s definition itself, not just a harder proof.
-/

namespace HyperellipticPolynomial

open Divisor

variable {k : Type*} [Field k]
variable {H : HyperellipticPolynomial k}

/-- The polynomial `X - C a`, i.e. "the coordinate function `x ↦ x - a`". -/
def linX (a : k) : k[X] := X - C a

@[simp] theorem linX_natDegree (a : k) : (linX a).natDegree = 1 := by
  unfold linX
  compute_degree!

theorem linX_ne_zero (a : k) : linX a ≠ 0 := by
  intro h
  have := linX_natDegree a
  rw [h, natDegree_zero] at this
  exact absurd this (by decide)

/-- `ordInfOfPair (linX a) 0 = -2`: `linX a` has degree `1`, so by
`PrincipalDivisors.lean`'s formula the pole order at infinity is `2 * 1 = 2`. -/
@[simp] theorem ordInfOfPair_linX (a : k) : ordInfOfPair (linX a) 0 = -2 := by
  unfold ordInfOfPair
  rw [if_neg (by simp [linX_ne_zero a])]
  simp [linX_natDegree]

/-- `linX a`'s image in `CoordinateRing H` (i.e. `g a := toPair H (linX a) 0`) lies in
`pointIdeal Q` exactly when `Q.X = a` — the vanishing locus of `x ↦ x - a` is exactly the
fiber of the `x`-coordinate over `a`. Proved the same way `pointIdeal_ne_of_ne` computes
`evalAtPoint _ (algebraMap _ (X - C _))`, just packaged as an iff at a single point instead
of a distinctness argument across two. -/
theorem toPair_linX_mem_pointIdeal_iff [IsDedekindDomain (CoordinateRing H)]
    (a : k) (Q : H.Point) :
    toPair H (linX a) 0 ∈ pointIdeal Q ↔ Q.X = a := by
  have hg : toPair H (linX a) 0 = algebraMap k[X] (CoordinateRing H) (linX a) := by
    unfold toPair; simp
  rw [hg]
  unfold linX
  change evalAtPoint Q (algebraMap k[X] (CoordinateRing H) (X - C a)) = 0 ↔ Q.X = a
  have hXeval : evalAtPoint Q (algebraMap k[X] (CoordinateRing H) X) = Q.X := by
    change Polynomial.eval₂ (Polynomial.evalRingHom Q.val.1) Q.val.2 (C X) = Q.X
    simp [Point.X]
  have hCeval : evalAtPoint Q (algebraMap k[X] (CoordinateRing H) (C a)) = a := by
    change Polynomial.eval₂ (Polynomial.evalRingHom Q.val.1) Q.val.2 (C (C a)) = a
    simp
  rw [map_sub (algebraMap k[X] (CoordinateRing H)), map_sub (evalAtPoint Q),
      hXeval, hCeval, sub_eq_zero]

/-- **§A: the easy case, fully proved.** Away from the fiber (`Q.X ≠ a`), `g a := toPair H
(linX a) 0` doesn't vanish at `Q` at all, so its local valuation at `pointIdeal Q` is trivial
(`= 1`) and `ordAt = 0`. Chain: `Q.X ≠ a` gives `g a ∉ pointIdeal Q`
(`toPair_linX_mem_pointIdeal_iff`), hence `pointIdeal Q ∤ Ideal.span {g a}`
(`Ideal.dvd_span_singleton`, "to divide is to contain", contrapositive), hence
`¬ (intValuationDef (g a) < 1)` (`intValuation_lt_one_iff_dvd`), which combined with
`intValuation_le_one` (always `≤ 1`) forces equality to `1`, so `WithZero.log = 0` and
`ordAt = -0 = 0`. **PLAUSIBLE, not checked against a live goal**: the exact lemma names
(`IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_dvd`,
`intValuation_le_one`, `Ideal.dvd_span_singleton`) and their precise argument shapes
(explicit vs. implicit, whether stated for `v.asIdeal` directly or need unfolding through
`pointHeightOne`) were sourced from Mathlib documentation, not confirmed against this file's
actual goal state. -/
theorem ordAt_linX_eq_zero_of_ne [IsDedekindDomain (CoordinateRing H)]
    (a : k) (Q : H.Point) (h_bot : pointIdeal Q ≠ ⊥) (hne : Q.X ≠ a) :
    ordAt Q (linX a) 0 = 0 := by
  have hnotmem : toPair H (linX a) 0 ∉ pointIdeal Q :=
    fun hmem => hne ((toPair_linX_mem_pointIdeal_iff a Q).mp hmem)
  have hgne : toPair H (linX a) 0 ≠ 0 := by
    intro hz
    apply hnotmem
    rw [hz]
    exact Submodule.zero_mem _
  have hnotdvd :
      ¬ pointIdeal Q ∣ Ideal.span ({toPair H (linX a) 0} : Set (CoordinateRing H)) := by
    rw [Ideal.dvd_span_singleton]
    exact hnotmem
  have hval_not_lt : ¬ (pointHeightOne Q h_bot).intValuation (toPair H (linX a) 0) < 1 := by
    rw [(pointHeightOne Q h_bot).intValuation_lt_one_iff_dvd]
    exact hnotdvd
  have hval_le : (pointHeightOne Q h_bot).intValuation (toPair H (linX a) 0) ≤ 1 :=
    (pointHeightOne Q h_bot).intValuation_le_one (toPair H (linX a) 0)
  have hval_eq : (pointHeightOne Q h_bot).intValuation (toPair H (linX a) 0) = 1 :=
    le_antisymm hval_le (not_lt.mp hval_not_lt)
  unfold ordAt
  rw [if_neg hgne, dif_neg h_bot]
  show -WithZero.log ((pointHeightOne Q h_bot).intValuation (toPair H (linX a) 0)) = 0
  rw [hval_eq]
  simp

/-- **§B: the hard case, `Q.X = a`, split into unramified/ramified sub-steps rather than
left as one opaque `sorry`.** Both sub-steps need the same genuine local-uniformizer input
absent from `PrincipalDivisors.lean` (see the module docstring): a description of the
`pointIdeal Q`-adic valuation of `linX a`'s image in terms of a chosen uniformizer at
`pointIdeal Q`. **Pointer for whoever picks this up**: Mathlib has
`IsDedekindDomain.HeightOneSpectrum.intValuation_exists_uniformizer`
(`∃ π, v.intValuation π = ofAdd (-1)`) and `intValuation_le_pow_iff_dvd`
(`v.intValuation r ≤ ofAdd (-n) ↔ v^n ∣ span {r}`) — the latter is the mechanical bridge
`§B.1d` below is built around. **§B.1 (unramified) is further split into `§B.1a`–`§B.1d`
below** (dvd direction proved; unit-`y H` fact, not-squared-dvd, and the final assembly each
`sorry`'d separately) rather than left as one lemma, per this session's scaffolding
convention: smaller named `sorry`s, easiest first, rather than one opaque block.

**§B.1a, mechanical, fully proved.** `pointIdeal Q` divides `Ideal.span {g a}` at all —
the easy half of pinning down the multiplicity, reusing the same
`toPair_linX_mem_pointIdeal_iff` + `Ideal.dvd_span_singleton` combo as §A, just without the
final "hence count = 0" step (here we want count ≥ 1, not = 0). -/
theorem ordAt_linX_eq_one_of_unramified_dvd [IsDedekindDomain (CoordinateRing H)]
    (a : k) (Q : H.Point) (heq : Q.X = a) :
    pointIdeal Q ∣ Ideal.span ({toPair H (linX a) 0} : Set (CoordinateRing H)) := by
  rw [Ideal.dvd_span_singleton]
  exact (toPair_linX_mem_pointIdeal_iff a Q).mpr heq

/-- **§B.1b, self-contained algebra fact, now proved.** At an unramified point (`Q.Y ≠ 0`),
`y H`'s image in the residue field `CoordinateRing H ⧸ pointIdeal Q` is nonzero (equivalently:
`y H ∉ pointIdeal Q`, i.e. `y H` is a unit there, since `pointIdeal Q` is maximal). Proof
sketch: `pointIdeal Q = RingHom.ker (evalAtPoint Q)`, and `evalAtPoint Q (y H)` should equal
`Q.Y` (mirroring `toPair_linX_mem_pointIdeal_iff`'s computation of `evalAtPoint Q` on
`algebraMap`-images, but here for the `y H` generator itself rather than an `algebraMap`
image — confirmed to unfold the same way, via `change` to the underlying `eval₂` after
`unfold evalAtPoint y`, exactly mirroring `evalAtPoint_surjective`'s own unfolding pattern).
`evalAtPoint Q (y H) = Q.Y` closes by `simp [Point.Y]`, and `hY : Q.Y ≠ 0` finishes it via
`RingHom.mem_ker`. -/
theorem y_notMem_pointIdeal_of_Y_ne_zero [IsDedekindDomain (CoordinateRing H)]
    (Q : H.Point) (hY : Q.Y ≠ 0) :
    y H ∉ pointIdeal Q := by
  have heval : evalAtPoint Q (y H) = Q.Y := by
    unfold evalAtPoint y
    change Polynomial.eval₂ (Polynomial.evalRingHom Q.val.1) Q.val.2 X = Q.Y
    simp [Point.Y]
  unfold pointIdeal
  rw [RingHom.mem_ker, heval]
  exact hY

/-- **§B.1c-support, the unit half of the `y H ± C Q.Y` factorization argument.** At an
unramified point (`Q.Y ≠ 0`, char `≠ 2`), `y H + C Q.Y ∉ pointIdeal Q`, i.e. it's a unit
in the residue field there: `evalAtPoint Q (y H + C Q.Y) = Q.Y + Q.Y = 2 * Q.Y ≠ 0`, using
`mul_ne_zero hchar hY` in the field `k`. Mirrors `y_notMem_pointIdeal_of_Y_ne_zero`'s
unfolding pattern exactly, just for `y H + C Q.Y` in place of `y H`. -/
theorem y_add_C_Y_notMem_pointIdeal_of_Y_ne_zero [IsDedekindDomain (CoordinateRing H)]
    (hchar : (2 : k) ≠ 0) (Q : H.Point) (hY : Q.Y ≠ 0) :
    y H + algebraMap k[X] (CoordinateRing H) (Polynomial.C Q.Y) ∉ pointIdeal Q := by
  have heval : evalAtPoint Q
      (y H + algebraMap k[X] (CoordinateRing H) (Polynomial.C Q.Y)) = 2 * Q.Y := by
    rw [map_add]
    have hy : evalAtPoint Q (y H) = Q.Y := by
      unfold evalAtPoint y
      change Polynomial.eval₂ (Polynomial.evalRingHom Q.val.1) Q.val.2 X = Q.Y
      simp [Point.Y]
    have hC : evalAtPoint Q (algebraMap k[X] (CoordinateRing H) (Polynomial.C Q.Y)) = Q.Y := by
      change Polynomial.eval₂ (Polynomial.evalRingHom Q.val.1) Q.val.2
        (Polynomial.C (Polynomial.C Q.Y)) = Q.Y
      simp
    rw [hy, hC]
    ring
  unfold pointIdeal
  rw [RingHom.mem_ker, heval]
  exact mul_ne_zero hchar hY

/-- **§B.1c.i, the true crux.** The earlier draft of this lemma stated a *false* claim: that
`a` is a simple root of `H.f - C (Q.Y^2)` **in `k[X]`**. That is genuinely false in general —
e.g. `H.f = X^5 - X` over `k = ℚ` has `H.f' = 5X^4 - 1`, whose (real, over `ℝ`/`ℂ`) roots `a`
give `Q.Y^2 = H.f.eval a ≠ 0` with `a` a *double* root of `H.f - C (Q.Y^2)` — these are the
ramification points of the *`x`-coordinate map* `C → 𝔸¹`, `(x,y) ↦ x`, a real geometric
phenomenon distinct from the Weierstrass locus (`Y = 0`), and `Squarefree H.f` says nothing
about them (it only rules out repeated roots of `H.f` itself, i.e. `c = 0`).

The correct statement was never about `k[X]`-side root multiplicity at all: `ordAt Q (linX a)
0` is the vanishing order of `x - a` **as a function on `C`**, i.e. the ramification index of
`x : C → 𝔸¹` at `Q` — and that map is the hyperelliptic double cover, unramified *everywhere
except* `Y = 0` (`ι` swaps the two preimages `(a, Q.Y)` and `(a, -Q.Y)` of any `a`, and they
coincide iff `Q.Y = -Q.Y` iff `Q.Y = 0`, char ≠ 2). So the right proof route is intrinsic to
`CoordinateRing H`, exactly as flagged as "more promising" in the previous draft: `y H - C
Q.Y` and `y H + C Q.Y` multiply to `algebraMap _ (H.f - C (Q.Y^2))`, hence to `algebraMap _
(linX a) * algebraMap _ r` for **whatever** `r` witnesses `(X-a) ∣ (H.f - C(Q.Y^2))` (`r.eval
a` need NOT be nonzero — that was the false part); since `y H + C Q.Y` is a unit mod
`pointIdeal Q` (residue `2 * Q.Y ≠ 0`, needs char ≠ 2 — not yet a file-level hypothesis here,
see below), `y H - C Q.Y` and `algebraMap _ (linX a) * algebraMap _ r` differ by a unit, so
`pointIdeal Q ∣ span {y H - C Q.Y}` transfers to `linX a * r`'s span — and **that** is where
`r.eval a ≠ 0` genuinely would matter (to isolate `linX a`'s valuation from `r`'s), UNLESS
`r`'s valuation at `pointIdeal Q` can be pinned down some other way. This restated version
produces a `k[X]`-side witness that's actually true (any root factors out) but weaker than
before; the downstream `not_sq_dvd` assembly needs rethinking to match. -/
theorem factors_sub_Y_sq [IsDedekindDomain (CoordinateRing H)]
    (Q : H.Point) :
    ∃ r : k[X], H.f - Polynomial.C (Q.Y ^ 2) = linX Q.X * r := by
  have hroot : (H.f - Polynomial.C (Q.Y ^ 2)).IsRoot Q.X := by
    show (H.f - Polynomial.C (Q.Y ^ 2)).eval Q.X = 0
    rw [Polynomial.eval_sub, Polynomial.eval_C, sub_eq_zero]
    exact (Point.Y_sq Q).symm
  have hdvd : linX Q.X ∣ (H.f - Polynomial.C (Q.Y ^ 2)) := by
    unfold linX
    exact (Polynomial.dvd_iff_isRoot).mpr hroot
  obtain ⟨r, hr⟩ := hdvd
  exact ⟨r, hr⟩

/-- **§B.1c-i, isolated sub-fact: `y H - C Q.Y` and `y H + C Q.Y` multiply to the
`algebraMap` image of `H.f - C (Q.Y^2)`, hence (via `factors_sub_Y_sq` at `a = Q.X`) to
`g * algebraMap r` where `g := toPair H (linX Q.X) 0`.** Purely algebraic, from `y_sq_eq` and
`factors_sub_Y_sq`; no valuation-theoretic content yet. -/
theorem y_sub_C_Y_mul_y_add_C_Y_eq [IsDedekindDomain (CoordinateRing H)]
    (Q : H.Point) (r : k[X]) (hr : H.f - Polynomial.C (Q.Y ^ 2) = linX Q.X * r) :
    (y H - algebraMap k[X] (CoordinateRing H) (Polynomial.C Q.Y)) *
        (y H + algebraMap k[X] (CoordinateRing H) (Polynomial.C Q.Y)) =
      toPair H (linX Q.X) 0 * algebraMap k[X] (CoordinateRing H) r := by
  have hg : toPair H (linX Q.X) 0 = algebraMap k[X] (CoordinateRing H) (linX Q.X) := by
    unfold toPair; simp
  rw [hg, ← map_mul]
  have hexpand : (y H - algebraMap k[X] (CoordinateRing H) (Polynomial.C Q.Y)) *
      (y H + algebraMap k[X] (CoordinateRing H) (Polynomial.C Q.Y)) =
      y H ^ 2 - (algebraMap k[X] (CoordinateRing H) (Polynomial.C Q.Y)) ^ 2 := by
    ring
  rw [hexpand, y_sq_eq, ← map_pow, ← Polynomial.C_pow, ← map_sub, hr]

/-- **§B.1c-ii, isolated sub-fact: `pointIdeal Q`-adic valuation is invariant under
multiplication by a `pointIdeal Q`-unit.** For `z : CoordinateRing H` and `u ∉ pointIdeal Q`,
`pointIdeal Q ^ n ∣ span {z * u} ↔ pointIdeal Q ^ n ∣ span {z}`. Route: `pointIdeal Q` is
maximal, so `u ∉ pointIdeal Q` makes `pointIdeal Q` and `Ideal.span {u}` coprime
(`Ideal.IsMaximal.eq_of_le` applied to `pointIdeal Q ≤ pointIdeal Q ⊔ span {u}`, forcing the
sup to `⊤` since it's strictly larger; then `Ideal.isCoprime_iff_sup_eq`). `IsCoprime.pow_left`
lifts this to `pointIdeal Q ^ n` coprime to `span {u}`, and `IsCoprime.dvd_of_dvd_mul_right`
(applied at ideal level, since `Ideal (CoordinateRing H)` is a `CommSemiring`) gives the
cancellation directly — no `Associates.count` machinery needed. -/
theorem pointIdeal_pow_dvd_span_mul_notMem_iff [IsDedekindDomain (CoordinateRing H)]
    (Q : H.Point) (z u : CoordinateRing H) (hu : u ∉ pointIdeal Q) (n : ℕ) :
    pointIdeal Q ^ n ∣ Ideal.span ({z * u} : Set (CoordinateRing H)) ↔
      pointIdeal Q ^ n ∣ Ideal.span ({z} : Set (CoordinateRing H)) := by
  have hspan_eq : Ideal.span ({z * u} : Set (CoordinateRing H)) =
      Ideal.span ({z} : Set (CoordinateRing H)) * Ideal.span ({u} : Set (CoordinateRing H)) :=
    (Ideal.span_singleton_mul_span_singleton z u).symm
  have hle : pointIdeal Q ≤ pointIdeal Q ⊔ Ideal.span ({u} : Set (CoordinateRing H)) :=
    le_sup_left
  have hne : pointIdeal Q ≠ pointIdeal Q ⊔ Ideal.span ({u} : Set (CoordinateRing H)) := by
    intro heq
    apply hu
    rw [heq]
    exact SetLike.le_def.mp le_sup_right (Ideal.mem_span_singleton_self u)
  have hsup_top : pointIdeal Q ⊔ Ideal.span ({u} : Set (CoordinateRing H)) = ⊤ := by
    by_contra hnotop
    exact hne ((pointIdeal_isMaximal Q).eq_of_le hnotop hle)
  have hcoprime : IsCoprime (pointIdeal Q) (Ideal.span ({u} : Set (CoordinateRing H))) :=
    Ideal.isCoprime_iff_sup_eq.mpr hsup_top
  have hcoprime_pow : IsCoprime (pointIdeal Q ^ n) (Ideal.span ({u} : Set (CoordinateRing H))) :=
    hcoprime.pow_left
  constructor
  · intro hdvd
    rw [hspan_eq] at hdvd
    exact hcoprime_pow.dvd_of_dvd_mul_right hdvd
  · intro hdvd
    have hsub : Ideal.span ({z * u} : Set (CoordinateRing H)) ≤
        Ideal.span ({z} : Set (CoordinateRing H)) := by
      rw [Ideal.span_singleton_le_iff_mem]
      exact Ideal.mem_span_singleton.mpr ⟨u, rfl⟩
    exact hdvd.trans (Ideal.dvd_iff_le.mpr hsub)

/-- **§B.1c-iii-pre, structural fact: `pointIdeal Q = span {s, t}`**, where `s := toPair H
(linX Q.X) 0` and `t := y H - C Q.Y`. Proved directly inside `CoordinateRing H`, no
localization: `⊇` is `s, t ∈ pointIdeal Q` (both easy `evalAtPoint` computations); `⊆` takes
`z ∈ pointIdeal Q`, writes `z = toPair H A B` (`toPair_surjective_local`), and uses the
factor-theorem decompositions `A = C (A.eval Q.X) + linX Q.X * A₁`, `B = C (B.eval Q.X) +
linX Q.X * B₁` (`Polynomial.dvd_iff_isRoot` applied to `A - C (A.eval Q.X)` etc.) to split off
a multiple of `s`, leaving a remainder `C (A.eval Q.X) + C (B.eval Q.X) * y H` that — using
`evalAtPoint Q z = 0`, i.e. `A.eval Q.X + B.eval Q.X * Q.Y = 0` — collapses to
`B.eval Q.X * t`, a multiple of `t`. -/
theorem pointIdeal_eq_span_pair [IsDedekindDomain (CoordinateRing H)] (Q : H.Point) :
    pointIdeal Q = Ideal.span ({toPair H (linX Q.X) 0,
      y H - algebraMap k[X] (CoordinateRing H) (Polynomial.C Q.Y)} : Set (CoordinateRing H)) := by
  set s : CoordinateRing H := toPair H (linX Q.X) 0 with hs_def
  set t : CoordinateRing H := y H - algebraMap k[X] (CoordinateRing H) (Polynomial.C Q.Y)
    with ht_def
  have hs_mem : s ∈ pointIdeal Q := (toPair_linX_mem_pointIdeal_iff Q.X Q).mpr rfl
  have ht_eval : evalAtPoint Q t = 0 := by
    rw [ht_def, map_sub]
    have hy : evalAtPoint Q (y H) = Q.Y := by
      unfold evalAtPoint y
      change Polynomial.eval₂ (Polynomial.evalRingHom Q.val.1) Q.val.2 X = Q.Y
      simp [Point.Y]
    have hC : evalAtPoint Q (algebraMap k[X] (CoordinateRing H) (Polynomial.C Q.Y)) = Q.Y := by
      change Polynomial.eval₂ (Polynomial.evalRingHom Q.val.1) Q.val.2
        (Polynomial.C (Polynomial.C Q.Y)) = Q.Y
      simp
    rw [hy, hC, sub_self]
  have ht_mem : t ∈ pointIdeal Q := by
    unfold pointIdeal
    rw [RingHom.mem_ker]
    exact ht_eval
  have hg : s = algebraMap k[X] (CoordinateRing H) (linX Q.X) := by
    rw [hs_def]; unfold toPair; simp
  clear_value s t
  apply le_antisymm
  · intro z hz
    obtain ⟨A, B, hzAB⟩ := toPair_surjective_local H z
    have hz' : evalAtPoint Q z = 0 := by
      have := hz
      unfold pointIdeal at this
      rwa [RingHom.mem_ker] at this
    have hzeval : A.eval Q.X + B.eval Q.X * Q.Y = 0 := by
      have : evalAtPoint Q z = 0 := hz'
      rw [hzAB] at this
      unfold toPair at this
      rw [map_add, map_mul] at this
      have hAeval : evalAtPoint Q (algebraMap k[X] (CoordinateRing H) A) = A.eval Q.X := by
        change Polynomial.eval₂ (Polynomial.evalRingHom Q.val.1) Q.val.2
          (Polynomial.C A) = A.eval Q.X
        simp [Point.X]
      have hBeval : evalAtPoint Q (algebraMap k[X] (CoordinateRing H) B) = B.eval Q.X := by
        change Polynomial.eval₂ (Polynomial.evalRingHom Q.val.1) Q.val.2
          (Polynomial.C B) = B.eval Q.X
        simp [Point.X]
      have hyeval : evalAtPoint Q (y H) = Q.Y := by
        unfold evalAtPoint y
        change Polynomial.eval₂ (Polynomial.evalRingHom Q.val.1) Q.val.2 X = Q.Y
        simp [Point.Y]
      rwa [hAeval, hBeval, hyeval] at this
    have hAdvd : linX Q.X ∣ (A - Polynomial.C (A.eval Q.X)) := by
      unfold linX
      apply Polynomial.dvd_iff_isRoot.mpr
      show (A - Polynomial.C (A.eval Q.X)).eval Q.X = 0
      simp
    have hBdvd : linX Q.X ∣ (B - Polynomial.C (B.eval Q.X)) := by
      unfold linX
      apply Polynomial.dvd_iff_isRoot.mpr
      show (B - Polynomial.C (B.eval Q.X)).eval Q.X = 0
      simp
    obtain ⟨A₁, hA₁⟩ := hAdvd
    obtain ⟨B₁, hB₁⟩ := hBdvd
    have hA_eq : A = Polynomial.C (A.eval Q.X) + linX Q.X * A₁ := by
      have := hA₁; rw [sub_eq_iff_eq_add] at this; linear_combination this
    have hB_eq : B = Polynomial.C (B.eval Q.X) + linX Q.X * B₁ := by
      have := hB₁; rw [sub_eq_iff_eq_add] at this; linear_combination this
    have hz_split : z = algebraMap k[X] (CoordinateRing H) (Polynomial.C (A.eval Q.X)) +
        algebraMap k[X] (CoordinateRing H) (Polynomial.C (B.eval Q.X)) * y H +
        s * toPair H A₁ B₁ := by
      have hstepA : algebraMap k[X] (CoordinateRing H) A =
          algebraMap k[X] (CoordinateRing H) (Polynomial.C (A.eval Q.X)) +
          s * algebraMap k[X] (CoordinateRing H) A₁ := by
        rw [hg, ← map_mul, ← map_add, ← hA_eq]
      have hstepB : algebraMap k[X] (CoordinateRing H) B =
          algebraMap k[X] (CoordinateRing H) (Polynomial.C (B.eval Q.X)) +
          s * algebraMap k[X] (CoordinateRing H) B₁ := by
        rw [hg, ← map_mul, ← map_add, ← hB_eq]
      rw [hzAB]
      unfold toPair
      rw [hstepA, hstepB]
      ring
    have hrem : algebraMap k[X] (CoordinateRing H) (Polynomial.C (A.eval Q.X)) +
        algebraMap k[X] (CoordinateRing H) (Polynomial.C (B.eval Q.X)) * y H =
        algebraMap k[X] (CoordinateRing H) (Polynomial.C (B.eval Q.X)) * t := by
      have hAeq : A.eval Q.X = -(B.eval Q.X * Q.Y) := by linear_combination hzeval
      rw [ht_def, mul_sub]
      have : algebraMap k[X] (CoordinateRing H) (Polynomial.C (A.eval Q.X)) =
          - (algebraMap k[X] (CoordinateRing H) (Polynomial.C (B.eval Q.X)) *
            algebraMap k[X] (CoordinateRing H) (Polynomial.C Q.Y)) := by
        rw [← map_mul, ← map_neg]
        congr 1
        rw [hAeq, Polynomial.C_neg, Polynomial.C_mul]
      rw [this]
      ring
    rw [hz_split, hrem]
    have hs_in_span : s ∈ Ideal.span ({s, t} : Set (CoordinateRing H)) :=
      Ideal.subset_span (by simp)
    have ht_in_span : t ∈ Ideal.span ({s, t} : Set (CoordinateRing H)) :=
      Ideal.subset_span (by simp)
    have hmem_s : s * toPair H A₁ B₁ ∈
        Ideal.span ({s, t} : Set (CoordinateRing H)) :=
      Ideal.mul_mem_right _ _ hs_in_span
    have hmem_t : algebraMap k[X] (CoordinateRing H) (Polynomial.C (B.eval Q.X)) * t ∈
        Ideal.span ({s, t} : Set (CoordinateRing H)) :=
      Ideal.mul_mem_left _ _ ht_in_span
    exact Ideal.add_mem _ hmem_t hmem_s
  · rw [Ideal.span_le]
    intro x hx
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · rw [hx]; exact hs_mem
    · rw [hx]; exact ht_mem

 
/-- **§B.1c-iii, isolated sub-fact: pointIdeal Q is not squared-divisible by span {s}.** -/
theorem pointIdeal_linX_not_sq_dvd [IsDedekindDomain (CoordinateRing H)]
    (Q : H.Point) (hchar : (2 : k) ≠ 0) (hY : Q.Y ≠ 0) :
    ¬ pointIdeal Q ^ 2 ∣ Ideal.span ({toPair H (linX Q.X) 0} : Set (CoordinateRing H)) := by
  classical
  set s : CoordinateRing H := toPair H (linX Q.X) 0 with hs_def
  set t : CoordinateRing H := y H - algebraMap k[X] (CoordinateRing H) (Polynomial.C Q.Y)
    with ht_def
  set u : CoordinateRing H := y H + algebraMap k[X] (CoordinateRing H) (Polynomial.C Q.Y)
    with hu_def
  obtain ⟨r, hr⟩ := factors_sub_Y_sq Q
  have htu : t * u = s * algebraMap k[X] (CoordinateRing H) r := by
    rw [ht_def, hu_def, hs_def]
    exact y_sub_C_Y_mul_y_add_C_Y_eq Q r hr
  have hu_notmem : u ∉ pointIdeal Q := by
    rw [hu_def]; exact y_add_C_Y_notMem_pointIdeal_of_Y_ne_zero hchar Q hY
  have hs_mem : s ∈ pointIdeal Q := (toPair_linX_mem_pointIdeal_iff Q.X Q).mpr rfl
  have ht_mem : t ∈ pointIdeal Q := by
    have heval : (evalAtPoint Q) t = 0 := by
      dsimp [t]
      rw [map_sub]
      have hy : (evalAtPoint Q) (y H) = Q.Y := by
        change Polynomial.eval₂ (evalRingHom Q.X) Q.Y Polynomial.X = Q.Y
        exact Polynomial.eval₂_X _ _
      have hC : (evalAtPoint Q) ((algebraMap k[X] H.CoordinateRing) (Polynomial.C Q.Y)) = Q.Y := by
        change Polynomial.eval₂ (evalRingHom Q.X) Q.Y (Polynomial.C (Polynomial.C Q.Y)) = Q.Y
        rw [Polynomial.eval₂_C]
        exact Polynomial.eval₂_C _ _
      rw [hy, hC, sub_self]
    unfold pointIdeal
    rw [RingHom.mem_ker]
    exact heval
  clear_value s t u
  have hle : pointIdeal Q ≤ pointIdeal Q ⊔ Ideal.span ({u} : Set (CoordinateRing H)) := le_sup_left
  have hne : pointIdeal Q ≠ pointIdeal Q ⊔ Ideal.span ({u} : Set (CoordinateRing H)) := by
    intro heq
    apply hu_notmem
    rw [heq]
    exact SetLike.le_def.mp le_sup_right (Ideal.mem_span_singleton_self u)
  have hsup_top : pointIdeal Q ⊔ Ideal.span ({u} : Set (CoordinateRing H)) = ⊤ := by
    by_contra hnotop
    exact hne ((pointIdeal_isMaximal Q).eq_of_le hnotop hle)
  have h1mem : (1 : CoordinateRing H) ∈
      pointIdeal Q ⊔ Ideal.span ({u} : Set (CoordinateRing H)) := hsup_top ▸ Submodule.mem_top
  obtain ⟨p, hp, w, hw, hpw⟩ := Submodule.mem_sup.mp h1mem
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hw
  have h1 : p + u * c = 1 := by rw [← hc]; exact hpw
  have ht_eq : t = t * p + c * (s * algebraMap k[X] (CoordinateRing H) r) := by
    have hstep : t * (p + u * c) = t * 1 := by rw [h1]
    have hexpand : t * (p + u * c) = t * p + (t * u) * c := by ring
    rw [hexpand, htu, mul_one] at hstep
    linear_combination -hstep
  have htp_mem : t * p ∈ pointIdeal Q ^ 2 := by
    rw [sq]
    exact Ideal.mul_mem_mul ht_mem hp
  have ht_sub_mem : t - c * (s * algebraMap k[X] (CoordinateRing H) r) ∈ pointIdeal Q ^ 2 := by
    have : t - c * (s * algebraMap k[X] (CoordinateRing H) r) = t * p := by
      linear_combination ht_eq
    rw [this]; exact htp_mem
  have ht_mem2 : t ∈ Ideal.span ({s} : Set (CoordinateRing H)) ⊔ pointIdeal Q ^ 2 := by
    have hsmem : c * (s * algebraMap k[X] (CoordinateRing H) r) ∈
        Ideal.span ({s} : Set (CoordinateRing H)) := by
      rw [mul_comm c, mul_assoc]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self s)
    have hsmem' : c * (s * algebraMap k[X] (CoordinateRing H) r) ∈
        Ideal.span ({s} : Set (CoordinateRing H)) ⊔ pointIdeal Q ^ 2 :=
      SetLike.le_def.mp le_sup_left hsmem
    have ht_sub_mem' : t - c * (s * algebraMap k[X] (CoordinateRing H) r) ∈
        Ideal.span ({s} : Set (CoordinateRing H)) ⊔ pointIdeal Q ^ 2 :=
      SetLike.le_def.mp le_sup_right ht_sub_mem
    have hsum := Submodule.add_mem _ hsmem' ht_sub_mem'
    have hrw : c * (s * algebraMap k[X] (CoordinateRing H) r) +
        (t - c * (s * algebraMap k[X] (CoordinateRing H) r)) = t := by ring
    rwa [hrw] at hsum
  have hs_mem2 : s ∈ Ideal.span ({s} : Set (CoordinateRing H)) ⊔ pointIdeal Q ^ 2 :=
    SetLike.le_def.mp le_sup_left (Ideal.mem_span_singleton_self s)
  have hspan_le : pointIdeal Q ≤ Ideal.span ({s} : Set (CoordinateRing H)) ⊔ pointIdeal Q ^ 2 := by
    have hgen : pointIdeal Q = Ideal.span ({s, t} : Set (CoordinateRing H)) := by
      rw [pointIdeal_eq_span_pair Q, ← hs_def, ← ht_def]
    conv_lhs => rw [hgen]
    rw [Ideal.span_le]
    intro x hx
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · rw [hx]; exact hs_mem2
    · rw [hx]; exact ht_mem2
  intro hdvd_contra
  have hspan_le2 : Ideal.span ({s} : Set (CoordinateRing H)) ≤ pointIdeal Q ^ 2 :=
    Ideal.dvd_iff_le.mp hdvd_contra
  have hsuple : Ideal.span ({s} : Set (CoordinateRing H)) ⊔ pointIdeal Q ^ 2 ≤ pointIdeal Q ^ 2 :=
    sup_le hspan_le2 (le_refl (pointIdeal Q ^ 2))
  have heq2 : pointIdeal Q ≤ pointIdeal Q ^ 2 := le_trans hspan_le hsuple
  have hpow_le : pointIdeal Q ^ 2 ≤ pointIdeal Q := by
    rw [sq]
    intro x hx
    refine Submodule.mul_induction_on hx (fun a ha b hb => Ideal.mul_mem_right b _ ha) ?_
    intro y z hy hz
    exact Ideal.add_mem _ hy hz
  have heq_final : pointIdeal Q = pointIdeal Q ^ 2 :=
    le_antisymm heq2 hpow_le
  have hfg : (pointIdeal Q).FG := Ideal.fg_of_isNoetherianRing (pointIdeal Q)
  have hle_smul : pointIdeal Q ≤ pointIdeal Q • pointIdeal Q := by
    rw [Ideal.smul_eq_mul, ← sq]
    exact heq2
  obtain ⟨e, he1, he0⟩ :=
    Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul (pointIdeal Q)
      (pointIdeal Q) hfg hle_smul
  have hbot := pointIdeal_ne_bot Q
  obtain ⟨x, hxmem, hxne⟩ : ∃ x ∈ pointIdeal Q, x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hbot
    rw [Submodule.eq_bot_iff]
    exact hcon
  have hex0 : e * x = 0 := he0 x hxmem
  have he_eq0 : e = 0 := by
    rcases mul_eq_zero.mp hex0 with he | hx0
    · exact he
    · exact absurd hx0 hxne
  rw [he_eq0, zero_sub] at he1
  have hone_mem : (1 : CoordinateRing H) ∈ pointIdeal Q := by
    have hneg1 : -(1 : CoordinateRing H) ∈ pointIdeal Q := he1
    have := neg_mem hneg1
    rwa [neg_neg] at this
  exact (pointIdeal_isMaximal Q).ne_top (Ideal.eq_top_iff_one _ |>.mpr hone_mem)   



/-- **§B.2a, the simple-root fact.** At a ramified point (`Q.Y = 0`, so `Q.X` is a root of
`H.f`), squarefreeness of `H.f` forces `Q.X` to be a *simple* root: writing `H.f = linX Q.X *
r` (via `factors_sub_Y_sq` specialized to `Q.Y = 0`, where `C (Q.Y^2) = C 0 = 0`), `r.eval
Q.X ≠ 0`. Proof: if `r.eval Q.X = 0` then `linX Q.X ∣ r` (factor theorem), so
`linX Q.X * linX Q.X ∣ linX Q.X * r = H.f`; `Squarefree H.f` then forces `linX Q.X` to be a
unit, contradicting `(linX Q.X).natDegree = 1 ≠ 0`
(`Polynomial.isUnit_iff_degree_eq_zero`/`natDegree_eq_zero_of_isUnit`). -/
theorem simple_root_of_squarefree_of_ramified [IsDedekindDomain (CoordinateRing H)]
    (hsf : Squarefree H.f) (Q : H.Point) (hY : Q.Y = 0) (r : k[X])
    (hr : H.f = linX Q.X * r) : r.eval Q.X ≠ 0 := by
  intro hr0
  have hdvd : linX Q.X ∣ r := by
    unfold linX
    exact Polynomial.dvd_iff_isRoot.mpr hr0
  obtain ⟨r', hr'⟩ := hdvd
  have hsq_dvd : linX Q.X * linX Q.X ∣ H.f := by
    rw [hr, hr']
    exact ⟨r', by ring⟩
  have hunit : IsUnit (linX Q.X) := hsf (linX Q.X) hsq_dvd
  have hdeg0 : (linX Q.X).natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hunit
  rw [linX_natDegree] at hdeg0
  exact absurd hdeg0 (by decide)

/-- **§B.2b, the unit fact.** At a ramified point, `algebraMap k[X] (CoordinateRing H) r ∉
pointIdeal Q`, where `r` is the cofactor from `simple_root_of_squarefree_of_ramified`. Mirrors
`y_notMem_pointIdeal_of_Y_ne_zero`'s unfolding pattern: `evalAtPoint Q (algebraMap _ r) =
r.eval Q.X`, nonzero by the simple-root fact. -/
theorem algebraMap_r_notMem_pointIdeal_of_ramified [IsDedekindDomain (CoordinateRing H)]
    (hsf : Squarefree H.f) (Q : H.Point) (hY : Q.Y = 0) (r : k[X])
    (hr : H.f = linX Q.X * r) :
    algebraMap k[X] (CoordinateRing H) r ∉ pointIdeal Q := by
  have heval : evalAtPoint Q (algebraMap k[X] (CoordinateRing H) r) = r.eval Q.X := by
    change Polynomial.eval₂ (Polynomial.evalRingHom Q.val.1) Q.val.2 (Polynomial.C r) = r.eval Q.X
    simp [Point.X]
  unfold pointIdeal
  rw [RingHom.mem_ker, heval]
  exact simple_root_of_squarefree_of_ramified hsf Q hY r hr

/-- **§B.2c, the ramified analogue of `y_sub_C_Y_mul_y_add_C_Y_eq`.** At `Q.Y = 0`,
`C Q.Y = 0`, so `y_sq_eq` directly gives `(y H) ^ 2 = s * algebraMap r`, where
`s := toPair H (linX Q.X) 0`. -/
theorem y_sq_eq_linX_mul_r_of_ramified [IsDedekindDomain (CoordinateRing H)]
    (Q : H.Point) (hY : Q.Y = 0) (r : k[X]) (hr : H.f = linX Q.X * r) :
    y H ^ 2 = toPair H (linX Q.X) 0 * algebraMap k[X] (CoordinateRing H) r := by
  have hg : toPair H (linX Q.X) 0 = algebraMap k[X] (CoordinateRing H) (linX Q.X) := by
    unfold toPair; simp
  rw [hg, ← map_mul, ← hr]
  exact y_sq_eq H

/-- **§B.2d, `y H` is a genuine uniformizer at a ramified point: `pointIdeal Q ^ 2 ∤ span {y
H}`.** Direct structural mirror of `pointIdeal_linX_not_sq_dvd`, with the roles of `s` and `t`
swapped: here `t := y H` is the element being shown not-squared-divisible, `s := toPair H
(linX Q.X) 0` plays the role `t` played before, and the "unit" is `algebraMap r` (in place of
`y H + C Q.Y`). Uses `pointIdeal Q = span {s, y H}` (`pointIdeal_eq_span_pair`, specialized:
`t = y H - C Q.Y = y H - C 0 = y H` since `hY : Q.Y = 0`). -/
theorem pointIdeal_y_not_sq_dvd_of_ramified [IsDedekindDomain (CoordinateRing H)]
    (hsf : Squarefree H.f) (Q : H.Point) (hY : Q.Y = 0) :
    ¬ pointIdeal Q ^ 2 ∣ Ideal.span ({y H} : Set (CoordinateRing H)) := by
  classical
  obtain ⟨r, hr⟩ := factors_sub_Y_sq Q
  rw [hY, zero_pow (by norm_num), Polynomial.C_0, sub_zero] at hr
  set s : CoordinateRing H := toPair H (linX Q.X) 0 with hs_def
  set t : CoordinateRing H := y H with ht_def
  have hst : t * t = s * algebraMap k[X] (CoordinateRing H) r := by
    rw [ht_def, hs_def, ← sq]
    exact y_sq_eq_linX_mul_r_of_ramified Q hY r hr
  have hu_notmem : algebraMap k[X] (CoordinateRing H) r ∉ pointIdeal Q :=
    algebraMap_r_notMem_pointIdeal_of_ramified hsf Q hY r hr
  have hs_mem : s ∈ pointIdeal Q := (toPair_linX_mem_pointIdeal_iff Q.X Q).mpr rfl
  have ht_mem : t ∈ pointIdeal Q := by
    have heval : evalAtPoint Q t = 0 := by
      rw [ht_def]
      have hy : evalAtPoint Q (y H) = Q.Y := by
        unfold evalAtPoint y
        change Polynomial.eval₂ (Polynomial.evalRingHom Q.val.1) Q.val.2 X = Q.Y
        simp [Point.Y]
      rw [hy, hY]
    unfold pointIdeal
    rw [RingHom.mem_ker]
    exact heval
  have hpq : pointIdeal Q = Ideal.span ({s, t} : Set (CoordinateRing H)) := by
    rw [pointIdeal_eq_span_pair Q, hY, Polynomial.C_0, map_zero, sub_zero, ← hs_def, ← ht_def]
  clear_value s t
  have hle : pointIdeal Q ≤
      pointIdeal Q ⊔ Ideal.span ({algebraMap k[X] (CoordinateRing H) r} : Set (CoordinateRing H)) :=
    le_sup_left
  have hne : pointIdeal Q ≠
      pointIdeal Q ⊔ Ideal.span ({algebraMap k[X] (CoordinateRing H) r} : Set (CoordinateRing H)) := by
    intro heq
    apply hu_notmem
    rw [heq]
    exact SetLike.le_def.mp le_sup_right
      (Ideal.mem_span_singleton_self (algebraMap k[X] (CoordinateRing H) r))
  have hsup_top : pointIdeal Q ⊔
      Ideal.span ({algebraMap k[X] (CoordinateRing H) r} : Set (CoordinateRing H)) = ⊤ := by
    by_contra hnotop
    exact hne ((pointIdeal_isMaximal Q).eq_of_le hnotop hle)
  have h1mem : (1 : CoordinateRing H) ∈ pointIdeal Q ⊔
      Ideal.span ({algebraMap k[X] (CoordinateRing H) r} : Set (CoordinateRing H)) :=
    hsup_top ▸ Submodule.mem_top
  obtain ⟨p, hp, w, hw, hpw⟩ := Submodule.mem_sup.mp h1mem
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hw
  have h1 : p + algebraMap k[X] (CoordinateRing H) r * c = 1 := by rw [← hc]; exact hpw
  have hs_eq : s = s * p + c * (t * t) := by
    have hstep : s * (p + algebraMap k[X] (CoordinateRing H) r * c) = s * 1 := by rw [h1]
    have hexpand : s * (p + algebraMap k[X] (CoordinateRing H) r * c) =
        s * p + (s * algebraMap k[X] (CoordinateRing H) r) * c := by ring
    rw [hexpand, ← hst, mul_one] at hstep
    linear_combination -hstep
  have hsp_mem : s * p ∈ pointIdeal Q ^ 2 := by
    rw [sq]
    exact Ideal.mul_mem_mul hs_mem hp
  have hs_sub_mem : s - c * (t * t) ∈ pointIdeal Q ^ 2 := by
    have : s - c * (t * t) = s * p := by linear_combination hs_eq
    rw [this]; exact hsp_mem
  have hs_mem2 : s ∈ Ideal.span ({t} : Set (CoordinateRing H)) ⊔ pointIdeal Q ^ 2 := by
    have htmem : c * (t * t) ∈ Ideal.span ({t} : Set (CoordinateRing H)) := by
      rw [mul_comm c, mul_assoc]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self t)
    have htmem' : c * (t * t) ∈
        Ideal.span ({t} : Set (CoordinateRing H)) ⊔ pointIdeal Q ^ 2 :=
      SetLike.le_def.mp le_sup_left htmem
    have hs_sub_mem' : s - c * (t * t) ∈
        Ideal.span ({t} : Set (CoordinateRing H)) ⊔ pointIdeal Q ^ 2 :=
      SetLike.le_def.mp le_sup_right hs_sub_mem
    have hsum := Submodule.add_mem _ htmem' hs_sub_mem'
    have hrw : c * (t * t) + (s - c * (t * t)) = s := by ring
    rwa [hrw] at hsum
  have ht_mem2 : t ∈ Ideal.span ({t} : Set (CoordinateRing H)) ⊔ pointIdeal Q ^ 2 :=
    SetLike.le_def.mp le_sup_left (Ideal.mem_span_singleton_self t)
  have hspan_le : pointIdeal Q ≤ Ideal.span ({t} : Set (CoordinateRing H)) ⊔ pointIdeal Q ^ 2 := by
    conv_lhs => rw [hpq]
    rw [Ideal.span_le]
    intro x hx
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · rw [hx]; exact hs_mem2
    · rw [hx]; exact ht_mem2
  intro hdvd_contra
  have hspan_le2 : Ideal.span ({t} : Set (CoordinateRing H)) ≤ pointIdeal Q ^ 2 :=
    Ideal.dvd_iff_le.mp hdvd_contra
  have hsuple : Ideal.span ({t} : Set (CoordinateRing H)) ⊔ pointIdeal Q ^ 2 ≤ pointIdeal Q ^ 2 :=
    sup_le hspan_le2 (le_refl (pointIdeal Q ^ 2))
  have heq2 : pointIdeal Q ≤ pointIdeal Q ^ 2 := le_trans hspan_le hsuple
  have hpow_le : pointIdeal Q ^ 2 ≤ pointIdeal Q := by
    rw [sq]
    intro x hx
    refine Submodule.mul_induction_on hx (fun a ha b hb => Ideal.mul_mem_right b _ ha) ?_
    intro y z hy hz
    exact Ideal.add_mem _ hy hz
  have heq_final : pointIdeal Q = pointIdeal Q ^ 2 := le_antisymm heq2 hpow_le
  have hfg : (pointIdeal Q).FG := Ideal.fg_of_isNoetherianRing (pointIdeal Q)
  have hle_smul : pointIdeal Q ≤ pointIdeal Q • pointIdeal Q := by
    rw [Ideal.smul_eq_mul, ← sq]
    exact heq2
  obtain ⟨e, he1, he0⟩ :=
    Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul (pointIdeal Q)
      (pointIdeal Q) hfg hle_smul
  have hbot := pointIdeal_ne_bot Q
  obtain ⟨x, hxmem, hxne⟩ : ∃ x ∈ pointIdeal Q, x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hbot
    rw [Submodule.eq_bot_iff]
    exact hcon
  have hex0 : e * x = 0 := he0 x hxmem
  have he_eq0 : e = 0 := by
    rcases mul_eq_zero.mp hex0 with he | hx0
    · exact he
    · exact absurd hx0 hxne
  rw [he_eq0, zero_sub] at he1
  have hone_mem : (1 : CoordinateRing H) ∈ pointIdeal Q := by
    have hneg1 : -(1 : CoordinateRing H) ∈ pointIdeal Q := he1
    have := neg_mem hneg1
    rwa [neg_neg] at this
  exact (pointIdeal_isMaximal Q).ne_top (Ideal.eq_top_iff_one _ |>.mpr hone_mem)

/-- **§B.2e, `pointIdeal Q ^ 2 ∣ span {s}`.** Via `pointIdeal_pow_dvd_span_mul_notMem_iff`
(`n = 2`, `z = s`, `u = algebraMap r`): reduces to `pointIdeal Q ^ 2 ∣ span {s * algebraMap r}
= span {(y H) ^ 2}`, true since `y H ∈ pointIdeal Q` gives `(y H) ^ 2 ∈ pointIdeal Q ^ 2`. -/
theorem pointIdeal_sq_dvd_span_linX_of_ramified [IsDedekindDomain (CoordinateRing H)]
    (hsf : Squarefree H.f) (Q : H.Point) (hY : Q.Y = 0) :
    pointIdeal Q ^ 2 ∣ Ideal.span ({toPair H (linX Q.X) 0} : Set (CoordinateRing H)) := by
  obtain ⟨r, hr⟩ := factors_sub_Y_sq Q
  rw [hY, zero_pow (by norm_num), Polynomial.C_0, sub_zero] at hr
  have hu_notmem : algebraMap k[X] (CoordinateRing H) r ∉ pointIdeal Q :=
    algebraMap_r_notMem_pointIdeal_of_ramified hsf Q hY r hr
  rw [← pointIdeal_pow_dvd_span_mul_notMem_iff Q (toPair H (linX Q.X) 0)
    (algebraMap k[X] (CoordinateRing H) r) hu_notmem 2]
  have hprod : toPair H (linX Q.X) 0 * algebraMap k[X] (CoordinateRing H) r = y H ^ 2 :=
    (y_sq_eq_linX_mul_r_of_ramified Q hY r hr).symm
  rw [hprod, sq]
  have hy_mem : y H ∈ pointIdeal Q := by
    have heval : evalAtPoint Q (y H) = 0 := by
      have hy : evalAtPoint Q (y H) = Q.Y := by
        unfold evalAtPoint y
        change Polynomial.eval₂ (Polynomial.evalRingHom Q.val.1) Q.val.2 X = Q.Y
        simp [Point.Y]
      rw [hy, hY]
    unfold pointIdeal
    rw [RingHom.mem_ker]
    exact heval
  have : Ideal.span ({y H * y H} : Set (CoordinateRing H)) ≤ pointIdeal Q * pointIdeal Q := by
    rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.mul_mem_mul hy_mem hy_mem
  simpa [pow_two] using (Ideal.dvd_iff_le.mpr this)

/-- **§B.2f, `¬ pointIdeal Q ^ 3 ∣ span {s}`.** Via `pointIdeal_pow_dvd_span_mul_notMem_iff`
(`n = 3`): reduces to `¬ pointIdeal Q ^ 3 ∣ span {(y H) ^ 2}`. Suppose it did: combined with
`pointIdeal Q ^ 2 ∣ span {y H} * span {y H}` trivially (from `y H ∈ pointIdeal Q`) this doesn't
immediately give a contradiction by itself, so instead argue directly: `pointIdeal Q ^ 3 ∣
span {(y H)^2}` means `(y H)^2 ∈ pointIdeal Q ^ 3`. Since `pointIdeal Q` is invertible
(Dedekind domain, nonzero prime), `pointIdeal Q ^ 2 ∣ Ideal.span {(y H)^2}` always holds (`y H ∈
pointIdeal Q`); if additionally `pointIdeal Q ^ 3 ∣ span {(y H)^2}`, cancelling one copy of
`pointIdeal Q` (`Ideal.mul_left_cancel'`-style, valid since `pointIdeal Q ≠ ⊥` in a Dedekind
domain, i.e. `pointIdeal Q` is a nonzero prime hence invertible/cancellable) forces `pointIdeal
Q ∣ span {y H}` — false, since that would need `y H ∈ pointIdeal Q`... this is not quite
`pointIdeal_y_not_sq_dvd_of_ramified`'s statement directly. Route instead: `span {(y H)^2} =
span {y H} * span {y H}` (`Ideal.span_singleton_mul_span_singleton`), and in a Dedekind domain
unique factorization of ideals gives: `pointIdeal Q ^ 3 ∣ span{y H} * span{y H}` together with
`¬ pointIdeal Q ^ 2 ∣ span {y H}` (§B.2d) is the direct contradiction via `Associates.count`
additivity over the product — proved via the `count`-based `ordAt_eq_count` route at the
assembly stage instead of re-deriving multiplicativity here; **this lemma is stated but its
proof needs the same `Associates.count` infrastructure as the final assembly, so it's proved
together with `ordAt_linX_eq_two_of_ramified` below rather than as an independent lemma.** -/
theorem ordAt_linX_eq_two_of_ramified [IsDedekindDomain (CoordinateRing H)]
    (hsf : Squarefree H.f) (a : k) (Q : H.Point) (h_bot : pointIdeal Q ≠ ⊥) (heq : Q.X = a)
    (hY : Q.Y = 0) :
    ordAt Q (linX a) 0 = 2 := by
  classical
  rw [← heq]
  have hdvd2 := pointIdeal_sq_dvd_span_linX_of_ramified hsf Q hY
  have hnot_sq_dvd_y := pointIdeal_y_not_sq_dvd_of_ramified hsf Q hY
  have hgne : toPair H (linX Q.X) 0 ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => linX_ne_zero Q.X hA
  rw [ordAt_eq_count Q (linX Q.X) 0 hgne h_bot]
  show ((Associates.mk (pointIdeal Q)).count
      (Associates.mk (Ideal.span ({toPair H (linX Q.X) 0} : Set (CoordinateRing H)))).factors : ℤ)
      = 2
  set g : CoordinateRing H := toPair H (linX Q.X) 0 with hg_def
  have hprime : Prime (pointIdeal Q) := (Ideal.prime_iff_isPrime h_bot).mpr
    (pointIdeal_isMaximal Q).isPrime
  have hirr : Irreducible (Associates.mk (pointIdeal Q)) :=
    Associates.irreducible_mk.mpr hprime.irreducible
  have hm_ne : Associates.mk (Ideal.span ({g} : Set (CoordinateRing H))) ≠ 0 :=
    Associates.mk_ne_zero.mpr (Ideal.span_singleton_eq_bot.not.mpr hgne)
  have hge2 : 2 ≤ (Associates.mk (pointIdeal Q)).count
      (Associates.mk (Ideal.span ({g} : Set (CoordinateRing H)))).factors := by
    rw [← Associates.prime_pow_dvd_iff_le hm_ne hirr]
    exact (Associates.mk_dvd_mk).mpr hdvd2
  -- Close `count ≤ 2` (hence, with `hge2`, `count = 2`) via `Associates.count` additivity
  -- (`Associates.factors_mul`) over `y H * y H = g * algebraMap r` (`hprod`, from
  -- `y_sq_eq_linX_mul_r_of_ramified`): `count` in `span {y H * y H}` = `count` in `span {y H}`
  -- + `count` in `span {y H}`. `pointIdeal_y_not_sq_dvd_of_ramified` (`hnot_sq_dvd_y`) gives
  -- `count in span {y H} < 2`, i.e. `≤ 1` (`Associates.prime_pow_dvd_iff_le` contrapositive at
  -- `k = 2`), so `count in span {y H * y H} ≤ 2`. On the other side, `count` in
  -- `span {g * algebraMap r} = count` in `span {g}` + `count` in `span {algebraMap r}`, and the
  -- latter is `0` (`algebraMap r ∉ pointIdeal Q`, so `pointIdeal Q ∤ span {algebraMap r}`, i.e.
  -- `count = 0` via `prime_pow_dvd_iff_le` at `k = 1`). Equating the two expressions for the
  -- same quantity (`hprod` makes `span {y H * y H} = span {g * algebraMap r}`) gives
  -- `count in span {g} ≤ 2`, closing the squeeze with `hge2`.
  obtain ⟨r, hr⟩ := factors_sub_Y_sq Q
  rw [hY, zero_pow (by norm_num), Polynomial.C_0, sub_zero] at hr
  have hu_notmem : algebraMap k[X] (CoordinateRing H) r ∉ pointIdeal Q :=
    algebraMap_r_notMem_pointIdeal_of_ramified hsf Q hY r hr
  have hprod : y H * y H = g * algebraMap k[X] (CoordinateRing H) r := by
    rw [← sq, hg_def]
    exact y_sq_eq_linX_mul_r_of_ramified Q hY r hr
  have hy_ne : y H ≠ 0 := by
    intro hy0
    have : H.f = 0 := by
      have h2 := y_sq_eq H
      rw [hy0, sq, mul_zero] at h2
      have h2' : algebraMap k[X] (CoordinateRing H) H.f = 0 := h2.symm
      have hdeg : (Polynomial.X ^ 2 - Polynomial.C H.f).degree ≠ 0 := by
        have hlt : (Polynomial.C H.f : Polynomial k[X]).degree <
            (Polynomial.X ^ 2 : Polynomial k[X]).degree := by
          have h2 : (Polynomial.X ^ 2 : Polynomial k[X]).degree = (2 : ℕ) := by
            rw [Polynomial.degree_pow, Polynomial.degree_X]; rfl
          rw [h2]
          exact lt_of_le_of_lt (Polynomial.degree_C_le (a := H.f)) (WithBot.coe_lt_coe.mpr (by decide))
        rw [Polynomial.degree_sub_eq_left_of_degree_lt hlt]
        rw [Polynomial.degree_pow, Polynomial.degree_X]
        intro h
        revert h
        decide
      have hinj : Function.Injective (algebraMap k[X] (CoordinateRing H)) :=
        AdjoinRoot.of.injective_of_degree_ne_zero hdeg
      have h2'' : algebraMap k[X] (CoordinateRing H) H.f = algebraMap k[X] (CoordinateRing H) 0 := by
        rw [map_zero, h2']
      exact hinj h2''
    have hnd := H.natDegree_eq
    rw [this, natDegree_zero] at hnd
    rcases hnd with h5 | h6 <;> omega
  have hr_ne : algebraMap k[X] (CoordinateRing H) r ≠ 0 := by
    intro hr0
    apply hu_notmem
    rw [hr0]
    exact Submodule.zero_mem _
  have hyspan_ne : Associates.mk
      (Ideal.span ({y H} : Set (CoordinateRing H))) ≠ 0 :=
    Associates.mk_ne_zero.mpr (Ideal.span_singleton_eq_bot.not.mpr hy_ne)
  have hrspan_ne : Associates.mk
      (Ideal.span ({algebraMap k[X] (CoordinateRing H) r} : Set (CoordinateRing H))) ≠ 0 :=
    Associates.mk_ne_zero.mpr (Ideal.span_singleton_eq_bot.not.mpr hr_ne)
  -- `count` of `pointIdeal Q` in `span {y H}` is `< 2` (§B.2d: `¬ pointIdeal Q ^ 2 ∣ span {y H}`,
  -- contrapositive of `Associates.prime_pow_dvd_iff_le` at `k = 2`).
  have hy_count_lt2 : (Associates.mk (pointIdeal Q)).count
      (Associates.mk (Ideal.span ({y H} : Set (CoordinateRing H)))).factors < 2 := by
    by_contra hge
    push Not at hge
    rw [← Associates.prime_pow_dvd_iff_le hyspan_ne hirr] at hge
    exact hnot_sq_dvd_y (by simpa [pow_two] using (Associates.mk_le_mk_iff_dvd.mp hge))
  -- `count` of `pointIdeal Q` in `span {algebraMap r}` is `0` (`algebraMap r ∉ pointIdeal Q`
  -- means `pointIdeal Q ∤ span {algebraMap r}`, contrapositive of `k = 1` case).
  have hr_count0 : (Associates.mk (pointIdeal Q)).count
      (Associates.mk (Ideal.span
        ({algebraMap k[X] (CoordinateRing H) r} : Set (CoordinateRing H)))).factors = 0 := by
    by_contra hne0
    have hge1 : 1 ≤ (Associates.mk (pointIdeal Q)).count
        (Associates.mk (Ideal.span
          ({algebraMap k[X] (CoordinateRing H) r} : Set (CoordinateRing H)))).factors :=
      Nat.one_le_iff_ne_zero.mpr hne0
    rw [← Associates.prime_pow_dvd_iff_le hrspan_ne hirr, pow_one] at hge1
    exact hu_notmem (Ideal.dvd_span_singleton.mp (Associates.mk_le_mk_iff_dvd.mp hge1))
  -- The two products `y H * y H` and `g * algebraMap r` are equal (`hprod`), so their `mk`s'
  -- `factors` (hence `count`s) agree; `Associates.factors_mul` turns each product's `factors`
  -- into a sum, giving the count-additivity equation directly.
  have hmk_eq : Associates.mk (Ideal.span ({y H} : Set (CoordinateRing H)) *
      Ideal.span ({y H} : Set (CoordinateRing H))) =
      Associates.mk (Ideal.span ({g} : Set (CoordinateRing H)) *
        Ideal.span ({algebraMap k[X] (CoordinateRing H) r} : Set (CoordinateRing H))) := by
    rw [Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_mul_span_singleton, hprod]
  have hcount_eq : (Associates.mk (pointIdeal Q)).count
      (Associates.mk (Ideal.span ({y H} : Set (CoordinateRing H)) *
        Ideal.span ({y H} : Set (CoordinateRing H)))).factors =
      (Associates.mk (pointIdeal Q)).count
        (Associates.mk (Ideal.span ({g} : Set (CoordinateRing H)) *
          Ideal.span
            ({algebraMap k[X] (CoordinateRing H) r} : Set (CoordinateRing H)))).factors := by
    rw [hmk_eq]
  -- `Associates.count` unfolds (via `hirr : Irreducible (mk (pointIdeal Q))`) to `bcount`,
  -- which on `factors = ↑s` (nonzero case, `factors_mk`/`factors_eq_some_iff_ne_zero`) is
  -- `Multiset.count`; `factors_mul` turns the product's `factors` into a `FactorSet` sum,
  -- `FactorSet.coe_add` pushes the coercion through, and `Multiset.count_add` distributes.
  have hcount_add : ∀ x y : CoordinateRing H, x ≠ 0 → y ≠ 0 →
      (Associates.mk (pointIdeal Q)).count
        (Associates.mk (Ideal.span ({x} : Set (CoordinateRing H)) *
          Ideal.span ({y} : Set (CoordinateRing H)))).factors =
      (Associates.mk (pointIdeal Q)).count
        (Associates.mk (Ideal.span ({x} : Set (CoordinateRing H)))).factors +
      (Associates.mk (pointIdeal Q)).count
        (Associates.mk (Ideal.span ({y} : Set (CoordinateRing H)))).factors := by
    intro x y hx hy
    have hxne : Associates.mk (Ideal.span ({x} : Set (CoordinateRing H))) ≠ 0 :=
      Associates.mk_ne_zero.mpr (Ideal.span_singleton_eq_bot.not.mpr hx)
    have hyne : Associates.mk (Ideal.span ({y} : Set (CoordinateRing H))) ≠ 0 :=
      Associates.mk_ne_zero.mpr (Ideal.span_singleton_eq_bot.not.mpr hy)
    rw [← Associates.mk_mul_mk, Associates.factors_mul]
    obtain ⟨sx, hsx⟩ := Associates.factors_eq_some_iff_ne_zero.mpr hxne
    obtain ⟨sy, hsy⟩ := Associates.factors_eq_some_iff_ne_zero.mpr hyne
    rw [hsx, hsy, ← Associates.FactorSet.coe_add]
    simp only [Associates.count, dif_pos hirr, Associates.bcount]
    exact Multiset.count_add _ sx sy

  -- `hcount_eq` is now the additivity equation: `count(y)+count(y) = count(g)+count(r-part)`.
  rw [hcount_add (y H) (y H) hy_ne hy_ne] at hcount_eq
  rw [hcount_add g (algebraMap k[X] (CoordinateRing H) r) hgne hr_ne] at hcount_eq
  rw [hr_count0, add_zero] at hcount_eq
  have hle2 : (Associates.mk (pointIdeal Q)).count
      (Associates.mk (Ideal.span ({g} : Set (CoordinateRing H)))).factors ≤ 2 := by omega
  have hcount2 : (Associates.mk (pointIdeal Q)).count
      (Associates.mk (Ideal.span ({g} : Set (CoordinateRing H)))).factors = 2 :=
    le_antisymm hle2 hge2
  rw [hcount2]
  norm_cast
  
/-- **The genuinely hard step, left open — now assembled from §A/§B.1/§B.2 above rather than
one monolithic `sorry`.** The exact order of vanishing of `g a := toPair H
(linX a) 0` at an affine point `Q`: `0` away from the fiber `Q.X = a`; `1` at an unramified
point of the fiber (`Q.X = a`, `Q.Y ≠ 0`); `2` at the ramification point (`Q.X = a`, `Q.Y = 0`,
which forces `f(a) = 0` and `Q = ι Q`). Needs a local-uniformizer argument at `pointIdeal Q`
not currently available anywhere in `PrincipalDivisors.lean` — see the module docstring above
for what specifically is missing. Stated with `hAB`-style nonvanishing side conditions
mirroring `ordAt_eq_count`'s own hypotheses (`h_bot`, both used identically here), so this
slots into the existing `ordAt` API without inventing new preconditions.
**Status: §A (`Q.X ≠ a`) is fully proved. §B.1/§B.2 (`Q.X = a`, both sub-cases) remain
`sorry`'d, isolated in their own named lemmas above rather than duplicated here.** -/
theorem ordAt_linX_eq_one_of_unramified [IsDedekindDomain (CoordinateRing H)]
    (hchar : (2 : k) ≠ 0) (a : k) (Q : H.Point) (h_bot : pointIdeal Q ≠ ⊥)
    (heq : Q.X = a) (hY : Q.Y ≠ 0) :
    ordAt Q (linX a) 0 = 1 := by
  classical
  rw [← heq]
  have hdvd := ordAt_linX_eq_one_of_unramified_dvd Q.X Q rfl
  have hnot_sq_dvd := pointIdeal_linX_not_sq_dvd Q hchar hY
  have hgne : toPair H (linX Q.X) 0 ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => linX_ne_zero Q.X hA
  rw [ordAt_eq_count Q (linX Q.X) 0 hgne h_bot]
  show ((Associates.mk (pointIdeal Q)).count
      (Associates.mk (Ideal.span ({toPair H (linX Q.X) 0} : Set (CoordinateRing H)))).factors : ℤ)
      = 1
  have hprime : Prime (pointIdeal Q) := (Ideal.prime_iff_isPrime h_bot).mpr
    (pointIdeal_isMaximal Q).isPrime
  have hirr : Irreducible (Associates.mk (pointIdeal Q)) :=
    Associates.irreducible_mk.mpr hprime.irreducible
  have hm_ne : Associates.mk (Ideal.span
      ({toPair H (linX Q.X) 0} : Set (CoordinateRing H))) ≠ 0 :=
    Associates.mk_ne_zero.mpr (Ideal.span_singleton_eq_bot.not.mpr hgne)
  have hge1 : 1 ≤ (Associates.mk (pointIdeal Q)).count
      (Associates.mk (Ideal.span
        ({toPair H (linX Q.X) 0} : Set (CoordinateRing H)))).factors := by
    rw [← Associates.prime_pow_dvd_iff_le hm_ne hirr, pow_one]
    exact Associates.mk_dvd_mk.mpr hdvd
  have hlt2 : (Associates.mk (pointIdeal Q)).count
      (Associates.mk (Ideal.span
        ({toPair H (linX Q.X) 0} : Set (CoordinateRing H)))).factors < 2 := by
    by_contra hge
    push Not at hge
    rw [← Associates.prime_pow_dvd_iff_le hm_ne hirr] at hge
    exact hnot_sq_dvd (by simpa [pow_two] using (Associates.mk_le_mk_iff_dvd.mp hge))
  have heq1 : (Associates.mk (pointIdeal Q)).count
      (Associates.mk (Ideal.span
        ({toPair H (linX Q.X) 0} : Set (CoordinateRing H)))).factors = 1 := by omega
  rw [heq1]
  norm_cast
theorem ordAt_linX_eq [IsDedekindDomain (CoordinateRing H)] [DecidableEq k]
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f) (a : k) (Q : H.Point)
    (h_bot : pointIdeal Q ≠ ⊥) :
    ordAt Q (linX a) 0 = if Q.X ≠ a then 0 else if Q.Y ≠ 0 then 1 else 2 := by
  split_ifs with hne hY
  · exact ordAt_linX_eq_zero_of_ne a Q h_bot hne
  · exact ordAt_linX_eq_one_of_unramified hchar a Q h_bot (not_ne_iff.mp hne) hY
  · exact ordAt_linX_eq_two_of_ramified hsf a Q h_bot (not_ne_iff.mp hne) (not_ne_iff.mp hY)

/-- The support of `ordAt _ (linX a) 0`, as a `Finset`, for a nonzero `Y`-coordinate point
`P` with `P.X = a`: exactly `{P, ι P}` (two distinct points, by `iota_ne_self_of_Y_ne_zero`).
Conditional on `ordAt_linX_eq`. -/
theorem divToPair_linX_eq_of_unramified [IsDedekindDomain (CoordinateRing H)]
    [DecidableEq H.Point]
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f) (P : H.Point) (hY : P.Y ≠ 0) :
    divToPair (linX P.X) 0 ({P, Point.iota P} : Finset H.Point) =
      single P + single (Point.iota P) := by
  classical
  have hne : P ≠ Point.iota P := (Point.iota_ne_self_of_Y_ne_zero hchar hY).symm
  unfold divToPair
  rw [Finset.sum_pair hne]
  have hordP : ordAt P (linX P.X) 0 = 1 := by
    rw [ordAt_linX_eq hchar hsf P.X P (pointIdeal_ne_bot P)]
    simp [hY]
  have hordIota : ordAt (Point.iota P) (linX P.X) 0 = 1 := by
    rw [ordAt_linX_eq hchar hsf P.X (Point.iota P) (pointIdeal_ne_bot _)]
    simp [Point.iota_X, Point.iota_Y, hY]
  rw [hordP, hordIota, one_smul, one_smul]

/-- The degenerate (Weierstrass/ramification) case: `P.Y = 0` forces `ι P = P`
(`iota` fixes it), and `g P.X` vanishes to order `2` there — matching
`single P + single (ι P) = single P + single P = 2 • single P`. Conditional on
`ordAt_linX_eq`. -/
theorem divToPair_linX_eq_of_ramified [IsDedekindDomain (CoordinateRing H)]
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f) (P : H.Point) (hY : P.Y = 0) :
    divToPair (linX P.X) 0 ({P} : Finset H.Point) =
      single P + single (Point.iota P) := by
  classical
  have hiota : Point.iota P = P := by
    apply Subtype.ext
    apply Prod.ext
    · exact Point.iota_X P
    · change (Point.iota P).Y = P.Y
      rw [Point.iota_Y, hY, neg_zero]
  rw [hiota]
  unfold divToPair
  rw [Finset.sum_singleton]
  have hordP : ordAt P (linX P.X) 0 = 2 := by
    rw [ordAt_linX_eq hchar hsf P.X P (pointIdeal_ne_bot P)]
    simp [hY]
  rw [hordP]
  change (2 : ℤ) • single P = single P + single P
  rw [two_smul]

/-- **Uniform fiber-support `Finset`, covering both the unramified and ramified case of a
single point `x`.** `fiberSupport x = {x}` when `x.Y = 0` (the point is its own `ι`-image, the
Weierstrass/ramified case) and `{x, ι x}` otherwise (two distinct points). Packaging this as
one `Finset`-valued function (rather than case-splitting at every call site) lets
`divToPair_linX_eq`/`hsupp_linX_eq_of_notMem_fiberSupport` below state the unramified/ramified
dichotomy once each, uniformly in `x`. -/
noncomputable def fiberSupport (x : H.Point) : Finset H.Point :=
  letI := Classical.dec
  if x.Y = 0 then {x} else {x, Point.iota x}


/-- `divToPair (linX x.X) 0 (fiberSupport x) = single x + single (ι x)`, uniformly across the
unramified/ramified dichotomy — immediate case split into `divToPair_linX_eq_of_ramified`/
`_of_unramified` after unfolding `fiberSupport`. -/
theorem divToPair_linX_eq [IsDedekindDomain (CoordinateRing H)]
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f) (x : H.Point) :
    divToPair (linX x.X) 0 (fiberSupport x) = single x + single (Point.iota x) := by
  classical
  unfold fiberSupport
  split_ifs with hY
  · exact divToPair_linX_eq_of_ramified hchar hsf x hY
  · exact divToPair_linX_eq_of_unramified hchar hsf x hY

/-- The `hsupp` side condition `fiberSupport x` needs to feed `deg_divToPairRatio_eq_zero`/
`principalSubgroup`'s generating-set membership: away from `fiberSupport x`, `ordAt _ (linX
x.X) 0 = 0`. Splits on whether `Q.X = x.X`: if not, `ordAt_linX_eq_zero_of_ne` (§A) applies
directly; if so but `Q ∉ fiberSupport x`, `Q` must still differ from both `x` and (when
`x.Y ≠ 0`) `ι x` — but `ordAt_linX_eq` (§B) shows `ordAt Q (linX x.X) 0 = 0` fails only at
`Q.X ≠ x.X`, so we instead show directly `Q ∉ fiberSupport x` together with `Q.X = x.X`
is impossible, closing this branch by deriving `Q ∈ fiberSupport x` and contradicting `hQ`. -/
theorem hsupp_linX [IsDedekindDomain (CoordinateRing H)]
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f) (x : H.Point) :
    ∀ Q, Q ∉ fiberSupport x → ordAt Q (linX x.X) 0 = 0 := by
  classical
  intro Q hQ
  rw [ordAt_linX_eq hchar hsf x.X Q (pointIdeal_ne_bot Q)]
  by_cases hne : Q.X = x.X
  · exfalso
    apply hQ
    unfold fiberSupport
    split_ifs with hxY
    · -- `x.Y = 0`: `fiberSupport x = {x}`; need `Q = x` from `Q.X = x.X` and `Q.Y = 0` (forced).
      by_cases hQY : Q.Y = 0
      · have : Q = x := by
          apply Subtype.ext; apply Prod.ext
          · exact hne
          · change Q.Y = x.Y; rw [hQY, hxY]
        simp [this]
      · exfalso
        -- `Q.Y ≠ 0` but `Q.X = x.X` and `x.Y = 0`: derive `Q.Y^2 = x.Y^2 = 0` from `Y_sq`
        -- and `hne`, contradicting `hQY`.
        have hQsq : Q.Y ^ 2 = H.f.eval Q.X := Point.Y_sq Q
        have hxsq : x.Y ^ 2 = H.f.eval x.X := Point.Y_sq x
        rw [hne, ← hxsq, hxY, zero_pow (two_ne_zero)] at hQsq
        exact hQY (sq_eq_zero_iff.mp hQsq)
    · -- `x.Y ≠ 0`: `fiberSupport x = {x, ι x}`; `Q.X = x.X` forces `Q = x` or `Q = ι x`.
      have hQsq : Q.Y ^ 2 = H.f.eval Q.X := Point.Y_sq Q
      have hxsq : x.Y ^ 2 = H.f.eval x.X := Point.Y_sq x
      rw [hne, ← hxsq] at hQsq
      have hYeq : Q.Y = x.Y ∨ Q.Y = -x.Y := by
        have hfact : (Q.Y - x.Y) * (Q.Y + x.Y) = 0 := by
          have hsub : Q.Y ^ 2 - x.Y ^ 2 = 0 := sub_eq_zero.mpr hQsq
          have : (Q.Y - x.Y) * (Q.Y + x.Y) = Q.Y ^ 2 - x.Y ^ 2 := by ring
          rw [this, hsub]
        rcases mul_eq_zero.mp hfact with h | h
        · left; exact sub_eq_zero.mp h
        · right; exact eq_neg_of_add_eq_zero_left h
      rcases hYeq with hYeq | hYeq
      · have : Q = x := by
          apply Subtype.ext; apply Prod.ext
          · exact hne
          · exact hYeq
        simp [this]
      · have : Q = Point.iota x := by
          apply Subtype.ext; apply Prod.ext
          · exact hne.trans (Point.iota_X x).symm
          · change Q.Y = (Point.iota x).Y; rw [Point.iota_Y]; exact hYeq
        simp [this]
  · simp [hne]

/-- **The target of this file**: for any two points `x₁, x₃`, the fiber-difference divisor is
principal for the concrete `D := principalDivisorData H hdeg` — i.e.
`(principalDivisorData H hdeg).HyperellipticClass`. Built as a `divToPairRatio` generator of
the (now correctly widened, matching-`ordInfOfPair`) `principalSubgroup` from
`PrincipalDivisorSubgroup.lean`: `A₁ = linX x₁.X`, `S₁ = fiberSupport x₁`, `A₂ = linX x₃.X`,
`S₂ = fiberSupport x₃`, with `ordInfOfPair` matching automatically (`ordInfOfPair_linX`, both
`-2`). The remaining `hspec` Nullstellensatz-style hypotheses (needed by `principalSubgroup`'s
own generating-set membership, per `PrincipalDivisors.lean`'s `deg_div_eq_zero_deg5`) are not
discharged anywhere in this codebase yet (see that theorem's doc comment), so they are threaded
through as extra hypotheses here, matching the convention already used for the `Module.Finite`
instance argument. -/
theorem hyperellipticClass_principalDivisorData (hdeg : H.f.natDegree = 5)
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f) [IsDedekindDomain (CoordinateRing H)]
    [∀ (a : k) (S : Finset H.Point),
      ∀ P : S, Module.Finite k (CoordinateRing H ⧸ pointIdeal P.1 ^ (ordAt P.1 (linX a) 0).toNat)]
    (hspec : ∀ (a : k), ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk v.asIdeal).count
        (Associates.mk (Ideal.span ({toPair H (linX a) 0} : Set (CoordinateRing H)))).factors
          ≠ 0 → ∃ P, v.asIdeal = pointIdeal P) :
    (principalDivisorData H hdeg).HyperellipticClass := by
  classical
  intro x₁ x₃
  show (single x₁ + single (Point.iota x₁) - single x₃ - single (Point.iota x₃) : Divisor H) ∈
    (principalDivisorData H hdeg).P
  have hgoal_eq : (single x₁ + single (Point.iota x₁) - single x₃ - single (Point.iota x₃)
        : Divisor H) =
      divToPairRatio (linX x₁.X) 0 (fiberSupport x₁) (linX x₃.X) 0 (fiberSupport x₃) := by
    unfold divToPairRatio
    rw [divToPair_linX_eq hchar hsf x₁, divToPair_linX_eq hchar hsf x₃]
    abel
  rw [hgoal_eq]
  show _ ∈ principalSubgroup H hdeg
  apply AddSubgroup.subset_closure
  refine ⟨linX x₁.X, 0, fiberSupport x₁, ?_, hsupp_linX hchar hsf x₁, hspec x₁.X,
    fun P => ‹∀ (a : k) (S : Finset H.Point), ∀ P : S, Module.Finite k
      (CoordinateRing H ⧸ pointIdeal P.1 ^ (ordAt P.1 (linX a) 0).toNat)› x₁.X (fiberSupport x₁) P,
    linX x₃.X, 0, fiberSupport x₃, ?_, hsupp_linX hchar hsf x₃, hspec x₃.X,
    fun P => ‹∀ (a : k) (S : Finset H.Point), ∀ P : S, Module.Finite k
      (CoordinateRing H ⧸ pointIdeal P.1 ^ (ordAt P.1 (linX a) 0).toNat)› x₃.X (fiberSupport x₃) P,
    ?_, rfl⟩
  · exact fun ⟨hA, _⟩ => linX_ne_zero x₁.X hA
  · exact fun ⟨hA, _⟩ => linX_ne_zero x₃.X hA
  · rw [ordInfOfPair_linX, ordInfOfPair_linX]

end HyperellipticPolynomial
