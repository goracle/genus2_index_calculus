import Mathlib
import Genus2Lean.HyperellipticFunctionField
import Genus2Lean.AffinePoints
import Genus2Lean.DivisorClassGroup
import Genus2Lean.PrincipalDivisors
import Genus2Lean.PrincipalDivisorSubgroup
import Genus2Lean.FFKSidon
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
below are left `sorry`'d for this reason, not merely because `ordAt_linX_eq` is open.** Fixing
this properly means revisiting `PrincipalDivisorSubgroup.lean`'s `principalSubgroup` definition
before this file's final theorem can be completed, not just filling in more Lean here.

## Summary of what's proved vs. open in this file
-/

/-!
* `linX_mem_pointIdeal_iff` (proved): `g a ∈ pointIdeal Q ↔ Q.X = a` — vanishing-locus
  membership, a direct corollary of `pointIdeal_ne_of_ne`'s own computation (`evalAtPoint Q`
  applied to `algebraMap (X - C a)` is `Q.X - a`). This is real and mechanical.
* **`ordAt_linX_eq` (NOT proved — `sorry`'d, isolated as the one genuinely hard step).** The
  *exact multiplicity* of vanishing: `ordAt Q (linX a) 0 = 1` when `Q.X = a` and `Q.Y ≠ 0`
  (the generic, unramified case), vs `= 2` when `Q.X = a` and `Q.Y = 0` (the Weierstrass /
  ramification case), vs `= 0` when `Q.X ≠ a`. This needs a genuine local-uniformizer
  argument at `pointIdeal Q` (is `linX a`, or `y H` in the ramified case, a uniformizer of the
  DVR-localization at `pointIdeal Q`?) that nothing in `PrincipalDivisors.lean` currently
  supplies — that file's `ordAt` machinery is entirely about *global* factorization/dimension
  bookkeeping (CRT, `finrank`), never a *local* computation of `ordAt` for a specific named
  function at a specific point. This is new mathematical content, not a citation gap.
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

/-- **§B.1c-iii, isolated sub-fact, the true geometric crux — `sorry`'d, isolated as the final
irreducible piece.** **Correction from an earlier draft of this lemma**: an earlier version of
this file attempted to show `y H - C Q.Y` itself is a uniformizer at `pointIdeal Q` (i.e.
`pointIdeal Q ^ 2 ∤ span {y H - C Q.Y}`, or even the stronger `span {y H - C Q.Y} = pointIdeal
Q`). **That version is false in general.** Writing `s := X - C Q.X`, `t := y H - C Q.Y`, the
curve relation gives `t * (t + 2 • C Q.Y) = s * r` for `r` from `factors_sub_Y_sq`, i.e. `2 *
Q.Y * t ≡ s * r (mod pointIdeal Q ^ 2)` (since `t ^ 2 ∈ pointIdeal Q ^ 2`); if `r ∈ pointIdeal
Q` (equivalently, `Q.X` is a *repeated* root of `H.f - C (Q.Y ^ 2)` in `k[X]`, i.e. the
`x`-coordinate map is ramified at `Q` for reasons unrelated to `Q.Y = 0` — genuinely possible,
`HyperellipticPolynomial` imposes no squarefreeness of `H.f`), then `s * r ∈ pointIdeal Q ^ 2`
too, forcing (as `2 * Q.Y` is a unit, being the image of a nonzero field element) `t ∈
pointIdeal Q ^ 2` — the negation of what the earlier draft claimed.

**The correct, unconditional uniformizer at an unramified point is `s := X - C Q.X` (i.e.
`toPair H (linX Q.X) 0`), not `t`.** Geometrically: the plane curve `Y² = f(X)` is smooth at
`(Q.X, Q.Y)` with tangent line `2·Q.Y·(dY) - f'(Q.X)·(dX) = 0`; since `Q.Y ≠ 0` (char ≠ 2), the
`dY`-coefficient `2·Q.Y` is always nonzero, so the tangent line is never vertical, so `X - Q.X`
is *always* a valid local coordinate there — regardless of whether `f'(Q.X)` vanishes. This
matches the algebra above: from `t * (y H + C Q.Y) = s * r` and `y H + C Q.Y` a **unit modulo
`pointIdeal Q`** (`y_add_C_Y_notMem_pointIdeal_of_Y_ne_zero`, unconditional on `r`), `t` is,
*in the localization at `pointIdeal Q`* (a DVR, since `IsDedekindDomain`), a multiple of `s`
— so the local maximal ideal is generated by `s` alone, giving `ordAt Q s 0 ≤ 1`; combined with
`s ∈ pointIdeal Q` (`ordAt ≥ 1`, `toPair_linX_mem_pointIdeal_iff`), `ordAt Q s 0 = 1` exactly.
**Left `sorry`'d**: formalizing this needs either (a) explicit `HeightOneSpectrum`/DVR
localization reasoning (`intValuation`, `exists_uniformizer`, division in the localization), or
(b) a Nakayama-style argument (`Submodule.eq_smul_of_le_smul_of_le_jacobson` in
`Mathlib.RingTheory.Nakayama`, applied to the f.g. ideal `pointIdeal Q` to show `pointIdeal Q =
span {s} + pointIdeal Q ^ 2` forces `pointIdeal Q = span {s}` outright) — neither is currently
built out in `PrincipalDivisors.lean`. -/
theorem pointIdeal_linX_not_sq_dvd [IsDedekindDomain (CoordinateRing H)]
    (Q : H.Point) (hchar : (2 : k) ≠ 0) (hY : Q.Y ≠ 0) :
    ¬ pointIdeal Q ^ 2 ∣ Ideal.span ({toPair H (linX Q.X) 0} : Set (CoordinateRing H)) := by
  sorry

/-- **§B.1c, the genuine hard step — reduced to `pointIdeal_linX_not_sq_dvd` above, which is now
the sole remaining `sorry` in this development's local-uniformizer argument.** Immediate from
`pointIdeal_linX_not_sq_dvd` after `heq : Q.X = a` rewrites `Q.X` to `a` (or vice versa). No
longer needs the `y H ± C Q.Y` factorization detour of the earlier (incorrect) draft — see
`pointIdeal_linX_not_sq_dvd`'s docstring for why that detour doesn't work in general. -/
theorem ordAt_linX_eq_one_of_unramified_not_sq_dvd [IsDedekindDomain (CoordinateRing H)]
    (hchar : (2 : k) ≠ 0) (a : k) (Q : H.Point) (h_bot : pointIdeal Q ≠ ⊥)
    (heq : Q.X = a) (hY : Q.Y ≠ 0) :
    ¬ pointIdeal Q ^ 2 ∣ Ideal.span ({toPair H (linX a) 0} : Set (CoordinateRing H)) := by
  rw [← heq]
  exact pointIdeal_linX_not_sq_dvd Q hchar hY

/-- **§B.1d, assembly — confirmed lemma names, mechanical modulo §B.1a/§B.1c.** Given
`pointIdeal Q ∣ span {g}` (§B.1a, proved) and `¬ pointIdeal Q ^ 2 ∣ span {g}` (§B.1c, open),
conclude `ordAt Q (linX a) 0 = 1`. Route (confirmed against Mathlib docs, not against a live
goal): `ordAt_eq_count` (already proved in `PrincipalDivisors.lean`) reduces the goal to
`(Associates.mk (pointIdeal Q)).count (Associates.mk (span {g})).factors = 1`. Irreducibility
of `Associates.mk (pointIdeal Q)` comes from `Ideal.prime_iff_isPrime h_bot` (turns
`(pointIdeal_isMaximal Q).isPrime` into `Prime (pointIdeal Q)`) then the generic `Prime →
Irreducible`. `Associates.prime_pow_dvd_iff_le {m p} (h₁ : m ≠ 0) (h₂ : Irreducible p) {k} :
p^k ≤ m ↔ k ≤ p.count m.factors` (with `Associates`-order `≤` = `dvd`) then gives `count ≥ 1`
from `hdvd` and (its contrapositive at `k=2`) `count < 2` from `hnotsqdvd`, forcing `count = 1`
by `Nat` antisymmetry — no `WithZero.log`/`intValuation` squeeze needed, sidestepping the
originally sketched route entirely. `hgne : toPair H (linX a) 0 ≠ 0` (needed for
`ordAt_eq_count`'s hypothesis) is proved directly via `toPair_eq_zero_iff` + `linX_ne_zero`.
**Not checked against a live goal**: whether the `show` step correctly unfolds `ordAt_eq_count`'s
`(pointHeightOne Q h_bot).asIdeal` to the bare `pointIdeal Q` used throughout the rest of this
proof (they're definitionally equal via `pointHeightOne`'s `asIdeal := pointIdeal P` field, but
`show` needs Lean to accept that unfolding at this point in the term), and the exact argument
order/simp behavior of `Associates.mk_dvd_mk`, were not confirmed. -/
theorem ordAt_linX_eq_one_of_unramified [IsDedekindDomain (CoordinateRing H)]
    (hchar : (2 : k) ≠ 0) (a : k) (Q : H.Point) (h_bot : pointIdeal Q ≠ ⊥) (heq : Q.X = a)
    (hY : Q.Y ≠ 0) :
    ordAt Q (linX a) 0 = 1 := by
  classical
  have hdvd := ordAt_linX_eq_one_of_unramified_dvd a Q heq
  have hnotsqdvd := ordAt_linX_eq_one_of_unramified_not_sq_dvd hchar a Q h_bot heq hY
  have hgne : toPair H (linX a) 0 ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => linX_ne_zero a hA
  rw [ordAt_eq_count Q (linX a) 0 hgne h_bot]
  show ((Associates.mk (pointIdeal Q)).count
      (Associates.mk (Ideal.span ({toPair H (linX a) 0} : Set (CoordinateRing H)))).factors : ℤ)
      = 1
  set g : CoordinateRing H := toPair H (linX a) 0 with hg_def
  have hprime : Prime (pointIdeal Q) := (Ideal.prime_iff_isPrime h_bot).mpr
    (pointIdeal_isMaximal Q).isPrime
  have hirr : Irreducible (Associates.mk (pointIdeal Q)) :=
    Associates.irreducible_mk.mpr hprime.irreducible
  have hm_ne : Associates.mk (Ideal.span ({g} : Set (CoordinateRing H))) ≠ 0 :=
    Associates.mk_ne_zero.mpr (Ideal.span_singleton_eq_bot.not.mpr hgne)
  have hge1 : 1 ≤ (Associates.mk (pointIdeal Q)).count
      (Associates.mk (Ideal.span ({g} : Set (CoordinateRing H)))).factors := by
    rw [← Associates.prime_pow_dvd_iff_le hm_ne hirr, pow_one]
    exact (Associates.mk_dvd_mk).mpr hdvd
  have hlt2 : ¬ (2 ≤ (Associates.mk (pointIdeal Q)).count
      (Associates.mk (Ideal.span ({g} : Set (CoordinateRing H)))).factors) := by
    rw [← Associates.prime_pow_dvd_iff_le hm_ne hirr]
    exact (Associates.mk_dvd_mk).not.mpr hnotsqdvd
  have hcount_eq : (Associates.mk (pointIdeal Q)).count
      (Associates.mk (Ideal.span ({g} : Set (CoordinateRing H)))).factors = 1 := by omega
  rw [hcount_eq]
  norm_cast

/-- **§B.2, ramified (`Q.Y = 0`), `sorry`'d.** Claim: `ordAt Q (linX a) 0 = 2`. Proof sketch:
`Q.Y = 0` forces `f(a) = 0` (from `Y_sq`) and `Q = ι Q` (fixed point of the involution), the
Weierstrass-point case. Here `linX a` is *not* a local uniformizer (it vanishes to even order
by the standard ramification-index-2 argument for a double cover branched at `Q`); the actual
uniformizer is `y H` itself, and `linX a` should be expressible as `(y H) ^ 2 · unit` locally,
giving multiplicity `2` directly. Needs the same local-uniformizer infrastructure as §B.1,
specialized to the branch-point case (ramification index `2` at a Weierstrass point of a
genus-2 hyperelliptic double cover — standard algebraic geometry, not yet in this codebase's
Lean). -/
theorem ordAt_linX_eq_two_of_ramified [IsDedekindDomain (CoordinateRing H)]
    (a : k) (Q : H.Point) (h_bot : pointIdeal Q ≠ ⊥) (heq : Q.X = a) (hY : Q.Y = 0) :
    ordAt Q (linX a) 0 = 2 := by
  sorry

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
theorem ordAt_linX_eq [IsDedekindDomain (CoordinateRing H)] [DecidableEq k]
    (hchar : (2 : k) ≠ 0) (a : k) (Q : H.Point) (h_bot : pointIdeal Q ≠ ⊥) :
    ordAt Q (linX a) 0 = if Q.X ≠ a then 0 else if Q.Y ≠ 0 then 1 else 2 := by
  split_ifs with hne hY
  · exact ordAt_linX_eq_zero_of_ne a Q h_bot hne
  · exact ordAt_linX_eq_one_of_unramified hchar a Q h_bot (not_ne_iff.mp hne) hY
  · exact ordAt_linX_eq_two_of_ramified a Q h_bot (not_ne_iff.mp hne) (not_ne_iff.mp hY)

/-- The support of `ordAt _ (linX a) 0`, as a `Finset`, for a nonzero `Y`-coordinate point
`P` with `P.X = a`: exactly `{P, ι P}` (two distinct points, by `iota_ne_self_of_Y_ne_zero`).
Conditional on `ordAt_linX_eq`. -/
theorem divToPair_linX_eq_of_unramified [IsDedekindDomain (CoordinateRing H)]
    [DecidableEq H.Point]
    (hchar : (2 : k) ≠ 0) (P : H.Point) (hY : P.Y ≠ 0) :
    divToPair (linX P.X) 0 ({P, Point.iota P} : Finset H.Point) =
      single P + single (Point.iota P) := by
  classical
  have hne : P ≠ Point.iota P := (Point.iota_ne_self_of_Y_ne_zero hchar hY).symm
  unfold divToPair
  rw [Finset.sum_pair hne]
  have hordP : ordAt P (linX P.X) 0 = 1 := by
    rw [ordAt_linX_eq hchar P.X P (pointIdeal_ne_bot P)]
    simp [hY]
  have hordIota : ordAt (Point.iota P) (linX P.X) 0 = 1 := by
    rw [ordAt_linX_eq hchar P.X (Point.iota P) (pointIdeal_ne_bot _)]
    simp [Point.iota_X, Point.iota_Y, hY]
  rw [hordP, hordIota, one_smul, one_smul]

/-- The degenerate (Weierstrass/ramification) case: `P.Y = 0` forces `ι P = P`
(`iota` fixes it), and `g P.X` vanishes to order `2` there — matching
`single P + single (ι P) = single P + single P = 2 • single P`. Conditional on
`ordAt_linX_eq`. -/
theorem divToPair_linX_eq_of_ramified [IsDedekindDomain (CoordinateRing H)]
    (hchar : (2 : k) ≠ 0) (P : H.Point) (hY : P.Y = 0) :
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
    rw [ordAt_linX_eq hchar P.X P (pointIdeal_ne_bot P)]
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
    (hchar : (2 : k) ≠ 0) (x : H.Point) :
    divToPair (linX x.X) 0 (fiberSupport x) = single x + single (Point.iota x) := by
  classical
  unfold fiberSupport
  split_ifs with hY
  · exact divToPair_linX_eq_of_ramified hchar x hY
  · exact divToPair_linX_eq_of_unramified hchar x hY

/-- The `hsupp` side condition `fiberSupport x` needs to feed `deg_divToPairRatio_eq_zero`/
`principalSubgroup`'s generating-set membership: away from `fiberSupport x`, `ordAt _ (linX
x.X) 0 = 0`. Splits on whether `Q.X = x.X`: if not, `ordAt_linX_eq_zero_of_ne` (§A) applies
directly; if so but `Q ∉ fiberSupport x`, `Q` must still differ from both `x` and (when
`x.Y ≠ 0`) `ι x` — but `ordAt_linX_eq` (§B) shows `ordAt Q (linX x.X) 0 = 0` fails only at
`Q.X ≠ x.X`, so we instead show directly `Q ∉ fiberSupport x` together with `Q.X = x.X`
is impossible, closing this branch by deriving `Q ∈ fiberSupport x` and contradicting `hQ`. -/
theorem hsupp_linX [IsDedekindDomain (CoordinateRing H)]
    (hchar : (2 : k) ≠ 0) (x : H.Point) :
    ∀ Q, Q ∉ fiberSupport x → ordAt Q (linX x.X) 0 = 0 := by
  classical
  intro Q hQ
  rw [ordAt_linX_eq hchar x.X Q (pointIdeal_ne_bot Q)]
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
    (hchar : (2 : k) ≠ 0) [IsDedekindDomain (CoordinateRing H)]
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
    rw [divToPair_linX_eq hchar x₁, divToPair_linX_eq hchar x₃]
    abel
  rw [hgoal_eq]
  show _ ∈ principalSubgroup H hdeg
  apply AddSubgroup.subset_closure
  refine ⟨linX x₁.X, 0, fiberSupport x₁, ?_, hsupp_linX hchar x₁, hspec x₁.X,
    fun P => ‹∀ (a : k) (S : Finset H.Point), ∀ P : S, Module.Finite k
      (CoordinateRing H ⧸ pointIdeal P.1 ^ (ordAt P.1 (linX a) 0).toNat)› x₁.X (fiberSupport x₁) P,
    linX x₃.X, 0, fiberSupport x₃, ?_, hsupp_linX hchar x₃, hspec x₃.X,
    fun P => ‹∀ (a : k) (S : Finset H.Point), ∀ P : S, Module.Finite k
      (CoordinateRing H ⧸ pointIdeal P.1 ^ (ordAt P.1 (linX a) 0).toNat)› x₃.X (fiberSupport x₃) P,
    ?_, rfl⟩
  · exact fun ⟨hA, _⟩ => linX_ne_zero x₁.X hA
  · exact fun ⟨hA, _⟩ => linX_ne_zero x₃.X hA
  · rw [ordInfOfPair_linX, ordInfOfPair_linX]

end HyperellipticPolynomial
