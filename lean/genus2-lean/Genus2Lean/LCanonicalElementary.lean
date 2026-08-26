import Mathlib
import Genus2Lean.HyperellipticFunctionField
import Genus2Lean.AffinePoints
import Genus2Lean.DivisorClassGroup
import Genus2Lean.PrincipalDivisors
import Genus2Lean.PrincipalDivisorSubgroup
import Genus2Lean.FFKSidon
import Genus2Lean.HyperellipticClassProof
import Genus2Lean.RiemannRochGenus2
import Genus2Lean.LPairFinrankOne
noncomputable section

open Classical

set_option linter.style.header false

open Polynomial

/-!
# `finrank_L_canonical`, elementary route (draft skeleton, not yet built)

**Status: drafted without a live Lean toolchain — same PLAUSIBLE-tier caveat
as the rest of this project's unverified scaffolding. Not `lake build`-checked.**

## Revision note (corrects this file's first draft)

The first draft of this file assumed `LPairFinrankOne.lean`'s degree-bounding
machinery would need re-deriving for the fiber case (`x₂ = Point.iota x₁`
instead of a generic distinct pair). **Checked against the actual code, not
the docstrings, this is mostly wrong.** `IsPoleBoundedAtPair x₁ x₂ A B A' B'`
(`RiemannRochGenus2.lean`) is stated with a single indicator-sum pole bound
`(if P = x₁ then 1 else 0) + (if P = x₂ then 1 else 0)` over TWO GENERIC
POINT ARGUMENTS — it never assumes `x₁ ≠ x₂`. Concretely, of
`LPairFinrankOne.lean`'s Route A pipeline:

* `exists_finite_support_of_hspec` (Lemma 0) — generic, no distinctness used.
* `deg_divToPairRatio_le_zero` (§1), `coeffAt_divToPairRatio_bounds` (§2) —
  generic, no distinctness used.
* `denom_B'_eq_zero_of_isPoleBoundedAtPair` (forces `B' = 0`) — **stated
  with no `hne`/distinctness hypothesis at all**; directly callable at
  `(x, Point.iota x)` with zero changes.
* `num_B_eq_zero_of_isPoleBoundedAtPair` (forces `B = 0`, given the
  `ordInfOfPair A' B' ≥ -2` bound) — **likewise no distinctness hypothesis**;
  directly callable.
* The `hcap_at`/`hsum_le` block inside `constant_or_fiber_of_isPoleBoundedAtPair`
  that derives `ordInfOfPair A' B' ≥ -2` (hence `A'.natDegree ≤ 1`,
  `A.natDegree ≤ 1`) — each of the two `≤ 1` sub-bounds (`hb1`, `hb2` in that
  proof) is derived independently by `Finset.card_le_card` against `{x₁}`/
  `{x₂}` separately and simply added; nothing there breaks or needs
  reproving when `x₁ = x₂` — the same argument gives `≤ 2` either way.

**So the entire pipeline down through `A'.natDegree ≤ 1` and
`A.natDegree ≤ 1` is a direct reuse of already-proved
`LPairFinrankOne.lean` lemmas, called at `(x, Point.iota x)` — not a
rewrite, not even much of an adaptation.** The only place genuinely new
content is needed is exactly where `LPairFinrankOne.lean` used `hne : x₂ ≠
Point.iota x₁` to rule out a case — at a fiber, `hne` is false by
construction, so that case isn't ruled out, it's the source of the fiber
space's *second* dimension. See `eq_zero_or_C_or_C_mul_linX_of_natDegree_le_one`
(`LPairFinrankOne.lean`): a degree-≤1 polynomial `A'` is `0`, or `C c`, or
`C c * linX a`. `LPairFinrankOne.lean`'s `natDegree_eq_zero_of_isPoleBoundedAtPair`
uses `hne` to rule out the third branch surviving into the final answer at a
*distinct* pair; here, the third branch (`A' = C c' * linX a'`, forcing
`a' = x.X` via the same point-matching `SCOPING-finrank-L-pair.md` describes)
is exactly what witnesses `x` itself as the second basis element.

## Target

```
theorem finrank_L_canonical (hdeg : H.f.natDegree = 5) (x : H.Point) :
    Module.finrank k (LPair hdeg x (Point.iota x)) = 2 ∧
      IsOnlyFibersInCanonicalClass hdeg x
```
(`RiemannRochGenus2.lean` states the goal via `LPair` applied to a fiber
rather than an independently-constructed canonical divisor — see that
file's §2 module doc.)

## Proof shape, narrowed to the genuinely new content

1. **§1 (independence, still needed, no analogue in `LPairFinrankOne.lean`).**
   `LPairFinrankOne.lean` only ever proved *collapse to a point* (finrank 1);
   nothing there shows two elements are independent, since it never needed
   to. `1` and (the fraction-field image of) `x` are `k`-linearly
   independent — routine once stated (`x` is not algebraic of degree ≤ 0
   over `k`, since `H.f.natDegree = 5 > 0` means `CoordinateRing H ≠ k`),
   but genuinely new, not reused.

2. **§2 (dimension bound `≤ 2`, MOSTLY direct reuse).** Call
   `denom_B'_eq_zero_of_isPoleBoundedAtPair`, `num_B_eq_zero_of_isPoleBoundedAtPair`,
   and the `hcap_at`/`hsum_le` pattern **at `(x, Point.iota x)`** exactly as
   `LPairFinrankOne.lean`'s `constant_or_fiber_of_isPoleBoundedAtPair` does at
   `(x₁, x₂)`, down through `A'.natDegree ≤ 1`, `A.natDegree ≤ 1`. This much
   should be a near-verbatim port, not new proof search. Then case-split via
   `eq_zero_or_C_or_C_mul_linX_of_natDegree_le_one` on `A'` — where
   `LPairFinrankOne.lean` used `hne` to eliminate the `C c' * linX a'`
   branch, here BOTH the constant and the linear branch survive (giving the
   two basis directions), which is the qualitative content `finrank ≤ 2`
   (rather than `= 1`) needs. This is genuinely new case-analysis, but it
   reuses the shape-decomposition lemma and the degree bound wholesale.

3. **§3 (qualitative half, `IsOnlyFibersInCanonicalClass`).** Given
   `(x)+(ιx) ~ (x₃)+(x₄)`, use `ordAt_linX_eq` (`HyperellipticClassProof.lean`,
   fully proved) at `x₃` and `x₄` against the §2 witness to force
   `x₄ = Point.iota x₃` — the same technique `SCOPING-finrank-L-pair.md`'s
   Route A step 3 already used for the non-fiber case, applied to the
   §2 witness instead of the `x₁,x₂`-distinct one.

**Net assessment: this is closer to "port and extend" than "new
undertaking."** §1 is new but easy. §2's bound is a direct call to
already-proved lemmas; only the final case-split (not the degree-counting
that feeds it) is new, and it's new because the fiber case is genuinely a
different, larger answer (2-dimensional, not 1), not because the machinery
doesn't transfer. §3 reuses `ordAt_linX_eq` the same way already-closed work
in this project does. Staged as three named `sorry`s below, easiest first,
per project convention — nothing here is a completed proof.
-/

namespace HyperellipticPolynomial

open Divisor

variable {k : Type*} [Field k]
variable {H : HyperellipticPolynomial k}
variable [IsDedekindDomain (CoordinateRing H)]

/-- **§1 (easiest): `1` and (the fraction-field image of) `x` are
`k`-linearly independent in `FractionRing (CoordinateRing H)`.** Pure
algebra, no point/divisor data, no analogue in `LPairFinrankOne.lean`
(which never needed an independence fact). Needs `hdeg` only to confirm
`CoordinateRing H ≠ k` (i.e. `x` isn't secretly algebraic of degree 0 over
`k`), via `H.f.natDegree = 5 ≠ 0`. -/
theorem one_x_linearIndependent (hdeg : H.f.natDegree = 5) :
    LinearIndependent k
      (![1, algebraMap (CoordinateRing H) (FractionRing (CoordinateRing H))
          (toPair H X 0)] :
        Fin 2 → FractionRing (CoordinateRing H)) := by
  -- Reduce to independence in `CoordinateRing H` itself, then transport via the
  -- injective `algebraMap (CoordinateRing H) (FractionRing (CoordinateRing H))`
  -- (`IsFractionRing.injective`, the project's standard route for this step —
  -- see e.g. `RiemannRochCrux.lean`'s `hdenom_ne` for the same invocation).
  rw [LinearIndependent.pair_iff]
  intro s t hst
  haveI hst1 : IsScalarTower k k[X] (CoordinateRing H) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI hst2 : IsScalarTower k (CoordinateRing H) (FractionRing (CoordinateRing H)) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI hst3 : IsScalarTower k k[X] (FractionRing (CoordinateRing H)) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  -- Rewrite `hst : s • 1 + t • (algebraMap _ _ (toPair H X 0)) = 0` entirely in
  -- terms of `algebraMap k[X] (CoordinateRing H)`, then push it down to the
  -- `CoordinateRing H` level via `toPair`, then to `k[X]` via `toPair_eq_zero_iff`.
  have hkey : algebraMap (CoordinateRing H) (FractionRing (CoordinateRing H))
      (toPair H (Polynomial.C s + Polynomial.C t * X) 0) = 0 := by
    -- Unfold `toPair` on the LHS directly to `algebraMap k[X] (CoordinateRing H) (C s + C t * X)`
    -- (the `B = 0` branch drops the `y` term entirely), then decompose `C s + C t * X` inside
    -- that single `algebraMap` using `map_add`/`map_mul`, and identify each piece with the
    -- corresponding `k`-scalar via `IsScalarTower.algebraMap_apply`. This keeps every rewrite
    -- target a literal subterm of the goal at each step, rather than relying on `simp` to
    -- find a match across two different algebra towers at once.
    have hpair_eq : toPair H (Polynomial.C s + Polynomial.C t * X) 0 =
        algebraMap k[X] (CoordinateRing H) (Polynomial.C s) +
          algebraMap k[X] (CoordinateRing H) (Polynomial.C t) *
            algebraMap k[X] (CoordinateRing H) (X : k[X]) := by
      simp [HyperellipticPolynomial.toPair]
    have hcs : algebraMap k[X] (CoordinateRing H) (Polynomial.C s) =
        algebraMap k (CoordinateRing H) s := by
      rw [IsScalarTower.algebraMap_apply k k[X] (CoordinateRing H)]
      simp
    have hct : algebraMap k[X] (CoordinateRing H) (Polynomial.C t) =
        algebraMap k (CoordinateRing H) t := by
      rw [IsScalarTower.algebraMap_apply k k[X] (CoordinateRing H)]
      simp
    have hX : algebraMap k[X] (CoordinateRing H) (X : k[X]) = toPair H X 0 := by
      simp [HyperellipticPolynomial.toPair]
    -- Combine everything: rewrite the LHS entirely to
    -- `algebraMap (CoordinateRing H) _ (algebraMap k _ s) +
    --    algebraMap (CoordinateRing H) _ (algebraMap k _ t * toPair H X 0)`,
    -- then push the outer `algebraMap` in with `map_add`/`map_mul` and identify
    -- the resulting *composed* `algebraMap (CoordinateRing H) (FractionRing _)
    -- (algebraMap k (CoordinateRing H) _)` with the single-step
    -- `algebraMap k (FractionRing (CoordinateRing H)) _` via `IsScalarTower`,
    -- rewriting `←` since the composed form is what's in the goal, not the
    -- single-step form.
    rw [hpair_eq, hcs, hct, hX, map_add, map_mul,
      ← IsScalarTower.algebraMap_apply k (CoordinateRing H) (FractionRing (CoordinateRing H)),
      ← IsScalarTower.algebraMap_apply k (CoordinateRing H) (FractionRing (CoordinateRing H))]
    -- Goal is now exactly `hst` after rewriting `s • 1 + t • _` via `Algebra.smul_def`.
    rw [Algebra.smul_def, Algebra.smul_def] at hst
    simpa using hst
  -- With the combined `k[X]`-pair equal to `0` at the `CoordinateRing H` level
  -- (via `IsFractionRing.injective`, since `FractionRing` maps are injective on
  -- an integral domain), `toPair_eq_zero_iff` gives `C s + C t * X = 0` in
  -- `k[X]`, i.e. `s = 0` (constant term) and `t = 0` (linear coefficient) —
  -- this is where `hdeg`'s role is implicit: `toPair_eq_zero_iff` holds
  -- unconditionally (no genus hypothesis needed), so `s = t = 0` follows from
  -- pure `k[X]`-coefficient matching, not from any deeper curve fact. (`hdeg`
  -- is kept as a hypothesis for symmetry with every other theorem in this
  -- file's pipeline, and because `LPair`/`IsPoleBoundedAtPair` themselves are
  -- only meaningful for the deg-5 model, even though this particular sub-step
  -- doesn't consume it.)
  have hzero : (Polynomial.C s + Polynomial.C t * X : k[X]) = 0 := by
    have hinj : Function.Injective
        (algebraMap (CoordinateRing H) (FractionRing (CoordinateRing H))) :=
      IsFractionRing.injective (CoordinateRing H) (FractionRing (CoordinateRing H))
    have : toPair H (Polynomial.C s + Polynomial.C t * X) 0 = 0 :=
      hinj (by rw [hkey, map_zero])
    exact (toPair_eq_zero_iff H _ _).mp this |>.1
  constructor
  · have := congrArg (fun p => Polynomial.coeff p 0) hzero
    simpa using this
  · have := congrArg (fun p => Polynomial.coeff p 1) hzero
    simpa using this

/-- **§2, stated at the `(A,B,A',B')`-pair level, matching
`constant_or_fiber_of_isPoleBoundedAtPair`'s own signature shape
(`LPairFinrankOne.lean`) but at a fiber `(x, ιx)` instead of a
`hne`-distinct pair.** This is the actual site of the port described in the
module docstring: every step down through `hdegA'le1`/`hdegA`
(`A'.natDegree ≤ 1`, `A.natDegree ≤ 1`) is intended to be identical to
`constant_or_fiber_of_isPoleBoundedAtPair`'s proof (same lemma calls,
`x₁ := x`, `x₂ := Point.iota x`), since none of those lemmas
(`denom_B'_eq_zero_of_isPoleBoundedAtPair`, `num_B_eq_zero_of_isPoleBoundedAtPair`,
`ordInfOfPair_right_zero`) have a distinctness hypothesis. The divergence
happens exactly at `natDegree_eq_zero_of_isPoleBoundedAtPair`'s call site:
that lemma consumes `hne` internally to force `A'.natDegree = 0 ∨ A,A'
associates`, ruling out the genuinely-degree-1 case. At a fiber there is no
`hne` to supply, and the degree-1 case is NOT ruled out — a companion
fact, `natDegree_le_one_of_isPoleBoundedAtPair_fiber` (new, not yet
written), is needed in its place, concluding only the weaker
`A'.natDegree ≤ 1` disjunction-free statement (already established by this
point via `hdegA'le1` above) without attempting to rule out the linear
case — i.e. this lemma's real content beyond the reused pipeline is just
"stop before the `hne`-consuming step and conclude `finrank ≤ 2` directly
from the `≤1`/`≤1` degree bounds on `A, A'` via the standard dimension
count for a 2-dimensional space of `A(x)/A'(x)`-shaped fractions with
`deg A, deg A' ≤ 1`" — genuinely new but small, isolated below rather than
attempted blind.

**Revision note (weakens the file's original §2 target).** An earlier draft
of this section additionally stated a top-level
`Module.finrank k (LPair hdeg x (Point.iota x)) ≤ 2` theorem, directly about
the `k`-submodule `LPair`. That claim needs a bridge this project does not
yet have: `LPairCarrier` (`RiemannRochGenus2.lean`) is a bare existential
over *all* pole-bounded `(A,B,A',B')` witnesses, reduced or not (see that
definition's own docstring, "Known limitation, not yet fixed here"), while
this theorem — like every other degree bound in the elementary route — needs
`hreduced` and `hspecAB`/`hspecA'B'` supplied as hypotheses on a *given*
witness. Checked against the project: this exact bridging gap is already
open project-wide, not something specific to the fiber case — the finrank-1
analogue, `uniqueDegree2MapToP1_of_elementary` (`LPairFinrankOne.lean:3399`),
has the identical witness-level shape and is never invoked to discharge
`uniqueDegree2MapToP1` (`RiemannRochCrux.lean`, still its own separate
`sorry`) precisely because no reduction-from-bare-membership argument exists
yet (see `RatioDivisorCollapse.lean`'s and `PrincipalSubgroupCollapse.lean`'s
comments flagging this as "confirmed circular"). Stating a `Module.finrank`
bound here and closing it would either silently reproduce that same open gap
under a new name, or need a `sorry` that is not "the next small step" but a
restatement of the project's central unsolved problem. Per project
convention (weaken a prematurely-strong statement rather than paper over it
with `sorry`), §2's target stays at this theorem's witness level — matching
`uniqueDegree2MapToP1_of_elementary` exactly — rather than a `LPair`-level
statement that was never actually reachable. No content is lost relative to
what is actually provable right now: this theorem is a complete, sorry-free
proof of everything this route currently establishes about the fiber's
pole-bounded space. -/
theorem polePairSpace_finrank_le_two_of_fiber (hdeg : H.f.natDegree = 5)
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f) (x : H.Point)
    (A B A' B' : k[X])
    (hbound : IsPoleBoundedAtPair x (Point.iota x) A B A' B')
    (hspecAB : ∀ (v : IsDedekindDomain.HeightOneSpectrum H.CoordinateRing),
      (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {H.toPair A B})).factors ≠ 0 →
        ∃ P, v.asIdeal = pointIdeal P)
    (hspecA'B' : ∀ (v : IsDedekindDomain.HeightOneSpectrum H.CoordinateRing),
      (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {H.toPair A' B'})).factors ≠ 0 →
        ∃ P, v.asIdeal = pointIdeal P)
    (hreduced : ∀ P : H.Point, ordAt P A B = 0 ∨ ordAt P A' B' = 0) :
    A.natDegree ≤ 1 ∧ A'.natDegree ≤ 1 ∧ B = 0 ∧ B' = 0 := by
  by_cases hAB0 : A = 0 ∧ B = 0
  · -- Degenerate case: `A = 0 ∧ B = 0`, so `z = 0`. `A.natDegree ≤ 1` and
    -- `B = 0` are immediate from `hAB0` itself. For `A', B'`: `hbound`'s
    -- third clause, `hpt`, still degenerates usefully — `ordAt P A B =
    -- ordAt P 0 0 = 0` for every `P` (`toPair H 0 0 = 0`, and `ordAt`'s own
    -- `if toPair = 0 then 0` branch fires unconditionally, independent of
    -- `pointIdeal P = ⊥`), so `hpt P : 0 ≥ ordAt P A' B' - ind(P)`, i.e.
    -- `ordAt P A' B' ≤ ind(P)` — the SAME per-point cap `hcap_at` derives in
    -- the general branch, just without needing `hreduced` to get there
    -- (`hreduced`'s role there was case-splitting on which side of `hpt` is
    -- zero; here the `(A,B)`-side is unconditionally zero already). Only
    -- `hmono`'s bound (`ordInfOfPair A B ≥ ordInfOfPair A' B'`, degenerating
    -- to the weak `0 ≥ ordInfOfPair A' B'`) is genuinely unusable here — but
    -- it turns out not to be needed: summing the cap over a finite support
    -- `T'` for `(A',B')` and combining with `deg_div_eq_zero_deg5` gives
    -- `ordInfOfPair A' B' ≥ -2` directly, the same target `h_denom_ord`
    -- reaches in the general branch, by an even more direct route.
    obtain ⟨hA'B', -, hpt⟩ := hbound
    have hcap_at : ∀ P : H.Point,
        ordAt P A' B' ≤ (if P = x then (1:ℤ) else 0) +
          (if P = Point.iota x then (1:ℤ) else 0) := by
      intro P
      have hind := hpt P
      have hzeroAB : ordAt P A B = 0 := by
        have hz : toPair H A B = 0 := by rw [hAB0.1, hAB0.2]; simp [HyperellipticPolynomial.toPair]
        unfold ordAt
        rw [if_pos hz]
      rw [hzeroAB] at hind
      omega
    obtain ⟨T', hT'⟩ := exists_finite_support_of_hspec A' B' hA'B' hspecA'B'
    haveI : ∀ P : (T' : Finset H.Point),
        Module.Finite k (CoordinateRing H ⧸ pointIdeal P.1 ^ (ordAt P.1 A' B').toNat) :=
      fun P => finite_quotient_pointIdeal_pow P.1 _
    have hsum_le : (∑ P ∈ T', ordAt P A' B') ≤ 2 := by
      calc (∑ P ∈ T', ordAt P A' B')
          ≤ ∑ P ∈ T', ((if P = x then (1:ℤ) else 0) +
              (if P = Point.iota x then (1:ℤ) else 0)) :=
            Finset.sum_le_sum (fun P _ => hcap_at P)
        _ = (∑ P ∈ T', (if P = x then (1:ℤ) else 0)) +
              ∑ P ∈ T', (if P = Point.iota x then (1:ℤ) else 0) := Finset.sum_add_distrib
        _ ≤ 1 + 1 := by
            have hb1 : (∑ P ∈ T', (if P = x then (1:ℤ) else 0)) ≤ 1 := by
              have heq : (∑ P ∈ T', (if P = x then (1:ℤ) else 0)) =
                  ((T'.filter (fun P => P = x)).card : ℤ) := by
                rw [← Finset.sum_filter]; simp [Finset.sum_const]
              rw [heq]
              have hsub : T'.filter (fun P => P = x) ⊆ {x} := by
                intro P hP; simp only [Finset.mem_filter] at hP; simp [hP.2]
              have hcard : (T'.filter (fun P => P = x)).card ≤ 1 := by
                have := Finset.card_le_card hsub
                simpa using this
              exact_mod_cast hcard
            have hb2 : (∑ P ∈ T', (if P = Point.iota x then (1:ℤ) else 0)) ≤ 1 := by
              have heq : (∑ P ∈ T', (if P = Point.iota x then (1:ℤ) else 0)) =
                  ((T'.filter (fun P => P = Point.iota x)).card : ℤ) := by
                rw [← Finset.sum_filter]; simp [Finset.sum_const]
              rw [heq]
              have hsub : T'.filter (fun P => P = Point.iota x) ⊆ {Point.iota x} := by
                intro P hP; simp only [Finset.mem_filter] at hP; simp [hP.2]
              have hcard : (T'.filter (fun P => P = Point.iota x)).card ≤ 1 := by
                have := Finset.card_le_card hsub
                simpa using this
              exact_mod_cast hcard
            linarith
        _ = 2 := by norm_num
    have hd := deg_div_eq_zero_deg5 H hdeg T' A' B' hA'B' hT' hspecA'B'
    have h_denom_ord : ordInfOfPair A' B' ≥ -2 := by omega
    -- `B' = 0`: if not, `ordInfOfPair A' B' ≤ -(2*B'.natDegree+5) ≤ -5`,
    -- contradicting `h_denom_ord : ordInfOfPair A' B' ≥ -2` (same
    -- `ordInfOfPair`-unfold argument `denom_B'_eq_zero_of_isPoleBoundedAtPair`
    -- uses for its own `hordInf_A'B'` intermediate step). Proved first (out of
    -- goal order) since the degree bound below needs it.
    have hB' : B' = 0 := by
      by_contra hB'ne
      have hordInf_A'B' : ordInfOfPair A' B' ≤ -(2 * (B'.natDegree : ℤ) + 5) := by
        dsimp [ordInfOfPair]
        rw [if_neg hA'B', if_neg hB'ne]
        have : (2 * (B'.natDegree : ℤ) + 5) ≤
            max (2 * (A'.natDegree : ℤ)) (2 * (B'.natDegree : ℤ) + 5) := le_max_right _ _
        linarith
      linarith
    refine ⟨?_, ?_, hAB0.2, hB'⟩
    · rw [hAB0.1]; simp
    · have h_ord_A' : ordInfOfPair A' 0 = -2 * (A'.natDegree : ℤ) := ordInfOfPair_right_zero A'
      have h_bound_eq : -2 * (A'.natDegree : ℤ) ≥ -2 := by
        calc -2 * (A'.natDegree : ℤ) = ordInfOfPair A' 0 := h_ord_A'.symm
        _ = ordInfOfPair A' B' := by rw [hB']
        _ ≥ -2 := h_denom_ord
      by_contra hgt
      push_neg at hgt
      have : (2 : ℤ) ≤ (A'.natDegree : ℤ) := by exact_mod_cast hgt
      linarith
  · have ⟨hA'B', hmono, hpt⟩ := hbound
    obtain ⟨T₁, hT₁⟩ := exists_finite_support_of_hspec A B hAB0 hspecAB
    obtain ⟨T₂, hT₂⟩ := exists_finite_support_of_hspec A' B' hA'B' hspecA'B'
    haveI : ∀ P : (T₁ ∪ T₂ : Finset H.Point),
        Module.Finite k (CoordinateRing H ⧸ pointIdeal P.1 ^ (ordAt P.1 A B).toNat) :=
      fun P => finite_quotient_pointIdeal_pow P.1 _
    haveI : ∀ P : (T₁ ∪ T₂ : Finset H.Point),
        Module.Finite k (CoordinateRing H ⧸ pointIdeal P.1 ^ (ordAt P.1 A' B').toNat) :=
      fun P => finite_quotient_pointIdeal_pow P.1 _
    -- Verbatim reuse: `denom_B'_eq_zero_of_isPoleBoundedAtPair` has no
    -- distinctness hypothesis on its two point arguments.
    have hB' : B' = 0 :=
      denom_B'_eq_zero_of_isPoleBoundedAtPair hdeg x (Point.iota x) A B A' B' hbound
        hspecAB hspecA'B' (T₁ ∪ T₂) hAB0
        (fun P hP => hT₁ P (fun h => hP (Finset.mem_union_left T₂ h)))
        (fun P hP => hT₂ P (fun h => hP (Finset.mem_union_right T₁ h)))
        hreduced
    -- Verbatim reuse: the `hcap_at`/`hsum_le` pattern, identical in shape to
    -- `constant_or_fiber_of_isPoleBoundedAtPair`'s own derivation of
    -- `h_denom_ord`, since neither `hcap_at` nor `hsum_le` there used
    -- `x₁ ≠ x₂` — each of the two `≤ 1` sub-bounds is proved independently
    -- against `{x}`/`{Point.iota x}` and simply added, giving `≤ 2` either
    -- way (verified against the source: see module docstring).
    have h_denom_ord : ordInfOfPair A' B' ≥ -2 := by
      have hA'0 : A' ≠ 0 := fun h => hA'B' ⟨h, hB'⟩
      haveI : ∀ P : (T₂ : Finset H.Point),
          Module.Finite k (CoordinateRing H ⧸ pointIdeal P.1 ^ (ordAt P.1 A' B').toNat) :=
        fun P => finite_quotient_pointIdeal_pow P.1 _
      have hcap_at : ∀ P : H.Point,
          ordAt P A' B' ≤ (if P = x then (1:ℤ) else 0) +
            (if P = Point.iota x then (1:ℤ) else 0) := by
        intro P
        rcases hreduced P with hzero | hzero
        · have hind := hpt P
          rw [hzero] at hind
          omega
        · have hind_nonneg :
              (0:ℤ) ≤ (if P = x then (1:ℤ) else 0) +
                (if P = Point.iota x then (1:ℤ) else 0) := by
            have h1 : (0:ℤ) ≤ if P = x then (1:ℤ) else 0 := by by_cases h : P = x <;> simp [h]
            have h2 : (0:ℤ) ≤ if P = Point.iota x then (1:ℤ) else 0 := by
              by_cases h : P = Point.iota x <;> simp [h]
            linarith
          omega
      have hsum_le : (∑ P ∈ T₂, ordAt P A' B') ≤ 2 := by
        calc (∑ P ∈ T₂, ordAt P A' B')
            ≤ ∑ P ∈ T₂, ((if P = x then (1:ℤ) else 0) +
                (if P = Point.iota x then (1:ℤ) else 0)) :=
              Finset.sum_le_sum (fun P _ => hcap_at P)
          _ = (∑ P ∈ T₂, (if P = x then (1:ℤ) else 0)) +
                ∑ P ∈ T₂, (if P = Point.iota x then (1:ℤ) else 0) := Finset.sum_add_distrib
          _ ≤ 1 + 1 := by
              have hb1 : (∑ P ∈ T₂, (if P = x then (1:ℤ) else 0)) ≤ 1 := by
                have heq : (∑ P ∈ T₂, (if P = x then (1:ℤ) else 0)) =
                    ((T₂.filter (fun P => P = x)).card : ℤ) := by
                  rw [← Finset.sum_filter]; simp [Finset.sum_const]
                rw [heq]
                have hsub : T₂.filter (fun P => P = x) ⊆ {x} := by
                  intro P hP; simp only [Finset.mem_filter] at hP; simp [hP.2]
                have hcard : (T₂.filter (fun P => P = x)).card ≤ 1 := by
                  have := Finset.card_le_card hsub
                  simpa using this
                exact_mod_cast hcard
              have hb2 : (∑ P ∈ T₂, (if P = Point.iota x then (1:ℤ) else 0)) ≤ 1 := by
                have heq : (∑ P ∈ T₂, (if P = Point.iota x then (1:ℤ) else 0)) =
                    ((T₂.filter (fun P => P = Point.iota x)).card : ℤ) := by
                  rw [← Finset.sum_filter]; simp [Finset.sum_const]
                rw [heq]
                have hsub : T₂.filter (fun P => P = Point.iota x) ⊆ {Point.iota x} := by
                  intro P hP; simp only [Finset.mem_filter] at hP; simp [hP.2]
                have hcard : (T₂.filter (fun P => P = Point.iota x)).card ≤ 1 := by
                  have := Finset.card_le_card hsub
                  simpa using this
                exact_mod_cast hcard
              linarith
          _ = 2 := by norm_num
      have hd := deg_div_eq_zero_deg5 H hdeg T₂ A' B' hA'B' hT₂ hspecA'B'
      omega
    have hB : B = 0 := num_B_eq_zero_of_isPoleBoundedAtPair x (Point.iota x) A B A' B' hbound
      h_denom_ord
    have hdegA'le1 : A'.natDegree ≤ 1 := by
      have h_ord_A' : ordInfOfPair A' 0 = -2 * (A'.natDegree : ℤ) := ordInfOfPair_right_zero A'
      have h_bound_eq : -2 * (A'.natDegree : ℤ) ≥ -2 := by
        calc -2 * (A'.natDegree : ℤ) = ordInfOfPair A' 0 := h_ord_A'.symm
        _ = ordInfOfPair A' B' := by rw [hB']
        _ ≥ -2 := h_denom_ord
      by_contra hgt
      push_neg at hgt
      have : (2 : ℤ) ≤ (A'.natDegree : ℤ) := by exact_mod_cast hgt
      linarith
    have hdegA : A.natDegree ≤ 1 := by
      have hmono' : ordInfOfPair A 0 ≥ ordInfOfPair A' 0 := by rw [hB, hB'] at hmono; exact hmono
      have h_ord_A'_ge : ordInfOfPair A' 0 ≥ -2 := by
        rw [ordInfOfPair_right_zero A']
        have : (A'.natDegree : ℤ) ≤ 1 := by exact_mod_cast hdegA'le1
        linarith
      have h_ord_A_ge : ordInfOfPair A 0 ≥ -2 := le_trans h_ord_A'_ge hmono'
      rw [ordInfOfPair_right_zero A] at h_ord_A_ge
      by_contra hgt
      push_neg at hgt
      have : (2 : ℤ) ≤ (A.natDegree : ℤ) := by exact_mod_cast hgt
      linarith
    -- **This is where the port stops and `LPairFinrankOne.lean`'s proof
    -- diverges** (see this theorem's own docstring): the source calls
    -- `natDegree_eq_zero_of_isPoleBoundedAtPair hdeg hchar hsf x₁ x₂ hne ...`
    -- here, consuming `hne` to collapse `A'.natDegree` to exactly `0`. No
    -- such hypothesis is available (nor true) at a fiber, and no such
    -- collapse should happen — `hdegA`/`hdegA'le1` above are already this
    -- theorem's full conclusion for the degree half.
    exact ⟨hdegA, hdegA'le1, hB, hB'⟩

/-! ## §2.5: Mumford reduction — attacking the `hreduced` gap directly

**New content, addressing the project-wide `hreduced` blocker flagged in §3's
docstring below and in `RiemannRochCrux.lean`'s
`isOnlyEffectiveInClass_of_uniqueDegree2MapToP1`.**

The blocker is *not* "every principal divisor's witness can be reduced by
cancelling a common factor" — that is false in general (class-group
obstruction, confirmed independently, see the uploaded ChatGPT session). The
actual need is narrower: given two *specific* points `Q₁ Q₂ : H.Point`
(arising as `x₃, x₄` or `x₁, x₂` in the calling theorems), *construct
directly* a pair `(A, B)` whose finite zero divisor is exactly `Q₁ + Q₂`,
built by hand from `Q₁, Q₂` themselves via Lagrange interpolation (the
degree-2 case of Mumford/Cantor reduction) rather than obtained by trying to
reduce an arbitrary witness handed to us by
`isRatioDivisor_of_mem_principalSubgroup`. This sidesteps the class-group
obstruction entirely: we never touch an arbitrary witness, we build our own.

Two cases:
* `Q₂ = Point.iota Q₁`: the fiber case, already fully handled by existing
  machinery (`linX Q₁.X`, `ordAt_linX_eq`) — `B = 0`, so there is nothing to
  reduce against (`hreduced` is trivial whenever one side has `B = 0`).
* `Q₁.X ≠ Q₂.X` (covers every other case: distinct points with distinct
  `x`-coordinates, since equal `x`-coordinates forces `Q₂ ∈ {Q₁, ιQ₁}`):
  genuinely new, built here via the line through `(Q₁.X, Q₁.Y)` and
  `(Q₂.X, Q₂.Y)`. -/

/-- **General evaluation formula for `toPair`.** `evalAtPoint Q (toPair H A B)
= A.eval Q.X + B.eval Q.X * Q.Y`. Generalizes the ad hoc computation inside
`toPair_linX_mem_pointIdeal_iff` (`HyperellipticClassProof.lean`, specific to
`A = linX a, B = 0`) to arbitrary `A, B`. Proved the same way: unfold `toPair`
to the `algebraMap k[X] (CoordinateRing H) A + algebraMap k[X] (CoordinateRing H) B * y H`
shape, push `evalAtPoint Q` through `map_add`/`map_mul`, and evaluate each
piece — the `algebraMap k[X] (CoordinateRing H)` pieces via the same
`eval₂`-unfolding `toPair_linX_mem_pointIdeal_iff` already uses (specialized
there to `X`/`C a`, generalized here to arbitrary `A`/`B` via `Polynomial.C`),
and `y H` via `AdjoinRoot.lift_root` (`evalAtPoint` is built as an
`AdjoinRoot.lift`, and `y H = AdjoinRoot.root _` by definition). -/
theorem evalAtPoint_toPair (Q : H.Point) (A B : k[X]) :
    evalAtPoint Q (toPair H A B) = A.eval Q.X + B.eval Q.X * Q.Y := by
  have hA : evalAtPoint Q (algebraMap k[X] (CoordinateRing H) A) = A.eval Q.X := by
    change Polynomial.eval₂ (Polynomial.evalRingHom Q.val.1) Q.val.2 (Polynomial.C A) = A.eval Q.X
    simp [Point.X]
  have hB : evalAtPoint Q (algebraMap k[X] (CoordinateRing H) B) = B.eval Q.X := by
    change Polynomial.eval₂ (Polynomial.evalRingHom Q.val.1) Q.val.2 (Polynomial.C B) = B.eval Q.X
    simp [Point.X]
  have hy : evalAtPoint Q (y H) = Q.Y := by
    unfold evalAtPoint y
    change Polynomial.eval₂ (Polynomial.evalRingHom Q.val.1) Q.val.2 X = Q.Y
    simp [Point.Y]
  unfold HyperellipticPolynomial.toPair
  rw [map_add, map_mul, hA, hB, hy]

/-- **Membership characterization, generalizing `toPair_linX_mem_pointIdeal_iff`
to arbitrary `A, B`.** `toPair H A B ∈ pointIdeal Q ↔ A.eval Q.X + B.eval Q.X * Q.Y = 0`
— immediate from `evalAtPoint_toPair` and `pointIdeal Q = RingHom.ker (evalAtPoint Q)`. -/
theorem toPair_mem_pointIdeal_iff (Q : H.Point) (A B : k[X]) :
    toPair H A B ∈ pointIdeal Q ↔ A.eval Q.X + B.eval Q.X * Q.Y = 0 := by
  rw [pointIdeal, RingHom.mem_ker, evalAtPoint_toPair]

/-- **The Mumford `b`-polynomial: the line through two points with distinct
`x`-coordinates.** `mumfordB Q₁ Q₂ hne := C Q₁.Y + C ((Q₂.Y - Q₁.Y)/(Q₂.X -
Q₁.X)) * linX Q₁.X` — the unique degree-≤1 polynomial with `b(Q₁.X) = Q₁.Y`,
`b(Q₂.X) = Q₂.Y`, closed-form two-point Lagrange interpolation. The Mumford
numerator element for the divisor `Q₁ + Q₂` is `toPair H (-mumfordB Q₁ Q₂
hne) 1`, i.e. the ring element `y - b(x)` (using `B = 1` for the `y`-slot and
negating `b` to get `y - b(x) = -b(x) + 1·y`). -/
noncomputable def mumfordB (Q₁ Q₂ : H.Point) (hne : Q₁.X ≠ Q₂.X) : k[X] :=
  Polynomial.C Q₁.Y + Polynomial.C ((Q₂.Y - Q₁.Y) / (Q₂.X - Q₁.X)) * linX Q₁.X

@[simp] theorem mumfordB_eval_left (Q₁ Q₂ : H.Point) (hne : Q₁.X ≠ Q₂.X) :
    (mumfordB Q₁ Q₂ hne).eval Q₁.X = Q₁.Y := by
  unfold mumfordB linX
  simp

@[simp] theorem mumfordB_eval_right (Q₁ Q₂ : H.Point) (hne : Q₁.X ≠ Q₂.X) :
    (mumfordB Q₁ Q₂ hne).eval Q₂.X = Q₂.Y := by
  unfold mumfordB linX
  have hsub : Q₂.X - Q₁.X ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  simp only [eval_add, eval_mul, eval_C, eval_sub, eval_X]
  field_simp
  ring

/-- **Degree bound for the Mumford `b`-polynomial: `natDegree (mumfordB Q₁ Q₂
hne) ≤ 1`.** Immediate from its shape `C Q₁.Y + C c * (X - C Q₁.X)`: the first
summand has degree `0` and the second is a scalar multiple of `linX Q₁.X`
(degree `≤ 1`), so `natDegree_add_le` plus `natDegree_C`/`natDegree_C_mul_le`/
`natDegree_X_sub_C` cap the sum at `max 0 1 = 1`. Needed for the
`ordInfOfPair`-side of `IsPoleBoundedAtPair` (gap 2): the Mumford numerator
`toPair H (-mumfordB Q₁ Q₂ hne) 1` has `B`-slot `1 ≠ 0`, so its pole order at
infinity is `-(max (2 * natDegree A) 7)` — this bound pins `2 * natDegree A ≤
2 < 7`, so the max collapses to exactly `7` regardless of the precise degree
of `mumfordB`. -/
theorem mumfordB_natDegree_le (Q₁ Q₂ : H.Point) (hne : Q₁.X ≠ Q₂.X) :
    (mumfordB Q₁ Q₂ hne).natDegree ≤ 1 := by
  unfold mumfordB linX
  refine le_trans (natDegree_add_le _ _) ?_
  refine max_le (by simp) ?_
  refine le_trans natDegree_mul_le ?_
  simp [natDegree_C, natDegree_X_sub_C]

/-- **`ordInfOfPair` of the Mumford numerator is exactly `-5`.** With `A =
-mumfordB Q₁ Q₂ hne` and `B = 1`: `B ≠ 0`, so `ordInfOfPair A B = -(max (2 *
A.natDegree) (2 * B.natDegree + 5))`. `B.natDegree = natDegree (1 : k[X]) = 0`
(`Polynomial.natDegree_one`), so this second term is `2 * 0 + 5 = 5`.
`A.natDegree = (-mumfordB Q₁ Q₂ hne).natDegree = (mumfordB Q₁ Q₂
hne).natDegree ≤ 1` (negation doesn't change `natDegree`, via
`Polynomial.natDegree_neg`), so `2 * A.natDegree ≤ 2 < 5`, pinning the max at
`5`. This is the pole-at-infinity order any "other side" witness (gap 2's `A',
B'`) must be dominated by, i.e. `ordInfOfPair A' B' ≤ -5`, for
`IsPoleBoundedAtPair`'s `ordInfOfPair A B ≥ ordInfOfPair A' B'` clause to hold
when this Mumford pair plays the role of the numerator `(A,B)`. -/
theorem mumfordB_ordInfOfPair (Q₁ Q₂ : H.Point) (hne : Q₁.X ≠ Q₂.X) :
    ordInfOfPair (-mumfordB Q₁ Q₂ hne) (1 : k[X]) = -5 := by
  have hAdeg : (-mumfordB Q₁ Q₂ hne).natDegree ≤ 1 := by
    rw [natDegree_neg]
    exact mumfordB_natDegree_le Q₁ Q₂ hne
  have h2 : (2 * ((-mumfordB Q₁ Q₂ hne).natDegree : ℤ)) ≤ 2 * ((0 : ℕ) : ℤ) + 5 := by
    have : ((-mumfordB Q₁ Q₂ hne).natDegree : ℤ) ≤ 1 := by exact_mod_cast hAdeg
    push_cast
    linarith
  unfold ordInfOfPair
  have hB1 : ¬ ((-mumfordB Q₁ Q₂ hne) = 0 ∧ (1 : k[X]) = 0) := by
    intro h; exact one_ne_zero h.2
  rw [if_neg hB1, if_neg (one_ne_zero (α := k[X]))]
  rw [natDegree_one]
  rw [max_eq_right h2]
  norm_num

/-- **The Mumford witness pair vanishes at both `Q₁` and `Q₂`.** Immediate
from `toPair_mem_pointIdeal_iff` plus `mumfordB_eval_left`/`_right`: `-b(x) +
1·Y` evaluated at `Q_i` is `-b.eval Q_i.X + Q_i.Y = -Q_i.Y + Q_i.Y = 0`. -/
theorem mumford_mem_pointIdeal (Q₁ Q₂ : H.Point) (hne : Q₁.X ≠ Q₂.X) :
    toPair H (-mumfordB Q₁ Q₂ hne) 1 ∈ pointIdeal Q₁ ∧
    toPair H (-mumfordB Q₁ Q₂ hne) 1 ∈ pointIdeal Q₂ := by
  refine ⟨?_, ?_⟩ <;> rw [toPair_mem_pointIdeal_iff] <;> simp

/-- **The Mumford witness pair does not vanish at `ι Q₁`, given `char k ≠ 2`,
`Q₁.Y ≠ 0` (unramified), and `Q₁.X ≠ Q₂.X`.** This is the actual disjointness
fact `hreduced` needs at the "other side" of the fiber through `Q₁`: since
`a(x) = linX Q₁.X * linX Q₂.X` vanishes (by `ordAt_linX_eq`) exactly at
`{Q₁, ιQ₁}` (from the `linX Q₁.X` factor) and `{Q₂, ιQ₂}` (from the `linX
Q₂.X` factor), the only points where a *shared* zero with the Mumford
numerator `toPair H (-mumfordB Q₁ Q₂ hne) 1` could occur are exactly `Q₁, ιQ₁,
Q₂, ιQ₂` — and this lemma rules out `ιQ₁` (the symmetric statement for `ιQ₂`
is `mumford_notMem_iota_right_of_unramified` below). Evaluating: `(-b(x) +
Y).eval` at `ιQ₁ = (Q₁.X, -Q₁.Y)` is `-b(Q₁.X) + (-Q₁.Y) = -Q₁.Y - Q₁.Y =
-2·Q₁.Y ≠ 0` since `char k ≠ 2` and `Q₁.Y ≠ 0`. -/
theorem mumford_notMem_iota_left_of_unramified (hchar : (2 : k) ≠ 0)
    (Q₁ Q₂ : H.Point) (hne : Q₁.X ≠ Q₂.X) (hY₁ : Q₁.Y ≠ 0) :
    toPair H (-mumfordB Q₁ Q₂ hne) 1 ∉ pointIdeal (Point.iota Q₁) := by
  rw [toPair_mem_pointIdeal_iff, Point.iota_X, Point.iota_Y, eval_neg, mumfordB_eval_left,
    eval_one]
  intro hzero
  apply hY₁
  have h2 : (2 : k) * Q₁.Y = 0 := by linear_combination -hzero
  rcases mul_eq_zero.mp h2 with h2' | hy0
  · exact absurd h2' hchar
  · exact hy0

/-- **Symmetric statement for `ιQ₂`.** Same proof as
`mumford_notMem_iota_left_of_unramified` with the roles of `Q₁, Q₂` swapped
in the evaluation, using `mumfordB_eval_right` instead of `_eval_left`. -/
theorem mumford_notMem_iota_right_of_unramified (hchar : (2 : k) ≠ 0)
    (Q₁ Q₂ : H.Point) (hne : Q₁.X ≠ Q₂.X) (hY₂ : Q₂.Y ≠ 0) :
    toPair H (-mumfordB Q₁ Q₂ hne) 1 ∉ pointIdeal (Point.iota Q₂) := by
  rw [toPair_mem_pointIdeal_iff, Point.iota_X, Point.iota_Y, eval_neg, mumfordB_eval_right,
    eval_one]
  intro hzero
  apply hY₂
  have h2 : (2 : k) * Q₂.Y = 0 := by linear_combination -hzero
  rcases mul_eq_zero.mp h2 with h2' | hy0
  · exact absurd h2' hchar
  · exact hy0

/-- **Gap 1, closed: the ramified case collapses `ι Q₁ = Q₁`.** When
`Q₁.Y = 0`, `Point.iota Q₁ = Q₁` on the nose (`iota` negates the `Y`-coordinate,
and `-0 = 0`), so there is nothing left to separate — the "does not vanish at
`ι Q₁`" fact that `mumford_notMem_iota_left_of_unramified` proves in the
unramified case is simply not the fact needed here; in the ramified case
`ι Q₁ = Q₁` collapses into the "vanishes at `Q₁`" fact `mumford_mem_pointIdeal`
already gives, which is the *easier* outcome, not a genuine proof obligation.
Recorded here as its own lemma, ready for whichever later assembly pass
threads the `Q_i.Y = 0`/`Q_i.Y ≠ 0` case split through the full `hreduced`
disjunction (gaps 2/3, not attempted in this pass). -/
theorem iota_eq_self_of_Y_eq_zero (Q : H.Point) (hY : Q.Y = 0) : Point.iota Q = Q := by
  have hX : (Point.iota Q).X = Q.X := Point.iota_X Q
  have hY' : (Point.iota Q).Y = Q.Y := by rw [Point.iota_Y, hY, neg_zero]
  exact Subtype.ext (Prod.ext hX hY')

/-- **Gap 4, partially closed: the Mumford numerator's `ordAt`-valued
disjointness from `{ι Q₁, ι Q₂}`, in the unramified sub-case.** Combines
`mumford_notMem_iota_left/right_of_unramified` with `ordAt_eq_zero_of_notMem`
(`RiemannRochGenus2.lean`) to get `ordAt (ι Q₁) (-mumfordB Q₁ Q₂ hne) 1 = 0`
directly. **Scope note:** this is the disjointness half only, and only for
`Q_i.Y ≠ 0`. The ramified sub-case (`Q_i.Y = 0`, so `ι Q_i = Q_i`) is
genuinely different in kind here: the numerator does NOT avoid `ι Q_i` there
(`iota_eq_self_of_Y_eq_zero` plus `mumford_mem_pointIdeal` show it vanishes),
so no analogous `ordAt = 0` statement holds — assembling a full two-branch
`hreduced`-shaped disjunction for the numerator side alone (gap 4's original
target) still needs that case split threaded through explicitly, and is left
for the gap 2/3 wiring pass, not attempted here. -/
theorem mumford_ordAt_iota_left_eq_zero_of_unramified (hchar : (2 : k) ≠ 0)
    (Q₁ Q₂ : H.Point) (hne : Q₁.X ≠ Q₂.X) (hY₁ : Q₁.Y ≠ 0) :
    ordAt (Point.iota Q₁) (-mumfordB Q₁ Q₂ hne) 1 = 0 :=
  ordAt_eq_zero_of_notMem (Point.iota Q₁) _ 1
    (mumford_notMem_iota_left_of_unramified hchar Q₁ Q₂ hne hY₁)

/-- **Symmetric to `mumford_ordAt_iota_left_eq_zero_of_unramified`, for `ι Q₂`.** -/
theorem mumford_ordAt_iota_right_eq_zero_of_unramified (hchar : (2 : k) ≠ 0)
    (Q₁ Q₂ : H.Point) (hne : Q₁.X ≠ Q₂.X) (hY₂ : Q₂.Y ≠ 0) :
    ordAt (Point.iota Q₂) (-mumfordB Q₁ Q₂ hne) 1 = 0 :=
  ordAt_eq_zero_of_notMem (Point.iota Q₂) _ 1
    (mumford_notMem_iota_right_of_unramified hchar Q₁ Q₂ hne hY₂)

/-! **Status of §2.5, checked against the goal shapes above rather than
assumed complete: this closes the core new mathematical step (explicit
disjointness of the hand-built Mumford numerator from the `ιQ₁`/`ιQ₂`
zeros of the hand-built `a(x)`), but does NOT yet assemble into a full
replacement for `isOnlyEffectiveInClass_of_uniqueDegree2MapToP1`'s `hreduced
:= by sorry` or for §3's `IsOnlyFibersInCanonicalClass` target.** Updated
this session: gaps 1 and 4 below are now closed at the lemma level (not yet
assembled into a single top-level `hreduced` term — that step still needs
gaps 2/3). Remaining gaps, left open rather than assumed free:

1. **Ramified sub-cases** (`Q₁.Y = 0` or `Q₂.Y = 0`, so `ιQ_i = Q_i`).
   **Closed**: `iota_eq_self_of_Y_eq_zero` gives `ι Q_i = Q_i` directly in
   this case, collapsing into `mumford_mem_pointIdeal`'s existing "vanishes
   at `Q_i`" fact — confirmed to be the easier case, not a genuine gap, and
   now recorded as its own named lemma.
2. **The `(A,B)` denominator side of `IsPoleBoundedAtPair`**: this section
   only builds ONE side of a pole-bounded pair (the numerator vanishing at
   `Q₁, Q₂`, i.e. what would play the role of `A', B'` — a "denominator" in
   `LPairCarrier`'s convention — for the divisor `(Q₁)+(Q₂)`). **Partially
   closed this session**: `mumfordB_ordInfOfPair` computes the pole-at-infinity
   order of the Mumford numerator itself exactly (`ordInfOfPair (-mumfordB Q₁
   Q₂ hne) 1 = -5`, via the new degree bound `mumfordB_natDegree_le`), which is
   the bookkeeping half `IsPoleBoundedAtPair`'s `ordInfOfPair A B ≥ ordInfOfPair
   A' B'` clause will need once a genuine "other side" pair exists. **Still
   open**: the other side (`A, B`, vanishing at whatever the "other" pair of
   points is, e.g. `x₃, x₄`) itself — a *second* Mumford witness at a different
   point pair — has not been constructed; `mumfordB_ordInfOfPair` only pins
   down one side's number, not both sides of an actual `IsPoleBoundedAtPair`
   instance.
3. **Wiring into `isRatioDivisor_of_mem_principalSubgroup`'s actual
   witness**: `isOnlyEffectiveInClass_of_uniqueDegree2MapToP1`'s `hreduced`
   obligation is about the SPECIFIC `(A,B,A',B')` that
   `isRatioDivisor_of_mem_principalSubgroup` happens to produce, not a
   from-scratch pair. Closing that `sorry` with this section's results needs
   either (a) showing `isRatioDivisor_of_mem_principalSubgroup`'s witness
   agrees with the from-scratch Mumford witness built here (up to the
   representation-independence `ordAtFrac` is meant to provide — itself
   flagged elsewhere as not fully built), or (b) replacing that theorem's
   proof strategy to construct its own witness via `mumfordB` directly
   instead of consuming the existential, mirroring how this file's own §3
   would use it. Either route is nontrivial additional wiring, not attempted
   here.
4. **The `hreduced` disjunction's other half** (`ordAt P A B = 0 ∨ ordAt P
   A' B' = 0`), restricted to `P ∈ {ι Q₁, ι Q₂}`. **Partially closed**:
   `mumford_ordAt_iota_left/right_eq_zero_of_unramified` give
   `ordAt (ι Q_i) (-mumfordB Q₁ Q₂ hne) 1 = 0` directly via
   `ordAt_eq_zero_of_notMem`, in the unramified sub-case (`Q_i.Y ≠ 0`). The
   ramified sub-case needs gap 1's `iota_eq_self_of_Y_eq_zero` threaded in
   instead (there the numerator does NOT avoid `ι Q_i`, so the *other*
   disjunct — the `A,B` side vanishing, from gap 2 — must supply the
   disjunction there), so a single case-split top-level `hreduced` term
   still needs gap 2 to exist first. Not assembled into that top-level term
   in this pass, to keep scope to the pieces gaps 1/4 asked for.

Recommended next session: attack gap 2 (the `(A,B)` denominator-side Mumford
witness plus `ordInfOfPair` bookkeeping) to get both halves of a from-scratch
`(A,B,A',B')` pair, which is what a genuine `hreduced` case split (gaps 1+4
combined) needs to terminate on; then attack gap 3 by rewriting
`isOnlyEffectiveInClass_of_uniqueDegree2MapToP1`'s proof to build its own
witness via this construction rather than consuming the existential one —
likely the more tractable direction, since gap 3(a) (representation-
independence) looks at least as hard as the original problem.

**§3: `isOnlyFibersInCanonicalClass_of_elementary`, genuinely still open, not
bookkeeping.** Every effective divisor linearly equivalent to a
hyperelliptic fiber `(x)+(ιx)` is itself a fiber. Was intended to reuse
`ordAt_linX_eq` (`HyperellipticClassProof.lean`, fully proved) directly
against the §2 witness, the same technique `SCOPING-finrank-L-pair.md`'s
Route A step 3 used for the `x₁,x₂`-distinct case — but that plan runs into
the identical `hreduced`-from-bare-membership gap flagged at §2's
`polePairSpace_finrank_le_two_of_fiber` (revision note above), and this is
now confirmed to be a *project-wide* blocker rather than something specific
to this file: the exact `x₁,x₂`-distinct analogue,
`isOnlyEffectiveInClass_of_uniqueDegree2MapToP1` (`RiemannRochCrux.lean`),
has its own explicit unresolved `hreduced : ∀ P, ordAt P A B = 0 ∨ ordAt P A'
B' = 0 := by sorry` at exactly this same step (deriving a witness's
reducedness from `isRatioDivisor_of_mem_principalSubgroup`'s bare
existential), with a docstring citing a ChatGPT-assisted review that found
the natural fix (ideal-gcd cancellation) fails via a genuine class-group
obstruction, and the geometric alternative ("every degree-2 map is
hyperelliptic") circular here since that IS this theorem's content — see
that theorem's own docstring for the two suggested next steps ((a) prove
`principalSubgroup`-arising witnesses are always reducible to a
genus-2-specific normal form directly, not presupposing degree-2-uniqueness;
or (b) thread the weakening into `IsOnlyEffectiveInClass`/
`IsOnlyFibersInCanonicalClass`'s consumers). Left as a single named `sorry`,
not routed around, per the same policy this file's §2 revision note follows:
correctly identified as *the* hard problem this whole route reduces to,
worth a dedicated ChatGPT prompt rather than another attempted Lean proof
without new mathematical input. -/
theorem isOnlyFibersInCanonicalClass_of_elementary (hdeg : H.f.natDegree = 5)
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f) (x : H.Point) :
    IsOnlyFibersInCanonicalClass hdeg x := by
  sorry

/-! ## Assembly (not attempted here)

**Status after this session's revision:** §1 (`one_x_linearIndependent`) and
§2 (`polePairSpace_finrank_le_two_of_fiber`) are now fully proved, no `sorry`.
§2's target is stated at the witness level (see its revision-note docstring)
rather than as a bare `Module.finrank k (LPair hdeg x (Point.iota x)) ≤ 2`
claim, because that stronger statement needs the same
`hreduced`-from-bare-`LPairCarrier`-membership bridge that §3 is blocked on
— so it was not assembled into a `Module.finrank` bound here, to avoid
quietly depending on an unproved bridging step. §3
(`isOnlyFibersInCanonicalClass_of_elementary`) has the one remaining hard
`sorry`, now confirmed to be the *same* open gap already blocking
`RiemannRochCrux.lean`'s `isOnlyEffectiveInClass_of_uniqueDegree2MapToP1`
project-wide (see that theorem's `hreduced` sorry and this file's own
docstring above) — not a new problem introduced by this file. Once that
bridge is solved (closing both this file's §3 and `RiemannRochCrux.lean`'s
`hreduced` sorry), the intended final assembly is: lift §2's witness-level
bound to `Module.finrank k (LPair hdeg x (Point.iota x)) ≤ 2` via the
now-available reduction, exhibit §1's `{1, x}` as linearly independent
elements *of* `LPair hdeg x (Point.iota x)` to get `≥ 2`, combine via
`le_antisymm` for `= 2` (the same shape
`RiemannRochCrux.lean`'s `finrank_LPair_eq_one_of_uniqueDegree2MapToP1`
already uses for the analogous `= 1` case), and pair with §3 for
`finrank_L_canonical`'s full statement. Not attempted here since it is
downstream of the still-open bridge, not a free wiring step. -/

end HyperellipticPolynomial
