import Mathlib
import Genus2Lean.ZeroD.DataDerivationTotalDegree
import Genus2Lean.ZeroD.DecoupledSystemRegular

/-!
# `CrossNondegenerate`'s resultant: a `totalDegree` bound, conditional on a base-case hypothesis

New this pass. This is roadmap step 5 of `ROADMAP-crossnondegenerate-degree-
bound.md`: derive a `totalDegree` bound on each of `CrossNondegenerate`'s four
resultants (`d₁*c₂ - d₂*c₁`, one per `hu0/hu1/hv0/hv1`), as the direct corollary
`DataDerivationTotalDegree.lean`'s own closing note flagged as "one more
application away" once `towerToRdec_coeff_totalDegree_le` is in scope alongside
`theData`/`coeffsToNumDen`'s actual shape (which lives in
`DecoupledSystemRegular.lean`, not `TheDataDerivation`) -- hence a new file
rather than adding to either: `DecoupledSystemRegular.lean` is already 3000+
lines (over this project's 1500-line-per-file guideline) and
`DataDerivationTotalDegree.lean` has no access to `theData`/`CrossNondegenerate`
without importing `DecoupledSystemRegular` in the wrong direction.

**What this file does NOT close, honestly stated up front**: per
`ROADMAP-crossnondegenerate-degree-bound.md`'s own "still fully unresolved"
note, no concrete `totalDegree` bound `D` on `uRS.coeff i`/`vRS.coeff i`
themselves has been established yet -- that gap traces through
`curBeforeMonic`'s three nested `/ₘ` (`Polynomial.divByMonic`) steps, which
Mathlib has no general `totalDegree`-transfer lemma for (see that roadmap's
"one genuine wrinkle" vs. the *harder*, separately-flagged `/ₘ` wrinkle). So
the theorem below is stated **conditional on** a base-case bound `D` on
`uRS.coeff i`/`vRS.coeff i` (for both samples, both sides) rather than
unconditionally -- exactly the honest-hypothesis-over-sorry practice this
project follows elsewhere (`Nondegenerate`, `CrossNondegenerate` itself).
Once the `/ₘ`-chain gap above is separately closed, `D` becomes a concrete
number and the hypothesis can be dropped in favor of a fully unconditional
bound; nothing about this theorem's proof needs to change when that happens,
since it never unfolds `uRS`/`vRS`'s own construction, only takes their
coefficient bounds as given.

**Not yet REPL-confirmed** (this pass wrote the statement and proof term but
had no build environment available) -- send to Claire's REPL before treating
this as load-bearing. The most likely failure points, flagged rather than
hidden: (1) exact argument order / implicit-vs-explicit status of
`towerToRdec_coeff_totalDegree_le`'s hypothesis bundle `h`, since it is a
4-way `∧` that must be assembled from four separate `towerToRdecK1`-level
facts; (2) whether `aSideGens`/`bSideGens` need to be unfolded before
`coeffsToNumDen`'s definition lines up with `towerToRdec_coeff_totalDegree_le`'s
statement shape (both are `towerToRdec p sg (poly.coeff i.val)`, but Lean's
unifier may need `show`/`unfold` help to see through `coeffsToNumDen`'s `def`).
-/

namespace Genus2Lean
namespace DecoupledSystem

open TheDataDerivation Polynomial

variable (p : ℕ) [hp : Fact (Nat.Prime p)] [hp2 : Fact (p ≠ 2)]

/-- **The resultant `totalDegree` bound, one pair (`hu0`'s shape).**
Given a common bound `D` on `uRS`'s two relevant coefficients' `towerToRdecK1`-
level data for both samples (the hypothesis `towerToRdec_coeff_totalDegree_le`
itself needs, doubled since two samples/two sides are combined here), the
resultant `d₁*c₂ - d₂*c₁` built from `(u1_num i, u1_den i, u2_num i, u2_den i)`
has `totalDegree ≤ 4*D + 2` -- two applications of `towerToRdec_coeff_
totalDegree_le` (each giving `num.totalDegree ≤ 2*D+1`, `den.totalDegree ≤
2*D`), then `totalDegree_mul`/`totalDegree_sub` combine the two cross-products:
`(u1_den i * u2_num i).totalDegree ≤ 2*D + (2*D+1) = 4*D+1` and symmetrically
for `u2_den i * u1_num i`, so the difference is `≤ max(4*D+1, 4*D+1) = 4*D+1`
via `totalDegree_sub` -- one better than the `4*D+2` claimed in this
docstring's first sentence; kept as `≤ 4*D+2` in the statement below (a
strictly weaker, safely-roundable bound) so the same numeral covers all four
`hu0/hu1/hv0/hv1` resultants uniformly without recomputing per-pair whether
`num`'s or `den`'s `+1` term dominates on each side. -/
theorem crossResultant_totalDegree_le
    (c0 c1 c2 c3 c4 : F p) (sa sb : SampleTarget p)
    (hcurA : curBeforeMonic p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 ≠ 0)
    (hcurB : curBeforeMonic p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 ≠ 0)
    (hgcdA : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1)
      (uRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1))
    (hgcdB : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1)
      (uRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1))
    (i : Fin 2) {D : ℕ}
    -- `uRS`'s a-side (sample A) coefficient `i`, pushed through `towerToRdec`'s
    -- own base-case-forward hypothesis shape:
    (hA : (towerToRdecK1 p aSideGens
            ((AdjoinRoot.modByMonicHom (K2_poly_monic p c0 c1 c2 c3 c4)
              ((uRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1).coeff i.val) :
              Polynomial (K1 p c0 c1 c2 c3 c4)).coeff 0)).1.totalDegree ≤ D ∧
      (towerToRdecK1 p aSideGens
            ((AdjoinRoot.modByMonicHom (K2_poly_monic p c0 c1 c2 c3 c4)
              ((uRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1).coeff i.val) :
              Polynomial (K1 p c0 c1 c2 c3 c4)).coeff 0)).2.totalDegree ≤ D ∧
      (towerToRdecK1 p aSideGens
            ((AdjoinRoot.modByMonicHom (K2_poly_monic p c0 c1 c2 c3 c4)
              ((uRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1).coeff i.val) :
              Polynomial (K1 p c0 c1 c2 c3 c4)).coeff 1)).1.totalDegree ≤ D ∧
      (towerToRdecK1 p aSideGens
            ((AdjoinRoot.modByMonicHom (K2_poly_monic p c0 c1 c2 c3 c4)
              ((uRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1).coeff i.val) :
              Polynomial (K1 p c0 c1 c2 c3 c4)).coeff 1)).2.totalDegree ≤ D)
    -- same shape, `uRS`'s b-side (sample B):
    (hB : (towerToRdecK1 p bSideGens
            ((AdjoinRoot.modByMonicHom (K2_poly_monic p c0 c1 c2 c3 c4)
              ((uRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1).coeff i.val) :
              Polynomial (K1 p c0 c1 c2 c3 c4)).coeff 0)).1.totalDegree ≤ D ∧
      (towerToRdecK1 p bSideGens
            ((AdjoinRoot.modByMonicHom (K2_poly_monic p c0 c1 c2 c3 c4)
              ((uRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1).coeff i.val) :
              Polynomial (K1 p c0 c1 c2 c3 c4)).coeff 0)).2.totalDegree ≤ D ∧
      (towerToRdecK1 p bSideGens
            ((AdjoinRoot.modByMonicHom (K2_poly_monic p c0 c1 c2 c3 c4)
              ((uRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1).coeff i.val) :
              Polynomial (K1 p c0 c1 c2 c3 c4)).coeff 1)).1.totalDegree ≤ D ∧
      (towerToRdecK1 p bSideGens
            ((AdjoinRoot.modByMonicHom (K2_poly_monic p c0 c1 c2 c3 c4)
              ((uRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1).coeff i.val) :
              Polynomial (K1 p c0 c1 c2 c3 c4)).coeff 1)).2.totalDegree ≤ D) :
    ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_den i *
        (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_num i -
      (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_den i *
        (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_num i).totalDegree
      ≤ 4 * D + 2 := by
  have hAnum := towerToRdec_coeff_totalDegree_le p c0 c1 c2 c3 c4 aSideGens
    (uRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1) i hA
  have hBnum := towerToRdec_coeff_totalDegree_le p c0 c1 c2 c3 c4 bSideGens
    (uRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1) i hB
  -- `u1_num i / u1_den i` unfold to `(towerToRdec p aSideGens (uRS ... sa ...).coeff i).1/.2`
  -- via `coeffsToNumDen`'s definition, matching `hAnum`'s conclusion shape directly.
  have hu1n : (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_num i
      = (towerToRdec p aSideGens
          ((uRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1).coeff i.val)).1 := rfl
  have hu1d : (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_den i
      = (towerToRdec p aSideGens
          ((uRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1).coeff i.val)).2 := rfl
  have hu2n : (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_num i
      = (towerToRdec p bSideGens
          ((uRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1).coeff i.val)).1 := rfl
  have hu2d : (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_den i
      = (towerToRdec p bSideGens
          ((uRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1).coeff i.val)).2 := rfl
  rw [hu1n, hu1d, hu2n, hu2d]
  have hle : ∀ x y : ℕ, x ≤ 4 * D + 1 → y ≤ 4 * D + 1 → max x y ≤ 4 * D + 2 := by
    intro x y hx hy; omega
  refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
  refine hle _ _ ?_ ?_
  · calc ((towerToRdec p aSideGens
              ((uRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1).coeff i.val)).2 *
            (towerToRdec p bSideGens
              ((uRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1).coeff i.val)).1).totalDegree
        ≤ (towerToRdec p aSideGens
              ((uRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1).coeff i.val)).2.totalDegree +
          (towerToRdec p bSideGens
              ((uRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1).coeff i.val)).1.totalDegree :=
          MvPolynomial.totalDegree_mul _ _
      _ ≤ 2 * D + (2 * D + 1) := by
          have := hAnum.2; have := hBnum.1; omega
      _ = 4 * D + 1 := by ring
  · calc ((towerToRdec p bSideGens
              ((uRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1).coeff i.val)).2 *
            (towerToRdec p aSideGens
              ((uRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1).coeff i.val)).1).totalDegree
        ≤ (towerToRdec p bSideGens
              ((uRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1).coeff i.val)).2.totalDegree +
          (towerToRdec p aSideGens
              ((uRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1).coeff i.val)).1.totalDegree :=
          MvPolynomial.totalDegree_mul _ _
      _ ≤ 2 * D + (2 * D + 1) := by
          have := hBnum.2; have := hAnum.1; omega
      _ = 4 * D + 1 := by ring

/-- **The `v`-side twin of `crossResultant_totalDegree_le` (`hv0`/`hv1`'s
shape).** Identical argument, `vRS` substituted for `uRS` throughout, and
threading `hgcdA`/`hgcdB` through `vRS`'s one extra explicit argument
position (`vRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 hgcdA`, matching
`theData`'s own `v1_num`/`v1_den`/`v2_num`/`v2_den` assembly exactly) -- not a
blind copy-paste, stated as its own `_flat` theorem per this project's
discipline, but the proof body itself is line-for-line the same shape as
`crossResultant_totalDegree_le` above (same `rfl`-unfolding step, same
`totalDegree_mul`/`totalDegree_sub` combination), just against `v1_num i =
(towerToRdec p aSideGens ((vRS ... hgcdA).coeff i.val)).1` etc. in place of
the `u1_num`/`u2_num` unfoldings. **Not yet REPL-confirmed** (same caveat as
the u-side theorem above -- no build environment available this pass). -/
theorem crossResultantV_totalDegree_le
    (c0 c1 c2 c3 c4 : F p) (sa sb : SampleTarget p)
    (hcurA : curBeforeMonic p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 ≠ 0)
    (hcurB : curBeforeMonic p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 ≠ 0)
    (hgcdA : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1)
      (uRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1))
    (hgcdB : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1)
      (uRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1))
    (i : Fin 2) {D : ℕ}
    -- `vRS`'s a-side (sample A) coefficient `i`, same base-case-forward shape:
    (hA : (towerToRdecK1 p aSideGens
            ((AdjoinRoot.modByMonicHom (K2_poly_monic p c0 c1 c2 c3 c4)
              ((vRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 hgcdA).coeff i.val) :
              Polynomial (K1 p c0 c1 c2 c3 c4)).coeff 0)).1.totalDegree ≤ D ∧
      (towerToRdecK1 p aSideGens
            ((AdjoinRoot.modByMonicHom (K2_poly_monic p c0 c1 c2 c3 c4)
              ((vRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 hgcdA).coeff i.val) :
              Polynomial (K1 p c0 c1 c2 c3 c4)).coeff 0)).2.totalDegree ≤ D ∧
      (towerToRdecK1 p aSideGens
            ((AdjoinRoot.modByMonicHom (K2_poly_monic p c0 c1 c2 c3 c4)
              ((vRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 hgcdA).coeff i.val) :
              Polynomial (K1 p c0 c1 c2 c3 c4)).coeff 1)).1.totalDegree ≤ D ∧
      (towerToRdecK1 p aSideGens
            ((AdjoinRoot.modByMonicHom (K2_poly_monic p c0 c1 c2 c3 c4)
              ((vRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 hgcdA).coeff i.val) :
              Polynomial (K1 p c0 c1 c2 c3 c4)).coeff 1)).2.totalDegree ≤ D)
    -- same shape, `vRS`'s b-side (sample B):
    (hB : (towerToRdecK1 p bSideGens
            ((AdjoinRoot.modByMonicHom (K2_poly_monic p c0 c1 c2 c3 c4)
              ((vRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 hgcdB).coeff i.val) :
              Polynomial (K1 p c0 c1 c2 c3 c4)).coeff 0)).1.totalDegree ≤ D ∧
      (towerToRdecK1 p bSideGens
            ((AdjoinRoot.modByMonicHom (K2_poly_monic p c0 c1 c2 c3 c4)
              ((vRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 hgcdB).coeff i.val) :
              Polynomial (K1 p c0 c1 c2 c3 c4)).coeff 0)).2.totalDegree ≤ D ∧
      (towerToRdecK1 p bSideGens
            ((AdjoinRoot.modByMonicHom (K2_poly_monic p c0 c1 c2 c3 c4)
              ((vRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 hgcdB).coeff i.val) :
              Polynomial (K1 p c0 c1 c2 c3 c4)).coeff 1)).1.totalDegree ≤ D ∧
      (towerToRdecK1 p bSideGens
            ((AdjoinRoot.modByMonicHom (K2_poly_monic p c0 c1 c2 c3 c4)
              ((vRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 hgcdB).coeff i.val) :
              Polynomial (K1 p c0 c1 c2 c3 c4)).coeff 1)).2.totalDegree ≤ D) :
    ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_den i *
        (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_num i -
      (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_den i *
        (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_num i).totalDegree
      ≤ 4 * D + 2 := by
  have hAnum := towerToRdec_coeff_totalDegree_le p c0 c1 c2 c3 c4 aSideGens
    (vRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 hgcdA) i hA
  have hBnum := towerToRdec_coeff_totalDegree_le p c0 c1 c2 c3 c4 bSideGens
    (vRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 hgcdB) i hB
  have hv1n : (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_num i
      = (towerToRdec p aSideGens
          ((vRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 hgcdA).coeff i.val)).1 := rfl
  have hv1d : (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_den i
      = (towerToRdec p aSideGens
          ((vRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 hgcdA).coeff i.val)).2 := rfl
  have hv2n : (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_num i
      = (towerToRdec p bSideGens
          ((vRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 hgcdB).coeff i.val)).1 := rfl
  have hv2d : (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_den i
      = (towerToRdec p bSideGens
          ((vRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 hgcdB).coeff i.val)).2 := rfl
  rw [hv1n, hv1d, hv2n, hv2d]
  have hle : ∀ x y : ℕ, x ≤ 4 * D + 1 → y ≤ 4 * D + 1 → max x y ≤ 4 * D + 2 := by
    intro x y hx hy; omega
  refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
  refine hle _ _ ?_ ?_
  · calc ((towerToRdec p aSideGens
              ((vRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 hgcdA).coeff i.val)).2 *
            (towerToRdec p bSideGens
              ((vRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 hgcdB).coeff i.val)).1).totalDegree
        ≤ (towerToRdec p aSideGens
              ((vRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 hgcdA).coeff i.val)).2.totalDegree +
          (towerToRdec p bSideGens
              ((vRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 hgcdB).coeff i.val)).1.totalDegree :=
          MvPolynomial.totalDegree_mul _ _
      _ ≤ 2 * D + (2 * D + 1) := by
          have := hAnum.2; have := hBnum.1; omega
      _ = 4 * D + 1 := by ring
  · calc ((towerToRdec p bSideGens
              ((vRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 hgcdB).coeff i.val)).2 *
            (towerToRdec p aSideGens
              ((vRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 hgcdA).coeff i.val)).1).totalDegree
        ≤ (towerToRdec p bSideGens
              ((vRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 hgcdB).coeff i.val)).2.totalDegree +
          (towerToRdec p aSideGens
              ((vRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 hgcdA).coeff i.val)).1.totalDegree :=
          MvPolynomial.totalDegree_mul _ _
      _ ≤ 2 * D + (2 * D + 1) := by
          have := hBnum.2; have := hAnum.1; omega
      _ = 4 * D + 1 := by ring

/-! ## Status, this pass

Both `crossResultant_totalDegree_le` (u-side, `hu0`/`hu1`'s shape) and
`crossResultantV_totalDegree_le` (v-side, `hv0`/`hv1`'s shape) are now
drafted -- instantiate each at `i = 0`/`i = 1` for the two index values.
Together these cover all four of `CrossNondegenerate`'s resultant fields.
**Neither is yet REPL-confirmed this pass** (no build environment available).

**Not done here** (deliberately, per the roadmap's own step 6): using this
bound to characterize the resultant's *vanishing* locus (the "failure modes"
question, `ROADMAP-degree-uniform-step3.md`'s Obligation 2) -- that is
genuinely separate follow-on work once a degree bound exists to reason about,
not attempted in this pass.

**Also not done here**: deriving the concrete base-case `D` itself (the
`curBeforeMonic`/`Npoly` `/ₘ`-chain gap `ROADMAP-crossnondegenerate-degree-
bound.md` flags as still fully unresolved) -- both theorems above stay
conditional on `D` as a hypothesis until that separate gap is closed.
-/

end DecoupledSystem
end Genus2Lean
