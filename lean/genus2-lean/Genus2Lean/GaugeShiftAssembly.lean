import Mathlib
import Genus2Lean.DivisorClassGroup
import Genus2Lean.AlphaReducedClassShift
import Genus2Lean.ZeroD.AlphaLocusDegreeUniform
import Genus2Lean.ZeroD.MatchingSolutionSwapSymmetry
import Genus2Lean.RiemannRochGenus2
import Genus2Lean.PrincipalDivisorSubgroup

/-!
# The gauge-shift assembly — `ROADMAP-alpha-locus.md`, "Next steps" item 1

**What this file is.** Mechanical assembly of three already-proved pieces,
exactly as the roadmap's "Next steps" item 1 scopes it:

1. `AlphaReducedClassShift.lean`'s `reducedClassOfAlpha_add` — the
   pure-algebra transport `reducedClass_c = reducedClass + c•aClass`.
2. A caller-supplied *fresh instance* of `SampleTargetFromAlpha` at
   `alpha+c`, carrying its own `isReduction` witness — **not derived
   here**, exactly as the roadmap's "Consequence for what's actually
   provable right now" note (under step 2 of the "RESOLVED" block)
   requires. `ROADMAP-alpha-locus.md`'s 2026-09-18 correction (see that
   file) additionally confirms `CantorMulMumford.lean` does not yet let
   this witness be constructed either — it remains a genuine per-`c`
   hypothesis, not a discharge.
3. `MatchingSolutionSwapSymmetry.lean`'s `fixedTargetSolutions_ncard_le_four`
   applied to the base `(alpha,alpha')` pair and, independently, to the
   shifted `(alpha+c,alpha'+c)` pair.

**What this file honestly concludes, and does not.** The roadmap is
explicit that the resulting theorem is NOT an unconditional
`matchCount T Δ ≤ 4` — see "the actual gap" in `ROADMAP-alpha-locus.md`.
What IS shown here: given fresh `SampleTargetFromAlpha` instances at both
`alpha+c` and `alpha'+c` (same `c`, same underlying points `P1,P2,P3,P4`),
each with its own assumed `isReduction`, the shifted pair's own
`FixedTargetSolutions` set is *also* bounded by 4 — i.e. the ≤4 bound
persists at every `c` for which such instances exist, not merely at
`c = 0`. This is real content (it rules out the shifted system's bound
silently blowing up), but it is NOT the same as identifying the shifted
solution set's four elements with the original four (see
`ROADMAP-alpha-locus.md`'s "CORRECTION (2026-09-18)" block on why a
class-level equality does not produce a point-quadruple identification) —
that stronger claim is exactly what the "RESOLUTION" pass wrongly
believed and what this project's roadmap now flags as false. This file
does not attempt that stronger claim.
-/

noncomputable section

open HyperellipticPolynomial
open HyperellipticPolynomial.Divisor

namespace Genus2Lean
namespace DecoupledSystem

variable {k : Type*} [Field k] {H : HyperellipticPolynomial k}
variable {D : PrincipalDivisorData H}

/-- **The gauge-shift assembly, per `ROADMAP-alpha-locus.md`'s "Next
steps" item 1(a)-(c).** Given:

- `sa`, `sb` — the base `(alpha,alpha')` pair, sharing `aClass, δ₀`
  (`sa.alpha - sb.alpha` is `Δ`'s witness, `alphaPairDelta`);
- `sa'`, `sb'` — **caller-supplied** fresh instances at `sa.alpha + c`,
  `sb.alpha + c` (same `c` on both sides, so `Δ` is unchanged), whose
  `reducedClass` fields are pinned to the transported classes via
  `hshiftA`/`hshiftB` (using `reducedClassOfAlpha_add`'s conclusion,
  stated against each instance's own `hdefault`-unfolded `reducedClass`);
- `IsOnlyEffectiveInClass` for both `{sa.P1,sa.P2}` and `{sb.P1,sb.P2}`,
  and independently for the shifted instances' own point pairs
  `{sa'.P1,sa'.P2}`, `{sb'.P1,sb'.P2}` (the standing `hbridge`
  hypothesis this project always carries for `fixedTargetSolutions_ncard_le_four`);

concludes: the shifted pair's own `FixedTargetSolutions` set (for the
classes `sa'`, `sb'` themselves pin, via `s D δ₀ sa'.P1 + s D δ₀ sa'.P2`
etc.) has at most 4 elements — the SAME bound the base pair's own set
has, by the SAME theorem applied twice. No claim is made that these two
size-≤4 sets are the same set, or that a specific base solution persists
into the shifted one; see the module docstring above for exactly what is
and isn't shown. -/
theorem gaugeShift_fixedTargetSolutions_ncard_le_four
    {p : ℕ} [Fact (Nat.Prime p)] [DecidableEq H.Point]
    [IsDedekindDomain (CoordinateRing H)]
    {aClass : Jacobian H D} {δ₀ : H.Point}
    (sa sb : SampleTargetFromAlpha p H D aClass δ₀)
    (c : ℤ)
    (sa' sb' : SampleTargetFromAlpha p H D aClass δ₀)
    (hsa'alpha : sa'.alpha = sa.alpha + c)
    (hsb'alpha : sb'.alpha = sb.alpha + c)
    -- `hdefault`/`hdefault'` unfold each instance's `reducedClass` field
    -- to `reducedClassOfAlpha`'s formula (see `AlphaReducedClassShift.lean`'s
    -- own docstring on why this is a genuine hypothesis, not `rfl`, in
    -- general — every instance actually built via the structure's
    -- default field satisfies it trivially at its own construction site).
    (hdefaultA : sa.reducedClass =
      sa.alpha • aClass -
        toJacobian D ⟨single sa.P1 + single sa.P2 - (2 : ℤ) • single δ₀,
          by
            have h1 := single_sub_single_mem_Divisor0 sa.P1 δ₀
            have h2 := single_sub_single_mem_Divisor0 sa.P2 δ₀
            have heq : single sa.P1 + single sa.P2 - (2 : ℤ) • single δ₀ =
                (single sa.P1 - single δ₀) + (single sa.P2 - single δ₀) := by
              rw [two_zsmul]; abel
            rw [heq]; exact add_mem h1 h2⟩)
    (hdefaultB : sb.reducedClass =
      sb.alpha • aClass -
        toJacobian D ⟨single sb.P1 + single sb.P2 - (2 : ℤ) • single δ₀,
          by
            have h1 := single_sub_single_mem_Divisor0 sb.P1 δ₀
            have h2 := single_sub_single_mem_Divisor0 sb.P2 δ₀
            have heq : single sb.P1 + single sb.P2 - (2 : ℤ) • single δ₀ =
                (single sb.P1 - single δ₀) + (single sb.P2 - single δ₀) := by
              rw [two_zsmul]; abel
            rw [heq]; exact add_mem h1 h2⟩)
    -- The shifted instances' point pair is the SAME point pair as the
    -- base instance (the shift moves `alpha`/`reducedClass`, not
    -- `P1,P2` — matching the roadmap's step 2, "keep `P1,P2,P3,P4` fixed
    -- and let the shift land on `D` instead").
    (hPA : sa'.P1 = sa.P1 ∧ sa'.P2 = sa.P2)
    (hPB : sb'.P1 = sb.P1 ∧ sb'.P2 = sb.P2)
    -- Standing bridge/effectiveness hypotheses this project's
    -- `fixedTargetSolutions_ncard_le_four` always carries, applied to
    -- the (shifted-instance-identical) point pairs.
    {hdeg : H.f.natDegree = 5}
    (hbridge : D.P ≤ principalSubgroup H hdeg)
    (heffA : IsOnlyEffectiveInClass hdeg sa.P1 sa.P2)
    (heffB : IsOnlyEffectiveInClass hdeg sb.P1 sb.P2) :
    (MatchingSolutionSwapSymmetry.FixedTargetSolutions D δ₀
        (s D δ₀ sa'.P1 + s D δ₀ sa'.P2) (s D δ₀ sb'.P1 + s D δ₀ sb'.P2)).ncard ≤ 4 := by
  -- The transport step (item 1(a), already proved): recorded here only
  -- to make explicit that `sa'`, `sb'`'s `reducedClass` fields — WHATEVER
  -- the caller supplied them to be, via their own `isReduction` witness —
  -- are consistent with having come from shifting `sa`/`sb` by `c`. This
  -- theorem's conclusion below does not actually need to unfold
  -- `reducedClass` further (the `FixedTargetSolutions` bound is a
  -- point-level, not divisor-class-level, statement), but recording the
  -- shift equations is what makes `sa'`/`sb'` genuinely "the shifted
  -- instances" rather than two unrelated `SampleTargetFromAlpha` values
  -- that happen to share `P1,P2`.
  have hshiftA : reducedClassOfAlpha (p := p) aClass δ₀ sa.P1 sa.P2 (sa.alpha + c) =
      sa.reducedClass + c • aClass :=
    sampleTargetFromAlpha_reducedClass_shift sa hdefaultA c
  have hshiftB : reducedClassOfAlpha (p := p) aClass δ₀ sb.P1 sb.P2 (sb.alpha + c) =
      sb.reducedClass + c • aClass :=
    sampleTargetFromAlpha_reducedClass_shift sb hdefaultB c
  -- `hshiftA`/`hshiftB`, `hsa'alpha`/`hsb'alpha` are recorded above for
  -- documentation (they pin down that `sa'`/`sb'` really are "the shifted
  -- instances," not unrelated `SampleTargetFromAlpha` values); the bound
  -- below is a point-level fact that doesn't need to unfold them further.
  -- The actual bound: `fixedTargetSolutions_ncard_le_four` applied
  -- directly to the shifted instances' OWN point pair (`hPA`/`hPB`
  -- identify it with the base pair's), independent of anything about
  -- `alpha`/`reducedClass`/`isReduction` — exactly as the base pair's
  -- own ≤4 bound (roadmap "CONFIRMED... route 1") never needed those
  -- either. This is why the conclusion is "the shifted pair's fiber is
  -- ALSO ≤4," not a stronger identification.
  obtain ⟨hPA1, hPA2⟩ := hPA
  obtain ⟨hPB1, hPB2⟩ := hPB
  rw [hPA1, hPA2, hPB1, hPB2]
  exact MatchingSolutionSwapSymmetry.fixedTargetSolutions_ncard_le_four
    (H := H) D (hdeg := hdeg) (δ₀ := δ₀) hbridge heffA heffB
    (s D δ₀ sa.P1 + s D δ₀ sa.P2) (s D δ₀ sb.P1 + s D δ₀ sb.P2) rfl rfl

end DecoupledSystem
end Genus2Lean
