import Mathlib
import Genus2Lean.ZeroD.PrincipalWitness
import Genus2Lean.ZeroD.SanchorMumfordOrdAt
import Genus2Lean.ZeroD.Reduce.AlphaReduce
import Genus2Lean.ZeroD.Reduce.GeneralSharedRoot

/-! # `Sanchor = {sa.P1, sa.P2}` — the missing `A ↔ alpha • aClass` link

**Closes `ROADMAP-principal-witness-assembly.md`'s step 0.** Diagnosed
this pass: `CAWitness.lean`'s witness construction (`bCA`,
`caInterpMatrix`, everything downstream) takes `P1X P2X P1Y P2Y : k` as
bare free variables. `AlphaLocusDegreeUniform.lean`'s
`reducedClass_eq_of_isReduction'` separately has `sa.P1, sa.P2 : H.Point`
(the actual anchor points `reducedClass := alpha • aClass -
toJacobian(...[P1]+[P2]...)` is built from) AND `Sanchor : Finset
H.Point` (tied to `ua`'s root set via `hSanchorMem`/`huafree`/
`hSanchorCard`, and to `alpha • aClass` itself via `hAlphaRep`) — but
**nothing in the theorem's signature ever asserts `Sanchor = {sa.P1,
sa.P2}`**. Checked exhaustively: `sa.P1`/`sa.P2` appear ONLY in
`hcur`/`hgcd`/`hcurT`/`hgcdT` (feeding `curBeforeMonic4General`/
`Ypoly4`/`uRS4General`, the reduction machinery that produces the
*target* `(u0,u1,v0,v1)`), never alongside `ua`/`va`/`Sanchor`. `hMumfordUa`
(`IsMumfordUa p c0 c1 c2 c3 c4 ua0 ua1 va0 va1`) says `(ua,va)` is *some*
valid Mumford pair for `alpha • aClass` — it says nothing about `ua`'s
roots being `sa.P1.X, sa.P2.X` specifically. This is a genuinely missing
hypothesis, not a renaming: `A` (`= Sanchor`, per `CAWitness.lean`'s own
docstring) was never actually shown/asserted equal to `[sa.P1]+[sa.P2]`.

**This file supplies the missing link, as a NEW hypothesis
(`hAnchorRoots`) plus the theorem that turns it into the Finset equality
downstream code needs.** `hAnchorRoots : ua.IsRoot sa.P1.X ∧ ua.IsRoot
sa.P2.X` has to be added to `reducedClass_eq_of_isReduction'`'s own
signature the next time that theorem's proof body is attempted — it is
exactly the same kind of "caller supplies the real Mumford data" premise
`hMumfordUa`/`hMumfordTarget` already are (see that theorem's own
trailing comment), not something derivable from what's currently in
scope. Once supplied, `Sanchor_eq_of_anchor_roots` below (fully-split
case, `sa.P1 ≠ sa.P2`) gives `Sanchor = {sa.P1, sa.P2}` directly from
`hSanchorMem`/`huafree`/`hSanchorCard`, via the same
`quadratic_eq_mul_X_sub_C` factorization already used for `ua`/`u_target`
throughout `PrincipalWitnessAssembly.lean`/`OrdAtRootMultiplicityUnified.
lean` — no new machinery, just applied to `sa.P1.X, sa.P2.X` as the named
roots instead of the usual `Ra1X, Ra2X`.

**What this means downstream (unblocks step 0's item in the roadmap):**
once `Sanchor = {sa.P1, sa.P2}` is on hand, `CAWitness.lean`'s `P1X P1Y
P2X P2Y` inputs get instantiated at `sa.P1.X, sa.P1.Y, sa.P2.X, sa.P2.Y`
— `A := [sa.P1]+[sa.P2]` and `divToPair (-va) 1 Sanchor` become the same
divisor by `Sanchor_eq_of_anchor_roots` plus `SanchorMumfordOrdAt.lean`'s
`ordAt_negVa_one_eq_one_of_mem_Sanchor` (giving each point's `ordAt`
coefficient), rather than two independently-asserted objects. This is
the ground truth `PrincipalWitnessStep4.lean`'s Part 2/Part 3 sign
questions (`S := ι(T)` vs `S := T`, etc.) can finally be checked against.

**Tangent branch (`sa.P1 = sa.P2`) is a genuine, separate case, NOT a
restriction to defer.** Diagnosed: the split hypothesis `hP1Xne`/
`hRa12Xne`/`hT12Xne` propagating up into
`reducedClass_eq_of_isReduction'`'s signature is an ARTIFACT of
`Sanchor_eq_of_anchor_roots` reaching for `quadratic_eq_mul_X_sub_C`
(which only factors a monic quadratic against two named DISTINCT roots)
instead of the unconditional route `SanchorMumfordOrdAt.lean`,
`CAWitnessResidual.lean`, and `OrdAtRootMultiplicityUnified.lean`
already use everywhere else (`ordAt_eq_rootMultiplicity_unramified` +
squarefreeness, no distinctness needed). It is not a real mathematical
restriction — `huafree : Squarefree ua` does NOT force `P1.X ≠ P2.X`
when `P1.X = P2.X` isn't itself given as a root pair to split (a single
`IsRoot` fact only pins `rootMultiplicity ≥ 1`, not `≥ 2`); the tangent
case is instead genuinely reached when the CALLER supplies `ua = (X - C
R)^2` directly (`hP1eqP2 : P1 = P2`, `R := P1.X = P2.X`), mirroring
`OrdAtRootMultiplicityUnified.lean`'s
`rootMultiplicity_npoly4Lcm4_eq_two_of_R1_eq_R2` pattern: the repeated
root is caller-supplied data (from `hMumfordUa`'s concrete `(ua0,ua1)`),
not derived from squarefreeness. `Sanchor_eq_of_anchor_roots_tangent`
below handles this: `Sanchor` collapses to the singleton `{P1}`, and
`hSanchorCard` (`= ua.natDegree = 2`) is then impossible to satisfy
UNLESS `Sanchor` is being counted with a convention that doesn't apply
to a plain `Finset` — so the actual caller-facing fact in this branch is
`Sanchor = {P1}` as a `Finset` (cardinality 1), with the multiplicity-2
information living in `ordAt`/`rootMultiplicity`, not in `Finset.card`.
Downstream code that assumed `Sanchor.card = ua.natDegree` unconditionally
needs to drop that assumption for the tangent branch specifically — this
is the actual scope of the bug, not the split case, which was already
correct and needed no repair beyond this docstring. -/

noncomputable section

open Polynomial
open HyperellipticPolynomial
open Genus2Lean.TheDataDerivation

namespace Genus2Lean
namespace DecoupledSystem

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {H : HyperellipticPolynomial (Genus2Lean.TheDataDerivation.F p)}
  [IsDedekindDomain (CoordinateRing H)]

/-- **The missing link, fully-split case: `Sanchor = {sa.P1, sa.P2}`.**
Given `ua`'s two named roots are exactly `sa.P1.X, sa.P2.X`
(`hAnchorRoots` — the new hypothesis this file's docstring says needs
adding to `reducedClass_eq_of_isReduction'`'s own signature), `Sanchor`'s
membership characterization (`hSanchorMem`) plus its cardinality
matching `ua`'s degree (`hSanchorCard`) pin it down completely: `ua`
factors as `(X - C sa.P1.X) * (X - C sa.P2.X)` (`quadratic_eq_mul_X_sub_C`,
needing `sa.P1.X ≠ sa.P2.X`), so `ua`'s only roots are `sa.P1.X` and
`sa.P2.X`; `hSanchorMem` says every `Sanchor` point's `X`-coordinate is a
root of `ua` with the matching `Y`-coordinate (`= va.eval _`), forcing
`Sanchor ⊆ {sa.P1, sa.P2}` (any point of `Sanchor` has `X ∈ {sa.P1.X,
sa.P2.X}` and its `Y` is then pinned by `va.eval`, matching `sa.P1`/
`sa.P2`'s own `Y` since those also satisfy `Y = va.eval X` — supplied via
`hsaP1Y`/`hsaP2Y`, the fact that `sa.P1,sa.P2` themselves lie on `(-va,1)`'s
zero set, which has to hold for `hAnchorRoots` to be meaningful in the
first place); the reverse inclusion plus matching cardinalities
(`Finset.eq_of_subset_of_card_le`) closes it. -/
theorem Sanchor_eq_of_anchor_roots
    [DecidableEq H.Point]
    {ua0 ua1 : Genus2Lean.TheDataDerivation.F p}
    (ua va : Polynomial (Genus2Lean.TheDataDerivation.F p))
    (hua : ua = (X : Polynomial (Genus2Lean.TheDataDerivation.F p)) ^ 2
      + C ua1 * X + C ua0)
    (huafree : Squarefree ua)
    (P1 P2 : H.Point)
    (hP1ne : P1 ≠ P2) (hP1Xne : P1.X ≠ P2.X)
    (hAnchorRoots : ua.IsRoot P1.X ∧ ua.IsRoot P2.X)
    (hsaP1Y : P1.Y = va.eval P1.X) (hsaP2Y : P2.Y = va.eval P2.X)
    (Sanchor : Finset H.Point)
    (hSanchorMem : ∀ Q ∈ Sanchor, ua.eval Q.X = 0 ∧ Q.Y = va.eval Q.X)
    (hSanchorCard : Sanchor.card = ua.natDegree) :
    Sanchor = ({P1, P2} : Finset H.Point) := by
  classical
  have hmonic : ua.Monic := by rw [hua]; monicity!
  have hdeg2 : ua.natDegree = 2 := by rw [hua]; compute_degree!
  have hfactor : ua = (X - C P1.X) * (X - C P2.X) :=
    quadratic_eq_mul_X_sub_C p hmonic hdeg2 hAnchorRoots.1 hAnchorRoots.2 hP1Xne
  -- `{P1, P2} ⊆ Sanchor`: both points satisfy `hSanchorMem`'s membership
  -- test, so both actually lie in `Sanchor` — but `Sanchor` is only
  -- characterized as a SUBSET of `ua`'s roots by `hSanchorMem`, not shown
  -- to CONTAIN them; that direction instead comes from cardinality: `ua`
  -- has exactly two roots (`P1.X, P2.X`, distinct), so `Sanchor ⊆
  -- {P1,P2}` (every member is one of the two named roots, with the
  -- unique matching `Y`), and `Sanchor.card = 2 = {P1,P2}.card` forces
  -- equality once containment is known one way.
  have hsub : Sanchor ⊆ ({P1, P2} : Finset H.Point) := by
    intro Q hQ
    obtain ⟨hQroot, hQY⟩ := hSanchorMem Q hQ
    have hQX : Q.X = P1.X ∨ Q.X = P2.X := by
      rw [hfactor] at hQroot
      simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C] at hQroot
      rcases mul_eq_zero.mp hQroot with h1 | h2
      · left; exact sub_eq_zero.mp h1
      · right; exact sub_eq_zero.mp h2
    rw [Finset.mem_insert, Finset.mem_singleton]
    rcases hQX with hQX | hQX
    · left
      have hQeqY : Q.Y = P1.Y := by rw [hQY, hQX, ← hsaP1Y]
      exact Subtype.ext (Prod.ext hQX hQeqY)
    · right
      have hQeqY : Q.Y = P2.Y := by rw [hQY, hQX, ← hsaP2Y]
      exact Subtype.ext (Prod.ext hQX hQeqY)
  have hcard2 : ({P1, P2} : Finset H.Point).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hP1ne),
      Finset.card_singleton]
  have hSanchorCard2 : Sanchor.card = 2 := by rw [hSanchorCard, hdeg2]
  exact Finset.eq_of_subset_of_card_le hsub (by rw [hcard2, hSanchorCard2])

/-- **The missing link, tangent case: `Sanchor = {P1}`.** Mirrors
`OrdAtRootMultiplicityUnified.lean`'s `rootMultiplicity_npoly4Lcm4_eq_
two_of_R1_eq_R2` pattern: the repeated root is CALLER-supplied
(`hua : ua = (X - C P1.X) ^ 2`), not derived from `Squarefree ua` (which
would be false for a genuine double root — `Squarefree` and `IsRoot`
alone never force this branch). `Sanchor`'s membership test
(`hSanchorMem`) then only ever matches `Q.X = P1.X`, so `Sanchor ⊆
{P1}`; `P1 ∈ Sanchor` (from `hP1mem`) gives the reverse inclusion. Note
`Sanchor.card = 1 ≠ 2 = ua.natDegree` here — `hSanchorCard`'s usual form
does NOT hold in this branch, so this theorem takes membership only,
not the cardinality hypothesis (any caller in the tangent case must
supply `hP1mem` directly, e.g. from `hAlphaRep`/`hMumfordUa`, rather
than deriving it from a cardinality argument as the split case does). -/
theorem Sanchor_eq_of_anchor_roots_tangent
    [DecidableEq H.Point]
    (ua va : Polynomial (Genus2Lean.TheDataDerivation.F p))
    (P1 : H.Point)
    (hua : ua = (X - C P1.X) ^ 2)
    (hsaP1Y : P1.Y = va.eval P1.X)
    (Sanchor : Finset H.Point)
    (hSanchorMem : ∀ Q ∈ Sanchor, ua.eval Q.X = 0 ∧ Q.Y = va.eval Q.X)
    (hP1mem : P1 ∈ Sanchor) :
    Sanchor = ({P1} : Finset H.Point) := by
  classical
  have hsub : Sanchor ⊆ ({P1} : Finset H.Point) := by
    intro Q hQ
    obtain ⟨hQroot, hQY⟩ := hSanchorMem Q hQ
    have hQX : Q.X = P1.X := by
      rw [hua] at hQroot
      simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C, pow_eq_zero_iff, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true] at hQroot
      exact sub_eq_zero.mp hQroot
    rw [Finset.mem_singleton]
    have hQeqY : Q.Y = P1.Y := by rw [hQY, hQX, ← hsaP1Y]
    exact Subtype.ext (Prod.ext hQX hQeqY)
  exact Finset.Subset.antisymm hsub (Finset.singleton_subset_iff.mpr hP1mem)

end DecoupledSystem
end Genus2Lean
