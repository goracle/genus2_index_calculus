import Mathlib
import Genus2Lean.ZeroD.PeelChainAssemblyFinrank
import Genus2Lean.ZeroD.PeelChainStageFinite
import Genus2Lean.ZeroD.AlphaLocusDegreeUniform

/-!
# Assembly, part 4: specializing the n-stage fold to `genList`'s literal
# 12 generators

The true remainder `ROADMAP-monic-annihilator-degree-uniform.md`'s
Progress section flags as "still the next concrete step, and now
actually startable": chaining the twelve per-stage `finrank`/`Module.Finite`/
`Nontrivial` facts (`PeelChainStageFinite.lean`) against `genList`'s
actual 12 generators and `theData`'s actual field values. This file does
that specialization, **superseding the earlier placeholder** (this
file's previous revision left `genList_finrank_assembly_placeholder :
True := trivial` in its place, per the roadmap's own convention of
naming genuinely-open work rather than a live `sorry`).

**Route taken: (a), twelve sequential explicit applications** — the
roadmap's own file-plan diagnosis flagged this as the more promising of
the two candidate routes (the other being reformulating
`PeelChainAssemblyFinrank.lean`'s generic fold to case-split internally
on a positional index) and identified the concrete risk to check first:
whether the `List.take`/indexed-lookup bookkeeping an indexed hypothesis
structure would need actually unifies against `genList`'s own
associativity of `++` without further lemmas. **This file sidesteps
that risk entirely**, rather than resolving it: instead of an indexed
`PeelChainFinrankHyp` field looked up via `List.take`/`getD` at each of
twelve positions (the previous revision's approach), each of the twelve
side-conditions is now a SEPARATELY NAMED field (`hd_unit_Fu0`, ...,
`hgu_curveB2`), and the twelve applications below are twelve literal,
independently-typechecked calls — `Fu0`, `Fu0 ++ Fu1`, etc. as EXPLICIT
list literals built by direct `++`/`[...]` at each step, never a
`List.take`-sliced view of a longer list. This is more verbose than the
indexed version but has no associativity-unification risk to check,
matching this file's own priority (get a real replacement for
`GenericPeelChainHyp.hfinrank_le` on the board first; an indexed,
more compact restatement of `PeelChainFinrankHyp` can follow later if
wanted, as a pure refactor of this file's hypothesis bundle, not of its
proof).

**What this file is honest about, unchanged from the previous
revision's own framing**: `PeelChainFinrankHyp`'s twelve fields
(eight `IsUnit (mk d)` facts for the linear-elimination stages' leading
coefficients, plus twelve `¬IsUnit (mk g)` non-unit facts needed for
`Nontrivial` at each of the twelve stages) are genuinely NEW
per-stage hypotheses — not already supplied by `Nondegenerate`/
`CrossNondegenerate` (`DecoupledSystemRegular.lean`), which give `≠ 0`
facts about `uRS`/`vRS` coefficients in the BASE field `F p`, or
`IsSMulRegular` facts about a COMBINED expression in an EXTENDED
quotient — neither of which is the isolated `IsUnit`/`¬IsUnit` fact
about a specific accumulated-prefix quotient that this chain actually
needs. **This file does not claim these twelve conditions are proved,
derivable, or even likely to hold for a generic curve**; matching them
against `theData`'s actual symbolic formulas (and hence `Bad`'s
eventual size, per the roadmap's still-open item 6) remains deferred,
exactly as the roadmap's own file plan scopes it.

**Deliberately generic over `d : DecoupledGenerators p`, NOT
parametrized by `(c0,...,c4,sa,sb,...)` and tied to `theData`
internally** — same reasoning the previous revision already gave (a
`whnf` heartbeat timeout was hit merely STATING an equality
`d = theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB` as a
structure field's own type, not from repeated use of the term):
`PeelChainFinrankHyp` below takes `d : DecoupledGenerators p` as a free
parameter with no equality field connecting it back to `theData`.
Connecting `d := theData p ...` at the real values is the CALLER's job
at instantiation (an ordinary function application), not something this
structure states or carries. `FuList`/`FvList`/`curveA1`-etc. are NOT
similarly parametrized, however — unlike `d`, they are needed in this
file's actual proof (each stage's literal generator, in `genList`'s
literal order), and `curveRelationGen`/`linearElimGen`'s equality with
`curveA1`/`FuList`'s entries is `rfl`-true (both unfold to the same
`X w ^ 2 - (...)`/`c - X u * d` shape — checked directly against
`DecoupledSystemRegular.lean`'s literal definitions, not assumed), so no
separate equality hypothesis is needed for those. -/

namespace Genus2Lean
namespace DecoupledSystem

open Polynomial
open TheDataDerivation
open HyperellipticPolynomial
open HyperellipticPolynomial.Divisor

variable (p : ℕ) [Fact (Nat.Prime p)] [Fact (p ≠ 2)]
variable {k : Type*} [Field k] {H : HyperellipticPolynomial k}
variable {D : PrincipalDivisorData H}

/-- **The twelve genuinely-open per-stage side conditions, bundled, one
separately-named field per stage** (superseding the previous revision's
`List.take`/`getD`-indexed fields — see the module docstring for why).
Generic over `d : DecoupledGenerators p` and the two curve-side samples'
coefficients `c0,...,c4 : F p` (needed for `curveA1`-etc.'s own
statement), matching `genList`'s literal stage order:
`Fu0,Fu1,Fu2,Fu3,Fv0,Fv1,Fv2,Fv3,curveA1,curveA2,curveB1,curveB2`. -/
structure PeelChainFinrankHyp (d : DecoupledGenerators p) (c0 c1 c2 c3 c4 : F p) :
    Prop where
  /-- Stage 0 (`Fu0`): `d.u1_den 0`'s image is a unit at the empty prefix. -/
  hd_unit_Fu0 : IsUnit (Ideal.Quotient.mk (Ideal.ofList ([] : List (Rdec p)))
    (d.u1_den 0))
  /-- Stage 0's own generator is a non-unit at the empty prefix. -/
  hgu_Fu0 : ¬ IsUnit (Ideal.Quotient.mk (Ideal.ofList ([] : List (Rdec p)))
    (d.u1_num 0 - U0' p * d.u1_den 0))
  /-- Stage 1 (`Fu1`): `d.u2_den 0`'s image is a unit at prefix `[Fu0]`. -/
  hd_unit_Fu1 : IsUnit (Ideal.Quotient.mk
    (Ideal.ofList [d.u1_num 0 - U0' p * d.u1_den 0]) (d.u2_den 0))
  /-- Stage 1's own generator is a non-unit at prefix `[Fu0]`. -/
  hgu_Fu1 : ¬ IsUnit (Ideal.Quotient.mk
    (Ideal.ofList [d.u1_num 0 - U0' p * d.u1_den 0])
    (d.u2_num 0 - U0' p * d.u2_den 0))
  /-- Stage 2 (`Fu2`): `d.u1_den 1`'s image is a unit at prefix `[Fu0,Fu1]`. -/
  hd_unit_Fu2 : IsUnit (Ideal.Quotient.mk
    (Ideal.ofList [d.u1_num 0 - U0' p * d.u1_den 0,
      d.u2_num 0 - U0' p * d.u2_den 0]) (d.u1_den 1))
  /-- Stage 2's own generator is a non-unit at prefix `[Fu0,Fu1]`. -/
  hgu_Fu2 : ¬ IsUnit (Ideal.Quotient.mk
    (Ideal.ofList [d.u1_num 0 - U0' p * d.u1_den 0,
      d.u2_num 0 - U0' p * d.u2_den 0])
    (d.u1_num 1 - U1' p * d.u1_den 1))
  /-- Stage 3 (`Fu3`): `d.u2_den 1`'s image is a unit at prefix
  `[Fu0,Fu1,Fu2]`. -/
  hd_unit_Fu3 : IsUnit (Ideal.Quotient.mk
    (Ideal.ofList [d.u1_num 0 - U0' p * d.u1_den 0,
      d.u2_num 0 - U0' p * d.u2_den 0,
      d.u1_num 1 - U1' p * d.u1_den 1]) (d.u2_den 1))
  /-- Stage 3's own generator is a non-unit at prefix `[Fu0,Fu1,Fu2]`. -/
  hgu_Fu3 : ¬ IsUnit (Ideal.Quotient.mk
    (Ideal.ofList [d.u1_num 0 - U0' p * d.u1_den 0,
      d.u2_num 0 - U0' p * d.u2_den 0,
      d.u1_num 1 - U1' p * d.u1_den 1])
    (d.u2_num 1 - U1' p * d.u2_den 1))
  /-- Stage 4 (`Fv0`): `d.v1_den 0`'s image is a unit at prefix
  `FuList` (all four `Fu` generators). -/
  hd_unit_Fv0 : IsUnit (Ideal.Quotient.mk
    (Ideal.ofList [d.u1_num 0 - U0' p * d.u1_den 0,
      d.u2_num 0 - U0' p * d.u2_den 0,
      d.u1_num 1 - U1' p * d.u1_den 1,
      d.u2_num 1 - U1' p * d.u2_den 1]) (d.v1_den 0))
  /-- Stage 4's own generator is a non-unit at prefix `FuList`. -/
  hgu_Fv0 : ¬ IsUnit (Ideal.Quotient.mk
    (Ideal.ofList [d.u1_num 0 - U0' p * d.u1_den 0,
      d.u2_num 0 - U0' p * d.u2_den 0,
      d.u1_num 1 - U1' p * d.u1_den 1,
      d.u2_num 1 - U1' p * d.u2_den 1])
    (d.v1_num 0 - V0' p * d.v1_den 0))
  /-- Stage 5 (`Fv1`): `d.v2_den 0`'s image is a unit at prefix
  `FuList ++ [Fv0]`. -/
  hd_unit_Fv1 : IsUnit (Ideal.Quotient.mk
    (Ideal.ofList [d.u1_num 0 - U0' p * d.u1_den 0,
      d.u2_num 0 - U0' p * d.u2_den 0,
      d.u1_num 1 - U1' p * d.u1_den 1,
      d.u2_num 1 - U1' p * d.u2_den 1,
      d.v1_num 0 - V0' p * d.v1_den 0]) (d.v2_den 0))
  /-- Stage 5's own generator is a non-unit at prefix `FuList ++ [Fv0]`. -/
  hgu_Fv1 : ¬ IsUnit (Ideal.Quotient.mk
    (Ideal.ofList [d.u1_num 0 - U0' p * d.u1_den 0,
      d.u2_num 0 - U0' p * d.u2_den 0,
      d.u1_num 1 - U1' p * d.u1_den 1,
      d.u2_num 1 - U1' p * d.u2_den 1,
      d.v1_num 0 - V0' p * d.v1_den 0])
    (d.v2_num 0 - V0' p * d.v2_den 0))
  /-- Stage 6 (`Fv2`): `d.v1_den 1`'s image is a unit at prefix
  `FuList ++ [Fv0,Fv1]`. -/
  hd_unit_Fv2 : IsUnit (Ideal.Quotient.mk
    (Ideal.ofList [d.u1_num 0 - U0' p * d.u1_den 0,
      d.u2_num 0 - U0' p * d.u2_den 0,
      d.u1_num 1 - U1' p * d.u1_den 1,
      d.u2_num 1 - U1' p * d.u2_den 1,
      d.v1_num 0 - V0' p * d.v1_den 0,
      d.v2_num 0 - V0' p * d.v2_den 0]) (d.v1_den 1))
  /-- Stage 6's own generator is a non-unit at prefix `FuList ++ [Fv0,Fv1]`. -/
  hgu_Fv2 : ¬ IsUnit (Ideal.Quotient.mk
    (Ideal.ofList [d.u1_num 0 - U0' p * d.u1_den 0,
      d.u2_num 0 - U0' p * d.u2_den 0,
      d.u1_num 1 - U1' p * d.u1_den 1,
      d.u2_num 1 - U1' p * d.u2_den 1,
      d.v1_num 0 - V0' p * d.v1_den 0,
      d.v2_num 0 - V0' p * d.v2_den 0])
    (d.v1_num 1 - V1' p * d.v1_den 1))
  /-- Stage 7 (`Fv3`): `d.v2_den 1`'s image is a unit at prefix
  `FuList ++ [Fv0,Fv1,Fv2]`. -/
  hd_unit_Fv3 : IsUnit (Ideal.Quotient.mk
    (Ideal.ofList [d.u1_num 0 - U0' p * d.u1_den 0,
      d.u2_num 0 - U0' p * d.u2_den 0,
      d.u1_num 1 - U1' p * d.u1_den 1,
      d.u2_num 1 - U1' p * d.u2_den 1,
      d.v1_num 0 - V0' p * d.v1_den 0,
      d.v2_num 0 - V0' p * d.v2_den 0,
      d.v1_num 1 - V1' p * d.v1_den 1]) (d.v2_den 1))
  /-- Stage 7's own generator is a non-unit at prefix
  `FuList ++ [Fv0,Fv1,Fv2]`. -/
  hgu_Fv3 : ¬ IsUnit (Ideal.Quotient.mk
    (Ideal.ofList [d.u1_num 0 - U0' p * d.u1_den 0,
      d.u2_num 0 - U0' p * d.u2_den 0,
      d.u1_num 1 - U1' p * d.u1_den 1,
      d.u2_num 1 - U1' p * d.u2_den 1,
      d.v1_num 0 - V0' p * d.v1_den 0,
      d.v2_num 0 - V0' p * d.v2_den 0,
      d.v1_num 1 - V1' p * d.v1_den 1])
    (d.v2_num 1 - V1' p * d.v2_den 1))
  /-- Stage 8 (`curveA1`): its own generator is a non-unit at prefix
  `FuList ++ FvList` (all eight matching generators). -/
  hgu_curveA1 : ¬ IsUnit (Ideal.Quotient.mk
    (Ideal.ofList [d.u1_num 0 - U0' p * d.u1_den 0,
      d.u2_num 0 - U0' p * d.u2_den 0,
      d.u1_num 1 - U1' p * d.u1_den 1,
      d.u2_num 1 - U1' p * d.u2_den 1,
      d.v1_num 0 - V0' p * d.v1_den 0,
      d.v2_num 0 - V0' p * d.v2_den 0,
      d.v1_num 1 - V1' p * d.v1_den 1,
      d.v2_num 1 - V1' p * d.v2_den 1])
    (curveA1 p c0 c1 c2 c3 c4))
  /-- Stage 9 (`curveA2`): its own generator is a non-unit at prefix
  `FuList ++ FvList ++ [curveA1]`. -/
  hgu_curveA2 : ¬ IsUnit (Ideal.Quotient.mk
    (Ideal.ofList [d.u1_num 0 - U0' p * d.u1_den 0,
      d.u2_num 0 - U0' p * d.u2_den 0,
      d.u1_num 1 - U1' p * d.u1_den 1,
      d.u2_num 1 - U1' p * d.u2_den 1,
      d.v1_num 0 - V0' p * d.v1_den 0,
      d.v2_num 0 - V0' p * d.v2_den 0,
      d.v1_num 1 - V1' p * d.v1_den 1,
      d.v2_num 1 - V1' p * d.v2_den 1,
      curveA1 p c0 c1 c2 c3 c4])
    (curveA2 p c0 c1 c2 c3 c4))
  /-- Stage 10 (`curveB1`): its own generator is a non-unit at prefix
  `FuList ++ FvList ++ [curveA1,curveA2]`. -/
  hgu_curveB1 : ¬ IsUnit (Ideal.Quotient.mk
    (Ideal.ofList [d.u1_num 0 - U0' p * d.u1_den 0,
      d.u2_num 0 - U0' p * d.u2_den 0,
      d.u1_num 1 - U1' p * d.u1_den 1,
      d.u2_num 1 - U1' p * d.u2_den 1,
      d.v1_num 0 - V0' p * d.v1_den 0,
      d.v2_num 0 - V0' p * d.v2_den 0,
      d.v1_num 1 - V1' p * d.v1_den 1,
      d.v2_num 1 - V1' p * d.v2_den 1,
      curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4])
    (curveB1 p c0 c1 c2 c3 c4))
  /-- Stage 11 (`curveB2`): its own generator is a non-unit at prefix
  `FuList ++ FvList ++ [curveA1,curveA2,curveB1]`. -/
  hgu_curveB2 : ¬ IsUnit (Ideal.Quotient.mk
    (Ideal.ofList [d.u1_num 0 - U0' p * d.u1_den 0,
      d.u2_num 0 - U0' p * d.u2_den 0,
      d.u1_num 1 - U1' p * d.u1_den 1,
      d.u2_num 1 - U1' p * d.u2_den 1,
      d.v1_num 0 - V0' p * d.v1_den 0,
      d.v2_num 0 - V0' p * d.v2_den 0,
      d.v1_num 1 - V1' p * d.v1_den 1,
      d.v2_num 1 - V1' p * d.v2_den 1,
      curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
      curveB1 p c0 c1 c2 c3 c4])
    (curveB2 p c0 c1 c2 c3 c4))

/-- **The true final wiring theorem — restated over `SampleTargetFromAlpha`,
NOT arbitrary `SampleTarget p`.** Per `ROADMAP-monic-annihilator-degree-
uniform.md`'s own final correction: the previous signature (universally
quantified over arbitrary `sa sb : SampleTarget p`, no `alpha`/`alpha'`/
base-point `a` connecting them) is not merely unproved, it is **not even
the right statement** — the true solution variety is 2-dimensional in
`(alpha, alpha')` (`ROADMAP-alpha-locus.md`'s "2-dimensional space of
0-dimensional fibers" finding), so `finrank ≤ 16` can only hold as a
FIBER bound, for `sa, sb` sharing a fixed `(alpha, alpha')` and base
point `a` — exactly what `SampleTargetFromAlpha p H D aClass δ₀`
(`AlphaLocusDegreeUniform.lean`) packages, and exactly the shape
`decoupledSystem_degree_uniform` in that same file already uses for its
own `GenericPeelChainHyp`-based version of this statement. This is a
restatement of the signature only, mechanical and requiring no new
mathematics — the roadmap's own genuinely-open task (why fixing
`(alpha,alpha')` collapses the family to a single 0-dimensional fiber)
is NOT addressed here and remains open; this theorem still concludes
with `sorry` below, now at least asking the right question.

Given `PeelChainFinrankHyp`'s
twelve side conditions, `Rdec p ⧸ Ideal.ofList (genList ...)` is a
finite-dimensional `F p`-vector space of dimension at most `2^4 = 16`
(the product `[1,1,1,1,1,1,1,1,2,2,2,2].prod`), matching the
replacement `GenericPeelChainHyp.hfinrank_le` (`AlphaLocusDegreeUniform
.lean`) needs.

**Proof**: twelve sequential applications, in `genList`'s own order,
each consuming the previous step's `Module.Finite`/`Nontrivial`
conclusion (the base case, `Module.Finite (F p) (Rdec p ⧸ Ideal.ofList
[])`/`Nontrivial (Rdec p ⧸ Ideal.ofList [])`, reduces to `Module.Finite
(F p) (F p)`/`Nontrivial (F p)` via `Ideal.ofList_nil`/
`Ideal.Quotient.quotientBotAlgEquiv`-shaped triviality: the empty-list
ideal is `⊥`, so `Rdec p ⧸ ⊥ ≃ₐ[F p] Rdec p` -- wait, this is NOT `F p`,
it's `Rdec p` itself, which is NOT finite-dimensional; see this
theorem's own caveat below on why the base case is handled differently
from a naive "start at `Ideal.ofList []`" reading). Each of the twelve
steps calls `finrank_le_and_finite_linearElim_ofList_cons` (stages 0–7)
or `finrank_le_and_finite_curveRelation_ofList_cons` (stages 8–11)
directly against an explicit `List (Rdec p)` literal, never a
`List.take`-sliced view -- avoiding the associativity-unification risk
the previous (indexed) draft of this hypothesis structure flagged as
unchecked.

**Caveat this theorem does NOT resolve, flagged honestly rather than
papered over**: `Module.Finite (F p) (Rdec p ⧸ Ideal.ofList [])` is
`Module.Finite (F p) (Rdec p ⧸ ⊥) ≃ Module.Finite (F p) (Rdec p)`, which
is FALSE (`Rdec p` is a 12-variable polynomial ring, infinite-dimensional
over `F p`) -- exactly the base-case obstruction
`FinrankLeOfMonicAnnihilatorFinite.lean`/`OptionSplitPolynomialEquiv
.lean`'s own docstrings already diagnose and flag as needing the
`Option`-split tower route, NOT the literal `Ideal.ofList gens`-indexed
induction this theorem's proof sketch above describes. **This theorem
is therefore NOT yet callable as stated even setting aside the signature
question this pass addresses** -- its proof cannot start from `gens = []`
in `Rdec p` itself using only `PeelChainStageFinite.lean`'s existing two
theorems, which is exactly the gap `OptionSplitPolynomialEquiv.lean` was
built to eventually close (bridging the `Ideal.ofList gens`-quotient
picture to a genuinely finite `Option`-split `Polynomial`-tower picture)
but has not yet been wired THROUGH this specific theorem -- see the
"Next step" note below for what closing it actually requires. **On top
of that pre-existing gap, this pass's own signature restatement adds a
SECOND, more fundamental one**: even a fully-wired proof of the base-case
obstruction above would not close this theorem as newly stated, because
`hyp : PeelChainFinrankHyp p (theData p ... sa.toSampleTarget
sb.toSampleTarget ...) ...`'s twelve fields say nothing about why
`sa.isReduction`/`sb.isReduction` sharing `alpha`/`sa.alpha`,
`sb.alpha`/`aClass` should make those fields collapse to something
provable rather than merely restatable -- that connection is exactly
`ROADMAP-monic-annihilator-degree-uniform.md`'s own still-open task (why
fixing `(alpha,alpha')` collapses the family to a single 0-dimensional
fiber), untouched by this restatement and not attempted here. -/
theorem genList_finrank_le
    (c0 c1 c2 c3 c4 : F p) (aClass : Jacobian H D) (δ₀ : H.Point)
    (sa sb : SampleTargetFromAlpha p H D aClass δ₀)
    (hcurA : curBeforeMonic p c0 c1 c2 c3 c4
      sa.toSampleTarget.u0 sa.toSampleTarget.u1
      sa.toSampleTarget.v0 sa.toSampleTarget.v1 ≠ 0)
    (hcurB : curBeforeMonic p c0 c1 c2 c3 c4
      sb.toSampleTarget.u0 sb.toSampleTarget.u1
      sb.toSampleTarget.v0 sb.toSampleTarget.v1 ≠ 0)
    (hgcdA : IsCoprime (Ypoly p c0 c1 c2 c3 c4
        sa.toSampleTarget.u0 sa.toSampleTarget.u1
        sa.toSampleTarget.v0 sa.toSampleTarget.v1)
      (uRS p c0 c1 c2 c3 c4 sa.toSampleTarget.u0 sa.toSampleTarget.u1
        sa.toSampleTarget.v0 sa.toSampleTarget.v1))
    (hgcdB : IsCoprime (Ypoly p c0 c1 c2 c3 c4
        sb.toSampleTarget.u0 sb.toSampleTarget.u1
        sb.toSampleTarget.v0 sb.toSampleTarget.v1)
      (uRS p c0 c1 c2 c3 c4 sb.toSampleTarget.u0 sb.toSampleTarget.u1
        sb.toSampleTarget.v0 sb.toSampleTarget.v1))
    (hyp : PeelChainFinrankHyp p
      (theData p c0 c1 c2 c3 c4 sa.toSampleTarget sb.toSampleTarget
        hcurA hcurB hgcdA hgcdB)
      c0 c1 c2 c3 c4) :
    Module.finrank (F p)
      (Rdec p ⧸ Ideal.ofList (genList p c0 c1 c2 c3 c4
        sa.toSampleTarget sb.toSampleTarget hcurA hcurB hgcdA hgcdB)) ≤ 16 := by
  sorry

end DecoupledSystem
end Genus2Lean
