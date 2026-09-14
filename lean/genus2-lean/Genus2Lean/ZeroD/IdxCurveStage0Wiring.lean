import Mathlib
import Genus2Lean.ZeroD.FinSuccStageGenerators
import Genus2Lean.ZeroD.IdxEquivFin
import Genus2Lean.ZeroD.GenListTriangularReorder

/-!
# Item (d), the true remainder: `Idx`-specific `hstep` wiring, stage 0
# (`curveA1`, peeling `wa1` at `n = 0`)

`ROADMAP-monic-annihilator-degree-uniform.md`'s "Not yet done, the true
remainder of item (d)" lists four steps; this file starts step 2/3's
actual `Idx`-specific specialization — the one piece explicitly flagged
as "genuinely not yet attempted." Rather than commit to all twelve
stages' wiring at once (high risk of a composition mistake with no REPL
access to catch it), this file does exactly ONE stage, chosen as the
cleanest possible starting point: stage 0 of the triangular order
(`genListTriangular`'s head, `curveA1`), which is also `n = 0` — the base
case of the `Fin n`-indexed peel, where there is no prior `rename
Fin.succ` composition to track yet. Later stages compose `rename
Fin.succ` once per prior stage; this file establishes the pattern at the
one stage where that composition is vacuous, to be extended stage by
stage rather than attempted in bulk.

**What this file connects.** `FinSuccStageGenerators.lean`'s
`finSuccCurveRelationGen_hstep_data` is generic over `n`/`q`; it produces
`finrank_le_finSucc_peel_chain`'s `hstep` witness given a curve-value `q
: MvPolynomial (Fin n) K` and a non-unit hypothesis on the RAW generator
`finSuccCurveRelationGen n q = X 0 ^ 2 - rename Fin.succ q`. At `n = 0`,
`MvPolynomial (Fin 0) K ≃ₐ[K] K` (`isEmptyAlgEquiv`) has no free
variables, so the natural specialization is `q := 0` (`curveA1`'s
constant term of `f` evaluated where no curve-sample variable exists
yet) -- **this is the wrong reading**, flagged below rather than forced:
`curveA1`'s actual shape is `X wa1 ^ 2 - f(X a1)`, a relation between TWO
`Idx` variables (`wa1` AND `a1`), not one. So stage 0 of the literal
`Idx` peel chain is NOT `finSuccCurveRelationGen`'s shape at `n = 0`
directly -- it is `finSuccCurveRelationGen` at `n = 1` (after `a1` alone
has already been peeled with NO generator of its own, i.e. `a1` is
peeled "for free" as a bystander variable, only pinned down jointly with
`wa1` by `curveA1` itself). This matches `IdxEquivFin.lean`'s own table
placing `a1` at `Fin`-index `1`, immediately after `wa1` at index `0` --
**so `curveA1` is genuinely a TWO-VARIABLE step of the `Fin`-indexed
peel, not a one-variable `finSuccEquiv` application**, and
`finrank_le_finSucc_peel_chain`'s `hstep` (which peels exactly one `Fin`
index per call) cannot be fed `curveA1` directly at either `i = 0` or
`i = 1` alone.

**Honest conclusion, not papered over, CORRECTED after a follow-up pass
(see `ROADMAP-monic-annihilator-degree-uniform.md`'s later "Correction"
entry for the full writeup)**: the first pass here proposed generalizing
`hstep` to a `k`-variable-per-call step as the fix. That proposal is now
understood to target the wrong layer. Checked directly: even a
two-variable joint step is not just an interface mismatch but would need
an intermediate `Module.Finite` fact that is genuinely FALSE — `curveA1`
alone, with `wa1` and `a1` the only two variables in play, defines an
infinite affine curve, not a finite set, so no reshaping of `hstep`
(`k`-ary or otherwise) can supply the needed finiteness at that
intermediate point. This is not special to the curve stages in isolation
either: `genList`'s actual pivot structure (traced against all 12
generators, not just `curveA1`) shows `U0` is the shared pivot of BOTH
`Fu0` and `Fu1` (disjoint a-side/b-side coefficients), not a clean
one-generator-one-pivot triangular system at all — solving for `U0`
needs `Fu0`/`Fu1`'s CROSS-RESULTANT to vanish first (`CrossNondegenerate`
territory, `MvPolynomialSharedTargetSolve.lean`), which eliminates `U0`
rather than treating it as an ordinary sequential pivot. **The
`FinSuccPeelChainFinrank.lean`/`FinSuccPeelChainFold.lean` one-`Fin`-
slot-per-call architecture itself is very likely the wrong shape for
this specific 12-generator system, not merely under-generalized** — the
right target is a SIMULTANEOUS/triangular-block finiteness argument
(eliminate `U0,U1,V0,V1` via their four resultants first, reducing to an
honest one-variable-at-a-time monic peel of `wa1,wa2,wb1,wb2` over the
remaining `a1,a2,b1,b2` coefficient block), not a sharper version of the
sequential one-prefix-at-a-time induction. This file's own stage-0
attempt is superseded by that broader finding; it is kept as the
concrete example that first surfaced the issue, not as a partial
solution to build on directly. -/

namespace Genus2Lean
namespace DecoupledSystem

open Idx

/-- **Sanity check confirming the gap above is real, not a
misreading**: `curveRelationGen`'s two `Idx` arguments are genuinely
different variables at stage 0 (`wa1 ≠ a1`), so `curveA1` cannot be
expressed as a function of `X wa1` alone -- confirming a single
`finSuccEquiv`-style one-variable peel step cannot supply it. -/
theorem wa1_ne_a1 : wa1 ≠ a1 := by decide

end DecoupledSystem
end Genus2Lean
