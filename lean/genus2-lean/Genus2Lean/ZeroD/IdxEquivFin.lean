import Mathlib
import Genus2Lean.ZeroD.DecoupledSystemRegular

/-!
# `Idx ≃ Fin 12`, in the peel order the finiteness Assembly needs

**Why this file exists.** `ROADMAP-monic-annihilator-degree-uniform.md`'s
"CORRECTION, later pass" section (ChatGPT-consulted fix for the
base-case gap `GenListFinrankAssembly.lean`'s `sorry` exposed) calls for
reindexing `Idx` through `Fin 12` and using Mathlib's own
`MvPolynomial.finSuccEquiv` to peel one variable at a time, rather than
hand-rolling an `Idx ≃ Option (Option (...))` chain. This file supplies
step 1 of that plan: the single fixed equivalence everything downstream
is stated against.

**The order is NOT `Idx`'s own constructor order** (`wa1,wa2,wb1,wb2,
a2,a1,b2,b1,U0,U1,V0,V1`, `DecoupledSystemRegular.lean`'s `dec_gens`
order, preserved from the original Julia script). It is the TRIANGULAR
peel order this roadmap's Open Questions section already resolved:
curve-relation variables (`wa1,wa2,wb1,wb2` — the "capital `W`" square-root
witnesses for the two curve relations at each of the two sample points)
must be peeled BEFORE the matching-generator variables (`U0,U1,V0,V1`),
because `FuList`/`FvList`'s own coefficients (`u1_num i` etc.) depend on
the curve-relation variables — peeling `U0,U1,V0,V1` first would leave a
NON-constant coefficient in the "already eliminated" ring at the point
`finSuccEquiv`'s monic-annihilator step needs a genuinely constant
leading coefficient. The four curve-SAMPLE variables `a1,a2,b1,b2` (the
free field-element inputs the curve relations `wa1²=f(a1)` etc. are
stated in terms of) are NOT separately peeled by any of this project's
12 generators — `genList` has exactly 12 generators for 12 `Idx` values,
and `a1,a2,b1,b2` are peeled ALONGSIDE their respective `wa`/`wb`
variable, one curve relation at a time (`curveA1` peels `wa1` while
witnessing a relation in `a1`, `curveA2` peels `wa2` while witnessing a
relation in `a2`, etc. — see `PeelChainAssembly.lean`'s own
`curveRelationGen`/`curveFImage` for the precise generic-`w`/`x` shape).
So the peel order below places EACH curve variable immediately before
its own sample variable, matching the order `curveA1,curveA2,curveB1,
curveB2` are actually applied in `genList`'s stated tail — this keeps
each curve-relation stage's own coefficient genuinely constant in the
ring already built by the time that stage's `finSuccEquiv` step fires,
without needing to further reorder within the curve block itself.

**Chosen order** (`Fin 12` index ↦ `Idx` constructor):
`0↦wa1, 1↦a1, 2↦wa2, 3↦a2, 4↦wb1, 5↦b1, 6↦wb2, 7↦b2, 8↦U0, 9↦U1, 10↦V0,
11↦V1` — curve relations `curveA1,curveA2,curveB1,curveB2` (in that
order, matching `genList`'s own stated tail order) each contributing
their `w`-variable immediately followed by their sample-point variable,
then the eight matching-generator variables in `FuList ++ FvList`'s own
stated order (`U0` appears in `Fu0,Fu1`; `U1` in `Fu2,Fu3`; `V0` in
`Fv0,Fv1`; `V1` in `Fv2,Fv3`).

**Built as an explicit `Equiv`, both directions `rfl`/`decide`-checkable
pattern matches** — no reliance on `Fintype`-derived machinery picking
some unspecified order (which would not match this file's own
documented triangularity requirement). -/

namespace Genus2Lean
namespace DecoupledSystem

open Idx

/-- Forward direction: each `Idx` constructor to its assigned `Fin 12`
value, in the triangular peel order documented above. -/
def idxToFin : Idx → Fin 12
  | wa1 => 0
  | a1 => 1
  | wa2 => 2
  | a2 => 3
  | wb1 => 4
  | b1 => 5
  | wb2 => 6
  | b2 => 7
  | U0 => 8
  | U1 => 9
  | V0 => 10
  | V1 => 11

/-- Backward direction, the explicit inverse table. -/
def finToIdx : Fin 12 → Idx
  | 0 => wa1
  | 1 => a1
  | 2 => wa2
  | 3 => a2
  | 4 => wb1
  | 5 => b1
  | 6 => wb2
  | 7 => b2
  | 8 => U0
  | 9 => U1
  | 10 => V0
  | 11 => V1

/-- **The fixed peel-order equivalence.** Both round-trips are closed by
`decide` (both `Idx` and `Fin 12` are finite with decidable equality, and
each direction is a finite case-split matching a finite case-split — no
induction needed). -/
def idxEquivFin : Idx ≃ Fin 12 where
  toFun := idxToFin
  invFun := finToIdx
  left_inv := by decide
  right_inv := by decide

@[simp] theorem idxEquivFin_wa1 : idxEquivFin wa1 = 0 := rfl
@[simp] theorem idxEquivFin_a1 : idxEquivFin a1 = 1 := rfl
@[simp] theorem idxEquivFin_wa2 : idxEquivFin wa2 = 2 := rfl
@[simp] theorem idxEquivFin_a2 : idxEquivFin a2 = 3 := rfl
@[simp] theorem idxEquivFin_wb1 : idxEquivFin wb1 = 4 := rfl
@[simp] theorem idxEquivFin_b1 : idxEquivFin b1 = 5 := rfl
@[simp] theorem idxEquivFin_wb2 : idxEquivFin wb2 = 6 := rfl
@[simp] theorem idxEquivFin_b2 : idxEquivFin b2 = 7 := rfl
@[simp] theorem idxEquivFin_U0 : idxEquivFin U0 = 8 := rfl
@[simp] theorem idxEquivFin_U1 : idxEquivFin U1 = 9 := rfl
@[simp] theorem idxEquivFin_V0 : idxEquivFin V0 = 10 := rfl
@[simp] theorem idxEquivFin_V1 : idxEquivFin V1 = 11 := rfl

end DecoupledSystem
end Genus2Lean
