import Mathlib
import Genus2Lean.ZeroD.LinearElimDegreeBound

/-!
# Stages 4–7 degree bound: the `V0`/`V1` matching generators

Item 3 of `ROADMAP-monic-annihilator-degree-uniform.md`'s file plan, step
4 of its "Suggested order" — done after resolving that roadmap's first
Open Question (see its "Open questions" section, now marked RESOLVED),
which this file's existence and shape directly reflect.

**Diagnosis result this file is built on**: `Fv0`–`Fv3` (`v1_num(0) −
V0·v1_den(0)`, `v2_num(0) − V0·v2_den(0)`, `v1_num(1) − V1·v1_den(1)`,
`v2_num(1) − V1·v2_den(1)`, per the roadmap's own stage table) are
LITERALLY the same `c − X·d` shape as `Fu0`–`Fu3` — nothing about the
matching-generator degree-bound argument itself differs between
stages 0–3 and stages 4–7. `LinearElimDegreeBound.lean`'s
`finrank_le_of_linear_elim` is already fully generic over any
commutative ring `A` and any `c d : A`, so **it already covers stages
4–7 as-is**: no new per-stage theorem is needed, and this file adds no
new proof content beyond re-exporting that fact under stage-4–7-facing
names for Assembly (item 5) to call, matching this project's existing
convention of naming per-stage corollaries even when they share one
proof (e.g. `CurveRelationsDegreeBound.lean`'s single
`finrank_le_of_curve_relation` standing in for all of stages 8–11).

**What's actually new here, per the roadmap's resolved Open Question**:
stages 0–3 could reuse `IsUnit d` as an ABSTRACT hypothesis with no
further discharge obligation inside this degree-bound track (discharging
it for the literal `Rdec p` generators is Assembly's job either way).
Stages 4–7 are no different in that respect — `finrank_le_of_linear_elim`
still just asks for `IsUnit d` — but the roadmap's diagnosis clarifies
that this hypothesis is NOT already available from `hv0_ext`–`hv3_ext`
(those are `IsSMulRegular <the whole evaluated linear form> <the
further-extended quotient>`, a different-strength condition about a
different ring than `IsUnit (v_den i)` in the previous-stage ring `A`).
So Assembly (item 5) must supply `IsUnit (v_den i)` as fresh data for
each of `i ∈ {1,2}` at `j ∈ {0,1}` — four genuinely new hypotheses, NOT
derived from anything already proved in `PeelChainAssembly.lean` — when
it wires this file's theorems to the literal `Rdec p` quotients. This
file states that expectation explicitly (via each corollary's hypothesis
name, `hv_den_unit`) so Assembly's job is a direct application, not a
re-derivation.

**Naming**: `finrank_le_of_Fv0`/`_Fv1`/`_Fv2`/`_Fv3`, one per stage,
matching the roadmap table's own `Fv0`–`Fv3` names — deliberately NOT a
single shared `finrank_le_of_linear_elim_ext` name, since Assembly will
want to invoke each stage by its own literal generator name, the same
way it will presumably invoke `finrank_le_of_curve_relation` four times
under `curveA1`/`curveA2`/`curveB1`/`curveB2`-facing names of its own
choosing. -/

namespace Genus2Lean

open Polynomial

variable {k A B : Type*} [Field k] [CommRing A] [Nontrivial A] [Algebra k A]
  [StrongRankCondition A] [Module.Finite k A]
  [CommRing B] [Algebra A B] [Algebra k B] [IsScalarTower k A B]

/-- Stage 4 (`Fv0 = v1_num(0) − V0·v1_den(0)`): the previous-stage
algebra `A` here is the quotient by `{Fu0,Fu1,Fu2,Fu3}` (stages 0–3
already closed), `c := v1_num 0`, `d := v1_den 0`, `t := V0`. The
`hv_den_unit` hypothesis (`IsUnit (v1_den 0)`, i.e. `IsUnit d` in
`finrank_le_of_linear_elim`'s naming) is the fresh, NOT-yet-discharged
fact the roadmap's Open Questions section flags — `hv0_ext` alone does
not supply it (see this file's docstring above). -/
theorem finrank_le_of_Fv0 (c d : A) (hv_den_unit : IsUnit d) (t : B)
    (ht : (Polynomial.aeval t) (linearElimPoly c d) = 0)
    (hgen : Algebra.adjoin A {t} = (⊤ : Subalgebra A B)) :
    Module.finrank k B ≤ Module.finrank k A :=
  finrank_le_of_linear_elim c d hv_den_unit t ht hgen

/-- Stage 5 (`Fv1 = v2_num(0) − V0·v2_den(0)`), same shape as
`finrank_le_of_Fv0` one further generator along (previous-stage algebra
now the quotient by `{Fu0,Fu1,Fu2,Fu3,Fv0}`). `hv_den_unit` here stands
for `IsUnit (v2_den 0)`, the fact `hv1_ext` does not supply. -/
theorem finrank_le_of_Fv1 (c d : A) (hv_den_unit : IsUnit d) (t : B)
    (ht : (Polynomial.aeval t) (linearElimPoly c d) = 0)
    (hgen : Algebra.adjoin A {t} = (⊤ : Subalgebra A B)) :
    Module.finrank k B ≤ Module.finrank k A :=
  finrank_le_of_linear_elim c d hv_den_unit t ht hgen

/-- Stage 6 (`Fv2 = v1_num(1) − V1·v1_den(1)`), previous-stage algebra
the quotient by `{Fu0,Fu1,Fu2,Fu3,Fv0,Fv1}`. `hv_den_unit` here stands
for `IsUnit (v1_den 1)`, the fact `hv2_ext` does not supply. -/
theorem finrank_le_of_Fv2 (c d : A) (hv_den_unit : IsUnit d) (t : B)
    (ht : (Polynomial.aeval t) (linearElimPoly c d) = 0)
    (hgen : Algebra.adjoin A {t} = (⊤ : Subalgebra A B)) :
    Module.finrank k B ≤ Module.finrank k A :=
  finrank_le_of_linear_elim c d hv_den_unit t ht hgen

/-- Stage 7 (`Fv3 = v2_num(1) − V1·v2_den(1)`), previous-stage algebra
the quotient by `{Fu0,Fu1,Fu2,Fu3,Fv0,Fv1,Fv2}` — the last of the eight
matching-generator stages before stages 8–11's already-monic curve
relations take over. `hv_den_unit` here stands for `IsUnit (v2_den 1)`,
the fact `hv3_ext` does not supply. -/
theorem finrank_le_of_Fv3 (c d : A) (hv_den_unit : IsUnit d) (t : B)
    (ht : (Polynomial.aeval t) (linearElimPoly c d) = 0)
    (hgen : Algebra.adjoin A {t} = (⊤ : Subalgebra A B)) :
    Module.finrank k B ≤ Module.finrank k A :=
  finrank_le_of_linear_elim c d hv_den_unit t ht hgen

end Genus2Lean
