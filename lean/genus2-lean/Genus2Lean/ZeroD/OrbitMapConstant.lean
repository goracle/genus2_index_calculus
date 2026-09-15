import Mathlib

/-!
# The orbit-map lemma: a connected group cannot move a point within a finite
# discrete set, via an algebraic (continuous) orbit map

Formalizes the single orbit-map lemma this pass's correction narrows the
whole "why is `Δ` forced to `0`" question down to — see
`MatchingEquationTranslation.lean`'s module docstring for the full context
and for why the naive "`G(Δ)(S)=S` ⟹ `Δ=0`" argument is FALSE in general
(an abstract finite group can act nontrivially on a finite set) and why the
fix genuinely needs `J`'s CONNECTEDNESS as a topological/algebraic-geometry
fact, not just its being a group.

## What this file proves, and what it deliberately leaves as a hypothesis

**Proved in full, using only genuine current-Mathlib4 topology
(`PreconnectedSpace.constant`, confirmed present, not guessed):** if `J` is
a preconnected topological space, `S` a discrete topological space, and
`φ : J → S` is continuous, then `φ` is constant. This is the general
topological fact underlying "a connected algebraic group cannot have a
nonconstant algebraic orbit inside a 0-dimensional target" — stated here at
exactly the level of generality Mathlib already supports, no more.

**Deliberately NOT attempted here, and flagged rather than silently
assumed:** giving `Jacobian H D` (`DivisorClassGroup.lean`) an actual
`TopologicalSpace` instance, still less proving it `PreconnectedSpace` —
checked this pass, not by guessing: this project has ZERO uses of
`TopologicalSpace`/`Scheme`/`PrimeSpectrum`/`IsConnected` anywhere, and
current Mathlib4 has no `AbelianVariety`/Jacobian-of-a-curve machinery to
build on (confirmed by search: `Mathlib.AlgebraicGeometry.EllipticCurve.*`
covers only genus-1 Weierstrass curves, a materially simpler and different
object). Constructing the Zariski topology on `Jacobian H D` and proving it
connected is itself a substantial, independent formalization project — out
of scope for this pass, and arguably for this roadmap's stated goal at all.
This file's theorems therefore take `PreconnectedSpace`/`DiscreteTopology`
as explicit hypotheses on abstract `J`/`S`, so they are complete, usable
theorems the moment someone (a future pass, or a different project) DOES
build that topology, rather than a claim that it already exists here.

## The two theorems

1. `orbit_map_constant_of_preconnected_of_discrete`: the general topology
   fact above, proved outright.
2. `delta_eq_zero_of_orbit_constant_and_faithful`: given `φ` constant
   (fact 1's conclusion, or hypothesized directly) AND a `Faithful`-style
   hypothesis that `φ` only agrees with itself at `0` when the underlying
   `Δ` is `0`, concludes `Δ = 0`. This packages the "faithfulness of the
   translation action" step ChatGPT's writeup calls out explicitly as a
   SEPARATE, not-yet-justified ingredient beyond orbit-constancy itself —
   left as a hypothesis here for the same reason, not proved, since it is
   a fact about `Reduce`'s specific Mumford-coordinate construction, not
   about `J`'s group or topological structure.
-/

namespace Genus2Lean
namespace HyperellipticPolynomial

/-! ## Fact: a preconnected space maps constantly into a discrete space -/

/-- **A connected space cannot have a nonconstant continuous map into a
discrete space.** Pure general topology — `PreconnectedSpace.constant`
(Mathlib, `Mathlib.Topology.Connected.TotallyDisconnected`), restated here
under the names this project's application (the orbit map
`Δ ↦ G(Δ) • s`) actually needs, so the application site doesn't have to
know Mathlib's exact lemma name. Takes the orbit map `φ : J → S` and its
continuity as hypotheses, rather than constructing `φ` itself — this file
is deliberately agnostic about where `φ`/its continuity come from (an
actual group action, a bare function, etc.), matching the "for each
individual `s`, it is enough to have `φₛ : J → S` a regular map" scoping
this pass settled on. -/
theorem orbit_map_constant_of_preconnected_of_discrete
    {J : Type*} [TopologicalSpace J] [PreconnectedSpace J]
    {S : Type*} [TopologicalSpace S] [DiscreteTopology S]
    (φ : J → S) (hφ : Continuous φ) (x y : J) :
    φ x = φ y :=
  PreconnectedSpace.constant ‹PreconnectedSpace J› hφ (x := x) (y := y)

/-! ## Fact: constancy of the orbit map, plus faithfulness, forces `Δ = 0` -/

/-- **Given the orbit map is constant (fact above) AND the translation
action is faithful at the basepoint, the acting element is forced to be
the identity.**

`hconst : φ Δ = φ 0` is exactly `orbit_map_constant_of_preconnected_of_discrete`'s
conclusion specialized to `y := 0` (the identity of `J`, matching `φ`'s own
role as the orbit map `Δ ↦ G(Δ) • s` — `φ 0 = s` is `G`'s identity axiom).
`hfaithful : φ Δ = φ 0 → Δ = 0` is the SEPARATE, genuinely project-specific
ingredient the module docstring flags as not proved here: it is a
statement about `Reduce`'s Mumford-coordinate construction (a nonzero
Jacobian translation genuinely changes the associated divisor data), not
about `J`'s group or topological structure, so it cannot be derived from
`PreconnectedSpace`/`DiscreteTopology` alone and is left as an explicit
hypothesis rather than asserted. -/
theorem delta_eq_zero_of_orbit_constant_and_faithful
    {J : Type*} [Zero J] {S : Type*}
    (φ : J → S) (Δ : J)
    (hconst : φ Δ = φ 0)
    (hfaithful : φ Δ = φ 0 → Δ = 0) :
    Δ = 0 :=
  hfaithful hconst

/-- **Composed form**: given `J` preconnected, `S` discrete, the orbit map
`φ` continuous, and faithfulness at the basepoint, `Δ = 0` follows in one
call — the full chain `orbit_map_constant_of_preconnected_of_discrete` then
`delta_eq_zero_of_orbit_constant_and_faithful`, matching ChatGPT's own
"complete conceptual argument" summary line for line, modulo the
`PreconnectedSpace (Jacobian H D)`/`DiscreteTopology S` instances this
file's module docstring flags as not yet constructed. -/
theorem delta_eq_zero_of_preconnected_discrete_faithful
    {J : Type*} [TopologicalSpace J] [PreconnectedSpace J] [Zero J]
    {S : Type*} [TopologicalSpace S] [DiscreteTopology S]
    (φ : J → S) (hφ : Continuous φ) (Δ : J)
    (hfaithful : φ Δ = φ 0 → Δ = 0) :
    Δ = 0 :=
  delta_eq_zero_of_orbit_constant_and_faithful φ Δ
    (orbit_map_constant_of_preconnected_of_discrete φ hφ Δ 0) hfaithful

end HyperellipticPolynomial
end Genus2Lean
