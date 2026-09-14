import Mathlib

/-!
# `finrank` of a principal quotient transports forward along a surjection

New this pass. Small, generic, standalone lemma — no `Rdec p`/`Idx`/
`genList` content — split out because it is exactly the reusable piece
`ROADMAP-monic-annihilator-degree-uniform.md`'s shared-pivot elimination
step needs and does not yet have: `SharedPivotResultantElim.lean`'s
theorem `finrank_le_of_shared_linear_elim_pair` bounds `finrank k B` by
`finrank k (A ⧸ Ideal.span {resultant})` for an ABSTRACT algebra `A`, but
wiring that bound to the literal peel chain needs `A` itself to be a
further quotient of an even earlier prefix ring `A0` (i.e. `A := A0 ⧸
Ideal.span {g1}`, after the first of the two shared-pivot generators has
already been imposed) — so the bound actually available in terms of the
literal peel chain's own base ring is stated over `A0`, not `A`, and
needs transporting across the surjection `A0 ↠ A`.

**The fact**: if `f : A →ₐ[k] A1` is a surjective `k`-algebra map and
`r : A`, then `Module.finrank k (A1 ⧸ Ideal.span {f r}) ≤ Module.finrank
k (A ⧸ Ideal.span {r})`. Proof: `f` induces a surjective `k`-algebra map
`A ⧸ Ideal.span {r} ↠ A1 ⧸ Ideal.span {f r}` (the image of `r` maps to
`0`, by construction, so `f` factors through the quotient via
`Ideal.Quotient.lift`), and `finrank` only decreases under a further
surjection (`LinearMap.finrank_le_finrank_of_surjective`) — the same
"factor through the quotient, transport `finrank` along the induced
surjection" shape `SharedPivotResultantElim.lean`'s own tail end already
uses once; this file states it as its own standalone, reusable fact
rather than inlining the same construction a second time at every call
site that needs it.

**`[Module.Finite k A]` added this pass**: `LinearMap.finrank_le_finrank_
of_surjective` needs `Module.Finite k` of the DOMAIN
(`A ⧸ Ideal.span {r}`) to even typecheck/hold (the original build error:
`failed to synthesize instance of type class Module.Finite k (A ⧸ Ideal.
span {r})` — the fact is false without some finiteness assumption
somewhere, e.g. take `A` infinite-dimensional with `r = 0`: both sides
are infinite-dimensional and the inequality is vacuous/unhelpful, but
Lean can't even STATE `Module.finrank` meaningfully as a bound without
`Module.Finite` in scope for the comparison to be about actual
dimensions rather than the junk-value `0` `finrank` returns on
infinite-dimensional modules — and indeed `finrank_le_finrank_of_surjective`
is stated for finite-dimensional domains specifically). Adding
`[Module.Finite k A]` (matching what every call site already has in
scope — e.g. `SharedPivotStageWiring.lean`'s own `A := Rdec p ⧸
Ideal.ofList gens` carries `[Module.Finite (F p) (Rdec p ⧸ Ideal.ofList
gens)]` as an explicit hypothesis already) gives `Module.Finite k (A ⧸
Ideal.span {r})` for free, since a quotient of a finite module is finite
(`Module.Finite.quotient` / `Module.Finite.of_surjective` applied to
`Ideal.Quotient.mk`). -/

namespace Genus2Lean

variable {k A A1 : Type*} [Field k] [CommRing A] [CommRing A1]
  [Algebra k A] [Algebra k A1] [Module.Finite k A]

/-- **The reusable transport fact.** A surjective `k`-algebra map `f : A
→ₐ[k] A1`, applied to a principal-ideal quotient's generator, transports
a `finrank` bound forward: `finrank k (A1 ⧸ span {f r}) ≤ finrank k (A ⧸
span {r})`. -/
theorem finrank_le_of_span_surjective (f : A →ₐ[k] A1) (hf : Function.Surjective f) (r : A) :
    Module.finrank k (A1 ⧸ Ideal.span ({f r} : Set A1)) ≤
      Module.finrank k (A ⧸ Ideal.span ({r} : Set A)) := by
  -- `ψ : A ⧸ span {r} →+* A1 ⧸ span {f r}`, the induced map: `f`
  -- composed with `mk`, which sends `r` to `0` by construction, so
  -- factors through `Ideal.Quotient.lift`.
  have hmem : ∀ x ∈ Ideal.span ({r} : Set A),
      (Ideal.Quotient.mk (Ideal.span ({f r} : Set A1))).comp f.toRingHom x = 0 := by
    intro x hx
    rw [Ideal.mem_span_singleton] at hx
    obtain ⟨c, rfl⟩ := hx
    show Ideal.Quotient.mk (Ideal.span ({f r} : Set A1)) (f (r * c)) = 0
    rw [map_mul]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.mem_span_singleton.mpr ⟨f c, rfl⟩
  set ψ : (A ⧸ Ideal.span ({r} : Set A)) →+* A1 ⧸ Ideal.span ({f r} : Set A1) :=
    Ideal.Quotient.lift (Ideal.span ({r} : Set A))
      ((Ideal.Quotient.mk (Ideal.span ({f r} : Set A1))).comp f.toRingHom) hmem with hψ_def
  have hψ_surj : Function.Surjective ψ := by
    intro b
    obtain ⟨b1, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨a, rfl⟩ := hf b1
    refine ⟨Ideal.Quotient.mk (Ideal.span ({r} : Set A)) a, ?_⟩
    rw [hψ_def]
    exact Ideal.Quotient.lift_mk _ _ _
  have hψ_lin : ∀ (c : k) (x : A ⧸ Ideal.span ({r} : Set A)), ψ (c • x) = c • ψ x := by
    have hcomm : ∀ a : A, ψ (algebraMap A (A ⧸ Ideal.span ({r} : Set A)) a) =
        algebraMap A1 (A1 ⧸ Ideal.span ({f r} : Set A1)) (f a) := by
      intro a
      rw [hψ_def]
      exact Ideal.Quotient.lift_mk (Ideal.span ({r} : Set A))
        ((Ideal.Quotient.mk (Ideal.span ({f r} : Set A1))).comp f.toRingHom) hmem
    intro c x
    rw [Algebra.smul_def, Algebra.smul_def, map_mul,
      IsScalarTower.algebraMap_apply k A (A ⧸ Ideal.span ({r} : Set A)),
      IsScalarTower.algebraMap_apply k A1 (A1 ⧸ Ideal.span ({f r} : Set A1)), hcomm, f.commutes]
  set ψₗ : (A ⧸ Ideal.span ({r} : Set A)) →ₗ[k] A1 ⧸ Ideal.span ({f r} : Set A1) :=
    { toFun := ψ, map_add' := map_add ψ, map_smul' := hψ_lin } with hψₗ_def
  have hψₗ_surj : Function.Surjective ψₗ := hψ_surj
  -- `Module.Finite k (A ⧸ Ideal.span {r})`: a quotient of the finite
  -- `k`-module `A` (via `[Module.Finite k A]`, added this pass) by
  -- `Ideal.Quotient.mk`, which is `k`-linear and surjective.
  have hfin : Module.Finite k (A ⧸ Ideal.span ({r} : Set A)) :=
    Module.Finite.of_surjective
      (Ideal.Quotient.mkₐ k (Ideal.span ({r} : Set A))).toLinearMap
      (Ideal.Quotient.mk_surjective)
  exact LinearMap.finrank_le_finrank_of_surjective hψₗ_surj

end Genus2Lean
