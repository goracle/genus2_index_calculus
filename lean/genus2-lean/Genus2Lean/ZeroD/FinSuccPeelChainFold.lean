import Mathlib
import Genus2Lean.ZeroD.FinSuccPeelChainFinrank

/-!
# Assembly, item (c): the `Fin n`-indexed n-stage fold, genuine `n = 0` base case

The second of the two files `FinSuccPeelChainFinrank.lean`'s own module
docstring calls out as still to come. That file supplies ONE step of the
peel (`finrank_le_and_finite_finSucc_peel`: go from `Fin n` with a
generator list `gens` to `Fin (n+1)` with `gens' ++ [g]`, given the new
generator's monic-annihilator witness data). This file chains `n` such
steps, starting the induction at the ACTUAL base case `n = 0`,
`gens = []` — which is now genuinely valid, unlike the old
`Ideal.ofList`-prefix-of-`Rdec p` approach
(`ROADMAP-monic-annihilator-degree-uniform.md`'s "CORRECTION, later
pass" section): `MvPolynomial (Fin 0) K` has no free variables at all
(`Fin 0` is empty), so it genuinely is finite-dimensional over `K` (in
fact `finrank = 1`), via `MvPolynomial.isEmptyAlgEquiv K (Fin 0) :
MvPolynomial (Fin 0) K ≃ₐ[K] K`.

**Interface shape, mirroring `PeelChainAssemblyFinrank.lean`'s
`finrank_le_and_finite_of_append`**: that file's `hstep` is a single
proof recipe, callable again at whatever prefix the induction has
reached so far, because each stage's own hypotheses are only available
once the induction actually gets there. The same reasoning applies
here, one level more dependent: at stage `i : Fin n` the generator `g`,
its monic image `G`, and every hypothesis about them live in
`MvPolynomial (Fin (i+1)) K`/`Polynomial (MvPolynomial (Fin i) K ⧸
Ideal.ofList gens)` for whatever `gens` the induction has accumulated by
that point — a genuinely dependent shape, not a fixed one repeated `n`
times. So `hstep` here is a single dependently-typed proof recipe,
quantified over an arbitrary already-reached stage `i` and prefix
`gens : List (MvPolynomial (Fin i) K)`, callable once per step of the
outer induction on `n`.

**Scope, matching `FinSuccPeelChainFinrank.lean`'s own stated split**:
fully generic over `n`/`K`/the per-stage recipe, zero `Idx`/`Rdec p`/
`theData` content. The `Idx`-specific wiring (item (d), transporting
`genList`'s twelve literal generators across `idxEquivFin`/`renameEquiv`
to actually discharge `GenListFinrankAssembly.lean`'s `genList_finrank_le`
`sorry`) is separate, later work — this file does not touch `Idx`/`Rdec
p` at all. -/

namespace Genus2Lean

open Polynomial MvPolynomial

variable {K : Type*} [Field K]

/-- **The `n`-stage fold, `Fin`-indexed, genuine `n = 0` base case.**
`hstep` is the caller-supplied per-stage recipe: given ANY already-reached
stage `i` and prefix `gens : List (MvPolynomial (Fin i) K)` with
`Module.Finite`/`Nontrivial` already established, together with a choice
of next generator `g`, its monic image `G` under
`finSuccSplitQuotientAlgEquiv`, and the two side facts
`finrank_le_and_finite_finSucc_peel` needs (`g`'s image is a non-unit,
and `hg` pins down `G` as `g`'s image under the split), `hstep` produces
the multiplier `d i` for that stage. `Module.finrank` at `Fin n` is then
bounded by the product of all `n` multipliers.

**Why `hstep` returns a `Σ`-style bundle (`g`, `G`, proofs) rather than
taking them as separate arguments**: at each step of the induction the
CALLER (this lemma's proof, not the eventual `Idx`-side user) must
supply `g`/`G` itself — there is no fixed formula for them at this level
of genericity; that data comes from item (d)'s eventual concrete
per-stage generators. So `hstep` is stated as producing a witness
(everything needed for `finrank_le_and_finite_finSucc_peel`'s hypotheses
to be satisfiable at that stage), existentially, rather than as a
non-existential fact about pre-supplied fixed data. -/
theorem finrank_le_finSucc_peel_chain
    (n : ℕ)
    (hstep : ∀ (i : ℕ) (gens : List (MvPolynomial (Fin i) K)),
      Module.Finite K (MvPolynomial (Fin i) K ⧸ Ideal.ofList gens) →
      Nontrivial (MvPolynomial (Fin i) K ⧸ Ideal.ofList gens) →
      ∃ (g : MvPolynomial (Fin (i + 1)) K)
        (G : Polynomial (MvPolynomial (Fin i) K ⧸ Ideal.ofList gens)),
        G.Monic ∧
        (¬ IsUnit (Ideal.Quotient.mk
          (Ideal.ofList (gens.map (MvPolynomial.rename Fin.succ))) g)) ∧
        finSuccSplitQuotientAlgEquiv i gens
          (Ideal.Quotient.mk (Ideal.ofList (gens.map (MvPolynomial.rename Fin.succ))) g) = G) :
    ∃ (gensN : List (MvPolynomial (Fin n) K)) (bound : ℕ),
      Module.Finite K (MvPolynomial (Fin n) K ⧸ Ideal.ofList gensN) ∧
      Nontrivial (MvPolynomial (Fin n) K ⧸ Ideal.ofList gensN) ∧
      Module.finrank K (MvPolynomial (Fin n) K ⧸ Ideal.ofList gensN) ≤ bound := by
  induction n with
  | zero =>
    -- Genuine base case: `MvPolynomial (Fin 0) K ≃ₐ[K] K`, so
    -- `Ideal.ofList []`'s quotient (which is `MvPolynomial (Fin 0) K ⧸ ⊥`,
    -- itself `≃ₐ[K] MvPolynomial (Fin 0) K`) has `finrank = 1`.
    refine ⟨[], 1, ?_, ?_, ?_⟩
    · have hbot : Ideal.ofList ([] : List (MvPolynomial (Fin 0) K)) = ⊥ := Ideal.ofList_nil
      rw [hbot]
      exact Module.Finite.equiv
        ((AlgEquiv.quotientBot K (MvPolynomial (Fin 0) K)).trans
          (MvPolynomial.isEmptyAlgEquiv K (Fin 0))).symm.toLinearEquiv
    · have hbot : Ideal.ofList ([] : List (MvPolynomial (Fin 0) K)) = ⊥ := Ideal.ofList_nil
      rw [hbot]
      exact ((AlgEquiv.quotientBot K (MvPolynomial (Fin 0) K)).trans
        (MvPolynomial.isEmptyAlgEquiv K (Fin 0))).toEquiv.nontrivial
    · have hbot : Ideal.ofList ([] : List (MvPolynomial (Fin 0) K)) = ⊥ := Ideal.ofList_nil
      rw [hbot]
      rw [LinearEquiv.finrank_eq
        ((AlgEquiv.quotientBot K (MvPolynomial (Fin 0) K)).trans
          (MvPolynomial.isEmptyAlgEquiv K (Fin 0))).toLinearEquiv]
      -- `Module.finrank K K = 1`: a standard fact, closed by `simp`
      -- rather than naming a specific lemma (several candidate names
      -- exist across Mathlib versions for "finrank of a field over
      -- itself"; `simp` finds whichever is currently tagged).
      simp
  | succ m ih =>
    obtain ⟨gensM, boundM, hfinM, hnontrivM, hboundM⟩ := ih
    obtain ⟨g, G, hG, hg_ne, hg⟩ := hstep m gensM hfinM hnontrivM
    obtain ⟨hfinExt, hnontrivExt, hboundExt⟩ :=
      finrank_le_and_finite_finSucc_peel m gensM g G hG hfinM hg_ne hg
    refine ⟨gensM.map (MvPolynomial.rename Fin.succ) ++ [g],
      G.natDegree * boundM, hfinExt, hnontrivExt, ?_⟩
    calc Module.finrank K (MvPolynomial (Fin (m + 1)) K ⧸
        Ideal.ofList (gensM.map (MvPolynomial.rename Fin.succ) ++ [g]))
        ≤ G.natDegree * Module.finrank K (MvPolynomial (Fin m) K ⧸ Ideal.ofList gensM) :=
          hboundExt
      _ ≤ G.natDegree * boundM := Nat.mul_le_mul_left _ hboundM

end Genus2Lean
