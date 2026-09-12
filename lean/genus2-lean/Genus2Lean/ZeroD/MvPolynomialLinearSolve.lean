import Mathlib

/-!
# Solving `n - X j • d = 0` for one variable, given the rest of the point fixed

New this pass. Second piece of general-purpose infrastructure toward
`ROADMAP-degree-uniform-step3.md`'s Obligation 1 (`htop_ne_smul`), alongside
`IdealOfListNeTopFromEval.lean`. `genList`'s 8 "matching" generators
(`FuList`/`FvList`, `DecoupledSystemRegular.lean`) all have the shape
`n - X j * d` for `j ∈ {U0,U1,V0,V1}` and `n,d` polynomials that (per
`DecoupledGenerators.u1_indep`/etc.) never themselves mention `U0,U1,V0,V1`
-- i.e. `j ∉ n.vars ∪ d.vars`. This file proves the general fact that lets a
future pass turn "the other 8 variables are fixed and `d` evaluates
nonzero" into "the whole equation vanishes at SOME value of `X j`": update
the assignment at `j` alone (leaving every other coordinate, including
whatever made the curve equations vanish, untouched) to the quotient
`eval assign n / eval assign d`, and the equation evaluates to `0` there.

**What this file does NOT do**: apply this to `genList`'s actual 8
generators, verify `j ∉ n.vars ∪ d.vars` holds for them (that's exactly
`u1_indep`/`u2_indep`/`v1_indep`/`v2_indep`, already proved, unconditional),
or exhibit the curve-side assignment the 4 curve-equation generators need.
That composition is genuine `Genus2Lean`-specific work for a later pass,
using this file's lemma once per matching generator plus
`IdealOfListNeTopFromEval.lean`'s lemma to close `htop_ne_smul` itself.

**Not yet REPL-confirmed** — drafted this pass; Claire tests via the REPL.
-/

namespace Genus2Lean

open MvPolynomial

/-- **Evaluation only sees a polynomial's own variables.** If two
assignments `g₁`/`g₂ : σ → S` agree on every variable of `p`, `eval g₁ p =
eval g₂ p`. Immediate from `MvPolynomial.hom_congr_vars` (`Mathlib.Algebra.
MvPolynomial.Variables`) applied to `f₁ := eval g₁`, `f₂ := eval g₂` --
both restrict to the identity on the base ring (`eval_C`), so the
`hC`/constant-agreement side condition is free (`rfl`-style, both sides
are literally `C`), leaving only the `hv` variable-agreement hypothesis to
supply. -/
theorem MvPolynomial.eval_eq_eval_of_eqOn_vars {σ S : Type*} [CommRing S]
    {p : MvPolynomial σ S} {g₁ g₂ : σ → S} (hv : ∀ i ∈ p.vars, g₁ i = g₂ i) :
    MvPolynomial.eval g₁ p = MvPolynomial.eval g₂ p := by
  have hC : (MvPolynomial.eval g₁ : MvPolynomial σ S →+* S).comp MvPolynomial.C =
      (MvPolynomial.eval g₂ : MvPolynomial σ S →+* S).comp MvPolynomial.C := by
    ext r
    simp only [RingHom.comp_apply, MvPolynomial.eval_C]
  have := MvPolynomial.hom_congr_vars (p₁ := p) (p₂ := p) hC
    (fun i hi _ => by simpa using hv i hi) rfl
  simpa using this

/-- **The headline fact.** Given `assign : σ → S`, `d ≠ 0` under `eval
assign`, and `j ∉ n.vars ∪ d.vars` (so updating the assignment at `j` alone
cannot change `eval _ n`/`eval _ d`), setting `assign' := Function.update
assign j (eval assign n / eval assign d)` makes `eval assign' (n - X j * d)
= 0`. Needs `S` a field (division), matching this project's eventual target
`S := AlgebraicClosure (F p)` or similar. -/
theorem MvPolynomial.exists_update_eval_sub_X_mul_eq_zero {σ S : Type*}
    [Field S] [DecidableEq σ] (n d : MvPolynomial σ S) (j : σ)
    (hj : j ∉ n.vars ∪ d.vars) (assign : σ → S)
    (hd : MvPolynomial.eval assign d ≠ 0) :
    MvPolynomial.eval (Function.update assign j
        (MvPolynomial.eval assign n / MvPolynomial.eval assign d))
      (n - MvPolynomial.X j * d) = 0 := by
  set assign' : σ → S := Function.update assign j
    (MvPolynomial.eval assign n / MvPolynomial.eval assign d) with hassign'_def
  have hjn : j ∉ n.vars := fun h => hj (Finset.mem_union_left _ h)
  have hjd : j ∉ d.vars := fun h => hj (Finset.mem_union_right _ h)
  -- On any variable `i` of `n` (resp. `d`), `i ≠ j` (since `j` isn't one of
  -- them), so `Function.update` leaves `assign i` untouched there --
  -- `simp [Function.update_apply]` normalizes the `if i = j then _ else
  -- assign i` this produces using that inequality, regardless of exactly
  -- which Mathlib-name convention (`update_apply`/`update_noteq`/etc.) the
  -- current snapshot uses for the underlying `ite`.
  have hn_eq : MvPolynomial.eval assign' n = MvPolynomial.eval assign n :=
    MvPolynomial.eval_eq_eval_of_eqOn_vars
      (fun i hi => by
        have : i ≠ j := fun h => hjn (h ▸ hi)
        simp [hassign'_def, Function.update_apply, this])
  have hd_eq : MvPolynomial.eval assign' d = MvPolynomial.eval assign d :=
    MvPolynomial.eval_eq_eval_of_eqOn_vars
      (fun i hi => by
        have : i ≠ j := fun h => hjd (h ▸ hi)
        simp [hassign'_def, Function.update_apply, this])
  have hXj : MvPolynomial.eval assign' (MvPolynomial.X j) = assign' j :=
    MvPolynomial.eval_X (n := j) (f := assign')
  have hassign'j : assign' j =
      MvPolynomial.eval assign n / MvPolynomial.eval assign d := by
    simp [hassign'_def, Function.update_apply]
  rw [MvPolynomial.eval_sub, MvPolynomial.eval_mul, hXj, hassign'j, hd_eq, hn_eq]
  -- Goal here: `eval assign n - (eval assign n / eval assign d) * eval assign d = 0`.
  -- Rewritten via `sub_eq_zero` into a plain division identity
  -- (`(eval assign n / eval assign d) * eval assign d = eval assign n`),
  -- closed by `div_mul_cancel₀`'s underlying `field_simp` normalization --
  -- done through `rw [sub_eq_zero]; field_simp` rather than guessing the
  -- exact current name/argument-order of a `div_mul_cancel₀`-style lemma
  -- directly.
  rw [sub_eq_zero]
  field_simp

end Genus2Lean
