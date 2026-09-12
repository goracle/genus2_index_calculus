import Mathlib
import Genus2Lean.ZeroD.MvPolynomialLinearSolve

/-!
# Solving TWO generators that share one target variable

New this pass. `MvPolynomialLinearSolve.lean`'s own closing note describes
the intended next step as "apply this [single-generator] lemma once per
matching generator" to close `ROADMAP-degree-uniform-step3.md`'s Obligation
1 (`htop_ne_smul`). **That description is incomplete, and this file exists
to correct it before anyone builds on it as stated.**

`FuList`/`FvList` (`DecoupledSystemRegular.lean`) do NOT have one generator
per target variable — each target variable (`U0`, `U1`, `V0`, `V1`) is
shared by exactly TWO generators, one from each sample:

```
d.u1_num 0 - U0' * d.u1_den 0   -- sample A's constraint on U0
d.u2_num 0 - U0' * d.u2_den 0   -- sample B's constraint on U0
```

`MvPolynomial.exists_update_eval_sub_X_mul_eq_zero` solves ONE such equation
for `U0`, at the value `(eval n)/(eval d)`. Applying it twice, once per
generator, in general produces TWO DIFFERENT values of `U0`
(`(eval n1)/(eval d1)` and `(eval n2)/(eval d2)`) — only one of which can
actually be assigned, since `U0` is a single variable. **Both generators
vanish simultaneously at a single assignment if and only if the two
fractions agree there**, i.e. `eval n1 * eval d2 = eval n2 * eval d1` — the
cross term `d1*n2 - d2*n1` (up to sign) vanishing under `eval`. This is
literally `CrossNondegenerate`'s `hu0`/`hu1`/`hv0`/`hv1` resultant, the same
element `CrossResultantIsRdecWitness.lean` already produces an
`IsRdecWitness` fact about (for a different purpose, bounding its degree —
see that file's own docstring). **So `htop_ne_smul`'s closure is NOT
independent of the `CrossNondegenerate`/resultant story the way
`ROADMAP-degree-uniform-step3.md`'s "Obligation 1... independent of steps
1-2, likely the cheapest" framing suggested** — solving for a shared target
variable at all requires the two samples' local data to already agree
there, i.e. requires the cross-resultant to vanish AT THE CHOSEN POINT.
Flagging this precisely rather than silently building a lemma that can't
actually be applied to `genList` as originally scoped.

**What this file DOES do**: states and proves the correct two-generator
lemma, conditional on the resultant vanishing at the ambient assignment
(an honest, narrow, checkable per-point hypothesis, not a blanket
`IsSMulRegular`-style condition — this is strictly weaker than
`CrossNondegenerate` itself, which asks for regularity in a quotient ring,
not just vanishing of one value at one point; a point where `CrossNondegenerate`
holds automatically satisfies this file's hypothesis, since regularity in
particular need not obstruct the specific point this file's `assign` is
built from — see this file's closing note for the precise relationship).
This turns the single-generator lemma from
`MvPolynomialLinearSolve.lean` into the actual two-generator building block
`genList`'s 4 shared-variable pairs need, cleanly isolating the one place
this obligation genuinely touches the cross-resultant.

**Not yet REPL-confirmed** — drafted this pass; Claire tests via the REPL.
-/

namespace Genus2Lean

open MvPolynomial

/-- **The headline fact.** Given `assign : σ → S`, both denominators
nonzero under `eval assign`, `j` foreign to all four of `n1,d1,n2,d2`'s
variables, and the cross-resultant `n1*d2 - n2*d1` vanishing under
`eval assign` (the one genuinely extra hypothesis beyond the single-
generator case — this is where the two generators' shared variable
actually bites), there is a single value of `X j` (namely `(eval assign
n1)/(eval assign d1)`, which the resultant hypothesis shows equals
`(eval assign n2)/(eval assign d2)` too) making BOTH `n1 - X j * d1` and
`n2 - X j * d2` vanish simultaneously. -/
theorem MvPolynomial.exists_update_eval_sub_X_mul_eq_zero_pair
    {σ S : Type*} [Field S] [DecidableEq σ]
    (n1 d1 n2 d2 : MvPolynomial σ S) (j : σ)
    (hj1 : j ∉ n1.vars ∪ d1.vars) (hj2 : j ∉ n2.vars ∪ d2.vars)
    (assign : σ → S)
    (hd1 : MvPolynomial.eval assign d1 ≠ 0)
    (hd2 : MvPolynomial.eval assign d2 ≠ 0)
    (hres : MvPolynomial.eval assign n1 * MvPolynomial.eval assign d2 =
      MvPolynomial.eval assign n2 * MvPolynomial.eval assign d1) :
    ∃ assign' : σ → S,
      (∀ i ∈ ({j}ᶜ : Set σ), assign' i = assign i) ∧
      MvPolynomial.eval assign' (n1 - MvPolynomial.X j * d1) = 0 ∧
      MvPolynomial.eval assign' (n2 - MvPolynomial.X j * d2) = 0 := by
  refine ⟨Function.update assign j
    (MvPolynomial.eval assign n1 / MvPolynomial.eval assign d1), ?_, ?_, ?_⟩
  · -- Off `j`, `Function.update` leaves `assign` untouched — closed via
    -- `Function.update_apply`'s underlying `ite`, same idiom
    -- `MvPolynomialLinearSolve.lean`'s own proof already uses, rather than
    -- naming a possibly-renamed `update_noteq`-style lemma directly.
    intro i hi
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hi
    simp [Function.update_apply, hi]
  · exact MvPolynomial.exists_update_eval_sub_X_mul_eq_zero n1 d1 j hj1 assign hd1
  · -- The value `assign' j` is defined as `n1/d1`'s ratio; `n2 - X j * d2`
    -- vanishing at it needs `n2/d2` to be the SAME ratio, which `hres`
    -- (cross-multiplied, so no need for `hd2`'s converse direction) gives.
    have hswap : MvPolynomial.eval assign n1 / MvPolynomial.eval assign d1 =
        MvPolynomial.eval assign n2 / MvPolynomial.eval assign d2 := by
      rw [div_eq_div_iff hd1 hd2]
      linear_combination hres
    have := MvPolynomial.exists_update_eval_sub_X_mul_eq_zero n2 d2 j hj2 assign hd2
    rwa [← hswap] at this

end Genus2Lean
