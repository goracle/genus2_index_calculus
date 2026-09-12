import Mathlib

/-!
# Negating one variable is a `totalDegree`-preserving ring involution

New this pass. Standalone, `Genus2Lean`-agnostic infrastructure toward
`ROADMAP-crossnondegenerate-degree-bound.md`'s "conjugate trick": the plan
to extract degree-bounded `IsRdecWitness`-style witnesses for a quadratic
tower element's two normal-form coefficients (`d0`, `d1` with `v = d0 +
d1*w`) out of a single witness for `v` itself, by combining the witness
equation with its image under negating the target ring's `w`-generator
variable (`X (sg.wGen k)`) — the two equations together form a 2×2 linear
system in `ι d0`/`ι d1`, solvable since the "coefficient matrix"
`[[d, d*W], [d', -d'*W]]` (`d' := ` `d` with the generator negated) has
determinant `-2*d*d'*W`, invertible whenever `d, d' ≠ 0` and `char ≠ 2`
(already assumed project-wide, `Fact (p ≠ 2)`).

This file proves only the piece that doesn't depend on any of that
downstream construction: negating a single `MvPolynomial` generator
variable (leaving all others fixed) is an involutive ring automorphism
that preserves `totalDegree` **exactly**, not just as an upper bound --
because it only flips the sign of each monomial's coefficient
(`(-1) ^ (exponent of j in that monomial)`), never touching the exponent
tuple itself, so the polynomial's `support` (and hence its `totalDegree`,
which is a `Finset.sup` over `support`) is unchanged verbatim.

**What this file does NOT do**: build the 2×2 Cramer solve itself, connect
it to `IsRdecWitness`, or touch any `Genus2Lean`-specific type (`K1`, `K2`,
`SideGens`, etc.) at all -- this is pure `MvPolynomial` algebra over an
arbitrary commutative ring, reusable regardless of how the tower-specific
assembly ends up shaped. Left for a later file/pass, per this project's
"build infrastructure, generalize" convention.

**Not yet REPL-confirmed** -- drafted this pass; Claire tests via the REPL.
-/

namespace Genus2Lean

open MvPolynomial

/-- **The negation map itself.** `negateVar j p` replaces every occurrence
of the generator `X j` in `p` with `-X j`, leaving every other variable
untouched -- i.e. `MvPolynomial.eval₂Hom C (Function.update X j (-X j))`.
Phrased via `eval₂Hom` with `C` as the coefficient-embedding hom (the
correct choice: `eval₂Hom`'s first argument is a hom OUT OF the
coefficient ring `R`, not an endomorphism of `MvPolynomial σ R` itself),
so it fixes every constant and only touches the chosen generator. -/
noncomputable def negateVar {σ R : Type*} [CommRing R] [DecidableEq σ]
    (j : σ) : MvPolynomial σ R →+* MvPolynomial σ R :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (Function.update MvPolynomial.X j (-MvPolynomial.X j))

/-- **On a single monomial, `negateVar` only flips the coefficient's
sign** (by `(-1) ^ (that monomial's exponent at `j`)`), leaving the
exponent tuple `u` itself untouched. Proved via `MvPolynomial.monomial_eq`
(`(monomial s) a = C a * s.prod fun n e => X n ^ e`, confirmed against
mathlib docs): `negateVar j` is a ring hom fixing `C a` (by construction,
`eval₂Hom C _`) and sending `X n ↦ if n = j then -X n else X n`
(`Function.update`), so it sends `C a * s.prod (fun n e => X n ^ e)` to
`C a * s.prod (fun n e => (if n = j then -X n else X n) ^ e)` -- and that
product differs from the original only at the (at most one) factor where
`n = j`, contributing an extra `(-1) ^ (s j)` there and leaving every
other factor untouched, via `Finsupp.prod_congr`-style splitting into the
`j`-factor and the rest (`Finsupp.prod` restricted off a `DecidableEq`
singleton). Rather than splitting the `Finsupp.prod` combinatorially, the
cleanest route folds `(-1) ^ (u j)` entirely into the coefficient at the
end: prove `negateVar j` sends the RAW PRODUCT to `(-1) ^ (u j)` times
itself (a single scalar identity via `Finsupp.prod_congr` applied
factor-by-factor, `map_pow`/`ite`-splitting each `X n ↦ ±X n`), then
multiply both sides by the untouched `C a`. -/
theorem negateVar_monomial {σ R : Type*} [CommRing R] [DecidableEq σ]
    (j : σ) (u : σ →₀ ℕ) (a : R) :
    negateVar j (MvPolynomial.monomial u a) =
      MvPolynomial.monomial u (a * (-1) ^ u j) := by
  classical
  have hme : MvPolynomial.monomial u a =
      MvPolynomial.C a * u.prod (fun n e => MvPolynomial.X n ^ e) :=
    MvPolynomial.monomial_eq
  have hme' : MvPolynomial.monomial u (a * (-1) ^ u j) =
      MvPolynomial.C a * ((-1) ^ u j * u.prod (fun n e => MvPolynomial.X n ^ e)) := by
    have h1 : MvPolynomial.monomial u (a * (-1) ^ u j) =
        MvPolynomial.C (a * (-1) ^ u j) * u.prod (fun n e => MvPolynomial.X n ^ e) :=
      MvPolynomial.monomial_eq
    rw [h1]
    have h2 : (MvPolynomial.C (a * (-1) ^ u j) : MvPolynomial σ R) =
        MvPolynomial.C a * (-1) ^ u j := by
      rw [map_mul]
      congr 1
      rw [map_pow]
      norm_num
    rw [h2, mul_assoc]
  rw [hme, hme', map_mul]
  congr 1
  · simp [negateVar]
  · -- Revision 2: close the `n = j` branch with the current Mathlib
    -- `Function.update_self` lemma (`update_same` is not an identifier).
    -- Product identity: `negateVar j (u.prod fun n e => X n ^ e) =
    -- (-1) ^ u j * u.prod fun n e => X n ^ e`.
    rw [map_finsuppProd (negateVar j)]
    have hstep : ∀ n ∈ u.support,
        negateVar j (MvPolynomial.X n ^ u n) =
          (if n = j then (-1 : MvPolynomial σ R) ^ u n else 1) * MvPolynomial.X n ^ u n := by
      intro n _
      rw [map_pow]
      have hXn : negateVar j (MvPolynomial.X n) =
          Function.update (MvPolynomial.X : σ → MvPolynomial σ R) j
            (-MvPolynomial.X j) n := by
        change MvPolynomial.eval₂Hom MvPolynomial.C
            (Function.update (MvPolynomial.X : σ → MvPolynomial σ R) j
              (-MvPolynomial.X j)) (MvPolynomial.X n) =
          Function.update (MvPolynomial.X : σ → MvPolynomial σ R) j
            (-MvPolynomial.X j) n
        rw [MvPolynomial.eval₂Hom_X']
      rw [hXn]
      by_cases hnj : n = j
      · subst hnj
        rw [Function.update_self, neg_pow]
        simp
      · simp [hnj]
    rw [Finsupp.prod, Finset.prod_congr rfl hstep]
    rw [Finset.prod_mul_distrib]
    by_cases hj : j ∈ u.support
    · rw [Finset.prod_eq_single j]
      · rw [if_pos rfl]
        rw [Finsupp.prod]
      · intro n _ hnj
        rw [if_neg hnj]
      · intro hnotin
        exact absurd hj hnotin
    · have huj : u j = 0 := by
        simpa only [Finsupp.mem_support_iff, not_not] using hj
      rw [huj, pow_zero]
      rw [Finset.prod_eq_one]
      · rw [Finsupp.prod]
      · intro n hn
        have hnj : n ≠ j := fun h => hj (h ▸ hn)
        rw [if_neg hnj]

/-- **`negateVar` is an involution.** Negating `X j` twice restores the
original polynomial: `Function.update X j (-X j)` composed with itself
sends `X j ↦ -(-X j) = X j` and fixes every other generator, so `eval₂Hom
(RingHom.id) (that composite)` is the identity on generators, hence (by
`MvPolynomial.ringHom_ext`) the identity map overall. -/
theorem negateVar_negateVar {σ R : Type*} [CommRing R] [DecidableEq σ]
    (j : σ) (p : MvPolynomial σ R) :
    negateVar j (negateVar j p) = p := by
  classical
  have hcomp : (negateVar j).comp (negateVar j) = RingHom.id (MvPolynomial σ R) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [negateVar, RingHom.comp_apply]
    · intro i
      simp only [RingHom.comp_apply, negateVar, MvPolynomial.eval₂Hom_X']
      by_cases hij : i = j
      · subst hij
        simp
      · simp [hij]
  exact DFunLike.congr_fun hcomp p

/-- **`negateVar`'s coefficient formula, at every monomial index `u`
simultaneously.** `coeff u (negateVar j p) = coeff u p * (-1) ^ u j` for
every `u`, not just when `p` itself is a single monomial -- obtained by
writing `p` as `∑ v ∈ p.support, monomial v (coeff v p)`
(`MvPolynomial.support_sum_monomial_coeff`), applying `negateVar j`
termwise (`map_sum`, `negateVar_monomial`), then reading off `coeff u` of
the resulting sum: every summand `monomial v (coeff v p * (-1) ^ v j)`
contributes `0` to `coeff u` unless `v = u` (`coeff_monomial`), in which
case it contributes exactly `coeff u p * (-1) ^ u j` -- matching the
right-hand side whether or not `u ∈ p.support` (if `u ∉ p.support`, both
`coeff u p` and this sum's `u`-th term are `0`, `Finset.sum_eq_zero`-style,
since the sum only ranges over `p.support`). -/
theorem negateVar_coeff {σ R : Type*} [CommRing R] [DecidableEq σ]
    (j : σ) (p : MvPolynomial σ R) (u : σ →₀ ℕ) :
    MvPolynomial.coeff u (negateVar j p) =
      MvPolynomial.coeff u p * (-1) ^ u j := by
  classical
  conv_lhs => rw [← MvPolynomial.support_sum_monomial_coeff p]
  rw [map_sum]
  simp only [negateVar_monomial]
  rw [MvPolynomial.coeff_sum]
  by_cases hu : u ∈ p.support
  · rw [Finset.sum_eq_single u]
    · rw [MvPolynomial.coeff_monomial, if_pos rfl]
    · intro v _ hvu
      simp [MvPolynomial.coeff_monomial, hvu]
    · intro h
      exact absurd hu h
  · have hp0 : MvPolynomial.coeff u p = 0 := by
      rwa [MvPolynomial.mem_support_iff, not_not] at hu
    rw [hp0, zero_mul]
    apply Finset.sum_eq_zero
    intro v hv
    have hvu : v ≠ u := fun h => hu (h ▸ hv)
    simp [MvPolynomial.coeff_monomial, hvu]

/-- **`negateVar` preserves `support` exactly**, immediate from
`negateVar_coeff`: `coeff u (negateVar j p) ≠ 0 ↔ coeff u p ≠ 0` since
`(-1) ^ u j` is always a unit (`±1`, never `0`), so multiplying by it never
changes whether a coefficient is nonzero. -/
theorem negateVar_support {σ R : Type*} [CommRing R] [DecidableEq σ]
    (j : σ) (p : MvPolynomial σ R) :
    (negateVar j p).support = p.support := by
  classical
  ext u
  simp only [MvPolynomial.mem_support_iff, negateVar_coeff]
  constructor
  · intro hne hp0
    exact hne (by rw [hp0, zero_mul])
  · intro hne hz
    apply hne
    exact mul_neg_one_pow_eq_zero_iff.mp hz

/-- **`negateVar` preserves `totalDegree` exactly**, immediate from
`negateVar_support`: `totalDegree` is `p.support.sup (fun m => (Finsupp.
toMultiset m).card)` (`MvPolynomial.totalDegree`'s own definition, via
`totalDegree_eq`), a function purely of `support`, so equal `support`s
force equal `totalDegree`s. -/
theorem negateVar_totalDegree {σ R : Type*} [CommRing R] [DecidableEq σ]
    (j : σ) (p : MvPolynomial σ R) :
    (negateVar j p).totalDegree = p.totalDegree := by
  rw [MvPolynomial.totalDegree_eq, MvPolynomial.totalDegree_eq, negateVar_support]

end Genus2Lean
