import Mathlib
import Genus2Lean.PrincipalDivisorSubgroup
import Genus2Lean.ZeroD.Reduce.AlphaReduce
import Genus2Lean.ZeroD.TheDataDerivation.DataDerivationBasics

/-!
# Step 3 (`ROADMAP-reduce-divisor-correctness.md`): the principal-witness lemma stack

This file starts the actual proof of `reducedClass_eq_of_isReduction'`'s
divisor-class content (`AlphaLocusDegreeUniform.lean`), following the
three-lemma skeleton from `CHATGPT-REPLY-step3-reduce-correctness.md` /
`ROADMAP-reduce-divisor-correctness.md` §3a-§3e:

1. residual-intersection (`u_old ∣ N`) — **already fully proved**,
   `uRS4General_dvd_Npoly4`/`uRS4General_natDegree_eq_two` in
   `GeneralSharedRoot.lean`, no new Lean needed.
2. residual-Mumford (`v_new ≡ -phi mod u_new`) — **already confirmed**
   (roadmap's "Status update, this pass" §3c sign check), matches
   `vRS4General := -E·Y⁻¹`.
3. principal-witness (`div(h) = D_old - D_new`, `h = g/u_new`,
   `g = E + Y·y`) — **this file**, not yet proved, built as many small
   named lemmas per project convention rather than attempted whole.

Per the ChatGPT reply's own recommendation (§16), this file is deliberately
kept ignorant of `SampleTargetFromAlpha`/`aClass`/`hr`/`sa.reducedClass` —
those only enter at the final assembly theorem back in
`AlphaLocusDegreeUniform.lean`. Everything here is stated directly against
`E Y : Polynomial (F p)` (or, more generally, `k[X]`) and `H : Hyperelliptic
Polynomial k`, so it can be reused by both the general (`P1 ≠ P2`) and
tangent (`P1 = P2`) branches without duplication.

**Status: lemma 1 of the stack only (the norm identity, ChatGPT §2/§13
step 2) — genuinely close to free from `toPair_mul_involution`, which is
already fully proved. Nothing else in the stack (root-multiplicity
translation, the residue-nonzero ⇒ valuation-zero lemma, the `δ₀`
degree-argument escape hatch) is attempted in this pass.**
-/

noncomputable section

namespace HyperellipticPolynomial

open Polynomial

variable {k : Type*} [Field k]
variable {H : HyperellipticPolynomial k}

/-- **Lemma 1 of the principal-witness stack (ChatGPT §2/§13 step 2):
the norm identity at the `toPair`/`CoordinateRing` level.**
`toPair H E Y * toPair H E (-Y) = algebraMap _ _ (pairNorm H E Y)`,
i.e. `g · ḡ = N` in `CoordinateRing H`, where `ḡ = E - Y·y` is exactly
`toPair H E (-Y)` (matches `toPair_involution`: the hyperelliptic
involution sends `A + By ↦ A - By`).

This is `toPair_mul_involution` restated with `involution H (toPair H E
Y)` unfolded via `toPair_involution` to the concrete pair form
`toPair H E (-Y)`, rather than left as `involution H (toPair H E Y)` — the
concrete form is what the rest of the stack (`ordAt_toPair_mul_of_ne_zero'`,
which needs the *pair* `(A', B')`, not the abstract involution) actually
needs to rewrite against. -/
theorem toPair_mul_toPair_neg_eq_algebraMap_pairNorm (E Y : k[X]) :
    toPair H E Y * toPair H E (-Y) = algebraMap k[X] (CoordinateRing H) (pairNorm H E Y) := by
  rw [← toPair_involution]
  exact toPair_mul_involution H E Y

/-- **Corollary, in `Npoly4`-shaped form for this project's genus-2, `K=4`
instance.** Given `Npoly4 = Epoly4^2 - curvePoly*Ypoly4^2` (`AlphaReduce.lean`)
and `H.f = curvePoly p c0 c1 c2 c3 c4` (the `hf` hypothesis threaded through
`reducedClass_eq_of_isReduction'`), `pairNorm H E Y = E^2 - Y^2 * H.f`
(`HyperellipticFunctionField.lean`'s definition, unfolded) specializes
exactly to `Npoly4` once `E := Epoly4 ...`, `Y := Ypoly4 ...` are
substituted and `hf` is used to rewrite `H.f`. Stated here as the bridge
lemma so downstream code can rewrite `Npoly4 ...` directly into
`pairNorm H (Epoly4 ...) (Ypoly4 ...)` (and hence into the `toPair`
identity above) without re-deriving this each time. -/
theorem pairNorm_eq_of_eq_curvePoly {p : ℕ} [hp : Fact (Nat.Prime p)]
    {H : HyperellipticPolynomial (Genus2Lean.TheDataDerivation.F p)}
    {c0 c1 c2 c3 c4 : Genus2Lean.TheDataDerivation.F p}
    (hf : H.f =
      Genus2Lean.TheDataDerivation.curvePoly p c0 c1 c2 c3 c4)
    (E Y : Polynomial (Genus2Lean.TheDataDerivation.F p)) :
    pairNorm H E Y =
      E ^ 2 - Y ^ 2 * Genus2Lean.TheDataDerivation.curvePoly p c0 c1 c2 c3 c4 := by
  unfold pairNorm
  rw [hf]

end HyperellipticPolynomial

end
