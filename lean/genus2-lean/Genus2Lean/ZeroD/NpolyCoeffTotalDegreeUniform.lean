import Mathlib
import Genus2Lean.ZeroD.NpolyCoeffTotalDegree
import Genus2Lean.ZeroD.DecoupledSystemRegular

/-!
# A single `k`-independent `IsRdecWitness` bound for every coefficient of `Npoly`

Closes the gap `NpolyCoeffTotalDegree.lean`'s own closing note flagged as
"not attempted this pass" (per `ROADMAP-crossnondegenerate-degree-bound.md`'s
"still fully unresolved" tracker): `Npoly_coeff_isRdecWitness` bounds
`Npoly.coeff k` in terms of `k` itself, for EVERY `k`, but that bound grows
with `k`. Combined with `Npoly_natDegree_le_six` (`DecoupledSystemRegular.lean`,
already proved, `sorry`-free: `Npoly.natDegree ≤ 6`), every `k > 6` coefficient
is literally `0` (`Polynomial.coeff_eq_zero_of_natDegree_lt`), which has the
trivial witness `(0, 1)` regardless of `k`; every `k ≤ 6` coefficient's bound,
from `Npoly_coeff_isRdecWitness`'s own formula `(k+1)*1408 + (k+1)*((k+1)*1408)`,
is monotone increasing in `k` (both summands are), so it's `≤` the `k = 6`
value, `78848`, computed directly: `7*1408 + 7*(7*1408) = 9856 + 68992 = 78848`.
Either way, `78848` (a fixed numeral, no `k`-dependence) covers every
coefficient of `Npoly` -- this is the promised single, `k`-independent bound.
-/

namespace Genus2Lean
namespace TheDataDerivation

variable (p : ℕ) [hp : Fact (Nat.Prime p)] [hp2 : Fact (p ≠ 2)]
variable (c0 c1 c2 c3 c4 : F p)

/-- **The `k`-independent bound.** Same hypotheses as `Npoly_coeff_isRdecWitness`
(the `IsRdecWitness`-shaped nonvanishing side conditions on the matrix/rhs/det
witnesses feeding `coeffsOut`), but the conclusion's numeral bound, `78848`,
no longer depends on `k` at all -- a single number that covers every
coefficient of `Npoly` uniformly, `k > 6` via vanishing and `k ≤ 6` via
monotonicity in `Npoly_coeff_isRdecWitness`'s own formula. -/
theorem Npoly_coeff_isRdecWitness_uniform {Vars : Type*} [DecidableEq Vars]
    (sg : SideGens Vars) (u0 u1 v0 v1 : F p)
    (ι : K2 p c0 c1 c2 c3 c4 →+* FractionRing (MvPolynomial Vars (F p)))
    (hι_t : ∀ i : Fin 2, ι (algebraMap (K1 p c0 c1 c2 c3 c4) (K2 p c0 c1 c2 c3 c4)
        (algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4)
          (algebraMap (MvPolynomial (Fin 2) (F p)) (K0 p) (MvPolynomial.X i)))) =
      algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p)))
        (MvPolynomial.X (sg.tGen i)))
    (hι_w1 : ι (algebraMap (K1 p c0 c1 c2 c3 c4) (K2 p c0 c1 c2 c3 c4) (w1 p c0 c1 c2 c3 c4)) =
      algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p)))
        (MvPolynomial.X (sg.wGen 0)))
    (hι_w2 : ι (w2 p c0 c1 c2 c3 c4) =
      algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p)))
        (MvPolynomial.X (sg.wGen 1)))
    (hbidx : ∀ col : Fin 4, otherIdx.getD col.val 0 < 5)
    (hAne : ∀ row col : Fin 4,
      (algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p))))
        ((matrixA_entry_totalDegree_le p c0 c1 c2 c3 c4 sg u0 u1 v0 v1 row col ι
          hι_t hι_w1 hι_w2 (hbidx col)).choose.2) ≠ 0)
    (hRne : ∀ row : Fin 4,
      (algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p))))
        ((rhsVec_entry_totalDegree_le p c0 c1 c2 c3 c4 sg u0 u1 v0 v1 row ι
          hι_t hι_w1 hι_w2).choose.2) ≠ 0)
    (hDne : (algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p))))
        ((matrixDet_totalDegree_le p c0 c1 c2 c3 c4 sg u0 u1 v0 v1 ι
          hι_t hι_w1 hι_w2 hbidx hAne).choose.2) ≠ 0)
    (hιdet_ne : ι (matrixA p c0 c1 c2 c3 c4 u0 u1 v0 v1).det ≠ 0)
    (k : ℕ) :
    ∃ nd : MvPolynomial Vars (F p) × MvPolynomial Vars (F p),
      IsRdecWitness p ι
        (algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p))))
        ((Npoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff k) nd ∧
      nd.1.totalDegree ≤ 78848 ∧ nd.2.totalDegree ≤ 78848 := by
  by_cases hk6 : k ≤ 6
  · -- `k ≤ 6`: reuse `Npoly_coeff_isRdecWitness` directly, then bound its
    -- own `(k+1)*1408 + (k+1)*((k+1)*1408)` formula by the `k = 6` value
    -- via monotonicity (`gcongr` on `k+1 ≤ 7`, both summands increase in `k`).
    obtain ⟨nd, hwit, hnd1, hnd2⟩ :=
      Npoly_coeff_isRdecWitness p c0 c1 c2 c3 c4 sg u0 u1 v0 v1 ι
        hι_t hι_w1 hι_w2 hbidx hAne hRne hDne hιdet_ne k
    have hbound : (k + 1) * 1408 + (k + 1) * ((k + 1) * 1408) ≤ 78848 := by
      have h1 : k + 1 ≤ 7 := by omega
      have hstep1 : (k + 1) * 1408 ≤ 7 * 1408 := by gcongr
      have hstep2 : (k + 1) * ((k + 1) * 1408) ≤ 7 * (7 * 1408) := by gcongr
      calc (k + 1) * 1408 + (k + 1) * ((k + 1) * 1408)
          ≤ 7 * 1408 + 7 * (7 * 1408) := Nat.add_le_add hstep1 hstep2
        _ = 78848 := by norm_num
    exact ⟨nd, hwit, le_trans hnd1 hbound, le_trans hnd2 hbound⟩
  · -- `k > 6`: `Npoly.coeff k = 0` outright (`Npoly.natDegree ≤ 6 < k`), so
    -- the trivial zero-witness `(0, 1)` works, with totalDegree `(0, 0)`.
    have hdeg := Genus2Lean.DecoupledSystem.Npoly_natDegree_le_six p c0 c1 c2 c3 c4 u0 u1 v0 v1
    have hk6' : 6 < k := by omega
    have hzero : (Npoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff k = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg hk6')
    refine ⟨(0, 1), ?_, ?_, ?_⟩
    · unfold IsRdecWitness
      simp [hzero]
    · simp
    · simp

end TheDataDerivation
end Genus2Lean
