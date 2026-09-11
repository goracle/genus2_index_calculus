import Mathlib
import Genus2Lean.ZeroD.CurBeforeMonicCoeffTotalDegree

/-!
# `uRS.coeff i`'s own `IsRdecWitness` bound, via `curBeforeMonic`'s leading coefficient

New this pass. `CurBeforeMonicCoeffTotalDegree.lean` closes an `IsRdecWitness`
bound (uniform `≤ 315448`) on `curBeforeMonic.coeff {0,1,2}` -- its only
possibly-nonzero coefficients, since `curBeforeMonic_natDegree_le_two` bounds
its degree. But `CrossNondegenerateDegreeBound.lean`'s resultant bound is
stated for `uRS`/`vRS`, not `curBeforeMonic` directly, and
`uRS := C curBeforeMonic.leadingCoeff⁻¹ * curBeforeMonic`
(`DataDerivationMumford.lean`) -- a genuine extra step, not a relabeling,
since `leadingCoeff⁻¹` is a FIELD INVERSE, and `IsRdecWitness` has no direct
"invert this witness" combinator, only `.mul`/`.div`.

**The bridge, closed here**: `IsRdecWitness.div` (`TowerToRdecMul.lean`)
already gives everything needed, with no new combinator required. Taking
`a := 1`, `b := leadingCoeff` (witness `(nb,db)` from whichever of
`curBeforeMonic.coeff {0,1,2}`'s three witnesses matches `leadingCoeff`,
`coeff (natDegree)`), `1`'s own trivial witness `(1,1)` gives
`leadingCoeff⁻¹ = 1 / leadingCoeff`'s witness as `(1*db, 1*nb) = (db, nb)`
-- literally the SWAP of `leadingCoeff`'s own witness pair, same `totalDegree`
bound `≤ 315448` on each side (swapping two `≤315448`-bounded polynomials
stays `≤315448`-bounded). `IsRdecWitness.mul` then combines this with
`curBeforeMonic.coeff i`'s own witness to give `uRS.coeff i`'s witness
directly (`uRS.coeff i = leadingCoeff⁻¹ * curBeforeMonic.coeff i` --
`Polynomial.coeff_C_mul`, mechanical), bound `≤ 630896` (`315448 + 315448`,
`.mul`'s bound is the SUM of its factors' bounds, matching this project's
existing `uniformBound_mul`-style arithmetic).

**The one genuine case split**: `leadingCoeff = curBeforeMonic.coeff
(curBeforeMonic.natDegree)`, and `natDegree` is only known `≤ 2`
(`curBeforeMonic_natDegree_le_two`), not `= 2` unconditionally -- so
`leadingCoeff` could be `coeff 0`, `coeff 1`, or `coeff 2` depending on
where the true degree lands. Handled by `interval_cases`/`omega` on
`natDegree ≤ 2`, picking the matching one of the three already-proved
witnesses in each of the three branches -- no new mathematical content,
pure case analysis, closed here rather than left as a hypothesis, since
`curBeforeMonic_coeff_totalDegree_le` already supplies all three cases'
witnesses uniformly at the SAME bound `≤315448`, so no branch is harder
than any other.

**Not yet REPL-confirmed** -- drafted this pass, sent for testing next.
-/

namespace Genus2Lean
namespace TheDataDerivation

open Polynomial

variable (p : ℕ) [hp : Fact (Nat.Prime p)] [hp2 : Fact (p ≠ 2)]
variable (c0 c1 c2 c3 c4 u0 u1 v0 v1 : F p)

set_option maxHeartbeats 20000000 in
/-- **`curBeforeMonic`'s leading coefficient has an `IsRdecWitness` bound
`≤ 315448`**, given `curBeforeMonic ≠ 0` (so `leadingCoeff ≠ 0`, needed for
the later `.div` step, not used directly in this statement) and the same
hypothesis bundle `curBeforeMonic_coeff_totalDegree_le` itself needs. Proved
by cases on `curBeforeMonic.natDegree ≤ 2` (`curBeforeMonic_natDegree_le_two`),
picking the matching one of that theorem's three witnesses (`coeff 0/1/2`)
in each branch -- `leadingCoeff = coeff natDegree` by definition
(`Polynomial.leadingCoeff`), so once `natDegree` is pinned to a literal `0`,
`1`, or `2` in each branch, `rfl`/`congrArg` identifies it with the matching
witness directly. -/
theorem curBeforeMonic_leadingCoeff_isRdecWitness {Vars : Type*} [DecidableEq Vars]
    (sg : SideGens Vars)
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
    (hA : MatrixNondegenerate p c0 c1 c2 c3 c4 u0 u1 v0 v1)
    (hMumford : IsMumfordTarget p c0 c1 c2 c3 c4 u0 u1 v0 v1) :
    ∃ nd : MvPolynomial Vars (F p) × MvPolynomial Vars (F p),
      IsRdecWitness p ι
        (algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p))))
        (curBeforeMonic p c0 c1 c2 c3 c4 u0 u1 v0 v1).leadingCoeff nd ∧
      nd.1.totalDegree ≤ 315448 ∧ nd.2.totalDegree ≤ 315448 := by
  obtain ⟨hw2, hw1, hw0⟩ := curBeforeMonic_coeff_totalDegree_le p c0 c1 c2 c3 c4 u0 u1 v0 v1 sg
    ι hι_t hι_w1 hι_w2 hbidx hAne hRne hDne hιdet_ne hA hMumford
  have hdle := Genus2Lean.DecoupledSystem.curBeforeMonic_natDegree_le_two
    p c0 c1 c2 c3 c4 u0 u1 v0 v1
  have hlc : (curBeforeMonic p c0 c1 c2 c3 c4 u0 u1 v0 v1).leadingCoeff =
      (curBeforeMonic p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff
        (curBeforeMonic p c0 c1 c2 c3 c4 u0 u1 v0 v1).natDegree := rfl
  -- `hw0`/`hw1`/`hw2` carry DIFFERENT bounds (`≤315448`/`≤157710`/`≤78848`
  -- respectively, per `curBeforeMonic_coeff_totalDegree_le`'s own statement)
  -- -- not uniformly `≤315448` as an earlier draft of this file wrongly
  -- assumed. Weaken `hw1`/`hw2` up to the common `≤315448` ceiling (the
  -- largest of the three) before using them, since this theorem's own
  -- conclusion states a single uniform bound.
  obtain ⟨nd0, hnd0wit, hnd0b1, hnd0b2⟩ := hw0
  obtain ⟨nd1, hnd1wit, hnd1b1, hnd1b2⟩ := hw1
  obtain ⟨nd2, hnd2wit, hnd2b1, hnd2b2⟩ := hw2
  have hw1' : ∃ nd : MvPolynomial Vars (F p) × MvPolynomial Vars (F p),
      IsRdecWitness p ι
        (algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p))))
        ((curBeforeMonic p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff 1) nd ∧
      nd.1.totalDegree ≤ 315448 ∧ nd.2.totalDegree ≤ 315448 :=
    ⟨nd1, hnd1wit, hnd1b1.trans (by norm_num), hnd1b2.trans (by norm_num)⟩
  have hw2' : ∃ nd : MvPolynomial Vars (F p) × MvPolynomial Vars (F p),
      IsRdecWitness p ι
        (algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p))))
        ((curBeforeMonic p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff 2) nd ∧
      nd.1.totalDegree ≤ 315448 ∧ nd.2.totalDegree ≤ 315448 :=
    ⟨nd2, hnd2wit, hnd2b1.trans (by norm_num), hnd2b2.trans (by norm_num)⟩
  have hw0' : ∃ nd : MvPolynomial Vars (F p) × MvPolynomial Vars (F p),
      IsRdecWitness p ι
        (algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p))))
        ((curBeforeMonic p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff 0) nd ∧
      nd.1.totalDegree ≤ 315448 ∧ nd.2.totalDegree ≤ 315448 :=
    ⟨nd0, hnd0wit, hnd0b1, hnd0b2⟩
  set nd := (curBeforeMonic p c0 c1 c2 c3 c4 u0 u1 v0 v1).natDegree with hndeq
  clear_value nd
  interval_cases nd
  · rw [hlc]; exact hw0'
  · rw [hlc]; exact hw1'
  · rw [hlc]; exact hw2'

set_option maxHeartbeats 20000000 in
/-- **`uRS.coeff i` has an `IsRdecWitness` bound `≤ 630896`**, the file's
actual deliverable: `leadingCoeff⁻¹`'s witness (`IsRdecWitness.div` at
`a := 1`, `b := leadingCoeff`, giving the SWAP of `leadingCoeff`'s own
witness, same `≤315448` bound each side) combined via `IsRdecWitness.mul`
with `curBeforeMonic.coeff i`'s own witness (one of
`curBeforeMonic_coeff_totalDegree_le`'s three, picked by `i`'s value the
same way the previous theorem's proof does) -- `.mul`'s bound is the SUM,
`315448 + 315448 = 630896`. Needs `curBeforeMonic ≠ 0` (`hcur`) both to make
`uRS` well-defined as `curBeforeMonic`'s monic associate and to supply
`leadingCoeff ≠ 0` (`Polynomial.leadingCoeff_ne_zero`) for `IsRdecWitness.div`'s
`ι leadingCoeff ≠ 0` side condition (via `RingHom.injective` off `K2`'s
`Field` instance, matching `anchor1_ne_anchor2`'s own idiom for this exact
move). The other side condition, `evalNd db ≠ 0` (`db` = leadingCoeff's
witness denominator), is threaded as its own explicit hypothesis `hlcd_ne`
rather than derived, since nothing upstream currently pins it down --
matching this file's and the project's own honest-hypothesis practice
(compare `hAne`/`hRne`/`hDne` above, all threaded the same way). -/
theorem uRS_coeff_isRdecWitness {Vars : Type*} [DecidableEq Vars]
    (sg : SideGens Vars)
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
    (hA : MatrixNondegenerate p c0 c1 c2 c3 c4 u0 u1 v0 v1)
    (hMumford : IsMumfordTarget p c0 c1 c2 c3 c4 u0 u1 v0 v1)
    (hcur : curBeforeMonic p c0 c1 c2 c3 c4 u0 u1 v0 v1 ≠ 0)
    (i : Fin 2)
    -- The one honestly-threaded side condition `.div` needs beyond `hcur`:
    -- `evalNd` doesn't kill the leading coefficient's own witness denominator.
    (hlcd_ne : ∀ nd : MvPolynomial Vars (F p) × MvPolynomial Vars (F p),
      IsRdecWitness p ι
        (algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p))))
        (curBeforeMonic p c0 c1 c2 c3 c4 u0 u1 v0 v1).leadingCoeff nd →
      (algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p)))) nd.2 ≠ 0) :
    ∃ nd : MvPolynomial Vars (F p) × MvPolynomial Vars (F p),
      IsRdecWitness p ι
        (algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p))))
        ((uRS p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff i.val) nd ∧
      nd.1.totalDegree ≤ 630896 ∧ nd.2.totalDegree ≤ 630896 := by
  set evalNd := algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p)))
  obtain ⟨⟨nb, db⟩, hlcwit, hnbb, hdbb⟩ :=
    curBeforeMonic_leadingCoeff_isRdecWitness p c0 c1 c2 c3 c4 u0 u1 v0 v1 sg ι
      hι_t hι_w1 hι_w2 hbidx hAne hRne hDne hιdet_ne hA hMumford
  have hlcne : (curBeforeMonic p c0 c1 c2 c3 c4 u0 u1 v0 v1).leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hcur
  have hιlcne : ι (curBeforeMonic p c0 c1 c2 c3 c4 u0 u1 v0 v1).leadingCoeff ≠ 0 :=
    fun h => hlcne ((RingHom.injective ι) (h.trans (map_zero ι).symm))
  have hone : IsRdecWitness p ι evalNd (1 : K2 p c0 c1 c2 c3 c4) (1, 1) := by
    unfold IsRdecWitness; simp
  have hinv := IsRdecWitness.div p hone hlcwit (hlcd_ne (nb, db) hlcwit) hιlcne
  rw [one_div] at hinv
  -- `hinv : IsRdecWitness p ι evalNd (curBeforeMonic ...).leadingCoeff⁻¹ (1 * db, 1 * nb)`
  have hcoeffwit := (curBeforeMonic_coeff_totalDegree_le p c0 c1 c2 c3 c4 u0 u1 v0 v1 sg ι
    hι_t hι_w1 hι_w2 hbidx hAne hRne hDne hιdet_ne hA hMumford)
  have huRScoeff : (uRS p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff i.val =
      (curBeforeMonic p c0 c1 c2 c3 c4 u0 u1 v0 v1).leadingCoeff⁻¹ *
        (curBeforeMonic p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff i.val := by
    unfold uRS
    rw [Polynomial.coeff_C_mul]
  -- One-multiplication-by-`1` bound, factored out so the four branches below
  -- don't each need to re-derive it: `totalDegree_mul` splits `(1 * x)` into
  -- `totalDegree 1 + totalDegree x`, THEN `totalDegree_one` rewrites the
  -- (now syntactically present) `totalDegree 1` term to `0`. Doing
  -- `totalDegree_mul` first is essential — `totalDegree 1` is not a subterm
  -- of the unsplit `(1 * x).totalDegree` goal, so `rw [totalDegree_one]`
  -- alone (tried in an earlier draft of this file) fails to find its pattern.
  have hone_mul : ∀ x : MvPolynomial Vars (F p), (1 * x).totalDegree ≤ x.totalDegree := by
    intro x
    have h := MvPolynomial.totalDegree_mul (1 : MvPolynomial Vars (F p)) x
    rw [MvPolynomial.totalDegree_one, zero_add] at h
    exact h
  fin_cases i
  · obtain ⟨⟨nc, dc⟩, hcwit, hncc, hdcc⟩ := hcoeffwit.2.2
    refine ⟨(1 * db * nc, 1 * nb * dc), ?_, ?_, ?_⟩
    · rw [huRScoeff]
      simpa using IsRdecWitness.mul p hinv hcwit
    · simp only
      refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
      have h1db : (1 * db : MvPolynomial Vars (F p)).totalDegree ≤ 315448 := by
        exact le_trans (hone_mul db) hdbb
      -- `hncc`'s literal bound depends on which conjunct this branch drew
      -- (`315448` for coeff 0, `157710` for coeff 1, `78848` for coeff 2) --
      -- weaken up to the common `315448` ceiling via `.trans`, never assume
      -- it already matches syntactically (an earlier draft's direct `:=`
      -- ascription broke here since `.2.2`/`.2.1` don't always carry the
      -- SAME literal bound).
      have hncc' : nc.totalDegree ≤ 315448 := hncc.trans (by norm_num)
      omega
    · simp only
      refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
      have h1nb : (1 * nb : MvPolynomial Vars (F p)).totalDegree ≤ 315448 := by
        exact le_trans (hone_mul nb) hnbb
      have hdcc' : dc.totalDegree ≤ 315448 := hdcc.trans (by norm_num)
      omega
  · obtain ⟨⟨nc, dc⟩, hcwit, hncc, hdcc⟩ := hcoeffwit.2.1
    refine ⟨(1 * db * nc, 1 * nb * dc), ?_, ?_, ?_⟩
    · rw [huRScoeff]
      simpa using IsRdecWitness.mul p hinv hcwit
    · simp only
      refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
      have h1db : (1 * db : MvPolynomial Vars (F p)).totalDegree ≤ 315448 := by
        exact le_trans (hone_mul db) hdbb
      have hncc' : nc.totalDegree ≤ 315448 := hncc.trans (by norm_num)
      omega
    · simp only
      refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
      have h1nb : (1 * nb : MvPolynomial Vars (F p)).totalDegree ≤ 315448 := by
        exact le_trans (hone_mul nb) hnbb
      have hdcc' : dc.totalDegree ≤ 315448 := hdcc.trans (by norm_num)
      omega

/-! ## Status, this pass

**Drafted, NOT yet REPL-confirmed** — no build environment available this
session. `curBeforeMonic_leadingCoeff_isRdecWitness` case-splits on
`curBeforeMonic.natDegree ≤ 2` via `interval_cases` and picks the matching
one of `curBeforeMonic_coeff_totalDegree_le`'s three witnesses; `hlc`'s `rfl`
(`leadingCoeff = coeff natDegree`) is `Polynomial.leadingCoeff`'s literal
definition, so this should discharge cleanly, but the `interval_cases hnd :`
naming syntax and whether it produces exactly three goals (`natDegree = 0/1/2`)
in the order assumed here is the one mechanical risk worth flagging —
alternate route if it doesn't fire as written: `have := hdle; interval_cases`
without the explicit binding, then `omega`-close each branch's `natDegree = k`
fact separately before `rw`.

`uRS_coeff_isRdecWitness` composes this with `IsRdecWitness.div` (swap trick
for the inverse) and `IsRdecWitness.mul` (combine with `curBeforeMonic.coeff
i`'s own witness), giving `≤ 630896` uniformly for `i = 0, 1`. Threads
`hlcd_ne` (the one side condition nothing upstream currently derives) as an
explicit hypothesis rather than proving it, per this project's
honest-hypothesis-over-`sorry` practice — narrower and more checkable than
`CrossNondegenerate`'s own current `IsSMulRegular` framing, since it names
exactly one concrete nonvanishing fact (`evalNd` doesn't kill the leading
coefficient's specific witness denominator) rather than an opaque
regularity condition.

**Deliberately not attempted here**: restating `CrossNondegenerateDegreeBound.
lean`'s `crossResultant_totalDegree_le`/`crossResultantV_totalDegree_le` to
consume this `IsRdecWitness`-shaped bound instead of the literal
`towerToRdecK1`-computed-pair hypothesis they currently take — those
theorems want the SPECIFIC `towerToRdec`-computed pair bounded (since
`theData`'s `u1_num`/`u1_den` etc. are literally `towerToRdec`'s output, not
an arbitrary witness), and `IsRdecWitness` genuinely does not pin down the
computed pair's own degree (a witness for `v` is not unique — `(n*k, d*k)`
is also a witness for any `k`, with unboundedly larger degree — so no
"existential witness bound implies computed-pair bound" lemma can exist in
general). This is the file's own real limitation, flagged here rather than
glossed over: closing `CrossNondegenerateDegreeBound.lean`'s hypothesis with
what this file now supplies needs `CrossNondegenerateDegreeBound.lean`
ITSELF rewritten to state its conclusion via `IsRdecWitness` too (bounding
*a* valid witness for the resultant, which is everything the downstream
`IsSMulRegular`/nonvanishing argument actually needs — it only cares about
the resultant's zero/nonzero status, not a canonical representation), not
attempted this pass given the size. This is the natural next step for
`ROADMAP-crossnondegenerate-degree-bound.md`'s remaining assembly work.

**Fix round, this pass** (in response to Claire's build errors): (1) fixed
a genuine argument-order bug in `curBeforeMonic_leadingCoeff_isRdecWitness`'s
own call to `curBeforeMonic_coeff_totalDegree_le` (`sg` and `u0 u1 v0 v1`
were transposed relative to that theorem's real signature -- a copy-paste
slip, not a math error); (2) added `set_option maxHeartbeats 20000000` to
both main theorems (matching this project's existing precedent for
`K2`-tower-heavy elaboration, e.g. `CurBeforeMonicCoeffTotalDegree.lean`'s
own `Qpoly_natDegree_le_four`); (3) replaced the broken `rw [h1]` idiom
(four occurrences) with a factored-out `hone_mul` helper -- the bug was
trying to `rw` a `(1:_).totalDegree = 0` fact directly against a
`(1*x).totalDegree` goal, where `totalDegree 1` is not yet a syntactic
subterm until `totalDegree_mul` has first split the product; `hone_mul`
does that split-then-simplify in one reusable `≤`-lemma instead.

**Second fix round, this pass** (compiler error log): (1)
`curBeforeMonic_natDegree_le_two` is defined in namespace
`Genus2Lean.DecoupledSystem` (see `DecoupledSystemRegular.lean`), not
`Genus2Lean.TheDataDerivation` (this file's own namespace) -- same lesson
already on record from `NpolyCoeffTotalDegreeUniform.lean`'s
`Npoly_natDegree_le_six` bug, now hit again here; fixed by fully qualifying
the call (`Genus2Lean.DecoupledSystem.curBeforeMonic_natDegree_le_two`)
rather than relying on `open`/unqualified lookup. (2) the
`set_option maxHeartbeats 20000000 in` line for `uRS_coeff_isRdecWitness`
was sitting BELOW its doc-comment (between the comment and the `theorem`
line) -- Lean4 rejects this (`unexpected token 'set_option'`); moved above
the doc-comment, matching the project's own standing style rule. (3) all
four `omega` calls in `uRS_coeff_isRdecWitness`'s `fin_cases i` branches
(bounding `(1*db*nc).totalDegree`/`(1*nb*dc).totalDegree` by `630896`) were
missing the OTHER factor's own bound (`nc`/`dc` from `hncc`/`hdcc`,
destructured earlier in the same branch but never turned into a `have` in
scope) -- `omega` only had `h1db`/`h1nb` (bounding `1*db`/`1*nb` alone) and
correctly failed to close `(1*db).totalDegree + nc.totalDegree ≤ 630896`
without a bound on `nc` too. Fixed by adding one small
`have hncc' : nc.totalDegree ≤ 315448 := hncc` (resp. `hdcc'`) immediately
before each `omega`, isolating just the needed numeral fact per this
project's standing heartbeat/recursion-depth mitigation practice (small
`have`s naming only what's needed, rather than handing `omega` the full
context).

**Third fix round, this pass** (compiler error log): (1)
`curBeforeMonic_leadingCoeff_isRdecWitness`'s own conclusion states a
UNIFORM `≤315448` bound, but `curBeforeMonic_coeff_totalDegree_le`'s three
conjuncts (`hw2`/`hw1`/`hw0` destructured from it) carry DIFFERENT literal
bounds (`≤78848`/`≤157710`/`≤315448` respectively) -- an earlier draft
wrongly assumed all three matched the theorem's own `315448` ceiling and
tried to `exact hw1`/`exact hw2` directly, a genuine type mismatch (`157710
≠ 315448`, `78848 ≠ 315448` as literals, even though `≤` holds). Fixed by
destructuring each of `hw0`/`hw1`/`hw2` down to its witness pair and both
`totalDegree` facts, then rebuilding `hw0'`/`hw1'`/`hw2'` at the COMMON
`315448` ceiling via `.trans (by norm_num)` before the `interval_cases`
branches consume them. (2) Same root issue recurred in
`uRS_coeff_isRdecWitness`'s `fin_cases i` branches: `hncc`/`hdcc` (destructured
from whichever of `hcoeffwit`'s conjuncts a branch draws) do NOT always
carry literal bound `315448` -- direct `have hncc' : nc.totalDegree ≤
315448 := hncc` type-mismatches whenever the branch's own conjunct is the
`157710` or `78848` one. Fixed the same way, via `.trans (by norm_num)`
rather than direct ascription -- this is more robust than trying to track
which literal each branch's conjunct carries by hand, since `.trans`
handles any starting bound `≤` the target uniformly. **General lesson for
this file/project**: when a downstream theorem states a uniform numeral
ceiling but its upstream witness-supplying lemma returns DIFFERENT
per-case literal bounds (common whenever a bound is tightened per-branch
upstream, as `curBeforeMonic_coeff_totalDegree_le` does), always weaken
via `.trans (by norm_num)` (or `le_trans _ (by norm_num)`) rather than
`exact`/direct-`:=` — never assume a `≤ N` fact from an upstream case
split already carries the SAME literal `N` the current goal wants, even
when both were written by the same project pass. **Not yet REPL-confirmed**
after this round. Cosmetic linter warnings from the last error log (short
copyright header on the module doc, unused `[DecidableEq Vars]` on both
theorems) are pre-existing lint-only issues, not build failures — left
alone, matching the rest of the project's practice of only suppressing
`linter.style.header`/`linter.unusedDecidableInType` in files that
explicitly choose to (e.g. `RegularSequenceFiniteQuotient.lean`), not as a
blanket default.
-/

end TheDataDerivation
end Genus2Lean
