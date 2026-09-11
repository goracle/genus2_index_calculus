import Mathlib
import Genus2Lean.ZeroD.NpolyTotalDegree

/-!
# `Epoly`'s own `totalDegree` bound — the four-slot case

New this pass. `NpolyTotalDegree.lean`'s own closing note flags this as
"genuinely harder than `Ypoly`'s, since FOUR `bj = 0` slots survive (not
one), so no single `Finset.sum_eq_single` collapse applies" and scopes it
as its own theorem rather than a hasty extension of that file's `Ypoly`
work. This file closes it.

**The concrete shape, computed directly from `rrBasisCandidates`/
`rrBasis5`'s definitions** (not re-derived abstractly — `rrBasis5` is a
literal 5-element list, so its entries are just computed):
`rrBasis5 = [(0,0,0), (2,1,0), (4,2,0), (5,0,1), (6,3,0)]`, i.e. `bidx`
`0,1,2,4` have `bj = 0` with **pairwise distinct** `bi = 0,1,2,3`
respectively, and `bidx = 3` (`= yIdx`, matching `NpolyTotalDegree.lean`'s
own `hyidx : yIdx = 3`) has `bj = 1`. So

    Epoly = C(coeffsOut 0)*X^0 + C(coeffsOut 1)*X^1
          + C(coeffsOut 2)*X^2 + C(coeffsOut 4)*X^3

as a plain 4-term sum (`Finset.sum` over `Fin 5` with the `bidx = 3` term
contributing `0`), and since the four surviving `bi`s are pairwise
distinct, `Epoly.coeff k` picks out AT MOST one nonzero term, matched by
`bi = k`: `coeffsOut 0` if `k = 0`, `coeffsOut 1` if `k = 1`, `coeffsOut 2`
if `k = 2`, `coeffsOut 4` if `k = 3`, and `0` otherwise (`k ≥ 4` or no
matching slot).

**Route to each nonzero slot's `IsRdecWitness` bound**: `coeffsOut bidx`
for `bidx ≠ yIdx` is `cramerSolution col` for `col := ` whichever `Fin 4`
`otherMap` hits `bidx` at (`otherMap_surjOn`, `DataDerivationSolve.lean`),
via the already-proved bridge `coeffsOut_otherMap : coeffsOut (otherMap
col) = cramerSolution col` (same file) — so `cramerSolution_totalDegree_le`
(`CoeffsOutTotalDegree.lean`, `≤ 704` both sides, under the same four
`hAne`/`hRne`/`hDne`/`hιdet_ne`-style hypotheses `coeffsOut_yIdx_
isRdecWitness`'s sibling theorems already carry) gives each of the four
slots' bound directly. Packaged below as `coeffsOut_isRdecWitness`, a
single lemma covering ANY `bidx ≠ yIdx` (not hardcoded to `0,1,2,4`
individually) so it is reusable outside `Epoly` too.

**Not yet REPL-confirmed** — no build environment available this
session; per project convention, Claude drafts, Claire tests.
-/

namespace Genus2Lean
namespace TheDataDerivation

open Polynomial

variable (p : ℕ) [hp : Fact (Nat.Prime p)] [hp2 : Fact (p ≠ 2)]
variable (c0 c1 c2 c3 c4 : F p)

/-- **`yIdx`'s literal value, as a standalone reusable fact.** Proved
inline three times already elsewhere in this project (`DecoupledSystemRegular.
lean`, `NpolyTotalDegree.lean` ×2) via the identical
`interval_cases yIdx <;> revert hyidxeq <;> native_decide` idiom against
`rrBasis5_yIdx_eq` — landed here as its own theorem since this file needs
it too and a fourth inline copy is one too many. -/
theorem yIdx_eq_three : yIdx = 3 := by
  have hlen : rrBasis5.length = 5 := by
    simp [rrBasis5, rrBasisCandidates, List.length_flatMap]
  have hylt : yIdx < rrBasis5.length := hlen ▸ yIdx_lt_five
  have hylt5 : yIdx < 5 := hylt.trans_eq hlen
  have hyidxeq := rrBasis5_yIdx_eq
  interval_cases yIdx <;> revert hyidxeq <;> native_decide

/-- **`coeffsOut` at any non-`yIdx` slot is `cramerSolution` at some
column, hence `IsRdecWitness`-bounded at `≤ 704`.** Threads the same four
nonvanishing hypotheses `cramerSolution_totalDegree_le` itself carries
(`hAne`/`hRne`/`hDne`/`hιdet_ne`, plus the tower-compatibility hypotheses
`hι_t`/`hι_w1`/`hι_w2` and the `hbidx` side condition — all inherited
unchanged, this lemma adds no new mathematical content beyond selecting
`otherMap`'s preimage column via `otherMap_surjOn` and rewriting through
`coeffsOut_otherMap`). Stated for an arbitrary `bidx ≠ yIdx5` rather than
hardcoded to `Epoly`'s four specific slots, so it is directly reusable for
`Npoly.coeff k`'s own later assembly (which will need the same fact at
whichever slots survive there too). -/
theorem coeffsOut_isRdecWitness {Vars : Type*} [DecidableEq Vars]
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
    (bidx : Fin 5) (hbne : bidx ≠ (⟨yIdx, yIdx_lt_five⟩ : Fin 5)) :
    ∃ nd : MvPolynomial Vars (F p) × MvPolynomial Vars (F p),
      IsRdecWitness p ι
        (algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p))))
        (coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 bidx)
        nd ∧ nd.1.totalDegree ≤ 704 ∧ nd.2.totalDegree ≤ 704 := by
  obtain ⟨col, hcol⟩ := otherMap_surjOn bidx hbne
  rw [← hcol, coeffsOut_otherMap]
  exact cramerSolution_totalDegree_le p c0 c1 c2 c3 c4 sg u0 u1 v0 v1 ι
    hι_t hι_w1 hι_w2 hbidx hAne hRne hDne hιdet_ne col

/-! ## `Epoly`'s own value, spelled out as an explicit 4-term sum

Mirrors `Ypoly_eq_C_coeffsOut`'s `Finset.sum_eq_single` collapse exactly,
but singles out FOUR terms (one per `bidx ∈ {0,1,2,4}`) rather than one.
`rrBasis5`'s literal computed value (this file's header) gives each
`bidx`'s `(bi, bj)` pair directly: `bj = 0` for `bidx ∈ {0,1,2,4}` with
`bi = 0,1,2,3` respectively, `bj = 1` only at `bidx = 3 (= yIdx)`. Since
the four `bj = 0` slots have PAIRWISE DISTINCT `bi`, singling out slot
`bidx0`'s term (all others — including `yIdx`'s — vanish, either because
`bj ≠ 0` there or because `bi ≠ bi0`) is the same
`fin_cases bidx <;> native_decide`-style argument `Ypoly_eq_C_coeffsOut`'s
`hsingle`/`hcases3` already use successfully, just checking `bi = bi0`
(a numeral equality) in place of `bidx = yidx5` (a `Fin 5` equality). -/

/-- **Single out `bidxK`'s contribution to `Epoly.coeff k`**, for each of
the four concrete `(bidxK, k) ∈ {(0,0),(1,1),(2,2),(4,3)}` pairs
separately. Unlike `Ypoly_eq_C_coeffsOut`'s `hsingle` (which shows the
whole OTHER terms vanish as polynomials, valid there since exactly one
slot has `bj = 1` at all), `Epoly` genuinely has four nonzero polynomial
terms, so no `bidx ≠ bidxK ⟹ term = 0` claim is true here — e.g. slot `1`'s
term `C(coeffsOut 1) * X` is not the zero polynomial. The correct claim,
proved instead, is at the COEFFICIENT level: for `bidx ≠ bidxK`, the term's
`.coeff k` (not the term itself) vanishes — either because `bj ≠ 0` there
(whole term `0`, `bidx = yIdx`'s case) or because `bj = 0` but `bi ≠ k`
(`(C _ * X^bi).coeff k = 0` since `k ≠ bi`, via `coeff_C_mul`/`coeff_X_pow`
— the same two lemmas `Ypoly_coeff_isRdecWitness` already uses safely).
Both branches decided against `rrBasis5`'s 5 literal entries via
`fin_cases bidx <;> native_decide`, the same idiom `Ypoly_eq_C_coeffsOut`'s
own `hcases3` already uses successfully. -/
theorem Epoly_hsingle0 (u0 u1 v0 v1 : F p) :
    ∀ bidx : Fin 5, bidx ≠ (⟨0, by norm_num⟩ : Fin 5) →
      (let (_, bi, bj) := rrBasis5.getD bidx.val (0, 0, 0)
       if bj = 0 then C (coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 bidx) *
         (X : Polynomial (K2 p c0 c1 c2 c3 c4)) ^ bi else 0).coeff 0 = 0 := by
  intro bidx hne
  have hcases : bidx = (⟨0, by norm_num⟩ : Fin 5) ∨
      (rrBasis5.getD bidx.val (0, 0, 0)).2.2 ≠ 0 ∨
      (rrBasis5.getD bidx.val (0, 0, 0)).2.1 ≠ 0 := by
    fin_cases bidx <;> native_decide
  rcases hcases with h | h | h
  · exact absurd h hne
  · dsimp; rw [if_neg h]; simp
  · dsimp
    rcases eq_or_ne (rrBasis5.getD bidx.val (0, 0, 0)).2.2 0 with hbj | hbj
    · rw [if_pos hbj, coeff_C_mul_X_pow, if_neg (Ne.symm h)]
    · rw [if_neg hbj]; simp

theorem Epoly_hsingle1 (u0 u1 v0 v1 : F p) :
    ∀ bidx : Fin 5, bidx ≠ (⟨1, by norm_num⟩ : Fin 5) →
      (let (_, bi, bj) := rrBasis5.getD bidx.val (0, 0, 0)
       if bj = 0 then C (coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 bidx) *
         (X : Polynomial (K2 p c0 c1 c2 c3 c4)) ^ bi else 0).coeff 1 = 0 := by
  intro bidx hne
  have hcases : bidx = (⟨1, by norm_num⟩ : Fin 5) ∨
      (rrBasis5.getD bidx.val (0, 0, 0)).2.2 ≠ 0 ∨
      (rrBasis5.getD bidx.val (0, 0, 0)).2.1 ≠ 1 := by
    fin_cases bidx <;> native_decide
  rcases hcases with h | h | h
  · exact absurd h hne
  · dsimp; rw [if_neg h]; simp
  · dsimp
    rcases eq_or_ne (rrBasis5.getD bidx.val (0, 0, 0)).2.2 0 with hbj | hbj
    · rw [if_pos hbj, coeff_C_mul_X_pow, if_neg (Ne.symm h)]
    · rw [if_neg hbj]; simp

theorem Epoly_hsingle2 (u0 u1 v0 v1 : F p) :
    ∀ bidx : Fin 5, bidx ≠ (⟨2, by norm_num⟩ : Fin 5) →
      (let (_, bi, bj) := rrBasis5.getD bidx.val (0, 0, 0)
       if bj = 0 then C (coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 bidx) *
         (X : Polynomial (K2 p c0 c1 c2 c3 c4)) ^ bi else 0).coeff 2 = 0 := by
  intro bidx hne
  have hcases : bidx = (⟨2, by norm_num⟩ : Fin 5) ∨
      (rrBasis5.getD bidx.val (0, 0, 0)).2.2 ≠ 0 ∨
      (rrBasis5.getD bidx.val (0, 0, 0)).2.1 ≠ 2 := by
    fin_cases bidx <;> native_decide
  rcases hcases with h | h | h
  · exact absurd h hne
  · dsimp; rw [if_neg h]; simp
  · dsimp
    rcases eq_or_ne (rrBasis5.getD bidx.val (0, 0, 0)).2.2 0 with hbj | hbj
    · rw [if_pos hbj, coeff_C_mul_X_pow, if_neg (Ne.symm h)]
    · rw [if_neg hbj]; simp

theorem Epoly_hsingle4 (u0 u1 v0 v1 : F p) :
    ∀ bidx : Fin 5, bidx ≠ (⟨4, by norm_num⟩ : Fin 5) →
      (let (_, bi, bj) := rrBasis5.getD bidx.val (0, 0, 0)
       if bj = 0 then C (coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 bidx) *
         (X : Polynomial (K2 p c0 c1 c2 c3 c4)) ^ bi else 0).coeff 3 = 0 := by
  intro bidx hne
  have hcases : bidx = (⟨4, by norm_num⟩ : Fin 5) ∨
      (rrBasis5.getD bidx.val (0, 0, 0)).2.2 ≠ 0 ∨
      (rrBasis5.getD bidx.val (0, 0, 0)).2.1 ≠ 3 := by
    fin_cases bidx <;> native_decide
  rcases hcases with h | h | h
  · exact absurd h hne
  · dsimp; rw [if_neg h]; simp
  · dsimp
    rcases eq_or_ne (rrBasis5.getD bidx.val (0, 0, 0)).2.2 0 with hbj | hbj
    · rw [if_pos hbj, coeff_C_mul_X_pow, if_neg (Ne.symm h)]
    · rw [if_neg hbj]; simp

/-- **`Epoly.coeff k`'s value for `k ∈ {0,1,2,3}`**, via commuting `.coeff
k` with `Epoly`'s defining sum (`Polynomial.finsetSum_coeff`) and then
`Finset.sum_eq_single` with the matching `Epoly_hsingleK` lemma above to
collapse every other term's contribution to `0`. Unlike the withdrawn
"`Epoly` itself equals a single term" approach, this is stated and proved
purely at the `.coeff k` level, which is both true and enough for
`Epoly_coeff_isRdecWitness`'s purposes. Uses `coeff_C_mul_X_pow` directly
(one lemma giving `(C x * X^bi).coeff k = if k = bi then x else 0`
outright) rather than `coeff_C_mul`/`coeff_X_pow` separately, since the
two-lemma route left `simp` unable to decide the resulting `if` against an
un-evaluated `bi`-expression. The surviving `bi` here is the LITERAL `0`
(from `rrBasis5`'s table, this file's header), so the `if 0 = 0` condition
resolves by `rfl`/`if_pos rfl` once `rw` reaches it, no `simp` guessing
needed. -/
theorem Epoly_coeff0 (u0 u1 v0 v1 : F p) :
    (Epoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff 0 =
      coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 (⟨0, by norm_num⟩ : Fin 5) := by
  have hcoeff : (Epoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff 0 =
      ∑ bidx : Fin 5,
        (let (_, bi, bj) := rrBasis5.getD bidx.val (0, 0, 0)
         if bj = 0 then C (coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 bidx) *
           (X : Polynomial (K2 p c0 c1 c2 c3 c4)) ^ bi else 0).coeff 0 := by
    unfold Epoly; exact Polynomial.finsetSum_coeff _ _ _
  rw [hcoeff, Finset.sum_eq_single (⟨0, by norm_num⟩ : Fin 5)
    (fun bidx _ hne => Epoly_hsingle0 p c0 c1 c2 c3 c4 u0 u1 v0 v1 bidx hne)
    (fun h => absurd (Finset.mem_univ _) h)]
  have hval : rrBasis5.getD 0 (0, 0, 0) = (0, 0, 0) := by native_decide
  simp only [hval, coeff_C_mul_X_pow]
  simp

theorem Epoly_coeff1 (u0 u1 v0 v1 : F p) :
    (Epoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff 1 =
      coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 (⟨1, by norm_num⟩ : Fin 5) := by
  have hcoeff : (Epoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff 1 =
      ∑ bidx : Fin 5,
        (let (_, bi, bj) := rrBasis5.getD bidx.val (0, 0, 0)
         if bj = 0 then C (coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 bidx) *
           (X : Polynomial (K2 p c0 c1 c2 c3 c4)) ^ bi else 0).coeff 1 := by
    unfold Epoly; exact Polynomial.finsetSum_coeff _ _ _
  rw [hcoeff, Finset.sum_eq_single (⟨1, by norm_num⟩ : Fin 5)
    (fun bidx _ hne => Epoly_hsingle1 p c0 c1 c2 c3 c4 u0 u1 v0 v1 bidx hne)
    (fun h => absurd (Finset.mem_univ _) h)]
  have hval : rrBasis5.getD 1 (0, 0, 0) = (2, 1, 0) := by native_decide
  simp only [hval, coeff_C_mul_X_pow]
  simp

theorem Epoly_coeff2 (u0 u1 v0 v1 : F p) :
    (Epoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff 2 =
      coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 (⟨2, by norm_num⟩ : Fin 5) := by
  have hcoeff : (Epoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff 2 =
      ∑ bidx : Fin 5,
        (let (_, bi, bj) := rrBasis5.getD bidx.val (0, 0, 0)
         if bj = 0 then C (coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 bidx) *
           (X : Polynomial (K2 p c0 c1 c2 c3 c4)) ^ bi else 0).coeff 2 := by
    unfold Epoly; exact Polynomial.finsetSum_coeff _ _ _
  rw [hcoeff, Finset.sum_eq_single (⟨2, by norm_num⟩ : Fin 5)
    (fun bidx _ hne => Epoly_hsingle2 p c0 c1 c2 c3 c4 u0 u1 v0 v1 bidx hne)
    (fun h => absurd (Finset.mem_univ _) h)]
  have hval : rrBasis5.getD 2 (0, 0, 0) = (4, 2, 0) := by native_decide
  simp only [hval, coeff_C_mul_X_pow]
  simp

theorem Epoly_coeff4 (u0 u1 v0 v1 : F p) :
    (Epoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff 3 =
      coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 (⟨4, by norm_num⟩ : Fin 5) := by
  have hcoeff : (Epoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff 3 =
      ∑ bidx : Fin 5,
        (let (_, bi, bj) := rrBasis5.getD bidx.val (0, 0, 0)
         if bj = 0 then C (coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 bidx) *
           (X : Polynomial (K2 p c0 c1 c2 c3 c4)) ^ bi else 0).coeff 3 := by
    unfold Epoly; exact Polynomial.finsetSum_coeff _ _ _
  rw [hcoeff, Finset.sum_eq_single (⟨4, by norm_num⟩ : Fin 5)
    (fun bidx _ hne => Epoly_hsingle4 p c0 c1 c2 c3 c4 u0 u1 v0 v1 bidx hne)
    (fun h => absurd (Finset.mem_univ _) h)]
  have hval : rrBasis5.getD 4 (0, 0, 0) = (6, 3, 0) := by native_decide
  simp only [hval, coeff_C_mul_X_pow]
  simp

/-- **`k ≥ 4`: `Epoly.coeff k = 0`.** Every surviving slot has `bi ≤ 3 <
k`, so every term's `.coeff k` vanishes — the same per-slot argument as
`Epoly_hsingleN` above (`bj ≠ 0` or `bi ≠ k`), but now true for ALL five
`bidx` simultaneously rather than four-of-five, so `Finset.sum_eq_zero`
(not `sum_eq_single`) is the right combinator, mirroring the
`Finset.sum_eq_zero` idiom already used successfully elsewhere in this
project (`PrincipalWitness.lean`). Uses `coeff_C_mul_X_pow` (one lemma,
`if k = bi then x else 0` outright) rather than `coeff_C_mul`/`coeff_X_pow`
separately — same fix as `Epoly_hsingleN`/`Epoly_coeffN` above. -/
theorem Epoly_coeff_ge_four (u0 u1 v0 v1 : F p) (k : ℕ) (hk : 4 ≤ k) :
    (Epoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff k = 0 := by
  have hcoeff : (Epoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff k =
      ∑ bidx : Fin 5,
        (let (_, bi, bj) := rrBasis5.getD bidx.val (0, 0, 0)
         if bj = 0 then C (coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 bidx) *
           (X : Polynomial (K2 p c0 c1 c2 c3 c4)) ^ bi else 0).coeff k := by
    unfold Epoly; exact Polynomial.finsetSum_coeff _ _ _
  rw [hcoeff]
  apply Finset.sum_eq_zero
  intro bidx _
  have hbi_lt : (rrBasis5.getD bidx.val (0, 0, 0)).2.1 ≤ 3 := by
    fin_cases bidx <;> native_decide
  dsimp
  rcases eq_or_ne (rrBasis5.getD bidx.val (0, 0, 0)).2.2 0 with hbj | hbj
  · rw [if_pos hbj, coeff_C_mul_X_pow,
      if_neg (show k ≠ (rrBasis5.getD bidx.val (0, 0, 0)).2.1 from by omega)]
  · rw [if_neg hbj]; simp

/-- **`Epoly.coeff k`'s `IsRdecWitness` bound.** `Epoly_coeff0/1/2/4`
identify `Epoly.coeff k` outright with `coeffsOut` at the matching slot for
`k = 0,1,2,3` respectively; `Epoly_coeff_ge_four` handles `k ≥ 4`. Then
`coeffsOut_isRdecWitness` (this file, above) supplies the `IsRdecWitness`
bound at the corresponding `bidx ∈ {0,1,2,4}` for the four small `k`; `k ≥
4` gets the trivial zero-witness `(0,1)`. -/
theorem Epoly_coeff_isRdecWitness {Vars : Type*} [DecidableEq Vars]
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
        ((Epoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff k) nd ∧
      nd.1.totalDegree ≤ 704 ∧ nd.2.totalDegree ≤ 704 := by
  have hyidx : yIdx = 3 := yIdx_eq_three
  have hne0 : (⟨0, by norm_num⟩ : Fin 5) ≠ (⟨yIdx, yIdx_lt_five⟩ : Fin 5) := by
    simp [Fin.ext_iff, hyidx]
  have hne1 : (⟨1, by norm_num⟩ : Fin 5) ≠ (⟨yIdx, yIdx_lt_five⟩ : Fin 5) := by
    simp [Fin.ext_iff, hyidx]
  have hne2 : (⟨2, by norm_num⟩ : Fin 5) ≠ (⟨yIdx, yIdx_lt_five⟩ : Fin 5) := by
    simp [Fin.ext_iff, hyidx]
  have hne4 : (⟨4, by norm_num⟩ : Fin 5) ≠ (⟨yIdx, yIdx_lt_five⟩ : Fin 5) := by
    simp [Fin.ext_iff, hyidx]
  rcases lt_or_ge k 4 with hk4 | hk4
  swap
  · rw [Epoly_coeff_ge_four p c0 c1 c2 c3 c4 u0 u1 v0 v1 k hk4]
    exact ⟨(0, 1), by unfold IsRdecWitness; simp, by simp, by simp⟩
  interval_cases k
  · rw [Epoly_coeff0]
    exact coeffsOut_isRdecWitness p c0 c1 c2 c3 c4 sg u0 u1 v0 v1 ι
      hι_t hι_w1 hι_w2 hbidx hAne hRne hDne hιdet_ne _ hne0
  · rw [Epoly_coeff1]
    exact coeffsOut_isRdecWitness p c0 c1 c2 c3 c4 sg u0 u1 v0 v1 ι
      hι_t hι_w1 hι_w2 hbidx hAne hRne hDne hιdet_ne _ hne1
  · rw [Epoly_coeff2]
    exact coeffsOut_isRdecWitness p c0 c1 c2 c3 c4 sg u0 u1 v0 v1 ι
      hι_t hι_w1 hι_w2 hbidx hAne hRne hDne hιdet_ne _ hne2
  · rw [Epoly_coeff4]
    exact coeffsOut_isRdecWitness p c0 c1 c2 c3 c4 sg u0 u1 v0 v1 ι
      hι_t hι_w1 hι_w2 hbidx hAne hRne hDne hιdet_ne _ hne4

/-! ## Status, this pass

**Drafted, not yet REPL-confirmed.** All pieces are now written at the
correct level (`.coeff k`, not whole-polynomial equalities — an earlier
draft this pass incorrectly tried to show `Epoly` equals a single term
outright, which is false since `Epoly` genuinely has four nonzero terms;
caught before it could compile to something subtly wrong, and replaced
with the `.coeff k`-level `Epoly_coeff0/1/2/4`/`Epoly_coeff_ge_four`
lemmas actually used here). Two things remain to verify against a real
build: (1) whether `Epoly_hsingle0/1/2/4`'s `fin_cases bidx <;>
native_decide` step for the 3-way disjunction closes cleanly (mirrors
`Ypoly_eq_C_coeffsOut`'s own `hcases3`, but with a 3-way rather than
2-way disjunction, since `Epoly` needs both a `bj`-check and a `bi`-check
to single out a slot, unlike `Ypoly`'s single `bj = 1` check); (2) whether
`yIdx_eq_three`'s copied proof still elaborates standalone outside
`DecoupledSystemRegular.lean`'s/`NpolyTotalDegree.lean`'s own context. -/

end TheDataDerivation
end Genus2Lean
