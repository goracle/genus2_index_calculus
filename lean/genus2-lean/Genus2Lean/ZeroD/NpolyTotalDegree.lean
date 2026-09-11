import Mathlib
import Genus2Lean.ZeroD.CoeffsOutTotalDegree

/-!
# `Npoly`'s own `totalDegree` bound — scoping, plus the first two pieces

New this pass. `ROADMAP-crossnondegenerate-degree-bound.md`'s own closing
note (see `CoeffsOutTotalDegree.lean`'s header) flags this as the next
assembly layer once `coeffsOut`/`cramerSolution` are bounded: `Epoly`,
`Ypoly`, `fAtX` (`DataDerivationSolve.lean`) are `Polynomial (K2 p ...)`
values built from `coeffsOut`, and `Npoly := Epoly^2 - fAtX * Ypoly^2`
(same file) is the object whose COEFFICIENTS (not `Npoly` itself, which
has no single "degree" in the `MvPolynomial` sense — each `Npoly.coeff k`
is a separate `K2`-element) are the base case `D` that `crossResultant_
totalDegree_le`/`crossResultantV_totalDegree_le` (`CrossNondegenerateDegreeBound.
lean`) still carry as an open hypothesis, per that file's own closing note.

**What this file scopes, not yet fully closes**: a `totalDegree` bound on
`Npoly.coeff k` for every `k`, via `IsRdecWitness`. The route:

1. `Epoly.coeff k`/`Ypoly.coeff k` are each either `0` or a single
   `coeffsOut bidx` value (`Epoly`/`Ypoly`'s own `∑ bidx, if bj = 0/1 then
   C (coeffsOut bidx) * X^bi else 0` definition collapses to a SINGLE
   nonzero summand per `k`, since distinct `bidx`s have distinct `bi`
   under each `bj`-branch — not yet proved here, flagged as step A).
   `coeffsOut bidx`'s own `IsRdecWitness` bound is `cramerSolution_
   totalDegree_le`/`coeffsOut_yIdx_isRdecWitness` (`CoeffsOutTotalDegree.
   lean`, both ≤704), so `Epoly.coeff k`/`Ypoly.coeff k` inherit that bound
   directly, for the (finitely many, `k ≤ 3`/`k = 0`) nonzero slots, `0`
   trivially witnessed (`IsRdecWitness _ (0,1)`) elsewhere.
2. `fAtX.coeff k = algebraMap (F p) (K2 ...) (curvePoly.coeff k)` — a
   PLAIN CONSTANT pushed through the tower's algebra map, not a
   `coeffsOut`-derived value at all. **This file's first proved piece**:
   `algebraMap_Fp_isRdecWitness` below gives this an unconditional
   `IsRdecWitness` pair `(C x, 1)`, bound `(0, 0)` — no hypothesis on `ι`
   beyond it being a ring hom, since `F p = ZMod p` makes every element a
   `ℕ`-cast, and ring homs agree on `ℕ`-casts automatically (`map_natCast`)
   — exactly the argument `towerToRdec_spec`'s own `hcomp` step already
   uses (`DataDerivationMumford.lean`, `ZMod.natCast_zmod_surjective` +
   `RingHom.comp_apply`), just extracted here as its own reusable fact
   rather than inlined in that proof.
3. `Npoly.coeff k`'s own witness needs `IsRdecWitness` to survive `+`,
   `-`, `^2`, and `*` at the COEFFICIENT level (`Polynomial.coeff_add`/
   `coeff_sub`/`coeff_mul`/`coeff_pow`, the last unrolling `Npoly.coeff k`
   into a `Finset.sum` over `Finset.antidiagonal`-style index pairs, NOT
   just the two witnesses combining once). `IsRdecWitness.mul`
   (`TowerToRdecMul.lean`) and `IsRdecWitness.neg` (`RhsVecTotalDegree.
   lean`) already exist; `IsRdecWitness.add` (added below, this file's
   second proved piece) is the missing combinator — cross-multiplied
   addition, `(n1,d1)`/`(n2,d2)` witnessing `v1`/`v2` combine to
   `(n1*d2 + n2*d1, d1*d2)` witnessing `v1+v2`, direct `map_add`/`map_mul`
   + `ring` algebra, no new mathematical content, mirroring `.mul`'s own
   proof shape exactly.

**Not yet attempted in this file** (steps A above, and the full
`Polynomial.coeff_mul`/`coeff_pow` unrolling for step 3): this is
substantial remaining bookkeeping — `Npoly.coeff k`'s `coeff_pow`
expansion for `Epoly^2` alone is a sum over `Finset.antidiagonal k`
(itself needing `IsRdecWitness.add` applied `|antidiagonal k|`-many
times, not just once), and `fAtX * Ypoly^2`'s `coeff_mul` expansion is a
further such sum. Scoped here rather than guessed at — the next pass's
concrete next step is a `Npoly_coeff_isRdecWitness`-shaped theorem in a
follow-up file (or lower in this one, once step A is proved), NOT
attempted this pass given the size. `IsRdecWitness.add`/
`algebraMap_Fp_isRdecWitness` are self-contained and useful independent
of that remaining work, which is why they're landed now rather than held
back.

**Not yet REPL-confirmed** — no build environment available this
session; per project convention, Claude drafts, Claire tests.
-/

namespace Genus2Lean
namespace TheDataDerivation

open Polynomial

variable (p : ℕ) [hp : Fact (Nat.Prime p)] [hp2 : Fact (p ≠ 2)]

/-- **Addition, cross-multiplied.** Given valid witnesses for `a` and `b`
under the SAME `ι`/`evalNd` pair, the cross-multiplied pair
`(na*db + nb*da, da*db)` is a valid witness for `a + b` — mirrors
`IsRdecWitness.mul`'s proof exactly (`map_add`/`map_mul` + `ring`, no
nonzero-denominator side condition needed, same reason `.mul` needs
none: the predicate is a plain equation, not an honest fraction). -/
theorem IsRdecWitness.add {Vars K L : Type*} [CommRing K] [CommRing L]
    {ι : K →+* L} {evalNd : MvPolynomial Vars (F p) →+* L}
    {a b : K} {na da nb db : MvPolynomial Vars (F p)}
    (ha : IsRdecWitness p ι evalNd a (na, da))
    (hb : IsRdecWitness p ι evalNd b (nb, db)) :
    IsRdecWitness p ι evalNd (a + b) (na * db + nb * da, da * db) := by
  unfold IsRdecWitness at *
  simp only [map_add, map_mul] at *
  rw [ha, hb]
  ring

/-- **Every constant of `F p`, pushed into `K2` via the tower's algebra
map, has the trivial `IsRdecWitness` pair `(C x, 1)` — unconditionally,
no hypothesis on `ι` beyond being a ring hom.** Needed for `fAtX.coeff k
= algebraMap (F p) (K2 ...) (curvePoly.coeff k)` (`DataDerivationSolve.
lean`), a plain constant, not a `coeffsOut`-derived value.

**Why no `hι_t`/`hι_w1`/`hι_w2`-style hypothesis is needed here** (unlike
`towerToRdec_isRdecWitness`/every other `IsRdecWitness` lemma in this
project so far): those hypotheses pin `ι`'s action on the tower's
GENERATORS (`X i`, `w1`, `w2`), which is genuinely extra information not
determined by `ι` being a ring hom alone. A plain constant `x : F p =
ZMod p`, by contrast, is ALWAYS a `ℕ`-cast (`ZMod.natCast_zmod_
surjective`), and every ring hom agrees with every other on `ℕ`-casts
unconditionally (`map_natCast`) — so `ι (algebraMap (F p) (K2 ...) x)`
and `evalNd (C x)` are both forced to equal `((n : ℕ) : L)` for the same
`n`, with no freedom for `ι`/`evalNd` to disagree, regardless of which
ring homs they are. This is exactly the argument `towerToRdec_spec`'s own
`hcomp` step already uses (`DataDerivationMumford.lean`), extracted here
as its own reusable fact.

**`MvPolynomial.C`'s own nat-cast lemma name not independently confirmed
against this snapshot** — the proof closes via a bare `simp only
[map_natCast, map_one, one_mul]`, relying on `simp`'s own `RingHomClass`
matching to fire `map_natCast` on `MvPolynomial.C` (bundled as a ring
hom) without naming that specific instance lemma directly, so this
should be robust to whichever exact name Mathlib uses internally — but
genuinely not yet checked against this project's own Mathlib snapshot;
flagged rather than asserted, per this project's own convention of not
guessing at unconfirmed API. -/
theorem algebraMap_Fp_isRdecWitness {Vars : Type*}
    (ι : K2 p c0 c1 c2 c3 c4 →+* FractionRing (MvPolynomial Vars (F p)))
    (x : F p) :
    IsRdecWitness p ι
      (algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p))))
      (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) x)
      (MvPolynomial.C x, 1) := by
  obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective x
  unfold IsRdecWitness
  -- Goal: `evalNd (C (n : F p)) = evalNd 1 * ι (algebraMap (F p) (K2 ...) (n : F p))`.
  -- Both sides reduce to `(n : L)` via `map_natCast` on `ι`/`evalNd` respectively
  -- (`ι`/`evalNd` are ring homs, so both send the `ℕ`-cast `(n : F p)`, resp.
  -- its image, to the literal `ℕ`-cast in `L` — no freedom for them to disagree,
  -- regardless of which specific ring homs they are), plus `MvPolynomial.C`
  -- commuting with `ℕ`-casts (`map_natCast` applied to the ring hom `C`
  -- itself, since `MvPolynomial.C` is a `RingHom`/bundled as such via
  -- `MvPolynomial.C_natCast`/an equivalent `simp` normal form).
  simp only [map_natCast, map_one, one_mul]

/-! ## Step A: `Ypoly = C (coeffsOut yIdx)` outright

**Route**: reuses `Ypoly_natDegree_le_zero`'s own proof shape
(`DecoupledSystemRegular.lean`) — `yIdx = 3` via `rrBasis5_yIdx_eq` plus
`interval_cases`/`native_decide`, then `Finset.sum_eq_single` collapses
`Ypoly`'s `Fin 5` sum to its single `bj = 1` summand (every other index
ruled out via `fin_cases bidx <;> native_decide` against `rrBasis5`'s
literal five entries) — but stops one step earlier, at the EQUATION
`Ypoly = C (coeffsOut yIdx)` itself, rather than pushing on to a
`natDegree` bound. That equation is the reusable fact `Ypoly.coeff k`'s
`IsRdecWitness` bound (below) actually needs; `Ypoly_natDegree_le_zero`
proves a strictly weaker consequence of it inline and does not export the
equation itself, hence re-derived here rather than imported. -/

theorem Ypoly_eq_C_coeffsOut (c0 c1 c2 c3 c4 u0 u1 v0 v1 : F p) :
    Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1 =
      C (coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1
        (⟨3, by norm_num⟩ : Fin 5)) := by
  have hlen : rrBasis5.length = 5 := by
    simp [rrBasis5, rrBasisCandidates, List.length_flatMap]
  have hylt : yIdx < rrBasis5.length := hlen ▸ yIdx_lt_five
  have hyidx : yIdx = 3 := by
    have hylt5 : yIdx < 5 := hylt.trans_eq hlen
    have hyidxeq := rrBasis5_yIdx_eq
    interval_cases yIdx <;> revert hyidxeq <;> native_decide
  -- `yidx5` is `⟨yIdx, _⟩` (matching `rrBasis5_yIdx_eq`'s own indexing
  -- exactly, no `.val` mismatch to bridge), with `hyidx5_three`
  -- separately recording its numeral value for the theorem statement's
  -- own `⟨3, _⟩` literal.
  set yidx5 : Fin 5 := ⟨yIdx, yIdx_lt_five⟩ with hyidx5_def
  have hyidx5_three : yidx5 = (⟨3, by norm_num⟩ : Fin 5) := by
    apply Fin.ext; simpa [yidx5] using hyidx
  have hsingle : ∀ bidx : Fin 5, bidx ≠ yidx5 →
      (let (_, bi, bj) := rrBasis5.getD bidx.val (0, 0, 0)
       if bj = 1 then C (coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 bidx) *
         (X : Polynomial (K2 p c0 c1 c2 c3 c4)) ^ bi else 0) = 0 := by
    intro bidx hne
    have hcases3 : bidx = (⟨3, by norm_num⟩ : Fin 5) ∨
        (rrBasis5.getD bidx.val (0, 0, 0)).2.2 ≠ 1 := by
      fin_cases bidx <;> native_decide
    have hcases : bidx = yidx5 ∨ (rrBasis5.getD bidx.val (0, 0, 0)).2.2 ≠ 1 := by
      rcases hcases3 with h | h
      · left; simpa [hyidx5_three] using h
      · exact Or.inr h
    rcases hcases with h | h
    · exact absurd h hne
    · dsimp; rw [if_neg h]
  have hcollapse : Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1 =
      (let (_, bi, bj) := rrBasis5.getD yidx5.val (0, 0, 0)
       if bj = 1 then C (coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 yidx5) *
         (X : Polynomial (K2 p c0 c1 c2 c3 c4)) ^ bi else 0) := by
    unfold Ypoly
    exact Finset.sum_eq_single yidx5 (fun bidx _ hne => hsingle bidx hne)
      (fun h => absurd (Finset.mem_univ _) h)
  rw [hcollapse]
  show (let (_, bi, bj) := rrBasis5.getD yidx5.val (0, 0, 0)
      if bj = 1 then C (coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 yidx5) *
        (X : Polynomial (K2 p c0 c1 c2 c3 c4)) ^ bi else 0) =
      C (coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 (⟨3, by norm_num⟩ : Fin 5))
  rw [show yidx5.val = yIdx from rfl, rrBasis5_yIdx_eq]
  simp [hyidx5_three]

/-- **`Ypoly.coeff k`'s `IsRdecWitness` bound.** Immediate corollary of
`Ypoly_eq_C_coeffsOut`: `Ypoly = C (coeffsOut yIdx) * X ^ 0` (`pow_zero`/
`mul_one`), so `coeff_C_mul`/`coeff_X_pow` (the established combination
this project's `CAWitness*.lean` family already uses via `simp`, not the
unconfirmed `Polynomial.coeff_C_mul_X`) give `Ypoly.coeff k = if k = 0
then coeffsOut yIdx else 0` outright — no `Finset.antidiagonal`/`coeff_pow`
machinery needed at all (that's `Npoly.coeff k`'s own later problem, not
`Ypoly`'s). **`coeffsOut yIdx = 1` on the nose** (`coeffsOut`'s own
`dif_pos` branch, since `(⟨3,_⟩ : Fin 5).val = yIdx` by `Ypoly_eq_C_
coeffsOut`'s own already-proved `hyidx`-equivalent fact, re-derived here
rather than threaded through since `Ypoly_eq_C_coeffsOut` doesn't export
it separately) — so the `k = 0` branch reduces to `IsRdecWitness _ 1 _`,
inheriting `coeffsOut_yIdx_isRdecWitness`'s witness pair directly (that
theorem is stated for the literal value `1`, matching after the `dif_pos`
rewrite, bound `(384, 320)`, both `≤ 704`); the `k ≠ 0` branch gets the
trivial zero-witness `(0, 1)` (`IsRdecWitness p ι evalNd 0 (0, 1)` reduces
to `evalNd 0 = evalNd 1 * ι 0`, i.e. `0 = 0`, via `map_zero`/`map_one`/
`mul_zero`), bound `(0, 0)` — both branches' bounds are `≤ 704` uniformly,
so no `max`/case-split on the bound itself is needed downstream. -/
theorem Ypoly_coeff_isRdecWitness {Vars : Type*} [DecidableEq Vars]
    (u0 u1 v0 v1 : F p)
    (ι : K2 p c0 c1 c2 c3 c4 →+* FractionRing (MvPolynomial Vars (F p)))
    (k : ℕ) :
    ∃ nd : MvPolynomial Vars (F p) × MvPolynomial Vars (F p),
      IsRdecWitness p ι
        (algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p))))
        ((Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff k) nd ∧
      nd.1.totalDegree ≤ 704 ∧ nd.2.totalDegree ≤ 704 := by
  have hlen : rrBasis5.length = 5 := by
    simp [rrBasis5, rrBasisCandidates, List.length_flatMap]
  have hylt : yIdx < rrBasis5.length := hlen ▸ yIdx_lt_five
  have hyidx : yIdx = 3 := by
    have hylt5 : yIdx < 5 := hylt.trans_eq hlen
    have hyidxeq := rrBasis5_yIdx_eq
    interval_cases yIdx <;> revert hyidxeq <;> native_decide
  have hcoeffsOut_one : coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 (⟨3, by norm_num⟩ : Fin 5) = 1 := by
    unfold coeffsOut
    rw [dif_pos (show ((⟨3, by norm_num⟩ : Fin 5) : Fin 5).val = yIdx from hyidx.symm)]
  have hYeq : Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1 = C (1 : K2 p c0 c1 c2 c3 c4) * X ^ 0 := by
    rw [pow_zero, mul_one, ← hcoeffsOut_one]
    exact Ypoly_eq_C_coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1
  rw [hYeq]
  rcases eq_or_ne k 0 with hk | hk
  · have hck : (C (1 : K2 p c0 c1 c2 c3 c4) * X ^ 0).coeff k = 1 := by
      subst hk; simp [coeff_C_mul, coeff_X_pow]
    rw [hck]
    obtain ⟨nd, hwit, hn, hd⟩ := coeffsOut_yIdx_isRdecWitness p c0 c1 c2 c3 c4 ι
    exact ⟨nd, hwit, hn.trans (by norm_num), hd.trans (by norm_num)⟩
  · have hck : (C (1 : K2 p c0 c1 c2 c3 c4) * X ^ 0).coeff k = 0 := by
      simp [coeff_C_mul, coeff_X_pow, hk, Ne.symm hk, Polynomial.coeff_one]
    rw [hck]
    exact ⟨(0, 1), by unfold IsRdecWitness; simp, by simp, by simp⟩

/-! ## Status, this pass

**Drafted, not yet REPL-confirmed.** Lands `IsRdecWitness.add` (the
missing addition combinator, alongside the already-proved `.mul`/`.neg`/
`.div`), `algebraMap_Fp_isRdecWitness` (the constant-embedding witness
`fAtX`'s coefficients need, unconditional on `ι` beyond being a ring
hom — proved via the same `ZMod.natCast_zmod_surjective` argument
`towerToRdec_spec`'s own `hcomp` step already relies on,
`DataDerivationMumford.lean`), `Ypoly_eq_C_coeffsOut` (`Ypoly`'s exact
value as a single `C (coeffsOut _)` term, re-derived from `Ypoly_
natDegree_le_zero`'s own proof shape, `DecoupledSystemRegular.lean`), and
(this pass, new) `Ypoly_coeff_isRdecWitness` — `Ypoly.coeff k`'s
`IsRdecWitness` bound, closing item A's `Ypoly` half in full: `Ypoly =
C 1 * X ^ 0` (`coeffsOut yIdx = 1` on the nose, via `coeffsOut`'s own
`dif_pos` branch once `yIdx = 3` is known), so `coeff_C_mul`/`coeff_X_pow`
gives `Ypoly.coeff k = if k = 0 then 1 else 0` outright, and the two
branches get `coeffsOut_yIdx_isRdecWitness`'s witness (weakened from its
own `≤384/≤320` bound to `≤704` both sides, matching this file's other
theorems' shared numeral) and the trivial `(0,1)` zero-witness
respectively.

**One risk flagged, not independently confirmed against this Mathlib
snapshot**: `hcoeffsOut_one`'s `unfold coeffsOut; rw [dif_pos ...]` step
assumes `unfold` exposes the `dif_pos`/`dif_neg` match in a form `rw`
can rewrite directly — this project's own `coeffsOut` definition uses a
dependent `if hy : ... then ... else ...` (Lean 4's `dite`), and whether
a bare `unfold` here needs an accompanying `dsimp only` first to beta-
reduce the resulting term into `dif_pos`-rewritable shape was not
checked against an actual build. If `rw [dif_pos ...]` fails to fire,
the likely fix is `simp only [coeffsOut, dif_pos ...]` in place of the
two-step `unfold`/`rw`, following this file's own established pattern
elsewhere (`hlen`'s `simp [rrBasis5, rrBasisCandidates, ...]` unfolds a
`def` and computes in one `simp` call rather than `unfold` then a
separate tactic) — flagged rather than silently assumed to work.

**What this does NOT yet close**:
1. `Epoly.coeff k`'s analogous fact — genuinely harder than `Ypoly`'s,
   since FOUR `bj = 0` slots survive (not one), so no single
   `Finset.sum_eq_single` collapse applies; needs either a full
   `Epoly = C(_) + C(_)*X + C(_)*X^2 + C(_)*X^3` expansion (via
   `rrBasis5`'s four `bj = 0` entries, `bi ∈ {0,1,2,3}` all distinct, so
   `coeff k` picks out at most one nonzero term by `bi = k`) or a
   `Finset.sum` argument keyed on `bi = k` rather than `bidx = yidx5` —
   not attempted this pass.
2. Step 3 (`Npoly.coeff k`'s own `IsRdecWitness`, unrolling
   `Polynomial.coeff_pow`/`coeff_mul`'s `Finset.antidiagonal`-indexed sums
   through repeated `IsRdecWitness.add`/`.mul` applications, built on
   `Epoly`/`Ypoly`/`fAtX`'s coefficient witnesses) — unattempted,
   unchanged from before this pass.

Scoped precisely here rather than attempted in one oversized theorem —
per this project's own 50-line-per-theorem guideline, `Epoly`'s four-slot
case is a genuinely different (not just longer) argument and deserves
its own theorem, not a hasty extension of this file's `Ypoly` work.

**REPL-confirmed green** (whole project build) — supersedes both "not yet
REPL-confirmed"/"Drafted, not yet REPL-confirmed" notes earlier in this
file. -/

end TheDataDerivation
end Genus2Lean
