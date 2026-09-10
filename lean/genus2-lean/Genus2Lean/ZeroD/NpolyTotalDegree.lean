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

/-! ## Status, this pass

**Drafted, not yet REPL-confirmed.** Lands `IsRdecWitness.add` (the
missing addition combinator, alongside the already-proved `.mul`/`.neg`/
`.div`) and `algebraMap_Fp_isRdecWitness` (the constant-embedding
witness `fAtX`'s coefficients need, unconditional on `ι` beyond being a
ring hom — proved via the same `ZMod.natCast_zmod_surjective` argument
`towerToRdec_spec`'s own `hcomp` step already relies on,
`DataDerivationMumford.lean`).

**What this does NOT yet close**: the actual `Npoly.coeff k`
`IsRdecWitness`/`totalDegree` bound — needs (step A, unattempted) that
`Epoly.coeff k`/`Ypoly.coeff k` each collapse to a single `coeffsOut`
slot or `0`, and (step 3's remaining half, unattempted) unrolling
`Polynomial.coeff_pow`/`coeff_mul`'s `Finset.antidiagonal`-indexed sums
through repeated `IsRdecWitness.add`/`.mul` applications. Scoped in this
file's header rather than attempted this pass, given the size — the
next concrete step, not a separate unmeasured risk. -/

end TheDataDerivation
end Genus2Lean
