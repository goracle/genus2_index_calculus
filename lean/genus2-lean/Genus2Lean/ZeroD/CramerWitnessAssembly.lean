import Mathlib
import Genus2Lean.ZeroD.TowerToRdecMul
import Genus2Lean.ZeroD.DataDerivationTotalDegree

/-!
# Revision 03: From per-entry `IsRdecWitness` to a witness for `Matrix.det`

Scoped in `ROADMAP-crossnondegenerate-degree-bound.md`'s "the
`matrixA`/`rhsVec` → `coeffsOut` bridge, scoped" section (that section's
step 3, "the crux"). `matrixA_entry_totalDegree_le`/`rhsVec_entry_
totalDegree_le` (`MatrixEntryTotalDegree.lean`/`RhsVecTotalDegree.lean`)
give an `IsRdecWitness` pair for every ENTRY of `matrixA`/`rhsVec`. This
file assembles those into a single `IsRdecWitness` pair for the
DETERMINANT, and (via `Matrix.cramer_apply`) for `Matrix.cramer` itself
— the missing link the roadmap's "correction note"
flagged: `cramerRatioDet_num_totalDegree_le` (`DataDerivationTotalDegree.lean`)
is stated for matrices already given as literal `MvPolynomial`-fractions,
not for `K2`-valued matrices related to such fractions only via
`IsRdecWitness`.

**The route** (per the roadmap's step 3): given `IsRdecWitness p ι evalNd
(M i j) (a i j, b i j)` for every entry, plus `evalNd (b i j) ≠ 0`, the
matrix `A := Matrix.of fun i j => evalNd (a i j) / evalNd (b i j)` equals
`M.map ι` entrywise, so `ι (M.det) = (M.map ι).det = A.det` via a small
self-contained `hmapdet : f N.det = (N.map f).det` helper (proved directly
from `Matrix.det_apply'` + `map_sum`/`map_prod`/the `sign σ = ±1` case
split already used by this file's own `det_totalDegree_le`, rather than
trusting an unconfirmed Mathlib lemma name for this exact fact — a first
draft tried `RingHom.map_det` directly and hit a real signature mismatch
against `Matrix.map`, caught by Claire's REPL and routed around here).
`cramerDenom_det_eq` (already proved, generic over any
field, applied here at `K := FractionRing (MvPolynomial Vars (F p))`,
`a i j := evalNd (a i j)`, `b i j := evalNd (b i j)`) then gives `(∏ i j,
evalNd (b i j)) * A.det = C.det` for `C i j := evalNd (a i j) * ∏ i' ≠ i,
evalNd (b i' j)`. Since `evalNd` is a ring hom, both sides of that
identity are themselves `evalNd` applied to the corresponding
`MvPolynomial`-valued expressions (`∏ i j, b i j` and `Matrix.det (Matrix.of
fun i j => a i j * ∏ i' ≠ i, b i' j)`, both `map_prod`/`hmapdet`
away from `evalNd (∏ i j, b i j)`/`evalNd (C_poly.det)`) — assembling
these gives `IsRdecWitness p ι evalNd (M.det) (C_poly.det, ∏ i j, b i j)`
directly, where `C_poly := Matrix.of fun i j => a i j * ∏ i' ≠ i, b i' j`
is the `MvPolynomial`-valued (not `evalNd`-applied) version. `C_poly.det`'s
own `totalDegree` bound is `cramerNumeratorDet_totalDegree_le`, and `∏ i
j, b i j`'s is `prod_totalDegree_le` twice (rows then columns) — both
already proved, generic in `n`, in `DataDerivationTotalDegree.lean`.

**REPL-confirmed green** (Claire's build).
-/

namespace Genus2Lean
namespace TheDataDerivation

variable (p : ℕ) [hp : Fact (Nat.Prime p)] [hp2 : Fact (p ≠ 2)]

/-- **The crux bridging lemma.** Given `IsRdecWitness` for every entry of
`M` (against the same `ι`/`evalNd` throughout) with nonvanishing
denominators (`evalNd (b i j) ≠ 0`, needed to legitimately divide inside
the field `L`), `(C.det, ∏ i j, b i j)` is a valid `IsRdecWitness` pair for
`M.det`, where `C i j := a i j * ∏ i' ∈ univ \ {i}, b i' j` — EXACTLY
`cramerDenom_det_eq`'s own `C`, now assembled as a genuine `IsRdecWitness`
conclusion rather than an `IsFractionRing.num`/`.den` statement, so it
composes with this project's `IsRdecWitness`-centric degree-bound story
(`towerToRdec_isRdecWitness`, `IsRdecWitness.mul`) with no detour through
`IsFractionRing` needed downstream. -/
theorem matrixDet_isRdecWitness_of_entries {Vars n K L : Type*}
    [CommRing K] [Field L] [DecidableEq n] [Fintype n]
    {ι : K →+* L} {evalNd : MvPolynomial Vars (F p) →+* L}
    {M : Matrix n n K} {a b : n → n → MvPolynomial Vars (F p)}
    (hwit : ∀ i j, IsRdecWitness p ι evalNd (M i j) (a i j, b i j))
    (hbne : ∀ i j, evalNd (b i j) ≠ 0) :
    IsRdecWitness p ι evalNd M.det
      (Matrix.det (Matrix.of fun i j => a i j * ∏ i' ∈ Finset.univ \ {i}, b i' j),
        ∏ i, ∏ j, b i j) := by
  classical
  -- Concrete determinant-map lemma for `ι`. Keeping this at the theorem's
  -- existing universe levels avoids introducing fresh `R S` universe
  -- parameters into the enclosing declaration.
  have hmapdet_ι : ι M.det = (M.map ι).det := by
    rw [Matrix.det_apply', Matrix.det_apply', map_sum]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hsign | hsign
    · simp only [hsign, Units.val_one, Int.cast_one, one_mul, map_prod, Matrix.map_apply]
    · simp only [hsign, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_mul,
        one_mul, map_neg, map_prod, Matrix.map_apply]
  -- Per-entry division fact, extracted from `hwit` cleanly (no reliance on
  -- `unfold`+`rw` seeing through the `.1`/`.2` tuple projections).
  have hdiv : ∀ i j, evalNd (a i j) / evalNd (b i j) = ι (M i j) := by
    intro i j
    have hw : evalNd (a i j) = evalNd (b i j) * ι (M i j) := hwit i j
    rw [hw]
    field_simp [hbne i j]
  -- `A`, the field-valued matrix of honest ratios, equals `M.map ι` entrywise.
  set A : Matrix n n L := Matrix.of fun i j => evalNd (a i j) / evalNd (b i j) with hA_def
  have hAeq : A = M.map ι := by
    ext i j
    simp only [hA_def, Matrix.of_apply, Matrix.map_apply]
    exact hdiv i j
  -- `ι (M.det) = A.det`, via the concrete determinant-map lemma.
  have hιdet : ι M.det = A.det := by
    rw [hmapdet_ι, hAeq]
  -- `cramerDenom_det_eq`, instantiated at `evalNd ∘ a`/`evalNd ∘ b`, gives the
  -- field-level identity `Δ * A.det = C.det` where `Δ := ∏ i j, evalNd (b i j)`.
  have hcramer := cramerDenom_det_eq (fun i j => evalNd (a i j)) (fun i j => evalNd (b i j))
    hbne
  -- Both sides of `hcramer` are `evalNd` applied to `MvPolynomial`-valued data:
  -- the LHS's `∏ i j, evalNd (b i j) = evalNd (∏ i j, b i j)` via `map_prod` twice,
  -- and the RHS's determinant is `evalNd`'s image of the `MvPolynomial`-valued
  -- determinant via the analogous concrete determinant-map proof below.
  have hΔ : (∏ i, ∏ j, evalNd (b i j) : L) = evalNd (∏ i, ∏ j, b i j) := by
    simp [map_prod]
  let Cpoly : Matrix n n (MvPolynomial Vars (F p)) :=
    Matrix.of fun i j => a i j * ∏ i' ∈ Finset.univ \ {i}, b i' j
  have hmapdet_eval : evalNd Cpoly.det = (Cpoly.map evalNd).det := by
    rw [Matrix.det_apply', Matrix.det_apply', map_sum]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hsign | hsign
    · simp only [hsign, Units.val_one, Int.cast_one, one_mul, map_prod, Matrix.map_apply]
    · simp only [hsign, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_mul,
        one_mul, map_neg, map_prod, Matrix.map_apply]
  have hC : Matrix.det (Matrix.of fun i j => evalNd (a i j) * ∏ i' ∈ Finset.univ \ {i},
      evalNd (b i' j)) =
      evalNd (Matrix.det (Matrix.of fun i j => a i j * ∏ i' ∈ Finset.univ \ {i}, b i' j)) := by
    calc
      Matrix.det (Matrix.of fun i j => evalNd (a i j) * ∏ i' ∈ Finset.univ \ {i},
          evalNd (b i' j)) =
          (Cpoly.map evalNd).det := by
            congr 1
            ext i j
            simp [Cpoly, Matrix.map_apply, Matrix.of_apply, map_mul, map_prod]
      _ = evalNd Cpoly.det := by
        symm
        exact hmapdet_eval
      _ = evalNd (Matrix.det (Matrix.of fun i j => a i j * ∏ i' ∈ Finset.univ \ {i}, b i' j)) := by
        rfl
  unfold IsRdecWitness
  rw [← hC, ← hcramer, hΔ, hιdet]

/-- **Roadmap step 4: the `Matrix.cramer`-specific corollary.** Given
`IsRdecWitness` for every entry of `M` AND every entry of the
right-hand-side vector `rhs` (same `ι`/`evalNd` throughout), with
nonvanishing denominators on both, `Matrix.cramer M rhs i` — column `i` of
Cramer's rule — has an `IsRdecWitness` pair of exactly the same shape as
`matrixDet_isRdecWitness_of_entries` gives `M.det` itself, applied instead
to `Matrix.updateCol M i rhs` (`Matrix.cramer_apply`: `M.cramer rhs i =
(M.updateCol i rhs).det`). The per-entry witness for `M.updateCol i rhs`
is `hwit`'s own witness off-column (`Matrix.updateCol_apply`'s
`if j' = i then rhs j' else M j' ...`-shape, mirrored on the witness pair
itself: `fun j' k => if k = i then ea j' else a j' k` and similarly for
denominators) and `hwitRhs`'s witness on-column — a direct case split, no
new algebra beyond `matrixDet_isRdecWitness_of_entries` itself.
`Matrix.updateCol` is used throughout (not the `updateColumn` alias, and
via the prefix form `Matrix.updateCol M i rhs` rather than dot notation
`M.updateCol i rhs`) — `M : Matrix n n K` is reducibly `n → n → K`, so
dot notation on `M` resolves against `Function`, not `Matrix`, and this
snapshot's Mathlib does not expose `Matrix.updateColumn`/`_apply` as
resolvable names here (a first draft used both and hit `Invalid field`/
`Unknown constant` errors from Claire's REPL — fixed by switching to the
confirmed-present `updateCol`/`updateCol_apply` names, prefix-applied). -/
theorem cramerSolution_isRdecWitness_of_entries {Vars n K L : Type*}
    [CommRing K] [Field L] [DecidableEq n] [Fintype n]
    {ι : K →+* L} {evalNd : MvPolynomial Vars (F p) →+* L}
    {M : Matrix n n K} {rhs : n → K} {a b : n → n → MvPolynomial Vars (F p)}
    {ea eb : n → MvPolynomial Vars (F p)}
    (hwit : ∀ i j, IsRdecWitness p ι evalNd (M i j) (a i j, b i j))
    (hbne : ∀ i j, evalNd (b i j) ≠ 0)
    (hwitRhs : ∀ j, IsRdecWitness p ι evalNd (rhs j) (ea j, eb j))
    (hebne : ∀ j, evalNd (eb j) ≠ 0) (i : n) :
    IsRdecWitness p ι evalNd (M.cramer rhs i)
      (Matrix.det (Matrix.of fun i'' j =>
          (if j = i then ea i'' else a i'' j) *
            ∏ i' ∈ Finset.univ \ {i''}, (if j = i then eb i' else b i' j)),
        ∏ i'', ∏ j, (if j = i then eb i'' else b i'' j)) := by
  have hwit' : ∀ i'' j, IsRdecWitness p ι evalNd (Matrix.updateCol M i rhs i'' j)
      ((if j = i then ea i'' else a i'' j), (if j = i then eb i'' else b i'' j)) := by
    intro i'' j
    rw [Matrix.updateCol_apply]
    split_ifs with h
    · exact hwitRhs i''
    · exact hwit i'' j
  have hbne' : ∀ i'' j, evalNd (if j = i then eb i'' else b i'' j) ≠ 0 := by
    intro i'' j
    split_ifs with h
    · exact hebne i''
    · exact hbne i'' j
  have := matrixDet_isRdecWitness_of_entries p hwit' hbne'
  rw [← Matrix.cramer_apply] at this
  exact this

/-! ## Status, this pass

**Third pass (this pass)**: Claire's REPL surfaced the two relevant failure modes
on first submission:
1. `hAeq`'s division step didn't close — `hw` (from `unfold IsRdecWitness
   at hw`) stayed in unreduced `.1`/`.2` tuple-projection form, so `rw
   [hw, ...]` never actually substituted the numerator. Fixed by extracting
   a standalone `hdiv` lemma with `hwit i j`'s type ascribed directly at
   the reduced `evalNd (a i j) = evalNd (b i j) * ι (M i j)` shape (Lean
   accepts this by defeq on the literal pair's `.1`/`.2`, no `unfold`/`rw`
   needed at all).
2. `rw [RingHom.map_det]` produced `(ι.mapMatrix M).det`, not `(M.map
   ι).det` — a genuine signature mismatch, not just a naming guess gone
   wrong. Fixed by writing a small self-contained `hmapdet` helper proved
   directly from `Matrix.det_apply'`, matching this file's OWN already-
   working `det_totalDegree_le`'s `sign σ = ±1` case-split pattern instead
   of trusting the unconfirmed Mathlib name — removes the dependency
   entirely rather than chasing the exact right combinator name.
3. `cramerDenom_det_eq` doesn't take `p` as an argument (it's fully
   generic over an abstract field `K`, never mentioning `F p`) — the
   erroneous `cramerDenom_det_eq p (...)` call shifted every subsequent
   argument by one position, producing the cascading type errors Claire's
   REPL reported. Fixed by dropping `p` from that call.
4. (Consequence of fixing 1–3, not a separate bug): the final `unfold
   IsRdecWitness; rw [...]` step's own goal only closes once `hC`/`hcramer`/
   `hΔ`/`hιdet` are all independently well-typed, which they are now.

**REPL-confirmed green after these fixes.**

**What this closes**: `matrixDet_isRdecWitness_of_entries`, the crux
bridging lemma scoped in `ROADMAP-crossnondegenerate-degree-bound.md`'s
"the `matrixA`/`rhsVec` → `coeffsOut` bridge" section, step 3. Built
entirely from already-proved pieces (`cramerDenom_det_eq`, `map_prod`,
`Matrix.map_apply`/`Matrix.of_apply`, plus this file's own self-contained
`hmapdet` in place of the Mathlib lemma that turned out to have a
different signature than assumed) — no new mathematical content beyond
the assembly itself, matching the roadmap's own framing of this as
"the crux," not a separate open question.

**Fourth pass (this pass): `cramerSolution_isRdecWitness_of_entries` added.**
Roadmap step 4, the `Matrix.cramer`-specific corollary: applies
`matrixDet_isRdecWitness_of_entries` to `Matrix.updateCol M i rhs`, whose
entries are `hwit`'s off-column and `hwitRhs`'s on-column via
`Matrix.updateCol_apply`'s `if j = i then rhs j else M i j`-shape,
mirrored on the witness pair by the same `if j = i then ea/eb else a/b`
case split; `Matrix.cramer_apply` then converts `(Matrix.updateCol M i
rhs).det` back to `M.cramer rhs i`. **First submission hit two REPL
errors**: `M.updateColumn` (`Invalid field 'updateColumn'`) and
`Matrix.updateColumn_apply` (`Unknown constant`) — `M : Matrix n n K` is
reducibly `n → n → K`, so dot notation resolved against `Function`, not
`Matrix`, and this snapshot's Mathlib doesn't expose the `updateColumn`
alias names at all (only `updateCol`/`updateCol_apply`). Fixed by
switching every occurrence to `Matrix.updateCol`, prefix-applied
(`Matrix.updateCol M i rhs`, not `M.updateCol i rhs`, to stay unambiguous)
and `Matrix.updateCol_apply`. **Not yet REPL-confirmed again after this
fix.**

**What this does NOT yet close** (per the roadmap's own remaining steps):
1. The `totalDegree` bounds on `C.det`/`∏ i j, b i j` (and their
   `cramerSolution_isRdecWitness_of_entries` analogues) themselves — these
   lemmas produce `IsRdecWitness` pairs but don't bound `totalDegree`;
   that's `cramerNumeratorDet_totalDegree_le`/`prod_totalDegree_le` (both
   already proved, `DataDerivationTotalDegree.lean`), applied as a direct
   corollary now that both lemmas are REPL-confirmed.
2. Instantiating both of the above at `matrixA`/`rhsVec`'s own `a`/`b`
   (i.e. `matrixA_entry_totalDegree_le`/`rhsVec_entry_totalDegree_le`'s
   own witness pairs) to get `coeffsOut`'s full bound — the actual
   original target, still one assembly pass away.

**REPL-confirmed green** (whole project build) — supersedes the "Not yet
REPL-confirmed again after this" note above. -/

end TheDataDerivation
end Genus2Lean
