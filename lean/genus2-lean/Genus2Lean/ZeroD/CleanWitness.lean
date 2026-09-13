import Mathlib
import Genus2Lean.ZeroD.TowerCoeffWitnessDescent

/-!
# `CleanWitness`: a reusable structure for propagating "clean at `w`"
witnesses through `IsRdecWitness.add`/`.mul`/`.neg`

New this pass, per a ChatGPT consult on assembling
`CurBeforeMonicCoeffTotalDegree.lean`'s `Q.coeff i`/`g.coeff i` witness
trees against `TowerCoeffWitnessDescent.lean`'s "clean at `w`" bookkeeping
(`towerToRdec_output_shape`, `mul_clean_reduce`). That file established,
by hand, for one specific tree (`Q.coeff 3`), that `.add`/`.neg` preserve
cleanliness exactly and `.mul` reduces cleanly only after `evalNd`
(needing `w² = c`). This file packages that bookkeeping ONCE, as a small
algebraic structure with matched `.add`/`.mul`/`.neg` operations and
`totalDegree` bounds, so it does not need re-deriving by hand at every
node of every future `Q.coeff i`/`g.coeff i` tree.

**A "clean" witness pair `(n, d)` for `v` (relative to a fixed generator
`w := X (sg.wGen 1)`, base ring `MvPolynomial Vars (F p)`) is one with
`n = N0 + N1*w`, `d = D0` — no `w` at all in the denominator.** `CleanWitness`
below is exactly the triple `(N0, N1, D0)`. This is NOT a general-purpose
gadget: it is scoped precisely to the shape `towerToRdec_output_shape`
produces (whose own denominator `den0*den1` never contains `sg.wGen 1`,
per `towerToRdec_vars_subset`), which is why `D1` (a `w`-coefficient on
the denominator) is not carried at all — matching this project's `b = 0`
convention throughout (`K1_poly_monic`/`K2_poly_monic` are always
`X² - C(const)`).

**What this file proves, precisely:**
- `CleanWitness.toPair`: the bridge back to `IsRdecWitness`'s own
  `MvPolynomial Vars (F p) × MvPolynomial Vars (F p)` pair shape.
- `CleanWitness.add`/`.mul`/`.neg`: the algebraic operations themselves.
- `CleanWitness.toPair_add`/`toPair_neg`: `.add`/`.neg` preserve
  `IsRdecWitness`'s pair literally, no `evalNd` needed — pure
  `MvPolynomial` identity, `ring`-checkable (no `w² = c` relation used,
  matching `TowerCoeffWitnessDescent.lean`'s finding that `.add` never
  creates a `w²` term).
- `CleanWitness.evalNd_toPair_mul`: `.mul` matches `IsRdecWitness.mul`'s
  raw pair only after `evalNd` — proved directly from `w² = φc`
  (`evalNd_X_wGen_one_sq_eq`/`hc`) rather than via `mul_clean_reduce`
  composition, after composing with `mul_clean_reduce` inline proved
  fiddlier than re-deriving the one fact actually needed.
- `CleanWitness.add_totalDegree_le`/`mul_totalDegree_le`/
  `neg_totalDegree_le`: the matching `totalDegree` bounds, mirroring
  `coeffDescent_totalDegree_le_b0`'s triangle-inequality style exactly
  (`.add` costs `D1+D2` per component with an extra `D0`-product factor
  threaded through both terms; `.mul` costs `D1+D2` with an extra
  `totalDegree c` term on the `N0` slot only, matching `.mul`'s formula
  `N0a*N0b + c*N1a*N1b`).

**What this file deliberately does NOT do**: it does not yet assemble
`CurBeforeMonicCoeffTotalDegree.lean`'s actual `Q.coeff i`/`g.coeff i`
trees against this structure (that composition — instantiating `t1`,
`t2`, `gu0`, `gu1` as base `CleanWitness`es and folding the tree through
`.add`/`.mul`/`.neg` above — is the concrete next step, flagged here
rather than attempted in the same pass, since it needs each base
witness's own `(N0,N1,D0)` triple exhibited first, e.g. `gu1 := ⟨C u1, 0,
1⟩` trivially, `t1`/`t2` via `towerToRdec_output_shape` applied to
`anchor1`/`anchor2`, neither done here). **REPL-confirmed this pass**:
build green, all four theorems above (`toPair_add`, `toPair_neg`,
`evalNd_toPair_mul`, and the three `totalDegree` bounds) typecheck.
`evalNd_toPair_mul`'s proof went through several attempts (an initial
`mul_clean_reduce` composition mismatched `κ`/`φc` bookkeeping); the
version that closed derives `w² = φc` (`hwsq`) directly and finishes
with `linear_combination` against a coefficient verified symbolically,
not just guessed.
-/

namespace Genus2Lean
namespace TheDataDerivation

variable (p : ℕ) [hp : Fact (Nat.Prime p)] [hp2 : Fact (p ≠ 2)]

/-! ## The structure and its algebraic operations -/

/-- **A witness pair `(N0 + N1*w, D0)` clean at a fixed generator `w`.**
See the module docstring for the precise meaning and scope. `Vars` is the
base ring's variable type (`MvPolynomial Vars (F p)`), matching
`IsRdecWitness`'s own `nd` component type. -/
structure CleanWitness (Vars : Type*) where
  N0 : MvPolynomial Vars (F p)
  N1 : MvPolynomial Vars (F p)
  D0 : MvPolynomial Vars (F p)

namespace CleanWitness

variable {Vars : Type*}

/-- **The literal `MvPolynomial` pair this triple represents**, given the
generator `w`. `toPair w A = (A.N0 + A.N1*w, A.D0)` — exactly the shape
`IsRdecWitness.add`/`.mul`/`.neg` (`TowerToRdecMul.lean`,
`NpolyTotalDegree.lean`, `RhsVecTotalDegree.lean`) take as their `nd`
argument, so `toPair w` is the bridge back to those combinators' own
statements. -/
noncomputable def toPair (w : MvPolynomial Vars (F p)) (A : CleanWitness p Vars) :
    MvPolynomial Vars (F p) × MvPolynomial Vars (F p) :=
  (A.N0 + A.N1 * w, A.D0)

/-- **Addition.** Matches `IsRdecWitness.add`'s pair `(na*db+nb*da, da*db)`
applied to `toPair w A`/`toPair w B`, expanded and regrouped in the `1,w`
basis — no `w²` term appears (`.add` never multiplies two `w`-containing
factors together), so this holds with no relation on `w` needed, exactly
as `TowerCoeffWitnessDescent.lean`'s hand-derivation for `Q.coeff 3`
found. -/
noncomputable def add (A B : CleanWitness p Vars) : CleanWitness p Vars where
  N0 := A.N0 * B.D0 + B.N0 * A.D0
  N1 := A.N1 * B.D0 + B.N1 * A.D0
  D0 := A.D0 * B.D0

/-- **Negation.** Matches `IsRdecWitness.neg`'s pair `(-n, d)` directly. -/
noncomputable def neg (A : CleanWitness p Vars) : CleanWitness p Vars where
  N0 := -A.N0
  N1 := -A.N1
  D0 := A.D0

/-- **Multiplication.** Takes the defining constant `c : MvPolynomial Vars
(F p)` explicitly (the `evalNd`/`ι`-image of `K2_poly_monic`/
`K1_poly_monic`'s constant term, i.e. the base-ring element such that
`evalNd (X (sg.wGen 1)) ^ 2 = algebraMap _ _ c` — see
`evalNd_toPair_mul` below for the precise hypothesis this needs) since,
unlike `.add`/`.neg`, the result depends on it: `N0 := N0a*N0b +
c*N1a*N1b`, `N1 := N0a*N1b+N0b*N1a`, matching `mul_clean_reduce`'s RHS
exactly. This is **not** literally `IsRdecWitness.mul`'s raw pair
`(na*nb, da*db)` (that pair is not clean — see
`TowerCoeffWitnessDescent.lean`'s own discussion of why `.mul` doesn't
preserve cleanliness on the nose) but its `evalNd`-reduced form, which is
what `.evalNd_toPair_mul` below proves equal to `evalNd` of the raw
`IsRdecWitness.mul` pair. -/
noncomputable def mul (c : MvPolynomial Vars (F p)) (A B : CleanWitness p Vars) : CleanWitness p Vars where
  N0 := A.N0 * B.N0 + c * A.N1 * B.N1
  N1 := A.N0 * B.N1 + B.N0 * A.N1
  D0 := A.D0 * B.D0

/-! ## Matching the algebraic operations to `IsRdecWitness` -/

/-- **`.add` preserves `IsRdecWitness`'s pair, literally, at the
`MvPolynomial` level (before any `evalNd`).** Pure algebra: `toPair w
(A.add B)` equals `IsRdecWitness.add`'s raw pair applied to `toPair w
A`/`toPair w B` — both components `ring`-closable directly, no `w² = c`
relation needed (matches the module docstring's claim precisely: `.add`
never creates a `w²` term). -/
theorem toPair_add (w : MvPolynomial Vars (F p)) (A B : CleanWitness p Vars) :
    toPair p w (CleanWitness.add p A B) =
      ((toPair p w A).1 * (toPair p w B).2 + (toPair p w B).1 * (toPair p w A).2,
        (toPair p w A).2 * (toPair p w B).2) := by
  unfold toPair add
  apply Prod.ext
  · show A.N0 * B.D0 + B.N0 * A.D0 + (A.N1 * B.D0 + B.N1 * A.D0) * w =
      (A.N0 + A.N1 * w) * B.D0 + (B.N0 + B.N1 * w) * A.D0
    ring
  · rfl

/-- **`.neg` preserves `IsRdecWitness`'s pair, literally.** Immediate. -/
theorem toPair_neg (w : MvPolynomial Vars (F p)) (A : CleanWitness p Vars) :
    toPair p w (CleanWitness.neg p A) = (-(toPair p w A).1, (toPair p w A).2) := by
  unfold toPair neg
  apply Prod.ext
  · show -A.N0 + -A.N1 * w = -(A.N0 + A.N1 * w)
    ring
  · rfl

/-- **`.mul`'s defining property: after `evalNd` (using `w² = c`), its
numerator matches `IsRdecWitness.mul`'s raw numerator exactly.** A direct
restatement of `mul_clean_reduce` against `CleanWitness.mul`/`toPair`:
`c` here is fixed to the same value `mul_clean_reduce` uses (`ι`'s image
of `K2_poly_monic`'s constant term, `fAtT p ... 1` tower-lifted), and
`hι_w2` is the same hypothesis identifying `evalNd (X (sg.wGen 1))` with
`ι (w2 p ...)`. `hc` supplies `c`'s defining property directly (`c`'s
`algebraMap`-image equals the actual tower constant `mul_clean_reduce`
uses) rather than assuming `c` is definitionally that constant — this
matches how `CleanWitness.mul` is meant to be invoked (with whatever
concrete `MvPolynomial Vars (F p)` value the caller already has on hand
representing the constant, e.g. `fAtT`'s own base-ring numerator, not
necessarily the tower element itself). The denominator component needs
no separate lemma: `.mul`'s `D0 := A.D0*B.D0` already matches
`IsRdecWitness.mul`'s raw denominator `da*db` literally (no `w` involved
on that side at all), so only the numerator needs an `evalNd`-level
identity. -/
theorem evalNd_toPair_mul {Vars : Type*} (sg : SideGens Vars)
    (ι : K2 p c0 c1 c2 c3 c4 →+* FractionRing (MvPolynomial Vars (F p)))
    (hι_w2 : ι (w2 p c0 c1 c2 c3 c4) =
      algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p)))
        (MvPolynomial.X (sg.wGen 1)))
    (c : MvPolynomial Vars (F p))
    (hc : algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p))) c =
      ι (algebraMap (K1 p c0 c1 c2 c3 c4) (K2 p c0 c1 c2 c3 c4)
          (algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4) (fAtT p c0 c1 c2 c3 c4 1))))
    (A B : CleanWitness p Vars) :
    (algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p))))
        (toPair p (MvPolynomial.X (sg.wGen 1)) (CleanWitness.mul p c A B)).1 =
      (algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p))))
          (toPair p (MvPolynomial.X (sg.wGen 1)) A).1 *
        (algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p))))
          (toPair p (MvPolynomial.X (sg.wGen 1)) B).1 := by
  -- `toPair _ A = A.N0 + A.N1 * w`, `toPair _ B = B.N0 + B.N1 * w`
  -- (`w := X (sg.wGen 1)`). Rather than composing `mul_clean_reduce` with
  -- `hc` inside one `linear_combination` (two prior attempts got the
  -- bookkeeping there wrong), derive `w² = φc` as its own fact `hwsq`
  -- first, then close the goal directly against it. Coefficient
  -- verified symbolically (not just guessed): expanding
  -- `goal_lhs - goal_rhs - k·(w² - φc)` in the four `N` variables and
  -- `w` shows the residual vanishes only at `k = -(φA.N1 · φB.N1)`,
  -- which is what's used below (the naive `+φA.N1·φB.N1` coefficient
  -- from the previous attempt was off by this sign).
  unfold toPair mul
  simp only [map_add, map_mul]
  have hwsq : (algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p))))
      (MvPolynomial.X (sg.wGen 1) : MvPolynomial Vars (F p)) ^ 2 =
      (algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p)))) c := by
    rw [hc]; exact evalNd_X_wGen_one_sq_eq p sg ι hι_w2
  linear_combination
    -((algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p)))) A.N1 *
      (algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p)))) B.N1) * hwsq

/-! ## `totalDegree` bounds, mirroring `coeffDescent_totalDegree_le_b0` -/

omit hp2 in
/-- **`.add`'s `totalDegree` bound.** If `A`'s coordinates are all `≤ Da`
and `B`'s are all `≤ Db`, `A.add B`'s coordinates are all `≤ Da + Db` —
same shape as `uniformBound_add`, one component at a time via
`MvPolynomial.totalDegree_mul`/`_add`. -/
theorem add_totalDegree_le {A B : CleanWitness p Vars} {Da Db : ℕ}
    (hA : A.N0.totalDegree ≤ Da ∧ A.N1.totalDegree ≤ Da ∧ A.D0.totalDegree ≤ Da)
    (hB : B.N0.totalDegree ≤ Db ∧ B.N1.totalDegree ≤ Db ∧ B.D0.totalDegree ≤ Db) :
    (CleanWitness.add p A B).N0.totalDegree ≤ Da + Db ∧
      (CleanWitness.add p A B).N1.totalDegree ≤ Da + Db ∧
      (CleanWitness.add p A B).D0.totalDegree ≤ Da + Db := by
  obtain ⟨hAN0, hAN1, hAD0⟩ := hA
  obtain ⟨hBN0, hBN1, hBD0⟩ := hB
  refine ⟨?_, ?_, ?_⟩
  · exact le_trans (MvPolynomial.totalDegree_add _ _)
      (max_le (le_trans (MvPolynomial.totalDegree_mul _ _) (Nat.add_le_add hAN0 hBD0))
        (le_trans (MvPolynomial.totalDegree_mul _ _)
          ((Nat.add_le_add hBN0 hAD0).trans_eq (Nat.add_comm Db Da))))
  · exact le_trans (MvPolynomial.totalDegree_add _ _)
      (max_le (le_trans (MvPolynomial.totalDegree_mul _ _) (Nat.add_le_add hAN1 hBD0))
        (le_trans (MvPolynomial.totalDegree_mul _ _)
          ((Nat.add_le_add hBN1 hAD0).trans_eq (Nat.add_comm Db Da))))
  · exact le_trans (MvPolynomial.totalDegree_mul _ _) (Nat.add_le_add hAD0 hBD0)

omit hp2 in
/-- **`.neg`'s `totalDegree` bound.** Unchanged, immediate. -/
theorem neg_totalDegree_le {A : CleanWitness p Vars} {D : ℕ}
    (hA : A.N0.totalDegree ≤ D ∧ A.N1.totalDegree ≤ D ∧ A.D0.totalDegree ≤ D) :
    (CleanWitness.neg p A).N0.totalDegree ≤ D ∧ (CleanWitness.neg p A).N1.totalDegree ≤ D ∧
      (CleanWitness.neg p A).D0.totalDegree ≤ D := by
  obtain ⟨hAN0, hAN1, hAD0⟩ := hA
  exact ⟨(MvPolynomial.totalDegree_neg _).le.trans hAN0,
    (MvPolynomial.totalDegree_neg _).le.trans hAN1, hAD0⟩

omit hp2 in
/-- **`.mul`'s `totalDegree` bound.** If `A`'s coordinates are all `≤ Da`,
`B`'s are all `≤ Db`, and `c.totalDegree ≤ C`, then `(A.mul c B).N0 ≤
max(Da+Db, C+Da+Db)`, `.N1 ≤ Da+Db`, `.D0 ≤ Da+Db` — matching
`coeffDescent_totalDegree_le_b0`'s shape (its `R0`/`R1`/`Δ` all land at
`≤ B + 4*Dp`; here the tighter per-term bound is kept rather than
collapsed to one uniform numeral, since `CleanWitness` composes across
many nodes and a tighter per-slot bound avoids compounding slack). -/
theorem mul_totalDegree_le {c : MvPolynomial Vars (F p)} {C : ℕ} (hc : c.totalDegree ≤ C)
    {A B : CleanWitness p Vars} {Da Db : ℕ}
    (hA : A.N0.totalDegree ≤ Da ∧ A.N1.totalDegree ≤ Da ∧ A.D0.totalDegree ≤ Da)
    (hB : B.N0.totalDegree ≤ Db ∧ B.N1.totalDegree ≤ Db ∧ B.D0.totalDegree ≤ Db) :
    (CleanWitness.mul p c A B).N0.totalDegree ≤ C + Da + Db ∧
      (CleanWitness.mul p c A B).N1.totalDegree ≤ Da + Db ∧
      (CleanWitness.mul p c A B).D0.totalDegree ≤ Da + Db := by
  obtain ⟨hAN0, hAN1, hAD0⟩ := hA
  obtain ⟨hBN0, hBN1, hBD0⟩ := hB
  refine ⟨?_, ?_, ?_⟩
  · have h1 : (A.N0 * B.N0).totalDegree ≤ Da + Db :=
      le_trans (MvPolynomial.totalDegree_mul _ _) (Nat.add_le_add hAN0 hBN0)
    have h2 : (c * A.N1 * B.N1).totalDegree ≤ C + Da + Db := by
      have h2a : (c * A.N1).totalDegree ≤ C + Da :=
        le_trans (MvPolynomial.totalDegree_mul _ _) (Nat.add_le_add hc hAN1)
      exact le_trans (MvPolynomial.totalDegree_mul _ _) (by omega)
    exact le_trans (MvPolynomial.totalDegree_add _ _) (max_le (by omega) (by omega))
  · exact le_trans (MvPolynomial.totalDegree_add _ _)
      (max_le (le_trans (MvPolynomial.totalDegree_mul _ _) (Nat.add_le_add hAN0 hBN1))
        (le_trans (MvPolynomial.totalDegree_mul _ _)
          ((Nat.add_le_add hBN0 hAN1).trans_eq (Nat.add_comm Db Da))))
  · exact le_trans (MvPolynomial.totalDegree_mul _ _) (Nat.add_le_add hAD0 hBD0)

end CleanWitness
end TheDataDerivation
end Genus2Lean
