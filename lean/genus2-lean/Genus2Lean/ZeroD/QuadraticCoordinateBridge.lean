import Mathlib
import Genus2Lean.ZeroD.TheDataDerivation.DataDerivationMumford
import Genus2Lean.ZeroD.DataDerivationTotalDegree

/-!
# The quadratic-coordinate bridge: reusable pieces for a `hA`/`hB` degree bound

New this pass. `ROADMAP-crossnondegenerate-degree-bound.md`'s latest
"Update" section traces the real remaining obstruction on
`crossResultant_totalDegree_le`/`crossResultantV_totalDegree_le`'s `hA`/
`hB`: a degree bound on `uRS.coeff i`/`vRS.coeff i`'s literal
`AdjoinRoot.modByMonicHom`-extracted `K1`/`K0` coordinates, not merely an
existential `IsRdecWitness` witness for the whole `K2`-value (which is
already in hand, unconditionally, via `towerToRdec_isRdecWitness`).

Two attempted routes to that bound were checked THIS pass and found not to
apply directly (both traced by hand before being written up, not assumed):

1. **Inverting a single witness equation.** Given `evalNd n = evalNd d *
   ι x` (`x = d0 + d1*w1 : K1`, `ι` a ring hom), `ι x = ι0 d0 + ι0 d1 * ι
   w1` is ONE linear equation in the two unknowns `ι0 d0`, `ι0 d1` — no
   second independent relation is available (no known/available Galois
   automorphism of `K1`/`K2` swapping `w1 ↦ -w1` is constructed anywhere in
   this project), so the two coordinates cannot be separated this way.
2. **Decomposing the witness pair itself against `w1`/`w2`.** This was
   ChatGPT's proposed 2×2 linear system (`a = a0+a1*w`, `b=b0+b1*w`,
   solving for `x`'s own coordinates via Cramer's rule on that system).
   It does not apply here: `IsRdecWitness`'s witness pair `nd :
   MvPolynomial Vars (F p) × MvPolynomial Vars (F p)` (`TowerToRdecMul.
   lean`) is always base-ring-valued, never a `K1`/`K2` element — there is
   no `w`-coordinate structure on `nd` to decompose in the first place.

**So neither route lets the coordinate bound be reverse-engineered from an
existing whole-value witness.** The bound instead needs to come from
directly tracing the ARITHMETIC that constructs `curBeforeMonic.coeff i`
(`Qpoly`/`t1*t2*U`-style, `CurBeforeMonicCoeffTotalDegree.lean`) through
`AdjoinRoot.modByMonicHom` at each step — a genuinely separate,
not-yet-attempted derivation.

**What this file provides instead, per instruction this pass**: the
concrete, level-specific facts that derivation (whichever exact shape it
ends up taking) will need regardless — laid down now rather than
re-derived piecemeal later. `w1_sq_eq`/`w2_sq_eq` (`DataDerivationSolve.
lean`) are `private` and so unusable from any other file; the two
theorems below reprove the same facts publicly (same short
`AdjoinRoot.eval₂_root`-based argument), and the two after that specialize
`adjoinRoot_quadratic_normal_form` (`DataDerivationMumford.lean`, generic
over any monic quadratic) to `K1 p .../w1`, `K2 p .../w2` by name, so
`x = algebraMap ... d0 + algebraMap ... d1 * w1` (resp. `K2`/`w2`) is
available as a named, directly-`rw`-able fact rather than needing
`adjoinRoot_quadratic_normal_form` re-specialized inline at each future
call site.

**Not yet REPL-confirmed** — drafted this pass; Claire tests via the REPL.
-/

namespace Genus2Lean
namespace TheDataDerivation

open Polynomial

variable (p : ℕ) [hp : Fact (Nat.Prime p)] [hp2 : Fact (p ≠ 2)]

/-- **`w1`'s defining quadratic relation, public.** `w1_sq_eq`
(`DataDerivationSolve.lean`) is `private`; this is the same fact,
reproved directly from `AdjoinRoot.eval₂_root` so it's usable from other
files. `w1 p ... = AdjoinRoot.root g` and `K1 p ... = AdjoinRoot g` for
`g := X^2 - C (fAtT p ... 0)` are `rfl`-transparent by `w1`/`K1`'s own
definitions (`DataDerivationTower.lean`), matching `w1_sq_eq`'s own proof
exactly. -/
theorem w1_sq_eq_public (c0 c1 c2 c3 c4 : F p) :
    (w1 p c0 c1 c2 c3 c4) ^ 2 =
      algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4) (fAtT p c0 c1 c2 c3 c4 0) := by
  have h := AdjoinRoot.eval₂_root
    (X ^ 2 - C (fAtT p c0 c1 c2 c3 c4 0) : Polynomial (K0 p))
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_C] at h
  -- Matching `w1_sq_eq`'s own proof exactly: identifying `AdjoinRoot.of g`
  -- with `algebraMap (K0 p) (K1 p ...)` as a SEPARATE `have`/`rw` step (not
  -- folded into one combined `rw [← AdjoinRoot.algebraMap_eq]` on `h`
  -- directly) is deliberate — that combined form previously hit the
  -- default heartbeat budget via an `isDefEq` search across the whole
  -- rewritten term (per `w1_sq_eq`'s own docstring), so it is avoided here
  -- too rather than re-introduced.
  have hof :
      (AdjoinRoot.of (X ^ 2 - C (fAtT p c0 c1 c2 c3 c4 0) : Polynomial (K0 p))) =
        algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4) :=
    (AdjoinRoot.algebraMap_eq
      (X ^ 2 - C (fAtT p c0 c1 c2 c3 c4 0) : Polynomial (K0 p))).symm
  rw [hof] at h
  exact sub_eq_zero.mp h

/-- **`w2`'s defining quadratic relation, public.** Same shape as
`w1_sq_eq_public`, one tower level up (`w2 p ... = AdjoinRoot.root g'` for
`g' := X^2 - C (algebraMap (K0 p) (K1 p ...) (fAtT p ... 1))`, matching
`w2_sq_eq`'s (private) statement in `DataDerivationSolve.lean`). -/
theorem w2_sq_eq_public (c0 c1 c2 c3 c4 : F p) :
    (w2 p c0 c1 c2 c3 c4) ^ 2 =
      algebraMap (K1 p c0 c1 c2 c3 c4) (K2 p c0 c1 c2 c3 c4)
        (algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4) (fAtT p c0 c1 c2 c3 c4 1)) := by
  have h := AdjoinRoot.eval₂_root
    (X ^ 2 - C (algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4) (fAtT p c0 c1 c2 c3 c4 1)) :
      Polynomial (K1 p c0 c1 c2 c3 c4))
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_C] at h
  -- Matching `w2_sq_eq`'s own proof exactly, NOT `w1_sq_eq_public`'s
  -- pattern above: `K1 p ...` is a reducible `abbrev` wrapping another
  -- `AdjoinRoot`, so both a separate `hof`/`rw [hof]` step and a plain
  -- `rw [← AdjoinRoot.algebraMap_eq]` hit the same `isDefEq` timeout here
  -- (per `w2_sq_eq`'s own docstring) — `rw`'s keyed matching forces
  -- repeated unfolding of the whole `abbrev` chain. `simp only` uses
  -- discrimination-tree indexing instead, which avoids it.
  simp only [← AdjoinRoot.algebraMap_eq] at h
  exact sub_eq_zero.mp h

/-- **`K1`'s quadratic normal form, named for direct reuse.**
`adjoinRoot_quadratic_normal_form` specialized to `K1 p .../w1`: every
`x : K1 p c0 c1 c2 c3 c4` decomposes as `x = algebraMap (K0 p) (K1 p ...)
d0 + algebraMap (K0 p) (K1 p ...) d1 * w1 p ...`, `d0 := (modByMonicHom
x).coeff 0`, `d1 := (modByMonicHom x).coeff 1` — exactly the coordinate
pair any future degree-bound derivation on `x`'s `K0`-level pieces needs
to name directly, matching `towerToRdec_spec`'s own internal `hK1repr`
local (same identity, proved inline there rather than as a standalone
reusable theorem — this makes it one). -/
theorem K1_quadratic_normal_form (c0 c1 c2 c3 c4 : F p) (x : K1 p c0 c1 c2 c3 c4) :
    x = algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4)
        ((AdjoinRoot.modByMonicHom (K1_poly_monic p c0 c1 c2 c3 c4) x).coeff 0) +
      algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4)
        ((AdjoinRoot.modByMonicHom (K1_poly_monic p c0 c1 c2 c3 c4) x).coeff 1) *
          w1 p c0 c1 c2 c3 c4 :=
  adjoinRoot_quadratic_normal_form
    (K1_poly_monic p c0 c1 c2 c3 c4) (natDegree_X_pow_sub_C) x

/-- **`K2`'s quadratic normal form, named for direct reuse.** Same shape
as `K1_quadratic_normal_form`, one tower level up (`v : K2 p ...`
decomposes against `w2 p ...`), matching `towerToRdec_spec`'s internal
`hK2repr` local. -/
theorem K2_quadratic_normal_form (c0 c1 c2 c3 c4 : F p) (v : K2 p c0 c1 c2 c3 c4) :
    v = algebraMap (K1 p c0 c1 c2 c3 c4) (K2 p c0 c1 c2 c3 c4)
        ((AdjoinRoot.modByMonicHom (K2_poly_monic p c0 c1 c2 c3 c4) v).coeff 0) +
      algebraMap (K1 p c0 c1 c2 c3 c4) (K2 p c0 c1 c2 c3 c4)
        ((AdjoinRoot.modByMonicHom (K2_poly_monic p c0 c1 c2 c3 c4) v).coeff 1) *
          w2 p c0 c1 c2 c3 c4 :=
  adjoinRoot_quadratic_normal_form
    (K2_poly_monic p c0 c1 c2 c3 c4) (natDegree_X_pow_sub_C) v

/-- **The `K0`-level bridge, made a standalone reusable theorem.**
`ROADMAP-crossnondegenerate-degree-bound.md`'s "ChatGPT reply received"
section derives this precisely but leaves it as prose (`mk'_eq_iff_eq_mul`
mentioned but never actually written as Lean, confirmed by direct search
this pass — `AlgebraMapFpLiteralTotalDegree.lean`'s closing note repeats
the same derivation, also as prose only). Written out here as an actual
theorem: an `IsRdecWitness`-shaped equation at the `K0` level (`ι :=
algebraMap (K0 p) L`, i.e. the case where `IsRdecWitness`'s generic `ι`
genuinely specializes to a plain `algebraMap`, unlike at `K1`/`K2` where
it is a composite tower embedding — see `towerToRdec_spec`'s own docstring
on this exact specialization) converts, via `IsLocalization.mk'_eq_iff_
eq_mul` (confirmed present in current Mathlib4,
`Mathlib.RingTheory.Localization.Defs`), into an `IsLocalization.mk'`
witness for `v`, then `isFractionRing_num_totalDegree_le`/
`isFractionRing_den_totalDegree_le` (`DataDerivationTotalDegree.lean`,
already proved) give the literal degree bound on `v`'s own canonical
`IsFractionRing.num`/`.den` — exactly `baseFracToRing_totalDegree_le`'s
`hv` hypothesis, one step further back (that theorem's `hv` is exactly
the `IsLocalization.mk'` fact this theorem's conclusion supplies, packaged
so this bridge's output is the exact input the rest of the tower-degree
chain (`towerToRdecK1_totalDegree_le`, etc.) already consumes). **Not
itself a closure of `hA`/`hB`** — this only handles the `K0` base case;
the harder, still-open step (per this file's earlier `K1`/`K2`
`quadratic_normal_form` theorems and the roadmap's own honest accounting)
is deriving a `K0`-level `IsRdecWitness` fact for `curBeforeMonic.coeff
i`'s ACTUAL sub-pieces in the first place, which is arithmetic-tracing
work this theorem does not attempt. -/
theorem base_isRdecWitness_bridge {n d : MvPolynomial (Fin 2) (F p)}
    {v : K0 p} (hd : d ≠ 0)
    (hwit : algebraMap (MvPolynomial (Fin 2) (F p)) (K0 p) n
        = algebraMap (MvPolynomial (Fin 2) (F p)) (K0 p) d * v) :
    v = IsLocalization.mk' (K0 p) n ⟨d, mem_nonZeroDivisors_of_ne_zero hd⟩ := by
  symm
  apply (IsLocalization.mk'_eq_iff_eq_mul (S := K0 p)).mpr
  -- Goal here (after `symm` flips the original `v = mk' ...` into `mk' ...
  -- = v`, matching `mk'_eq_iff_eq_mul`'s LHS shape): `algebraMap n = v *
  -- algebraMap d` (unifying `x:=n, y:=⟨d,_⟩, z:=v` in `mk'_eq_iff_eq_mul`'s
  -- RHS). `rw [mul_comm]` turns the goal's `v * algebraMap d` into
  -- `algebraMap d * v`, matching `hwit` exactly.
  rw [mul_comm]
  exact hwit

/-- **`IsFractionRing.num`/`.den` themselves form an `IsRdecWitness`
witness, at `K0`.** The other direction of `base_isRdecWitness_bridge`:
rather than converting a witness INTO an `IsLocalization.mk'` fact, this
produces a witness FOR ANY `v : K0 p` directly, unconditionally, from
Mathlib's own canonical `num`/`den` — `IsFractionRing.mk'_num_den'` (the
same fact `hbase`'s local proof inside `towerToRdec_spec` uses inline,
`DataDerivationMumford.lean`) rearranged via `div_eq_iff`. Combined with
`base_isRdecWitness_bridge` (which goes the other way), this shows the
`IsRdecWitness`-at-`ι=id`-shaped fact and the `IsLocalization.mk'`-witness
fact are, at the `K0` level, freely interconvertible — so any `K0`-level
`IsRdecWitness`-shaped fact built via `.add`/`.mul`/`.neg` (`TowerToRdecMul.
lean`, `NpolyTotalDegree.lean`, `RhsVecTotalDegree.lean`) can be pushed
through the `IsLocalization.mk'`-witness route to reach
`isFractionRing_num_totalDegree_le`/`isFractionRing_den_totalDegree_le`
directly — closing the loop `ROADMAP-crossnondegenerate-degree-bound.md`'s
base-case bridge section describes, now as two composable theorems rather
than one-directional prose. -/
theorem num_den_isRdecWitness (v : K0 p) :
    algebraMap (MvPolynomial (Fin 2) (F p)) (K0 p) (IsFractionRing.num (MvPolynomial (Fin 2) (F p)) v)
      = algebraMap (MvPolynomial (Fin 2) (F p)) (K0 p)
          (IsFractionRing.den (MvPolynomial (Fin 2) (F p)) v : MvPolynomial (Fin 2) (F p)) * v := by
  have hden_ne : algebraMap (MvPolynomial (Fin 2) (F p)) (K0 p)
      (IsFractionRing.den (MvPolynomial (Fin 2) (F p)) v : MvPolynomial (Fin 2) (F p)) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (IsFractionRing.den (MvPolynomial (Fin 2) (F p)) v).property
  have hdiv := IsFractionRing.mk'_num_den' (MvPolynomial (Fin 2) (F p)) v
  -- `div_eq_iff hden_ne : a / c = b ↔ a = b * c`, so `.mp hdiv : algebraMap
  -- num = v * algebraMap den` — commuted from this theorem's stated goal
  -- (`algebraMap den * v`), matching `towerToRdec_spec`'s own `hbase` local
  -- proof (`DataDerivationMumford.lean`), which needs the same `mul_comm`
  -- after its own `div_eq_iff` step for exactly this reason.
  have h := (div_eq_iff hden_ne).mp hdiv
  rw [mul_comm] at h
  exact h

end TheDataDerivation
end Genus2Lean
