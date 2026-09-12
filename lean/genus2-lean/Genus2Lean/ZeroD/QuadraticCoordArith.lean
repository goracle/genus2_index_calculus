import Mathlib
import Genus2Lean.ZeroD.TowerToRdecMul

/-!
# Explicit coordinate arithmetic for `AdjoinRoot (X^2 - C c)`

**Status, read first**: §1 below (the actual algebraic identity) is
complete. §2 (packaging it as an `IsRdecWitness` bridge) is NOT drafted in
this file -- see that section's own header for why, and for the two
concrete options left for the next pass. Importing `TowerToRdecMul` anyway
since `IsRdecWitness` is referenced throughout this docstring's motivation
and by §2's own header notes.

New this pass. `ROADMAP-crossnondegenerate-degree-bound.md`'s final
"Update" section and `ZeroD-README.md`'s "Current state" item 1 both trace
the remaining `hA`/`hB` gap in `CrossNondegenerateDegreeBound.lean` to one
precisely-scoped missing piece: a `totalDegree` bound on the `K1`/`K0`
*coordinates* `(modByMonicHom v).coeff 0`/`.coeff 1` of a `K2`/`K1`-valued
tower element `v`, not merely an existential `IsRdecWitness`/`IsLocalization.
mk'` bound on `v` as a whole (`QuadraticCoordinateBridge.lean`'s own header
documents two ruled-out routes for getting the former from the latter: (1)
inverting a single witness equation -- one equation in two unknowns, no
second relation available; (2) decomposing the witness pair's own
`w`-coordinate structure, which doesn't exist, since `IsRdecWitness`'s
witness pair is always base-ring-valued).

**What this file provides instead, per the roadmap's own "concrete next
step": trace the arithmetic construction directly, rather than
reverse-engineering it from a whole-value witness.** `AdjoinRoot.
modByMonicHom` is NOT a ring homomorphism in general (documented at
`TowerToRdecMul.lean`'s header), but for a monic QUADRATIC `g := X^2 - C c`
specifically there IS an explicit, elementary closed-form multiplication
rule on coordinates -- the familiar `(x0+x1 w)(y0+y1 w) = (x0 y0 + c x1 y1)
+ (x0 y1 + x1 y0) w` quadratic-extension formula, `w^2 = c` used exactly
once. This is standard algebra, not curve-specific, so §1 below proves it
fully generically (`CommRing R`, arbitrary `c : R`, no `Field`/`Genus2Lean`
content at all), matching this project's existing precedent for standalone
generic lemmas (`MvPolynomialTotalDegreeMulEq.lean`, `NegateVarTotalDegree.
lean`) -- reusable verbatim at both the `K1` (`c := fAtT p ... 0`) and `K2`
(`c := algebraMap ... (fAtT p ... 1)`) tower levels without restating the
proof. **§2 is scoped but not drafted** -- see its own header below for
exactly what it should say and why a first attempt at stating it fully
generically this pass was caught as type-incorrect before being left in the
file, plus the two concrete options for actually writing it next time.
Closing `hA`/`hB` fully needs §1 (or its §2 packaging) threaded all the way
through `curBeforeMonic.coeff i`'s actual construction (`t1,t2,gu0,gu1,
Npoly.coeff k`'s combination, `CurBeforeMonicCoeffTotalDegree.lean`) -- also
not attempted in this file.

**§1 not yet REPL-confirmed** -- drafted this pass; Claire tests via the
REPL. Update: the first REPL run surfaced three errors, now fixed: (1)
`monic_X_sq_sub_C`'s degree comparison was stated against a bare `2`
instead of `(X^2).degree`, fixed via `degree_X_pow`; (2)
`modByMonic_X_sq_sub_C_eq`'s `hgne1`/`compute_degree!` step needs
`Nontrivial R` (in the trivial ring `X^2 - C c = 0`, so `natDegree ≠ 2`),
now added as a file-wide hypothesis since no downstream file uses these
lemmas without it being available anyway; (3) `mk_mul_coord_eq`'s
`hexpand` `ring` calls failed because `set`-introduced `g` is opaque to
`ring` -- fixed by expanding `C`'s `map_add`/`map_mul` first so the goal
is pure ring elements before calling `ring`. Still awaiting Claire's
re-run to confirm these compile.
-/

namespace Genus2Lean
namespace TheDataDerivation

open Polynomial

variable {R : Type*} [CommRing R] [Nontrivial R]

/-! ## §1. The generic quadratic-coordinate multiplication identity -/

/-- **`X^2 - C c` is monic.** Same proof shape as `K1_poly_monic`/
`K2_poly_monic` (`DataDerivationMumford.lean`), generalized away from any
particular `R`/`c` -- those two theorems could (if convenient later) be
restated as direct applications of this one instead of reproving the fact
locally each time; not done here, to avoid touching load-bearing files this
pass. -/
theorem monic_X_sq_sub_C (c : R) : (X ^ 2 - C c : Polynomial R).Monic := by
  have hrw : (X ^ 2 - C c : Polynomial R) = X ^ 2 + C (-c) := by
    rw [Polynomial.C_neg, sub_eq_add_neg]
  rw [hrw]
  refine (monic_X_pow 2).add_of_left ?_
  calc (C (-c) : Polynomial R).degree ≤ 0 := degree_C_le
    _ < (X ^ 2 : Polynomial R).degree := by
        rw [degree_X_pow]
        norm_cast

/-- **Every polynomial's `%ₘ (X^2 - C c)` remainder is exactly its own
`coeff 0 + coeff 1 • X`** (a two-term normal form). Same shape as
`adjoinRoot_quadratic_normal_form`'s inline `hrpoly`/`hrdeg` argument
(`DataDerivationMumford.lean`), extracted as its own reusable lemma since
`mk_mul_coord_eq` below needs it applied three separate times (to `fx %ₘ
g`, `fy %ₘ g`, and implicitly to the product's own remainder via the
`AdjoinRoot.mk`-kernel argument). -/
theorem modByMonic_X_sq_sub_C_eq (c : R) (f : Polynomial R) :
    f %ₘ (X ^ 2 - C c) = C ((f %ₘ (X ^ 2 - C c)).coeff 0) +
      C ((f %ₘ (X ^ 2 - C c)).coeff 1) * X := by
  set r := f %ₘ (X ^ 2 - C c) with hr
  have hgmonic := monic_X_sq_sub_C (R := R) c
  have hgdeg : (X ^ 2 - C c : Polynomial R).natDegree = 2 := by
    compute_degree!
  have hgne1 : (X ^ 2 - C c : Polynomial R) ≠ 1 := by
    intro h
    rw [h, Polynomial.natDegree_one] at hgdeg
    omega
  have hrdeg : r.natDegree < 2 := by
    have hlt := Polynomial.natDegree_modByMonic_lt f hgmonic hgne1
    simpa [r, hgdeg] using hlt
  apply Polynomial.ext
  intro n
  match n with
  | 0 => simp
  | 1 => simp
  | n + 2 =>
      have hn : r.coeff (n + 2) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      simp [hn]

/-- **The key algebraic identity: `AdjoinRoot.mk`'s coordinates multiply via
the standard quadratic-extension rule.** For `g := X^2 - C c` and any two
polynomials `fx fy`, writing `x0,x1` (resp. `y0,y1`) for `fx`'s (resp.
`fy`'s) `%ₘ g`-coordinates, `(mk g fx) * (mk g fy) = mk g ((x0*y0+c*x1*y1) +
(x0*y1+x1*y0)*X)` -- the familiar `(x0+x1 w)(y0+y1 w) = (x0y0+c x1y1) +
(x0y1+x1y0) w` formula, `w^2 = c` used exactly once. Proved by rewriting
both factors to their two-term normal forms (`modByMonic_X_sq_sub_C_eq`),
expanding the product, and replacing the resulting `X^2` term via `X^2 = g +
C c` -- `AdjoinRoot.mk g` kills the resulting `g`-multiple
(`AdjoinRoot.mk_self`), leaving exactly the claimed two-term value. -/
theorem mk_mul_coord_eq (c : R) (fx fy : Polynomial R) :
    (AdjoinRoot.mk (X ^ 2 - C c) fx) * (AdjoinRoot.mk (X ^ 2 - C c) fy) =
      AdjoinRoot.mk (X ^ 2 - C c)
        (C (((fx %ₘ (X ^ 2 - C c)).coeff 0) * ((fy %ₘ (X ^ 2 - C c)).coeff 0) +
              c * ((fx %ₘ (X ^ 2 - C c)).coeff 1) * ((fy %ₘ (X ^ 2 - C c)).coeff 1)) +
          C (((fx %ₘ (X ^ 2 - C c)).coeff 0) * ((fy %ₘ (X ^ 2 - C c)).coeff 1) +
              ((fx %ₘ (X ^ 2 - C c)).coeff 1) * ((fy %ₘ (X ^ 2 - C c)).coeff 0)) * X) := by
  set g : Polynomial R := X ^ 2 - C c with hgdef
  set x0 := (fx %ₘ g).coeff 0 with hx0
  set x1 := (fx %ₘ g).coeff 1 with hx1
  set y0 := (fy %ₘ g).coeff 0 with hy0
  set y1 := (fy %ₘ g).coeff 1 with hy1
  have hgmonic := monic_X_sq_sub_C (R := R) c
  -- `mk g fx = mk g (fx %ₘ g)`, via the SAME `mk_leftInverse`-based idiom
  -- `adjoinRoot_quadratic_normal_form` already uses (`hmod`/`hmk` there,
  -- `DataDerivationMumford.lean`).
  have hmodx : AdjoinRoot.modByMonicHom hgmonic (AdjoinRoot.mk g fx) = fx %ₘ g :=
    AdjoinRoot.modByMonicHom_mk hgmonic fx
  have hmkx : AdjoinRoot.mk g fx = AdjoinRoot.mk g (fx %ₘ g) := by
    rw [← hmodx]
    exact (AdjoinRoot.mk_leftInverse hgmonic (AdjoinRoot.mk g fx)).symm
  have hmody : AdjoinRoot.modByMonicHom hgmonic (AdjoinRoot.mk g fy) = fy %ₘ g :=
    AdjoinRoot.modByMonicHom_mk hgmonic fy
  have hmky : AdjoinRoot.mk g fy = AdjoinRoot.mk g (fy %ₘ g) := by
    rw [← hmody]
    exact (AdjoinRoot.mk_leftInverse hgmonic (AdjoinRoot.mk g fy)).symm
  rw [hmkx, hmky, ← map_mul]
  have hxr : fx %ₘ g = C x0 + C x1 * X := modByMonic_X_sq_sub_C_eq c fx
  have hyr : fy %ₘ g = C y0 + C y1 * X := modByMonic_X_sq_sub_C_eq c fy
  rw [hxr, hyr]
  have hX2 : (X : Polynomial R) ^ 2 = g + C c := by rw [hgdef]; ring
  have hexpand :
      (C x0 + C x1 * X) * (C y0 + C y1 * X) =
        g * (C x1 * C y1) +
          (C (x0 * y0 + c * x1 * y1) + C (x0 * y1 + x1 * y0) * X) := by
    have hstep : (C x0 + C x1 * X) * (C y0 + C y1 * X) =
        C (x0 * y0) + C (x0 * y1 + x1 * y0) * X + (C x1 * C y1) * X ^ 2 := by
      simp only [map_add, map_mul]
      ring
    rw [hstep, hX2]
    simp only [map_add, map_mul]
    ring
  rw [hexpand, map_add, map_mul, AdjoinRoot.mk_self, zero_mul, zero_add]

/-! ## §2. Not yet attempted: the `IsRdecWitness` coordinate-splitting bridge

**Deliberately left for the next pass, not drafted half-working here.**
The natural next step is to package §1's identity in the shape the rest of
the tower-degree chain consumes: given `IsRdecWitness`-shaped witnesses
(against the RESTRICTED embedding `ι0 := ι.comp (algebraMap R (AdjoinRoot
g))`, `R`-valued, one tower level below `AdjoinRoot g`) for `x`'s two `%ₘ
g`-coordinates, `y`'s two `%ₘ g`-coordinates, and `c` itself, produce an
`IsRdecWitness`-shaped witness (against the FULL embedding `ι : AdjoinRoot g
→+* L`) for `(mk g fx)*(mk g fy)` directly, via `IsRdecWitness.add`/`.mul`
(`TowerToRdecMul.lean`) composing the five input witnesses through
`mk_mul_coord_eq`'s `(x0y0+c x1y1, x0y1+x1y0)` formula.

**Why this is genuinely more delicate to STATE than it first looks, flagged
honestly rather than papered over with a rushed draft**: `IsRdecWitness p ι
evalNd v nd`'s `ι : K →+* L` argument fixes a SPECIFIC field `K` (in this
project's actual use, always the concrete `K1 p c0 c1 c2 c3 c4` or `K2 p
c0 c1 c2 c3 c4`, never a bare `AdjoinRoot (X^2 - C c)` for a free-standing
variable `c : R`). Stating the bridge theorem fully generically (parametric
in `R`/`c`, matching §1's own generality) means `ι`'s domain has to be
`AdjoinRoot (X^2 - C c)` itself as a genuinely varying type across the
statement, which interacts awkwardly with how `IsRdecWitness` is currently
set up (implicit `{Vars K L}` with `K` inferred from `ι`'s stated type, not
threaded separately) -- a first attempt at this pass produced a
type-incorrect draft (confusing `ι`'s intended domain with `R` itself) that
was caught before being left in the file. **The two honest options for next
time**: (a) state the bridge already specialized to `K1`/`K2` (two
near-duplicate theorems, `R := K0 p`/`c := fAtT p ... 0` and `R := K1 p ...`
/`c := algebraMap ... (fAtT p ... 1)` respectively) rather than fully
generically -- more code, less abstraction risk; (b) find the right fully
generic phrasing (likely: take `ι0 : R →+* L` and `ι : AdjoinRoot (X^2 - C
c) →+* L` as SEPARATE hypotheses with an explicit compatibility hypothesis
`hι : ∀ r, ι (algebraMap R (AdjoinRoot (X^2-C c)) r) = ι0 r` and `hιroot : ι
(AdjoinRoot.root (X^2-C c)) = <whatever the ambient w-generator maps to>`,
mirroring `towerToRdec_spec`'s own `hι_t`/`hι_w1`/`hι_w2` hypothesis-style
rather than trying to derive the restriction automatically). Option (b)
matches this project's existing `towerToRdec_spec`/`hι_w1`-style precedent
more closely and is likely the right one, but is real, un-attempted design
work, not a small follow-up -- left for the next pass rather than rushed. -/

end TheDataDerivation
end Genus2Lean
