import Mathlib
import Genus2Lean.ZeroD.EpolyTotalDegree

/-!
# `Npoly.coeff k`'s own `IsRdecWitness` bound

New this pass. Closes the gap `NpolyTotalDegree.lean`'s own closing note
flagged as "not attempted this pass given the size": item 3 of that
file's route, `Npoly.coeff k`'s `IsRdecWitness` bound, built from
`Epoly`/`Ypoly`/`fAtX`'s own coefficient witnesses (`Epoly_coeff_
isRdecWitness`, `EpolyTotalDegree.lean`; `Ypoly_coeff_isRdecWitness`/
`algebraMap_Fp_isRdecWitness`, `NpolyTotalDegree.lean`) via
`IsRdecWitness.add`/`.mul`/`.neg` unrolled through `Npoly := Epoly^2 -
fAtX * Ypoly^2`'s `Polynomial.coeff_mul`/`coeff_sub` expansion.

**Route, concretely**:

1. `Npoly = Epoly * Epoly - fAtX * (Ypoly * Ypoly)` (`sq` unfolded to a
   plain product, avoiding `Polynomial.coeff_pow`/`Finset.antidiagonal`'s
   general-exponent machinery entirely — `Polynomial.coeff_mul` alone
   suffices for a SQUARE, since `f^2 = f*f` by `sq`/`pow_two`).
2. `Polynomial.coeff_sub`/`coeff_mul` unroll `Npoly.coeff k` into
   `(∑ x ∈ antidiagonal k, Epoly.coeff x.1 * Epoly.coeff x.2) - (fAtX *
   (Ypoly*Ypoly)).coeff k`, and the second term itself needs ONE more
   `coeff_mul` (`fAtX` against `Ypoly*Ypoly`), so overall TWO nested
   `antidiagonal`-indexed sums, each term a product of coefficients
   individually witnessed by `Epoly_coeff_isRdecWitness`/`Ypoly_coeff_
   isRdecWitness`/`algebraMap_Fp_isRdecWitness` (`fAtX.coeff k =
   algebraMap (F p) (K2 ...) (curvePoly.coeff k)`, `Polynomial.coeff_map`).
3. Rather than hand-unroll `IsRdecWitness.add` `|antidiagonal k|`-many
   times (which would need a length-dependent induction the caller has
   no easy handle on), this file proves ONE reusable helper,
   `IsRdecWitness_finsetSum` (below): given a witness for `f i` at every
   `i` in a finite index set `s`, `∑ i ∈ s, f i` itself has a witness,
   by a plain `Finset.sum_induction`-style induction on `s` using
   `IsRdecWitness.add` at the cons step and the trivial zero-witness
   `(0,1)` at the empty step. This is the missing "sum" combinator
   `IsRdecWitness.mul`/`.add`/`.neg` were building toward, genuinely new
   this pass (not attempted anywhere else in this project so far), and
   is exactly general enough to close BOTH nested sums here (and any
   future `Finset.sum`-shaped `IsRdecWitness` obligation) without
   re-deriving induction machinery per call site.
4. Each individual product term `Epoly.coeff i * Epoly.coeff j` (resp.
   `Ypoly.coeff i * Ypoly.coeff j`, `fAtX.coeff i * (Ypoly*Ypoly).coeff
   j`) gets its witness via `IsRdecWitness.mul` applied to the two
   factors' own witnesses — `Epoly_coeff_isRdecWitness`/`Ypoly_coeff_
   isRdecWitness` directly for the two squared terms, and a THIRD
   nested `IsRdecWitness_finsetSum`+`.mul` application for `(Ypoly *
   Ypoly).coeff j` itself (a further `antidiagonal j`-indexed sum),
   giving three `antidiagonal`-nesting levels total for the `fAtX *
   Ypoly^2` branch. Finally `IsRdecWitness.neg`/`.add`-as-subtraction
   (`a - b = a + (-b)`, `sub_eq_add_neg`) combines the two top-level
   pieces.

**Concrete bound**: `Epoly.coeff _`/`Ypoly.coeff _` are both witnessed at
`≤ 704` (both numerator and denominator, per `Epoly_coeff_isRdecWitness`/
`Ypoly_coeff_isRdecWitness`), and `fAtX.coeff _` at `≤ 0` (numerator
`MvPolynomial.C x` has `totalDegree 0`; denominator `1` has `totalDegree
0`) via `algebraMap_Fp_isRdecWitness`. Each `IsRdecWitness.mul` step adds
the two factors' bounds (`totalDegree_mul`-style, baked into `.mul`'s own
proof, though `.mul` itself doesn't STATE a totalDegree bound — that's
tracked separately below via `MvPolynomial.totalDegree_mul`/`_add`/`_neg`
applied to the WITNESS PAIRS `IsRdecWitness_finsetSum`/`.mul`/`.add`/`.neg`
produce, mirroring `cramerSolution_totalDegree_le`'s own style of pairing
an existence proof with an explicit numeral bound rather than folding the
bound into the existence statement itself). Each `antidiagonal k` sum has
`≤ k+1` terms (`Finset.Nat.card_antidiagonal`), so for `Npoly.coeff k` the
final numeral bound genuinely depends on `k` — stated here as a bound
LINEAR in `k` (`≤ (k+1) * 1408` for the `Epoly*Epoly` branch's numerator,
`≤ (k+1) * (k+1) * 704`-ish for the doubly-nested `fAtX*Ypoly^2` branch —
see `Npoly_coeff_isRdecWitness`'s own statement for the exact closed
form), NOT a single `k`-independent numeral the way every earlier file in
this chain (`Epoly`/`Ypoly`/`coeffsOut`) managed, since `Npoly`'s degree
in `X` is unbounded a priori from this file's viewpoint (`CrossNondegenerateDegreeBound.lean`'s
`D` hypothesis is exactly this: a caller-supplied bound on which `k`s can
be nonzero at all — see that file's own docstring). This file bounds
EVERY `k` uniformly in terms of `k` itself; pinning down the actual
nonzero range of `k` (i.e. `Npoly.natDegree`) is `Npoly_natDegree_le_six`
(`DecoupledSystemRegular.lean`, already proved) — combining the two
(this file's per-`k` bound, evaluated only at `k ≤ 6`) is the next
assembly step, not attempted here.

**Not yet REPL-confirmed** — no build environment available this
session; per project convention, Claude drafts, Claire tests.
-/

namespace Genus2Lean
namespace TheDataDerivation

open Polynomial

variable (p : ℕ) [hp : Fact (Nat.Prime p)] [hp2 : Fact (p ≠ 2)]
variable (c0 c1 c2 c3 c4 : F p)

/-- **The missing "finite sum" combinator.** Given an `IsRdecWitness`
witness for `f i` at every `i ∈ s` (`s : Finset ι`, any index type), the
plain product-pair recursion (`IsRdecWitness.add` at each step,
`(0,1)` — the trivial `evalNd 0 = evalNd 1 * ι 0` witness for `0` — at
the empty base case) gives a witness for `∑ i ∈ s, f i` itself, by
`Finset.cons_induction` on `s`. Proved once, generically, rather than
re-derived per call site — this is the piece `NpolyTotalDegree.lean`'s
own closing note flagged as needed ("`IsRdecWitness.add` applied
`|antidiagonal k|`-many times, not just once") without yet supplying a
combinator general enough to do that in one step. -/
theorem IsRdecWitness_finsetSum {Vars K L ι : Type*} [CommRing K] [CommRing L]
    {ιmap : K →+* L} {evalNd : MvPolynomial Vars (F p) →+* L}
    (s : Finset ι) (f : ι → K)
    (nd : ι → MvPolynomial Vars (F p) × MvPolynomial Vars (F p))
    (hnd : ∀ i ∈ s, IsRdecWitness p ιmap evalNd (f i) (nd i)) :
    ∃ nd' : MvPolynomial Vars (F p) × MvPolynomial Vars (F p),
      IsRdecWitness p ιmap evalNd (∑ i ∈ s, f i) nd' := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
      refine ⟨(0, 1), ?_⟩
      unfold IsRdecWitness
      simp
  | cons a t hat ih =>
      have hrest : ∃ nd' : MvPolynomial Vars (F p) × MvPolynomial Vars (F p),
          IsRdecWitness p ιmap evalNd (∑ i ∈ t, f i) nd' :=
        ih (fun i hi => hnd i (Finset.mem_cons_of_mem hi))
      obtain ⟨ndt, hwt⟩ := hrest
      have hwa : IsRdecWitness p ιmap evalNd (f a) (nd a) :=
        hnd a (Finset.mem_cons_self a t)
      refine ⟨((nd a).1 * ndt.2 + ndt.1 * (nd a).2, (nd a).2 * ndt.2), ?_⟩
      have hsum : ∑ i ∈ Finset.cons a t hat, f i = f a + ∑ i ∈ t, f i :=
        Finset.sum_cons hat
      rw [hsum]
      exact IsRdecWitness.add p hwa hwt

/-- **`totalDegree` bound accompanying `IsRdecWitness_finsetSum`.** If
every `i ∈ s`'s witness pair has both components `≤ D`, the assembled
sum-witness has both components `≤ s.card * D` — a direct induction
mirroring the existence proof above, tracking the numeral bound
alongside it (`IsRdecWitness.add`'s own witness pair `(na*db+nb*da,
da*db)` has `totalDegree ≤ max (Da+Db) (Da+Db) = Da+Db` on the numerator
side, `≤ Da+Db` on the denominator side too, both `MvPolynomial.
totalDegree_mul`/`_add` — so combining a running bound `k*D` (for the
first `k` terms already summed) with one more term's `≤ D` gives
`≤ (k+1)*D` at each step, exactly `Finset.card`-many steps total). -/
theorem IsRdecWitness_finsetSum_totalDegree_le {Vars K L ι : Type*} [CommRing K] [CommRing L]
    {ιmap : K →+* L} {evalNd : MvPolynomial Vars (F p) →+* L}
    (s : Finset ι) (f : ι → K) {D : ℕ}
    (nd : ι → MvPolynomial Vars (F p) × MvPolynomial Vars (F p))
    (hnd : ∀ i ∈ s, IsRdecWitness p ιmap evalNd (f i) (nd i))
    (hD : ∀ i ∈ s, (nd i).1.totalDegree ≤ D ∧ (nd i).2.totalDegree ≤ D) :
    ∃ nd' : MvPolynomial Vars (F p) × MvPolynomial Vars (F p),
      IsRdecWitness p ιmap evalNd (∑ i ∈ s, f i) nd' ∧
      nd'.1.totalDegree ≤ s.card * D ∧ nd'.2.totalDegree ≤ s.card * D := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
      refine ⟨(0, 1), ?_, ?_, ?_⟩
      · unfold IsRdecWitness; simp
      · simp
      · simp
  | cons a t hat ih =>
      have hrest := ih (fun i hi => hnd i (Finset.mem_cons_of_mem hi))
        (fun i hi => hD i (Finset.mem_cons_of_mem hi))
      obtain ⟨ndt, hwt, hnt, hdt⟩ := hrest
      have hwa : IsRdecWitness p ιmap evalNd (f a) (nd a) :=
        hnd a (Finset.mem_cons_self a t)
      have hDa := hD a (Finset.mem_cons_self a t)
      have hsum : ∑ i ∈ Finset.cons a t hat, f i = f a + ∑ i ∈ t, f i :=
        Finset.sum_cons hat
      refine ⟨((nd a).1 * ndt.2 + ndt.1 * (nd a).2, (nd a).2 * ndt.2), ?_, ?_, ?_⟩
      · rw [hsum]; exact IsRdecWitness.add p hwa hwt
      · have hb1 : ((nd a).1 * ndt.2).totalDegree ≤ D + t.card * D := by
          have h1 : ((nd a).1 * ndt.2).totalDegree ≤ (nd a).1.totalDegree + ndt.2.totalDegree :=
            MvPolynomial.totalDegree_mul _ _
          have h2 := hDa.1
          have h3 := hdt
          omega
        have hb2 : (ndt.1 * (nd a).2).totalDegree ≤ D + t.card * D := by
          have h1 : (ndt.1 * (nd a).2).totalDegree ≤ ndt.1.totalDegree + (nd a).2.totalDegree :=
            MvPolynomial.totalDegree_mul _ _
          have h2 := hDa.2
          have h3 := hnt
          omega
        have hb3 : ((nd a).1 * ndt.2 + ndt.1 * (nd a).2).totalDegree ≤
            max (((nd a).1 * ndt.2).totalDegree) ((ndt.1 * (nd a).2).totalDegree) :=
          MvPolynomial.totalDegree_add _ _
        rw [Finset.card_cons]
        show ((nd a).1 * ndt.2 + ndt.1 * (nd a).2).totalDegree ≤ (t.card + 1) * D
        have hexp : (t.card + 1) * D = D + t.card * D := by ring
        have : max (((nd a).1 * ndt.2).totalDegree) ((ndt.1 * (nd a).2).totalDegree) ≤ D + t.card * D :=
          max_le hb1 hb2
        omega
      · have h1 : ((nd a).2 * ndt.2).totalDegree ≤ (nd a).2.totalDegree + ndt.2.totalDegree :=
          MvPolynomial.totalDegree_mul _ _
        have h2 := hDa.2
        have h3 := hdt
        rw [Finset.card_cons]
        show ((nd a).2 * ndt.2).totalDegree ≤ (t.card + 1) * D
        have hexp : (t.card + 1) * D = D + t.card * D := by ring
        omega

/-- **`fAtX.coeff k`'s `IsRdecWitness` bound.** `fAtX = curvePoly.map
(algebraMap (F p) (K2 ...))`, so `Polynomial.coeff_map` gives `fAtX.coeff
k = algebraMap (F p) (K2 ...) (curvePoly.coeff k)` directly — a plain
constant of `F p` pushed through the tower's algebra map, exactly
`algebraMap_Fp_isRdecWitness`'s own shape, applied at `x := curvePoly.coeff
k`. -/
theorem fAtX_coeff_isRdecWitness {Vars : Type*}
    (u0 u1 v0 v1 : F p)
    (ι : K2 p c0 c1 c2 c3 c4 →+* FractionRing (MvPolynomial Vars (F p)))
    (k : ℕ) :
    ∃ nd : MvPolynomial Vars (F p) × MvPolynomial Vars (F p),
      IsRdecWitness p ι
        (algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p))))
        ((fAtX p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff k) nd ∧
      nd.1.totalDegree ≤ 0 ∧ nd.2.totalDegree ≤ 0 := by
  have heq : (fAtX p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff k =
      algebraMap (F p) (K2 p c0 c1 c2 c3 c4) ((curvePoly p c0 c1 c2 c3 c4).coeff k) := by
    unfold fAtX
    exact Polynomial.coeff_map _ k
  rw [heq]
  refine ⟨(MvPolynomial.C ((curvePoly p c0 c1 c2 c3 c4).coeff k), 1), ?_, ?_, ?_⟩
  · exact algebraMap_Fp_isRdecWitness p ι _
  · simp [MvPolynomial.totalDegree_C]
  · simp [MvPolynomial.totalDegree_one]

/-- **`(Ypoly * Ypoly).coeff k`'s `IsRdecWitness` bound.** `Polynomial.
coeff_mul` unrolls it to `∑ x ∈ antidiagonal k, Ypoly.coeff x.1 *
Ypoly.coeff x.2`; each summand's witness is `IsRdecWitness.mul` applied
to two `Ypoly_coeff_isRdecWitness` instances (bound `≤704` each side, so
`≤1408` each side per product term via `.mul`'s own `totalDegree_mul`-
style addition, tracked explicitly below rather than through `.mul`
itself which doesn't carry a bound), and `IsRdecWitness_finsetSum_
totalDegree_le` assembles the `antidiagonal k`-indexed sum, using
`Finset.Nat.card_antidiagonal : (antidiagonal k).card = k+1`. -/
theorem Ypoly_sq_coeff_isRdecWitness {Vars : Type*} [DecidableEq Vars]
    (u0 u1 v0 v1 : F p)
    (ι : K2 p c0 c1 c2 c3 c4 →+* FractionRing (MvPolynomial Vars (F p)))
    (k : ℕ) :
    ∃ nd : MvPolynomial Vars (F p) × MvPolynomial Vars (F p),
      IsRdecWitness p ι
        (algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p))))
        ((Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1 * Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff k) nd ∧
      nd.1.totalDegree ≤ (k + 1) * 1408 ∧ nd.2.totalDegree ≤ (k + 1) * 1408 := by
  classical
  -- `s` is bound to whatever index Finset `Polynomial.coeff_mul` itself
  -- uses, never spelled out as a literal `Finset.antidiagonal k` term by
  -- this proof — avoids a name-resolution ambiguity between the
  -- `Finset.HasAntidiagonal`-based `Finset.antidiagonal` (the one
  -- `Polynomial.coeff_mul` actually uses) and an unrelated PWO-based
  -- `antidiagonal` also in scope under some name.
  obtain ⟨s, heq, hcard⟩ : ∃ s : Finset (ℕ × ℕ),
      ((Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1 * Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff k =
        ∑ x ∈ s, (Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff x.1 *
          (Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff x.2) ∧ s.card = k + 1 :=
    ⟨_, Polynomial.coeff_mul _ _ _, Finset.Nat.card_antidiagonal k⟩
  rw [heq]
  -- Build the per-term witness/bound data by extracting each `x.1`/`x.2`
  -- witness pair via `obtain` ONCE (not `.choose`/`.choose_spec` used
  -- afresh at every occurrence, which forces the elaborator to re-check
  -- the same large applied `Ypoly_coeff_isRdecWitness` term repeatedly
  -- and was the source of a `whnf` heartbeat timeout here) then combine
  -- via `IsRdecWitness.mul`.
  set f : ℕ × ℕ → K2 p c0 c1 c2 c3 c4 :=
    fun x => (Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff x.1 *
      (Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff x.2 with hf_def
  have hchoose : ∀ i : ℕ, ∃ nd0 : MvPolynomial Vars (F p) × MvPolynomial Vars (F p),
      IsRdecWitness p ι
        (algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p))))
        ((Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff i) nd0 ∧
      nd0.1.totalDegree ≤ 704 ∧ nd0.2.totalDegree ≤ 704 :=
    fun i => Ypoly_coeff_isRdecWitness p u0 u1 v0 v1 ι i
  choose nd0 hnd0wit hnd0n hnd0d using hchoose
  set nd : ℕ × ℕ → MvPolynomial Vars (F p) × MvPolynomial Vars (F p) :=
    fun x => ((nd0 x.1).1 * (nd0 x.2).1, (nd0 x.1).2 * (nd0 x.2).2) with hnd_def
  have hwit : ∀ x ∈ s, IsRdecWitness p ι
      (algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p))))
      (f x) (nd x) := by
    intro x _
    exact IsRdecWitness.mul p (hnd0wit x.1) (hnd0wit x.2)
  have hDbound : ∀ x ∈ s, (nd x).1.totalDegree ≤ 1408 ∧
      (nd x).2.totalDegree ≤ 1408 := by
    intro x _
    refine ⟨?_, ?_⟩
    · calc (nd x).1.totalDegree ≤ _ := MvPolynomial.totalDegree_mul _ _
        _ ≤ 1408 := by have := hnd0n x.1; have := hnd0n x.2; omega
    · calc (nd x).2.totalDegree ≤ _ := MvPolynomial.totalDegree_mul _ _
        _ ≤ 1408 := by have := hnd0d x.1; have := hnd0d x.2; omega
  obtain ⟨nd', hwit', hn', hd'⟩ :=
    IsRdecWitness_finsetSum_totalDegree_le p s f nd hwit hDbound
  refine ⟨nd', hwit', ?_, ?_⟩
  · rw [hcard] at hn'; exact hn'
  · rw [hcard] at hd'; exact hd'



set_option maxHeartbeats 2000000 in
/-- **`Npoly.coeff k`'s own `IsRdecWitness` bound, at last.** `Npoly :=
Epoly^2 - fAtX * Ypoly^2`; rewritten as `Epoly*Epoly - fAtX*(Ypoly*Ypoly)`
(`sq`/`pow_two`, avoiding `coeff_pow`'s general machinery), so
`Polynomial.coeff_sub`/`coeff_mul` give `Npoly.coeff k = (∑ x ∈
antidiagonal k, Epoly.coeff x.1 * Epoly.coeff x.2) - (∑ y ∈ antidiagonal
k, fAtX.coeff y.1 * (Ypoly*Ypoly).coeff y.2)`. The first sum's witness:
same `IsRdecWitness_finsetSum_totalDegree_le` route as `Ypoly_sq_coeff_
isRdecWitness` above, but with `Epoly_coeff_isRdecWitness` (bound `≤704`
each side, `≤1408` per product term) in place of `Ypoly`'s. The second
sum's witness: `IsRdecWitness.mul` applied to `fAtX_coeff_isRdecWitness`
(bound `≤0`) and `Ypoly_sq_coeff_isRdecWitness` (bound `≤(k+1)*1408`,
itself `k`-dependent since it's ALREADY a sum), giving each product term
bound `≤ 0 + (y.2+1)*1408 ≤ (k+1)*1408` (since `y.2 ≤ k` for `y ∈
antidiagonal k`), then `IsRdecWitness_finsetSum_totalDegree_le` again for
the outer sum, `≤ (k+1) * ((k+1)*1408)`. Finally `IsRdecWitness.neg` plus
`IsRdecWitness.add` (via `sub_eq_add_neg`) combines the two top-level
pieces, giving the stated bound. -/
theorem Npoly_coeff_isRdecWitness {Vars : Type*} [DecidableEq Vars]
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
      nd.1.totalDegree ≤ (k + 1) * 1408 + (k + 1) * ((k + 1) * 1408) ∧
      nd.2.totalDegree ≤ (k + 1) * 1408 + (k + 1) * ((k + 1) * 1408) := by
  classical
  have hNeq : Npoly p c0 c1 c2 c3 c4 u0 u1 v0 v1 =
      Epoly p c0 c1 c2 c3 c4 u0 u1 v0 v1 * Epoly p c0 c1 c2 c3 c4 u0 u1 v0 v1 -
        fAtX p c0 c1 c2 c3 c4 u0 u1 v0 v1 *
          (Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1 * Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1) := by
    unfold Npoly; ring
  rw [hNeq, Polynomial.coeff_sub]
  -- First summand: `(Epoly*Epoly).coeff k`.
  obtain ⟨s1, heq1, hcard1⟩ : ∃ s : Finset (ℕ × ℕ),
      ((Epoly p c0 c1 c2 c3 c4 u0 u1 v0 v1 * Epoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff k =
        ∑ x ∈ s, (Epoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff x.1 *
          (Epoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff x.2) ∧ s.card = k + 1 :=
    ⟨_, Polynomial.coeff_mul _ _ _, Finset.Nat.card_antidiagonal k⟩
  set f1 : ℕ × ℕ → K2 p c0 c1 c2 c3 c4 :=
    fun x => (Epoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff x.1 *
      (Epoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff x.2 with hf1_def
  -- Extract each index's witness pair ONCE via `choose` rather than
  -- calling `.choose`/`.choose_spec` afresh at every occurrence (the
  -- latter forces the elaborator to re-check the same large applied
  -- `Epoly_coeff_isRdecWitness` term repeatedly and was the source of a
  -- `whnf` heartbeat timeout here).
  have hchoose1 : ∀ i : ℕ, ∃ nd0 : MvPolynomial Vars (F p) × MvPolynomial Vars (F p),
      IsRdecWitness p ι
        (algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p))))
        ((Epoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff i) nd0 ∧
      nd0.1.totalDegree ≤ 704 ∧ nd0.2.totalDegree ≤ 704 :=
    fun i => Epoly_coeff_isRdecWitness p c0 c1 c2 c3 c4 sg u0 u1 v0 v1 ι
      hι_t hι_w1 hι_w2 hbidx hAne hRne hDne hιdet_ne i
  choose nd1a hnd1awit hnd1an hnd1ad using hchoose1
  set nd1 : ℕ × ℕ → MvPolynomial Vars (F p) × MvPolynomial Vars (F p) :=
    fun x => ((nd1a x.1).1 * (nd1a x.2).1, (nd1a x.1).2 * (nd1a x.2).2) with hnd1_def
  have hwit1 : ∀ x ∈ s1, IsRdecWitness p ι
      (algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p))))
      (f1 x) (nd1 x) := by
    intro x _
    exact IsRdecWitness.mul p (hnd1awit x.1) (hnd1awit x.2)
  have hDbound1 : ∀ x ∈ s1, (nd1 x).1.totalDegree ≤ 1408 ∧
      (nd1 x).2.totalDegree ≤ 1408 := by
    intro x _
    refine ⟨?_, ?_⟩
    · calc (nd1 x).1.totalDegree ≤ _ := MvPolynomial.totalDegree_mul _ _
        _ ≤ 1408 := by have := hnd1an x.1; have := hnd1an x.2; omega
    · calc (nd1 x).2.totalDegree ≤ _ := MvPolynomial.totalDegree_mul _ _
        _ ≤ 1408 := by have := hnd1ad x.1; have := hnd1ad x.2; omega
  obtain ⟨ndA, hwitA, hnA, hdA⟩ :=
    IsRdecWitness_finsetSum_totalDegree_le p s1 f1 nd1 hwit1 hDbound1
  rw [hcard1] at hnA hdA
  have hwitA' : IsRdecWitness p ι
      (algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p))))
      ((Epoly p c0 c1 c2 c3 c4 u0 u1 v0 v1 * Epoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff k) ndA := by
    rw [heq1]; exact hwitA
  -- Second summand: `(fAtX * (Ypoly*Ypoly)).coeff k`. Route via
  -- `Finset.Nat.sum_antidiagonal_eq_sum_range_succ` to convert the
  -- antidiagonal sum straight into a `Finset.range (k+1)` sum — this
  -- sidesteps needing any `Finset.antidiagonal`/`mem_antidiagonal` name
  -- at all (a genuine ambiguity hazard in this build: unqualified
  -- `Finset.antidiagonal`/`Finset.mem_antidiagonal` were each observed to
  -- resolve to an unrelated, incompatible overload here), and the
  -- `Finset.range`-indexed shape hands us `y ≤ k` for free from
  -- `Finset.mem_range`, exactly the fact the old antidiagonal-membership
  -- route needed a separate lemma for.
  have heq2 : (fAtX p c0 c1 c2 c3 c4 u0 u1 v0 v1 *
      (Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1 * Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1)).coeff k =
      ∑ y ∈ Finset.range (k + 1), (fAtX p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff y *
        (Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1 * Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff (k - y) := by
    rw [Polynomial.coeff_mul]
    exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => (fAtX p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff i *
        (Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1 * Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff j) k
  set f2 : ℕ → K2 p c0 c1 c2 c3 c4 :=
    fun y => (fAtX p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff y *
      (Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1 * Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff (k - y)
    with hf2_def
  -- Same `choose`-once fix as `nd1a` above, applied to both factors of
  -- this second product (`fAtX_coeff_isRdecWitness`, `≤0` each side, and
  -- `Ypoly_sq_coeff_isRdecWitness`, `≤(i+1)*1408` each side).
  have hchoose2a : ∀ i : ℕ, ∃ nd0 : MvPolynomial Vars (F p) × MvPolynomial Vars (F p),
      IsRdecWitness p ι
        (algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p))))
        ((fAtX p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff i) nd0 ∧
      nd0.1.totalDegree ≤ 0 ∧ nd0.2.totalDegree ≤ 0 :=
    fun i => fAtX_coeff_isRdecWitness p c0 c1 c2 c3 c4 u0 u1 v0 v1 ι i
  choose nd2a hnd2awit hnd2an hnd2ad using hchoose2a
  have hchoose2b : ∀ i : ℕ, ∃ nd0 : MvPolynomial Vars (F p) × MvPolynomial Vars (F p),
      IsRdecWitness p ι
        (algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p))))
        ((Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1 * Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff i) nd0 ∧
      nd0.1.totalDegree ≤ (i + 1) * 1408 ∧ nd0.2.totalDegree ≤ (i + 1) * 1408 :=
    fun i => Ypoly_sq_coeff_isRdecWitness p c0 c1 c2 c3 c4 u0 u1 v0 v1 ι i
  choose nd2b hnd2bwit hnd2bn hnd2bd using hchoose2b
  set nd2 : ℕ → MvPolynomial Vars (F p) × MvPolynomial Vars (F p) :=
    fun y => ((nd2a y).1 * (nd2b (k - y)).1, (nd2a y).2 * (nd2b (k - y)).2)
    with hnd2_def
  have hwit2 : ∀ y ∈ Finset.range (k + 1), IsRdecWitness p ι
      (algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p))))
      (f2 y) (nd2 y) := by
    intro y _
    exact IsRdecWitness.mul p (hnd2awit y) (hnd2bwit (k - y))
  have hDbound2 : ∀ y ∈ Finset.range (k + 1), (nd2 y).1.totalDegree ≤ (k + 1) * 1408 ∧
      (nd2 y).2.totalDegree ≤ (k + 1) * 1408 := by
    intro y hy
    have hy2 : k - y ≤ k := Nat.sub_le k y
    have hmono : (k - y + 1) * 1408 ≤ (k + 1) * 1408 := by
      apply Nat.mul_le_mul_right; omega
    refine ⟨?_, ?_⟩
    · calc (nd2 y).1.totalDegree ≤ _ := MvPolynomial.totalDegree_mul _ _
        _ ≤ (k + 1) * 1408 := by
            have hb1 := hnd2an y; have hb2 := hnd2bn (k - y); omega
    · calc (nd2 y).2.totalDegree ≤ _ := MvPolynomial.totalDegree_mul _ _
        _ ≤ (k + 1) * 1408 := by
            have hb1 := hnd2ad y; have hb2 := hnd2bd (k - y); omega
  obtain ⟨ndB, hwitB, hnB, hdB⟩ :=
    IsRdecWitness_finsetSum_totalDegree_le p (Finset.range (k + 1)) f2 nd2 hwit2 hDbound2
  rw [Finset.card_range] at hnB hdB
  have hwitB' : IsRdecWitness p ι
      (algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p))))
      ((fAtX p c0 c1 c2 c3 c4 u0 u1 v0 v1 *
        (Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1 * Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1)).coeff k) ndB := by
    rw [heq2]; exact hwitB
  -- Combine via `sub_eq_add_neg` and `IsRdecWitness.add`/`.neg`.
  -- `IsRdecWitness.neg hwitB' : IsRdecWitness _ (-(fAtX*(Ypoly*Ypoly)).coeff k) (-ndB.1, ndB.2)`,
  -- then `IsRdecWitness.add hwitA' this` gives the witness for the SUM
  -- `Epoly*Epoly.coeff k + (-(fAtX*Ypoly^2).coeff k)`, pair
  -- `(ndA.1 * ndB.2 + (-ndB.1) * ndA.2, ndA.2 * ndB.2)` — read off directly
  -- from `IsRdecWitness.add`'s own stated conclusion shape, not hand-rolled.
  have hsub : (Epoly p c0 c1 c2 c3 c4 u0 u1 v0 v1 * Epoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff k -
      (fAtX p c0 c1 c2 c3 c4 u0 u1 v0 v1 *
        (Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1 * Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1)).coeff k =
      (Epoly p c0 c1 c2 c3 c4 u0 u1 v0 v1 * Epoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff k +
        (-(fAtX p c0 c1 c2 c3 c4 u0 u1 v0 v1 *
          (Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1 * Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1)).coeff k) := by
    ring
  rw [hsub]
  have hwitBneg := IsRdecWitness.neg p hwitB'
  refine ⟨(ndA.1 * ndB.2 + (-ndB.1) * ndA.2, ndA.2 * ndB.2), IsRdecWitness.add p hwitA' hwitBneg, ?_, ?_⟩
  · calc (ndA.1 * ndB.2 + (-ndB.1) * ndA.2).totalDegree
        ≤ max (ndA.1 * ndB.2).totalDegree ((-ndB.1) * ndA.2).totalDegree :=
          MvPolynomial.totalDegree_add _ _
      _ ≤ (k + 1) * 1408 + (k + 1) * ((k + 1) * 1408) := by
          have hterm1 : (ndA.1 * ndB.2).totalDegree ≤ ndA.1.totalDegree + ndB.2.totalDegree :=
            MvPolynomial.totalDegree_mul _ _
          have hterm2 : ((-ndB.1 : MvPolynomial Vars (F p)) * ndA.2).totalDegree ≤
              (-ndB.1 : MvPolynomial Vars (F p)).totalDegree + ndA.2.totalDegree :=
            MvPolynomial.totalDegree_mul _ _
          have hnegdeg : (-ndB.1 : MvPolynomial Vars (F p)).totalDegree = ndB.1.totalDegree :=
            MvPolynomial.totalDegree_neg _
          rw [hnegdeg] at hterm2
          omega
  · calc (ndA.2 * ndB.2).totalDegree ≤ ndA.2.totalDegree + ndB.2.totalDegree :=
          MvPolynomial.totalDegree_mul _ _
      _ ≤ (k + 1) * 1408 + (k + 1) * ((k + 1) * 1408) := by omega

/-! ## Status, this pass

**Drafted, not yet REPL-confirmed.** Closes the gap `NpolyTotalDegree.lean`'s
own closing note flagged as "not attempted this pass given the size":
`Npoly.coeff k`'s own `IsRdecWitness` bound, via the new `IsRdecWitness_
finsetSum`/`IsRdecWitness_finsetSum_totalDegree_le` combinators (genuinely
new infrastructure, general enough to reuse for any future `Finset.sum`-
shaped `IsRdecWitness` obligation, not just this one), `fAtX_coeff_
isRdecWitness` (the `Polynomial.coeff_map`-level fact connecting `fAtX`'s
coefficients to `algebraMap_Fp_isRdecWitness`), and `Ypoly_sq_coeff_
isRdecWitness` (the one intermediate square needed before `fAtX`'s
product).

**Update, this pass — the flagged `.choose`/`.choose_spec` pattern below
was the actual `whnf` heartbeat-timeout cause, now fixed in place.** The
original draft called `.choose`/`.choose_spec` directly on the EXISTENTIAL
conclusions of `Epoly_coeff_isRdecWitness`/`Ypoly_coeff_isRdecWitness`/
`fAtX_coeff_isRdecWitness`/`Ypoly_sq_coeff_isRdecWitness` inside a
`set ... := fun x => (... ).choose ...` definition, then separately
re-derived `.choose_spec` for the SAME application inside `hwit`/
`hDbound`'s own proofs — four independent re-elaborations of the same
large applied term per lemma, which is exactly what timed out (REPL:
`whnf` heartbeat exhaustion in both `Ypoly_sq_coeff_isRdecWitness` and
`Npoly_coeff_isRdecWitness`). **Fix**: extract each index's witness pair
ONCE via the `choose` tactic on a `∀ i, ∃ nd0, ...` statement (`hchoose`/
`hchoose1`/`hchoose2a`/`hchoose2b` below), giving named functions
(`nd0`/`nd1a`/`nd2a`/`nd2b`) and their spec lemmas as plain hypotheses —
no repeated `.choose` term to re-elaborate, `hwit`/`hDbound` just apply
the already-extracted spec directly. Same underlying mathematical content,
same `IsRdecWitness.mul`/`Finset`-indexed-family shape the original note
below still describes accurately; only the extraction mechanism changed.

**Numeral bounds used, traced**: `Epoly_coeff_isRdecWitness`/`Ypoly_coeff_
isRdecWitness` both `≤704` each side (`CoeffsOutTotalDegree.lean`'s own
`cramerSolution_totalDegree_le` bound, `384+320`), so any PRODUCT of two
such witnesses is `≤1408` each side (`.mul`'s totalDegree-additive
shape); `fAtX_coeff_isRdecWitness` is `≤0` each side (a bare constant).
`Ypoly_sq_coeff_isRdecWitness`'s own bound is `(k+1)*1408` (a sum of
`k+1` such `≤1408` product terms, `Finset.Nat.card_antidiagonal`). The
final `fAtX * Ypoly^2` branch's bound is `(k+1) * ((k+1)*1408)` (another
`k+1`-term sum, each term now `≤ 0 + (k+1)*1408` by monotonicity in the
second `antidiagonal` index). **Not independently sanity-checked against
a numerical example this pass** — flagged rather than asserted exact,
though the ARITHMETIC shape (linear-times-linear in `k`, i.e. quadratic
overall) matches this file's own header note predicting exactly that
before any theorem was written.

**What this does NOT yet close** (the actual remaining work per
`ROADMAP-crossnondegenerate-degree-bound.md`'s "still fully unresolved"
note): this file bounds `Npoly.coeff k` for every `k` in terms of `k`
itself — it does NOT yet combine that with `Npoly_natDegree_le_six`
(`DecoupledSystemRegular.lean`, already proved: `Npoly.natDegree ≤ 6`) to
get a single `k`-independent numeral bound covering every NONZERO
coefficient of `Npoly` (which only needs `k ≤ 6` evaluated into this
file's own formula, e.g. `k = 6` gives `≤ 7*1408 + 7*(7*1408) = 9856 +
68992 = 78848` on both sides — arithmetic not yet double-checked, flagged
rather than asserted). That final combination, plus threading the result
through `Npoly_eq_curBeforeMonic_mul`'s exact-quotient identity to reach
`curBeforeMonic`'s own coefficientwise bound (the "genuinely new
territory" step `ROADMAP-crossnondegenerate-degree-bound.md`'s closing
section and `AnchorTotalDegree.lean`'s own status note both flag as
needing a from-scratch `totalDegree`-of-exact-quotient lemma, good
ChatGPT-consultation material per that note), is the next assembly step —
not attempted here.

**REPL-confirmed green** (whole project build) — supersedes both "not yet
REPL-confirmed"/"Drafted, not yet REPL-confirmed" notes earlier in this
file. -/

end TheDataDerivation
end Genus2Lean
