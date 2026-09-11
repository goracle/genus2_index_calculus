import Mathlib

set_option linter.style.header false

/-! # `MvPolynomial.totalDegree` is exact (not just `≤`) for products over a domain

This is the blocking generic-algebra lemma `ROADMAP-crossnondegenerate-degree-
bound.md`'s latest pass flags as the single next step for "Revised route 1"
(the `exists_reduced_factors'` fix to the reduced-witness/unit-correction
argument): *"in a domain, `c*a' = a`, `a ≠ 0` ⟹ `totalDegree c ≤ totalDegree
a`"* for `MvPolynomial`. That roadmap section confirms `MvPolynomial.
totalDegree_mul` (the `≤`-only direction) is present, but found no equality or
reverse-direction lemma under any plausible name, and sketches the fix via
`MvPolynomial.IsHomogeneous.totalDegree`/`homogeneousComponent` — this file
carries out exactly that sketch, no curve-specific content, pure `MvPolynomial`
algebra over an arbitrary domain (so it's equally usable wherever else in this
project the same gap resurfaces, not just at the one call site that motivated
it).

**No curve/finite-field-specific content — `R`/`σ` are fully generic**, matching
this project's "closed field machinery is poison, finite fields only" stance
by simply not caring: the argument only needs `[CommRing R] [IsDomain R]`,
which `F p` (or `MvPolynomial Vars (F p)` itself, wherever this gets applied
one level up) satisfies trivially.

## Main results

- `MvPolynomial.exists_support_totalDegree`: a nonzero polynomial has some
  support element whose `Finsupp.degree` equals its `totalDegree` (the
  "argmax exists" fact `totalDegree`'s `Finset.sup` definition needs to be
  usable at all — surprisingly not stated directly under any name found this
  pass, so proved here from `Finset.sup'`/`Finset.exists_mem_eq_sup'`).
- `MvPolynomial.homogeneousComponent_totalDegree_ne_zero`: the top-degree
  homogeneous component of a nonzero polynomial is itself nonzero.
- `MvPolynomial.totalDegree_mul_of_ne_zero`: **the headline fact** —
  `(p * q).totalDegree = p.totalDegree + q.totalDegree` for nonzero `p q`
  over a domain (strengthens `MvPolynomial.totalDegree_mul`'s `≤` to `=`).
- `MvPolynomial.totalDegree_le_of_mul_eq_of_ne_zero`: **the actual roadmap
  target** — `c * a' = a`, `a ≠ 0`, domain ⟹ `c.totalDegree ≤ a.totalDegree`,
  a direct corollary.

## Proof idea for the headline fact (no graded-ring machinery needed)

Let `n := p.totalDegree`, `m := q.totalDegree`, `P := homogeneousComponent n p`,
`Q := homogeneousComponent m q`. `P`, `Q` are nonzero (top component of a
nonzero polynomial is nonzero) and homogeneous of degrees `n`, `m`
respectively, so `P * Q ≠ 0` (domain) and is homogeneous of degree `n + m`
(`IsHomogeneous.mul`), hence has `totalDegree` exactly `n + m`
(`IsHomogeneous.totalDegree`) and so some `d` in its support with
`Finsupp.degree d = n + m`. The key computation is `(p * q).coeff d = (P *
Q).coeff d`: every pair `(d1, d2)` with `d1 + d2 = d` contributing to
`(p*q).coeff d` (via `MvPolynomial.coeff_mul`) has `Finsupp.degree d1 ≤ n`,
`Finsupp.degree d2 ≤ m` (`MvPolynomial.le_totalDegree`), and `Finsupp.degree
d1 + Finsupp.degree d2 = Finsupp.degree d = n + m` (`Finsupp.degree` is
additive), which forces `Finsupp.degree d1 = n` and `Finsupp.degree d2 = m`
exactly — i.e. `p.coeff d1 = P.coeff d1` and `q.coeff d2 = Q.coeff d2` for
every contributing pair, so the two coefficient-sums agree termwise. Since
`(P*Q).coeff d ≠ 0`, so is `(p*q).coeff d`, giving `d ∈ (p*q).support` and
hence `n + m ≤ (p*q).totalDegree` (`MvPolynomial.le_totalDegree`). Combined
with `MvPolynomial.totalDegree_mul`'s `≤` direction, equality follows.

## Status — REPL-confirmed green (whole project build)

Per this project's convention, Claude drafts/scopes, Claire tests. The
file's original "Status" section (guessing `Finsupp.degree` was
definitionally `fun d => d.sum fun _ e => e`) was wrong: as of current
Mathlib, `Finsupp.degree` is a bundled `AddMonoidHom` (`(σ →₀ R) →+ R`,
`Mathlib.Data.Finsupp.Weight`), NOT definitionally equal to `MvPolynomial.
totalDegree`'s own raw `Finsupp.sum`-headed `def`. This caused three build
failures (closing `rfl` in `exists_support_totalDegree`; the `Finsupp.
sum_add_index'`-based proof of `degree_add'`; downstream `omega` calls that
needed `Finsupp.degree d1`/`le_totalDegree`'s raw-`Finsupp.sum` output to be
the same atom). Fixes applied this pass:
1. `Finsupp.degree_add'` now proved by `map_add Finsupp.degree d1 d2` (free,
   since `degree` is an `AddMonoidHom`) instead of `Finsupp.sum_add_index'`.
2. `exists_support_totalDegree`'s closing step now `unfold
   MvPolynomial.totalDegree; simp only [Finsupp.degree_apply, Finsupp.sum]`
   instead of `rfl`.
3. New bridging lemma `MvPolynomial.le_totalDegree'` explicitly converts
   `le_totalDegree`'s raw-`Finsupp.sum` conclusion to a `Finsupp.degree`-
   headed one; the two `omega` call sites in `totalDegree_mul_of_ne_zero`
   now go through it instead of relying on defeq.

`Finset.exists_mem_eq_sup'`/`Finset.sup'_eq_sup` (used in
`exists_support_totalDegree`) remain not individually doc-confirmed this
pass, though the surrounding build errors were not about these names. If
either is off, `Finset.max'_mem`/`Finset.le_max'`-style alternatives, or a
direct `Finset.strongInductionOn`-style extraction, are the fallback route.

Everything downstream of `exists_support_totalDegree` (the homogeneous-
component argument itself) uses only names confirmed present this pass:
`MvPolynomial.homogeneousComponent_isHomogeneous`, `MvPolynomial.
IsHomogeneous.mul`, `MvPolynomial.IsHomogeneous.totalDegree`, `MvPolynomial.
coeff_mul`, `MvPolynomial.le_totalDegree`, `MvPolynomial.mem_support_iff`,
`MvPolynomial.totalDegree_mul`, and the `MvPolynomial σ R`-is-a-domain
instance (`R` a domain ⟹ `MvPolynomial σ R` a domain, confirmed present).
-/

open MvPolynomial

variable {σ R : Type*}

/-- `Finsupp.degree` is additive. `Finsupp.degree` is actually an
`AddMonoidHom` (`(σ →₀ R) →+ R`, see `Mathlib.Data.Finsupp.Weight`), not a
plain function as this file's docstring originally guessed — so additivity
is just `map_add`, not something needing `Finsupp.sum_add_index'` at all.
Keeping the original name/statement as a thin wrapper since the rest of the
file's proof refers to it by this name. -/
theorem Finsupp.degree_add' (d1 d2 : σ →₀ ℕ) :
    Finsupp.degree (d1 + d2) = Finsupp.degree d1 + Finsupp.degree d2 :=
  map_add Finsupp.degree d1 d2

/-- Bridging lemma: `MvPolynomial.le_totalDegree`'s conclusion is headed by
`totalDegree`'s own raw `def` (`Finset.sup (·.sum fun _ e => e)`), not by the
bundled `Finsupp.degree` `AddMonoidHom` used everywhere else in this file —
these are equal but NOT syntactically/definitionally the same term as far as
`omega` (which works up to syntactic atoms, not `simp`-normal forms) is
concerned. Stated and proved once here, by unfolding both to `Finset.sum`, so
every later call site can `rw`/`rwa` through it explicitly instead of
silently hoping the two forms line up. -/
theorem MvPolynomial.le_totalDegree' [CommSemiring R] {p : MvPolynomial σ R}
    {d : σ →₀ ℕ} (hd : d ∈ p.support) : Finsupp.degree d ≤ p.totalDegree := by
  -- Unfold ONLY `Finsupp.degree` (via `Finsupp.degree_apply`/`Finsupp.sum`)
  -- on the goal's LHS, leaving `p.totalDegree` on the RHS completely
  -- untouched — that's what lets the result land exactly on
  -- `MvPolynomial.le_totalDegree hd`'s own conclusion (which is stated with
  -- `p.totalDegree` folded, not unfolded). Unfolding `p.totalDegree` too
  -- (on either side) breaks the match, since then there's nothing left with
  -- the folded `p.totalDegree` shape to close against.
  rw [show Finsupp.degree d = ∑ i ∈ d.support, d i from Finsupp.degree_apply d]
  exact MvPolynomial.le_totalDegree hd

/-- A nonzero polynomial has some support element whose `Finsupp.degree`
equals its `totalDegree` — i.e. the `Finset.sup` defining `totalDegree` is
actually achieved on the (nonempty) support. See the file docstring's
"Status" section for the one real naming risk in this proof. -/
theorem MvPolynomial.exists_support_totalDegree [CommSemiring R]
    {p : MvPolynomial σ R} (hp : p ≠ 0) :
    ∃ d ∈ p.support, Finsupp.degree d = p.totalDegree := by
  classical
  have hsupp : p.support.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr fun h => hp (MvPolynomial.support_eq_empty.mp h)
  obtain ⟨d, hd, hdeq⟩ :=
    Finset.exists_mem_eq_sup' hsupp (fun s : σ →₀ ℕ => Finsupp.degree s)
  refine ⟨d, hd, ?_⟩
  rw [← hdeq, Finset.sup'_eq_sup hsupp]
  -- `Finsupp.degree` is (as of current Mathlib) a bundled `AddMonoidHom`
  -- (`Finsupp.degree_apply : degree d = ∑ i ∈ d.support, d i`), not
  -- definitionally the raw `Finsupp.sum`-headed term `MvPolynomial.
  -- totalDegree`'s own `def` unfolds to — so this needs both unfolded to a
  -- plain `Finset.sum` rather than closing by `rfl`. `MvPolynomial.
  -- totalDegree` is a plain (non-`@[simp]`) `def`, so `unfold` rather than
  -- `simp only` is what actually exposes it.
  unfold MvPolynomial.totalDegree
  simp only [Finsupp.degree_apply, Finsupp.sum]

/-- The top-degree homogeneous component of a nonzero polynomial is itself
nonzero: it has a nonzero coefficient at the `Finsupp.degree`-`p.totalDegree`
support witness `exists_support_totalDegree` supplies. -/
theorem MvPolynomial.homogeneousComponent_totalDegree_ne_zero [CommSemiring R]
    {p : MvPolynomial σ R} (hp : p ≠ 0) :
    MvPolynomial.homogeneousComponent p.totalDegree p ≠ 0 := by
  classical
  obtain ⟨d, hd, hdeg⟩ := MvPolynomial.exists_support_totalDegree hp
  intro hzero
  have hc : (MvPolynomial.homogeneousComponent p.totalDegree p).coeff d = 0 := by
    rw [hzero]; simp
  rw [MvPolynomial.coeff_homogeneousComponent, if_pos hdeg] at hc
  exact (MvPolynomial.mem_support_iff.mp hd) hc

/-- **Headline fact.** `MvPolynomial.totalDegree_mul` strengthened from `≤` to
`=` for two NONZERO polynomials over a domain — needs `IsDomain R` genuinely
(false in general otherwise, e.g. zero divisors can cancel top terms). -/
theorem MvPolynomial.totalDegree_mul_of_ne_zero [CommRing R] [IsDomain R]
    {p q : MvPolynomial σ R} (hp : p ≠ 0) (hq : q ≠ 0) :
    (p * q).totalDegree = p.totalDegree + q.totalDegree := by
  classical
  refine le_antisymm (MvPolynomial.totalDegree_mul p q) ?_
  set n := p.totalDegree
  set m := q.totalDegree
  set P := MvPolynomial.homogeneousComponent n p with hP_def
  set Q := MvPolynomial.homogeneousComponent m q with hQ_def
  have hPne : P ≠ 0 := MvPolynomial.homogeneousComponent_totalDegree_ne_zero hp
  have hQne : Q ≠ 0 := MvPolynomial.homogeneousComponent_totalDegree_ne_zero hq
  have hPhom : P.IsHomogeneous n := MvPolynomial.homogeneousComponent_isHomogeneous n p
  have hQhom : Q.IsHomogeneous m := MvPolynomial.homogeneousComponent_isHomogeneous m q
  have hPQne : P * Q ≠ 0 := mul_ne_zero hPne hQne
  have hPQhom : (P * Q).IsHomogeneous (n + m) := hPhom.mul hQhom
  have hPQdeg : (P * Q).totalDegree = n + m := hPQhom.totalDegree hPQne
  obtain ⟨d, hdmem, hddeg⟩ := MvPolynomial.exists_support_totalDegree hPQne
  rw [hPQdeg] at hddeg
  have hPQd_ne : (P * Q).coeff d ≠ 0 := MvPolynomial.mem_support_iff.mp hdmem
  have hcoeff_eq : (p * q).coeff d = (P * Q).coeff d := by
    simp only [MvPolynomial.coeff_mul]
    refine Finset.sum_congr rfl ?_
    rintro ⟨d1, d2⟩ hmem
    -- Sidestepping a `Finset.mem_antidiagonal` name-resolution surprise
    -- (the bare name appears to resolve to a declaration with a different,
    -- wider-arity signature than the `Finset.HasAntidiagonal` class field
    -- this file needs — possibly a distinct generic-`Multiset`/`List`-based
    -- declaration also named `Finset.mem_antidiagonal` elsewhere in
    -- Mathlib). Going through the class field `Finset.HasAntidiagonal.
    -- mem_antidiagonal` directly, fully qualified, avoids the ambiguity.
    have hd12 : d1 + d2 = d := Finset.HasAntidiagonal.mem_antidiagonal.mp hmem
    by_cases hd1n : Finsupp.degree d1 = n
    · by_cases hd2m : Finsupp.degree d2 = m
      · have hPc : P.coeff d1 = p.coeff d1 := by
          rw [hP_def, MvPolynomial.coeff_homogeneousComponent, if_pos hd1n]
        have hQc : Q.coeff d2 = q.coeff d2 := by
          rw [hQ_def, MvPolynomial.coeff_homogeneousComponent, if_pos hd2m]
        rw [hPc, hQc]
      · -- `Finsupp.degree d2 ≠ m`: then `q.coeff d2 = 0`, since `d2 ∉ support q`
        -- would follow from `Finsupp.degree d2 > m` — but we only know `≠`, so
        -- instead show `Q.coeff d2 = 0` directly and match it against `q.coeff
        -- d2` being forced to `0` too via the degree-additivity pigeonhole.
        have hsum : Finsupp.degree d1 + Finsupp.degree d2 = n + m := by
          rw [← hd12] at hddeg; rwa [Finsupp.degree_add'] at hddeg
        have : Finsupp.degree d2 = m := by omega
        exact absurd this hd2m
    · -- `Finsupp.degree d1 ≠ n` ⟹ `P.coeff d1 = 0` (`coeff_homogeneousComponent`'s
      -- `if_neg`). For the LHS `p.coeff d1 * q.coeff d2` to also vanish:
      -- if `d1 ∉ p.support`, `p.coeff d1 = 0` directly. If `d1 ∈ p.support`,
      -- `le_totalDegree'` gives `Finsupp.degree d1 ≤ n`, strict since
      -- `≠ n`; combined with the pigeonhole `hsum` this forces
      -- `Finsupp.degree d2 > m`, so `d2 ∉ q.support` (else `le_totalDegree'`
      -- on `q` would give `Finsupp.degree d2 ≤ m`, a contradiction), giving
      -- `q.coeff d2 = 0` instead.
      have hPc : P.coeff d1 = 0 := by
        rw [hP_def, MvPolynomial.coeff_homogeneousComponent, if_neg hd1n]
      have hsum : Finsupp.degree d1 + Finsupp.degree d2 = n + m := by
        rw [← hd12] at hddeg; rwa [Finsupp.degree_add'] at hddeg
      by_cases hmemp : d1 ∈ p.support
      · have hle1 : Finsupp.degree d1 ≤ n := MvPolynomial.le_totalDegree' hmemp
        have hd1lt : Finsupp.degree d1 < n := lt_of_le_of_ne hle1 hd1n
        have hmemq : d2 ∉ q.support := by
          intro hmemq
          have hle2 : Finsupp.degree d2 ≤ m := MvPolynomial.le_totalDegree' hmemq
          omega
        have hqc : q.coeff d2 = 0 := MvPolynomial.notMem_support_iff.mp hmemq
        simp [hPc, hqc]
      · have hpc : p.coeff d1 = 0 := MvPolynomial.notMem_support_iff.mp hmemp
        simp [hPc, hpc]
  have hpq_ne : (p * q).coeff d ≠ 0 := hcoeff_eq ▸ hPQd_ne
  have hmem_pq : d ∈ (p * q).support := MvPolynomial.mem_support_iff.mpr hpq_ne
  -- Same `le_totalDegree'` bridge as above, so `omega` sees `Finsupp.degree
  -- d` as the same atom as `hddeg`'s.
  have hle_pq : Finsupp.degree d ≤ (p * q).totalDegree := MvPolynomial.le_totalDegree' hmem_pq
  omega

/-- **The actual roadmap target.** In a domain, if `c * a' = a` and `a ≠ 0`,
then `c.totalDegree ≤ a.totalDegree` — the blocking lemma for the "Revised
route 1" reduced-witness plan (`ROADMAP-crossnondegenerate-degree-bound.md`,
latest pass): bounding a `exists_reduced_factors'` cofactor's `totalDegree`
by the dividend's, needed to keep the reduced-witness degree bound from
getting worse than the unreduced one it starts from. -/
theorem MvPolynomial.totalDegree_le_of_mul_eq_of_ne_zero [CommRing R] [IsDomain R]
    {c a' a : MvPolynomial σ R} (heq : c * a' = a) (ha : a ≠ 0) :
    c.totalDegree ≤ a.totalDegree := by
  have hc : c ≠ 0 := fun hc0 => ha (by rw [hc0, zero_mul] at heq; exact heq.symm)
  have ha' : a' ≠ 0 := fun ha0 => ha (by rw [ha0, mul_zero] at heq; exact heq.symm)
  rw [← heq, MvPolynomial.totalDegree_mul_of_ne_zero hc ha']
  omega
