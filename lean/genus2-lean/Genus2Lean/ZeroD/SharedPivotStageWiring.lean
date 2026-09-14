import Mathlib
import Genus2Lean.ZeroD.QuotOfListChainFinrankStep
import Genus2Lean.ZeroD.QuotOfListChainAdjoinTop
import Genus2Lean.ZeroD.SharedPivotResultantElim
import Genus2Lean.ZeroD.LinearElimStageWiring
import Genus2Lean.ZeroD.FinrankLeOfSpanSurjective

/-!
# Shared-pivot stage wiring: two matching generators, one shared target
# variable, against a literal `Ideal.ofList` prefix

`ROADMAP-monic-annihilator-degree-uniform.md`'s final proposed direction
(the "CORRECTION, later pass" / "simultaneous finiteness" entry, its most
recent, not-yet-superseded update): the naive `Fin`-indexed one-variable-
per-call peel architecture (`FinSuccPeelChainFold.lean` etc.) cannot
accommodate a stage that needs to introduce two variables jointly or that
never becomes finite at an intermediate one-relation checkpoint — exactly
what happens at `U0` (shared pivot of `Fu0`/`Fu1`), `U1` (`Fu2`/`Fu3`),
`V0` (`Fv0`/`Fv1`), `V1` (`Fv2`/`Fv3`). The roadmap's own proposed fix is
to eliminate each such pivot via `SharedPivotResultantElim.lean`'s
`finrank_le_of_shared_linear_elim_pair` — which bounds `finrank` of the
ring where BOTH matching generators already hold by `finrank` of a
RESULTANT quotient that never mentions the pivot variable at all, sidestepping
the "no valid intermediate finiteness fact" obstruction that roadmap
section found for every one-relation-at-a-time ordering.

**What this file does**: wires that abstract bound to the literal
`Ideal.ofList` two-generator extension `gens ++ [g1, g2]` (the shape
`FuList`/`FvList`'s pairs actually take in `genList`, two consecutive
list entries sharing one pivot), by composing `finrank_le_ofList_cons`
(`QuotOfListChainFinrankStep.lean`) with itself once, matching
`LinearElimStageWiring.lean`'s already-established single-generator
wiring pattern but for the two-generator resultant-elimination shape
instead. Generic over the prefix `gens : List (Rdec p)`, the peeled
symbol `u : Idx`, and the four coefficients `n1 d1 n2 d2 : Rdec p` — NOT
yet specialized to which of `U0/U1/V0/V1` this is, or to `theData`'s
actual `u1_num`/`u1_den`/`u2_num`/`u2_den` values. That final
substitution (four applications of this file's theorem, one per shared
pivot, plus discharging `hd1 : IsUnit (mk_A d1)` against `theData`'s real
formulas — a genuinely new hypothesis this stage needs, not implied by
the existing `hFu*_reg`/`hv*_ext` regularity fields, per this roadmap's
own resolved Open Questions diagnosis for the analogous single-generator
case) is later Assembly work, same split this project's other stage-
wiring files already follow.

**Two-hop composition, not a bespoke two-element-ideal quotient**: rather
than building `A ⧸ Ideal.span {mk g1, mk g2}` as its own object and
proving it isomorphic to the `Ideal.ofList` two-step chain from scratch,
this file reuses `finrank_le_ofList_cons` TWICE — once to reach
`Ideal.ofList (gens ++ [g1])`, once more to reach
`Ideal.ofList ((gens ++ [g1]) ++ [g2]) = Ideal.ofList (gens ++ [g1, g2])`
(`List.append_assoc`) — chained via `Module.finrank_mul_finrank`. The
FIRST hop's bound is the weak one-relation bound
(`finrank_le_linearElim_ofList_cons`, already proved,
`LinearElimStageWiring.lean`) since only `g1`'s own relation is imposed
after one hop; the RESULTANT bound only becomes available once `g2`'s
relation is ALSO imposed — i.e. `finrank_le_of_shared_linear_elim_pair`
is naturally a fact about the two-step ring
`(A ⧸ Ideal.span {mk_A g1}) ⧸ Ideal.span {mk (mk_A g2)}` (matching its
own `B`), not the one-step ring, so it is applied at the SECOND hop,
with the first hop's target playing the role of that theorem's own `A`.
This means the first hop's `finrank` bound (`≤ finrank A`, no
improvement yet) is NOT literally what ends up composed — the actual
composition goes through the second hop's abstract statement directly,
using `QuotOfListChainAdjoinTop.lean`'s free `hgen` fact at the
TWO-STEP ring exactly as `LinearElimStageWiring.lean` already does at
the one-step ring, generalized one level. -/

namespace Genus2Lean
namespace DecoupledSystem

variable (p : ℕ) [Fact (Nat.Prime p)]

/-- **The shared-pivot resultant bound, wired to a literal two-generator
`Ideal.ofList` extension.** Given a prefix `gens`, base field `k := F p`,
a peeled variable symbol `u : Idx`, four already-fixed coefficients
`n1 d1 n2 d2 : Rdec p` with `d1`'s image in `A := Rdec p ⧸ Ideal.ofList
gens` a UNIT, and the two matching-generator relations
`g1 := linearElimGen n1 d1 u`, `g2 := linearElimGen n2 d2 u` sharing the
SAME pivot `u` — the doubly-extended quotient's `finrank` is bounded by
the RESULTANT quotient's `finrank`, never mentioning `u` at all.

**Why `[StrongRankCondition ...]`/`[Module.Finite (F p) ...]`/
`[Nontrivial ...]` on `A` are hypotheses here, not free instances**:
identical reasoning to every other stage-wiring file in this project —
genuinely undischargeable for an arbitrary prefix `gens`, left for the
not-yet-written final Assembly file. `hd1 : IsUnit (mk_A d1)` is the
roadmap's own correctly-scoped per-pivot hypothesis (matching
`finrank_le_linearElim_ofList_cons`'s `hd_unit`, but supplied only for
ONE of the two generators — `SharedPivotResultantElim.lean`'s own
theorem needs `IsUnit d1` specifically, not `IsUnit d2`, since it solves
`g1`'s relation for `t` first).

**`[Nontrivial (A ⧸ span {mk_A g1})]` added this pass**: a SECOND
`Nontrivial` hypothesis, on the intermediate ring `A1 := A ⧸ Ideal.span
{mk_A g1}` (spelled out in the signature without `A1`'s local
abbreviation, since `A1` only exists as a `set`-introduced name inside
the proof). `finrank_le_of_shared_linear_elim_pair` is applied at `A1`
in this file's proof (not at `A`), and its own `[Nontrivial A]` section
variable becomes `[Nontrivial A1]` at that instantiation — genuinely not
free from `[Nontrivial A]` alone (an arbitrary further quotient of a
nontrivial ring can still be trivial, e.g. if `g1`'s image happens to be
a unit already), so it needs its own explicit hypothesis, same
undischargeable-for-arbitrary-`gens` status as the others, left to
Assembly. -/
theorem finrank_le_sharedPivotResultantElim_ofList_cons2
    (gens : List (Rdec p)) (u : Idx) (n1 d1 n2 d2 : Rdec p)
    [StrongRankCondition (Rdec p ⧸ Ideal.ofList gens)]
    [Module.Finite (F p) (Rdec p ⧸ Ideal.ofList gens)]
    [Nontrivial (Rdec p ⧸ Ideal.ofList gens)]
    [Nontrivial ((Rdec p ⧸ Ideal.ofList gens) ⧸
      Ideal.span ({Ideal.Quotient.mk (Ideal.ofList gens) (linearElimGen p n1 d1 u)} :
        Set (Rdec p ⧸ Ideal.ofList gens)))]
    (hd1 : IsUnit (Ideal.Quotient.mk (Ideal.ofList gens) d1)) :
    Module.finrank (F p)
        (Rdec p ⧸ Ideal.ofList
          (gens ++ [linearElimGen p n1 d1 u, linearElimGen p n2 d2 u])) ≤
      Module.finrank (F p)
        ((Rdec p ⧸ Ideal.ofList gens) ⧸
          Ideal.span ({Ideal.Quotient.mk (Ideal.ofList gens) n2 *
              Ideal.Quotient.mk (Ideal.ofList gens) d1 -
            Ideal.Quotient.mk (Ideal.ofList gens) n1 *
              Ideal.Quotient.mk (Ideal.ofList gens) d2} :
            Set (Rdec p ⧸ Ideal.ofList gens))) := by
  -- `gens ++ [g1, g2] = (gens ++ [g1]) ++ [g2]` — the two-hop shape
  -- `finrank_le_ofList_cons` (applied twice) needs.
  rw [show gens ++ [linearElimGen p n1 d1 u, linearElimGen p n2 d2 u] =
      (gens ++ [linearElimGen p n1 d1 u]) ++ [linearElimGen p n2 d2 u] by
    rw [List.append_assoc]; rfl]
  set A := Rdec p ⧸ Ideal.ofList gens with hA_def
  set g1 := linearElimGen p n1 d1 u with hg1_def
  set n1A : A := Ideal.Quotient.mk (Ideal.ofList gens) n1 with hn1A_def
  set d1A : A := Ideal.Quotient.mk (Ideal.ofList gens) d1 with hd1A_def
  set n2A : A := Ideal.Quotient.mk (Ideal.ofList gens) n2 with hn2A_def
  set d2A : A := Ideal.Quotient.mk (Ideal.ofList gens) d2 with hd2A_def
  set A1 := A ⧸ Ideal.span ({Ideal.Quotient.mk (Ideal.ofList gens) g1} : Set A) with hA1_def
  -- `g2`'s image in `A1`, via the composite quotient map — matches
  -- `LinearElimStageWiring.lean`'s `φ`, one level up.
  set φ1 : Rdec p →+* A1 :=
    (Ideal.Quotient.mk (Ideal.span ({Ideal.Quotient.mk (Ideal.ofList gens) g1} : Set A))).comp
      (Ideal.Quotient.mk (Ideal.ofList gens)) with hφ1_def
  set g2 := linearElimGen p n2 d2 u with hg2_def
  -- The abstract `B := A1 ⧸ Ideal.span {φ1 g2}` — the object
  -- `SharedPivotResultantElim.lean`'s theorem is actually about, once we
  -- transport `finrank_le_ofList_cons`'s goal shape onto it.
  set B := A1 ⧸ Ideal.span ({φ1 g2} : Set A1) with hB_def
  -- `t := X u`'s image at the deepest level, threefold-quotiented.
  set t : B := Ideal.Quotient.mk _ (φ1 (MvPolynomial.X u)) with ht_def
  -- `d1A`'s image is a unit in `A1` too — `algebraMap A A1` preserves
  -- units, and `d1A`'s unit-ness was already assumed in `A`.
  have hd1A1 : IsUnit (algebraMap A A1 d1A) := hd1.map (algebraMap A A1)
  -- `ht1 : aeval (algebraMap A1 B (φ1' u-stuff)) ... = 0` — the first
  -- relation `g1`'s image already vanishes in `A1` by construction
  -- (`A1` quotients by `Ideal.span {mk_A g1}`), hence its image in `B`
  -- (via `algebraMap A1 B`) vanishes too. Matches
  -- `LinearElimStageWiring.lean`'s `ht`/`hφg'` pattern, transported one
  -- level up from `A`/`A1` to `A1`/`B`.
  have ht1 : (Polynomial.aeval t) (linearElimPoly (algebraMap A A1 n1A) (algebraMap A A1 d1A))
      = 0 := by
    have hφ1g1 : algebraMap A A1 (Ideal.Quotient.mk (Ideal.ofList gens) g1) = 0 := by
      show Ideal.Quotient.mk (Ideal.span ({Ideal.Quotient.mk (Ideal.ofList gens) g1} : Set A))
          (Ideal.Quotient.mk (Ideal.ofList gens) g1) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
    -- `algebraMap A A1 (mk g1)` decomposed via `g1 = n1 - X u * d1`,
    -- matching `n1A`/`d1A`/`φ1 (X u)`'s own definitions (`φ1` restricted
    -- to `A`'s image of `X u`, i.e. `algebraMap A A1 (mk (X u)) = φ1 (X
    -- u)` since `φ1 := mk_A1 ∘ mk_gens` and `algebraMap A A1 = mk_A1`
    -- post-composed with the SAME `mk_gens`-quotient structure `A`
    -- already carries).
    -- NOTE: cannot `rw [hg1_def, ...]` (or `rw [← hφ1g1, hg1_def, ...]`)
    -- anywhere `A1` is in scope — `A1` is ITSELF defined (via the
    -- ambient `set A1 := ...`) using `Ideal.span {mk g1}`, so Lean sees
    -- `g1` as potentially occurring inside `A1`'s own (unfolded) type,
    -- and any `rw` targeting `g1` produces an ill-typed motive ("motive
    -- is not type correct") regardless of whether the rewrite site is
    -- the goal or a hypothesis. Do the `g1 = n1 - X u * d1` unfolding
    -- FIRST, purely at the level of `A` (an equation with NO `A1` or
    -- `algebraMap A A1` in sight, so no such dependency exists there),
    -- THEN apply `algebraMap A A1` to the already-unfolded equation via
    -- `congrArg`, never `rw`ing `g1` itself once `A1` is around.
    have hmkg1 : (Ideal.Quotient.mk (Ideal.ofList gens) g1 : A) =
        n1A - Ideal.Quotient.mk (Ideal.ofList gens) (MvPolynomial.X u) * d1A := by
      rw [hg1_def, linearElimGen, hn1A_def, hd1A_def, map_sub, map_mul]
    have hgoal : algebraMap A A1 n1A - algebraMap A A1 (Ideal.Quotient.mk (Ideal.ofList gens)
        (MvPolynomial.X u)) * algebraMap A A1 d1A = 0 := by
      have := congrArg (algebraMap A A1) hmkg1
      rw [map_sub, map_mul] at this
      rw [← this, hφ1g1]
    -- `algebraMap A A1 (mk (X u)) = φ1 (X u)`: both unfold to the same
    -- composite quotient map applied to `X u : Rdec p`.
    have hφ1X : algebraMap A A1 (Ideal.Quotient.mk (Ideal.ofList gens) (MvPolynomial.X u)) =
        φ1 (MvPolynomial.X u) := rfl
    rw [hφ1X] at hgoal
    -- Unfold the goal via `linearElimPoly`/`aeval` to the same shape
    -- `algebraMap A1 B (algebraMap A A1 n1A) - t * algebraMap A1 B
    -- (algebraMap A A1 d1A) = 0`, then apply `algebraMap A1 B` to
    -- `hgoal` (which is an equation in `A1`) and match `t` against
    -- `algebraMap A1 B (φ1 (X u))`.
    rw [linearElimPoly, map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X,
      Polynomial.aeval_C]
    have ht_eq : t = algebraMap A1 B (φ1 (MvPolynomial.X u)) := rfl
    rw [ht_eq, ← map_mul, ← map_sub, hgoal, map_zero]
  -- `ht2` : `g2`'s own relation holds in `B` by construction (`B`
  -- quotients `A1` by `Ideal.span {φ1 g2}`) — same free-by-construction
  -- pattern as `ht1`, one relation instead of a difference.
  have ht2 : (Polynomial.aeval t) (linearElimPoly (algebraMap A A1 n2A) (algebraMap A A1 d2A))
      = 0 := by
    -- Same restructuring as `ht1`, and same reason: `g2` occurs inside
    -- `B`'s own definition (`B := A1 ⧸ Ideal.span {φ1 g2}`, via the
    -- ambient `set B := ...`), so `rw [hg2_def, ...]` anywhere `B` is in
    -- scope risks the same "motive is not type correct" failure `ht1`
    -- hit. Unfold `g2 = n2 - X u * d2` FIRST at the level of `A` alone
    -- (an equation with no `A1`/`B`/`φ1` in sight), THEN push it forward
    -- via `congrArg (Ideal.Quotient.mk (Ideal.span {mk gens g1}))` /
    -- `φ1`, never `rw`ing `g2` once `B` is around.
    have hmkg2 : (Ideal.Quotient.mk (Ideal.ofList gens) g2 : A) =
        n2A - Ideal.Quotient.mk (Ideal.ofList gens) (MvPolynomial.X u) * d2A := by
      rw [hg2_def, linearElimGen, hn2A_def, hd2A_def, map_sub, map_mul]
    have hφ1g2 : algebraMap A A1 n2A - algebraMap A A1 (Ideal.Quotient.mk (Ideal.ofList gens)
        (MvPolynomial.X u)) * algebraMap A A1 d2A = φ1 g2 := by
      have := congrArg (algebraMap A A1) hmkg2
      rw [map_sub, map_mul] at this
      rw [← this]
      rfl
    have hφ1X : algebraMap A A1 (Ideal.Quotient.mk (Ideal.ofList gens) (MvPolynomial.X u)) =
        φ1 (MvPolynomial.X u) := rfl
    rw [hφ1X] at hφ1g2
    rw [linearElimPoly, map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X,
      Polynomial.aeval_C]
    have ht_eq : t = algebraMap A1 B (φ1 (MvPolynomial.X u)) := rfl
    rw [ht_eq, ← map_mul, ← map_sub, hφ1g2]
    show Ideal.Quotient.mk (Ideal.span ({φ1 g2} : Set A1)) (φ1 g2) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  have hgen : Algebra.adjoin A1 ({t} : Set B) = (⊤ : Subalgebra A1 B) :=
    adjoin_singleton_eq_top_of_quotient _ t
  have hbound := finrank_le_of_shared_linear_elim_pair (k := F p)
    (algebraMap A A1 n1A) (algebraMap A A1 d1A) (algebraMap A A1 n2A) (algebraMap A A1 d2A)
    hd1A1 t ht1 ht2 hgen
  -- `hbound : finrank B ≤ finrank (A1 ⧸ span {algebraMap A A1 resultant})`.
  -- Transport the RHS back down to `A ⧸ span {resultant}` via
  -- `finrank_le_of_span_surjective`, applied to the surjective algebra
  -- map `algebraMap A A1 : A →ₐ[F p] A1` (surjective since `A1` is a
  -- further quotient of `A`) at `r := resultant`.
  have hsurj : Function.Surjective (algebraMap A A1) := Ideal.Quotient.mk_surjective
  -- `finrank_le_of_span_surjective` wants `f : A →ₐ[F p] A1` explicitly.
  -- `Algebra.ofId A A1` was the WRONG tool — it always builds the
  -- identity-extension map `A →ₐ[A] A1` (algebra over `A` itself), never
  -- an `F p`-algebra map, hence the reported type mismatch. The right
  -- map is `Ideal.Quotient.mkₐ (F p) (Ideal.span {mk_A g1}) : A →ₐ[F p]
  -- (A ⧸ Ideal.span {mk_A g1})` — literally `A1` by `A1`'s own `set`
  -- definition — the standard algebra-quotient map, already used
  -- elsewhere in this project (`FinrankLeOfSpanSurjective.lean`,
  -- `PeelChainAssembly.lean`) for exactly this "quotient map as an
  -- `AlgHom`" need.
  set f1 : A →ₐ[F p] A1 :=
    Ideal.Quotient.mkₐ (F p) (Ideal.span ({Ideal.Quotient.mk (Ideal.ofList gens) g1} : Set A))
    with hf1_def
  have hsurj' : Function.Surjective f1 := hsurj
  have htransport := finrank_le_of_span_surjective (k := F p) f1 hsurj' (n2A * d1A - n1A * d2A)
  -- `htransport : finrank (A1 ⧸ span {f1 (n2A*d1A-n1A*d2A)}) ≤
  --   finrank (A ⧸ span {n2A*d1A-n1A*d2A})`. `hbound`'s own RHS is
  -- `finrank (A1 ⧸ span {algebraMap A A1 n2A * algebraMap A A1 d1A -
  -- algebraMap A A1 n1A * algebraMap A A1 d2A})` — the SAME element,
  -- since `f1`'s underlying function IS `algebraMap A A1` (`Ideal.
  -- Quotient.mkₐ`'s own definition) and `map_sub`/`map_mul` expand the
  -- difference-of-products — but not syntactically identical to
  -- `hbound`'s RHS without spelling that out, so rewrite `htransport`'s
  -- LHS ideal generator into `hbound`'s literal shape before chaining
  -- them with `le_trans`.
  have hgenEq : f1 (n2A * d1A - n1A * d2A) =
      algebraMap A A1 n2A * algebraMap A A1 d1A - algebraMap A A1 n1A * algebraMap A A1 d2A := by
    show algebraMap A A1 (n2A * d1A - n1A * d2A) = _
    rw [map_sub, map_mul, map_mul]
  rw [hgenEq] at htransport
  -- `htransport : finrank (A1 ⧸ span {algebraMap A A1 (n2A*d1A-n1A*d2A)}) ≤
  --   finrank (A ⧸ span {n2A*d1A-n1A*d2A})`, which is literally this
  -- theorem's stated RHS (`n2A`, `d1A`, `n1A`, `d2A` unfold to the
  -- `Ideal.Quotient.mk (Ideal.ofList gens) ...` terms in the goal, by the
  -- `set ... with h..._def` lines above).
  have hB_le_A : Module.finrank (F p) B ≤
      Module.finrank (F p) (A ⧸ Ideal.span ({n2A * d1A - n1A * d2A} : Set A)) :=
    le_trans hbound htransport
  -- Remaining gap: `B` (the abstract `A1 ⧸ span {φ1 g2}` ring `hB_le_A`
  -- is stated about) needs identifying, `finrank`-wise, with the goal's
  -- actual LHS `Rdec p ⧸ Ideal.ofList ((gens ++ [g1]) ++ [g2])` — i.e.
  -- `finrank (F p) B = finrank (F p) (Rdec p ⧸ Ideal.ofList ((gens ++
  -- [g1]) ++ [g2]))`, THEN `rw` that equality into the goal and close
  -- with `hB_le_A`. This is genuinely just `quotOfListCons_ringEquiv`
  -- applied at `gens := gens ++ [g1]`, `g := g2` (`B`'s literal
  -- definition, `A1 ⧸ span {φ1 g2}`, is already exactly that lemma's
  -- domain PROVIDED `A1` and `φ1` are first identified with
  -- `Rdec p ⧸ Ideal.ofList (gens ++ [g1])` and its own `mk`, via
  -- `quotOfListCons_ringEquiv gens g1` one level down — a nested
  -- application of the same lemma this file already imports
  -- (`QuotOfListChainFinrankStep.lean`/`QuotOfListChain.lean`) — not new
  -- mathematical content, but enough live API surface (`Ideal.
  -- quotientEquiv`'s exact argument order, whether `Ideal.map_span`
  -- needs `Set.image_singleton` alongside it, `AlgEquiv.ofRingEquiv`'s
  -- `algebraMap`-agreement obligation unfolding through TWO nested
  -- quotients rather than one) that it is worth a fresh ChatGPT consult
  -- rather than more guessing here, per this project's working
  -- agreement (hard sorries get a prompt, not a struggle-in-place).
  sorry

end DecoupledSystem
end Genus2Lean
