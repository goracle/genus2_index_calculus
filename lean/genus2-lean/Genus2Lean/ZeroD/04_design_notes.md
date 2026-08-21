# Design for `regularSeq_of_peel_chain`

## Strategy

Rather than fighting `Idx`'s flat-inductive shape directly, build ONE
reusable "pull back a variable-restricted regularity fact from `Rdec p ⧸
Ideal.ofList prefix` to the abstract `Option τ` shape" lemma using:

- `MvPolynomial.exists_rename_eq_of_vars_subset_range` to pull each
  already-imposed generator AND the current stage's `c`/`d`/`g` back to
  `τ := {v : Idx // v ≠ x}` (injective inclusion `Subtype.val`).
- `isSMulRegular_of_ringEquiv_of_mapsTo` (new, generic, proved via the
  `Ideal.quotientEquiv` pattern already used twice in this file) to
  transport `IsSMulRegular` between `Rdec p ⧸ Ideal.ofList gensRdec` and
  `MvPolynomial (Option τ) (F p) ⧸ Ideal.ofList (gens'.map (rename some))`
  via `e := (renameEquiv (F p) (optionSplit x)) : Rdec p ≃+*
  MvPolynomial (Option τ) (F p)`.
- `regular_of_linear_elim` / `regular_of_disjoint_extension` /
  `isSMulRegular_of_mul_eq_of_isSMulRegular` / `regular_of_peeled_leadingCoeff`
  applied at the `Option τ` level, then transported back via the bridge.

## The 12-fold assembly itself

`genList = [Fu0,Fu1,Fu2,Fu3,Fv0,Fv1,Fv2,Fv3,curveA1,curveA2,curveB1,curveB2]`.

Process via `RingTheory.Sequence.isRegular_cons_iff'` (the PRIMED version,
whose tail is stated with `List.map (Ideal.Quotient.mk (Ideal.span {r}))`,
matching what `regular_of_linear_elim` naturally produces once transported)
12 times, i.e.

```
IsRegular (Rdec p) (Fu0 :: rest)
  ↔ IsSMulRegular (Rdec p) Fu0 ∧ IsRegular (QuotSMulTop Fu0 (Rdec p)) (rest.map (mk (span {Fu0})))
```

`QuotSMulTop Fu0 (Rdec p)` as a MODULE is `Rdec p ⧸ (Ideal.span {Fu0} • ⊤)`,
which for `M := R` (ring acting on itself) is `Rdec p ⧸ Ideal.span {Fu0}` AS
A MODULE (this needs its own tiny bridge: `IsRegular (QuotSMulTop r R) l ↔
IsRegular (R ⧸ Ideal.span {r}) l` — genuinely needs checking that the two
`Module (R ⧸ ...)`-structures agree, or more simply that `QuotSMulTop r R`
and `R ⧸ Ideal.span {r}` are literally the same TYPE with the same module
structure via `Submodule.ideal_span_singleton_smul`-style unfolding).

**IMPORTANT SIMPLIFICATION, confirmed by looking at the existing file's own
successful `regular_of_norm_eliminate`/`regular_of_norm_eliminate_one`
proofs (lines ~1093-1182):** they NEVER separately prove
`QuotSMulTop r R ≃ R ⧸ Ideal.span {r}` -- they just carry `QuotSMulTop r R`
around AS-IS throughout the whole induction, and get `IsSMulRegular
(QuotSMulTop g0 A) x`-shaped goals directly from `RingTheory.Sequence.
isRegular_cons_iff`. The ONLY point they ever need "regular in the actual
quotient RING" is when invoking a fact whose statement is phrased that
way -- and at THAT point (not before) they'd need the bridge.

So: reformulate the "regularity of stage k's generator" facts I derive
(via `regular_of_linear_elim` etc., all phrased as `Rdec p ⧸ Ideal.ofList
prefix`) to feed `isRegular_cons_iff` (UNPRIMED -- `IsSMulRegular M r`
where `M` is `QuotSMulTop (prefix so far)`, built incrementally) rather
than `isRegular_cons_iff'`. Concretely, since `Ideal.ofList [r] =
Ideal.span {r}` (`Ideal.ofList_singleton`, confirmed used in this file),
and iterating: `QuotSMulTop r₁ (QuotSMulTop r₂ (... R))`-nesting is what
`isRegular_cons_iff` (unprimed) produces at each step, INSTEAD OF working
with `Rdec p ⧸ Ideal.ofList [r1,...,rk]` directly.

This is a REAL fork in strategy: unprimed `isRegular_cons_iff` nests
`QuotSMulTop` modules increasingly deeply (`QuotSMulTop r1 (QuotSMulTop r2
(... (QuotSMulTop r11 (Rdec p))))`), which is awkward to relate to
`regular_of_linear_elim`'s clean `Rdec p ⧸ Ideal.ofList prefix` statements.
The PRIMED version avoids the nesting (`rs.map (mk (span {r}))` re-expresses
the TAIL back at the ring-quotient level after ONE step, not nested), so
each step's *generator list* stays a `List (Rdec p ⧸ Ideal.span {r})`
rather than the original ring -- meaning `regular_of_linear_elim`-style
facts, stated for the ORIGINAL ring `Rdec p` quotiented by an EXPLICIT
finite list of ORIGINAL-ring elements, don't directly match either.

**Resolution (this is the actual missing piece, genuinely needing a
fresh, but small and mechanical, bridging lemma):** what I actually need,
at stage k, is:

  `IsSMulRegular (QuotSMulTop r_k (Rdec p ⧸ Ideal.ofList prefix)) (mk r_{k+1})`

i.e. regularity of the (k+1)-th generator's IMAGE in the quotient-of-a-
quotient, stated as a `QuotSMulTop`-module fact over the ALREADY-quotiented
ring `Rdec p ⧸ Ideal.ofList prefix` -- NOT over `Rdec p` itself. This
matches neither `isRegular_cons_iff` (unprimed, nests QuotSMulTop over the
ORIGINAL ring `Rdec p`, never re-quotienting) NOR naively what
`regular_of_linear_elim` gives (regularity in `Rdec p ⧸ Ideal.ofList
prefix`, stated as a ring-level `IsSMulRegular` fact, self-action).

ACTUALLY -- checking Mathlib's `isRegular_cons_iff` once more: `M` is a
free parameter, not fixed to `R`. So `isRegular_cons_iff (Rdec p ⧸
Ideal.ofList prefix) r_{k+1} rest` is a perfectly good instance, with
`QuotSMulTop r_{k+1} (Rdec p ⧸ Ideal.ofList prefix)` on the RHS. The
substance needed is just: `IsRegular (Rdec p ⧸ Ideal.ofList prefix) L`
(for `L` the REMAINING generator list, viewed as elements of the ALREADY-
quotiented ring `Rdec p ⧸ Ideal.ofList prefix` via `Ideal.Quotient.mk`)
built up via `RingTheory.Sequence.IsRegular.cons` applied WITHIN that ring,
one generator at a time, then the WHOLE thing related back to `Rdec p`
via `isRegular_cons_iff'` used ONCE per step at the TOP level only.

**This is exactly what `regular_of_disjoint_extension`/`regular_of_linear_elim`
are already stated for**: their conclusion is `IsSMulRegular (Rdec-shape
quotiented by an explicit Ideal.ofList prefix) (the new generator's
image)` -- literally the `r` argument `isRegular_cons_iff`
(unprimed, `M := Rdec p ⧸ Ideal.ofList prefix`) wants for `IsSMulRegular M
r` component, PROVIDED `r` here means the generator's IMAGE in that
quotient (`Ideal.Quotient.mk _ r_{k+1}`), matching `regular_of_linear_elim`'s
conclusion `IsSMulRegular (MvPolynomial (Option τ) R ⧸ Ideal.ofList
(gens'.map (rename some))) g` -- `g` is stated as an ELEMENT of the
AMBIENT ring `MvPolynomial (Option τ) R` (or `Rdec p` after the bridge),
and `IsSMulRegular (ring ⧸ I) g` uses `g`'s IMAGE implicitly via the
`Module (ring ⧸ I) ring` instance -- CHECK: does `IsSMulRegular (R ⧸ I) g`
for `g : R` even typecheck? `IsSMulRegular M c` needs `c : α` and
`[SMul α M]` -- here `α := R` (NOT `R ⧸ I`) acting on `M := R ⧸ I` via the
quotient's own `Module R (R⧸I)` (through `Ideal.Quotient.mk`). YES -- this
is EXACTLY `isRegular_cons_iff`'s own shape: `r : R`, `M`, `IsSMulRegular M
r` uses `R`'s action on `M`, not `R⧸I`'s self-action. So NO extra `mk`
wrapping is needed at all -- `regular_of_linear_elim`'s literal conclusion
`IsSMulRegular (MvPolynomial (Option τ) R ⧸ Ideal.ofList gens') g` (`g`
bare, unwrapped) is ALREADY exactly the shape `isRegular_cons_iff` wants
for `r := g` acting on `M := MvPolynomial (Option τ) R ⧸ Ideal.ofList gens'`.

**This resolves the fork: use `isRegular_cons_iff` (UNPRIMED), with `M`
INSTANTIATED AT EACH STEP to `Rdec p ⧸ Ideal.ofList (prefix so far)` --
NOT nested `QuotSMulTop`s over the original ring, and NOT the primed
version's `List.map mk` reformulation either. `QuotSMulTop r_k (Rdec p ⧸
Ideal.ofList prefix)` -- the module `isRegular_cons_iff` produces for the
tail -- is quotienting the ALREADY-a-quotient ring `Rdec p ⧸ Ideal.ofList
prefix` by `Ideal.span {r_k}` (as a submodule over itself), which is
EXACTLY (as a ring) `Rdec p ⧸ Ideal.ofList (prefix ++ [r_k])` -- but I
don't even need to prove that ring-level identification explicitly if I
set up the induction so this identification IS the induction's own
invariant, carried along as a `QuotSMulTop`-nested module throughout,
exactly like `regular_of_norm_eliminate`'s induction already does.**

## Revised, concrete plan

Prove a HELPER lemma doing the "one step" work generically:

```
stepLemma (prefix : List (Rdec p)) (r : Rdec p)
  (hprefix_reg : IsRegular (Rdec p) prefix)  -- or: build incrementally
  (hr_reg : IsSMulRegular (Rdec p ⧸ Ideal.ofList prefix) r) :
  IsRegular (Rdec p) (prefix ++ [r])
```
via `isRegular_append_iff'`/`cons`-chaining -- OR, simpler, just chain
`IsRegular.cons` TWELVE TIMES EXPLICITLY (no generic helper, no induction,
since the list is a FIXED literal length 12, not a variadic parameter) --
matching this file's own established style elsewhere (`regular_of_norm_eliminate_one`,
the very first proved regular-sequence-flavored theorem in the file, chains
`IsRegular.cons` a FIXED small number of times without a generic recursion
helper). Given `genList` is a literal 12-element list built by `++`, the
cleanest route is 12 nested applications of (unprimed) `isRegular_cons_iff`
/`IsRegular.cons`, computing `QuotSMulTop` module memberships as
`Rdec p ⧸ Ideal.ofList (prefix)` at each step via a SINGLE small
"QuotSMulTop-as-quotient-ring" identification lemma (below), applied 11
times (once per step after the first) -- OR avoiding that identification
entirely by keeping every stage's regularity FACT already stated directly
against the correct nested `QuotSMulTop`, which is what
`regular_of_linear_elim`/etc. do NOT do (they use `Ideal.ofList`, not
`QuotSMulTop`).

**Given the genuine complexity here, the pragmatic move (matching project
convention: ship a real, checkable partial proof with NAMED sub-sorries
rather than one opaque sorry) is:**

1. State and prove `quotSMulTop_eq_quotient_span` (or similar): for a
   commutative ring `R` and `r : R`, `QuotSMulTop r R` and `R ⧸ Ideal.span
   {r}` carry the SAME module structure -- likely literally `rfl`/`Iff.rfl`
   after unfolding `Ideal.span {r} • (⊤ : Submodule R R) = Ideal.span {r}`
   (as submodules) via `Submodule.ideal_span_singleton_smul`. THIS is the
   one genuinely fiddly new "plumbing" lemma (flagged as its own named
   `sorry` below, easiest of the new sorries, pure API chasing).
2. Iterate: define `prefixIdeal (k : Fin 13) : Ideal (Rdec p) :=
   Ideal.ofList ((genList ...).take k)`, and prove, by 12 EXPLICIT
   (non-recursive) applications, `IsSMulRegular (Rdec p ⧸ prefixIdeal k)
   (genList.get k)` for each `k`, using the appropriate one of: 8×
   `regular_of_linear_elim` (transported via the bridge), 4×
   `isSMulRegular_of_mul_eq_of_isSMulRegular` + `hcross` (transported), 4×
   `regular_of_peeled_leadingCoeff` + `curveCoeffRegular` (transported,
   needs the "shape ⟺ literal definition" bridge flagged as NOT YET
   ESTABLISHED in `curveCoeffRegular`'s own docstring -- a SECOND named
   sub-sorry, flagged below).
3. Chain via `isRegular_cons_iff`/`.cons` + step 1's identification.
4. `Nontrivial` at the end: since `Rdec p` is a domain (MvPolynomial over
   a field) and each stage's `IsSMulRegular` implies the quotient at that
   stage is nontrivial IF the sequence overall isn't degenerate -- actually
   `RingTheory.Sequence.IsRegular.nontrivial` (used already in this file,
   `htail_reg.nontrivial`) gives Nontrivial FROM an already-established
   IsRegular fact of the TAIL, so this is free once the chain is built,
   NO separate side-argument needed (matches how `regular_of_norm_eliminate_one`
   closes its own `Nontrivial (QuotSMulTop n R)` goal -- via
   `Submodule.Quotient.nontrivial_iff` + `hn_not_unit`, i.e. it DOES need
   an explicit non-unit argument at the very last step, not automatic).
   For the 12-step chain, `IsRegular.nil` at the very end needs
   `Nontrivial (final QuotSMulTop nest)` -- get this from `curveB2`'s OWN
   `IsSMulRegular` fact applied to `1 ≠ 0`-style reasoning (`IsSMulRegular
   M r` alone doesn't give `Nontrivial M`; need `r` not obviously
   annihilating everything -- but `Rdec p` a domain and `curveB2 ≠ 0`
   should suffice via `Ideal.Quotient.nontrivial`-style: quotient by a
   PROPER ideal of a domain by an element that's not a unit is nontrivial
   IF the ideal itself is proper, i.e. `1 ∉ Ideal.ofList genList`). THIS
   is a THIRD new sub-obligation, likely needing its own small argument
   or possibly free from `IsSMulRegular`'s own definition (`IsSMulRegular
   M r` is European in a TRIVIAL module -- vacuously true! So getting
   `Nontrivial` from regularity ALONE is not possible in general; must
   check the actual full ideal is proper).
