import Mathlib
import Genus2Lean.AverageComplexity
import Genus2Lean.SidonEnergy
import Genus2Lean.MatchCountAutocorr
set_option linter.style.header false

/-!
# Genus-2 index calculus: `matchCount` *is* the sumset energy `E(S,S)` (advisory-7 §7.6)

Advisory-7 §7.6 ("A note on a tempting but incorrect shortcut") warns that
`E(S,S)` — the additive energy of `S := T + T`, counted *with the
multiplicity that the sumset construction gives it* — is easy to conflate
with `E(T,T) = Σ_g repCount T g ²`, a different, already-bounded quantity
(`sidon_energy_bound_nat`, `SidonEnergy.lean`). The advisory states in words
that `E(S,S)`'s pointwise representation function is instead the
*autocorrelation* of the pairwise-sum histogram `repCount T`:

    r_{S-S}(Δ) = Σ_g repCount T g · repCount T (g - Δ)             (advisory §7.6)

A precision worth flagging explicitly (the naive version of this file first
tripped on it): `S = T + T` here means the sumset counted *with
multiplicity* — i.e. `r_{S-S}` is built from `T × T` pairs directly, not
from `sumsetFin T` as a plain `Finset` (which would silently collapse
multiplicity and give a strictly smaller, different count). Advisory-7 §3's
own `E(S,S) = #{(s1,s2,s3,s4) ∈ S⁴ : s1-s2=s3-s4}` already means this: `S`
there is a formal multiset of `B²` sums (one per ordered pair `(P1,P2)`), not
its underlying set. This file's `diffCountS` is defined accordingly, as a
count over `T ×ˢ T ×ˢ T ×ˢ T` directly (same domain `matchCount` uses),
which makes the identity with `matchCount` immediate rather than requiring
a separate multiplicity-tracking argument.

Punchline (`energy_S_eq_matchCount_sq_sum`): `E(S,S)` (advisory-7 §3 eq (1))
is *literally* `Σ_Δ (matchCount T Δ)²` — i.e. `PaleyZygmund.lean`'s
`SecondMomentBound` hypothesis, applied to `T`, already *is* a bound on
`E(S,S)`, not merely analogous to one.

Nothing here narrows the open gap — `E(S,S)` remains unbounded in general,
exactly as advisory §7.4-7.6 leaves it. This file only nails down *what*
the open quantity is, in terms already in scope (`matchCount`).
-/

open Finset

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- `r_{S-S}(Δ)`, counted with the sumset's natural multiplicity: the number
of ordered quadruples `(a,b,c,d) ∈ T⁴` with `(a+b) - (c+d) = Δ`, i.e. two
"virtual" sumset elements `s1 := a+b`, `s2 := c+d` (each ranging over all
`B²` ordered-pair representations, not deduplicated) with `s1 - s2 = Δ`.

This is DEFINITIONALLY THE SAME expression as `matchCount T Δ`
(`a+b-c-d=Δ` vs. `(a+b)-(c+d)=Δ` differ only by `abel`), by design — see the
file docstring for why `diffCountS` must be built this way (over `T⁴`
directly) rather than via `sumsetFin T` as a plain `Finset`, to correctly
track multiplicity the way advisory-7 §3's `E(S,S)` does. -/
noncomputable def diffCountS (T : Finset G) (Δ : G) : ℕ :=
  ((T ×ˢ T ×ˢ T ×ˢ T).filter
    (fun p : G × G × G × G => (p.1 + p.2.1) - (p.2.2.1 + p.2.2.2) = Δ)).card

/-- **Exact identity**: `diffCountS T Δ = matchCount T Δ`. Immediate: both
sides filter the same `Finset (T ×ˢ T ×ˢ T ×ˢ T)` by predicates that agree
pointwise (`a+b-c-d = Δ` and `(a+b)-(c+d) = Δ` are equal by `abel`), so the
filtered `Finset`s — hence their cards — are equal. -/
theorem diffCountS_eq_matchCount (T : Finset G) (Δ : G) :
    diffCountS T Δ = matchCount T Δ := by
  unfold diffCountS matchCount
  congr 1
  apply Finset.filter_congr
  rintro ⟨a, b, c, d⟩ _
  constructor
  · intro h; rw [← h]; abel
  · intro h; rw [← h]; abel

/-- **Corollary**: `E(S,S)` (advisory-7 §3 eq (1), `Σ_Δ diffCountS T Δ ²`,
with `S`'s multiplicity tracked correctly per the file docstring) equals
`Σ_Δ (matchCount T Δ)²` — exactly `PaleyZygmund.lean`'s `SecondMomentBound T`
quantity. So `SecondMomentBound T M` is not merely analogous to "a bound on
`E(S,S)`": it IS that bound, in already-available notation. Immediate from
`diffCountS_eq_matchCount`. -/
theorem energy_S_eq_matchCount_sq_sum (T : Finset G) :
    ∑ Δ : G, (diffCountS T Δ : ℝ) ^ 2 = ∑ Δ : G, (matchCount T Δ : ℝ) ^ 2 :=
  Finset.sum_congr rfl (fun Δ _ => by rw [diffCountS_eq_matchCount])

/-- **Corollary, via the already-proven autocorrelation formula**: combining
`diffCountS_eq_matchCount` with `MatchCountAutocorr.lean`'s
`matchCount_eq_autocorr` gives advisory-7 §7.6's identity in exactly the
form stated there — `r_{S-S}(Δ) = Σ_g repCount T g · repCount T (g - Δ)` —
with `diffCountS` playing the role of `r_{S-S}`. This is the precise
statement the advisory gives only in prose. -/
theorem diffCountS_eq_autocorr (T : Finset G) (Δ : G) :
    diffCountS T Δ = ∑ g : G, repCount T g * repCount T (g - Δ) := by
  rw [diffCountS_eq_matchCount, matchCount_eq_autocorr]
