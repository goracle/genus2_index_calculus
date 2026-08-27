Thank you — that was extremely useful, and we confirmed your §4 diagnostic (the 6-vs-8 degree mismatch) was right, though the actual cause was different from what you guessed. Two corrections/constraints before we use your §5 proof sketch, since we think they change how it needs to be stated:

## Correction 1: our `A+C+T` claim was incomplete, not wrong — and we found the missing pieces

We went back and checked: our Lean theorem proving `div_aff(g) restricted to {6 named points} = A+C+T` never actually claimed this was g's COMPLETE affine divisor — that completeness claim only existed in our own prose summary of the theorem, not in the theorem itself. So there was no contradiction in the math, just an incomplete statement.

We then found the missing 2 zeros directly, using facts already proved in our codebase: `ḡ(x,y) := E(x)-Y(x)y` satisfies `ḡ(x,y) = g(x,-y) = g(ι(x,y))` where `ι` is the hyperelliptic involution (this is immediate from the definitions). We already have a proved fact that `ḡ(ρ_i) = 0` at each of `u_new`'s (the residual quadratic's) two roots `ρ1, ρ2` (with a specific y-lift). Therefore `g(ι ρ_i) = ḡ(ρ_i) = 0`, so:

  div(g) = A + C + T + [ι ρ1] + [ι ρ2]     (complete, degree 8, matches ord_∞(g) = -8) ✓.

This resolves your §4 diagnostic without needing multiple points at infinity or any change to the curve model — our curve has odd-degree f (degree 5), hence a single ramified point at infinity, and our `ordInfOfPair` formula already accounts for that ramification (it has the shape `-max(2 deg A, 2 deg B + 5)`, the `+5` pricing in the ramification). So please don't reach for a "distribute the pole across several points at infinity" framing — that doesn't apply to our model.

## Correction 2 (important, changes how §5 needs to be restated): our formalized `H.Point` type has NO point at infinity at all

This is a hard constraint on our Lean model, not a choice we can revisit for this theorem: our `Divisor H` type is `H.Point →₀ ℤ` where `H.Point := {p : k×k // (curve equation) p.1 p.2}` — a subtype of AFFINE pairs only. There is no value of type `H.Point` representing "the point at infinity." Our own module docstring says this explicitly: "points at infinity are excluded [from Divisor H]." Consequently:

- `δ₀` in our target identity `C - A - T + 2•[δ₀] ∈ PrincSub` is necessarily an AFFINE point (any affine point the caller supplies) — it is NOT, and cannot be instantiated as, "the point at infinity," however natural that would be classically.
- Any principal-divisor identity we can actually formalize and use must be stated entirely in terms of affine points and affine `ordAt`/`div_aff` — no term like `2∞` or `6∞` can appear as an addend anywhere in a `Divisor H` value, since there is no such value to write down.
- Our "principal divisor subgroup" (`PrincSub`) is generated only by DIFFERENCES of two affine-only function divisors with MATCHING pole order at infinity (so the infinity contribution cancels invisibly, never appearing as a term) — see our first message for the exact `divToPairRatio`/`ordInfOfPair`-matching definition.

## What we need from you

Please redo your §5 proof sketch (the K=4→K=2 correctness proof via `h = y - v` interpolating `C` and `ι(A)`) entirely within this affine-only framing. Concretely:

1. Restate `div(h) = C + ι(A) + D_res - 6∞` as a genuine `Divisor H`-level (affine-only) equality. Since `6∞` can't appear as a term, this presumably becomes: `div_aff(h) = C + ι(A) + D_res` (an honest affine equality, degree 6) together with a SEPARATE fact `ord_∞(h) = -6` (a bare integer, not a `Divisor H` term) — mirroring exactly how our existing `div_aff(g) = A+C+T+ιρ` / `ord_∞(g)=-8` pair works. Is that the right translation, or is there subtlety we're missing?
2. Given that translation, walk through explicitly how the final Jacobian identity `C - A - T + 2δ₀ ∈ PrincSub` (or `~ 0`) is meant to be extracted using ONLY: (a) affine divisor equalities like the one in (1), (b) `ordInfOfPair`-matching-based membership in PrincSub (our only actual tool for principality), and (c) whatever combination of (a)/(b) is needed. We specifically want to know whether `div_aff(h) - div_aff(g)` (or some other combination of our OLD `g` and this NEW `h`) ends up being a pole-matched ratio after all, now that we have the corrected complete divisors for both — since if `ord_∞(h) = -8` too (matching `ord_∞(g)`), that pairing WOULD be directly usable via our existing `divToPairRatio` machinery, without needing any new machinery beyond constructing `h` itself.
3. If it's cleaner, feel free to propose the whole thing as: prove `div_aff(h) - div_aff(g') = 0` for some explicit combination `g'` built from our existing `g` (e.g. `g' := g` itself, or `g` composed with something), with matching pole order at infinity confirmed explicitly by degree count, so that the final principality argument is a single, direct `divToPairRatio` membership check we can port immediately — that would be the ideal shape for us to formalize, since it reuses 100% of our existing `principalSubgroup`/`divToPairRatio` machinery with no widening needed.

As before, please be concrete and explicit about degrees/pole orders at every step — we've now twice found that "should balance/cancel" claims needed a literal degree count to confirm, and we'd rather check the arithmetic together now than discover another mismatch after starting to formalize this.
