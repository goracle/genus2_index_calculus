# Status handoff: elim2.jl Gröbner elimination bottleneck

Paste this whole file at the start of a new conversation, along with the
current `elim2.jl`, `err2.txt` (latest run log), and any crash logs.

## The research goal (one sentence)

We're trying to match two symbolic genus-2 curve computations (`sample 1`,
`sample 2`) by eliminating square-root variables from a polynomial system,
to eventually extract a discrete-log relation. Right now we're stuck purely
on the *computational algebra engineering* — making Gröbner elimination
actually finish — not on the underlying math, which is believed sound.

## What's been established as TRUE (don't re-derive these)

1. **Cross-multiplying the two samples directly** (`num1*den2 - num2*den1`)
   produces enormous polynomials: degree 32/48, ~30k/~150k terms. Too big
   to eliminate directly.

2. **The "graph formulation"** (introduce a variable `U_i` per matched
   coefficient, use `num - U_i*den = 0` instead of cross-multiplying)
   shrinks this dramatically: degree 17/25, ~300-700 terms per equation.
   This part is a real, unconditional win — no assumptions needed.

3. **The "decoupled" construction** (`Iu_decoupled` in the code) takes this
   further: instead of one ideal with all 8 variables from both samples,
   it introduces `U0, U1, V0, V1` as shared target variables and builds
   generators that are *each* only in ONE sample's variables + the shared
   `U`/`V`. E.g. `Fu_decoupled[1]` uses only `wa1,wa2,a1,a2,U0` (sample 1);
   `Fu_decoupled[2]` uses only `wb1,wb2,b1,b2,U0` (sample 2). They share
   **only** the variable `U0`.

4. **This is a fiber product**, and the math is fully verified (no missing
   hypotheses): eliminating the w's from the combined ideal equals summing
   the two samples' *independently computed* eliminations:
   ```
   elim_{wa,wb}(Ia + Ib) = elim_wa(Ia) + elim_wb(Ib)
   ```
   This holds because the two ideals' generators have disjoint variable
   support except for the shared `U0`. **This identity is settled — do not
   re-litigate it.** The open question was always the *computational*
   question: does Singular actually get faster if you exploit this?

5. **Norm elimination** (splitting `h = P + Q*w`, taking `P² - Q²·f(t)` to
   kill one `w` at a time) roughly **doubles the degree at each step**
   (17→34→68, 25→50→100). This route is confirmed NOT cheap. Deprioritize it.

## What's been established as a SOFTWARE PROBLEM, not a math problem

This is the actual current blocker, and it's the important part:

- `eliminate(Iu_decoupled, [wa1_d, wa2_d, wb1_d, wb2_d])` on the FULL
  12-variable combined ideal (all 4 generators + 4 curve equations): **hangs
  indefinitely** (never returns, confirmed reproducible across ≥2 runs).

- A smaller version of the same combined ideal (`Fu_decoupled[1:2]` + curves,
  6 generators instead of 8): **times out after 5 min, then segfaults**
  Singular when a second elimination call is attempted afterward.

- Calling `dim()` on the ideal made from JUST the 4 curve equations (the
  simplest, smallest ideal in the whole file — degree 5, 4 terms each):
  **segfaulted**, in a completely different code path (`krull_dim` →
  `groebner_assure` → Singular's `std()`), unrelated to `eliminate()`.

- **Most importantly, reproduced twice now**: eliminating a SINGLE variable
  (`wa1_d` alone) from the full `Iu_decoupled` also hangs. This makes no
  sense if the problem were "genuinely hard elimination math" — a
  single-variable elimination on generators that are individually cheap
  (degree 17, a few hundred terms) should not hang. This strongly suggests
  something is wrong with how Oscar/Singular handles the ~12-variable
  *ambient ring itself*, independent of how many variables you're actually
  asking it to eliminate.

- By contrast, `Fu_decoupled[1]` + curves ALONE (5 variables, 3 generators,
  same generator, same variables to eliminate) **worked fine: 14-15
  seconds, clean result** (degree 36, 1445 terms). Same math, different
  (smaller) ring, no problem.

**Working hypothesis**: this is an Oscar/Singular.jl bug or fragility
specific to this environment/version, triggered by something about the
12-variable `R_dec` ring construction or ideal object — not an inherent
difficulty of the elimination problem. The evidence for this is strong but
not yet 100% nailed down (see "unfinished experiment" below).

## What's IN the current elim2.jl but hasn't finished running yet

**Part H** (near the end of the file, search for `PART H`) is the
decisive test and was added specifically to settle the hypothesis above.
It:
- Builds a **brand new, completely separate 5-variable ring** containing
  only `wa1, wa2, a1, a2, U0` — built directly from `u1_num[1]`/`u1_den[1]`,
  never touching the 12-variable `R_dec` ring at all.
- Eliminates `wa1, wa2` there.
- Repeats independently for sample 2 (`wb1, wb2, b1, b2, U0`).
- **If both finish quickly** (expected, based on the Part B k=1 precedent
  above): this proves the hang/segfault is an artifact of the big ambient
  ring, not the math. Answer: always build small per-sample rings, never
  the big combined one. Ship that as the real solution.
- **If either one ALSO hangs**: that would contradict the Part B k=1 result
  (same generator, same variables, different ring, worked in 15s) and would
  itself be the new mystery to chase — the discrepancy between the two
  would need explaining.

**This is the very next thing to run and read.** The uploaded log cuts off
right after Part C's `wa1_d only` step starts hanging — Part H's output is
what's needed next.

## Practical instructions for the next Claude instance

1. Run the current `elim2.jl` again (or resume monitoring if a run is still
   going). Skip straight to reading **Part H's** output when it appears —
   that's the test that resolves the open question.
2. If Part H succeeds cleanly: the answer is "always build small per-sample
   rings, combine after eliminating each independently." Help refactor the
   working pipeline around that (this needs the code that currently builds
   `R_dec`/`Iu_decoupled` reworked to do Part H's approach for every
   matched coefficient, not just the one Part H currently tests by hand,
   and extended to the `V0,V1`/`Fv_decoupled` side too).
3. If Part H also hangs: don't propose new algorithms yet. The priority is
   figuring out why the SAME generator behaves differently in a 5-variable
   ring built one way vs. built another way — that's a narrower, more
   answerable question than "why is Gröbner slow."
4. **Do not**: re-derive the fiber-product math (point 4 above, settled),
   re-litigate whether the graph formulation helps pre-elimination size
   (point 2, settled), or suggest Dixon resultants / sparse resultants /
   other exotic elimination algorithms — Oscar has no built-in support for
   any of those (confirmed by checking the actual API), so they're not
   actionable here regardless of theoretical merit.
5. **Do** consider, if Part H's evidence holds up, filing a bug report
   against Singular.jl/Oscar.jl (https://github.com/oscar-system/Oscar.jl/issues)
   — a single-variable elimination hanging, plus `dim()` segfaulting on a
   4-generator degree-5 ideal, is unusual enough to be worth reporting. Not
   urgent; the priority is unblocking the actual research via Part H's
   approach.

## Known code hazards in elim2.jl (so a new instance doesn't get bitten)

- `run_with_timeout()` (defined ~line 1385) uses `Threads.@spawn` to poll a
  background computation. **It cannot actually kill a hung Singular C
  call** — it can only stop *waiting* for it. A "timed out" step may still
  be silently consuming CPU/RAM afterward. This is believed to be why the
  segfaults happened (two concurrent Singular calls colliding). A real fix
  would run each risky step as a separate OS process
  (`timeout 300 julia -e '...'`) instead — not yet built, flagged as
  future work if the crashes keep recurring even after Part H's approach
  is adopted.
- Several sections (`PART_B_FULL_SWEEP`, `PART_C_FULL_SWEEP`,
  `PART_F_ENABLED`, all `const ... = false` near the top of their
  respective Parts) are **deliberately disabled** because they reproduce
  the hang/segfault. Don't flip them to `true` without the subprocess-based
  timeout fix above, or expect another crash.
