# genus2-lean

Lean 4 / Mathlib formalization supporting a genus-2 hyperelliptic-curve
index-calculus complexity analysis. The top-level `.lean` files build up
the curve/Jacobian/divisor-class-group theory (`HyperellipticFunctionField.lean`,
`DivisorClassGroup.lean`, `PrincipalDivisors*.lean`, `RiemannRochGenus2.lean`,
...) that everything else depends on, and `Complexity.lean` states the
actual top-level `O(p^(4/5))` average-case complexity theorem, conditional
on a small number of explicitly named, unproved hypotheses (see that
file's own module docstring for exactly which).

**`ZeroD/` is a self-contained subsystem** attempting an independent,
alternative route to close one of those hypotheses (the "8th moment" /
advisory-6/7 Question 4 bound) via a uniform algebraic-geometry degree
argument rather than the additive-combinatorics route `Complexity.lean`
currently uses. Start at `ZeroD/README.md` for that subsystem's own map
and current status -- it was in need of a single source of truth when
this note was written (17+ partially-contradictory roadmap files), and
`ZeroD/README.md` plus `ZeroD/STATUS.md` are a first attempt at
providing one. The top-level directory (this one) has its own body of
`ROADMAP-*.md`/`SCOPING-*.md` docs (`ROADMAP-ffk-sidon.md`,
`ROADMAP-lpaircarrier-nonclosed-field.md`, `SCOPING-finrank-L-pair.md`,
`SCOPING-isRatioDivisorSpec.md`, `shift-graph-ES-notes.md`,
`genus2-index-calculus-advisory-6.md`) that have **not** been audited
or indexed yet as of this note -- that's the natural next piece of this
documentation effort, not yet started.

## GitHub configuration

To set up your new GitHub repository, follow these steps:

* Under your repository name, click **Settings**.
* In the **Actions** section of the sidebar, click "General".
* Check the box **Allow GitHub Actions to create and approve pull requests**.
* Click the **Pages** section of the settings sidebar.
* In the **Source** dropdown menu, select "GitHub Actions".

After following the steps above, you can remove this section from the README file.
