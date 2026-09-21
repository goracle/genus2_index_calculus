# genus2-lean

Lean 4 / Mathlib formalization supporting a genus-2 hyperelliptic-curve
index-calculus complexity analysis over finite fields.

* The top-level `.lean` files build the curve, Jacobian and divisor-class-group
  theory (`HyperellipticFunctionField.lean`, `DivisorClassGroup.lean`,
  `PrincipalDivisors*.lean`, the Riemann–Roch files, ...).
* The complexity argument is `IndexCalculusComplexity.lean` (balance
  `B ~ p^(2/5)`, cost `p^(4/5)` from a per-solve rate `hRate = B⁴/p²`),
  with `IndexCalculusRelations.lean`, `IndexCalculusHitRate.lean`,
  `IndexCalculusReachability.lean` and `HitRateSumsetReduction.lean` making
  that rate precise. The older Sidon/second-moment route is in
  `Complexity.lean`.
* `ZeroD/` holds the algebraic-geometry side: the `≤ 4` fixed-target bound
  (`ZeroD/FixedTargetBoundCanonical.lean`), the Cantor-reduction/Mumford
  machinery, and an earlier degree-uniform 0-dimensional-system route that is
  no longer being extended.

**Where things stand:** `ZeroD/ROADMAP-current.md`. Older roadmaps, scoping
notes and status logs are session history, not specs; they live in
`ZeroD/oldroadmaps/`. Treat each `.lean` file's own module docstring as ground
truth over any `.md` file.

## GitHub configuration

To set up your new GitHub repository, follow these steps:

* Under your repository name, click **Settings**.
* In the **Actions** section of the sidebar, click "General".
* Check the box **Allow GitHub Actions to create and approve pull requests**.
* Click the **Pages** section of the settings sidebar.
* In the **Source** dropdown menu, select "GitHub Actions".

After following the steps above, you can remove this section from the README file.
