# elim2.jl split manifest

`elim2.jl` (6669 lines) was split into the files below, included in this
order by the new top-level `elim2.jl` driver via `include()`. Julia's
`include` shares the caller's (Main) top-level scope, so execution order,
global variable visibility, and semantics are unchanged from the original
monolithic file -- this is a pure file-size split, not a refactor.

One exception: several parts used `@__DIR__` to locate files sitting next
to `elim2.jl` (`phi_general/`, `part_j_worker.jl`, `tmp/`,
`part_k_results/`, `part_f_scratch/`). Since `@__DIR__` inside an
`include`d file resolves to *that file's own* directory rather than the
includer's, those spots were changed to reference `ELIM2_ROOT_DIR` (set
once in the new `elim2.jl` to `@__DIR__` at the top level, i.e. wherever
you actually keep `elim2.jl` and its sibling files). No other code was
changed.

| File | Original lines | Contents |
|---|---|---|
| 01a_header_and_ring_map.jl | 1-446 | Script header/docstring, engine include, curve/field constants, sample1/sample2 `symbolic_residual` calls, tower-to-ring helpers, `map_coeffs_threaded`, symmetry check |
| 01b_wdegree_diagnostic.jl | 447-899 | Degree-in-w diagnostic, `coeff_equal`, `report_wdeg`, `reduce_mod_w_squares`, `split_linear`, `norm_eliminate`, `_tower_to_ring_instrumented` |
| 01c_norm_elim_diag_prelude.jl | 900-1339 | Embedded second script `norm_elim_diag.jl` (own header, own `using Oscar`, re-declares curve/field constants) -- answers the incremental sub-ideal/variable sweep setup used by PARTS A-E below |
| 02_part_a_static_diagnostics.jl | 1340-1471 | PART A: static diagnostics on `Fu_decoupled` + curve generators |
| 03_part_b_subideal_sweep.jl | 1472-1541 | PART B: incremental sub-ideal sweep |
| 04_part_c_variable_sweep.jl | 1542-1597 | PART C: incremental variable sweep on full `Iu_decoupled` |
| 05_part_d_dim_codim.jl | 1598-1645 | PART D: dim/codim diagnostics |
| 06_part_e_ordering.jl | 1646-1723 | PART E: confirm the ordering `eliminate()` is using |
| 07_part_g_fiber_product.jl | 1724-1867 | PART G: fiber-product decomposition |
| 08_part_h_independent_reconstruction.jl | 1868-2035 | PART H: fully independent small-ring reconstruction + PART H readout |
| 09_part_i_sandbox_factory.jl | 2036-2305 | PART I: the Sandbox Factory (automated elimination) |
| 10a_part_j_diagnostics.jl | 2306-3105 | PART J helper functions, batch 1: `part_j_launch_next!`, `canonical_factor_key`, `factor_multiset`, `squarefree_multiplicity_diagnostic`, `run_diag_on_bench_result`, `factor_stage_trace`, `inflating_factor_division_diagnostic` |
| 10b_part_j_bench_helpers.jl | 3106-3991 | PART J helper functions, batch 2: `correct_multiplicity`, `verify_correction`, `map_into_ring`, `identify_inflating_factor`, `discriminant_of_curve`, `leading_coeff_in`, `jacobian_2x2`, `_measure`, `_run_bench`, `run_bench_sample1/2` |
| 11_part_j_driver.jl | 3992-4104 | PART J automated driver: runs all 8 benchmark cases + cross-benchmark summary |
| 12_part_k_core.jl | 4105-4392 | PART K: build final 8-variable ring, the collision setup |
| 13_part_k_quartic_diagnostic.jl | 4393-4592 | PART K DIAGNOSTIC: quartic-in-T structure probe |
| 14a_part_k_bezout_probe.jl | 4593-4901 | PART K DIAGNOSTIC COMPLETE banner, `d1T`/`d2T` guard, Bezout entry sparsity probe |
| 14b_part_k_deep_diagnostic_af.jl | 4902-6595 | The nested `if d1T == 4 && d2T == 4` deep diagnostic block: inner PARTS A-F (coefficient-vector analysis, GCD structure, symmetry reduction, Bezout sparsity, PRS growth prediction, abstract-variable separated resultant). **Left as one file** -- this is a single unbroken Julia scope (~1700 lines) and splitting it without a Julia parser to verify block balance risked introducing a hidden syntax error, which would be worse than an oversized file. |
| 14c_part_k_resultant_finalize.jl | 6596-6669 | Final resultant-via-subresultant-PRS computation and save; trailing comment noting old permutation/subprocess-pool machinery is dead code |

## Note on duplicate/superseded blocks
The original file already contained multiple full attempts at PART K
("take 3", "REDESIGNED", diagnostic vs non-diagnostic versions) and a
second embedded `norm_elim_diag.jl` script pasted in whole. This split
preserves all of that as-is -- no dead code was removed, no logic was
deduplicated. That's a separate cleanup task from "make the file smaller."
