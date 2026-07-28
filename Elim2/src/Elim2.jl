#!/usr/bin/env julia

################################################################################
#
#  Elim2.jl -- top-level module for the Elim2 package (src/Elim2.jl).
#
#  This is the Pkg-loadable entry point: `Project.toml` names this
#  package `Elim2` with this file as its `src/` entry, so `using Elim2`
#  (see run_elim2.jl) loads this file, which `include()`s the five
#  submodule files below, each defining one `module ... end` block
#  nested inside this one. Nothing in any of those files runs at
#  `include`/`using` time -- they only define types and functions.
#  Nothing runs until you call one of the `run_*` entry points, e.g.:
#
#      import Pkg; Pkg.activate("Elim2")
#      using Elim2
#      session = Elim2.Elim2Main.run_main(PhiSymbolic)
#
#  or, to reproduce the original elim2.jl's end-to-end behavior (all
#  five units below, in original order), call `Elim2.run_all(PhiSymbolic)`.
#
#  ---------------------------------------------------------------------------
#  WHY THE PACKAGE LOOKS THE WAY IT DOES
#  ---------------------------------------------------------------------------
#  The original elim2.jl was not one script: it was (at least) five
#  originally-separate Julia scripts concatenated back-to-back over the
#  course of a research investigation, each with its own `#!/usr/bin/env
#  julia` header and its own `using Oscar`, plus a large trailing
#  block-comment epilogue. Nothing here reorders or merges that content --
#  every top-level statement from the original file has been kept, moved
#  into a function body, and called from the appropriate `run_*` entry
#  point in its submodule file, in the same relative order it appeared
#  in the original. Dead branches (`if false ... end`) and the trailing
#  `#= ... =#` comment are preserved as-is (as unreachable code / as
#  comments) rather than deleted.
#
#  The five original units, and the submodule file each now lives in:
#
#    1. elim2.jl proper (original lines 1-1090)
#         -> 01_elim2_main.jl,             module Elim2Main
#    2. norm_elim_diag.jl (original lines 1091-2853)
#         -> 02_norm_elim_diag.jl,         module NormElimDiag
#    3. part_i_squarefree_diag.jl (original lines 2854-3964)
#         -> 03_part_i_squarefree_diag.jl, module PartISquarefreeDiag
#    4. part_i_eliminate_vs_resultant_bench.jl (original lines 3965-~5006)
#         -> 04_part_i_bench.jl,           module PartIBench
#    5. elim2.jl's own PART K continuation ("The Final Collision",
#       original lines 4684-8017; original lines 8019-8397 are the
#       dead/removed PART G block, kept as a comment)
#         -> 05_part_k_resultant.jl,       module PartKResultant
#
#  Each submodule exposes one or more `run_*` functions instead of running
#  at top-level on `include`. Shared per-script state (what used to be
#  bare global variables) is now carried in a struct returned by the
#  earlier stage and threaded into the later ones as an explicit argument
#  -- nothing relies on Julia global scope.
#
#  This split from one 7015-line file (elim2_refactored.jl) into this
#  package directory is a pure file-size/organization change, exactly
#  like the earlier flat-to-parts split documented in the predecessor
#  `elim2/` package's own 00_MANIFEST.md -- no logic changed, only where
#  each already-refactored submodule's code physically lives. See each
#  submodule file's own header comment for its part of the original
#  line-range mapping.
#
################################################################################

module Elim2

using Oscar
using Serialization

################################################################################
# Root directory for sibling files/directories this package needs to find
# on disk at runtime: phi_general/ (the PhiSymbolic engine) and the tmp/,
# part_k_results/, part_f_scratch/ working directories PART J/K create.
# (part_j_worker.jl -- PART J's subprocess worker -- used to be one of
# these top-level siblings too, but now lives at Elim2/src/part_j_worker.jl,
# a sibling of this file, so it no longer needs ELIM2_ROOT_DIR to find it.)
#
# As a real Julia package, this file lives at <root>/Elim2/src/Elim2.jl --
# `@__DIR__` here resolves to `<root>/Elim2/src`, which is TWO levels
# below the actual root those sibling files/directories live in, not one
# (unlike the original flat elim2_refactored.jl, where `@__DIR__` in a
# single top-level script WAS the right root). ELIM2_ROOT_DIR corrects
# for that nesting, same convention/name as the flat-file Pkg split this
# package replaces used, so existing `ELIM2_ROOT_DIR` env-var overrides
# and directory layouts keep working unchanged:
#
#   <root>/
#   ├── Elim2/                 <- this package
#   │   └── src/
#   │       ├── Elim2.jl       <- @__DIR__ here == <root>/Elim2/src
#   │       └── part_j_worker.jl
#   ├── phi_general/
#   ├── tmp/
#   ├── part_f_scratch/
#   └── part_k_results/
#
# Override via ENV["ELIM2_ROOT_DIR"] (must be set before `using Elim2`,
# since this is evaluated once at module load as a `const`) if you keep
# this package somewhere other than directly inside <root>.
################################################################################
const ELIM2_ROOT_DIR = haskey(ENV, "ELIM2_ROOT_DIR") ?
    ENV["ELIM2_ROOT_DIR"] :
    dirname(dirname(@__DIR__))   # src/ -> Elim2/ -> <root>

################################################################################
# Shared engine include, common to every submodule below (each original
# script located trial3_phi_symbolic_unified.jl slightly differently --
# see each submodule's own `locate_engine()` for the exact original
# search path it used).
################################################################################

"""
    locate_engine_default()

Original elim2.jl's fixed assumption: the symbolic engine lives at
`<root>/phi_general/src/trial3_phi_symbolic_unified.jl`, where `<root>`
is `ELIM2_ROOT_DIR` (see that constant's docstring above) -- i.e. a
sibling of this package's own directory, not of this file.
"""
function locate_engine_default()
    return joinpath(ELIM2_ROOT_DIR, "phi_general", "src", "trial3_phi_symbolic_unified.jl")
end


################################################################################
# Submodules, included in dependency order (each `using ..X` clause in a
# submodule file requires X's file to be included first):
#
#   00_sample_specs.jl          module SampleSpecs           (no deps -- see
#                                that file's header for why this is split
#                                out: part_j_worker.jl `include()`s it
#                                directly as a bare-Julia file, without
#                                going through this package/Oscar at all)
#   01_elim2_main.jl            module Elim2Main            (needs SampleSpecs)
#   02_norm_elim_diag.jl        module NormElimDiag          (needs Elim2Main, SampleSpecs)
#   03_part_i_squarefree_diag.jl module PartISquarefreeDiag  (needs NormElimDiag)
#   04_part_i_bench.jl          module PartIBench            (needs NormElimDiag, PartISquarefreeDiag)
#   05_part_k_resultant.jl      module PartKResultant        (needs Elim2 root only)
#
# This mirrors the original single-file elim2_refactored.jl's top-to-
# bottom submodule order exactly -- only the file boundaries are new
# (00_sample_specs.jl did not exist as a separate original unit; it is a
# pure extraction of a few lines that used to live inside 01_elim2_main.jl).
################################################################################
include("00_sample_specs.jl")
include("01_elim2_main.jl")
include("02_norm_elim_diag.jl")
include("03_part_i_squarefree_diag.jl")
include("04_part_i_bench.jl")
include("05_part_k_resultant.jl")

"""
    run_all(PhiSymbolic; full_sweep_b=false)

Top-level entry point reproducing elim2.jl's original end-to-end
behavior, in original order, across all five submodules documented at
the top of this file:

  1. `Elim2Main.run_main(PhiSymbolic)` -- original lines 1-1090. Builds
     both samples' residuals, the shared target ring, the decoupled U/V
     system, etc.
  2. `NormElimDiag.run_norm_elim_diag(PhiSymbolic)` -- original lines
     1091-~1477. Standalone sample-1-only norm-elimination experiment,
     independent of step 1's state (see that function's own docstring).
  3. `NormElimDiag.run_all_diagnostics(PhiSymbolic, main)` -- original
     lines ~1478-2848 (PARTS A/B/D/E/H/H'/J). Consumes step 1's
     `DecoupledSystem`/`res1`/`s1`/`s2`; produces `clean_sample_1`/
     `clean_sample_2` (PART J's assembly-line output) needed by step 5.
  4. `PartIBench.run_full_bench_and_overlap_suite(res1, res2, cfg)` --
     original lines 3965-~5006 (part_i_eliminate_vs_resultant_bench.jl).
     Uses step 1's `res1`/`res2`, but its OWN `DiagCurveConfig` (built
     fresh here via `NormElimDiag.default_diag_curve_config()`, same
     values as `Elim2Main.CurveConfig` -- these were two independently
     top-level-`const`-declared `p`/`F_POLY_ASC`/`F` in the original,
     never actually different, so this is preserved duplication, not a
     bug -- see `NormElimDiag.run_all_diagnostics`'s own docstring for
     the same pattern).
  5. `PartKResultant.run_part_k!(F, p, clean_sample_1, clean_sample_2)`
     -- original lines ~4684-8017 (PART K, "The Final Collision"). Uses
     step 3's `clean_sample_1`/`clean_sample_2` and step 4's `cfg.F`/
     `cfg.p`.

PART I (part_i_squarefree_diag.jl, original lines 2854-3964) is NOT
called from here: it is pure function/diagnostic-machinery definitions
(`correct_multiplicity`, `squarefree_multiplicity_diagnostic`,
`factor_stage_trace`, etc.) consumed BY step 4's `_run_bench` internally
-- the original file never called a top-level driver for this section on
its own, only via PART I's bench cases. `PartISquarefreeDiag.
run_diag_on_bench_result` is available for ad hoc use afterward on any
one of step 4's `all_bench_results[case_key]` entries, but note it
expects NamedTuple-style `.gA`/`.gB` field access while `_run_bench`
actually returns a `Dict{String,Any}` (see that function's own
docstring, which already flags this as unverified) -- use
`bench_result["gA"]`/`bench_result["gB"]` directly with
`PartISquarefreeDiag.squarefree_multiplicity_diagnostic` instead if
needed, rather than `run_diag_on_bench_result` as written.

Returns a NamedTuple with each step's full result under `main`, `norm_diag`,
`diagnostics`, `bench`, `part_k`.
"""
function run_all(PhiSymbolic; full_sweep_b::Bool=false)
    main = Elim2Main.run_main(PhiSymbolic)

    norm_diag = NormElimDiag.run_norm_elim_diag(PhiSymbolic)
    diagnostics = NormElimDiag.run_all_diagnostics(PhiSymbolic, main; full_sweep_b = full_sweep_b)

    diag_cfg = NormElimDiag.default_diag_curve_config()
    bench = PartIBench.run_full_bench_and_overlap_suite(main.res1, main.res2, diag_cfg)

    part_k = PartKResultant.run_part_k!(diag_cfg.F, diag_cfg.p,
                                         diagnostics.clean_sample_1, diagnostics.clean_sample_2)

    return (main = main, norm_diag = norm_diag, diagnostics = diagnostics,
            bench = bench, part_k = part_k)
end

end # module Elim2
