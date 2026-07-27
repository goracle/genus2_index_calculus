#!/usr/bin/env julia
################################################################################
#
#  run_elim2.jl -- driver script for the Elim2 package.
#
#  Expected layout (Elim2/ is a real, precompilable Julia package -- see
#  Elim2/Project.toml -- so `using Elim2` no longer runs anything itself;
#  everything happens only when you call one of the `run_*` functions
#  below):
#
#    <root>/
#    ├── run_elim2.jl              <- this file
#    ├── Elim2/                     <- the package
#    │   ├── Project.toml
#    │   └── src/
#    │       └── Elim2.jl
#    ├── phi_general/
#    │   └── src/
#    │       └── trial3_phi_symbolic_unified.jl
#    ├── part_j_worker.jl
#    ├── tmp/                       <- created by PART J on first run
#    ├── part_k_results/            <- created by PART K on first run
#    └── part_f_scratch/            <- created by PART K/F on first run
#
#  Usage:
#
#      julia run_elim2.jl                    # full run_all() pipeline
#      julia -t 20 run_elim2.jl              # with 20 Julia threads
#      OMP_NUM_THREADS=20 julia -t 20 run_elim2.jl
#
#      julia run_elim2.jl --stage main       # just Elim2Main.run_main
#      julia run_elim2.jl --stage diagnostics
#      julia run_elim2.jl --stage bench
#      julia run_elim2.jl --stage k
#
#  Or, from the REPL, `include("run_elim2.jl")` and then call the pieces
#  yourself -- see "Running stages individually" below for exactly what
#  each stage needs and returns. This is the recommended way to run PART
#  B/PART J for the first time on a new machine, rather than committing
#  to one long run_all() call -- see the docstrings on
#  NormElimDiag.run_all_diagnostics and PartKResultant.run_part_k! for
#  the specific timeout/segfault history that motivates this.
#
################################################################################

# ELIM2_ROOT_DIR: where phi_general/, part_j_worker.jl, tmp/, etc. live.
# Defaults to this script's own directory. Override by setting
# ENV["ELIM2_ROOT_DIR"] before running this script if you keep those
# sibling files/directories somewhere else relative to Elim2/.
if !haskey(ENV, "ELIM2_ROOT_DIR")
    ENV["ELIM2_ROOT_DIR"] = @__DIR__
end

import Pkg
Pkg.activate(joinpath(@__DIR__, "Elim2"))

using Oscar
using Elim2

include(Elim2.Elim2Main.locate_engine_default())
using .PhiSymbolic

################################################################################
# Stage selection: --stage main|diagnostics|bench|k, or no argument for the
# full run_all() pipeline.
################################################################################

stage = "all"
for (i, a) in enumerate(ARGS)
    if a == "--stage" && i < length(ARGS)
        global stage = ARGS[i+1]
    end
end

if stage == "all"
    println("Running Elim2.run_all(PhiSymbolic) -- the full pipeline.")
    println("(Use `julia run_elim2.jl --stage main|diagnostics|bench|k` to run one")
    println("stage at a time instead -- see this script's header comment.)")
    println()
    result = Elim2.run_all(PhiSymbolic)
    println()
    println("run_all() complete.")

elseif stage == "main"
    println("Running Elim2.Elim2Main.run_main(PhiSymbolic) only.")
    main = Elim2.Elim2Main.run_main(PhiSymbolic)
    println()
    println("Stage 'main' complete. To continue from here in the same session,")
    println("run: Elim2.NormElimDiag.run_all_diagnostics(PhiSymbolic, main)")

elseif stage == "diagnostics"
    println("Running stage 'main' first (diagnostics needs its output)...")
    main = Elim2.Elim2Main.run_main(PhiSymbolic)
    println()
    println("Running Elim2.NormElimDiag.run_all_diagnostics(PhiSymbolic, main)...")
    diagnostics = Elim2.NormElimDiag.run_all_diagnostics(PhiSymbolic, main)
    println()
    println("Stage 'diagnostics' complete. clean_sample_1/clean_sample_2 are ready")
    println("for PartKResultant.run_part_k! (stage 'k').")

elseif stage == "bench"
    println("Running stage 'main' first (bench needs res1/res2)...")
    main = Elim2.Elim2Main.run_main(PhiSymbolic)
    diag_cfg = Elim2.NormElimDiag.default_diag_curve_config()
    println()
    println("Running Elim2.PartIBench.run_full_bench_and_overlap_suite(res1, res2, cfg)...")
    bench = Elim2.PartIBench.run_full_bench_and_overlap_suite(main.res1, main.res2, diag_cfg)
    println()
    println("Stage 'bench' complete.")

elseif stage == "k"
    println("Running stages 'main' and 'diagnostics' first (PART K needs")
    println("clean_sample_1/clean_sample_2 from PART J)...")
    main = Elim2.Elim2Main.run_main(PhiSymbolic)
    diagnostics = Elim2.NormElimDiag.run_all_diagnostics(PhiSymbolic, main)
    diag_cfg = Elim2.NormElimDiag.default_diag_curve_config()
    println()
    println("Running Elim2.PartKResultant.run_part_k!(F, p, clean_sample_1, clean_sample_2)...")
    part_k = Elim2.PartKResultant.run_part_k!(diag_cfg.F, diag_cfg.p,
                                               diagnostics.clean_sample_1,
                                               diagnostics.clean_sample_2)
    println()
    println("Stage 'k' complete. Results (if any targets ran this call) are in")
    println("part_k.results; all four targets' resultants are also saved under")
    println(joinpath(ENV["ELIM2_ROOT_DIR"], "part_k_results"), " regardless.")

else
    error("Unknown --stage '$stage'. Valid: main, diagnostics, bench, k (or omit for 'all').")
end
