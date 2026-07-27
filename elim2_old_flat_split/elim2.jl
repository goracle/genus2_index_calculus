module elim2

################################################################################
#
#  elim2.jl  --  Monster elimination: match u_RS/v_RS symbolic residuals
#                between two DIFFERENT K's (K=2 sample vs K=3 sample), each
#                with c=2 free symbolic anchors.
#
#  This is the module entry point for the `elim2` package. It just
#  `include`s the split-up parts below, in order, inside this module's
#  scope -- same execution order and semantics as the original single
#  6669-line elim2.jl, just organized as a loadable package instead of a
#  bare script.
#
#  See 00_MANIFEST.md (if present) for a description of each part and the
#  line ranges of the original elim2.jl each one came from.
#
################################################################################

using Oscar

#  IMPORTANT: @__DIR__ inside an `include`d file resolves to that file's
#  OWN directory, i.e. this src/ directory -- not ~/crypto, where
#  phi_general/, part_j_worker.jl, part_k_summand_worker.jl, tmp/,
#  part_f_scratch/, and part_k_results/ actually live. Those are all
#  still siblings of the elim2/ PACKAGE directory, not of this src/ file.
#
#  ~/crypto/
#  ├── elim2/              <- this package
#  │   └── src/
#  │       └── elim2.jl    <- @__DIR__ here == ~/crypto/elim2/src
#  ├── phi_general/
#  ├── part_j_worker.jl
#  ├── tmp/
#  └── ...
#
#  So ELIM2_ROOT_DIR needs to go up TWO levels from this file
#  (src/ -> elim2/ -> crypto/), not one. Every part below references
#  ELIM2_ROOT_DIR instead of @__DIR__ for exactly this reason.
#
#  If you ever run this from somewhere other than ~/crypto/elim2/src
#  relative to ~/crypto, define ELIM2_ROOT_DIR yourself before `using
#  elim2` -- but note this is set at module-load time as a `const`, so
#  that only works via Base.eval or an environment variable, not a
#  plain global assignment after the fact. Simplest override: set
#  ENV["ELIM2_ROOT_DIR"] before loading the package.
const ELIM2_ROOT_DIR = haskey(ENV, "ELIM2_ROOT_DIR") ?
    ENV["ELIM2_ROOT_DIR"] :
    dirname(dirname(@__DIR__))   # src/ -> elim2/ -> crypto/

include("01a_header_and_ring_map.jl")
include("01b_wdegree_diagnostic.jl")
include("01c_norm_elim_diag_prelude.jl")
include("02_part_a_static_diagnostics.jl")
include("03_part_b_subideal_sweep.jl")
include("04_part_c_variable_sweep.jl")
include("05_part_d_dim_codim.jl")
include("06_part_e_ordering.jl")
include("07_part_g_fiber_product.jl")
include("08_part_h_independent_reconstruction.jl")
include("09_part_i_sandbox_factory.jl")
include("10a_part_j_diagnostics.jl")
include("10b_part_j_bench_helpers.jl")
include("11_part_j_driver.jl")
include("12_part_k_core.jl")
include("13_part_k_quartic_diagnostic.jl")
include("14a_part_k_bezout_probe.jl")
include("14b_part_k_deep_diagnostic_af.jl")
include("14c_part_k_resultant_finalize.jl")

end # module elim2
