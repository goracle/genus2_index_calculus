module phi_general

using LinearAlgebra
using Base.Threads
using Random
using StaticArrays
using Nemo
# ------------------------------------------------------------------
# 1. Include Sub-files (No parent directory scripts included directly here)
# ------------------------------------------------------------------
include("01_header_setup.jl")
include("02_fp_arith_basis.jl")
include("03_gauss_elim.jl")
include("04_scratchpad.jl")
include("05_branch_series.jl")
include("06_monomial_columns.jl")
include("07_build_phi_general.jl")
include("08_poly_ops_core.jl")
include("09_residual_and_modinv.jl")
include("10_root_finding.jl")
include("11_step_phi.jl")
include("12_symbolic_report.jl")
include("trial3_phi_symbolic_unified.jl")
using .PhiSymbolic   # now visible inside phi_general

# ------------------------------------------------------------------
# 2. Exports 
# ------------------------------------------------------------------
export FpArith, StandardArith, MontgomeryArith, validate_backend
export init_phi_general_caches!, init_scratch_caches!
export step_phi_dispatch!, ThreadScratchpad
export record_symbolic_sample!, record_symbolic_sample2!
export PHI_TIMING_ENABLED, SYMBOLIC_REPORT_ENABLED
export init_phi_timing!, init_symbolic_report!, init_symbolic_report2!
export phi_timing_stats, rr_basis_cached, print_phi_timing_report, run_symbolic_report!, run_symbolic_report2!
export run_symbolic_crosscheck!, run_symbolic_crosscheck2!
export sqrt_fp_fast

global F_POLY::Vector{Int} = Int[]
global K_MAX::Int = 0
global p::Int = 0
global ell::Int = 0

function set_curve_context!(f_poly, k_max, p_loc, ell_loc)
    global F_POLY = f_poly
    global K_MAX = k_max
    global p = p_loc
    global ell = ell_loc
end

end # module phi_general
