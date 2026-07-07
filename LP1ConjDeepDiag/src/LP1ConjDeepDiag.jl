module LP1ConjDeepDiag

using Printf
using Random
using TrialConfig
using PhiBiasTypes
using LP1ConjLSM

# TrialConfig / PhiBiasTypes / LP1ConjLSM symbols used directly in these
# files (CanonicalLP1Key, canonical_lp1_conj_key, PhiBiasStat,
# conj_total_entries) must be visible unqualified — `using X` (not `import`)
# already does this for a package's own code, so no explicit `import` list
# is needed here the way LP1ConjLSM needed one for the shared conj_* generics.

# Sub-modules in dependency order (mirrors the legacy lp1_conj_deep_diag.jl
# include order).
include("lp1_conj_deep_diag_core.jl")
include("lp1_conj_deep_diag_d1_d6.jl")
include("lp1_conj_deep_diag_d7_d11.jl")
include("lp1_conj_deep_diag_d12_d18.jl")
include("lp1_conj_deep_diag_d19.jl")
include("lp1_conj_deep_diag_d20_d21.jl")
include("lp1_conj_deep_diag_d22_d24.jl")
include("lp1_conj_deep_diag_d25.jl")
include("lp1_conj_deep_diag_d26.jl")
include("lp1_conj_deep_diag_d27.jl")
include("lp1_conj_deep_diag_d28.jl")
include("lp1_conj_deep_diag_d30.jl")
include("lp1_conj_deep_diag_d32.jl")
include("lp1_conj_deep_diag_d33.jl")
include("lp1_conj_deep_diag_d34.jl")
include("lp1_conj_deep_diag_d35.jl")
include("lp1_conj_deep_diag_d36.jl")
include("lp1_conj_deep_diag_d40.jl")
include("lp1_conj_deep_diag_d29.jl")
include("lp1_conj_deep_diag_d37.jl")
include("lp1_conj_deep_diag_d38.jl")
include("lp1_conj_deep_diag_d39.jl")

# Top-level dispatcher — print_conj_deep_report.
include("lp1_conj_deep_diag_dispatcher.jl")

export ConjDeepStat,
       merge_conj_deep_stats,
       OPCODE_0LP,
       OPCODE_1LP_AFF,
       OPCODE_1LP_CONJ,
       OPCODE_2LP_AFF,
       OPCODE_2LP_CONJ,
       OPCODE_SKIP,
       _deep_bucket,
       record_conj_deep_miss!,
       record_conj_deep_step!,
       record_conj_deep_opcode!,
       record_d16_emission!,
       record_d19_closure!,
       record_d20_step!,
       record_d20_emission!,
       record_d22_d23_d24_emission!,
       record_d22_d23_d24_step!,
       flush_d22_open_burst!,
       record_d25_closure!,
       record_d28_aff_step!,
       record_d29_step!,
       record_d30_closure!,
       record_d33_store!,
       record_d34_step!,
       record_d35_closure!,
       record_d36_closure!,
       record_d37_closure!,
       record_d39_closure!,
       D34_OUTCOME_OTHER,
       D34_OUTCOME_0LP,
       D34_OUTCOME_STORE,
       D38Stat,
       print_conj_deep_report

end # module LP1ConjDeepDiag
