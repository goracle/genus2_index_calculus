module LP1ConjLSM

using Printf
using TrialConfig
# NOTE: `using TrialConfig` here makes TrialConfig's exports available INSIDE
# this module's own code, but does NOT re-export them to code that only does
# `using LP1ConjLSM`. Consumers that need TrialConfig symbols directly
# (CanonicalLP1Key, conj_shard_idx, canonical_lp1_conj_key, LP1ConjVal, ...)
# must `using TrialConfig` themselves alongside `using LP1ConjLSM`.

# conj_haskey / conj_getval / conj_pop! / conj_insert! / conj_total_entries are
# generic functions OWNED by TrialConfig (defined there on ShardedLP1Conj).
# Importing (rather than merely `using`) them here means the `function
# conj_haskey(sc::LP1ConjLSMStore, ...)`-style definitions inside the included
# files below add NEW METHODS to those same generics instead of silently
# shadowing them with a separate local function of the same name — this is
# what lets `conj_haskey(sc, ...)` dispatch correctly regardless of whether
# `sc` is a ShardedLP1Conj or an LP1ConjLSMStore. Do not remove this import or
# redefine these names as plain `function ... end` without it.
import TrialConfig: conj_haskey, conj_getval, conj_pop!, conj_insert!, conj_total_entries, conj_insert_or_pop!
# Original files, unmodified except for one rename, included in the same
# dependency order as the legacy lp1_conj_lsm.jl entry point.
#
# RENAME NOTE: the struct originally named `LP1ConjLSM` (same as this
# module) has been renamed to `LP1ConjLSMStore` throughout every file below.
# A struct cannot share its exact name with the module that exports it when
# downstream code references the bare type name after `using` (e.g.
# `Union{ShardedLP1Conj{V}, LP1ConjLSM{V}}` in trial3_phase2.jl) — Julia
# binds the module itself to that name first, so the struct becomes
# unreachable under the shared name and any `LP1ConjLSM{...}` type
# expression errors with "expected UnionAll, got a value of type Module".
# This is the ONE content change made to the original files during
# packaging; everything else is a byte-identical copy.
include("lp1_conj_lsm_constants.jl")
include("lp1_conj_lsm_bloom.jl")
include("lp1_conj_lsm_disk.jl")
include("lp1_conj_lsm_topk.jl")
include("lp1_conj_lsm_core.jl")
include("lp1_conj_lsm_renyi.jl")

export LP1ConjLSMStore,
       BloomFilter,
       conj_total_entries,
       conj_haskey,
       conj_getval,
       conj_pop!,
       conj_insert!,
       conj_insert_or_pop!,
       conj_pop_safe,
       conj_roundtrip_ok,
       lsm_flush_all!,
       lsm_close!,
       lsm_info,
       lsm_to_dict,
       lsm_stream_into_dict!,
       lsm_snapshot_and_free!,
       lsm_recommended_hot_cap,
       lsm_resize_hot!,
       lsm_autotune!,
       lsm_mem_report,
       lsm_flush_stats,
       lsm_multiplicity_report,
       lsm_bday_report

global F_POLY::Vector{Int} = Int[]
global p::Int = 0
global ell::Int = 0

function set_curve_context!(f_poly, p_loc, ell_loc)
    global F_POLY = f_poly
    global p = p_loc
    global ell = ell_loc
end



end # module LP1ConjLSM
