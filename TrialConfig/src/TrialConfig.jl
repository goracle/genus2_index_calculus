module TrialConfig

# Original file content, unmodified.
include("trial3_config.jl")

# ---------------------------------------------------------------------------
#  Shared generic functions.
#
#  conj_haskey / conj_getval / conj_pop! / conj_insert! / conj_total_entries
#  are defined here on ShardedLP1Conj. LP1ConjLSM (a separate package) adds
#  methods on LP1ConjLSM for the SAME generic functions via
#  `import TrialConfig: conj_haskey, conj_getval, conj_pop!, conj_insert!,
#  conj_total_entries` — do not redefine these as new local functions in any
#  downstream package, or Julia will error on ambiguous unqualified calls
#  when both packages are `using`'d together.
# ---------------------------------------------------------------------------

export ASSERT_RELATIONS,
       MAX_LP1_ENTRIES,
       MAX_LP1_DOUBLED_ENTRIES,
       LP1_CONJ_CAP_MULTIPLIER,
       LP1_CONJ_CAP_MAX,
       N_CONJ_SHARDS,
       CONJ_LOAD_NUM,
       CONJ_LOAD_DENOM,
       CanonicalLP1Key,
       CONJ_KEY_EMPTY,
       K_MAX,
       ANCHOR_IDX_NONE,
       LP1ConjVal,
       LP1ConjValFull,
       ConjShard,
       ShardedLP1Conj,
       WorkerStats,
       DEFAULT_MAX_LP2_NODES,
       DEFAULT_MAX_LP2_CONJ_NODES,
       MAX_RANK_GROWTH_SAMPLES,
       PHASE3_STEP_MULTIPLIER,
       PHASE3_STEP_CAP_MIN,
       PHASE3_STEP_CAP_MAX,
       PHASE3_LOCAL_LP_NUM,
       PHASE3_LOCAL_LP_DENOM,
       PHASE3_LOCAL_LP_MIN,
       PHASE3_LOCAL_LP_MAX,
       phase3_default_step_cap,
       phase3_local_lp_cap,
       canonical_lp1_conj_key,
       conj_shard_idx,
       conj_haskey,
       conj_getval,
       conj_pop!,
       conj_insert!,
       conj_total_entries,
       conj_to_dict,
       _pack_anchor_indices,
       _unpack_anchor_row,
       _conj_make_val,
       _conj_prev_be,
       _conj_find


global F_POLY::Vector{Int} = Int[]
global p::Int = 0
global ell::Int = 0

function set_curve_context!(f_poly, p_loc, ell_loc)
    global F_POLY = f_poly
    global p = p_loc
    global ell = ell_loc
end

function conj_insert_or_pop! end
end # module TrialConfig
