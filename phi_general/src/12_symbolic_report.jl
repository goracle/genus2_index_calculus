# ==============================================================================
# 12_symbolic_report.jl
# Split fragment of trial3_phi_general.jl (lines 5194-5382 of original).
# NOT standalone-includable yet -- wiring/includes to be sorted out separately.
# ==============================================================================

# =============================================================================
#  SYMBOLIC RESIDUAL REPORT -- wiring into trial3_phi_symbolic_unified.jl
#  ---------------------------------------------------------------------------
#  Provides unified tracing logic bridging the concrete solver and the 
#  OSCAR-based generic extension tower (PhiSymbolic). Supports both c=1 
#  (last anchor free) and c=2 (last two free).
# =============================================================================

const SYMBOLIC_REPORT_ENABLED    = Ref(false)
const SYMBOLIC_REPORT_MAX_SAMPLES = 8

struct SymbolicSample
    K::Int
    c::Int
    fixed_anchors::Vector{NTuple{2,Int}}
    sym_anchors::Vector{NTuple{2,Int}}
    u0::Int; u1::Int; v0::Int; v1::Int
end

# Kept separated to map cleanly onto the distinct driver expectations
const SYMBOLIC_SAMPLES  = Ref{Vector{Vector{SymbolicSample}}}(Vector{SymbolicSample}[])
const SYMBOLIC_SAMPLES2 = Ref{Vector{Vector{SymbolicSample}}}(Vector{SymbolicSample}[])

function init_symbolic_report!(nthreads::Int = Threads.nthreads())
    SYMBOLIC_SAMPLES[] = [SymbolicSample[] for _ in 1:nthreads]
    return nothing
end

function init_symbolic_report2!(nthreads::Int = Threads.nthreads())
    SYMBOLIC_SAMPLES2[] = [SymbolicSample[] for _ in 1:nthreads]
    return nothing
end

@inline function _get_sample_buffer(c::Int)
    tid = Threads.threadid()
    target_ref = c == 1 ? SYMBOLIC_SAMPLES : SYMBOLIC_SAMPLES2
    if isempty(target_ref[]) || tid > length(target_ref[])
        if c == 1
            init_symbolic_report!(max(tid, Threads.nthreads()))
        else
            init_symbolic_report2!(max(tid, Threads.nthreads()))
        end
    end
    return target_ref[][tid]
end

@inline function _record_sample!(anchors, k_cur::Int, c::Int, u0::Int, u1::Int, v0::Int, v1::Int)
    SYMBOLIC_REPORT_ENABLED[] || return nothing
    k_cur < c && return nothing
    
    buf = _get_sample_buffer(c)
    length(buf) >= SYMBOLIC_REPORT_MAX_SAMPLES && return nothing
    
    fixed = NTuple{2,Int}[(anchors[i][1], anchors[i][2]) for i in 1:(k_cur-c)]
    sym_anchors = NTuple{2,Int}[(anchors[k_cur - c + i][1], anchors[k_cur - c + i][2]) for i in 1:c]
    
    push!(buf, SymbolicSample(k_cur, c, fixed, sym_anchors, u0, u1, v0, v1))
    return nothing
end

record_symbolic_sample!(anchors, k_cur::Int, u0::Int, u1::Int, v0::Int, v1::Int) = 
    _record_sample!(anchors, k_cur, 1, u0, u1, v0, v1)

record_symbolic_sample2!(anchors, k_cur::Int, u0::Int, u1::Int, v0::Int, v1::Int) = 
    _record_sample!(anchors, k_cur, 2, u0, u1, v0, v1)


function _run_report!(c::Int, F_POLY_ASC::Vector{Int}, p::Int;
                      io::IO=stdout, max_per_thread::Int=typemax(Int), single_thread::Bool=true)
    target_ref = c == 1 ? SYMBOLIC_SAMPLES : SYMBOLIC_SAMPLES2
    label = c == 1 ? "[SYMBOLIC-REPORT]" : "[SYMBOLIC2-REPORT]"

    isempty(target_ref[]) && (println(io, "$label no samples recorded."); return nothing)

    n_printed = 0
    for (tid, buf) in enumerate(target_ref[])
        single_thread && n_printed > 0 && break
        for (i, samp) in enumerate(buf)
            i > max_per_thread && break
            
            println(io, "\n### thread $tid, sample $i: K=$(samp.K), c=$(samp.c), symbolic anchors = $(samp.sym_anchors), u0,u1=$(samp.u0),$(samp.u1) v0,v1=$(samp.v0),$(samp.v1) ###")
            try
                res = PhiSymbolic.symbolic_residual(samp.K, samp.c, samp.fixed_anchors,
                                                    samp.u0, samp.u1, samp.v0, samp.v1, F_POLY_ASC, p)
                PhiSymbolic.print_symbolic_residual(res; io=io)

                u_c, v_c = PhiSymbolic.symbolic_residual_concrete(samp.K, samp.c, samp.fixed_anchors,
                                                                  samp.u0, samp.u1, samp.v0, samp.v1,
                                                                  F_POLY_ASC, p, samp.sym_anchors)
                PhiSymbolic.print_symbolic_residual_concrete(samp.K, samp.c, samp.sym_anchors, u_c, v_c; io=io)
            catch e
                println(io, "  $label sample failed: $e")
            end
            n_printed += 1
        end
    end
    suffix = (single_thread && c == 2) ? " (single_thread=true -- others skipped in printing)." : "."
    println(io, "\n$label printed $n_printed sample(s)$suffix")
    return nothing
end

run_symbolic_report!(F_POLY_ASC::Vector{Int}, p::Int; kwargs...) = _run_report!(1, F_POLY_ASC, p; kwargs...)
run_symbolic_report2!(F_POLY_ASC::Vector{Int}, p::Int; kwargs...) = _run_report!(2, F_POLY_ASC, p; kwargs...)

function reset_symbolic_report!()
    for buf in SYMBOLIC_SAMPLES[]; empty!(buf); end
end
function reset_symbolic_report2!()
    for buf in SYMBOLIC_SAMPLES2[]; empty!(buf); end
end

# =============================================================================
#  HARD CROSS-CHECKS
# =============================================================================

function _cross_check_symbolic!(K::Int, c::Int, fixed_anchors, sym_anchors, 
                                u0::Int, u1::Int, v0::Int, v1::Int,
                                F_POLY_ASC::Vector{Int}, p::Int)
    
    @assert length(fixed_anchors) == K - c "cross_check_phi_symbolic!: need $(K-c) fixed anchors"
    @assert !isempty(F_POLY_DESC) "cross_check_phi_symbolic!: F_POLY_DESC empty"
    @isdefined(F_POLY) && @assert F_POLY_ASC == F_POLY "cross_check_phi_symbolic!: F_POLY_ASC mismatch"

    # Path 1: Symbolic evaluation
    u_c, v_c = PhiSymbolic.symbolic_residual_concrete(K, c, fixed_anchors, u0, u1, v0, v1,
                                                      F_POLY_ASC, p, sym_anchors)

    # Path 2: Concrete execution
    anchors_vec = NTuple{2,Int}[fixed_anchors...; sym_anchors...]
    anchors = ntuple(i -> anchors_vec[i], K)

    backend = StandardArith(p)
    scratch = ThreadScratchpad{K}()
    init_scratch_caches!(scratch, p, backend)

    ok = build_phi_general!(scratch, anchors, u0, u1, v0, v1; backend=backend)
    @assert ok "cross_check_phi_symbolic!: build_phi_general! returned false"

    basis = rr_basis_cached(K + 3)
    ok2 = phi_residual_general!(scratch, basis, anchors, u0, u1)
    @assert ok2 "cross_check_phi_symbolic!: phi_residual_general! returned false"

    u_len_g = scratch.u_RS_len[1]
    v_len_g = scratch.v_RS_len[1]
    u_g = scratch.u_RS[1:u_len_g]
    v_g = scratch.v_RS[1:v_len_g]

    @assert length(u_c) == length(u_g) && u_c == u_g "cross_check_phi_symbolic!: u_RS MISMATCH"
    @assert length(v_c) == length(v_g) && v_c == v_g "cross_check_phi_symbolic!: v_RS MISMATCH"

    return true
end

function _run_crosscheck!(c::Int, F_POLY_ASC::Vector{Int}, p::Int;
                          io::IO=stdout, max_per_thread::Int=typemax(Int))
    target_ref = c == 1 ? SYMBOLIC_SAMPLES : SYMBOLIC_SAMPLES2
    label = c == 1 ? "[SYMBOLIC-CROSSCHECK]" : "[SYMBOLIC2-CROSSCHECK]"
    
    isempty(target_ref[]) && (println(io, "$label no samples recorded."); return nothing)
    n_checked = 0
    
    for (tid, buf) in enumerate(target_ref[])
        for (i, samp) in enumerate(buf)
            i > max_per_thread && break

            full_anchors = push!(copy(samp.fixed_anchors), samp.sym_anchors...)
            if length(unique(full_anchors)) != length(full_anchors)
                println(io, "$label thread $tid sample $i: SKIPPED (coinciding anchors)")
                continue
            end

            _cross_check_symbolic!(samp.K, samp.c, samp.fixed_anchors, samp.sym_anchors,
                                   samp.u0, samp.u1, samp.v0, samp.v1, F_POLY_ASC, p)
            println(io, "$label thread $tid sample $i: OK (K=$(samp.K))")
            n_checked += 1
        end
    end
    println(io, "\n$label $n_checked sample(s) verified bit-for-bit against production.")
    return nothing
end

cross_check_phi_symbolic!(K::Int, fixed, u0::Int, u1::Int, v0::Int, v1::Int, F_POLY_ASC::Vector{Int}, p::Int, t0::Int, y0::Int) = 
    _cross_check_symbolic!(K, 1, fixed, [(t0, y0)], u0, u1, v0, v1, F_POLY_ASC, p)

cross_check_phi_symbolic2!(K::Int, fixed, u0::Int, u1::Int, v0::Int, v1::Int, F_POLY_ASC::Vector{Int}, p::Int, t1::Int, y1::Int, t2::Int, y2::Int) = 
    _cross_check_symbolic!(K, 2, fixed, [(t1, y1), (t2, y2)], u0, u1, v0, v1, F_POLY_ASC, p)

run_symbolic_crosscheck!(F_POLY_ASC::Vector{Int}, p::Int; kwargs...) = _run_crosscheck!(1, F_POLY_ASC, p; kwargs...)
run_symbolic_crosscheck2!(F_POLY_ASC::Vector{Int}, p::Int; kwargs...) = _run_crosscheck!(2, F_POLY_ASC, p; kwargs...)
