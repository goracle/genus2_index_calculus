################################################################################
#
#  02_norm_elim_diag.jl -- part of the Elim2 package (src/Elim2.jl
#  includes this file). See src/Elim2.jl for the package-level overview
#  and the full include order of all submodule files.
#
#  Submodule: NormElimDiag
#
#  Encapsulation of original norm_elim_diag.jl (original elim2.jl lines
#  1091-2853): a standalone diagnostic script that answers "is per-sample
#  norm elimination of the w's actually cheap?" using ONLY sample 1 (K=2,
#  c=2), independently of Elim2Main's R/tring/decoupled-system state --
#  the original script re-declared its own small 4-variable ring, its own
#  copies of _reduce_frac/_base_frac_to_ring/_tower_to_ring/tower_to_ring/
#  map_coeffs, and even its own top-level `const p`/`F_POLY_ASC`/`F`,
#  entirely separate from elim2.jl proper's globals of the same name.
#  That duplication is preserved here: NormElimDiag has its own
#  CurveConfig-equivalent setup and its own tower-flattening helpers
#  (`_reduce_frac`, `_base_frac_to_ring`, `_tower_to_ring`, `tower_to_ring`,
#  `map_coeffs`) rather than reusing Elim2Main's, exactly as the original
#  two scripts never shared state.
#
#  This submodule also carries PART A-J of the original file (the
#  post-summary experimental continuation starting at original line
#  ~1478 "EXPERIMENT: eliminate the w's ... from the DECOUPLED ideal"),
#  which is NOT a continuation of the norm-elimination summary above it
#  but a second, independent experiment against Elim2Main's decoupled
#  system (Fu_decoupled/R_dec/etc, built in Elim2Main) -- so functions in
#  this later part take that state as explicit arguments
#  (`decoupled::Elim2Main.DecoupledSystem`) rather than rebuilding it.
#
#  PART J launches external `julia part_j_worker.jl` subprocesses; that
#  worker script was not part of the two uploaded files, so
#  `run_part_j!` below reproduces the launcher/poller exactly but will
#  fail at the `run(...)` call if `part_j_worker.jl` is not present next
#  to this file, same as the original would.
#
################################################################################
module NormElimDiag

using Oscar
using ..Elim2: locate_engine_default, ELIM2_ROOT_DIR
using ..Elim2Main: DecoupledSystem
using ..SampleSpecs: default_sample1

################################################################################
# Struct: DiagCurveConfig -- this script's own copy of the curve/field
# constants (identical values to Elim2Main.CurveConfig, but kept as an
# independent struct/constructor since the original file never shared
# this state with elim2.jl proper). Original top-level consts: p,
# F_POLY_ASC, F (this script's OWN copies, redeclared here).
################################################################################
struct DiagCurveConfig
    p::Int
    F_POLY_ASC::Vector{Int}
    F  # GF(p)
end

function default_diag_curve_config()
    p = 2371157
    F_POLY_ASC = [2, 1, 0, 0, 0, 1]   # y^2 = x^5 + x + 2, ascending coeffs
    F = GF(p)
    return DiagCurveConfig(p, F_POLY_ASC, F)
end

"""
    default_diag_sample1()

Sample 1's (K,c,fixed,u0,u1,v0,v1), now pulled directly from the shared
SampleSpecs.default_sample1() (single source of truth for both samples)
instead of keeping this script's own separate hardcoded copy of the same
literals -- that duplication is exactly the pattern that let
part_j_worker.jl's copy silently drift to K=3,c=2 for sample 2.
Returned as a plain NamedTuple (not SampleSpecs.SampleSpec) to keep every
downstream caller in this file working with `.K`/`.c`/etc. field access
unchanged.
"""
function default_diag_sample1()
    spec = default_sample1()
    return (K = spec.K, c = spec.c, fixed = spec.fixed,
            u0 = spec.u0, u1 = spec.u1, v0 = spec.v0, v1 = spec.v1)
end

"""
    run_sample1_residual(PhiSymbolic, spec, cfg)

Original lines 1152-1160: calls PhiSymbolic.symbolic_residual for sample
1 only, checks it isn't degenerate, prints its degrees.
"""
function run_sample1_residual(PhiSymbolic, spec, cfg::DiagCurveConfig)
    println("Calling PhiSymbolic.symbolic_residual for sample 1 (K=$(spec.K), c=$(spec.c))...")
    res1 = PhiSymbolic.symbolic_residual(spec.K, spec.c, spec.fixed, spec.u0, spec.u1,
                                          spec.v0, spec.v1, cfg.F_POLY_ASC, cfg.p)
    if isempty(res1.u_RS_coeffs) || isempty(res1.v_RS_coeffs)
        error("sample 1 (K=$(spec.K)): construction failed or degenerate -- no u_RS/v_RS to test")
    end
    println("sample 1: deg(u_RS)=$(length(res1.u_RS_coeffs)-1)  deg(v_RS)=$(length(res1.v_RS_coeffs)-1)")
    println()
    return res1
end

################################################################################
# Struct: DiagRing -- this script's own single-sample target ring (JUST
# wa1,wa2,a1,a2 -- 4 variables, no b's, no U/V target vars at this
# stage). Original top-level: R, (wa1,wa2,a1,a2), curve_a1, curve_a2.
################################################################################
struct DiagRing
    R
    wa1; wa2; a1; a2
    curve_a1; curve_a2
end

"""
    build_diag_ring(cfg)

Original lines 1169-1172.
"""
function build_diag_ring(cfg::DiagCurveConfig)
    R, (wa1, wa2, a1, a2) = polynomial_ring(cfg.F, ["wa1", "wa2", "a1", "a2"])
    curve_a1 = wa1^2 - (a1^5 + a1 + 2)
    curve_a2 = wa2^2 - (a2^5 + a2 + 2)
    return DiagRing(R, wa1, wa2, a1, a2, curve_a1, curve_a2)
end

################################################################################
# Tower -> ring flattening, copied verbatim from elim2.jl's own
# _tower_to_ring / _base_frac_to_ring / _reduce_frac (original lines
# 1179-1225), restricted to a single sample and single-threaded (no
# Threads.@threads here, unlike Elim2Main.map_coeffs_threaded -- the
# original norm_elim_diag.jl used a plain sequential loop).
################################################################################

function _reduce_frac(num, den)
    iszero(num) && return (num, one(den))
    g = gcd(num, den)
    if !isone(g)
        num = divexact(num, g)
        den = divexact(den, g)
    end
    return (num, den)
end

function _base_frac_to_ring(val, t_gens::Vector)
    num = numerator(val)
    den = denominator(val)
    num_R = evaluate(num, t_gens)
    den_R = evaluate(den, t_gens)
    return _reduce_frac(num_R, den_R)
end

function _tower_to_ring(val, level::Int, t_gens::Vector, w_gens::Vector)
    if level == 0
        return _base_frac_to_ring(val, t_gens)
    end
    val_poly = data(val)
    c0 = coeff(val_poly, 0)
    c1 = coeff(val_poly, 1)
    n0, d0 = _tower_to_ring(c0, level - 1, t_gens, w_gens)
    n1, d1 = _tower_to_ring(c1, level - 1, t_gens, w_gens)
    wv = w_gens[level]
    num = n0 * d1 + n1 * d0 * wv
    den = d0 * d1
    return _reduce_frac(num, den)
end

tower_to_ring(val, t_gens::Vector, w_gens::Vector) = _tower_to_ring(val, 2, t_gens, w_gens)

function map_coeffs(coeffs, t_gens, w_gens)
    n = length(coeffs)
    nums = Vector{Any}(undef, n)
    dens = Vector{Any}(undef, n)
    for i in 1:n
        nums[i], dens[i] = tower_to_ring(coeffs[i], t_gens, w_gens)
    end
    return nums, dens
end

################################################################################
# Struct: DiagMapped -- sample 1's u_RS/v_RS coefficients flattened into
# DiagRing.R, plus N_U_MATCH (the trivial leading u_RS coefficient
# dropped, same convention as Elim2Main). Original top-level: t_gens_1,
# w_gens_1, u1_num, u1_den, v1_num, v1_den, N_U_MATCH.
################################################################################
struct DiagMapped
    t_gens::Vector
    w_gens::Vector
    u_num::Vector
    u_den::Vector
    v_num::Vector
    v_den::Vector
    N_U_MATCH::Int
end

"""
    map_sample1(res1, dring)

Original lines 1214-1248: flattens sample 1's coefficients into
DiagRing.R and reports per-sample sizes before any elimination.
"""
function map_sample1(res1, dring::DiagRing)
    t_gens_1 = [dring.a1, dring.a2]
    w_gens_1 = [dring.wa1, dring.wa2]

    println("Flattening sample 1's u_RS, v_RS coefficients into F[wa1,wa2,a1,a2]...")
    u1_num, u1_den = map_coeffs(res1.u_RS_coeffs, t_gens_1, w_gens_1)
    v1_num, v1_den = map_coeffs(res1.v_RS_coeffs, t_gens_1, w_gens_1)
    println("done.")
    println()

    N_U_MATCH = length(u1_num) - 1

    println("Per-sample (uncrossed) sizes BEFORE any elimination:")
    for (label, nums, dens, n_use) in [
            ("u1", u1_num, u1_den, N_U_MATCH),
            ("v1", v1_num, v1_den, length(v1_num)),
        ]
        for i in 1:n_use
            n, d = nums[i], dens[i]
            println("  $label num[$i]: degree=", total_degree(n), " terms=", length(terms(n)),
                    "   $label den[$i]: degree=", total_degree(d), " terms=", length(terms(d)))
        end
    end
    println()

    return DiagMapped(t_gens_1, w_gens_1, u1_num, u1_den, v1_num, v1_den, N_U_MATCH)
end

################################################################################
# THE ACTUAL QUESTION (original lines 1250-1420): per-coefficient,
# per-sample norm elimination of wa2 then wa1 from the matching equation
# h = num - U*den. See the original file's extensive derivation comment
# (reproduced narratively above each function below) for why this must
# be done on num-U*den jointly rather than on num,den's norms
# separately, and why reduce_mod_curves must run before AND after every
# split_linear/norm step (the sympy-caught cross-term bug: squaring a
# wa2-linear coefficient that itself contains wa1 reintroduces wa1^2,
# which the free polynomial ring does not auto-reduce).
################################################################################

# f(a) = a^5 + a + 2, evaluated symbolically at whichever anchor variable
f_of(a) = a^5 + a + 2

"""
    reduce_mod_curves(g, wa1, a1, wa2, a2)

Original lines 1339-1360. Reduces `g` modulo wa1^2 -> f(a1), wa2^2 ->
f(a2) at every even power up to 12 (k from 6 down to 1), repeating until
a fixed point -- necessary before AND after every split_linear/norm step
so that step's degree-<=1-in-w precondition genuinely holds in the free
polynomial ring (which does not auto-reduce w_i^2).
"""
function reduce_mod_curves(g, wa1, a1, wa2, a2)
    changed = true
    while changed
        changed = false
        for k in 6:-1:1
            d1 = degree(g, wa1)
            if d1 >= 2*k
                g = g - (coeff(g, [wa1], [2*k]) * wa1^(2*k)) +
                        (coeff(g, [wa1], [2*k]) * f_of(a1)^k)
                changed = true
            end
            d2 = degree(g, wa2)
            if d2 >= 2*k
                g = g - (coeff(g, [wa2], [2*k]) * wa2^(2*k)) +
                        (coeff(g, [wa2], [2*k]) * f_of(a2)^k)
                changed = true
            end
        end
    end
    return g
end

"""
    split_linear(g, w)

Original lines 1362-1374. `g` must be degree <=1 in `w` AFTER
reduce_mod_curves has already been applied -- asserts this rather than
silently mis-splitting (this assert is what originally caught the
cross-term bug).
"""
function split_linear(g, w)
    d = degree(g, w)
    @assert d <= 1 "expected degree <=1 in $w after curve reduction, got $d " *
                    "-- reduce_mod_curves did not fully linearize; check its loop bound (k up to 6) " *
                    "is high enough for this g's actual degree in $w"
    Q = coeff(g, [w], [1])
    P = g - Q * w
    return P, Q
end

"""
    norm_eliminate_step(g, w, a_anchor, wa1, a1, wa2, a2)

Original lines 1376-1385. Reduces mod curves, splits linearly in `w`,
takes the norm P^2 - Q^2*f(a_anchor), then reduces mod curves again
(squaring can reintroduce even powers of the OTHER w).
"""
function norm_eliminate_step(g, w, a_anchor, wa1, a1, wa2, a2)
    g = reduce_mod_curves(g, wa1, a1, wa2, a2)
    P, Q = split_linear(g, w)
    result = P^2 - Q^2 * f_of(a_anchor)
    return reduce_mod_curves(result, wa1, a1, wa2, a2)
end

"""
    run_norm_elim_for_coeff(label, num, den, U_placeholder_name, dring)

Original lines 1387-1420. Builds h0 = num - U*den in a fresh 5-variable
ring (wa1,wa2,a1,a2,U_placeholder_name), norm-eliminates wa2 then wa1,
and reports degree/terms at each stage.
"""
function run_norm_elim_for_coeff(label, num, den, U_placeholder_name, dring::DiagRing)
    println("=" ^ 70)
    println(label)
    println("=" ^ 70)

    Rh, (wa1h, wa2h, a1h, a2h, Uh) = polynomial_ring(
        base_ring(dring.R), ["wa1", "wa2", "a1", "a2", U_placeholder_name]
    )
    new_gens = [wa1h, wa2h, a1h, a2h]
    remap(f) = evaluate(f, new_gens)

    num_h = remap(num)
    den_h = remap(den)
    h0 = num_h - Uh * den_h

    println("  h0 = num - U*den:  degree=", total_degree(h0), "  terms=", length(terms(h0)))

    # Step 1: eliminate wa2 (reduces mod both curve relations internally,
    # which is what fixes the wa1-cross-term bug found by the sympy check)
    h1 = norm_eliminate_step(h0, wa2h, a2h, wa1h, a1h, wa2h, a2h)
    println("  after eliminating wa2:  degree=", total_degree(h1), "  terms=", length(terms(h1)),
            "   (still contains wa1? ", (wa1h in vars(h1)), ")")

    # Step 2: eliminate wa1
    h2 = norm_eliminate_step(h1, wa1h, a1h, wa1h, a1h, wa2h, a2h)
    println("  after eliminating wa1:  degree=", total_degree(h2), "  terms=", length(terms(h2)),
            "   (still contains any w? ", any(v -> v in (wa1h, wa2h), vars(h2)), ")")

    println()
    return (h0=h0, h1=h1, h2=h2)
end

"""
    run_norm_elim_experiment(dmapped, dring)

Original lines 1427-1465: runs `run_norm_elim_for_coeff` on every u_RS
and v_RS coefficient of sample 1 (the whole norm-elimination experiment
-- no Groebner basis, no cross-sample anything), then prints the
supervisor-facing summary table.
"""
function run_norm_elim_experiment(dmapped::DiagMapped, dring::DiagRing)
    results = Dict{String,Any}()

    for i in 1:dmapped.N_U_MATCH
        results["u1_$i"] = run_norm_elim_for_coeff(
            "u1 coefficient x^$(i-1)  (norm-eliminate wa2 then wa1)",
            dmapped.u_num[i], dmapped.u_den[i], "U", dring)
    end

    for i in 1:length(dmapped.v_num)
        results["v1_$i"] = run_norm_elim_for_coeff(
            "v1 coefficient x^$(i-1)  (norm-eliminate wa2 then wa1)",
            dmapped.v_num[i], dmapped.v_den[i], "V", dring)
    end

    println()
    println("#" ^ 70)
    println("SUMMARY: per-sample, per-coefficient norm elimination cost")
    println("#" ^ 70)
    println()
    println(rpad("coefficient", 14), rpad("h0 deg/terms", 18),
            rpad("after wa2", 18), rpad("after wa1", 18))
    for (key, r) in sort(collect(results); by = first)
        d0, t0 = total_degree(r.h0), length(terms(r.h0))
        d1, t1 = total_degree(r.h1), length(terms(r.h1))
        d2, t2 = total_degree(r.h2), length(terms(r.h2))
        println(rpad(key, 14), rpad("$d0 / $t0", 18), rpad("$d1 / $t1", 18), rpad("$d2 / $t2", 18))
    end
    println()
    println("Compare the 'after wa1' column to the cross-multiplied Fu/Fv sizes")
    println("(degree 32/48, ~29,889 / ~150,241 terms) already measured. If these")
    println("numbers stay in the hundreds/low-thousands, per-sample norm elimination")
    println("is cheap as claimed. If they blow up comparably, the claim was wrong")
    println("and the per-sample base-size advantage does not survive elimination --")
    println("in which case the fiber-product win has to come entirely from the")
    println("decoupled-U/V Groebner route (elim2.jl's Iu_decoupled/Iuv_decoupled),")
    println("not from norm elimination, and that's the next thing to test.")

    return results
end

################################################################################
# run_with_timeout -- shared timing helper for PARTS B/C/D/G/H/H'. See
# the original's extensive caveat (reproduced in the docstring): this
# cannot truly KILL a hung Singular/msolve C call, only stop WAITING for
# it; a genuinely reclaiming kill needs an OS-level `timeout N julia ...`
# subprocess instead (not done here, matching the original, which notes
# this as a known limitation rather than fixing it).
################################################################################

"""
    run_with_timeout(f, limit_secs; poll_secs=1.0)

Original lines 1594-1616. Runs `f` (a zero-arg closure) on a background
Task, polling every `poll_secs` up to `limit_secs`. Returns `(value,
:ok, elapsed)`, `(nothing, :error, elapsed)`, or `(nothing, :timeout,
elapsed)`. CAVEAT (original comment, preserved): if `f` blocks in a
Singular/msolve C call, this reports `:timeout` correctly but the
underlying computation is NOT reclaimed -- it keeps running in the
background for the rest of the Julia session. This is exactly what the
original file documents caused a Singular allocator segfault when Part
B's k=3 step started a second concurrent Singular call while k=2's
still-running background Task held allocator state (see
`run_part_b_subideal_sweep!`'s docstring). A true kill requires an
OS-level `timeout N julia -e '...'` subprocess instead, which Part J
(further below) actually does for its own (differently-shaped) reason.
"""
function run_with_timeout(f, limit_secs; poll_secs=1.0)
    t_start = time()
    task = Threads.@spawn begin
        try
            (:ok, f())
        catch e
            (:error, e)
        end
    end
    while !istaskdone(task) && (time() - t_start) < limit_secs
        sleep(poll_secs)
    end
    elapsed = time() - t_start
    if !istaskdone(task)
        return (nothing, :timeout, elapsed)
    end
    status, val = fetch(task)
    if status == :error
        println("  -> error: ", val)
        return (nothing, :error, elapsed)
    end
    return (val, :ok, elapsed)
end

const SUBIDEAL_TIMEOUT_SECS = 300.0   # 5 min per step -- adjust as needed
const VARSWEEP_TIMEOUT_SECS = 300.0

################################################################################
# PART A: static diagnostics on Fu_decoupled + curve generators (no
# Groebner call -- pure structural facts). Takes Elim2Main's
# DecoupledSystem as an explicit argument rather than reaching for
# module-level globals, since this is the point where norm_elim_diag.jl
# (a standalone script in the original) starts operating on state that,
# in the original flat file, was actually built earlier by elim2.jl
# proper (R_dec, Fu_decoupled, curve_*_d) -- i.e. this is the boundary
# where the two originally-separate scripts' state genuinely merges.
################################################################################

"""
    run_part_a_static_diagnostics(decoupled)

Original lines 1529-1566 (PART A). Reports degree/terms/#vars/
homogeneity and a total-degree term-count histogram for every
Fu_decoupled generator plus the four curve relations -- no Groebner
call.
"""
function run_part_a_static_diagnostics(decoupled::DecoupledSystem)
    println()
    println("===========================================================")
    println("PART A: static diagnostics on Fu_decoupled + curve generators")
    println("(no Groebner call -- pure structural facts)")
    println("===========================================================")
    println()

    curve_gens_d = [decoupled.curve_a1_d, decoupled.curve_a2_d,
                    decoupled.curve_b1_d, decoupled.curve_b2_d]
    all_gens_for_diag = vcat(decoupled.Fu_decoupled, curve_gens_d)
    diag_labels = vcat(["Fu_decoupled[$i]" for i in 1:length(decoupled.Fu_decoupled)],
                        ["curve_a1_d", "curve_a2_d", "curve_b1_d", "curve_b2_d"])

    println(rpad("generator", 18), rpad("degree", 8), rpad("terms", 8),
            rpad("#vars", 7), rpad("vars-used", 30), rpad("homogeneous?", 13))
    for (label, g) in zip(diag_labels, all_gens_for_diag)
        vs = vars(g)
        is_hom = is_homogeneous(g)
        println(rpad(label, 18), rpad(total_degree(g), 8), rpad(length(terms(g)), 8),
                rpad(length(vs), 7), rpad(join(string.(vs), ","), 30), rpad(is_hom, 13))
    end
    println()

    println("Degree profile (term-count histogram by total degree) per generator:")
    for (label, g) in zip(diag_labels, all_gens_for_diag)
        profile = Dict{Int,Int}()
        for t in terms(g)
            d = total_degree(t)
            profile[d] = get(profile, d, 0) + 1
        end
        println("  $label: ", sort(collect(profile); by = first))
    end
    println()

    println("Number of generators (Fu_decoupled + curves) = ", length(all_gens_for_diag))
    println("Ambient ring R_dec has ", ngens(decoupled.R_dec), " variables: ", symbols(decoupled.R_dec))
    println()

    return (all_gens_for_diag = all_gens_for_diag, diag_labels = diag_labels, curve_gens_d = curve_gens_d)
end

################################################################################
# PART B: incremental sub-ideal sweep.
################################################################################

"""
    run_part_b_subideal_sweep!(decoupled, curve_gens_d; full_sweep=false)

Original lines 1622-1699 (PART B). Builds `ideal(Fu_decoupled[1:k],
curves)` for k in 1..length(Fu_decoupled) (or just k=1 if
`full_sweep=false`) and eliminates the four w's from each, timing every
step against `SUBIDEAL_TIMEOUT_SECS`.

EVIDENCE FROM THE ORIGINAL RUN (preserved from the original comment,
since it is the reason `full_sweep` defaults to `false`): k=1 completed
in 15s (degree 36, 1445 terms). k=2 timed out at 300s, and the k=3 step
that followed triggered a Singular segfault (omalloc bin-page crash
inside redtailBbb) -- most likely because the k=2 background Task from
`run_with_timeout` was still running when k=3 started a second
concurrent Singular call against shared allocator state. A segfault
kills the entire Julia process and is not catchable by
`run_with_timeout`'s try/catch, so leaving `full_sweep=true` risks
crashing before PART G (which answers the same cross-sample question
safely via fiber-product decomposition) ever runs.
"""
function run_part_b_subideal_sweep!(decoupled::DecoupledSystem, curve_gens_d::Vector; full_sweep::Bool=false)
    println("===========================================================")
    println("PART B: incremental sub-ideal sweep on Fu_decoupled")
    println("(each step: eliminate [wa1_d,wa2_d,wb1_d,wb2_d], timeout=",
            SUBIDEAL_TIMEOUT_SECS, "s)")
    if !full_sweep
        println("full_sweep=false: running only k=1 (confirmed safe/fast).")
        println("k=2 previously timed out and k=3 segfaulted Singular in this exact")
        println("construction -- see PART G below for the safe way to get the")
        println("k=2-equivalent answer via fiber-product decomposition.")
    end
    println("===========================================================")
    println()

    R_dec = decoupled.R_dec
    Fu_decoupled = decoupled.Fu_decoupled
    wa1_d, wa2_d, wb1_d, wb2_d = decoupled.wa1_d, decoupled.wa2_d, decoupled.wb1_d, decoupled.wb2_d

    k_range = full_sweep ? (1:length(Fu_decoupled)) : (1:1)

    for k in k_range
        prefix = Fu_decoupled[1:k]
        Ik = ideal(R_dec, vcat(prefix, curve_gens_d))
        println("--- k=$k: ideal(Fu_decoupled[1:$k], curves)  [", length(prefix) + 4, " generators] ---")
        result, status, elapsed = run_with_timeout(SUBIDEAL_TIMEOUT_SECS) do
            eliminate(Ik, [wa1_d, wa2_d, wb1_d, wb2_d])
        end
        if status == :ok
            gk = gens(result)
            println("  status=OK  elapsed=", round(elapsed, digits=3), "s  ",
                    "generators_out=", length(gk),
                    "  degrees=", total_degree.(gk),
                    "  terms=", length.(terms.(gk)))
        elseif status == :timeout
            println("  status=TIMEOUT after ", round(elapsed, digits=3), "s ",
                    "(still running in background -- see note on run_with_timeout)")
        else
            println("  status=ERROR after ", round(elapsed, digits=3), "s")
        end
        println()
    end
end

################################################################################
# PART C: incremental VARIABLE sweep. NOTE: the original wraps this
# entire loop in `if false # this times out ... end` -- i.e. it is dead
# code in the original file, never executed. Preserved as such: this
# function exists but `run_all_diagnostics` below does not call it,
# exactly mirroring the original's disabled state.
################################################################################

"""
    run_part_c_variable_sweep(decoupled; full_sweep=false)

Original lines 1744-1772 (PART C), inside the original's `if false #
this times out ... end` dead branch -- NOT called by `run_all_diagnostics`,
kept only as a defined-but-unreachable function so the original code is
not lost. Would eliminate wa1_d alone, then +wa2_d, then +wb1_d, then all
four, from the FULL `Iu_decoupled`, each against `VARSWEEP_TIMEOUT_SECS`.
"""
function run_part_c_variable_sweep(decoupled::DecoupledSystem; full_sweep::Bool=false)
    println("===========================================================")
    println("PART C: incremental VARIABLE sweep on full Iu_decoupled")
    println("(timeout=", VARSWEEP_TIMEOUT_SECS, "s per step)")
    if !full_sweep
        println("full_sweep=false: running only step 1 (wa1_d alone).")
        println("Steps 2-4 add more variables/cross-sample coupling and risk the")
        println("same timeout/segfault seen in Part B k=2/k=3 -- see PART G below")
        println("for the safe, decomposed way to get the cross-sample answer.")
    end
    println("===========================================================")
    println()

    wa1_d, wa2_d, wb1_d, wb2_d = decoupled.wa1_d, decoupled.wa2_d, decoupled.wb1_d, decoupled.wb2_d
    var_prefixes = [
        ("wa1_d only",                     [wa1_d]),
        ("wa1_d, wa2_d (sample 1 only)",   [wa1_d, wa2_d]),
        ("wa1_d, wa2_d, wb1_d",            [wa1_d, wa2_d, wb1_d]),
        ("wa1_d, wa2_d, wb1_d, wb2_d (all)", [wa1_d, wa2_d, wb1_d, wb2_d]),
    ]
    prefixes_to_run = full_sweep ? var_prefixes : var_prefixes[1:1]

    for (label, vs) in prefixes_to_run
        println("--- eliminating: $label ---")
        result, status, elapsed = run_with_timeout(VARSWEEP_TIMEOUT_SECS) do
            eliminate(decoupled.Iu_decoupled, vs)
        end
        if status == :ok
            gk = gens(result)
            println("  status=OK  elapsed=", round(elapsed, digits=3), "s  ",
                    "generators_out=", length(gk),
                    "  degrees=", total_degree.(gk),
                    "  terms=", length.(terms.(gk)))
        elseif status == :timeout
            println("  status=TIMEOUT after ", round(elapsed, digits=3), "s ",
                    "(still running in background -- see note on run_with_timeout)")
        else
            println("  status=ERROR after ", round(elapsed, digits=3), "s")
        end
        println()
    end
end

################################################################################
# PART D: cheap dimension/codimension diagnostics on the curve-only ideal
# and the smallest Part-B sub-ideal.
################################################################################

"""
    run_part_d_dim_codim(decoupled, curve_gens_d)

Original lines 1788-1818 (PART D). dim()/codim() on the full
Iu_decoupled are deliberately NOT called (see the module docstring's
note on `singular_groebner_generators` triggering an uncontrolled
default-ordering Groebner computation internally) -- only on the
4-generator curve-only ideal and on `Fu_decoupled[1]` + curves.
"""
function run_part_d_dim_codim(decoupled::DecoupledSystem, curve_gens_d::Vector)
    println("===========================================================")
    println("PART D: dim/codim diagnostics (curve ideal, and smallest sub-ideal)")
    println("===========================================================")
    println()

    R_dec = decoupled.R_dec

    println("--- dim/codim of curve-only ideal (4 gens, degree 5 each) ---")
    result, status, elapsed = run_with_timeout(SUBIDEAL_TIMEOUT_SECS) do
        Icurve = ideal(R_dec, curve_gens_d)
        (dim(Icurve), codim(Icurve))
    end
    if status == :ok
        println("  status=OK  elapsed=", round(elapsed, digits=3), "s  dim=", result[1], "  codim=", result[2])
    else
        println("  status=$status after ", round(elapsed, digits=3), "s")
    end
    println()

    println("--- dim/codim of smallest sub-ideal (Fu_decoupled[1] + curves) ---")
    result, status, elapsed = run_with_timeout(SUBIDEAL_TIMEOUT_SECS) do
        I1 = ideal(R_dec, vcat([decoupled.Fu_decoupled[1]], curve_gens_d))
        (dim(I1), codim(I1))
    end
    if status == :ok
        println("  status=OK  elapsed=", round(elapsed, digits=3), "s  dim=", result[1], "  codim=", result[2])
    else
        println("  status=$status after ", round(elapsed, digits=3), "s  ",
                "(if this alone times out, dim()/codim() themselves are the ",
                "pathological call, not eliminate() -- see PART A/B/C results ",
                "above for where actual elimination first breaks)")
    end
    println()
end

################################################################################
# PART E: confirm the ordering eliminate() is actually constructing.
################################################################################

"""
    run_part_e_ordering_note(decoupled)

Original lines 1836-1854 (PART E). Prints `block_ordering_dec` (only
consumed by direct `groebner_basis(...; ordering=)` calls) and a caveat
that `eliminate(I, vars)` does not expose its own internal ordering
object for inspection via any documented Oscar API.
"""
function run_part_e_ordering_note(decoupled::DecoupledSystem)
    println("===========================================================")
    println("PART E: ordering actually in use")
    println("===========================================================")
    println()
    println("block_ordering_dec (explicit, only consumed by direct groebner_basis")
    println("calls, NOT by eliminate()):")
    println("  ", decoupled.block_ordering_dec)
    println()
    println("eliminate(I, vars) builds its own internal elimination ordering")
    println("(an elimination-ordering variant, block-with-vars-dominant in spirit)")
    println("and does not expose that ordering object for inspection via any")
    println("documented Oscar API as of this writing -- not claiming a specific")
    println("internal implementation here since it isn't independently checkable")
    println("from user code. If the exact internal ordering matters, the only")
    println("verifiable route is calling groebner_basis(I; ordering=<explicit")
    println("elimination ordering built by hand>, algorithm=:f4) directly instead")
    println("of eliminate(), so the ordering used is the one YOU constructed and")
    println("printed above, not an opaque internal choice.")
    println()
end

################################################################################
# PART G: FIBER-PRODUCT DECOMPOSITION. NOTE: the original wraps its
# per-pair loop body in `if false # this section segfaults ... end` --
# dead code in the original, preserved as such: `run_part_g_fiber_product`
# is defined but not called by `run_all_diagnostics`.
################################################################################

"""
    run_part_g_fiber_product(decoupled)

Original lines 1880-2018 (PART G), inside the original's `if false #
this section segfaults ... end` dead branch -- NOT called by
`run_all_diagnostics`. Would eliminate each of the two fiber-product
pairs (Fu_decoupled[1] vs [2] over U0; [3] vs [4] over U1)
INDEPENDENTLY in their own small remapped rings, then report the
combined generator count -- exploiting that
`elim_{wa,wb}(Ia + Ib) = elim_wa(Ia) + elim_wb(Ib)` when Ia, Ib share
only the target U-variable, so Singular never needs to see the full
joint system.
"""
function run_part_g_fiber_product(decoupled::DecoupledSystem)
    println()
    println("===========================================================")
    println("PART G: fiber-product decomposition (eliminate each side ")
    println("independently, then combine via shared U-variable)")
    println("===========================================================")
    println()

    Fu_decoupled = decoupled.Fu_decoupled
    U_vars = decoupled.U_vars
    curve_gens_d_local = [decoupled.curve_a1_d, decoupled.curve_a2_d,
                           decoupled.curve_b1_d, decoupled.curve_b2_d]
    R_dec = decoupled.R_dec
    F = base_ring(R_dec)

    fiber_pairs = [
        ("U0", Fu_decoupled[1], Fu_decoupled[2], U_vars[1]),
        ("U1", Fu_decoupled[3], Fu_decoupled[4], U_vars[2]),
    ]

    for (uname, ga, gb, Uvar) in fiber_pairs
        println("--- fiber pair over $uname ---")
        println("  side A vars: ", vars(ga), "   side B vars: ", vars(gb))
        shared = intersect(Set(vars(ga)), Set(vars(gb)))
        println("  shared variables: ", collect(shared),
                shared == Set([Uvar]) ? "  (confirmed: only $uname shared)" :
                "  *** WARNING: shared set is not just {$uname} -- fiber-product ***" *
                "  *** decomposition below is NOT valid for this pair, skipping ***")
        if shared != Set([Uvar])
            println()
            continue
        end

        # Side A: self-contained ring with only the variables ga uses.
        a_vars_sorted = sort(vars(ga); by = string)
        Ra, ra_gens = polynomial_ring(F, string.(a_vars_sorted))
        a_remap = Dict(zip(a_vars_sorted, ra_gens))
        full_remap_a = [v in a_vars_sorted ? a_remap[v] : zero(Ra) for v in gens(R_dec)]
        ga_small = evaluate(ga, full_remap_a)

        curves_a = [c for c in curve_gens_d_local if !isempty(intersect(Set(vars(c)), Set(a_vars_sorted)))]
        curves_a_small = [evaluate(c, full_remap_a) for c in curves_a]

        Ia_small = ideal(Ra, vcat([ga_small], curves_a_small))
        w_vars_a = [v for v in ra_gens if string(v) in ("wa1","wa2","wb1","wb2")]

        println("  side A: independent ring with ", ngens(Ra), " vars, eliminating ", w_vars_a)
        resultA, statusA, elapsedA = run_with_timeout(SUBIDEAL_TIMEOUT_SECS) do
            eliminate(Ia_small, w_vars_a)
        end
        if statusA == :ok
            gA = gens(resultA)
            println("    status=OK  elapsed=", round(elapsedA, digits=3), "s  ",
                    "generators=", length(gA), "  degrees=", total_degree.(gA),
                    "  terms=", length.(terms.(gA)))
        else
            println("    status=$statusA after ", round(elapsedA, digits=3), "s")
        end

        # Side B, same procedure.
        b_vars_sorted = sort(vars(gb); by = string)
        Rb, rb_gens = polynomial_ring(F, string.(b_vars_sorted))
        b_remap = Dict(zip(b_vars_sorted, rb_gens))
        full_remap_b = [v in b_vars_sorted ? b_remap[v] : zero(Rb) for v in gens(R_dec)]
        gb_small = evaluate(gb, full_remap_b)
        curves_b = [c for c in curve_gens_d_local if !isempty(intersect(Set(vars(c)), Set(b_vars_sorted)))]
        curves_b_small = [evaluate(c, full_remap_b) for c in curves_b]
        Ib_small = ideal(Rb, vcat([gb_small], curves_b_small))
        w_vars_b = [v for v in rb_gens if string(v) in ("wa1","wa2","wb1","wb2")]

        println("  side B: independent ring with ", ngens(Rb), " vars, eliminating ", w_vars_b)
        resultB, statusB, elapsedB = run_with_timeout(SUBIDEAL_TIMEOUT_SECS) do
            eliminate(Ib_small, w_vars_b)
        end
        if statusB == :ok
            gB = gens(resultB)
            println("    status=OK  elapsed=", round(elapsedB, digits=3), "s  ",
                    "generators=", length(gB), "  degrees=", total_degree.(gB),
                    "  terms=", length.(terms.(gB)))
        else
            println("    status=$statusB after ", round(elapsedB, digits=3), "s")
        end

        if statusA == :ok && statusB == :ok
            println("  BOTH sides eliminated independently -- combined result would be")
            println("  elim_A(Ia) + elim_B(Ib) in k[a1,a2,b1,b2,$uname], WITHOUT Singular")
            println("  ever seeing the joint 6+ generator system that hung/segfaulted")
            println("  in Part B. Total combined generator count = ",
                    length(gens(resultA)) + length(gens(resultB)), ".")
            println("  (Not re-embedding into R_dec here -- these live in Ra/Rb, two")
            println("  DIFFERENT small rings, both sharing the variable name \"$uname\"")
            println("  but as distinct ring objects; embedding both into one common")
            println("  k[a1,a2,b1,b2,$uname] ring for actual downstream use is a")
            println("  mechanical remap, omitted here since the point of this pass is")
            println("  the elimination-cost comparison, not the final variety.)")
        end
        println()
    end
end

################################################################################
# PART H: FULLY INDEPENDENT small-ring reconstruction (not a restriction
# of Part G) -- U0 only. Builds sample 1's and sample 2's u_num[1]/u_den[1]
# into brand-new 5-variable rings from scratch, with NO reference to
# R_dec/Iu_decoupled/Fu_decoupled.
################################################################################

"""
    run_part_h_isolated_u0(dmapped, s2::Elim2Main.MappedSample)

Original lines 2057-2224 (PART H). `dmapped` is this submodule's own
sample-1 mapping (from `map_sample1`, giving `u1_num[1]/u1_den[1]` in
DiagRing's 4-variable ring). `s2` is Elim2Main's sample-2 MappedSample
(giving `u2_num[1]/u2_den[1]` in Elim2Main's original 8-variable ring
`[wa1,wa2,wb1,wb2,a2,a1,b2,b1]`) -- the original hardcodes that 8-slot
gens order when zeroing out sample 1's variables for sample 2's remap,
reproduced verbatim below rather than via a generic Dict-based helper,
matching the original's own comment about wanting this directly
inspectable.
"""
function run_part_h_isolated_u0(dmapped::DiagMapped, s2)
    println()
    println("===========================================================")
    println("PART H: fully independent small-ring reconstruction (no R_dec)")
    println("===========================================================")
    println()

    println("Building sample 1's isolated ring: [wa1, wa2, a1, a2, U0], from")
    println("u1_num[1]/u1_den[1] directly -- R_dec is not referenced anywhere below.")
    println()

    F = base_ring(parent(dmapped.u_num[1]))
    Rs1, (wa1_s, wa2_s, a1_s, a2_s, U0_s) = polynomial_ring(F, ["wa1", "wa2", "a1", "a2", "U0"])

    images_s1 = [wa1_s, wa2_s, a1_s, a2_s]
    u1_num1_s = evaluate(dmapped.u_num[1], images_s1)
    u1_den1_s = evaluate(dmapped.u_den[1], images_s1)
    h_s1 = u1_num1_s - U0_s * u1_den1_s

    curve_a1_s = wa1_s^2 - (a1_s^5 + a1_s + 2)
    curve_a2_s = wa2_s^2 - (a2_s^5 + a2_s + 2)

    println("  h_s1 = u1_num[1] - U0*u1_den[1], rebuilt in Rs1: degree=",
            total_degree(h_s1), "  terms=", length(terms(h_s1)))
    println("  (compare to Fu_decoupled[1]'s degree=17/terms=306 from PART A --")
    println("  these should match exactly since it's the same polynomial,")
    println("  independently reconstructed)")
    println()

    Is1 = ideal(Rs1, [h_s1, curve_a1_s, curve_a2_s])

    println("Eliminating [wa1_s, wa2_s] from Is1 (5-variable ring, 3 generators)...")
    resultS1, statusS1, elapsedS1 = run_with_timeout(SUBIDEAL_TIMEOUT_SECS) do
        eliminate(Is1, [wa1_s, wa2_s])
    end
    if statusS1 == :ok
        gS1 = gens(resultS1)
        println("  status=OK  elapsed=", round(elapsedS1, digits=3), "s")
        println("  parent ring = ", base_ring(resultS1))
        println("  number of generators = ", length(gS1))
        for (i, g) in enumerate(gS1)
            println("    gen $i: degree=", total_degree(g), "  terms=", length(terms(g)))
        end
    else
        println("  status=$statusS1 after ", round(elapsedS1, digits=3), "s")
    end
    println()

    println("Building sample 2's isolated ring: [wb1, wb2, b1, b2, U0], from")
    println("u2_num[1]/u2_den[1] directly.")
    println()

    Rs2, (wb1_s, wb2_s, b1_s, b2_s, U0_s2) = polynomial_ring(F, ["wb1", "wb2", "b1", "b2", "U0"])

    # r_gens_full order is [wa1,wa2,wb1,wb2,a2,a1,b2,b1] -- images_s2
    # follows that SAME order: wa1,wa2,a2,a1 -> 0; wb1,wb2,b2,b1 -> their
    # Rs2 generators. Written out explicitly rather than via a generic
    # Dict-based remap helper, matching the original's own stated reason
    # (directly inspectable against r_gens_full's printed order).
    images_s2 = [zero(Rs2), zero(Rs2), wb1_s, wb2_s, b2_s, zero(Rs2), zero(Rs2), b1_s]
    u2_num1_s = evaluate(s2.u_num[1], images_s2)
    u2_den1_s = evaluate(s2.u_den[1], images_s2)
    h_s2 = u2_num1_s - U0_s2 * u2_den1_s

    curve_b1_s = wb1_s^2 - (b1_s^5 + b1_s + 2)
    curve_b2_s = wb2_s^2 - (b2_s^5 + b2_s + 2)

    println("  h_s2 = u2_num[1] - U0*u2_den[1], rebuilt in Rs2: degree=",
            total_degree(h_s2), "  terms=", length(terms(h_s2)))
    println()

    Is2 = ideal(Rs2, [h_s2, curve_b1_s, curve_b2_s])

    println("Eliminating [wb1_s, wb2_s] from Is2 (5-variable ring, 3 generators)...")
    resultS2, statusS2, elapsedS2 = run_with_timeout(SUBIDEAL_TIMEOUT_SECS) do
        eliminate(Is2, [wb1_s, wb2_s])
    end
    if statusS2 == :ok
        gS2 = gens(resultS2)
        println("  status=OK  elapsed=", round(elapsedS2, digits=3), "s")
        println("  parent ring = ", base_ring(resultS2))
        println("  number of generators = ", length(gS2))
        for (i, g) in enumerate(gS2)
            println("    gen $i: degree=", total_degree(g), "  terms=", length(terms(g)))
        end
    else
        println("  status=$statusS2 after ", round(elapsedS2, digits=3), "s")
    end
    println()

    println("#" ^ 70)
    println("PART H READOUT")
    println("#" ^ 70)
    println()
    println("Sample 1 isolated elimination: ", statusS1,
            statusS1 == :ok ? " ($(round(elapsedS1,digits=3))s)" : "")
    println("Sample 2 isolated elimination: ", statusS2,
            statusS2 == :ok ? " ($(round(elapsedS2,digits=3))s)" : "")
    println()
    if statusS1 == :ok && statusS2 == :ok
        println("BOTH isolated 5-variable eliminations succeeded where PART C's")
        println("single-variable (wa1_d alone) elimination on the full 12-variable")
        println("Iu_decoupled did not. This is direct evidence the pathology is NOT")
        println("intrinsic to the elimination mathematics -- a 5-variable, 3-generator")
        println("elimination is not hard -- but IS specific to how Oscar/Singular")
        println("handles the larger ambient ring/ideal object, independent of how")
        println("many variables are actually being eliminated from it.")
    elseif statusS1 == :timeout || statusS2 == :timeout
        println("At least one isolated elimination ALSO timed out. This would mean")
        println("the pathology is not purely an ambient-ring artifact -- something")
        println("about eliminating wa1,wa2 (or wb1,wb2) from THIS SPECIFIC degree-17")
        println("generator is intrinsically expensive, contradicting Part B k=1's")
        println("15s/degree-36/1445-term result for the FOUR-variable elimination of")
        println("the same generator. If that happens, the discrepancy between this")
        println("result and Part B k=1 (same generator, same variables eliminated,")
        println("different ring) is itself the next thing to explain.")
    end
    println()
    println("On the dim() segfault (PART D, curve-only ideal): this happened on a")
    println("4-generator, degree-5 ideal -- about as simple as this ring gets. That")
    println("a crash occurred there specifically inside krull_dim ->")
    println("singular_groebner_generators -> groebner_assure -> Singular's std()")
    println("(see the backtrace) suggests dim()'s particular code path may be doing")
    println("something version-specific and fragile in THIS Oscar/Singular build,")
    println("independent of ideal difficulty. If PART H's isolated eliminations")
    println("above succeed cleanly, that further isolates the problem: eliminate()")
    println("itself may be fine on appropriately small inputs, and dim() specifically")
    println("(not eliminate()) may be the fragile call. This combination -- ")
    println("eliminate() hanging on the full ring, dim() segfaulting on a trivial")
    println("ideal -- is exactly the shape of evidence worth filing as an issue")
    println("against Singular.jl/Oscar.jl (https://github.com/oscar-system/Oscar.jl/issues),")
    println("including: Oscar/Julia/Singular.jl versions (Pkg.status() output),")
    println("this file's construction of R_dec and Is1/Is2, and both crash")
    println("backtraces already captured in this run's output.")
    # See the original file's extended note (reproduced in
    # run_with_timeout's docstring) on the redtailBbb/omalloc allocator
    # crash being consistent with two concurrent Singular calls sharing
    # global allocator state across independent Task-based threads.

    return (statusS1 = statusS1, statusS2 = statusS2)
end

################################################################################
# PART H': same isolated-small-ring test as PART H, but for V0/V1 instead
# of just U0. Gated off by default (PART_H_PRIME_ENABLED, ENV var
# ELIM2_RUN_PART_H_PRIME) since the original documents it as an
# already-validated, expensive re-check rather than something worth
# rerunning on every invocation.
################################################################################

const PART_H_PRIME_ENABLED = get(ENV, "ELIM2_RUN_PART_H_PRIME", "false") == "true"

# Expected values, read directly off the original run's own PART A
# printout (degree=25/terms=698 pre-elimination sizes for v1/v2 num[*]
# and Fv_decoupled). If a re-run disagrees with these, that disagreement
# is exactly the bug this section exists to catch -- not assumed.
const PART_H_PRIME_EXPECTED = Dict(
    ("V0", 1) => (h_degree = 25, h_terms = 698),
    ("V0", 2) => (h_degree = 25, h_terms = 698),
    ("V1", 1) => (h_degree = 25, h_terms = 698),
    ("V1", 2) => (h_degree = 25, h_terms = 698),
)

"""
    part_h_prime_build_and_eliminate(target_name, sample_num, num_coeff, den_coeff, t_names, w_names)

Original lines 2282-2391 (the `part_h_prime_build_and_eliminate` helper
inside PART H'). NOTE the original's own bisect comment, preserved
verbatim in spirit: sample 1's v/u_num live in the REBUILT 4-variable
ring (DiagRing.R in this refactor, via `dmapped`), while sample 2's stay
in the ORIGINAL 8-variable ring (Elim2Main's `tring.R`, via `s2`) --
callers must pass `num_coeff`/`den_coeff` from the matching source, and
the length-mismatch `@assert` below exists specifically because that
asymmetry is a real, recurring failure mode in the original file, not a
hypothetical one.
"""
function part_h_prime_build_and_eliminate(target_name::String, sample_num::Int,
                                            num_coeff, den_coeff,
                                            t_names::Vector{String}, w_names::Vector{String})
    println("Building $(target_name) sample $(sample_num)'s isolated ring: ",
            "[$(w_names[1]), $(w_names[2]), $(t_names[1]), $(t_names[2]), $(target_name)], from")
    println("v$(sample_num)_num/v$(sample_num)_den directly -- R_dec is not referenced.")
    println()

    F = base_ring(parent(num_coeff))
    Rloc, gensloc = polynomial_ring(F, [w_names[1], w_names[2], t_names[1], t_names[2], target_name])
    w1_l, w2_l, t1_l, t2_l, T_l = gensloc

    # Sample 1's num_coeff lives in the 4-variable ring [wa1,wa2,a1,a2];
    # sample 2's lives in the original 8-variable ring
    # [wa1,wa2,wb1,wb2,a2,a1,b2,b1]. images_local must match whichever
    # ring num_coeff actually came from -- see the @assert just below,
    # which is the original's own bisect checkpoint for exactly this.
    images_local = sample_num == 1 ?
        [w1_l, w2_l, t1_l, t2_l] :
        [zero(Rloc), zero(Rloc), w1_l, w2_l, zero(Rloc), zero(Rloc), t2_l, t1_l]
    @assert length(images_local) == nvars(parent(num_coeff)) (
        "PART H' bisect: images_local has $(length(images_local)) entries but " *
        "num_coeff for $(target_name) sample $(sample_num) lives in a ring with " *
        "$(nvars(parent(num_coeff))) variables -- sample 1's v/u_num live in the " *
        "rebuilt 4-variable R, sample 2's stay in the original 8-variable R; " *
        "check which one num_coeff actually came from before editing the mapping."
    )
    num_l = evaluate(num_coeff, images_local)
    den_l = evaluate(den_coeff, images_local)
    h_l = num_l - T_l * den_l

    println("  h = $(target_name)_num - $(target_name)*$(target_name)_den, rebuilt: degree=",
            total_degree(h_l), "  terms=", length(terms(h_l)))

    expected = get(PART_H_PRIME_EXPECTED, (target_name, sample_num), nothing)
    if expected !== nothing
        @assert total_degree(h_l) == expected.h_degree (
            "PART H' bisect: $(target_name) sample $(sample_num) pre-elimination h " *
            "has degree=$(total_degree(h_l)), expected $(expected.h_degree) from " *
            "this run's own PART A printout -- mismatch is BEFORE elimination, so " *
            "the bug is in the mapping/construction above, not in eliminate()."
        )
        @assert length(terms(h_l)) == expected.h_terms (
            "PART H' bisect: $(target_name) sample $(sample_num) pre-elimination h " *
            "has terms=$(length(terms(h_l))), expected $(expected.h_terms) -- " *
            "mismatch is BEFORE elimination; check the images_local mapping first."
        )
        println("  [assert OK] h matches this run's own PART A degree/terms for $(target_name).")
    else
        println("  [no expected value recorded for ($(target_name), sample $(sample_num)) -- skipping assert]")
    end
    println()

    curve1_l = w1_l^2 - (t1_l^5 + t1_l + 2)
    curve2_l = w2_l^2 - (t2_l^5 + t2_l + 2)

    Iloc = ideal(Rloc, [h_l, curve1_l, curve2_l])

    println("Eliminating [$(w_names[1]), $(w_names[2])] from I$(target_name)_$(sample_num) ",
            "(5-variable ring, 3 generators)...")
    resultLoc, statusLoc, elapsedLoc = run_with_timeout(SUBIDEAL_TIMEOUT_SECS) do
        eliminate(Iloc, [w1_l, w2_l])
    end

    if statusLoc == :ok
        gLoc = gens(resultLoc)
        println("  status=OK  elapsed=", round(elapsedLoc, digits=3), "s")
        println("  parent ring = ", base_ring(resultLoc))
        println("  number of generators = ", length(gLoc))
        for (i, g) in enumerate(gLoc)
            println("    gen $i: degree=", total_degree(g), "  terms=", length(terms(g)))
        end
        @assert length(gLoc) >= 1 (
            "PART H' bisect: $(target_name) sample $(sample_num) elimination " *
            "returned status=:ok but zero generators -- this is NOT the same " *
            "success PART H reported for U0 and should not be treated as such."
        )
    else
        println("  status=$statusLoc after ", round(elapsedLoc, digits=3), "s")
    end
    println()

    return (result = resultLoc, status = statusLoc, elapsed = elapsedLoc)
end

"""
    run_part_h_prime_isolated_v0v1(s1::Elim2Main.MappedSample, s2::Elim2Main.MappedSample)

Original lines 2256-2438 (PART H'). Gated by `PART_H_PRIME_ENABLED`
(`ENV["ELIM2_RUN_PART_H_PRIME"]="true"` to enable) exactly as in the
original -- calling this while the gate is off prints the original's
skip message and returns `nothing`. `s1`/`s2` are Elim2Main's
MappedSample for each sample (v1_num/v1_den, v2_num/v2_den).
"""
function run_part_h_prime_isolated_v0v1(s1, s2)
    if !PART_H_PRIME_ENABLED
        println()
        println("[PART H' skipped -- PART_H_PRIME_ENABLED=false. Set ENV[\"ELIM2_RUN_PART_H_PRIME\"]=\"true\" ",
                "to re-run the isolated small-ring V0/V1 elimination check.]")
        println()
        return nothing
    end

    println()
    println("===========================================================")
    println("PART H': isolated small-ring reconstruction, extended to V0/V1")
    println("(same construction as PART H, which only covered U0)")
    println("===========================================================")
    println()

    part_h_prime_results = Dict{Tuple{String,Int}, Any}()

    part_h_prime_results[("V0", 1)] = part_h_prime_build_and_eliminate(
        "V0", 1, s1.v_num[1], s1.v_den[1], ["a1", "a2"], ["wa1", "wa2"])
    part_h_prime_results[("V0", 2)] = part_h_prime_build_and_eliminate(
        "V0", 2, s2.v_num[1], s2.v_den[1], ["b1", "b2"], ["wb1", "wb2"])
    part_h_prime_results[("V1", 1)] = part_h_prime_build_and_eliminate(
        "V1", 1, s1.v_num[2], s1.v_den[2], ["a1", "a2"], ["wa1", "wa2"])
    part_h_prime_results[("V1", 2)] = part_h_prime_build_and_eliminate(
        "V1", 2, s2.v_num[2], s2.v_den[2], ["b1", "b2"], ["wb1", "wb2"])

    println("#" ^ 70)
    println("PART H' READOUT")
    println("#" ^ 70)
    println()
    for key in [("V0", 1), ("V0", 2), ("V1", 1), ("V1", 2)]
        r = part_h_prime_results[key]
        println("$(key[1]) sample $(key[2]) isolated elimination: ", r.status,
                r.status == :ok ? " ($(round(r.elapsed,digits=3))s)" : "")
    end
    println()

    all_v_ok = all(r.status == :ok for r in values(part_h_prime_results))
    if all_v_ok
        println("ALL FOUR V0/V1 isolated 5-variable eliminations succeeded, matching")
        println("PART H's U0 result. This closes the gap PART H left open: the")
        println("small-ring-reconstruction claim ('the pathology is an artifact of")
        println("the 12-variable ambient ring, not the elimination math') now holds")
        println("for every one of the 8 bench targets (U0,U1,V0,V1 x sample1,sample2),")
        println("not just U0. The 12-variable Iu_decoupled/Iuv_decoupled object should")
        println("not be needed again except as a cross-check artifact -- the per-")
        println("sample isolated-ring + multiplicity-correction pipeline (this section")
        println("+ correct_multiplicity below) is now evidenced as the full route.")
    else
        println("** At least one V0/V1 isolated elimination did NOT succeed -- this")
        println("BREAKS the generalization from PART H's U0-only result. Do not")
        println("assume the small-ring route works for V just because it worked for")
        println("U; the degree-25 V generators (vs degree-17 for U) may behave")
        println("differently. See per-case status above before proceeding. **")
    end
    println()

    return part_h_prime_results
end

################################################################################
# PART I: The Sandbox Factory (Automated Elimination) -- Groebner-free
# per-coefficient production pipeline via sequential resultants +
# correct_multiplicity, replacing the eliminate()/Groebner route entirely.
#
# canonical_factor_key/factor_multiset are defined here (matching the
# original's own "Forward declarations, hoisted..." comment: the
# original file is a flat top-to-bottom script with no function
# hoisting, so it redefines these -- identically -- a second time later,
# near part_i_squarefree_diag.jl's own definitions). Since this refactor
# uses functions (not top-level flat execution), only ONE definition of
# each is needed; PartISquarefreeDiag (the next submodule down) reuses
# these via `using ..NormElimDiag: canonical_factor_key, factor_multiset`
# rather than redefining them, so the "harmless redefinition" the
# original relied on is replaced here by ordinary code reuse.
################################################################################

"""
    canonical_factor_key(f) -> String

Original lines 2459-2490. Returns a hashable, order-independent,
unit-scaled key for an irreducible polynomial `f`, so two irreducible
factors coming out of independent `factor()` calls (potentially
differing by a nonzero field-element unit, and with no guaranteed
enumeration order) compare equal iff they are associates.

Normalization: divide by the coefficient of the lexicographically-first
monomial (in a fixed, deterministic term order), so the leading
coefficient of the normalized polynomial is always 1.
"""
function canonical_factor_key(f)
    R = parent(f)
    F = base_ring(R)
    exps = collect(AbstractAlgebra.exponent_vectors(f))
    cfs  = collect(coefficients(f))
    order = sortperm(exps)
    lead_c = cfs[order[1]]
    inv_lead = inv(lead_c)
    io = IOBuffer()
    for idx in order
        c = cfs[idx] * inv_lead
        print(io, string(c), ":", string(exps[idx]), ";")
    end
    return String(take!(io))
end

"""
    factor_multiset(f) -> (Dict{String,Int}, factorization)

Original lines 2492-2507. Factors `f` and returns a map:
canonical_factor_key(irreducible factor) => exponent, plus the raw
factorization object.
"""
function factor_multiset(f)
    fac = factor(f)
    d = Dict{String,Int}()
    for (p, e) in fac
        key = canonical_factor_key(p)
        d[key] = get(d, key, 0) + e
    end
    return d, fac
end

"""
    correct_multiplicity_legacy(Res2)

SUPERSEDED -- original lines 2514-2621. Not called anywhere in this
file (both `process_sample_1_coeff` and `process_sample_2_coeff` call
the general 2-argument `correct_multiplicity(Res1, Res2; label="")`
defined in PartISquarefreeDiag instead). Kept only because the original
kept it (Julia dispatches it and the 2-arg version as separate methods
of the same name; not deleted since that wasn't asked for in the
original either). Renamed from `correct_multiplicity` to
`correct_multiplicity_legacy` here since this refactor's module system
does not auto-merge same-named functions across submodules the way flat
top-level `function` redefinition did in the original -- giving it a
distinct name preserves both definitions instead of one silently
shadowing the other. Hardcodes the correction exponent from the target
variable's name (U->4, V->6) and errors out if there's more than one
degree-8 factor, instead of handling every inflated factor a
Res1-vs-Res2 comparison finds -- do not wire this back in.
"""
function correct_multiplicity_legacy(Res2)
    R = parent(Res2)
    ring_vars = gens(R)
    if isempty(ring_vars)
        error("The resultant parent ring has no generators.")
    end

    target_var = ring_vars[end]
    target_str = string(target_var)

    coord_char = uppercase(target_str[1])
    if coord_char == 'U'
        exponent = 4
    elseif coord_char == 'V'
        exponent = 6
    else
        error("Could not determine coordinate ('U' or 'V') from target variable: $target_str")
    end

    local factors
    try
        factors = factor(Res2)
    catch e
        error("Failed to factor the second resultant Res2: ", e)
    end

    get_poly_degree(p) = begin
        try
            return total_degree(p)
        catch
            try
                return degree(p)
            catch
                error("Unable to determine degree of factor: $p")
            end
        end
    end

    f_infl = nothing
    f_infl_mult = 0

    for (fac, mult) in factors
        if get_poly_degree(fac) == 8
            if f_infl !== nothing
                error("Ambiguity detected: Found multiple distinct degree-8 factors in Res2:\n" *
                      "  1) $f_infl\n" *
                      "  2) $fac\n" *
                      "Cannot deterministically isolate the true inflation factor.")
            end
            f_infl = fac
            f_infl_mult = mult
        end
    end

    if f_infl === nothing
        fac_list = [(fac, mult) for (fac, mult) in factors]
        error("Mathematical assumption violated: Could not find the expected degree-8 " *
              "inflation factor in the factorization of Res2.\n" *
              "Factors found: $fac_list")
    end

    if f_infl_mult < exponent
        error("The identified degree-8 inflation factor ($f_infl) has multiplicity $f_infl_mult " *
              "in Res2, which is less than the required exponent of $exponent for coordinate '$coord_char'.")
    end

    divisor = f_infl^exponent
    success, corrected_poly = divides(Res2, divisor)

    if !success
        error("Exact division failed: Non-zero remainder when dividing Res2 by F_infl^$exponent.")
    end

    return (corrected = corrected_poly, inflation_factor = f_infl, exponent = exponent)
end

"""
    process_sample_1_coeff(raw_coeff, target_name, dring, correct_multiplicity_fn)

Original lines 2638-2670 (Factory for Sample 1, uses 'a' variables).
Groebner-free rewrite: builds the 5-variable sandbox
[wa1,wa2,a1,a2,target_name], flattens `raw_coeff` via `tower_to_ring`,
forms `h = T*den - num`, then eliminates w1 then w2 via SEQUENTIAL
RESULTANTS (`resultant(h, curve1, w1)` then `resultant(step1, curve2,
w2)`) rather than `eliminate()`'s Groebner-basis route, and divides out
the excess multiplicity the resultant chain introduces via
`correct_multiplicity_fn` (the caller passes PartISquarefreeDiag's
2-argument `correct_multiplicity`, matching what the original wired
this to). This route was checked (CHECK_GROEBNER=true runs of
`_run_bench`, in PartIBench below) to reproduce the Groebner-based
`eliminate()` generator exactly.
"""
function process_sample_1_coeff(raw_coeff, target_name, dring::DiagRing, correct_multiplicity_fn)
    println("  Spinning up sandbox for: ", target_name)

    R_small, (w1, w2, a1, a2, T) = polynomial_ring(base_ring(dring.R), ["wa1", "wa2", "a1", "a2", target_name])

    t_gens = [a1, a2]
    w_gens = [w1, w2]
    num_s, den_s = tower_to_ring(raw_coeff, t_gens, w_gens)

    h_s = T * den_s - num_s

    curve1 = w1^2 - (a1^5 + a1 + 2)
    curve2 = w2^2 - (a2^5 + a2 + 2)

    step1 = resultant(h_s, curve1, w1)
    step2 = resultant(step1, curve2, w2)

    corr = correct_multiplicity_fn(step1, step2)

    return corr.corrected
end

"""
    process_sample_2_coeff(raw_coeff, target_name, dring, correct_multiplicity_fn)

Original lines 2678-2709 (Factory for Sample 2, uses 'b' variables
instead of 'a'). Mirrors `process_sample_1_coeff` exactly, just with
`wb1,wb2,b1,b2` in place of `wa1,wa2,a1,a2`.
"""
function process_sample_2_coeff(raw_coeff, target_name, dring::DiagRing, correct_multiplicity_fn)
    println("  Spinning up sandbox (Sample 2) for: ", target_name)

    R_small, (w1, w2, b1, b2, T) = polynomial_ring(base_ring(dring.R), ["wb1", "wb2", "b1", "b2", target_name])

    t_gens = [b1, b2]
    w_gens = [w1, w2]
    num_s, den_s = tower_to_ring(raw_coeff, t_gens, w_gens)

    h_s = T * den_s - num_s

    curve1 = w1^2 - (b1^5 + b1 + 2)
    curve2 = w2^2 - (b2^5 + b2 + 2)

    step1 = resultant(h_s, curve1, w1)
    step2 = resultant(step1, curve2, w2)

    corr = correct_multiplicity_fn(step1, step2)

    return corr.corrected
end

################################################################################
# PART J: The Assembly Line -- dispatches process_sample_{1,2}_coeff's
# work to separate OS-process workers (`julia part_j_worker.jl`), NOT
# Threads.@spawn, because PART H already demonstrated that two
# eliminate()/Singular calls sharing one process's global omalloc
# allocator state can crash. Each job is its own subprocess with its own
# address space.
#
# `part_j_worker.jl` itself is an EXTERNAL file, not one of the two
# uploaded to this refactor -- it was not part of elim2.jl or
# elim2_refactored.jl's own content, only referenced by path. This
# function reproduces the launcher/poller exactly, but `run_part_j!`
# will fail at the `run(cmd; wait=false)` call if that worker script
# is not present next to this file, same as the original would.
################################################################################

const PART_J_MAX_WORKERS = 4

"""
    run_part_j!(res1, output_dir=joinpath(ELIM2_ROOT_DIR, "tmp"), worker_path=joinpath(@__DIR__, "part_j_worker.jl"))

Original lines 2711-2848 (PART J). Builds the list of (sample,target)
jobs from `res1`'s u_RS/v_RS coefficient counts (skipping u_RS's trivial
leading "1"), skips any job whose output file already exists (persistent
across runs, no cleanup), then runs the remaining jobs through a bounded
worker pool of at most `PART_J_MAX_WORKERS` concurrent `julia
part_j_worker.jl <sample> <target> <outfile>` subprocesses, launching
the next queued job into any freed slot as each process exits. Raises an
error immediately if any worker subprocess exits with a nonzero code.
Returns `(clean_sample_1, clean_sample_2)`, the loaded results in the
same U0,U1,...,V0,V1,... order as the original's sequential loop.
`output_dir`/`worker_path` default to siblings of `ELIM2_ROOT_DIR`
(this package's own directory's parent, or `ENV["ELIM2_ROOT_DIR"]` if
set) rather than of this source file, since `part_j_worker.jl` lives
next to wherever this package itself is checked out, not inside `src/`.
"""
function run_part_j!(res1;
                      output_dir::String = joinpath(ELIM2_ROOT_DIR, "tmp"),
                      worker_path::String = joinpath(@__DIR__, "part_j_worker.jl"))
    println("===========================================================")
    println("PART J: The Assembly Line (Processing All Coefficients)")
    println("===========================================================")

    num_u_coeffs = length(res1.u_RS_coeffs) - 1   # skip trivial leading "1"
    num_v_coeffs = length(res1.v_RS_coeffs)

    part_j_jobs = NamedTuple{(:sample, :target), Tuple{Int,String}}[]
    for i in 1:num_u_coeffs
        push!(part_j_jobs, (sample = 1, target = "U$(i-1)"))
        push!(part_j_jobs, (sample = 2, target = "U$(i-1)"))
    end
    for i in 1:num_v_coeffs
        push!(part_j_jobs, (sample = 1, target = "V$(i-1)"))
        push!(part_j_jobs, (sample = 2, target = "V$(i-1)"))
    end

    mkpath(output_dir)

    part_j_jobs_full = map(part_j_jobs) do job
        outfile = joinpath(output_dir, "sample$(job.sample)_$(job.target).oscar")
        (job = job, outfile = outfile)
    end

    part_j_todo = filter(jf -> !isfile(jf.outfile), part_j_jobs_full)
    part_j_skipped = filter(jf -> isfile(jf.outfile), part_j_jobs_full)

    if !isempty(part_j_skipped)
        println("  Skipping ", length(part_j_skipped), " job(s) with existing output file(s):")
        for jf in part_j_skipped
            println("    already have: ", jf.outfile)
        end
    end
    println("  Running ", length(part_j_todo), " of ", length(part_j_jobs_full),
            " sandboxes (up to ", PART_J_MAX_WORKERS, " concurrent worker(s))...")

    part_j_queue = collect(part_j_todo)
    part_j_running = Vector{NamedTuple}()
    part_j_next_idx = Ref(1)

    function part_j_launch_next!()
        part_j_next_idx[] > length(part_j_queue) && return nothing
        jf = part_j_queue[part_j_next_idx[]]
        part_j_next_idx[] += 1
        println("  Spinning up sandbox", jf.job.sample == 2 ? " (Sample 2)" : "", " for: ", jf.job.target)
        cmd = `julia $worker_path $(jf.job.sample) $(jf.job.target) $(jf.outfile)`
        proc = run(pipeline(cmd; stdout=stdout, stderr=stderr); wait=false)
        push!(part_j_running, (job = jf.job, outfile = jf.outfile, proc = proc))
        return nothing
    end

    for _ in 1:min(PART_J_MAX_WORKERS, length(part_j_queue))
        part_j_launch_next!()
    end

    while !isempty(part_j_running)
        finished_idx = nothing
        while finished_idx === nothing
            for (idx, pr) in enumerate(part_j_running)
                if process_exited(pr.proc)
                    finished_idx = idx
                    break
                end
            end
            finished_idx === nothing && sleep(0.5)
        end
        pr = popat!(part_j_running, finished_idx)
        if !success(pr.proc)
            error("Part J worker failed for sample=$(pr.job.sample) target=$(pr.job.target) " *
                  "(exit code $(pr.proc.exitcode)). See its output above for the Singular/Oscar backtrace.")
        end
        part_j_launch_next!()
    end

    println("  All Part J sandboxes finished. Loading results back in...")

    clean_sample_1 = Any[]
    clean_sample_2 = Any[]

    for jf in part_j_jobs_full
        if !isfile(jf.outfile)
            error("Part J: expected output file missing for sample=$(jf.job.sample) " *
                  "target=$(jf.job.target): $(jf.outfile)")
        end
        result = load(jf.outfile)
        if jf.job.sample == 1
            push!(clean_sample_1, result)
        else
            push!(clean_sample_2, result)
        end
    end

    println("\nAssembly Line Finished!")
    println("Sample 1 produced ", length(clean_sample_1), " clean polynomials.")
    println("Sample 2 produced ", length(clean_sample_2), " clean polynomials.")

    return (clean_sample_1 = clean_sample_1, clean_sample_2 = clean_sample_2)
end

"""
    run_norm_elim_diag(PhiSymbolic; full_sweep_b=false, full_sweep_c=false)

Top-level entry point reproducing norm_elim_diag.jl's own original
end-to-end behavior in original top-to-bottom order (PARTS C/G are
defined above but were dead code in the original -- `if false` blocks --
and are NOT called here either, matching the original exactly). Runs
sample-1-only setup (`run_sample1_residual`/`build_diag_ring`/
`map_sample1`) and the norm-elimination experiment
(`run_norm_elim_experiment`); does NOT run PARTS A/B/D/E/G/H/H'/I/J,
since those original lines operate on Elim2Main's DecoupledSystem state
(built later, from BOTH samples) rather than this standalone sample-1
diagnostic -- call those separately via `run_part_a_static_diagnostics`,
etc., once a `DecoupledSystem` is available (see `Elim2.run_all`).
"""
function run_norm_elim_diag(PhiSymbolic; full_sweep_b::Bool=false, full_sweep_c::Bool=false)
    cfg = default_diag_curve_config()
    spec = default_diag_sample1()
    res1 = run_sample1_residual(PhiSymbolic, spec, cfg)
    dring = build_diag_ring(cfg)
    dmapped = map_sample1(res1, dring)
    results = run_norm_elim_experiment(dmapped, dring)
    return (res1 = res1, cfg = cfg, dring = dring, dmapped = dmapped, results = results)
end

"""
    run_all_diagnostics(PhiSymbolic, main; full_sweep_b=false)

Top-level entry point for original lines ~1478-2848 (the PART A-J
continuation against Elim2Main's `DecoupledSystem`, as opposed to
`run_norm_elim_diag`'s standalone sample-1-only experiment above). Takes
`main`, the NamedTuple returned by `Elim2Main.run_main`, and threads its
`decoupled`/`res1`/`s1`/`s2` fields through PARTS A, B, D, E, H, H', and
J in original order:

  - PART A (`run_part_a_static_diagnostics`) -- static structural facts,
    also yields `curve_gens_d`, needed by B and D below
  - PART B (`run_part_b_subideal_sweep!`; `full_sweep=false` by default
    -- k=2 previously timed out and k=3 segfaulted Singular in this
    exact construction, see that function's own docstring)
  - PART C: skipped. Dead code in the original (`if false # this times
    out ... end`) -- `run_part_c_variable_sweep` is defined but
    deliberately not called here, matching the original's disabled state.
  - PART D (`run_part_d_dim_codim`)
  - PART E (`run_part_e_ordering_note`)
  - PART G: skipped. Also dead code in the original (`if false # this
    section segfaults ... end`) -- `run_part_g_fiber_product` is defined
    but not called here either, for the same reason.
  - PART H (`run_part_h_isolated_u0`), using this submodule's own
    sample-1 `dmapped` (built fresh here via `run_sample1_residual`/
    `build_diag_ring`/`map_sample1`, exactly as `run_norm_elim_diag`
    does -- both need `PhiSymbolic` to recompute sample 1's residual in
    this submodule's own 4-variable DiagRing rather than reusing
    `main.res1`, matching the original's genuine duplication) together
    with `main.s2` (Elim2Main's sample-2 MappedSample)
  - PART H' (`run_part_h_prime_isolated_v0v1`), using `main.s1`/`main.s2`
    directly -- no-ops unless `ENV["ELIM2_RUN_PART_H_PRIME"]="true"`
  - PART J (`run_part_j!`), using `main.res1` (Elim2Main's own sample-1
    residual, matching the original's single top-level `res1` -- PART J's
    coefficient counts come from the full two-sample pipeline, not this
    submodule's standalone `res1_local`)

Returns a NamedTuple bundling every part's result, plus
`clean_sample_1`/`clean_sample_2` at the top level (from PART J) since
`PartKResultant.run_part_k!` needs those directly.
"""
function run_all_diagnostics(PhiSymbolic, main; full_sweep_b::Bool=false)
    cfg = default_diag_curve_config()
    spec = default_diag_sample1()
    res1_local = run_sample1_residual(PhiSymbolic, spec, cfg)
    dring = build_diag_ring(cfg)
    dmapped = map_sample1(res1_local, dring)

    part_a = run_part_a_static_diagnostics(main.decoupled)
    curve_gens_d = part_a.curve_gens_d

    run_part_b_subideal_sweep!(main.decoupled, curve_gens_d; full_sweep = full_sweep_b)

    run_part_d_dim_codim(main.decoupled, curve_gens_d)
    run_part_e_ordering_note(main.decoupled)

    run_part_h_isolated_u0(dmapped, main.s2)
    run_part_h_prime_isolated_v0v1(main.s1, main.s2)

    part_j = run_part_j!(main.res1)

    return (part_a = part_a, dmapped = dmapped,
            clean_sample_1 = part_j.clean_sample_1, clean_sample_2 = part_j.clean_sample_2)
end

end # module NormElimDiag
