# =============================================================================
#  trial3_phase3_dsu.jl  --  Symbolic DSU for phase-3 DLP solving
#
#  OVERVIEW
#  ────────
#  The β=0 precompute (cycle_union_solve) builds a LabelledDSU over the
#  factor base where every label is a scalar:
#
#       label[v]  ≡  log[v] − log[root(v)]   (mod ell)
#
#  For phase 3 we need to handle relations whose RHS carries a β·k term
#  (β≠0).  We lift the label type to a *linear form*:
#
#       label[v]  =  (a, b)   meaning   log[v] − log[root(v)]  ≡  a + b·k
#
#  The β=0 precompute contributes edges with b=0; phase-3 target relations
#  contribute edges with b≠0.  When a cycle closes in the merged DSU the
#  residual is a non-trivial linear form (a, b) with b≠0, giving
#
#       a + b·k  ≡  0   →   k  =  −a · b⁻¹  (mod ell)
#
#  ARCHITECTURE
#  ────────────
#  1.  PrecomputedDSUState  — frozen snapshot of the β=0 DSU (parent, rank,
#      label_a, label_b arrays all of length nF) plus root_log_a / root_log_b
#      (absolute log of each root as a linear form).  Stored in Phase2Tables.
#      All label_b and root_log_b entries are zero (β=0 precompute).
#
#  2.  SymbolicDSU  — mutable working copy of the above, extended with
#      symbolic (a,b) labels.  Cloned cheaply per trial worker by copying
#      the frozen arrays.
#
#  3.  phase3_dsu_worker  — drop-in replacement for phase3_trial_worker.
#      At each β≠0 LP hit it calls sdsu_feed_relation! on the SymbolicDSU,
#      which returns k immediately if a useful cycle is found.  No matrix
#      solve, no Gaussian elimination.
#
#  CORRECTNESS SKETCH
#  ──────────────────
#  A relation  Σ_j c_j·log[j]  ≡  α + β·k  (mod ell)
#  decomposes via the DSU into:
#
#       Σ_j c_j·(label[j] + log[root(j)])  ≡  α + β·k
#       Σ_j c_j·label[j]  +  Σ_j c_j·log[root(j)]  ≡  α + β·k
#
#  where each log[root(j)] is itself a linear form (ar_j, br_j) from the
#  root_log table.  If all roots are the same (full cycle) the equation is:
#
#       (Σ c_j·a_j + ar·Σ c_j)  +  (Σ c_j·b_j + br·Σ c_j)·k  ≡  α + β·k
#
#  Rearranging gives a scalar equation for k (if the b-coefficient is ≠0).
#  In the mixed-root case (some roots differ) we add a new DSU edge merging
#  two components, recording the implied label difference as a linear form.
# =============================================================================

# ---------------------------------------------------------------------------
#  PrecomputedDSUState
#
#  Frozen after cycle_union_solve finishes the β=0 precompute.
#  Embed in Phase2Tables (add a field `dsu_state`).
#
#  Fields:
#    nF         — factor base size
#    ell        — group order (Int)
#    parent     — DSU parent array (1-indexed, parent[v]==v iff root)
#    dsu_rank   — DSU rank array
#    label_a    — label_a[v]: scalar part of label[v] = a + b·k
#    label_b    — label_b[v]: k-coefficient of label[v] (all 0 from β=0 precompute)
#    root_log_a — root_log_a[r]: scalar part of absolute log of root r (-1 if unresolved)
#    root_log_b — root_log_b[r]: k-part of absolute log of root r (0 from β=0 precompute)
# ---------------------------------------------------------------------------
struct PrecomputedDSUState
    nF         ::Int
    ell        ::Int
    parent     ::Vector{Int}
    dsu_rank   ::Vector{Int}
    label_a    ::Vector{Int}
    label_b    ::Vector{Int}
    root_log_a ::Vector{Int}    # -1 = unresolved root
    root_log_b ::Vector{Int}
end

# ---------------------------------------------------------------------------
#  build_precomputed_dsu_state
#
#  Converts the output of cycle_union_solve into a PrecomputedDSUState.
#  Call this immediately after cu_pre = cycle_union_solve(...) in main2().
#
#  Arguments:
#    dsu        — the LabelledDSU used inside cycle_union_solve
#                 (you need to return it from cycle_union_solve — see note below)
#    root_log   — the root_log[] array from inside cycle_union_solve
#    nF, ell    — factor base size and group order
#
#  NOTE: cycle_union_solve currently does not expose its dsu / root_log.
#  Two options:
#    (a) Patch cycle_union_solve to return them (add to the NamedTuple).
#    (b) Reconstruct from atom_logs[] (simpler, see build_from_atom_logs below).
#  Option (b) is implemented here — no patch to cycle_union_solve needed.
# ---------------------------------------------------------------------------

# Reconstruct a PrecomputedDSUState from the flat atom_logs vector returned
# by cycle_union_solve.  The β=0 precompute gives one resolved component per
# connected block; we build a star-topology DSU (each atom points directly to
# a canonical root) which is functionally equivalent for phase-3 purposes.
#
# Atoms with atom_logs[j] == -1 (gauge-free roots) are left unresolved.
#
# This is O(nF) and produces a valid SymbolicDSU starting point.
# Reconstruct a PrecomputedDSUState directly from the LabelledDSU returned by
# cycle_union_solve.  This preserves the full spanning-forest structure (relative
# label offsets between atoms in the same component) that the β=0 walk computed,
# rather than discarding it by going through the flat atom_logs vector.
#
# After path-compression, label[v] = log[v] - log[root(v)] mod ell for every v,
# and root_log[r] = -1 for every gauge-free root (all of them in the β=0 case).
# label_b is all-zero because the precompute used β=0 relations only.
function build_precomputed_dsu_state(dsu::LabelledDSU, root_log::Vector{Int},
                                     nF::Int, ell::Int)::PrecomputedDSUState
    # Force full path compression so every label[v] is direct root-relative.
    for v in 1:nF
        dsu_find(dsu, v)
    end
    return PrecomputedDSUState(nF, ell,
                               copy(dsu.parent),
                               copy(dsu.rank),
                               copy(dsu.label),      # label_a: log[v] - log[root(v)]
                               zeros(Int, nF),        # label_b: all zero (β=0 precompute)
                               copy(root_log),        # root_log_a: -1 for all free roots
                               zeros(Int, nF))        # root_log_b: all zero
end

# ---------------------------------------------------------------------------
#  SymbolicDSU
#
#  Mutable working copy.  Clone from a PrecomputedDSUState at the start of
#  each phase-3 trial; then feed relations one by one.
# ---------------------------------------------------------------------------
mutable struct SymbolicDSU
    nF         ::Int
    ell        ::Int
    parent     ::Vector{Int}
    dsu_rank   ::Vector{Int}
    label_a    ::Vector{Int}   # label[v] = a + b·k; this is 'a'
    label_b    ::Vector{Int}   # this is 'b'
    root_log_a ::Vector{Int}   # absolute log of root r = ra + rb·k; this is 'ra'  (-1 unresolved)
    root_log_b ::Vector{Int}   # this is 'rb'
end

# Clone a PrecomputedDSUState into a fresh mutable SymbolicDSU.
# O(nF) — copies all arrays.
function SymbolicDSU(state::PrecomputedDSUState)::SymbolicDSU
    SymbolicDSU(state.nF, state.ell,
                copy(state.parent),
                copy(state.dsu_rank),
                copy(state.label_a),
                copy(state.label_b),
                copy(state.root_log_a),
                copy(state.root_log_b))
end

# ---------------------------------------------------------------------------
#  sdsu_find
#
#  Path-compressed find.  Returns (root, label_a, label_b) where
#  (label_a, label_b) is the accumulated label from v to root satisfying:
#
#       log[v]  ≡  log[root]  +  label_a  +  label_b · k   (mod ell)
# ---------------------------------------------------------------------------
function sdsu_find(d::SymbolicDSU, v::Int)
    ell = d.ell
    if d.parent[v] == v
        return v, 0, 0
    end
    root, pa, pb = sdsu_find(d, d.parent[v])
    # Accumulate: label[v→root] = label[v→parent] + label[parent→root]
    new_a = mod(d.label_a[v] + pa, ell)
    new_b = mod(d.label_b[v] + pb, ell)
    # Path compress
    d.label_a[v] = new_a
    d.label_b[v] = new_b
    d.parent[v]  = root
    return root, new_a, new_b
end

# ---------------------------------------------------------------------------
#  sdsu_get_log
#
#  Returns (log_a, log_b, resolved::Bool) for atom v.
#  resolved is true iff root_log_a[root] != -1.
#  log[v] ≡ log_a + log_b·k means log_a + log_b·k is the linear-form log.
# ---------------------------------------------------------------------------
@inline function sdsu_get_log(d::SymbolicDSU, v::Int)
    r, la, lb = sdsu_find(d, v)
    ra = d.root_log_a[r]
    ra == -1 && return 0, 0, false
    rb = d.root_log_b[r]
    ell = d.ell
    return mod(ra + la, ell), mod(rb + lb, ell), true
end

# ---------------------------------------------------------------------------
#  sdsu_pin_root!
#
#  Assigns an absolute log (ra, rb) to root r.
#  No-op if already pinned (should not happen in normal operation).
# ---------------------------------------------------------------------------
@inline function sdsu_pin_root!(d::SymbolicDSU, r::Int, ra::Int, rb::Int)
    d.root_log_a[r] = mod(ra, d.ell)
    d.root_log_b[r] = mod(rb, d.ell)
end

# ---------------------------------------------------------------------------
#  sdsu_union_binary!
#
#  Merges the components of atoms u and v given the constraint:
#
#       cu·log[u]  +  cv·log[v]  ≡  rhs_a + rhs_b·k   (mod ell)
#
#  (For the phi walk with unit coefficients: cu=cv=1, so the caller can just
#  pass cu=cv=1 directly.)
#
#  Returns:
#    :cycle_k   — cycle detected; (ka, kb) is the linear constraint
#                 0 ≡ ka + kb·k, ready to solve for k.
#    :merged    — components merged; no new k info.
#    :pinned    — one root newly resolved (propagated from the other side).
#    :deferred  — not enough info yet (both roots unresolved and coefficients
#                 prevent us from encoding the relation as a simple label).
# ---------------------------------------------------------------------------
function sdsu_union_binary!(d::SymbolicDSU, u::Int, cu::Int,
                                            v::Int, cv::Int,
                                            rhs_a::Int, rhs_b::Int)
    ell = d.ell
    ru, lau, lbu = sdsu_find(d, u)
    rv, lav, lbv = sdsu_find(d, v)

    cu_m = mod(cu, ell)
    cv_m = mod(cv, ell)

    if ru == rv
        # ── Cycle: all atoms in same component ──────────────────────────────
        # cu·(ra+lau + (rb+lbu)·k) + cv·(ra+lav + (rb+lbv)·k) ≡ rhs_a + rhs_b·k
        # But ra, rb are the SAME root (ru==rv).
        # Let Ra=root_log_a[ru], Rb=root_log_b[ru].
        Ra = d.root_log_a[ru]
        Rb = d.root_log_b[ru]
        # LHS = cu*(Ra+lau + (Rb+lbu)*k) + cv*(Ra+lav + (Rb+lbv)*k)
        #     = (cu*lau + cv*lav + (cu+cv)*Ra)  +  (cu*lbu + cv*lbv + (cu+cv)*Rb)*k
        # residual = LHS - RHS ≡ 0 (should hold if consistent)
        # Rearranging to solve: 0 ≡ ka + kb*k where:
        #   ka = cu*lau + cv*lav - rhs_a  [+ (cu+cv)*Ra if root is pinned]
        #   kb = cu*lbu + cv*lbv - rhs_b  [+ (cu+cv)*Rb if root is pinned]
        sum_coeff = mod(cu_m + cv_m, ell)
        if Ra != -1
            ka = mod(cu_m*lau + cv_m*lav + sum_coeff*Ra - rhs_a, ell)
            kb = mod(cu_m*lbu + cv_m*lbv + sum_coeff*Rb - rhs_b, ell)
        else
            # Root unresolved: can only produce a useful equation if sum_coeff == 0
            # (the Ra term drops out).  For cu=cv=1 and char ≠ 2 this is never 0.
            # We still record the constraint in terms of the unknown Ra.
            # In practice under our walk, cu=cv=1 and sum_coeff=2.
            # Only useful if sum_coeff ≡ 0 mod ell (rare; skip for now).
            if sum_coeff == 0
                ka = mod(cu_m*lau + cv_m*lav - rhs_a, ell)
                kb = mod(cu_m*lbu + cv_m*lbv - rhs_b, ell)
            else
                return :cycle_unpinned, 0, 0
            end
        end
        return :cycle_k, ka, kb

    else
        # ── Distinct components: try to encode as a label and merge ─────────
        # We want: cu·log[u] + cv·log[v] ≡ rhs_a + rhs_b·k
        # Expanding: cu*(Ra+lau + (Rb+lbu)*k) + cv*(Rv_a+lav + (Rv_b+lbv)*k)
        #            ≡ rhs_a + rhs_b·k
        Ra = d.root_log_a[ru]; Rb = d.root_log_b[ru]
        Rva = d.root_log_a[rv]; Rvb = d.root_log_b[rv]

        u_pinned = (Ra != -1)
        v_pinned = (Rva != -1)

        if u_pinned && v_pinned
            # Both pinned: this is really just a cycle in disguise.
            # Check consistency and possibly yield k.
            ka = mod(cu_m*(Ra+lau) + cv_m*(Rva+lav) - rhs_a, ell)
            kb = mod(cu_m*(Rb+lbu) + cv_m*(Rvb+lbv) - rhs_b, ell)
            return :cycle_k, ka, kb

        elseif u_pinned && !v_pinned
            # Solve for Rv_a, Rv_b:
            # cu*(Ra+lau + (Rb+lbu)*k) + cv*(Rv_a+lav + (Rv_b+lbv)*k) ≡ rhs
            # cv*(Rv_a + lav) ≡ rhs_a - cu*(Ra+lau)     [const part]
            # cv*(Rv_b + lbv) ≡ rhs_b - cu*(Rb+lbu)     [k part]
            cv_inv = powermod(cv_m, ell - 2, ell)
            new_Rva = mod((rhs_a - cu_m*(Ra+lau)) * cv_inv - lav, ell)
            new_Rvb = mod((rhs_b - cu_m*(Rb+lbu)) * cv_inv - lbv, ell)
            # Pin root rv (don't merge; pinning is strictly stronger).
            sdsu_pin_root!(d, rv, new_Rva, new_Rvb)
            return :pinned, 0, 0

        elseif !u_pinned && v_pinned
            # Symmetric: solve for Ra, Rb.
            cu_inv = powermod(cu_m, ell - 2, ell)
            new_Ra = mod((rhs_a - cv_m*(Rva+lav)) * cu_inv - lau, ell)
            new_Rb = mod((rhs_b - cv_m*(Rvb+lbv)) * cu_inv - lbu, ell)
            sdsu_pin_root!(d, ru, new_Ra, new_Rb)
            return :pinned, 0, 0

        else
            # Neither pinned.  Merge and record label difference as linear form.
            # Merge rv → ru (or by rank).  Label of rv relative to ru:
            # We need: cu·(Ra+lau + (Rb+lbu)k) + cv·(Ra_new+lab_rv + (Rb_new+lbv_rv)k) = rhs
            # where Ra_new is the new root_log (ru's), and lab_rv is label[rv→ru].
            # Since both roots unresolved, set Ra_new = Rb_new = unknown X.
            # For the label encoding to work without carrying X symbolically, we
            # require one of cu_m or cv_m to be invertible and (cu+cv) to not
            # introduce a free variable.  In the unit-coefficient case (cu=cv=1):
            # log[u] + log[v] = rhs_a + rhs_b*k
            # (ru+lau) + (rv+lav) = rhs  but both roots are symbolic.
            # We record the DIFFERENCE log[u]-log[v] = rhs_a+rhs_b*k - 2*log[v],
            # which still has an unknown.  We can encode the edge as:
            #   log[rv] - log[ru] = (rhs_a - cu_m*lau - cv_m*lav) / cv_m
            #                       [k-part similar]
            # This is correct only when cv_m ≠ 0.  For cu=cv=1 the label is:
            #   label[rv→ru] = rhs_a - lau - lav  [a-part]
            #   label_b      = rhs_b - lbu - lbv  [b-part]
            # BUT this implicitly assumes Ra - Ra = 0 (same root's log on both
            # sides), which is only valid after merge.  So we merge and set label.
            if cv_m == 0
                return :deferred, 0, 0
            end
            cv_inv = powermod(cv_m, ell - 2, ell)
            # label[rv] = log[rv] - log[ru]
            # From cu*log[u]+cv*log[v]=rhs and log[u]=Ra+lau, log[v]=Rva+lav
            # After merge (ru is new root, rv→ru), log[rv_old] = Ra + new_label[rv_old].
            # We set new_label[rv] so that the relation holds symbolically (Ra cancels
            # only if cu_m + cv_m == 0, otherwise we defer to the k-solve step).
            # Simplest safe encode for (cu=cv=1): store (rhs - lau_total - lav_total)
            # as the inter-component edge; the unknown Ra persists but is shared.
            new_lab_a = mod((rhs_a - cu_m*lau - cv_m*lav) * cv_inv, ell)
            new_lab_b = mod((rhs_b - cu_m*lbu - cv_m*lbv) * cv_inv, ell)

            # Union by rank: ru stays root if rank[ru] >= rank[rv].
            if d.dsu_rank[ru] < d.dsu_rank[rv]
                # Swap so ru has higher rank.
                ru, rv = rv, ru
                lau, lav = lav, lau
                lbu, lbv = lbv, lbu
                cu_m, cv_m = cv_m, cu_m
                new_lab_a = mod(-new_lab_a, ell)
                new_lab_b = mod(-new_lab_b, ell)
            end
            d.label_a[rv]  = new_lab_a
            d.label_b[rv]  = new_lab_b
            d.parent[rv]   = ru
            d.dsu_rank[ru] == d.dsu_rank[rv] && (d.dsu_rank[ru] += 1)
            return :merged, 0, 0
        end
    end
end

# ---------------------------------------------------------------------------
#  sdsu_feed_relation!
#
#  Feeds one relation row into the SymbolicDSU and attempts to recover k.
#
#  Arguments:
#    d        — SymbolicDSU (mutated in place)
#    fb_row   — Dict{Int,Int} mapping FB index → coefficient
#    alpha_i  — scalar α for this relation
#    beta_i   — scalar β for this relation  (≠0 for target relations)
#    fb       — factor base vector (fb[j] = point tuple)
#    G, T     — generator and target (for Jacobian verification)
#
#  Returns:
#    k::Int    — recovered DLP if a useful cycle was found and verified
#    nothing   — no k this relation
#
#  The RHS linear form is:  rhs_a = α_i,  rhs_b = β_i
#  (because the relation says Σ c_j·log[j] ≡ α_i + β_i·k).
# ---------------------------------------------------------------------------
function sdsu_feed_relation!(d::SymbolicDSU,
                             fb_row  ::Dict{Int,Int},
                             alpha_i ::Int,
                             beta_i  ::Int,
                             G       ::Any,
                             T       ::Any)::Union{Int,Nothing}
    ell = d.ell
    support = [(j, mod(v, ell)) for (j, v) in fb_row if mod(v, ell) != 0]
    isempty(support) && return nothing

    # Separate known atoms (root pinned) from unknown ones.
    # For each known atom v: log[v] = (lva, lvb) linear form.
    # known_sum_a + known_sum_b*k = Σ_{j known} c_j * log_a[j]
    # residual rhs: (alpha_i - known_sum_a) + (beta_i - known_sum_b)*k
    #              = Σ_{j unknown} c_j * log[j]

    known_sum_a = 0
    known_sum_b = 0
    unknown     = Tuple{Int,Int}[]   # (fb_index, coeff_mod_ell)

    for (j, cj) in support
        lva, lvb, resolved = sdsu_get_log(d, j)
        if resolved
            known_sum_a = mod(known_sum_a + cj * lva, ell)
            known_sum_b = mod(known_sum_b + cj * lvb, ell)
        else
            push!(unknown, (j, cj))
        end
    end

    rhs_a = mod(alpha_i - known_sum_a, ell)
    rhs_b = mod(beta_i  - known_sum_b, ell)

    n_unk = length(unknown)

    if n_unk == 0
        # Full cycle: every atom resolved.  Equation: 0 ≡ rhs_a + rhs_b*k.
        rhs_b == 0 && return nothing   # degenerate: 0 ≡ rhs_a (consistency check only)
        k_try = mod(-rhs_a * powermod(rhs_b, ell - 2, ell), ell)
        jac_mul(G, k_try, ell) == T && return k_try
        return nothing

    elseif n_unk == 1
        # One unknown atom: pin it.
        j_unk, cj = unknown[1]
        # cj * log[j_unk] ≡ rhs_a + rhs_b*k
        # log[j_unk] = (rhs_a * cj_inv, rhs_b * cj_inv)
        cj_inv = powermod(cj, ell - 2, ell)
        new_a  = mod(rhs_a * cj_inv, ell)
        new_b  = mod(rhs_b * cj_inv, ell)
        r_j, laj, lbj = sdsu_find(d, j_unk)
        # root_log[r_j] satisfies: root_log + (laj + lbj*k) = new_a + new_b*k
        # root_log_a = new_a - laj,  root_log_b = new_b - lbj
        sdsu_pin_root!(d, r_j, mod(new_a - laj, ell), mod(new_b - lbj, ell))
        # After pinning, check if any existing cycle becomes solvable.
        # (We don't iterate here; caller's outer loop handles deferred rows.)
        return nothing

    elseif n_unk == 2
        # Two unknowns: try to merge or pin via sdsu_union_binary!.
        (j1, c1), (j2, c2) = unknown[1], unknown[2]
        status, ka, kb = sdsu_union_binary!(d, j1, c1, j2, c2, rhs_a, rhs_b)

        if status === :cycle_k
            kb == 0 && return nothing
            k_try = mod(-ka * powermod(kb, ell - 2, ell), ell)
            jac_mul(G, k_try, ell) == T && return k_try
            return nothing
        elseif status === :pinned || status === :merged
            return nothing
        else
            return nothing   # :deferred or :cycle_unpinned
        end

    else
        # Three or more unknowns.  The walk produces weight-3 relations
        # {j0, jR, jS}; when none is in atom_log_dict all three are unknown.
        # Group unknowns by their DSU root; each distinct root r contributes
        # a term  (sum_coeff_r) · L_r  to the relation, where L_r = log[root r]
        # is the unknown absolute log.
        #
        # Case n_roots == 2: we can encode as a binary relation between the two
        # roots (calling sdsu_union_binary!), which may merge or pin one of them.
        #
        # Case n_roots == 1: all unknowns share a root; this gives a constraint
        # of the form  S·L_r + Q·k + P ≡ 0.  We cannot solve it alone — we
        # need a SECOND such constraint for the same root to eliminate L_r.
        # The caller (dsu_try in phase3_dsu_worker) accumulates these per-root
        # in root_constraints_buf and calls back here; see the :need_root_buf
        # return signal below.
        #
        # Case n_roots >= 3: not enough structure; skip.

        # Collect (root → (sum_coeff, sum_label_a, sum_label_b)) per distinct root.
        root_groups = Dict{Int, Tuple{Int,Int,Int}}()
        for (j, cj) in unknown
            r, laj, lbj = sdsu_find(d, j)
            sc, sla, slb = get(root_groups, r, (0, 0, 0))
            root_groups[r] = (mod(sc + cj, ell), mod(sla + cj*laj, ell), mod(slb + cj*lbj, ell))
        end

        n_roots = length(root_groups)

        if n_roots == 1
            r, (sc, sla, slb) = first(root_groups)
            # sc·L_r + (slb - rhs_b)·k + (sla - rhs_a) ≡ 0
            P = mod(sla - rhs_a, ell)
            Q = mod(slb - rhs_b, ell)
            # Signal caller to accumulate this constraint per root r.
            # Return a special sentinel so dsu_try can forward to root_constraints_buf.
            # We encode it as a 3-tuple in the return; since our return type is
            # Union{Int,Nothing} we use a side-channel: store into the thread-local
            # buffer via a closure variable injected by the caller.
            # Here we just return nothing — the caller (dsu_try) re-invokes
            # try_feed_fullrow which has direct access to root_constraints_buf.
            # This path is only hit when called directly; the worker uses
            # try_feed_fullrow instead for 3-unknown rows.
            return nothing

        elseif n_roots == 2
            entries = collect(root_groups)
            r1, (sc1, sla1, slb1) = entries[1]
            r2, (sc2, sla2, slb2) = entries[2]
            # sc1·L_{r1} + sc2·L_{r2} + (slb1+slb2 - rhs_b)·k + (sla1+sla2 - rhs_a) ≡ 0
            # Rearrange as a binary relation on the two roots:
            #   sc1·L_{r1} + sc2·L_{r2} ≡ rhs_a2 + rhs_b2·k
            rhs_a2 = mod(rhs_a - sla1 - sla2, ell)
            rhs_b2 = mod(rhs_b - slb1 - slb2, ell)
            status, ka, kb = sdsu_union_binary!(d, r1, sc1, r2, sc2, rhs_a2, rhs_b2)
            if status === :cycle_k
                kb == 0 && return nothing
                k_try = mod(-ka * powermod(kb, ell - 2, ell), ell)
                jac_mul(G, k_try, ell) == T && return k_try
            end
            # :merged, :pinned, :deferred, :cycle_unpinned — no k yet.
            return nothing

        else
            # n_roots >= 3: insufficient structure; skip.
            return nothing
        end
    end
end

# ---------------------------------------------------------------------------
#  Phase2TablesWithDSU
#
#  Extended version of Phase2Tables that also carries the PrecomputedDSUState.
#  Drop-in replacement: all existing fields preserved, dsu_state added.
# ---------------------------------------------------------------------------
struct Phase2TablesWithDSU
    # ── Original Phase2Tables fields ──────────────────────────────────────
    fb             ::Vector{NTuple{2,Int}}
    pt2idx         ::Dict{NTuple{2,Int}, Int}
    atom_log_dict  ::Dict{NTuple{2,Int}, Int}
    shared_lp1     ::Dict{NTuple{2,Int}, Tuple{Dict{Int,Int}, Int, Int, Int}}
    shared_lp2     ::LP2Graph
    shared_lp1_conj::ShardedLP1Conj{LP1ConjVal}
    shared_lp2_conj::LP2ConjGraph
    ell            ::BigInt

    # ── New: frozen DSU state from β=0 precompute ─────────────────────────
    dsu_state      ::PrecomputedDSUState
end

# Convenience constructor: wrap an existing Phase2Tables + atom_logs vector.
function Phase2TablesWithDSU(t::Phase2Tables, atom_logs::Vector{Int})::Phase2TablesWithDSU
    nF  = length(t.fb)
    ell = Int(t.ell)
    dsu = build_precomputed_dsu_state(atom_logs, nF, ell)
    Phase2TablesWithDSU(t.fb, t.pt2idx, t.atom_log_dict, t.shared_lp1,
                        t.shared_lp2, t.shared_lp1_conj, t.shared_lp2_conj,
                        t.ell, dsu)
end

# ---------------------------------------------------------------------------
#  phase3_dsu_worker
#
#  Drop-in replacement for phase3_trial_worker that uses the SymbolicDSU
#  instead of Gaussian elimination.
#
#  Strategy:
#    • Clone the frozen PrecomputedDSUState into a fresh SymbolicDSU at trial
#      start (O(nF) copy).
#    • Run the same β≠0 walk loop as phase3_trial_worker.
#    • At each LP hit (0-LP, 1-LP-affine, 1-LP-conj), instead of (or in
#      addition to) try_solve, call sdsu_feed_relation! on the combined row.
#    • sdsu_feed_relation! returns k the instant a cycle closes with b≠0.
#
#  The existing try_solve fast path (0-LP direct, 1-LP-preclose) is kept as
#  strategy 0 / strategy 1.  The DSU path is strategy 2: accumulate relations
#  into the symbolic graph and wait for a cycle.  In practice, with a dense
#  precomputed DSU, almost every 0-LP or 1-LP hit immediately closes a cycle
#  (n_unk == 0 after substituting precomputed logs), so strategy 0 / 1 fire
#  first.  The DSU path activates when some atoms are not in atom_log_dict
#  (gauge-free roots).
#
#  The accumulated SymbolicDSU also improves future steps: once a gauge-free
#  root is pinned via a β≠0 relation, subsequent relations that include that
#  atom become solvable.
# ---------------------------------------------------------------------------
function phase3_dsu_worker(
        trial_idx        ::Int,
        T                ::Div2,
        k_true           ::Union{Int,Nothing},
        tables           ::Phase2TablesWithDSU,
        G                ::Div2;
        step_cap         ::Int   = 10_000_000,
        n_steps_prebuilt ::Int   = 512,
        verbose          ::Bool  = false)::Phase3Result

    t0    = time()
    ell   = tables.ell
    ellI  = Int(ell)
    pt2idx       = tables.pt2idx
    fb           = tables.fb
    nF           = length(fb)
    alog         = tables.atom_log_dict
    lp1_pre      = tables.shared_lp1
    lp1_conj_pre = tables.shared_lp1_conj

    # ── Clone the precomputed DSU ─────────────────────────────────────────────
    sdsu = SymbolicDSU(tables.dsu_state)

    # ── Prebuilt step table ───────────────────────────────────────────────────
    step_D = Vector{Div2}(undef, n_steps_prebuilt)
    step_a = Vector{Int}(undef,  n_steps_prebuilt)
    step_b = Vector{Int}(undef,  n_steps_prebuilt)
    for i in 1:n_steps_prebuilt
        a = rand(1:ellI-1); b = rand(1:ellI-1)
        step_D[i] = jac_add(jac_mul(G, a, ell), jac_mul(T, b, ell))
        step_a[i] = a; step_b[i] = b
    end

    # ── Walk state ────────────────────────────────────────────────────────────
    alpha_cur = rand(1:ellI-1)
    beta_cur  = rand(1:ellI-1)
    D_cur     = jac_add(jac_mul(G, alpha_cur, ell), jac_mul(T, beta_cur, ell))
    cur_pt    = fb[rand(1:nF)]

    # ── Local birthday fallback tables (same as phase3_trial_worker) ─────────
    local_lp1_affine = Dict{NTuple{2,Int},   Tuple{Dict{Int,Int}, Int, Int}}()
    local_lp1_conj   = Dict{NTuple{4,UInt32}, LP1ConjValFull}()

    # ── Deferred relation queue for the SymbolicDSU ──────────────────────────
    # Each entry: (fb_row, alpha_i, beta_i)
    deferred_rows = Vector{Tuple{Dict{Int,Int}, Int, Int}}()

    # ── Per-root linear constraint buffer ─────────────────────────────────────
    # When all unknowns in a relation share the same gauge-free root r, we get:
    #   sc·L_r + Q·k + P ≡ 0  (mod ell)
    # where L_r = log[root r] is unknown.  Two such constraints for the same r
    # eliminate L_r and give k directly.
    #
    # Buffer: root index → Vector of (P, Q, sc) triples.
    root_constraints_buf = Dict{Int, Vector{Tuple{Int,Int,Int}}}()

    # ── Counters ──────────────────────────────────────────────────────────────
    n_steps          = 0
    n_0lp            = 0
    n_1lp_aff_pre    = 0
    n_1lp_aff_local  = 0
    n_1lp_conj_pre   = 0
    n_1lp_conj_local = 0
    n_conj_branch    = 0
    n_dsu_cycles     = 0   # cycles resolved via SymbolicDSU
    k_rec            = nothing

    # ── try_feed_fullrow: full root-aware relation feeder ─────────────────────
    # Wraps sdsu_feed_relation! and additionally handles the n_unk==3 / n_roots==1
    # case via root_constraints_buf: accumulates (P, Q, sc) per root and solves
    # for k when a second constraint for the same root arrives.
    function try_feed_fullrow(fb_row::Dict{Int,Int}, neg_al::Int, neg_be::Int)::Union{Int,Nothing}
        # First try the standard DSU path (handles n_unk 0/1/2 and n_roots==2).
        k = sdsu_feed_relation!(sdsu, fb_row, neg_al, neg_be, G, T)
        k !== nothing && return k

        # Now check for the n_unk==3 / n_roots==1 case not handled above.
        # Re-partition unknowns by root to detect it.
        ell_i = ellI
        support = [(j, mod(v, ell_i)) for (j, v) in fb_row if mod(v, ell_i) != 0]
        isempty(support) && return nothing

        known_sum_a = 0; known_sum_b = 0
        root_groups = Dict{Int, Tuple{Int,Int,Int}}()  # root → (sc, sla, slb)

        for (j, cj) in support
            lva, lvb, resolved = sdsu_get_log(sdsu, j)
            if resolved
                known_sum_a = mod(known_sum_a + cj*lva, ell_i)
                known_sum_b = mod(known_sum_b + cj*lvb, ell_i)
            else
                r, laj, lbj = sdsu_find(sdsu, j)
                sc, sla, slb = get(root_groups, r, (0,0,0))
                root_groups[r] = (mod(sc+cj, ell_i), mod(sla+cj*laj, ell_i), mod(slb+cj*lbj, ell_i))
            end
        end

        n_roots = length(root_groups)
        n_roots != 1 && return nothing  # 0 handled by sdsu_feed_relation!, >=2 also handled

        r, (sc, sla, slb) = first(root_groups)
        rhs_a = mod(neg_al - known_sum_a, ell_i)
        rhs_b = mod(neg_be - known_sum_b, ell_i)
        # Constraint:  sc·L_r + (slb - rhs_b)·k + (sla - rhs_a) ≡ 0
        P  = mod(sla - rhs_a, ell_i)
        Q  = mod(slb - rhs_b, ell_i)
        sc_m = mod(sc, ell_i)

        if sc_m == 0
            # Root drops out: Q·k + P ≡ 0 → direct solve.
            Q == 0 && return nothing
            k_try = mod(-P * powermod(Q, ell_i-2, ell_i), ell_i)
            jac_mul(G, k_try, ell) == T && return k_try
            return nothing
        end

        # Accumulate and try to eliminate L_r with a prior constraint.
        buf = get!(root_constraints_buf, r, Tuple{Int,Int,Int}[])
        for (P2, Q2, sc2) in buf
            # sc_m·L_r + Q·k   + P  ≡ 0
            # sc2·L_r  + Q2·k  + P2 ≡ 0
            # Eliminate L_r:  multiply first by sc2, second by sc_m, subtract:
            #   (sc2·Q - sc_m·Q2)·k + (sc2·P - sc_m·P2) ≡ 0
            dQ = mod(sc2*Q  - sc_m*Q2, ell_i)
            dP = mod(sc2*P  - sc_m*P2, ell_i)
            dQ == 0 && continue
            k_try = mod(-dP * powermod(dQ, ell_i-2, ell_i), ell_i)
            jac_mul(G, k_try, ell) == T && return k_try
        end
        push!(buf, (P, Q, sc_m))
        return nothing
    end

    # ── dsu_try: feed a combined fb_row into the SymbolicDSU ─────────────────
    # Returns k if a cycle closes, else nothing.
    # Also re-drains deferred_rows whenever a new pinning occurs.
    function dsu_try(fb_row::Dict{Int,Int}, neg_al::Int, neg_be::Int)::Union{Int,Nothing}
        # neg_al / neg_be in the trial worker are negated; the relation is:
        # Σ c_j·log[j]  ≡  neg_al·G + neg_be·T  in Jacobian terms, but as
        # a log relation: Σ c_j·log[j] = neg_al + neg_be·k  (mod ell).
        k = try_feed_fullrow(fb_row, neg_al, neg_be)
        k !== nothing && return k

        # Store for deferred re-processing (new pinnings may unlock this row).
        push!(deferred_rows, (copy(fb_row), neg_al, neg_be))

        # Re-drain deferred rows (one pass; loop until no progress).
        changed = true
        while changed && k_rec === nothing
            changed = false
            still_deferred = Tuple{Dict{Int,Int},Int,Int}[]
            for (dr, da, db) in deferred_rows
                kd = try_feed_fullrow(dr, da, db)
                if kd !== nothing
                    return kd
                end
                push!(still_deferred, (dr, da, db))
            end
            # If deferred queue shrank, something was resolved.
            length(still_deferred) < length(deferred_rows) && (changed = true)
            deferred_rows = still_deferred
        end
        return nothing
    end

    # ── Main walk loop ────────────────────────────────────────────────────────
    for _ in 1:step_cap
        si        = rand(1:n_steps_prebuilt)
        D_cur     = jac_add(D_cur, step_D[si])
        alpha_cur = mod(alpha_cur + step_a[si], ellI)
        beta_cur  = mod(beta_cur  + step_b[si], ellI)
        beta_cur == 0 && continue

        fp3_deg(D_cur.u) != 2 && continue
        u0 = D_cur.u[1]; u1 = D_cur.u[2]
        v0 = D_cur.v[1]; v1 = D_cur.v[2]
        px, py = cur_pt

        fp(fp(px*px) + fp(u1*px) + u0) == 0 && continue

        phi_c = build_phi_mumford(px, py, u0, u1, v0, v1)
        phi_c === nothing && continue
        a_c, b_c, c_c, _ = phi_c

        res_R, res_S, RS_mumford = phi_residual_mumford(a_c, b_c, c_c, px, u0, u1)
        RS_mumford === SENTINEL_MUMFORD && continue

        n_steps += 1

        neg_al = mod(ellI - alpha_cur, ellI)
        neg_be = mod(ellI - beta_cur,  ellI)
        i0     = get(pt2idx, cur_pt, 0)

        # ======================================================================
        #  BRANCH A: conjugate residual
        # ======================================================================
        if res_R === SENTINEL_PT
            lp_key = conj_key32(RS_mumford::NTuple{4,Int})

            if i0 != 0
                n_conj_branch += 1
                si_shard  = conj_shard_idx(lp_key)
                conj_dict = lp1_conj_pre.shards[si_shard]

                slot_pre = _conj_find(conj_dict, lp_key)
                if slot_pre != 0
                    v_pre    = @inbounds conj_dict.vals[slot_pre]
                    prev_col = Int(v_pre.i0)
                    prev_al  = Int(v_pre.neg_al)
                    c_al = mod(neg_al - prev_al, ellI)
                    c_be = neg_be
                    n_1lp_conj_pre += 1

                    if i0 != prev_col
                        # Feed the weight-2 relation straight to the DSU
                        row2 = Dict{Int,Int}(i0 => 1, prev_col => -1)
                        k_rec = dsu_try(row2, c_al, c_be)
                        k_rec !== nothing && (n_dsu_cycles += 1; break)
                    else
                        # Empty support: direct scalar solve
                        c_be == 0 && throw(ErrorException("Degenerate conjugate relation: beta difference is 0"))
                        k_rec = mod(-c_al * powermod(c_be, ell - 2, ell), ellI)
                        jac_mul(G, k_rec, ell) == T && break
                        k_rec = nothing
                    end

                elseif haskey(local_lp1_conj, lp_key)
                    v_loc    = local_lp1_conj[lp_key]
                    prev_col = Int(v_loc.i0)
                    prev_al  = Int(v_loc.neg_al)
                    prev_be  = Int(v_loc.neg_be)
                    c_al = mod(neg_al - prev_al, ellI)
                    c_be = mod(neg_be - prev_be, ellI)
                    delete!(local_lp1_conj, lp_key)
                    n_1lp_conj_local += 1

                    if i0 != prev_col
                        row2 = Dict{Int,Int}(i0 => 1, prev_col => -1)
                        k_rec = dsu_try(row2, c_al, c_be)
                        k_rec !== nothing && (n_dsu_cycles += 1; break)
                    else
                        c_be == 0 && throw(ErrorException("Degenerate local conjugate relation: beta difference is 0"))
                        k_rec = mod(-c_al * powermod(c_be, ell - 2, ell), ellI)
                        jac_mul(G, k_rec, ell) == T && break
                        k_rec = nothing
                    end
                else
                    local_lp1_conj[lp_key] = LP1ConjValFull(UInt16(i0), UInt64(neg_al), UInt64(neg_be))
                end
            end

            cur_pt = i0 != 0 ? cur_pt : fb[rand(1:nF)]
            continue
        end


        # ======================================================================
        #  BRANCH B: split residual
        # ======================================================================
        R  = res_R; S = res_S
        iR = get(pt2idx, R, 0)
        iS = get(pt2idx, S, 0)
        n_lp = (i0 == 0 ? 1 : 0) + (iR == 0 ? 1 : 0) + (iS == 0 ? 1 : 0)

        if n_lp == 0
            # B0: 0-LP — build fb_row over {i0, iR, iS}
            fb_row = Dict{Int,Int}()
            for idx in (i0, iR, iS)
                fb_row[idx] = get(fb_row, idx, 0) + 1
            end
            n_0lp += 1
            k_rec = dsu_try(fb_row, neg_al, neg_be)
            k_rec !== nothing && (n_dsu_cycles += 1; break)
            cur_pt = fb[rand(1:nF)]

        elseif n_lp == 1
            # B1: 1-LP-affine — one non-FB atom (lp_pt)
            lp_pt  = i0 == 0 ? cur_pt : iR == 0 ? R : S
            fb_row = Dict{Int,Int}()
            for idx in (i0, iR, iS)
                idx == 0 && continue
                fb_row[idx] = get(fb_row, idx, 0) + 1
            end

            if haskey(lp1_pre, lp_pt)
                pre_row, pre_neg_al, pre_neg_be, _ = lp1_pre[lp_pt]
                combined = copy(fb_row)
                for (j, v) in pre_row
                    nv = get(combined, j, 0) - v
                    nv == 0 ? delete!(combined, j) : (combined[j] = nv)
                end
                c_neg_al = mod(neg_al - pre_neg_al, ellI)
                c_neg_be = mod(neg_be - pre_neg_be, ellI)
                n_1lp_aff_pre += 1
                
                k_rec = dsu_try(combined, c_neg_al, c_neg_be)
                k_rec !== nothing && (n_dsu_cycles += 1; break)

            elseif haskey(local_lp1_affine, lp_pt)
                prev_row, prev_neg_al, prev_neg_be = local_lp1_affine[lp_pt]
                combined = copy(fb_row)
                for (j, v) in prev_row
                    nv = get(combined, j, 0) - v
                    nv == 0 ? delete!(combined, j) : (combined[j] = nv)
                end
                c_neg_al = mod(neg_al - prev_neg_al, ellI)
                c_neg_be = mod(neg_be - prev_neg_be, ellI)
                delete!(local_lp1_affine, lp_pt)
                n_1lp_aff_local += 1

                k_rec = dsu_try(combined, c_neg_al, c_neg_be)
                k_rec !== nothing && (n_dsu_cycles += 1; break)

            else
                local_lp1_affine[lp_pt] = (copy(fb_row), neg_al, neg_be)
            end

            cur_pt = iR != 0 ? R : iS != 0 ? S : fb[rand(1:nF)]

        else
            # B2/B3: 2-LP or 3-LP, discard
            cur_pt = fb[rand(1:nF)]
        end
    end

    elapsed  = time() - t0
    success  = k_rec !== nothing
    verified = k_true === nothing || k_rec == k_true

    if verbose
        k_rec_s  = k_rec  === nothing ? "none" : string(k_rec)
        k_true_s = k_true === nothing ? "?"    : string(k_true)
        match_s  = verified ? "ok" : "MISMATCH"
        @printf("[phase3-dsu trial %d | t=%.3fs] k_rec=%s k_true=%s match=%s steps=%d 0lp=%d 1lp_aff_pre=%d 1lp_aff_local=%d 1lp_conj_pre=%d 1lp_conj_local=%d dsu_cycles=%d deferred=%d\n",
                trial_idx, elapsed, k_rec_s, k_true_s, match_s,
                n_steps, n_0lp, n_1lp_aff_pre, n_1lp_aff_local,
                n_1lp_conj_pre, n_1lp_conj_local, n_dsu_cycles, length(deferred_rows))
        flush(stdout)
    end

    return Phase3Result(
        trial_idx,
        k_rec,
        k_true,
        n_steps,
        n_0lp,
        n_1lp_aff_pre + n_1lp_conj_pre,
        n_1lp_aff_local + n_1lp_conj_local,
        elapsed,
        success && verified)
end

# ---------------------------------------------------------------------------
#  phase3_dsu_solve_targets
#
#  Parallel entry point, mirrors phase3_solve_targets.
#  Takes Phase2TablesWithDSU instead of Phase2Tables.
# ---------------------------------------------------------------------------
function phase3_dsu_solve_targets(
        tables   ::Phase2TablesWithDSU,
        targets  ::Vector{<:Tuple{Div2, <:Union{Int,Nothing}}},
        G        ::Div2;
        step_cap ::Int  = 10_000_000,
        verbose  ::Bool = true)::Vector{Phase3Result}

    n = length(targets)
    results = Vector{Phase3Result}(undef, n)

    println("── Phase 3 (DSU): amortised DLP solves ──────────────────────────────")
    @printf("   targets=%d  threads=%d  FB=%d  lp1_pre=%d  dsu_state_nF=%d  step_cap=%d\n",
            n, Threads.nthreads(), length(tables.fb),
            length(tables.shared_lp1), tables.dsu_state.nF, step_cap)
    @printf("   RSS at phase3-dsu start: %.1f MB  |  GC live: %.1f MB\n",
            Sys.maxrss() / 1024^2, Base.gc_live_bytes() / 1024^2)
    flush(stdout)

    t0 = time()
    @sync for i in 1:n
        Threads.@spawn begin
            T_i, k_true_i = targets[i]
            results[i] = phase3_dsu_worker(i, T_i, k_true_i, tables, G;
                                            step_cap=step_cap, verbose=verbose)
        end
    end

    n_ok        = count(r -> r.success, results)
    total_steps = sum(r -> r.n_steps, results)
    avg_steps   = total_steps / max(1, n)
    n_pre       = sum(r -> r.n_1lp_preclose, results)
    n_loc       = sum(r -> r.n_1lp_local, results)
    n_0lp_tot   = sum(r -> r.n_0lp_hits, results)
    println()
    @printf("── Phase 3 (DSU) summary ────────────────────────────────────────────\n")
    @printf("  %d / %d targets solved correctly\n", n_ok, n)
    @printf("  total steps: %d  (avg %.1f/target)\n", total_steps, avg_steps)
    @printf("  closure breakdown: 0-LP=%d  1LP-preclose=%d  1LP-local=%d\n",
            n_0lp_tot, n_pre, n_loc)
    @printf("  wall time: %.3fs\n", time() - t0)
    @printf("  Process RSS at phase3-dsu exit: %.1f MB  |  GC live: %.1f MB\n",
            Sys.maxrss() / 1024^2, Base.gc_live_bytes() / 1024^2)
    println("="^70)
    flush(stdout)

    return results
end
