# =============================================================================
#  lp1_conj_lsm_topk.jl — Top-K multiplicity reservoir for LP1ConjLSMStore
#
#  Min-heap reservoir tracking the TOPK_K keys with highest observed emission
#  count across all store+close events.
#
#  Thread safety: all mutations must be called under the owner LSM's bday_lock.
#
#  Heap invariant: heap[1] is the key with the LOWEST count among the top-K
#  (so we can quickly decide whether to evict it).
#  Entry layout: (count::Int, key::CanonicalLP1Key)
# =============================================================================

mutable struct TopKMultiplicity
    heap    ::Vector{Tuple{Int, CanonicalLP1Key}}   # (count, key), min-heap on count
    index   ::Dict{CanonicalLP1Key, Int}            # key → heap position (1-based)
    total_keys_seen ::Int                           # distinct keys ever submitted
end

function TopKMultiplicity()
    TopKMultiplicity(
        sizehint!(Tuple{Int,CanonicalLP1Key}[], TOPK_K + 4),
        sizehint!(Dict{CanonicalLP1Key,Int}(), TOPK_K * 2),
        0
    )
end

# --- Min-heap helpers (count-keyed) ---

@inline function _topk_parent(i::Int)::Int; i >> 1; end
@inline function _topk_left(i::Int)::Int;  i << 1; end
@inline function _topk_right(i::Int)::Int; (i << 1) | 1; end

function _topk_swap!(tk::TopKMultiplicity, i::Int, j::Int)
    h = tk.heap
    ki = h[i][2]; kj = h[j][2]
    h[i], h[j] = h[j], h[i]
    tk.index[ki] = j
    tk.index[kj] = i
    nothing
end

function _topk_sift_up!(tk::TopKMultiplicity, i::Int)
    h = tk.heap
    while i > 1
        p = _topk_parent(i)
        h[p][1] <= h[i][1] && break
        _topk_swap!(tk, p, i)
        i = p
    end
    nothing
end

function _topk_sift_down!(tk::TopKMultiplicity, i::Int)
    h = tk.heap; n = length(h)
    while true
        lo = i
        l = _topk_left(i);  l <= n && h[l][1] < h[lo][1] && (lo = l)
        r = _topk_right(i); r <= n && h[r][1] < h[lo][1] && (lo = r)
        lo == i && break
        _topk_swap!(tk, i, lo)
        i = lo
    end
    nothing
end

# Record one emission of `key`.  Must be called under bday_lock.
function _topk_record!(tk::TopKMultiplicity, key::CanonicalLP1Key)
    h = tk.heap
    pos = get(tk.index, key, 0)
    if pos != 0
        # Key already in heap: increment its count and restore heap invariant.
        old_c, k = h[pos]
        h[pos]   = (old_c + 1, k)
        _topk_sift_down!(tk, pos)   # count increased → may need to sift down
        return nothing
    end
    # New key.
    tk.total_keys_seen += 1
    if length(h) < TOPK_K
        # Heap not full yet: just push and sift up.
        push!(h, (1, key))
        new_pos = length(h)
        tk.index[key] = new_pos
        _topk_sift_up!(tk, new_pos)
    else
        # Heap full: only insert if this key would beat the current minimum.
        # A brand-new key starts at count=1; it only beats the minimum if the
        # minimum is also 1 (which would be a wash) — we skip it to avoid
        # churning the heap with singleton keys.
        # Instead, skip if count=1 and heap min is already ≥ 1 (which is always).
        # The meaningful case: key was seen before but fell out (not tracked).
        # We can't recover that, so new keys start at 1 and only enter if min=1.
        min_c = h[1][1]
        if 1 > min_c
            # Evict the minimum.
            evict_key = h[1][2]
            delete!(tk.index, evict_key)
            h[1] = (1, key)
            tk.index[key] = 1
            _topk_sift_down!(tk, 1)
        end
        # else: skip (new key count=1 ≤ min; not worth tracking)
    end
    nothing
end
