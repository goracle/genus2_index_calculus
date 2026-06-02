# =============================================================================
#  lp1_conj_lsm_bloom.jl — Bloom filter for LP1ConjLSM
#
#  Lockless gate in front of disk probes.  Bits are only ever set, never
#  cleared, so stale reads produce false positives (safe) but never false
#  negatives (which would be a correctness bug).
# =============================================================================

mutable struct BloomFilter
    bits    ::Vector{UInt64}
    n_bits  ::Int
end

function BloomFilter(capacity::Int; bits_per_entry::Int = 8)
    n_bits = max(64, capacity * bits_per_entry)
    BloomFilter(zeros(UInt64, cld(n_bits, 64)), n_bits)
end

@inline function _bloom_hashes(bf::BloomFilter, fp::UInt64)
    h1 = fp * 0x9e3779b97f4a7c15
    h2 = fp * 0x6c62272e07bb0142
    h3 = h1 ⊻ (h2 >> 17)
    n  = UInt64(bf.n_bits)
    (Int(h1 % n) + 1, Int(h2 % n) + 1, Int(h3 % n) + 1)
end

@inline function bloom_maybe_has(bf::BloomFilter, fp::UInt64)::Bool
    b1, b2, b3 = _bloom_hashes(bf, fp)
    bits = bf.bits
    @inbounds begin
        w1, r1 = divrem(b1 - 1, 64)
        (bits[w1+1] >> r1) & UInt64(1) == 0 && return false
        w2, r2 = divrem(b2 - 1, 64)
        (bits[w2+1] >> r2) & UInt64(1) == 0 && return false
        w3, r3 = divrem(b3 - 1, 64)
        (bits[w3+1] >> r3) & UInt64(1) == 0 && return false
    end
    true
end

function set_bloom!(bf::BloomFilter, fp::UInt64)
    b1, b2, b3 = _bloom_hashes(bf, fp)
    bits = bf.bits
    @inbounds begin
        w1, r1 = divrem(b1 - 1, 64); bits[w1+1] |= UInt64(1) << r1
        w2, r2 = divrem(b2 - 1, 64); bits[w2+1] |= UInt64(1) << r2
        w3, r3 = divrem(b3 - 1, 64); bits[w3+1] |= UInt64(1) << r3
    end
    nothing
end
