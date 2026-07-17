#!/usr/bin/env julia
#
# test_shard_coeff_roundtrip.jl
#
# Standalone smoke test for the ONE unverified API call in the new
# flat-binary shard format: `lift(ZZ, x)` converting an FqFieldElem
# back to a plain integer. This has NOT been run (no Julia available
# where it was written) -- run this BEFORE trusting save_shard_native/
# load_shard_native on real 17.8M-term shards, since a wrong conversion
# here would silently corrupt every coefficient (wrap to the wrong
# residue) rather than error.
#
# USAGE: julia test_shard_coeff_roundtrip.jl
# Expected output: "ALL ROUNDTRIPS OK" and nothing else unusual.
# If it errors or prints a mismatch, the lift(ZZ, ...) call in
# elim2.jl's save_shard_native needs to be replaced with whatever this
# script shows DOES work.

using Oscar

const p = 2371157
F = GF(p)
Rcoef, (a1_c, a2_c, b1_c, b2_c) = polynomial_ring(F, ["a1", "a2", "b1", "b2"])

test_values = [0, 1, 2, p - 1, p ÷ 2, 12345, 2000000]

println("Testing lift(ZZ, ...) roundtrip for F=GF($p)...")
for v in test_values
    elt = F(v)
    lifted = lift(ZZ, elt)
    back = Int(lifted)
    if back != v
        error("MISMATCH: F($v) -> lift(ZZ,...) -> Int gave $back, expected $v -- " *
              "the lift(ZZ, ...) call in save_shard_native is WRONG for this " *
              "Oscar version and must be replaced before running on real shards")
    end
    println("  F($v) -> lift(ZZ,...) -> $back  OK")
end

# Also test round-tripping through a real polynomial term, since that's
# the actual code path (coefficients(poly) elements, not raw F(v) calls).
test_poly = a1_c^2 * b1_c + F(999999) * a2_c
for c in coefficients(test_poly)
    lifted = lift(ZZ, c)
    back = Int(lifted)
    reconstructed = F(back)
    if reconstructed != c
        error("MISMATCH on real polynomial coefficient: lift(ZZ, $c) -> " *
              "$back -> F($back) = $reconstructed != original $c")
    end
    println("  polynomial coeff $c -> lift(ZZ,...) -> $back -> F(...) roundtrips OK")
end

println("ALL ROUNDTRIPS OK")
