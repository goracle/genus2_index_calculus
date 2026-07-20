#!/usr/bin/env julia
#
# convert_to_native.jl
#
# ONE-TIME converter: reads an Oscar .oscar/.mrdi polynomial file DIRECTLY AS
# BYTES -- never through Oscar.load / JSON3 / any generic JSON parser that
# would materialize the whole document (or the whole MPolyRingElem object
# graph) in memory at once -- and writes a flat native binary file.
#
# Two output formats are supported, selected by whether a prime modulus is
# given on the command line:
#
#   - No prime given: "NEWTPOL1" v1 (exponents only, coefficients scanned
#     past and discarded). This is what every prior run of this script
#     produced, and `load_native_support` in newton_polytope.jl still reads
#     it -- Newton-polytope analysis never needed coefficients.
#   - Prime given: "NEWTPOL2" v2 (exponents AND coefficients, coefficients
#     stored as canonical non-negative residues mod p in UInt64). This is
#     for the numerical evaluation-interpolation elimination approach
#     (interpolate_elimination.jl), which specializes the actual polynomial
#     at field points and therefore needs real coefficient values, not just
#     the monomial support.
#
# WHY A HAND-ROLLED SCANNER IS SAFE HERE (and not "fragile improvisation"):
# this file's schema was inspected directly (see inspect_schema.jl output)
# and is extremely regular for the object we care about:
#
#   {"_ns":{...}, "_type":{"name":"MPolyRingElem", "params":"<uuid>"},
#    "data":[[["e1","e2","e3","e4"],"coeff"], ..., [["e1",...],"coeff"]],
#    "_refs":{"<uuid>":{...ring context, irrelevant here...}}}
#
# i.e. "data" is a flat JSON array of exactly [exponent_vector, coeff_string]
# pairs, exponents as decimal-string integers, coefficients as a decimal
# string too (Oscar's GF(p) element serialization -- observed as the
# canonical non-negative residue in [0, p), but this converter defensively
# also accepts a leading '-' and reduces mod p rather than assuming the
# sign convention), no nesting beyond that, no polymorphic term encoding.
# This scanner exploits exactly that regularity: it looks for the literal
# `"data":[` opening marker, then repeatedly matches the fixed pattern
# `[[..,..,..,..],"..."]` term-by-term until it hits the closing `]` of the
# data array, ignoring everything before/after (the "_ns"/"_type" header and
# the "_refs" footer are never parsed as JSON -- only byte-scanned past). It
# does NOT attempt to be a general JSON parser; it is not used as one, and it
# explicitly refuses (raises) if the file's ambient dimension doesn't match
# what's expected or if a term doesn't match the expected shape.
#
# This is fine as a one-shot conversion because:
#   1. it never buffers more than the current term's bytes plus the output
#      IO buffer -- true streaming, same discipline as save_shard_native /
#      load_shard_native in elim2.jl;
#   2. the resulting native file is then the thing all subsequent Newton
#      polytope / interpolation runs load, so this scanner runs exactly
#      once per resultant.
#
# Output format ("NEWTPOL1" v1 flat binary, unchanged from before):
#   magic       :: UInt64  (0x4E455754504F4C31, ASCII "NEWTPOL1")
#   ambient_dim :: Int64
#   n_terms     :: Int64  (placeholder, patched at the end once counted)
#   exps        :: Int32, ambient_dim * n_terms values, row-major
#     (term i's exponents at indices ambient_dim*i+1 .. ambient_dim*i+ambient_dim)
#
# Output format ("NEWTPOL2" v2 flat binary, new):
#   magic       :: UInt64  (0x4E455754504F4C32, ASCII "NEWTPOL2")
#   ambient_dim :: Int64
#   n_terms     :: Int64  (placeholder, patched at the end once counted)
#   prime       :: UInt64 (the GF(p) modulus every coefficient was reduced against)
#   exps        :: Int32, ambient_dim * n_terms values, row-major (same layout as v1)
#   coeffs      :: UInt64, n_terms values, coeffs[i] = canonical residue of
#                  term i's coefficient in [0, prime), in the SAME term order
#                  as the exponent block (so coeffs[i] pairs with
#                  exps[ambient_dim*(i-1)+1 .. ambient_dim*i])
#
# Usage:
#   julia convert_to_native.jl <input.oscar> <output.native> [ambient_dim] [prime]
#
# ambient_dim is optional; if omitted it is inferred from the first term
# encountered (and every subsequent term is checked against it). To get an
# ambient_dim of "infer" while still passing a prime, pass 0 for
# ambient_dim.
#
# prime is optional; if omitted (or if only 3 args are given), the v1
# exponents-only format is written, exactly as before. If given, the v2
# format is written and every coefficient is required to fit as a residue
# mod p that itself fits in a UInt64 (p < 2^64) -- this converter refuses
# rather than silently truncating if a reduced coefficient somehow doesn't
# fit, which should never happen for a genuine residue mod a < 2^64 prime
# but is checked anyway per this project's "raise, don't silently swallow"
# convention.

const NATIVE_MAGIC = UInt64(0x4E455754504F4C31)    # ASCII "NEWTPOL1" -- v1, exponents only
const NATIVE_MAGIC_V2 = UInt64(0x4E455754504F4C32)  # ASCII "NEWTPOL2" -- v2, exponents + coefficients
const NATIVE_EXP_TYPE = Int32
const NATIVE_COEFF_TYPE = UInt64

# ---------------------------------------------------------------------------
# Low-level byte scanner helpers
# ---------------------------------------------------------------------------

# Reads the whole input file as one Vector{UInt8}. NOTE: this DOES hold the
# raw file bytes in memory at once (a 560 MB file is fine; this is not the
# same failure mode as Oscar.load, which built a full parsed JSON DOM PLUS a
# full MPolyRingElem term-object graph -- multiple heap-object-per-term
# structures layered on top of the bytes). If input files grow to the point
# where even the raw bytes don't fit, this function is the one to convert to
# a chunked/mmap read -- flagged here rather than silently assumed fine at
# any size.
function read_all_bytes(path)
    fsize = filesize(path)
    println("  reading ", round(fsize / 1024 / 1024, digits=1), " MB into memory (raw bytes only)...")
    flush(stdout)
    return open(path, "r") do io
        buf = Vector{UInt8}(undef, fsize)
        nread = readbytes!(io, buf, fsize)
        nread == fsize ||
            error("read_all_bytes: expected to read $fsize bytes from $path, got $nread")
        buf
    end
end

# Find the byte offset (1-based, pointing at the byte AFTER the match) of the
# literal ASCII marker `needle` within `buf`, starting the search at `from`.
# Raises if not found -- callers should never silently proceed past a
# missing structural marker.
function find_marker(buf::Vector{UInt8}, needle::String, from::Int; context::String="")
    nb = codeunits(needle)
    n = length(nb)
    m = length(buf)
    i = from
    while i + n - 1 <= m
        matched = true
        @inbounds for j in 1:n
            if buf[i + j - 1] != nb[j]
                matched = false
                break
            end
        end
        matched && return i + n
        i += 1
    end
    error("find_marker: could not locate marker $(repr(needle)) starting from " *
          "byte offset $from" * (isempty(context) ? "" : " ($context)") *
          " -- file does not match the expected schema (see inspect_schema.jl " *
          "output before trusting this converter against a new file)")
end

# Parse an ASCII decimal integer (optionally signed) starting at buf[pos],
# stopping at the first non-digit byte. Returns (value::Int, next_pos::Int).
# Raises if pos does not point at a digit or '-'.
function parse_int_at(buf::Vector{UInt8}, pos::Int)
    m = length(buf)
    start = pos
    neg = false
    if pos <= m && buf[pos] == UInt8('-')
        neg = true
        pos += 1
    end
    digit_start = pos
    val = 0
    while pos <= m && UInt8('0') <= buf[pos] <= UInt8('9')
        val = val * 10 + Int(buf[pos] - UInt8('0'))
        pos += 1
    end
    pos == digit_start &&
        error("parse_int_at: no digits found at byte offset $start " *
              "(byte value: $(pos <= m ? buf[pos] : missing)) -- malformed or " *
              "unexpected content, refusing to guess")
    return (neg ? -val : val, pos)
end

# ---------------------------------------------------------------------------
# Term scanner
# ---------------------------------------------------------------------------

# Scans one term of the form  [["e1","e2",...,"eK"],"coeff"]  starting at
# buf[pos] (pos must point at the opening '[' of the term). Returns
# (exponents::Vector{Int}, coeff_range::UnitRange{Int}, next_pos::Int) where
# next_pos points just past the term's closing ']' and coeff_range is the
# byte range of the coefficient's digits (and possible leading '-') within
# buf, EXCLUDING the surrounding quotes. Callers that only care about
# exponents (v1 / Newton polytope path) simply ignore coeff_range; callers
# that need the coefficient (v2 / interpolation path) parse
# buf[coeff_range] themselves. Either way the coefficient bytes are always
# scanned past correctly to advance pos -- this function never skips work
# based on whether the caller wants the coefficient.
#
# Raises on any deviation from the expected shape rather than trying to
# "recover" -- a malformed term here means the schema assumption is wrong
# and continuing would silently produce wrong exponent/coefficient data.
function scan_term(buf::Vector{UInt8}, pos::Int)
    m = length(buf)
    pos <= m && buf[pos] == UInt8('[') ||
        error("scan_term: expected '[' opening a term at byte offset $pos, " *
              "got $(pos <= m ? Char(buf[pos]) : "EOF")")
    pos += 1  # past outer '['

    pos <= m && buf[pos] == UInt8('[') ||
        error("scan_term: expected '[' opening the exponent-vector array at " *
              "byte offset $pos, got $(pos <= m ? Char(buf[pos]) : "EOF")")
    pos += 1  # past exponent-vector '['

    exps = Int[]
    while true
        pos <= m && buf[pos] == UInt8('"') ||
            error("scan_term: expected '\"' opening an exponent string at " *
                  "byte offset $pos, got $(pos <= m ? Char(buf[pos]) : "EOF")")
        pos += 1  # past opening quote
        (val, pos) = parse_int_at(buf, pos)
        pos <= m && buf[pos] == UInt8('"') ||
            error("scan_term: expected '\"' closing an exponent string at " *
                  "byte offset $pos -- got $(pos <= m ? Char(buf[pos]) : "EOF")")
        pos += 1  # past closing quote
        push!(exps, val)

        pos <= m || error("scan_term: unexpected EOF while scanning exponent vector")
        if buf[pos] == UInt8(',')
            pos += 1
            continue
        elseif buf[pos] == UInt8(']')
            pos += 1  # past exponent-vector ']'
            break
        else
            error("scan_term: expected ',' or ']' after an exponent at byte " *
                  "offset $pos, got $(Char(buf[pos]))")
        end
    end

    pos <= m && buf[pos] == UInt8(',') ||
        error("scan_term: expected ',' between exponent vector and " *
              "coefficient at byte offset $pos, got $(pos <= m ? Char(buf[pos]) : "EOF")")
    pos += 1  # past comma

    pos <= m && buf[pos] == UInt8('"') ||
        error("scan_term: expected '\"' opening the coefficient string at " *
              "byte offset $pos, got $(pos <= m ? Char(buf[pos]) : "EOF")")
    pos += 1
    # Scan the coefficient digits, remembering their byte range so callers
    # that need the coefficient (the v2/interpolation path) can parse it
    # without a second scan over the file; callers that only need exponents
    # (the v1/Newton-polytope path) simply ignore coeff_range.
    coeff_start = pos
    while pos <= m && buf[pos] != UInt8('"')
        pos += 1
    end
    pos <= m ||
        error("scan_term: unterminated coefficient string starting at byte " *
              "offset $coeff_start")
    coeff_range = coeff_start:(pos - 1)
    pos += 1  # past closing quote

    pos <= m && buf[pos] == UInt8(']') ||
        error("scan_term: expected ']' closing the term at byte offset $pos, " *
              "got $(pos <= m ? Char(buf[pos]) : "EOF")")
    pos += 1  # past term's outer ']'

    return (exps, coeff_range, pos)
end

# ---------------------------------------------------------------------------
# Top-level conversion
# ---------------------------------------------------------------------------

function convert_to_native(input_path::String, output_path::String;
                            expected_ambient_dim::Union{Int,Nothing}=nothing,
                            prime::Union{UInt64,Nothing}=nothing)
    isfile(input_path) ||
        error("convert_to_native: no such file: $input_path")

    write_coeffs = prime !== nothing
    if write_coeffs
        prime::UInt64 > 1 ||
            error("convert_to_native: prime=$prime is not a valid modulus " *
                  "(must be > 1) -- pass no prime argument at all for the " *
                  "v1 exponents-only format instead")
    end

    println("Reading raw bytes from: ", input_path)
    buf = read_all_bytes(input_path)
    m = length(buf)

    # Sanity-check the top-level type tag before trusting the rest of the
    # scan -- if this isn't an MPolyRingElem .mrdi file, refuse rather than
    # silently scanning garbage.
    type_marker_pos = find_marker(buf, "\"name\":\"MPolyRingElem\"", 1;
                                   context="expected top-level _type.name to be MPolyRingElem")
    println("  confirmed _type.name == MPolyRingElem")

    data_start = find_marker(buf, "\"data\":[", type_marker_pos;
                              context="looking for the top-level data array opening")
    println("  found \"data\":[ at byte offset ", data_start - 1)

    n_terms = 0
    ambient_dim = expected_ambient_dim
    pos = data_start

    # v2 only: coefficients are buffered here as we scan (n_terms * 8 bytes
    # -- e.g. ~140MB for 17.8M terms -- well within the 13GB budget) and
    # written as a single trailing block AFTER the full exponent block, per
    # the v2 layout in the header comment above. This keeps the exponent
    # block byte-identical between v1 and v2 (same streamed-write discipline
    # as before) rather than interleaving two differently-sized element
    # types term-by-term. Always a concretely-typed Vector{UInt64} (empty
    # and unused in the v1 path) rather than a Union{Vector,Nothing}, so the
    # push! loop below stays type-stable regardless of write_coeffs.
    coeff_buffer = NATIVE_COEFF_TYPE[]

    # Output: stream terms straight to disk as we scan, same discipline as
    # save_shard_native in elim2.jl -- never hold more than the current
    # term's few ints plus the IO buffer. We don't know n_terms up front, so
    # write a placeholder header and patch it via seek() once done (exact
    # same pattern used there).
    mkpath(dirname(output_path))
    open(output_path, "w") do out
        write(out, write_coeffs ? NATIVE_MAGIC_V2 : NATIVE_MAGIC)
        dim_pos = position(out)
        write(out, Int64(ambient_dim === nothing ? 0 : ambient_dim))  # patched below if inferred
        n_terms_pos = position(out)
        write(out, Int64(0))  # placeholder, patched below
        if write_coeffs
            write(out, prime::UInt64)
        end

        while true
            m_pos = pos
            # Stop condition: the data array's closing ']' comes right after
            # the last term with no trailing comma (standard JSON array
            # syntax) -- check for that before attempting to scan another
            # term.
            pos <= m || error("convert_to_native: unexpected EOF while scanning " *
                               "the data array (no closing ']' found)")
            if buf[pos] == UInt8(']')
                pos += 1  # past data array's closing ']'
                break
            end

            (exps, coeff_range, next_pos) = scan_term(buf, pos)

            if ambient_dim === nothing
                ambient_dim = length(exps)
                println("  inferred ambient_dim = ", ambient_dim, " from first term")
                seek(out, dim_pos)
                write(out, Int64(ambient_dim))
                seek(out, n_terms_pos + sizeof(Int64) + (write_coeffs ? sizeof(UInt64) : 0))  # back to end of header
            else
                length(exps) == ambient_dim ||
                    error("convert_to_native: term $n_terms has $(length(exps)) " *
                          "exponents, expected ambient_dim=$ambient_dim (mismatch " *
                          "at byte offset $m_pos) -- refusing to write an " *
                          "inconsistent native file")
            end

            for e in exps
                write(out, NATIVE_EXP_TYPE(e))
            end

            if write_coeffs
                # Parse the coefficient as a (possibly signed) decimal
                # integer directly from the raw bytes -- reuses
                # parse_int_at's digit-scanning logic rather than
                # allocating a String first. Use Int128 as the parsing
                # accumulator since a 64-bit prime's residues can need the
                # full UInt64 range and we must support a leading '-'
                # before reducing mod p.
                (raw_val, after) = parse_int_at(buf, coeff_range.start)
                after - 1 == coeff_range.stop ||
                    error("convert_to_native: coefficient at byte range " *
                          "$coeff_range for term $n_terms did not fully parse " *
                          "as a single decimal integer (parsed through byte " *
                          "$(after-1), range ends at $(coeff_range.stop)) -- " *
                          "unexpected coefficient format, refusing to guess")
                p_big = Int128(prime::UInt64)
                residue = mod(Int128(raw_val), p_big)  # always in [0, p) regardless of raw_val's sign
                residue >= 0 && residue < p_big ||
                    error("convert_to_native: internal error -- mod($raw_val, $prime) " *
                          "produced $residue, not in [0, $prime)")
                push!(coeff_buffer, NATIVE_COEFF_TYPE(residue))
            end

            n_terms += 1

            if n_terms % 5_000_000 == 0
                println("    ", n_terms, " terms converted (byte offset ", next_pos, "/", m, ")")
                flush(stdout)
            end

            pos = next_pos
            pos <= m || error("convert_to_native: unexpected EOF right after term $n_terms " *
                               "(expected ',' or ']' next)")
            if buf[pos] == UInt8(',')
                pos += 1
                continue
            elseif buf[pos] == UInt8(']')
                pos += 1  # past data array's closing ']'
                break
            else
                error("convert_to_native: expected ',' or ']' after term $n_terms " *
                      "at byte offset $pos, got $(Char(buf[pos]))")
            end
        end

        end_pos = position(out)
        seek(out, n_terms_pos)
        write(out, Int64(n_terms))
        seek(out, end_pos)

        if write_coeffs
            length(coeff_buffer::Vector{NATIVE_COEFF_TYPE}) == n_terms ||
                error("convert_to_native: internal error -- coeff_buffer has " *
                      "$(length(coeff_buffer)) entries, expected n_terms=$n_terms " *
                      "-- coefficient count diverged from exponent-term count")
            println("  writing trailing coefficient block (", n_terms, " x 8 bytes)...")
            flush(stdout)
            write(out, coeff_buffer)
        end
    end

    println("Done: ", n_terms, " terms, ambient_dim=", ambient_dim,
             write_coeffs ? " (with coefficients mod $prime)" : "",
             " written to ", output_path)
    println("  output size: ", round(filesize(output_path) / 1024 / 1024, digits=1), " MB")

    return (n_terms=n_terms, ambient_dim=ambient_dim, prime=prime)
end

function main()
    length(ARGS) >= 2 ||
        error("convert_to_native.jl: usage: julia convert_to_native.jl " *
              "<input.oscar> <output.native> [ambient_dim] [prime]")
    input_path = ARGS[1]
    output_path = ARGS[2]
    # ambient_dim=0 means "infer" while still allowing a 4th (prime) arg to
    # be given -- 0 is never a valid ambient_dim so this is unambiguous.
    expected_dim = length(ARGS) >= 3 ? parse(Int, ARGS[3]) : nothing
    expected_dim = (expected_dim == 0) ? nothing : expected_dim
    prime = length(ARGS) >= 4 ? parse(UInt64, ARGS[4]) : nothing

    t0 = time()
    convert_to_native(input_path, output_path; expected_ambient_dim=expected_dim, prime=prime)
    println("Total time: ", round(time() - t0, digits=1), "s")
end

main()
