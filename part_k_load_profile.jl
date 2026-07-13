#!/usr/bin/env julia
################################################################################
#  part_k_load_profile.jl  --  isolate "reading bytes off disk" from
#  "Oscar reconstructing the polynomial object" for one term file, so we
#  know whether switching serialization formats (e.g. to HDF5, or to a
#  hand-rolled binary format) would actually help, or whether the cost is
#  inherent to rebuilding a 17M-term MPoly term-by-term regardless of how
#  the bytes got onto disk.
#
#  Usage:
#      julia part_k_load_profile.jl <term_file>
################################################################################

using Oscar

term_file = length(ARGS) >= 1 ? ARGS[1] :
    joinpath(@__DIR__, "part_k_results", "U0_summand_1.stats.term.oscar")

isfile(term_file) || error("not found: $term_file")

filesize_bytes = filesize(term_file)
println("file: ", term_file)
println("size: ", round(filesize_bytes / 1024^2, digits=1), " MiB")

println("\n-- raw file read (just bytes into memory, no parsing) --")
t0 = time()
raw = read(term_file)
t_read = time() - t0
println("  raw read: ", round(t_read, digits=3), "s  (",
        round(filesize_bytes / 1024^2 / t_read, digits=1), " MiB/s)")

println("\n-- full Oscar load() (read + parse + reconstruct polynomial) --")
t0 = time()
p = load(term_file)
t_load = time() - t0
println("  full load: ", round(t_load, digits=3), "s")
println("  degree=", total_degree(p), " terms=", length(terms(p)))

println("\n-- summary --")
println("  raw I/O:         ", round(t_read, digits=3), "s")
println("  parse+reconstruct (inferred): ", round(t_load - t_read, digits=3), "s")
println("  fraction spent NOT on raw I/O: ",
        round(100 * (t_load - t_read) / t_load, digits=1), "%")
