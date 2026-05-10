
using Oscar, Hecke

println("=== Oscar symbols matching 'poly' or 'zeta' ===")
for n in sort(names(Oscar, all=true))
    s = string(n)
    if occursin(r"(?i)poly|zeta|lser|weil|froben|jacobi", s) && occursin(r"(?i)l_|lpoly|zeta|weil", s)
        println("  Oscar.", s)
    end
end

println("\n=== Hecke symbols matching 'poly' or 'zeta' ===")
for n in sort(names(Hecke, all=true))
    s = string(n)
    if occursin(r"(?i)poly|zeta|lser|weil|froben|jacobi", s) && occursin(r"(?i)l_|lpoly|zeta|weil", s)
        println("  Hecke.", s)
    end
end

println("\n=== Oscar hyperelliptic-related ===")
for n in sort(names(Oscar, all=true))
    s = string(n)
    occursin(r"(?i)hyperelliptic|hypell|genus2", s) && println("  Oscar.", s)
end

println("\n=== Hecke hyperelliptic-related ===")
for n in sort(names(Hecke, all=true))
    s = string(n)
    occursin(r"(?i)hyperelliptic|hypell|genus2", s) && println("  Hecke.", s)
end
