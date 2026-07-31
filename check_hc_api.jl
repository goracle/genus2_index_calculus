using HomotopyContinuation
using InteractiveUtils: @which

# ---------------------------------------------------------------------------
# Toy system: a 2D sphere (dim-1 component) union 4 isolated points, so we
# get both a positive-dimensional AND a dimension-0 piece -- exercises the
# same witness_sets(N; dims=[0]) path as the real 12-eq/12-unknown system,
# but finishes in seconds instead of hours.
# ---------------------------------------------------------------------------
@var x y z
# sphere (dim-1 curve on it via a second cutting plane) UNION 4 isolated
# points well off the sphere -- guarantees a real dim-0 result to inspect,
# unlike the previous version of this script which had no dim-0 component
# at all (both f1==f2 meant no genuine intersection cutting it to points).
sphere = x^2 + y^2 + z^2 - 1
plane  = x + y + z
pt1 = (x - 3)^2 + (y - 3)^2 + (z - 3)^2 - 0.0
pt2 = (x - 4)^2 + (y - 4)^2 + (z - 4)^2 - 0.0
F = System([sphere * plane * pt1 * pt2,
            sphere * plane * pt1 * pt2,
            sphere])

println("=" ^ 70)
println("CHECK 1: what does witness_sets(N; dims=[0]) actually return?")
println("=" ^ 70)
N = numerical_irreducible_decomposition(F)
println(N)
println()

raw = witness_sets(N; dims = [0])
println("typeof(raw) = ", typeof(raw))
println("raw = ", raw)
println()

if raw isa Dict
    println(">>> RESULT: witness_sets(N; dims=[0]) returns a Dict{Int,Vector{WitnessSet}}.")
    println(">>> Iterating it with `for entry in raw` yields Pair{Int,Vector{WitnessSet}}")
    println(">>> objects (that's how Dict iteration works in Julia) -- so destructuring")
    println(">>> `dim, wsets = entry` inside the loop, as in Claude's fix, is correct.")
    println(">>> Gemini's flat-vector assumption (reduce(vcat, solutions.(dim0_sets)))")
    println(">>> would fail: solutions() doesn't accept a Vector{WitnessSet} directly")
    println(">>> without first extracting it from the dict's value for key 0.")
    if haskey(raw, 0)
        println(">>> raw[0] has ", length(raw[0]), " witness set(s); solutions.(raw[0]) works.")
    else
        println(">>> No key 0 present -- no dimension-0 component was found in this toy system.")
    end
elseif raw isa AbstractVector{<:WitnessSet}
    println(">>> RESULT: witness_sets(N; dims=[0]) returns a flat Vector{WitnessSet}.")
elseif raw isa AbstractVector && !isempty(raw) && first(raw) isa Pair
    println(">>> RESULT: witness_sets(N; dims=[0]) returns a Vector of Pair(s).")
else
    println(">>> RESULT: something else entirely -- inspect `raw` above by hand.")
end
println()

println("=" ^ 70)
println("CHECK 2: does numerical_irreducible_decomposition forward")
println("max_trials_u_homotopy, or silently swallow it?")
println("=" ^ 70)
try
    N2 = numerical_irreducible_decomposition(F; max_trials_u_homotopy = 15)
    println(">>> Call succeeded with no error. This does NOT by itself prove the")
    println(">>> kwarg was actually used (Julia's `options...` splatting can accept")
    println(">>> an unrecognized kwarg without erroring if it's forwarded blindly")
    println(">>> into a Dict, then never consumed). Cross-check against CHECK 3 below.")
catch e
    println(">>> Call THREW an error -- max_trials_u_homotopy is NOT accepted here:")
    println(">>> ", sprint(showerror, e))
    println(">>> Do not pass this kwarg to numerical_irreducible_decomposition directly.")
    println(">>> It may still be usable via a nested options struct -- see CHECK 3.")
end
println()

println("=" ^ 70)
println("CHECK 3: @edit / @which -- find the real method and its true signature")
println("=" ^ 70)
println("Run these two lines yourself in the REPL (not scriptable non-interactively --")
println("@edit opens your \$EDITOR on the actual source file/line, @which just prints it):")
println()
println("    @which numerical_irreducible_decomposition(F)")
println("    @edit  numerical_irreducible_decomposition(F)")
println()
println("@which prints the method signature + file/line without opening an editor --")
println("run that first if you just want the file/line printed to stdout.")
m = @which numerical_irreducible_decomposition(F)
println("@which says: ", m)
println()
println("Now open that file at that line and read the actual options-handling code")
println("to see whether max_trials_u_homotopy is destructured explicitly or just")
println("passed through in a catch-all `options...` / `kwargs...` that regeneration()")
println("consumes internally. That's the only way to know for certain -- the")
println("docstring only lists numerical_irreducible_decomposition's OWN documented")
println("options, not what it silently forwards to functions it calls internally.")
