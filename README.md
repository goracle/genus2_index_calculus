run like:
julia -t 32 trial3_fixed.jl 1000000
where 32 is threads
1000000 is nearest integer to prime you want for F_p
for basic mode.

for amortized mode, try:
julia -t 32 trial3_fixed.jl 65536 --amortized --n-targets=30

to ignore LP2 terms (usually faster) try option:
--no-lp2

what I usually run:
julia -t 32 trial3_fixed.jl 65536 --no-lp2 --amortized --n-targets=30
