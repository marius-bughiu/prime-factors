# Skipping rejected sums with one small table

The six public checks cut the number of exact square tests, but the first version still visits each original candidate to apply those checks. **One shared table lets the search generate fewer than 6.494% of the original candidates.** Building it for every input and checking the remaining three moduli together take fewer than **10.901 small lookups per 100 original candidates**, summed over the entire balanced 2,048-bit population. The survivors and their order through the correct sum are unchanged. [Generation bound](../PrimeFactors/ThreeSquareWheelWork.lean) · [Correspondence between table entries and visited candidates](../PrimeFactors/SharedThreeSquareScoreWheel.lean)

The earlier search has up to ten streams, each advancing by 100. The first three added tests repeat every 53,361 entries within a stream. Scan the integers $j$ from 0 through 53,360 once, storing $j$ whenever the sum $100j$ passes those three tests. For a stream starting at $z$, its entry $z+100j$ passes exactly when $j+100^{-1}z$ is a stored position modulo 53,361. The inverse exists because 100 and 53,361 are coprime. Every stream can therefore read the same circular list from a different position. Reaching the end advances the stream by one period. [Increasing output, wraparound and completeness](../PrimeFactors/ShiftedScoreSieveCycle.lean)

| Quantity per product | Checked bound |
| --- | ---: |
| Stored positions | At most 3,465 |
| Storage per position | 16 bits, lossless |
| Shared list plus the three remaining bit tables | At most 7,035 bytes |
| List plus all six bit tables during setup | At most 7,060 bytes |
| Small residue checks to construct the list | At most 78,771 |

These byte counts cover the packed table contents. Pointers, counters, the product and large-integer working storage require additional memory. The construction count starts with the six small residue bitsets available and includes the first failing test at each position. Some product remainders attain 78,771 initialization lookups. The 10.901-per-100 bound includes that scan for each eligible input. Building the bitsets, advancing pointers, comparing scores and computing each next sum have separate costs. [Memory, exact initialization count and sharpness](../PrimeFactors/ScoreWheelMemory.lean)

Setup makes a visible difference for small numbers. On $134{,}765{,}977=8{,}233\times16{,}369$, the old search visits 140 sums. The shared list emits five, then eight small lookups leave one exact square test. Building the list costs 70,301 small lookups on this short search. On $8{,}398{,}823=2{,}053\times4{,}091$, three of 35 candidates are emitted, and five further lookups leave one exact square test. The latter example pays the full 78,771 setup lookups. The bounded experiment checks the positions against a direct scan through the true sum, and also checks two complete laps of each example table. [Reproduce the examples](../experiments/shared_sum_phase_table.py)

After the wheel advances, the last three checks still leave exactly the six-screen set. The previous unconditional result therefore continues to apply: fewer than 0.6681% of the old exact square tests in total, and at least $2^{853}$ tests for all but fewer than one in $2^{35}$ inputs. This search still cannot factor ordinary 2,048-bit products practically. [Square counts and remaining work](six-small-checks-before-an-integer-square-test.md)
