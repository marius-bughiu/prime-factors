# Generating eligible multipliers with limited memory

All three traversals recovered the factors of the same 24 independently generated products. On the eight products of 24-bit primes, keeping a single weight sequence brought complete search time to 59.9 ms in total against 58.5 ms for the original merge, which retained up to 242 sequences. Time to the first factor increased from 20.8 to 26.4 ms. A lazy merge preserved every sorted first hit with up to 60 sequences and took 69.9 ms for those complete searches. [Measured results and checked factor certificates](../research/rectangular-weight-streams.json)

For a product of two balanced primes, a complete search of the rectangular difference-of-squares rows can recover a factor. Each eligible multiplier has the form $k=tab$, where $a\le b$ are coprime. Either $t=1$ and both weights are odd, or $t=4$ and the weights have opposite parity. The product gives an upper ratio $b/a\le (s+e)/s$ and cutoff $k\le K$. Several pairs can produce the same $k$. [Splitting theorem and cofactor requirements](../PrimeFactors/MixedUnityCofactors.lean) · [Finite multiplier count](../PrimeFactors/RectangularMultiplierCount.lean)

The original generator builds a sorted sequence for each small weight $a$, stores every sequence and then merges them. That startup cost matters on a full-size input. On each of the two public 2,048-bit products it would retain more than $2^{341}$ separate sequences before emitting its first multiplier. The count follows from the generator's integer endpoints. No such allocation was attempted. [Original generator](../experiments/rectangular_root_windows.py) · [Inputs and counts](../research/rectangular-weight-streams.json)

## Two ways to avoid the startup cost

For an odd $a>1$ the first coprime odd $b\ge a$ is $a+2$, since $\gcd(a,a+2)=\gcd(a,2)=1$. The exceptional first pair is $(1,1)$. In the opposite-parity family the first $b$ is $a+1$. It follows that a sequence with gap $g\in\{1,2\}$ can emit a product only if $ea\ge sg$. The implementation jumps to that threshold, adjusts for parity, and checks the cutoff. Reaching the first output takes a fixed number of arithmetic operations on integers of input-dependent bit length. When $e=0$, the entire output consists of $k=1$, provided $K\ge1$.

The **lazy sorted merge** keeps the next unstarted sequence in each family and a heap of live sequences. The first products $a(a+2)$ and $4a(a+1)$ increase within their families. Comparing the two pending beginnings against the heap minimum therefore exposes the next global product. Equal consecutive products are emitted once. This gives the same strictly increasing sequence as the original merge for every finite cutoff.

At a prefix ending at multiplier $z$, a live sequence with small weight $a$ must satisfy $ta^2\le z$ and $sz\le t(s+e)a^2$. The first inequality follows from its first output. The second follows because the sequence can still reach $z$. The integer weights in that interval bound the memory needed at this prefix, together with at most two pending beginnings. The capacity can grow as $z$ grows.

The **pair-order traversal** visits the odd family, then the opposite-parity family, increasing $a$ within each. It retains one sequence at a time. Each coprime pair sends its multiplier directly to the search. Duplicate products cause additional full row visits. The proved bound on the *number of pairs* already charges these visits. The method uses a constant number of live integer records throughout, with integer sizes growing with $K$ and $N$. It gives up increasing order of $k$. [Both implementations](../experiments/rectangular_weight_streams.py)

Each family visits its nonempty sequences once. Within a sequence the traversal charges one gcd per later weight tested. An implementation can thus realize the existing pair-count bound on row visits using one sequence at a time. The cost of testing and rejecting noncoprime weights, and the cost of inspecting the denominator interval for each visited row, are separate. The sorted merge additionally maintains a priority queue. [Checked raw-pair bound](../PrimeFactors/RectangularMultiplierCount.lean)

## What the comparisons measure

All three traversals run the same row search. It applies the primitive mod-64 screen, derives the interval of denominators $y$ from $kN$ and the public numerator cutoff, tests $x^2=y^2-kN$, then takes $\gcd(y-x,N)$ at each square hit. The first hit and total cost come from a complete pass. When positions are capped, each visit starts at the low end of its row. The scanner retains only the first witness, a fixed set of counters and the generator state.

The 24 products, three equal-prime widths and two full-size inputs are exactly those in the earlier multiplier panel. Search receives the public product and factor width. An untimed check compared the entire sorted sequences, compared their distinct set with the full pair-order traversal and verified all 24 recovered prime pairs with Lean. The retained-lane count measures generator state. It excludes memory used by the separate equality check, certificate generation and report. [Prior panel](../research/rectangular-multiplier-products.json) · [Regression tests](../tests/test_rectangular_weight_streams.py)

Each timing entry below is **first factor / complete search**, in CPU milliseconds summed over eight products. The memory column gives the largest number of retained sequences in a complete run, in the same method order.

| Bits per prime | Original sorted | Lazy sorted | Pair order | Peak sequences |
|---|---:|---:|---:|---:|
| 16 | 3.8 / 4.6 | 3.8 / 4.9 | 3.7 / 4.6 | 35 / 11 / 1 |
| 20 | 6.5 / 11.0 | 7.2 / 13.4 | 6.0 / 10.9 | 93 / 27 / 1 |
| 24 | 20.8 / 58.5 | 22.0 / 69.9 | 26.4 / 59.9 | 242 / 60 / 1 |

At the three widths, the scans contained 934, 5,272 and 31,977 distinct rows respectively. Pair order made 0, 51 and 752 additional visits to repeated rows. It reached a first factor after fewer visits than sorted order on 16 products, more visits on seven, and the same number on one. Across the eight largest products its few expensive losses raised total visits to a first hit from 8,622 to 14,138. For example, on $156{,}149{,}346{,}964{,}109$ all three found a factor on row $k=5{,}880$. Sorted traversal reached it in 529 visits, while pair order needed 3,415.

## The 2,048-bit prefixes

Both products used $k\le65{,}536$ and at most one denominator per row, matching the previous experiment. All six searches ended with their original cofactor unresolved. Measurements below cover the entire capped search.

| Input | Distinct rows / extra pair-order visits | Peak sequences, original / lazy / pair | CPU ms, original / lazy / pair |
|---|---:|---:|---:|
| Fresh | 2,535 / 1 | 252 / 31 / 1 | 26.6 / 28.1 / 25.8 |
| Crossed | 5,547 / 154 | 254 / 64 / 1 | 56.2 / 56.9 / 56.3 |

A separate generator-only test used the full mathematical cutoff on each input and requested just 64 outputs. The lazy merge required six live sequences on the fresh input and eight on the crossed input. The 64th sorted multipliers were 1,672 and 725. Pair order retained one sequence and its 64th outputs were 2,679 and 1,073. The fresh sorted sequence starts $1,63,80,99,120$, while pair order starts $1,63,99,143,195$. These tests establish that generation can start on the full domain. They ran no denominator search outside the capped trials. [Operation counts, unresolved inputs and prefix traces](../research/rectangular-weight-streams.json)

Run `python3 -m experiments.rectangular_weight_streams --output build/rectangular-weight-streams.json` to regenerate the results. The timing covers setup, multiplier generation, row screening, square-root tests and gcds. Each product runs in three rotations. Process and elapsed time to first factor and through complete traversal are recorded separately. The earlier generators and certificates use the repository's MIT license. [Reproduction code](../experiments/rectangular_weight_streams.py) · [License](../LICENSE)
