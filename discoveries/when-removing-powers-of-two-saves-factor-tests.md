# When removing powers of two saves factor tests

Consider 8,927, a product of two seven-bit primes. Both factors lie between 70 and 127. With target 5, position 13 gives a difference of 164. That lies between twice 70 and twice 127, so the original interval test keeps it. Halving it gives 82, which also passes the interval test. But 164 is divisible by **four**, and the remaining 41 is too small to contain either prime. We can skip this gcd. At position 20 the difference is 395, and its gcd with 8,927 is 79. [Bounded experiment](../experiments/circle_mark_reduced.py) · [Proof that division preserves every successful position](../PrimeFactors/CircleMarkReducedBands.lean)

## What the product and the width tell us

Write the product as $N=pq$ with distinct odd primes of known width $b$. Both lie between $P=\lfloor N/2^b\rfloor+1$ and $H=2^b-1$. Choose the first positive $a$ with Jacobi symbol $-1$ modulo $N$. This symbol can be computed from $N$ alone. Exactly one of the two primes can divide $x^2-a$. Each successful gcd therefore returns a proper factor. [Initial search and its costs](which-marked-coordinate-tests-can-be-skipped.md)

Let $y=x^2-a>0$. Write $y=2^v z$ with $z$ odd. The gcd of $y$ and $N$ equals the gcd of $z$ and $N$. If a prime in $[P,H]$ divides $z$, some positive integer $k$ must satisfy $kP\le z\le kH$. This can be checked with one division, by taking $k=\lfloor z/P\rfloor$. Any reduced remainder that passes also passed the original interval test on $y$. The converse fails, as 164 shows. These statements also hold when dividing out any known divisor of $y$ coprime to $N$. [Exact gcd and candidate inclusion](../PrimeFactors/CircleMarkReducedBands.lean)

## Jumping over positions in groups

For many targets, the amount to remove is known as soon as we know whether $x$ is even or odd. Each row gives the **entire** power of two dividing a positive difference.

| Target | Even position | Odd position |
| --- | ---: | ---: |
| $a=2$ | 2 | 1 |
| $a$ is 3 or 7 modulo 8 | 1 | 2 |
| $a$ is 5 modulo 8 | 1 | 4 |

Let $c$ be the entry for one parity. Band $k$ consists of the positions of that parity from $\lceil\sqrt{a+ckP}\rceil$ through $\lfloor\sqrt{a+ckH}\rfloor$, inclusive. Generate the even and odd positions in order and take the smaller next position. Once both sets contain every remaining coordinate of their parity, the implementation switches to consecutive gcds. This preserves the first successful coordinate and avoids testing the band at each position. [Parity and endpoint proofs](../PrimeFactors/CircleMarkParityLanes.lean) · [Two-stream search and timing harness](../experiments/circle_mark_reduced.py)

## How much work did the test save?

The census includes all 27,527 pairs of distinct primes with widths from 7 through 12 bits whose product has twice the prime width. The input to each search was the product and the width. Selecting the target took 71,966 Jacobi tests in total. The comparison checks the first hit and factor on every input, and supplies seven distinct example certificates for Lean to check. [Deterministic counts and selected examples](../benchmarks/circle-mark-reduced.json)

| Search | Gcd calls | Other measured work |
| --- | ---: | --- |
| Consecutive positions | 18,830,097 | One gcd per position |
| Previous interval jumps | 17,226,088 | 147,129 integer square roots |
| Test the odd part at every remaining position | 16,823,840 | 17,574,995 band classifications |
| Two parity streams with a per-position fallback | 16,823,840 | 287,410 stream endpoint square roots, 1,178,470 head comparisons and 138,356 fallback classifications |
| Consecutive Fermat midpoints | — | 680,639 midpoint square tests |

The reduced test saved **402,248 additional gcds** compared with the original bands. In 76,434 of those cases a single halving would still have left a possible multiple of a prime. The parity streams applied on 27,326 products. Across the other 201 the chosen target was 17 or 41. On the selected product $15{,}571{,}079=3{,}823\cdot4{,}073$, full division saved 250 gcds beyond the original bands. Fermat found the factors at its second midpoint. [Per-width accounting and selection rule](../benchmarks/circle-mark-reduced.json)

On the 19,546 products in the 12-bit row, the two-stream search finished earlier than the previous interval search in all four paired trials. The straightforward consecutive loop still finished earlier than both, despite doing more gcds. The median times were 1.660 seconds for the two-stream implementation, 1.769 for the previous jumps, 1.455 for consecutive positions and 0.060 for Fermat. The instrumented searches ran on an Apple M4 under CPython 3.9.6. Target selection and validation were outside the clock. [Reproduce with the timing option](../experiments/circle_mark_reduced.py)

| Trial | Original intervals (s) | Two streams with fallback (s) | Consecutive (s) | Fermat (s) |
| ---: | ---: | ---: | ---: | ---: |
| 1 | 1.766 | 1.662 | 1.457 | 0.061 |
| 2 | 1.779 | 1.658 | 1.442 | 0.060 |
| 3 | 1.765 | 1.652 | 1.453 | 0.060 |
| 4 | 1.771 | 1.671 | 1.456 | 0.060 |

## What about targets 17 and 41?

For any target congruent to 1 modulo 8, every even coordinate gives an odd difference. The remaining coordinates separate into two progressions for each exact exponent from 3 through a chosen depth $K$. Two classes modulo $2^K$ still require more bits. At each new depth only four child residues have to be tested. For 17 at depth 8, the unresolved coordinates are 23 and 233 modulo 256. The two classes 105 and 151 give valuation exactly 8. [Progression construction and proof of coverage](../PrimeFactors/CircleMarkDyadicLanes.lean)

We ran the progression search on every one of the 201 products for which the previous method used a per-coordinate fallback. It preserved the first mark, its factor and all 117,249 gcd tests of the full-removal scan at every depth. Increasing the depth gave a tradeoff in preparing the streams and testing unresolved positions. The counts include work to obtain the next value from a stream, even when an earlier hit on another stream ends the search. [Measured work and sample certificate input](../benchmarks/circle-mark-dyadic-lanes.json) · [Reproduction](../experiments/circle_mark_dyadic_lanes.py)

| Depth | Positions requiring an individual band classification | Band endpoint square roots | Prefetched candidates left unused |
| ---: | ---: | ---: | ---: |
| Full per-position scan | 138,356 | 201 prefix square roots | 0 |
| 3 | 28,436 | 3,765 | 804 |
| 5 | 5,762 | 7,557 | 1,601 |
| 8 | 938 | 11,874 | 2,633 |

For $135{,}529=313\cdot433$ with target 17, all three depths reach position 59 after 24 gcds. The previous unreduced bands used 42 gcds. At depth 8 this selected example used 27 endpoint roots, prefetched nine unused candidates and needed zero individual classifications. The timing table above measures the two-stream implementation with its original fallback. We have counted operations for the sparse progressions separately.

## How often is a small target enough at full size?

The first positive target with negative Jacobi symbol is prime. Otherwise its factorization would contain a smaller negative target. The first six possible targets are 2, 3, 5, 7, 11 and 13. Every one has a row in the parity table. For an odd product coprime to 120,120, all six tests have positive symbol precisely when the product or its negative is a square modulo 120,120. Exactly 360 of its 23,040 invertible residues have that property. [Reciprocity and the first target](../PrimeFactors/CircleMarkFirstTarget.lean) · [Exact residue count](../PrimeFactors/CircleMarkFirstTargetPopulation.lean)

Now count all products of two distinct 1,024-bit primes whose product has 2,048 bits, weighting each product once. The proportion whose first target exceeds 13 differs from $1/64$ by at most $2^{-146}$ under the explicit prime-count estimates of Ernvall-Hytönen and Palojärvi for modulus 120,120. Some later targets also admit the two-parity method. The local proof takes the paper’s endpoint inequalities as hypotheses. The external Riemann-hypothesis project supplies the separate zero-location result for Dirichlet L-functions on which those estimates depend. [Lean transfer to prime pairs](../PrimeFactors/CircleMarkFirstTargetPopulation.lean) · [Prime-count inequalities, Corollary 2](https://arxiv.org/abs/2003.01925) · [External verification](https://math.mit.edu/~drew/grh/)

## How much can be saved on a typical large input?

Compare against one gcd per positive coordinate through the first mark. Even allowing the full power of two at every coordinate, the fraction of those gcds that the band test removes is below $2^{-350}$ outside fewer than one in $2^{85}$ eligible products. This holds simultaneously for all positive negative-Jacobi targets through 2,015,165. Grouping remainders by their power of two proves the bound. The larger that power is, the fewer residue classes can produce it. The counting proof uses no analytic assumption. [Full-removal bound](../PrimeFactors/CircleMarkTwoAdicSavings.lean)

For the parity-table targets the sharper bound is $2^{-359}$ outside the same exceptions. Combining it with the prime-count estimates above gives an actual first target through 13 and this sharper limit on more than a $63/64-2^{-84}$ share of all eligible products. Much of the work remains even when the skips are free. These comparisons apply to this particular coordinate search. [Bound for the target actually chosen](../PrimeFactors/CircleMarkSelectedSavings.lean)
