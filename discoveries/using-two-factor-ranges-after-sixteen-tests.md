# What do two new search ranges buy for the same 34 square roots?

On every one of the **592,048** eligible products of two 16-bit primes, we compared three searches with the same budget. They all began with sixteen ordinary square tests. Continuing ordinary search found 62,262 additional pairs, switching to one new range found 89,779, and splitting the work between two new ranges found **142,452**. The two-range search still left 303,793 products unresolved. On two 2,048-bit products in the target range, the same schedule covered over three times as many new integer locations as ordinary continuation. All three searches missed both products. [Complete finite counts](../research/two-interior-population.json) · [Benchmark inputs](../benchmarks/two-interior-batches.json)

## The two ranges

Write the product as $N=pq$ with $p<q$. For weights $(a,b)$, start at $\lceil2\sqrt{abN}\rceil$ and test candidate values $S$ of $ap+bq$ in increasing order. Only labels with $\gcd(S,24)=\gcd(a+bN,24)$ need a square test. At the true value, $S^2-4abN=(ap-bq)^2$. Taking the gcd of $(S+\sqrt{S^2-4abN})/2$ with $N$ gives one of the factors when $ab$ is coprime to $N$. All weights below are coprime to a product of two 1,024-bit primes. The search uses only $N$ and the public weights. [Admissible labels and recovery](../PrimeFactors/TwoInteriorTraceBatches.lean)

| Search | Common prefix | Additional square tests | Starting square roots | Total roots |
|---|---:|---|---:|---:|
| Ordinary | 16 | 17 at $(1,1)$ | 1 | 34 |
| One new range | 16 | 16 at $(3,2)$ | 2 | 34 |
| Two new ranges | 16 | 7 at $(3,2)$, then 8 at $(7,5)$ | 3 | 34 |

The first new range covers possible smaller factors near $\sqrt{2N/3}$, where $q$ is near $3p/2$. The second is near $\sqrt{5N/7}$, where $q$ is near $7p/5$. In each range the first few tests reach farther per test than the next few. Spending one extra square root to locate the second range pays for itself in the number of positions covered. The comparison counts square roots. It assigns no cost to the other arithmetic and makes no elapsed-time claim.

## What holds at 2,048 bits

Put $U=2^{1024}$ and assume $9U^2/16\le N\le5U^2/8$. Both ranges lie inside the bounds imposed by the bit lengths, above $0.80\sqrt N$. They are disjoint from each other and from the ordinary range. Their combined ordinary length beats **both** alternatives by more than $N^{1/4}/2$. The proof includes the alignment of each starting label independently modulo 24. The first omitted labels for the new ranges are between 20 and 24, and between 48 and 216, respectively, above their theoretical minimum. [Interval and length bounds](../PrimeFactors/TwoInteriorTraceBatches.lean)

The integer comparison survives additional modular filters. For any one residue class modulo an integer $1\le M\le2^{500}$, the two new ranges cover more locations in that class than either alternative. The proof rounds the winners' endpoints inward and grants both endpoints to each baseline. Summing over any nonempty fixed set of admissible residues preserves the strict inequality. For an actual divisor in either range, Lean proves that one of the tested labels has the correct square and gcd. These results are unconditional. They give no lower bound for how often an unknown prime actually lies in the winning intervals at this size. [Rounded counts, feasibility and factor recovery](../PrimeFactors/TwoInteriorTraceBatches.lean)

| Eligible full-size benchmark | New locations, ordinary | One new range | Two new ranges | Factors found |
|---|---:|---:|---:|---:|
| Constructed near $q=3p/2$ | $5.049\times10^{154}$ | $8.628\times10^{154}$ | $1.728\times10^{155}$ | 0 |
| Crossed comparison | $4.858\times10^{154}$ | $8.477\times10^{154}$ | $1.699\times10^{155}$ | 0 |

The fresh benchmark is outside the theorem's size range and also remained unresolved. The benchmark records exact integer counts, clipping intervals to the feasible bit-width bounds and removing the common prefix. Computing those diagnostic counts uses eleven extra square roots after the search. Running the three schedules together shares calculations and uses 60 search roots in total. [Exact counts and budgets](../benchmarks/two-interior-batches.json)

## How often did the two new ranges contain actual factors?

The smaller experiment fixes $U=2^{16}$ and enumerates **every** distinct pair of 16-bit primes with product in the same proportional range. Each method receives only the product. A sieve generates the prime pairs and checks every returned divisor afterward. The common prefix recovered 145,803 products. Of the remaining products, 75,632 were found only by the two-range continuation, 22,959 only by the one-range switch, 62,262 only by ordinary continuation, and 66,820 by both switched searches. [Reproduce with `python3 -m experiments.two_interior_population`](../experiments/two_interior_population.py) · [All outcomes](../research/two-interior-population.json)

For example, $2,416,359,541=40,949\times59,009$. The third admissible $(7,5)$ label was $581,688$. It yielded root $8,402$ and gcd $59,009$. Lean checked primality and multiplication, the winning label and gcd, and the absence of squares at all 33 ordinary labels and all 16 multiplier-six labels. The large-size proof and this small-size census answer different questions. A proof comparing actual success rates at 2,048 bits for these particular short schedules remains open. [Checked example](../PrimeFactors/TwoInteriorTraceBatches.lean)
