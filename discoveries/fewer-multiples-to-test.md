# Which multiples can reveal the two primes?

Given only a 2,048-bit product of two distinct 1,024-bit primes, we can skip at least **81.2316%** of the multiples in one complete difference-of-squares search. At least one of the remaining multiples has a solution that reveals a prime factor. On our independently generated example we can skip at least **94.56%**. Even that leaves a search far beyond our budget. The bounded search found neither prime. [Uniform Lean theorem](../PrimeFactors/RectangularFullWidth.lean) · [Public inputs and measured work](../research/rectangular-multiplier-products.json)

## How a multiple reveals a factor

Take 2,257. Multiplying by 15 gives 33,855, just one short of 184². So 15 × 2,257 = 183 × 185. The greatest common divisor of 183 and 2,257 is 61. Division gives the other prime, 37. The question is how many multipliers like 15 we need to try before finding a working one. [Checked example](../PrimeFactors/MixedUnityCofactors.lean)

Write the input as $N=pq$ with $p<q$. For a trial multiplier $k$, look for integers $x,y$ with $y^2=kN+x^2$, $0<y\le B$ and $0\le x\le H$. We take $T=\lceil\sqrt[3]N\rceil$, $B=\max(\lfloor N/T\rfloor,\lfloor\sqrt N\rfloor+1)$, $H=\lfloor N/(B+1)\rfloor$, and $K=\lfloor B^2/N\rfloor$. All four come from the input alone. For each $1\le k\le K$, the interval starts at $\lceil\sqrt{kN}\rceil$ and ends at the smaller of $B$ and $\lfloor\sqrt{kN+H^2}\rfloor$. A square difference in this interval gives a proper divisor by taking $\gcd(y-x,N)$. [Recovery theorem](../PrimeFactors/MixedUnityRectangle.lean)

Why must some interval work? There is a residue equal to $+1$ modulo one prime and $-1$ modulo the other. Dirichlet approximation gives a fraction $x/y$ representing that residue within these bounds, up to sign. The primes exceed $H$, so the denominator is invertible after removing common factors. The two different signs force $k>0$. The algorithm needs neither the residue nor the primes to enumerate the intervals. This is a form of the classical multiplier approach to factoring. [Representation proof](../PrimeFactors/RectangularRootWindows.lean) · [R. Sherman Lehman, *Factoring Large Integers* (1974)](https://doi.org/10.1090/S0025-5718-1974-0340163-2)

## Why the input rules out most multipliers

For a solution with $\gcd(x,y)=1$, one prime divides $y-x$ and the other divides $y+x$. Remove those primes from the two sides, and remove a factor of two from each side when both are even. The remaining two weights $a\le b$ are coprime. The multiplier has one of two forms, $ab$ with both weights odd, or $4ab$ with opposite parities. In the example the weights are 3 and 5. [Parity and factor placement](../PrimeFactors/MixedUnityCofactors.lean)

The weights also have to be close in size. Let $U$ be the largest integer of the known prime width and $S=\lfloor\sqrt N\rfloor$. Since $q/p=q^2/N\le U^2/N$ and $y\ge S$, the multiplier weights satisfy

$$\frac ba\le\frac{U^2}{N}\frac{S+H}{S-H}.$$

We round this bound up to $1+e/1024$. Listing only pairs within that ratio gives a finite count of the multipliers. The proof allows duplicates and some impossible pairs when upper-bounding the count. The search removes duplicates and tests coprimality. Every balanced input of the stated size retains a splitting row. The cost of generating the pairs and the work inside each interval both matter. A separate bound counts every candidate square position before sieving. [Counting multipliers](../PrimeFactors/RectangularMultiplierCount.lean) · [Counting positions](../PrimeFactors/RectangularWeightCost.lean)

## How much work can remain?

On every such input the complete generator still emits **more than $10^{102}$ distinct multiples**, even after testing the ratio, parity and coprimality. To see why, take $a=2049+2i$ and $b=a+2$ for $0\le i<2^{339}-1025$. Each pair is coprime, its ratio fits even the narrowest positive rounded allowance, and $a(a+2)$ is under the multiplier cutoff. These products strictly increase with $i$. This lower bound counts different multiples visited on a **complete traversal**. A factor can appear before the traversal ends. [Lean proof of the surviving count](../PrimeFactors/RectangularSearchFloor.lean)

## What we actually searched

On each full-size input we tried multipliers through 65,536 and at most the first position in each surviving interval. Both variants used the same modular square filters. Each timing is the median of four CPU measurements including setup. Both whole inputs remained unresolved by these runs. [Exact inputs, caps and counts](../benchmarks/rectangular-root-windows.json) · [Timing records](../research/rectangular-multiplier-products.json)

| Input | Guaranteed share of all multipliers skipped | Multipliers visited, before → after | Exact square tests, before → after | CPU time, before → after |
| --- | ---: | ---: | ---: | ---: |
| Fresh 2,048-bit product | ≥94.56% | 65,536 → 2,535 | 11,328 → 851 | 388 ms → 26 ms |
| Crossed 2,048-bit product | ≥85.51% | 65,536 → 5,547 | 11,281 → 1,828 | 390 ms → 56 ms |

A second implementation can start listing eligible multiples even with the full search limit. It generated the first 64 in order while keeping at most six sequences in memory on the fresh input and eight on the crossed input. [Generation costs and checked examples](streaming-eligible-multipliers.md)

The full-range upper bounds on eligible multipliers are still about $2^{678.34}$ and $2^{679.60}$ respectively. Counting the candidate positions within all those intervals gives upper bounds of about $2^{679.34}$ on the fresh input and $2^{680.60}$ on the crossed input. These are coverage guarantees. A factor can appear earlier, as it did in the small examples. An earlier experiment recovered the crossed product with a clue selected using its published factors. Neither run in this table used such a clue. [Origin of the crossed clue](testing-one-factor-remainder.md)

On 24 smaller independently generated products the search reached a factor on every input. For the eight 48-bit products, total time to the first factor fell from 129 ms to 20 ms. These are sums of per-input median CPU times. On 157,243,323,583,487, both variants first succeeded at multiplier 975. The restricted search visited 90 multipliers and performed 234 exact square tests on the way, down from 975 and 1,203. The checked answer is 10,040,453 × 15,660,979. [Experiment and seed](../experiments/rectangular_weight_panel.py) · [Recorded factors and certificates](../research/rectangular-multiplier-products.json)

We also tried the interval construction on three signed equations motivated by the quadratic-form method of D. H. Lehmer and Emma Lehmer. A complete small comparison checked 438 root classes across 126 products by direct enumeration. For eight products of two 20-bit primes the earlier curve search took 963 ms total to reach a first factor, the three interval searches took 63 ms, and the single difference-of-squares search took 14 ms. The interval bound grows on the order of the cube root of the input for these fixed targets. Published deterministic methods already achieve a smaller exponent for general factoring. These results measure a reduction within the specified search. [D. H. and Emma Lehmer (1974)](https://doi.org/10.2307/2005939) · [Comparison data](../research/rectangular-root-windows.json) · [Lean bound for a full interval search](../PrimeFactors/RectangularRowCost.lean) · [David Harvey, exponent-one-fifth factoring](https://arxiv.org/abs/2010.05450)
