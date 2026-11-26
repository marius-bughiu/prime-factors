# A shorter Pascal row for equally wide primes

Knowing that both prime factors have the same bit length lets us skip part of the usual search interval. On eight independently drawn 80-bit products this removed **21.1% of the candidate divisors** in total. The same program factored all eight with either interval. On one 88-bit product the reduced interval dropped CPU time from **18.9 to 14.6 seconds**. The reductions were **59.3%** on our freshly generated 2,048-bit comparison and **15.0%** on the earlier constructed crossed comparison. Each remaining interval contains more than $2^{1020}$ integers. [Recorded 80-bit comparisons](../research/short-pascal-panel.json) · [88-bit and full-size fixtures](../benchmarks/short-pascal.json)

## Why we can skip these candidates

Suppose someone hands us **143** and tells us that both its prime factors have four bits. The larger prime can be at most 15. The smaller must therefore be at least $\lceil143/15\rceil=10$. It can be at most $\lfloor\sqrt{143}\rfloor=11$. Only 10 and 11 remain. The entry in row 11, column 2 of Pascal’s triangle is $11\times10/2=55$. Its greatest common divisor with 143 is 11. The other factor is 13.

For $N=pq$ with $p<q$, assume both primes lie in $[B,2B)$, where $B$ is the power of two for their bit length. The promise determines that bit length from $N$ alone. Define

$$
U=\lfloor\sqrt N\rfloor,\qquad
L=\max\left(B,\left\lceil\frac{N}{2B-1}\right\rceil\right),\qquad
K=U-L+1.
$$

Then $L\le p\le U<q$, and
$$
\gcd\!\left(N,\binom{U}{K}\right)=p.
$$

The numerator runs through all integers from $L$ to $U$. Its denominator $K!$ is coprime to both primes because $K<p$. More generally, for any row $p\le U<2p$, a column $0\le k\le U$ contains a multiple of $p$ exactly when $U-p<k<p$. This follows from the factorial identity or Lucas’s theorem. The same equal-width lower endpoint was already used in our divisor-window work. Here we apply it to the Pascal row and to the interval-product benchmark, and count its effect on the full target population. [Earlier divisor-window bound](limits-of-linear-divisor-windows.md)

These observations are elementary. They let us replace an earlier Pascal row indexed near $N$ with one indexed near $\sqrt N$. [Lean characterization and exact gcd](../PrimeFactors/ShortPascalRow.lean) · [Earlier row and its cost](pascal-readout.md) · [Granville on binomial congruences](https://www.cecm.sfu.ca/organics/papers/granville/paper/binomial/html/node2.html)

For **2,028,838,549**, the earlier entry in row 2,028,838,548 occupied 761,262 bits. The new row is 45,042, its column is 12,275, and the entry occupies **38,056 bits**. Its remainder is 560,089,168. One gcd yields 32,993, and division gives 61,493. Generally $\binom{U}{K}<2^U$. When $2K\le U$, we also have $2^K\le\binom{U}{K}$. The lower bound follows by comparing with the middle entry of row $2K$. On the two full-size controls it already exceeds what we can store. [Exact evaluator](../experiments/short_pascal_row.py) · [Exact row benchmarks](../benchmarks/short-pascal.json)

## How often does the range shrink substantially?

Compare with the ordinary ratio bound $p\ge\lceil\sqrt{N/2}\rceil$, available when $q\le2p$. If $N\ge3B^2$ and $B\ge1000$, the new interval contains fewer than half as many integers. At $2N\ge7B^2$ it contains fewer than a quarter. The proof includes integer rounding. These two conditions involve only the product.

For distinct 1,024-bit primes drawn uniformly subject to their product having 2,048 bits, **more than 18.9%** of pairs get the half-width saving and **more than 4.2%** get the quarter-width saving. We divided the prime interval into 32 equal bins. Of the 1,024 ordered pairs of bins, 661 can contain an eligible product, 126 guarantee the first threshold, and 28 guarantee the second. The count allows the populations of different bins to differ and excludes equal primes. It measures integer candidates before wheel filtering. Actual time also depends on polynomial and memory costs. [Lean width and population theorems](../PrimeFactors/ShortRowPopulation.lean)

**Across the full 2,048-bit population, the mean number of integer candidates falls by more than 30%.** The theorem sums both interval lengths over exactly the same eligible prime pairs. It proves that ten times the sum of the new lengths is less than seven times the sum of the old lengths. This compares two means. The observed 21.1% reduction in the eight smaller examples is a separate measurement. [Aggregate cost theorem](../PrimeFactors/ShortRowPopulation.lean)

When an algorithm searches in square blocks, an interval of $W$ integers fits into a grid with side $\lceil\sqrt W\rceil$. **The mean of that side falls by more than 16%** across the same prime pairs. The proof accounts for rounding on every input. Simply taking the square root of the two mean interval sizes would give a different quantity. The cost of multiplying and evaluating the block polynomials still enters the runtime. [Integer block-size theorem](../PrimeFactors/ShortRowBatchCost.lean)

The finite population calculation uses the published unconditional bound on the first Chebyshev function at 33 endpoints. Their natural logarithms lie between 709 and 710, within the theorem’s range. Lean takes those 33 inequalities as hypotheses and checks the bin counts and final fractions. The width reductions for a specified input use integer arithmetic alone. [Axler, equation (1.6), citing Broadbent et al.](https://arxiv.org/pdf/2203.05917#page=1)

## How much work did this save?

We evaluated the same interval product with the same wheel and interpolation algorithm. The wider run used only the two-to-one bound on the primes. The tighter run also used their known bit width. Both completed the whole interval before taking the final gcd. The eight 80-bit inputs were the first qualifying pairs from a fixed SHAKE-256 seed. Each search received only its product and the stated promise. Lean checked all eight prime pairs. [Panel generator and certificate replay](../experiments/short_pascal_panel.py)

| Across the same eight products | Ratio bound | Equal-width bound |
|---|---:|---:|
| Integers in the intervals | 1,974,250,457,924 | 1,557,083,661,675 |
| Candidates after skipping multiples of 2, 3, 5 and 7 | 451,257,247,528 | 355,904,836,954 |
| Polynomial convolution input coefficients | 9,307,266 | 8,337,292 |
| Total CPU seconds in one local run | 28.26 | 25.68 |

On the independent 88-bit input **192,452,556,327,192,827,635,402,733**, the new interval gave **11,036,210,959,057 × 17,438,281,765,469**. The product was the first full-width draw from `draw_prime` in `affine_radix_holdout.py` using 44 bits, seed `short-pascal-eighty-eight-v1` and independent side labels `p` and `q` (draw index 3, starting at zero). Both runs used wheel 210 and the decimal interpolation backend. They covered 928,737,756,553 and 670,415,039,709 wheel candidates, respectively. We reused the classical Pollard–Strassen approach with small-prime removal. The input-specific change is where the interval starts. [Sampler](../experiments/affine_radix_holdout.py) · [Existing interpolation implementation](../experiments/factorial_progressions.py) · [Costa and Harvey](https://arxiv.org/abs/1201.2116)

A product tree also computes the gcd without constructing the exact binomial. On a fresh 60-bit product it covered 53,938,129 wheel candidates with a degree-7,352 polynomial, 7,336 evaluation points and 3,857 direct edge terms. The search took 1.35 CPU seconds. Direct trial division on the same wheel stopped at the factor after 15,444,322 divisions in 1.01 seconds. Each 2,048-bit comparison input exhausted the 4,096-candidate budget. A complete tree on either would need a degree that itself has 510 bits. [Product-tree evaluator](../experiments/short_pascal_blocks.py) · [Benchmarks and unresolved inputs](../benchmarks/short-pascal.json)
