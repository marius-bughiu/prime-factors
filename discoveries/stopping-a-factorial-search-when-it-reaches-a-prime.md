# Stopping a factorial search when it reaches a prime

We found both factors of eight fresh 80-bit products using **22.6% fewer polynomial input coefficients in total** than our previous complete folded search. Search CPU time fell from **20.77 to 15.99 seconds** in one paired run. The saving came from three inputs. The other five needed the same polynomial calculations as before. A ninth, 88-bit product also needed the full calculation. All nine prime pairs have separate Lean certificates. [Inputs, counts and timings](../research/capped-folded-factorial-panel.json) · [Replay the experiment](../experiments/growing_factorial_panel.py)

## What lets the search stop?

For an example, take $2,028,838,549$. Both primes have 16 bits, so the smaller one must lie between 32,768 and 45,042. A first set of block products covered 32,768 through 43,260. Its gcd with the input was **32,993**. Division gave **61,493**. The search had no reason to construct the larger tables needed to reach 45,042. [Checked factorization and interval](../benchmarks/growing-factorial.json)

In general, let $N=pq$, with distinct odd primes $B\le p<q<2B$ and $B$ a power of two. Put $M=2B-1$. The public search interval is $L=\max(B,\lceil N/M\rceil)$ through $U=\lfloor\sqrt N\rfloor$. Its lower end is especially good when either prime is near its respective bit-width boundary. The exact distance is

$$
p-L=\min\left(p-B,\left\lfloor\frac{p(M-q)}{M}\right\rfloor\right).
$$

The equality describes when the search will stop early. The algorithm computes $L$ directly from $N$ and receives neither distance. Inside the interval, a product of candidates has gcd $p$ with $N$ if it contains $p$, and gcd 1 otherwise. After checking the wheel primes we can skip their multiples. [Endpoint identity and gcd proof](../PrimeFactors/GrowingFactorial.lean) · [Equal-width interval](a-shorter-pascal-row-for-equal-width-primes.md)

The previous search groups the candidates into blocks, builds their products by doubling the block length, and uses polynomial interpolation to evaluate many blocks together. The folded version pairs blocks on opposite sides of a wheel-aligned midpoint. We check the already available block products with one gcd before each expensive extension. A unit gcd lets us skip those blocks in later checks. We also allocate factorial tables only as far as the current extension needs them. The final version keeps the same midpoint, terminal block length, and final interpolation as the complete folded method. A late search can incur additional gcds and inversions. [Complete folded algorithm](folded-factorial.md) · [Growing search](../experiments/growing_factorial.py) · [Classical factorial algorithm of Costa and Harvey](https://arxiv.org/abs/1201.2116)

With $\rho$ residues per wheel cycle and a block of $h$ cycles, a full intermediate stage covers $h(\rho h+1)$ cycles on each active side. If a target is $D$ cycles away and the search has to double after that stage, then the next degree satisfies $(2\rho h)^2<4\rho D$. An odd number of old blocks can leave one overlapping block at the next stage. That overlap contains only previously checked units, so the new gcd still represents exactly the search region just reached. Lean proves this for both forward and symmetric coverage. This bound concerns polynomial degrees. Arithmetic on the coefficients, locating a gcd, and allocating the tables carry separate costs. [Coverage, degree and table identities](../PrimeFactors/GrowingFactorial.lean)

## How often does a large input avoid the final calculation?

For a uniformly chosen pair of distinct 1,024-bit primes conditioned on a 2,048-bit product, the forward search saves **more than 3.6889%**, and the folded search **more than 1.911%**, in mean normalized convolution input counts. To form the mean we compare each search with its own complete version, divide the saving on that product by its complete count, then weight all eligible products equally. A product requiring no convolution contributes zero saving. These are bounds for the searches using the complete method’s final block size. [Finite averaging proof](../PrimeFactors/FactorialCheckpointMean.lean)

The proof counts products on which we can locate the smaller prime inside an intermediate batch. Before rounding the endpoints, more than 9.97% of eligible pairs have the smaller prime between 1% and 11% of the way through the interval. More than 3.90% have it between 48% and 52%. Both counts already exclude intervals of width below $2^{40}$. In the forward search the first band lies inside the penultimate batch. In the folded search the second band lies inside that batch, including the shift caused by aligning the midpoint to a complete block. A hit saves a final convolution accounting for at least 37% or 49% of the respective baseline. Other hits can also save work. [Population estimates and external assumptions](where-the-smaller-prime-appears-in-order.md) · [Rounded batch coverage and final-operation shares](../PrimeFactors/FactorialCheckpointCoverage.lean)

The population argument applies Axler’s published unconditional prime-count estimate to sections of the factor interval. The integration and its connection to the prime-pair counts are written proofs. From those three explicit prime-count inequalities, Lean proves the bounds on the actual eligible set. It checks that the wheel-product gcd at a credited checkpoint equals the smaller prime. The formal model gives credit for just one skipped convolution and assigns zero credit to short intervals. Extra gcds and modular inversions are billed separately in the benchmarks. These reductions still leave impractically large searches for general 2,048-bit products. [End-to-end Lean theorem and its three hypotheses](../PrimeFactors/FactorialCheckpointTarget.lean)

## Why retain the old final block size?

These were three successive experiments. Each used a separate seed, eight independently drawn 80-bit products, and one 88-bit product. The choices for the last experiment used what we learned from the first two. Each search received only its product and the equal-width promise. The eight-input totals below use the complete folded method on the same eight products as each variant.

| Search on eight 80-bit products | Complete folded inputs | Early-stop inputs | Complete folded CPU | Early-stop CPU |
|---|---:|---:|---:|---:|
| Grow forward from the lower end | 7,580,662 | 7,873,148 | 21.60 s | 24.73 s |
| Grow around the midpoint | 7,466,546 | 9,134,812 | 20.13 s | 24.46 s |
| Keep the complete folded method’s final block size and reuse table entries | 6,683,412 | 5,171,776 | 20.77 s | 15.99 s |

The forward version also beat the complete forward baseline on its eight cases, 7,873,148 versus 8,367,702 inputs. Unrestricted growth around the midpoint did well on its 88-bit draw, $164,544,282,475,788,555,705,336,053$. It covered 2.43% of the interval and found $11,056,262,994,011\times14,882,450,115,823$ in 2.17 CPU seconds, versus 13.44 seconds with the complete folded search. Its eight smaller cases show the cost of letting a late doubling build a larger array. [Forward panel](../research/growing-factorial-panel.json) · [Midpoint panel](../research/centered-growing-factorial-panel.json)

The final variant’s 88-bit draw, $159,685,451,837,934,099,525,764,951$, gave $12,003,351,986,137\times13,303,404,917,423$. Both methods used 4,034,946 convolution input coefficients. The early-stop version used thirteen inversions to the complete method’s one. Timing order reversed on a replay, and the observed peak memory was slightly higher for the early-stop run. The durable arithmetic comparison is the match in coefficients. [Third panel](../research/capped-folded-factorial-panel.json)

## What happened when the budget ran out?

On a fourth independent set, **none of eight 96-bit products split**. The program used the midpoint of the whole feasible interval and a budget of 1,100,000 convolution input coefficients. Each search covered 84,558,028,800 integers, between 0.155% and 0.659% of its interval. Each had 412,164 coefficients left in its budget. The next stage needed 688,132, so it stopped. The sample was fixed before any searches, and the record keeps all eight unresolved products. [All eight results, seeds and ranges](../research/budgeted-factorial-panel.json)

On the independently generated fresh 2,048-bit input, an 8,192-coefficient budget covered 10,328,657 integers growing forward, or 5,167,680 around the midpoint. On the constructed crossed input the same budgets covered 10,328,668 and 5,167,680, respectively. Neither direction found a factor in either comparison. Separate small tests cap the interval itself at 4,096 integers to check boundary handling. [Discovery budgets and certificate cases](../benchmarks/growing-factorial.json)
