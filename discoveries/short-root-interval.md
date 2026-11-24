# Recovering a factor from a shorter reading

One fixed sum, rounded to 1,366 fractional bits, let us recover both primes in 32 tests on 2,048-bit products. Each recovery used the Euclidean algorithm and one integer square test. We used known primes to generate these readings. On the smaller product 60,491 we could also compute the reading from the product alone. The nine-bit reading was 1,345/512 and gave the factors 241 and 251. Its calculation scanned residues and encountered 241 directly. [Definition of the sum](divisor-samples.md) · [Code](../experiments/phase_interval.py) · [Product-only benchmark](../benchmarks/salie-blocks.json)

## A short interval gives an ordinary quadratic

Kuwakado and Tanaka previously used continued fractions to find small roots of quadratic modular equations. Here we use a cube-root radius with an explicit constant and obtain the interval from a rounded sum. [Kuwakado and Tanaka](https://doi.org/10.1007/BFb0030410)

Let $N=pq$ be a product of distinct odd primes. Suppose we have a closed integer interval centered at $c$ with radius $M$ containing a mixed square root $h$ of one modulo $N$. Such a root is one modulo one prime and minus one modulo the other, so a gcd with $h-1$ recovers a factor. The following argument also finds any other square roots of one in the interval. Assume $M\ge1$. A singleton only needs direct testing.

Put $B=\lfloor\sqrt{N/M}\rfloor$. The Euclidean algorithm on $2c/N$ gives integers $j,b$ with $1\le b\le B$ and $r=2bc-Nj$ satisfying $|r|\le N/(B+1)$. One can take the last continued-fraction convergent with denominator at most $B$. Its error after multiplication by its denominator is at most the reciprocal of the next denominator. If the expansion ends, the residual is zero. Integer parts do not affect the denominator. [Lean approximation and stopping inequalities](../PrimeFactors/RootIntervalSlope.lean)

Set $s=b(c^2-1)\bmod N$. The unknown offset $v=h-c$ satisfies the following equation and bound for some integer $t$.

$$b v^2+rv+s=Nt,\qquad |Nt-s|\le E=bM^2+|r|M.$$

All quantities used to bound $t$ come from the endpoints and $N$. Since $b^2 M\le N$ and $r^2\le NM$, each of the two error terms is at most $\sqrt{NM^3}$. If $64M^3\le N$, then $E\le N/4$. The interval $[s-E,s+E]$ contains at most one multiple of $N$. For that multiple, test whether $r^2-4b(s-Nt)$ is a square, check the two integer offsets from the quadratic formula, and take the gcd. These steps take polynomial time in the bit length with ordinary integer arithmetic. Wider intervals sometimes also satisfy $2E<N$ for the actual coefficients. The implementation tries that inexpensive test before subdividing. [Lean lift, range, uniqueness and discriminant proofs](../PrimeFactors/RootInterval.lean)

## How much precision this saves

Write $n$ for the bit length, $H$ for the mixed root folded into $[0,N/2]$, and $\mu$ for the distance of $H/N$ from the nearer endpoint of $[0,1/2]$. The fixed sum determines $2\cos(2\pi H/N)$ after subtracting a public term. Given the sum rounded to $d$ fractional bits, inversion gives an integer interval of span at most $2+N2^{-d}/(4\mu)$, including numerical padding. The decoder computes the interval from the reading, without knowing $\mu$. [Cosine estimate and distribution of the margin](phase-precision.md)

Set $T=N^{1/3}$, $R=\lfloor T/4\rfloor$ and $d=\lceil 2n/3\rceil+g$ with $g\ge0$. The span is at most $2+T2^{-g}/(4\mu)$. Cutting it into blocks of $2R+1$ consecutive integers gives each block radius at most $R$. For $R\ge1$ the number of blocks is at most $2+2^{-g}/\mu$, since $T<4(R+1)$ and $2/(2R+1)<1$. Each needs at most one quadratic test. The bounded program reports how many blocks the complete cover needs and how many it visited.

For uniformly chosen distinct 1,024-bit primes, conditional on a 2,048-bit product, the inverse-residue counting argument gives $\mathbb E[1/\mu]<2^{29}$ and $\Pr(\mu<2^{-38})<2^{-20}$. More generally the mean is polynomial in the bit length. Three precisions illustrate the resulting cost.

* **1,366 fractional bits** suffice for polynomial average work with the elementary decoder in this population, extending as $\lceil2n/3\rceil$ at other widths.
* **1,395 fractional bits** give fewer than three quadratic tests on average at the target width.
* **1,404 fractional bits** give one block except on a fraction below $2^{-20}$. When $\mu\ge2^{-38}$, the integer span is at most $R+2\le2R$. One centered block then contains every candidate.

The population bounds apply to supplied readings and include exceptional inputs through the complete cover. With lattice postprocessing one can lower the average-case precision to 1,024 fractional bits. With 2,048 fractional bits an earlier elementary decoder has a uniform two-candidate guarantee. Computing even the lower-precision reading efficiently from an arbitrary large product remains open. [Lattice bound](phase-precision.md) · [Uniform elementary bound](divisor-samples.md#rounding-a-square-from-the-fixed-sample)

## Reproducible readings

The five benchmark files for continued squares, gap strides, predecessor squares, reduced orders and shifted squares each contain a pair of certified 1,024-bit primes. Take the first complete 2,048-bit pair in each of those files, cross primes from different files and retain all 2,048-bit products of distinct primes. This gives 32 distinct products. A generator used the known factors to calculate each rounded reading at $d=1366$. Given the word, precision and product alone, the decoder used one square test on each, with 28 to 421 Euclidean updates. These crossed structured primes do not constitute the random population of the theorem. A separate process-isolation test replays the original continued-square fixture with the same precision. [Tests, including a wide cell and capped searches](../tests/test_phase_interval.py)

```sh
python3 experiments/phase_interval.py --emit 1366 | python3 experiments/phase_interval.py --decode
python3 experiments/salie_blocks.py 60491 --fractional-bits 9 --max-orbits 15001
```

In the small product-only run the phase interval was $[12049,12057]$. The single successful quadratic gave $h=12049$, with $\gcd(h-1,60491)=251$. Its complementary factor is 241. This directly checks a coarse reading without using the benchmark primes to calculate it.

## The cost of evaluating the sum directly

Negation and inversion partition the terms into groups with identical signed real projection. Visit the lower half of the residues and mark the inverse partner of each representative. To add its contribution with no new trigonometric call, set $z=\exp(2\pi i/N)$, $w=\lceil\sqrt N\rceil$, and write its integer phase as $jw+i$ with $0\le i<w$. Generate the baby powers $1,z,\ldots,z^{w-1}$ once. Accumulate signed multiples of these powers into block $j$, then evaluate the polynomial of blocks at $z^w$ by Horner's rule. Sine and cosine enclosures for $z$ and $z^w$ take four real trigonometric calls. Every intermediate product and sum uses outward-rounded rectangles. If the final enclosure crosses a rounding boundary the program reports that it could not certify the word. This applies classical blocked polynomial evaluation to the projected sum. [Paterson and Stockmeyer](https://doi.org/10.1137/0202007) · [Implementation](../experiments/salie_blocks.py)

For 60,491, the 60,000 unit terms became 15,001 groups. Evaluation used 489 complex interval products and 15,246 explicit unit-membership tests. On 667, the 616 terms became 155 groups and took 49 complex products. The four-call count is for computing the raw sum and excludes the subsequent decoding. The overall scan still takes order $N$ work and the marking array uses order $N$ space. At 2,048 bits it is impractical. The distinction matters because even the shortest exact rational phase expansion has order $N$ terms, whereas the blocked evaluation can reuse powers to calculate many terms. [Proof of the exact expansion bound](salie-orbits.md)
