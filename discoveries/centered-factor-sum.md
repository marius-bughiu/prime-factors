# Using the product to narrow the sum of the factors

Suppose two 1,024-bit primes give a 2,048-bit product. Guess the last **612 binary digits** of either prime. Those digits and the product specify a fourth-degree equation whose integer roots include that prime. Lean proves that at most four numbers must be checked for this guess. On the fresh comparison product, the same argument needed only **611 digits**. We tested the old guess, remainder 1, and it missed both primes. Finding a good guess remains open. [Lean theorem](../PrimeFactors/CenteredSumQuartic.lean) · [Full-size measurements](../research/centered-sum-quartic.json)

## What does the product tell us?

Write the factors as $x,y$ and the product as $N$. If both factors are at most $U$, the inequalities $(U-x)(U-y)\ge0$ and $(x-y)^2\ge0$ give

$$\lceil\sqrt{4N}\rceil\le x+y\le U+\lfloor N/U\rfloor.$$

Either factor is also at least $\lceil N/U\rceil$. For example, suppose $N=10403$ and both factors have seven bits. Their maximum is 127. The sum must lie between 204 and 208. Since the factors are odd, only 204, 206 and 208 need a square test in this small example. At 204, $204^2-4N=4$ gives 101 and 103. At full size, even this short sum interval can contain far too many integers to test one by one.

Choose $h$ near the center of the sum interval and $c$ near the center of the common factor interval. Write $T=x+y-h$ and $Z=x-c$. Let $|T|\le2s$, $|Z|\le H$ with positive integer radii. The five expressions

$$1,\quad T,\quad Z,\quad T^2-2s^2,\quad ZT$$

have respective bounds $1,2s,H,2s^2,2Hs$. They are an integral change of coordinates for the degree-two expressions in $x,y$ after substituting $xy=N$. Indeed, the coefficient of $y^2$ determines the fourth coordinate, the coefficient of $x^2$ then gives the fifth, and the coefficients of $y,x,1$ recover the first three. The narrow sum interval thus reduces the sizes of three columns without losing any possible relation.

For a positive remainder $u$ modulo $R=2^e$, use the same modular conditions on a quartic as in the previous search. The finite box argument proves a nonzero relation whenever

$$5^5\cdot8H^2s^4 < 12960 R^{10}.$$

The argument finds two distinct coefficient vectors with equal modular labels. Their difference has small enough absolute value that the trace must vanish on the true pair. Substituting $y=N/x$ and multiplying by $x^2$ gives a nonzero quartic. The implementation uses lattice reduction to propose a vector, checks its weighted size, and tests the raw polynomial at the 15 local values that certify the whole class. The finite existence proof and the measured solver have separate guarantees. [Finite box](../PrimeFactors/UnitQuarticBox.lean) · [Modular labels](../PrimeFactors/QuarticUnitLabels.lean) · [Implementation](../experiments/centered_sum_quartic.py)

## The uniform count and the measured count

Put $k=2^{1017}$. The width assumptions give $64k\le x,y<128k$ and $N\ge2(64k)^2$. With $K=\lceil\sqrt{4N}\rceil$, Lean proves $K\le x+y\le K+12k$. One may therefore take $h=K+6k$, $c=96k$, $s=3k$ and $H=32k$. At exponent 612 those choices satisfy the strict box inequality on every input in the stated class. The solver tightens the bounds using the actual product. [Uniform proof](../PrimeFactors/CenteredSumQuartic.lean)

This search tests positive remainders and identifies a remainder $u$ with its partner $N/u$ modulo $R$. At $e\ge3$, the number of groups is $2^{e-2}+2$ when $N\equiv1\bmod 8$ and $2^{e-2}$ otherwise. The extra two come from the four fixed odd square roots of $N$ in the first case. The old search also combined both signs, so two fewer guessed bits cut the total number of groups by about half. On the fresh product three fewer bits cut it by a factor of approximately four. The original signed count there was $2^{611}+1$.

| Product | Exponent from the product | Positive groups | Outcome of testing remainder 1 |
| --- | ---: | ---: | --- |
| Earlier constructed comparison | 612 | $2^{610}+2$ | Both known primes, 2.16 s |
| Fresh comparison | 611 | $2^{609}$ | No factor, 2.23 s |

These times measure discovery on one local run per input. The benchmark checks the prime certificates for recovered factors separately. We chose remainder 1 after seeing the earlier example's factors and kept it fixed for the fresh product. The experiment left $2^{609}-1$ groups untested on the fresh product. Higher-degree methods for divisors in a specified class already exist at the classical fourth-root scale. The comparison here concerns explicit degree-four equations and their cost. [Benchmark fixtures](../benchmarks/centered-quartic.json) · [Earlier signed search](unit-newton-lanes.md) · [Coppersmith, Howgrave-Graham and Nagaraj](https://dominoweb.draco.res.ibm.com/reports/rc23466.pdf)
