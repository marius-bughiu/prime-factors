# How many products have two 1024-bit prime factors and 2048 bits?

**At least $2^{2025}$ distinct products** meet both requirements with two different primes. This count gives a denominator for success rates measured across the entire population. If we draw two primes independently and uniformly from all 1024-bit primes, then condition on distinct factors and a 2048-bit product, every eligible product has the same probability. Each has exactly two orders for drawing its factors. [Population, bit lengths and uniqueness of products](../PrimeFactors/BalancedPairPopulation.lean)

Set $Y=2^{1017}$. A prime with 1024 bits lies between $64Y=2^{1023}$ and $128Y=2^{1024}$. Its product with a second such prime has 2048 bits precisely when the product is at least $8192Y^2=2^{2047}$. We can count three disjoint families inside that region. In the table the endpoints are multiples of $Y$ and $(a,b]$ means the lower endpoint is excluded.

| Smaller prime | Larger prime | Product of the two lower endpoints, in units of $Y^2$ |
| --- | --- | ---: |
| $(91,128]$ | $(91,128]$, strictly above the smaller prime | 8,281 |
| $(80,91]$ | $(103,128]$ | 8,240 |
| $(72,80]$ | $(114,128]$ | 8,208 |

The smaller prime occurs in just one of the three rows. Every row clears 8,192. The upper endpoint $128Y$ is composite, so including that endpoint in an interval count keeps both primes strictly below $2^{1024}$. In the first row we choose two distinct primes from one interval. In the other rows every smaller prime may be paired with every larger prime. [Checked interval inclusions and disjointness](../PrimeFactors/BalancedPairPopulation.lean)

To bound the number of available primes, let $\pi(n)$ count primes at most $n$. On these endpoints, Dusart’s explicit inequalities imply $707\pi(n)\le n\le710\pi(n)$. Consequently $(aY,bY]$ contains at least

$$
L(a,b)=\left\lfloor\frac{(707b-710a)Y}{501970}\right\rfloor
$$

primes for each interval in the table. Lean checks that the following integer expression is at least $2^{2025}$.

$$
\binom{L(91,128)}{2}
+ L(80,91)L(103,128)
+ L(72,80)L(114,128).
$$

The Lean theorem takes the published prime-count inequalities as its sole analytic premise and checks the rest, including exact endpoint rounding and the correspondence between sorted pairs and distinct products. Dusart’s inequalities are unconditional. [Dusart, equation (6.6), page 9](https://arxiv.org/pdf/1002.0442#page=9) · [Lean statement of the analytic premise](../PrimeFactors/WeightedCrowdingEstimates.lean)
