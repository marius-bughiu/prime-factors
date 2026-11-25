# What the exact factor curve saves

Two numbers with a known product cannot move independently. If the smaller factor moves up, the larger one must move down. Using that relationship, we found the exact range of a weighted sum as the two real numbers vary over the balanced range. On the 82-bit example this removed **683,229 candidate sums** while keeping the factors. Most of those discarded sums already failed a cheap sign check, so it saved **36,104 square roots**. [Measured comparisons](../research/curved-weight-holdout.json) · [Lean proof of both extrema](../PrimeFactors/CurvedWeightInterval.lean)

## Which sums are possible?

Suppose the factors are positive and within a factor of two of each other. Write them as $h-d$ and $h+d$, so $h^2-d^2=N$ and $3|d|\le h$. For a weighted sum $a(h+d)+b(h-d)$, we can negate the whole sum and exchange the two factors to work with coefficients $u=|a+b|$, $v=|a-b|$. Write $z=\sqrt{N/8}$. The maximum is $(3u+v)z$. The minimum is

$$
\begin{cases}
(3u-v)z, & 3v\ge u,\\
\sqrt{N(u^2-v^2)}, & 3v<u.
\end{cases}
$$

The endpoint $(h,d)=(3z,z)$ gives the maximum. In the first case the opposite endpoint gives the minimum. In the second case the minimum occurs at $d/h=-v/u$. At that point the right-hand side of the identity $(uh+vd)^2-N(u^2-v^2)=(ud+vh)^2$ vanishes. The Lean proof establishes attainment as well as both inequalities. In the search we round the two endpoints with integer square roots, allow negative weighted sums and retain the original integer-coordinate bounds when those round more tightly. [Exact rounding](../experiments/curved_weight_interval.py) · [Proof](../PrimeFactors/CurvedWeightInterval.lean)

We kept the base, weights and order of the remainder pairs fixed in each comparison. Both versions recovered all eight pairs in the original 49–50-bit sample and the same two primes on the 82-bit input. On the latter they each visited 7,188,480 groups. The 2,048-bit run visited the same first 128 groups, leaving the whole product unresolved. [Comparison program](../experiments/curved_weight_holdout.py) · [Benchmarks](../benchmarks/midpoint-weights.json)

| Input | Candidate sums, rectangle → curve | Integer square roots, rectangle → curve | Discovery time, rectangle → curve |
| --- | ---: | ---: | ---: |
| Eight 49–50-bit products | 23,956 → 20,124 | 20,337 → 20,124 | 0.0612 s → 0.0622 s |
| 82-bit product | 4,342,642 → 3,659,413 | 3,695,517 → 3,659,413 | 8.262 s → 8.124 s |
| 2,048-bit product, 128 groups | 84 → 68 | 2 → 2 | 0.313 s → 0.321 s |

Times are local paired measurements. The eight small cases use the sum of five-run medians. The 82-bit comparison alternates order over two runs per method. The full-size comparison uses three runs and the optional reduced-discriminant square test. The counts follow from the fixed inputs and parameters. [Raw measurements](../research/curved-weight-holdout.json)

A six-sided region also gives a smaller sufficient base for every slope. On the 82-bit input, ranking the admissible bases by slope count cut the time of the grouped search from 3.65 to 2.71 seconds. [Area proof](hexagonal-weight-bound.md) · [Measurements](choosing-hexagonal-radices.md)

## Could a much smaller base leave only one candidate?

Even granting the exact curve and a different best choice of weights for each slope, we can put a lower bound on the necessary base. Suppose a single base $R$ is coprime to $N$, each pair of remainders has a weighted sum fixed modulo $R^2$ by the stationary congruence, and its test uses the range of that sum on the **whole** balanced real factor curve. The interval must cover both orderings. For every $N\ge2^{2047}$:

- Requiring every such interval to have width below $R^2$ forces $R>2^{648}$.
- Even allowing each slope to choose a favorable remainder, requiring at most one integer of that class in its whole interval forces $R>2^{647}$.

These statements apply to this particular way of certifying a single candidate. Additional constraints on the integer factors, smaller sections of the curve, or sharing work between slopes give different questions. [Full curve theorem](../PrimeFactors/CurvedWeightLimit.lean) · [Stationary coefficient count](../PrimeFactors/AdaptiveWeightLimit.lean)

Here is the counting argument. Three points already lie on the real curve: $(\sqrt N,\sqrt N)$, $(2z,4z)$ and $(4z,2z)$. For an interval of width $W$, comparing the first trace with the mean of the last two gives $|a+b|(3z-\sqrt N)\le W$. Comparing the last two gives $2z|a-b|\le W$. At target size these force both $2^{1024}|a|$ and $2^{1024}|b|$ to be at most $17W$. Also, every closed interval at least two moduli wide contains two integers from every prescribed residue class. [Three-point proof](../PrimeFactors/CurvedWeightLimit.lean) · [Interval lemma](../PrimeFactors/CongruenceInterval.lean)

For a fixed $1\le a\le B$, put $g=\gcd(a,R)$. Any compatible nonzero $b$ with $|b|\le B$ is a multiple of $g$. There are at most $2\lfloor B/g\rfloor$ choices, and each permits at most $g$ slopes modulo $R$. Thus **every** choice of weights of size at most $B<R$ can cover, between them, at most $2B^2$ unit slopes. Changing both signs lets us take $a$ positive. A zero coefficient would force its partner to vanish. [Lean counting proof](../PrimeFactors/WeightSlopeCover.lean)

The product requires exactly $\varphi(R)/T$ slopes, where $T$ is the number of unit square roots of one modulo $R$. For $R\le2^{648}$ the first 91 primes already have product larger than $R$, so $R$ has at most 90 distinct prime factors. Each odd prime power contributes at most two roots, and the power of two contributes at most four. Hence $T\le2^{91}$. The repository's totient estimate also gives $R<13\varphi(R)$ in this range. Combining the number of required slopes with the number small weights can cover gives both lower bounds above. The argument allows the base and all the weights to depend on the input. [Prime-power and CRT proof](../PrimeFactors/StationaryRadixLimit.lean) · [Totient estimate](../PrimeFactors/QuotientBudget.lean)

Even if work within each slope could be combined for free, more than $2^{552}$ distinct slopes are required for the favorable-offset case and more than $2^{553}$ for the strict-width case. These bounds allow arbitrarily large bases. With at least 91 prime factors the product of $(p-1)/2$ is minimized by choosing the smallest 91 primes. With fewer prime factors the square-root count stays small and the totient gives the lower bound. [Lean proof for every radix](../PrimeFactors/StationarySlopeBudget.lean)
