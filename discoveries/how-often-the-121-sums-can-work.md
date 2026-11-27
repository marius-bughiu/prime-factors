# How often can the 121 sums contain the right answer?

**Even trying all 121 sums can factor fewer than one in $2^{491}$ eligible 2,048-bit prime pairs.** This counts every pair of distinct 1,024-bit primes whose product has 2,048 bits, with the smaller prime first. The bound still holds if a rule can read the whole product and always pick the right sum whenever it is in the list. It explains why recovering many small examples gives little evidence about the full-size problem. [Lean bounds](../PrimeFactors/WordBlockFrequency.lean)

For a given product $N$, put $B=2^{1024}$. Its upper half determines an interval of $B$ consecutive possible products. Call its upper endpoint $T$ and put $a=\lfloor\sqrt T\rfloor$. The 121 midpoints are $a$ through $a+120$. Each stands for the sum twice that midpoint. An earlier proof showed that one of those sums fits at least as many odd integer pairs with the observed high word and remainder modulo 120 as any sum anywhere. Here we ask how often the prime factors of the particular input have **any** sum in that list. [Ranking theorem and worked examples](choosing-a-sum-from-a-word-and-a-remainder.md)

## Why the upper bound is so small

Write the true factors as $p=u-v$ and $q=u+v$. Then $v^2=u^2-N$. For a midpoint in the list, $u-a\le120$, both $u$ and $a$ are below $B$, and $a^2-N<B$. Consequently,

$$
v^2=(u-a)(u+a)+(a^2-N)<241B < (2^{516})^2.
$$

Once $p$ is fixed, every covered pair has a different half-gap $v<2^{516}$. Let $H$ count all primes of the target factor width and $E$ all eligible pairs. The existing finite prime estimate gives $2^{1023}H<41056E$. Multiplying $H$ by the half-gap bound shows that fewer than $2^{-491}E$ pairs can appear anywhere in the block. The proof uses integer inequalities and an unconditional finite prime count. [Prime-count normalization](../PrimeFactors/SquareRootPhasePopulation.lean)

## What the block does catch

The fraction is also **greater than $2^{-514}$**. Among the primes in the upper part of the factor range, any two in the same interval of width $2^{516}$ have a sum reached by the first 120 ordinary Fermat midpoints. Counting pairs in the same interval gives the lower bound even when individual intervals contain very different numbers of primes. The first ordinary midpoint is either $a$ or $a+1$, so all those successes also lie in the 121-row block. This lower bound applies when every candidate may be tried. A rule making just one guess can recover fewer pairs. [Bucket count](../PrimeFactors/FirstSumMenuPopulation.lean) · [Inclusion and both numerical bounds](../PrimeFactors/WordBlockFrequency.lean)
