# Can a square reveal the prime sum?

Start with **102,029**. The next square is $320^2=102,400$, a difference of 371. One divisor of that square is 1,024. Trying $1024-371+1=654$ as the sum gives the correct primes **257 and 397**. We found the divisor by trying the fraction $16/5$ of 320. Only a short list of fractions was needed for this example. [Benchmark fixture](../benchmarks/square-anchor-slopes.json)

## Which squares can work?

Write $N=pq$ and $F=(p-1)(q-1)=N+1-(p+q)$. The rule chooses a positive integer $m$ and a divisor $g$ of $m$, and tries $N+1-m+g$ as the sum. It succeeds exactly when $m=F+g$. Thus $g$ must divide $F$ and $m\le2F$. This also allows values of $m$ below the product. Once a candidate sum is available, one integer square root of $S^2-4N$ suffices to test it. [Lean counting and readout proof](../PrimeFactors/SquareAnchorCoverage.lean)

At the first square $m=r^2$ above the product, any divisor giving the right answer must lie between $2r$ inclusive and $5r$ exclusive for two distinct odd primes of equal width. Write the ratio $g/r$ in lowest terms as $a/b$. The condition $g\mid r^2$ is equivalent to $ab\mid r$. This makes small fractions cheap to test, even when $r$ itself is expensive to factor. We used all 66 reduced fractions in that interval with $b\le8$, discarding guesses outside the public bounds on $p+q$. [Public search](../experiments/square_anchor_slopes.py)

| Input set | Found using the product and width | With all divisors of the first square | With all divisors of every square |
| --- | ---: | ---: | ---: |
| All 903 pairs of distinct nine-bit primes | 21 | 31 | 191 |
| 64 separate products of 12-, 20-, 28- or 36-bit primes | 0 | — | — |
| Two 2,048-bit comparison products | 0 | — | — |

The last two columns used the known primes to measure the ceiling. For the small sample we tested all 52,313 divisors of the predecessor products $F$ to see whether $F+g$ was square. The actual product-only search spent 903 setup square roots, 58,407 fraction visits, 1,076 divisibility tests, and 39 candidate square roots. Ordinary Fermat search with the same per-input candidate-square-root budget found 17 products. Nine were found by both. One fixed weighted Fermat guess per input found 46, at a cost of 903 candidate square roots. [Full results and operation counts](../research/square-anchor-slopes.json)

There is an example where the difference looks dramatic. In the family $p=18u+1$, $q=32u-3$, the square root rounded up is $24u$ and three times that root gives the right divisor. We chose the first $u\ge1,000,000$ giving two primes. The product was 576,025,322,278,297. The public square rule recovered 18,000,397 and 32,000,701 on its first candidate square root. Ordinary Fermat took 1,000,022 midpoint tests. The same construction also makes $16p-9q=43$, so a weighted Fermat search with those two weights already succeeds on its first test. [Construction and comparison](../experiments/square_anchor_slopes.py)

## What happens at 2,048 bits?

**Fewer than one in $2^{738}$ eligible prime pairs can give the correct sum this way, even with every divisor of every square available for free.** Here we choose uniformly from sorted pairs of distinct 1,024-bit primes whose product has 2,048 bits. This includes squares at any distance on either side of the product. The conclusion concerns this one rule for reading the sum from a square. [Uniform finite bound](../PrimeFactors/SquareAnchorCoverage.lean)

The count has two parts. Any successful square divisor has the form $g=ta^2$ with square root $r=tab$. Counting all positive triples with $tab\le U$ gives at most $U(1+1/2+\dots+1/U)^2$ possibilities. For each resulting $F=r^2-g$, the smaller prime minus one must be one of the divisors of $F$. The library bounds how many there can be and compares the total with its proved minimum number of eligible prime pairs. The same counting argument for a finite list of $A$ arbitrary positive targets below $2^{2049}$ bounds its coverage by a fraction smaller than $A/2^{1541}$ for $A>0$, even if the choice among those targets depends on the full product. [Divisor bound](../PrimeFactors/UniformDivisorCount.lean) · [Prime-pair count](../PrimeFactors/ChebyshevPrimeSample.lean) · [Square and general target bounds](../PrimeFactors/SquareAnchorCoverage.lean)
