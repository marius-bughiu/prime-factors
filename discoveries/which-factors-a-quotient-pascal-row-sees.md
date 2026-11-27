# Which factors does a binomial coefficient test?

Starting with 2,623 and the information that its two primes each have six bits, we can get both factors with one binomial coefficient. The formula halves the number of candidate terms by using just the odd numbers. On the project's independently generated 2,048-bit comparison product, the shorter calculation still contains more than $2^{1019}$ terms. Our five-term test on that input returned gcd 1 and left the whole product unresolved. [Lean proof](../PrimeFactors/QuotientPascalMasks.lean) · [Reproducible benchmarks](../benchmarks/quotient-pascal.json)

## The example by hand

The largest six-bit prime is at most 63. Thus the smaller factor must be at least $\lceil2623/63\rceil=42$ and at most $\lfloor\sqrt{2623}\rfloor=51$. The ten integers between these endpoints contain five odd candidates, 43, 45, 47, 49 and 51. Their product modulo 2,623 is 1,720. Its gcd with 2,623 is 43, giving $2623=43\times61$.

The related binomial coefficient is $\binom{1290}{5}$, where $1290=(2623-43)/2$. Its remainder is 2,322, whose gcd with 2,623 is also 43. Each multiplication, both primality proofs and the connection to the binomial coefficient can be checked using the public input and the benchmark receipt. A search that already skips even integers visits the same five candidates. [Benchmark runner](../scripts/quotient_pascal_benchmark.py) · [Earlier full-interval coefficient](a-shorter-pascal-row-for-equal-width-primes.md)

## The identity behind the search

Let $N=pq$ with distinct primes $p<q$. Pick $c,d,m\ge0$ with $\gcd(d,N)=1$ and $c+dm$ a multiple of $N$. For $0\le k<p$, the following holds exactly:

$$
\gcd\!\left(N,\binom{m}{k}\right)
=\gcd\!\left(N,\prod_{0\le j<k}(c+dj)\right).
$$

Lucas's theorem says that $p$ divides the coefficient precisely when $m\bmod p<k$. The only index $j<p$ for which $p$ divides $c+dj$ is $j=m\bmod p$, since $d$ is invertible modulo $p$. Applying the same argument at $q$ proves the gcd identity. We import Gareth Ma's Apache-2.0 implementation of Lucas's theorem from the project's pinned mathlib. [Mathlib source and license notice](https://raw.githubusercontent.com/leanprover-community/mathlib4/v4.19.0/Mathlib/Data/Nat/Choose/Lucas.lean)

For two odd primes in $[B,2B)$, choose $c$ to be the first odd integer at or above $\max(B,\lceil N/(2B-1)\rceil)$. Set $u=\lfloor\sqrt N\rfloor$, $d=2$, $m=(N-c)/2$ and $k=1+\lfloor(u-c)/2\rfloor$. These choices depend only on the product and the promised width. Every positive term is at most $u<q$, and one is $p$. Their gcd with $N$ is exactly $p$. Multiplying the terms modulo $N$ avoids constructing the large binomial coefficient. A fast way to evaluate this gcd for enormous $k$ would change the cost of using the formula. [Equal-width theorem and column length](../PrimeFactors/QuotientPascalMasks.lean) · [Existing batch multiplication methods](batch-intervals.md)

## What happens when factors repeat?

The same progression has a unique row $0\le m<N$ for every choice of $c$ and every stride $d$ coprime to $N$. One modular inverse gives $m=-c/d\pmod N$. The gcd identity above holds for every modulus coprime to $d\,k!$, including products with repeated factors. For example, the progression 25, 28 and the coefficient $\binom{175}{2}$ both have gcd 25 with 275. With arbitrary $d$ and $k$, let $g=\gcd(N,d^k k!)$. The exact progression gcd is $g\,\gcd(N/g,\binom{m}{k})$. This identifies the part lost by division even when the denominator shares a factor with the input. [Congruence, general gcd formula and examples](../PrimeFactors/QuotientPascalTransfer.lean)

## Could an unusually high row help?

For the plain quotient $m=\lfloor aN/d\rfloor$ with $d>0$, the exact condition for a hit at $p$ is $p\,((aq)\bmod d)<dk$. The unknown $q$ occurs in this condition. One can instead calculate the public remainder $r=(aN)\bmod d$. When $d$ is coprime to $N$, the coefficient tests precisely the list $r,r+d,\ldots,r+(k-1)d$. If $r>0$ and $dk\le p$, all these terms are positive and smaller than both primes. If $r=0$ and $k>0$, both primes divide the coefficient. Increasing $a$ while keeping the same remainder leaves the gcd unchanged. These statements concern a particular family of formulas. [Quotient threshold and small-parameter proof](../PrimeFactors/QuotientPascalMasks.lean)

Consider any row index $k\le m<N<2^{2048}$ and $k<2^{1023}$. A 1,024-bit prime can divide the coefficient only if it divides one of the $k$ positive integers from $m-k+1$ through $m$. At most two such primes fit in a single term. In every 60 consecutive terms, 28 have a common divisor of at least four with 60, so each of those accommodates at most one such prime. The coefficient therefore has at most $92\lfloor k/60\rfloor+2(k\bmod60)$ distinct 1,024-bit prime divisors. When the gcd with the input is 1, these are the prime locations directly excluded by this coefficient. This is a count of locations, with no probability assigned to the choice of row. The bounds add across a sequence of rows even when the public product and previous results determine the next choice. [Prime count and period-60 proof](../PrimeFactors/PascalCandidateCount.lean)
