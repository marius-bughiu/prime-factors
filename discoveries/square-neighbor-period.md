# A maximum local score with no splitting norm relation

On a specially constructed 2,048-bit product, the multiplier score makes the most favorable prediction it can make at every tested prime. Yet every continued-fraction norm is $1$ or $-1$, and **every square dependency is trivial**, however far the ordinary walk runs. The very first Fermat midpoint recovers the two 1,024-bit primes. Lean checked their primality, their product and the algebra behind the obstruction. [Successful midpoint](../benchmarks/cases.json) · [Scored search](../benchmarks/scored-multipliers.json) · [Lean proof](../PrimeFactors/SquareNeighborPeriod.lean)

## Why the whole walk fails

For a positive even integer $a$ take $N=a^2+1$. The relation $(\sqrt N-a)(\sqrt N+a)=1$ and $2a<\sqrt N+a<2a+1$ give the entire continued fraction $[a;\overline{2a}]$. Write $X_j+Y_j\sqrt N=(a+\sqrt N)^j$. The pair starts at $(1,0)$ and then $(a,1)$. From there each coordinate satisfies the continuant recurrence $Z_{j+2}=2aZ_{j+1}+Z_j$. Thus the pairs for $j\ge1$ are the full sequence of convergent numerators and denominators.

Each multiplication by $a+\sqrt N$ flips the norm, giving $X_j^2-NY_j^2=(-1)^j$. It also sends $X_j$ to $aX_j$ modulo $N$, so $X_j\equiv a^j\pmod N$. A set of these signed norms has a positive square product only when its indices sum to an even number $2k$. The product of its numerators is then $a^{2k}\equiv(-1)^k\pmod N$. The integer square root of the norm product is 1. Taking a gcd with the sum or difference of these two roots therefore gives 1 or $N$, since $N$ is odd. This proves the limitation for every finite choice of convergents, including combinations across periods. It concerns the usual congruence-of-squares extraction from these rows. [Formal recurrence, norm and square-dependency theorems](../PrimeFactors/SquareNeighborPeriod.lean)

## Why this input maximizes the score

Given a small-prime cutoff $B$, take $b$ divisible by every prime through $B$, including 2, and set $a=2b^2$. Then $N=(2b^2)^2+1\equiv1\pmod8$ and $N\equiv1\pmod\ell$ at every odd prime tested. With $m=1$, all terms of the primitive-pair score already have their maximum value. Changing the multiplier can leave some local terms at their maximum or reduce them. Every $m>1$ pays a positive size penalty. Thus 1 wins uniquely among the permitted multipliers, including with the implemented rounded logarithm weights. At the same time
$$N=(2b^2-2b+1)(2b^2+2b+1).$$
The first Fermat midpoint $2b^2+1$ gives square difference $(2b)^2$. Primality of both displayed factors is needed only for the complete two-prime example below. The period obstruction and these integer identities hold throughout the family.

For $B=97$, write $97\#$ for the product of all primes through 97. Choose
$$ b=11{,}507{,}636\cdot 2^{367}\cdot97\#.$$
Starting at $k=11{,}502{,}678$, we tried successive values of $b=k2^{367}97\#$ in the 2,048-bit range. The witness above has both displayed factors prime and $k$ supported on primes through 10,000, allowing the existing order-certificate generator to check both primes. GMP probable-prime tests were used only to look for a witness. Neither benchmark receives $b$ or the factors. The product and fixed budgets suffice for both outcomes. [Factor certificate on Pages](https://marius-bughiu.github.io/prime-factors/#fermat-maximal-score-2048) · [Performance on 64 independently sampled products](scored-multipliers.md)
