# When a small set of powered values determines the factor sum

Suppose we have only a 2,048-bit product $N=pq$ of two distinct 1,024-bit primes. We choose an integer $E$ between 1 and $N$, draw a uniformly random invertible residue $u$, and raise it to $E$ modulo $N$. How much would a good choice of $E$ already tell us?

Consider any set of at most $2^{20}$ acceptable outputs. The set can differ between products and can even be unknown to the person searching. The input $u$ must be drawn after fixing the exponent and the set. Suppose the chance of entering the set is at least one in $2^{410}$. For every product whose prime predecessors satisfy $\gcd(p-1,q-1)\le2^{80}$, a continued fraction of $E/N$ contains the exact ratio $E/((p-1)(q-1))$. Testing its candidate values gives the prime factors using just $N$ and $E$. A qualifying exponent remains an extra input. This explains why a search for such an exponent can be as informative as the factor search itself. [Conditional recovery theorem](../PrimeFactors/SmallPowerImage.lean) · [An exact worked example with a clue constructed from the primes](what-a-successful-power-would-reveal.md)

## How often the common-divisor condition holds

Among all eligible **unordered** prime pairs, fewer than one in $2^{55}$ have a common predecessor divisor larger than $2^{80}$. This is an unconditional count of finite sets. It leaves open how to decide which side of the bound a specific unknown pair lies on.

Both predecessors are even. Write $p-1=2x$ and $q-1=2y$. If $\gcd(p-1,q-1)>2^{80}$ then $x,y$ share a divisor $d>2^{79}$. There are at most $\lfloor2^{1023}/d\rfloor^2$ ordered pairs of multiples in their range. Summing over $d$ is an upper bound even if a pair is counted more than once. The reciprocal square tail from $d>T$ is at most $1/T$ by telescoping. Each distinct unordered pair has two orientations. Comparing this upper bound with the project's lower count of eligible prime pairs gives the claimed fraction. [Common-divisor count](../PrimeFactors/CommonPredecessorTail.lean) · [Certified lower count of prime pairs](../PrimeFactors/ChebyshevPrimeSample.lean)

## How concentration affects the denominator

Set $P=p-1$, $Q=q-1$, $F=PQ$. Raising a uniform input to $E$ gives a uniform output on an image of size $XY$, where $X=P/\gcd(P,E)$ and $Y=Q/\gcd(Q,E)$. Uniformity follows because every element in the image has the same number of preimages. At rate at least $1/2^{410}$, at most $2^{20}$ accepted outputs imply $XY\le2^{430}$. The reduced denominator $b$ of $E/F$ divides $\gcd(P,Q)XY$. Thus $b\le2^{510}$ for the indicated products. [Power-map fibers and arbitrary output sets](../PrimeFactors/PowerImageSupport.lean) · [Denominator divisibility](../PrimeFactors/PowerImageDenominator.lean)

The size promise gives $N-F=p+q-1<2^{1025}$ and $F\ge2^{2046}$. This yields $2b^2(N-F)<F$. Since $E\le N$, the exact ratio $E/F$ is within $1/(2b^2)$ of $E/N$. Legendre’s theorem places it on the list of convergents. If it is $a/b$, then $F=Eb/a$ and $p+q=N+1-F$. Each candidate is checked by the integer quadratic identity. The calculation never needs to identify the set of successful powered outputs. [Verified approximation argument](../PrimeFactors/PowerImageDenominator.lean)

One broad family of exponents cannot concentrate that much. For **every** positive divisor $E$ of $N-1$, each local kernel size is at most $\gcd(P,Q)$. Therefore the probability of hitting even $2^{20}$ outputs is at most $2^{-1866}$ whenever $\gcd(P,Q)\le2^{80}$. The same statement covers $E=1$, $(N-1)/2$, and $N-1$. It covers searches with at most the given number of successful outputs. A method admitting many more successful outputs requires a different analysis. [Predecessor-exponent bound](../PrimeFactors/SmallPowerImage.lean)
