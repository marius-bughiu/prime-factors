# Which short recurrences can skip a Jacobi period?

Suppose $N=pq$ is a product of distinct primes at least 11. Write $u_j$ for the complete Jacobi moment at degree $2(j+1)$. A rule that combines exactly three terms with fixed coefficients invertible modulo $N$ can hold for every starting position only if **all three offsets agree modulo the true period**. Thus each pair of readings in the rule already gives the same value. The distance from the first to the last offset is at least two periods. This holds even if the coefficients are chosen specifically for $N$. [Three-term theorem](../PrimeFactors/JacobiThreeTerms.lean) · [Exact period of the moments](what-the-period-of-the-jacobi-moments-reveals.md)

## Why three terms force a period

A rule specifies offsets $a<b<c$ and coefficients $A,B,C$ such that $A u_{j+a}+B u_{j+b}+C u_{j+c}=0$ for all $j$, with arithmetic modulo $N$. Reduce it at one prime factor $p$. The local even sequence has period $d=(p-1)/2$. For a rule with fewer than $d$ nonzero terms, Lean proves that the coefficients at offsets in each residue class modulo $d$ sum to zero in the prime field. With three terms and $p\ge11$ this applies. A class containing just one coefficient could not sum to zero, since an invertible coefficient stays nonzero modulo $p$. Splitting three terms between two or more classes always leaves a singleton, so all three offsets must share a class. The same argument at $q$ makes every difference divisible by $L=\operatorname{lcm}((p-1)/2,(q-1)/2)$, the composite even period. [Coefficient sums within a class](../PrimeFactors/JacobiSparseSupport.lean) · [Proof for three terms](../PrimeFactors/JacobiThreeTerms.lean)

For 1,024-bit primes the even period is at least $2^{1022}$. Three such terms therefore span at least $2^{1023}$ positions in the even sequence. This measures the distance between the terms. The theorem gives no lower bound on the time needed to evaluate a single high-degree moment. It assumes an identity holding everywhere and leaves open a rule that succeeds only over a particular finite prefix. [Full-size period bound](../PrimeFactors/JacobiMomentPeriod.lean)

## Two places where the conclusion fails

**Four terms at 143.** The even sequence modulo $143=11\cdot13$ has period 30. For every $j$ it satisfies

$$u_{j+11}+u_j=u_{j+5}+u_{j+6}.$$

The offsets $0,5,6,11$ are all different modulo 30. Modulo 11, the local period is 5 and the terms cancel in pairs. Modulo 13, the local period is 6 and they cancel in a different pairing. This corresponds to the polynomial $(X^5-1)(X^6-1)$. More generally, multiplying the two local period polynomials always gives such an identity. Constructing it this way uses the local periods, which depend on the unknown factors. [Four-term identity and the 143 example](../PrimeFactors/JacobiThreeTerms.lean)

**Three terms at 77.** The even sequence modulo $77=7\cdot11$ has period 15, yet for every $j$ it satisfies

$$u_{j+10}+23u_{j+5}+53u_j=0.$$

All coefficients are invertible modulo 77, and all offsets differ modulo 15. Here the prime 7 has local period 3, so the three terms can occupy every residue class at that prime. Lean checks the identity for every starting position. Both examples illustrate the limits of the theorem on known small products. [The 77 identity and coefficient checks](../PrimeFactors/JacobiThreeTerms.lean)
