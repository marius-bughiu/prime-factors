# What counting points on a sphere reveals about its radius

Take the entire product $N=pq$ as the radius of a sphere. Count all integer triples $(x,y,z)$ on its surface, so $x^2+y^2+z^2=N^2$. Zeros are allowed, signs matter, and the coordinates are ordered. On a sphere of radius **91**, the count is **702**. Subtract six times the radius and divide by twelve. The result is $(702-546)/12=13$, a prime factor of 91.

There is a reason this works on 91 and gives zero on 65. Two classical counting formulas determine exactly which information the count carries. They express the answer in terms of the unknown primes. A direct census gets the count without the factors by enumerating coordinate pairs. That costs $(N+1)^2$ iterations in the implementation, more than $2^{4094}$ at a 2,048-bit radius. The open question is whether the relevant count can be obtained cheaply for a single large radius. [Lean deductions and small census](../PrimeFactors/ThreeSquareRadiusCounts.lean) · [Hürlimann, Theorem 2 and equation (2)](https://www.maths.tcd.ie/EMIS/journals/JIS/VOL18/Huerlimann/huerli6.pdf#page=2)

## What the total count tells us

Call the total count $C(N)$ and put $E=(C(N)-6N)/12$. For a product of two distinct odd primes, the classical Hurwitz formula yields the following values. [Lean case analysis](../PrimeFactors/ThreeSquareCountPrecision.lean)

| Prime remainders modulo 4 | Value of $E$ | Example |
| --- | --- | --- |
| 1 and 1 | Zero | $65=5\times13$ gives $C=390$ |
| 1 and 3 | The prime congruent to 1 | $91=7\times13$ gives $C=702$ and $E=13$ |
| 3 and 3 | $p+q+2$ | $77=7\times11$ gives $C=702$ and $E=20$ |

For 77 the last case gives a sum of 18. Its square minus four times the product is $18^2-4\cdot77=16$. The two primes are $(18-4)/2=7$ and $(18+4)/2=11$. The identical counts at 77 and 91 illustrate why we subtract the baseline for the known radius. The ordinary small-prime check recovers both factorizations before it reaches a Fermat midpoint test. [Independent baseline inputs and expected prime factors](../benchmarks/cases.json)

Across all distinct pairs of 1,024-bit primes with a 2,048-bit product, the fraction where an exact total count would reveal a prime or the sum is within $1/4160$ of **three quarters**. This uses the published unconditional Bennett–Martin–O’Bryant–Rechnitzer estimate for primes modulo 16. Lean counts the sixteen silent pairs among the 64 ordered pairs of unit residues and transfers their frequency to the full-size population. The Ernvall-Hytönen–Palojärvi estimates under Dirichlet GRH tighten the error to $2^{-148}$. Both results still require a way to obtain the sphere count for the individual product. [Population proof](../PrimeFactors/ThreeSquareSignalPopulation.lean) · [Bennett and coauthors, Theorem 1.3](https://personal.math.ubc.ca/~bennett/BeMaObRe-IJM-2018.pdf#page=5) · [Ernvall-Hytönen and Palojärvi, Corollary 2](https://arxiv.org/pdf/2003.01925#page=2)

## Can we fix the zero case by changing the radius?

When both primes are 1 modulo 4, **every positive integer multiplier** $m$ satisfies $C(mN)=N\,C(m)$. This includes multipliers divisible by either or both primes. An exact count at any of these radii therefore reports a quantity already determined by the public product and the count at $m$. For odd multipliers the identity follows because the local factor at a prime $\ell\equiv1\bmod4$ is exactly $\ell^a$ at every exponent $a$. Doubling the radius doubles every coordinate in a bijection of surface points, so even multipliers obey the same identity. [Odd multipliers](../PrimeFactors/ThreeSquareRadiusCounts.lean) · [All positive multipliers](../PrimeFactors/EvenThreeSquareRadius.lean)

There is a precise interpretation of even a rough estimate. Suppose $N\equiv1\bmod4$, $p\le q<2p$, and $s=\lfloor\sqrt N\rfloor$. If an integer $v$ approximates $C(N)$ with error strictly below $12s$, then $v<6N+12s$ exactly when $-1$ has a square root modulo $N$. Conversely, if someone supplies the answer to that yes-or-no question, then $6N$ for yes and $6N+24s+24$ for no already give the stated accuracy. The proof accounts for the rounding of $\sqrt N$. At this precision the count is equivalent to a square-existence question already identified by the project's quartic tests. [Both implications](../PrimeFactors/ThreeSquareCountPrecision.lean) · [Earlier square-existence criterion](one-modulus-and-the-low-bits-of-the-prime-sum.md)

## What about changing the number being represented?

Write $r_3(T)$ for the number of signed, ordered integer triples whose squares sum to $T$. Count representations of $dN^2$, allowing a multiplier $d$ that is itself nonsquare. At $N=65$, the count at $d=1$ only returns $65\,r_3(1)$. Trying $d=2$ yields 1,260, different from $65\,r_3(2)=780$. The same change does nothing at $N=697$: both $d=1$ and $d=2$ give exactly $697\,r_3(d)$. At $d=3$, both examples depart from their baselines. [Six counts checked in Lean from the recurrence](../PrimeFactors/ThreeSquareTwistExamples.lean)

| $N$ | $r_3(N^2)$ | $r_3(2N^2)$ | $r_3(3N^2)$ |
| ---: | ---: | ---: | ---: |
| 65 | 390 | 1,260 | 728 |
| 697 | 4,182 | 8,364 | 6,536 |

**Every fixed finite list of positive multipliers has arbitrarily large balanced products on which all its counts equal $N\,r_3(d)$.** The proof finds primes $p<q<2p$ for which every $-d$ on the list is a square modulo both primes. The three-square recurrence then scales each base count by $pq$. The result allows the prime sizes to grow. It leaves open what happens at a prescribed bit width or if the list is chosen after reading $N$. The recurrence is a published mathematical input to the Lean deduction. [Finite-list theorem and arbitrarily large balanced prime pairs](../PrimeFactors/FiniteThreeSquareTwists.lean) · [Hirschhorn and Sellers, equation (4)](https://www.d.umn.edu/~jsellers/p8.pdf#page=3)

## What changes if we count only primitive points?

A point is primitive when $\gcd(|x|,|y|,|z|)=1$. Write $R(N)$ for the number of primitive points. Let $\chi(\ell)$ equal $1$ on primes congruent to 1 modulo 4 and $-1$ on those congruent to 3. The classical formula gives $R(N)=6(p-\chi(p))(q-\chi(q))$. This count is always a multiple of 96, so an integer estimate with absolute error **strictly below 48** suffices to recover the exact count by rounding. When $N\equiv1\bmod4$, the distance between $R(N)/6$ and $N+1$ is the prime sum. When $N\equiv3\bmod4$, the distance to $N-1$ is the prime gap. At $N=65$, for instance, the primitive count is 288. The distance from 48 to 66 is 18, the true sum. [Count identity and rounding proof](../PrimeFactors/ThreeSquareRadiusCounts.lean)

Sampling points also has a measurable limitation. The coordinate gcd divides the radius. For $N=pq$, a point therefore has gcd $1$, $p$, $q$ or $N$. The six signed coordinate-axis points have gcd $N$. Exactly $C(N)-R(N)-6$ points have a proper factor as their gcd. For a uniform surface point this gives a chance strictly below $1/p+1/q$. On distinct 1,024-bit primes this is less than $2^{-1022}$ per uniform draw, even if drawing the point were free. [Geometric partition and probability bound](../PrimeFactors/ThreeSquarePointDensity.lean)

Dividing each point with gcd $p$ by $p$ gives a primitive point on the sphere of radius $q$, preserving its coordinate signs and order. The corresponding statement holds with $p$ and $q$ exchanged. This proves $R(pq)=C(pq)-C(p)-C(q)+6$ and gives the formula for $R(pq)$ from the Hurwitz formula for total counts alone. [Scaling and deduction of the primitive formula](../PrimeFactors/ThreeSquarePointDensity.lean)

| Radius | All signed, ordered points | Primitive points | Points with a proper factor as gcd |
| ---: | ---: | ---: | ---: |
| 15 | 150 | 96 | 48 |
| 65 | 390 | 288 | 96 |
| 77 | 702 | 576 | 120 |
| 91 | 702 | 576 | 120 |

Lean checks radius 15 directly in the kernel. The three larger examples are finite executable censuses, cross-checked by enumerating signed coordinates independently. The individual count identities and the uniform point-sampling bound require no Riemann-hypothesis estimates. [Surface counts](../PrimeFactors/ThreeSquareRadiusCounts.lean) · [Coordinate gcd counts](../PrimeFactors/ThreeSquarePointDensity.lean)
