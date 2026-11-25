# Can one equation check twice as many possible factors?

Yes, for the search we have been studying. Choose a stretch of odd numbers and try to build an equation that every divisor there has to satisfy. A different way of writing the equation lets us join two neighboring stretches. We can now cover the entire possible range of the smaller of two 1,024-bit primes in **fewer than $2^{508}$ locations**. The earlier construction needed about twice as many. Each location in this bound requires 24,576 rows. On each of our two example products the new grid still contains **more than $2^{506}$ locations**. We have run five-row calculations on these products. The large grid is a proved work count. [Coverage and counts](../PrimeFactors/ChebyshevDivisorCover.lean) · [Earlier grid](what-the-product-says-about-the-window.md)

## A factor at the edge of the range

Starting with 132,079, the product and the assumption of two equal-width primes give the public lower-quartile center 285. We checked the 17 odd integers from 269 through 301, writing each as $285+2x$. The ordinary quartic search gave a bound of 90,601. To force the equation to vanish at a divisor we needed a bound strictly below $269^2=72,361$.

The new search returned the equation

$$5912-6733x-534x^2+98x^3+6x^4=0.$$

Its certified bound was 38,608 across the same range. The root $x=-8$ gives **269**, and division gives **491**. Lean checked both primes and their product. We selected this small example by looking for a difference between the methods. It establishes that a difference can occur. [Benchmark and factor certificate](https://marius-bughiu.github.io/prime-factors/#chebyshev-divisor-window-132079)

## What changed in the equation

The input gives an odd center $c$ and an anchor $t=(N-c)/2$. If $d=c+2x$ is an odd divisor of $N$, then $d$ divides $x-t$. We impose divisibility conditions on the coefficients of $F(t+Y)$ so that $d^m$ divides $F(x)$. If we can also prove $|F(x)|<d^m$, its only possible value is zero. Trying the integer roots of a degree-$k$ equation then costs at most $k$ candidate divisor tests, in addition to constructing the equation and isolating its roots. [Divisibility in Lean](../PrimeFactors/HigherDivisorWindow.lean)

The first search bounded each ordinary power of $x$ separately. On $|x|\le 2U$, the monic Chebyshev polynomials give integer coordinates with smaller individual bounds. Start with $D_0=2$, $D_1=x$ and $D_{j+2}=xD_{j+1}-U^2D_j$. Use 1 as the constant basis element. Each positive-degree element satisfies $|D_j|\le 2U^j$. For instance, $D_2=x^2-2U^2$ stays between $-2U^2$ and $2U^2$ across that interval. This uses a classical identity, already proved in the project's work on factor gaps. [Earlier Dickson identity](../PrimeFactors/GapPolynomialScale.lean) · [NIST, formula 18.5.1](https://dlmf.nist.gov/18.5.E1)

Changing between these polynomials and ordinary powers has integer determinant one. With $k+1$ rows and divisor power $m\le k$, the determinant after scaling is exactly

$$N^{m(m+1)/2}\,2^k U^{k(k+1)/2}.$$

The ordinary weights on that same interval give the last factor $(2U)^{k(k+1)/2}$ instead. Lean proves the determinant, a finite counting theorem that guarantees a nonzero equation, and the conditions under which the classical LLL first-vector bound is strong enough. The lattice-reduction guarantee uses the published LLL theorem. The actual benchmark certificates check their integer equations in Lean independently of how we found them. [Coordinate and existence proofs](../PrimeFactors/ChebyshevDivisorWindow.lean) · [LLL, Proposition 1.6](https://doi.org/10.1007/BF01457454) · [May, unknown-divisor construction](https://digital.ub.uni-paderborn.de/hsmig/download/pdf/3235#page=38)

The previous grid used radii $13\cdot2^{507}$ and $15\cdot2^{507}$ in its two regions. Its inequalities have enough room for the extra factor $2^k$ when each of those radii becomes $U$. Each new radius is consequently $2U$. Pairing neighboring addresses changes the counts in the two regions from $a,b$ to $\lceil a/2\rceil,\lceil b/2\rceil$. This improves the project’s local search by a constant factor. General-purpose deterministic factoring already has a stronger asymptotic running-time bound. [Integer budgets](../PrimeFactors/FeasibleDivisorCover.lean) · [Complete address proof](../PrimeFactors/ChebyshevDivisorCover.lean) · [Harvey and Hittmeir](https://arxiv.org/abs/2105.11105)

There is also a concrete change in the largest dyadic radius that the determinant test can guarantee on the crossed input. At its public lower divisor bound, the ordinary test failed at radius $2^{511}$ for every degree. In Chebyshev coordinates, 633 rows with multiplicity 316 suffice there. The next dyadic radius, $2^{512}$, fails this particular estimate in every degree at the same floor. On the fresh input, 2,587 rows with multiplicity 1,293 meet the estimate at $2^{512}$. These are existence and cost calculations. Our measured full-size reductions below used five rows. [Old threshold](../PrimeFactors/DivisorWindowThreshold.lean) · [Chebyshev threshold and checked parameters](../PrimeFactors/ChebyshevDivisorThreshold.lean)

## What happened at 2,048 bits

We used the same product-derived lower-quartile center, degree four and depth two for both ways of writing the equation. We explored three radii on both existing public products. Here a pass means the reduced equation met the strict bound. Each passing case in this table also had a small modulus ruling out an integer root.

| Radius in odd-index steps | Fresh, ordinary | Fresh, Chebyshev | Crossed, ordinary | Crossed, Chebyshev |
|---|---|---|---|---|
| $2^{408}$ | Passed | Passed | Passed | Passed |
| $2^{409}$ | Passed | Passed | Passed | Passed |
| $2^{410}$ | Missed | Missed | Missed | Passed |

At the widest radius, the equation on the crossed input ruled out **$2^{411}+1$ odd positions**. Its height was about 87% of the limit and its polynomial had no root modulo 29. On the fresh input both searches missed the height bound at that radius. At radius $2^{409}$ the fresh Chebyshev row ruled out its interval modulo 3. The fixtures preserve both outcomes at the widest radius and the smaller successful fresh case. Neither product yielded a factor in these runs. [Crossed exclusion](https://marius-bughiu.github.io/prime-factors/#chebyshev-divisor-window-crossed-410) · [Fresh miss](https://marius-bughiu.github.io/prime-factors/#chebyshev-divisor-window-fresh-410) · [Fresh exclusion](https://marius-bughiu.github.io/prime-factors/#chebyshev-divisor-window-fresh-409)

## Two ranges with a gap

Suppose the possible offsets are within $W$ of either $-A$ or $A$, with $A>W$. The public polynomial $P=x^2-A^2-W^2$ stays between $-2AW$ and $2AW$ on both ranges. A quartic in the integer basis $1,x,P,xP,P^2$ therefore serves both at once. The separation has a cost. Even the best real monic quadratic has maximum absolute value at least $2AW$ there. The displayed $P$ attains that value. [Two-window proof and exact bound](../PrimeFactors/PairedDivisorWindows.lean)

For 9,009, the smaller-divisor range gave midpoint 83. We checked the groups $75,77,79$ and $87,89,91$. One quartic found divisors 77 and 91 in the two different groups. It took 24 row swaps and 34 size reductions. Testing the groups separately took two lattice reductions with 59 swaps and 83 size reductions in total. One ordinary quartic on the enclosing interval missed its bound. This example has several divisors in the smaller-factor range. Its checked prime factorization is $3^2\cdot7\cdot11\cdot13$. A semiprime with two unequal primes has only one prime below the square root. [Reproducible comparison and certificate](https://marius-bughiu.github.io/prime-factors/#paired-divisor-windows-9009)

## What does an equation for the other factor add?

If $xy=N$, then multiplying $x^iy^j$ by $x^B$ gives $N^jx^{B+i-j}$ for $j\le B$. All monomials on the same diagonal $i-j$ contribute to the same coefficient. Lean proves that the full rectangle of such monomials spans exactly the corresponding one-variable lattice. Shifting to an equation for the cofactor can still select a different short row. After expressing both rows in the same variable, we can test whether their common roots give additional information. [Elimination and cofactor transform](../PrimeFactors/FactorCurveElimination.lean)

For 2,501, the two selected equations were proportional after this substitution. For 6,901, their only common rational index was $-1$. It gave $69+2(-1)=67$ and $6,901=67\cdot103$. The one-sided search already recovered this pair. Having two equations helps only to the extent that their common roots narrow what the first equation leaves possible. [Both checked cases](../PrimeFactors/FactorCurveElimination.lean)
