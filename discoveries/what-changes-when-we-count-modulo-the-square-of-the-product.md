# When a count modulo the square of a product gives the prime sum

At $N=35$, exactly 1,953,875 ordered triples of remainders modulo $35^2$ satisfy

$$x^2+y^2+z^2\equiv0\pmod{35^2}.$$

Divide the count by $35^3$ and discard the remainder. The quotient is 45. Subtract 35 and add two to get **12**, the sum of the two primes. Knowing the sum and product gives the primes as the two roots of $X^2-12X+35=0$. The same counting rule holds for every pair of distinct 1,024-bit primes. Computing the required count cheaply from a large product remains open. [Lean proof of the reading and its precision](../PrimeFactors/SquaredConeSum.lean)

## Which triples carry the information?

First use remainders modulo $N$ itself. Take distinct odd primes $p,q$ with $N=pq$. There are exactly $N^2$ ordered triples whose squares sum to zero modulo $N$, including the origin. This total is already known from $N$. A more selective count, $P$, keeps triples satisfying $\gcd(x,y,z,N)=1$. This excludes the zero triple at each prime in the Chinese remainder representation. There are $p^2-1$ choices at one prime and $q^2-1$ at the other. Consequently

$$P=(p^2-1)(q^2-1),\qquad (N+1)^2-P=(p+q)^2.$$

For 35 there are 1,225 triples in all and 1,152 survive that restriction. The difference $36^2-1{,}152=144$ gives the sum 12 by a square root. The test for keeping an individual triple uses its coordinates and $N$. Knowing how to test one triple gives no fast census. [Prime-field count](../PrimeFactors/ThreeSquareCone.lean) · [Composite count, gcd condition and sum identity](../PrimeFactors/SemiprimeThreeSquareCone.lean)

## What changes at the squared modulus?

At one odd prime $p$, each solution modulo $p$ other than the origin has exactly $p^2$ lifts to solutions modulo $p^2$. At the origin, all three new coordinates can independently be any multiple of $p$, giving $p^3$ lifts. Thus the count at $p^2$ is $(p^2-1)p^2+p^3$. Lean checks all 99 solutions at modulus 9 by direct enumeration. [Proof of the two lift counts](../PrimeFactors/PrimeSquareThreeSquareCone.lean)

These local counts are classical. Tóth gives the counts at every prime power and a general sum over the square divisors of an odd modulus. At modulus $N^2$, that sum includes the divisors associated with both unknown primes. The closed form alone leaves their contributions to be evaluated. [Tóth, equation (30) and Corollary 37](https://arxiv.org/pdf/1404.4214#page=15)

The Chinese remainder theorem combines the prime-square counts. Write $C$ for the count at $N^2$. It has the exact value

$$C=N^2(p^2+p-1)(q^2+q-1).$$

To see where the prime sum appears, set $S=p+q$ and $D=(q-p)^2+S-1$. Expanding gives $C=N^3(N+S-1)-N^2D$. When $5\le p<q\le2p$, the proof puts $D$ strictly between zero and $N$. Dividing by $N^3$ therefore gives a number strictly between $N+S-2$ and $N+S-1$. Its integer part determines $S$. Both sides of this size condition are automatic for distinct 1,024-bit primes in increasing order. [Identity and interval proof](../PrimeFactors/SquaredConeSum.lean)

| Product $N$ | Count $C$ | Integer part of $C/N^3$ | Predicted sum | Actual sum |
| ---: | ---: | ---: | ---: | ---: |
| $35=5\cdot7$ | 1,953,875 | 45 | 12 | 12 |
| $77=7\cdot11$ | 42,718,445 | 93 | 18 | 18 |
| $65=5\cdot13$ | 22,177,025 | 80 | 17 | 18 |

The last row illustrates the condition $q\le2p$. All three counts were independently computed from the product alone on these small examples. Set $m=N^2$ and tally how often each square remainder occurs among $0,\ldots,m-1$, giving counts $h(a)$. The census is $\sum_{a,b}h(a)h(b)h(-a-b)$ with the arguments read modulo $m$. The Lean examples separately verify the numbers from the proven count formula. The benchmark rows certify the small factorizations with the project's ordinary small-prime tests. [Lean numerical controls](../PrimeFactors/SquaredConeSum.lean) · [Baseline fixtures](../benchmarks/cases.json)

## How accurate must an estimate be?

An integer estimate $v$ with $|v-C|\le N^3/2$ also determines the exact sum. The sum of two odd primes is even, so the intervals for successive possible sums leave room for rounding. The formula is

$$S=2\left\lfloor\frac{2v+3N^3}{4N^3}\right\rfloor-N+1.$$

The public value $N^4$ already gives a surprisingly close estimate. Lean proves $0<C-N^4<3N^4/p$. Yet the interval above gives $C-N^4>N^3(S-2)$ for balanced primes. The easily computed estimate misses by far more than the permitted half cube. This distinguishes a small *relative* error from accuracy sufficient to learn even the sum. [Rounding theorem](../PrimeFactors/SquaredConeSum.lean) · [Error of the public estimate](../PrimeFactors/ConeSamplingBudget.lean)

There are $N^6$ possible triples modulo $N^2$. For $B$ independent, uniform draws the chance of seeing even one solution is below $2B/N^2$. There is also a limit that holds for every sample. If $0<B\le N^2/4$, multiplying the fraction of hits by $N^6$ gives either zero or at least twice the true count. Its relative error is at least 100%. These bounds apply to uniform sampling and that particular estimator. Whether another way of measuring the count can reach the required precision remains open. [Exact probability and estimator bound](../PrimeFactors/ConeSamplingBudget.lean)
