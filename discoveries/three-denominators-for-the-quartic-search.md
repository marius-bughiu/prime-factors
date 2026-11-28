# Three denominators give the same answer as 2,048

For a 2,048-bit product of two distinct 1,024-bit primes, we can replace **2,048 denominator trials by three**. The two searches return the same pair of primes or both report failure, for every such input. The gain concerns one particular search using Sophie Germain’s identity. Even after trying every denominator through 2,048, fewer than one in $2^{1102}$ eligible products qualify. [Executable equality and population theorem](../PrimeFactors/ThreeQuarticDenominators.lean)

## What the search reads from the product

Choose a denominator $d$ and compute $M=d^4N$. Test whether $M=a^4+4b^4$ for positive integers $a,b$. One branch guesses $a$ as the integer fourth root of $M$. The other guesses $b$ as the integer fourth root of $\lfloor M/4\rfloor$. In each branch one more fourth root supplies the other candidate coordinate, and an exact equality checks it. These branches recognize precisely the representations with $M<(a+1)^4$ or $M<4(b+1)^4$, respectively. A fixed denominator costs at most four integer fourth roots. [The two recognition intervals](reading-the-other-fourth-power.md)

The identity gives $A=a^2+2b^2-2ab$ and $B=a^2+2b^2+2ab$ with $AB=M$. Take the gcd of each with the original $N$. The program returns the gcds in increasing order after checking that both exceed one and multiply to $N$. For eligible inputs and $d\le2048$, either successful branch gives the prime pair. The executable routine takes only $N$ and uses the fixed list $[1,725,1517]$. [Gcd extraction and search](../PrimeFactors/ScaledQuarticReadings.lean)

## Why the other trials can be skipped

1. Given any successful representation, cancel $g=\gcd(a,b)$. Since $N$ is squarefree, $g$ divides $d$. The reduced representation still satisfies the corresponding strict recognition interval. Every successful trial therefore has a primitive witness at a divisor of its denominator. [Cancellation and preservation of the interval](../PrimeFactors/ReduceQuarticDenominator.lean)
2. In a primitive witness, the denominator splits as $d=uv$ with $u,v$ coprime. Its primes are all $1\bmod 4$. Up to the order of $p,q$, the two identity factors are $u^4p$ and $v^4q$. For a balanced odd prime pair with $6d^4\le N$, these conditions and the factor ratio already give a minimum nontrivial denominator of **221**. The earlier 48-bit example attains it with a supplied rational point. [Denominator split](../PrimeFactors/QuarticDenominatorSplit.lean) · [Sharp minimum for supplied points](../PrimeFactors/LeastPrimitiveQuarticDenominator.lean)
3. At 2,048 bits the recognition interval forces one quartic coordinate to be much smaller than the other. This makes $8B\le9A$, which together with $q\le2p$ implies both $4u^4\le9v^4$ and $4v^4\le9u^4$. For $uv\le2048$, the only coprime splits satisfying both conditions are $1\times1$, $25\times29$ and $37\times41$, up to ordering. Every denominator through 724 gives only successes already available at 1. Whether the two larger denominators add full-size successes remains open. [Bounds and finite enumeration](../PrimeFactors/QuarticStripDenominators.lean) · [Equality for both denominator ranges](../PrimeFactors/ReduceQuarticDenominator.lean)

For the coverage bound, each of the three scales gives fewer than $2^{2092}$ as an upper bound for the scaled product. The first branch has $a<2^{523}, b<2^{393}$. The other has $a<2^{394}, b<2^{523}$. Counting coordinate pairs therefore gives at most $3\cdot2^{916}$ eligible products per denominator before testing primality. Summing this upper bound over the three denominators and comparing with a proved lower bound on the eligible prime population gives the stated share. [Coordinate counts and population comparison](../PrimeFactors/ScaledQuarticMenuBound.lean)

## Examples where scaling adds a factorization

| Input | Only successful denominator among the three | Prime factors | First successful ordinary Fermat test |
| --- | ---: | --- | ---: |
| 96,702,339,781 | 725 | 229,777 × 420,853 | 14,346 |
| 194,329,760,155,033,121 | 1,517 | 362,037,209 × 536,767,369 | 8,573,797 |

Both inputs were constructed to have a representation. In the second example $1517^4N=189173^4+4\cdot22521920^4$. The formula recovers these coordinates from the scaled product alone. Both outputs have 29 bits, and their product has 58. The first example has prime widths 18 and 19. Lean checks the failed branches, successful branches, prime factors and products for both inputs. The last column counts consecutive integer midpoints starting at $\lceil\sqrt N\rceil$ and ending at $(p+q)/2$. [Exact branch outcomes](../PrimeFactors/ScaledQuarticControls.lean) · [Fermat benchmark fixtures](../benchmarks/cases.json)
