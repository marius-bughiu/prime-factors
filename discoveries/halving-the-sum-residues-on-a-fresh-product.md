# Halving the factor sums allowed by an existing test

For each of our two 2,048-bit comparison products, the product alone gave a way to discard about half the possible sums that an ordinary modular square test still admits. On the fresh product, the proved reduction is **at least 49.83%** on the actual search interval. On the crossed product it exceeds **49.99%**. The ordinary test and the new test use the same modulus, the same earlier small-prime filters, and the same interval. Neither search recovered a prime from either full-size product. [Exact comparison proof](../PrimeFactors/ReciprocalTraceHalving.lean) · [Finite interval proof](../PrimeFactors/HalfPeriodWindow.lean) · [Search fixtures](../benchmarks/reciprocal-anchors.json)

On the smaller product 137,649,271, the old test left 40 possible sums and the new test left 19. Testing them in ascending order reached $24{,}160$ on the fourteenth try. Since $24{,}160^2-4N=5{,}754^2$, the primes are 9,203 and 14,957. Both methods incurred setup costs. [Four certified comparisons, candidate ranks and setup work](comparing-reciprocal-sum-classes.md)

## How the product chooses the modulus

For an odd $N$, we seek an odd $d\equiv3\pmod4$ coprime to $60N$, and two checkable roots

$$t^2\equiv-d\pmod N,\qquad e^2\equiv N\pmod d.$$

We run the continued fraction of $\sqrt{4N}$. A lower convergent with numerator $A$ and denominator $m$ gives $A^2-4Nm^2=-Q$. For odd $Q\equiv3\pmod4$, remove square factors of odd primes through 251, writing $Q=b^2d$. Then $t=A/b\pmod N$ and $e=A/(2m)\pmod d$. Every division here is a modular inversion. The search checks both root equalities on the actual integers. It also reports any proper divisor found in its gcd with $Q$. Continued-fraction norm relations are classical. Here they give a modulus for a subsequent search over divisors or sums. [Product-only implementation](../experiments/reciprocal_anchor.py) · [Morrison and Brillhart](https://doi.org/10.1090/S0025-5718-1975-0371800-5)

The full-size run used 32,768 convergent steps and selected the shortest eligible period, breaking ties by the first occurrence. It then replayed the selected convergent modulo $d$. This construction uses no expected factors. Searching for a short period costs time, and its length depends on the input.

| Input | Selected step | Square removed | Period size | Minimum complete periods in each sum progression modulo 60 |
|---|---:|---:|---:|---:|
| Fresh 2,048-bit comparison | 14,765 | $237^2$ | 1,005 bits | 148 |
| Crossed 2,048-bit comparison | 11,821 | $2259^2$ | 1,003 bits | 3,798 |

## What the two roots reveal

From $t^2\equiv-d\pmod N$, both hidden primes have Jacobi symbol $+1$ modulo $d$. For each unit residue $x$ modulo $d$, its candidate partner is $N/x$, and together they give one sum $s=x+N/x$. The ordinary test admits exactly those $s$ for which $s^2-4N$ is a square modulo $d$, including zero and nonunit squares. [Divisor sign from a public square](what-a-negative-square-says-about-every-divisor.md) · [Ordinary sum characterization](../PrimeFactors/ReciprocalTraceHalving.lean)

The second root ensures all factor pairs giving a particular sum agree on the sign. At a prime dividing $d$, any two possible first factors with that sum are equal or have product $N$. Because $N$ is a unit square there, their Legendre symbols agree. Multiplying over the prime powers gives the same Jacobi sign even when $d$ is composite. Replacing both factors by their negatives negates the sum and flips the sign. This pairs every admitted sum with an opposite one. Exactly one member can be the true sum. [Lean proof, including repeated prime factors of the modulus](../PrimeFactors/ReciprocalTraceHalving.lean)

There is also an upper bound independent of a table of residues. Only half the units have positive sign, and swapping $x$ with $N/x$ leaves the sum unchanged. For $d\le2^{1024}$, the number of reciprocal pairs to generate is at most $(\varphi(d)+2^{130})/4$. The correction counts possible fixed points of the swap. This bound applies before removing duplicate sums. For both comparison inputs, counting periods shows that at most **25.2%** of the possible sum positions left by the earlier modulus-60 filter need remain after the new restriction. For candidate divisors, at most **50.1%** of the corresponding positions need remain. These percentages use the modulus-60 baseline. [Pair enumeration bound](../PrimeFactors/ReciprocalDivisorSums.lean) · [Candidate intervals and capacities](../PrimeFactors/ReciprocalSearchWindow.lean)

## Checking one sum without a table

Given $s$, the identity $x(s\pm2e)=(x\pm e)^2$ holds for a factor residue $x$ with partner $N/x$. Where $s-2e$ is a unit, its Jacobi symbol reads the factor sign. Where it shares a prime with $d$, $s+2e$ is a unit at that prime. One gcd with a modular power separates the two parts of $d$, including repeated prime powers. Multiplying the two symbols reads the factor sign on every sum the ordinary sieve admits. This handles cases where both whole-modulus offset symbols are zero. [Gcd split](../PrimeFactors/SaturatedTraceSplit.lean) · [Exact sign formula](../PrimeFactors/ReciprocalAdaptiveCharacter.lean)

There is one canonical query per pair of opposite sum residues. Evaluate the sign on the smaller residue and use its answer to select one of the two. Over a complete period this directly generates exactly $(d-1)/2$ residues, without any inversions for the candidate factors. Intersecting the resulting set with the ordinary discriminant test gives exactly the positive-factor sum set. Generating a whole period is still enormous. On an individual candidate, testing the sign avoids building a period. Testing whether an arbitrary number is a square modulo an unfactored composite $d$ can itself take substantial work. An exact integer square root of $s^2-4N$ remains available for each surviving position. [Generator and exactness proof](../PrimeFactors/OrientedTraceClasses.lean)

## What the full-size experiments actually ran

We used the factor width to bound both primes below $2^{1024}$. Within the resulting sum interval, the earlier wheel keeps the sums of unit pairs with product $N$ modulo 60. In each remaining progression of step 60, a full period covers every residue modulo $d$. If there are $B$ complete periods, the positive sum set retains at most $(B+1)/(2B+1)$ of the ordinary test’s positions even with an incomplete final period. This is how the table above gives the two percentages at the top. It avoids enumerating either full interval. [Progression counting](../PrimeFactors/CharacterInterval.lean) · [Same-modulus bound](../PrimeFactors/HalfPeriodWindow.lean)

Each comparison tried the first 128 positions in each of six permissible sum classes, for 768 positions per product. On the fresh input, the two simple sign checks passed 204 and the canonical orientation passed 401. Their intersection needed 197 exact square roots. On the crossed input the counts were 194, 375 and 194. Every square test missed. The whole-interval theorem also uses ordinary local feasibility; the 768-position scan only used the specified sign checks before the integer square root. These counts give no runtime advantage over a direct square root at this budget. [Fixtures containing both unresolved products](../benchmarks/reciprocal-anchors.json) · [Verification and proof generation](../scripts/reciprocal_anchor_benchmark.py)
