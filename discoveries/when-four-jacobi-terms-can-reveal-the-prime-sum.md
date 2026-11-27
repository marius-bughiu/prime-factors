# When four Jacobi terms can reveal the prime sum

For $143$, the shortest four-term identity in the even Jacobi moments spans 11 positions. Doubling 11 and adding two gives 24, the sum of 11 and 13. For $247$, the shortest span is 12 and a second formula gives 32, the sum of 13 and 19. **Measuring the minimum is the expensive step.** In all six small tests, the measurement had already exposed a factor by a gcd before establishing the minimum. [Minimum-span theorem](../PrimeFactors/JacobiFourMinimum.lean) · [Product-only experiment](../experiments/jacobi_four_width.py)

## What the minimum measures

Let $N=pq$ with distinct odd primes. Write $a=(p-1)/2$ and $b=(q-1)/2$, and assume $4<a<b<2a$. Consider four distinct positions in the positive even Jacobi moment sequence. Combine their readings with fixed coefficients invertible modulo $N$. Require the combination to be zero at every starting position. We can normalize the last coefficient to one. The **span** is the difference between the greatest and least positions. The smallest possible span $D$ is

| Condition | Minimum span | Factor sum |
| --- | ---: | ---: |
| $2b\ne3a$ | $a+b$ | $2D+2$ |
| $2b=3a$ | $2a$ | $5D/2+2$ |

Thus a supplied or measured minimum gives at most two candidate sums. For each candidate $S$, compute $S^2-4N$ and check whether it is a nonnegative square giving two proper factors with product $N$. A longer identity by itself does not supply the minimum. [Minimum and its hypotheses](../PrimeFactors/JacobiFourMinimum.lean) · [Sum and factor readout](../PrimeFactors/JacobiFourUpper.lean)

In the ordinary construction, the four positions are $0,a,b,a+b$. The terms cancel in one pairing modulo $p$ and in a different pairing modulo $q$. When $a=2h$ and $b=3h$, positions $0,h,3h,4h$ suffice. To prove minimality, the coefficients in each exponent class at either prime must sum to zero. A class with just one of the four unit coefficients cannot do so. The lower-bound proof classifies the arrangements that meet this condition for both primes. Constructing either displayed pattern uses the local periods of the unknown factors. [Constructions](../PrimeFactors/JacobiFourUpper.lean) · [Arrangement of four offsets](../PrimeFactors/JacobiFourSpan.lean)

## What the product-only search actually did

The panel contains all six products of distinct primes from $11,13,17,19$. The checker uses the same span cap of 24 throughout. It first computes all $N$ Jacobi signs, then $N+24$ consecutive even moments with $N$ modular term updates each. For each possible set of offsets it tests coefficient choices modulo $N$. The first equation determines the constant coefficient, and a four-equation lookup eliminates most other choices. Survivors are checked over a block of $N$ starting positions and their coefficients tested for invertibility. A block this long spans a full period because $(p-1)(q-1)<N$ is a period. Periodicity also lets the search translate the least offset to zero. The fixture's prime factors enter only after the measurements. [Checker](../experiments/jacobi_four_width.py) · [Fixture](../benchmarks/jacobi-four-width.json)

| Product | Minimum span | Modular term updates | Coefficient lookups | First proper gcd (span) |
| ---: | ---: | ---: | ---: | ---: |
| 143 | 11 | 23,881 | 21,312 | 13 (6) |
| 187 | 13 | 39,457 | 48,376 | 17 (8) |
| 209 | 14 | 48,697 | 68,866 | 19 (9) |
| 221 | 14 | 54,145 | 74,156 | 17 (8) |
| 247 | 12 | 66,937 | 46,512 | 19 (9) |
| 323 | 17 | 112,081 | 207,386 | 19 (9) |

At 247 the search examined 190 offset sets, prepared 5,658 coefficient table entries and tested 24 candidates against the full equations. A shorter identity had a coefficient of 38, and $\gcd(38,247)=19$. The search recorded that factor and continued to establish the minimum for unit coefficients. The previously proved first exceptional moment is another way to read a factor from the same data. Direct summation over all residues at every degree gives no practical large-input procedure here. [What the first exceptional moment reveals](when-jacobi-moments-first-change.md)

The exceptional case also admits a one-square shortcut. Under $2b=3a$, we have $3p-2q=1$ and $24N+1=(6p-1)^2$. At 247 the square root is 77, giving $(77+1)/6=13$ and $(77-1)/4=19$. The opposite relation $3p-2q=-1$ makes the same expression a square with the signs reversed. At 187 the root is 67, giving $(67-1)/6=11$ and $(67+1)/4=17$, even though its minimum span follows the ordinary formula. Testing both integer quotient pairs and checking their product recovers these two cases in one square-root calculation each. The other four inputs fail the square test. Run `python3 -m experiments.jacobi_four_width` to reproduce the panel. [Square identities and checked prime products](../PrimeFactors/JacobiFourUpper.lean)
