# An exact count that determines the factors

For $N=pq$ with distinct primes above 864, consider the publicly computable twelve-residue key. **Knowing exactly how many different regular keys occur determines a prime factor with at most four square roots and gcds.** Conversely, knowing the factors gives the count with two integer divisions and a multiplication. A fast general way to compute this count would therefore give a fast general way to factor these products. [Lean proof and worked example](../PrimeFactors/TwelveImageSize.lean)

## Why the count contains a factor

For a regular residue $x$, the key is the fraction

$$
\frac{(x^6-45x^4+135x^2-27)^2}{(x^2+3)^6}\pmod N.
$$

The mask must be a unit so the denominator is invertible and the local fibers have their full size. Modulo either prime $p$, the five distinct inputs $0,1,-1,3,-3$ fail the mask. Its polynomial has degree 13, so at most thirteen inputs fail it. Exactly twelve regular inputs give each attainable key. Consequently the number of distinct keys is $M_p=\lfloor(p-5)/12\rfloor$, and $12M_p$ is the number of regular inputs. The Chinese remainder theorem allows every pair of local regular inputs and every pair of attainable local keys. The public image therefore has size $K=M_pM_q$. [Twelve-to-one map and mask](../PrimeFactors/TwelveResidueCollision.lean) · [Image count over the product](../PrimeFactors/TwelveImageSize.lean)

Write $p=12M_p+e$ and $q=12M_q+f$. Each offset is one of $5,7,11,13$. The public residue of $N$ restricts their product $w=ef$ to the following list.

| $N\bmod12$ | Possible $w$ |
|---:|---|
| 1 | 25, 49, 121, 169 |
| 5 | 65, 77 |
| 7 | 55, 91 |
| 11 | 35, 143 |

For the correct $w$, expand $144K=(p-e)(q-f)$. Then $T=N+w-144K=fp+eq$, and the roots of $X^2-TX+wN$ are $fp$ and $eq$. The gcd of $N$ with the larger root recovers one prime because the weights are smaller than either prime. This gives at most two distinct quadratics in three of the four residue classes. [Checked table and recovery theorem](../PrimeFactors/TwelveImageSize.lean)

For $N=781{,}447$, a product-only enumeration of all residues found 767,376 regular inputs and **5,329 distinct keys**. The two possible weights are 55 and 91. Weight 55 gives $T=14{,}126$ and discriminant $5{,}256^2$. The larger root is 9,691 and $\gcd(9{,}691,781{,}447)=881$. The other prime is 887. Weight 91 has negative discriminant. Lean certifies the count and the factorization independently. The exhaustive count itself already encountered a proper gcd of 887 at input 186 while testing whether the mask was a unit. Enumerating all $N$ inputs would be impractical at 2,048 bits. [Kernel-checked arithmetic](../PrimeFactors/TwelveImageSize.lean) · [Mask and batched key evaluation](../experiments/twelve_residue_collision.py)

## Sampling keys to find a factor

There is also a result that needs no full image count. Fix two distinct 1,024-bit primes. Draw $2^{511}$ independent, uniform regular residues modulo their product, with replacement. The probability that some pair of normalized keys agrees at exactly one prime is **greater than 95%**. Comparing the original residues themselves on the same draws gives probability **at most $7/16$**. A single-coordinate agreement gives a proper gcd of the public difference with $N$. The comparison concerns the existence of a successful pair in the full sample. It still requires an infeasible number of draws and a way to find the matching pair. [Concrete regular seeds and key reductions](../PrimeFactors/TwelveSeedBirthday.lean) · [Finite sampling bounds](../PrimeFactors/UniformFiberBirthday.lean)
