# Which squares does a rational rectangle miss?

With the product 323 and the target 2, try numerators and denominators from 1 through 3. The choice $i=1$, $j=3$ gives $i^2-2j^2=-17$. Its gcd with 323 reveals 17, and division gives 19. If we try every target with Jacobi symbol $-1$ modulo 323, the same nine cells succeed on **119 of 144**. We can say exactly which targets escape and why. [Batch gcd proof](../PrimeFactors/CircleMarkRationalProduct.lean) · [Verified 323 example](../PrimeFactors/CircleMarkRationalTargetCount.lean)

## Which targets escape?

Write $N=pq$ for two distinct odd primes. We can compute the Jacobi symbol of a target $a$ using $N$ alone. A symbol of $-1$ means exactly one prime, say $p$, admits a square root $r$ of $a$. For denominator bound $D$ below both primes, a rectangle hits precisely when some fraction $i/j$, with $1\le i\le H$ and $1\le j\le D$, equals $r$ or $-r$ modulo $p$. Every hit reveals $p$ by gcd. The earlier square-grid method used this relation with $H=D$. [Earlier square search](short-norm-boxes.md) · [Rectangular equivalence](../PrimeFactors/CircleMarkRationalCover.lean)

For positive $H,D$, put $A=H+1$ and $B=D+1$. **Every nonzero square at $p$ is covered exactly when $AB>p$.** If $p=AB+s$ with $0<s<\min(A,B)$, the missing squares are exactly

$$
\left\{(A/t)^2\bmod p : t\text{ is a positive divisor of }s\right\}.
$$

Division here means multiplication by the inverse modulo $p$. Distinct divisors give distinct squares. For 323, $A=B=4$. Modulo 17 the excess is 1 and only 16 escapes. Modulo 19 the excess is 3 and the omitted squares are 16 and 6. Seven square targets are covered at each prime. The Chinese remainder theorem pairs each covered square modulo 17 with any of nine nonsquares modulo 19, or each covered square modulo 19 with any of eight nonsquares modulo 17. That gives $7\cdot9+7\cdot8=119$ successes among $2\cdot8\cdot9=144$ possible targets. More generally, if both primes exceed $AB$ by positive amounts $s_p,s_q<\min(A,B)$, the fraction of all negative-Jacobi targets hit at this fixed product is $1-\tau(s_p)/(p-1)-\tau(s_q)/(q-1)$, where $\tau$ counts positive divisors. [Exact target-frequency formula](../PrimeFactors/CircleMarkRationalTargetCount.lean) · [Sharp threshold](../PrimeFactors/CircleMarkRationalCover.lean) · [Distinct squares and divisor count](../PrimeFactors/CircleMarkRationalTwoHoles.lean)

There is an exact formula for larger excesses too. Take coprime positive denominators $b,d\le D$ with $b+d\ge B$. Find nonnegative $u,v$ satisfying

$$
 (b+d-B)A+du+bv=s.
$$

Each solution gives a missing root $(A+u)/b$ modulo $p$, and each missing root gives exactly one solution. The proof locates the nearest positive and negative residues of $jr$ as $j$ runs from 1 to $D$. When both miss the numerator range, their magnitudes are $A+u$ and $A+v$. Their denominators obey $d(A+u)+b(A+v)=p$, which gives the displayed equation. Using this classification directly requires the prime $p$. [Farey bracket, uniqueness and exact parametrization](../PrimeFactors/CircleMarkRationalDeficit.lean)

Far below the threshold, different cells can represent the same fraction. Let $F$ be the number of coprime pairs in the rectangle. When $2HD<\min(p,q)$, a uniformly chosen negative-Jacobi target at this fixed product hits with probability $F/(p-1)+F/(q-1)$. For example, $1/1$ and $2/2$ coincide. At $143=11\cdot13$, a $2\times2$ rectangle succeeds on 33 of 60 targets. Testing four consecutive integers instead succeeds on 44. [Coprime pairs and exact target frequency](../PrimeFactors/CircleMarkRationalFrequency.lean)

## What the search actually found

The search received only the product and the promise of equal factor width. It selected the first positive target with Jacobi symbol $-1$. All 2,465 products in the census passed through this selector without an early factor. The wider rectangles used a public upper bound for either prime to guarantee coverage. [Search and comparison methods](../experiments/circle_mark_rational_grid.py) · [Counts and three certified examples](../benchmarks/circle-mark-rational-grid.json)

| Bits per prime | Eligible products | Fixed 8 × 8 hits | Wider rectangle with 8 numerators | Near-square rectangle |
|---:|---:|---:|---:|---:|
| 6 | 14 | 14 | 14 | 14 |
| 7 | 42 | 33 | 42 | 42 |
| 8 | 148 | 20 | 148 | 148 |
| 9 | 543 | 10 | 543 | 543 |
| 10 | 1,718 | 3 | 1,718 | 1,718 |

The smallest rescue was $8{,}633=89\cdot97$. With target 3, the 8 × 8 rectangle missed. Extending the denominators through 14 found $i=7$ and $j=9$, giving $7^2-3\cdot9^2=-194=-2\cdot97$. Batching the rectangle uses one final gcd after polynomial evaluation. Across the 1,718 ten-bit products, the near-square batch took **1.082 s** and checking cells individually until the first hit took **0.059 s**. A folded wheel search of the factor interval took **0.015 s**, and Fermat took **0.00183 s**. These are median CPU times over three trials on an Apple M4 using CPython 3.9.6, including per-product setup. [Reproduce with the timing option](../experiments/circle_mark_rational_grid.py)

Across all five cohorts the near-square batches covered 1,952,416 cells, performed 477,854 packed polynomial multiplications and used 2,465 final gcds. Checking the same rectangles directly took 885,309 gcds with early stopping. The selector also made 6,321 Jacobi tests. [Recorded operation counts](../benchmarks/circle-mark-rational-grid.json)

## What the result says at 2,048 bits

For a 1,024-bit prime, a rectangle near the universal threshold has roughly $2^{512}$ entries **on each side** when its shape is balanced. A polynomial batch can cover many cells with one gcd, but it still builds the numerator polynomial and evaluates it at the denominator points. Counting $HD$ gives the number of implicit cells. Classical interval factoring also batches products with polynomial evaluation at this fourth-root scale. [Threshold and list-size tradeoff](../PrimeFactors/CircleMarkRationalCover.lean) · [Polynomial computation](../PrimeFactors/CircleMarkRationalProduct.lean) · [Bostan, Gaudry and Schost on fast interval products](https://cs.uwaterloo.ca/~eschost/publications/pollard.pdf)

Count each product of two distinct 1,024-bit primes with a 2,048-bit product once. Even allowing the best rectangle shape **and** any negative-Jacobi target from 1 through 2,015,165 for each product, fewer than one in three products has a hit at $HD\le2^{975}$. At $HD\le2^{900}$ the fraction is below $2^{-76}$. These two bounds are unconditional. For the actual first negative-Jacobi target, fewer than half of the products have a hit even at $HD\le2^{994}$, under the Ernvall-Hytönen–Palojärvi prime-count estimates at the required endpoints for modulus 120,120. Lean takes those estimates as hypotheses. The open factoring question is how to locate a successful cell cheaply using the product alone. [Full-width population proofs](../PrimeFactors/CircleMarkRationalPopulation.lean) · [Published prime-count estimates](https://arxiv.org/abs/2003.01925) · [Analytic assumptions](../docs/research.md)
