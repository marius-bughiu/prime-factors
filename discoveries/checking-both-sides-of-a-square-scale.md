# Checking both sides with one scaled square root

On all 32,385 products of two distinct 12-bit primes, trying squarefree scales through 16 found the factors of 321 products using $(p-1)(q-1)$ alone. Checking $(p+1)(q+1)$ as well found 638. Both checks use the same scaled square root. Ordinary Fermat search found 13,818 products with the number of square roots the two-sided method actually spent on each input. The two-sided method found 463 products that this Fermat comparison missed. [Complete small census](../benchmarks/opposite-square-scales.json) · [Replay](../experiments/opposite_square_scales.py)

## The same root gives two possible sums

Let $N=pq$, $1<p<q<2p$, and $S=p+q$. The two products of interest are $N+1-S$ and $N+1+S$. Given a positive guess $t$, compute $r=\lfloor\sqrt{N/t}\rfloor$. If $t\ge2$, a true representation $N+1-S=t y^2$ requires $y=r$, and $N+1+S=t z^2$ requires $z=r+1$. For $t=1$ the two root guesses are $r-1$ and $r+2$. This gives the two public candidates $s=N+1-ty^2$ and $u=tz^2-N-1$. The first successful scale on each side is the squarefree part of the corresponding product. [Predecessor root](../PrimeFactors/DiscriminantStride.lean) · [Successor root and minimum](../PrimeFactors/SuccessorSquareScale.lean)

For example, at $551{,}987$ the integer square root is 742. The successor root guess at scale one is 744. Subtracting $N+1$ from $744^2$ gives the sum $1{,}548$ and the two factors $557$ and $991$. This example was selected because the successor product is square. The predecessor scan exhausted all eleven squarefree scales through 16. [Selected positive and negative controls](../benchmarks/opposite-square-scales.json)

## Which candidate deserves a discriminant test?

A balanced prime sum satisfies $4N<S^2\le 9N/2$. For $N\ge9$, even **different** sums $s,u$ in that interval cannot yield the same square scale on opposite sides. To see why, write $L=\sqrt N$, $v=\sqrt{N+1-s}$ and $w=\sqrt{N+1+u}$. When both sums exceed $2L$, we get $v<L-1$ and $w>L+1$. When both sums meet the upper bound, each is at most $17L/8$. Squaring the endpoints gives $v\ge L-11/10$ and $w\le L+11/10$. Together these conditions force $2<w-v\le11/5$. But $(w-v)^2=t(z-y)^2$ is an integer, and there is no integer strictly between 4 and 5. [Lean separation and selection](../PrimeFactors/OppositeSquareScaleBands.lean)

This gives a rule before doing a discriminant square root. If $t(z-y)^2\le4$, only the **larger** sum could pass the lower bound. Otherwise only the **smaller** sum could pass the upper bound. For the squarefree scan the first case occurs at 2 and 3. Scale one uses roots three apart, so it is in the second case. The program forms the two sums, compares them, and tests only the selected one against the interval. A passing sum still needs a square discriminant and a verified factor. [Scan with independent checks on the discarded sign](../experiments/opposite_square_scales.py)

## Cost on complete small prime populations

| Bits per prime | Products | Predecessor only, through 16 | Both sides, through 16 | Predecessor only, matched roots | Fermat, matched roots |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 10 | 2,775 | 89 | 172 | 89 | 2,023 |
| 12 | 32,385 | 321 | 638 | 319 | 13,818 |

The cap permits eleven squarefree scales. The matched runs receive the two-sided scan’s actual root count on each product, including its discriminant roots. Fermat spends one root on its starting midpoint. The matched predecessor search can go past scale 16 when its budget allows. On the 12-bit population the two-sided scan used 352,884 scaled roots and 21,341 discriminant roots in total. The original used 354,575 and 9,537. Adding the second sign reduced the first count through earlier stops and increased the second by admitting more sums into the window. The comparison counts roots and records the extra sign comparisons. It gives no elapsed-time estimate for a large input. [All counts](../benchmarks/opposite-square-scales.json)

## The mixed signs give the factor gap

The other two products, $(p-1)(q+1)$ and $(p+1)(q-1)$, are $N-1-G$ and $N-1+G$ with $G=q-p$. If either is $t$ times a square, its root is $r$ or $r+1$. The nearer of the two scaled squares to $N-1$ gives the gap. A proposed gap can be tested by checking whether $G^2+4N$ is a square. For $2{,}627=37\times71$, scale two gives $r=36$. Then $2\times36^2=2592$, and $2626-2592=34$ is the true gap. Its square plus $4N$ is $108^2$, giving the factors $(108\pm34)/2$. [Mixed-sign root bounds](../PrimeFactors/MixedSquareScale.lean) · [Worked controls](../benchmarks/four-neighbor-scales.json)

All four neighboring products are divisible by four for odd primes. If $t$ is squarefree, the root in a successful product must therefore be **even**. At $t\ge2$ precisely one of $r,r+1$ is even. Its scaled square $X$ is the only value to consider for all four sign choices. The two candidates read from it are the distance from $X$ to $N+1$ for the sum and to $N-1$ for the gap. At $t=1$ the sum uses a second square, still from the same integer square root of $N$. The balanced sum and gap windows cannot both pass at even roots of the same scale. Thus at most one discriminant root is needed per guess. [Parity and separation of the two windows](../PrimeFactors/FourNeighborSquareBands.lean)

| Bits per prime | Products | Four signs, through 16 | Two signs, matched roots | Fermat, matched roots | Four signs only vs. Fermat |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 10 | 2,775 | 347 | 168 | 2,079 | 152 |
| 12 | 32,385 | 1,343 | 661 | 14,500 | 919 |

In this table both comparisons receive the four-sign scan’s actual root allowance on the same product. The two-sign comparison uses the even-root rule and can continue past scale 16 if its budget permits. On the 12-bit population the four-sign scan used 348,977 scaled roots and 66,792 discriminant roots. It succeeded on 706 products that the two-sign comparison missed and missed 24 that the comparison found. These are exhaustive small populations. [Census and operation counts](../benchmarks/four-neighbor-scales.json) · [Replay](../experiments/four_neighbor_scales.py)

## Two checks using the published 2,048-bit factors

Neither the fresh nor the crossed comparison product admits **any** representation $(p\pm1)(q\pm1)=t y^2$ with $1\le t\le2^{40}$. Both receipts use the two known primes to certify the exclusion. For the fresh input, two auxiliary primes from its published primality construction also contribute to the predecessor and mixed-sign bounds. [Fresh certificate](https://marius-bughiu.github.io/prime-factors/proofs/opposite-scale-valuations-fresh-2048.lean) · [Crossed certificate](https://marius-bughiu.github.io/prime-factors/proofs/opposite-scale-valuations-crossed-2048.lean) · [Certificate generator](../experiments/opposite_scale_valuations.py)

For the successor product on the fresh input, primes appearing to odd multiplicity forced $261{,}956{,}129\mid t$. This left just 4,197 positive multiples below the cap. After dividing out the forced part, each remaining multiplier times the reduced product had to be a square modulo every test prime. Small primes through 97 excluded them all. On the crossed successor product, 3,693 remaining multipliers were excluded by primes through 43. One crossed mixed product required a similar check on 3,077 multipliers, ending at 47. On the other branches the forced divisor already exceeded the cap. [Valuations, survivors and input provenance](../benchmarks/opposite-scale-valuations.json)

## How often can the four tests work at full size?

Choose uniformly among sorted pairs of distinct 1,024-bit primes whose product has 2,048 bits. The bounds below count every pair for which **any** of the four neighboring products is $t$ times a square for **any** positive $t$ through the stated cap. They apply even if the choice of scale and signs uses every bit of the product. [Lean population bounds](../PrimeFactors/FourNeighborScaleFrequency.lean)

| Maximum scale | Upper bound on fraction of prime pairs reached |
| ---: | ---: |
| $2^{40}$ | Less than one in $2^{959}$ |
| $2^{1024}$ | Less than one in $2^{462}$ |
| $2^{1792}$ | Less than one in $2^{77}$ |

The middle row gives the search more scales than there are possible integers for the smaller prime. Its chance of reaching the correct factors is still below $2^{-462}$. Directly constructing a successful scale above the cap would answer a different question. The table bounds coverage by the stated scale values.

To count possible pairs, let $A,B\le H$ be positive and $AB=t y^2$. There are positive integers $d,u,v,x,z$ with $A=du x^2$, $B=dv z^2$ and $uv\mid t$. For fixed $d,u,v$, the two bounds on $A$ and $B$ allow at most $H/(d\sqrt{uv})$ pairs of square roots. Summing over $d\le H$, $u\le L$, $v\le L/u$ bounds the number of ordered integer pairs that could work at any scale through $L$ by

$$2H\sqrt L\,(1+\log H)(1+\log L).$$

Each fixed sign choice maps the prime pairs injectively into these integer pairs with $H=2^{1024}$. Adding the four bounds and using the project’s finite lower bound on eligible prime pairs gives the table. An earlier count bounded the number of divisors of each admissible neighbor product separately and gave $2^{-735}$ at the smallest cap. Counting both neighboring integers together accounts for the improvement. [Integer coordinates](../PrimeFactors/SquareScalePairCoordinates.lean) · [Finite cover](../PrimeFactors/SquareScalePairCover.lean) · [Harmonic sums](../PrimeFactors/SquareScaleHarmonicBound.lean) · [Earlier divisor bound](../PrimeFactors/OppositeSquareScalePopulation.lean)

For fixed $L$, the $H\log H$ order in the unrestricted integer box is classical already at $t=1$. Tolev gives $(6/\pi^2)H\log H+O(H)$ for the number of ordered pairs whose product is a square. Our upper count allows all scales through an explicit $L$ and applies to a subset obtained by shifting the two primes. The published integer-pair lower bound supplies no matching lower bound for that prime subset. Both the square-pair count and our upper bound are unconditional. [Tolev, p. 496](https://msp.org/pjm/2011/249-2/pjm-v249-n2-p14-p.pdf#page=3)
