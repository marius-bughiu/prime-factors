# Which marked coordinates can be skipped?

On **3,127**, two consecutive gcd tests can be skipped, and the very next coordinate gives a factor. Start with target 3. A coordinate $x$ is *marked* when $x^2-3$ shares a factor with 3,127. Both prime factors have six bits, so each is at most 63 and at least $\lfloor3127/64\rfloor+1=49$. At $x=9$ and $10$, the remainders are 78 and 97. Both exceed 63 and fall below $2\cdot49$, so neither can be a positive multiple of a factor. At $x=11$ the remainder is 118 and its gcd with 3,127 is **59**. Lean checks the skipped coordinates and the successful endpoint. [Cofactor bands and worked example](../PrimeFactors/CircleMarkCofactorBands.lean)

The same rule preserved the first factor found on all **27,527** products in a small census and cut the combined gcd count by **8.52%**. To see how much that saving means for large products, we can bound both the number of coordinates skipped and the distance to the first mark. [Census receipt](../benchmarks/circle-mark-prefix-skip.json) · [Full-size population bound](../PrimeFactors/CircleMarkSmallTargetPopulation.lean)

## Two reasons to skip a coordinate

Let $N=pq$ with distinct odd primes. Choose a positive target $a$ whose Jacobi symbol modulo $N$ is $-1$. This public check means $a$ is a square at exactly one of the primes. Thus $x^2-a$ can be divisible by at most one of them, and every mark gives a proper factor by a gcd. If the factors have $w$ bits, public bounds for both are $P=\lfloor N/2^w\rfloor+1$ and $H=2^w-1$. [What a mark certifies](../PrimeFactors/CircleBranchCount.lean) · [Public factor floor](../PrimeFactors/CircleMarkSmallTargets.lean)

**At the start**, any nonzero remainder of absolute value below $P$ is too small for a mark. A zero remainder would make $a$ an integer square, contradicting the Jacobi check. For $a<P$, every coordinate through $\lfloor\sqrt{a+P-1}\rfloor$ can therefore be skipped, including the endpoint. The strict size bound matters. At $N=77$, target 2 and factor floor 7, coordinates 0, 1 and 2 miss, but $3^2-2=7$. [Initial interval and sharp example](../PrimeFactors/CircleMarkSmallTargets.lean)

**After the start**, a positive remainder $y=x^2-a$ at a mark must lie between $kP$ and $kH$ for some positive integer cofactor $k$. The largest possible $k$ is $\lfloor y/P\rfloor$. If even that $k$ gives $kH<y$, we can jump to $\lceil\sqrt{a+(k+1)P}\rceil$. Keeping that endpoint preserves exactly the same set of marks through any stopping coordinate. Once $k(H-P)\ge P-1$, consecutive bands touch or overlap and every larger remainder belongs to a band. The theorem also allows a known multiplier coprime to $N$ to be removed from $y$ before testing band membership. The census uses the original remainder throughout. [Jump, endpoint and coverage proofs](../PrimeFactors/CircleMarkCofactorBands.lean)

## How many tests did the small census save?

Each row includes every pair of distinct primes with the indicated bit width whose product has twice that many bits. The searches used the product and width as inputs. They tested targets from 2 upwards until the first negative Jacobi symbol, then compared the first positive marked coordinate and its factor. Reference prime labels checked the answers. Fermat's comparison started at the ceiling of the square root of the same product and tested consecutive midpoints. [Reproducible experiment](../experiments/circle_mark_prefix_skip.py) · [Fermat implementation](../scripts/factor.py)

| Factor bits | Products | Gcds testing every coordinate | Gcds after skips | Fermat midpoint tests |
|---:|---:|---:|---:|---:|
| 7 | 42 | 997 | 568 | 65 |
| 8 | 148 | 7,661 | 5,479 | 363 |
| 9 | 543 | 60,916 | 48,488 | 2,244 |
| 10 | 1,718 | 341,537 | 286,327 | 14,258 |
| 11 | 5,530 | 2,292,356 | 2,039,618 | 82,017 |
| 12 | 19,546 | 16,126,630 | 14,845,608 | 581,692 |
| **All** | **27,527** | **18,830,097** | **17,226,088** | **680,639** |

Of the **1,604,009** gcds saved, 1,255,102 came from the initial interval and 348,907 from later gaps. Later gaps helped on 24,494 products. The band search performed 147,129 integer square roots to locate endpoints, and target selection took 71,966 Jacobi tests. No factor appeared during target selection. These are operation counts. The census did not measure elapsed time, and a gcd and a Fermat midpoint test have different costs. [Per-width accounting](../benchmarks/circle-mark-prefix-skip.json)

For example, on $16{,}695{,}347=4{,}079\cdot4{,}093$ with target 2, the first mark was $x=1{,}955$. The band search saved 63 initial and 584 later gcds. It still used 1,308 gcds and 453 integer square roots. Fermat found the factors at its first midpoint, 4,086, where $4{,}086^2-N=49$. [Recorded example](../benchmarks/circle-mark-prefix-skip.json)

## What survives at 2,048 bits?

Take all products of two distinct 1,024-bit primes whose product has 2,048 bits. For **every** such product and **every** Jacobi-negative target $1\le a\le2{,}015{,}165$, all coordinates from zero through $2^{511}$ miss. A related test looks for a coordinate marked at $a$ and, after a shift $h$, marked at $a(2L)^2$. Every shift $1\le h\le L\le2^{500}$ misses too. A hit would require one of two integer expressions to share a factor with the product. Both expressions are nonzero and smaller in absolute value than either prime. [Full-size coordinate and shifted-target bounds](../PrimeFactors/CircleMarkSmallTargets.lean) · [Why two integer expressions suffice](../PrimeFactors/CircleMarkResultant.lean)

Even through coordinate $2^{900}$, **fewer than one in $2^{86}$** of these products admits any mark for any allowed target. The target and coordinate may both be chosen after seeing the product. Including the shifted test at the **fixed** scale $L=2^{900}$, with all shifts from 1 through $L$, raises the upper bound to **fewer than one in $2^{85}$**. The count uses a simple size limit. Each nonzero integer tested is below $2^{2046}$ in absolute value, so it can have at most one distinct 1,024-bit prime divisor. [Population and scale quantifiers](../PrimeFactors/CircleMarkSmallTargetPopulation.lean)

How much of the wait for the first mark do the skips remove? Start the baseline at coordinate 1 and count one gcd per coordinate, including the successful one. Using the public $P=\lfloor N/2^{1024}\rfloor+1$ and $H=2^{1024}-1$, Lean proves two bounds for the original remainder. Each holds simultaneously for every allowed target with Jacobi symbol $-1$. [Band savings through a marked coordinate](../PrimeFactors/CircleMarkBandSavings.lean)

| Fraction of all products excepted | Maximum gcds saved on each remaining product | Fraction saved through its first mark |
|---:|---:|---:|
| Less than $2^{-23}$ | $2^{524}-1$ | Less than $2^{-376}$ |
| Less than $2^{-85}$ | $2^{540}-1$ | Less than $2^{-360}$ |

The exceptions allow for an unusually early mark or two primes unusually close to the upper width limit, where the public factor band is narrow. Elsewhere the bands already cover every remainder long before the first mark. These bounds include the initial skips and measure gcd counts only. [Endpoint exceptions, continuous bands and fractional bounds](../PrimeFactors/CircleMarkBandSavings.lean)

The target ceiling comes from a separate question. Under the Generalized Riemann Hypothesis for Dirichlet L-functions, Theorem 1.1(2) of Lamzouri, Li and Soundararajan supplies a prime outside the subgroup of units with Jacobi symbol $+1$ up to $(\log N)^2$ for products this size. The project's Lean interface converts that real bound into the integer ceiling 2,015,165. Every exclusion above holds unconditionally for targets in the stated range. [Theorem 1.1(2), page 2](https://arxiv.org/pdf/1309.3595#page=2) · [Local integer-bound proof](../PrimeFactors/LeastPrimeBoundInterface.lean) · [Research assumptions and external formalization](../docs/research.md)
