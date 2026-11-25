# How many products can a fixed list of guesses reach?

The sum of the two primes is enough to find both. We found a rule that computes a candidate sum from the product and an integer guess. On a 24-bit example the rule found the factors even though the guess was wrong. Allowing such lucky hits matters when measuring the method. Even with **$2^{40}$ guesses, more than a trillion**, the fraction of target products on which the sum can occur among the divisors tested is **less than $2^{-532}$**. The list must be fixed independently of the input, and every guess must have magnitude below $2^{1024}$. A way to choose a useful guess from the digits of the product would change the question. [Counting proof](../PrimeFactors/InverseGapPopulation.lean) · [The positive examples](sums-dividing-the-neighbor.md)

## The wrong guess that worked

For $N=pq$ with distinct primes, let $u$ be the inverse of $p$ modulo $q$ between 1 and $q-1$, and let $v$ be the inverse of $q$ modulo $p$ between 1 and $p-1$. For the signed difference $e=u-v$, the unknown sum $S=p+q$ divides the public integer

$$Z_e=(N+1)^2+Ne^2.$$

For $e=0$ the sum already divides $N+1$. One cheap proposal is to extract all powers of primes through a fixed cutoff from the appropriate public integer and test their product as $S$. An exact square test on $S^2-4N$, followed by multiplication, verifies a success. The population bound even allows testing *every* divisor of $Z_e$ for free. Factoring $Z_e$ or obtaining its divisors cheaply in general remains open. [Divisibility identities](../PrimeFactors/ReciprocalInverseSums.lean) · [Public candidate calculation](../experiments/neighbor_smooth_sum.py)

Take $N=10{,}740{,}343$. With $e=8$ we get $Z_8=115{,}355{,}676{,}620{,}288$. Extracting its prime powers through 13 gives $6{,}656$. Then $6{,}656^2-4N=1{,}158^2$, which yields **$2{,}749\times3{,}907$**. The two inverse residues are 388 and 2,476. Their signed difference is **$-2{,}088$**. Guesses 0, 2, 4 and 6 missed with the same cutoff. The calculation for 8 required 16 remainder checks and one square test. Using the same cutoff and guess on both 2,048-bit controls gave proposed sums 64 and 4. Both lie below the smallest possible sum. [Checked arithmetic](../PrimeFactors/InverseGapPopulation.lean) · [Benchmark inputs and results](../benchmarks/neighbor-smooth-sum.json)

This illustrative success was selected by enumerating primes $1000\le p<8000$, primes $5p/4\le q<2p$ below 16,000 with the same bit length, and retaining full double-width products with $S\nmid N+1$. We tested the even guesses 2 through 8 and prime cutoffs from 3 through 31. The recorded search then received only the product, the cutoff and the guess. The population estimate below uses all eligible prime pairs at the target size. [Replayed search and missed guesses](../tests/test_neighbor_smooth_sum.py)

## Counting true guesses and accidental hits

Choose an unordered pair of distinct 1,024-bit primes uniformly, conditional on their product having 2,048 bits. Write the smaller prime first. For any fixed nonempty list of $T\le 2^{40}$ guesses with $|e|<2^{1024}$, the two bounds are

| Success counted | Fraction of target products | At $T=2^{40}$ |
| --- | --- | --- |
| The true signed difference is on the list | less than $T2^{-768}$ | less than $2^{-728}$ |
| The sum divides at least one $Z_e$, even by coincidence | less than $T2^{-572}$ | less than $2^{-532}$ |

Fix the smaller prime $p$ and a guess $e$. If it is the true difference, the identity $pu+qv=N+1$ gives

$$p^2+ep-1=(p-v)(p+q).$$

Each divisor of the left side gives at most one partner $q$ by subtracting $p$. For *any* successful guess, reduce $Z_e$ modulo $S=p+q$. Substituting $N\equiv-p^2\pmod S$ shows that $S$ must divide

$$(p^2+ep-1)(p^2-ep-1).$$

Neither factor vanishes, since both equal $-1$ modulo $p$. Their absolute values are below $2^{2049}$ and the absolute product is below $2^{4098}$. Lean proves both injections into divisor lists and the size bounds. This is a way to count partners in a proof. Computing these row integers uses $p$, so the search itself uses $Z_e$. [Finite counting proof](../PrimeFactors/InverseGapPopulation.lean)

To bound the length of each list, let $\tau(n)$ count the positive divisors. For every $n>0$, Lean proves

$$\tau(n)^{336}\le2^{14882}n^{32}.$$

On a prime power the quantity to bound is $(a+1)^{336}/r^{32a}$. For $r\ge1449$ it is at most one. At the 229 smaller primes, a finite certificate rounds each necessary correction up to a power of two. The ratio decreases for all $a\ge15$, so only the first 16 exponents can maximize it. Multiplying the prime-power inequalities gives the displayed bound. Integer comparisons then give $\tau(n)\le 11\cdot2^{236}$ at the first size and $\tau(n)\le3\cdot2^{433}$ at the second. [Kernel-checked divisor bound](../PrimeFactors/UniformDivisorCount.lean)

For the denominator, set $X=2^{1023}$ and $U=X/\log X$. The published Rosser–Schoenfeld estimates give fewer than $1.511U$ choices of first prime and more than $(0.22U)^2/2$ eligible unordered prime pairs. The latter counts just the pairs with both primes at least $\sqrt2 X$. Since $\log X<710$, the ratio of possible first primes to eligible pairs is below $44331/X$. Multiplying by the row bounds and the number of guesses gives the table. The analytic prime-count estimates enter the Lean population theorems as an explicit numerical hypothesis. The remaining finite bounds and comparisons are kernel-checked. [Derivation of the population constants](stride-budget.md#an-explicit-bound-at-exactly-2048-bits) · [Rosser and Schoenfeld, Corollary 1](https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf#page=6)

## What if we choose the guess after seeing the product?

For the implemented rule with a prime cutoff through 31, the proposed sum has no prime factor greater than 31, however the guess was chosen. Even allowing all such sums at once covers **less than one in $2^{947}$** of the eligible products. This restriction persists when the guess and the cutoff both depend on every digit of the input. A search that also uses large prime divisors of $Z_e$ has a different set of possible sums.

To count the sums, remove all factors of two. Each odd integer below $2^{1024}$ with prime factors through 31 gives exactly one even sum in $[2^{1024},2^{1025})$ by multiplying by the appropriate power of two. Conversely, every possible sum has such an odd part. For the ten odd primes $r$ through 31 set $w_r=\lfloor256\log_2 r\rfloor$, computed exactly as the binary length of $r^{256}$ minus one. Count exponent tuples with $\sum a_r w_r < 256\cdot1024$. The smaller costs make this an upper bound. Using $w_r+1$ gives a lower bound. For each prime in turn the integer recurrence adds the count at cost $j-w_r$ to the count at $j$ in ascending order. This counts each exponent tuple once.

The resulting interval is **1,656,965,853,583,758,893 to 1,676,749,662,954,303,816** possible sums. For each first prime a sum specifies at most one partner. Multiplying the upper endpoint by the first-prime to eligible-pair ratio, $44331/2^{1023}$, gives the stated fraction. These two endpoints and the final integer comparison have a reproducible exact-integer implementation. [Integer recurrence](../experiments/smooth_factor_sums.py) · [Checks against exhaustive small intervals](../tests/test_neighbor_smooth_sum.py)

An independent Lean proof counts at most 1,995,556,406,373,313,773 candidate sums by enclosing their exponent vectors in a simplex. This gives a kernel-checked fraction below $2^{-946}$ under the same prime-count hypothesis. For sums allowed to have large prime divisors, even the product-dependent choice $e=aN+b$ has a separate population bound when its coefficients are small. [Lean smooth-sum count](../PrimeFactors/SmallPrimeSumCoverage.lean) · [Affine guesses](affine-guesses-from-the-product.md) · [Complete search for sums supported on just 2 and 3](recovering-a-smooth-prime-sum.md)
