# Narrowing the search for two unknown primes

We recovered **678,730,100,668,523 × 931,320,152,449,657** from their 99-bit product in 7.59 seconds on an arm64 Mac. The search received the product alone. Lean checked both primes and their product separately. On a fresh 89-bit input, our previous grouped factor search took 14.18 seconds and this search took 1.34 seconds. On the 2,048-bit control a capped run exhausted its 96 blocks with the entire product unresolved. [Checked examples](https://marius-bughiu.github.io/prime-factors/#weighted-stride-99) · [Fixtures and budgets](../benchmarks/weighted-stride.json)

The input promise is that the product is made from two distinct primes with the larger at most twice the smaller. The idea is to multiply each unknown prime by a small weight. With the right weights the two scaled primes almost coincide, so their sum has very few possible values. We can compute the ranges of those sums using the product alone. We can also skip most of the integers within each range. Harvey showed how to check many such sums together by comparing powers. Our changes specify tighter ranges and put every surviving progression into a shared table. [Harvey, Algorithms 4.1–4.2 and Lemma 2.4](https://arxiv.org/abs/2010.05450) · [Earlier bounds and local power matches](searching-the-balanced-interval.md#collisions-visible-at-one-unknown-prime)

## Which sums could be right?

Write the input as $N=pq$ with $p\le q\le 2p$. Choose any positive denominator cutoff $K$. Sort the reduced fractions in $[1,2]$ whose denominators are at most $K$. Consecutive fractions $a/b<c/d$ satisfy $bc-ad=1$ and $b+d>K$. One such pair brackets $q/p$. For the proof, start with $1/1,2/1$, insert $(a+c)/(b+d)$ whenever its denominator is at most $K$, and keep the bracket containing the ratio. Each insertion increases the sum of the retained denominators. A fraction strictly between determinant-one endpoints has denominator at least $b+d$, which also shows why the terminal bracket appears in the sorted list. [Lean subdivision and coverage](../PrimeFactors/FareyWindow.lean)

In that bracket put $x=bq-ap$, $y=cp-dq$, and $h=b+d$. The determinant gives $dx+by=p$. If $x\le y$, then $hx\le p$, and
$$bN=ap^2+px\ \ge\ h(ha+1)x^2.$$
Since $(ap+bq)^2=4abN+x^2$, the true sum for the lower slope is between
$$\left\lceil\sqrt{4abN}\right\rceil\quad\text{and}\quad
\left\lfloor\sqrt{4abN+\left\lfloor bN/[h(ha+1)]\right\rfloor}\right\rfloor.$$
If $y\le x$, apply the upper slope instead. Now $hy\le p$ and $dN=cp^2-py\ge h(hc-1)y^2$. The difference factors as $(p-hy)(c(p+hy)-y)\ge0$. This gives the analogous upper endpoint with $dN/[h(hc-1)]$. The implementation takes the larger of the two upper endpoints at an interior slope, and uses its one neighbor at an endpoint. Bounds with upper endpoint below lower endpoint cost no search. The unrounded bounds meet with equality at the mediant. [Endpoint proofs and complete-cover theorem](../PrimeFactors/FareyWindow.lean) · [Integer implementation](../experiments/weighted_windows.py)

To find a neighbor of $a/b$, take the largest denominator $d\le K$ for which $ad\equiv1\pmod b$ on the left or $ad\equiv-1\pmod b$ on the right. Its numerator is $(ad-1)/b$ or $(ad+1)/b$, respectively. A single modular inverse gives both denominators. For $b=1$, the eligible neighbor has denominator $K$. [Executable checks against sorted rational fractions](../tests/test_weighted_windows.py)

## How many values can one remainder remove?

Test factors 2 and 3 directly. For the remaining inputs $p^2\equiv1\pmod{24}$. Set $C=a+bN$ and $s=\gcd(24,2C)$. Then
$$ap+bq\equiv Cp\equiv C\pmod s.$$
The first congruence uses $p^2\equiv1$. The second uses that $p-1$ is even and $s$ divides $2C$. For example, when $s=24$, at most one out of every 24 consecutive sums needs a label. [Lean congruence](../PrimeFactors/WeightedStride.lean)

This particular rule has a sharp limit. Take coprime weights, a positive modulus $m$ coprime to $N$, and allow the unknown factor to occupy **any unit class** $r\bmod m$. The weighted sum in that model is $ar+bN/r$. Lean proves it is constant over all those classes **if and only if** $m$ divides $s$. Testing $r=-1$ forces $m\mid 2C$. Projecting onto its odd part and testing $r=2$ shows the odd part divides 3. Projection onto modulus 16 and testing $r=3$ rules out a factor of 16 in $m$. Multiple surviving residues or independent information about the factor can give other filters. [Complete classification](../PrimeFactors/ConstantWeightedResidue.lean)

## Testing all surviving progressions together

Let $\beta$ be a unit. The true weighted exponent $t=ap+bq$ satisfies $\beta^t=\beta^C\pmod p$ by Fermat's little theorem. Divide each surviving progression into blocks of $m$ labels. For a block starting at $u$ a true label $t=u+si$, $0\le i<m$, therefore gives
$$(\beta^{24})^i = (\beta^{C}/\beta^u)^{24/s}\pmod p.$$
All slopes now use the same $m$ starting powers. The right-hand residues are computed modulo the public product. Equality at just one prime suffices. Multiplying the corresponding linear factors into a polynomial and evaluating it at the starting powers batches the tests. One convolution does the geometric evaluation using $ij=\binom{i+j}{2}-\binom i2-\binom j2$. [Lean power identity](../PrimeFactors/WeightedStride.lean) · [Search and evaluation](../experiments/weighted_stride_search.py)

Before discarding any full-modulus equality, the program checks the gcd of $N$ with the product of $(\beta^{24})^j-1$ for $1\le j<m$. A gcd of one certifies the starting powers are distinct at **each** prime. A proper gcd already factors $N$. A gcd of $N$ is refined one term at a time. If a base still has short order, the bounded run reports that outcome. For a full equality the unique index is checked for membership in the block, and its candidate sum is tested for an exact square discriminant and a proper factor. The remaining unequal residues go through the polynomial. A final gcd of $N$ is likewise refined. Thus a full schedule with a certified base finds a factor under the stated input promise. A bounded run can end early with a factor or exhaust its budget. [Implementation and regression tests](../tests/test_weighted_stride_search.py)

Small prime bases that repeat too soon can be combined. On 32,817,151, the individual bases 2 and 3 both failed the order test. Their combination 486 produced the factors 4,051 and 8,101. A bound from the Dirichlet result guarantees enough bases on the target input family. [Proof, example and assumptions](combining-weighted-bases.md)

## Measurements

All timings below are discovery only. The first three rows are three-run medians on the same arm64 Mac and the same inputs. The middle column of timings uses the same narrowed windows with stride one, isolating the effect of the common residue rule. The 99-bit run was a separate single measurement. The comparison is with this repository's previous full balanced-interval implementation. [Raw timing samples and counts](../research/weighted-stride-comparison.json) · [Comparison runner](../experiments/weighted_stride_comparison.py)

| Input | Previous grouped factor interval | Narrow windows, stride one | Narrow windows, compressed | Starting powers | Compressed blocks |
|---|---:|---:|---:|---:|---:|
| 63 bits | 0.119 s | 0.051 s | 0.022 s | 1,406 | 1,299 |
| 79 bits | 2.316 s | 0.722 s | 0.312 s | 13,924 | 12,439 |
| 89 bits, first draw | 14.175 s | 3.099 s | 1.338 s | 53,130 | 47,323 |
| 99 bits, first draw | — | — | 7.591 s | 228,006 | 201,804 |

A second 89-bit draw reached a full-modulus equality and split in 0.220 seconds. For all four sizes the parameter rule used only $z=\lfloor N^{1/10}\rfloor$, choosing $K=\lfloor(z+1)/2\rfloor$, $m=\max(1,\lfloor z^2/4\rfloor)$, and base 2. The 99-bit search covered 37,911,763,615 candidate sums. It found one factor with its first polynomial batch gcd. On the 2,048-bit capped control we used $K=32$, $m=64$ and 96 blocks, covering only 6,144 sums in the first slope. [Full work counters and expected results](../benchmarks/weighted-stride.json)

The 89-bit sampler draws its two 45-bit primes independently by SHAKE256 and exact trial division. For the separate 99-bit run, concatenate ASCII `farey-window-blind-50-v1`, one zero byte, the ASCII side `p` or `q`, and an eight-byte big-endian counter starting at zero. Take seven SHAKE256 output bytes as a big-endian integer modulo $2^{50}$, set bits 49 and 0, and retain the first prime on each side. There was no search-outcome or spacing criterion. The benchmark discovery function receives only $N$ and its public settings. Expected factors are used to check the output, and every complete benchmark has a replayable Lean certificate. [Benchmark runner](../scripts/benchmark.py)

## What still stands in the way at 2,048 bits?

For any positive choices of the two table-size parameters, the full mediant-based schedule above requires **more than $2^{404}$ records** on every 2,048-bit product. The count includes one setup per primitive slope, the starting powers and the blocks. Early discoveries remain possible. This lower bound applies to the specific full schedule, and motivates asking which intervals we can omit altogether. [Finite work bound and Lean proof](farey-work.md)

Moving the boundaries and omitting some fractions reduced the number of blocks by about a quarter on two 89-bit products. It sped up one search and slowed down the other. A separate finite argument bounds how often the original windows can succeed through an accidental match when the prime pair and base are sampled at random. [Allocated windows, certificates and timings](farey-allocation.md) · [Chance of an early coincidence, with sampling assumptions](farey-wraps.md)
