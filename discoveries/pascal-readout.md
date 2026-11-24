# One entry of Pascal’s triangle gives a factor

Suppose the only input is an odd integer $N=pq$, where $p<q$ are primes. Take the largest odd integer $k\le\lfloor\sqrt N\rfloor$. If $q<4p$, the following formula returns the larger prime exactly:

$$q=1+\left(\binom{N-1}{k}\bmod N\right).$$

This applies to every pair of distinct 1024-bit primes. For example, $N=143$ gives $k=11$. The remainder of $\binom{142}{11}$ upon division by 143 is 12, giving $q=13$ and then $p=11$. The difficulty is computing the remainder at a large index. Even for a 31-bit input the exact coefficient in the example below occupied 761,262 bits. [Lean proof](../PrimeFactors/PascalReadout.lean) · [Bounded evaluator](../experiments/pascal_readout.py)

There is also one **fixed index per bit width**. If both primes have $b$ bits, put $K=2^b-1$. Then

$$p+q=1+\left(\binom{N-1}{K}\bmod N\right).$$

Given this sum $S$, the two factors are $(S\pm\sqrt{S^2-4N})/2$. The equal-width promise lets us infer $b=\lceil\operatorname{bitlength}(N)/2\rceil$. Both identities are elementary consequences of Lucas’s theorem and Pascal’s recurrence. Lean verifies them without an analytic hypothesis. [Mathlib’s Lucas theorem](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Choose/Lucas.html) · [Granville on binomial congruences](https://www.cecm.sfu.ca/organics/papers/granville/paper/binomial/html/node2.html)

A follow-up shows that 511 binary digits of one scaled fraction give enough low bits of a 1024-bit prime to recover it. The same coefficient can have all its raw low bits equal to zero. Computing the scaled fraction cheaply is the open step. [Precision, decoding, and the zero-residue control](pascal-projections.md)

## Why two entries carry the information

For $0<j<2p$, the coefficient $\binom Nj$ modulo $N$ is $q$ at $j=p$, is $p$ at $j=q$ if that position lies in range, and is zero everywhere else. Modulo $p$, Lucas’s theorem reads the low digit of $N$ as zero. A positive index below $2p$ must therefore equal $p$ to contribute, and that index gives $q\bmod p$. Working modulo $q$ and combining the residues gives the result. Equivalently, through degree $2p-1$, the only possible nonconstant terms of $(1+X)^N\bmod N$ are $qX^p$ and $pX^q$.

Pascal’s recurrence gives $\sum_{j=0}^k(-1)^j\binom Nj=(-1)^k\binom{N-1}k$. For an odd $k<2p$, the remainder $C_k=\binom{N-1}k\bmod N$ therefore has three possible values:

| Index | Canonical remainder $C_k$ |
| --- | ---: |
| $k<p$ | $N-1$ |
| $p\le k<q$ | $q-1$ |
| $q\le k<2p$ | $p+q-1$ |

Here “canonical” means between zero and $N-1$. The square-root cutoff lies in the middle range when $q<4p$ because $p\le\sqrt N<q$ and $\sqrt N<2p$. Rounding down to an odd number keeps $k\ge p$. The fixed-width cutoff is in the last range because $q<2^b\le2p$. For a perfect square or a product with more prime factors these hypotheses change. The example driver checks every proposed split.

## One coarse observation can decide a factor interval

For any odd $k\le\lfloor\sqrt N\rfloor$ in the same input class, comparing $C_k$ with $N/2$ tells whether $p\le k$. Binary search on the ordered odd candidates then locates $p$ in at most $b$ comparisons for $b$-bit factors. All computations of the observation itself have to be counted.

A public scaling even makes **constant precision on the circle** sufficient. For any integer $0<a<p$, the fractional part of $a(\binom{N-1}k+1)/N$ is zero before the threshold and $a/p$ after it. The lemma `pascal_scaled_phase` proves the integer residue giving these two possibilities. For $b$-bit factors with $b\ge2$, choose $a=2^{b-2}$. Since $2a\le p<4a$, a hit has phase in $(1/4,1/2]$. Measuring the phase with circular error strictly below $1/8$ distinguishes a hit from zero. In contrast the unscaled circular separation is only $1/p$. An evaluator achieving this accuracy directly from $N,k,a$ in polynomial time would give a polynomial-time classical factoring algorithm for every such input.

More precisely, suppose only $L\le p\le U$ is used to select the scale. For a real multiplier the best uniform distance of $a/x$ from the nearest integer, over *all real* $x\in[L,U]$, is $L/(L+U)$. Take $a=LU/(L+U)$, making the two endpoints equally distant from an integer. To prove optimality for $a\ge0$, any positive uniform distance $d$ puts the connected interval $[a/U,a/L]$ between $j+d$ and $j+1-d$ for some integer $j\ge0$. Consequently $d(L+U)\le L-j(U-L)\le L$. Negating $a$ gives the same distances. Rounding the optimum to an integer loses at most $1/(2L)$ by the triangle inequality. For $L=\lceil\sqrt{N/2}\rceil$ and $U=\lfloor\sqrt N\rfloor$ this gives a separation approaching at least $1/(1+\sqrt2)$. This optimum is for a continuous interval; additional information about the actual prime could change it. [Lean endpoint equalities and bound](../PrimeFactors/PascalReadout.lean)

## The cost of evaluation

For a 2048-bit product and $K=2^{1024}-1$, directly constructing $\binom{N-1}K$ requires **more than $2^{1033}$ bits**. Indeed each factor in $\binom{n}K=\prod_{i=0}^{K-1}(n-i)/(K-i)$ is at least $n/K$, and $(N-1)/K\ge2^{1023}$. This is an output-size bound on the exact integer. A modular algorithm could avoid constructing it. Using Lucas at the two unknown prime moduli would already require their values.

For $q\le2p$, take the public lower bound $L=\lceil\sqrt{N/2}\rceil$. Over $L\le k\le\lfloor\sqrt N\rfloor$, the product $\prod_{i=L}^k i$ has gcd with $N$ equal to one when $k<p$ and to $p$ when $k\ge p$. Neither $q$ nor $2p$ lies in this interval. Thus the threshold can already be evaluated through a batched interval gcd, after which the two canonical binomial residues follow immediately. The polynomial-tree bound is $\widetilde O(1+\sqrt{k-L+1})$ ring operations for a single interval. A faster evaluation of the coarse binomial phase would need to improve on the cost of locating that first nonunit. [Interval batch and time bounds](batch-intervals.md)

Two ways of exploiting the sparseness have precise limitations:

* **Truncated polynomial powering.** In any ordinary addition chain computing $(1+X)^N$ from $1+X$ by multiplication, consider the first exponent reaching $p$. One of its parents has exponent $e$ between $\lceil p/2\rceil$ and $p-1$. Every one of the $e+1$ coefficients of $(1+X)^e$ is nonzero modulo $p$, since no factorial up to $e$ contains $p$. Thus a method explicitly listing the nonzero coefficients of each intermediate truncated at degree at least $p$ must store at least $\lceil p/2\rceil+1$ at that step, even though the final prefix is sparse.
* **Fixed linear row updates.** With $K$ fixed, the sequence $f(n)=\binom nK$ over $\mathbb Z/N\mathbb Z$ has minimum monic constant-coefficient recurrence order $K+1$, even if an order-$r$ recurrence need hold only at $K+1$ consecutive starting indices. Write $E$ for forward shift and $\Delta=E-1$. Pascal gives $\Delta^t f(n)=\binom n{K-t}$ for $0\le t\le K$ and $\Delta^{K+1}f=0$. A monic recurrence polynomial of degree $r\le K$ in $E$ is also monic of degree $r$ in $\Delta$. Its vanishing yields a linear combination of the binomial basis functions of degrees $0$ through $K$ whose coefficient at $K-r$ is one. Lean proves that any such combination vanishing on $K+1$ consecutive rows has all coefficients zero, over every commutative ring. This excludes fixed linear updates promising correctness across rows. The single product-specific evaluation, compressed nonlinear representations, and variable-coefficient algorithms remain open approaches.

## A product chosen before evaluation

Using CPython’s `Random(20261124)`, take successive uniform odd integers from `range(32769,65536,2)` until two primes occur. Their product is $2028838549$. The search receives just this product, the cutoff rule and the index budget. The square-root rule uses index 45,041 and returns residue 61,492. The fixed-width rule uses index 65,535 and returns residue 94,485 from a 1,072,190-bit coefficient. Both yield $32993\cdot61493$. One local run spent about 3.2 and 6.3 seconds on the coefficients respectively. A simple trial search starting from the first odd candidate in the balanced interval, 31,851, finds the smaller prime in 572 divisions. The 2048-bit budget-control fixture stops before constructing a coefficient, retaining the entire product as unresolved. [Decimal inputs and expected results](../benchmarks/pascal.json)

```sh
python3 experiments/pascal_readout.py 2028838549 --cutoff sqrt
python3 experiments/pascal_readout.py 2028838549 --cutoff dyadic
```
