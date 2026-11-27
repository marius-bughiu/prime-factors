# Reading a factor sum from equally spaced samples

For $77=7\cdot11$, the sum of the divisors is $1+7+11+77=96$. Remove $1$ and $77$ and the answer is $18$. Knowing that sum recovers the primes because their difference is $\sqrt{18^2-4\cdot77}=4$. A classical power series puts the divisor sum at position $77$. Can we read that one position cheaply by evaluating the series at a few points? In the four-sample calculation below, the contribution from position $65$ alone is $4{,}096$ times the desired answer. [Earlier theta-series calculation](theta-residues.md) · [Jacobi’s four-square identity](https://dlmf.nist.gov/27.13.iv)

## What four samples read

Write $a_B(n)$ for the sum of divisors $d$ of $n$ such that both $d$ and $n/d$ exceed a chosen cutoff $B$. At a product of two distinct primes above $B\ge1$, this leaves their sum. Form the series $F(z)=\sum_{n\ge1}a_B(n)z^n$. To read position $N$, evaluate $F$ at $M$ equally spaced points on a circle of radius $0<r<1$, starting at $r$. If $\zeta$ is a primitive $M$th root of unity, the weighted average is

$$
\frac{1}{M r^N}\sum_{j=0}^{M-1}\zeta^{-jN}F(r\zeta^j)
=\sum_{\substack{n\ge1\\ n\equiv N\pmod M}} a_B(n)r^{n-N}.
$$

The weights cancel every position except those with the same remainder as $N$ upon division by $M$. Lean checks the identity for finite polynomials. It passes to the series by absolute convergence since $a_B(n)\le n^2$. For $B=2$, $M=4$ and $r=1/2$, both $65$ and $77$ have remainder one. The coefficient at $65=5\cdot13$ contributes $(5+13)2^{77-65}=73{,}728$. Every other term on the right is nonnegative. The bounded checker evaluates the degree-140 polynomial at all four points with exact fractions and independently sums the surviving positions. [Lean proof](../PrimeFactors/CircularCoefficientFilter.lean) · [Exact checker](../experiments/circular_coefficient_filter.py)

## What changes at 2,048 bits

Suppose $N$ is the product of two distinct 1,024-bit primes and has 2,048 bits. Allow both the cutoff and the number of samples to reach $2^{40}$. **For every such input, an earlier position adds more than $2^{2005}$ to the estimate at every radius.** The prime sum itself is below $2^{1025}$. To see where that earlier coefficient comes from, take $d=1+M\lceil B/M\rceil$. It exceeds the cutoff and is coprime to the step $M$. Within $d$ steps on either side of $N$, the arithmetic progression reaches a multiple of $d$. Its cofactor is large enough to survive the cutoff. The checker also verifies the construction on all 24,920 eligible choices drawn from pairs of distinct odd primes below 128 and $1\le B,M\le8$. [Uniform bounds and hypotheses](../PrimeFactors/CircularCoefficientFilter.lean)

Even if someone supplies and subtracts **every earlier contribution exactly**, a later coefficient of at least $2^{2006}$ lies within $2^{81}$ positions. Damping that term below $1/2$ requires a smaller radius. Dividing by $r^N$ then amplifies any errors in the individual evaluations. If each evaluation is guaranteed only within absolute error $2^{-b}$, those errors can align, giving a total error of $2^{-b}r^{-N}$. Lean shows that keeping this below one while damping the later term requires $b>2007\cdot2^{1966}$. This is a worst-case precision requirement for the stated sampling rule. Methods that prove cancellation among evaluation errors would need a different analysis. [Precision theorem](../PrimeFactors/CircularCoefficientFilter.lean) · [Bornemann on circular quadrature and accuracy](https://doi.org/10.1007/s10208-010-9075-z)

For a comparison with guaranteed rounding, take $M=N$ samples and $r^N=1/(64N^2)$. The constant term is zero, so every extra term comes from a later positive multiple of $N$. Their sum is at most $1/15$, using $a_B((j+1)N)\le4^jN^2$ for $j\ge1$. An absolute error of $r^N/4$ per sample now suffices for exact rounding. The precision grows with the bit length of $N$, but the sample count grows with the integer $N$ itself. Modular transformations can accelerate individual theta evaluations. The cost here comes from isolating a single coefficient. [Theta transformations](https://dlmf.nist.gov/20.7.viii)

Reproduce the finite checks with `python3 experiments/circular_coefficient_filter.py` and the formal results with `lake build PrimeFactors.CircularCoefficientFilter`.
