# Computing a Salié sample with a short count

Given only $N=pq$ for distinct odd primes and a frequency $t$ coprime to $N$, one Boolean tensor contraction approximates the normalized diagonal Salié sum $F(t)$ within any fixed absolute error. The contraction reports a few high bits of an integer. Its input uses $N$ and $t$, and its output suffices to evaluate the sample without first finding either prime or listing the modular square roots. For $n=\lceil\log_2 N\rceil$, the deterministic asymptotic cost is $2^{O(n/\sqrt{\log n})}$ bit operations and polynomial space. This applies an existing counting theorem to the sample and matches the asymptotic upper bound for factoring first. [Normalized Salié sum and its factoring reduction](divisor-samples.md) · [Shunia’s factoring theorem](https://hexagonmath.org/pdf/2610.00711v1)

## What the count returns

Use the least residue $0<t<N$ and compute $c=t^2\bmod N$. The classical Salié evaluation gives $F(t)=\sum_{y^2\equiv c\pmod N}\exp(2\pi i y/N)$, over distinct residues. CRT gives four choices of signs for $y$ relative to $t$ at $p$ and $q$. Two residues are $t$ and $N-t$. The other two add up to $N$. Define a public predicate on integers by

$$
 0<2y<N,\qquad y\ne\min(t,N-t),\qquad y^2\equiv c\pmod N.
$$

Exactly one integer $y_*$ passes. Indeed, the unit $t$ and its negative differ in both odd prime fields. The two mixed sign choices therefore form one distinct pair, and exactly one lies below $N/2$. Consequently

$$
 F(t)=2\cos(2\pi t/N)+2\cos(2\pi y_*/N).
$$

The primes establish uniqueness in the proof. The predicate itself requires only arithmetic on its public inputs. The modular equation can be implemented as $y^2=kN+c$ with $0\le k<N$. Euclidean division gives precisely one such $k$ for each valid $y$. [Classical Salié evaluation, Lemma 4.14](https://link.springer.com/article/10.1007/s40687-025-00544-4) · [Lean proofs of uniqueness, orientation and quotient bounds](../PrimeFactors/SalieCounts.lean)

For any $1\le d\le n$, put $W=2^{n-d}$. Add an unsigned $d$-bit integer $z$ and the test $z<\lfloor y/W\rfloor$. The number of satisfying assignments is exactly $j=\lfloor y_*/W\rfloor$, including when $j=0$. Since $j<2^d$, a single count modulo $2^d$ returns it exactly. This gives the interval $jW\le y_*<(j+1)W$. Approximating $y_*$ by its midpoint $m=(j+1/2)W$ changes $F(t)$ by at most $2\pi W/N<4\pi\,2^{-d}$ by the Lipschitz bound for cosine. At $d=n$, $j=y_*$ and we use $j$ itself. To achieve error $0<\delta\le1$, take $d=\min(n,\lceil\log_2(8\pi/\delta)\rceil)$ and compute the two cosines and their scaled sum to total numerical error at most $\delta/2$. Argument reduction and a Taylor expansion on a bounded interval take polynomial time in $n+\log(1/\delta)$. For the fixed precision in the factor-recovery reduction, $d=\min(n,14)$ already bounds the phase contribution to the error in $F(t)$ by $0.000767$, before numerical rounding. [Checked prefix count and midpoint error](../PrimeFactors/SalieCounts.lean) · [Accuracy needed by the decoder](divisor-samples.md#recovering-the-integer-with-bounded-errors)

An exact sign query costs only a parity count. For the selected $0<y_*<N/2$, the hidden cosine is negative exactly when $4y_*>N$. Add this comparison to the predicate and count modulo two. The same construction computes any specified bit of $y_*$ by pinning the bit to one. Thus $d$ nonadaptive parity counts are an alternative interface for the same prefix. At dyadic frequencies the exact cosine signs give adjacent binary-digit comparisons, even when the sample is very close to the public threshold. [Lean sign and parity lemmas](../PrimeFactors/SalieCounts.lean) · [Sign decoding](divisor-samples.md#exact-signs-determine-adjacent-binary-digits)

## Work charged to one sample

Use two copies of the parsimonious multiplication network of Akshima et al., Theorem 3, for $n$-bit inputs and the full $2n$-bit products. Bind both inputs of the first copy to $y$, and fix one input of the second to $N$, giving $y^2$ and $kN$. A ripple adder adds the public $c$ and equality tests its result against $y^2$. Pin the terminal carry to zero. Fix leading zeros throughout. Ripple comparisons implement the half-interval, the excluded public root and the slack bound. The prefix is already present on the top $d$ input wires. Copies and pins on interface edges use bounded-degree equality vertices. Every auxiliary bit used by an adder, comparator or wire copy is determined by its inputs, so the unique witness property survives composition. [Original multiplication theorem](https://github.com/bochum-crypto/subexponential-ecdl/blob/main/subexponential-ecdl.pdf) · [Interface bounds and their use in counting, Theorem 3](https://hexagonmath.org/pdf/2610.00711v1)

Each multiplier has fewer than $1100(n+1)$ edges and degree less than $136(n+1)^{3/4}$. The auxiliary logic adds $O(n)$ edges and bounded degree. Subdivide all edges with equality to form a bipartite network. Its description has polynomial length and each local entry is uniformly polynomial-time computable. In Theorem D.1 take $s=\Theta(n)$ large enough for the degree bound $\lceil s^{9/10}\rceil$, the ordinary ring with $P_0=d$ and $\ell=1$, or $P_0=1$ for parity. This yields the stated deterministic time and space for the count, including setup. The small-width example below uses enumeration to check the meaning of the count. An implementation of the asymptotically faster contraction and its cost at 2,048 bits remain open here. [OpenAI, quantitative tensor contraction, Theorem D.1](https://raw.githubusercontent.com/openai/math/main/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/quantitative-reduction.tex)

For $N=667$, $t=8$ and $d=5$, Lean enumerates the public predicate and returns the prefix $4$. Here $W=32$, so $128\le y_*<160$. The midpoint $144$ gives $F(8)\approx2.41966$ compared with the full sum’s $2.25265$. Their difference is below $2\pi\cdot32/667\approx0.30144$. The interval also decides the exact sign since $4\cdot160<667$. [Checked enumeration](../PrimeFactors/SalieCounts.lean) · [Direct sum on the same input](divisor-samples.md#bounded-calculation)
