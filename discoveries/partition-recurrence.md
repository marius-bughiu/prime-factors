# Computing a factor coefficient with a sparse theta series

For $667=23\cdot29$, the selected factor is $29$. Both partition calculations recover it from the product alone. At six-bit precision the original calculation uses 222,111 convolution terms, each with a coefficient multiplication. The new calculation uses 13,386 signed additions and a final divisibility check. It also has lower asymptotic cost than the original series decoder. Ordinary divisor search still has a better asymptotic bound, and the new decoder still requires storage proportional to the numerical value of the product. [Earlier calculation](theta-residues.md) · [Experiments](../experiments/partition_recurrence.py)

## One theta series gives the coefficient

Suppose $N=pq$ for distinct odd primes, and $N\equiv2,3\pmod5$. Exactly one of its factors, $r$, lies in $1,4\pmod5$. Among the divisors in these two classes only $1$ and $r$ occur. Put
$$
U(x)=\prod_{d\ge1,\ d\bmod5\in\{0,1,4\}}(1-x^d)
     =\sum_{j\in\mathbb Z}(-1)^j x^{j(5j-3)/2}.
$$
The second equality is Jacobi's triple product with parameters $q=x^5,z=x$. Write $L=-xU'/U$. At every positive index $i$ its coefficient is the sum of the divisors of $i$ in those three classes. As $5\nmid N$, this gives $L_N=1+r$. Multiples of five must still be included when computing the intermediate coefficients. In the companion series with $z=x^2$, the permitted classes are $0,2,3$. Its coefficient at $N$ is $N$ plus the other prime. [Jacobi's identity](https://dlmf.nist.gov/17.8.E1) · [Lau, Lee and Ono's formalization](https://github.com/AxiomMath/RogersRamanujan)

At another eligible prime $\ell\equiv1\pmod4$ with $(N/\ell)=-1$, the positive character classes form $(\ell-1)/4$ pairs $\{a,-a\}$. Use one triple product with $q=x^\ell,z=x^a$ per pair. Adding their logarithmic derivatives with the same negative sign gives $1+r$ at $N$ because $\ell\nmid N$. The shifts for each pair are $j(\ell j\pm(\ell-2a))/2$ with $j\ge1$, taking $1\le a<\ell/2$. There are $O(1+\sqrt{N/\ell})$ per pair through $N$. This gives $O(\ell N+\sqrt{\ell}N^{3/2})$ signed updates with $O(N)$ coefficient slots by processing the pairs sequentially. The implementation below uses level five. The character-selection bound from Dirichlet GRH applies before this calculation. [Selection of the auxiliary prime](theta-residues.md)

## What the recurrence costs

Let $S$ contain the positive shifts $j(5j\pm3)/2$ for $j\ge1$, and write $u_s=(-1)^j$ there, with $u_i=0$ off the support. Comparing coefficients in $U L=-xU'$ gives
$$
L_0=0,\qquad L_i=-i u_i-\sum_{s\in S,\ s<i}u_s L_{i-s}.
$$
It works modulo any positive integer. Initialize the forcing terms $-i u_i$, then process the slots in increasing order. Reduce each finished coefficient modulo the requested modulus. If it is nonzero, add or subtract it from each later slot at an allowed shift. No division or general coefficient multiplication is required. The shift $1$ occurs, so following every dependency backwards from a single target index visits every earlier positive index. A faster isolated-coefficient method would need to exploit additional structure.

The number of available updates before skipping zeros is exactly $\sum_{s\in S,\ s<N}(N-s)$. There are $2\sqrt{2t/5}+O(1)$ shifts through $t$. Summing over $t<N$ gives $(4/3)\sqrt{2/5}\,N^{3/2}+O(N)$ available updates. The implementation defers modular reduction until a slot is processed. With $k$ output bits each accumulator consequently uses $O(k+\log N)$ bits. The original dense recurrence had $N(N-1)/2$ convolution terms. Both counts exclude initialization.

There is an additional saving at **fixed precision** $2^k$, $k\ge1$. For an intermediate index $i$, let $m$ be its part coprime to $10$. Let $h$ count the primes of odd exponent in $m$. In both $\sigma(m)$ and $\sum_{d\mid m}(d/5)d$, each such prime contributes a geometric sum with an even number of odd terms, so both integers are divisible by $2^h$. Their sum or difference, divided by two, is the divisor sum in one specified character class. For the full $i$, separate the powers of two in every divisor coprime to five. The remaining divisors of $m$ belong to one of those two classes. Divisors divisible by five add $5\sigma(i/5)$ when $5\mid i$, which is also divisible by $2^h$. Thus $h>k$ forces $L_i=0\pmod{2^k}$. The implementation discovers zeros from its computed coefficients.

Every eligible nonzero index has the form $2^e5^f s^2 d$, where $e,f\in\{0,1\}$ and $d$ is squarefree with at most $k$ prime factors. Landau's estimate gives $O_k(N(\log\log N)^{k-1}/\log N)$ such indices through $N$. To see the effect of the squares, sum the estimate for $d$ over $s\le N^{1/4}$ using $\sum_s 1/s^2<\infty$. For larger $s$ the trivial upper bound contributes $O(N^{3/4})$. Each active index can send $O(\sqrt N)$ updates. This proves a fixed-$k$ bound of $O_k(N^{3/2}(\log\log N)^{k-1}/\log N)$ signed updates. For precision growing with the bit length of $N$, the uniform guarantee here is $O(N^{3/2})$. [Wright's proof of Landau's estimate](https://www.cambridge.org/core/journals/proceedings-of-the-edinburgh-mathematical-society/article/simple-proof-of-a-theorem-of-landau/912EC9C6F7F0978E0E40B93FB418934E)

This order of growth is sharp for the stated recurrence at each fixed $k$. Take squarefree $i$ made of exactly $k$ primes all congruent to $13\pmod{20}$. Each prime has negative character modulo five and is $1\bmod4$. Thus $\prod_{p\mid i}(1+p)$ has exactly $k$ factors of two while $\prod_{p\mid i}(1-p)$ has at least $2k$. Half their sum has exactly $k-1$ factors of two, so the recurrence must propagate $L_i$. Meng's asymptotic for distinct prime factors in prescribed classes gives $\gg_k N(\log\log N)^{k-1}/\log N$ such indices in $[N/3,N/2]$ for $k\ge2$. For $k=1$ the prime number theorem in the fixed progression gives the same assertion. Every such index sends $\gg\sqrt N$ updates. Even for growing precision the $k=1$ family alone forces $\gg N^{3/2}/\log N$ updates because an odd coefficient stays nonzero at every higher precision. These lower bounds concern this particular forward recurrence. [Meng's prescribed-factor theorem](https://arxiv.org/abs/1607.01882)

### Full precision forces the full order of growth

At the benchmark's factor-recovery precision, skipping zero coefficients still requires $\Theta(N^{3/2})$ signed updates. More generally this holds whenever $k/(\log\log N)^2\to\infty$ for a modulus $2^k$.

To see why, take any odd $m$ coprime to five. Write $A$ and $B$ for its divisor sums over the two quadratic character classes, so $A+B=\sigma(m)$. The odd divisors of $2m$ are the divisors of $m$. Its even divisors are twice those divisors, and doubling interchanges the two character classes. Thus $L_m=A$ and $L_{2m}=A+2B$. If both coefficients vanish modulo $2^k$, their sum $2\sigma(m)$ vanishes there too. Lean checks the doubling identity and this divisibility implication. [Lean proof](../PrimeFactors/PartitionRecurrence.lean)

For completeness, the mean of $v_2(\sigma(m))$ over the odd positive integers $m\le N$ is $O((\log\log N)^2)$. By multiplicativity it suffices to sum the contributions of odd prime powers. A prime occurring with exponent one contributes at most $v_2(p+1)/p$ to the sum divided by $N$. To bound the total, expand $v_2(p+1)$ as a count of $j\ge1$ with $p\equiv-1\pmod{2^j}$. Through $J=\lceil\log_2\log(2N)\rceil$ the sum is at most $J\sum_{p\le N}1/p=O((\log\log N)^2)$. The reciprocal-prime estimate follows by setting $s=1+1/\log N$. For $p\le N$, $1/p\le e/p^s$, and the Euler product and the integral test give $\sum_p p^{-s}\le\log\zeta(s)\le\log(1+\log N)$. Above $J$, summing over every integer $a2^j-1\le N$ in the progression costs $O(2^{-j}\log(2N))$ at each $j$, or $O(1)$ altogether. Finally, odd primes with exact exponent $b\ge2$ divide at most $N/p^b$ of the indices to that power, and $v_2(\sigma(p^b))\le1+b\log_2 p$. The series $\sum_p\sum_{b\ge2}(1+b\log_2 p)/p^b$ converges by comparison with $\sum_{n\ge2}(1+\log n)/n^2$. Restricting to odd indices changes the normalization by at most a constant.

There are $\asymp N$ choices of $m$ coprime to ten in $[N/6,N/4]$. By the mean bound, at most $O(N(\log\log N)^2/(k-1))=o(N)$ can have $2^{k-1}\mid\sigma(m)$. Each remaining pair $m,2m$ contributes an active index at most $N/2$. The pairs are disjoint because their first members are odd and their second members even. Each active index sends $\gg\sqrt N$ signed updates. This gives the lower bound matching the unrestricted upper bound. At the full readout modulus, $k=\tfrac12\log_2 N+O(1)$, so this result applies.

The local Lean proof also covers the finite Euler-product logarithmic derivative, its triangular coefficient equation over a commutative ring, the added residue class at multiples of five, and the even-factor divisibility argument. The triple product and the analytic counting estimates are paper results. [Lean proofs](../PrimeFactors/PartitionRecurrence.lean)

## Equal-precision measurements

Both independent series implementations ran at both moduli on each row. At quarter precision they recover the factor residue. At the higher modulus $M>\lfloor\sqrt{2N}\rfloor+1$, balance $\max(p,q)\le2\min(p,q)$ guarantees $1+r<M$, so subtracting one recovers the exact prime. The dense term count is the same at either precision. The signed-update counts are measured and the available-update bound counts every shift before skipping zeros. These are arithmetic operation counts. [Reproducible tests](../tests/test_partition_recurrence.py) · [Public benchmark cases](../benchmarks/partition-recurrence.json)

| Product | Quarter modulus | Signed updates | Exact-readout modulus | Signed updates | Available updates | Dense convolution terms | Prime found |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 143 | 4 | 904 | 32 | 1,252 | 1,302 | 10,153 | 11 |
| 667 | 8 | 10,966 | 64 | 13,386 | 13,864 | 222,111 | 29 |
| 1,457 | 8 | 34,858 | 64 | 43,613 | 45,455 | 1,060,696 | 31 |
| 1,537 | 8 | 37,724 | 64 | 47,254 | 49,288 | 1,180,416 | 29 |

The unbalanced input $123=3\cdot41$ produces $42\bmod32=10$, and the implied candidate $9$ fails division. The input $91$ fails the character prerequisite. The 2,048-bit control passes the character test and exceeds the cap of 1,537 before the program allocates its coefficient array, leaving the whole number unresolved.
