# Which factor intervals can a prime modulus discard?

Let $N=pq$ with distinct primes $p<q\le 2p$, and write $X=\sqrt N$. Divide the possible smaller factors in $[X/\sqrt2,X]$ into consecutive blocks of $H$ integers. For a block $I=[u,v]\cap\mathbb Z$, take the public companion interval $J=[N/v,N/u]\cap\mathbb Z$. A prime $2X<\ell<4X$ discards the whole block if $xy\equiv N\pmod\ell$ has no solution in $I\times J$. This retains the true factor block on every input.

For each fixed $\delta>0$, **almost every block is discarded when $H\le X^{1/2-\delta}$, and almost every full block survives when $H\ge X^{2/3+\delta}$**. Both assertions are uniform over the product and the auxiliary prime, whenever there are full blocks. They count search intervals, so they apply also when the prime factors are sampled independently. The bounds below leave a range of widths between the two conclusions.

## Narrow blocks and the cost of testing them

A local witness has $xy=N+j\ell$ for an integer $j$. As $N/v\le y\le N/u$ and $u\le x\le v$,
$$
 |xy-N|\le N(v-u)/u\le \sqrt2 X(H-1).
$$
Hence $|j|<H$. Each of these fewer than $2H$ possible positive products is at most $\sqrt2 X^2$ and has at most $X^{o(1)}$ positive divisors, uniformly. Each first divisor determines its partner and its unique row block. Thus **at most $HX^{o(1)}$ blocks survive** one prime. There are order $X/H$ blocks for $H=o(X)$, so a surviving fraction of at most $H^2 X^{-1+o(1)}$ follows. This uses the same elementary divisor bound as the existing square-modulus search. [Earlier algorithm and divisor estimate](modular-hyperbola.md)

Several independently sampled primes give a stronger guarantee on narrow blocks. Let $P$ be the number of primes in $(2X,4X)$. The interval $J$ contains at most $2H$ integers since $N(v-u)/(uv)\le 2(H-1)$. In a block containing no exact factor pair, each of its at most $2H^2$ candidate pairs has a nonzero absolute product error smaller than $(2X)^2$. At most one prime in the pool divides that error. If the same $T$ uniform independent primes are tested on every block, the probability **any false block survives them all** is at most
$$
  \#\{\text{blocks}\}\;\min(1,2H^2/P)^T .
$$
Independence is needed only between prime draws for one fixed false block. By the prime number theorem $P\asymp X/\log X$. At $H\le X^{1/2-\delta}$ even $T>1/(2\delta)$ fixed suffices for the bound to tend to zero. Uniform primes can be drawn by testing uniformly sampled integers for primality until one passes, at expected $O(\log X)$ trials per prime. [Lean bound on the number of primes preserving a false witness](../PrimeFactors/HyperbolaBoxes.lean) · [Agrawal, Kayal and Saxena, polynomial-time primality testing](https://doi.org/10.4007/annals.2004.160.781)

For $N=15049=101\cdot149$ and $H=7$, the six smaller-factor blocks cover $87$ through $122$. Successive tests at $251,257,263$ leave three, then two, then just the true block $[101,107]$. The false block $[94,100]\times[151,160]$ has two witnesses at $251$, one at $257$ and zero at $263$. Lean checks those counts. A direct test scans the rows and checks whether the unique residue $Nx^{-1}\bmod\ell$ belongs to $J$. Across all blocks this costs $O(X)$ modular inversions for the first prime alone in a full scan, and at most $O(TX\,\operatorname{polylog}N)$ bit operations for all tests. The small surviving set gives a reduction in candidate intervals. Achieving a corresponding reduction in arithmetic work needs a faster way to locate it.

## Why wide blocks survive even when their columns follow the product

Fix any nonzero residue $c\bmod\ell$. Let $C(a,b)$ count $xy=c$ over $\mathbb F_\ell$ in a translated window with consecutive side lengths $h,k\le\ell$. All $\ell^2$ cyclic translations have mean $\mu=(\ell-1)hk/\ell^2$. Their total squared deviation satisfies
$$
   \sum_{a,b}|C(a,b)-\mu|^2 \le 4\ell hk.
$$
Indeed, take the unnormalized additive Fourier transform on the two coordinates. Away from the zero frequency, the transform of the hyperbola indicator is a Kloosterman sum of magnitude at most $2\sqrt\ell$. On either nonzero coordinate axis the sum is exactly $-1$. The transform of the translated count multiplies this by the two interval transforms, up to conjugation. Parseval gives a factor $1/\ell^2$ and the one-dimensional interval transforms have squared sums $\ell h$ and $\ell k$. The trivial frequency contributes only the mean. This argument uses Weil's theorem over finite fields. Chan gives a corresponding translated second-moment estimate for general moduli, and Browning and Haynes treat paired intervals with disjoint rows. [Weil](https://doi.org/10.1073/pnas.34.5.204) · [Chan, Theorem 1](https://arxiv.org/abs/0812.1526) · [Browning and Haynes, Theorem 1](https://arxiv.org/abs/1204.6374)

An empty $H\times K$ rectangle contains $(H-h+1)(K-k+1)$ translates of the small window, each contributing $\mu^2$ to that sum. For a family whose row intervals are disjoint modulo $\ell$, these translation sets are disjoint even if the column intervals are chosen from the product or overlap. Thus the number $D$ of empty rectangles satisfies
$$
 D\le \frac{4\ell^5}{(\ell-1)^2 h(H-h+1)k(K-k+1)}
   \le \frac{64\ell^5}{(\ell-1)^2 H^2K^2},
$$
where the second bound uses $h=\lceil H/2\rceil$, $k=\lceil K/2\rceil$. In particular **every individual rectangle** with $HK>8\ell^{5/2}/(\ell-1)$ contains a witness. The finite packing and squared-deviation charge are proved in Lean. The Fourier estimate above is a paper deduction from the cited theorem. [Lean packing and deviation lemmas](../PrimeFactors/HyperbolaBoxes.lean)

For the factor blocks, the real interval $[N/v,N/u]$ has length $N(v-u)/(uv)\ge H-1$ on a full block. Its integer points contain a run of $K=H-1$ columns. All row and column intervals fit below $\ell$, and distinct row blocks are disjoint. For $H\ge2$ the number of discarded full blocks is therefore $O(X^3/H^4)$. For $H=o(X)$ they account for at most $O(X^2/H^3)$ of the full blocks. The same proportion bound holds whenever the interval contains at least one full block, as its full-block count is then comparable to $X/H$ for large $X$. A final short block can be checked separately. With a menu of $T$ such primes, a union bound raises the upper bound on the discarded proportion to $O(TX^2/H^3)$ even if the search chooses different members of the menu for different blocks. This last conclusion concerns tests that ask for a witness at each prime separately. Requiring one pair to satisfy a joint product modulus is a stronger test.
