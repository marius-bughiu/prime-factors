# How precisely must we know the fixed sum?

For a 2,048-bit product of two distinct 1,024-bit primes, the fixed sum $F(1)$ rounded to **1,024 fractional bits** supports recovery with polynomial *average* decoding work. The average is over uniformly chosen distinct primes of the given size, conditioned on their product having 2,048 bits. Decoding can be expensive on individual inputs. With **1,060 fractional bits**, one application of a univariate small-root theorem suffices for all but a fraction below $2^{-20}$ of the same population. These are bounds for decoding a supplied value. We have no cheap way to calculate the sum itself from a general product. The earlier 2,048-fractional-bit result gives a worst-case guarantee using ordinary integer arithmetic. [Definition and full-precision proof](divisor-samples.md#rounding-a-square-from-the-fixed-sample) · [Lean finite steps](../PrimeFactors/PhasePrecision.lean)

## How many intervals does one reading leave?

Let $N=pq$ have $n$ bits and put $b=\lceil n/2\rceil+g$ for $g\ge0$. The four-root formula gives $F(1)=2\cos(2\pi/N)+2\cos(2\pi x)$, where $x=H/N\in(0,1/2)$ and $H$ is a folded mixed square root of one. Set $\mu=\min(x,1/2-x)$. We use $\mu$ to bound work in the proof. The decoder uses the measured word and $N$ alone. [Classical Salié evaluation, Lemma 4.14](https://doi.org/10.1007/s40687-025-00544-4)

Rounding $F(1)$ contributes at most $2^{-b-2}$ to the hidden cosine after division by two. Calculate the public cosine to error at most $2^{-b-2}$, so the hidden cosine is known to within $2^{-b-1}$. For any $y\in[0,1/2]$ consistent with the same estimate, the cosine difference from the true $x$ is at most $2^{-b}$. It is also bounded below by

$$2\,|\sin(\pi(x+y))\sin(\pi(x-y))|\ \ge\ 8\mu|x-y|.$$

Here $\mu\le x+y\le1-\mu$ and $|x-y|\le1/2$, so Jordan's sine inequality applies to both factors. All possible integer numerators therefore lie in a real interval of diameter at most $N2^{-b}/(4\mu)$. Compute its endpoints by inverting the upper and lower cosine bounds after clipping to $[-1,1]$. Polynomially many bits and operations suffice to round both ends outward with total excess at most two integer units. For example, bisection to an error below $1/(4N)$ in turns suffices. At an inconclusive midpoint comparison one can use cosine error $O(N^{-2})$ and the global inequality $|\cos(2\pi u)-\cos(2\pi v)|\ge8|u-v|^2$ to certify such a phase enclosure. [Inverse bounds](divisor-samples.md#a-single-higher-precision-sample)

Partition the resulting integers into consecutive blocks of $\lfloor\sqrt N\rfloor+1$ entries. For a block starting at $c$, every possible offset is a root of interest only if $(c+u)^2-1=0\pmod N$. The full-modulus, monic quadratic case of May's Theorem 7 finds all roots with $|u|\le\sqrt N$ in polynomial bit time. Check the returned roots by squaring and extracting a proper gcd. The true $H$ is in the cover. A bound on the number of calls for the whole cover, even if every block is visited, is

$$2+\frac{2^{-g}}{4\mu}.$$

Indeed the number of blocks for an integer interval $[L,U]$ is at most $1+(U-L)/(\lfloor\sqrt N\rfloor+1)$, and $\sqrt N2^{-b}\le2^{-g}$. For a short interval the decoder can instead center one call at its rounded midpoint, covering both positive and negative offsets. An interval of diameter at most $\sqrt N+2$ fits in this single call for $N\ge25$. The polynomial lattice bound supplies no practical running time at the endpoint. [May, Theorem 7](https://digital.ub.uni-paderborn.de/hsmig/download/pdf/3235#page=38)

## Counting the primes near a flat part of the cosine

Take the primes from $[X,2X)$ with $X$ a power of two, and condition on $pq\ge 2X^2$. We count ordered pairs, so exchanging the primes gives each allowed product the same weight. Hold $q$ fixed. If $z$ is the least positive residue of $2p^{-1}\bmod q$, then $u=pz-1$ is $-1\bmod p$ and $1\bmod q$, with $0<u<N$. The unfolded phase is

$$\frac{u}{N}=\frac{z}{q}-\frac1N.$$

Folding preserves its distance $\mu$ to the nearest integer or half-integer. Distinct allowed $p$ in this row give distinct $z$, because the interval of possible partners has length $X\le q$. A narrow interval of inverse labels consequently contains few candidate primes, regardless of how the primes are distributed within that interval.

For each label define the positive integer $D=\min(2z,|2z-q|,2(q-z))$. There are at most four labels at each $D$, since $2z$ must equal one of $D,q-D,q+D,2q-D$. Before shifting by $1/N$ the margin is $D/(2q)$. After the shift $\mu\ge D/(2q)-1/N\ge D/(4q)$ when $p\ge4$. Hence the sum of $1/\mu$ over all eligible $p$ in one row is at most $16q\sum_{j=1}^q1/j\le16q(1+\log q)$. The prime count in $[X,2X)$ is $O(X/\log X)$, while the subinterval $[\sqrt2X,2X)$ alone yields $\gg(X/\log X)^2$ ordered eligible pairs. Dividing the row total summed over $q$ by the population size gives

$$\mathbb E[1/\mu]=O((\log X)^2).$$

Thus one fixed half-precision word gives deterministic recovery with a polynomial mean operation count over this population. The proof never assumes uniform random phases. Even subtracting $O(\log\log N)$ further fractional bits keeps the mean polynomial, since this only multiplies the number of blocks by a polynomial in the bit length. [Lean inverse-label multiplicity, margin and summation](../PrimeFactors/PhasePrecision.lean)

For the explicit target put $X=2^{1023}$. There are fewer than $1.511X/\log X$ possible choices for $q$ and more than $(0.22X/\log X)^2$ eligible ordered pairs. Also $\log(2X)<710$. Inserting these values in the row estimate yields $\mathbb E[1/\mu]<2^{29}$. At $g=27$, the bound on the average number of lattice calls is therefore **less than three**. This is a count of theorem applications. [Explicit prime counts](stride-budget.md#an-explicit-bound-at-exactly-2048-bits) · [Rosser and Schoenfeld, Corollary 1](https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf#page=6)

For the single-call guarantee choose $g=36$ and $\rho=2^{-38}$. When $\mu\ge\rho$, the diameter including numerical padding is at most $\sqrt N+2$. Conversely, if $\mu<\rho$, the grid point $z/q$ lies within $\rho+1/N$ of an integer or half-integer. On one whole period the three intervals at $0,1/2,1$ have total length at most $4(\rho+1/N)$, so at most $4q\rho+4/p+3\le8X\rho+8\le9X\rho$ candidate labels occur per row. The same prime counts bound the exceptional fraction by $1.511\cdot9\cdot710\rho/(0.22)^2<2^{18}\rho=2^{-20}$. The complete cover still works on exceptions. Lean checks the cosine inequality, the four-label row bound, the shift in margin, the finite weighted summation and the last numerical comparisons. The use of the prime-count and lattice theorems and the aggregate population bounds are paper deductions.

## When the interval stays wide

For $N=4{,}112{,}783=2027\cdot2029$ the folded mixed root is $2028$. With $b=11$, the rounded sum is exactly four. Lean shows that **every** real candidate numerator between zero and 7,000 gives the same rounded answer under the cosine formula. This interval is longer than three times $\sqrt N$. Most of these numerators fail the modular square test. The example explains why the half-precision enclosure can require several blocks, even with exact arithmetic. Its factors are also recoverable using the special identity $2028^2=N+1$. [Checked interval and primes](../PrimeFactors/PhasePrecision.lean)

The interval strategy also has a precision limit away from the flat ends. For any complete quantization cell of width $2^{-b}$ in the range of $2\cos(2\pi/N)+2\cos(2\pi x)$, the derivative in turns has absolute value at most $4\pi$. Its inverse interval therefore covers at least $N2^{-b}/(4\pi)$ units in the numerator. Tiling that *entire* interval with blocks of diameter $O(\sqrt N)$ requires $\Omega(\sqrt N2^{-b})$ blocks whenever this quantity grows. For instance, dropping a fixed fraction of the $n/2$ precision incurs exponentially many blocks for each full cell. This only measures complete interval coverage. A shortcut using other information in $N$ is still possible.
