# Can neighboring factorials reveal a prime outside the tested interval?

Yes, if one skips a row. For $N=2183$, all nine integers from 46 through 54 are coprime to $N$. A determinant made from that same block nevertheless reveals 37. A weighted square test also finds 37. In fact, for distinct 1024-bit primes, two square tests cover every success of the 72-offset determinant search below. [Lean proofs](../PrimeFactors/NeighborFactorialDeterminant.lean)

## Consecutive rows

Write $F_w(x)=x(x+1)\cdots(x+w-1)$, with $F_0(x)=1$. Choose any strictly increasing nonnegative widths $n_0,\ldots,n_{r-1}$. For consecutive starting points $x,x+1,\ldots,x+r-1$, with $x>0$, the integer determinant satisfies

$$
\det [F_{n_j}(x+i)]_{i,j=0}^{r-1}
=\prod_{i<j}(n_j-n_i)\prod_{j=0}^{r-1}F_{n_j-j}(x+j).
$$

The width differences can be checked once for every start. If $s$ is the first column with $n_s>s$, the remaining factors cover exactly the ordinary interval from $x+s$ through $x+n_{r-1}-1$. If every $n_j=j$, the remaining product is one. For a product of two distinct primes, testing the width differences and the interval together gives exactly the determinant's gcd, including the case in which both primes divide it. The proof uses the Vandermonde determinant for a monic polynomial basis. [Normand on shifted-factorial determinants](https://arxiv.org/abs/math-ph/0401006) · [Earlier work on overlapping products](reusing-neighboring-interval-products.md)

## Skipping one row

Take starts $x,x+1,x+3$ and widths $0,1,w$, with $w\ge3$. The determinant equals

$$
w(w-1)F_{w-3}(x+3)(3x+w+4).
$$

At $x=46$ and $w=6$, the final term is $148=4\cdot37$. Taking its gcd with 2183 gives 37. Lean checks the complete factorization $2183=37\cdot59$ and the gcd of all nine original integers.

Now assume $N=pq$ with primes $3<p<q\le2p$. Set $x=\lfloor\sqrt N\rfloor$ and $c=w+4$. For $7\le c\le p/2$, a multiple of $p$ at $3x+c$ must equal $4p$. A multiple of $q$ there must equal $3q$. A necessary test accepts exactly 14 residue classes modulo 72. It requires divisibility by four or three with quotient coprime to six. The filtered batch therefore accumulates 14 terms per 72 offsets, down from 72, with one final gcd in either case. It preserves the exact divisor. The two primes cannot occur in the same batch. The runner enforces the offset limit from the public lower bound $p\ge\lceil\sqrt{N/2}\rceil$. [Experiment and work counts](../experiments/neighbor_factorial.py)

## Two square tests cover the short search

For a hit at $4p$, the distance of the integral weighted trace from its square-root lower bound is

$$
16p+9q-24\sqrt N=\frac{(4p-3\sqrt N)^2}{p}\le\frac{c^2}{p}.
$$

For a hit at $3q$, the ordinary trace excess is $(q-\sqrt N)^2/q\le c^2/(9q)$. When $c^2<p$, one of the two integral traces is exactly the ceiling of its lower bound. Its discriminant is the square of $16p-9q$ or $p-q$. This covers all offsets through 78 on every balanced 2048-bit product with 1024-bit factors. At the single width $w=6$ and $p\ge101$, the affine test can succeed only if $16p-9q$ equals 61, 67, 73 or 79. These four possibilities give each $p$ at most two odd partners. [Weighted square tests](factoring-with-two-weighted-square-tests.md) · [Coverage theorem](../PrimeFactors/NeighborFactorialDeterminant.lean)

For $587963$, the 14-term batch and the first parity-eligible $(16,9)$ square test both find $577$, with prime cofactor $1019$. The weighted test also finds 37 on 2183. Both independent 2048-bit controls return their entire input unresolved after the batch and both square tests. Among all 19,546 pairs of distinct 12-bit primes with a 24-bit product, 19,325 have all nine original positions coprime to the input. On these, the single width-six test finds two factors and checking $x+9$ finds 21, with no overlap. Reproduce the census and Lean-checked fixtures with `python3 -m experiments.neighbor_factorial --census --verify`. [Decimal fixtures and expected outcomes](../benchmarks/neighbor-factorial.json)
