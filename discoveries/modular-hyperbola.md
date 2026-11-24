# Counting modular inverses in the balanced factor interval

Given an odd integer $N$, one can find every factor pair $1<x\le y\le2x$ in deterministic $N^{1/3+o(1)}$ bit operations without constructing a multiplication circuit. The algorithm counts points in rectangles by Euclidean division and verifies their products. It visits exponentially many low residues at 2048 bits. It improves on a complete balanced trial scan, while Lehman's classical method already reaches the cube-root exponent and Harvey proves a one-fifth bound for general factorization. [Lehman](https://doi.org/10.1090/S0025-5718-1974-0340163-2) · [Harvey](https://arxiv.org/abs/2010.05450)

## What a pair of high prefixes reveals

Take an odd target and modulus $M=2^m$ with $m\ge1$. In aligned blocks $x\in[aL,(a+1)L)$ and $y\in[cL,(c+1)L)$ where $M\mid L$, the accepted suffixes for $xy\equiv N\pmod M$ are identical for every pair of prefixes $a,c$. There are exactly $L^2/(2M)$ accepted pairs. Each of the $L/2$ odd values of $x$ selects one residue $Nx^{-1}$, realized $L/M$ times by $y$. Thus every odd low residue survives a prefix guard that selects a whole pair of such blocks. For $b$-bit inputs with $h$ fixed top bits, this holds through precision $m=b-h$.

## Counting an entire family of higher digits

For the full balanced search take the smallest power $B=2^b$ greater than $\lfloor\sqrt{2N}\rfloor$. Use the inclusive integer ranges

$$
\max(2,\lceil\sqrt{N/2}\rceil)\le x\le\lfloor\sqrt N\rfloor,
\qquad \lceil\sqrt N\rceil\le y\le\lfloor\sqrt{2N}\rfloor.
$$

Set $r=\lceil2b/3\rceil$ and $R=2^r$. For each odd $0<u<R$ compute $i=u^{-1}\bmod R$, $w=Ni\bmod R$ and $d=(N-uw)/R$. Write $x=u+Rv$ and $y=w+Rz$. Both ranges yield intervals for the high digits, with $0\le z<R$ because $R^2\ge B$. Expanding the product gives

$$
xy\equiv N\pmod{R^2}
\quad\Longleftrightarrow\quad
uz+wv\equiv d\pmod R
\quad\Longleftrightarrow\quad
z\equiv i(d-wv)\pmod R.
$$

For an affine value $f(v)=i(d-wv)$ and desired interval $l\le z<h\le R$, its indicator is

$$
\left\lfloor\frac{f(v)+R-l}{R}\right\rfloor-
\left\lfloor\frac{f(v)+R-h}{R}\right\rfloor .
$$

Sum both floors over the requested $v$ interval. For $F(n,m,a,t)=\sum_{j=0}^{n-1}\lfloor(aj+t)/m\rfloor$, first remove the integer multiples of $m$ from $a,t$. With $0\le a,t<m$, $n>0$ and $H=\lfloor(a(n-1)+t)/m\rfloor$, the sum is zero for $H=0$. Otherwise count indices above each level from $1$ through $H$ to get

$$
F(n,m,a,t)=nH-F(H,a,m,m-t+a-1).
$$

The denominators follow Euclid's algorithm, giving $O(b)$ divisions per count. For a positive count, bisect the interval until all hits can be emitted. Each split needs only the left count because the parent count is known. Verify $xy=N$ at each reported pair. A count or a sum of weights over the *exact* factors can then be accumulated as the pairs are accepted.

## Work and possible state sharing

If $T$ pairs pass the modular test, the search needs $O((R+T)\operatorname{poly}(b))$ bit operations. There are $R/2$ initial classes. In a class with $t$ hits, every split contains a hit and the bisection has depth $O(b)$, giving $O(1+tb)$ count queries. A depth-first traversal uses polynomial working space, plus any retained output.

Every hit has a positive product $jR^2+(N\bmod R^2)<B^2$. For any one such integer $m$, its first factor identifies a divisor and determines its partner. Hence $T\le(1+B^2/R^2)B^{o(1)}$ uniformly. To see the divisor estimate, fix $\epsilon>0$. For prime powers $p^e$ with $p\ge2^{1/\epsilon}$, use $e+1\le 2^e\le p^{e\epsilon}$. For the finitely many smaller primes, multiply the finite constants $\sup_e(e+1)p^{-e\epsilon}$. This bounds the divisor count by $C_\epsilon m^\epsilon$. Choosing $R$ within a constant factor of $B^{2/3}$ balances the two work terms. These bounds hold for every odd input, including ones with no balanced pair.

Can a digit DP simply merge classes with the same affine rule? The slope is $-Nu^{-2}\bmod R$. For $r\ge3$ it has exactly $R/8$ distinct values. Two slopes coincide exactly when the ratio of the two odd residues squares to one. The roots are precisely $t\equiv\pm1\pmod{2^{r-1}}$, giving four choices modulo $R$. Indeed, of $t-1,t+1$ one has 2-adic valuation one, so the other must supply $2^{r-1}$. Distinct slopes give distinct maps on the full high-digit residue domain regardless of the intercept. This counts states for direct merging of identical affine maps. Sharing arithmetic across different slopes or exploiting restricted intervals remains possible. A 2048-bit balanced input has $b=1025$ and $r=684$, giving $2^{683}$ initial classes in this algorithm.

For comparison, Cilleruelo and Garaev bound the number of points in an arbitrary translated square of side $L$ for a **prime** modulus $p$. In particular the count is at most $L^{o(1)}$ when $L<p^{1/4}$. Their result concerns concentration. The exact reporting procedure here uses the square modulus and its affine expansion at half the precision. [Cilleruelo and Garaev, Theorem 1](https://arxiv.org/abs/1007.1526)

## Reproducing the measurements

Both searches below finish the whole balanced interval, including work after a factor is found. Timings are three-run medians in CPython 3.9.6 on arm64. The class and hit counts are deterministic. The Euclidean steps column counts floor-sum iterations. Timings also include modular inversions and integer product checks.

| $N$ | Low classes | Range counts | Euclidean steps | Modular hits | Odd trial candidates | Affine / trial seconds |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1900014700027 | 8,192 | 10,175 | 64,561 | 422 | 201,863 | 0.036 / 0.007 |
| 1500000011500000007 | 1,048,576 | 1,202,499 | 11,553,487 | 20,565 | 179,359,734 | 5.86 / 7.39 |

```sh
python3 experiments/modular_hyperbola.py 1900014700027 --compare-trial 3
python3 experiments/modular_hyperbola.py 1500000011500000007 --compare-trial 3
python3 -m unittest discover -s tests -p test_modular_hyperbola.py
```

The returned pairs are $(1000003,1900009)$ and $(1000000007,1500000001)$. Lean checked the factorization certificates generated from both outputs. The implementation takes only the product. Tests compare floor sums, reported points and exact pairs against exhaustive enumeration at small widths. Lean proves equality of the aligned suffix filters, both lift equivalences, the interval indicator, and the divisor-sum bound. The search schedule and asymptotic work estimate are paper arguments. [Lean theorems](../PrimeFactors/ModularHyperbola.lean) · [Implementation](../experiments/modular_hyperbola.py) · [Decimal fixtures](../benchmarks/modular-hyperbola.json) · [Tests](../tests/test_modular_hyperbola.py)
