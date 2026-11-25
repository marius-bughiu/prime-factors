# Finding a divisor from two nearby continued-fraction rows

For a nonsquare odd product $N$, two nearby rows in the continued fraction of its square root give a signed integer $r$. We can check four numbers congruent to $r$ modulo $N$. Under a height bound computed from the intervening rows, every square found in those four numbers, apart from one predictable value, gives a proper divisor. On 32 independently generated balanced products of 41 or 42 bits, allowing nonzero shifts split nine, including two missed by three bounded comparison searches. On the existing 2,048-bit control, 65,536 rows gave no such square. [Lean proofs](../PrimeFactors/RelativePellWindows.lean) · [Benchmark fixtures](../benchmarks/pell-local-windows.json)

## How the product fixes a square modulo $N$

Take $D=mN$ nonsquare, with public $m>0$. Number the regular continued-fraction rows of $\sqrt{D}$ starting at 1. Row $i$ has numerator $P_i$, denominator $Q_i$, and previous denominator $Q_{i-1}$, with $D=P_i^2+Q_iQ_{i-1}$. Here $P_0=0, Q_0=1$. The partial quotient $a_i$ advances row $i$ to row $i+1$. Starting at $j>i$ with $U=1,V=0$, read $a_{j-1},\ldots,a_i$ backwards, updating the two coordinates by $(U,V)\gets(aU+V,U)$. Then

$$
 w=|Q_iU-P_iV|,\qquad r=(-1)^{j-i}Q_iQ_j,\qquad w^2-DV^2=r.
$$

To see the identity, use the form $F_i(u,v)=Q_i u^2-2P_iuv-Q_{i-1}v^2$. The recurrence gives $F_i(a_i u+v,u)=-F_{i+1}(u,v)$. Walking back from $F_j(1,0)=Q_j$ and completing the square gives the displayed identity. Thus even rows deep in the expansion require only the intervening partial quotients. Classical continued-fraction factorization combines signed norms that multiply to an integer square. Shanks's SQUFOF seeks square forms in a real quadratic cycle and follows an inverse cycle. Bradford and Wagstaff also discuss evaluating reduced forms on small vectors and combining smooth values. Here the specific test looks for an integer square after an additive shift of a pair of norms by a multiple of $N$. The implementation and proofs were written for this repository. [Gower and Wagstaff, *Square form factorization*](https://homes.cerias.purdue.edu/~ssw/squfof.pdf) · [Bradford and Wagstaff, *Square form factorization II*](https://homes.cerias.purdue.edu/~ssw/squfof2.pdf) · [Existing signed-norm search](pell-cycles.md)

Write $b=\lceil\sqrt{D}\rceil$. The regular complete quotients give $0<Q_i\le\sqrt{D}+P_i<2\sqrt{D}$. Hence $r<4D$ and $w^2<D(V^2+4)$. When $b(V+4)<N$, check squares $z^2=r+kN$ with $0\le z^2<4D$. The single shift $k=mV^2$ reproduces $w^2$ and can be skipped. Every other square gives $w\ne z$, while $w+z\le b(V+2)+2b<N$. Now $N$ divides $(w-z)(w+z)$. If $w+z$ were coprime to $N$, then $N$ would divide the nonzero integer $w-z$ of absolute value less than $N$. Thus $1<\gcd(w+z,N)<N$. For a product of two primes this determines both. Equivalently, a hit expresses $(mV^2-k)N$ as a difference of squares. [Kernel-checked height and split implications](../PrimeFactors/RelativePellWindows.lean)

For $m=1$, the four possible radicands are $(r\bmod N)+tN$ for $t=0,1,2,3$. The scan checks a table of quadratic residues modulo 240 before taking an integer square root. It retains at most eight earlier rows. For $T$ steps and depth $d$, it examines at most $Td$ pairs and at most $4Td$ radicands, with $O(d)$ stored rows. No proved bound makes a successful square occur within a practical budget. [Search implementation](../experiments/pell_local_windows.py)

## An example and the cost of larger tests

For $N=34{,}387$, rows 10 and 14 have $Q_{10}=201$ and $Q_{14}=38$. Their intervening quotients, read backwards, are $3,1,1,1$. This yields $V=7$, $w=1301$, and $r=7638$. The shift $k=1$ gives $7638+34387=205^2$. The sum gives $\gcd(1301+205,34387)=251$, leaving the prime 137. The first plain positive square row that splits this product is row 26. Fermat already finds this small pair on its ninth midpoint. [Verified fixture](../benchmarks/pell-local-windows.json)

The holdout used the first 32 distinct 21-bit prime pairs from two SHAKE256 streams with seed `pell-local-windows-v1`, with no gap filter or outcome selection. Each method received only the product. The continued-fraction methods used $m=1$ and up to 4,096 rows, and Fermat used up to 4,096 consecutive midpoints. The local scan processed every row to measure coverage. The methods have different costs per step. Lean checked all 32 exact prime factorizations. [Holdout generator and verification command](../experiments/pell_window_holdout.py) · [Individual witnesses and counts](../research/pell-local-windows.json)

| Test | Products split out of 32 |
| --- | ---: |
| Plain positive square row with a proper gcd | 25 |
| Fermat midpoint | 16 |
| Two-row square with shift $k=0$ | 7 |
| Two-row square with $k\ne0$ | 9 |
| Union of the first three | 26 |
| Union of all four | 28 |

The complete window scans tested 1,042,866 pairs and 3,966,296 non-tautological lifts. Of these, 594,574 required an integer square root. Samples 5 and 26 supplied the two additional splits. Sample 26 used rows 3,811 and 3,816 with opposite signs. Their product was $-850{,}231{,}960{,}080$. Adding four copies of $3{,}618{,}749{,}364{,}589$ gave $3{,}691{,}174^2$. The two prime factors were 1,739,239 and 2,080,651. [Individual results](../research/pell-local-windows.json)

On the existing balanced 2,048-bit fixture, 65,536 rows produced 524,252 eligible pairs, 1,994,506 candidate lifts and 333,639 integer square-root tests. The full input remains unresolved. This result excludes every non-tautological square in the four tested lifts for those pairs. Other depths, longer walks, and other ways to combine rows are open. [Input and reproducible budget](../benchmarks/pell-local-windows.json)
