# One equation can cover more factor remainders

For an odd 2,048-bit product of two comparable primes, the quartic construction guarantees at most four candidates after guessing one factor's remainder modulo $2^{616}$. Keeping the factorials in the forward differences lowers the sufficient radix to **$2^{615}$**. This joins two former remainder classes in one quartic equation. With degree eight the guaranteed radix falls from $2^{571}$ to $2^{569}$, joining four former classes. These are worst-case existence bounds for each chosen remainder. Finding the correct remainder still requires a large search. [Taylor construction](polynomial-factor-lanes.md) · [Lean lemmas](../PrimeFactors/DifferenceLane.lean)

## Complete small searches and a bounded 2,048-bit comparison

Both solvers used signed quartic equations, the exact same LLL inequality and the same rule for rounding up to a smooth radix. Eight frozen products of two 16-bit primes were passed to each solver using the product alone. We ran both searches three times on each input, alternating their order, then checked the returned prime factors and their products in Lean. Each timing below is the sum of the eight per-input medians. It excludes certificate checking. [Reproduction script](../experiments/newton_lane_holdout.py) · [Per-input results and timings](../research/newton-lane-holdout.json)

| Complete searches over eight products | Exact Taylor | Newton |
| --- | ---: | ---: |
| Prime pairs recovered | 8 | 8 |
| Signed remainder groups and lattice reductions | 902 | 504 |
| Integer-root search nodes | 4,556 | 3,180 |
| Wall time | 0.353 s | 0.210 s |
| Process CPU time | 0.352 s | 0.210 s |

For the 2,048-bit comparison input, Newton's smooth radix reduced the number of signed groups by **43.32%**, from about $4.492\times10^{183}$ to $2.546\times10^{183}$. We searched the first two groups at each method's own radix. Taylor took 5.75 seconds, used 820 integer-root search nodes and returned no factor. Newton took 5.52 seconds, used four integer-root search nodes and returned no factor. The two prefixes cover different remainder classes. These single timings do not establish an average cost per group. The entire input remains unresolved. [Exact counts, work and cofactor](../research/newton-lane-holdout.json)

## What the values of an integer polynomial force

Suppose $N=xy$ with positive $x,y$ within a factor of two. Put $B=\lfloor\sqrt{2N}\rfloor$. For a chosen power $t\ge1$, write $d=2t$ and $m=d+1$. Use the same integer trace as the Taylor construction, with monomials $y^t,\ldots,y,1,x,\ldots,x^t$. Multiplying the trace by $x^t$ gives the polynomial
$$F(X)=\sum_{j=0}^d c_j N^{\max(t-j,0)}X^j.$$
We know $N$, a trial remainder $u$ and a stride $R\ge1$. There is no additional information about $x$ or $y$. Choose a positive modulus $M$ coprime to $N$. If $M$ divides $F(u+Rk)$ for every integer $k$, it also divides the trace at any true factor pair with $x\equiv u\pmod R$. A short trace with absolute value less than $M$ must vanish there. A nonzero coefficient vector gives a nonzero polynomial and at most $d$ integer roots.

For $j=0,\ldots,d$ put $E_j(X)=\prod_{i=0}^{j-1}(X-u-Ri)$, with $E_0=1$. These are monic of successive degrees, so every integer polynomial of degree at most $d$ has unique integer coordinates $b_j$ in this basis. At $X=u+Rk$,
$$E_j(u+Rk)=R^j j!\binom{k}{j}.$$
The binomial is integral even for negative $k$. The matrix of binomials at $k=0,\ldots,d$ is lower triangular with diagonal ones. Its inverse over the integers is the forward-difference transform. Thus $M$ divides every value on the lane exactly when $M\mid b_j R^j j!$ for each $j$. Equivalently the independent moduli in Newton coordinates are
$$q_j=\frac{M}{\gcd(M,R^j j!)},\qquad
  [\mathbb Z^m:\Lambda]=\prod_{j=0}^d q_j.$$
The quotient in these coordinates is the product of the cyclic groups of orders $q_j$. Passing to the actual trace coefficients preserves the index. Multiplication of the monomial coordinates by the indicated powers of $N$ is invertible modulo $M$, and the Newton change of basis is unit triangular. This argument needs $\gcd(M,N)=1$. The same gcd also lets us cancel $x^t$ at the true pair. The factorial method here is an application of classical fixed-divisor theory. [Bhargava on polynomial functions](https://doi.org/10.1515/crll.1997.490.101) · [Bhargava on fixed divisors](https://www.sciencedirect.com/science/article/pii/S0022314X9892220X)

If a trace coefficient multiplier is a nonunit modulo $M$, the unrestricted-polynomial index need not survive. An exact fallback for the coefficient lattice uses $V_{ij}=N^{\max(t-j,0)}(u+Ri)^j$ at $0\le i,j\le d$. Let $g$ be the gcd of the absolute values of the $m$-rowed square minors of the integer matrix $[M I_m\mid V]$. Its columns generate $M\mathbb Z^m+V\mathbb Z^m$, of index $g$ by Smith normal form. The image of $V$ modulo $M$ consequently has size $M^m/g$, which is the exact congruence-lattice index. This formula alone does not permit cancellation of $x^t$ at a nonunit. The factoring bounds below use the public coprimality check.

## Powers of two alone can save one radix bit

For $R=2^e$ and $M=2^L$, write $f_j=v_2(j!)$. Then $q_j=2^{\max(0,L-ej-f_j)}$. An already divisible column imposes no condition. At the original precision $L=ed$, this lowers the base-two logarithm of the Taylor index by exactly
$$S(e,d)=\sum_{j=0}^d \min(f_j,e(d-j)).$$
For example, the last Taylor column has no constraint to save. Simply subtracting $\sum f_j$ from this fixed-precision index would overstate the improvement.

Scale the trace coefficients by $B^{|j-t|}$. The scaled determinant is the index times $B^{t(t+1)}$. The classical LLL first-vector estimate and Cauchy–Schwarz give a sufficient $\ell_1$ bound of $\sqrt m\,2^{t/2}$ times the $m$th root of the scaled determinant. The margin contributed by the congruences, raised to the $m$th power, is $M^m/[\mathbb Z^m:\Lambda]=\prod_j\gcd(M,R^j j!)$. For dyadic $M$, its logarithm is $\sum_j\min(L,ej+f_j)$. This reaches its maximum at $L=ed+f_d$ and stays there. In the optimal dyadic comparison the sufficient condition is
$$2^{et+\sum f_j/m}>\sqrt m\,2^{t/2}B^{t(t+1)/m}.$$
Since $f_j=j-s_2(j)$, where $s_2(j)$ counts binary ones, $\sum_{j=0}^d f_j<\sum_{j=0}^d j=tm$. This gains strictly less than one bit in the continuous radix threshold. Integer rounding can save exactly one bit. This limit concerns the determinant guarantee for this lattice and norm. [LLL first-vector estimate](https://doi.org/10.1007/BF01457454)

## All the primes in the factorial contribute

For any integer stride $R$, take $M=R^d d!$. All $R^j j!$ divide $M$, so the previous product of gcds is exactly $R^{tm}J_d$, where $J_d=\prod_{j=0}^d j!$. This attains the largest possible margin for this lattice over all moduli $M$ coprime to $N$ whenever $\gcd(N,Rd!)=1$. A trial divisor shared by $R$ or one of the primes through $d$ can instead be extracted directly. If a gcd equals $N$, the small-prime check can be performed prime by prime. No factor values are assumed when choosing the modulus.

The implemented search also handles inputs sharing a prime with $d!$. It uses $C_j$, the largest divisor of $j!$ coprime to $N$, and $M=R^d C_d$. Because $R$ is chosen coprime to $N$, $\gcd(M,R^j j!)=R^j C_j$. Thus the triangular basis and its index are exact after replacing each $j!$ by $C_j$ in the margin. For each computed relation the solver checks the weighted size and evaluates $F(u+Rk)$ modulo this actual $M$ at $k=0,\ldots,d$. Lean’s `finite_grid_dvd` proves these evaluations suffice for every integer $k$, including negative values. The theorem `grid_mem_candidates` uses only $\gcd(M,N)=1$, the finite checks and shortness to place the true factor among the roots. It therefore applies to the reduced $M$ even when $N$ shares a prime with $d!$. [Solver](../experiments/newton_lanes.py) · [Direct lattice and search tests](../tests/test_newton_lanes.py)

The weighted LLL criterion for the full factorial becomes
$$ R^{t}J_d^{1/m}>\sqrt m\,2^{t/2}B^{t(t+1)/m}. $$
Dividing the old threshold for $R$ by $J_d^{1/(tm)}$ gives the new threshold. From $\log J_d=\sum_{i=1}^d(d+1-i)\log i=\tfrac12d^2\log d-\tfrac34d^2+O(d\log d)$, the divisor is asymptotic to $d\exp(-3/2)$. For fixed degree this changes a constant. If $t$ grows proportionally to $\log N$, it gives a sufficient stride of order $N^{1/4}/\log N$ under the same balance assumptions. Such high-dimensional lattice reductions have additional cost. The theorem bounds the number of possible remainders and gives no measured end-to-end speedup at those degrees. [Existing growing-degree comparison](polynomial-factor-lanes.md)

With $B^2\le2^{2049}$ the table gives the smallest $e$ satisfying the indicated strict LLL inequality using this size bound for all odd inputs below $2^{2048}$, subject to the public coprimality check. Each radix is $2^e$. These are sufficient mathematical thresholds, and individual products or individual short vectors can do better.

| Degree | Taylor | Dyadic differences at $L=ed$ | Best dyadic differences | Full factorial |
| ---: | ---: | ---: | ---: | ---: |
| 2 | 685 | 685 | 684 | 684 |
| 4 | 616 | 616 | 616 | 615 |
| 6 | 587 | 587 | 586 | 586 |
| 8 | 571 | 570 | 570 | 569 |
| 16 | 544 | 543 | 543 | 541 |
| 64 | 521 | 520 | 520 | 517 |
| 1,024 | 514 | 513 | 513 | 506 |
| 4,096 | 513 | 512 | 512 | 504 |

To reproduce the full-factorial column, compare the integers $2^{2etm}J_d^2$ and $m^m 2^{tm+2049t(t+1)}$ at $e$ and $e-1$. For Taylor replace $J_d$ by 1. For the two dyadic variants replace it by $2^{S(e,d)}$ and $2^{\sum f_j}$, respectively. Even the degree-4,096 full-factorial bound still has $2^{503}$ odd oriented remainders before using reciprocal or sign symmetries.

The following integer checks reproduce the full-factorial column without expanding its largest products. The sums bound $256\log_2 J_d$ below by $H$ and strictly above by $H+tm$. The strict upper bound follows from $\log_2(i^{256})<\lfloor\log_2(i^{256})\rfloor+1$ at every term.

```python
for t, e in [(1, 684), (2, 615), (3, 586), (4, 569),
             (8, 541), (32, 517), (512, 506), (2048, 504)]:
    m = 2*t + 1
    H = sum((m-i) * ((i**256).bit_length()-1) for i in range(1, m))
    K = (m**m).bit_length()-1 + t*m + 2049*t*(t+1)
    assert 2*(256*e*t*m + H) >= 256*(K+1)
    assert 2*(256*(e-1)*t*m + H + t*m) <= 256*K
```

Lean also checks the full-factorial thresholds and failure of the preceding exponent directly through degree 16. It proves the Newton evaluation identity over all integers, the individual dyadic and full-factorial divisibilities, the sizes of their independent residue spaces, and the candidate-membership implication for any coprime modulus after the finite evaluation check. The reduced-factorial index formula follows from the gcd calculation above. The tests check the Python basis and finite evaluations directly. The two-branch valuation calculation below and the asymptotic estimates are mathematical derivations. [Formal statement](../PrimeFactors/DifferenceLane.lean)

## Joining two separated remainder classes

Some pairs can share a polynomial even when their union is not a single congruence class. Take distinct residues $a,b$ modulo $2^e$ and write $h=v_2(a-b)<e$. In the Newton construction interleave the nodes $a,b,a+R,b+R,\ldots$, where $R=2^e$. For the successive Newton products the smallest possible 2-adic valuations on the union are
$$\alpha_{2j}=j(e+h)+f_j,\qquad
  \alpha_{2j+1}=j(e+h)+h+f_j.$$
Indeed, cross-branch differences always have valuation $h$. On a branch containing $j$ previous nodes the product of the same-branch differences is a multiple of $R^j j!$, with equality of valuations at its next node. At an odd step the branch with an extra previous node has minimum valuation larger by $e-h+v_2(j+1)>0$. Each displayed minimum is attained at the next node. Divisibility on the union therefore gives exactly the independent precisions $\max(0,L-\alpha_i)$ by induction on these nodes. The earlier terms have the required divisibility everywhere and later terms vanish at the current node. This is the two-branch instance of a classical $p$-ordering. [Bhargava's construction](https://doi.org/10.1515/crll.1997.490.101)

Take $L\ge\alpha_d$ to maximize the determinant margin. Writing $T=2\sum_{j<t}f_j+f_t$ gives
$$\sum_{i=0}^{2t}\alpha_i=etm-(e-h)t(t+1)+T.$$
Siblings at $h=e-1$ give the same valuation sequence as a single lane of stride $2^{e-1}$. Every extra bit of separation below $e-1$ lowers the sum by $t(t+1)$. At degree eight, $e=571$, $h=569$, $T=7$ and the sum is $20523$. The squared LLL comparison $2^{2\cdot20523}>9^9 2^{36+2049\cdot20}$ covers both branches at once. For example $a=1$ and $b=1+2^{569}$ give two distinct, non-sibling odd classes. At $h=568$ this sufficient comparison fails. The sibling pairing is always at least as good for the pure count; the separated formula also allows a prescribed pair of classes to be tested together.
