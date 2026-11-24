# How much work can overlapping power products share?

For a unit $\alpha$ modulo $N$, the polynomial $F_B(X)=\prod_{i=0}^{B-1}(X-\alpha^i)$ tests a whole block of modular powers at once. For $N=150235091$ we combined 24 dense search rows into 22 intervals, built one degree-55 polynomial and evaluated it at 110 points. Three evaluation gcds split the input. The first returned $10007$, and the complete factorization is $10007\cdot15013$. Lean checks that evaluation and both primes. [Proofs and factor certificate](../PrimeFactors/ImplicitPowers.lean)

Merging overlapping intervals can reduce the work on a particular input. On almost all rows of the asymptotic wide-modulus search, however, there is little overlap between the underlying **integer exponent** progressions. Three different short weights in a common class would force a nonzero integer smaller than $m^2$ to be divisible by $m^2$. The argument below bounds this route to sharing without requiring a distributional assumption about $N$.

## A batch algorithm for arbitrary ranges on known orbits

Assume $N=pq$ with distinct primes and the orders of $\alpha$ at both primes exceed some public $H$. For each of $G$ rows one knows a unit $v$, an explicit representation $v=x\alpha^k$, and an interval $[l,h]$ of at most $H$ integers. A row asks whether $v=\alpha^j$ modulo a factor for some $j\in[l,h]$. Group the rows by their supplied representative $x$. The question in one group is whether $x=\alpha^e$ for an exponent in the union of the intervals $[l-k,h-k]$. Merge their overlaps by sorting the endpoints. Let $C$ count the resulting intervals and $V$ their total number of integers, adding separately for each $x$. Both are computable from the input, including any negative endpoints. [Finite orbit identity](../PrimeFactors/ImplicitPowers.lean)

Choose a block width $1\le B\le H$. For a full block starting at $L$, evaluate $F_B$ at $x\alpha^{-L}$. Its zeros modulo either hidden prime are precisely the desired collisions. Build $F_B$ once by a monic product tree and batch all evaluations by a monic remainder tree over $\mathbb Z/N\mathbb Z$. For the incomplete final block of each interval, split its length into powers of two. Build the corresponding $F_{2^j}$ once for each needed size and batch equal sizes across all intervals. Total polynomial degree constructed is $O(B)$ and the number of evaluation points is $O(V/B+C\log(2B))$. The single-point square-root algorithm for a $q$-Pochhammer product is due to Bostan and Yurkevich. This range calculation shares polynomials across input points and accounts for overlapping ranges before evaluation. [Bostan–Yurkevich, Algorithms 1–2](https://arxiv.org/abs/2012.08656) · [Arbitrary-point evaluation over the composite ring, Lemma 3.9](https://arxiv.org/html/2611.06580v1#S3)

A proper gcd immediately gives a divisor. A block gcd equal to $N$ can come from one whole-modulus equality or two different roots modulo $p$ and $q$. Bisect such blocks and evaluate their smaller polynomials by size, across all affected blocks. At most two index positions in an initial block can give a nonunit difference since $B\le H$. At each depth there are at most four children to examine per initially ambiguous block. Only $O(\log(2B))$ different child widths occur from bisection of full blocks and dyadic remainders, with total degree $O(B)$. At a whole-modulus singleton report every original interval containing that position, then apply its row-specific trace recovery. A row contains at most one such singleton by the order condition, so a sorted interval sweep reports the incidences in quasilinear time in the input and output sizes.

If $G\le N^{O(1)}$ and all supplied integers and exponents have $O(\log N)$ bits, the complete range procedure costs $(G+B+V/B)(\log N)^{O(1)}$ bit operations. This pays for sorting, forming powers and polynomials, multipoint evaluation, gcd refinement, and decoding. With $B=\min(H,\lceil\sqrt V\rceil)$ the bound becomes $(G+\sqrt V)(\log N)^{O(1)}$, since $C\le G$ and $V\le GH$. Empty input is immediate. The bound assumes the orbit descriptions and local order certificate are available. In the wide search the descriptions come from Euclidean division of known exponents, and its ordinary setup still costs a visit to every unit residue and a separate order search. [Order setup and its cost](wide-modulus-sieve.md)

## A quadratic bound on merging actual lattice rows

In the one-interval sieve put $\alpha=\beta^{m^2}$. A row indexed by a unit $\sigma\bmod m$ chooses signed weights $|a|,|b|\le C_0\sqrt m$ and $b\sigma^2\equiv aN\bmod m$. Let
$$
 \tau\equiv aN\sigma^{-1}+b\sigma\pmod{m^2},\qquad
 0\le\tau<m^2,\qquad E=aN+b-\tau .
$$
The common radius adds the same multiple of $m^2$ to every $E$. Write $E=e+m^2k$ by ordinary division, giving the public representation $\beta^E=\beta^e\alpha^k$. A CRT translation moves both the row and the admissible indices by the same amount and cancels in their difference. The result here concerns sharing through these ordinary integer representatives. Additional relations obtained from a known modular order could identify further groups.

Fix $a$ and $e=E\bmod m^2$. Since $aN\sigma^{-1}\equiv b\sigma\bmod m$, squaring their difference gives
$$
 \tau^2\equiv4abN\pmod{m^2}.
$$
Consequently every possible $b$ is a root modulo $m^2$ of the same monic quadratic $f(X)=(aN+X-e)^2-4aNX$. For any three roots $x,y,z$, the integer $f(x)(y-z)+f(y)(z-x)+f(z)(x-y)$ equals $(x-y)(x-z)(y-z)$. If all three weights are distinct, its absolute value is positive and at most $(2C_0\sqrt m)^3$. For sufficiently large $m$ this is less than $m^2$, contradicting its divisibility by $m^2$. **There are at most two distinct second weights for a fixed first weight and exponent class.** The argument works with composite $m$. Lean verifies the discriminant congruence, the Vandermonde identity and the finite cardinality bound with its explicit interval-diameter hypothesis. [Lean proof](../PrimeFactors/ImplicitPowers.lean)

For a fixed $b$ let $d=\gcd(a,b,m)$, $r=m/d$, $u=a/d$ and $v=b/d$. Each odd prime of $r$ sees an invertible $2b$, and $\tau\equiv2b\sigma\bmod m$. It therefore determines $\sigma$ there. If $2\mid r$ the residue of a unit at 2 is already fixed.

Shortness restricts the lifts to modulus $m$ as well: **at most $2^{\omega(d)}$ rows have the given $a,b,e$.** For each $\ell\mid d$, at least one of $u,v$ is a unit modulo $\ell$. Otherwise both original weights are divisible by $\ell^2$. The integer $b\sigma^2-aN$ would be divisible by both $m$ and $\ell^2$, hence by $m\ell$ since $m$ is squarefree. Dividing both weights by $\ell$ would give a nonzero shorter vector in the same lattice, a contradiction.

Knowing $e$ fixes $\tau\bmod m^2$ once $a,b$ are fixed, and $d\mid\tau$. Because $d\ell\mid m^2$ we know $\tau/d\bmod\ell$. Dividing the trace congruence and multiplying by $\sigma$ gives
$$
 v\sigma^2-(\tau/d)\sigma+uN\equiv0\pmod\ell.
$$
This is a nonzero polynomial of degree at most two. Each such prime allows at most two roots, and all primes of $r$ have already been fixed. CRT proves the lift bound. The polynomial argument is also valid if $v$ vanishes. [Local root-count theorem](../PrimeFactors/ImplicitPowers.lean)

Write $P$ for the largest prime in the growing primorial and $t\sim P/\log P$ for the number of selected primes. On **every ordinary row** of the wide sieve $d<D_0=\exp(o(\log m))$, hence $\omega(d)=o(t)$. Indeed if $d$ has $j$ distinct prime divisors then $d\ge(j+1)!$, while $t\sim\log m/\log\log m$. The same multiplicity estimate holds on a proportion $1-o(1)$ of *all* rows, by an elementary count. Take $D_1=4^{\omega(m)}(\log m)^2$. The known bound $O(m3^{\omega(m)}/D_1)$ on rows with $d\ge D_1$ is $o(\varphi(m))$, and $\log D_1=o(\log m)$. The ordinary rows also represent a proportion $1-o(1)$ since the original $D_0$ grows faster than $D_1$. [Large-content row count and cutoff](wide-modulus-sieve.md#counting-the-rows-that-need-all-their-candidates)

On this majority of rows a pair $(a,e)$ can occur at most $\exp(o(t))$ times. Different $a$ cannot contribute overlapping dense integer intervals within an $e$ group at the wide-sieve scaling. Their $E$ values differ by at least $N-m^2-2C_0\sqrt m$, while an interval of $W$ indices spans at most $Wm^2=O(\sqrt{Nm}+m^2)=o(N)$. With one interval of length $W$ per row this proves
$$
 V\ \ge\ (1-o(1))\,\varphi(m)W\exp(-o(t)).
$$
Indeed the majority-row intervals belonging to any one $(a,e)$ have pointwise overlap at most $\exp(o(t))$, and intervals for other $a$ or other $e$ cannot increase that multiplicity. Omitting the $o(1)$ exceptional fraction of the wide search preserves the estimate. This result concerns the size of the merged dense intervals. In a scheme that explicitly forms a degree-$B$ polynomial and evaluates at least one point per $B$ successive indices, the $B+V/B$ work count is at least $2\sqrt V$. Thus integer-orbit merging can improve the square-root dense-block estimate by at most $\exp(o(t))$ at this scale. For the dense-block schedule, with $W\asymp\sqrt N/m^{3/2}$, the resulting lower bound is $N^{1/4}m^{-1/4}\exp(-o(t))$. For example, if $\log m=\log N/5-cE+o(E)$ with $E=\log N/\log\log N$ and fixed $c>0$, this is $N^{1/5}\exp(cE/4-o(E))$. This count concerns explicit polynomial degrees and labelled block queries, with common subranges identified by their integer exponents. The argument gives no general lower bound for arithmetic circuits or other implicit representations of the sparse quadratic-image sets.

## One finite block that split the product

With $N=150235091$, $m=70$ and $\beta=2$, the public order check certifies $\alpha=81017472$ through $W=275$. The ordinary-length dense schedules for the 24 units give 22 merged intervals, each of length 275. Choosing $B=55$ yields $V=6050$, a single polynomial of degree 55 and 110 full-block evaluations. There are 107 unit gcds, two gcds of $10007$ and one of $15013$. For exponent residue 1396 and block start $-30686$, the argument $2^{1396}\alpha^{30686}\bmod N$ equals $23098282$. The block product there is $56209319\bmod N$. Its gcd is $10007$. At this same block width the 24 unmerged rows require 120 evaluations, so merging saves ten. Setup scanned 70 residues, used 116 Gauss iterations, and performed 275 direct local-order gcds after 17 baby entries and 17 giant lookups. Polynomial construction, modular powers and the remainder tree add arithmetic work. These counts do not establish a wall-time advantage. [Checked block arithmetic and primality](../PrimeFactors/ImplicitPowers.lean)

The following bounded replay uses the existing product and remainder trees. The assertion on the final block width holds for this fixture.

```python
from collections import Counter, defaultdict
from math import gcd, isqrt
from experiments.powered_order import search
from experiments.short_basis_sieve import shortest_lattice_vector
from experiments.wide_modulus import product_tree, values_at

n, m, block = 150235091, 70, 55
radius = 3*(isqrt(n)+1)*(2*isqrt(m)+2)//(m*m)+2
width = 2*radius+1
cert = search(n, m, width, 4, 100, 0)
assert cert["status"] == "certified_base"
beta, alpha = cert["beta"], cert["alpha"]
intervals = defaultdict(list)
for sigma in range(m):
    if gcd(m, sigma) != 1:
        continue
    eta = n*pow(sigma, -2, m) % m
    a, b = shortest_lattice_vector(m, eta, lambda x: x, Counter())
    tau = (a*n*pow(sigma, -1, m*m) + b*sigma) % (m*m)
    k, e = divmod(a*n+b-tau+radius*m*m, m*m)
    intervals[e].append((-k, width-1-k))

points = []
for e, rows in sorted(intervals.items()):
    merged = []
    for lo, hi in sorted(rows):
        if merged and lo <= merged[-1][1]+1:
            merged[-1][1] = max(merged[-1][1], hi)
        else:
            merged.append([lo, hi])
    for lo, hi in merged:
        assert (hi-lo+1) % block == 0
        for start in range(lo, hi+1, block):
            points.append(pow(beta, e, n)*pow(alpha, -start, n) % n)
poly = product_tree([pow(alpha, i, n) for i in range(block)], n)[-1][0]
print(Counter(gcd(value, n) for value in values_at(poly, points, n)))
```
