# Finding a line through the candidates in a factor interval

Given only $N=pq$ with $p<q\le2p$, one can test a whole interval of possible $p$ by counting integer points and evaluating their first and second moments. If the points lie on a line, one quadratic checks the interval, however many points it contains. A small wheel makes this guarantee apply to wider intervals. On the 41-bit product $1900014700027$, a complete sweep took 5,111 interval tests without a wheel and 1,200 with modulus 210. Both recovered $1000003$ and $1900009$.

The result concerns the number of interval tests and their cost. Hiary already gives a deterministic cube-root factoring algorithm that tests a short divisor interval by one quadratic, using a continued fraction of $N/x^2$. The approach below constructs the line from all the integer points in a rational triangle, tests whether wider intervals are collinear on the actual input, and counts the effect of an affine congruence lattice. Small-triangle determinant methods for integral points on arcs are classical. Harvey's general one-fifth exponent is stronger. [Hiary, Lemmas 3.1–3.2](https://arxiv.org/pdf/1408.2608) · [Bombieri and Pila](https://people.maths.ox.ac.uk/pila/Ovals.pdf) · [Harvey](https://arxiv.org/abs/2010.05450)

## A strip with a computable line

For $\lceil\sqrt{N/2}\rceil\le A\le x\le B\le\lfloor\sqrt N\rfloor$, the tangent at $A$ and the chord joining the endpoints enclose the reciprocal:
$$
 T(x)=N(2A-x)/A^2\ \le\ N/x\ \le\ U(x)=N(A+B-x)/(AB).
$$
Take every integer pair with $T(x)\le y\le U(x)$ satisfying the chosen lattice constraint. Every targeted factor pair is included. Let $C$ count these points, and let $S_x,S_y,S_{xx},S_{xy},S_{yy}$ be their coordinate sums. Empty strips end the search in that cell. Set
$$
 V_x=C S_{xx}-S_x^2,\quad V_y=C S_{yy}-S_y^2,\quad D=C S_{xy}-S_x S_y.
$$
If $V_x=0$, all first coordinates equal $S_x/C$. Otherwise the points are collinear exactly when $V_xV_y=D^2$. Indeed the sum of the squared residuals of the centered line vanishes in this case. Every point then obeys
$$
 C V_x y=C D x+V_x S_y-D S_x.
$$
Substituting $y=N/x$ gives a quadratic, including a possible linear case. Verify integer roots against the interval, lattice and product. Wider strips whose points span two dimensions can be bisected. [Lean covariance and quadratic lemmas](../PrimeFactors/QuotientSearch.lean)

These moments require no list of points. For each integer first coordinate, the included ordinates end at $\lfloor U(x)\rfloor$ and start immediately after $\lceil T(x)\rceil-1$. The same bounds apply after an affine change to integer lattice coordinates. Summing powers of the ordinate first leaves fixed-degree weighted floor sums in the other coordinate. For a reduced slope and intercept $0\le a,b<m$, write $f(i)=\lfloor(ai+b)/m\rfloor$, $h=f(n-1)$, and define
$$
 F_{r,s}=\sum_{0\le i<n}{i\choose r}{f(i)\choose s}.
$$
For $s>0$ transpose the levels of $f$ and apply the hockey-stick identity. This gives
$$
 F_{r,s}={n\choose r+1}{h\choose s}
 -\sum_{0\le j<h}{j\choose s-1}
 {\lfloor(mj+m-b+a-1)/a\rfloor\choose r+1}.
$$
The last sum is zero when $h=0$, including $a=0$. For arbitrary signed slope or intercept, divide by $m$ first. Expand the removed affine term by Vandermonde's binomial identity and finite differences. The sum of the two indices never increases, so caching all the required pairs costs a bounded number of states per Euclidean step at fixed degree. Coefficients, counts and moments have $O(\log N)$ bits whenever the wheel is at most polynomial in $N$. This follows from the fixed degrees, the $O(\log N)$-bit triangle coefficients, and the polynomial bounds on coordinates. [Implementation and direct recurrence checks](../experiments/quotient_search.py)

## How many cells the wheel saves

Take an integer $m$ coprime to $N$. The code records a proper setup gcd separately as `setup_divisor`, removes all primes shared with $N$ from the requested wheel, and completes the band with the resulting coprime wheel. An incidental divisor outside the band is absent from `pairs`. In each unit class $x\equiv a\pmod m$ choose $i=a^{-1}\bmod m^2$. A true factor pair obeys
$$
 y\equiv Ni-Ni^2(x-a)\pmod {m^2}.
$$
To see this, expand the reciprocal and use $(x-a)^2\equiv0\pmod{m^2}$. Thus all such pairs lie in one affine lattice with first-coordinate spacing $m$ and vertical spacing $m^2$. The signed determinant of any three of its points is divisible by $m^3$. All classes and bases are determined by $N,m$. [Lean lift and determinant](../PrimeFactors/QuotientSearch.lean) · [Earlier digit-based use of the lift](modular-hyperbola.md)

Set $H=B-A$. The triangle between the chord and tangent has twice its area equal to $NH^3/(A^2B)$. Every inscribed triangle has at most that area, and a nonzero signed determinant in this lattice has magnitude at least $m^3$. Consequently every occupied cell is collinear when
$$
 N H^3 < m^3 A^2 B.
$$
The implementation uses a uniform width determined by the smallest $A$. A balanced band of length $O(\sqrt N)$ needs
$$
 O\!\left(\varphi(m)\left[1+N^{1/3}/m\right]\right)
$$
cells. Each costs $O(\log N)$ arithmetic operations on $O(\log N)$-bit integers at fixed moment degree. Enumerating residues costs $m$ gcds and at most $\varphi(m)$ inverses modulo $m^2$. For example, choose $z=\lfloor\sqrt{\log N}\rfloor$ and $m=z!$. Then $m=N^{o(1)}$, including its construction and enumeration in the cost. Expanding the finite Euler product shows $m/\varphi(m)\ge\sum_{j=1}^z1/j$, since all prime factors of those integers divide $m$. This proves **$O(N^{1/3}/\log\log N)$ interval tests** for sufficiently large balanced inputs. The logarithmic cost per test still applies. For the particular $m=210$ schedule a 2048-bit balanced input coprime to 210 takes more than $2^{678}$ initial cells: the band has at least $\sqrt N/4$ integers, the implemented width is at most $210N^{1/6}$ at this size, and there are 48 classes.

One further constant is available without enumerating residues. When $N$ is coprime to 6, every factor $x$ has $x^2\equiv1\pmod{24}$. All true points therefore lie in the single affine lattice $x$ odd, $y\equiv Nx\pmod{24}$, of index 48. The same area proof replaces $m^3$ with 48 for that lattice. The measurements below use the explicit unit-class construction above.

## The best uniform width at 2,048 bits

For **every 2,048-bit product of two 1,024-bit primes**, the minimum number of initial cells in this particular full, uniform-width wheel sweep lies strictly between $2^{677}$ and $2^{678}$. This optimizes over all positive wheel moduli coprime to the product, including choices that depend on the entire product. The upper bound uses a single wheel chosen in advance. This counts the cells visited if the sweep completes. Early discovery, skipping whole residue classes by a different argument, or using adaptive larger widths changes the question. [Finite integer checks](../PrimeFactors/QuotientBudget.lean)

Write $L=\lceil\sqrt{N/2}\rceil$, $U=\lfloor\sqrt N\rfloor$, and $W=U-L+1$. The default rule chooses the column width $h=\lceil mL/N^{1/3}\rceil$. Capping a width at $W+1$ leaves its number of cells unchanged, so we can use the uncapped expression. Its exact count is

$$C_N(m)=\varphi(m)\left\lceil\frac W h\right\rceil.$$

For a lower bound write $X=\sqrt N$. At this size $W\ge X/4$ and $h\le(3/4)mN^{1/6}$. Indeed $L\le X/\sqrt2+1$ and $h\le mL/N^{1/3}+1$, and both endpoint errors fit within the displayed slack. Thus $C_N(m)\ge N^{1/3}\varphi(m)/(3m)$. If $m\le2^{1366}$, it has at most 166 distinct prime divisors, since the product of the first 167 primes, through 991, is larger. In the product $m/\varphi(m)=\prod_{r\mid m}r/(r-1)$ over distinct prime divisors, replacing each divisor by the corresponding smallest prime can only increase the value. The product through the 166th prime, 983, is less than 13. Consequently $C_N(m)>N^{1/3}/39>2^{677}$ because $39^3<2^{16}$ and $N\ge2^{2047}$. If $m>2^{1366}$, even one cell per class suffices for the lower bound. To see this, $\varphi(m)^2\ge m/2$ by multiplication over prime powers. The ratio $\varphi(r^a)^2/r^a=r^{a-2}(r-1)^2$ is at least one except for $r^a=2$, where it is one half.

For the upper bound choose $m$ as the product of all primes through 463. Both input primes exceed 463, so $m$ is coprime to $N$. Exact integer products give $11\varphi(m)<m<2^{641}$. Here $W\le(5/12)L$ since $U+1\le\sqrt2 L+1\le(17/12)L$. It follows that

$$C_N(m)\le\varphi(m)+\frac{5\varphi(m)}{12m}\,N^{1/3}<2^{641}+\frac{5}{132}N^{1/3}<2^{678}.$$

For the last inequality, $N^{1/3}<26\cdot2^{678}$ since $26^3>2^{14}$. The calculation uses integer comparisons on a few small prime products. It does not generate the cells of this enormous sweep.

There is also a sharp asymptotic count as balanced semiprimes grow. With natural logarithms,

$$\min_{(m,N)=1} C_N(m)\sim e^{-\gamma}(\sqrt2-1)\,\frac{N^{1/3}}{\log\log N}.$$

Indeed $W/L\to\sqrt2-1$ and $mL/N^{1/3}\to\infty$ uniformly in $m\ge1$, so rounding the width gives a relative $o(1)$ error. For $m\le N$, compare the prime divisors of $m$ in increasing order with the primes in the largest primorial at most $N$. Its last prime is asymptotic to $\log N$ by the prime number theorem. Mertens' product theorem gives $m/\varphi(m)\le(e^\gamma+o(1))\log\log N$. For $m>N$, $\varphi(m)\ge\sqrt{m/2}$ already exceeds the claimed scale. To attain the constant, take the product of all primes up to $(\log N)/4$. Then $m=N^{1/4+o(1)}$ is coprime to the balanced factors, $W/h\to\infty$ so the outer ceiling is negligible, and Mertens' theorem gives the matching density. The constant is for interval counts. Each actual count still takes arithmetic and memory. [Mertens products and totient estimates, Rosser and Schoenfeld](https://doi.org/10.1215/ijm/1255631807)

## How far can adaptive collinearity extend the intervals?

The same product can permit wider intervals than the uniform guarantee. Even so, a full sweep that visits every unit class and ends its cells only on emptiness, a single column or collinearity requires **more than $2^{504}$ terminal cells at 2,048 bits**, for every coprime wheel. The intervals can depend on the entire input and can differ between classes. The bound applies when the cells cover the geometric band for every visited class, as in the implemented line search. Other exclusion rules and stopping on an early factor fall outside it.

The gap between the upper and lower lines in a cell $[A,B]$ is exactly $NH(x-A)/(A^2 B)$, where $H=B-A$. On its last half the gap is at least $H^2/(2\sqrt N)$ since $A,B\le\sqrt N$. If $H\ge2mN^{1/4}$ that gap is at least $2m^2$. The last half is at least $2m$ wide at this input size, so it contains two distinct integer columns in the required residue class modulo $m$. At each column the allowed heights form a progression of step $m^2$. A closed interval of length $2m^2$ contains at least two points of any such progression. Two points in one column and one in the other are noncollinear. Thus the algorithm must subdivide this cell, irrespective of where the factors actually lie. [Geometric lemmas](../PrimeFactors/QuotientSearch.lean)

A terminal cell therefore covers fewer than $2mN^{1/4}+1\le3mN^{1/4}$ integer columns. Summing their lengths over the full band and all classes gives at least $N^{1/4}\varphi(m)/(12m)$ cells. For $m\le2^{1366}$ the finite totient bound above makes this greater than $N^{1/4}/156>2^{504}$ (since $156^4<2^{31}$). For larger $m$ one terminal cell per visited class already suffices. This estimate makes no assumption about how primes or points are distributed inside a cell. It leaves open whether another exclusion rule can discard whole classes at once.

## Measurements and a second exclusion test

Run `python3 experiments/quotient_search.py 1900014700027 --wheel 210`. The public band contains 403,727 integers. Every row completes the band, including work after finding the pair.

| Wheel | Integer width | Cells | Enclosed points | Euclidean steps for counts | Cached moment states evaluated | Quadratic solves |
|---:|---:|---:|---:|---:|---:|---:|
| 1 | 79 | 5,111 | 1,534 | 43,953 | 112,890 | 114 |
| 6 | 473 | 1,708 | 526 | 10,044 | 27,478 | 41 |
| 30 | 2,361 | 1,368 | 426 | 15,471 | 41,048 | 37 |
| 210 | 16,526 | 1,200 | 399 | 11,061 | 30,664 | 34 |

Each moment state includes fixed-degree binomial arithmetic. At this scale the modulus-210 Python run took about 0.06 seconds, compared with about 0.008 seconds for a complete odd trial sweep. The timing and the cell count describe different costs. [Existing checked prime pair](../benchmarks/modular-hyperbola.json) · [Wheel and adaptive fixtures](../benchmarks/quotient-search.json)

For the generic product $140188063=10007\cdot14009$, deliberately wider 24-integer cells and $m=1$ start with 154 enclosed points in 145 cells. Bisection on every nonempty strip used 443 counts. Testing collinearity first used 147 counts, 8,128 moment states and only one bisection. Eight above-threshold cells with at least three points ended by the observed line. The unbalanced control 51 has no factor in the searched band.

A separate option, `--method errors`, examines $e=xy-N$. If one of $C$ errors vanishes then $(\sum e)^2\le(C-1)\sum e^2$. A strict violation discards even an occupied strip. At small occupancy the power sums determine the complete monic polynomial of the errors by Newton's identities. Its constant term decides whether a zero occurs. If it occurs once, divide the polynomial by its variable to get $P$; then the factor coordinate is $\sum xP(e)/P(0)$. The code bisects when more than one zero remains. On the same width-24 example this version excluded 97 sparse strips and two more by the strict inequality, using 159 counts and 16,136 moment states. The rank test performed less work on this input. [Lean zero-error bounds and isolation](../PrimeFactors/QuotientSearch.lean)

Lean checks the strip bounds, sheared determinant bound, wheel lift, covariance implication, quadratic equation, and finite error-moment identities. The Euclidean recurrence, schedule and work analysis above are paper arguments and the Python implementation has bounded direct checks. Reproduce them with `python3 experiments/quotient_search.py --self-test`.
