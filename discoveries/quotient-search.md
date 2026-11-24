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
