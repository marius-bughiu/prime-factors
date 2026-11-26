# Recovering a factor sum from repeated matches

For **793,157**, a power of base 79 matched at two candidate positions for each hidden prime. The positions were **36 and 80** modulo one prime and **16 and 36** modulo the other. Position 36 came first in one list and last in the other. The earlier search exhausted its 48 quotient tests. The new search recovered 36 as a root of a quadratic computed from the product alone. The possible sums started at 1,782, so the sum was 1,818. Subtracting four times the product from $1{,}818^2$ gave $364^2$, hence **727 × 1,091**. The two lists explain the result after the fact. The search used seven positions admitted by the public residue test and received neither list. [Earlier search](../benchmarks/geometric-wheel-readout.json) · [New search and factor certificates](https://marius-bughiu.github.io/prime-factors/#geometric-precision-mixed-rank)

**More precision changed the outcome on 30,607.** Each prime had three matches. Using the product as the polynomial modulus, the four-row lattice search exhausted its budget. Using the product squared, the same four-row budget gave position 18, sum 368 and **127 × 241**. Lean separately proves that 18 is the only root of the measured cubic in the entire interval from 0 to 21. [Cubic and proof of uniqueness](../PrimeFactors/GeometricSmallRoot.lean) · [Matched runs](../benchmarks/geometric-precision-readout.json)

| Product | Matches per prime | Modulus for the polynomial | Positions read | Lattice rows | Outcome |
| ---: | ---: | ---: | ---: | ---: | --- |
| 793,157 | 2 | $N$ | 7 | 3 | Index 36, $727\times1{,}091$ |
| 30,607 | 3 | $N$ | 22 | 4 | No sufficiently short row found |
| 30,607 | 3 | $N^2$ | 22 | 4 | Index 18, $127\times241$ |
| 45,803 | 4 | $N^2$ | 25 | 5 | Index 15, $163\times281$ |
| 81,217 | 5 | $N^3$ | 35 | 6 | Index 8, $241\times337$ |
| 81,217 | 5 | $N^5$ | 35 | 6 | Same index and factors at the sufficient one-reduction precision |

The table gives distinct positions per pass. Each successful polynomial run made one pass to count the matches, then evaluated $r+1$ directions together in a second pass. On the two 2,048-bit controls, the mod-32 filter still left about $2^{1017.77}$ and $2^{1017.54}$ positions. The 128-position cap stopped both runs before the first probe, leaving both products unfactored. [Public inputs, budgets and outcomes](../benchmarks/geometric-precision-readout.json) · [Bounded evaluator](../experiments/geometric_precision_readout.py)

## From repeated powers to a polynomial

Suppose $N=pq$ for distinct odd primes $p<q\le2p$. Their sum lies between $L=\lceil2\sqrt N\rceil$ and $U=\lfloor\sqrt{9N/2}\rfloor$. Index $i$ stands for the sum $L+i$. Let $W=U-L$, take a base $g$ coprime to $N$, and choose any set $I\subseteq\{0,\ldots,W\}$ of indices. To recover the true sum, the chosen set must retain its index $j=p+q-L$. The full interval and the exact mod-32 sum filter both do. [Sum filter and coverage](../PrimeFactors/GeometricSumLanes.lean)

Put $E=N+1-L$. A local match modulo $p$ means $g^i=g^E\pmod p$. The true index matches modulo both primes because $E-j=(p-1)(q-1)$. A single public reading determines how many matches matter. Set $G_0=g^N$ and multiply the terms $G_0^E(1-N)-(G_0(1+N))^i$ over $I$, modulo $N^{R+1}$ for a chosen cap $R$. If $i+1<p$ throughout $I$, every local match contributes exactly one factor of that prime to the unrestricted product. Divide the sample by $N$ until the first nonzero base-$N$ digit. Its position is the smaller match count. The gcd of the digit with $N$ gives the prime with more matches, or 1 if the counts agree. A zero sample means both counts exceed $R$. On 33,127 with base 13 the first nonzero digit immediately gave the factor 157. [Automatic multiplicity theorem](../PrimeFactors/GeometricMultiplicityProbe.lean)

When the two counts agree at $r\ge1$, choose a precision $k\ge1$, put $t=N^k$, $G=g^{N^{2k-1}}$ and $Y=G^E$. For each direction $z=0,1,\ldots,r$, compute

$$
V_z=\prod_{i\in I}\bigl(Y(1+zt)-(G(1+t))^i\bigr)\pmod{t^{r+1}}.
$$

The exponent in $G$ lifts an original match modulo $p$ to agreement modulo $p^{2k}$, and likewise at $q$. This compensates for the larger step $t$. Each $V_z$ is divisible by $t^r$. The resulting digits $V_z/t^r\bmod t$ are values of a degree-$r$ polynomial whose leading coefficient is invertible. Interpolate using the $r+1$ directions and divide by that coefficient to make the polynomial monic. Consecutive directions determine it uniquely when $\gcd(r!,N)=1$. The implementation checks the small denominators for a factor before interpolating. [Power lift](../PrimeFactors/GeometricPrincipalLift.lean) · [Digit, interpolation and monic polynomial proofs](../PrimeFactors/GeometricPrecisionReadout.lean)

Modulo $p^k$ the monic polynomial is the product of $z-i$ over the $p$-side matches. Modulo $q^k$ it is the corresponding product for the $q$-side matches. Lean proves that, for $W<p$, its integer roots modulo $N^k$ in $[0,W]$ are exactly the indices that match on both sides. This holds for disconnected sets $I$ and for different orderings of the matches. Multiple common indices can survive at every precision. Each candidate sum $S=L+i$ therefore gets the integer square test on $S^2-4N$. [Exact in-range root theorem](../PrimeFactors/GeometricPrecisionReadout.lean)

## Finding the roots and checking the answer

The public width satisfies $W^2<N$. Taking $k=\lceil r/2\rceil$ gives $W^r<N^k$, placing every possible index within the classical univariate small-root bound for the monic polynomial modulo $N^k$. Coppersmith gives a polynomial-time root-finding method once that polynomial is available. Lean checks the width and exponent inequalities. Producing its coefficients still requires the geometric products above. The bounded implementation visits each retained index and performs one modular product update per direction there. [Width proof](../PrimeFactors/GeometricSmallRoot.lean) · [Coppersmith, *Finding Small Solutions to Small Degree Polynomials*](https://cr.yp.to/bib/2001/coppersmith.pdf)

There is also a sufficient precision for a single reduction with exactly $r+1$ lattice rows. Center the interval, let $B=\max(1,\lceil W/2\rceil)$ and $M=N^k$. Use the shifted monic polynomial and the $r$ rows $M,MX,\ldots,MX^{r-1}$, scaling column $i$ by $B^i$. The determinant is $M^r B^{r(r+1)/2}$. Combining the classical LLL first-vector estimate with the norm bound below gives the public test

$$
(r+1)^{2(r+1)}\,2^{r(r+1)}\,B^{2r(r+1)} < M^4.
$$

When this holds, a first vector satisfying that LLL estimate has absolute column sum below $M$. Lean verifies the determinant and the implication from the estimate. The code can choose the least positive $k$ satisfying the strict inequality. Its value is 2 for the cubic and 5 for the quintic. The quintic also succeeded at $k=3$ by directly checking the row it found. [Checked precision bound](../PrimeFactors/GeometricLatticePrecision.lean) · [Lenstra, Lenstra and Lovász, Proposition 1.6, inequality (1.9)](https://pub.math.leidenuniv.nl/~lenstrahw/PUBLICATIONS/1982f/art.pdf)

For an actual row, the program checks its signed integer combination of the input rows. At every modular root this combination evaluates to a multiple of $M$ for the one-reduction cases above. The absolute column sum bounds that evaluation over the centered interval. A bound strictly below $M$ forces the value to equal zero over the integers. For the cubic, in the centered coordinate $x=i-10$, the signed row was $929296+485766x-58081x^2-2145x^3$. Its checked bound was **16,155,518**, below **936,788,449**. The program isolates the integer roots, tests their candidate sums, and submits each recovered split to Lean for product and primality verification. [Integer-row and evaluation bounds](../PrimeFactors/GeometricSmallRoot.lean) · [Implementation](../experiments/geometric_precision_readout.py)
