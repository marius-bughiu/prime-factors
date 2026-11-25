# Can a few frequencies tell us which interval contains a factor?

For $N=34,387$, consider all 34,387 cyclic intervals of length 13. Exactly 29,512 of them contain only numbers coprime to $N$. That single count determines the factor sum, 388, and hence the two primes, **137 and 251**. Counting directly took 34,387 gcd tests and encountered the factor 137 during the scan. We tested the conjecture that the lowest $\lfloor\sqrt N\rfloor$ frequencies capture at least half the variation between these intervals. Here they capture **less than 4%**. [Checked count, frequency bound and example](../PrimeFactors/DivisorWindowSignal.lean)

## An interval count with a margin for error

Suppose $N=pq$ for distinct odd primes $p<q$, and fix $1\le H\le p$. A window ending at $a$ comprises $a,a-1,\ldots,a-H+1$ modulo $N$. There are $p-H$ possible residues of $a\bmod p$ for which the window misses all multiples of $p$, and $q-H$ such residues modulo $q$. The Chinese remainder theorem makes these choices independent. The total number $Z_H$ of windows missing both primes satisfies
$$
Z_H=(p-H)(q-H)=N-H(p+q)+H^2.
$$
Thus an estimate of $Z_H$ with absolute error strictly below $H$ determines $p+q$ by rounding $(N+H^2-Z_H)/H$ to the nearest even integer. Consecutive even sums predict counts $2H$ apart. Knowing $Z_H$ exactly is equivalent to knowing $\varphi(N)$ through $Z_H=H\varphi(N)-(H-1)(N-H)$. To locate the smaller factor one then takes the smaller root of $x^2-(p+q)x+N=0$. The case $H=1$ is the familiar totient readout. [Empty-window and robust uniqueness proofs](../PrimeFactors/DivisorWindowSignal.lean) · [Previous totient-count route](counting-modular-inverses.md)

The product alone also defines a yes-or-no test for one specified window. Multiply its entries modulo $N$ and take their gcd with $N$. A gcd of 1 certifies emptiness. A proper gcd gives a factor. A gcd of $N$ certifies a nonempty window. Splitting can isolate a proper gcd when separate entries meet separate primes. The singleton residue 0 has gcd $N$ by itself. Direct evaluation uses $H$ modular multiplications, and product trees can share work across windows. For a balanced input with $q\le 2p$, the interval $[\sqrt{N/2},\sqrt N]$ contains $p$ and lies below both $2p$ and $q$, so $p$ is its only nonunit. Both the total count and the individual window test leave the cost of obtaining the desired information to account for. [Earlier block-product algorithms and costs](batch-intervals.md)

## How much information resides at low frequencies?

Count the number of marked multiples inside each window, counting 0 twice because both primes divide it. Each individual mark is computed from $N$ alone as $\mathbf1_{\gcd(x,N)>1}+\mathbf1_{x=0\bmod N}$. This equals $\mathbf1_{p\mid x}+\mathbf1_{q\mid x}$. Denote its sum in the window ending at $a$ by $W(a)$. Over all translations the two prime contributions are independent Bernoulli variables with means $H/p$ and $H/q$. Consequently
$$
V=\operatorname{Var}(W)=\frac Hp\!\left(1-\frac Hp\right)+\frac Hq\!\left(1-\frac Hq\right).
$$
Double-counting 0 removes a known impulse in the transform and preserves the set of empty windows. Lean proves the first two moments of this public signal. [Moment identities](../PrimeFactors/DivisorWindowSignal.lean)

Use the normalized Fourier transform $\widehat W(k)=N^{-1}\sum_a W(a)e^{-2\pi iak/N}$. For $0<k<N$, its exact value is
$$
\widehat W(k)=\frac{p\,\mathbf1_{p\mid k}+q\,\mathbf1_{q\mid k}}{N}
                  \sum_{h=0}^{H-1}e^{-2\pi ihk/N}.
$$
This follows from the principal-character transform and translation of a finite sum. In particular, all nonconstant modes below $p$ vanish. An individual nonzero mode already gives a factor as $\gcd(k,N)$, even without evaluating its coefficient. Getting the zero-frequency coefficient accurately would also supply $p+q$, since $\widehat W(0)=H(p+q)/N$. The new estimate concerns the variation after subtracting this constant. [Ramanujan's original trigonometric sums](https://ramanujan.sirinudi.org/Volumes/published/ram21.pdf) · [Existing principal transform](../PrimeFactors/FourierAccess.lean) · [Translated transform and gcd theorem](../PrimeFactors/DivisorWindowSignal.lean)

Let $2H\le p\le q$ and $0<K<N/2$. The fraction of centered energy at frequencies $1\le |k|\le K$ is at most
$$
\frac{\sum_{1\le |k|\le K}|\widehat W(k)|^2}{V}\le \frac{4KH}{N}.
$$
Indeed the geometric sum has magnitude at most $H$. There are at most $K/p$ positive multiples of $p$ through $K$ and at most $K/q$ multiples of $q$. Adding both signs gives an energy bound of $(2KH/N)(H/p+H/q)$, while $V\ge(H/p+H/q)/2$. Orthogonality makes the truncated transform the best least-squares approximation supported on those frequencies. Also, each nonconstant coefficient has magnitude at most $H/p$. Even an arbitrary selection of frequencies, including high ones, needs at least $p/(4H)$ individual modes to capture half the variance. [Checked consecutive and sparse bounds](../PrimeFactors/DivisorWindowSignal.lean)

For a 2,048-bit product of two 1,024-bit primes, take $H=2^{512}$. Capturing half the centered energy across all cyclic starts requires **$K\ge2^{1532}$** for the consecutive band, or **at least $2^{509}$ individual frequencies** for any sparse selection. These are a largest frequency and a number of terms, respectively. The bounds apply to recovering the sliding signal over all translations. A method designed for a single balanced interval, a nonlinear use of $N$, or a fast evaluation of the global count remains possible.

## Small product and the RH connection

For $N=34,387$, $H=13$, the three occupancy counts for zero, one and two marks were 29,512, 4,706 and 169. For a comparison entirely inside the balanced interval, the window $[132,144]$ contains 137 and $[145,157]$ is empty. Their truncated signals agree exactly at every cutoff below 137. At $K=185$ the only informative positive frequency is 137. Direct numerical summation gives an energy fraction of approximately 0.0393943. The rigorous upper bound from the geometric-sum inequality is $243997/6139573<1/25$. The proof uses no numerical Fourier evaluations. The following run reproduces the counts and the floating-point diagnostic using only $N$ and $H$.

~~~python
from cmath import exp
from collections import Counter
from math import gcd, isqrt, pi

N, H = 34387, 13
marks = [int(gcd(x, N) > 1) + int(x == 0) for x in range(N)]
windows = [sum(marks[(a-h) % N] for h in range(H)) for a in range(N)]
counts = Counter(windows)
S = (N + H*H - counts[0]) // H
d = isqrt(S*S - 4*N)
print(counts, (S-d)//2, (S+d)//2)
mean = sum(windows) / N
variance = sum((x-mean)**2 for x in windows) / N
band = 0
for k in range(1, isqrt(N) + 1):
    mode = sum((w-mean)*exp(-2j*pi*k*a/N) for a,w in enumerate(windows)) / N
    band += 2*abs(mode)**2
print(band / variance)
~~~

The pinned RH repository states that Dirichlet $L$-functions have no zeros strictly to the right of real part $1/2$, apart from the separately excluded principal pole, and locates their nontrivial zeros on that line. Earlier work here isolated the missing Euler factors in the principal $L$-function and studied what one boundary value could reveal. The present experiment instead asks about a finite sum of its principal-character coefficients over a moving window. The zero-location statements provide neither this finite count with error below $H$ nor a local occupancy oracle. All finite counts and bandwidth bounds above are unconditional. [Pinned definitions](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab/src/Statements.lean) · [Independent verification](https://math.mit.edu/~drew/grh/) · [Earlier boundary-value analysis](reading-the-boundary.md)
