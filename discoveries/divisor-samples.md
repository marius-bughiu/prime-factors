# A factor in constant-precision Salié sums

For $N=pq$ with two distinct odd primes, a classical Salié sum computable from $N$ has a four-term evaluation. Two terms are public. The other two give the cosine of a nontrivial square root of one modulo $N$. We show that $O(\log N)$ suitably chosen frequencies, each evaluated to constant absolute error after normalization, suffice to recover the root and factor $N$. Factoring also lets us compute the observations in polynomial bit time. A cheap independent evaluator would therefore give a factoring algorithm. The direct summation and elementary sampling methods examined below take substantial work. This result is unconditional and requires no balance assumption. [Salié evaluation, Lemma 4.14](https://doi.org/10.1007/s40687-025-00544-4) · [Lean identities](../PrimeFactors/DivisorSample.lean)

## Which root enters the answer?

Write $e_N(u)=\exp(2\pi i u/N)$, $\chi(x)=(x/N)$ for the Jacobi symbol, and $\varepsilon_N=1$ if $N=1\bmod4$ and $i$ otherwise. For a unit frequency $t$ set $A=t/2\bmod N$. The observed number is

$$
 F(t)=\frac{1}{\varepsilon_N\chi(A)\sqrt N}
 \sum_{x\bmod N,\ (x,N)=1}\chi(x)e_N\big(A(x+x^{-1})\big).
$$

Every summand uses only public arithmetic. Salié's evaluation expresses the normalized sum as $\sum_{v^2=A^2\bmod N}e_N(2v)$. Substituting $v=Aw$ makes the exponents $tw$ with $w^2=1$. The four CRT sign pairs give $1,-1,h,-h$, where $h$ has signs $(1,-1)$ at $(p,q)$. In particular

$$
 F(t)=2\cos(2\pi t/N)+2\cos(2\pi th/N).
$$

The right-hand sum is real. Either representative of the hidden sign pair splits the product by taking gcds with $h-1$ and $h+1$. In the earlier principal-character transform all unit frequencies were equal to one. Here the twist by the inverse inside the exponential retains information even at unit frequencies. [CRT and gcd proofs](../PrimeFactors/DivisorSample.lean) · [Earlier Ramanujan-sum calculation](reading-the-boundary.md)

There is a short way to see why a quadratic Gauss sum appears. For fixed unit $b$, Fourier-transform $\sum_{v^2=4ab} e_N(v)$ in $a$ against $e_N(-ay)$. Each $v$ occurs once, leaving $\sum_v e_N(v-yv^2/(4b))$. A nonunit $y$ gives zero by translation by $N/\gcd(y,N)$. For unit $y$, completing the square and evaluating the quadratic Gauss sum gives $\varepsilon_N\sqrt N\,\chi(-y/(4b))e_N(b/y)$. Fourier inversion gives the Salié formula. Lean verifies the finite change of summation and the four-root collapse; this argument uses the classical Gauss-sum evaluation. [Fourier lemma](../PrimeFactors/DivisorSample.lean) · [Published evaluation with its coprimality hypotheses](https://doi.org/10.1007/s40687-025-00544-4)

## Recovering the integer with bounded errors

Let $J=\lceil\log_2 N\rceil$. Suppose each request for $F(t)$ gives enough absolute accuracy to approximate $c_t=\cos(2\pi th/N)$ within $\eta=1/1000$, after subtracting the public cosine and dividing by two. For example, rounding the real $F(t)$ to the nearest multiple of $1/256$ contributes at most $1/1024$ to the error in $c_t$. The public cosine can be calculated to absorb the remaining rounding allowance. No independence between errors is required. Reduce requested frequencies modulo $N$. A proper nonunit gcd already supplies a factor. At $t=0$ the needed cosine is one.

1. Request $c_t$ at $t=2^j$, $0\le j\le J$. Pick the frequency $a$ minimizing the absolute measured cosine. To see that its sine is bounded away from zero, consider the distance of $2^j h/N$ from an integer in turns. Some distance lies in $[1/8,3/8]$. If the initial distance exceeds $3/8$, one doubling makes it at most $1/4$. A distance below $1/8$ doubles at each subsequent step until it reaches $[1/8,1/4]$. Nonzero distances are at least $1/N$ since $N$ is odd and $h$ is a unit. The chosen true cosine consequently has magnitude at most $1/\sqrt2+2\eta$. Both its true and estimated sine magnitudes exceed $1/2$.
2. Choose the orientation of $h$ for which the sine at $a$ is positive. For each of the same dyadic $t$, request the cosine at $t+a$. If tildes denote the cosine estimates, estimate the signed sine at $t$ by
   $$
     \frac{\widetilde c_t\widetilde c_a-\widetilde c_{t+a}}
          {\sqrt{1-\widetilde c_a^2}}.
   $$
   The numerator differs from its true value by less than $4\eta$. The error in the denominator is at most $3\eta$ by taking a difference of squares. As the true sine at $t$ has magnitude at most one, division by the estimated denominator gives sine error at most $14\eta$. The resulting cosine–sine pair is within $15\eta$ of the true unit vector. Normalizing it increases that bound to at most $30\eta$. A chord for a circular separation of $d\le1/2$ turns has length at least $4d$, so the recovered phase has circular error below $\delta=1/32$ turns, with room for numerical rounding.
3. Starting with the measured phase at $t=1$, successively choose the lift of the measured phase at $2^j$, divided by $2^j$, that is closest to the preceding estimate. The correct lift improves the error to at most $\delta/2^j$. Indeed, after scaling by $2^j$ the previous error is at most $2\delta$ and the new measurement error is at most $\delta$, so $3\delta<1/2$ guarantees a unique nearest lift. At $j=J$, round $N$ times the estimate and reduce modulo $N$. Its distance from the true signed root, modulo $N$, is less than $1/2$.

There are at most $2(J+1)$ requests and polynomial bit overhead. The second round depends only on the anchor chosen in the first. Substituting every pair of initial frequencies for the adaptive choice gives a nonadaptive $O((\log N)^2)$ version. Conversely, once the primes are known, CRT supplies $h$ and two ordinary cosines evaluate any normalized sample to the stated accuracy. The reduction measures the cost of obtaining samples separately from the cost of decoding them.

Randomization also gives a nonadaptive version with linear query count. Choose an anchor uniformly in $\mathbb Z/N\mathbb Z$ and request its frequency, the dyadic frequencies, and all their translates by the anchor in one round. Accept an anchor with estimated cosine of magnitude at most $3/4$. Both sine magnitudes still exceed $1/2$, so the same error proof applies. Multiplication by $h$ permutes the residues. The two intervals $[1/8,3/8]$ and $[5/8,7/8]$ contain at least $N/2-2$ residue phases between them. Every such anchor either yields a proper gcd or passes the cosine test. For $N\ge15$ the success probability is at least $1/3$. Preselecting $r$ independent anchors gives failure probability at most $(2/3)^r$ with $O(r\log N)$ requests and polynomial decoding work. The probability concerns only the chosen anchors and allows adversarial observation errors within the stated bound.

## Exact signs determine adjacent binary digits

A fixed list of only $J=\lceil\log_2N\rceil$ comparisons also suffices if each sign is reliable. Write the binary expansion $h/N=0.b_1 b_2\ldots$. The sign of $F(2^j)-2\cos(2\pi 2^j/N)$ is negative exactly when the fractional part of $2^jh/N$ belongs to the middle two quarters. Their two-bit prefixes are $01$ and $10$, so the comparison gives $b_{j+1}\mathbin{\mathrm{XOR}}b_{j+2}$. Quarter boundaries never occur for a unit root and odd $N$. Fix $b_1=0$, which chooses the smaller of $h$ and $N-h$ because complementing every bit preserves these comparisons. The $J$ adjacent comparisons successively determine $J+1$ bits. Their dyadic cell has width $2^{-J-1}<1/N$. Multiplying its endpoints by $N$ locates the unique integer root between them. [Lean adjacent-digit identity](../PrimeFactors/DivisorSample.lean)

This one-bit answer model requires an exact threshold decision for each frequency. The grid of possible phases is at least $1/(4N)$ turns from a quarter boundary, so the absolute comparison margin is at least $2\sin(\pi/(2N))$. Computing the comparison with $O(\log N)$ fractional bits suffices uniformly. The calibrated version above has a fixed absolute accuracy independent of $N$.

## Stopping at square-root width

An integer interval of length $O(\sqrt N)$ containing either mixed root suffices for polynomial-time postprocessing. From its integer center $c$, the offset $u=h-c$ is a small root of the monic quadratic $(u+c)^2-1$ modulo the full $N$. May's Theorem 7 with $\beta=1$ and degree two includes $|u|\le C\sqrt N$ for fixed $C$. Equivalently, cover the interval by constantly many blocks with integer centers and radius at most $\lfloor\sqrt N\rfloor$. Test the polynomial's returned roots modulo $N$ and take gcds for the nontrivial ones. The same argument applies to a wrapped interval by splitting at $0$. The lattice result is an external theorem. [May, Theorem 7](https://digital.ub.uni-paderborn.de/hsmig/download/pdf/3235#page=38) · [Coppersmith's original theorem](https://doi.org/10.1007/s001459900030)

For the fixed dyadic comparisons put $K=\lfloor\log_2\sqrt N\rfloor-1$ and use $t=2^j$ for $0\le j<K$. The decoded $K+1$ bits locate the root in a cell of length $N/2^{K+1}<2\sqrt N$. Precision improves too. Let $r$ be the distance from $4th$ to the nearest odd multiple of $N$. Then $r$ is an odd positive integer at most $N$, and $r^2\equiv(4t)^2\pmod N$. For these frequencies $4t<\sqrt N$, since $N$ is a nonsquare. The distinct squares $r^2$ and $(4t)^2$ differ by a nonzero multiple of $N$, and $(4t)^2<N$. Thus $r^2\ge N+(4t)^2$. The comparison margin is
$$
 \big|F(t)-2\cos(2\pi t/N)\big|
   =2\sin\!\left(\frac{\pi r}{2N}\right)\ge\frac{2r}{N}\ge\frac2{\sqrt N}.
$$
Consequently $\tfrac12\log_2 N+O(1)$ fractional bits per comparison suffice. [Lean square-separation proof](../PrimeFactors/DivisorSample.lean)

For the constant-accuracy decoder, take $B=\lceil\log_2\sqrt N\rceil$. A well-conditioned anchor already occurs at some $j\le B$. Indeed, the integer $u=\min(h,N-h)$ is greater than one and $u^2\equiv1\pmod N$, giving $u^2\ge N+1$. If the initial phase lies beyond $3/8$ turns from the nearest integer, one doubling gives distance $|2h-N|/N$. The numerator is odd and its square is congruent to $4$ modulo $N$. The same separation gives $(2h-N)^2\ge N+4$. Thus a starting distance below $1/8$, or one still below $1/8$ after that doubling, is already at least $1/\sqrt N$. Doubling reaches the good annulus by $j\le B$. Using these same $B+1$ scales in the decoding round gives a signed-root interval of radius at most $\delta N/2^B\le\delta\sqrt N$.

For a 2048-bit product the original full-root bounds are 4,098 constant-accuracy queries or 2,048 nonadaptive sign comparisons. The quadratic finish reduces the respective bounds to **2,050 constant-accuracy queries** or **1,022 nonadaptive comparisons**. Approximating each side of the latter comparisons to absolute error at most $2^{-1025}$ suffices, compared with $2^{-2049}$ for the full-resolution bound. These counts exclude the lattice postprocessing and the work to obtain each sum. The executable example below uses the original full-root decoder. A separate construction evaluates an individual coarse sample by a Boolean count over folded roots. [Counting Salié phases](counting-salie-phases.md)

## A single higher-precision sample

At the fixed frequency $t=1$, fold $h/N$ into $[0,1/2]$. For $z,w$ in this interval put $d=|z-w|$. Since $d\le z+w\le 1-d$,
$$
 |\cos(2\pi z)-\cos(2\pi w)|\ge 2\sin^2(\pi d)\ge8d^2 .
$$
Consequently a hidden-cosine estimate with absolute error $1/N$ yields a folded-root interval of length $O(\sqrt N)$ by clipping the range to $[-1,1]$ and inverting cosine. The same quadratic finish recovers a mixed root. The phase inverse can be evaluated by bisection with polynomial bit overhead.

A uniformly random frequency reduces the required precision to $O(1/\sqrt N)$ with constant success probability. A proper nonunit gcd already splits $N$; discard frequency zero. For a unit frequency let $v$ be the smaller representative of $\pm th\pmod N$. Compute the hidden cosine to error at most $1/(100\sqrt N)$ and accept if its measured magnitude is at most $3/4$. The true value and the estimate then lie in $[-4/5,4/5]$, where the inverse derivative for phase measured in turns has absolute value at most $5/(6\pi)$. Inverting therefore locates $v$ to $O(\sqrt N)$. Apply May's theorem to $(u+c)^2-t^2$ modulo $N$ around the resulting center $c$. The true $v$ satisfies this equation and differs from $\pm t$ modulo $N$. Multiply each candidate by $t^{-1}$, check its square modulo $N$ and take gcds. As in the random anchor argument, each trial succeeds with probability at least $1/3$. Repetition gives a verified split in at most three trials in expectation. One can also select a good dyadic anchor deterministically from the first round of coarse samples and refine that frequency once. This trades query count for the precision of an individual sum. The constant-error Boolean evaluator requires additional output information to implement this finer observation.

## What individual summands cost

A direct evaluation takes $\varphi(N)$ unit terms after selecting those units. Consider instead sampling $x$ uniformly in $\mathbb Z/N\mathbb Z$, taking the summand as zero on nonunits. If $Y$ is the resulting term multiplied by $\sqrt N/(\varepsilon_N\chi(A))$, its expectation is $F(t)$ and $\mathbb E|Y|^2=\varphi(N)$. Averaging $m$ independent samples has mean squared complex error $(\varphi(N)-|F(t)|^2)/m$. The four-term formula gives $|F(t)|\le4$. Lean checks the finite squared-error expansion underlying this calculation. [Finite variance identity](../PrimeFactors/DivisorSample.lean)

Using only the real part still has large variance. Since the square of the Jacobi weight is one on the units, $\mathbb E Y^2=\chi(-1)\operatorname{Kl}_N(2A,2A)$, the ordinary Kloosterman sum. The Weil bound gives magnitude at most $4\sqrt N$ here. Hence
$$
 \operatorname{Var}(\operatorname{Re}Y)
   =\tfrac12\big(\varphi(N)+\operatorname{Re}\mathbb EY^2\big)-F(t)^2
   =\tfrac12\varphi(N)+O(\sqrt N).
$$
Uniform independent term averaging therefore requires $\Theta(N)$ samples for fixed root-mean-square accuracy. This estimate describes that estimator. Structured summation or a different observation might have a different cost. On balanced inputs a random $x$ itself has a proper gcd with $N$ with probability $(p+q-2)/N$, so random gcds would already give a split in order $\sqrt N$ trials. [Kloosterman bound, Lemma 4.13](https://doi.org/10.1007/s40687-025-00544-4)

## Bounded calculation

For $667$, direct sums at frequencies $1,2,4,8$ gave normalized values that rounded to $221,331,127,577$ in units of $1/256$. The full procedure chose anchor 8, used 21 distinct sums, and recovered root 436. It gives $\gcd(435,667)=29$ and $\gcd(437,667)=23$. The 616 unit terms per sum amount to 12,936 summands with one real trigonometric evaluation each, in addition to testing the 666 nonzero residues and computing their modular inverses once for the units. A gcd encountered during setup could already split this example. The counts describe the full calculation with that shortcut suppressed.

The Python evaluator caps the number of summands and each complete sum uses the full unit table. It accepts at most $N=65{,}535$ for its floating-point demonstration and checks a recovered root and divisor with integer arithmetic. With a 6,776-term cap, the same input reaches the anchor and remains unresolved. An independent fixture uses the first two distinct primes among the draws from Python's `Random(20261124).randrange(33, 64, 2)`. Their product 1,763 yields root 1,721 in 38,640 summands. Run `python3 -m experiments.divisor_samples 667 --max-terms 12936` to reproduce the first split. [Bounded evaluator](../experiments/divisor_samples.py) · [Inputs and controls](../benchmarks/divisor-samples.json)

## Rounding a square from the fixed sample

One normalized reading $F(1)$ rounded to $n$ fractional bits suffices for every $n$-bit product $N=pq$ of distinct odd primes. Once the reading is supplied, the decoder uses at most two rounded integers, integer square roots and gcds. The earlier fixed-sample argument above decoded an interval of length $O(\sqrt N)$ and invoked May's small-root theorem. Here the integer determined by the observation is a quotient. The cost of producing $F(1)$ from a large product remains open. [Earlier lattice finish](#a-single-higher-precision-sample) · [May, Theorem 7](https://digital.ub.uni-paderborn.de/hsmig/download/pdf/3235#page=38)

Let $H=\min(h,N-h)$ for the mixed root represented in $[0,N)$ and $c=\cos(2\pi H/N)$. From the reported value $W$ compute $d=W/2-\cos(2\pi/N)$. Rounding $F(1)$ introduces at most $2^{-n-1}<1/(2N)$ error. An additional absolute error of at most $1/(4N)$ in the public cosine still gives $|d-c|\le 1/(2N)$. No sign decision is needed. Try the following two signed estimates:

| $b$ | Signed estimate | True phase $x$ in the correct branch | Integer $a=bNx$ |
|---:|---:|---:|---:|
| 1 | $d$ | $H/N$ if $H/N\le 1/4$ | $H$ |
| 2 | $-d$ | $1/2-H/N$ if $H/N>1/4$ | $N-2H$ |

For each signed estimate clip it to $[0,1]$ and set $y=\arccos(\mathrm{clipped})/(2\pi)$. For $0\le y\le x\le1/4$, the cosine difference is $2\sin(\pi(x+y))\sin(\pi(x-y))$. Both arguments are on the first quarter of a turn, where $\sin(\pi u)\ge 2u$ for $0\le u\le1/2$. Interchanging $x,y$ if necessary yields
$$
 |\cos(2\pi x)-\cos(2\pi y)|\ge 8|x^2-y^2|.
$$
In the correct branch $a^2\equiv b^2\pmod N$, so $k=(a^2-b^2)/N$ is an integer. Clipping cannot increase the error, and therefore
$$
 \left|b^2Ny^2-b^2/N-k\right|\le \frac{b^2N}{8}\cdot\frac1{2N}\le\frac14.
$$
Evaluate this score to additional error strictly less than $1/4$ and round. For example, an enclosure for $y$ of width at most $1/(16N)$ gives a score interval of width at most $1/8$. It takes polynomial bit work to invert the monotone cosine to this accuracy. Bisection can stop at a midpoint whose cosine is within $O(1/N^2)$ of the target, since $|x^2-y^2|\ge |x-y|^2$ on this interval. Test whether $Nk+b^2$ is a nonnegative square. For its integer square root $a'$, check $h'=a'b^{-1}\bmod N$, its square modulo $N$, and a proper gcd with $h'\pm1$. The correct branch returns $h'\equiv\pm h\pmod N$. [Lean clipping, conditioning, rounding and two-branch theorem](../PrimeFactors/FoldedSquare.lean)

For $N=667$, the direct sum of 616 unit terms certifies the ten-bit reading $W=883/1024$. Subtracting the public cosine and using the second branch gives $629/4096<y<630/4096$ by interval evaluations of cosine at both endpoints. The resulting score lies between $62.91$ and $63.12$, so $k=63$. Then $667\cdot63+4=205^2$, $205\cdot2^{-1}\equiv436\pmod{667}$, and the two gcds are 29 and 23. The first branch gives $k=42$ and a nonsquare. The calculation uses one public sum and checks the factors by multiplication. The direct evaluator uses gcds for unit membership and would encounter the divisors during that scan. Running `python3 experiments/folded_square.py --direct 667 --max-terms 616` reproduces it. [Product-only benchmarks and capped run](../benchmarks/folded-square.json) [Directed-rounding sum evaluator](../experiments/salie_seed.py) · [Cosine enclosures](../experiments/salie_reference.py) · [Kernel-checked integer steps](../PrimeFactors/FoldedSquare.lean)

### Full-width decoder test

On the already certified 2,048-bit fixture, a generator used its two known primes to calculate the single rounded value. A fresh process received only the product and the signed integer encoding that value. It recovered both primes using the reflected branch. The decoder checked the rounding decisions over the entire range consistent with the transmitted integer. This was a test of recovery from one supplied value. The small direct runs on 77, 667 and 1,763 instead computed the value from each product alone. [Bounded reference implementation](../experiments/folded_square.py) · [Direct-sum and process-isolated tests](../tests/test_folded_square.py)

```sh
python3 experiments/folded_square.py --emit | python3 experiments/folded_square.py --decode
```
