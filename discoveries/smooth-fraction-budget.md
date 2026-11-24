# How much can changing the shape of a smooth fraction help?

Suppose $N=pq$ is 2,048 bits and $p,q$ are distinct 1,024-bit primes. Draw a unit $x$ uniformly modulo $N$. Even if we can inspect **every** reduced fraction $a/b$ representing $x^2$ with $0<|a|b\le N/2$, the probability that one uses only a prescribed list of at most $2^{40}$ primes is below **$2^{-208}$**. After $2^{48}$ draws the probability is below **$2^{-160}$**. The same bounds hold when arbitrary square factors are allowed free of charge in both numerator and denominator. This counts the first eligible fraction, before collecting enough relations to extract a factor.

The numerator can be nearly as large as $N/2$ when the denominator is one. The search may choose a different balance on every draw, inspect several fractions, or inspect every one. The prime list may depend on $N$ and earlier draws. For an arbitrary list, fix it before seeing the current root. Ordinary cutoffs containing every prime up to $B$ are nested, so even choosing a cutoff after the draw is covered when $\pi(B)\le2^{40}$. Selecting arbitrary primes after inspecting the current fraction can tailor the list to its factors and changes the event.

## Counting all shapes at once

Let $S$ be the allowed set of primes. A positive integer is $S$-smooth if all its prime factors belong to $S$. The integer 1 qualifies as an empty product. For $\sigma>0$ set

$$
Z_S(\sigma)=\prod_{\ell\in S}(1-\ell^{-\sigma})^{-1}.
$$

An ordered positive pair $(u,b)$ with $ub\le N/2$ has weight $(N/(2ub))^\sigma\ge1$. Summing this weight over all ordered $S$-smooth pairs, including pairs above the product limit, gives $(N/2)^\sigma Z_S(\sigma)^2$ by unique factorization and two products of geometric series. This also counts pairs with common factors and repeated representations, giving an upper bound for the reduced fractions. [Lean proof for ordered pairs and arbitrary prime lists](../PrimeFactors/SmoothFractionHyperbola.lean) · [Single-remainder bound](smooth-sample-bound.md)

Each pair allows two signs for its numerator. Each resulting unit residue has four square roots by the Chinese remainder theorem. In a reduced fraction with $a\equiv bx^2\pmod N$, a prime dividing both $b$ and $N$ would also divide $a$, so the denominator must be a unit. Dividing the root count by $\varphi(N)$ yields

$$
P\le \frac{8(N/2)^\sigma}{\varphi(N)} Z_S(\sigma)^2.
$$

Each Euler factor decreases with its prime, so the first $K=2^{40}$ primes maximize $Z_S$ over all allowed lists. Write $Z$ for this maximal product at the chosen $\sigma$. For $0<\sigma<1$, the factor $N^{\sigma-1}$ decreases with $N$. Using $N\ge2^{2047}$ and $\varphi(N)\ge N(1-2^{-1023})^2$ gives the uniform bound

$$
\log_2 P\le 3-2047+2046\sigma+2\log_2 Z+1/1024.
$$

The last term bounds $-2\log_2(1-2^{-1023})$. The choice of an arbitrary permitted fraction after seeing $x$ is already inside the event counted above. For the next draw, condition on the entire past and any independent choice of the next list. If the new unit is uniform under that conditioning, the same upper bound applies. Summing over at most $2^{48}$ opportunities proves the stated probability, including for a search that stops early.

## Allowing arbitrary square factors

Both probability bounds still hold if each of $|a|$ and $b$ may contain an arbitrary square factor at no cost. The remaining requirement is that every prime outside $S$ have even exponent in that coordinate. For $\sigma>1/2$, the corresponding Euler product for one coordinate, with $\ell$ ranging over primes, is

$$
Z_S(\sigma)\prod_{\ell\notin S}(1-\ell^{-2\sigma})^{-1}
=\zeta(2\sigma)\prod_{\ell\in S}(1+\ell^{-\sigma}).
$$

The right side is again largest for the first $K$ primes. Their last prime is at least $K$, so the added natural logarithm per coordinate is at most $2\sum_{n>K}n^{-2\sigma}\le 2K^{1-2\sigma}/(2\sigma-1)$, using $-\ln(1-z)\le2z$ for $0\le z\le1/2$. The program verifies this is below $2^{-26}$ at both exponents. Including both coordinates and converting to bits adds less than $2^{-24}$ to the upper bound for $\log_2 P$, preserving even the rounded probabilities in the table. A search can also keep several rows containing the same unlisted prime to odd exponent, then cancel it by multiplication. The cross-row argument below covers dependencies that use at least one draw exactly once.

## Two explicit numerical certificates

The table reports upper bounds rounded upward. Run `python3 experiments/smooth_fraction_budget.py` to reproduce both rows using integer and rational operations. The loop never constructs a list of a trillion primes. [Standalone certificate program](../experiments/smooth_fraction_budget.py)

| Prime bound | $\sigma$ | Certified upper bound for $2^{64}\ln Z$ | Upper bound for $\log_2 P$ | Probability in $2^{48}$ draws |
|---|---:|---:|---:|---:|
| Dusart's lower bound for the $k$-th prime | $109/128$ | 597140142584509257281 | $-208.299$ | $<2^{-160}$ |
| Binomial coefficients alone, after sieving to 65,536 | $223/256$ | 667550208704054139854 | $-157.324$ | $<2^{-109}$ |

Both calculations sieve the 6,542 primes up to 65,536 exactly. The first treats the remaining prime indices in 256 subdivisions of each interval $[2^j,2^{j+1})$. For a bin starting at index $k$, Dusart's unconditional theorem gives the lower bound $k(\ln k+\ln\ln k-1)$ for every prime in that bin. Replacing each prime by a rounded-down lower bound increases its Euler factor. [Dusart, *The kth prime is greater than k(ln k + ln ln k − 1) for k ≥ 2*, Math. Comp. 68 (1999), 411–415](https://www.ams.org/mcom/1999-68-225/S0025-5718-99-01037-6/S0025-5718-99-01037-6.pdf)

The second calculation has an elementary proof. Every prime in $(2^j,2^{j+1}]$ divides $\binom{2^{j+1}}{2^j}$, which is smaller than $2^{2^{j+1}}$. Since every such prime exceeds $2^j$, the interval contains at most $\lfloor 2^{j+1}/j\rfloor$ primes. Give every available slot the weight of its lower endpoint $2^j$, then fill intervals from smallest to largest up to the capacity $K$. This can only increase the sum of logarithmic Euler factors.

To check the rounding, write $\sigma=c/d$ with $d$ a power of two. At precision $M\cdot 2^{64}$, round the reciprocal of each prime lower bound $L$ upward, take $\log_2 d$ square roots, and raise the result to $c$ by repeated squaring. Every step rounds upward. Rounding up again to precision $M$ gives $z=q/M\ge L^{-\sigma}$. The evaluator uses the first 16 terms of $-\ln(1-z)$ and upper-bounds the remaining terms by $z^{17}/[17(1-z)]$. It uses $M=2^{64}$ for the original table and $2^{128}$ for the larger capacities below. For lower logarithms it writes $x=2^j y$ with $1\le y<2$, uses $t=(y-1)/(y+1)$, and keeps eight positive terms in $2\sum_{k\ge0}t^{2k+1}/(2k+1)$. The same expansion at $t=1/3$ supplies the lower bound for $\ln 2$.

## When primes can cancel between different draws

Take at most $T=2^{48}$ independently uniform unit draws. Each draw is a **source**. A fraction $a/b$ for source $x$ supplies a row with signed integer $ab\equiv(bx)^2\pmod N$. A square dependency selects rows whose signed integers multiply to a square. The following bounds even allow arbitrary exponents at an external list of at most $2^{40}$ primes fixed before the draws, and require even exponents only at the other primes.

| Rows available from each source | Event anywhere in the batch | Prime-list capacity for one source | Dusart bound | Elementary bound |
|---|---|---:|---:|---:|
| At most one fraction, chosen by the time the source is processed | Any nonempty dependency | $2^{56}$ | $<2^{-80}$ | $<2^{-38}$ |
| Every eligible fraction, even with hindsight | A dependency using some source exactly once | $2^{68}$ | $<2^{-46}$ | $<2^{-9}$ |

For the first row, process sources in order. Consider the latest source used in a proposed nonempty dependency. Conditional on its past, put in $S$ every prime dividing an earlier selected row, together with the external list. Every prime outside $S$ in the current $|a|b$ must occur to even exponent, because no earlier row can cancel it. Since $\gcd(|a|,b)=1$, these exponents must be even in the two coordinates separately. Thus the event requires a fraction of the square-times-$S$-smooth kind bounded above. The current fraction may depend on earlier choices and the current draw. This reasoning also applies if each source has one fraction chosen by a fixed rule depending only on its own residue, and the dependency is chosen after examining the whole batch.

Every norm satisfies $|a|b\le N/2<2^{2047}$ and has at most 255 distinct prime factors. The product of the first 256 primes, ending at 1,619, already has 2,290 bits. The certificate multiplies them directly. Thus $2^{40}+255(T-1)<2^{56}$ bounds the size of $S$. Applying the single-source bound at capacity $2^{56}$, then summing over all possible latest sources, gives the first row.

For the second row, fix a potential singly used source $i$ and condition on **all other draws**. Include in $S$ the primes of **every** eligible fraction from those other sources, along with the external list. This set is independent of $x_i$ even if the eventual choice of fractions examines the whole batch. Other sources may contribute any number of their rows. If source $i$ contributes exactly one, all its primes outside $S$ must again occur to even exponent. Sum the resulting bound over the $T$ possible choices of $i$. Dependencies using two or more rows from each participating source have no singly used source. Their probability remains open under this argument.

The size of this second list follows from continued fractions. Write $y=x^2\bmod N$ with $1\le y<N$. For a reduced eligible fraction, $k=(by-a)/N$ is integral, $k/b$ is reduced, and

$$
\left|\frac yN-\frac kb\right|=\frac{|a|}{Nb}<\frac1{2b^2}.
$$

The inequality is strict since $N$ is odd. Legendre's continued-fraction criterion places $k/b$ among the convergents of $y/N$, and each convergent determines $a$. In the Euclidean remainder sequence, $r_{j+2}<r_j/2$ whenever $r_{j+2}>0$. If $r_{j+1}>r_j/2$, the next remainder is $r_j-r_{j+1}$, and otherwise the next remainder is smaller than $r_{j+1}$. Starting from $N<2^{2048}$ leaves fewer than 4,100 states including endpoints. Hence $2^{40}+4100\cdot255(T-1)<2^{68}$. [Euclidean correspondence and rational endpoints](shared-root-signs.md)

The evaluator reruns the Euler product at each capacity. At $2^{56}$ the exponents $921/1024$ and $235/256$ give respective single-source log-probability bounds $-128.284$ and $-86.384$. At $2^{68}$, $943/1024$ and $15/16$ give $-94.357$ and $-57.391$. All four are base-two upper bounds including arbitrary square factors. Adding 48 for the union over sources yields the displayed probabilities. [Reproduce all six certificate rows](../experiments/smooth_fraction_budget.py)

A separate count handles two rows from the same source whose signed norms multiply to an exact square. Combining it with the singly used source result above bounds the probability of any two-row exact square in $2^{48}$ independent unit-square sources by $2^{-45}$. Dependencies of three or more rows with each participating source used at least twice remain open. [Two-row count and its assumptions](same-source-pairs.md)
