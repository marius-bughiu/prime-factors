# Can signed measurements cancel the neighboring terms?

The coefficient at 527 in the normalized modular index series reveals the sum of its two primes. A positive average tuned to 527 picks up a large contribution from 528. A signed average can cancel 528 exactly. We tested three such averages, canceling the next one, two or three terms. All three still missed the accuracy needed to recover the sum. [Positive average](isolating-an-index-coefficient-by-averaging.md) · [Reproducible interval calculation](../experiments/signed_index_notches.py)

## The price of an exact cancellation

Suppose the reading combines frequencies $t_j$ between $-T$ and $T$ with complex weights $c_j$ summing to one. A term at log-distance $x$ from the desired index gets multiplier $K(x)=\sum_j c_j e^{it_jx}$. If every frequency measurement has absolute error at most $\varepsilon$, the error in the result can reach $\varepsilon\sum_j |c_j|$ when the errors align. This describes precision in the measurements after multiplying each by $N^{2+it_j}$.

For $0<Tx\le\pi/2$, imposing $K(x)=0$ requires $\sum_j |c_j|\ge1/\sin(Tx)$. Two samples at the endpoints of the band attain equality. The proof bounds the distance from 1 to $\cos(Tx)e^{it_jx}$, then sums over the weights. If the first $r$ positive multiples of $x$ must all vanish, the lower bound becomes $1/\sin(Tx)^r$. For neighboring integers $N$ and $N+1$, $x=\log(1+1/N)$, so exact cancellation in a narrow band can amplify errors greatly. This is a bound on precision for these linear readings. [Lean lower bound and matching endpoint construction](../PrimeFactors/SignedIndexNotches.lean)

## Three complete readings at 527

For arbitrary chosen neighbors, let $x_i=\log((N+i)/N)$ and choose $\Delta$ so that $z_i=e^{i\Delta x_i}\ne1$. The polynomial $\prod_i(z-z_i)/(1-z_i)$ equals one at the desired index and zero at each neighbor. Its coefficients specify at most $r+1$ equally spaced measurements. Lean checks the normalization, zeros and degree. [Polynomial construction](../PrimeFactors/SignedIndexNotches.lean)

We set $N=527$, removed all squarefree divisor terms through 7, and used $\Delta=2\pi/((r+1)x_1)$. Centering the frequencies gives the real kernel $\prod_i\sin(\Delta(x_i-x)/2)/\sin(\Delta x_i/2)$. The desired coefficient is $49/527$. Each interval below encloses the full signed reading minus this exact target. The rounding tolerance is $12/527$, about 0.023.

| Neighbors canceled | Enclosure of the error |
| --- | --- |
| 528 | 60.45 to 92.22 |
| 528 and 529 | 896.19 to 938.50 |
| 528 through 530 | −142.81 to −79.56 |

The calculation encloses the first 5,000 terms with outward-rounded decimal arithmetic. For a cutoff $Y$ and last index $J$, the remaining absolute error is at most $N^2L(2/(JY)+1/J^2)$, where $L$ bounds the magnitude of the kernel. To see this, group omitted terms by divisor $d$. For $d\le J$, use $\sum_{k>J/d}k^{-2}\le2d/J$ and sum $d^{-2}$ over $d>Y$. For $d>J$, use $\sum_{k\ge1}k^{-2}\le2$ and sum $d^{-3}$. The experiment bounds $L$ by the reciprocal of the absolute product of the normalizing sines. Other frequency choices and choices of which terms to cancel remain open. [Calculation and precision](../experiments/signed_index_notches.py) · [Inputs and expected bounds](../benchmarks/signed-index-notches.json)
