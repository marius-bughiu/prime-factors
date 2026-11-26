# Factoring products whose prime gap is close to a cube root

We recovered the two 1,024-bit prime factors of **two specially constructed 2,048-bit numbers**, starting only from each product. We guessed roughly how far apart the primes were, used that guess to pick one midpoint, and tested it. Lean verified both factorizations. The same test missed both ordinary full-size controls. [First full-size certificate](../benchmarks/controls/CubicForcedControl.lean) · [Second full-size certificate](../benchmarks/controls/CubicGapControl.lean)

## How can a wrong guess find the right primes?

Consider **1,007**. The cube root of $4\times1{,}007$ is just under 16. Round it up, add 1, and try 17 as half the distance between the primes. Then $1{,}007+17^2=1{,}296=36^2$. The primes are $36-17=19$ and $36+17=53$.

For an arbitrary odd product $N$, the same test sets $g=1+\lceil\sqrt[3]{4N}\rceil$ and rounds $\sqrt{N+g^2}$ to the nearest integer $m$. If $m^2-N$ is a square $d^2$, we check the two candidates $m-d,m+d$. This takes one integer cube root and at most two integer square roots. It is a choice of where to try Fermat's difference of squares. An exact guess for $d$ is unnecessary because a range of nearby guesses can round to the same $m$. [Product-only search](../experiments/cubic_gap_window.py)

For any odd 2,048-bit product of the form $p(p+2d)$, Lean proves that an error $|d-g|\le2^{339}$ suffices. The size of $N$ makes the rounding stable. The change in the squared midpoint is at most $E(2g+E)$ when the half-gap error is at most $E$. Here that is smaller than the true midpoint. [Rounding and recovery theorem](../PrimeFactors/CubicGapWindow.lean)

| Input | What was known to the search | Result |
| --- | --- | --- |
| 1,007 | Product alone | 19 × 53 |
| Constructed 2,048-bit product in the exact polynomial family | Product alone | Both 1,024-bit primes checked |
| Second constructed 2,048-bit product, outside the exact family | Product alone | Both 1,024-bit primes checked despite a 338-bit half-gap error |
| Two ordinary 2,048-bit controls | Each product alone | One midpoint tested on each, both cofactors unresolved |

The second control was generated specifically to test the tolerance. Its primes each have a predecessor divisible by the same independently certified 513-bit prime. This makes their primality certificates inexpensive to construct. Only the generator uses that shared prime and the target gap. The search takes $N$ alone. Starting Fermat's search at the square root and moving one midpoint at a time would require more than $6\times10^{102}$ square tests on each of the two constructed products. That is an exact count to the first nontrivial midpoint, calculated from the checked factors. [Off-family construction and work counts](../research/cubic-gap-control.json) · [Independent parameter generation](../experiments/cubic_gap_control.py)

## Why try a cube root in the first place?

We started with two rows in a cubic field. For **every** positive odd input, we can choose $H\in\{1,-1\}$ with $4\mid N+H$, put $w=(N+H)/4$, and set $F(X)=(X+1)(X+4)(X+w)-H$. This cubic is irreducible. A rational root would be an integer and its first two shifted factors, which differ by 3, would both have absolute value 1.

At the public input $X=0$, the first two rows multiply to the ordinary square 4. In the cubic field each has norm $H$, so the product has square norm 1. The field element itself is a square **exactly for the four positive inputs 9, 11, 27 and 91**. The trace equation reduces to $u^4-2H(2w-5)u^2-8u+9=0$, so only signed divisors of 9 need consideration. On 91 the actual field square gives ordinary gcds 91 and 1. A separate public derivative check already gives 7. This is an exact reason the first pair of rows cannot produce a square at the target size. [Complete field-square classification](../PrimeFactors/CubicForcedUnits.lean)

Allowing different row values gives genuine splits. For $F(X)=(X+r)(X+t)(X+w)-H$ with $rt=z^2$ and $N=rtw-H$, a nonzero usable trace $u$ divides $H^2(r-t)^2$. The two integers

$$
z\bigl(u^2+H(r+t)\bigr)\ \pm\ 2H(u+rt)
$$

multiply to $4Hu^2N$. Dividing out a common factor with $N$ can reveal a prime. With $r=1,t=196,H=9$ it gives **1,883,747 = 1,193 × 1,579**, with no factor supplied to the search. Exhausting the twelve fixed row pairs and their prescribed small shifts produced 221 possible odd inputs with a square, the largest only 4,198,095. The bound on the trace lets us enumerate every possible input for that menu. [Identity and divisor bound](../PrimeFactors/CubicForcedParameters.lean) · [Complete menu census](../research/cubic-forced-units.json)

Let the row size grow instead. Taking $r=H=u=1$, $t=4s^2$ gives the factorization

$$
16s^6-4s^2-1=(4s^3-4s^2+2s-1)(4s^3+4s^2+2s+1).
$$

For $s\ge2$, the ceiling of the cube root of $4N$ is exactly $4s^2$. One more square root recovers $s$ and therefore both factors. The algebra also shows that the true half-gap is $4s^2+1$, which suggested trying the broader midpoint test above. The proof gives the two integer factors for every parameter. In our first full-size example both are prime. [Exact decoder](../PrimeFactors/CubicForcedParameters.lean) · [Construction, generation budget and independent prime checks](../experiments/cubic_planted_control.py)

## How often can the shortcut work?

For the exact polynomial family, fewer than $2^{341}$ parameters fit below $2^{2048}$. Even if every one gave two primes, the family would account for less than one in $2^{1680}$ eligible pairs. For the wider single-midpoint test, Lean bounds **all** successful inputs, including accidental matches outside the sufficient error band, by fewer than one in $2^{666}$ eligible pairs. The population is uniformly drawn distinct 1,024-bit primes conditioned on their product having 2,048 bits. The result measures this particular prediction of the gap. Finding a practical way to predict a useful midpoint for ordinary products remains open. [Exact-family count](../PrimeFactors/CubicForcedParameters.lean) · [Rounding converse and population theorem](../PrimeFactors/CubicGapWindow.lean)

The discoveries use elementary algebra, Fermat's identity and the classical cubic trace quartic. The full-size examples use modular-order primality certificates. The first uses a cube-root-sized part of each predecessor, in the tradition of Brillhart, Lehmer and Selfridge. The second uses a known prime order larger than the square root required for Pocklington's criterion. These certificates check primality after the public search proposes the factors. [Earlier cubic quartic and sources](cubic-square-relations.md) · [Primality proof](../PrimeFactors/CubicPlantedPrimality.lean) · [Brillhart, Lehmer and Selfridge](https://doi.org/10.1090/S0025-5718-1975-0384673-1)
