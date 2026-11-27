# Reading factor bits from counts of coprime integers

Suppose the only input is the product of two distinct odd primes of equal bit length. We found a sequence of integers determined by that product. On at least one row, taking the greatest common divisor with the product gives a prime factor. For two 1024-bit primes, there are at most 1022 rows. Constructing even the smallest integer in the sequence would require more than $2^{1024}$ bits when the product has 2048 bits. This leaves the original computational problem open.

## What the counts tell us

Write $N=pq$. At binary position $j\ge1$, let $A=\lfloor N/2^j\rfloor$, $m=\lfloor A/2\rfloor$, and let $C(A)$ count the integers from 1 through $A$ coprime to $N$. Every excluded integer is a multiple of exactly one of the two primes, since $A<N$. Counting these multiples gives

$$
A-C(A)=\lfloor p/2^j\rfloor+\lfloor q/2^j\rfloor.
$$

Twice the count at the next endpoint minus the count at this endpoint, corrected by the public parity of $A$, therefore reads a pair of bits. With bit zero the units digit,

$$
2C(m)-C(A)+(A\bmod2)=\operatorname{bit}_j(p)+\operatorname{bit}_j(q).
$$

At $j=1$ the first identity already gives $p+q=N+1-2C(\lfloor N/2\rfloor)$. With that sum, the two factors follow from the quadratic formula. Conversely, given the factors, two integer divisions suffice for each count. An exact half-count algorithm would thus solve the factoring problem for this family. The cancellation identity does not supply an economical way to count the missing multiples. Lehmer studied the classical distribution of integers coprime to a modulus. The project previously recovered the same binary sums by counting accepted multiplier assignments. [Lehmer, *The Distribution of Totatives*](https://doi.org/10.4153/CJM-1955-038-5) · [Counting the factor sum](counting-the-factor-sum.md)

## What one coefficient can reveal

Use the integer

$$
F(A)=\frac{A!}{(m!)^2}=
\begin{cases}
\binom{2m}{m}, & A=2m,\\
(2m+1)\binom{2m}{m}, & A=2m+1.
\end{cases}
$$

Assume $p<q<2p$. At any $j\ge1$, $A<p^2$ and $A<q^2$. By Legendre’s factorial formula, the exponent of $p$ in $A!$ is simply $\lfloor A/p\rfloor$. Subtracting twice the corresponding value at $m$ gives
$$
v_p(F(A))=\operatorname{bit}_j(q),\qquad
v_q(F(A))=\operatorname{bit}_j(p).
$$
These identities need no assumption on prime gaps or the Riemann hypothesis. Granville describes the classical connections between prime divisibility of binomial coefficients and digits. [Granville, *Arithmetic Properties of Binomial Coefficients I*](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/granville.pdf)

| Bit of $p$ | Bit of $q$ | $\gcd(F(A),N)$ |
| --- | --- | --- |
| 0 | 0 | 1 |
| 0 | 1 | $p$ |
| 1 | 0 | $q$ |
| 1 | 1 | $N$ |

Distinct odd primes of equal width agree in their lowest and highest bits and differ somewhere between them. For 1024-bit primes, searching positions 1022 through 1 therefore guarantees a split if each indicated gcd can be evaluated. With the factors in hand those gcds are cheap to predict, so a fast algorithm for evaluating the gcds and a fast algorithm for factoring this family would each imply the other.

## Cost and bounded checks

On every row of this schedule both $m!$ and $A!$ are divisible by $N$. Reducing those factorials separately modulo $N$ gives two zeros and erases the information used in their integer quotient. Moreover $F(A)\ge2^m$. When $N\ge2^{2047}$ and $j\le1022$, the row has $A\ge2^{1025}$ and $m\ge2^{1024}$. These bounds quantify the cost of writing down the exact coefficient. They leave open the cost of computing its gcd by another method. The Lean file proves the count identities, valuations, split schedule, vanishing residues, coefficient-size bound and three exact small factorizations. [Lean proofs](../PrimeFactors/DyadicTotativeMasks.lean)

The experiment starts at the highest eligible position and computes exact central binomials only when $A\le4096$. It receives the input and cap alone. The expected factors are read by a separate check after the search. Across the examples, unhelpful gcds of 1 and the whole product both occur. Across the three examples, direct coprimality counts checked 18 contrasts.

| Product | Tested row sizes | Observed gcds | Result |
| --- | --- | --- | --- |
| 2257 | 141 | 37 | $37\times61$ |
| 3127 | 195, 390 | 3127, 53 | $53\times59$ |
| 1763 | 110, 220, 440, 881 | 1, 1763, 1, 41 | $41\times43$ |
| Fresh 2048-bit control | None | None | First requested row has 1026 bits |
| Crossed 2048-bit control | None | None | First requested row has 1026 bits |

Run `python3 experiments/dyadic_totative_masks.py --fixtures` to reproduce all five cases. Both full-size inputs remain unresolved under this cap. The optional `--small-census` run checks every unordered pair of distinct primes of widths six through nine. At the same 4096 cap it split 21 of 21, 77 of 78, 236 of 253 and 747 of 903 products respectively, using 35, 138, 439 and 1438 coefficient evaluations in total at the respective widths. Can a method working directly modulo the public product retain the cancellation information without materializing the coefficient or extracting the two factorial residues separately? [Experiment](../experiments/dyadic_totative_masks.py) · [Fixtures and budgets](../benchmarks/dyadic-totative-masks.json)
