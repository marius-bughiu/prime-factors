# When the factor sum divides the next integer

The product **7,687,946,879,999** splits after removing the powers of 2, 3 and 5 from its neighbor and testing one square. Those powers multiply to **5,760,000**. Subtracting four times the product from $5,760,000^2$ gives **1,557,502²**. Taking half of $5,760,000-1,557,502$ and half of $5,760,000+1,557,502$ gives the primes **2,101,249** and **3,658,751**. The procedure used 19 small-prime remainder checks, 16 exact divisions and one integer square root. Both 2,048-bit controls remain unresolved by this rule. [Lean proof and prime certificates](../PrimeFactors/ReciprocalInverseSums.lean) · [Reproducible benchmarks](../benchmarks/neighbor-smooth-sum.json)

## Why the sum appears

Write $N=pq$, where $1<p<q$ are coprime, and let $u$ be the positive inverse of $p$ modulo $q$, and $v$ the positive inverse of $q$ modulo $p$. Then $pu+qv=N+1$. Both sides are 1 modulo $p$ and $q$, and the left side lies strictly between 1 and $2N$. This is an established reciprocity identity. [Ko, *Modular Inverse and Reciprocity Formula*, Theorem 3.1](https://arxiv.org/pdf/1304.6778)

The two inverses coincide precisely when $S=p+q$ divides $N+1$. Indeed $pu+qv=vS+p(u-v)$. Since $p$ is coprime to $S$ and $|u-v|<S$, divisibility forces $u=v$. For a fixed sum there is also an exact construction rule. The condition $S\mid N+1$ is equivalent to $p^2\equiv1\pmod S$ because $N=p(S-p)$. Each root $0<p<S/2$ fixes $q=S-p$. One still checks the actual sum on a given $N$. For example, 158 divides $6,161+1$ and lies in the balanced sum range, but $158^2-4\cdot6,161=320$ is between consecutive squares. [Equivalences and necessary signed conditions](../PrimeFactors/ReciprocalInverseSums.lean)

For a signed difference $e=u-v$, the identities give

$$
S\mid(N+1)^2+Ne^2,\qquad p^2+ep-1=S(p-v).
$$

The second identity limits the possible partners for a fixed smaller factor and a guessed difference. The first produces a public integer whose divisors can be tried. It has remainder 1 modulo $N$, so taking its gcd with $N$ gives 1. Both signs of $e$ give the same public integer. For odd factors $e$ is even. A trial that starts from these conditions must still generate candidate divisors and verify a square. [Signed identities](../PrimeFactors/ReciprocalInverseSums.lean) · [An accidental success and population bounds](which-inverse-guesses-can-work.md)

## A bounded public choice

Choose a fixed set of small primes, and let $B$ be the product of their full powers in $N+1$. Test $S=B$ when $S$ is even and $4N\le S^2\le 9N/2$. The bounds follow from $p\le q\le2p$. If $z^2=S^2-4N$, verify the product of $(S-z)/2$ and $(S+z)/2$. For the equal-inverse family the one-guess rule finds every balanced pair for which the prime support of $S$ lies in the chosen set and $(N+1)/S$ is coprime to every chosen prime. A larger set can make this single choice worse. On the 43-bit example, including 23 multiplies the guessed sum by 23 and the range check rejects it. [Acceptance proof](../PrimeFactors/ReciprocalInverseSums.lean)

| Public product | Selected primes | $B$ | Remainder checks | Exact divisions | Discriminant square roots | Outcome |
| --- | --- | ---: | ---: | ---: | ---: | --- |
| 8,590,000,127 | 2, 3 | 196,608 | 19 | 17 | 1 | 65,537 × 131,071 |
| 7,687,946,879,999 | 2, 3, 5 | 5,760,000 | 19 | 16 | 1 | 2,101,249 × 3,658,751 |
| Fresh 2,048-bit | 2, 3 | 16 | 6 | 4 | 0 | Unresolved |
| Crossed 2,048-bit | 2, 3 | 2 | 3 | 1 | 0 | Unresolved |
| Fresh 2,048-bit | All primes through 31 | 880 | 17 | 6 | 0 | Unresolved |
| Crossed 2,048-bit | All primes through 31 | 10 | 13 | 2 | 0 | Unresolved |

Checks include the final unsuccessful remainder check for each selected prime. Counts exclude the final multiplication and independent primality certificates. Enumerating every divisor $d$ of $B$ and testing both $d$ and $(N+1)/d$ broadens coverage to cases where either the true sum or its complementary divisor is smooth. The extended rule generates at most $2\tau(B)$ candidates before the size test. On the two full-size controls with primes through 31, $B$ has respectively 20 and 4 divisors. Neither list, even with complements included, puts an even sum in the balanced range. [Benchmark results and public controls](../benchmarks/neighbor-smooth-sum.json)

## How the examples were chosen

The successes were deliberately constructed. For the first example we enumerated $S=2^a3^b$ with $3\le a\le16$ and $1\le b\le11$. For the second we used $S=2^a3^b5^c$ with $2\le a\le13$, $1\le b\le9$, $1\le c\le5$. In both cases we kept $50,000<S<10^8$, enumerated square roots of 1 by CRT, and required $S/3<p<0.41S$, equal factor bit lengths, prime $p,q=S-p$, and $(N+1)/S$ coprime to all the selected primes. Each bounded construction produced one product. The subsequent recovery from each product used only $N$ and the selected prime list. [Checked splits and baseline arithmetic](../PrimeFactors/ReciprocalInverseSums.lean)

Ordinary Fermat search, testing each successive integer midpoint starting at $\lceil\sqrt N\rceil$, takes 5,622 and 107,286 square checks respectively. On the first example $2p-q=3$, so weighted Fermat also succeeds at its very first parity-compatible trace for weights $(2,1)$. On the second, all 43 ordered coprime weight pairs $1\le a,b\le8$ miss at their first parity-compatible trace. The fewest parity-compatible steps through the specific trace $ap+bq$ among these 43 choices is 47, attained by $(7,4)$. This count measures distance to that trace. Other ways of splitting the multipliers can give a different square. [Weighted trace receipts](../PrimeFactors/ReciprocalInverseSums.lean)

## How large is the two-prime family?

Two 1,024-bit factors have sum in $[2^{1024},2^{1025})$. If their sum has the form $2^a3^b$, fixing $b$ leaves at most one $a$ in that entire band. Also $3^{647}>2^{1025}$, giving at most 647 possible sums. Each sum has at most eight unit square roots of 1, by the prime-power counts and CRT. A smaller root $p$ and its larger partner $S-p$ use two roots. Thus there are at most **2,588 unordered pairs** across the whole band even if composite factors are admitted, before checking that $N$ itself has 2,048 bits. This limits the entire equal-inverse family with a 2,3-smooth sum, including every success of the one-guess rule with those two primes. [Factor-sum count](../PrimeFactors/ReciprocalInverseSums.lean) [Prime-power root bound](../PrimeFactors/StationaryRadixLimit.lean)
