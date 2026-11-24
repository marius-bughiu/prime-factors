# Choosing the multiplier before a continued-fraction search

On 64 fresh products of two 40-bit primes, a small-prime score found both factors on **26 products**, compared with **14** using the ordinary continued fraction. Both searches took exactly 5,138 steps on each product. The score retained every ordinary success and added 12 new ones. Each score used only the product and a fixed list of small primes. This is a result on the 79-bit sample. The 2,048-bit controls below explain why a high score alone gives no guarantee. [All 64 inputs, outcomes and work counts](../research/scored-holdout.json)

## The 64 paired trials

Before sampling, we fixed the seed `crt-cf-score-v1`, the three schedules below, the multiplier menu, the score precision, the step budget and the sample size. We used separate SHAKE256 domains to rejection-sample each 40-bit prime, checked primality by exact trial division, and retained the first 64 distinct 79-bit products of distinct primes. The final retained pair had zero-based attempt number 154. Discovery received $N$ and the fixed schedule. We used the generated factors only to check the answers and to build Lean certificates. All 64 products and both primes in each product passed the kernel replay, including those for which a given search exhausted its budget. [Sampling protocol](crt-holdout.md#sampling-and-verification) · [Search and replay](../experiments/scored_multipliers.py)

| Multiplier for the continued fraction of $\sqrt{mN}$ | Splits | Steps over the sample | Rows excluded by private factors | Independent square relations | Relations tested before returning |
| --- | ---: | ---: | ---: | ---: | ---: |
| $m=1$ | 14 | 328,832 | 322,863 | 999 | 661 |
| First positive odd squarefree $m$ with $mN\equiv1\pmod8$ | 11 | 328,832 | 323,056 | 952 | 623 |
| Highest-scoring $m$ | 26 | 328,832 | 319,984 | 1,199 | 711 |

Comparing the score with the dyadic rule on the same inputs, both found 10, the score alone found 16, the dyadic rule alone found one, and neither found 37. The score chose $m=1$ on 34 inputs. On the remaining 30 it chose values from 3 through 47. For example, on $542358138529489482307733$ the score chose $m=3$. Its seventh square-relation test recovered 708327820313 and 765688037341. The other two walks exhausted their budgets. The scored schedule reduced each input modulo 24 small odd primes. Those remainders checked divisibility and supplied the signs from a fixed table. Comparing them with the 26 multiplier rows took 591 sign comparisons per input. The elementary dyadic rule requires at most four residue tests and one multiplier gcd. Matching the walk lengths leaves those differences in setup and relation processing visible.

### Shorter searches and measured cost

We reran both methods on the same 64 products, stopping each walk at four different lengths. The CPU times below total all 64 searches on one arm64 Mac running Python 3.9.6. They include choosing the multiplier and checking candidate relations. The clock stopped before comparing each result with the previously certified factors. We alternated which method ran first on successive products.

| Steps per product | Ordinary splits | Scored splits | Ordinary CPU seconds | Scored CPU seconds |
| ---: | ---: | ---: | ---: | ---: |
| 2,048 | 0 | 0 | 1.35 | 1.39 |
| 3,072 | 0 | 0 | 2.86 | 3.00 |
| 4,096 | 3 | 4 | 5.32 | 5.92 |
| 5,138 | 14 | 26 | 10.57 | 13.08 |

At the longest setting the scored search used about 24% more CPU time and recovered 12 more products. The two shortest searches recovered none. The measurements compare these settings on this sample and do not establish how much work would be required at 2,048 bits. [Per-method counts, solved indices and timings](../research/scored-prefixes.json) · [Timing script](../experiments/scored_prefixes.py)

## What the score measures

Put $d=mN$ and $Q=x^2-dy^2$. The local model draws a pair $(x,y)$ uniformly modulo a power of each small prime $\ell$, conditional on not both coordinates being divisible by $\ell$. The numerator and denominator of each continued-fraction convergent are coprime. This motivates the model, but actual convergents of a fixed $\sqrt d$ need not follow this distribution. We check for proper common divisors during setup. At each odd $\ell\le97$ that passes the check, the expected valuation in the model is

$$
E_\ell(d)=
\begin{cases}
2\ell/(\ell^2-1) & d\text{ is a nonzero square modulo }\ell,\\
0 & d\text{ is a quadratic nonresidue},\\
1/(\ell+1) & \ell\mid m .
\end{cases}
$$

Indeed projective classes modulo $\ell^j$ number $\ell^j+\ell^{j-1}$. A primitive pair satisfying the congruence has unit second coordinate, so its class is one of the roots of $z^2=d$. Each class has the same number of primitive representatives. In the first case there are two roots at every level. Summing the resulting geometric series gives the first expectation. In the last case $m$ is squarefree and $N$ is a unit. The single root at level one has no lift to level two. For odd $d$, the same argument at 2 gives $E_2(d)=4/3$ for $d\equiv1\pmod8$, $2/3$ for $d\equiv5\pmod8$, and $1/3$ otherwise. For the first case the counts of roots modulo $2,4,8,16,\ldots$ are $1,2,4,4,\ldots$. [Local counting results](../PrimeFactors/PrimitiveNorm.lean) · [Finite-level checks for the score](../tests/test_scored_multipliers.py)

Take all 26 odd squarefree $1\le m\le63$, put $w(t)=\lfloor256\log_2t\rfloor$, and maximize

$$\sum_{\ell\le97,\ \ell\text{ prime}}w(\ell)E_\ell(mN)-w(m)/2.$$

The implementation computes $w(t)$ as the bit length of $t^{256}$ minus one and breaks ties toward the smaller $m$. Once per process it generates the 517 distinct nonzero squares across the 24 odd prime moduli. It then prepares 624 multiplier–prime entries. The 33 entries where the prime divides the multiplier contribute fixed terms, and the other 591 store a sign and a weight. At query time, multiplicativity makes $mN$ a nonzero square precisely when the signs of $m$ and $N$ agree. The scorer uses the same $N$ remainder for its divisibility check and sign lookup. The dyadic residue adds the contribution from two. A common denominator of 613368531270855360 lets the candidate comparisons use integers exactly. Exhaustive checks compare every candidate score against direct Euler-criterion evaluation on every admissible odd input up to 1,023. The penalty charges for the growth of $\sqrt{mN}$. Scoring known small-prime contributions against a multiplier-size penalty is the classical Knuth–Schroeppel idea. Pomerance and Wagstaff applied it to continued fractions. Our experiment uses the specified primitive-pair expectations, rounded weights, fixed schedules and the repository's exact relation checker. It independently implements the score. [Pomerance and Wagstaff, *Implementation of the Continued Fraction Integer Factoring Algorithm*](https://math.dartmouth.edu/~carlp/PDF/implementation.pdf)

Across all 67,108,864 possible combinations of signs and residues in the uniform local model, picking the best multiplier improves the predicted small-prime contribution after its size penalty by 0.7252 bits on average. This measures the score itself. Measuring factor discoveries requires checking the actual continued fractions, as in the trials above. [Exact count and limits of the score](multiplier-score.md)

## Checked examples and two full-size controls

On the existing $150235091$ example, the score selected $m=11$. At 60 steps a relation gave $10007\cdot15013$. At 59 steps the input remained unresolved. The ordinary and dyadic walks with $m=1$ and $m=3$ still failed at 128 steps. We selected this earlier example to illustrate the difference; the 64 newly drawn products above supply the comparison across inputs. [Fixtures and expected work counts](../benchmarks/scored-multipliers.json)

On the crossed 2,048-bit control from the CRT experiment, the score chose $m=1$. All 1,024 rows in its CI budget were excluded by private nonsquare factors. The already checked 131,072-row ordinary walk on this same input contains every row of its 65,536-step prefix, so the earlier exclusion applies to that longer scored budget as well. [Full-size comparison](crt-square-norms.md)

On a different, deliberately constructed 2,048-bit example, the product is a nonzero square modulo every odd prime through 97 and is one modulo eight. Every other multiplier incurs a positive size penalty. The score selects $m=1$ uniquely. The continued fraction ends its first period after one step, giving a single negative norm of $-1$ and no positive square dependency. One ordinary Fermat midpoint recovers both factors of this product. [Construction and proof](square-neighbor-period.md)

The following command reruns all three fixed schedules, regenerates the report, and replays the 64 Lean certificates.

```sh
python3 experiments/scored_multipliers.py --holdout --verify
```
