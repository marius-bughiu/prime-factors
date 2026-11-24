# How often a small prime divides a primitive norm

A multiplier $m$ changes which small primes can divide the signed quantities $x^2-mNy^2$ in a continued-fraction search. For each prime $p$, we can calculate exactly how much divisibility to expect **if the two coordinates are sampled uniformly modulo prime powers, subject to at least one being a unit**. The formula takes only $d=mN$. It does not require the factorization of $N$.

This is the quadratic case of the local count behind Murphy's $\alpha$ for homogeneous forms. Knuth–Schroeppel multiplier selection in the quadratic sieve likewise favors products with many small-prime roots and accounts for the size increase due to the multiplier. Silverman's multiple-polynomial sieve and FLINT's implementation use their own sampling and scoring conventions. In CFRAC the samples come from consecutive convergents of $\sqrt{mN}$. A complete period can avoid every predicted odd-prime hit, even on a balanced semiprime. [Barbulescu and Lachand, §2.1 and equation (5)](https://arxiv.org/pdf/1403.0184#page=3) · [Silverman](https://doi.org/10.1090/S0025-5718-1987-0866119-8) · [FLINT's multiplier selection](https://flintlib.org/doc/qsieve/qsieve_knuth_schroeppel.html) · [Morrison and Brillhart's continued-fraction method](https://doi.org/10.1090/S0025-5718-1975-0371800-5) · [A complete-period counterexample](square-neighbor-period.md)

## Exact finite probabilities

Let $j\ge1$ and $r_j=\#\{z\bmod p^j:z^2\equiv d\pmod{p^j}\}$. Among the $p^{2j}-p^{2(j-1)}$ locally primitive pairs modulo $p^j$, precisely $r_j\varphi(p^j)$ satisfy $x^2=d y^2$. Indeed $p\mid y$ would force $p\mid x$, so $y$ must be a unit in a solution. The bijection $(z,u)\mapsto(zu,u)$ has inverse $(x,y)\mapsto(x/y,y)$. Dividing gives the exact probability
$$P_j(d)=\frac{r_j}{p^{j-1}(p+1)}.$$
A primitive pair modulo $p^j$ has the same number of lifts as each other primitive pair at any higher level. Thus the expected value of the valuation capped at $J$ is $\sum_{j=1}^J P_j(d)$. As $J$ tends to infinity these sums give the expected uncapped valuation for compatible uniformly sampled local digits. Lean checks the bijection and the finite probability with denominators cleared. [Lean proofs](../PrimeFactors/PrimitiveNorm.lean)

| Condition on $p$ and nonzero $d$ | Root counts $r_j$ | Expected $p$-valuation |
| --- | --- | ---: |
| $p$ odd, $d$ a nonzero square modulo $p$ | 2 at every level | $2p/(p^2-1)$ |
| $p$ odd, $d$ a quadratic nonresidue modulo $p$ | 0 at every level | 0 |
| $p\mid d$, $p^2\nmid d$, including $p=2$ | 1 at level 1, then 0 | $1/(p+1)$ |
| $p=2$, $d\equiv1\pmod8$ | $1,2,4,4,\ldots$ | $4/3$ |
| $p=2$, $d\equiv5\pmod8$ | $1,2,0,0,\ldots$ | $2/3$ |
| $p=2$, $d\equiv3,7\pmod8$ | $1,0,0,0,\ldots$ | $1/3$ |

For an odd split prime there are two initial roots with distinct signs. Each lifts uniquely since $2z$ is a unit. Summing through level $J$ gives $[2p/(p^2-1)](1-p^{-J})$. When $p\parallel d$ the first residue is zero and no root modulo $p^2$ is possible. Lean proves these two root counts at all levels. For odd $d$, every odd square equals 1 modulo 8. When $d\equiv1\pmod8$ there are four roots at level 3. At each level $j\ge3$, translating a root by $2^{j-1}$ pairs the roots and changes its square by $2^j\bmod 2^{j+1}$. Exactly one in each pair has the correct next square bit, and each such root has two lifts. Thus the count stays four. Lean checks the bit-change identity and existence of lifts. The table then follows by summing the finite probabilities.

More generally put $s=v_p(d)$ and $u=d/p^s$. For $j\le s$, the roots are precisely the multiples of $p^{\lceil j/2\rceil}$, giving $r_j=p^{\lfloor j/2\rfloor}$. For $j>s$, an odd $s$ precludes any root. If $s=2a$ then a root has the form $p^a z$ with $z$ a unit. Each root of $z^2=u$ modulo $p^{j-2a}$ yields $p^a$ roots at level $j$. This covers multipliers containing higher prime powers.

For any finite set of primes, linearity of expectation gives the modeled logarithm of the small-prime part by summing $\log(p)\sum_{j\ge1}P_j(d)$. An alternative scoring rule can subtract the random-integer baseline $\log(p)/(p-1)$ or a multiplier size penalty as appropriate. Convergent coordinates are globally coprime, which makes the local restriction necessary. Their distribution within the permitted classes still depends on the continued fraction and its chosen prefix.
