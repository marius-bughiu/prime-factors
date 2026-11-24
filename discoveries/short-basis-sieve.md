# A smaller worst-case search bound for balanced prime products

Given only $N=pq$ with distinct primes $p<q\le2p$, the search derived here takes

$$N^{1/5}\exp\!\left[-\left(\frac{\log(4/3)}{25}+o(1)\right)
                 \frac{\log N}{\log\log N}\right]$$

deterministic classical bit operations as $N\to\infty$. Stănică’s November 2026 preprint gives the same main power with $\log(4/3)/50$ in the secondary exponent and covers general inputs. Our balance assumption includes every pair of distinct 1024-bit primes. Doubling that constant improves the asymptotic upper bound for this deterministic search. It gives neither a measured speedup at 2048 bits nor a runtime comparison with the number field sieve. [Stănică, Theorem 3.13 and Remark 3.14](https://arxiv.org/html/2611.06580v1#S3) · [Harvey and Hittmeir’s underlying factor search](https://arxiv.org/abs/2105.11105)

A subsequent derivation doubles this secondary constant again for the same balanced inputs. It uses a larger primorial, counts exceptional rows directly, and uses a different way to obtain the powered base. [One-interval sieve and finite checks](wide-modulus-sieve.md)

The change is how we handle an unhelpful pair of weights. We always take the shortest lattice vector. If its coefficients share a few primes with the sieve modulus, the search can tolerate those failed tests. If they share many, dividing out their common divisor leaves much smaller weights. A separate search can afford to try every such reduced pair. The argument below charges for both searches, including unsuccessful guesses.

This is a research derivation using the cited lattice, collision and order theorems. Lean checks finite counting, modular and inequality steps. The full asymptotic theorem currently has a written proof. The bounded code checks the arithmetic using direct operations and records their cost. Independent mathematical review of the full result remains outstanding. [Finite sieve bounds](../PrimeFactors/ShortBasisSieve.lean) · [Normalized weights](../PrimeFactors/ExceptionalWeights.lean) · [Exceptional search](../experiments/exceptional_weights.py)

## The public lattice and its estimates

Write $s=\sqrt N$, $L=\log N$ and $E=L/\log L$ with natural logarithms. Parameters below are for sufficiently large $N$. Trial division suffices for the finitely many smaller inputs. Handle an even product immediately. Choose the squarefree primorial $m$, the interval parameter $m_0$ and the set $\mathcal S$ of selected odd primes as specified at the end. Put $X=mm_0$, $t=|\mathcal S|$, $M=\prod_{\ell\in\mathcal S}\ell$. A nonunit gcd with $m$ splits the input for these parameters since $m<p$. Otherwise all the residue calculations below exist.

Enumerate the units $\sigma\bmod m$ and the geometric intervals $[\sigma_0,(1+1/m_0)\sigma_0)$ of Harvey–Hittmeir intersecting $[s/\sqrt2,s]$. Successive integer starts are $\lceil(1+1/m_0)\sigma_0\rceil$. There are $O(m_0\log N)$ starts even if generated from one. For the genuine pair, $p\equiv\sigma\bmod m$ and $\sigma_0\le p<(1+1/m_0)\sigma_0$. We may restrict to $s/(2\sqrt2)\le\sigma_0\le s$. Use the integer lattice
$$ b\equiv aN\sigma^{-2}\pmod m,\qquad
T(a,b)=(Na,m_0(\sigma_0^2 b-Na)). $$
Its transformed determinant is $D=N X\sigma_0^2$. Two-dimensional Gauss reduction in polynomial bit time gives a nonzero first vector with $\|T(a,b)\|\le2\sqrt D$. The bound holds even when the second vector is very long. [Stănică, Lemmas 3.1–3.3 and Proposition 3.8](https://arxiv.org/html/2611.06580v1#S3)

In particular $|a|\le2\sqrt X$ and $|b-aN/\sigma_0^2|\le 2s\sqrt{m/m_0}/\sigma_0$. For a true cell, $|N/\sigma_0^2-N/p^2|\le 2N/(m_0\sigma_0^2)\le16/m_0$. With a common absolute constant, say 40, this gives
$$|aq-bp|\le40s\sqrt{m/m_0}.$$
The source’s approximation to $aq+bp$ by $aN/\sigma_0+b\sigma_0$ has error at most $\sqrt2\|T(a,b)\|/(m_0^2\sigma_0)$, hence $O(m^2\lambda)$ for $\lambda=s/X^{3/2}$. All interval endpoints can use outward integer rounding. This estimate applies to signed weights.

Take $d=\gcd(|a|,|b|,m)$. For a prime $\ell\mid m$, one coefficient vanishes modulo $\ell$ precisely when both do. Split at $D_0=\exp(t\sqrt{\log L})$. This has $\log D_0/t\to\infty$ and $\log D_0=o(L)$. Rounding it to a nearby integer does not affect the estimates.

## Few failed tests

For $d<D_0$, fewer than $h=\lceil\log D_0/\min_{\ell\in\mathcal S}\log\ell\rceil=o(t)$ selected primes can divide $d$. The true trace $aq+bp$ is known modulo $m^2$ from $\sigma$, and can be written $j+m^2 i$ with public $j$ and $0\le i\le C(\lambda+1)$ for an absolute $C$. For example use $\tau=(aN/\sigma+b\sigma)\bmod m^2$, $g=\lfloor(aN/\sigma_0+b\sigma_0)/m^2\rfloor$, and $j=m^2(g-\Lambda)+\tau$ with $\Lambda$ an integer exceeding the scaled error by two. For each $\ell\in\mathcal S$ with $\ell\nmid d$, Stănică’s extra-digit identity makes $i$ a quadratic polynomial in the unknown next digit of $p$ with nonzero leading coefficient. A computable local translation moves its image into the universal set $A_\ell$ of relative size $3/4+O(1/\ell)$. Use zero translation at the other primes. CRT gives a public $c\in[0,M)$ for this giant record. [Source, Lemma 3.4 and Proposition 3.5](https://arxiv.org/html/2611.06580v1#S3)

Build **one** table permitting up to $h$ failed local constraints, regardless of which giant record is being queried. Its density in a full period is at most
$$\rho_h\le \left(\prod_{\ell\in\mathcal S}\frac{|A_\ell|}{\ell}\right)
             \sum_{j=0}^h {t\choose j}2^j
          =\exp(-t\log(4/3)+o(t)).$$
For any allowed set of $j$ exceptions, erasing those constraints multiplies the full product density by at most $2^j$. The logarithm of the displayed sum is $o(t)$ by $h=o(t)$ and $\binom tj\le(et/j)^j$. The region passing every test is also retained, giving the same logarithmic density from below. Scanning $M$ residues to build the table costs $M\operatorname{polylog}N$. Emit the retained residues and their period lifts through $L_*=C'(\lambda+1)+M$, increasing $C'$ for rounding. There are $O(\rho_h(\lambda+M+1))$ such powers, including incomplete periods. A dense scan through $\lambda$ would lose the gain.

Use $\alpha=\beta^{m^2}$ with the order certification below. Fermat’s theorem gives $aq+bp\equiv aN+b\bmod(p-1)$. Thus the true shifted baby $\alpha^{i+c}$ equals the giant $\beta^{aN+b-j}\alpha^c\bmod p$. Exact equalities modulo $N$ are tested by decoding $i$ and factoring the quadratic with sum $j+m^2 i$ and product $abN$, checking both assignments and verifying the product. For zero weights the remaining linear equation suffices. For the true giant an exact match must have the right baby exponent by the certified order. Process the remaining records with the source’s monic multipoint evaluation and gcd collision routine. Its bit cost is quasilinear in the numbers of baby and giant records up to powers of $\log N$. This gives
$$\bigl(m+X+M+\rho_h(\lambda+M+1)\bigr)(\log N)^{O(1)}.$$
This cost includes visiting every public cell and identifying those that will need the second search. [Source, Lemmas 3.9–3.11 and exact-match recovery](https://arxiv.org/html/2611.06580v1#S3)

## Many failed tests

Run the following search for each $d\mid m$ with $d\ge D_0$. Factoring $m$ is part of its construction. For the true exceptional cell let $r=m/d$, and simultaneously change both signs as necessary. Its normalized weights $u=a/d$, $v=b/d$ satisfy
$$ 1\le u\le U=\lceil 2\sqrt X/d\rceil,\qquad 1\le v\le3u. $$
Indeed $|u q/p-v|\le 40(s/p)\sqrt{m/m_0}/d<1$ for large $N$ with the parameter choice below. This rules out $u=0$ and opposite or zero signs, as $1<q/p\le2$. If $u<0$ reverse both weights. This step uses balance. Enumerating the indicated integer pairs includes decoys; all actual recovery attempts check divisibility.

For each such pair, skip it unless $\gcd(uv,r)=1$. A genuine pair has this property since $m$ is squarefree and all primes shared by the original coefficients and $m$ are in $d$. Enumerate roots $z$ of $v z^2\equiv uN\bmod r$. The genuine $p\bmod r$ is one by cancellation in the lattice congruence. There are at most $P=2^{\omega(m)}$ root classes. Small-prime tables built once in $O(\sum_{\ell\mid m}\ell)$ operations supply all local square roots, and CRT enumerates the combinations in $P\operatorname{polylog}N$ time per weight pair. For $r=1$ use a single residue class. In a root class the **normalized integer trace** $T=u q+v p$ is fixed modulo $r^2$. If $p=z+rj$, then $uN/p+vp\equiv uN/z+vz+rj(v-uN/z^2)\bmod r^2$. The last term vanishes. Write the computable residue as $\tau$, taking $\tau=0$ for $r=1$.

We can also bound the trace in the ordinary integers. Factoring a difference of squares gives
$$0\le T-2\sqrt{uvN}=\frac{(u q-v p)^2}{T+2\sqrt{uvN}}
   \le \frac{1600s m}{m_0 d^2 u}.$$
Here $T+2\sqrt{uvN}\ge u q\ge u s$. **Dividing by the residue spacing $r^2$ cancels the full $d^2$** in this width bound. Starting at the first $\tau\bmod r^2$ at or above $\lceil2\sqrt{uvN}\rceil$, we therefore need only $O(1+s/(Xu))$ consecutive indices. An implementation may enlarge the right endpoint by one for rounding. [Lean slack and stationarity lemmas](../PrimeFactors/ExceptionalWeights.lean) · [Divided width](../PrimeFactors/ShortBasisSieve.lean)

Split these indices into chunks of $B_d$ with one common baby table $\{\alpha_d^e:0\le e<B_d\}$ for this $d$, where $\alpha_d=\beta^{r^2}$. If $J$ is the integer trace at the start of a chunk, the giant is $\beta^{uN+v-J}$. It agrees modulo $p$ with the true baby since $T=J+r^2e$ and $T\equiv uN+v\bmod(p-1)$. Charge a separate record per chunk and root class and keep that metadata through matches. Because $\alpha_d^{d^2}=\alpha$, the order of $\alpha_d$ at either hidden prime is at least that of $\alpha$. Consequently the single order certification suffices whenever $B_d\le L_*$. Exact matches recover a trace by adding $r^2e$ to the chunk start; genuine factors are checked through the same quadratic recovery.

There are at most $3u$ values of $v$ for each $u$. Up to polylogarithms the total per divisor is at most
$$ B_d+O\!\left(P U^2+\frac{P s U}{X B_d}\right). $$
Use $B_d=\max(1,\lceil\sqrt{P s U/X}\rceil)$. For our parameters $d\le m\le\sqrt X$ for large $N$, so $U=O(\sqrt X/d)$. Summing over at most $P$ divisors gives the uniform exceptional cost
$$ (\log N)^{O(1)}\left( P+\frac{P^2 X}{D_0^2}
                       +\frac{P^{3/2}\sqrt{s}}{X^{1/4}\sqrt{D_0}}\right). $$
Since $\log P=O(t)$ whereas $\log D_0/t\to\infty$, even the last term is $N^{1/5}\exp(-\omega(E))$. In particular all $B_d\le L_*$ for large $N$. This pays for the roots, the public search over weights and divisors, and each separate table construction. Counting only genuine reduced weights would give an unjustified saving.

## Parameters and scope

Put $a_0=\log(4/3)$, $c=a_0/25$, and $B=\lfloor L/10-E/10\rfloor$. Take $m=\prod_{\ell\le B}\ell$ and select its odd prime factors $\ell>\sqrt B$. The quantitative prime number theorem used in the source gives $\log m=L/10-E/10+o(E)$, $\omega(m)=(1/10+o(1))E$ and $t=(1/10+o(1))E$. The minimum selected log-prime is of order $\log L$, as required for $h=o(t)$. Choose $m_0=\lceil N^{1/5}\exp(-cE)/m\rceil$. Then
$$\log X=L/5-cE+o(E),\qquad \log\lambda=L/5+3cE/2+o(E).$$
Here $m/m_0\to0$ and we may use fixed-error rational approximations to the logarithmic cutoffs before integer rounding. Changing the cutoffs by bounded amounts, or rounding the large parameters within fixed multiplicative constants, leaves the estimates intact. The term $X$ balances $\rho_h\lambda$ since $5c/2=a_0/10$. The $m,M$ terms are polynomially smaller.

The remaining setup is a sufficiently high-order group element. Apply Harvey–Hittmeir with $D=\lceil m^2 L_*\rceil<N-1$ to obtain a factor or a unit $\beta$ of order exceeding $D$. The cost is $\sqrt D(\log N)^{O(1)}$. Its logarithm is $L/5+(-1/10+3c/4)E+o(E)$, below the target because $1/10>7c/4$. Thus $\alpha$ has order exceeding $L_*$ modulo $N$. Stănică’s square-root-cost certification either splits $N$ or guarantees the same lower bound at each prime. This pays for bases before either search. All computations use classical deterministic arithmetic. [Harvey–Hittmeir, unrestricted order theorem](https://arxiv.org/abs/2601.11131) · [Stănică’s certification](https://arxiv.org/html/2611.06580v1#S3)

The result is asymptotic and specific to balanced prime products. With substantially unbalanced factors a first vector with zero leading weight can enter the exceptional branch, invalidating the positive-weight enumeration. The derivation does not use RH. The comparison is to the stated deterministic upper bounds. The coefficient of $\log N$ remains $1/5$, and constants and lower-order terms preclude extrapolating this improvement into a 2048-bit wall time.

## Reproducible finite checks

The finite reference takes $N$ and the public sieve parameters. It reduces the lattice exactly, builds the translated table, and compares explicit modular powers. For small inputs it sends cells to the second search by their observed count of degenerate primes and derives its weight and gap budgets from interval endpoints. Signed or zero exceptional weights at these finite parameters use a dense fallback. The asymptotic proof above instead gives uniform bounds for every large divisor. The code uses direct pairwise gcds, so these runs do not measure the asymptotic multipoint backend. [Reference search](../experiments/short_basis_sieve.py) · [Benchmarks including unresolved control](../benchmarks/short-basis.json)

| Product | What the search found | Work observed |
| --- | --- | --- |
| $5459$ | The ordinary branch left it unresolved. Enabling the exceptional branch recovered $53\cdot103$ at normalized trace 209. | 18 ordinary gcds and six exceptional gcds. A dense comparison over all 16 original giant records took 80 gcds. |
| $22261$ | Tolerating one failed local restriction retained the exact match for $113\cdot197$. Its shortest weights were $(5,5)$. | 89 baby entries and 363 ordinary gcds. The unshifted dense table had just five baby entries, illustrating the setup cost at this size. |
| $150235091$ | The full bounded schedule recovered $10007\cdot15013$. | For the same 12 ordinary giants, 97 baby entries and 1,070 gcds versus 167 entries and 2,004 gcds in the dense search. The exceptional sweep used another three gcds, plus root and weight enumeration. |

A separate check connects the larger example $1900014700027$ to a genuinely nonunit first vector. At the correct original lattice cell, $(100,190)$ and $(203,389)$ form a determinant-330 basis; their transforms satisfy the exact Gauss inequalities. Dividing the first vector by ten gives $(10,19)$. The reference sweep with the public cap 20 and error budget 40 examines 400 pairs and 172 final root classes. Two candidate traces remain and two modular gcds suffice to find $1000003\cdot1900009$. On this particular example the unfiltered integer bounds already leave two traces. Lowering the budget to 32 leaves the input unresolved. This budget is a finite experimental choice. The proof accounts for enumerating the required budgets and divisors in general. [Independent finite checks](../tests/test_exceptional_weights.py)

```sh
python3 experiments/short_basis_sieve.py 5459 --m 15 --m0 3 --selected 3 5 --compare --exceptional
python3 experiments/short_basis_sieve.py 150235091 --m 15 --m0 3 --selected 3 5 --compare --exceptional
python3 experiments/exceptional_weights.py 1900014700027 --m 330 --d 10 --weight-cap 20 --gap-bound 40 --baby-width 8
```

Two related checks explain why the gain comes from treating the weights differently. Choosing jointly optimized translations on many primes still has the same minimum full-period table size as optimizing each prime separately. Allowing a giant-specific reflection can replace one eligible local table by a single square class. For primes 7, 11 and 19 the exact size drops from 560 to 400 per period, a constant-factor saving. [Translation theorem](coupled-image-sieve.md) · [Reflection theorem and finite count](reflected-image-sieve.md)
