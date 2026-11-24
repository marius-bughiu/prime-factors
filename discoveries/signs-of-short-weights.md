# How many sign patterns occur on the actual search rows?

A shared sieve table must cover the quadratic-image classes of the rows it serves. Its size could fall substantially if most sign patterns were absent from the actual shortest vectors. For the one-interval arithmetic search, we can now bound those frequencies using Burgess’s character-sum estimate. The result is a paper deduction from that theorem and elementary finite counts. [One-interval factoring algorithm](wide-modulus-sieve.md) · [Burgess’s bound, equation (1)](https://arxiv.org/pdf/1203.5219#page=1)

Let $m$ be a growing primorial with largest prime $B$. The only public number needed for this count is $N$ coprime to $m$; it need not have known factors. For each unit $\sigma\bmod m$, choose **any** nonzero integer vector satisfying
$$b\sigma^2\equiv aN\pmod m,\qquad |a|,|b|\le C\sqrt m,$$
for a fixed $C$. A shortest Euclidean vector meets this bound. The selected primes $\mathcal S$ are the odd divisors of $m$ above $\sqrt B$; write $t=|\mathcal S|$. Where $a$ is nonzero modulo a selected prime, completing the square in the next trace digit gives the sign $\chi_\ell(aN\sigma^{-3})$. A sign is called degenerate when the coefficient vanishes. Let
$$\mathcal S' = \{\ell\mid m:\ell>B/(\log B)^2\},\qquad k=|\mathcal S'|.$$
For large $B$ this lies inside $\mathcal S$ and $k=t-o(t)$.

**Result.** A proportion $1-o(1)$ of the unit rows has no degeneracies on $\mathcal S'$. On those rows each specified vector of $k$ signs occurs at most $O_C(\varphi(m)/2^k)$ times. In particular an absolute fraction (depending only on $C$) of all $2^k$ patterns appears. This holds uniformly in $N$ and for any choice among eligible vectors. Removing the exceptional rows from the published search preserves these conclusions about sign support because the removed fraction tends to zero.

## Counting one pattern while charging every possible weight

Write $d=\gcd(|a|,|b|,m)$, $r=m/d$, $u=a/d$, $v=b/d$. Both normalized weights are units modulo $r$. Given $u,v$, a possible row satisfies $v\sigma^2=uN\bmod r$. Each unit solution modulo $r$ has exactly $\varphi(d)$ unit lifts modulo $m$ by squarefreeness. Up to this factor the number of candidate rows is bounded by a sum over the entire square $|u|,|v|\le U=\lfloor C\sqrt m/d\rfloor$.

At any odd prime of $r$, set $z=v\sigma$ and $x=uvN$. The row equation becomes $z^2=x$. Its leading sign is $\chi_\ell(d)\chi_\ell(z)$. Thus a required sign fixes a sign $\epsilon$ for $z$. For unit $x$ the local numbers of admissible roots are

| Requirement | Root count |
| --- | --- |
| No specified sign | $1+\chi(x)$ |
| Specified sign, $\ell\equiv3\pmod4$ | $(1+\chi(x))/2$ |
| Specified sign, $\ell\equiv1\pmod4$ | $(1+\chi(x)+\epsilon(\psi(x)+\overline{\psi(x)}))/2$ |

Here $\chi$ is the Legendre character and $\psi$ is a quartic character with $\psi^2=\chi$. In the second case the two roots of a nonzero square have opposite signs. In the third they have the same sign, which equals $\psi(x)$ since $x=z^2$. For the prime two there is one root for a unit. Extend the constant term in each formula as the principal character, zero on nonunits. Then the product counts precisely the eligible pairs over all integer weights, discarding any pair with a nonunit weight at a prime of $r$. [Finite change of root variable and character sum identities](../PrimeFactors/ActualSigns.lean)

Prescribe signs on any $j$ primes of $r$ from the selected set. Expanding the product gives at most $4^{\omega(m)}$ terms. There is exactly one completely principal term, and every coefficient has absolute value $2^{-j}$. In the sum over $u,v$ each term separates as $\xi(N)(\sum_{|u|\le U}\xi(u))^2$ for a character $\xi\bmod r$. It is the square of a possibly complex sum; bounding its absolute value by the squared magnitude suffices.

Suppose $d\le m^{1/16}$, so $U\gg_C m^{7/16}$. The principal sum counts the integers in the interval coprime to $r$, hence equals $(2U+1)\varphi(r)/r+O(2^{\omega(r)})$ by inclusion–exclusion. For a nonprincipal term let $a_0>1$ be its conductor. Its active local factors give a primitive character modulo the squarefree $a_0\mid r$. Inclusion–exclusion for the other primes contributes at most $2^{\omega(m)}$ shorter sums. For a term with extra divisor $e$ the interval has positive and negative parts of length at most $U/e$; terms with $e>U$ vanish. Applying Burgess with index two bounds each signed sum by $O_\delta(U^{1/2}m^{3/16+\delta})$. Full periods of a primitive nonprincipal character sum to zero if an interval exceeds its modulus. Consequently even after summing all the nonprincipal terms the error inside the common factor $2^{-j}$ is $O_\delta(U m^{3/8+2\delta+o(1)})$.

For fixed sufficiently small $\delta$, this error saves a fixed positive power of $m$ against $U^2$. It also saves a power against $U^2(\varphi(r)/r)^2$, since $r/\varphi(r)=m^{o(1)}$. Including unit lifts, the count of rows of exact content $d$ with the prescribed signs is at most
$$
  \ll_C 2^{-j}\varphi(d) U^2(\varphi(r)/r)^2
  \ll_C 2^{-j}\,m(\varphi(m)/m)^2/\varphi(d). \tag{1}
$$
This upper bound counts every possible short pair for each row. The procedure can choose its vector as a function of all its public data. For $d>m^{1/16}$ the earlier root-and-lift count gives $O_C(m^{15/16}3^{\omega(m)})$ rows in total. That total is $o(\varphi(m)2^{-t})$ because $t,\omega(m)=O(\log m/\log\log m)$. [Finite large-content row bound](wide-modulus-sieve.md#counting-the-rows-that-need-all-their-candidates)

## From rows to sign support

For squarefree $m$, $\sum_{d\mid m}1/\varphi(d)=m/\varphi(m)$. Requiring $\ell\mid d$ multiplies this sum by $1/\ell$. Apply (1) with $j=0$, then sum over the primes in $\mathcal S'$. The proportion of rows degenerate anywhere on $\mathcal S'$ is at most $O_C(\sum_{\ell\in\mathcal S'}1/\ell)+o(1)=o(1)$. The reciprocal sum is $O(\log\log B/\log B)$ by partial summation and the elementary bound $\pi(x)=O(x/\log x)$.

Next apply (1) with $j=k$ for a specified sign vector and sum over contents coprime to the product of $\mathcal S'$. Enlarging the reciprocal-totient sum to all divisors yields $O_C(\varphi(m)2^{-k})$. Dividing the number of nondegenerate rows by this capacity gives the asserted support. The omitted selected primes have product at most $\exp(O(B/(\log B)^2))=\exp(o(t))$ by the Chebyshev prime-sum bound. These facts hold for all sufficiently large $m$, without assuming independence of the signs.

In the actual 63-bit benchmark all 16 patterns occurred on its four selected primes; their frequencies ranged from 128 to 232 among 2,912 nondegenerate rows. The 79-bit benchmark also had all 16, with frequencies from 3,680 to 4,640 among 65,024 such rows. These finite counts use the lattice, not knowledge of either prime divisor of $N$. [Public products and parameter sets](../benchmarks/wide-modulus.json)

## Consequence for the arithmetic search

Consider the model that explicitly lists one shared baby table covering each ordinary row’s **complete Cartesian product of local images in full periods**, allowing arbitrary row-specific translations. On $\mathcal S'$ the sign-mass theorem bounds the minimum union for a set of patterns by its fraction of the sign cube times the full two-sign union. The support bound just proved makes this fraction bounded below. Projecting away the remaining selected coordinates can only lose their total modulus as a factor in the density. Thus the required fraction of a full period is at least
$$\exp[-t\log(4/3)-o(t)].$$
For the one-interval construction the matching upper bound is $\exp[-t\log(4/3)+o(t)]$. This is a statement about the actual rows of the arithmetic search, including the choice of short weights. [Sign-mass theorem](grouped-images.md) · [Compression for arbitrary translations](coupled-image-sieve.md)

In this model a complete sweep needs at least $\varphi(m)$ giant records and its prescribed exponent window has width comparable to $\sqrt N/m^{3/2}$. Where the width is much larger than the period $M\le m$, all translated intervals share all but $O(1)$ full periods in a central overlap. For growing primorials, $t=(1+o(1))\log m/\log\log m$. These constraints match the secondary constant $2\log(4/3)/25$. In detail, write $c=2\log(4/3)/25$, $L=\log N$, $E=L/\log L$. To beat this constant by a fixed $\eta>0$, the giant count would require $\log m\le L/5-(c+\eta)E+o(E)$. Then $t\le(1/5+o(1))E$, the window is much larger than $m$, and the necessary baby count has logarithm at least $L/5+3(c+\eta)E/2-\log(4/3)E/5-o(E)=L/5-cE+3\eta E/2-o(E)$. Bounded moduli already require windows of order $\sqrt N$. This excludes such an improvement in the specified model.

The bound concerns explicit complete-image coverage of every ordinary row. A search might exploit information tying coordinates to the actual hidden prime, represent a table implicitly, use a shorter interval derived from the product, or exit with a factor in setup. None of those behaviors requires the coverage used in this proof.
