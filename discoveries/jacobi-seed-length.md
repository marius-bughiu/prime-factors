# How many random bits does one shared Jacobi test need?

For positive $D$, remove from $a$ every prime factor dividing $2D$, with its full multiplicity. Call the remaining odd integer $a_D$ and put $H_D(a)=(D/a_D)$, the Jacobi symbol with $(D/1)=1$. Repeatedly dividing by $\gcd(a,2D)$ computes $a_D$. A square $D$ always produces $+1$.

Fix nonsquares $1\le D,E<2^{2048}$ in distinct rational square classes, so $DE$ is also a nonsquare. Draw one uniform integer $1\le a\le 2^{2202}$ using **2,202 random bits**. For each of the four prescribed sign pairs,
$$
  \left|\Pr[(H_D(a),H_E(a))=(s,t)]-\tfrac14\right|<2^{-40}.
$$
The total variation distance from two independent fair signs is also below $2^{-40}$. The bound holds for each fixed pair, uniformly in its values. Several tests on independently drawn integers can use it one draw at a time. Inputs chosen after the draw require their own argument. In the same square class the values can differ at removed primes, as $H_2(3)=-1$ and $H_{18}(3)=+1$ show.

## Summing over the removed factors

Let $T=8DE$. Write $a=wu$ uniquely with every prime of $w$ dividing $T$ and $\gcd(u,T)=1$. For fixed $w$, each of $H_D(wu),H_E(wu),H_D(wu)H_E(wu)$ equals a sign depending on $w$ times a quadratic character of $u$. Indeed $a_D=w_D u$ and the Jacobi symbol is multiplicative in the denominator. The three characters on the units modulo $T$ correspond to the square classes $D,E,DE$. All are nonprincipal. For a nonsquare $F$ their primitive conductor is the absolute discriminant of $\mathbb Q(\sqrt F)$, which divides $4F$ and hence divides $T$ in these three cases. Extend each character by zero at every nonunit modulo $T$. [Quadratic characters and fundamental discriminants, Conrad, §3](https://math.stanford.edu/~conrad/676Page/handouts/quadchar.pdf)

Suppose every such character $\chi$ satisfies $|\sum_{n\le Y}\chi(n)|\le B_T$ for every $Y\ge1$. Let $Z$ denote any of the three sign variables and let $a$ be uniform on $[1,M]\cap\mathbb Z$. For $0<\theta<1$ the preceding decomposition gives
$$
 |\mathbb E Z|
 \le \frac1M\sum_{w}\min(M/w,B_T)
 \le (B_T/M)^\theta
       \prod_{p\mid T}\frac1{1-p^{-(1-\theta)}}.
$$
The last sum extends over all positive $w$ supported on the primes dividing $T$. It converges because the set of primes is finite. This interpolation bounds the effect of every possible removed factor without imposing a valuation cutoff. Periodicity and the zero complete sum already supply $B_T=T$.

A shorter seed follows from $B_T=2\sqrt T(1+\log T)$, with the natural logarithm. For a primitive nonprincipal character of conductor $f$, its additive Fourier coefficients have magnitude at most $\sqrt f$ and the constant coefficient vanishes. For nonzero frequencies $j$, interval geometric sums are bounded by $f/(2\min(j,f-j))$. Fourier inversion and the harmonic sum bound give $\sqrt f(1+\log f)$ for every partial sum. To induce the character to $T$, impose coprimality to the additional primes in $R=\prod_{p\mid T,\ p\nmid f}p$ by inclusion-exclusion. The resulting $2^{\omega(R)}$ primitive sums each have the same bound. Since $(2/\sqrt p)\le1$ for $p\ge5$, and $(2/\sqrt2)(2/\sqrt3)<2$, one has $2^{\omega(R)}\le 2\sqrt R$. Now $fR\mid T$, which proves the displayed choice of $B_T$. [Pomerance, Pólya–Vinogradov inequality and Gauss sums](https://math.dartmouth.edu/~carlp/pvrev.pdf)

## An exact finite bound for 2048-bit values

Here $T<2^{4099}$ and $B_T<2^{2062}$. For the latter use $\log 2<0.7$ and $2871\sqrt2<4096$. At $\theta=1/2$, the Euler product is less than $2^{30}$. The product of the first 419 primes exceeds $2^{4099}$, so at most 418 primes divide $T$. The Euler factors decrease with the prime. The following integer calculation checks both bounds using $j_p=\lfloor 2^{16}\sqrt p\rfloor$. Replacing $\sqrt p$ by $j_p/2^{16}$ increases the corresponding Euler factor.

```python
from math import isqrt, prod

primes = [p for p in range(2, 2898) if all(p % j for j in range(2, isqrt(p) + 1))]
assert len(primes) == 419 and prod(primes) > 2**4099
scale = 2**16
roots = [isqrt(scale**2 * p) for p in primes[:418]]
assert prod(roots) < 2**30 * prod(j - scale for j in roots)
```

For any bit budget $K$ with $M=2^K$, all three absolute expectations are consequently below $2^{30+(2062-K)/2}$. Taking $K=2202$ gives $2^{-40}$, and $K=2250$ gives $2^{-64}$. With periodicity alone the corresponding lengths are $4239$ and $4287$ bits. If the three expectations are $\beta_1,\beta_2,\beta_3$, a sign pair's probability equals $(1+s\beta_1+t\beta_2+st\beta_3)/4$. Its error is at most $3\max_i|\beta_i|/4$. Cauchy–Schwarz over the four outcomes bounds total variation by $\tfrac12(\beta_1^2+\beta_2^2+\beta_3^2)^{1/2}$.

## Shorter asymptotic ranges

If $D,E\le U$ and $\epsilon>0$ is fixed, Burgess's short character sum theorem yields a power saving in the three biases already for $M\ge U^{1/2+\epsilon}$. For the marginal of one nonsquare $D\le U$, take $T=8D$. The corresponding range is $M\ge U^{1/4+\epsilon}$. The following argument is asymptotic. The 2,202-bit guarantee above uses the explicit Pólya–Vinogradov bound. [Burgess, *On Character Sums and L-Series II*](https://doi.org/10.1112/plms/s3-13.1.524) · [Hasanalizade et al., cubefree moduli](https://arxiv.org/abs/2511.17778)

For any fixed integer $r\ge2$ and $\eta>0$, the primitive cubefree-modulus estimate for an interval of length $Y\ge1$ is $O_{r,\eta}(Y^{1-1/r} f^{(r+1)/(4r^2)+\eta})$. For a fundamental discriminant, the only possible non-cubefree conductor has the form $f=8m$ with $m$ odd squarefree. Split the primitive character modulo $8m$ into its two CRT factors and sum separately on each odd residue class modulo eight. On $n=8j+c$ the factor modulo $m$ becomes $\chi_m(8)\chi_m(j+c\,8^{-1})$, an interval sum of a primitive character modulo $m$ if $m>1$. The four classes cost a bounded factor. If $m=1$, the original character has bounded partial sums by periodicity.

As above, inclusion-exclusion over $R$ contributes at most $2^{\omega(T)}$. Summing the resulting bound at $Y=M/w$ gives
$$
 |\mathbb E Z|\ll_{r,\eta}
 M^{-1/r} f^{(r+1)/(4r^2)+\eta}\,
 2^{\omega(T)}\prod_{p\mid T}(1-p^{-(1-1/r)})^{-1}.
$$
For fixed $r$ the two final factors together are $U^{o(1)}$, since the product of $\omega(T)$ distinct primes is at least $\omega(T)!$ and $T\le8U^2$. For pairs $f\le4U^2$, so choose $r>1/(2\epsilon)$ and then $\eta$ sufficiently small to obtain a negative power of $U$. For a marginal $f\le4U$, $r>1/(4\epsilon)$ suffices. These estimates quantify the randomness required for the Jacobi decisions. Evaluating or finding the surviving factor candidates is a separate arithmetic cost.
