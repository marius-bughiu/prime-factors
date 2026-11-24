# A factor from two elliptic-curve coefficients

For $N=65$, two sums computed from $65$ alone give $-12$ and $24$. Squaring and adding gives $720$, whose greatest common divisor with $65$ is **5**. Changing one public parameter gives $-12$ and $-8$, which return the other prime, **13**. The same formula works whenever both hidden primes are 1 modulo 4. The expensive part is evaluating the sums. The direct method still needs about $N$ symbol evaluations. [Lean proof](../PrimeFactors/QuarticTrace.lean) · [Implementation](../experiments/quartic_trace.py)

## The formula

Suppose $N=pq$ with distinct odd primes. Choose an integer $d$ with public Jacobi symbol $(d/N)=-1$. Such a $d$ is a square modulo exactly one hidden prime. A uniformly sampled unit has the required sign with probability $1/2$, and encountering a nonunit can itself reveal a divisor. Define

$$A_N(c)=\sum_{x=0}^{N-1}\left(\frac{x(x^2-c)}{N}\right).$$

If $p,q\equiv1\pmod4$, then $\gcd(N,A_N(1)^2+A_N(d)^2)$ equals the prime at which $d$ is a nonsquare. The other factor is the quotient. The formula accepts the two sums reduced modulo $N$. When using integer sums on $65$, $d=3$ selects 5 and $d=11$ selects 13. If either hidden prime is 3 modulo 4, every one of these sums is zero. For instance, $N=77$ and $d=2$ give zero twice. [Checked factor-selection theorem](../PrimeFactors/QuarticTrace.lean)

## Why one prime divides the answer

For a prime $r$, write $T_r(c)$ for the same sum with denominator $r$, and $\chi$ for the Legendre symbol at $r$. The Chinese remainder theorem gives $A_N(c)=T_p(c)T_q(c)$. Replacing $c$ by $u^2c$ for $u\ne0$ multiplies $T_r(c)$ by $\chi(u)$. Consequently the square of the sum is constant within each of the two square classes. If $r\equiv3\pmod4$, the terms at $x$ and $-x$ cancel.

When $r\equiv1\pmod4$ and $d$ is a nonsquare, an exact identity gives

$$T_r(1)^2+T_r(d)^2=4r.$$

To see it, sum $T_r(c)^2$ over all $c$. For any $u,v$, the correlation $\sum_c\chi(u-c)\chi(v-c)$ is $r-1$ when $u=v$ and $-1$ otherwise. On expanding the square, the constant $-1$ contributes zero since $\sum_x\chi(x)=0$. The surviving sum is $r\sum_{x^2=y^2}\chi(x)\chi(y)$. Each nonzero $x$ admits $y=x,-x$ and both signs contribute one because $\chi(-1)=1$. Thus the second moment is $2r(r-1)$. The $c=0$ term vanishes and each nonzero square class has $(r-1)/2$ members. This proves the identity. [Checked character correlation](../PrimeFactors/PhaseCharacters.lean) · [Second moment and exact norm](../PrimeFactors/QuarticTrace.lean)

For definiteness, let $d$ be a nonsquare at $p$ and a square at $q$. Then $T_q(d)^2=T_q(1)^2$ and

$$A_N(1)^2+A_N(d)^2=4p\,T_q(1)^2.$$

The norm identity at $q$ also proves that $q$ cannot divide $T_q(1)$. Otherwise it would divide both coordinates, so $q^2$ would divide $4q$. This gives the exact gcd. At the base parameter the only zero terms are $0,1,-1$. The remaining terms occur in equal pairs at $x,-x$, proving $T_r(1)\equiv2\pmod4$. This fixes which of the half-trace coordinates in the representation of $r$ is odd. It also gives a three-bit test for coverage. For any product of distinct odd primes, $A_N(1)\equiv4\pmod8$ holds exactly when both primes are 1 modulo 4. Computing those three bits cheaply from $N$ alone remains open here. [Formal proof](../PrimeFactors/QuarticTrace.lean)

## What it costs to obtain the two numbers

For the curve $E_c:y^2=x^3-cx$, the prime-index Fourier coefficient is $-T_r(c)$ at each odd prime $r$ with $r\nmid c$, where this displayed model has good reduction. At a squarefree index $pq$ coprime to $2c$, the two minus signs cancel and the coefficient is $A_N(c)$. For $r\equiv1\pmod4$ the local values are the signed doubles of the two coordinates of $r$ as a sum of squares. These prime-field trace formulas are classical. Their usual fast evaluation takes the prime $r$ as input. Bach and Charles gave a separate reduction using the coefficients of one eigenform at $N$ and $N^2$. Our formula uses the single index $N$ on two related curves. [Walsh’s prime-field trace formula](https://ami.uni-eszterhazy.hu/uploads/papers/finalpdf/AMI_55_from184to188.pdf) · [Bach and Charles](https://arxiv.org/abs/0708.1192)

On a covered input the terms at $x$ and $-x$ agree globally, so the direct evaluator takes $(N-1)/2$ positions for both sums, or $N-1$ Jacobi evaluations altogether. A 2,048-bit product requires at least $2^{2046}$ positions. A short prefix does not determine either complete sum. A quick evaluator at an **unfactored composite index** would advance this route. Lower output precision saves storage while the direct sum still visits the same positions. [Bounded implementation](../experiments/quartic_trace.py)

Projective point counts provide a different way to see where factor information enters. Across the four local quadratic-twist sign patterns, their sum is $4(p+1)(q+1)$. Across the same patterns the affine counts sum to $4pq$. The difference comes from points at infinity at one or both primes. A point at infinity at just one prime already reveals it through the gcd of its projective coordinate $Z$ with $N$. For ordinary quadratic twists, the Fourier coefficient at $N$ merely gets multiplied by the public Jacobi sign. The change $x^3-x\mapsto x^3-dx$ used above is a quartic twist that exchanges one local squared trace with its complementary value. [Dieulefait and Jiménez Urroz, equations (1) and (2)](https://www.mdpi.com/2227-7390/8/12/2126)

## A limitation shared by all rational CM elliptic curves

Adding more fixed imaginary quadratic fields still leaves a positive proportion of prime pairs on which every coefficient at the product vanishes. Include $\mathbb Q(i)$ with the chosen fields and let their compositum have degree $2^r$. Complex conjugation acts nontrivially on every imaginary quadratic subfield. A prime with this Frobenius element is inert in all the chosen fields and is 3 modulo 4. Conversely those signs on the generators specify that single element. Chebotarev gives it density $2^{-r}$ among primes. In this abelian case, the prime number theorem in fixed arithmetic progressions also gives the density. At an inert prime of good reduction, a CM elliptic curve has Frobenius trace zero. [Chen, Park and Swaminathan, final remark](https://arxiv.org/pdf/1506.09170) · [Prime-counting asymptotic, Appendix A](https://academic.oup.com/qjmath/article/74/4/1505/7240642)

Draw distinct primes uniformly without replacement from the primes $3\bmod4$ in $[X,2X)$ and let $X$ tend to infinity through powers of two. Exclude the finitely many ramified and bad primes of any fixed menu of curves. Subtracting the prime-counting asymptotics at $2X$ and $X$ gives a limiting proportion $s=2^{1-r}$ of eligible primes inert in all fields. The probability that either chosen prime is in this set tends to $2s-s^2$. On all these products the first coefficient of every curve vanishes. The probability that *both* primes are in the set tends to $s^2$. In that case even the coefficients at every power of $N$ are determined by $N$ alone. At an inert prime the Hecke recurrence gives $a_{p^{2k}}=(-p)^k$ and $a_{p^{2k+1}}=0$, so $a_{N^{2k}}=N^k$ and $a_{N^{2k+1}}=0$. These are limiting proportions for the stated sampling rule. [Checked recurrence](../PrimeFactors/QuarticTrace.lean) · [Hecke coefficients and multiplicativity](https://arxiv.org/abs/0708.1192)

There are only nine possible CM fields for elliptic curves over $\mathbb Q$. Their square classes are generated independently by $-1,-2,-3,-7,-11,-19,-43,-67,-163$. The prime supports distinguish the last eight, and $-1$ gives the remaining sign. Using all nine yields $s=1/256$. Thus a limiting fraction at least **511/65,536** of these prime pairs has zero coefficient at $N$ for *every* rational CM elliptic curve of good reduction at both primes. On at least **1/65,536** of the pairs the same public formulas hold at every power of $N$. Choosing such curves after reading $N$ cannot change these simultaneous zero traces. [Classification of rational CM curves, §1 and Table 3](https://www.sciencedirect.com/science/article/pii/S0022247X24011144) · [A count over a quadratic algebra that escapes the zero traces](quadratic-extension-trace.md)
