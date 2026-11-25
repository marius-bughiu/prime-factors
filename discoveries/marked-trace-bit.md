# One bit of a marked sum decides quadratic residuosity

Take an odd product $N=pq$ of distinct primes greater than 7. In the [single-mark formula](quadratic-extension-trace.md), the lowest three bits of the complete sum always read **101**. They can be written down from the input promise alone. With two marks, the lowest four bits are always zero. The **fifth bit** answers whether a chosen integer is a square modulo one of the hidden primes. Computing it directly still takes $N^2$ terms. [Lean formulas](../PrimeFactors/MarkedTraceBit.lean)

For example, with $N=143$ and selector $D=5$, the hidden split prime is 11. To ask about 2, marks 46 and 47 give a sum of $-48$, or **16 modulo 32**. Thus 2 is a nonsquare modulo 11. To ask about 3, marks 106 and 107 give zero, so 3 is a square modulo 11. Direct enumeration used $143^2$ terms per sum. Lean also verifies both residues from the general identity. [Checked examples](../PrimeFactors/MarkedTraceBit.lean)

## What changes when two points are removed

Choose any public $D$ with $(D/N)=-1$. Label the primes so that $D$ is square at $p$ and nonsquare at $q$. The same $D$ works for every query below. Put $f(z)=z^3-z$ and $g(z)=(z-a)^2(z-b)^2f(z)$. Use marks $a,b$ whose difference and whose $f$-values are units modulo $N$. Write $G=B_D(g)$ for the sum of the Jacobi symbols of the norms of $g(x+y\sqrt D)$ over $x,y\bmod N$.

Let $u$ and $v$ be the prime-field sums of the Legendre symbols of $f$ at $p$ and $q$ respectively. Write $s_1=(f(a)/p)$ and $s_2=(f(b)/p)$. In the split algebra each of the two coordinates loses the two marked terms. In the field extension every nonzero base-field value has square norm, so the two removed contributions are both one. Consequently

$$G=(u-s_1-s_2)^2(2q-v^2-2).$$

The second factor is always 4 modulo 8. When $q\equiv3\pmod4$, $v=0$. When $q\equiv1\pmod4$, $v\equiv2\pmod4$. The same two alternatives apply to $u$. If $p\equiv3\pmod4$, the square in the first factor is 4 modulo 8 exactly when $s_1=s_2$. If $p\equiv1\pmod4$, it is 4 modulo 8 exactly when $s_1=-s_2$. In the other cases it is zero modulo 8. Together these give

$$G\equiv16\pmod{32}\quad\Longleftrightarrow\quad
\left(\frac{-f(a)f(b)}p\right)=-1.$$

In the original single-mark formula the square factor is odd and the second factor is $2q-v^2-1\equiv5\pmod8$. This gives the fixed low bits stated above. [Full grid and congruence proofs](../PrimeFactors/MarkedTraceBit.lean)

## Choosing the marks for one query

Given any unit $c$ modulo $N$, set $h=-c$. Try $a_0=h t^2$ for $t=1,2,3,4$. Check the gcd of $(1-a_0)(1+2a_0)(2+a_0)$ with $N$. A proper gcd already gives a factor, after which both local characters are easy to compute. Skip a gcd of $N$. At most three trials can fail this way. Modulo $p>7$, the four squares $1,4,9,16$ are distinct and the forbidden values of $a_0$ are $1,-1/2,-2$. A small prime up to 7 can be tested directly.

On a successful trial set $a=(1+2a_0)/(1-a_0)\bmod N$, $b=a+1$. The residues $a-1,a,a+1,a+2$ are units. Indeed their numerators over $1-a_0$ are $3a_0,1+2a_0,2+a_0,3$. Adjacent marks give the identity

$$f(a)f(a+1)=a_0\big(a(a+1)(a+2)\big)^2.$$

The target $-a_0$ differs from $c$ by a unit square. Thus one fifth-bit query decides the Legendre symbol $(c/p)$ at the selected hidden prime. Only the selector search and a bounded number of gcds and modular operations are needed beyond the query. [Checked adjacent-mark identity](../PrimeFactors/MarkedTraceBit.lean)

This also gives a one-query reduction in each direction with composite quadratic residuosity on units of Jacobi symbol $+1$. For such a unit $c$, knowing $(c/p)$ tells whether $c$ is square at both primes. Conversely, to learn $(c/p)$ from a residuosity oracle, query $c$ if its Jacobi symbol is $+1$, or $cD$ if it is $-1$. The selected argument has Jacobi symbol $+1$ and retains $c$'s square class at $p$. This holds for each fixed $N$ and selector. It supplies neither a cheap fifth-bit evaluator nor a classical polynomial-time factoring reduction from a decision oracle. [Goldwasser and Micali’s quadratic-residuosity problem](https://doi.org/10.1016/0022-0000(84)90070-9) · [Corrigan-Gibbs and Wu on hidden-prime Legendre symbols](https://eprint.iacr.org/2024/1252)

## A shorter count gives a comparison

There is already a one-dimensional sum whose third bit decides the same composite residuosity question. For a unit $c$ with $(c/N)=+1$, count the $x\bmod N$ with $\gcd(x^2-c,N)>1$. If $N\equiv1\pmod4$ additionally require $\gcd(x,N)=1$. If $c$ is nonsquare at both primes the count is zero. If it is square at both primes, the two roots at each prime give $2(p+q-2)$ by inclusion-exclusion without the extra restriction, or $2(p+q-4)$ with it. The public choice makes the count **4 modulo 8** in either square case. Its direct evaluation takes $N$ positions. Reaching a position with a proper gcd already gives a factor. The fifth-bit result locates the same information inside an elliptic character sum and does not improve on this simpler evaluation cost.
