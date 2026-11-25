# How often a quadratic power comparison reveals a prime

A public quadratic equation can have two roots at one unknown prime and none at the other. Can we detect that difference by raising a random value to the power of the product? On 899, the shift 8 exposes the prime 29 this way. On **every** product of two distinct 1,024-bit primes, one uniformly random shift has probability **less than one in $2^{509}$** of exposing either prime in the norm test below. This bound applies separately to each input, including specially chosen prime pairs. [Lean proofs and example](../PrimeFactors/FrobeniusShiftCount.lean)

The same power comparison also gives an exact formula for a hidden prime. On 77, counting all pairs gives the numbers **9 and 57**, from which the formula returns **11**. Directly evaluating those counts takes $N^2$ pairs. A simpler count described below gives the other prime in $N$ positions. [Count identities](../PrimeFactors/FrobeniusFixedCounts.lean)

## The product-only test

Given the odd product $N$, choose $D$ with public Jacobi symbol $(D/N)=-1$. A random unit gives such a selector with probability one half. Fix a unit $k$ in the quadratic algebra modulo $N$ with $w^2=D$, for example $k=1$. Both $D$ and $k$ may depend on $N$. Draw $a$ uniformly modulo $N$. Compute

$$z=(a+w)^N-k(a-w)=u+vw,\qquad g=\gcd(u^2-Dv^2,N).$$

A proper gcd gives an exact factor. Repeated squaring needs $O(\log N)$ multiplications of pairs of residues for each shift. This conjugate comparison is related to quadratic Frobenius primality tests. Here success requires a proper factor from the norm gcd. [Grantham, *A Probable Prime Test With High Confidence*](https://arxiv.org/abs/1903.06823)

For $N=899$, take $D=-1,k=1$ and $a=8$. The computed power is $285+655w$, and $z=277+656w$. Its norm has gcd **29** with 899, while the shift itself is coprime to 899. Lean verifies the full modular power using $w^2=-1$, the gcd, and primality in $899=29\cdot31$. An exhaustive count for this example gives 150 shifts returning 29, 24 returning 31, five returning 899 and 720 returning 1. The successful local shift residues are $0,8,14,15,21$ modulo 29 and $0$ modulo 31. These finite counts also follow by testing the two roots $\pm12$ of $-1$ modulo 29. At 31 the translated point has to be a 28th root of unity, of which there are four in the quadratic field. Only $-w$ lies on the line $a-w$. [Power and factor certificate](../PrimeFactors/FrobeniusShiftCount.lean)

## Counting shifts at the two primes

Call the split prime $p$ and the other prime $q$, in either size order. At $p$ write $r$ for either square root of $D$. Under the embedding $w\mapsto r$, the selected unit maps to a nonzero scalar $A$. Write $x=a+r$. Vanishing in this embedding requires

$$x^q=A x+B,\qquad B=-2Ar\ne0.$$

A root is nonzero. For distinct roots $ty,y$ with ratio $t\ne1$, substitution gives $(t^q-t)Ay=(1-t^q)B$. If $t^q=t$, this forces $t=1$. Otherwise the ratio determines $y$ uniquely, and hence determines the ordered pair. If there are $s$ roots, their $s(s-1)$ ordered pairs have distinct ratios in the field of $p$ elements. Thus $s(s-1)\le p$ for each of the two embeddings.

At $q$ use the quadratic field. Its Frobenius sends $w$ to $-w$, so $v=a-w$ must satisfy $v^{p-1}=k$. The ratio of any two such points is a $(p-1)$st root of unity. Again the ratio determines the pair. Indeed, if $(a-w)/(b-w)=(c-w)/(d-w)$, comparing coefficients of 1 and $w$ gives $a+d=c+b$ and $ad=cb$. For $a\ne b$ these equations give $a=c,b=d$. Hence $t$ successful shifts at this prime satisfy $t(t-1)\le p-1$. This is the distinct-ratios property of a line in a quadratic field extension used in the Bose–Chowla construction. [Quadratic Frobenius formula](../PrimeFactors/JacobiSeparation.lean) · [Nathanson on the Bose–Chowla argument](https://arxiv.org/abs/2104.12711)

Both primes are at least $2^{1023}$ and $p<2^{1024}$. Each of the three local counts is at most $2^{512}$, since $(2^{512}+1)2^{512}>p$. A union bound over the two split embeddings and the inert prime gives probability at most $3\cdot 2^{512}/2^{1023}<2^{-509}$. Counting gcds equal to $N$ as successes could only increase this bound. Lean checks both local cardinality bounds, their power reductions, and this finite inequality. The decomposition into the two fields and the lift of each residue class modulo $N$ are the paper steps connecting them. [Checked bounds](../PrimeFactors/FrobeniusShiftCount.lean)

For a menu of $J$ preselected units per shift, the upper bound is $J\,2^{-509}$. A fresh uniform shift on every trial gives the same conditional bound even if earlier trials determine the next selector and menu. A method that directs the shift toward the unknown successful residues, or uses the coordinates of the result separately, needs its own analysis.

## Two counts determine the split prime

Keep $D$ and set $k=1$. This time let $z$ range over all $N^2$ elements $u+vw$ of the algebra, including zero divisors. Write $\bar z=u-vw$. Let $K$ be the number for which $z^N=\bar z$. Let $C$ be the number for which the **norm** of $z^N-\bar z$ vanishes modulo $N$. The extra solutions of the second test contain information about the split prime.

At the split prime, identify $z$ with $(x,y)$ and conjugation with the swap. Since Frobenius fixes the prime field, the two component equations are $x^q=y$ and $y^q=x$. Their graphs each have $p$ points. Their intersection has $t=1+\gcd(p-1,q^2-1)$ points, since $x^{q^2}=x$ permits zero and the $(q^2-1)$st roots of unity. Thus their union has $2p-t$ points. At the other prime the algebra is a field, so norm zero and equality to zero coincide. With $v=\bar z=z^q$ the test is $v^p=v$. That again has $t$ solutions, because the quadratic field has $q^2-1$ nonzero elements in a cyclic group. CRT now gives

$$K=t^2,\qquad C=(2p-t)t,\qquad p=\frac{C/\sqrt K+\sqrt K}{2}.$$

Lean proves the graph intersection and union, the finite-field fixed-point count, and the integer decoder. The CRT multiplication of the two local counts is a paper argument. On $N=77$ we enumerated all 5,929 pairs using repeated squaring for each power. For $D=3$ the measured counts were $K=9,C=57$, giving $(57/3+3)/2=11$. For $D=2$ the counts were $K=C=49$, giving 7. Switching the selector can switch which factor the formula returns. [Lean count and decoding lemmas](../PrimeFactors/FrobeniusFixedCounts.lean)

If both coordinates of $z$ are sampled uniformly, the same counts give the exact chance of a proper gcd. Put $s=(2p-t)/p^2$ and $e=t/q^2$. The two local events are independent by CRT, so the probability that exactly one occurs is $s+e-2se$. For 1,024-bit primes this is less than $2^{-1021}$, since $t\le p<2q$ gives $s+e<2/p+2/q$. This bound is for uniform sampling over the full quadratic algebra. The earlier fixed-slice result covers the choice $z=a+w$.

### How much information is needed?

For odd primes, $t$ is odd. For $b\ge2$, knowing just $C,K$ modulo $2^{b+1}$ gives $p$ modulo $2^b$ up to sign. First obtain $(C+K)/2=pt$ modulo $2^b$. Enumerate the odd square roots of $K$ modulo $2^{b+1}$ by successively lifting the roots one bit. Their reductions modulo $2^b$ are $t$ and $-t$. Indeed for any such root $s$, the product $(s-t)(s+t)$ is divisible by $2^{b+1}$, and one factor is 2 modulo 4, so the other is divisible by $2^b$. Each candidate root is invertible modulo $2^b$. Dividing the known $pt$ by it gives the two possible residues of the selected prime.

For two 1,024-bit primes, two 513-bit counts would therefore suffice. The same candidate residues give the other prime modulo $2^{512}$ by modular inversion and multiplication by $N$. One of these boundedly many candidates belongs to the larger prime. The usual unknown-divisor small-root theorem applies there with the larger prime at least $\sqrt N$ and its quotient by $2^{512}$ at most $\sqrt2 N^{1/4}$. This reduction says how to use the two counts if they can be evaluated. [Quarter-width factor recovery and hypotheses](quarter-width-count.md)

### What does evaluating the formula cost?

Directly tallying $C$ and $K$ still visits $N^2$ pairs, with $O(\log N)$ quadratic multiplications at each pair. Reducing the tallies to 513 bits reduces storage. It leaves the same enumeration. The order divisor $t-1=\gcd(p-1,N^2-1)$ still depends on the hidden $p$. Computing just its public second argument gives no value for that gcd. An evaluator of both counts at low precision that costs less than existing factor searches remains open.

In comparison, count the $a$ modulo $N$ for which $\gcd(a^2-D,N)>1$. The split prime permits exactly two residues; the inert prime permits none. Consequently this single count is $2q$ and every hit gives $p$ immediately. Even the interval from 0 through $\lfloor p/2\rfloor$ contains one of the two roots modulo $p$. An algorithm can simply try increasing $a$ without knowing this endpoint. This cheaper one-dimensional comparison also requires an enormous search at the target size.
