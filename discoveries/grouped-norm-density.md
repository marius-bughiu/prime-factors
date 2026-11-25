# How many products can pass the grouped norm probe?

With $T=\lfloor\sqrt N\rfloor<U$, the number of distinct inputs that pass the probe has order $U\sqrt U$. The same order holds when the probe may choose its best multiplier or when it must use the single public choice $k=\lfloor(T-1)/(N-T^2)\rfloor$. With $U=2^{1024}$, the upper bound is $18\cdot2^{1536}$. A separate construction gives at least $2^{1519}$ **odd 2048-bit inputs** for which the public choice returns two odd 1024-bit factors. The count allows composite factors. [Lean counting proof](../PrimeFactors/GroupedNormDensity.lean) · [Probe and earlier frequency bound](grouped-norm-frequency.md)

## Distinct inputs from one multiplier

Choose integers $\lceil U/2\rceil\le T<U$ and $1\le u\le\lfloor\sqrt U/4\rfloor$. Set $z=u(u+1)$ and $h=T-z$. Then $2z\le T$, so $0<z\le h$ and $\lfloor(T-1)/h\rfloor=1$. The test accepts because $u(u+1)=1\cdot z$. Its two returned factors are $u^2+h=T-u$ and $(u+1)^2+h=T+u+1$. Their product is $T^2+h$, whose floor square root recovers $T$. Subtracting the square recovers $h$, and $T-h=u(u+1)$ determines $u$ uniquely. Thus the exact rectangle contributes

$$
\left\lfloor\frac U2\right\rfloor\left\lfloor\frac{\sqrt U}{4}\right\rfloor
$$

distinct composite inputs. This is $2^{1533}$ at $U=2^{1024}$ and grows as $U\sqrt U/8$. Every product in this rectangle is even because its factors differ by $2u+1$. [Checked injection, count and successful probes](../PrimeFactors/GroupedNormDensity.lean)

## An odd family at the target bit widths

Take $U=2^{1024}$ and $X=\sqrt U/64=2^{506}$. Choose $0\le j<X$ and an even integer $244X^2\le h<248X^2$. Put $u=1+8j$, $v=1+6j$, $a=4$ and $b=3$. Then $4v=3u+1$, and the two odd factors and their product are

$$
p=u^2+16h,\qquad q=v^2+9h,\qquad N=pq=(uv+12h)^2+h.
$$

Here $u\le8X$ and $v\le6X$, giving $uv\le48X^2\le h$. The public multiplier is therefore 12 and the square test returns exactly $(p,q)$. Both factors exceed $U/2=2048X^2$, since $q\ge2196X^2$ and $p\ge3904X^2$. Both lie below $U=4096X^2$, since $p<4032X^2$ and $q<2268X^2$. Moreover $T=uv+12h\ge2928X^2$ and $2\cdot2928^2>4096^2$, so $U^2/2<N<U^2$. The floor square root and offset recover $T,h$, and $T-12h=(1+8j)(1+6j)$ strictly increases with $j$. All choices therefore give different 2048-bit inputs. There are $X$ choices of $j$ and $2X^2$ of $h$, totaling $2X^3=2^{1519}$. These inequalities also give the same order of growth for scaled cutoffs $U=4096X^2$. Whether both odd factors are prime for many such choices remains open. [Exact Lean theorem for multiplier 12](../PrimeFactors/GroupedNormDensity.lean)

## An upper bound allowing every multiplier

A passing probe yields positive $a,b,h$ and nonnegative $u,v$ with $av=bu+1$ and $T=uv+hab<U$. Fix $a,b$, and write $z=\lfloor u/a\rfloor$. Then $u\ge az$, and $av=bu+1$ gives $v\ge bz$. Consequently $abz^2\le uv<U$. Once $a,b,h,z$ are given, at most one input is possible. For another solution $ay=bx+1$, subtraction gives $x-u=a(vx-yu)$. Equal quotients $\lfloor u/a\rfloor=\lfloor x/a\rfloor$ and equal residues force $x=u$, then $y=v$. [Witnesses from successful probes](../PrimeFactors/GroupedNormFrequency.lean)

Let $d=\lfloor U/(ab)\rfloor$. There are at most $d$ choices of $h$ and $1+\lfloor\sqrt d\rfloor$ choices of $z$. A contributing pair has $d\ge1$, so its contribution is at most $2(U/(ab))^{3/2}$. For every finite upper cutoff $m$, the sum $\sum_{i=1}^{m}i^{-3/2}$ is at most 3. One elementary bound for each term after the first is $i^{-3/2}\le2((i-1)^{-1/2}-i^{-1/2})$, which telescopes. Summing independently over $a,b$ gives at most $2\cdot3^2 U\sqrt U$. Counting multiple possible representations of a product can only increase this upper estimate. [Finite encoding and telescoping bound in Lean](../PrimeFactors/GroupedNormDensity.lean)

## What this says about unknown primes

Among all $N<U^2$, the share that can pass under any multiplier is of order $1/\sqrt U$. For two uniformly selected distinct 1024-bit primes conditioned on their product being 2048 bits, the earlier lower bound on the number of such pairs and the new upper count give a success probability **below $2^{-481}$**, even allowing any multiplier. The odd construction supplies no corresponding lower bound for prime pairs. [Population bound](grouped-norm-frequency.md) · [Checked integer comparison](../PrimeFactors/GroupedNormDensity.lean)
