# A smaller positive factor remainder from the shape of the factor curve

For the two 2,048-bit comparison products, one can lower the required factor remainder by **one more bit** and still guarantee a quartic with at most four candidate factors for each chosen class. The crossed product needs a remainder modulo $2^{611}$ and the fresh product modulo $2^{610}$. This halves the leading term in the number of positive remainder classes to try for each input. Picking the correct class remains open. The improvement is an existence result from Minkowski's theorem. Lean checks the coordinate identities and the exact numerical inequalities. [Previous positive-window bound](centered-factor-sum.md) · [Lean checks](../PrimeFactors/ChebyshevQuarticScale.lean)

## A coordinate for both orders of the factors

Let $xy=N$ with positive factors of equal bit width. Put $S=x+y$, $K=2\sqrt N$, and choose a public $W>0$ for which $K\le S\le K+W$. With both factors at most $U$ and $U\ge\sqrt N$, the larger factor lies on the increasing part of $z+N/z$. Thus the integer $S$ is at most $U+\lfloor N/U\rfloor$. Our examples use $U=2^{1024}-1$ and $W=U+\lfloor N/U\rfloor-\lfloor\sqrt{4N}\rfloor$.

Define $D=\sqrt{W(2K+W)}$ and

$$
t=\operatorname{sgn}(x-y)\sqrt{(S-K)/W},\qquad
h(t)=\sqrt{(2K+Wt^2)/(2K+W)}.
$$

Then $|t|\le1$, $0<h\le1$, $S=K+Wt^2$, and $x-y=D\,h(t)t$. The last equality follows by squaring and checking the sign. At $x=y$ both sides vanish. Interchanging the factors changes the sign of $t$.

Let $T_j$ be the Chebyshev polynomial with $T_j(\cos\theta)=\cos(j\theta)$. Every quartic factor trace is an integer combination of $1,S,x,S^2,Sx$. This coordinate change from $1,x,y,x^2,y^2$ is unimodular on $xy=N$, since $y=S-x$, $x^2=Sx-N$, and $y^2=S^2-Sx-N$. The new real representation is

$$E(t)+h(t)O(t),\qquad E=a_0T_0+a_2T_2+a_4T_4,\quad O=a_1T_1+a_3T_3.$$

Order the trace terms as $1,S,x,S^2,Sx$ and the output functions as $T_0,T_2,hT_1,T_4,hT_3$. The coefficient matrix is triangular in these orders. Its diagonal entries are $1,W/2,D/2,W^2/8,DW/8$. For example $Sx=S^2/2+(D/2)(K+3W/4)hT_1+(DW/8)hT_3$. The absolute determinant from integer trace coordinates to real Chebyshev coefficients is therefore $W^4D^2/256$. [Coordinate expansions](../PrimeFactors/ChebyshevQuarticScale.lean)

## The volume that certifies a short trace

Write $\|E\|$ and $\|O\|$ for their separate suprema in absolute value on $[-1,1]$. If $\|E\|+\|O\|<M$, then every eligible trace has absolute value less than $M$ for either factor order. Both component norms allow cancellation between coefficients.

For the even terms set $z=T_2(t)$. The even unit ball consists of $(a,b,c)$ for which $|a+bz+c(2z^2-1)|\le1$ on $[-1,1]$. By overall sign and reflection in $z$ it suffices to integrate over $b,c\ge0$. For $b\ge4c$ the quadratic is increasing. The allowable interval in $a$ has length $2(1-b)$ for $0\le b\le1$, giving volume $1/12$ in this region. For $0\le b\le4c$ the minimum is at $z=-b/(4c)$ and the maximum is at $z=1$. Set $v=b/(4c)$. Then $0\le v\le1$, $0\le c\le(1+v)^{-2}$, and the length in $a$ is $2[1-c(1+v)^2]$. Including the Jacobian $4c$ gives $(4/3)\int_0^1(1+v)^{-4}\,dv=7/18$. Multiplying the sum by four gives even volume $17/9$, or $17/12$ times the three-dimensional absolute-sum unit ball.

For the odd terms the two equal-sign quadrants each have area $1/2$, since the largest absolute value occurs at $t=1$ or $-1$. In an opposite-sign quadrant write the polynomial as $r t-s(4t^3-3t)$ with $r,s\ge0$ and put $v=r/s$. For $0\le v\le9$ the squared supremum is $s^2(v+3)^3/27$, from the critical point $t^2=(v+3)/12$. It dominates the squared endpoint value because $(v+3)^3-27(v-1)^2=v(v-9)^2$. For $v\ge9$ the supremum is $s(v-1)$. The area of one such quadrant is

$$\frac12\left(\int_0^9\frac{27\,dv}{(v+3)^3}+\int_9^\infty\frac{dv}{(v-1)^2}\right)=\frac{49}{64}.$$

The odd unit ball has area $81/32$, or $81/64$ times the two-dimensional absolute-sum unit ball. For the five-dimensional body $\|E\|+\|O\|<1$, integrate the odd-ball radius $1-\|E\|$ over the even ball. Its volume is $3!2!/5!$ times the product of the two component volumes. Thus it is $459/256$ times the ordinary five-dimensional absolute-sum ball of volume $2^5/5!$.

For dyadic $R\ge8$, put $M=360R^4$ and assume $\gcd(N,30)=1$. Fix a proposed factor remainder $u$. The integral trace vectors whose twelve local labels vanish form a full-rank sublattice. Each label is linear modulo its component modulus. Its index is the size of the image, at most $466560000R^{10}=M^5/(12960R^{10})$. After the real coordinate change its covolume is at most that index times $W^4D^2/256$. Minkowski's theorem puts a nonzero lattice vector in the open radius-$M$ body whenever

$$\boxed{120\,W^4D^2 < 12960\cdot459\,R^{10}.}$$

At a true factor $x\equiv u\bmod R$, the label congruences make $x^2$ times its trace divisible by $M$. Both factors are units modulo $M$, so the trace is divisible by $M$. Its strict bound forces zero. A nonzero trace vector gives a nonzero polynomial of degree at most four, so this same polynomial covers at most four integer candidates. [Linear local labels and divisibility](../PrimeFactors/QuarticUnitLabels.lean) · [Trace-to-polynomial proof](../PrimeFactors/QuarticFactorLane.lean) · [Minkowski's convex body theorem](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Group/GeometryOfNumbers.html#MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure)

## Exact comparisons on the public products

For an all-integer comparison, put $k=\lfloor\sqrt{4N}\rfloor$ and bound $D^2$ above by $W(2(k+1)+W)$. The margin is the right side of the boxed inequality divided by this integer upper bound on its left side. Only the public product and common factor bit width enter the calculation.

| 2,048-bit product | Previous sufficient exponent | New sufficient exponent | Lower bound on the margin |
| --- | ---: | ---: | ---: |
| Crossed comparison | 612 | 611 | 1.03416 |
| Fresh comparison | 611 | 610 | 1.36682 |

Lean checks both successful integer comparisons and the failure of the same sufficient test one exponent lower on each product. The volume integrations and the application of Minkowski to this coordinate change are paper proofs. The calculation establishes existence for every remainder on these two inputs. Constructing a qualifying vector, isolating its roots and choosing the right class are separate computational costs. [Public product inputs](../benchmarks/quartic-factor-lanes.json) · [Exact scale, transformation and numerical certificates](../PrimeFactors/ChebyshevQuarticScale.lean)

## What the solver actually recovered

We kept the previously frozen remainder $u=1$, ran the existing centered lattice reduction, and tested all five returned rows. For each raw polynomial $F$ we checked that both $Mx^2-F(x)$ and $Mx^2+F(x)$ are strictly positive throughout the closed real factor interval. This directly bounds the trace $F(x)/x^2$ on the hyperbola $xy=N$. The checker tests both endpoints for strict positivity and uses a Sturm sequence to count roots in the interior. Zero at even a single point rejects the row. The divisions use integer arithmetic, normalizing remainders by positive factors to keep the required signs. An accepted polynomial then undergoes the 15 local congruence checks and an integer-root search. [Probe](../experiments/chebyshev_quartic_window.py) · [Sturm's theorem](https://isa-afp.org/entries/Sturm_Sequences.html)

| Product | Exponent tested | Rows passing old bound | Rows passing curve test | Result for remainder 1 | Search time |
| --- | ---: | ---: | ---: | --- | ---: |
| Crossed | 611 | 3/5 | 4/5 | One root, both primes recovered | 2.02 s |
| Crossed | 610 | 0/5 | 0/5 | Unresolved | 2.17 s |
| Fresh | 610 | 2/5 | 4/5 | No integer root, class ruled out | 2.36 s |
| Fresh | 609 | 0/5 | 0/5 | Unresolved | 2.32 s |

For the selected crossed polynomial the old bound was $0.6653M$ to four decimal places rounded down. Its actual maximum absolute trace was in $[0.498M,0.499M)$. For the fresh polynomial the corresponding figures were $0.6418M$ and $[0.560M,0.561M)$. These enclosures use the same exact positivity test at successive rational thresholds. The curve test admitted three additional rows across the four runs. Both full-size outcomes at the proved exponents were already obtainable from other rows that passed the old bound. At the two smaller exponents the procedure tested no class to completion. All five rows failed, leaving even remainder 1 open.

The crossed run independently generated and kernel-checked the factorization in a further 7.43 s. The certificate proves the product and both primes, and its axiom audit passed. The fresh input remained wholly unresolved as a factorization, with $2^{608}-1$ positive groups still unchecked at exponent 610. Remainder 1 was originally chosen after inspecting the crossed example and frozen before generating the fresh product. Each run used only the public product, the specified remainder and the radix. Reproduce the full run, including Lean verification, with `python3 -m experiments.chebyshev_quartic_window`. [Full traces, root counts, certificate digest and timings](../research/chebyshev-quartic-window.json)

On a separate bounded comparison we multiplied each of the nine smallest 13-bit primes by each of the nine largest and tested every positive reciprocal group modulo 16. Across 81 products and 366 groups, the old bound certified 210 groups and recovered the pair on 42 products. The curve test certified 253 groups and recovered the pair on **47 products**. The same five rows were available to both checks on every group. The prime labels were used only to validate results. A further regression compared 48 oriented remainders with direct division, including a product with several equal-width decompositions. Reproduce the bounded comparison with `python3 -m experiments.chebyshev_quartic_window --small`. [Regression checks](../tests/test_chebyshev_quartic_window.py)
