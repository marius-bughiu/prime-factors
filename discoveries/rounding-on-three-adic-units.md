# A degree-144 equation for both nonzero residues modulo 3

On a balanced 2,048-bit semiprime, one polynomial of degree at most 144 now covers a prescribed window of $2^{515}+1$ consecutive odd-factor positions. Every eligible divisor in that window gives an integer root. The left endpoint is public, and a single equation covers both possible residues of a prime factor modulo 3. The theorem gives an existence guarantee. It leaves open which window to choose and how quickly a reduction can find the equation. [Checked theorem](../PrimeFactors/ThreeUnitFactorialWindows.lean)

## How the denominator grows

Let $d=c+2x$ be the trial divisor, with $0\le x\le H$ and public odd $c$. Write $z=x+2c$. Since $2d=z+3x$, the public condition $3\nmid N$ guarantees $3\nmid z$ at every divisor of $N$. Hence $y=(z^2-1)/3$ is a nonnegative integer there.

For each degree $i$ write $h=\lfloor i/2\rfloor$ and $e=i-2h$. Consider the two monic integer polynomials

$$P_i(X)=(X)_i,\qquad Q_i(X)=X^e\prod_{j=0}^{h-1}\big((X+2c)^2-1-3j\big).$$

Here $(X)_i=X(X-1)\cdots(X-i+1)$. The first evaluates to $i!\binom{x}{i}$ throughout the interval. The second evaluates to $3^h h!\,x^e\binom{y}{h}$ at the eligible indices. Put $A=i!$, $B=3^h h!$ and $D_i=\operatorname{lcm}(A,B)$. The integers $D_i/A$ and $D_i/B$ are coprime. Take Bézout coefficients so that $uD_i/A+vD_i/B=1$. Then

$$S_i=u(D_i/A)P_i+v(D_i/B)Q_i$$

is monic of degree $i$, and $D_i$ divides its evaluation throughout the eligible set. Both factorial sequences divide their successors, so $D_i\mid D_k$ whenever $i\le k$. This construction uses the classical theory of fixed divisors and generalized factorials. The two explicit polynomials make the construction on the 3-units directly checkable. [Bhargava’s paper on $P$-orderings](https://geodesic.mathdoc.fr/item/JRAM_1997__490_153942/) · [Monic construction and divisibility](../PrimeFactors/ThreeUnitFactorialWindows.lean)

The prime factors of $D_i$ other than 3 come from $i!$, since $h!\mid i!$. Legendre’s formula gives $v_3(i!)\le i/2$, so the exact 3-exponent in $D_i$ is $h+v_3(h!)$. For even $i>0$ the ratio $D_i/D_{i-1}$ is $3i$. For odd $i$ it is $i/3^{v_3(i)}$. At degree 144 the product of the 145 denominators is $3^{2592}$ times the ordinary product of factorials. Taking the $1/10440$ power, the leading-term estimate alone improves the width by a factor of about 1.314. The dyadic comparison below includes the rounding errors.

## Width after rounding

Set $H=4U$. Center a monic Chebyshev polynomial $T_i$ at $2U$, giving the uniform bound $C_i=2U^i$ for $i>0$, with $C_0=1$. The leading terms of $T_i$ and $S_i$ agree. Expand their difference using the lower ordinary binomial polynomials, then round each coefficient after dividing by $D_i$. This changes $S_i/D_i$ by an integer combination of functions that take integer values on the interval. The error from $T_i/D_i$ is at most $\tfrac12\sum_{j<i}\binom{H}{j}$. Because $j!\mid D_i$ for $j\le i$, multiplying the rounded row by $D_i$ still gives a monic polynomial with integer coefficients. The size bound is independent of the Bézout coefficients. Lean uses the positive integer bounds

$$w_i=1+\left\lfloor C_i/D_i\right\rfloor+
           \sum_{j<i}\left\lfloor H^j/j!\right\rfloor.$$

Clear all denominators with $D_{144}$, choose a public anchor $t$ with $N\mid c+2t$, and impose 72 Taylor divisibility conditions there. For the divisor floor $L=\lceil N/2^{1024}\rceil$ the sufficient inequality is

$$N^{2628}\,145^{145}\prod_{i=0}^{144}w_i<L^{10440}.$$

The public checks are $N\ge2^{2047}$, odd $N$, and $\gcd(N,D_{144})=1$. Every 2,048-bit product of two 1,024-bit primes meets them. If either factor lies in the chosen window, the Taylor conditions force its 72nd power to divide the cleared evaluation. Coprimality permits cancellation of the denominator, and the strict bound forces the resulting integer to vanish. [General and finite proofs](../PrimeFactors/ThreeUnitFactorialWindows.lean) · [Earlier rounded construction](rounding-chebyshev-into-binomial-coordinates.md)

At $H=2^{515}$ the sifted $145^{145}\prod w_i$ has 5,299,878 bits. The public bound $N\le2^{1024}L$ allows $145^{145}\prod w_i<2^{5,300,604}$ uniformly. At the same degree, depth and width, the previous rounded weights give a 5,303,986-bit integer. On the two published 2,048-bit products, the earlier criterion already passes for the fresh product and fails for the crossed product at this width. The new criterion passes for both. These comparisons use only $N$ and its public floor. They count feasible positions per chosen equation. Constructing a suitable equation and locating an occupied window still cost work. [Kernel-checked comparisons](../PrimeFactors/ThreeUnitFactorialWindows.lean)


Using a disjoint grid of windows, the 145-row theorem covers the entire feasible range in fewer than $2^{506}$ locations. Its first odd candidate is calculated from $\lceil N/2^{1024}\rceil$, and its last possible smaller factor is $\lfloor\sqrt N\rfloor$. Each location holds $2^{515}+1$ odd positions. This count includes the final partial block and still makes a full sweep impractical. [Coverage proof](../PrimeFactors/UnitWindowCover.lean)
