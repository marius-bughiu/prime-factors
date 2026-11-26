# Choosing a quartic width from the product

Given 156,263, take its integer square root 395 and subtract its square from the input. The remainder is 238. Computing $238^2-22\cdot238+1=51{,}409$ and taking its gcd with the input gives 509. The other prime is 307. This choice of width succeeds where the three fixed widths 3, 5 and 7 each give gcd one. The same remainder calculation gave gcd one on both existing 2,048-bit controls. [Lean calculation](../PrimeFactors/QuarticSquareRemainder.lean) · [Control inputs](../benchmarks/block-subresultant.json)

## Why the width can change

For $t=\lfloor\sqrt N\rfloor$ and $r=N-t^2$, the normalized block coefficient satisfies the congruence

$$Q_m(t)=48t^4-24(1+m^2)t^2+(m^2-1)^3
\equiv 48r^2+24(1+m^2)r+(m^2-1)^3\pmod N.$$

Choose the width $m=t$ when $t$ is odd. For an odd input and even $t$, choose $m=t+N$ to obtain an odd width with identical residue. At this width the expression factors over the integers before the remainder substitution,

$$Q_t(t)=(t^2-1)(t^4+22t^2+1)
\equiv(t^2-1)(r^2-22r+1)\pmod N.$$

One square root, the calculation of its remainder, one more square and one gcd suffice to test the second factor. An extra gcd checks whether $576t(t^2-1)$ is a unit, as required to identify the normalized test with the original elimination coefficient. This gcd was one on the small example and both full-size controls. The search need never construct the $m^2$ individual positions. [Coefficient and normalization](a-factor-outside-the-resultant-block.md) · [Remainder and width identities](../PrimeFactors/QuarticSquareRemainder.lean)

## Exactly which shifts work at one prime

Write $H(t)=t^4+22t^2+1$. For a prime $p>5$, its roots are precisely the four signed sums $\pm a\pm b$ when $a^2=-5$ and $b^2=-6$ both have solutions modulo $p$. If either square root is missing, $H$ has no root. Indeed, $t=0$ gives $H(0)=1$. At a root put $a=(t^2+1)/(2t)$ and $b=(t^2-1)/(2t)$. Their sum is $t$ and their squares are $-5,-6$. Conversely those two equations imply $H(a+b)=0$. Also $(a+b)(a-b)=1$, so the sum fixes the difference and hence both signed values. For $p>5$ each square root is nonzero.

For 509 one can take $a=153$, $b=39$. The four possible centers are 114, 192, 317 and 395. The full width-dependent coefficient also vanishes at $1,-1$ because of its elementary first factor. Lean checks all six residue classes and the small example's prime factorization. This characterizes a possible hit given a prime. Testing the product's gcd requires only $N$. [Coordinate, uniqueness and six-class theorems](../PrimeFactors/QuarticSquareRemainder.lean)

## Limits of a rational width rule

More generally let the width modulo a prime be $A(t)/B(t)$, where $A,B$ are fixed polynomials over that field, $B$ is a nonzero polynomial, and $B(t)\ne0$ at the tested center. Clearing the denominator yields

$$48t^4B^6-24t^2(A^2+B^2)B^4+(A^2-B^2)^3.$$

In characteristic other than two or three its degree is **exactly** $\max(6\deg A,4+6\deg B)$, with degree zero used for the zero numerator. When $\deg A>\deg B$ the cubic term dominates. Otherwise the first term dominates. Thus this degree bounds the number of possible center residues even when the chosen width takes very large values. The six classes at 509 attain the bound for $A(t)=t$, $B(t)=1$. The four nontrivial classes are the ones for which the original width normalization can be a unit.

A rational width in the public quantities $N,t,r$ admits the same test after substituting $N=0$ and $r=-t^2$ modulo a divisor prime. Use the reduced polynomials' degrees. If the denominator vanishes at the center, it instead supplies its own gcd test with $N$. Counting center residues alone gives no bound on how quickly an arbitrary rule for choosing a width will factor a particular input. [Exact degree and local root-count proofs](../PrimeFactors/QuarticSquareRemainder.lean)
