# Checking a larger interval at any chosen location

Given only the product of two 1,024-bit primes, we can choose a location, build one polynomial of degree at most four, and check the surrounding **$2^{408}+1$ odd numbers** for a factor. On both of our 2,048-bit comparison inputs we checked the lower quartile of the possible smaller-factor range. Both intervals were empty. Each exclusion has a downloadable Lean proof. Covering *every* 1,024-bit odd number this way takes $2^{614}$ locations, about $7\times10^{184}$. We do not know how to identify the winning location cheaply. [Fresh example](https://marius-bughiu.github.io/prime-factors/#quartic-divisor-window-fresh-2048) · [Crossed example](https://marius-bughiu.github.io/prime-factors/#quartic-divisor-window-crossed-2048) · [Lean proof](../PrimeFactors/QuarticDivisorWindow.lean)

For a small example, take $N=2501$. The same public rule puts the center at 43. Its odd neighbors in the radius-one index window are 41, 43 and 45. Write them as $43+2x$ for $x=-1,0,1$. The constructed polynomial is $-5-32x-5x^2+25x^3+3x^4$. Its only root in that window is $-1$. This gives 41, and division gives 61. Lean checks both primes. [Worked example and certificate](https://marius-bughiu.github.io/prime-factors/#quartic-divisor-window-2501)

## Why the divisor must appear as a root

Let $N$ be the input and choose a progression $d=c+sx$ with $\gcd(s,N)=1$ and $|x|\le W$. Assume the divisors sought satisfy $d\ge D>0$. All four parameters $c,s,W,D$ are public. Compute $t$ such that $c+st$ is a multiple of $N$. Any divisor $d$ at position $x$ divides $s(x-t)$ and is coprime to $s$, hence divides $x-t$.

Seek an integer polynomial $P(X)=\sum_{i=0}^4 a_i X^i$ satisfying

$$N^2\mid P(t),\qquad N\mid P'(t),\qquad 0<\sum_{i=0}^4 |a_i|W^i<D^2.$$

Expanding at $t$ gives $P(x)=P(t)+(x-t)P'(t)+(x-t)^2 Q$ for an integer $Q$. Each term is divisible by $d^2$. The coefficient bound gives $|P(x)|<d^2$, so $P(x)=0$. A nonzero quartic has at most four distinct integer roots. Each root still has to give a divisor when substituted into $c+sx$. [Divisibility, bounds and root-count proofs](../PrimeFactors/QuarticDivisorWindow.lean)

## Existence and the cost of finding the equation

Lean proves that a suitable nonzero polynomial exists for **every** anchor when $N^3 5^5 W^{10}<D^{10}$. The five coefficient bounds in a box are $\lfloor(D^2-1)/(5W^i)\rfloor$. There are more tuples in that box than the $N^3$ possible pairs of residues $(P(t)\bmod N^2,P'(t)\bmod N)$. Subtract two tuples with the same pair. Their difference is nonzero and meets all three conditions. With $N<2^{2048}$, $D=2^{1023}$ and $W=2^{407}$, Lean checks the strict inequality. [Finite box lemma](../PrimeFactors/UnitQuarticBox.lean) · [Uniform theorem and grid of odd centers](../PrimeFactors/QuarticDivisorWindow.lean)

The implementation finds such coefficients by integer lattice reduction. It uses the coefficient rows of $N^2$, $N(X-t)$, $(X-t)^2$, $X(X-t)^2$ and $X^2(X-t)^2$, multiplying column $i$ by $W^i$. This triangular basis has absolute determinant $N^3 W^{10}$. The classical dimension-five LLL bound gives a first vector with sum of absolute entries at most $2\sqrt5(N^3W^{10})^{1/5}$. Since $2\sqrt5<5$, the same inequality suffices. The implementation compares all five reduced rows and checks the two divisibilities and the strict height bound directly. Neither Lean certificate needs to trust the reduction implementation. This is a fixed-degree instance of the classical small-root method for an unknown divisor. May's higher-dimensional theorem permits larger windows on paper. [Implementation](../experiments/quartic_divisor_window.py) · [LLL theorem](https://doi.org/10.1007/BF01457454) · [May, Theorem 7](https://digital.ub.uni-paderborn.de/hsmig/download/pdf/3235#page=38) · [Comparison for the same type of progression](batch-intervals.md)

Take $s=2$ and an odd center for an odd product. There are $2^{1022}$ odd 1,024-bit integers. Partition their indices into $2^{614}$ blocks of $2^{408}$ consecutive indices, and center the equation in each block. The endpoint shared with the next window is harmless. This gives a complete list from the product and bit bounds. Compared with the earlier $2^{682}$ prescribed centers, the count falls by $2^{68}$, while each quartic costs more than the earlier square test. This comparison concerns those two specific grids. [Earlier prescribed-center proof](ruling-out-an-interior-interval.md) · [Grid and coverage proof](../PrimeFactors/QuarticDivisorWindow.lean)

## What the two full-size checks used

Both centers used the lower quartile of the equal-bit-width smaller-factor range, rounded upward to an odd integer. Every integer in $[c-2W,c+2W]$ is covered since the even ones cannot divide the input. On both examples the entire product remains unresolved by this run. The finite-field check establishes that the quartic has no integer root, including between the requested endpoints. [Fixtures](../benchmarks/quartic-divisor-window.json)

| Work for one center | Fresh product | Crossed product |
| --- | ---: | ---: |
| Integer positions covered, including even ones | $2^{409}+1$ | $2^{409}+1$ |
| LLL size reductions / row swaps | 1,140 / 613 | 1,062 / 579 |
| Nodes checked to isolate integer roots | 3 | 1 |
| Primes tried for an independent exclusion | 4 | 10 |
| Residues evaluated across those primes | 15 | 75 |
| Final prime with no polynomial root | 7 | 29 |

## A cheaper equation for a smaller interval

When $N$ is coprime to six, each divisor $d$ satisfies $d^2\equiv1\pmod{24}$. For its cofactor $q$ this gives $q\equiv Nd\pmod{24}$. Choose positive weights $a,b$ with $12\mid a+bN$ by approximating $(N/c^2+(N\bmod12))/12$ by a fraction. Then $ad+bq\equiv a+bN\pmod{24}$, since $d$ is odd. At each admissible center the analytic bound on this sum spans at most 24 units, with strict endpoints. Only one permitted value remains. Its discriminant gives at most two candidates. [Weight existence and trace proof](../PrimeFactors/UniversalTraceWindow.lean) · [Related interval method of Hiary](https://arxiv.org/abs/1408.2608)

For two 1,024-bit primes this permits radius $23\cdot2^{337}$ everywhere with at most one square test after finding the weights. The complete grid has $\lceil2^{685}/23\rceil$ locations, about 2.875 times fewer than the earlier parity grid. At the fresh quartile the calculation used 199 continued-fraction steps and one square test. At the crossed quartile it used 191 steps and the endpoints ruled out its only trace. Separate Lean certificates reject the candidate discriminants modulo 17 and 11 respectively. The same calculation at center 255 recovered $251\times347=87097$. [Positive example](https://marius-bughiu.github.io/prime-factors/#arbitrary-divisor-window-mod24-87097) · [Fresh exclusion](https://marius-bughiu.github.io/prime-factors/#arbitrary-divisor-window-mod24-fresh-2048) · [Crossed exclusion](https://marius-bughiu.github.io/prime-factors/#arbitrary-divisor-window-mod24-crossed-2048)

For the earlier parity-only test we can also bound how many tests a complete cover needs, even if it chooses its locations adaptively. On the fresh example, covering all prime locations in the public range takes more than $2^{662}$ width-four strips. The proof allows trying a successful location early. [Proof assumptions and both controls](limits-of-linear-divisor-windows.md)
