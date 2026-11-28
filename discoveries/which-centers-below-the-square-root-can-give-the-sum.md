# Which centers below the square root can give the sum?

For **138,953**, the integer square root is 372. Every positive shift in the square identity fails there. Move down just one integer to **371**, and the remainder gives the exact prime sum **774**. On this chosen product, one discriminant check then recovers **283 and 491**. Across all pairs of distinct 1,024-bit primes producing a 2,048-bit number, even a free choice of *every* center from zero through the square root gives this power-of-two prediction a success rate below **one in $2^{474}$**. [Checked example](../PrimeFactors/FloorShiftCenterWindow.lean) · [All-center bound](../PrimeFactors/FloorShiftDyadicCenters.lean)

## What moving one step buys on 138,953

At any proposed center $s\le\lfloor\sqrt N\rfloor$, compute $D_s=N-s^2$. The rule adds the largest power of two dividing $D_s$ to $2s$. Both factors are odd, so their sum is even. An odd remainder can be rejected immediately. For the promised product of distinct primes, $D_s$ is positive at every such center. The proof also treats a zero remainder on other inputs, where the gcd rule returns 1. [The all-center reading](../PrimeFactors/FloorShiftDyadicCenters.lean) · [The original floor-center rule](using-the-power-of-two-in-a-square-remainder.md)

| Center $s$ | Remainder $D_s$ | Public calculation |
| ---: | ---: | --- |
| 372 | 569 | Odd. A positive shift would have to multiply the even difference $p+q-2s$ to give 569. |
| 371 | 1,312 | $1,312=41\cdot32$. Twice 371 plus 32 gives 774. |

The discriminant is $774^2-4\cdot138{,}953=208^2$. Halving $774-208$ and $774+208$ gives the two primes. Moving down one step costs one remainder update, $D_{s-1}=D_s+2s-1$. The full calculation uses the initial integer square root, the parity check at 372, one trailing-zero count or gcd at 371, and one exact square test. An implementation that reads the power of two at both centers spends one additional reading. Consecutive Fermat starts at 373 and reaches the true midpoint 387 on test 15. The prime labels verify the output after the prediction. [Center, shift, primality and discriminant checks](../PrimeFactors/FloorShiftCenterWindow.lean)

## Finding the viable centers without scanning down to zero

Suppose both factors are odd and below $2^b$. Write $r=\lfloor\sqrt N\rfloor$. A candidate sum $2s+2^j$ can only succeed inside $2r<2s+2^j<2^{b+1}$. Thus $1\le j\le b$, including the last exponent, and the distance $e=r-s$ must satisfy $0\le 2e<2^j$. For that exponent the reading also requires $N-s^2\equiv 2^j\pmod{2^{j+1}}$. These conditions leave **at most two centers per exponent**. Lean proves that the compressed list contains the true sum exactly when the original reading at some center does. [List equivalence and size](../PrimeFactors/FloorShiftCenterCompression.lean)

At $j=1$ the interval allows only $s=r$, and the remainder passes exactly when $r$ is odd and $N\equiv3\pmod4$. At $j=2$ the interval allows $r$ and $r-1$. Its odd member passes the remainder test exactly when $N\equiv5\pmod8$. The upper sum limit still applies at both levels. Starting at $j=3$ a solution requires $N\equiv1\pmod8$. In that case compute a single odd square root $u$ of $N$ modulo $2^{b+1}$ by lifting one binary digit at a time. For each $j$ the two possible classes of $s$ modulo $2^j$ are $u+2^{j-1}$ and its negative. For a class $a$, set $e=(r-a)\bmod 2^j$. Keep $s=r-e$ when $e\le r$, $2e<2^j$ and the candidate sum is within the width limit. Each class gives at most one center because the eligible interval is shorter than its period. For $37{,}001=163\cdot227$, the final level $j=b=8$ gives $s=67$ and the correct sum $390$. [Shared root and checked endpoints](../PrimeFactors/FloorShiftCenterCompression.lean)

This costs one integer square root to find $r$, at most $b-2$ one-bit lifting steps for $b\ge3$, and at most $2b$ candidate centers before filtering and removing duplicate sums. Each surviving sum needs at most one exact discriminant check. On **138,953**, five centers give sums 746, 762, 774, 838 and 954. After parity and square-residue screening, the second exact check finds 774. On **141,217**, five centers give just four sums, 754, 766, 802 and 862. All miss the true sum $283+499=782$. With the same screening, ordinary Fermat reaches the answer on its second exact check on both products. The replay records the lifting and square-test counts separately. [Bounded replay](../experiments/dyadic_center_compression.py) · [Recorded results](../benchmarks/dyadic-center-compression.json)

There is a tighter bound on **distinct sums**. At every level $j\ge3$, the proposed midpoint $H=s+2^{j-1}$ is congruent to $u$ or $-u$ modulo $2^j$. For two consecutive levels $j,j+1$, every midpoint lies in the same interval $r<H\le r+2^j$, which contains each residue modulo $2^j$ exactly once. The two levels together therefore give at most two sums. For 1,024-bit factors, this means **at most 1,022 distinct sums** when $N\equiv1\pmod8$, and **at most one** for every other odd product. For example, levels 7 and 8 on 141,217 give the same sum 862 from centers 367 and 303. The tighter bound counts checks after removing duplicates. [Adjacent-level and full-width proofs](../PrimeFactors/FloorShiftDistinctSums.lean)

## What even all the centers can reveal

Suppose any center $s$ gives the true factor sum $S=p+q$ by adding a power of two $J$ to $2s$, with $J\mid D_s$. This grants the choice of *any* power of two dividing the remainder, including the one used by the actual rule. Expanding the squares gives

$$
(q-p)^2=J(S+2s)-4D_s.
$$

Thus $J$ also divides the squared prime gap. Write the gap as $q-p=2^v g$ with $g$ odd. Then $J\le2^{2v}$. For factors at most $H$, we have $S+2s\le4H$ and $D_s\ge0$. Combining these inequalities gives $2^{2v}g^2\le2^{2v}\,4H$, hence **$g\le2\sqrt H$**. If the odd part of the prime gap is larger, every center misses. This is a condition on the true factors used to measure coverage. [Odd-part necessity](../PrimeFactors/FloorShiftDyadicCenters.lean)

For $H=2^{1024}$, there are at most $H$ choices for the smaller factor, 1,024 choices for $v$, and $2^{513}$ choices for $g$. Those three numbers fix the pair. Comparing that bound with the unconditional lower bound for the eligible prime population gives the fraction below $2^{-474}$. The count allows every nonnegative center $s\le\lfloor\sqrt N\rfloor$ and charges nothing for finding the best center. [Finite count and full-width theorem](../PrimeFactors/FloorShiftDyadicCenters.lean) · [Prime-pair denominator](../PrimeFactors/ChebyshevPrimeSample.lean)

## What changes if any divisor of the remainder is allowed?

A different search can try every positive integer $h$ dividing $D_s$ and predict $2s+D_s/h$ using exact division. For a nonsquare semiprime the prediction is correct exactly when the integer identity $(p-h)(q-h)=(s-h)^2$ holds. Using signed subtraction matters when $s<h$. For instance, $p=11$, $q=19$, $s=7$ and $h=10$ give $(11-10)(19-10)=(-3)^2=9$. [Shift equivalence and signed example](../PrimeFactors/FloorShiftCenterWindow.lean)

Let $L$ count the consecutive centers starting at $\lfloor\sqrt N\rfloor$ and moving down. For $p<q\le H$, the number of pairs that work at one or more of these centers is at most the smaller of

$$
12 L H\sqrt H
\qquad\text{and}\qquad
2H\sqrt{2LH}\left(1+\tfrac12+\cdots+\tfrac1H\right).
$$

The proof counts the whole window once. A successful shift forces $p=h+ux^2$ and $q=h+u(x+k)^2$ for $u,k\ge1$ and $x\ge0$. The common constraint $huk^2\le2LH$ holds for every center in the window, including when $s<h$. Counting the possible coordinates in two ways gives the two bounds. [Coordinate proof and window counts](../PrimeFactors/FloorShiftCenterWindow.lean)

Even granting **$2^{900}$ consecutive centers** and every exact divisor at each, fewer than **one in $2^{24}$** eligible prime pairs can succeed. The bound for a single floor center is below one in $2^{482}$. Each fraction refers to all unordered pairs of distinct 1,024-bit primes with a 2,048-bit product. The size bounds use no RH or prime-distribution hypothesis. [Window population theorem](../PrimeFactors/FloorShiftCenterWindow.lean) · [Single-center population theorem](../PrimeFactors/FloorSquareShiftPopulation.lean)
