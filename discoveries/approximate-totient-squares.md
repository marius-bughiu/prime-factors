# When a totient is close to a small multiple of a square

Let $N=pq$ with distinct primes $p<q\le 2p$. Suppose public integers $L,E$ satisfy $1\le L\le N$, $0\le E\le\sqrt N$, and

$$
  |(p-1)(q-1)-dy^2|\le E
  \qquad\text{for some integers }1\le d\le L,\ y\ge0.
$$

The product supplies at most three trial values of $y$ per scale $d$, and at most two for $N\ge16$. When $q-p\ge\kappa\sqrt N$ for fixed $\kappa>0$, and $E\le C N^{1/4}$ for fixed $C$, these trials give a deterministic factoring bound of $L\,\operatorname{polylog} N$ bit operations under the stated promise. The lattice step is May's published theorem on approximating a divisor. The contribution here is locating the possible squares from the product, propagating the error through the quadratic, and counting the resulting applications of that theorem. The case $E=0$ also admits direct square tests. [Exact scaled-square recovery](discriminant-strides.md#a-scaled-square-root-that-determines-both-factors) · [May, Theorems 7 and 11](https://digital.ub.uni-paderborn.de/hsmig/download/pdf/3235#page=38)

## Finding the candidate square

Write $S=p+q$, $\varphi=N+1-S$ and $t=\lfloor\sqrt{\lfloor N/d\rfloor}\rfloor$. Since $S\ge 2\sqrt N$ and $E\le\sqrt N$, the promised square satisfies $dy^2\le\varphi+E\le N$. Thus $y\le t$. For every $N$ covered by the hypotheses, the Lean candidate theorem gives $\max(0,t-2)\le y\le t$. At $N=6$, $d=1$ and $E=2$, the witness $y=0$ attains $t-2$. [Lean candidate and sum bounds](../PrimeFactors/ApproximateTotient.lean)

For $N\ge16$ this can be tightened to two trials. Write $r=\sqrt N\ge4$. Since $q/p\le2$ and $x+1/x$ is increasing for $x\ge1$, one has $S/r\le3/\sqrt2<9/4$. Consequently

$$
 dy^2\ge \varphi-E > N-\tfrac{13}{4}r+1
   \ge (r-2)^2,
$$

where the last difference is $3r/4-3\ge0$. Hence $0\le t-y<2/\sqrt d$. Test $y=t$ and, when $t>0$ and $d<4$, also $y=t-1$. For $N<16$ direct division suffices. For each trial compute $H=N+1+E-dy^2$. The correct trial satisfies $S\le H\le S+2E<5\sqrt N$. Discard trials with $H^2<4N$ or $H^2>25N$.

## A public interval for the larger factor

Form the integers

$$
  s=\lfloor\sqrt N\rfloor,\qquad
  U=\left\lfloor\frac{H+\lfloor\sqrt{H^2-4N}\rfloor}{2}\right\rfloor.
$$

For the correct trial, $q\le U$ and $(U-q)(U-p)\le 2EU$. Indeed, the larger real root of $x^2-Hx+N$ is at least $q$, and rounding it down leaves the integer $U$ between $q$ and that root. Thus $U^2-HU+N\le0$. Adding $(H-S)U$ proves the inequality. The integral form, including its rounding, is formalized in [ApproximateTotient.lean](../PrimeFactors/ApproximateTotient.lean).

Discard $U\le s$, since the true $q>\sqrt N$. The following radius uses only known integers and contains the true factor in $[U-R,U]$ on the correct trial.

$$
 R=\min\left(\left\lfloor\sqrt{2EU}\right\rfloor,
                \left\lfloor\frac{2EU}{U-s}\right\rfloor\right).
$$

Both bounds follow from $U-p\ge U-q$ and $U-p\ge U-s$. Put $g=q-p$. Since $U\le H<5\sqrt N$ on the correct trial and $q-\sqrt N=g\sqrt q/(\sqrt p+\sqrt q)\ge g/2$,

$$
 R\le\min\left(\sqrt{10E}\,N^{1/4},\;\frac{20E\sqrt N}{g}\right).
$$

There is also a sharper criterion for a single approximation. The actual error $\Delta=U-q\ge0$ satisfies $\Delta(\Delta+g)\le10E\sqrt N$. For any $b>0$, the condition $10E\sqrt N\le b(b+g)$ implies $\Delta\le b$. In particular, $g\ge\kappa\sqrt N$ and $E\le C N^{1/4}$ give $\Delta\le(10C/\kappa)N^{1/4}$. This criterion explains when growing absolute error still permits recovery from one approximation.

## Recovering a factor from the interval

Set $M=\lfloor N^{1/4}\rfloor\ge1$. Cover the integer interval by blocks of at most $M$ consecutive integers, clipping to $[s+1,\lfloor\sqrt{2N}\rfloor]$ if desired. For a block with right endpoint $A$ containing $q$, its offset $x=q-A$ satisfies $|x|<M$ and $A+x\equiv0\pmod q$. May's Theorem 7 applies to the monic polynomial $A+T$, a divisor $q\ge N^{1/2}$, and degree one. The theorem includes the $N^{1/4}$ endpoint and permits a fixed constant multiplier. Its bit cost per block is polynomial in $\log N$. Test every returned candidate by exact division, accepting only proper divisors. [May, Theorem 7](https://digital.ub.uni-paderborn.de/hsmig/download/pdf/3235#page=38) · [Coppersmith's original small-root paper](https://doi.org/10.1007/s001459900030)

Across the at most $2L$ trials for $N\ge16$, visit the first block of each interval, then the second of each, and so on. This scheduling bounds work on incorrect guesses by the number of rounds the correct guess needs. The total bit cost to find a divisor under the promise is

$$
  O\!\left(L\left[1+\min\!\left(\sqrt E,\frac{E N^{1/4}}{g}\right)\right]
      \operatorname{polylog}N\right).
$$

In particular, for $g\ge\kappa\sqrt N$ the block count per trial is $O(1+E/(\kappa N^{1/4}))$ through the full stated range $E\le\sqrt N$. The algorithm can use the public $R$ without knowing $g$ or $\kappa$. Across all balanced gaps the corresponding bound is $O(1+\sqrt E)$. The project also treats recovery from a short sum interval by matching modular powers. [Matching powers to recover the sum](searching-the-balanced-interval.md#matching-powers-to-recover-the-sum)

For example, take $N=12{,}267{,}695{,}389$, $d=6$ and $E=60$. The trial $y=t=45{,}217$ gives $H=232{,}916$, $U=152{,}440$ and $R=438$. The factors are $80{,}567$ and $152{,}267$, with $\varphi=6y^2+22$. The true offset is $-173$, within one $M=332$ block ending at $U$. These values check the interval arithmetically.

## How many inputs can satisfy the promise?

For $X\le p<q<2X$, $E=O(X)$ and $1\le L\le X^2$, the number of prime pairs satisfying the promise is at most

$$
  (1+E)X\sqrt L\; X^{o(1)}.
$$

Indeed $dy^2\le4X^2+E$, so the number of candidate pairs $(d,y)$ is $O(\sum_{d\le L}(1+X/\sqrt d))=O(X\sqrt L)$. Each of the $2E+1$ integer offsets fixes a candidate totient $v$. Retain $1\le v\le4X^2$. Each divisor $p-1$ of $v$ fixes $q-1$, so at most $\tau(v)=X^{o(1)}$ pairs yield this value. The divisor bound is uniform here. The finite injection behind this last count is formalized in [PredecessorCount.lean](../PrimeFactors/PredecessorCount.lean).

The prime number theorem gives order $X^2/(\log X)^2$ pairs in this box. For $E=O(\sqrt X)$ and polylogarithmic $L$, the covered fraction is at most $X^{-1/2+o(1)}$. Thus the separated-gap recovery result applies to a sparse promise at this error scale. There are nevertheless infinite families with bounded, nonzero offsets, including examples beyond every prescribed finite list of exact square classes. [Prime pairs with a totient just below a square](near-square-families.md)
