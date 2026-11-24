# A quarter-width phase of one Pascal coefficient

Let $N=pq$ with distinct odd primes $p<q\le 2p$. A single binomial coefficient, computed at a public index, already gives $q-1$ modulo $N$. One can ask for less from an evaluator. For a 2048-bit product of two 1024-bit primes, the first **511 binary fractional digits of one scaled phase** give the low 512 bits of $q$. The least significant bit is known because $q$ is odd. The classical small-root theorem then suffices to recover both primes in polynomial time. The open step is producing those phase digits cheaply from the product. [Original Pascal formula](pascal-readout.md) · [Lean identities and error bounds](../PrimeFactors/PascalProjection.lean) · [Quarter-width decoding theorem](quarter-width-count.md)

## Reading the digits

Write $n=\operatorname{bitlength}(N)$, $k=\lceil n/4\rceil$, $M=2^k$ and $a=\lfloor N/M\rfloor$. Let $r=N\bmod M$. Start with the largest odd index $K\le\sqrt N$, and write $C=\binom{N-1}{K}$. The exact phase is the fraction $\theta=R/N$, where $R=a(C+1)\bmod N$. All inputs to this observation are public.

The identity behind the decoder holds for every $p,q,M>0$, even without primality. Write $q=Mv+s$, $0\le s<M$. Then $a=pv+\lfloor ps/M\rfloor$ and $r=ps\bmod M$. Here $R=(a q)\bmod(pq)=q(a\bmod p)$ by the binomial congruence. Consequently

$$
   MR+r q=N(q\bmod M), \qquad
   M\theta=s-r/p.
$$

Whenever $r\le p$, the number $M\theta$ lies between $s-1$ and $s$, inclusive. The integer $s=q\bmod M$ is odd. Ordinary truncation gives the exact answer

$$
   q\bmod M=2\left\lfloor 2^{k-1}\theta\right\rfloor+1.
$$

The sufficient condition $M\le p$ can be checked using the public lower bound $\lceil\sqrt{N/2}\rceil$. It holds throughout the 2048-bit case. For a noisy measurement, the distance to the nearest boundary between adjacent odd labels, in phase units, is at least $(1-r/p)/M$. Circular error strictly below that value preserves the label. Replacing $p$ by the public lower bound gives an error budget that can be computed before evaluation. Exact truncation needs no extra guard digits.

For the postprocessing, $M\ge N^{1/4}$, $q\ge\sqrt N$ and $q\le\sqrt{2N}$. Given $s$, the integer $(q-s)/M$ is at most $\sqrt 2 N^{1/4}$. It is a root of a monic linear polynomial modulo the unknown divisor $q$, since $M$ is invertible modulo $N$. May's Theorem 7 allows this fixed constant at the $N^{1/4}$ endpoint. The product is used in decoding as well as in specifying the phase. [May, Theorems 6–7](https://digital.ub.uni-paderborn.de/hsmig/download/pdf/3235#page=38)

## Nonadaptive observations at constant precision

All measurements can use the **same coefficient and cutoff**. To recover bits in blocks, suppose $P$ is a power of two and the decoder already has $s=q\bmod P$. To obtain another $d$ bits put $B=2^d$ and request the phase for the public scale $\lfloor N/(BP)\rfloor$. Its distance on the circle from $q/(BP)$ is at most
$$
  \frac{N\bmod(BP)}{BPp}<\frac1p.
$$
The $B$ candidate phases are $(s+iP)/(BP)$ for $0\le i<B$, spaced exactly $1/B$ apart. Pick the one closest on the circle to the estimate and output $s+iP$. The choice is unique when the estimator's circular error plus the scale's displacement is strictly below $1/(2B)$. The exact displacement varies with the scale. For a sufficient public condition on each observation replace $p$ in its denominator by $\lceil\sqrt{N/2}\rceil$. Errors may otherwise vary arbitrarily between observations. [Lean separation of block labels, including wraparound](../PrimeFactors/PascalProjection.lean)

Begin with $P=2$ and $s=1$. For a target of $k$ bits the scales are fixed by $N,k,d$ before any measurement. Only decoding uses the previously recovered bits. There are $\lceil(k-1)/d\rceil$ measurements, with a smaller final block when needed. On the 2048-bit family, $d=1$ gives 511 nonadaptive observations. Rounding each phase to the nearest quarter turn incurs circular error at most $1/8$, safely below $1/4-1/p$. For a $d$-bit block, rounding to the nearest multiple of $1/(2B)$ costs at most $1/(4B)$ and suffices whenever $p>4B$. These are precision and query counts. The computational cost of obtaining even a quarter-turn observation at the specified scales remains unresolved.

## A raw projection with every bit zero

One can arrange for **the same coefficient** to have $C\bmod M=0$ throughout the search. Put $u=\lfloor\sqrt N\rfloor$ and choose

$$
   K=M\left\lfloor\frac{u+1+M/2}{M}\right\rfloor-1.
$$

Assume $M\le\lceil\sqrt{N/2}\rceil\le p$, so the aligned index exists. This is the nearest index congruent to $-1\bmod M$ to the real square root $x=\sqrt N$. The rounding uses just the integer square root because $M/2$ is an integer. In fact $K\le u+M/2$ and $u+1\le K+M/2$, hence $|K-x|\le M/2$.

Test the **first Fermat midpoint** $\lceil x\rceil$. If its square minus $N$ is a square, we have the factors. Otherwise $p\le K<q$. Indeed if $K<p$, then $x-p\le M/2$. If $q\le K$, then $x-p\le q-x\le M/2$ by the arithmetic–geometric mean inequality. Either would imply

$$
  \frac{p+q}{2}-x=\frac{(x-p)^2}{2p}
      \le\frac{M^2}{8p}\le\frac{x}{2p}\le\frac{\sqrt2}{2}<1.
$$

Here $M^4\le 2^{n+3}\le16N$. The true midpoint is an integer at least $x$, and would therefore have been the first one tested. After an unsuccessful test, $K$ is odd and $p\le K<q\le2p$, so the Pascal threshold theorem gives $C\bmod N=q-1$. Thus the same 511-bit phase prefix suffices on every remaining 2048-bit input.

The coefficient identity $N\binom{N-1}{K}=(K+1)\binom{N}{K+1}$ proves the raw divisibility. Since $M\mid K+1$ and $N$ is odd, $M\mid C$. Directly computing the low $k$ bits of $C$ returns zeros for every one of these inputs. This identifies a particular inexpensive modular computation that loses the projected factor information. Finding a different way to evaluate the phase remains open. [Aligned cutoff and raw divisibility proofs](../PrimeFactors/PascalProjection.lean)

For the earlier fixed-width cutoff there is also an exact valuation formula. For every prime $\ell\nmid N$ and $\ell^b\le N$,

$$
 v_\ell\!\binom{N-1}{\ell^b-1}
   =b+v_\ell\!\left(\left\lfloor N/\ell^b\right\rfloor\right).
$$

Removing a trailing zero digit of a binomial index preserves the valuation if the top index is simultaneously divided by $\ell$ and rounded down. This follows from the factorial valuation recurrence. Repeating the step for $\binom N{\ell^b}$ and applying the preceding identity gives the formula. For $N=143,b=4,\ell=2$, the raw coefficient at index 15 has seven trailing zero bits, whereas its canonical remainder modulo 143 is $11+13-1=23$. [Lean valuation proof](../PrimeFactors/PascalProjection.lean) · [Granville on valuations and binomial coefficients](https://www.cecm.sfu.ca/organics/papers/granville/paper/binomial/html/node2.html)

## Bounded example

On the existing independently sampled product $N=2028838549$, $M=256$ and the aligned index is 45055. The first midpoint gives $45043^2-N=33300$, a nonsquare. The 761,479-bit coefficient gives $C\bmod256=0$ and $C\bmod N=61492$. The public multiplier 7925150 gives $R=419997190$ and $\lfloor128R/N\rfloor=26$. Thus the predicted residue is $53\bmod256$, which agrees with the verified larger prime 61493. This calculation constructed the full coefficient. It demonstrates the observation and gives no improvement in the cost of evaluating it. [Input and certified factors](../benchmarks/pascal.json)

On the same coefficient, round the phases at scales $\lfloor N/2^j\rfloor$, $j=2,\ldots,8$, independently to the nearest quarter turn. The seven observed numerators over four are $1,2,1,3,3,2,1$. Starting from the known low bit, choosing the nearest candidate gives $1,5,5,21,53,53,53$ at successive moduli. The final label agrees with the single seven-bit prefix.
