# A short vector exists for every trial factor

For $N=117449$, the smaller balanced factor could lie at any integer from **243 to 342** on size grounds. All **100** trial values admit a positive primitive vector satisfying the same shortness bound as the true factor. Even the vector $(4,3)$ fits the true prime 257 and both neighboring trial primes 251 and 263. What distinguishes the three is the denominator of a rational number computed using the trial. The true prime gives denominator 1. The other primes give 251 and 263. [Lean proof and checked example](../PrimeFactors/OffsetFactorProjection.lean)

## What survives the size test

Take a positive nonsquare $N$, $T=\lfloor\sqrt N\rfloor$ and $h=N-T^2$. If $d$ were a factor, the successful search uses the positive form $ds^2-2Tsv+(N/d)v^2$. Clear its denominator to define the integer

$$
R_d(s,v)=(ds-Tv)^2+hv^2=d^2s^2-2dTsv+Nv^2.
$$

The matrix of $R_d$ has determinant $d^2h$ for **every positive integer $d$**. The two-dimensional Gauss minimum bound supplies coprime integers $s,v$ with $R_d>0$ and $3R_d^2\le4d^2h$. For $6\le d$, $d^2\le N\le2d^2$, one can in addition take $s,v>0$ and $v<d$. Indeed $h\le2T\le4d$ gives $4h<3d^2$, so $R_d<d^2\le N$. If $s,v$ had opposite signs, or either vanished, the positive form would have value at least $\min(d^2,N)$. Simultaneous negation gives positive coordinates. Finally $v^2\le hv^2\le R_d<d^2$. [Short-vector bound](../PrimeFactors/ReducedOffsetMinimum.lean) · [Positive balanced projection](../PrimeFactors/OffsetFactorProjection.lean)

At any nonsquare $N\ge2^{2047}$, the integer trials $d=T-i$ for $0\le i<2^{1021}$ already give **at least $2^{1021}$ different passing values** inside the balanced smaller-factor interval. Indeed $4i\le T$, and $d\ge3T/4$ implies $2d^2\ge N$ when $T\ge16$. This counts integer candidates before a primality screen. It shows exactly which interval survives projecting the short-vector condition onto $d$. Methods using other information about $N$ may reduce this interval. [Target-size coverage theorem](../PrimeFactors/OffsetFactorProjection.lean)

## Where divisibility enters

Suppose $R_d/d=a/b$ with $b>0$. Reduction modulo $d$ gives $R_d\equiv Nv^2\pmod d$. Consequently, if $d$ is coprime to $N$, then $d\mid bv^2$. With $v>0$ this implies $d\le bv^2$, so $hd\le bhv^2\le bR_d$. Squaring and applying the shortness bound yields

$$
3h\le4b^2.
$$

The inequality holds for any short representation at a coprime trial, including fractions presented with a common factor. On both published 2,048-bit controls the public gap satisfies $3h>4(2^{511})^2$. Thus a coprime trial on either control has denominator **greater than $2^{511}$**. That numerical floor depends on $h$. Inputs very close to a square can have a small gap. [Checked control gaps and denominator theorem](../PrimeFactors/OffsetFactorProjection.lean)

For a prime trial $d$ the conclusion is exact. If $d\mid N$, then $d\mid R_d$ and the reduced denominator is 1. Otherwise $d$ is coprime to $Nv^2$ since $0<v<d$, hence also coprime to $R_d$, and the reduced denominator is $d$. Partial cancellation can also occur at a composite trial. At $d=252$ in the small example, $(s,v)=(4,3)$ gives $4689/252=521/28$. [Prime denominator dichotomy](../PrimeFactors/OffsetFactorProjection.lean)

| Trial $d$ for 117449 | $(s,v)$ | $R_d$ | Reduced $R_d/d$ |
|---:|---:|---:|---:|
| 251 | (4,3) | 4,849 | 4,849/251 |
| 257 | (4,3) | 4,369 | 17 |
| 263 | (4,3) | 5,041 | 5,041/263 |

Here $T=342$ and $h=485$. The checked interval computation finds that 257 is the only one of the 100 trials with a common factor with $N$. Since $3h>4$, the denominator bound rules out an integral $R_d/d$ at all other trials. The split is $117449=257\times457$. For a specified $d$, reducing the form is possible and direct divisibility is already cheaper. Selecting a trial with small denominator from the product alone is the remaining problem. [Existing complete-search fixture](../benchmarks/offset-lattice-batches.json) · [Kernel-checked interval and three witnesses](../PrimeFactors/OffsetFactorProjection.lean)

## What supplied coordinates tell us about the larger factor

Assume someone supplies **the oriented pair** $(s,v)$ of a winning vector, meaning $p<q$, $j+2Tsv=ps^2+qv^2$ and $j\le J=\lfloor\sqrt{4h/3}\rfloor$. The calculation below uses only $N,s,v$. The two full-size examples source the coordinates from a previous diagnostic that used the published prime factors. [Origin of the coordinates](one-or-two-winning-tests.md#where-were-the-winning-positions-on-the-large-examples)

Multiplying the winning identity by $q$ gives $(qv-Ts)^2+hs^2=qj$. For a possible larger factor $x$ it is consequently necessary that $v^2x^2+Ns^2\le Cx$, where $C=2Tsv+J$. If $C^2<4N(sv)^2$ the pair cannot work. Otherwise put $B=\lfloor\sqrt{C^2-4N(sv)^2}\rfloor$. Completing the square gives the **exact integer interval for that inequality**, given by

$$
\left\lceil\frac{C-B}{2v^2}\right\rceil\le x\le
\left\lfloor\frac{C+B}{2v^2}\right\rfloor .
$$

Intersect this with $[T+1,U]$, where $U=\lfloor\sqrt{2N}\rfloor$ comes from $p<q\le2p$. For integer endpoints $l,r$ and $M=\lfloor N^{1/4}\rfloor$, the number of blocks of up to $M$ consecutive integers is $\lceil\max(0,r-l+1)/M\rceil$. The supplied pair locates the known larger factor within **four blocks on the fresh input and thirteen on the crossed input**. Lean checks the exact counts from the product and the two published coordinates. The table compares a looser calculation using $|xv-Ts|\le\lfloor\sqrt{UJ-hs^2}\rfloor$. [Rounded interval and full-size arithmetic](../PrimeFactors/OffsetFactorProjection.lean) · [Previously certified coordinates](../PrimeFactors/OffsetWinnerExamples.lean)

| Known-factor diagnostic | Bits in supplied $s,v$ | $v/\sqrt J$ | Looser blocks | Exact blocks |
|---|---:|---:|---:|---:|
| Fresh | 256, 256 | 0.514 | 5 | 4 |
| Crossed | 254, 254 | 0.167 | 15 | 13 |

There is also a uniform guarantee. Any two allowed integers $l,r$ obey $((r-l)v)^2\le4UJ$ by applying $(xv-Ts)^2\le UJ$ at both endpoints. Thus **$b$ blocks suffice whenever $4UJ<(bMv)^2$**. For $M\ge49$, $N<(M+1)^4$ and $U^2\le2N$ imply $16U<25M^2$. If $v\ge\sqrt J/a$ for a positive integer $a$, the public check holds with $b=\lceil5a/2\rceil$. May's approximation theorem gives the significance of the $N^{1/4}$ scale for a divisor exceeding $\sqrt N$. The block counts here are static mathematics. The coordinate pair still has to be supplied or discovered. [Finite bound](../PrimeFactors/OffsetFactorProjection.lean) · [Earlier fourth-root interval argument](approximate-totient-squares.md#recovering-a-factor-from-the-interval) · [May, Theorem 7 and its divisor-approximation corollary](https://digital.ub.uni-paderborn.de/hsmig/download/pdf/3235#page=38)

The unconditional projection count above concerns trial values for the **smaller** factor. Any collection of blocks covering every one of its $2^{1021}$ distinct passing integers needs at least $2^{509}$ blocks if each contains at most $2^{512}$ integers. Overlap can only increase the count required. This finite-union bound prices an exhaustive cover of the unconditioned trial interval. The four and thirteen blocks apply to the **larger** factor after supplying the winning coordinates. [Finite union bound](../PrimeFactors/OffsetFactorProjection.lean)
