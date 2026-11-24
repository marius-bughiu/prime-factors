# A deterministic calibration for signed Salié residues

A product of two distinct odd primes $N<2^{2048}$ can be split using **at most 43 normalized Salié measurements in total**, followed by polynomial-time arithmetic and one univariate lattice search. Each measurement needs absolute error at most $2^{-53}$ in the concealed cosine, after subtracting the publicly known cosine. The primes may be unbalanced. The underlying two-multiplier contraction gives an asymptotic deterministic evaluator. Computing even one measurement at a practical cost for general 2,048-bit inputs remains open. [Salié samples](divisor-samples.md) · [Earlier residue decoder](recovering-residues-from-sums.md) · [Cost of obtaining a measurement](counting-salie-phases.md)

Write $h$ for either mixed square root of one modulo $N$. A measurement at a unit $t$ yields an approximation to $\cos(2\pi th/N)$. Write $\|th/N\|$ for its distance in turns from an integer. Choose

$$
 B=2^{24},\qquad E=\tfrac{17}{16}2^{-28},\qquad BE=17/256.
$$

Clamp the measured cosine to $[-1,1]$ and apply $\arccos/(2\pi)$. For folded turns $x,y\in[0,1/2]$, the cosine difference is at least $8|x-y|^2$ in magnitude by the cosine difference formula and $\sin(\pi u)\ge2u$ on $[0,1/2]$. Thus the inverse error is at most $2^{-28}$. Round the computed turns to absolute error at most $2^{-32}$ and clamp to $[0,1/2]$ again. The resulting rational estimate has error at most $E$. One can meet the concealed-cosine premise from an absolute $2^{-53}$ approximation to the full normalized sample by computing the public cosine to error $2^{-55}$, since the sample is divided by two. Certified inverse-cosine approximation on this bounded interval requires polynomial bit work, for instance by interval bisection with additional guard digits. All later comparisons use the rounded rationals.

## Calibrate or shrink a public interval

Let $H$ be the folded integer representative of $h$, so $0<H<N/2$. Start with one measurement at $t=1$ and denote its folded reading by $v$. Choose $b=1$ if $v\le1-2v$, and $b=2$ otherwise. The corresponding hidden positive integer is $W=H$ or $W=N-2H$. In either case $W\equiv\pm bh\pmod N$, $W^2\equiv b^2\pmod N$, and the initial estimate $z=\min(v,1-2v)\le1/3$ differs from $W/N$ by at most $bE$. No decision about the true side of the comparison is needed when the measured value is near a third.

At level $i$, maintain an estimate $z$ of $S_iW/N$ with error at most $e_i$. Initially $(S_0,e_0)=(1,bE)$. At later levels $S_i=B^i/b$ and $e_i=E$. Every reached level therefore has $e_i/S_i=bE/B^i$. Its public interval for the integer $W$ has endpoints

$$
 L=\max(0,\lceil (z-e_i)N/S_i\rceil),\qquad
 U=\min(N-1,\lfloor (z+e_i)N/S_i\rfloor).
$$

If $(U-L)^2\le N$, proceed directly to the lattice step with $M=1$. Otherwise use the following two cases.

1. If $z<3e_i$, the true turn is below $4e_i$. Multiply by $B/b$ on the first move and by $B$ thereafter. In each case the new true turn is below $4BE=17/64<1/2$. Its folded value is exactly $S_{i+1}W/N$ with no wrap or reflection. Obtain the next reading at $t=B^{i+1}\bmod N$. It gives that same folded value because $bS_{i+1}=B^{i+1}$. Every such failed calibration shrinks the width bound on the original integer $W$ by a factor $B$.
2. If $z\ge3e_i$, the relative error is at most a third of $z$. For $z\le1/4$ choose a power of two $c$ with $1/8\le cz\le1/4$, by doubling until the lower bound is reached. Then the integer $Y=cS_iW$ satisfies $1/12\le Y/N\le1/3$. For $z>1/4$ choose $c=1$. At level zero $z\le1/3$ and $e_i\le2E$, while at every later level the previous move placed the true turn below $17/64$. Thus $1/12\le Y/N\le3/8$ in this case as well. Set $A=bcS_i\bmod N$. We know $Y\equiv\pm Ah\pmod N$ and its positive orientation is fixed on every subsequent observation. The choice of $c$ is entirely arithmetic and requires no additional sample. [Checked rescaling, signed residues and interval bound](../PrimeFactors/AnchorScale.lean)

## Read signed residues and finish

Use distinct odd primes $\ell<B$. A proper $\gcd(\ell,N)$ supplies a factor immediately. Otherwise measure the folded turn $y/N=\|A\ell^{-1} h/N\|$. Here $y$ is the least nonnegative folded representative. For some integer $k$ and $\sigma\in\{-1,1\}$,

$$
 \ell y=kN+\sigma Y.
$$

Multiply the observed turn by $\ell$. Its distance from $k+\sigma Y/N$ is below $BE=17/256$. Since $1/12\le Y/N\le3/8$, the nearest integer is $k$ and the sign of the difference from $k$ is $\sigma$. Hence $Y\equiv-\sigma kN\pmod\ell$. Invert the **known positive** power of two $cS_i$ modulo $\ell$ to obtain $W\bmod\ell$. This inversion uses the same $W$ even when the signs in the individual folded observations are different. Accumulate the residues by CRT until $M^2N\ge (U-L)^2$.

Let $r\in[0,M)$ be the CRT result and $C=\lceil(L-r)/M\rceil$. Then $W=r+M(C+x)$ for an integer $0\le x\le(U-L)/M\le\sqrt N$. The polynomial $(r+M(C+X))^2-b^2$ can be made monic modulo $N$ by multiplying by $M^{-2}$. May’s full-modulus univariate theorem with degree two, including the endpoint using its fixed-constant form, recovers the small roots in polynomial bit time. Verify each $W$ in its interval and retain a proper gcd with $W-b$ or $W+b$. The true root is mixed and $b$ is a unit, so it gives a split. [May, small-root bounds, Theorems 7–8](https://digital.ub.uni-paderborn.de/hsmig/download/pdf/3235#page=38)

## Counting every measurement

Take the largest 42 primes below $2^{24}$, from 16,776,547 through 16,777,213. Their product $P$ has 1,008 bits. This can be checked by trial division up to 4,096 on the 669 integers from 16,776,547 through 16,777,215 and multiplying the primes. The product exceeds $2^{1007}>4E\,2^{1024}$. At level $i\le42$, keeping any $42-i$ of them gives $M B^i\ge P$, since every omitted prime is smaller than $B$. Also

$$
 U-L\le 2bEN/B^i,\qquad 2bE\sqrt N\le4E\,2^{1024}<P.
$$

Thus these $42-i$ primes suffice at that level. At level 42 the public interval is already short enough with $M=1$ whatever the reading. Level $i$ consumes $i+1$ calibration measurements, counting the first and every unsuccessful one, and at most $42-i$ inverse-modulus measurements. The procedure is deterministic and adaptive. Its setup, including selecting the primes, computing frequencies and reducing them modulo $N$, uses public integer arithmetic. For other widths the same product accounting applies whenever the chosen distinct primes below $B$ have product at least $4E\sqrt N$.

## A calibrated phase needs only 20 fine readings

There is a second tradeoff if random coarse calibration is available. Choose $A$ uniformly in $\{1,\ldots,N-1\}$. A nonunit gives a factor by gcd. For a unit, measure the concealed cosine to error at most $1/64$ and accept $|\widehat c|\le2/3$. The true folded turn $z=Y/N=\|Ah/N\|$ then belongs to $[1/8,3/8]$. If $\|Ah/N\|\in[1/6,1/3]$, the anchor is always accepted or yields a factor. Multiplication by $h$ permutes the nonzero residues, and the two corresponding closed arcs contain at least $(N-1)/3$ residues, by checking $N\bmod6$. Thus at most three coarse trials are needed in expectation. The following bound has **20 further fine readings**, each with absolute error $2^{-53}$ in the full normalized sum.

Put $R=2^{51}$ and $\eta=2^{-55}$. Compute each public cosine to error $2^{-59}$, so that the concealed-cosine error is at most $(1+1/32)2^{-54}$. Use one fine observation at $A$ to estimate $z$ to $\eta$ turns by inverting cosine on $[1/8,3/8]$. Its derivative with respect to turns has magnitude greater than four throughout this interval. At step $j=1,\ldots,19$, suppose $|z_{j-1}-z|\le\eta/R^{j-1}$. Consider the three integers $t=R^j,R^j+1,R^j+2$. Select the one for which $t z_{j-1}$ is farthest from $\tfrac12\mathbb Z$, the set of cosine extrema. All three distances can be compared using rational arithmetic.

On the circle of circumference $1/2$, the gaps between $0,z,2z$ are $s,s,1/2-2s$, in some order, where $s=\min(z,1/2-z)\in[1/8,1/4]$. The largest gap is at most $1/4$. Hence after any common translation, one of the three points is within $1/8$ of the point farthest from the extrema. Use the translation $R^j z_{j-1}$ and replace the two offsets $z,2z$ by $z_{j-1},2z_{j-1}$. This loses at most $2\eta$. The chosen center is therefore at distance at least $1/8-2\eta$ from the extrema. The interval of radius $(R+2)\eta=1/16+2\eta$ around it contains $tz$ and stays at distance greater than $1/17$ from the extrema. On that interval cosine is monotone and its derivative in turns has magnitude at least $2\pi\sin(2\pi/17)\ge12\pi/17>2.2$. The sine bound follows by concavity between zero and $\pi/6$.

Query $F(At\bmod N)$, checking the gcd first. A proper gcd splits the input. A frequency zero gives its known cosine exactly. Clip the concealed-cosine estimate to the image of the interval and invert on that monotone branch. Dividing the measurement error by $2.2$ and allowing $2^{-60}$ further turns for numerical inversion still costs less than $\eta$ turns before division by $t$. Dividing by $t\ge R^j$ yields $|z_j-z|\le\eta/R^j$. After 19 steps the error is at most $2^{-1024}$, since $55+19\cdot51=1024$. Therefore $Y$ is within $\sqrt N$ of the public estimate $Nz_{19}$. The full-modulus small-root theorem applied after translation to $Y^2\equiv A^2\pmod N$ finishes, followed by an exact mixed-root and gcd check. Branch selection and trigonometric calculations on rational intervals use polynomial bit work. This is an adaptive paper reduction; the small checks below concern the signed residues and deterministic scaling.

## Bounded checks

The same geometry can be tested at a deliberately coarse precision to exercise several unsuccessful calibrations. Use modulus 1,021, multiplier $B=4$, $E=17/1024$ and $\ell=3$. For every integer $1\le H\le510$, give every reading each of the three errors $-E,0,E$, including the inverse-modulus reading, clamping each result to $[0,1/2]$. Apply the rules above with exact rational arithmetic, continuing to the first calibrated level without the early lattice stop. The 9,360 resulting paths all returned the correct residue of $Y$ modulo three. The numbers of paths finishing after zero through four unsuccessful readings were 3,681, 2,061, 1,512, 1,134 and 972. This checks the phase arithmetic on arbitrary labels, without assuming they are square roots of one. The no-wrap and orientation inequalities hold for all admissible errors by the Lean proofs. [Anchor lemmas](../PrimeFactors/AnchorScale.lean)

The signed-residue step also agrees with direct Salié sums. Using the first anchor drawn by Python’s `Random(20261124).randrange(1,N)` for each input, a $1/256$ grid for the anchor’s full normalized sum and a $2^{-20}$ grid for the inverse-modulus sums, $N=667$ gives $A=178$ and residues $1\bmod5$, $5\bmod7$. The mixed representative $236\equiv26\bmod35$ yields the factor 29. On $N=1763$, $A=1688$ gives $5\bmod7$ and $2\bmod11$. Here $376\equiv68\bmod77$ yields 41. These small checks enumerated the final CRT interval and used three direct sums each, with 1,848 and 5,040 unit terms respectively. The 43-measurement bound uses the deterministic scale choice above and is a paper result. [Direct finite-sum evaluator](../experiments/divisor_samples.py)
