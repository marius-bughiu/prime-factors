# What stopping a square test reveals about the primes

At $N=2{,}183$, stop a scan after 23 positions. Exactly 936 eligible targets produce a hit and 108 miss. The difference is 828. Divide by 23 and add one to recover **37**. The fraction of eligible targets that hit also gives the other prime, **59**. Lean proves both formulas for every product of two distinct odd primes. Computing the count cheaply from a large product remains open. In the small example, direct measurement took 2,183 Jacobi evaluations and 12,411 gcd tests. The gcd tests already found factors during the count. [Proof](../PrimeFactors/CircleMarkMidcutReadout.lean) · [Measured counts and work](../benchmarks/stopping-rank-readout.json)

## Where to stop

Write $N=pq$ with $p<q$. A target $a$ is eligible if its Jacobi symbol modulo $N$ is $-1$. At positions $i=1,2,\ldots$ test $\gcd(i^2-a,N)$. An eligible target is a square modulo exactly one of the two primes, and a hit returns that prime. Use $K=\lfloor\sqrt{N}/2\rfloor$ as the last position. This cutoff uses only the product.

Half the eligible targets are squares modulo $p$. Those targets' first-hit positions are uniform from 1 through $(p-1)/2$. The other half are squares modulo $q$, with positions uniform from 1 through $(q-1)/2$. The choice of $K$ gives $(p-1)/2\le K\le(q-1)/2$. The smaller prime’s half of the population has therefore finished. Every position through $K$ gets the same additional contribution from the larger prime. [First-hit distribution](../PrimeFactors/CircleMarkTargetFrequency.lean) · [Cutoff bounds](../PrimeFactors/CircleMarkMidcutReadout.lean)

Let $H$ and $M$ count eligible hits and misses. Give every residue a score of $+1$ for a hit, $-1$ for an eligible miss and zero for an ineligible residue. There are two readings.

| Reading supplied | Exact value | Factor recovered |
| --- | --- | --- |
| Signed total $D=H-M$ over all $N$ residues | $K(p-1)$ | $p=1+D/K$ |
| Fraction $f=H/(H+M)$ among eligible residues | $1/2+K/(q-1)$ | $q=1+K/(f-1/2)$ |

For 2,183 the signed total gives $1+828/23=37$. The hit fraction gives $1+23/(26/29-1/2)=59$. For $2{,}701$ the same public rule stops at 25, giving 1,098 hits and 198 misses. The signed total recovers 37 again, and the fraction $61/72$ recovers 73. All 10,109 residues across five small products were classified directly. [Reproduce the census](../experiments/stopping_rank_readout.py) · [Exact two-factor recovery](../PrimeFactors/CircleMarkMidcutReadout.lean)

## How much precision does the reading need?

The smaller prime is odd. If an external measurement of $D$ has absolute error strictly less than $K$, the nearest odd integer to $1+D/K$ is the correct prime. At 2,183, rounding the true count 828 to 830 still recovers 37. Rounding to 800 predicts 35, which fails division. For 187 the true total is 60 and $K=6$. At 66 there is an exact tie and rounding up chooses 13 in place of 11. Since each missing residue changes the signed total by at most one, a tally that omits fewer than $K$ residues still suffices. [Rounding proof and tie example](../PrimeFactors/CircleMarkMidcutPrecision.lean)

For distinct 1,024-bit primes, $K\ge2^{1022}$ and $N/K<2^{1026}$. Thus an absolute error below $2^{-1026}$ in the mean score $D/N$ suffices for exact recovery. Even an error of at most $2^{-64}$ confines the smaller prime to at most $2^{962}$ odd integers. This is a bound on candidates given the reading. The width of the factor interval already known from the product varies by input. [Exact rounding](../PrimeFactors/CircleMarkMidcutPrecision.lean) · [Coarse-reading interval](../PrimeFactors/CircleMarkMidcutWindow.lean)

Sampling is one way to attempt that measurement. For a uniform residue with score $Y$, the ordinary estimate $1+NY/K$ has mean $p$ and variance strictly greater than $N$ for every pair of distinct odd primes. Getting root-mean-square error below one by averaging independent draws with replacement needs more than $N$ draws. Sampling distinct residues uniformly still needs more than $N/2$ draws for that accuracy. For a 2,048-bit product, even root-mean-square error below $2^{962}$ needs more than $2^{123}$ independent draws. These statements concern the sample average. An RMS error is a property of repeated samples, while the rounding condition above is an absolute error on a particular supplied reading. [Independent draws](../PrimeFactors/CircleMarkMidcutSampling.lean) · [Sampling without replacement](../PrimeFactors/CircleMarkMidcutWithoutReplacement.lean) · [Coarse precision](../PrimeFactors/CircleMarkMidcutWindow.lean)

For $N=15$, enumerating every subset of 12 residues gives mean squared error exactly 1. Across the 105 subsets of size 13, it falls to $8/13$. [Exhaustive sampling control](../benchmarks/stopping-rank-readout.json)

## What if we let every scan finish?

Over uniform eligible targets, the **mean first-hit position** is $(p+q+2)/8$. Multiply it by eight and subtract two to get the sum of the primes. Together with $N$, that sum determines the factors as the roots of $x^2-(p+q)x+N$. The second moment is $[p(p+1)+q(q+1)]/24$. For $2{,}183$, the mean is $49/4$, giving $p+q=96$. The first target selected from the product hits at position 8. One target can differ considerably from the population mean. [Lean moments of the actual stopping position](../PrimeFactors/CircleMarkStoppingMoments.lean) · [Five exact population averages](../benchmarks/stopping-rank-readout.json)

The known product fixes $p+q$ modulo four. When $N\equiv3\pmod4$, it fixes the sum modulo eight. This lets us round a supplied mean with error less than $1/4$ in the first case, or less than $1/2$ in the latter. Bringing the ordinary independent sample average below even $1/2$ root-mean-square error requires more than $2^{2044}/3$ draws for two 1,024-bit primes. [Rounding to the permitted sums](../PrimeFactors/CircleMarkStoppingDecoder.lean) · [Exact sampling variance](../PrimeFactors/CircleMarkStoppingPrecision.lean)

## What if we only count early hits?

Before either prime’s half-period ends, each first-hit position has the same probability $d=1/(p-1)+1/(q-1)$. With $N$ known, an exact measurement of that probability already gives Euler’s totient through $(1+d)\varphi(N)=N-1$. The first position alone has exactly $(p+q-2)/2$ eligible hits. Keeping only a position conditional on an early hit leaves a uniform distribution over the observed positions. [Counts, conditioning and totient identity](../PrimeFactors/CircleMarkEarlyReadout.lean)

The products $2{,}501=41\cdot61$ and $2{,}701=37\cdot73$ illustrate what short scans can hide. Through position 18 both give probability $1/24$ at every position and probability $1/4$ of a miss. Their full mean positions are 13 and 14. The normalized short-scan observations are identical. Each known product combined with the exact $1/24$ still gives its own sum. [Checked histogram identity](../PrimeFactors/CircleMarkEarlyReadout.lean) · [Raw counts for both products](../benchmarks/stopping-rank-readout.json)

Suppose instead we estimate $d$ from how often $T$ independently drawn eligible targets hit within the first $L$ positions, using the hit fraction divided by $L$. At full width with $1\le L\le2^{256}$, RMS error below $2^{-2046}$ in that estimate requires $TL>2^{3068}$. Accounting for early stops still leaves more than $3\cdot2^{3066}$ expected scalar gcd tests. The exact rank and score identities use finite arithmetic. The analytic input studied elsewhere in the project concerns finding a small eligible target. It does not evaluate these population averages. [Sampling a capped hit count](../PrimeFactors/CircleMarkCappedSampling.lean) · [Scope of the analytic input](../docs/research.md)
