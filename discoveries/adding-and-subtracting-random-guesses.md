# Can two random guesses reveal a hidden prime?

Suppose we know only the product of two distinct 1,024-bit primes. We pick two positive integers independently, giving smaller integers at least as much probability as larger ones. Even the best choice of those probabilities gives **less than one chance in $2^{1022}$ per pair** of finding a prime through their sum. The same limit holds for their difference when we draw both numbers from the same distribution. These are limits on the two sampling rules. They leave open how well a different calculation on the product might work. [Sum proof](../PrimeFactors/TwoDrawSampling.lean) · [Difference proof](../PrimeFactors/DifferenceSampling.lean)

## What an ideal choice would tell us

Let $N=pq$ with odd primes $p<q<2p$. Choose the first integer uniformly from 1 through $a$ and the second uniformly from 1 through $b$, with $a\le b$. A pair succeeds if the greatest common divisor of $N$ and its sum lies strictly between 1 and $N$. This frequency is defined entirely by $N,a,b$. Lean proves that **every pair of lengths with the highest possible frequency has $b+1=p$ or $b+1=q$**. A way to locate such a length cheaply from $N$ would give a prime directly. Counting all the hits in a rectangle already calculates gcds that can reveal a factor.

Put $P=p-1$ and $Q=q-1$. The highest possible probability for independent draws with decreasing probabilities is the larger of

$$
B=\frac{P+Q-1}{PQ},\qquad C=\frac{3P-Q}{P^2}.
$$

Uniform draws with lengths $(P,Q)$ attain $B$. Lengths $(P,P)$ attain $C$. The first choice is at least as good exactly when $(q-p)^2\ge p-1$. The bound includes unequal distributions and infinite supports. Their best possible performance is already attained by one of these two finite choices. [Counting, attainment, and readout](../PrimeFactors/TwoDrawSampling.lean)

| Product | Highest probability for a sum | One maximizing pair of lengths | Prime obtained from the larger length |
| --- | ---: | ---: | ---: |
| $77=7\times11$ | $15/60=1/4$ | $(6,10)$ | $10+1=11$ |
| $143=11\times13$ | $18/100=9/50$ | $(10,10)$ | $10+1=11$ |

To find these example rectangles from the product alone, we scored all ordered lengths through one period. On 77 this used 153 gcds to mark the possible sums, then 3,003 rectangle scores and one cutoff gcd. The first gcd with a proper factor occurred at sum 7. On 143 the corresponding counts were 285, 10,296 and one, with the first factor at sum 11. A six-rectangle budget on 77 encountered no factor. The computation records both the gcd seen while scoring sums and the gcd obtained from the best length. [Benchmark inputs and outputs](../benchmarks/two-draw-sampling.json) · [Product-only scan](../experiments/monotone_divisor_sampling.py)

For a single prime $d$, a whole block of $d$ choices for the second draw hits once per first draw. When both remaining prefix lengths $i,j$ are shorter than $d$, precisely $\max(0,i+j+1-d)$ pairs have a sum divisible by $d$. Applying these counts for $p$ and $q$ bounds the fraction in every rectangle, including rectangles longer than the product. If both lengths are below $p$, either only the $p$ diagonal can be reached, or the two diagonal counts increase in density up to the corner $(P,P)$. If the larger length reaches $p$, the completed blocks give the bound $B$. The strict inequalities away from $b=P,Q$ give the factor readout. Applying summation by parts once in each coordinate extends the rectangle bound to all independent decreasing probability weights. [Single-draw comparison](sampling-for-a-hidden-prime.md) · [Formal counting proof](../PrimeFactors/TwoDrawSampling.lean)

## What changes for a difference

For a difference, suppose both independent draws follow the **same** decreasing distribution. The exact maximum chance that their difference shares a proper factor with $N$ is $(p+q-2)/N$. Uniform draws from 1 through the public product $N$ attain this maximum. For example, the probability on 77 is exactly $16/77$. A tie gives difference zero and gcd $N$, so it contributes no success. Equal marginals matter. Fixing the first draw at 1 and drawing the other uniformly through 57 gives $13/57>16/77$. [Sharp bound and uniform example](../PrimeFactors/DifferenceSampling.lean)

To prove the result, let $C_m$ be the probability that the two draws agree modulo $m$. The success probability is $C_p+C_q-2C_N$. Write the ordered probabilities of the $N$ residue classes as $c_r$ and subtract $1/N$ from each. Grouping these centered numbers into columns by residue modulo any $m\mid N$ cannot increase their sum of squares. The order of the masses is what makes this inequality possible. The inequality gives $C_m-1/m\le C_N-1/N$ twice, once for each prime. Lean also checks the passage from a distribution on all positive integers to these finite residue probabilities. [Folding inequality, normalization and exact count](../PrimeFactors/DifferenceSampling.lean)

These per-pair bounds apply in particular to independent samples from weights proportional to $x^{-s}$ for real $s>1$. Testing all pairs from one collection of draws makes more than one comparison per draw. A different cost analysis is needed for selecting those pairs or processing them in batches. The bounds here use elementary arithmetic and probability and have no hypothesis on zeta zeros. [Relation to the Dirichlet sampling proposal](sampling-for-a-hidden-prime.md#connection-with-the-riemann-repository)
