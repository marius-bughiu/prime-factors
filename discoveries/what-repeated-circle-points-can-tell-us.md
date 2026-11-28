# What repeated circle points can tell us

Two small products illustrate the limits of counting repeats. The circle $x^2+y^2=1$ has **1,120 points modulo 1,189** and **1,152 points modulo 1,147**. Imagine choosing one of the circles by a fair coin, drawing points uniformly with replacement, and revealing only which draws match. Even after **280 draws**, the best possible decision is correct about **53.44%** of the time. The observer knows the two possible sizes. The modulus and the coordinates are hidden in this experiment. [Verified circle sizes](../PrimeFactors/CircleBranchExamples.lean) · [Exact finite calculation](../experiments/circle_projection_counts.py)

## The best decision for these two circles

| Draws | Choose 1,152 if distinct points reach | Best probability of a correct decision |
| ---: | ---: | ---: |
| 2 | 2 | 50.0012% |
| 16 | 16 | 50.1350% |
| 64 | 63 | 50.7659% |
| 160 | 150 | 51.9327% |
| 280 | 249 | 53.4371% |
| 560 | 443 | 57.1528% |

The percentages are truncated to four decimal places. For each draw count we computed both distributions using exact integers. We also independently enumerated all words of length four on alphabets of sizes three and four to check the calculation. [Exact decision table](../benchmarks/circle-projection-counts.json)

Why does counting the distinct labels suffice? A specific pattern with $k$ distinct labels can be filled in $m(m-1)\cdots(m-k+1)$ ways using labels from a population of size $m$. Every word of length $t$ has probability $1/m^t$. Compared with a smaller population, a larger population becomes more likely as $k$ increases. With equal prior probabilities the best decision therefore uses a threshold on $k$. Population estimation from repetitions and the sufficiency of the number of distinct labels are established statistical results. [Lean counting proof](../PrimeFactors/EqualityPatternSampling.lean) · [Threshold and optimality](../PrimeFactors/EqualityPatternThreshold.lean) · [Viswanathan, Orlitsky and Santhanam](https://ita.ucsd.edu/workshop/07/files/paper/paper_621.pdf)

## Required and sufficient samples

Suppose the two possible sizes are $m$ and $m+d$. For $2t\le m$, the square of the difference between any test's two acceptance probabilities is at most $t^2 d^2/m^3$. The proof follows the conditional probabilities after each draw. After $k$ distinct labels, each old label recurs with probability $1/m$, while the probability of a new label is $1-k/m$. It accounts for the dependence between successive repeat observations. [Finite-word bound](../PrimeFactors/EqualityPatternSeparation.lean)

If $d^2=m$, at most $m/4$ draws give at most **5/8** correct decisions under a fair prior. In the other direction, **$12m$ draws suffice for at least 3/4 accuracy under either size**. The constructive test counts equal pairs of draw positions. With $B=\binom{t}{2}$, this count has mean $B/m$ and variance $B(m-1)/m^2$ at population size $m$. Comparing the realization against the midpoint of the two possible means gives the guarantee. The proof permits overlapping pairs of draw positions. [Sample lower bound](../PrimeFactors/EqualityPatternSeparation.lean) · [Collision estimator and variance](../PrimeFactors/EqualityCollisionEstimator.lean)

## What happens at 2,048 bits

There exist two different products of distinct 1,024-bit primes, both 2,048 bits long, whose circle sizes differ by a positive amount below $2^{269}$. The smaller size $m$ is at least $2^{2046}$. Even after as many as **$m/2$ draws**, every test using only the equality patterns of the actual sampled points has an acceptance-probability difference **below $2^{-755}$**. The proof counts enough distinct circle sizes to force the existence of such a pair. The average success rate across products remains open. [Actual circle sizes and observation bound](../PrimeFactors/CircleOrderNeighbors.lean)

The two input products in that comparison have different public values. Algorithms given the product can use its digits and can perform arithmetic on the coordinates. There is also a comparison at a **single** product. Unit targets $t$ in $x^2+y^2=t$ always give the same number of points, so every anonymous repeat test has exactly the same distribution at all those targets, for any number of draws. The two-lift coordinate counts at 77 still distinguish targets 2 and 3. [Same-product equality law](../PrimeFactors/EqualityPatternThreshold.lean) · [Which coordinate count reveals a prime](counting-the-two-lift-coordinates-of-a-circle.md)
