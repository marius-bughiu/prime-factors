# One circle count lands next to a prime factor

Start with **77**. Count the ordered pairs of residues satisfying $x^2+y^2=t$ modulo 77. Each of the four targets below gives **96 points**. Now ask how many first coordinates $x$ have **exactly two** possible second coordinates $y$. At $t=2$ the answer is **12**, one above the prime 11. At $t=3$ it is **8**, one above the other prime, 7. A Jacobi symbol of $-1$, computable from the target and the product, guarantees this one-away rule. [Lean proof](../PrimeFactors/CircleBranchReadout.lean) · [Checked examples](../PrimeFactors/CircleBranchExamples.lean)

| Target $t$ | Jacobi symbol | No $y$ | One $y$ | Two $y$ | Four $y$ | Total points |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | +1 | 42 | 4 | 16 | 15 | 96 |
| 2 | −1 | 47 | 0 | 12 | 18 | 96 |
| 3 | −1 | 49 | 0 | 8 | 20 | 96 |
| 6 | +1 | 53 | 0 | 0 | 24 | 96 |

Each column counts values of $x$. Multiplying each column by its number of possible $y$ values and adding gives the last column. The census uses the product and target as inputs. [Reproducible census](../experiments/circle_projection_counts.py) · [Counts and work](../benchmarks/circle-projection-counts.json)

## Why the two-lift count isolates one prime

Let $N=pq$ with distinct odd primes. A target with Jacobi symbol $-1$ is a nonzero square at exactly one prime. Name that prime $p$ for this argument. Exactly half the unit targets pass the public Jacobi check, so finding a suitable target takes two independent uniform unit draws on average. [Local signs](../PrimeFactors/CircleBranchCount.lean) · [Exact half of the units](../PrimeFactors/CharacterDivisorColumn.lean)

Over a prime field the possible values of $y$ are a pair $y,-y$, a single zero, or the empty set. At $p$, the two roots of $x^2=t$ each give one lift. At $q$, the target is a nonsquare, so every occupied first coordinate has two lifts. The Chinese remainder theorem multiplies the local counts. A global first coordinate has exactly two lifts precisely when its component at $p$ has one and its component at $q$ has two. If $C_q$ is the total number of circle points modulo $q$, this gives $2(C_q/2)=C_q$ such first coordinates. [Local fibers and product proof](../PrimeFactors/CircleCoordinateFibers.lean)

For every nonzero target, $C_q=q-\chi_4(q)$, where $\chi_4(q)=1$ for $q\equiv1\pmod4$ and $-1$ for $q\equiv3\pmod4$. Given the exact count $T$, testing $T-1$ and $T+1$ for divisibility of $N$ therefore recovers a prime. The full circle has $C_p C_q$ points for every unit target. [Readout theorem](../PrimeFactors/CircleBranchReadout.lean) · [Lean proof of the total](../PrimeFactors/SphereCircleIdentity.lean) · [Tóth on quadratic congruence counts](https://arxiv.org/abs/1404.4214)

## What it costs to get the count

There is a second reading that dispenses with the circle points. Mark $x$ when $\gcd(t-x^2,N)>1$. Under the same Jacobi condition the congruence $x^2=t$ can never hold at $q$. It holds in two residue classes at $p$. Each has $q$ lifts modulo $N$, so there are **exactly $2q$ marks**. Halving this count gives $q$ itself. Every individual mark already gives the proper divisor $p$ by the same gcd. In the example with $t=2$, there are 22 marks, and the first, $x=3$, gives $\gcd(2-9,77)=7$. [Exact count and proper-gcd equivalence](../PrimeFactors/CircleBranchCount.lean)

The small census builds a table of all $N$ squared residues and looks up one entry for each of the $N$ first coordinates. It also checks one gcd per first coordinate. No faster way to obtain the exact count at full size follows from the identity. With independent uniform $x$, a mark occurs with probability $2/p$ per draw, so the expected number of draws until the first mark is $p/2$. For a 1,024-bit square-side prime this is at least $2^{1022}$. [Counting proof](../PrimeFactors/CircleBranchCount.lean) · [Census implementation](../experiments/circle_projection_counts.py)

Sampling a uniform circle point and checking its coordinate changes the probability to $2/(p-\chi_4(p))$. For a 1,024-bit $p$ the **relative change** in the per-draw probability is less than $2^{-1022}$ in either direction. At modulus 15, target 7 lowers the probability from $2/3$ to $1/2$, while target 11 raises it from $2/5$ to $1/2$. These comparisons grant an independent uniform circle point for free. [Exact rates and full-size bound](../PrimeFactors/CircleBranchSampling.lean)

## One count at target one reveals a factor or sum on about three quarters of products

Let $K$ count **ordered pairs of circle points with the same first coordinate**, including a point paired with itself, on $x^2+y^2=1$. An $x$ with $j$ lifts contributes $j^2$ to $K$. For example, on 77 the count is $4+4\cdot16+16\cdot15=308=4N$. Lean proves $K/4=(p-\chi_4(p)-1)(q-\chi_4(q)-1)$. [Collision and mixed-sign counts](../PrimeFactors/CircleCoordinateFibers.lean) · [Arithmetic specialization](../PrimeFactors/CircleCollisionReadout.lean)

| Public condition after obtaining $K$ | What it gives | Checked example |
| --- | --- | --- |
| $N\equiv3\pmod4$ | $(N-K/4)/2$ is the prime congruent to 3 modulo 4. | $N=15$, $K=36$ gives $3$. |
| $N\equiv1\pmod4$ and $K\ne4N$ | $(N+4-K/4)/2$ is the prime sum. | $N=65$, $K=132$ gives $18$, hence $5\cdot13$. |
| $K=4N$ | Both primes are 3 modulo 4. The count is fixed by the product. | $N=161$, $K=644$. |

For all pairs of distinct 1,024-bit primes producing a 2,048-bit product, the share with $K\ne4N$ is within $1/4160$ of three quarters using the published unconditional Bennett–Martin–O’Bryant–Rechnitzer estimate. The Ernvall-Hytönen–Palojärvi prime-count estimate under Dirichlet GRH tightens this to $2^{-148}$. The local Lean theorems take the respective numerical endpoint estimates as hypotheses. The separate GRH verification concerns Dirichlet L-functions. All three readout formulas are elementary. [Population theorem and premises](../PrimeFactors/CircleCollisionPopulation.lean) · [Unconditional progression estimate](https://personal.math.ubc.ca/~bennett/BeMaObRe-IJM-2018.pdf#page=5) · [GRH progression estimate](https://arxiv.org/pdf/2003.01925#page=2) · [Independent GRH verification](https://math.mit.edu/~drew/grh/)

Given an exact $K$, the arithmetic in the table uses a constant number of operations on large integers. Obtaining $K$ is the bottleneck. The recorded census uses $N$ entries in the square table and $N$ first-coordinate lookups to tabulate all the fiber sizes and sum their squares. Sampling two independent circle points measures a collision **probability**, $K/(C_p C_q)^2$. Turning that probability into the integer $K$ also requires the population size and adequate precision. [Census and verified outputs](../benchmarks/circle-projection-counts.json)
