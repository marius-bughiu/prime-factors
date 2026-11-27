# Which guesses give the prime sum?

On $323=17\times19$, the first common repeat of the strided Jacobi sums is 72. The project's earlier square-root calculation finds the factors at its **second guess**. Rejecting 2 as a repeat would discard a correct answer to the original factor search. Lean proves exactly how far apart these two stopping points are for balanced primes. [Two minima in Lean](../PrimeFactors/JacobiPeriodSquareClass.lean) · [Earlier square-root calculation](discriminant-strides.md#a-scaled-square-root-that-determines-both-factors)

## Two stopping points

Suppose $7\le p<q\le2p$ and we know only $N=pq$. Define $g=\gcd(p-1,q-1)$ and the shortest shared repeat $R=(p-1)(q-1)/g^2$. Write $R=c z^2$ with $c$ squarefree, so $c$ consists of the primes occurring to odd exponent in $R$. This also makes $(p-1)(q-1)=c(gz)^2$. The formulas involving $p,q$ explain the stopping points; the searches in the table below received only $N$. [Why $R$ is the period](testing-a-jacobi-stride-period.md#one-base)

For each guess $t=1,2,\ldots$, compute $h=\lfloor\sqrt{\lfloor N/t\rfloor}\rfloor$, using $h=\lfloor\sqrt N\rfloor-1$ at $t=1$. Try the sum $S=N+1-th^2$ by testing whether $S^2-4N$ is a nonnegative square that gives a proper factor pair. The first successful guess is exactly **$c$**. More generally, the successful guesses are exactly $c w^2$ for positive divisors $w$ of $gz$. The reason is that a correct sum is equivalent to $th^2=(p-1)(q-1)$, and the balanced-input rounding theorem recovers the right $h$ at every such scale. [All successful scales](../PrimeFactors/JacobiPeriodSquareClass.lean) · [Rounding proof](../PrimeFactors/DiscriminantStride.lean)

Checking the same guesses for a repeat first succeeds at **$R=c z^2$**. Restricting the sum calculation to valid periods keeps exactly the candidates $R k^2$ with $k\mid g$. At 221 the working sum guesses are 3, 12, 48 and 192. Six and twenty-four illustrate different failures: six repeats from only some starts, while twenty-four repeats from all starts and gives a sum below $2\sqrt{221}$. [Intersection theorem and 221 counterexample](../PrimeFactors/JacobiPeriodScales.lean)

| Product | First successful square-root guess | First shared repeat | Modular powers used to reach that repeat |
|---:|---:|---:|---:|
| 77 | 15 | 15 | 88 |
| 221 | 3 | 12 | 215 |
| 323 | 2 | 72 | 431 |
| 14,647 | 1 | 400 | 15,209 |

The last number was chosen because $96\times150=120^2$ for its prime factors 97 and 151. The direct search tried the scales in order with one sum candidate per scale. The period comparison tested units in increasing order, abandoning each wrong guess on the first failed power. Enumerating the units cost a further $N-1$ gcds and already revealed the smaller prime on each input. These counts describe the specified scans. Discovering a large $R$ or its squarefree part cheaply from an arbitrary product remains open. [Comparison code](../experiments/jacobi_period_scale_compare.py) · [Measured controls](../benchmarks/jacobi-period-scales.json)

## How often can the direct search finish early?

On the repository's existing **constructed 2,048-bit control**, the direct test split the product after six guesses. From those recovered prime factors, the common predecessor divisor is 6 and the shortest shared period has **2,043 bits**, so it is at least $2^{2042}$. The five-guess cutoff on the same number and a six-guess run on the comparison product both remained unresolved. The construction ensured that the totient was six times a square. This is a period diagnosis after the existing split. [Origin of the control](discriminant-strides.md#a-2048-bit-product-recovered-at-the-sixth-scale) · [Budgets and expected outcomes](../benchmarks/predecessor-square.json) · [Replay](../experiments/jacobi_period_scale_compare.py)

Among sorted pairs of distinct 1,024-bit primes whose product has 2,048 bits, fewer than one in $2^{736}$ has even one correct sum scale at most $2^{40}$. For any successful scale $t$, the predecessor product must equal $th^2$. Bound the number of possible roots $h$ at each $t$, then bound the number of possible divisors $p-1$ for each resulting product. This supplies an explicit full-size bound for the earlier asymptotic sparsity estimate. The separate fraction $2^{-978}$ covers the smaller event that the **period itself** is at most $2^{40}$. Both are upper bounds; dividing them would give no estimate of the relative frequency. [Lean count for direct recovery](../PrimeFactors/JacobiSquareClassPopulation.lean) · [Earlier asymptotic estimate](discriminant-strides.md#a-scaled-square-root-that-determines-both-factors)

## What the two comparison products require

| Previously factored 2,048-bit product | Bits in its shortest shared repeat | Proved lower bound on its first successful direct scale |
|---|---:|---:|
| Fresh comparison | 2,046 | Greater than $2^{1079}$ |
| Crossed comparison | 1,439 | Greater than $2^{64}$ |

These are diagnoses made **with the published prime factors**. For a successful scale $t$, every prime occurring to odd multiplicity in $(p-1)(q-1)=ty^2$ must divide $t$. We checked all primes through 25,000. On the fresh comparison we also checked the two distinct 513-bit primes used in its original Pocklington construction; both occur to multiplicity one. Multiplying just the certified odd-multiplicity primes gives the lower bounds above, without requiring the entire factorizations of $p-1$ and $q-1$. Both comparison products therefore exceed the $2^{40}$ budget for both searches. On the fresh comparison the first successful direct scale even exceeds the smaller prime itself. The exact first scales remain unknown. [Lean valuation argument](../PrimeFactors/JacobiScaleValuations.lean) · [Reproduce and check both certificates](../experiments/jacobi_scale_valuations.py) · [Expected bounds and disclosed factor pairs](../benchmarks/jacobi-scale-valuations.json)

## Can the difference grow without bound?

Yes, on specially structured products. For $547{,}606{,}837$, the first square-root guess yields $22{,}501\times24{,}337$. Here $22{,}501=150^2+1$ and $24{,}337=156^2+1$. The shortest shared repeat is $(25\times26)^2=422{,}500$. A second constructed product, $59{,}068{,}927{,}717$, split at scale one into $240{,}101\times246{,}017$, and its shortest shared repeat was $3{,}691{,}777{,}600$. In both controls the program obtained the period from the recovered factors and cross-checked it with modular powers. It did not search through billions of candidates. [Lean example](../PrimeFactors/JacobiSquarePeriodFamily.lean) · [Product-only readout and separate period check](../experiments/jacobi_square_period_family.py) · [Family controls](../benchmarks/jacobi-square-period-family.json)

More generally, choose $A\ge150$ and the fifty linear forms $(A+i)^2 t+1$, $0\le i<50$. Any two prime values at the same positive $t$ give balanced primes with square totient, so scale one works. For indices $i<j$, write $d=\gcd(A+i,A+j)$. Their shortest shared period is $(((A+i)/d)((A+j)/d))^2$. Because $d$ divides $j-i$, it is at most 49. The period is at least $\lfloor A/49\rfloor^4$, so it can exceed any prescribed bound while the direct search still takes one guess. For each fixed $A$, these are distinct forms with positive slopes, nonzero pairwise determinants, and no local obstruction: $t=0$ gives 1 in every form modulo every prime. Kim's unconditional Lemma 2.1 therefore gives infinitely many positive parameters with at least two prime values. Lean proves the algebra, admissibility, exact periods and the transfer from prime hits. The infinitude step uses the cited theorem on paper. [Lean family](../PrimeFactors/JacobiSquarePeriodFamily.lean) · [Kim, Lemma 2.1](https://www.csun.edu/~sungjin/SJK_Totient2-3%281%29.pdf#page=4)

The prime factors can also remain a fixed relative distance apart as the period grows. Use $u_i=1+(200+i)A$ and the forms $t u_i^2+1$ instead. Every common divisor of $u_i,u_j$ divides $(200+j)u_i-(200+i)u_j=j-i$. The same construction now gives $q-p\ge p/300$, $q<2p$ and a shortest period at least $\lfloor 200A/49\rfloor^4$. The scale-one readout still succeeds. This strengthens the earlier square-totient family by letting the period exceed any prescribed threshold while keeping a uniform gap between the primes. [Lean relative-gap theorem](../PrimeFactors/JacobiSquarePeriodFamily.lean) · [Earlier square-totient construction](discriminant-strides.md#a-2048-bit-product-recovered-at-the-sixth-scale)
