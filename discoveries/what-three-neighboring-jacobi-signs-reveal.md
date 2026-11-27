# What three neighboring Jacobi signs reveal

Three carefully chosen readings of a product obey a rule that three independent coin flips break half the time. The same rule works for every odd product. Learning the two primes takes a different piece of information. For 77, for example, two of the readings were both zero at exactly 19 positions. Subtracting one gives the prime sum 18, from which we recover 7 and 11. Obtaining 19 by direct counting took all 77 positions.

Given only the product $N$, write $J(t)$ for the Jacobi symbol of $t^2-4$ modulo $N$. This is a public calculation returning $-1$, $0$ or $1$. Choose a uniform residue $s$ and read $J(2s-2)$, $J(2s+2)$ and $J(s)$. The first two arguments differ by four. Whenever both readings are nonzero, their product equals the third. In fact, for every integer $s$,

$$
J(2s-2)J(2s+2)=\left(\frac{4s}{N}\right)^2J(s).
$$

The product of all three readings can therefore never be negative. Three independent fair signs have a negative product four times out of eight. The argument uses multiplication of Jacobi symbols and the identity $((2s-2)^2-4)((2s+2)^2-4)=(4s)^2(s^2-4)$. [Lean proof of the three-query rule](../PrimeFactors/NeighboringJacobiSamples.lean)

## How much of the pattern depends on the primes?

Suppose $N=pq$ with distinct odd primes $p,q$. For $p,q\ge5$, the total variation distance between the first two readings and two independent fair signs is exactly

$$
1-\frac{(p-3)(q-3)}{pq}.
$$

Total variation distance is the greatest difference in probability that any event can have between two distributions. Here the event that at least one sign is zero attains the displayed difference. For $p,q\ge13$, the distance between the **three** readings and **three independent** fair signs is exactly $1/2$. The negative-product event attains it. [Exact finite histogram](../PrimeFactors/NeighboringJacobiMoments.lean) · [Proof of both distances](../PrimeFactors/NeighboringJacobiSamples.lean)

Two fair coin flips also give a way to reproduce most of the three-reading distribution without knowing $N$. Output the two signs and their product. Relative to this reference, the three actual readings have exactly the small distance shown above. Across $k$ independent choices of $s$, the distance is $1-[(p-3)(q-3)/(pq)]^k$. For two 1,024-bit primes and at most $2^{40}$ draws, this is below $2^{-980}$. This calculation covers the signs alone. Retaining sample arguments or computing gcds gives a different observation. [Proof for repeated draws](../PrimeFactors/NeighboringJacobiSamples.lean) · [Earlier result for independently chosen arguments](what-random-jacobi-signs-can-reveal.md)

| Product | Pair counts for $--,-+,+-,++$ | Both zero | Two readings vs. two fair signs | Three readings vs. three fair signs |
| ---: | --- | ---: | ---: | ---: |
| 77 | 8, 8, 8, 8 | 19 | 45/77 | 45/77 |
| 221 | 36, 34, 34, 36 | 31 | 81/221 | 1/2 |

## What would recover the factors?

The simultaneous-zero count is exactly $p+q+1$. Modulo each prime, the centered arguments give discriminants $x(x-4)$ and $x(x+4)$. Both vanish at $x=0$. The Chinese remainder theorem gives $p+q-1$ positions with a zero coordinate at either prime. Two further positions mix $4$ at one prime and $-4$ at the other. From the full count $C$ one obtains $S=C-1$ and then $p,q=(S\mp\sqrt{S^2-4N})/2$. [Lean proof of the count](../PrimeFactors/NeighboringJacobiMoments.lean)

The bounded experiment builds a table with $N$ Jacobi evaluations, tallies $N$ pairs and $N$ triples from it, and takes one integer square root to recover the factors. It counted 31 simultaneous zeros for 221, giving sum 30 and factors 13 and 17. The same program checked every residue for all 276 products of distinct odd primes through 97, covering 526,786 residues in total. At full size the direct count needs one table entry per residue. The much cheaper three-sign rule gives no way to read the exact count. [Experiment](../experiments/neighboring_jacobi_samples.py) · [Fixed examples](../benchmarks/neighboring-jacobi-samples.json)

Reproduce the two examples and the exhaustive comparison with `python3 -m experiments.neighboring_jacobi_samples --exhaustive`.
