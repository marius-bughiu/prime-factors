# When does a short search for a 2,048-bit product have a guaranteed hit?

Take any 1,024-bit prime between $79/128$ and $82/128$ of $2^{1024}$. A published prime-gap estimate under the Riemann hypothesis guarantees it has at least one larger prime partner for which the following search finds both factors in at most **16,598 square tests**. The search takes only the product. The guarantee concerns a suitable choice of partner for each smaller prime. An independently chosen partner can fall outside the range the search checks. [Lean theorem `partner`](../PrimeFactors/PrimeGapMultiplier.lean) · [Carneiro, Milinovich and Soundararajan, Theorem 5](https://arxiv.org/pdf/1708.04122#page=5)

For example, the same search found the two primes of our constructed 2,048-bit input on test **10,176**. It exhausted its budget on both full-size comparison inputs. All three used the same starting rule. The successful example has a Lean certificate for the product, the primality of both factors, and the exact test number. [Three benchmark inputs and expected outcomes](../benchmarks/prime-gap-blocks.json) · [Search implementation](../experiments/interior_prime_family.py)

## How the product tells us what to test

Write the product as $N=pq$. If $q$ is close to $3p/2$, the integer $S=3p+2q$ lies just above $\sqrt{24N}$. At that integer, $S^2-24N=(3p-2q)^2$. Compute the square root $d$ of this difference and take the greatest common divisor of $N$ and $(S+d)/2$. This gives one of the primes, and division gives the other. Neither prime is an input to these calculations. [Square and gcd proof](../PrimeFactors/WeightedTracePrefix.lean)

Let $f$ be the first integer at least $\sqrt{24N}$. Start at the multiple of six at or immediately below $f$. In each of 8,299 blocks of six consecutive integers, check only the residues 1 and 5, skipping any label below $f$. For an input coprime to six, every actual square occurs at one of these two residues. This last saving applies regardless of the distance between the primes. [Lean proof of the skipped residues](../PrimeFactors/SixTraceResidues.lean)

## Why there is a partner

Set $y=3p/2$. The published estimate says that for real $x\ge4$, there is a prime between $x$ and $x+(22/25)\sqrt{x}\log x$, assuming RH. Take $x=y-(11/25)\sqrt y\log y$. The one-sided estimate now gives a prime $q$ within $(11/25)\sqrt y\log y$ of the desired center. Both numbers have 1,024 bits in our chosen range. The estimate is an explicit premise in Lean. The pinned Riemann repository specifies the zeta-zero statement used by the published result. [Prime-gap estimate](https://arxiv.org/pdf/1708.04122#page=5) · [Pinned zeta statement](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab/src/Statements.lean)

The excess of the true label above its starting point is $2(\sqrt q-\sqrt y)^2$. Dividing the distance $|q-y|$ by $\sqrt q+\sqrt y$ bounds that excess by $(8/81)(\log y)^2$. At 1,024 bits, $\log y<710$, so the excess is less than 49,788. Even after accounting for the starting remainder modulo six, 8,299 blocks suffice. The general bound in `centered` also applies at other sizes whenever $y\ge16$ and $100\log y\le\sqrt y$. [Centered bound and full-size specialization](../PrimeFactors/PrimeGapMultiplier.lean)
