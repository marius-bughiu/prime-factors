# When the product is close to the largest possible square

Suppose you are given a 2,048-bit number and told that it is the product of two 1,024-bit primes. If its binary expansion begins with **511 ones**, one integer square root suffices to recover both primes. You can check those digits before attempting to factor the number. The same calculation can succeed on some inputs outside that range. It missed both of our pre-existing full-size comparison products. [Lean proof](../PrimeFactors/EndpointOffsetProduct.lean) · [Benchmark inputs](../benchmarks/endpoint-offset-product.json)

## A small example

For $N=2,257$, suppose both factors are six bits long. Each lies below $C=64$. The calculation below predicts that their distances below 64 multiply to 81 and add to 30. Since $30^2-4\times81=576=24^2$, those distances differ by 24. They must be 27 and 3. Subtracting from 64 gives $37$ and $61$, and $37\times61=2,257$.

## What the product tells us

Write $N=pq$ with $p\le q\le C$ and put $a=C-p$ and $b=C-q$. Multiplication gives

$$ab=C^2-C(p+q)+N.$$

For primes greater than 3, the sum $p+q$ and $N+1$ have the same remainder modulo $t=\gcd(24,2(N+1))$. The project has already proved that this is the largest single modulus for the sum in the model that allows all local unit residues. Consequently the least nonnegative remainder

$$r=((C-1)(C-N))\bmod(Ct)$$

equals $ab\bmod(Ct)$. Our test guesses that $ab=r$. The public decoder computes $s=(C^2+r-N)/C$ and takes the integer square root of $s^2-4r$. If the guess was correct, $s=a+b$ and the root is $a-b$. The final check verifies both the product of the returned factors and the product of their distances from $C$. Lean proves that the test returns the actual pair **exactly when** $ab<Ct$. A hit takes one root plus a fixed number of integer operations. [Decoder and both directions of the proof](../PrimeFactors/EndpointOffsetProduct.lean) · [Earlier single-residue classification](../PrimeFactors/ConstantWeightedResidue.lean)

There is also a way to read off the search cost. The largest possible factor sum consistent with the endpoint bound and this remainder is $(C^2+N-r)/C$. Its distance above the true sum, measured in steps of size $t$, is exactly $\lfloor ab/(Ct)\rfloor$. The single test checks step zero. This is a search from the upper end of the factor-sum interval. The usual Fermat method starts at the square just above $N$. [Exact step count](../PrimeFactors/EndpointOffsetProduct.lean) · [Lehman's account of Fermat's method](https://doi.org/10.1090/S0025-5718-1974-0340163-2)

## How to tell in advance that the test will work

A public integer $h$ with $(C-h)^2\le N$ and $0\le h\le C$ guarantees $ab\le h^2$. To see why, $p+q\ge 2\sqrt N\ge2(C-h)$, so $a+b\le2h$. The product of two nonnegative numbers with this sum is at most $h^2$. Whenever $h^2<Ct$, the predicted remainder is exact. The Lean proof uses only integers.

For $C=2^{1024}$, every eligible product has $t\ge4$. If $N\ge2^{2048}-2^{1537}$, we can take $h=2^{512}+1$. That is the 511-leading-ones guarantee. If $t=24$, the guarantee extends down to $2^{2048}-2^{1539}$, or 509 leading ones, by taking $h=4\cdot2^{512}+9$. We checked the ordinary Fermat baseline over these entire ranges. Every input with 511 leading ones splits at the first ordinary midpoint. Every input with 509 leading ones splits within nine ordinary midpoints. The potentially large saving lies outside these guaranteed ranges, when one offset is much smaller than the other. [Proof for both ordinary budgets](../PrimeFactors/EndpointOffsetProduct.lean)

## Full-size comparisons

We made two deliberately constructed products that share one prime. Set $C=2^{1024}$ and $q=C-18679\cdot2^{466}+1$. For the product with 529 leading ones we used the other prime $C-25725\cdot2^{480}+1$. The public guarantee applies. Ordinary Fermat also finds this pair on its first midpoint.

For the second product we used $p=C-22603590534\cdot2^{512}+1$. This input begins with 477 ones. The two distances have 547 and 481 bits. Their product lies between $6C$ and $7C$, while the public modulus is $12C$. Reducing modulo $4C$ gives the wrong guess. The full public modulus gives the exact offsets in one square root. Ordinary Fermat would pass **63,865,288,128,591,800,642** consecutive unsuccessful midpoints before reaching this pair. We calculated this count from the recovered factors. We did not time a scan of that length. The benchmark checks the primes and their product in Lean; its search receives the product alone. [Inputs and expected decimal factors](../benchmarks/endpoint-offset-product.json) · [Search and certificate generation](../scripts/endpoint_offset_benchmark.py)

On the separately generated fresh comparison and the existing crossed comparison, the test spent one square root each and returned neither pair. The large distance saved on a constructed example does not give a general factoring algorithm. [How the fresh comparison was made](certified-fresh-control.md)

## How many full-size pairs can this test reach?

Choose uniformly among sorted pairs of distinct 1,024-bit primes whose product has 2,048 bits. The chance that the single upper-end test returns the actual pair is **less than one in $2^{987}$**. This is an unconditional finite bound. Each hit requires $ab<24C$. Grouping the smaller offset into intervals between consecutive powers of two bounds the number of pairs under that hyperbola. Keeping only the two allowed offset residues modulo six gives at most $513\lfloor25C/9\rfloor$ eligible pairs in the window. We divide this count by the project's previously proved lower bound on the total eligible population. The result measures this one test. [Population proof](../PrimeFactors/EndpointOffsetPopulation.lean) · [Full-size pair count](../PrimeFactors/ChebyshevPrimeSample.lean)
