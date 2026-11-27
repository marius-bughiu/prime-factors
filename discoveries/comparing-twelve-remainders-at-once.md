# Grouping twelve remainders to find a factor

If two numbers leave the same remainder when divided by one of the hidden primes, the difference is a multiple of that prime. A greatest common divisor (gcd) with the public product can then reveal it. We can make these useful matches more frequent by assigning the same value to twelve different remainders. Across all 19,546 eligible products of two 12-bit primes, twelve draws per product found a factor on 8,470 products. Direct comparison with the same preliminary checks found one on 2,075. At 2,048 bits the new method still requires an enormous search for useful odds. [Reproducible counts](../research/twelve-residue-panel.json)

For a small example, give the search only $N=1{,}040{,}279$ and eight random draws from seed 2. Two of those draws, 993,869 and 88,994, receive values 1,001,365 and 227,462. Their difference is 773,903. Taking its gcd with $N$ gives 1,009, and division gives 1,031. Direct comparison and comparison of twelfth powers both miss on these eight draws. The search computes the values using arithmetic modulo $N$ and needs neither prime to do so. [Implementation](../experiments/twelve_residue_collision.py)

## Why twelve remainders share a value

For a sample $x$, compute

$$J(x)=\frac{(x^6-45x^4+135x^2-27)^2}{(x^2+3)^6}\pmod N.$$

Screen out exceptional samples using the gcd of $N$ with the product of $x$, $x\pm1$, $x\pm3$, $x^2\pm3$, and $x^2\pm6x-3$. A proper gcd at this stage already reveals a factor. For every prime $p>864$, at most thirteen remainders are exceptional. For every regular $x$ modulo $p$, the solutions of $J(y)=J(x)$ consist of the two signs of each of the following six values:

$$x,\quad \frac{3x-3}{x+3},\quad \frac{x-3}{x+1},\quad \frac{-3}{x},\quad \frac{-x-3}{x-1},\quad \frac{-3x-3}{x-3}.$$

All twelve are distinct and regular. Clearing denominators gives an exact product of twelve linear factors in $y$. Lean checks the identity, the absence of repeated values on regular inputs, and the count of exceptions. These transformations are powers of the rotation $x\mapsto(3x-3)/(x+3)$ followed optionally by the reflection $x\mapsto-x$. Rational functions invariant under a finite group of fractional linear transformations are classical. The displayed function, its proof and the experiment were implemented in this project. [Lean proof](../PrimeFactors/TwelveResidueCollision.lean) · [Gow and McGuire on invariant rational functions](https://arxiv.org/abs/2105.11247)

Let $r_p,r_q$ be the counts of regular remainders modulo the two primes. Fix one regular sample. For a second sample there are exactly $12(r_p+r_q-24)$ possible regular remainder pairs that match its value at exactly one prime. Direct equality gives $r_p+r_q-2$. The Chinese remainder theorem makes each such pair equally likely under independent uniform sampling among regular residues modulo $N$. The first count exceeds eleven times the second for all distinct primes above 864. The extra arithmetic to form the values still costs time. [Exact comparison](../PrimeFactors/TwelveCollisionBatch.lean)

## What the proof says at 2,048 bits

For any two distinct 1,024-bit primes, take $2^{511}$ independent uniform regular samples with replacement. The probability that some pair has equal values at exactly one prime exceeds 95%. The upper bound for direct equality on those same samples is $7/16$, or 43.75%. The proof counts words without any repeated value and accounts for pairs that match at both primes. It applies to every such prime pair, regardless of how the primes were chosen. It is a theorem about ideal random samples. The bounded experiments below use a seeded generator for reproducibility. [Counting proof](../PrimeFactors/UniformFiberBirthday.lean)

The sample count is about $6.7\times10^{153}$. Even storing just one 256-byte remainder for each draw would take about $1.7\times10^{156}$ bytes. This gives a sufficient sample budget for this method. It places no lower bound on other factoring methods. Counting exactly how many distinct keys the product admits would itself yield the primes in at most four quadratic tests. Computing that count cheaply remains open. [Probability theorem on the actual keys](../PrimeFactors/TwelveSeedBirthday.lean) · [Recovering factors from the count](counting-twelve-residue-keys.md)

## How we find a matching pair

Normalize all the keys with one modular inverse for the batch. For distinct public keys $v_i$, construct $F(T)=\prod_i(T-v_i)$. Then $F'(v_i)=\prod_{j\ne i}(v_i-v_j)$. A product tree and remainder tree evaluate the derivative at all the keys. A row with a nontrivial gcd is scanned for a pair whose difference gives a proper factor. This also works when different entries in the same row pick up both primes. A global repeated key is checked separately using its twelve linear comparisons. In particular, when a raw comparison succeeds, either its grouped values already split the product or the ordinary equality comparison within that repeated key does. [Derivative and preservation proofs](../PrimeFactors/TwelveCollisionBatch.lean) · [Polynomial arithmetic in factoring](https://specfun.inria.fr/bostan/publications/BoGaSc07.pdf)

| Prime bits | Products | Draws per product | Raw remainders | Direct with same screen | Twelfth powers | Twelve-remainder map |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 12 | 19,546 | 12 | 796 | 2,075 | 4,149 | 8,470 |
| 20 | 512 | 128 | 11 | 13 | 54 | 106 |
| 24 | 256 | 256 | 1 | 1 | 8 | 17 |

Counts are products split. The first row covers every pair of distinct 12-bit primes whose product has 24 bits, with one fixed seed per pair. The other two use seeded, without-replacement samples of eligible pairs. On exactly the same draws, the new method preserved every success of direct comparison with the same screen and added 6,395, 93 and 16 successes, respectively. Nineteen small products split by checking different transformations within a shared public key. On the 20-bit sample, elapsed time over all 512 products was 2.11 seconds for the map, 1.99 seconds for the direct screened method, and 1.98 seconds for twelfth powers. One run on a shared machine supports only a rough timing comparison. The proofs concern these particular methods. A comparison to the fastest general-purpose factoring software is a separate experiment. [Counts, timings and parameters](../research/twelve-residue-panel.json) · [Panel generator](../experiments/twelve_residue_panel.py)

The normal benchmark checks the two kinds of successful comparisons separately. Lean verifies 65,497 × 65,521 from a pair of distinct public keys and 1,009 × 1,151 from a shared key resolved using its signed transformations. On each of the fresh and crossed 2,048-bit products, all four methods tried the same 128 draws and found no factor. The full input remains unresolved in both results. [Benchmark inputs and expected results](../benchmarks/twelve-residue-collision.json)
