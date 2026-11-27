# Two ways to read the prime sum

Knowing the sum of two primes turns factoring into a square-root calculation. For example, if the product is 9,017 and the sum is 198, the squared distance between the primes is $198^2-4\cdot9017=3136$. The primes are $(198-56)/2=71$ and $(198+56)/2=127$. The question is how to get the sum when the product is all we have.

## One digit of a polynomial

Let $\Phi_N$ be the cyclotomic polynomial indexed by the public product $N$. At $N=9017$, evaluating that polynomial at 9 gives remainder **17** on division by 64. In base eight the remainder is written **21**, so its upper digit is 2. This tells us that the sum of the factors is 6 modulo 16. The factors are both seven bits wide. The possible sum lies from 190 through 205 using the proved width bound, so 198 is the only possibility. On this small example the tighter interval is 190 through 198. The product is 2 modulo 3, so one prime is 1 modulo 3. Both primes are odd. Thus $(p-1)(q-1)$ is divisible by 12 and the sum is 6 modulo 12, which already singles out 198. [Lean proof and numerical example](../PrimeFactors/CyclotomicSumDigit.lean)

For $N=pq$ with distinct primes, the polynomial has value 1 at 1 and derivative $(p-1)(q-1)/2$ there. Consequently, modulo $M^2$, its value at $1+M$ is $1+M\,(p-1)(q-1)/2$. One upper digit gives the sum modulo $2M$. For two 1,024-bit primes, $M=2^{1020}$ suffices to locate the exact sum in the interval above $2\sqrt N$. [Derivative literature](https://arxiv.org/abs/1805.05207) · [Local modular decoder](../PrimeFactors/CyclotomicSumDigit.lean)

The missing step is computing that digit from $N$. Computing the whole integer value first takes more than $(p-1)(q-1)\log_2 M$ output bits. Reading the polynomial's coefficients in order also has a concrete cost. From degree two up to the smaller prime $p$, the first nonzero coefficient occurs at degree $p$ itself. Both observations leave open the possibility of a faster direct modular evaluation. Given the primes, the modular value takes just the arithmetic in the formula above. [Output size and first nonzero coefficient](../PrimeFactors/CyclotomicSumDigit.lean)

One possible shortcut is to look up the digit using just the product's remainder modulo some fixed number. For every fixed modulus and every radix $M\ge3$, Lean constructs two products of distinct odd primes with the same remainder but different digits, 0 and 2. These products can use arbitrarily large primes. The general theorem does not prescribe their widths. We checked a separate width-matched example using four published 1,024-bit primes. Both 2,048-bit products end in exactly the same 506 low bits, but their digits at radix $2^{1020}$ are 0 and $7\cdot2^{1014}$. Thus a lookup on those low bits cannot handle both full-size examples. [General theorem and certified examples](../PrimeFactors/CyclotomicDigitPeriod.lean)

### How much of the polynomial value is needed?

For $N=107,683$, the public size bounds and divisibility leave three possible sums. The polynomial value at 4 leaves remainder 7 modulo 9. That small piece of information selects the sum 676 and the primes 257 and 419. We certified the remainder using the known prime pair. Obtaining it cheaply from $N$ alone is still an open step. [Certified radix-three example](../PrimeFactors/CyclotomicRadixLift.lean)

There is a cheap clue available directly from $N$: a guaranteed divisor $W$ of $F=(p-1)(q-1)$. For primes larger than 3 the four possibilities are as follows.

| $N$ modulo 12 | 1 | 5 | 7 | 11 |
| --- | ---: | ---: | ---: | ---: |
| Guaranteed divisor $W$ | 4 | 12 | 8 | 24 |
| Sufficient bits for the supplied residue at 2,048 bits | 2,037 | 2,034 | 2,035 | 2,032 |

Both primes are odd. A product of 3 modulo 4 ensures one prime is 1 modulo 4. A product of 2 modulo 3 ensures one prime is 1 modulo 3. These rules give the four divisors above. The lower and upper bounds on the sum also give an interval for $F$. If that interval contains $C$ multiples of $W$, the polynomial digit distinguishes every one exactly when $C\le M/\gcd(M,W/2)$. Using the smallest qualifying odd radix gives the listed upper bounds for the complete residue modulo $M^2$. [Divisibility, precision and decoder](../PrimeFactors/CyclotomicRadixLift.lean)

How much more divisibility can a bigger remainder guarantee? Fix any positive modulus $T$ divisible by 12 and a residue $n$ coprime to $T$. Among products of distinct primes in that residue class, $W$ is exactly the largest common divisor of all the corresponding $F$ values. This remains true when both primes must exceed any prescribed lower bound. Lean uses Dirichlet's theorem to realize the necessary residues with primes. This general statement allows their widths to vary. [Optimality proof and assumptions](../PrimeFactors/ForcedTotientDivisor.lean)

For modulus 12 we also checked the exact width in the research question. In each row of the table, two 2,048-bit products of certified 1,024-bit primes already give two values of $F$ whose greatest common divisor is precisely $W$. This proves that each row's guarantee is the strongest possible at that width. [Reproduce the four Lean certificates](../experiments/full_width_totient_divisor.py)

### When four possible sums can share a digit

For $7,294,033$, the factor widths and the guaranteed divisor leave 52 positions for the prime sum. Choosing radix 13 allows four positions to share a digit. The supplied polynomial remainder is 40 modulo 169. It leaves the four sums **5,578, 5,526, 5,474 and 5,422**. The product is 3 modulo 5, so its prime sum must be 1 or 4 modulo 5. It is also 5 modulo 7, so the sum must be 0, 1 or 6 modulo 7. Only 5,474 passes both tests. It gives the factors **2,293 and 3,181**. The consecutive-position rule would have used radix 53 and requested a remainder modulo 2,809. [Four-position decoder and example](../PrimeFactors/CyclotomicResiduePacking.lean)

This works whenever the product is a quadratic nonresidue at both 5 and 7. We choose the distance between adjacent proposed sums so that the tests modulo 5 distinguish sums two or three steps apart and the tests modulo 7 distinguish sums one step apart. As a result, four consecutive proposals can never contain two locally possible sums. If there are $C$ original positions, a suitable radix can be chosen between $\lceil C/4\rceil$ and $\lceil C/4\rceil+419$ inclusive. The cheap tests use only $N$. The polynomial remainder is still necessary to select the four proposals in this calculation, and we have no efficient general procedure for producing it. [Separation proof and radix selection](../PrimeFactors/CyclotomicResiduePacking.lean)

## Counting consecutive integers

Imagine numbering $N$ positions in a circle and looking at a run of $t$ consecutive numbers from each starting point. Count the runs that contain no multiple of either prime. For $1\le t\le p<q$, this count is exactly $C=(p-t)(q-t)$. This follows because a run misses the multiples of $p$ at $p-t$ possible starting residues modulo $p$, and likewise for $q$. The Chinese remainder theorem combines the two counts. Hence $t(p+q)=N+t^2-C$. When both primes are odd, an estimate of $C$ with absolute error strictly less than $t$ still gives the exact sum by rounding to the nearest even integer. [Count and integer rounding proof](../PrimeFactors/UnitRunCounts.lean)

For $143=11\cdot13$ and $t=6$, exactly 35 of the 143 runs avoid both primes, 72 encounter just one, and 36 encounter both. The count 35 gives the sum $(143+36-35)/6=24$. Determining the count cheaply for an unknown full-size pair remains open. Trying one randomly placed run with up to $2^{40}$ terms has less than a $2^{-982}$ chance of encountering exactly one prime when both factors have 1,024 bits. A length chosen to make that chance exceed one half uses more than $2^{1022}$ consecutive terms. These are counts of terms in the direct product. They do not bound faster algorithms for evaluating factorial products. [Exact odds and deterministic interval comparison](../PrimeFactors/UnitRunCounts.lean)


## Can a remainder tell which interval to search?

Take 134,231 and 198,103. Both leave remainder 87 when divided by 128. The first product has a divisor between 257 and 270, and the second has none. Their prime pairs are $269\times499$ and $397\times499$. For every modulus up to $2^{1011}$, Lean also proves that some two 2,048-bit products of 1,024-bit primes share the same remainder and larger prime but have different smaller primes. A divisor interval ending at the first smaller prime distinguishes those products. The choice of interval here may depend on the modulus. [Worked example and balanced collision theorem](../PrimeFactors/DivisorCountPeriod.lean)

More generally, fix a finite set of distinct positive trial divisors. To get even the parity of the number that divide an arbitrary positive input, a decoder using only one fixed remainder needs a modulus divisible by the least common multiple of the whole list. For a particular remainder class $N\bmod T$, some compatible integer has a hit precisely when a listed $d$ satisfies $\gcd(d,T)\mid N$. Every compatible integer has a hit precisely when some listed $d$ divides $\gcd(N,T)$. These statements describe what the remainder alone determines. Algorithms that use other arithmetic on the full product have more information. [Exact period and both tests](../PrimeFactors/DivisorCountPeriod.lean)
