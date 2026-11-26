# When two failed square tests give a factor

On 559,697 the first two tests give the remainders 29,248 and 4,113. Neither is a square. Their product is the square of 10,968. This gives the prime factors **631 and 887** using one gcd. The extra comparison does recover cases that individual tests miss. In a census of 2,753,877 larger products it did so only 22 times. Spending the extra test on the next ordinary sum recovered 96,821 instead. [Search from the product](../experiments/weighted_square_pairs.py) · [Checked examples](../PrimeFactors/WeightedSquarePair.lean) · [Full census](../research/weighted-square-pairs.json)

## The two remainders

Take an odd product $N$ coprime to six. For weight $w=1$ or $2$, form the first integer at or above $2\sqrt{wN}$ congruent to $w+N$ modulo $s_w=\gcd(24,2(w+N))$. These are the progressions containing the weighted factor sums $wp+q$ when $N=pq$ has primes greater than three. Call the first labels $A,B$, respectively. Calculate
$$D=A^2-4N,\qquad E=B^2-8N.$$
When $DE=z^2$, both $AB$ and $z$ square to the same residue modulo $N$. Test $\gcd(AB-z,N)$. The method of congruent squares is classical. Our question is which products this particular choice of two labels can reach. [Weighted residue proof](../PrimeFactors/WeightedStride.lean) · [Handbook of Applied Cryptography, §3.2.5](https://cacr.uwaterloo.ca/hac/about/chap3.pdf)

**Every square match with $D,E\le N/10$ gives a proper factor.** The size bounds give $10z\le N$ and $5.1N<AB<5.9N$, by squaring and using $(AB)^2=(4N+D)(8N+E)$. Thus $AB-z$ and $AB+z$ both lie strictly between $5N$ and $6N$. Their product is a multiple of $N$, and neither factor in that product is itself a multiple of $N$. The gcd is therefore proper. The proof applies to all labels meeting the size test and does not require $N$ to be semiprime. [General interval theorem and two-weight specialization](../PrimeFactors/WeightedSquarePair.lean)

For the opening example, the two labels are 1,506 and 2,117. The gcd is 887. On this particular product the next admissible ordinary sum, 1,518, also succeeds. On 143,840,057 the two labels give $351808\cdot49473=131928^2$ and the gcd gives 14,243, with cofactor 10,099. Neither next single test succeeds there. A first-label search requires two integer roots for the labels, one square test on their excess product, and one gcd on a hit. Testing the two excesses individually is a separate baseline. [Reproducible benchmark inputs](../benchmarks/weighted-square-pairs.json)

| Bits per prime | Eligible products | Found by either first test | Extra from combining them | Extra from the next ordinary sum | Extra from the next weight-two sum |
|---:|---:|---:|---:|---:|---:|
| 10 | 1,718 | 978 | 1 | 275 | 62 |
| 14 | 228,713 | 39,699 | 6 | 15,048 | 325 |
| 15 | 783,832 | 95,344 | 7 | 37,219 | 640 |
| 16 | 2,753,877 | 242,896 | 22 | 96,821 | 1,150 |

Each extra column starts after both first tests have missed. The 22 cross-test recoveries at 16 bits include **21 missed by both alternatives**. Each alternative gets one additional square test. Their operands differ in size. The census includes every pair of distinct primes of the indicated width with a full-width product. The two ordinary 2,048-bit comparison inputs both exhausted the first-label test with their entire cofactor unresolved. [Counts and comparison rules](../research/weighted-square-pairs.json) · [Full-width inputs](../benchmarks/weighted-square-pairs.json)

## A constructed 2,048-bit example

We chose two 1,024-bit primes so that the *first* labels satisfy $3A=17p-7q$ and $8B=17p+7q$. The primes differ by a 1,023-bit integer. Neither individual remainder is square, and the next label in each of the two progressions also misses. Expanding these equations gives $9D=64E$, hence $D=64h$, $E=9h$ and $DE=(24h)^2$. Feeding just their product into the same square test returned the larger prime by gcd. Lean verified both primes and their product. [Decimal input and factors](../research/weighted-pair-control.json) · [Primality and multiplication certificate](../benchmarks/controls/WeightedPairControl.lean) · [Identity for the two excesses](../PrimeFactors/WeightedSquarePair.lean)

The construction uses the fixed ratio $r=(137-48\sqrt2)/49$ and chooses $0<rp-q<1$. Continued fractions provide candidate pairs, and divisibility of both predecessors by $2^{496}$ helps certify primality. There were 1,162,798 candidate pairs and 42,474 passed the small-prime sieve during construction. This setup cost is separate from the product-only search. Someone told the ratio can also recover $p$ directly as $1+\lfloor\sqrt{N/r}\rfloor$, since $p-1<\sqrt{pq/r}<p$. That comparison succeeds here as well. The two ordinary full-size controls still give nonsquare excess products. [Generator and reproduction options](../experiments/weighted_pair_control.py) · [Comparison fixtures](../benchmarks/weighted-square-pairs.json)

## What if we try many labels?

Set $X=2^{1023}$. Draw $p<q$ uniformly among the eligible pairs with $X<p<q<2X$ and $N=pq\ge2X^2$. Allow **every** pairing of the first $J$ labels from each progression. The following bounds count successes even if one already knew which two labels to use.

| Labels per progression | Upper bound on the fraction having any square match |
|---:|---:|
| 1 | $2^{-740}$ |
| $2^{64}$ | $2^{-663}$ |
| $2^{128}$ | $2^{-587}$ |
| $2^{256}$ | $2^{-435}$ |
| $2^{512}$ | $2^{-130}$ |

These bounds concern square *products* of the two positive excesses. An individual excess can be square without producing a match with the other row. Other choices of weights or products of three or more excesses lead to different equations. The finite size estimate and population denominator are checked in Lean. The geometric count used as its hypothesis follows below. [Finite population proof](../PrimeFactors/WeightedPairPopulation.lean) · [Uniform bound on the divisor count](../PrimeFactors/UniformDivisorCount.lean)

Write $t=\sqrt N$, so $X<t<2X$. For the allowed labels, $0\le A-2t<24J$ and $0\le B-2\sqrt2t<6J$. The second bound uses the fact that $N+2$ is odd, so $s_2$ divides six. There are at most $5X$ choices of $A$. For each $A$, the possible integers $B$ lie between $\sqrt2 A-24\sqrt2 J$ and $\sqrt2 A+6J$, giving at most $42J$ choices. Since $J\le2^{512}$, expanding the squares gives $0<D<193XJ$ and $0<E<70XJ$. Both are positive since neither $N$ nor $2N$ is square. The integer $c=2A^2-B^2=2D-E$ is nonzero since $\sqrt2$ is irrational, and $|c|<512XJ$.

Fix $A,B$. If $DE$ is square, put $g=\gcd(D,E)$. The coprime integers $D/g$ and $E/g$ must be squares, say $u^2$ and $v^2$. Then $g$ divides $|c|$ and
$$v^2-2u^2=-c/g=d.$$
Put $s=|d|$. Primitivity gives $\gcd(u,s)=1$. The slope $v/u$ modulo $s$ is a root of 2; at $s=1$ there is just one class. Each odd prime power in $s$ contributes at most two roots: there are at most two modulo the prime, and the derivative $2v/u$ is a unit at a root, so each has a unique lift. Modulo 2 there is one and modulo 4 there are none. The total number of slope classes is at most $2^{\omega(s)}$.

In one class order the solutions by $\alpha=v+u\sqrt2>1$. The ratio of a larger solution to a smaller one has the form $h+k\sqrt2$ with integer $h,k$. Indeed, multiplying by the conjugate of the smaller solution gives numerators $v'v-2u'u$ and $u'v-v'u$, both divisible by $d$ by the common slope. The ratio has norm one, so its conjugate is its positive reciprocal. Hence $h$ is an integer strictly larger than one and the ratio is larger than two. From the bounds on $D,E$, $\alpha<32\sqrt{XJ}<2^{1024}$; there are at most 1,024 solutions per class. Each $(g,u)$ gives at most one $N$ through $4N=A^2-gu^2$.

Summing the class bound over $s\mid |c|$ gives $\sum 2^{\omega(s)}=\tau(c^2)$ by multiplying the contributions $1+2e$ for each prime exponent $e$ in $|c|$. Thus at most $1024\tau(c^2)$ products occur at each $A,B$. The checked divisor estimate $\tau(m)^{336}\le2^{14882}m^{32}$ and eligible population $T>X^2/21000000$ now give the table. Even the last bound allows $2^{1024}$ different label pairings on each input. The small success examples and this population bound measure different aspects of the same test.
