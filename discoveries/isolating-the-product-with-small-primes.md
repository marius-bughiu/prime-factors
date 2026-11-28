# How much does isolating the right product tell us about its factors?

At **12,827**, the product alone selects the modulus **401** in the small example below. The toy rule starts at $\lfloor12{,}827/32\rfloor+1=401$. This already satisfies $m\equiv12{,}827\pmod6$ and $2m\equiv12{,}827\pmod5$ and is coprime to the input. Two ordered pairs pass the congruence and balance tests. Their products are 12,827 and 14,030. The latter is even, so the only pair left is **101 × 127**. There is also a direct way to check either supplied pair: multiply its entries and compare with 12,827. The challenge is to find the entries when only the product is known. [Lean proof of the singleton](../PrimeFactors/FractionalRoughMatchedPairs.lean) · [Small controls](../benchmarks/fractional-rough-lifts.json)

| Candidate pair | Product | Difference from 12,827 | Common divisor with 30 |
| --- | ---: | ---: | ---: |
| 101 × 127 | 12,827 | 0 | 1 |
| 115 × 122 | 14,030 | 3 × 401 | 10 |

## A smaller modulus for a full-size input

Suppose the input is a product $N=pq$ of primes with $p\le q<2p$. A potential pair $1<x\le y<m$ must satisfy the balance test $y<2x$, the public sum window $4N\le(x+y)^2<9N/2$, and $xy\equiv N\pmod m$. These imply $8N/9<xy<9N/8$. Thus its product is $N+jm$ for an integer $j$ between $-\lfloor(N-1)/(9m)\rfloor$ and $\lfloor(N-1)/(8m)\rfloor$. The earlier result took $m\ge N/8$ to leave only $j=0$. [Product interval and previous cutoff](../PrimeFactors/FractionalBalancedLifts.lean) · [Exact index range](../PrimeFactors/FractionalMatchedDivisors.lean)

Let $P$ be the product of all primes through 1,000 and $W=1009P$. Use the Chinese remainder theorem to choose a modulus satisfying $m\equiv N\pmod P$ and $2m\equiv N\pmod{1009}$. Round upward from $\lfloor N/8000\rfloor+1$ in this residue class. Among the first three representatives, choose the first coprime to $N$. Each of the two prime factors can exclude at most one of these representatives. For $N\ge2^{2047}$, Lean proves that all three fit between $N/8000$ and $N/7992$ and that the selected $m$ exceeds $q$. This choice uses the product and fixed small primes. [Product-only selection and full-width theorem](../PrimeFactors/FractionalSelectedProgression.lean)

Every nonzero index in the resulting interval has a known prime dividing $N+jm$. For example, at $j=-2$ the auxiliary prime 1,009 divides $N-2m$. At the other indices a prime dividing $j+1$ suffices, with 2 handling $j=-1$. The true prime factors exceed 1,009, so the actual pair passes the test $\gcd(xy,W)=1$. The ordered pair satisfying every test is unique at a modulus at least **999 times smaller** than the former $N/8$ sufficient threshold. This compares the required modulus sizes. [Divisibility proof and pair uniqueness](../PrimeFactors/FractionalRoughMatchedPairs.lean)

## What can the pattern of rejected products reveal?

For every signed index, including far outside the allowed interval, Lean gives the complete reading
$$
\gcd(N+jm,W)=\gcd(|j+1|,P)\,\gcd(|j+2|,1009).
$$
The first congruence makes $N+jm$ agree with $(j+1)N$ modulo $P$. The second makes it agree with $(j+2)m$ modulo 1,009. The multipliers are units of their respective moduli, so both cancel in the gcd. The right-hand side contains no input-dependent term. Every eligible product gives the same infinite sequence of readings. [Exact gcd identity](../PrimeFactors/FractionalWheelTranscript.lean)

The nearest nonzero indices with gcd one are **−1010 and +1008**. The positive index enters the allowed interval precisely when $N>8\cdot1008m$, and the negative one enters when $N>9\cdot1010m$. Consequently the gcd removes every noncentral product in that interval exactly when $N\le8064m$ for these congruences. A product passing the gcd outside this cutoff would still need a divisor pair satisfying the two balance tests. For example, take 4,453 and the supplied toy modulus 139. Index +4 survives the wheel of 30, but its product 5,009 is prime and cannot split into two entries greater than one. The only surviving matched pair is 61 × 73. The bounded experiment compared all 2,019 readings from −1010 through +1008 on a deliberately chosen 2,048-bit integer coprime to $W$. This control checks the index pattern. Its factorization was unnecessary. [Neighbouring indices](../PrimeFactors/FractionalWheelNeighbours.lean) · [Exact cutoff](../PrimeFactors/FractionalWheelCutoff.lean) · [Full-width control](../benchmarks/fractional-rough-lifts.json)

## How much work remains?

The comparison used all **141** distinct prime pairs with $41\le p<q\le127$ and $q<2p$. Each row below covers the same products. On the wheel of 210, only 32 of 141 toy moduli fell inside the narrower target interval $[N/40,N/32]$, although all 141 gave uniqueness. The full-width size guarantee starts at $N=2^{2047}$. The small-prime wheel is the product of the primes used in that row. All counts refer to actual arithmetic or table lookups, and exclude independent checks of the recorded results. [Experiment](../experiments/fractional_rough_lifts.py) · [Counts and setup](../benchmarks/fractional-rough-lifts.json)

| Method | Wheel 30 | Wheel 210 |
| --- | ---: | ---: |
| Gcds to select the moduli | 141 | 141 |
| Candidate products checked by gcd across the cohort | 970 | 832 |
| Candidate pairs before the gcd filter | 285 | 258 |
| Pairs after the filter | 141 | 141 |
| Ascending divisions to first factor on the surviving products | 961 | 961 |
| Ascending divisions to first factor by direct balanced trial | 961 | 961 |
| Ascending divisions using the same wheel directly on trial divisors | 545 | 470 |

The direct wheel method also used 961 table lookups to the first factor and a one-time table of 30 or 210 small gcds. It reduced the number of divisions without constructing a modulus. In a separate small control at 62,113 the first proposed modulus already shared the factor 179 with the input. This was a factor found during modulus selection. None of the 282 selections in the main cohort did so. [Selection and work breakdown](../benchmarks/fractional-rough-lifts.json)

The public balance interval for the smaller factor is $\sqrt{N/2}<x\le\sqrt N$. At full width, more than $2^{1017}$ integers in that interval pass coprimality with $W$. Requiring coprimality with both $W$ and a positive $m<2^{2048}$ still leaves more than $2^{1013}$. These are counts after specific filters, before checking divisibility of $N$. If both primes have 1,024 bits, the larger prime is at most $2^{1024}-1$, so the smaller prime is at least $\lceil N/(2^{1024}-1)\rceil$. Throughout the lower half of the 2,048-bit range, $2^{2047}\le N\le3\cdot2^{2046}$, more than $2^{1012}$ entries remain after imposing this additional endpoint and both coprimality tests. The proof also accepts other interval endpoints. [Candidate counts and assumptions](../PrimeFactors/FractionalRoughProjection.lean)

## Could a different wheel exclude many more products?

Let $g(W)$ be the least length of a consecutive interval guaranteed to contain an integer coprime to $W$. Suppose $N$ is coprime to $W$ and we want every noncentral product in the allowed interval to share a divisor with $W$. Then, for **every** choice of positive step $m$,
$$
N\le 8m\,g(W).
$$
To see this, remove from $W$ all prime powers supported on primes that divide $m$. Those primes miss every $N+jm$ because they miss $N$. Modulo the remaining divisor of $W$, dividing the progression by its now-invertible step turns it into consecutive integers. At least one of the first $g(W)$ positive indices therefore survives. If $N>8m\,g(W)$, that index is inside the public product window. Lean proves this transfer for any supplied gap bound and covers steps with common divisors with $W$. [Wheel translation and necessary modulus](../PrimeFactors/FractionalWheelGapBound.lean)

Iwaniec's published bound for arbitrary sets of $k$ primes gives $g(W)=O(1+k^2\log^2(2+k))$. Together with the Lean theorem, this limits the improvement over the old $N/8$ threshold to a polynomial in the input bit length whenever the wheel uses only polynomially many distinct primes. This applies even when both the wheel and the step are chosen from $N$. It bounds strategies that discard **every** other product by a shared small divisor. A surviving product might have no factor pair in the balanced window. The asymptotic bound comes from the paper, and the numerical thresholds 8,064 and $2^{1013}$ above have separate Lean proofs. [Iwaniec, corollary on Jacobsthal's problem](https://doi.org/10.1515/dema-1978-0121) · [Ziller and Morack on computing primorial gaps](https://arxiv.org/abs/1611.03310)

For this specific wheel we can put a number on the limit even if all congruences are redesigned. It is the product of the first 169 primes. Costello and Watts report a computational upper bound $g(W)\le0.27749612254\,k^2\log k$ for primorials in the range $50\le k\le10000$. At $k=169$ this gives $g(W)<41{,}000$. The transfer therefore requires $N<328{,}000m$ and, for a 2,048-bit input, **$m>2^{2028}$**. This inference uses their published computation for the gap and our checked transfer theorem. [Costello and Watts, computational results](https://researchrepository.ucd.ie/server/api/core/bitstreams/75644f16-719c-426a-8174-5192a721a8d2/content) · [Lean transfer](../PrimeFactors/FractionalWheelGapBound.lean)
