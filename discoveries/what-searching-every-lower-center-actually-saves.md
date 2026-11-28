# What searching every lower center actually saves

On **134,271,337**, the search finds **8,237 × 16,301** on its fourth exact square test. Ordinary Fermat takes 682 consecutive midpoint tests. Applying parity and a modulo-256 square screen brings that baseline down to 42 exact tests. The new route uses the product and the promised 14-bit factor width. To produce its candidates it also takes the starting integer square root, 12 modular lifting steps, and residue checks. We selected this example from the census after observing the savings. [Exact candidate list and work](../benchmarks/dyadic-center-compression.json) · [Reproducible search](../experiments/dyadic_center_compression.py)

## How every center fits in a short list

For each nonnegative integer $s\le\lfloor\sqrt N\rfloor$, let $2^j$ be the largest power of two dividing $N-s^2$. The proposed prime sum is $2s+2^j$. For two odd primes below $2^b$, every viable exponent lies between 1 and $b$. At each exponent the search checks at most two centers, regardless of how many integers lie below the square root. For $j\ge3$, one lifted square root of $N$ supplies both residue classes for every exponent. The search keeps only centers close enough to the floor for the predicted sum to exceed twice the floor. Two consecutive exponents at or above three contribute at most two distinct sums between them. For 1,024-bit factors the entire list has at most 1,022 distinct sums when $N\equiv1\pmod8$, and at most one for every other odd product. [Completeness and size of the list](../PrimeFactors/FloorShiftCenterCompression.lean) · [Derivation and low exponents](which-centers-below-the-square-root-can-give-the-sum.md)

For the example above, 11 centers yield nine distinct midpoints. Six survive parity and the modulo-256 screen. The fourth is 12,269. Its square exceeds the input by $4032^2$, so subtracting and adding 4,032 gives the two primes. On 141,217 all proposed sums miss, even though a screened Fermat scan finds its factors in two exact tests. [Positive and negative controls](../benchmarks/dyadic-center-compression.json)

## What happened on every small product

The comparison enumerates all unordered distinct prime pairs of each stated width whose product has twice that width. For each product we give ordinary screened Fermat as many exact square tests as there are distinct, screened candidates in the compressed list. Both searches stop at the first verified split. At widths 7 through 10 an independent enumeration checks the entire predicted list against every center, including incorrect predictions. At all widths the prime labels check after discovery whether any exponent could have returned the true sum. [Policies, input generation and checks](../experiments/dyadic_center_compression.py)

| Bits per prime | Products | Hits at the floor alone | Hits with all lower centers | Screened Fermat hits at the same budget | Hits only the compressed list found |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 7 | 42 | 16 | 33 | 33 | 0 |
| 8 | 148 | 46 | 90 | 93 | 0 |
| 9 | 543 | 136 | 283 | 306 | 2 |
| 10 | 1,718 | 299 | 666 | 773 | 5 |
| 11 | 5,530 | 795 | 1,821 | 2,193 | 32 |
| 12 | 19,546 | 1,973 | 4,764 | 6,112 | 190 |
| 13 | 64,719 | 4,783 | 12,246 | 16,135 | 801 |
| 14 | 228,713 | 12,356 | 33,417 | 44,061 | 3,244 |

At 14 bits the compressed list found 3,244 products that screened Fermat missed at the same per-input allowance. Screened Fermat found 13,888 that the list missed. The two policies performed 237,583 and 223,408 exact square tests respectively, from a common allowance of 291,183. The compressed policy also performed 683,832 lifting steps across the population. The comparison measures search coverage and work counts. [All counts](../benchmarks/dyadic-center-compression.json)

## How much of the full population this reaches

The full population consists of all unordered pairs of distinct 1,024-bit primes with a 2,048-bit product. A necessary condition on the odd part of the prime gap gives a success fraction below $2^{-474}$, even if every lower center is available. [All-center upper bound](../PrimeFactors/FloorShiftDyadicCenters.lean)

There is also a positive bound. **More than one in $2^{517}$** eligible pairs has a prime gap of at least $2^{1000}$ and its true sum among the at most two guesses at the single exponent $j=1023$. Ordinary Fermat would visit at least $2^{973}$ positions before reaching the true midpoint on each of these pairs. This lower bound counts genuine prime pairs even after excluding close primes. The upper bound of one in $2^{474}$ counts the entire method, so both figures describe a rare family. [Recovery, population and consecutive-search bounds](../PrimeFactors/FloorShiftRecoveryPopulation.lean)

The lower bound comes from counting primes that fall into the same remainder class. The class is used in the proof to guarantee that one of the proposed sums succeeds. The compressed search itself needs only the product and factor-width bound. The population argument uses elementary prime counts and the pigeonhole principle. [Counting proof](../PrimeFactors/FloorShiftRecoveryPopulation.lean) · [Prime population used](../PrimeFactors/ChebyshevPrimeSample.lean)
