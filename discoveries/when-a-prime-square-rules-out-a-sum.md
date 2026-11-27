# When does the square of a prime rule out another factor sum?

On two published 2,048-bit products, replacing seven small prime moduli with their squares reduced the number of candidate sums by a further **6.42 times** on one product and **13.87 times** on the other. The smaller of the two resulting searches still contains at least $2^{1006}$ sums. Lean obtained these bounds from the product and the widths of its factors, without using either prime as a clue. [Full-width proof](../PrimeFactors/PublicPrimeSquareCounts.lean)

| Product | Reduction from the modulo-four starting list | Further reduction from the seven ordinary prime tests | Sums left for an integer square test |
| --- | ---: | ---: | ---: |
| Fresh | 801.89–801.90× | 6.42–6.43× | At least $2^{1006}$ and below $2^{1007}$ |
| Crossed | 1,168.66–1,168.67× | 13.87–13.88× | At least $2^{1007}$ and below $2^{1008}$ |

The seven primes are 3, 5, 7, 11, 13, 17 and 19. The interval runs from the first integer at least $2\sqrt N$ through the upper bound implied by two 1,024-bit factors. Both sets of tests begin with the same condition $s\equiv N+1\pmod4$. For the stronger tests the joint pattern repeats every 94,083,986,096,100 consecutive integers. In each complete period exactly 29,331,862,560 sums pass on the fresh product and 20,126,346,240 on the crossed product. Allowing a whole period of uncertainty at the end gives the bounds in the table. These count final square tests in a full scan. Elapsed time also depends on how candidates are generated and how much each table lookup costs. [Published comparison products](../PrimeFactors/IntervalWheelControls.lean) · [Earlier lookup counts](what-ordering-saves-on-the-full-width-interval.md)

## Why 9 catches something that 3 misses

Suppose $N=pq$ and we guess the sum $s=p+q$. Then $s^2-4N=(p-q)^2$ must be a square. For the product **136,831**, the false guess **748** gives $748^2-4N=12,180$. This is zero modulo 3, so the first test accepts it. It is **3 modulo 9**, and squares modulo 9 can only be 0, 1, 4 or 7. The true sum **760** survives. Its discriminant is $174^2$, giving the primes $(760-174)/2=293$ and $(760+174)/2=467$. Ordinary prime tests on this example had to reach 41 to isolate the sum. Adding 9 leaves just two choices at that stage, 752 and 760, and 11 eliminates 752. [Checked example and classification](../PrimeFactors/ToySquareLiftIsolation.lean) · [Prime-only search](../PrimeFactors/ToySumIsolation.lean)

For any odd test prime $\ell$, an accepted nonzero square modulo $\ell$ always lifts to a square modulo $\ell^2$. The extra test matters precisely when $\ell$ divides the discriminant and $\ell^2$ does not. This can happen only when $N$ is a square modulo $\ell$, provided $\ell$ does not divide $N$. It explains why the same list of test primes gives different savings on different products. The local counts come from the modular hyperbola formulas of Bower, Evans, Luo and Miller. [Primary source](https://arxiv.org/abs/1212.2930) · [Lean count formulas](../PrimeFactors/PrimePowerCount.lean)

## What happened on every pair of small primes?

We took every unordered pair of **distinct primes of the stated factor width**, including products of either possible bit length. For each product the search sees only the product and the factor width. It begins with the entire compatible sum interval and the modulo-four condition. The known primes let us verify which sum each search returned. [Population definition and kernel-checked census](../PrimeFactors/ToySumIsolation.lean)

| Factor width | Number of pairs | Largest prime needed with prime tests alone | Largest modulus needed when also checking 9 | Products still ambiguous through 19 with 9 included |
| --- | ---: | ---: | ---: | ---: |
| 8 bits | 253 | 23 | 23 | 1 |
| 9 bits | 903 | 41 | 23 | 4 |

The cutoff of 23 is necessary in both populations. For **137,317**, even testing *every* prime square through $19^2$ leaves the false sum 778. Modulo 23 rules it out, leaving $742=353+389$. Thus checking more digits at the existing primes and checking a new prime can have different outcomes on the very same sum. [Sharp cutoff and example](../PrimeFactors/ToySquareLiftIsolation.lean)

## What if we keep taking higher powers?

Even **every power** of every prime through 19, including 2, leaves more than $2^{998}$ wrong sums in the fresh product's factor-width interval and more than $2^{1000}$ in the crossed interval. The proof constructs repeating classes of midpoints whose discriminants have square roots at every tested precision. Their corresponding sums are distinct, and removing the genuine sum costs at most one. A method that isolates the answer on either of these products must therefore use information beyond these local conditions. [Width-specific lower bounds](../PrimeFactors/PublicPrimeSquareCounts.lean) · [Construction of the persistent classes](persistent-local-survivors.md)

There is a related classical result for checking **one proposed sum**. Strip all powers of 2, 3, 5, 7, 11 and 13 from its positive midpoint discriminant $D=(s/2)^2-N$. If the remaining integer is below 8,089, then $D$ is a square exactly when all stripped exponents are even, the remainder is 1 modulo 8, and it is a nonzero square modulo each of the five odd primes. The bound is strict. The nonsquare 8,089 itself passes these local tests. Lehmer, Lehmer and Shanks tabulated this threshold in 1970. Lean checks all smaller candidates congruent to 1 modulo 8. [Original paper, Table I](https://oeis.org/A002189/a002189.pdf#page=2) · [Threshold certificate](../PrimeFactors/PseudosquareThirteen.lean)

For **126,727**, the true sum 712 gives $D=9$, and the false sum 728 gives $D=5,769=9\cdot641$. Both pass the ordinary squares through 13. After stripping the factor of nine, 1 passes and 641 fails modulo 3. Treating zero modulo 3 as grounds for rejection at the outset would have discarded the true sum as well. The threshold certifies a candidate once its discriminant is in hand. Finding that candidate in a large interval remains the expensive part. [Normalization theorem](../PrimeFactors/PseudosquareNormalization.lean) · [Worked values](../PrimeFactors/PseudosquareThirteen.lean)
