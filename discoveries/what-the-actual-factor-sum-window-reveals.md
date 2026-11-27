# How much does the actual factor-sum interval reveal?

Three products illustrate why the endpoints alone can be misleading. Each product below has two 10-bit prime factors. All three have the same upper ten product bits, the same square-root ceiling of 750, the same two quotients used to form the search interval, and the same remainder modulo 24. Yet all three true sums are different. [Lean certificates](../PrimeFactors/ActualWindowAdvice.lean)

| Product | Prime factors | Their sum |
|---:|---:|---:|
| 562,013 | 557 × 1,009 | 1,566 |
| 562,109 | 683 × 823 | 1,506 |
| 562,157 | 641 × 877 | 1,518 |

There is a full-size version of this ambiguity. Choose uniformly from all pairs of distinct 1,024-bit primes whose product has 2,048 bits, counting each pair once. **For all but fewer than one pair in $2^{30}$, more than $2^{900}$ different true prime sums occur among products with exactly the same recorded information.** At least one such group has more than $2^{960}$ distinct sums. These counts use actual prime pairs. For each individual product only its own pair supplies its prime sum. [Counting proof](../PrimeFactors/ActualWindowAdvice.lean)

## What the search gets to see

Put $X=2^{1023}$ and $B=2X$. The recorded information consists of $\lfloor N/B\rfloor$, $\lceil\sqrt N\rceil$, $\lfloor N/X\rfloor$, $\lfloor N/(B-1)\rfloor$, and $N\bmod24$. These give the upper half of the product's bits, the upper and lower sum endpoints, the stride, and its phase. A search may prepare a different list of exact sums for every combination of these values. It can also receive additional bits chosen separately for each product, even by someone who knows the factors. The theorem puts no limit on the effort spent preparing these lists. [Endpoint formulas](../PrimeFactors/ProductDeficitBand.lean) · [Stride](../PrimeFactors/CyclotomicRadixLift.lean)

| Additional information | Sums the search may try | Upper bound on the fraction of pairs whose sum appears |
|---|---:|---:|
| None | 1 | Below $2^{-480}$ |
| 128 bits | $2^{40}$ | Below $2^{-396}$ |
| 512 bits | $2^{40}$ | Below $2^{-204}$ |

The fraction is over the prime pairs just described. The search can use the entire product to check the proposed sums. If it also uses the remaining product digits to choose new guesses, that is extra information beyond this model. This proof bounds the reach of a particular way of proposing sums. The computational difficulty of factoring from the entire product remains open here.

A comparison in the other direction comes from an ordinary square-root search. Its first guess succeeds on more than one in $2^{517}$ eligible pairs, while the first row above bounds every single guess from the recorded information below one in $2^{480}$. [Constructive lower bounds and advice costs](how-often-the-first-even-sums-work.md)

## Where the count comes from

Products with the same upper word $h$ lie between $Bh$ and $Bh+B-1$. Inside that block, the square-root ceiling has at most two values, one width quotient has at most two, and the other has at most three. Even allowing all 24 remainders gives at most 288 distinct records per upper word.

Suppose two pairs have the same sum and smaller factors $p$ and $p+t$. Writing the second pair as $(p+t,b)$ makes the first $(p,b+t)$. Their products differ by $t(b-p)$. If the smaller factors differ by at least $U$ and the second pair has a gap of at least $D$, the difference is at least $UD$. Choosing $UD\ge B$ ensures these two products cannot occupy the same block. Consequently, among pairs with gap at least $D$, the upper word, sum, and smaller factor modulo $U$ identify at most one pair. For the remaining pairs we count smaller factors and gaps directly.

If a record's list contains at most $J$ sums, the combined count is at most $BD+B(288J)U$. For 128 advice bits and $2^{40}$ guesses, even the union of every possible advice list has at most $J=2^{168}$ sums per record. Taking $D=2^{600}$ and $U=2^{424}$ and dividing by the project's proven lower bound on the number of eligible prime pairs gives the stated $2^{-396}$ limit. To count ambiguous records, allow a list containing every true sum for any record with few possibilities. The same argument bounds the share of pairs belonging to those records. The deductions and the prime-population denominator are machine-checked without an RH hypothesis. [Counting proof and numerical bounds](../PrimeFactors/ActualWindowAdvice.lean) · [Prime-population bound](../PrimeFactors/ChebyshevPrimeSample.lean)
