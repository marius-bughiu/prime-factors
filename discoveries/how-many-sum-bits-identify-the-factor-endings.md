# How many sum bits identify the factor endings?

If someone supplies the lowest **168 bits of the true sum** of two primes, their product and those bits determine the lowest **160 bits of both primes** on about **255 out of 256** eligible 2,048-bit products. The recovery returns the two endings in either order. The population estimate assumes a published prime-count bound under Dirichlet GRH. On each individual input, an elementary test tells us whether the supplied bits suffice, and a verified decoder returns the endings when they do. Obtaining the sum bits from the product remains open. [Full-size frequency](../PrimeFactors/FactorPairSeparationPopulation.lean) · [Stopping test](../PrimeFactors/ObservableSeparationDepth.lean) · [Decoder](../PrimeFactors/FactorEndingDecoder.lean)

## Six small products where one more sum bit matters

Suppose we want five low bits of each factor, so an ending is a remainder from 0 to 31. The six selected 20-bit products below form three matched pairs. Within each pair, even the lowest **twelve product bits** are identical. We computed the sum clues from the known primes. All remainders in the table are written in decimal. [Primality certificates, input readings and uniqueness proofs](../PrimeFactors/FactorEndingSeparationControls.lean)

| Product | Known primes | Product mod 4,096 | Shared sum reading one bit earlier | Supplied sum reading | Factor endings mod 32 |
| ---: | ---: | ---: | --- | --- | --- |
| 545,339 | 619 × 881 | 571 | 28 at 5 bits | 28 at 6 bits | 11 and 17 |
| 578,107 | 673 × 859 | 571 | 28 at 5 bits | 60 at 6 bits | 1 and 27 |
| 539,477 | 643 × 839 | 2,901 | 10 at 6 bits | 74 at 7 bits | 3 and 7 |
| 584,533 | 659 × 887 | 2,901 | 10 at 6 bits | 10 at 7 bits | 19 and 23 |
| 601,049 | 619 × 971 | 3,033 | 54 at 8 bits | 54 at 9 bits | 11 and 11 |
| 842,713 | 827 × 1,019 | 3,033 | 54 at 8 bits | 310 at 9 bits | 27 and 27 |

For the first two products, the five-bit sum reading 28 is compatible with two different pairs of endings. At six bits, reading 28 forces 11 and 17, while reading 60 forces 1 and 27. The last two examples show that distinct primes can have identical five-bit endings. [Checked ambiguity and determination](../PrimeFactors/FactorEndingSeparationControls.lean)

## What the product guarantees before seeing the sum

Write $N=pq$. To recover the lowest $k$ bits of both factors, with $k\ge4$, the following are the **least** numbers of low sum bits that guarantee success for every compatible modular pair. Only the same number of low product bits is needed. At one bit less, different factor endings can still give the same sum and product readings. [Upper bounds](../PrimeFactors/FactorEndingSeparation.lean) · [Matching lower bounds](../PrimeFactors/FactorEndingCollisions.lean)

| Last three product bits | Sum bits sufficient in every case | At $k=160$ |
| --- | ---: | ---: |
| `011` or `111` | $k+1$ | 161 |
| `101` | $k+2$ | 162 |
| `001` | $2k-1$ | 319 |

The product also tells us how many pairs of endings are possible before receiving any sum bits. Every odd ending $a$ has the unique partner $N/a$ modulo $2^k$. Grouping partners in either order leaves exactly $2^{k-2}$ pairs, or $2^{k-2}+2$ when $N$ ends in `001`. One representative per pair is the shortest list guaranteed to name an ending of either factor. At $k=160$, even the smaller list has $2^{158}$ entries. [Exact count and minimum list size](../PrimeFactors/DyadicFactorOrbitCount.lean)

## When the supplied bits already suffice

For an individual pair of distinct odd factors, let $t$ be the number of trailing zero bits in $q-p$. At $k\ge3$, the exact threshold is $k+t$ when $t<k-1$, **$2k-3$ when $t=k-1$**, and $2k-1$ when $t\ge k$. At the middle value, the two true factors already occupy both possible next bits of their common $(k-1)$-bit ending. For 71 and 79 the gap is 8. Their four-bit sum remainder 6 is ambiguous for four-bit factor endings, but their five-bit sum remainder 22 suffices. [Individual threshold and sharpness](../PrimeFactors/FactorPairSeparationDepth.lean) · [Checked stopping decision](../PrimeFactors/ObservableSeparationDepth.lean)

We can perform the test without knowing the gap. Let $s$ be the supplied $e$-bit sum remainder, with $e\ge2$. The even sum gives two extra bits when squared, so $R=(s^2-4N)\bmod 2^{e+2}$ equals $(q-p)^2$ modulo the same power. At $e\ge2k-1$ we can stop immediately. Below that, a zero reading means more precision is needed. For a nonzero reading, half its trailing-zero count gives $t$, so we can check the individual threshold directly. [Public test and equivalence proof](../PrimeFactors/ObservableSeparationDepth.lean)

To recover the endings once the test succeeds, take $h=s/2$ and find one square root of $h^2-N$ modulo $2^e$. The decoder removes factors of four and lifts an odd square root one binary digit at a time. If it returns $d$, the two outputs are $h+d$ and $h-d$ modulo $2^k$. The number of stripping and lifting steps grows linearly with $e$. Each step performs arithmetic on multi-bit integers. Lean checks that these two outputs equal the true endings up to swapping. [Decoder and correctness theorem](../PrimeFactors/FactorEndingDecoder.lean)

## How frequently do a few extra bits suffice?

Count each unordered pair of distinct 1,024-bit primes whose product has 2,048 bits once. If $j+3<k$, then $k+j$ supplied sum bits identify the $k$-bit factor endings exactly when the two primes differ within their lowest $j+1$ bits. This equivalence for each pair is unconditional. Prime-count estimates give the following frequencies across the entire eligible population. Lean takes the published analytic estimates as explicit inputs. [Population proof and assumptions](../PrimeFactors/FactorPairSeparationPopulation.lean)

| Sum bits supplied for 160-bit endings | Share of eligible pairs where they suffice | Absolute error at most |
| ---: | ---: | ---: |
| 163 | $7/8$ | $1/8320$ |
| 168 | $255/256$ | $2^{-154}$ |
| 180 | $1-2^{-20}$ | $2^{-166}$ |

The 163-bit row uses Bennett, Martin, O’Bryant and Rechnitzer’s unconditional prime-count estimate at modulus 16. The 168- and 180-bit rows use Ernvall-Hytönen and Palojärvi’s estimate under Dirichlet GRH, at moduli 512 and $2^{21}$ respectively. [Bennett et al., Theorem 1.3](https://personal.math.ubc.ca/~bennett/BeMaObRe-IJM-2018.pdf#page=5) · [Ernvall-Hytönen and Palojärvi, Corollary 2](https://arxiv.org/pdf/2003.01925#page=2) · [Verification of the released Dirichlet GRH statements](https://math.mit.edu/~drew/shortgrh/)

On the repository’s independently generated 2,048-bit comparison product, **161** true sum bits are necessary and sufficient for both 160-bit endings. The constructed quartic example needs **319**. Its sum remainder is numerically 2 at both 318 and 319 bits. Knowing that the next bit is also zero settles both factor endings as 1 modulo $2^{160}$. In each case the supplied sum remainder comes from the known prime factors. The output consists of two 160-bit remainders of 1,024-bit primes. [Comparison input](certified-fresh-control.md) · [Quartic construction](when-a-quartic-reading-beats-consecutive-fermat.md) · [Full-size decoder checks](../PrimeFactors/FactorEndingDecoderControls.lean)
