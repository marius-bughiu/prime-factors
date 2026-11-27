# Which extra fractions are worth checking?

A wider search found **118 of the 903 products of two distinct nine-bit primes** using only the product and the common prime width. The old search found 78. We checked every small candidate independently and Lean verified the recovered primes. On our two 2,048-bit controls the wider search still found neither pair. The theory explains both how to check the extra guesses cheaply and why the same choice of exponents rarely works at full size. [Recorded experiments](../research/intermediate-totient-rows.json) · [Full-size benchmark inputs](../benchmarks/intermediate-totient-rows.json)

For example, start with **102,709**. One of the public guesses is 2,520. Its ordinary continued fraction with denominator 102,709 gives no factor. Between two of its usual fractions lies $2/81$. It proposes $2{,}520\times81/2=102{,}060$ as the value of $(p-1)(q-1)$. The implied prime sum is $102{,}709+1-102{,}060=650$. Then $650^2-4\times102{,}709=108^2$, giving **271 and 379**. One candidate square root sufficed. Ordinary Fermat took five midpoints. We selected this example from the census to show a gain. [Checked arithmetic and factorization](../PrimeFactors/IntermediateTotientRows.lean)

## Which fractions the search visits

For a public exponent $E$, write the Euclidean algorithm for $E/N$. When its quotient is $q$, the canonical search takes the entire step to the fraction $(a_0+qa_1)/(b_0+qb_1)$. The wider search admits all positive steps $1\le t\le q$ in the same expression. For a candidate $a/b$ above $E/N$, the proposed deficit is $(Na-Eb)/a$. A genuine candidate gives the integer $D=N-(p-1)(q-1)=p+q-1$.

The possible deficits decrease within each upper block. Between the last fraction of one upper block and the first of the next, the numerator at least doubles and the positive cross-product error drops. Consequently **at most one block per exponent can enter $[L,H)$ if $0<L<H\le2L$**. Two integer divisions give the first and last eligible coefficients of that block. This covers a quotient of any size. It still costs work to find the block and inspect its surviving coefficients. [One-block theorem, exact cutoff and counterexample for wider intervals](../PrimeFactors/IntermediateBlockCutoff.lean)

If $A=2^{k-1}$ and $B=2^k-1$ bound the two $k$-bit odd primes, their sum is even. Its minimum is at least $2\lceil\sqrt{N}\rceil$. Both $(p-A)(q-A)$ and $(B-p)(B-q)$ are nonnegative, so its maximum is at most the smaller of $A+\lfloor N/A\rfloor$ and $B+\lfloor N/B\rfloor$. Even at the widest point, the resulting interval for $D$ has length at most $11/128$ of the original dyadic width plus one integer. Replacing the full square root with the leading eight root bits keeps the bound at $3/32$ of the original width plus one for $k\ge8$. These are bounds on the range of possible sums. The number of fractions that land in that range varies with the product. [Endpoint proofs and rounding costs](../PrimeFactors/ProductDeficitBand.lean)

## What the extra work bought

Across all 903 small products there were 2,495 eligible exponents and 311,590 positive intermediate coefficients before pruning. Testing the exact public interval left 225 coefficients. All 40 additional recoveries use later blocks. Eight also escaped a separate base-two gcd test, which recovered 298 products overall. Standard Fermat found all 903 within 1,024 midpoint tests each, spending 4,051 midpoints across the census. On the separate pre-existing 64-product panel with 12-, 20-, 28- and 36-bit factors, the wider search recovered the same single pair as the canonical search. [Census and comparison budgets](../research/intermediate-totient-rows.json)

The following totals include the small census, the 64 holdouts and both full-size controls. Each method applied the same 3,066 eligible exponent guesses and performed 42,038 Euclidean steps. The last column includes interpreter startup and search setup. The medians come from ten separate runs on the same machine. [Reproducible timing and operation counts](../research/midpoint-table-band.json)

| Deficit interval | Candidate fractions | Integer candidates | Candidate square roots | Setup square roots | Median elapsed |
| --- | ---: | ---: | ---: | ---: | ---: |
| Common prime width alone | 3,480 | 1,760 | 939 | 0 | 101.35 ms |
| Exact interval from the product | 276 | 225 | 225 | 969 | 99.61 ms |
| Leading bits and a 256-entry square table | 282 | 226 | 225 | 0 | 98.89 ms |
| Table with one small interpolation | 276 | 225 | 225 | 0 | 99.56 ms |

The table version used seven small comparisons per input and recovered the same 119 pairs. On the fresh and crossed 2,048-bit products its 106 guesses left 12 and 34 candidate fractions. Using the exact interval left 9 and 33, respectively. None proposed an integer totient in the exact band. One further division of at most 17 bits by at most 9 bits interpolates between the two table entries. With this refinement, every individual exponent gave the same recorded candidate counts and factor witnesses as the exact interval on all 969 inputs. A separate Lean replay regenerated the 106 distinct prefix exponents from each public product and verified the absence of any integer candidate in the exact interval. The timing ranges overlap. The saved square roots did not produce a measured wall-clock speedup. [Table construction and five-way comparison](../experiments/midpoint_table_band.py) · [Full-size verification command](../experiments/intermediate_menu_receipt.py)

## Why repeating this menu cannot solve the general case

The lower neighboring fraction $c/d$ of a successful intermediate $a/b$ has $ad-bc=1$ and $Ed=Nc+w$ for a positive remainder $w$. Substituting $E/F=a/b$ gives an exact identity,

$$\gcd(E,F)=w+c(N-F).$$

When $c=0$, the search is just testing a multiple of $E$ as the candidate for $F$. Otherwise a success needs $\gcd(E,F)>p+q-1$. This means that if $E\le p+q-1$, the wider search succeeds exactly when $E$ divides $F$. For example, $E=1$ always includes the true totient, but testing its equally spaced candidates would amount to searching the whole prime-sum interval.

For a uniformly chosen pair of distinct 1,024-bit primes with a 2,048-bit product, fewer than one in $2^{553}$ pairs admit even one nondivisibility shortcut using **any** exponent made entirely from primes at most 1,500. The same bound covers any success at all with such an exponent at least $2^{1024}$. Every exponent in the full-size experiment passes that size threshold. This restriction applies even if we choose the exponent after inspecting the product. It leaves open ways to choose exponents with larger prime factors, and other factoring methods. [Proof for every intermediate coefficient](../PrimeFactors/IntermediateTotientObstruction.lean) · [Counting the exceptional pairs](which-powers-could-reveal-the-prime-sum.md)
