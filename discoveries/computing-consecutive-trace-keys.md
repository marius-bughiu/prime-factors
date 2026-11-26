# Computing consecutive factor-sum lookup keys

On a fresh 92-bit product, the factor-sum search found the same two primes after 11,774 table lookups with each of three ways of computing the keys. A recurrence reduced the explicit modular multiplication count from 45,942 in the original implementation to 41,514. Direct evaluation with cached powers used 43,834. All three stored 6,480 entries. The product was the first eligible draw from a seed fixed before testing. Only the product and public budgets entered the searches. [Factor certificates and fixtures](../benchmarks/lifted-period-trace.json) · [Sample rule and all six comparisons](../research/lifted-period-traces.json)

## Where the multiplications go

A lookup compares a modular unit and its inverse using their sum. For units $v,H$ modulo the input $N$, the keys for consecutive positions are $T_k=vH^k+v^{-1}H^{-k}$. Expanding the product gives

$$T_{k+2}=(H+H^{-1})T_{k+1}-T_k.$$

After two seed values, each new key costs one modular multiplication and a subtraction. This is the classical Chebyshev recurrence. Lean checks it for signed indices over any commutative ring with the supplied units, including composite moduli. If a lookup succeeds, the program restores the oriented unit and checks the candidate sum or a gcd. [NIST, recurrence coefficients](https://dlmf.nist.gov/18.9.T1) · [Lean recurrence](../PrimeFactors/LiftedPeriodTrace.lean)

The right table also has consecutive indices. If its original period is $M$ and the enlarged period is $Q=hM$, take the representatives $r+kM$ in $(-Q/2,Q/2]$. Reciprocal units have the same key, so the stored position is $|r+kM|$. For self-inverse residues only the nonnegative positions are needed. The comparison checks the entire table, including entry order within each bucket, and charges powers, inversions and multiplications separately. [Implementation and replay](../experiments/lifted_period_trace.py) · [Lifted-period coverage proof](../PrimeFactors/LiftedWheelPeriod.lean)

| Product | Lookups to split | Original multiplications | Direct multiplications | Recurrence multiplications | Setup powers, original / direct / recurrence |
|---|---:|---:|---:|---:|---:|
| Fresh 92-bit draw | 11,774 | 45,942 | 43,834 | 41,514 | 79 / 79 / 77 |
| Earlier 96-bit draw 3 | 14,764 | 90,754 | 64,230 | 46,257 | 72 / 80 / 70 |

Nine rounds rotated the evaluation order. Median table setup plus search on the fresh product took 18.3, 18.0 and 16.5 ms in table order, after 21.1 ms of shared planning. On the 96-bit example those medians were 25.6, 26.8 and 23.7 ms after 20.6 ms of planning. On 96-bit draw 2 the original implementation was faster than the recurrence. The arithmetic counts are reproducible. The timings depend on the host and exclude primality certification. The factor-sum candidates and the number of lookups remain the same. [Counts and local timings](../research/lifted-period-traces.json)

## Can an extra prime skip the lookup?

At a prime $\ell$ coprime to $N$, the true sum must belong to $A_\ell=\{x+N/x\bmod\ell:x\ne0\}$. One lookup tests an offset $c$ together with a set of signed right positions $t$. The extra prime rules out the lookup exactly when **every** $t$ with $c+t$ in the search interval has $(c+t)\bmod\ell\notin A_\ell$. On the fresh draw, the complete schedule has 13,449 distinct keys. One lookup has no positions within the interval. Every other lookup admits a position modulo 37. Across the four earlier 96-bit products, the largest omitted prime rejected just two additional lookups in total. Using all omitted primes together rejected eleven. These counts concern rejection before a hash lookup on the selected schedules. [Exact geometry census](../research/deferred-wrap-filter.json)

For each 2,048-bit control, divide $(-Q/2,Q/2]$ into 256 equal bins. Vary just the right digits modulo 709 and 733 and take all lifts, fixing every other right digit at its least allowed value. On the fresh product every bin contains at least 641 distinct residues modulo 739, while the sum menu has 369. On the crossed product the corresponding counts are at least 719 and 372 modulo 743. Two subsets of a prime residue ring must meet when their sizes add to more than the prime. Consequently every clipped interval containing an entire bin admits a signed position for every translation of the deferred menu. The calculation visited 388,692 and 649,650 positions in these two-digit subsets. The full right tables exceeded the storage budget on both products, and neither run found a factor. [Reproducible calculation](../experiments/deferred_wrap_filter.py) · [Exact results and budgets](../research/deferred-wrap-filter.json)
