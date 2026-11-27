# Testing one remaining prime after the predecessor sweep

On one previously constructed 2,048-bit product, trying 143 small primes after the first sweep recovered a certified prime factor in **32,561 modular squares and multiplies**, including setup. Extending the original prime-power sweep to the same limit took **124,802**. Both methods used only the product as input. Both left the fresh and crossed 2,048-bit controls unresolved. [Pinned inputs](../benchmarks/weighted-crowding.json) · [Bounded reproducer](../experiments/projected_prime_continuation.py)

## Why this input responds

Start with $2^{N-1}\bmod N$. For every prime at most 100, raise the residue to the largest power of that prime below $2^{1024}$. Call the resulting residue $z$. On all three inputs, $\gcd(z-1,N)=1$, so $z$ was still different from 1 at both unknown primes. For a prime $\ell>100$, a nontrivial gcd of $z^\ell-1$ with $N$ reveals a factor. This happens when $z$ has order exactly $\ell$ at that factor. The initial $N-1$ power ensures the two local orders are coprime, which also lets the cumulative sweep use a single final readout. [Projected-order and readout proofs](../PrimeFactors/ReducedSmoothReadout.lean)

The positive fixture was originally built for a different experiment. Its two primes have the form $p=521h+1$ and $q=557h+1$ with the same $h$. We selected it for this pilot by inspecting existing published factors. The search then ran with the fixed base 2 and fixed bounds 100 and 1,000. After the split, checking $z$ against the certified primes gave order 521 at $p$ and 557 at $q$. The ordinary comparison started directly at 2, omitted the $N-1$ projection, and used the same stage-one powers and independent prime tests. It missed. [Original construction and certificate generator](../scripts/weighted_crowding_benchmark.py)

## Work on the constructed input

| Continuation after the common first sweep | Extra squares | Extra multiplies | Extra gcds | Squares + multiplies including setup |
| --- | ---: | ---: | ---: | ---: |
| Test each prime independently and batch the gcds | 23 | 310 | 7 | 32,561 |
| Raise the running residue to each prime once | 437 | 690 | 1 | 33,355 |
| Raise it to the largest allowed power of each prime | 78,339 | 14,235 | 1 | 124,802 |

The common projection cost 2,044 squares and 268 multiplies. The sweep through 97 cost another 25,483 squares and 4,433 multiplies. Setup also checked the base gcd and the stage-one gcd. Each modular square or multiplication counts as one operation in the last column. Gcds are reported separately. Additions, comparisons, prime-list generation and certificate verification are outside those counts.

The independent test computes every $z^\ell$ for $100<\ell\le1000$, reusing powers of $z$ across the gaps between consecutive primes. The multiply count includes construction of the product tree for the gcds. Both factors appear, so the first gcd is $N$ and the search descends the tree to isolate one factor. The cumulative methods stop when the entire residue first equals 1, at prime 557. Their final gcd uses the preceding residue. On each control, the independent continuation spent 333 modular operations and one gcd, the single-power continuation spent 2,310 modular operations and one gcd, and the full-power continuation spent 171,788 modular operations and one gcd.

A second stage for one remaining prime is classical in Pollard's $p-1$ method and Williams's $p+1$ setting. Montgomery describes accelerated versions for both. The experiment here applies that idea after the public $N-1$ projection, which removed the shared part of these two predecessors. An order divisible by $991^2$, for example, needs more than one factor of 991 in the exponent. The full prime-power continuation covers that case when the rest of the order also divides its exponent. [Pollard, 1974](https://doi.org/10.1017/S0305004100049252) · [Williams, 1982](https://doi.org/10.1090/S0025-5718-1982-0658227-7) · [Montgomery, 1987](https://www.ams.org/journals/mcom/1987-48-177/S0025-5718-1987-0866113-7/S0025-5718-1987-0866113-7.pdf)

From the repository root, run `python3 -m experiments.projected_prime_continuation`. It runs the three public comparisons before accessing any expected factors. It then replays the registered `weighted-crowding-constructed-2048` Lean certificate, checks the discovered divisor against the certified factorization, and prints the two local matches. The operation counts and misses are Python results. Lean checks the prime factors and their product.
