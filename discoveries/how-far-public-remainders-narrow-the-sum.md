# How far can the product’s remainders narrow the factor sum?

On the 39-bit product **419,636,024,497**, remainders alone selected one sum, **1,310,542**. No reading of a character sum or clue from the known factors was used. At 2,048 bits we can also prove a reduction from the product and the factor widths alone. The resulting guarantee still permits up to $2^{519}$ sums and uses primes up to $2^{520}$. [Worked control](../PrimeFactors/PublicSumSieveControl.lean) · [Full-width theorem](../PrimeFactors/FactorSumLargerSieve.lean)

## How the 39-bit example works

Both factors have 20 bits. Their product and those widths put their sum between 1,295,587 and 1,324,680. Since both primes are odd, the sum has the same remainder as $N+1$ modulo four. This leaves 7,273 starting candidates. For each odd prime $\ell$ in increasing order, we keep a candidate $s$ if two residues can multiply to $N$ and add to $s$ modulo $\ell$. The true factors always give such a pair. For example, modulo 3 this product is 1. The pairs $(1,1)$ and $(2,2)$ give sums 2 and 1, so a multiple of three cannot be the factor sum. [Modular condition and proof of retention](../PrimeFactors/FactorSum.lean) · [Width calculation](what-four-square-divisors-reveal.md#enforcing-both-factor-widths)

| Largest odd prime tested | Sums remaining |
| --- | ---: |
| Before testing odd primes | 7,273 |
| 5 | 1,939 |
| 13 | 271 |
| 23 | 38 |
| 31 | 7 |
| 41 | 3 |
| 43 | 1 |

Through 41, the three sums are 1,310,542, 1,321,358 and 1,323,998. The check modulo 43 eliminates the last two. For the survivor, the discriminant $s^2-4N$ is $197{,}424^2$, giving $556{,}559\times753{,}983$. The original experiment published these primes, and we reused that product for this comparison. The inputs to each filter were the product, the endpoints and the small modulus. A straightforward pass that checks every surviving candidate at each stage uses 16,226 small remainder lookups before the final square test. The Lean certificate checks the same stages using bit masks. [Stage counts, survivor and factorization](../PrimeFactors/PublicSumSieveControl.lean)

## Which remainder should we check first?

On the same 39-bit product, changing the order of the thirteen prime tests saves **3,495 of 16,226 lookups (21.54%)**. A lookup checks one candidate sum against one prime’s allowed remainders. Both orders start with all 7,273 candidates, use the same tables, apply all thirteen tests and finish with the same sum. The new order can be chosen before looking at any candidate. Sort the thirteen primes by the fraction of their residues that pass. These fractions come from the product alone. [Order, work counts and final sum](../PrimeFactors/PublicSumSieveOrdering.lean) · [Reproducible inputs and counts](../benchmarks/square-divisor-clue-window.json)

| Order | First three primes | Candidates left after three tests | Total lookups |
| --- | --- | ---: | ---: |
| Increasing prime | 3, 5, 7 | 1,108 | 16,226 |
| Increasing fraction of residues that pass | 5, 11, 29 | 638 | 12,731 |

The setup cost shared by both scans is building the thirteen tables. The changed order also sorts thirteen fractions. The count above measures candidate lookups. A program using packed bit masks has a different cost, and the comparison gives no elapsed-time estimate. [Scalar replay](../experiments/square_divisor_clue_window.py)

There is an exact rule for swapping two adjacent tests in any fixed order. Everything after them sees the same candidates either way, so the saving is exactly the difference between how many current candidates each of the two tests passes. On a complete period of coprime moduli, the Chinese remainder theorem makes the residue frequencies independent. With equal costs per lookup, sorting by increasing passing fraction minimizes the total on that complete period. [Adjacent exchange proof](../PrimeFactors/FiniteFilterWork.lean) · [Independence on complete periods](../PrimeFactors/FactorSumCRT.lean) · [Minimum over all orders](../PrimeFactors/IndependentFilterOrdering.lean)

The actual search interval can favor a different order. In the 638 candidates left after 5, 11 and 29, the modulo-37 test passes 310 and the modulo-41 test passes only 286. Their full-period passing fractions are $18/37$ and $20/41$, in the opposite order. Swapping this particular adjacent pair would save another 24 lookups. Discovering such a reversal by counting the current candidates has its own cost. [Verified partial-period counterexample](../PrimeFactors/PublicSumSieveOrdering.lean)

## What do inexpensive remainders save at 2,048 bits?

On the two published comparisons, we counted how many square tests would be needed to visit the **entire** interval allowed by the factor widths. Both columns use only the product and the widths. The first uses the known sum modulo four. The second also uses the odd primes through 19. Counting complete blocks of 19,399,380 residues and bounding the last partial block gives both an upper and a lower bound. [Exact comparison proofs](../PrimeFactors/PublicWheelWidthControls.lean)

| Product | Candidates after modulo four | Candidates after the small-prime checks | Ratio of the two counts |
| --- | ---: | ---: | ---: |
| Fresh | $2^{1015}$ to below $2^{1016}$ | $2^{1008}$ to below $2^{1009}$ | 124.73 to 124.74 |
| Crossed | $2^{1017}$ to below $2^{1018}$ | $2^{1011}$ to below $2^{1012}$ | 84.19 to 84.20 |

These are reductions in the number of candidates for an exhaustive search. Even on the fresh product, the smaller list has over $10^{303}$ entries. The count tells us neither where the correct entry appears nor how long an early success would take. [Published controls and modular counts](../PrimeFactors/IntervalWheelControls.lean)

## What can be proved for every full-size product?

If both primes have 1,024 bits, their sum lies in the $2^{1024}$ consecutive integers from $2^{1024}$ to $2^{1025}-1$. At each odd prime $\ell$ below the factors, at most $(\ell+1)/2$ residues can be sums. After imposing all of these conditions through $2^{520}$, **at most $2^{519}$ sums survive**, including the true sum. This is an unconditional statement about the number of survivors. It gives no fast way to locate them in the original interval. [Local residue count](../PrimeFactors/IntervalWheelResidues.lean) · [Containment and cardinality](../PrimeFactors/FactorSumLargerSieve.lean)

How expensive is it to apply that many conditions? There are **more than $2^{511}$ odd primes** through the cutoff. A method that visits each of them already has at least that many steps before accounting for candidate enumeration. Lean verifies this cost bound using an elementary least-common-multiple estimate. [Prime-count proof](../PrimeFactors/IntervalSievePrimeCount.lean)

The result specializes Gallagher’s 1971 larger sieve. Suppose $K$ integers occupy at most $g$ residue classes at a prime $\ell$. Then at least $K^2/g-K$ ordered pairs of distinct integers agree modulo $\ell$. Each agreement means $\ell$ divides their difference. If the interval has diameter $H$, one difference can contain distinct prime divisors with total log weight at most $\log H$. Counting the agreements both ways bounds $K$. Gallagher treats the same half-residue pattern. Our Lean proof gives explicit constants and checks the factor-sum application. [Gallagher, Theorem 1 and its first application](https://www.impan.pl/en/publishing-house/journals-and-series/acta-arithmetica/all/18/0/97714/a-larger-sieve) · [Finite collision proof](../PrimeFactors/IntervalLargerSieve.lean)

More generally, in any interval of diameter at most $2^{2k}$, a product coprime to the odd primes through $2^{k+8}$ has at most $2^{k+7}$ locally admissible sums after those tests. This bound follows from an elementary estimate for the sum of $\log\ell/(\ell+1)$ over the selected primes. The factorial and binomial estimates in this calculation need no assumption about zeta zeros. [Prime-weight proof](../PrimeFactors/IntervalSievePrimeWeights.lean) · [General interval result](../PrimeFactors/FactorSumLargerSieve.lean)

An earlier argument using Dirichlet GRH isolates the true sum with much smaller primes on the narrower, product-dependent balanced interval. That result also leaves open how to find the survivor cheaply. The unconditional count here makes a different tradeoff between the number of allowed sums and the sizes of the moduli. [Earlier GRH deduction and its assumptions](factor-sum-residues.md#a-uniform-set-of-primes-that-isolates-the-sum)

A subsequent unconditional argument proves uniqueness on the public range for the same factor widths by raising the cutoff to $2^{940}$. More than $2^{930}$ odd primes lie below that cutoff. [Which prime rejects a wrong factor sum?](which-prime-rejects-a-wrong-factor-sum.md)
