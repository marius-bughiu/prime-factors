# Testing a chain of powers with one gcd

On our independently generated 2,048-bit example, checking each successive square of $t=\lfloor\sqrt N\rfloor$ took 1,024 gcds. We can check whether **any** of those gcds would yield a proper factor using just **one gcd** and the same 1,023 modular squarings. The answer was no. The same computation rules out all later squarings under the stated promise that the two distinct primes have at most 1,024 bits. [One-gcd theorem](../PrimeFactors/LastPowerGCD.lean) · [Exact cutoff](../PrimeFactors/SquareRootPowerPopulation.lean)

## Which power to keep

Suppose that each exponent divides the next. Then $a^e-1$ divides $a^f-1$ when $e\mid f$, so the gcds of these integers with $N$ form a divisibility chain. Compute the powers modulo $N$ and retain the last residue different from one. Stop when the next residue is one or the exponent budget is exhausted. If there was a retained value $v$, compute $\gcd(v-1,N)$. If it is one, every earlier gcd was one. If it is larger than one, it is a proper factor because $v$ differs from one modulo $N$. All subsequent residues after a one are also one. This argument applies to composite inputs with repeated factors as well. A classical use of a nontrivial square root of one to recover a divisor appears in Rabin's primality test. [Divisibility and stopping proof](../PrimeFactors/LastPowerGCD.lean) · [Rabin, 1980](https://doi.org/10.1016/0022-314X(80)90084-0)

The last step of a chain can conceal a useful earlier value. For $33{,}227=149\times223$ and $t=182$, start with $t^{16613}\bmod N$. Subtracting one and taking a gcd gives 149. After just one squaring, the residue is one and the gcd would be the entire input. On $33{,}389=173\times193$, starting directly at $t=182$ requires six squarings before a gcd first reveals 193. [Reproducible search](../experiments/square_root_power_chain.py) · [Prime-power example](../PrimeFactors/SquareRootPowerPopulation.lean)

## How far each family reaches

For exponents $2^k$, only elements of power-of-two multiplicative order can ever reach one at a prime $p$. The number of such elements is $2^{v_2(p-1)}$. Counting odd partners compatible with their squared square-root residues and summing these weights over the dyadic interval shows that **fewer than one in $2^{989}$** eligible prime pairs can split at *any* $k$. At each prime the local zero condition has stabilized by $k=1023$. Lean proves equality of the actual gcds after that point, including both trivial outcomes. The population consists of unordered pairs of distinct 1,024-bit primes whose product has 2,048 bits. [Weight sum, population and stabilization](../PrimeFactors/SquareRootPowerPopulation.lean)

There is a separate result for the product-dependent exponent $N-1$. At a prime $p\mid N=pq$, an order $e$ dividing $N-1$ must divide both $p-1$ and $q-1$. For small $e$, at most $2e$ odd partners give the necessary square-root residues, and there are few eligible first primes congruent to one modulo $e$. For large $e$, write $p=1+ae$, $q=1+ce$ in ascending order. The available values of $a,c,e$ already bound the pair count. Splitting the two counts at $e=2^{512}$ gives **fewer than one in $2^{484}$** eligible pairs for which the final gcd even exceeds one. This covers every $t^d-1$ for $d\mid N-1$ and every $t^d+1$ for $2d\mid N-1$. The same bound allows an additional gcd with $t$, which can succeed in this population only for twin primes. [Product exponent and both signs](../PrimeFactors/ProductExponentPopulation.lean)

## Measured work

We tested every pair of distinct 12-bit primes with a 24-bit product. Both versions found the same factors, including which prime was returned. The per-stage version stops at its first proper gcd. The one-gcd version sometimes performs extra modular squarings before it checks. For the second row both searches start with the same modular exponentiation at the odd part of $N-1$.

| Exponents on 19,546 products | Pairs split | Per-stage gcds | One-gcd version | Per-stage squarings | One-gcd version squarings |
|---|---:|---:|---:|---:|---:|
| $1,2,4,\ldots,2^{11}$ | 85 | 233,861 | 19,546 | 214,318 | 214,979 |
| Odd part of $N-1$, doubled up to $N-1$ | 122 | 58,312 | 19,539 | 38,780 | 38,956 |

On the fresh and crossed 2,048-bit examples, both families' terminal gcds were one. For the $N-1$ experiment the two inputs required one and 303 modular squarings, respectively, after the initial modular exponentiation. The infinite-power exclusion uses the assumed factor widths. The $N-1$ divisor exclusion follows directly from the checked terminal residue. [Census and counters](../experiments/square_root_power_chain.py) · [How the controls were generated](certified-fresh-control.md)
