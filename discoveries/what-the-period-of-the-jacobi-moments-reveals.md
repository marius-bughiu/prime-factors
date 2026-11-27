# What does the period of the Jacobi moments reveal?

For $77$, the positive-degree Jacobi moments repeat every 30 degrees. Keeping only even degrees produces a sequence that repeats every 15 terms. Lean proves what these numbers mean for every product $N=pq$ of distinct primes at least seven. **The smallest period of the full sequence is the Carmichael function $\lambda(N)$, and the smallest period of the even sequence is $\lambda(N)/2$.** The Carmichael function is the least positive exponent that sends every unit modulo $N$ to one. For these products it is $\operatorname{lcm}(p-1,q-1)$. Knowing either period gives this familiar group invariant by at most one doubling. The calculation below measures it on small products. An inexpensive way to find it from an arbitrary balanced 2,048-bit product remains open. [Lean period theorem](../PrimeFactors/JacobiMomentPeriod.lean)

## Why is this the *smallest* period?

The degree-$k$ moment is $M_k=\sum_{t\bmod N}t^k(\frac{t^2-4}{N})\pmod N$. Reduce the positive even moments $M_2,M_4,\ldots$ modulo a prime factor $\ell\ge7$. Fermat's little theorem gives a period $d=(\ell-1)/2$. A period $h$ would give the recurrence $u_{j+h}-u_j=0$. The earlier recurrence theorem requires its order to be at least $(\ell-3)/2=d-1$. The least period divides $d$, and every proper divisor of $d$ is at most $d/2$. Since $d\ge3$, the least period must be $d$. [Recurrence lower bound](can-a-short-recurrence-skip-the-moment-scan.md)

The Chinese remainder theorem says a shift preserves the sequence modulo $N$ exactly when it preserves both prime-field sequences. Their least common multiple is therefore the composite period. At prime 3 the local even sequence is zero. At prime 5 it is constant because the only contributing square base is one. Both have least period one. This changes the half-Carmichael formula on some small products. At $35$ the even period is 3 and $\lambda(35)=12$. At $65$ the even period is 6 and $\lambda(65)=12$. For primes at least seven, every odd-degree moment vanishes and $M_2=2\pmod N$. Thus a shift preserving the full sequence must be even, and its half must preserve the even subsequence. All periods here start at positive degree. [Small-prime cases and full-sequence proof](../PrimeFactors/JacobiMomentPeriod.lean)

## Measuring the periods from a small product

The checker takes $N$ alone, computes all $N$ Jacobi signs once, and weights each residue’s successive powers by its sign through degree $4N$. It tests each candidate shift against a block of $N$ values. That block spans a whole period because Fermat's theorem at the two primes gives a common period at most $(p-1)(q-1)<N$. It independently finds the unit-group exponent by enumerating the units and measuring their orders. The comparison reads the fixture's factors after both measurements. [Reproducible checker](../experiments/jacobi_moment_periods.py) · [Inputs and expected results](../benchmarks/jacobi-moment-periods.json)

| Product | Period of all positive degrees | Period using only even degrees | Unit-group exponent |
| ---: | ---: | ---: | ---: |
| 15 | 2 | 1 | 4 |
| 21 | 6 | 3 | 6 |
| 35 | 6 | 3 | 12 |
| 65 | 12 | 6 | 12 |
| 77 | 30 | 15 | 30 |
| 143 | 60 | 30 | 60 |
| 221 | 48 | 24 | 48 |

Run `python3 -m experiments.jacobi_moment_periods` to reproduce the table. At 77 the checker evaluates 308 degrees with 77 weighted terms each, or 23,716 modular term updates, before comparing shifts. For two 1,024-bit primes Lean bounds the least even period $L$ by $2^{1022}\le L<2^{2046}$. This measures the distance between repetitions in a sequence. It gives neither a lower bound on the number of samples an indirect algorithm must take nor a running time for evaluating one carefully chosen high degree. [Full-size period bounds](../PrimeFactors/JacobiMomentPeriod.lean)
