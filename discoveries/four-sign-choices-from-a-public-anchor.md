# Trying all four sign choices from the product

For two unknown 1,024-bit primes, a deterministic search used to allow every prime through one billion to cover four possible sign choices. We can cover the same four choices with **at most 83,634 discriminants**, after a separate search for one publicly recognizable starting value. Both guarantees use published consequences of the Dirichlet generalized Riemann hypothesis. Covering a sign choice helps only when the corresponding arithmetic on the hidden factors is favorable. [Previous construction](jacobi-separation.md) · [Lean covering theorem](../PrimeFactors/FourDiscriminants.lean) · [Analytic bounds, Theorems 1.1 and 1.4](https://arxiv.org/html/1309.3595v3#S1.SS1)

## Where the four choices enter

Let the input be $N=pq$ for distinct odd primes. An integer $D$ coprime to $N$ has a sign at each prime. Its sign at $p$ is $+1$ when $D$ is a square modulo $p$ and $-1$ otherwise. The product of the two signs is the Jacobi symbol, which can be computed from $D$ and $N$ alone. For signs $s,t$, a quadratic arithmetic test uses local groups of sizes $P=p-s$ and $Q=q-t$. Raising a group element to the public power $N-st$ removes the common part $g=\gcd(P,Q)$ from the two group sizes. The two remaining orders divide $P/g$ and $Q/g$ and are coprime. If either is small or has only small prime divisors, this can make a factor easier to recover. [Local group and exponent identities](../PrimeFactors/JacobiSeparation.lean) · [Prime-power readout](../PrimeFactors/FourDiscriminants.lean)

Choose an integer $a$ whose Jacobi symbol is $-1$. Then $a$ has opposite signs at the two primes. In the proof, call the prime where $a$ is a square $r$. If $b$ is a nonsquare at $r$, the four integers $1,a,b,ab$ exhibit all four sign pairs. At $r$ the signs of $1,a$ are positive and those of $b,ab$ negative. At the other prime, multiplying by $a$ flips the sign in both pairs. The search needs no way of recognizing $r$ or the right $b$. It tries $1,a$ once and tries both $b$ and $ab$ for each small prime $b$. The Lean result takes the existence of a nonsquare at each prime in the tested list as an explicit premise. [Proof and maximum menu size](../PrimeFactors/FourDiscriminants.lean)

For example, $N=77$ has Jacobi symbol $-1$ at $a=2$. Its signs at 7 and 11 are $+,-$. Taking $b=3$, the four discriminants $1,2,3,6$ give respectively $(+,+),(+,-),(-,+),(-,-)$. Checking the signs in this illustration uses the known primes. Generating the discriminants uses just 77.

## Cost at 2,048 bits

Theorem 1.1(2) of Lamzouri, Li and Soundararajan applies at modulus $N$. The Jacobi-positive units form a proper subgroup by quadratic reciprocity and the Chinese remainder theorem. The prime divisors of $N$ exceed $(\log N)^2$. Thus a prime anchor $a$ occurs by $(\log N)^2 < 2{,}015{,}166$. This preliminary scan requires only Jacobi symbols. At either hidden prime $r$, their Corollary 1.1 bounds the least quadratic nonresidue by $(\log r)^2 < 503{,}792$. A least positive nonresidue is prime by multiplicativity. There are 41,816 primes through 503,792, hence at most $2+2\cdot41{,}816=83{,}634$ discriminants for the expensive group tests. A prime sieve reproduces the counts. The numerical bounds use natural logarithms and the specified factor widths. This application of the published bounds is a written deduction. The local Lean proof checks the covering step independently. [Analytic bounds](https://arxiv.org/html/1309.3595v3#S1.SS1) · [Verified upstream Dirichlet statements](https://math.mit.edu/~drew/grh/)

For a given discriminant one still has to find a group element that survives the initial power, and the smoothness or size of its local orders determines whether the subsequent search succeeds within budget. An arbitrary product can have large residual orders for all four choices. [Exact local success conditions](jacobi-separation.md)

## What happened with eight choices?

We gave three discriminant searches eight trials each. One used the paired construction, one tried ascending primes, and the third started with $1,a$ and continued with primes. An ordinary $p-1$ sweep and a sweep starting with the public power $N-1$ supplied two more comparisons. All three discriminant searches use the same product-derived starting element whenever they try the same $D$. Each tries the public power first and then the prime powers $8,9,5,7,11,13$ in order. This short schedule has product $\mathrm{lcm}(1,\ldots,13)$. Larger powers of these primes can survive it. [Implementation and seed selection](../experiments/signed_discriminant_menu.py)

| Bits per prime | Products | Covered all signs, paired / ascending | Found a factor, paired / ascending | Paired alone / ascending alone |
|---:|---:|---:|---:|---:|
| 12 | 512 | 451 / 324 | 230 / 228 | 36 / 34 |
| 16 | 512 | 449 / 335 | 42 / 37 | 17 / 12 |
| 20 | 512 | 440 / 324 | 5 / 8 | 0 / 3 |

The sign columns use the full planned list of eight choices and the known primes to score it afterward. Searches stop at the first factor. On the fresh and mixed-negative 2,048-bit comparisons, all five methods exhausted the eight trials. Each discriminant method spent 56 power evaluations and 56 readout gcds per product. Both products remain unresolved. [Per-product records, operation counts and timings](../research/signed-discriminant-menu.json)

On $2{,}218{,}279{,}573$, the paired construction tried $D=10$, whose signs are both negative. The final power of 13 exposed $58{,}967$, giving the other prime $37{,}619$. The eight ascending primes missed this sign pair and found no factor. On $2{,}222{,}165{,}411$, the ascending search found $37{,}799\times58{,}789$ with $D=11$, while the paired search missed. Lean checks both positive power computations from their published integer seeds. [Certified fixtures](../benchmarks/signed-discriminant-menu.json)

Random choices provide another way to cover the signs. After one negative-Jacobi anchor is known, sixteen independent uniform unit draws paired with their anchor multiples cover all four signs with probability $65{,}535/65{,}536$. The subsequent factor search has its own success condition. [Exact count and cost for one prescribed Jacobi sign](random-discriminants-in-pairs.md)
