# Can we jump directly to divisors that pass a sign test?

Yes, when the product supplies a small enough modulus. On twelve held-out products, jumping cut the number of trial divisions by about half. Building the lists still cost enough that plain trial division finished sooner across each six-product batch. The smallest moduli found on the two 2,048-bit examples already require around $10^{298}$ to $10^{300}$ sign evaluations for this implementation. [All results and certificates](../research/divisor-sign-jumps.json)

## How to generate the candidates

Given $N$ and the common bit width $b$ of its two prime factors, search for the smaller prime from $\max(2^{b-1},\lceil N/(2^b-1)\rceil)$ through $\lfloor\sqrt N\rfloor$. In these examples the primes exceed 5, so only the 16 invertible classes modulo 60 need a trial division. A continued-fraction search on $4N$ also finds a public witness $a^2\equiv-d\pmod N$ with $d\equiv3\pmod4$ and $\gcd(d,60N)=1$. Every odd divisor of $N$ then has Jacobi symbol $+1$ modulo $d$. [Proof of the divisor test](../PrimeFactors/ReciprocalDivisorClasses.lean)

For each $1\le x\le(d-1)/2$, compute one Jacobi symbol. A positive sign selects $x$, a negative sign selects $d-x$, and zero skips both. This lists every positive class exactly once because negation reverses the sign. The **eager** method combines those classes with the wheel modulo 60 by the Chinese remainder theorem and sorts the resulting list. The **lazy** method sorts only the positive classes modulo $d$. In a block starting at a multiple $h$ of $d$, it keeps the offsets $r$ for which $h+r$ is coprime to 60. It caches each translated list the first time the scan reaches that phase $h\bmod60$. Both methods visit precisely the same integers in ascending order and neither evaluates another Jacobi symbol while testing divisors. [Search implementation](../experiments/divisor_sign_jumps.py)

There is also a proved algebraic generator when a suitable prime component of $d$ is known. For an odd prime $p$, the squares of $1,\ldots,(p-1)/2$ enumerate every positive class exactly once. For $d=p^e m$, with $p\equiv3\pmod4$, $e$ odd and $\gcd(p,m)=1$, fixing a unit class modulo $m$ lets a sign and a CRT lift select the correct square classes modulo $p$. The resulting progressions have stride $pm$. The timings below use the general Jacobi loop. [Lean proofs of the prime and composite generators](../PrimeFactors/GeneratingDivisorSigns.lean)

## Timings on the held-out products

We used the first six pairs at each width to develop the lazy implementation. Before testing the remaining six at each width, we fixed an optional public choice. If the whole interval has $C$ candidates modulo 60, build the lazy table only when $(d-1)/2\le C/4$. This forecasts that the search reaches the middle of the interval and saves half the divisions up to that point. Both quantities are available from the input. The test treats an initial Jacobi evaluation and a trial division as equally costly. That approximation has no runtime guarantee. [Input selection and frozen rule](../experiments/divisor_sign_jumps.py)

| Method | 20-bit primes, divisions | Six-product CPU | 24-bit primes, divisions | Six-product CPU |
|---|---:|---:|---:|---:|
| Modulo 60 | 110,476 | 9.91 ms | 1,026,317 | 90.36 ms |
| Segmented sieve, then divide by primes | 30,749 | 10.77 ms | 235,464 | 107.04 ms |
| Eager sorted table | 54,305 | 70.10 ms | 504,786 | 1,616.71 ms |
| Lazy sorted blocks | 54,305 | 33.71 ms | 504,786 | 633.46 ms |
| Public choice between lazy blocks and modulo 60 | 74,483 | 16.72 ms | 553,327 | 240.58 ms |

The choice beat modulo 60 on four of the six 24-bit products and none of the six 20-bit products. For $252256028742617=15453343\cdot16323719$, the modulus was 727. The lazy search needed 363 initial signs and 55,606 divisions, taking 5.88 ms against 9.70 ms for modulo 60. For $173120549043383=10743773\cdot16113571$, the rule accepted a modulus of 295,423. Its 147,711 initial sign evaluations already exceeded the 113,329 divisions needed by modulo 60. The selected search took 179.21 ms against 9.95 ms. Lean verified primality and the product for every recovered pair. [Per-product work, timings and certificate hashes](../research/divisor-sign-jumps.json)

## Cost on the two full-size inputs

After $2^{20}$ public continued-fraction steps per input, the smallest eligible $d$ had **999 bits** on the fresh input and **991 bits** on the crossed input. We checked each root against its public $N$. The initial positive-class lists would take about $1.82\times10^{300}$ and $8.08\times10^{297}$ sign evaluations respectively. Moreover, the eager table has $8\varphi(d)$ entries. For these sizes $d<13\varphi(d)$, so even a packed fixed-width array of the CRT residues would exceed $2^{1004}$ and $2^{996}$ bytes respectively. Lazy blocks avoid the full CRT array but still need the initial list. We did not build either full-size list or recover a factor from it. These costs apply to the measured generators and the moduli found with this budget. [Public roots and periods](../research/many-character-windows.json) · [Totient bound](../PrimeFactors/QuotientBudget.lean)

## Reproduce the comparison

Run `python3 -m experiments.divisor_sign_jumps --check` to replay the exact counts and all 24 distinct Lean factorizations. Run `python3 -m experiments.divisor_sign_jumps --write` to remeasure. Each method receives only $N$ and the common factor width. Each sign search pays for up to 256 continued-fraction steps and uses the smallest eligible $d\le10^6$. All 24 products yielded such a modulus. Timers include bounds, table construction, sorting, sieve setup and scanning through the first factor. The reported CPU medians use five cyclic method orders per product on ARM64 macOS with Python 3.9.6. The report also preserves the initial three-method comparison and elapsed times, and excludes input selection and certificate verification from search timing. [Experiment](../experiments/divisor_sign_jumps.py) · [Recorded results](../research/divisor-sign-jumps.json)
