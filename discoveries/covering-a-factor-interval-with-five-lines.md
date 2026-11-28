# Covering a factor interval with five lines

For $N=119{,}423$, consider possible divisors from 301 through 314. The product and the two endpoints give weights 5 and 4. Every factor pair in that interval has $5x+4y$ equal to 3,091 or 3,092. The factors are odd, so only 3,091 can work. Its discriminant is $3091^2-4\cdot5\cdot4\cdot119423=441=21^2$. The integer root is $(3091-21)/10=307$, yielding $119{,}423=307\cdot389$. This is one block in the ordinary ascending schedule. Lean verifies the enclosure and uniqueness for every possible factor pair in that block. [Worked Lean proof](../PrimeFactors/QuotientStripLevels.lean) · [Prime certificate fixture](../benchmarks/cases.json)

## Where five comes from

Let $[a,b]$ be a block inside the balanced search interval $[\lceil\sqrt{N/2}\rceil,\lfloor\sqrt N\rfloor]$. Put $d=b-a$. The block has at most twice the nearest integer sixth root of $N$ columns, so $d^6\le64N$. For $d\ge2$, use $Q=\lfloor d/2\rfloor$ and choose a rational approximation $u/v$ to $N/(ab)$ such that $0<v\le Q$ and $|uab-vN|(Q+1)\le ab$. Dirichlet approximation guarantees existence. The experiment obtains the direction from the last continued-fraction convergent with denominator at most $Q$, and checks the displayed integer inequality. A block of one or two columns can always be tested directly. [Approximation and schedule proofs](../PrimeFactors/QuotientStripLevels.lean) · [Integer implementation](../experiments/quotient_strip_levels.py)

Write $z=ux+vy$. On the chord joining $(a,N/a)$ and $(b,N/b)$, $z$ changes by at most $d/(Q+1)<2$. A true point on $xy=N$ lies below the chord by at most $Nd^2/(4a^2b)$ in its second coordinate. Its downward displacement in $z$ is therefore at most $vNd^2/(4a^2b)<3$. For the last bound, use $2v\le d$, $N\le2a^2$ and $d^3<12a$. The two weighted endpoint values and the downward allowance give a computable closed interval of width strictly below five. It contains at most five integers. [Chord-depth inequality](../PrimeFactors/SecantQuotientCells.lean) · [Uniform five-level cover](../PrimeFactors/QuotientStripLevels.lean)

For odd $N$, an odd $x$ satisfies $x^2\equiv1\pmod8$, so $y\equiv Nx\pmod8$. Among the five possible labels, retain only residues $(u+vN)j$ for $j=1,3,5,7$ modulo eight. At most three remain, at most two when $u+vN$ is even, and at most one when four divides it. All three cardinality bounds are sharp for the residue filter. A surviving label still needs its discriminant checked. For $35=5\cdot7$ the filter keeps both 15 and 19 for $x+2y$ on the labels 15 through 19. Only 19 comes from the indicated factors, and Lean excludes 15 for every integer factor pair. [Residue classes, sharp bounds and false positive](../PrimeFactors/QuotientStripLevelResidues.lean)

Hiary’s deterministic factoring algorithm already used rational approximations and quadratic tests to examine short intervals in cube-root time up to subpolynomial factors. Here the chord gives an explicit five-label bound for this repository’s block width, and the experiment compares it against our existing moment-based implementations. The proofs use elementary geometry, integer arithmetic and Dirichlet approximation. They require no Riemann hypothesis. [Hiary, algorithm 1](https://arxiv.org/html/1408.2608v3#S2) · [Previous interval search](quotient-search.md) · [Project’s analytic assumptions](../docs/research.md)

## How much work does the local calculation save?

All methods received only the product for each of the 99 ratio-selected inputs and 64 holdout inputs. The holdout uses distinct 10-bit primes with no prescribed ratio. Every method recovered the expected smaller prime. The entries below charge work through the first returned factor. Continued fractions and square roots have different costs from ordinary remainder checks. [Full-scan and first-hit measurements](../benchmarks/quotient-strip-levels.json) · [Moment comparison](narrowing-a-factor-interval-with-strip-moments.md)

| Method and measured operation | 99 ratio-selected products | 64 holdout products |
|---|---:|---:|
| Direct odd trial, remainder checks | 33,216 | 4,252 |
| Joint product-error bound, remainder checks | 21,552 | 2,488 |
| Joint product-error bound, floor-moment states | 525,044 | 103,561 |
| Chord and mod 8, continued-fraction divisions with remainder | 9,908 | 2,007 |
| Chord and mod 8, retained labels | 1,500 | 368 |
| Chord and mod 8, integer square roots of discriminants | 1,260 | 301 |

The chord calculation needs no floor-moment states. The timing comparison gave a different winner at different sizes. Each cell below reports median CPU milliseconds through the first factor, with the same ascending-block or ascending-divisor stopping rule. The 41-bit and 46-bit products were chosen from existing fixtures. Three rotated repetitions were used for the twelve small products and five alternating repetitions for each larger input. Measurements used CPython 3.14.7 on arm64 macOS 27.0.1. The chord implementation includes its operation counters. Direct trial uses a plain remainder loop. Both exclude input preparation and verification of the expected answer. [Timing driver](../experiments/quotient_strip_levels.py) · [Input provenance](../benchmarks/modular-hyperbola.json)

| Input | Chord and mod 8 | Direct odd trial |
|---|---:|---:|
| Twelve small products combined | 0.835 ms | 0.113 ms |
| 1,900,014,700,027 (41 bits) | 0.714 ms | 0.635 ms |
| 45,249,671,261,437 (46 bits) | 23.929 ms | 30.918 ms |

The 46-bit run through the first hit used 23,071 continued-fraction divisions and 2,020 discriminant square roots across 3,411 blocks. Direct trial tested 644,576 odd divisors. For complete sweeps on this same input the medians were 34.304 ms for the chord search and 48.721 ms for direct trial. These measurements establish a win on one known product against this baseline. [Deterministic work and full-sweep counts](../benchmarks/quotient-strip-levels.json)

## What happens at 2,048 bits?

Every 2,048-bit product has **more than $2^{679}$ and fewer than $2^{680}$ blocks** in this full balanced sweep. If $N=pq$, $p\le q$ and $3q\le4p$, the ascending sweep must visit more than $2^{678}$ blocks even to reach the smaller factor. A known upper bound on the larger prime can move the starting point. When $N\ge3\cdot2^{2046}$ and $q\le2^{1024}$, starting at $\lfloor N/2^{1024}\rfloor$ skips at least $2^{678}$ whole blocks. These bounds apply to this particular schedule. [Exact counts and optional jump](../PrimeFactors/QuotientStripScheduleCost.lean)

On the existing certified 2,048-bit product, we tested four blocks selected by their public indices before consulting either factor. They contained zero, two, one and zero possible integer labels before residue screening. None yielded a factor. In a separate positive control we **used the known smaller prime to select its block**. That block required 215 continued-fraction divisions and one discriminant square root to recover the prime. The unresolved cost is finding the right block from the product alone. [Full-size inputs, selection rules and measurements](../benchmarks/quotient-strip-levels.json) · [Provenance of the certified product](certified-fresh-control.md)
