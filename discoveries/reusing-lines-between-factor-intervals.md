# Reusing lines between factor intervals

On the 46-bit product **45,249,671,261,437**, the search found the first factor after **1,189 integer square-root tests**, down from **2,020** in the earlier search. Both reached the factor in the same interval. The modulo-24 rule saves those square roots by rejecting candidate lines earlier. A separate change carries a rational approximation forward as the intervals move, cutting the divisions needed to choose it. The largest complete search in this comparison was 46 bits. [Operation counts](../benchmarks/quotient-strip-farey.json) · [Original interval search](covering-a-factor-interval-with-five-lines.md)

## How one line can find a pair of factors

Suppose the unknown factors satisfy $N=xy$ and $x\le y\le 2x$. If $x$ lies in a short interval $[A,B]$, then $y=N/x$ lies on a short arc. A line with positive integer weights $u,v$ has equation $ux+vy=z$. Choosing the slope $-u/v$ close to the slope of the chord through the ends of the arc, $-N/(AB)$, confines the integer $z$ to a short range. Each candidate gives the quadratic $ux^2-zx+vN=0$. Its discriminant $z^2-4uvN$ must be a nonnegative square, and the resulting integer $x$ must divide $N$. Hiary used an approximation to $N/x^2$ to recover divisors in a short interval by solving a quadratic. Here the intervals and their chord bounds come from the repository's five-line search. [Hiary, Lemmas 3.1–3.2](https://arxiv.org/pdf/1408.2608) · [Chord bounds](../PrimeFactors/QuotientStripLevels.lean)

The full intervals have the same width, twice the rounded sixth root of $N$. They therefore share a denominator limit $Q=\max(1,\lfloor(B-A)/2\rfloor)$. Order the reduced fractions in $[1,2]$ with denominator at most $Q$. As $A$ and $B$ increase, $N/(AB)$ decreases. The search moves through these Farey fractions in one direction. For consecutive neighbors $a/b<c/d$, the preferred fraction changes at their *mediant* $(a+c)/(b+d)$, where the two errors $|aAB-bN|$ and $|cAB-dN|$ agree. An integer comparison detects the crossing. One integer quotient generates the next neighbor. The last, shorter interval uses its own continued fraction if it contains more than one column. [Farey neighbor recurrence, properties 4–5](https://dummit.cos.northeastern.edu/teaching_sp21_4527/4527_lecture_03_farey_sequences_v2.pdf) · [Earlier Farey factor windows](farey-weighted-sums.md)

Either neighbor at a tie minimizes the error and gives the required approximation. To reproduce the original program exactly, the walk chooses the smaller denominator at a tie, then the smaller integer if both denominators are one. It matched the old direction and both chord endpoints on all **11,119** nonsingleton study intervals. An independent enumeration checked **6,686** slope queries, including **995** with multiple minimizers. [Lean optimality and coverage theorems](../PrimeFactors/QuotientStripFareyRuns.lean) · [Canonical implementation checks](../experiments/quotient_strip_farey.py)

## Which lines survive modulo 24?

For $N$ coprime to six, both factors are units modulo 24. Every such unit is its own inverse, so $y\equiv Nx\pmod{24}$. Writing $C=u+vN$, a genuine line must satisfy $z\equiv Cx\pmod{24}$. As $x$ runs through all eight units, these are **exactly** the residues with $\gcd(z,24)=\gcd(C,24)$. The earlier weighted stride retains the single progression $z\equiv C\pmod{\gcd(24,2C)}$. The exact rule can remove further residues within that progression. Passing the rule establishes consistency modulo 24. The quadratic and final division decide whether the integer factor exists. [Existing weighted stride](../PrimeFactors/WeightedStride.lean) · [Lean proof of the exact residue image](../PrimeFactors/QuotientStripLevelMod24.lean)

For example, take $N=12{,}403$ and the scheduled interval $[79,88]$. The weights $(7,4)$ give $1178\le z\le1181$. Here $C\equiv11\pmod{24}$, so the single progression retains the two odd values 1179 and 1181. Since 1179 is divisible by three, the exact rule removes it, saving a square-root test on 905. At 1181 the discriminant is $5625=75^2$, which gives $x=(1181-75)/14=79$ and $y=157$. Multiplication confirms $79\cdot157=12{,}403$. [Interval and quadratic formulas](../experiments/quotient_strip_levels.py)

## Complete scans and first factors

The 99 ratio-selected examples take every eighth prime $p$ starting at 257 and the first prime $q>\lfloor5p/4\rfloor$, with both at most 8,191. The 64 holdouts use deterministic, independently labelled SHA-256 draws from the 10-bit primes, excluding equal primes and duplicate unordered pairs. The 41-bit and 46-bit controls reuse previously published products. Each search receives $N$ alone. Expected factors are used to check its output. [Cohort construction](../experiments/quotient_strip_localization.py) · [Larger control inputs](../benchmarks/modular-hyperbola.json)

Each cell gives the **complete scan / search to the first factor**. The first three columns count square roots of nonnegative discriminants. The last counts trial divisions when testing odd integers in the same balanced interval. These operations have different costs. [Square-root counts](../benchmarks/quotient-strip-farey.json) · [Direct trial counts](../benchmarks/quotient-strip-levels.json)

| Inputs | Modulo 8, either direction method | Single stride modulo 24 | Exact modulo 24 | Direct odd trial divisions |
|---|---:|---:|---:|---:|
| 99 ratio-selected | 1,733 / 1,260 | 1,493 / 1,079 | 1,070 / 776 | 52,049 / 33,216 |
| 64 holdouts | 398 / 301 | 350 / 270 | 262 / 210 | 6,901 / 4,252 |
| 41-bit control | 958 / 76 | 802 / 63 | 584 / 48 | 201,863 / 12,660 |
| 46-bit control | 2,881 / 2,020 | 2,464 / 1,722 | 1,720 / 1,189 | 985,115 / 644,576 |

On the complete 46-bit scan, independent continued fractions used **32,727 divisions** to select directions. The walk used **10,797 divisions** and **15,961 mediant comparisons**. To the first hit the corresponding counts were 23,071 divisions versus 8,226 divisions and 11,637 comparisons. The exact residue filter also checked 2,906 single-stride labels on the full scan and 2,017 to the first hit. These costs are separate from checking the surviving quadratics. [Full operation breakdown](../benchmarks/quotient-strip-farey.json)

In one arm64 macOS run on CPython 3.9.6, median CPU times in milliseconds were as follows. The four chord methods include their operation counters. Direct odd trial uses a plain loop. Each median uses five rotated runs after warmup, with result validation outside the clock. On the 41-bit input the plain loop reached the first factor fastest. On the 46-bit input, repeat runs put the exact residue filter and the single stride in either timing order. Their square-root counts reproduced exactly. [Timing procedure](../experiments/quotient_strip_farey.py)

| Input and stopping point | Independent fractions, mod 8 | Farey walk, mod 8 | Walk, single stride 24 | Walk, exact mod 24 | Direct odd trial |
|---|---:|---:|---:|---:|---:|
| 41-bit complete | 14.91 | 14.13 | 13.73 | 13.62 | 14.77 |
| 41-bit first factor | 0.96 | 1.07 | 1.04 | 1.04 | 0.92 |
| 46-bit complete | 45.61 | 42.49 | 41.48 | 40.87 | 72.59 |
| 46-bit first factor | 31.30 | 29.85 | 28.50 | 28.42 | 47.45 |

From the repository root, replay the checked operation counts with the command below. Add `--timings` to measure both larger controls on the local machine. The replay also checks the exact local image on all **4,608** residue triples, compares both modulo-24 searches with direct division on **1,664** small products, and includes two additional products with three balanced divisors each. [Reproduction harness and validation cases](../experiments/quotient_strip_farey.py)

```sh
python3 -B -m experiments.quotient_strip_farey
```
