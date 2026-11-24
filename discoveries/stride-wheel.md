# Skipping midpoint indices inside a lifted root class

For an odd product $N=pq$ with $p<q\le2p$ and $\gcd(N,30)=1$, the public digits of $N$ determine which indices to skip inside a Fermat root class. At the exact power of five dividing the half-gap, at most **16 of every 120 indices** need an integer square test. In a bounded comparison the method used 116,447 such tests to recover the same 46,850 pairs for which an ordinary modulus-120 wheel used 183,510. Finding and rotating the root classes also costs arithmetic. [Lean proofs](../PrimeFactors/StrideWheel.lean) · [Experiment](../experiments/stride_wheel.py)

## Which digit should be skipped?

Let $H=(p+q)/2$, $D=(q-p)/2$ and $r=\lceil\sqrt N\rceil$. For $m=5^v$, lift the roots of $N$ modulo $m^2$. For each root, let $h$ be its least representative at least $r$. Then $A=(h^2-N)/m^2$ is an integer and the divided discriminant at index $j$ is

$$
Q(j)=\frac{(h+m^2j)^2-N}{m^2}=A+2hj+m^2j^2.
$$

At the true midpoint this equals $(D/m)^2$. Assign a pair to the unique level $m=5^{v_5(D)}$. At that level $Q(j)$ must be a **nonzero** square modulo 5. For $v\ge1$, let $z\bmod5$ be the unique digit such that $(h+m^2z)^2\equiv N\pmod{5m^2}$. This digit is available while lifting to the next level. Now $Q(z)=0\bmod5$ and $Q(j)=2h(j-z)\bmod5$. With $i=(2h)^{-1}\bmod5$ the complete list of permitted indices is

$$ j\equiv z+i\quad\text{or}\quad j\equiv z-i\pmod5. $$

The two residues are distinct. This test sees a digit that $H^2-N\bmod5$ cannot see once the search is inside a root class modulo $m^2$. A nonzero residue square at an odd prime lifts to a square at every positive power. Consequently, for a given integer $j$ that passes, testing $Q(j)$ at higher powers of five saves **zero** additional exact-valuation square tests. At $v=0$ one directly tests $H^2-N\in\{1,4\}\bmod5$. The allowed $H$ digits are $0$ when $N=1,4\bmod5$, $\pm1$ when $N=2\bmod5$, and $\pm2$ when $N=3\bmod5$. [Square lifting](../PrimeFactors/PrimePower.lean)

## Rotating one short table

For a modulus coprime to $m$, dividing by $m^2$ preserves square residuosity. Use $24$ for this external test. Since $m^2\equiv1\bmod24$, the candidate midpoint is $h+j\bmod24$. Its allowed residues are those $t$ for which $t^2-N$ belongs to $\{0,1,4,9,12,16\}\bmod24$. For $v\ge1$ take $b=h\bmod24$ and

$$\delta=b+24((b+z)\bmod5).$$

Then $t=j+\delta$ has the correct midpoint phase modulo 24 and satisfies $t=j-z\bmod5$. Thus a single sorted table indexed by $N\bmod24$ and the five-pattern $\{\pm i\}$ gives all permitted $j$ by rotation. At $v=0$ rotate by $h$ and use the initial five-pattern above.

The number of permitted offsets per 120 is the product of three counts. Modulo 8 it is four when $N=1\bmod4$ and two otherwise. Modulo 3 it is two when $N=1\bmod3$ and one otherwise. Modulo 5 it is two for a $\pm i$ pattern and one for $\{0\}$. Thus positive levels retain 4, 8 or 16 offsets per 120. All three initial patterns together need just 180 offset entries across the eight possible $N\bmod24$ values.

For example $N=27130781$, $r=5209$, $m=5$, and one class begins at $h=5216$. Here $z=0$, $i=3\bmod5$ and $\delta=80$. The next table entry is 87. The first admissible index is therefore $j=7$. It gives $5391^2-N=1390^2$. Lean verifies both prime factors $4001$ and $6781$. [Checked example](../PrimeFactors/StrideWheel.lean)

## Coverage at a fixed budget

If the old search finds $H$ in the first $B$ raw indices at some divisor $m_0$ of $D$, it still appears in the first $B$ permitted indices at its exact level $m$. Indeed $m_0\mid m$, so the new root class is a subset of the old progression. Restricting that subset to eligible indices keeps $H$ and can only reduce its rank. The same argument applies if the old search already uses the external wheel. If it uses the inclusive divided-discriminant wheel at a strictly lower level, every member of the higher root class has divided discriminant zero modulo five at that lower level and passes there. This proves that the exact-valuation schedule retains all those earlier hits when all possible gap valuations are covered. If computation stops at an exponent chosen just as a budget, assign every higher valuation to its terminal level. At that last level also admit $j=z\bmod5$, the zero quotient digit. The terminal filter then has at most 24 offsets per 120. The same nesting argument preserves coverage. The implementation uses this fallback on the 2048-bit fixtures.

A per-root square budget $B$ suffices for all permitted positions in the first $120\lfloor B/16\rfloor$ raw indices. Conversely each period contains at least one allowed index, so every tested index is below $120B$. This fixed wheel gives a constant-factor extension to the covered interval. The asymptotic exponent for a fixed set of smooth gap divisors remains the one in the frequency analysis. Fermat sieving and modular-hyperbola sumsets have an established literature. The specific result here selects and counts the indices *inside* a stride using its already lifted digit. [Gap-search frequency](gap-search-frequency.md) · [Hittmeir, Fermat sieve](https://doi.org/10.1016/j.jnt.2023.02.010) · [Local prime-power sumsets](prime-power-counts.md)

## Bounded comparison

The experiment searches every one of the 104,196 unordered distinct prime pairs in $[4000,8000]$, with $B=8$ and powers of five up to $4000/2$. All schedules share the same Hensel root generator and public midpoint bound $H\le\lfloor\sqrt{9N/8}\rfloor$, which follows from $q\le2p$. The latter removes impossible high branches. The ordinary 120-wheel tests $H^2-N$ for square residuosity. The inclusive wheel also tests the divided discriminant, accepting $0,1,4\bmod5$ at every level. The exact wheel accepts $1,4$ and assigns hits to their exact valuation.

| Schedule | Hits, first 8 raw indices | Square tests | Hits, first 8 permitted indices | Square tests | Hensel digits, permitted scan |
| --- | ---: | ---: | ---: | ---: | ---: |
| Raw stride | 46,850 | 1,162,439 | 46,850 | 1,162,439 | 112,077 |
| External 24 | 46,850 | 244,405 | 74,128 | 600,618 | 57,479 |
| Ordinary 120 | 46,850 | 183,510 | 88,272 | 473,499 | 39,429 |
| Inclusive divided discriminant | 46,850 | 151,128 | 88,272 | 448,595 | 46,362 |
| Exact valuation | 46,850 | 116,447 | 93,750 | 497,116 | 70,570 |

At the common raw window, the exact wheel pays 155,576 Hensel digit steps, 107,906 center extractions, 212,102 phase lookups and 281,699 offset reads. Each digit step includes an integer square, an exact integer division by the old precision, and a multiply and reduction for the new digit. Each center extraction uses a modular remainder and a division by the stride. At the common square cap, the exact wheel pays 50,579 center extractions, 154,775 phase lookups and 528,089 offset reads. Its 10,446 unresolved products consume 88,443 square tests. Scans stop on a verified split. Two initial integer square roots per input set the public endpoints.

Fixed setup for all five comparisons takes 24 small squares, 192 external residue checks, 4,800 combined residue checks including the two extra inclusive patterns, and 4,992 phase-table entries. The setup ran in under one millisecond on the test machine. This cost can be shared across products. In one CPython 3.9.6 arm64 run, the ordinary 120-wheel at $B=8$ took 0.306 seconds and the exact wheel took 0.352 seconds, summing time inside the individual searches. Increasing the ordinary budget to 12 recovered **94,654** pairs in 0.310 seconds, compared with **93,750** for the exact wheel at eight. Square tests are cheap at this width. The coverage and operation counts establish the saving under a fixed index or square budget. At this width, giving the ordinary wheel more indices can therefore recover the additional pairs within the time spent by the exact wheel.

On the repository's 2048-bit fixtures the cost of a full square test changes the comparison. With the **same 128 raw indices per root**, the ordinary 120-wheel needed 18,546 full square tests on the checked structured product, against 7,468 for the exact wheel. Three-run medians were 55.1 ms and 23.7 ms. The unresolved 2048-bit control needed 4,658 and 1,863 square tests, with medians of 15.5 ms and 8.3 ms. Both algorithms recovered the known factor on the structured input and exhausted the budget on the control. At the much smaller budget of one *permitted* position per root, the positive case needed 439 and 438 tests, respectively, and the extra scheduling work made the exact wheel slower. These are two fixed products, including one selected for its gap structure. [Decimal fixtures](../benchmarks/gap-stride.json)

```sh
python3 experiments/stride_wheel.py --gap-fixtures --budget 128 --cap indices
python3 experiments/stride_wheel.py 4000 --budget 8 --cap indices
python3 experiments/stride_wheel.py 4000 --budget 8 --cap squares --verify
python3 experiments/stride_wheel.py 4000 --budget 12 --cap squares
```

The independent check computes the true midpoint's rank by enumerating earlier indices only after discovery. Lean proves the quotient identity, the relation to the next root lift, the two exact index digits, the higher-power limit, the phase rotation, the complete period counts and the example. It also verifies rank monotonicity for nested root classes and the zero residue at a coarser level. The coverage comparison applies these lemmas across the valuation levels.
