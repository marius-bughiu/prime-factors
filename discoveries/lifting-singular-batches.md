# One more remainder digit can be forced by the product

On **502,005,281,288,939**, the product alone fixed an extra remainder digit in four of the local directions. Using those digits reduced a complete search from **4,800 to 3,040 lattice reductions** and from **91,261 to 46,350 integer square-root tests**. The two primes were **17,838,631 and 28,141,469**. On the two 2,048-bit controls the resulting complete schedules still exceed $2^{888}$ groups each. The first eight groups produced no factor on either input. [Arithmetic receipts](../benchmarks/offset-row-geometry.json) · [Search implementation](../experiments/offset_row_geometry.py)

## When a digit is forced

Let $T=\lfloor\sqrt N\rfloor$ and $h=N-T^2>0$. The balanced search looks for coprime positive integers $(j,k)$ for which $D=(j+2Tk)^2-4Nk^2$ is a square. Fix an odd prime $p\nmid N$ from the public list. A finite direction $r$ means $j\equiv rk\pmod p$. Primitivity makes $k$ invertible modulo $p$. Put $F(r)=(r+2T)^2-4N$. When $F(r)\equiv0\pmod p$, any integer square $D$ in this direction is divisible by $p^2$. The derivative $2(r+2T)$ is a unit modulo $p$ since $p\nmid 2N$. The next digit of the slope is therefore given by the public formula

$$
i\equiv-\frac{F(r)}p\,[2(r+2T)]^{-1}\pmod p,\qquad R=r+pi.
$$

Indeed $F(R)\equiv0\pmod{p^2}$. Subtracting its multiple $k^2F(R)$ from $D$ gives $(j-Rk)\big(j+(R+4T)k\big)$. The second factor reduces to $2(r+2T)k$, a unit, so $j\equiv Rk\pmod{p^2}$. The same branch now has a lattice of index $p$ inside its old lattice, with one basis reduction still sufficient to search it. Lean proves that a lift can be selected before the unknown position is supplied, and that all primitive hits use it. [Projective lift proof](../PrimeFactors/OffsetRowGeometry.lean) · [Earlier proof of the local digit formula](../PrimeFactors/PrimePower.lean)

This local arithmetic comes from the coordinate sums of the modular hyperbola $xy=N$. Bower, Evans, Luo and Miller counted them at prime powers. At a split odd prime there are two first digits with zero discriminant. Each has one surviving child modulo $p^2$ and each other allowed projective direction has $p$ children. Using one lattice at modulus $p$ for each regular direction and one at $p^2$ for each singular direction represents that entire second-digit filter with the original number of branches. The existing fixed prime-power scanner explicitly counts or enumerates the children of a uniform modulus. [Bower, Evans, Luo and Miller](https://arxiv.org/abs/1212.2930) · [Local counts](prime-power-counts.md) · [Earlier odd prime-power and grouped searches](grouping-remainder-searches.md)

## Spending the extra digit

Start with the same odd primes as the ordinary grouped search and denote their retained product by $M_0$. The first version uses every forced digit and visits the same number of groups. A second version holds the four smallest retained primes in reserve. If earlier digits already made the index at least $M_0$, the current group can be searched immediately. Unused primes still check each candidate discriminant. A nonzero square residue modulo $p$ passes, and a zero residue requires divisibility by $p^2$.

The group count is exact. With reserve set $S$ and additional index requirement $b$, stop at cost 1 when $b=1$. Opening $p\in S$ with $g_p$ original directions, of which $s_p$ are singular, costs

$$
(g_p-s_p) C(S\setminus\{p\},\lceil b/p\rceil)+
s_p C(S\setminus\{p\},\lceil b/p^2\rceil).
$$

The program chooses the minimum over the available $p$. Its count of initial requirements uses a histogram. A singular prefix digit gives an extra factor $p$, updating the requirement from $b$ to $\lceil b/p\rceil$. Regular digits retain $b$. Each split in the tree partitions primitive positions by their unique projective directions. Every true square follows one leaf, and every leaf has index at least $M_0$. Distinct lattice points within a leaf still require work. The implementation streams the leaves and stores local masks, histogram counts and the small reserve table. It reports unfinished groups under both a reduction cap and a separate row-plus-position cap. [Lattice coordinates and row bounds](../PrimeFactors/OffsetLatticeBatches.lean) · [Scanner and counting algorithm](../experiments/offset_row_geometry.py)

## Measured searches

All three 49-bit runs used the same distinct-prime selection and deferred its two largest primes before grouping. Elapsed times are local search-only medians from five runs in rotated order, including setup. All three exhausted their groups and returned the same single winning position $(2921,2322)$. Lean checked the product and primality of its factors separately.

| 49-bit search | Lattice reductions | Gauss iterations | Rows | Positions visited | Square roots | Seconds |
|---|---:|---:|---:|---:|---:|---:|
| Ordinary | 4,800 | 30,504 | 96,203 | 1,070,273 | 91,261 | 0.596 |
| Forced digits | 4,800 | 34,437 | 59,828 | 537,732 | 46,534 | 0.354 |
| Forced digits and four reserves | 3,040 | 19,637 | 55,361 | 563,759 | 46,350 | 0.331 |

For this input, setup examined 48 unit images and tested 26 finite directions for singularity. It computed four Newton digits. The reserve planner evaluated 52 choices over 30 states. Regrouping slightly increased position visits relative to the fixed set of lifted groups while saving 1,760 reductions. On 134,683,853 the retained directions trigger no lifts. All 168 reductions and 693 positions remain, while checking the second digit at the deferred prime cuts the square roots from 172 to 142. [Checked split fixtures](../benchmarks/offset-row-geometry.json)

Across the eight earlier holdout products, all three modes exhausted the search and found the same eight factorizations and nine proper hits. The program took five timing samples per mode and checked the eight factor pairs in Lean. The lift-only runs tested 86 finite residues and computed 14 Newton digits across all inputs. The reserve planner additionally evaluated 100 choices. [Frozen product list](../research/quartic-lane-holdout.json) · [Reproduction code](../experiments/offset_row_geometry.py)

| Eight products combined | Lattice reductions | Gauss iterations | Rows | Positions visited | Square roots | Seconds |
|---|---:|---:|---:|---:|---:|---:|
| Ordinary | 571 | 2,354 | 7,573 | 57,737 | 6,562 | 0.040 |
| Forced digits | 571 | 2,634 | 5,683 | 42,824 | 4,829 | 0.033 |
| Forced digits and four reserves | 471 | 1,996 | 5,512 | 43,459 | 4,821 | 0.032 |

At 2,048 bits, the ordinary comparison deferred one odd prime. Both versions use that same starting wheel. On the fresh input the adaptive count is 30.44% of the ordinary count, about $2^{888.32}$ groups. On the crossed input it is 18.77%, about $2^{888.10}$. Setup computed 116 and 144 Newton digits respectively, with 3,245 and 6,645 histogram-state updates. The eight-group caps visited 1 and 805 positions respectively, yielding 0 and 104 square roots. The search order changes when primes are reserved, and these first groups do not estimate the work per group for the full schedule or the time to a first factor. [Full integers, budgets and unresolved cofactors](../benchmarks/offset-row-geometry.json)

## Why a straight strip does little on these rows

One alternative is to bracket the square root of $D$ along a lattice row by two parallel affine functions, then look for the integer heights in a thin strip. Let $M$ be the lattice determinant and $u$ its row index. At three consecutive positions on row $u$ let $l,z,r$ be the nonnegative real square roots when they exist. The row quadratic has Gram determinant $-4NM^2$. Expansion gives

$$
(2z-l-r)(2z+l+r)\big(4z^2-(l-r)^2\big)=64N(Mu)^2.
$$

If the three values lie in an affine strip of vertical width $E$ and all are at most $U$, the first absolute factor is at most $2E$, the second at most $4U$, and the third at most $4U^2$. Thus $2N(Mu)^2\le E U^3$. On the sharp schedule, $hD=Nj^2-(2hk-Tj)^2$ and $3j^2\le4h$, so $U=2\sqrt N$ suffices. Even when $|u|=1$, any such strip needs width at least $M^2/(4\sqrt N)$. Substituting the minimum determinants in both full-size receipts gives width above $2^{1005}$. This obstructs ruling out three consecutive positions by fitting the unrestricted roots inside a strip of width one. The argument concerns a single affine approximation on nonaxis rows. Individual residue branches may still have further arithmetic constraints. [Kernel-checked three-position identity and width bound](../PrimeFactors/OffsetRowGeometry.lean) · [Control determinants](../benchmarks/offset-row-geometry.json)

Both commands below run the product-only search and check the recovered primes.

```sh
python3 -m experiments.offset_row_geometry 502005281288939 --drop 2 --reserve-size 4 --max-batches 3040 --max-events 2000000 --exhaust --verify
python3 -m experiments.offset_row_geometry --holdout --verify
```
