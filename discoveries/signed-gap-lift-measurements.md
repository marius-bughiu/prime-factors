# Measuring the signed-gap lift

On the 49-bit holdout $N=502005281288939$, grouping the possible traces modulo 24 into at most two progressions per coordinate reduced the number of positions examined from 13,274 to 5,303 against a matched control. Both searches visited all 613 coordinates and recovered $17838631\cdot28141469$. The surviving search spaces on two 2,048-bit controls remained enormous even at four sampled coordinates per input. [Benchmark inputs and budgets](../benchmarks/offset-coordinate-gaps.json) · [Search implementation](../experiments/offset_coordinate_gaps.py)

## What the comparison measures

Assume $N=pq$ with $p,q$ coprime to 6. For a public guess of positive coprime coordinates $s,v$, write $k=sv$, $S=2\lfloor\sqrt N\rfloor k+j$, $H=s^2+Nv^2$. An actual factorization at these coordinates requires $S\equiv Hp\pmod{24}$. Set $g=\gcd(H,24)$, $f=24/g$, $L=\operatorname{lcm}(2,f)$. Eligible traces satisfy $S=gt$ with $\gcd(t,f)=1$. There are at most two progressions of such $t$ because only primes 2 and 3 can divide $f$. An affine representative for $p\pmod L$ then predicts one signed-gap residue modulo $2k^2L$ on each progression. This experiment uses the common residue. When $3\nmid f$, the additional exclusion of one in three residues could further reduce the work. [Trace theorem and exclusion](nonunit-offset-traces.md) · [Implementation and explicit eight-unit reference](../experiments/offset_gap_lift.py)

The matched control takes the same $j$ progressions, chord endpoints, coordinate budget and test budget as the lift. It uses the original modulus $4k^2$ on those progressions. Both modes test $\gcd(j,k)=1$ before checking candidate gaps. The two signs can cover overlapping positions, so the floor-sum count for each band gives lower and upper bounds. Exhaustive enumeration counts distinct positions exactly. The scanner charges roots used to construct the bounds separately from square checks at surviving positions. [Counting and endpoint code](../experiments/offset_coordinate_gaps.py)

## An exhaustive 49-bit comparison

The coordinate bounds contained 731,911 parity-compatible positions. The trace condition excluded 457,517 and retained 274,394. The compressed implementation used 613 small gcds for the trace image, 612 coordinate projector inverses and zero per-progression inverses. It produced 922 nonempty progressions, partitioned into at most 16 chord bands each. Times below are median process CPU seconds on the development machine, five alternating runs per mode for the compressed comparison and three for the explicit comparison. All four runs found the same single successful slot $(j,k)=(2921,2322)$. Lean checked both reported primes and their product.

| Trace grouping and gap modulus | Bands | Roots for bounds | Survivor bounds | Distinct positions examined | After gcd | Direct gap square checks | Fallback square roots | CPU seconds |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Compressed, original | 14,490 | 42,884 | 11,159–14,021 | 13,274 | 11,768 | 8,633 | 4,786 | 0.183 |
| Compressed, lifted | 14,490 | 42,884 | 4,269–5,794 | 5,303 | 4,863 | 4,694 | 1,182 | 0.144 |
| Individual trace residues, original | 42,437 | 120,890 | 10,769–12,765 | 12,120 | 10,786 | 7,763 | 4,507 | 0.329 |
| Individual trace residues, lifted | 42,437 | 120,890 | 4,014–5,195 | 4,782 | 4,409 | 4,135 | 1,074 | 0.301 |

The individual-residue implementation splits the original parity index into up to 12 classes per coordinate. It yields the same local condition at every $j$. Its larger number of chord bands changes the geometric bounds and lets fewer nonsquares through. Compression saved 78,006 bound roots while examining 521 additional positions in the lifted run. The finite regression tests compare the affine residues point by point, including every divisor $f$ of 24, short clipped windows and both trace parities. [Regression tests](../tests/test_offset_gap_lift.py)

Other choices of modulus on the same input illustrate the cost of obtaining a stronger residue. At cap 8, the basic rule selects the largest divisor $d\mid k$ with $d\le8$ using public coordinates. Its lifted run charges 1,960 per-class inverses in addition to the coordinate projector setup. Each cell below gives the matched original-modulus count followed by the lifted count. [Divisor and square-modulus proofs](lifting-a-signed-gap.md)

| Rule | Bands per full run | Positions examined | After gcd | Median CPU seconds |
| --- | ---: | ---: | ---: | ---: |
| Basic divisor lift, cap 8 | 31,646 | 28,230 → 8,688 | 24,307 → 8,283 | 0.403 → 0.297 |
| Odd-trace square rule modulo 8, cap 8 | 43,245 | 27,753 → 6,600 | 23,929 → 6,314 | 0.462 → 0.353 |
| Odd-trace square rule modulo 24, cap 1 | 19,524 | 30,524 → 18,101 | 24,768 → 14,256 | 0.340 → 0.265 |

## What four full-size coordinates establish

For each control the scanner chose four coordinates from $N$ alone, formed eight compressed progressions, and used 64 bands per progression. Both modes spent 1,540 roots on bounds and visited their budget of three distinct positions. Neither found a factor. Every one of the 512 bands still had untested positions. The table encloses the base-two logarithm of the number of distinct positions passing the corresponding chord filter, with endpoints rounded outwards. These counts apply before the gcd check and cover the four sampled coordinates only.

| 2,048-bit input | Original log₂ count | Lifted log₂ count | Positions after gcd, original → lifted | CPU seconds, original → lifted |
| --- | ---: | ---: | ---: | ---: |
| Fresh | [500.170, 501.171] | [498.176, 499.177] | 3 → 3 | 1.436 → 1.426 |
| Crossed | [500.705, 501.706] | [497.120, 498.121] | 2 → 3 | 1.405 → 1.415 |

Even the lifted upper bound lies below the original lower bound by a factor greater than 1.99 on fresh and 5.99 on crossed. Counting a range of this size with floor sums takes seconds here. Finding a factor requires identifying an actual square and a successful coordinate, and the sampled counts give no bound on that time.

## Reproducing the run

```sh
python3 -m experiments.offset_gap_lift --case 49 --cap 1 --trace-units --rounds 5
python3 -m experiments.offset_gap_lift --case fresh --cap 1 --trace-units --rounds 3
python3 -m experiments.offset_gap_lift --case crossed --cap 1 --trace-units --rounds 3
python3 -m experiments.offset_gap_lift --case 49 --cap 8 --rounds 3
python3 -m experiments.offset_gap_lift --case 49 --cap 8 --unit-square 8 --rounds 3
python3 -m experiments.offset_gap_lift --case 49 --cap 1 --unit-square 24 --rounds 3
python3 -m unittest tests.test_offset_gap_lift tests.test_offset_coordinate_gaps
```

The explicit reference can be selected for the same benchmark without changing its geometry or budgets. The standalone trace helper falls back to the ordinary divisor rule when $d>1$ or $3\mid N$. The cap-1 comparisons above always use its supported trace path.

```python
from functools import partial
from unittest.mock import patch
from experiments.offset_gap_lift import affine_classes, compare

with patch("experiments.offset_gap_lift.affine_classes",
           partial(affine_classes, explicit_trace=True)):
    reference = compare("49", 1, rounds=3, trace_units=True)
    print(reference)
```
