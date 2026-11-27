# Three equations that cover every pair of primes

Given only the product of two different primes larger than three, we can choose three small equations. At least one has two solutions that reveal the factors. The open computational question is how to find those solutions cheaply. On a 40-bit test set our search recovered 22 of 32 products. At 48 bits it recovered five of 32. It found no solution on either 2,048-bit comparison within its budget. [Checked theorem](../PrimeFactors/ThreeTargetRepresentations.lean) · [Individual runs](../research/three-root-targets.json)

## How it works on 55

The rule picks the numbers 2, −3 and −6. The last one leads to two ways to write 55 as a square plus six times another square.

$$55=7^2+6\cdot1^2=1^2+6\cdot3^2.$$

Cross-multiply the coordinates and subtract. This gives $7\cdot3-1\cdot1=20$. The greatest common divisor of 20 and 55 is 5, and dividing 55 by 5 gives 11. For a product with hundreds of digits, this last calculation is still cheap once we have both pairs of coordinates. Discovering the pairs is where the work goes.

## What is guaranteed

Take the list $-1,2,-2,3,-3,6,-6$ in that order. Keep the first three entries whose Jacobi symbol at the public product $N$ is positive. The symbol is inexpensive to compute by successive divisions. The three selected entries have a product which is an ordinary integer square. At either hidden prime, their three quadratic signs therefore multiply to +1. At least one of the three signs must be positive. Since the public signs are all positive, the signs at the other hidden prime match. That entry $D$ has a square root modulo both primes, hence modulo their product. The finite selection proof also covers the case where all seven public signs are positive. [Lean selection theorem](../PrimeFactors/ThreeRootTargets.lean)

For such a $D$, changing the sign of a root at just one prime gives a second root. For each root $r$, the lattice of pairs satisfying $x\equiv ry\pmod N$ has a short vector. Lean proves that the associated coordinates are coprime and satisfy

$$x^2-Dy^2=mN,\qquad x^2+|D|y^2<3N,\qquad 1\le |m|\le2.$$

When $|D|\le3$, the stronger conclusion $|m|=1$ holds. If $(x_1,y_1)$ and $(x_2,y_2)$ represent the two roots, $\gcd(|x_1 y_2-x_2 y_1|,N)$ is a proper factor. Applying lattice reduction directly takes a root as input. Starting with $N$ alone still requires a search. [Lattice bound and factor recovery](../PrimeFactors/SmallDiscriminantLattice.lean) · [Combined theorem and multiplier bound](../PrimeFactors/ThreeTargetRepresentations.lean)

A second normalization chooses exactly one multiplier from the product for each target. This gives three actual equations in total. For positive targets the coordinate interval follows by choosing the shortest representative among equivalent solutions of the same equation. A complete block search on the two 2,048-bit comparisons still requires more than $2^{685}$ blocks on each. [Three equations and their intervals](../PrimeFactors/ThreeNormCurves.lean) · [Search costs](scanning-signed-norm-arcs.md)

D. H. and Emma Lehmer published the three-equation factoring principle in 1974. They chose equations using $N$ modulo 24 and gave a complete search over intervals of length proportional to $\sqrt N$. Seven of the eight eligible remainders give the same three values of $D$ as our signed rule. For remainder 1 their choices are $-2,-3,6$ and ours are $-1,2,-2$. The formalization here uses the public signs and a lattice bound. It requires no hypothesis about zeta zeros. [Lehmer and Lehmer, pp. 625–627](https://doi.org/10.2307/2005939)

## Could the targets be smaller?

The signed rule needs targets of absolute value at most six. Using positive targets only, the same sign argument applied to $2,3,5$ gives a ceiling of 30. Both ceilings are attained even on 2,048-bit products of two 1,024-bit primes. We constructed one where every integer nonsquare of absolute value less than six fails, and another where every positive integer nonsquare below 30 fails. For each, Lean checked the two prime certificates, exclusion of every smaller target, and an explicit root at the ceiling. The construction used the prime factors to certify sharpness. A separate finite theorem shows that two targets chosen from the seven sign masks can both fail for compatible local signs. [Checked inputs](../research/three-target-limits.json) · [Certificate generator](../experiments/three_target_limits.py) · [Sign patterns at full width](../PrimeFactors/PrimeResidueSignWheel.lean)

## Does searching three targets work better?

We froze 32 independently generated products per width and ran four rules on each. Each rule received at most 8,192 continued-fraction updates, with multipliers at most 320 and at most 256 updates per multiplier. The search only received the product. A rule could find two different roots of one target, or one root of each of three targets whose product is a square. Both routes can reveal a factor. The counter for successful roots includes runs which yielded no factor. [Search implementation and seed](../experiments/three_root_targets.py)

| Targets used | 40-bit products with a root | 40-bit products split | 48-bit products with a root | 48-bit products split |
|---|---:|---:|---:|---:|
| One positive target, previous rule | 16 | 14 | 10 | 5 |
| Three positive targets | 30 | 18 | 18 | 5 |
| First target from the signed list | 18 | 16 | 14 | 6 |
| Three signed targets | 30 | 22 | 21 | 5 |

For $585{,}669{,}273{,}599$, the signed rule found two roots of 6 after 3,250 updates. Their difference exposed the factor 1,006,853 and the other prime was 581,683. At 40 bits, the signed rule gained 12 products and lost four compared with the previous rule. At 48 bits it gained three and lost three. On the 48-bit batch, it performed 79,539 exact square tests compared with 41,567 for the previous rule. On each 2,048-bit input every rule used its full 8,192 updates and found zero roots. Across the four rules, Lean checked 38 distinct factorizations. [Per-input results, work counts and certificate digest](../research/three-root-targets.json)

The theorem guarantees solutions somewhere in a bounded region. The continued-fraction search visits only part of that region. For some numbers it can miss a valid equation for an entire period, even if we run it indefinitely at a fixed multiplier. [Explicit example and proof](when-a-soluble-norm-never-appears.md)

To replay the panel and its Lean certificate, run `python3 -m experiments.three_root_targets --output build/three-root-targets-replay.json`. CPU timings vary. Run `python3 -m experiments.three_target_limits` to regenerate and check the two 2,048-bit sharpness examples.
