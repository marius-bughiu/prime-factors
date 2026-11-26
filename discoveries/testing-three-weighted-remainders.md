# Can three failed square tests reveal the factors?

Yes on some inputs. On **2,100,271**, none of sixteen single tests or their 120 pairs found a factor. Three of the remainders together gave **1,283 × 1,637**. A single further test at weight one gave the same answer. At 2,048 bits, Lean proves that fewer than one in $2^{475}$ eligible prime pairs can give this three-nonsquare pattern anywhere in the sixteen tests. [Checked example](../benchmarks/weighted-square-triples.json) · [Population theorem](../PrimeFactors/WeightedTripleLabels.lean)

## Where the answer comes from

Given only $N$, take weights $r=1,\ldots,8$. At each weight take the first two integers $A\ge2\sqrt{rN}$ that are congruent to $r+N$ modulo $\gcd(24,2(r+N))$. Each remainder $D=A^2-4rN$ has the same residue as $A^2$ modulo $N$. If $D_1D_2D_3=z^2$, the products $A_1A_2A_3$ and $z$ have the same square modulo $N$. A gcd with their sum or difference can reveal a factor. Collecting square congruences is classical. The question here concerns this small, product-dependent selection of remainders. [Quadratic sieve, Carl Pomerance](https://math.dartmouth.edu/~carlp/PDF/paper52.pdf)

| Weight | Rank, starting at zero | Label | Remainder on 2,100,271 |
|---:|---:|---:|---:|
| 3 | 1 | 5,026 | 57,424 |
| 4 | 0 | 5,797 | 873 |
| 7 | 0 | 7,670 | 21,312 |

The three remainders multiply to $1{,}033{,}632^2$. The labels multiply to 223,470,987,740. Subtract the root and take a gcd with the input to obtain 1,637. Adding the root gives 1,283. This is the only square product among the 65,535 nonempty subsets of the sixteen remainders. Weight one at rank two gives $2{,}920^2-4N=354^2$, so an ordinary test reaches the answer as well. [Reproducible search](../experiments/weighted_square_triples.py) · [Checked work and expected factors](../benchmarks/weighted-square-triples.json)

## Measuring the extra work

Each run checked all 16 singles and 120 pairs, then compared all 560 triples with a further 70 single tests per weight. Each square triggered gcds with both signs. The additional counts below exclude inputs already split by the initial singles or pairs. A genuine triple uses three individually nonsquare remainders.

| Input selection | Products | Initial singles or pairs | Additional genuine triples | Additional ordinary tests found | Triples missed by ordinary comparison |
|---|---:|---:|---:|---:|---:|
| All eligible 11-bit prime pairs | 5,530 | 4,177 | 7 | 1,353 | 0 |
| All eligible 12-bit prime pairs | 19,546 | 10,790 | 14 | 8,756 | 0 |
| Existing seeded 16-bit holdout | 8,192 | 1,219 | 0 | 5,166 | 0 |

All eight 80-bit examples and both 2,048-bit controls exhausted every arm. On the large controls the biggest triple square tests used 3,092 and 3,093 bits. The comparison single tests used at most 1,038 and 1,037 bits. On each large control every one of the sixteen remainders had a nonsquare cofactor coprime to all other rows. That rules out **every** nonempty square subset of these sixteen rows on both inputs. The experiment archives each arm's costs and compares census splits with independent prime-sieve labels. Six highlighted factorizations were separately checked by Lean. [Measurements](../research/weighted-square-triples.json) · [Private-cofactor argument](pooled-relations.md)

## Why the three-test pattern is rare

Fix three weights $r_i$ and three labels $A_i$. Put $C_{ij}=|r_jA_i^2-r_iA_j^2|$. This public integer also equals $|r_jD_i-r_iD_j|$. Consequently any common prime divisor of the two remainders divides $C_{ij}$. If $C_{12}=0$ and all three positive remainders multiply to a square, then $D_3$ must already be a square. Indeed, $A_2^2D_1=A_1^2D_2$ makes $D_1D_2$ a rational square, and an integer that is a rational square is an integer square. Thus a genuine triple has three nonzero determinants. [Lean reduction](../PrimeFactors/WeightedTripleReduction.lean)

If $D_1D_2D_3=z^2$, then $D_1D_2=m u^2$ and $D_3=m v^2$ for the same squarefree integer $m$. Every prime of $m$ divides $D_3$ and at least one of $D_1,D_2$. Thus $m$ divides $\operatorname{lcm}(C_{13},C_{23})$. This conclusion holds without factoring $N$ or assuming that the remainders act independently. It also holds across any partition of a square product, using the lcm of the determinants between its two parts. [Support theorem](../PrimeFactors/WeightedTripleSupport.lean)

For each possible $m$, write $r_1r_2m=t f^2$ with $t$ squarefree. Then $x=r_2D_1+r_1D_2$ satisfies

$$
x^2-t(2fu)^2=C_{12}^2,\qquad
x+8r_1r_2N=r_2A_1^2+r_1A_2^2.
$$

The second equality makes each $x$ identify at most one product. For $x<2^H$ the first equality gives at most $2H\tau(C_{12}^2)$ points, where $\tau$ counts positive divisors. Counting $m$ by the divisors of $C_{13}C_{23}$ gives an upper bound on the number of possible inputs for each triple of labels. [Point count](../PrimeFactors/WeightedMultiplierPoints.lean) · [Count for a fixed triple](../PrimeFactors/WeightedTripleFiber.lean)

At target size each determinant is below $2^{1037}$ and $H=2048$ suffices. For the two integers whose divisors are counted, the divisor count is below $2^{242}$. The proof counts the possible triples of labels around the same square root and allows all 512 ordered choices of three weights, including repetitions. The resulting bound is on the actual integer tests before the gcd step. The population chooses distinct 1,024-bit primes uniformly, conditioned on a 2,048-bit product. No hypothesis about zeta zeros enters this calculation. [Finite count](../PrimeFactors/WeightedTriplePopulation.lean) · [Bridge to the executable labels](../PrimeFactors/WeightedTripleLabels.lean)

## What extends to more rows

There is also an asymptotic deduction for every fixed number of pairwise nonproportional rows. Keep the allowed weights, the number of labels per weight, and the number of rows fixed as the prime size $X$ grows. Each label is $2\sqrt{rN}+O(1)$, so across inputs in $[X^2,4X^2]$ there are $O(X)$ choices for the first label and $O(1)$ choices for each of the others once the first is fixed. All the determinants are $O(X)$. For a collection of at least three rows, apply the support theorem to its first two rows versus all remaining rows. The product of the crossing determinants is a positive integer of size $X^{O(1)}$. Its divisor count and that of $C_{12}^2$ are $X^{o(1)}$. The preceding point count with $H=O(\log X)$ therefore gives at most $X^{1+o(1)}$ possible products in total. For two rows the same argument uses $m=1$. [Divisor bound, Terence Tao](https://terrytao.wordpress.com/2008/09/23/the-divisor-bound/) · [Arbitrary finite partition in Lean](../PrimeFactors/WeightedTripleSupport.lean)

The eligible prime-pair count grows on the order of $X^2/(\log X)^2$, by the prime number theorem. Dividing gives an upper fraction $X^{-1+o(1)}$ for such nonsingular fixed-size collections with at least two rows. This last paragraph and the asymptotic count above are written deductions. The explicit $2^{-475}$ bound for three rows is kernel-checked. Allowing the tested set to grow with the input changes this counting argument. [Prime number theorem project](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd)
