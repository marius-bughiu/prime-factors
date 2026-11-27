# Where the multiplier search first succeeds

On each of our two 2,048-bit examples, exactly **two** multiples have a square in the complete search interval. On both examples the first one is above $2^{681}$. The public search that starts at multiplier one must visit at least $2^{501}$ different eligible multiples before it reaches either answer. This holds even if it can check an entire interval in one operation. [Numerical records](../research/rectangular-winning-rows.json) · [Lean certificate generator](../experiments/rectangular_winner_receipt.py)

We used the published factors to *locate* the two answers after the search. This explains the earlier misses on these particular inputs. It gives no way to predict their positions from the product alone. On 24 smaller products the same calculation predicted the first hit of the actual search in every case. [How the public search performed](fewer-multiples-to-test.md) · [Diagnostic and seed data](../experiments/rectangular_winning_rows.py)

| Constructed input | First winning multiplier as a share of the full multiplier range | Second winning multiplier |
| --- | ---: | ---: |
| Fresh 2,048-bit product | 42.93% | 84.87% |
| Crossed 2,048-bit product | 67.17% | 69.75% |

The percentages give the numerical positions within the full range from 1 to $K$. The search skips many values in that range, and time per visit varies. A different ordering would change the time to a first hit. [Original budgets](../benchmarks/rectangular-root-windows.json)

## Why two solutions suffice for a complete count

For positive $k$ we seek $y^2=x^2+kN$ with $x\le H$ and $0<y\le B$. Each solution splits $N$ between $y-x$ and $y+x$. There are only two ways to allocate the two primes. For two solutions with the same allocation, $N$ divides $x_1 y_2-x_2 y_1$. Its absolute value is at most $HB<N$, so it is zero. When both fractions are reduced, equal fractions give identical coordinates. Consequently there are at most two distinct successful multipliers with coprime coordinates. [Proof of the two-solution bound](../PrimeFactors/WeightWindowOverlap.lean)

Other solutions can arise by multiplying both coordinates by an integer $g$. Lean checks that **every** such solution uses $k=g^2 k_0$ for a primitive solution at $k_0$. On both full-size examples the two primitive indices already exceed $K/4$, so doubling even once puts the resulting index beyond $K$. The certificates verify the original prime factorizations, the integer dimensions of the search, both square identities, and the universal exclusion of every other index. [Normalization and exclusion theorem](../PrimeFactors/RectangularRowNormalization.lean)

To find the two candidate fractions retrospectively, use the known primes to construct a residue $r$ equal to $+1$ modulo one and $-1$ modulo the other. Compute the nearest fractions on each side of $r/N$ with denominators at most $B$. For a neighbor $m/y$, its numerator in the search rectangle is $|ry-mN|$. Test whether that is at most $H$. The two fractions have determinant one, and their denominators sum to more than $B$. These facts and $HB<N$ imply that every reduced point in the rectangle occurs at one of these neighbors. This calculation took 795 quotient steps on the fresh example and 754 on the crossed example. Eighteen of the smaller examples had only one retained neighbor and the other six had two. [Farey proof](../PrimeFactors/RectangularFareyOracle.lean) · [Direct enumeration checks](../tests/test_rectangular_winning_rows.py)

## How many distinct multiples come before the first hit?

The earlier proof counted a single sequence of more than $10^{102}$ surviving multipliers. Here we construct at least $2^{501}$ distinct ones **below or equal to $2^{680}$**, each passing the actual parity, coprimality, ratio and product tests, even when the positive ratio allowance is as small as the implementation permits. Both measured first hits lie beyond this entire family. [Lean construction and count](../PrimeFactors/RectangularDistinctProducts.lean)

The idea is to pack products just below successive squares. Write $k=a(a+2j)=(a+j)^2-j^2$. Choose $a$ odd and coprime to $j$, and large enough that $k$ lies between $(a+j-1)^2$ and $(a+j)^2$. Then $k$ uniquely specifies the upper square and its distance $j^2$ below it. This recovers both weights and avoids counting the same multiplier twice. To obtain many weights, let $W=2^{168}$. Take each coprime $1\le x\le j\le W$, lift $x$ to an odd residue modulo $j$, and add $2jt$ for each $W\le t<2W$. The existing elementary coprime-pair estimate supplies at least $W^2/8$ pairs, and each gives $W$ different products. [Coprime-pair estimate](../PrimeFactors/FareyWork.lean)

For every input of the stated balanced size, a uniformly chosen eligible multiplier has probability at most $2^{-157}$ of hitting a square, even if the whole interval is checked. The proof counts at most two primitive indices and at most $2^{343}$ possible scales per index, against the $2^{501}$ eligible values. The union bound puts a trillion such trials at probability at most $2^{-117}$ when each draw has a uniform marginal distribution. A choice based on further information about the product would need its own analysis. [Finite counting inequality](../PrimeFactors/RectangularSampling.lean)

Reproduce the small comparisons with `python3 -m experiments.rectangular_winning_rows`. Run `python3 -m experiments.rectangular_winner_receipt` to regenerate and kernel-check the two full-size classification proofs using the repository's existing prime certificates.
