# When a square excess predicts the prime sum

Given an odd semiprime $N$ and a candidate Fermat midpoint $m$ above $\sqrt N$, compute the positive difference $D=m^2-N$. Add the largest power of two dividing $D$ to $2m$. If there are at least four steps between the first Fermat midpoint and the true midpoint, this rule gives the correct prime sum at one of the centers one, two or four steps before the true midpoint. A scan that tests the rule at every center would reach one of these centers. Choosing it in advance from the product remains a separate problem. [Exact classification and four-step guarantee](../PrimeFactors/CeilingShiftDyadicDistances.lean)

## Which centers work?

Write $M=(p+q)/2$ for the true midpoint and $d=(q-p)/2$ for the half-gap. Let $v$ be the exponent of two in $d$. Any correct reading has $M-m=2^k$ for some nonnegative integer $k$, since the amount added to $2m$ must be $2(M-m)$. The table gives all successful distances for which $m^2>N$ and $m<M$. [Distance and classification theorems](../PrimeFactors/CeilingShiftDyadicDistances.lean)

| Half-gap | Successful distances $M-m$ |
| --- | --- |
| $d$ odd | 1 |
| $d$ divisible by 2 but not 4 | 2 |
| $2^v$ exactly divides $d$, with $v\ge 2$ | $2^k$ for $2\le k\le 2v-2$ |

For $m=M-2^k$, the identity $M^2-N=d^2$ gives

$$
D+2^{k+1}M=d^2+2^{2k}.
$$

Success requires $D$ to be an odd multiple of $2^{k+1}$. For $k\ge2$ and even $d$, $M$ is odd and $2^{2k}$ is divisible by $2^{k+2}$. Reducing the identity modulo $2^{k+2}$ shows that success is equivalent to $2^{k+2}\mid d^2$. An odd $d$ makes $D$ odd in this range. The two smaller values of $k$ follow by checking squares modulo eight. [Proof](../PrimeFactors/CeilingShiftDyadicDistances.lean)

## How rare are long jumps?

A correct reading at distance at least $2^{128}$ requires $2^{66}\mid(q-p)$. For a jump of at least $2^{512}$ the required divisor is $2^{258}$. For fixed $p$, the positive gap is less than $2^{1023}$ among the eligible 1,024-bit prime pairs. Counting the possible multiples of each divisor and applying the project's prime count gives the following unconditional bounds. Both grant every candidate center for every product. [Long-jump population proof](../PrimeFactors/CeilingShiftDyadicDistances.lean) · [Prime count used in the bound](../PrimeFactors/SquareRootPhasePopulation.lean)

| Distance of a correct reading | Fraction of eligible pairs admitting one |
| --- | --- |
| At least $2^{128}$ midpoints | Less than $2^{-50}$ |
| At least $2^{512}$ midpoints | Less than $2^{-242}$ |

The denominator counts each pair of distinct 1,024-bit primes with a 2,048-bit product once. These bounds measure how far this particular reading can jump. Evaluating the rule at a supplied center requires an integer square, a subtraction and the power of two dividing the result. A proposed sum $S$ can be checked by testing $S^2-4N$ for a square and verifying the resulting factors. The count gives no cost bound for locating a successful center. [Population and cost scope](../PrimeFactors/CeilingShiftDyadicDistances.lean)

## A successful jump of sixteen

For $532937=523\cdot1019$, the true midpoint is $771$ and the half-gap is $248=2^3\cdot31$. At $m=755$, the excess is $37088=32\cdot1159$. The reading gives $2\cdot755+32=1542$, the correct sum. At $m=739$, twice as far back, the excess is still positive but equals $13184=128\cdot103$. This time the reading gives $1606$. [Checked control](../PrimeFactors/CeilingShiftDyadicDistances.lean)
