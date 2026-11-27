# What an empty curve tells us about both factors

An exhaustive search of one of our three equations can reveal a bit about each prime even when the equation has no solution. On the fresh 2,048-bit product, the cheapest way to obtain that negative answer with our current arc scanner would cost more than $2^{683}$ blocks. A search stopped at 64 blocks still leaves the answer open. [Complete curve and sign proofs](../PrimeFactors/CompleteCurveSigns.lean) · [Recorded search budgets](scanning-signed-norm-arcs.md)

## An example with 77

The product 77 selects targets $-1,6,-6$. For $-1$ the equation is $x^2+y^2=77$. Checking the squares from 0 through 64 proves that there is no solution. For $-6$, the pair $(10,3)$ gives $10^2+6\cdot3^2=154=2\cdot77$, and 3 is coprime to 77. These two observations determine the residues of the factors. One factor must be 7 modulo 24, the other 11 modulo 24. Trying 7 finds $77=7\times11$. Lean verifies the empty curve, the point, the residue sets and both primes. [Worked example](../PrimeFactors/CompleteCurveSigns.lean)

## How the information is obtained

Assume the input is the product of two distinct primes greater than three. Each chosen target $D$ has Jacobi symbol $+1$ at the product. The two primes therefore agree on whether $D$ is a square at each of them. Every modular square has a representative on the bounded curve with an invertible denominator. Finding one point with an invertible denominator proves that both primes regard $D$ as a square. Checking the entire bounded curve without finding one proves that both regard it as a nonsquare. A denominator with a proper gcd already yields a factor. [Bounded representatives](../PrimeFactors/ThreeNormCurves.lean) · [Equivalence and residue tables](../PrimeFactors/CompleteCurveSigns.lean)

Every prime greater than three belongs to one of eight residue classes modulo 24. One observed sign leaves four classes. Two different targets, each with a known sign, leave two classes. When $N\not\equiv1\pmod{24}$, those two classes give the actual unordered residues of the factors. A trial interval known to contain **both** factors needs only one representative of each possible pair. The number of progressions to search is four initially, two after one answer and one after two answers. An interval restricted to the smaller factor must keep both orientations. When $N\equiv1\pmod{24}$ the two primes have the same residue, and two answers leave two choices for that common residue. [Residue counts and orientation proof](../PrimeFactors/CompleteCurveSigns.lean)

On the fresh product, which is 7 modulo 24, the factor sum could be 8 or 16 modulo 24. A complete miss on the $-3$ curve would force the sum to be 16 modulo 24. One witnessed point would force 8. The recorded prefix yielded neither answer. [Factor-sum projection](../PrimeFactors/CompleteCurveSigns.lean)

A full miss on one target also proves that exactly one of the other two curves has a solution. A single witnessed point on either identifies which curve to pursue. A second full miss establishes existence on the third curve, and finding its points still takes work. Conversely, given roots on two curves, the product relation constructs a root on the third, but inserting this derived root in the three-root calculation gives exactly 1. An independently found root can give a different answer. [Remaining-curve and derived-root theorems](../PrimeFactors/CompleteCurveSigns.lean)

## What it costs on our full-size comparisons

These are base-two logarithms of the full unit-reduced chart block counts, rounded to three decimals. The counts use the public product, the existing chart endpoints and the existing block widths. They exclude setup, per-block arithmetic and any later trial divisions. Both previous 64-block runs remain incomplete. [Chart implementation](../experiments/signed_norm_arcs.py) · [Inputs and full-menu totals](../research/unit-reduced-signed-arcs.json)

| Product | $N\bmod 24$ | First target and cost | Second target and cost | Third target and cost | Cheapest two complete scans, combined |
| --- | ---: | --- | --- | --- | ---: |
| Fresh | 7 | $2$, 683.378 | $-3$, 683.780 | $-6$, 683.614 | 684.501 |
| Crossed | 1 | $-1$, 683.892 | $2$, 683.225 | $-2$, 683.725 | 684.496 |

Even if the observations were supplied for free, a single residue class modulo 24 occupies roughly $2^{1023}/24$ positions across the full 1,024-bit factor interval. The open problem is to obtain substantially more information at much lower cost. [Complete signed-curve comparison](scanning-signed-norm-arcs.md)
