# What if we could try every combination?

Take sixteen numbers computed from the public product. There are 65,535 ways to select at least one of them. **Even if every selection were free to test, fewer than one in $2^{277}$ eligible 2,048-bit products would give a factor this way.** Lean proves this over all distinct pairs of 1,024-bit primes with a 2,048-bit product. It includes factors exposed by a single label and both gcd signs for every square relation. [Exact theorem](../PrimeFactors/WeightedSubsetLabels.lean)

The sixteen numbers are the first two permitted square remainders at each weight from one through eight. For a label $A$ and weight $r$, the remainder is $D=A^2-4rN$. If remainders multiply to a square $z^2$, multiply their labels and take a gcd of $N$ with this product plus or minus $z$. On 2,100,271 one selection gave the primes 1,283 and 1,637. On both ordinary full-size controls, every selection failed the square test. The population bound says how many inputs could succeed even with perfect selection. [Worked example, comparison and control inputs](testing-three-weighted-remainders.md)

## When the extra combinations actually help

For **8,928,473**, exactly one selection out of the 65,535 multiplied to a square. It needed five remainders,

$$70{,}432\cdot214{,}144\cdot59{,}241\cdot16{,}969\cdot273=64{,}336{,}673{,}856^2.$$

Their labels were 5,982, 5,994, 8,455, 14,639 and 16,903. One gcd gave 3,511 and the other gave 2,543. A direct scan of ordinary labels found the answer on its 49th test. The subset search used 48 integer square roots including setup, and 156 gcds. A second example, 2,222,417, required four rows and gave 1,123 and 1,979. Separate Lean proofs show these selections are the only nonempty ones yielding a square on their respective inputs. [Five-row uniqueness proof](../benchmarks/controls/WeightedSubsetFive.lean) · [Four-row uniqueness proof](../benchmarks/controls/WeightedSubsetFour.lean) · [Benchmark fixtures and expected factors](../benchmarks/weighted-square-subsets.json)

On 137,649,271 the four-row search found 9,203 and 14,957 using 41 integer square roots and 121 gcds. A direct scan needed 190 ordinary labels. Screening labels for quadratic residues first found the same answer at that 190th label with only five post-setup square roots. Both the sieving and the gcd refinement consume work, so a saving in square-root calls alone does not establish a speedup. [Product-only comparison and complete censuses](../research/weighted-subset-search.json) · [Search and work counters](../experiments/weighted_subset_search.py)

Across all 253,789 eligible products of 11-, 12- and 14-bit prime pairs, five required four or more rows after the direct label gcds had been checked. The sieved ordinary comparison recovered all five within their respective square-root budgets. No such example occurred in the 8,192-product 16-bit holdout. On both 2,048-bit inputs, sixteen small primes provided unconditional certificates excluding every nonempty subset. The published Dirichlet-GRH result also supplies a worst-case bound on the prime scan for arbitrary positive rows. [Character method, bounds and certificates](character-certificates-for-square-relations.md)

## How one row constrains every subset containing it

Write $X=2^{1023}$. First suppose every label is coprime to $N$. All remainders are then positive. Two rows $(r,A)$ and $(s,B)$ can have $sA^2=rB^2$. In this case $DE$ has an integer square root congruent to $AB$ modulo $N$. Erasing the two rows from a square relation preserves both gcd outputs exactly. Repeat until every remaining pair of rows has a nonzero determinant. If the gcd gives a proper factor, some row remains, since the empty selection gives gcds $N$ and 1. [Pair removal and subset reduction](../PrimeFactors/WeightedSubsetReduction.lean)

Fix a remaining row $(r,A)$. From the **entire sixteen-label menu**, form $M$ by multiplying the nonzero values $|sA^2-rB^2|$ for all other rows. Every prime occurring to odd exponent in $D$ must divide another selected remainder $E$. It then divides $sD-rE=sA^2-rB^2$, so it divides $M$. Consequently $D=mu^2$ for a squarefree divisor $m$ of $M$. This one condition is necessary for all choices of the other rows at once. With $A$ and $r$ fixed, each such $D$ permits only one $N$. [Anchor and determinant proof](../PrimeFactors/WeightedSubsetAnchor.lean)

For these weights and ranks, $D\le U^2$ with $U=2^{517}$, and $M<2^{15\cdot1037}$. For each possible $m$, at most $\lfloor U/\sqrt m\rfloor$ positive integers $u$ fit. To count them using rational arithmetic, assign a prime $\ell$ a weight $c(\ell)$ of 1 below 16, 4 from 16 through 255, and 16 thereafter. Each weight satisfies $c(\ell)^2\le\ell$. Expanding a finite product therefore bounds the input count at a fixed anchor by

$$U\prod_{\ell\mid M}\left(1+\frac1{c(\ell)}\right) < U\,2^{193}.$$

There are at most six primes in the first group and 48 in the second. A product below $2^{15555}$ cannot contain more than 1,945 distinct primes of size at least 256. The resulting rational inequality is checked in Lean. [Fixed-label count](../PrimeFactors/WeightedSubsetFiber.lean)

## How many different menus are there?

As $N$ increases, the eight raw ceilings $\lceil2\sqrt{rN}\rceil$ are all nondecreasing. If their sum is equal on two inputs, each individual ceiling is equal. Knowing $N\bmod24$ then fixes all strides and both admissible labels at every weight. On the eligible population the sum and residue together admit at most $153X+8$ distinct complete menus. Multiplying by sixteen choices of anchor and the count above bounds the whole unit-label branch. This step avoids charging for each subset. [Menu count](../PrimeFactors/WeightedSubsetMenu.lean) · [Combining menus and anchors](../PrimeFactors/WeightedSubsetPopulation.lean)

If a label itself shares a prime $p$ with $N=pq$, write $A=cp$. Here $1\le c<15$ and $0\le D/p=c^2p-4rq<1296$. Thus the integers $p,r,c,D/p$ determine $q$. Counting these exceptional inputs allows fewer than one in $2^{980}$ eligible prime pairs. Including them in the exact integer count still leaves the total fraction below $2^{-277}$. The only population estimate is the project's unconditional lower bound on the number of eligible prime pairs. [Nonunit labels](../PrimeFactors/WeightedSubsetNonunit.lean) · [Prime-pair denominator](../PrimeFactors/ChebyshevPrimeSample.lean)

## If the number of rows grows

A separate written proof allows *every* integer label within a specified distance of the square-root endpoint. If both the weights and the allowed distance are bounded by any fixed polynomial in the input's bit length, the fraction of balanced semiprimes admitting a successful relation tends to zero, even for subsets of unrestricted length. For bounded weights the argument also excludes a range of subexponential distances. At 2,048 bits, a separate finite calculation allows as many as 33,554,432 labels and still bounds the successful fraction below $2^{-60}$. [Finite calculation and proof status](finite-budgets-for-weighted-subsets.md) [Growing-menu estimates, proof and precise range](growing-weighted-square-menus.md)
