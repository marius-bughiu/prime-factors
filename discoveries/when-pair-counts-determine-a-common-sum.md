# When do counts for pairs of tests determine a common sum?

Consider two small products. On each, take the first four possible sums from its balanced interval and test the primes 3, 13 and 11. Each test passes twice. Each pair of tests passes together once. **One interval has a sum that passes all three, and the other is empty.** Both products even give the same remainder modulo each test prime. [Lean proof of the products, endpoints and counts](../PrimeFactors/PairwiseSumCounts.lean)

| Product | Four possible sums | Pass patterns in order, for 3, 13, 11 | Sums passing all three |
| --- | --- | --- | --- |
| $10{,}961=97\times113$ | 210, 214, 218, 222 | 111, 001, 010, 100 | 210 |
| $187{,}709=337\times557$ | 870, 874, 878, 882 | 101, 011, 000, 110 | None |

Here 1 means that a sum passes. Both products are 665 modulo $4\cdot3\cdot13\cdot11=1716$. Their starting sums differ by 660. This preserves their positions in the modulo-3 and modulo-11 tables. In the modulo-13 table, it moves the two passing positions from first and third to second and fourth. The exact lower endpoint of the interval is public, so a method that retains those positions can distinguish the cases. The counterexample concerns methods that retain only the six counts. The two products were selected to exhibit this behavior. [Position-by-position proof](../PrimeFactors/PairwiseSumCounts.lean)

## What six exact counts do tell us

In a window of $w$ positions, call the three singleton counts $a,b,c$ and the three pair counts $u,v,z$, in the order $AB,AC,BC$. Then the possible number of common hits runs from $L$ to $U$, inclusive, where

$$
L=\max(0,u+v-a,u+z-b,v+z-c),\qquad
U=\min(u,v,z,w-a-b-c+u+v+z).
$$

For example, $A$ contains the $u$ hits shared with $B$ and the $v$ shared with $C$. If $u+v>a$, at least $u+v-a$ hits must belong to all three. Counting all eight possible pass patterns gives the other inequalities. Lean constructs a finite table for **every integer** between the endpoints. With inconsistent input counts the interval is empty. Sharp bounds from marginal totals are classical. The examples above show that both endpoints of the interval $[0,1]$ also occur in this arithmetic setting. [Constructive proof](../PrimeFactors/ThreeTestMarginals.lean) · [Dobra and Fienberg on sharp integer bounds](https://sites.stat.washington.edu/adobra/Files/Papers/sju00499.pdf)

## All 429 starting positions

Keep the product remainder 665 modulo 1,716. The allowed sums are 2 modulo 4. Advance the starting sum by four each time, taking four consecutive allowed sums per window. After 429 advances the whole pattern repeats, because $3\cdot13\cdot11=429$. Lean checked all starting phases against the original definition of a factor-sum remainder. [Local tables, period and exact census](../PrimeFactors/FourRowResidueCounts.lean)

| Possible common hits from the six counts | Number of starts | Actual common hits |
| --- | ---: | --- |
| Exactly zero | 275 | Zero |
| Exactly one | 128 | One |
| Exactly two | 2 | Two |
| Zero or one | 24 | Zero at 12 starts, one at 12 |

The counts determine the answer at **405 of 429 starts**. The remaining 24 split evenly. This proportion describes uniformly chosen starting phases for this one set of residues. The first allowed sum for an actual semiprime comes from its size, and may favor particular phases. Obtaining the six counts also takes work. This calculation measures the information those counts contain once available. [Corresponding counterexample using pairwise yes-or-no answers](which-prime-rejects-a-wrong-factor-sum.md#can-pairs-of-tests-tell-us-which-interval-to-search)

## How much can a summary lose?

**One more remainder can settle the four-row example.** Suppose we keep the positions that pass the first two tests and already have the six counts. Only one position passes both of those tests in either example. Read the third test there. For 10,961 that position is 210 and it passes. For 187,709 it is 882 and it fails. This identifies the joint hit when it exists. We paid for one additional test after obtaining the six counts and the first two lists of positions. [Checked position tables](../PrimeFactors/PairwiseSumCounts.lean) · [General four-row statement](../PrimeFactors/BooleanWindowQueries.lean)

For $k\ge1$ yes-or-no tests on $w$ positions, suppose two tables agree on the exact counts of every assignment to every proper subset of tests. Their numbers of positions passing all $k$ tests can differ by at most $\lfloor w/2^{k-1}\rfloor$. For abstract tables, some pair attains this bound for every $w$ and $k$. As a result, when $w<2^{k-1}$, all those lower-order counts determine how often every complete pattern occurs. For three tests on four positions the largest difference is one, exactly what the two semiprimes exhibit. [Sharp integer bound](../PrimeFactors/BooleanMarginalAmbiguity.lean)

The proof starts with the difference between the counts of the all-pass row. Flipping one bit reverses the difference because the two tables agree when that bit is hidden. Half of the $2^k$ patterns must therefore carry at least that difference in one of the tables. The alternating pattern is the classical parity example for binary contingency tables. The proof here spells out its finite integer bound, including leftover rows when $2^{k-1}$ does not divide $w$. [Kahle, Example 2.5.1, printed p. 54](https://d-nb.info/1006748466/34#page=59)

## How many tests need to be counted together?

With any number of columns, exact single and pair counts determine all pass patterns in a window of at most three rows, including their multiplicities. Four rows are enough for ambiguity, as our two products show. More generally, when the counts include every group of up to $r$ tests, fewer than $2^r$ rows guarantee a unique histogram. If there are more than $r$ tests, two different abstract histograms of size exactly $2^r$ can give the same counts. Lean formalizes this classical minimum-size theorem for combinatorial trades. A histogram loses the ordering of positions. [Lean proof including repeated rows](../PrimeFactors/BooleanTradeVolume.lean) · [Ghorbani, Kamali, Khosrovshahi and Krotov, Lemma 4](https://arxiv.org/pdf/1810.02296#page=6)

If only $d$ distinct pass patterns occur, one pattern can be singled out by fixing at most $\lfloor\log_2 d\rfloor$ suitably chosen test values. Each split can keep the nonempty side with fewer distinct patterns. Once a group of weight $w>0$ has been singled out, ask how many of those rows pass each remaining test. If all the answers are either zero or $w$, every row in the group has the same complete pattern. Its count is $w$. Finding the group, acquiring the required counts and recovering original positions have separate costs. [Lean isolation and recognition proofs](../PrimeFactors/SparseBooleanRow.lean) · [Mazumdar and Pal, Algorithm 1](https://mazumdar.ucsd.edu/Support_Recovery_in_Mixture_Models_With_Sparse_Parameters.pdf#page=4)

## What knowing the positions saves

Suppose we know the ordered results of $k$ earlier tests and the exact counts of all partial assignments that omit a test. The earlier tests divide the $w$ positions into $2^k$ groups, according to which of those tests passed. The smallest group contains at most $\lfloor w/2^k\rfloor$ positions. Read the last test on those positions. To move to a neighboring group, the supplied total for the two groups tells us how many last-test hits it contains by subtraction. Repeating this step determines the count in the group that passed every earlier test. If a group is empty, even its first count comes for free. [Reconstruction theorem](../PrimeFactors/BooleanWindowQueries.lean)

This bound charges only the final test at individual positions. It assumes the other positions and partial counts are already available. It gives a count, and in the ambiguous four-row case identifies the actual winning position. For longer groups, even a count of one can leave the identity of its position open. [Count and position examples](../PrimeFactors/BooleanWindowQueries.lean)

In this model the smallest-group cost can be unavoidable. Suppose two possible sets of totals give the same public summaries, their hit counts differ by at most one in every group, and all placements within each group are possible. Even an adaptive deterministic procedure that knows both sets of totals can need as many individual probes as there are positions in the smallest group. This applies when the two possible counts for the all-pass group are zero and one. The proof allows the numerical prime remainders to impose additional structure outside this model. [Decision-tree bound and its placement assumptions](../PrimeFactors/StratifiedPointQueryLower.lean)
