# Using both the location and the remainder of a sum

Suppose an earlier sum has an ordinary remainder and a later sum has a more frequent remainder. Which should we test first? Two earlier searches always give opposite answers. Checking sums in ascending order favors the earlier sum, while searching all favored remainders first favors the later one. A third order weighs both pieces of information.

On every pair of distinct 14-bit primes with a 28-bit product, the three orders took the following numbers of exact square tests. All three recovered all 228,713 pairs. [Complete finite census](../experiments/location_weighted_sum_order.py)

| Search order | Total exact square tests |
| --- | ---: |
| Increasing sum | 4,631,541 |
| All favored remainders first | 4,494,936 |
| Combine location and remainder | 4,390,120 |

The third order saved **5.21%** relative to ascending order and **2.33%** relative to visiting all favored remainders first. On 47,162 products it took more square tests than ascending order. For example, $134{,}230{,}699=10{,}009\times13{,}411$ took 17 tests in ascending order and 41 in each of the other two. On $134{,}373{,}121=8{,}209\times16{,}369$ the counts were 98, 28 and 40, respectively.

## How the location changes a guess

For a candidate sum $s$, compute $d=s^2-4N$. Give it weight five if $d$ is divisible by five and weight two otherwise. For the two square product residues modulo five, these weights count the ordered ways of obtaining each sum remainder modulo 25. For the two other product residues every passing sum has equal weight. Rank candidates by increasing $d/w^2$, breaking ties by the smaller sum. Each weight group is already in numerical order, so only the first remaining candidate in each group needs to be compared. Integer comparisons suffice. [Definition, order and unique successful test](../PrimeFactors/ScoreSumOrder.lean)

The rule comes from a model that draws two factor coordinates uniformly by area. If we keep their product fixed, their separation on a logarithmic scale is uniform. Transforming that separation to the sum gives a density proportional to $1/\sqrt{s^2-4N}$. Multiplying by the residue weight gives the stated order wherever the discriminant is positive. Among finite candidates with those modeled masses, Lean proves that this order minimizes the mean number of guesses. In the continuous version, taking all candidates above a density threshold gives the largest hit probability for that candidate volume. The derivation describes the model distribution. Measurements above use actual primes. [Density, discrete optimality and threshold theorem](../PrimeFactors/SumOrderDensity.lean) · [The original factor-coordinate model](where-to-look-for-the-factor-sum.md)

There is a sharp limit on what these weights can buy in a finite model. Start with any nonnegative candidate probabilities that decrease in ascending order, then multiply each by either two or five. **Every possible search order still costs at least $\sqrt{2/5}$ times the ascending mean**, about 63.25%. Dividing all masses by their sum keeps that comparison the same. Thus a different order can save at most about 36.75% in this class of models. The sharpness statement lets the positions of the weight-five labels vary freely. The specific modulo-25 pattern imposes further restrictions. [Bound for every order and limiting examples](../PrimeFactors/BoundedSumPrior.lean)

## Guarantees for the actual search

* **A favored true sum can only move earlier** relative to ascending order. It can be reached later than in the search that tries the entire favored group first. [Prefix inclusions](../PrimeFactors/ScoreSumOrder.lean)
* **An ordinary target has a limit on how far it can move back.** For any distinct same-width primes in the stated range above five, twice the new test count is at most five times the ascending count plus 21. The bound applies even when the true sum is close to the lower endpoint. [Worst-case guarantee](../PrimeFactors/ScoreOrderSlowdown.lean)
* **On more than 24.9% of all eligible 2,048-bit products**, the combined order uses at least 59% fewer square tests than ascending order. The same products still require at least $2^{894}$ tests. Lean checks the work bound using the published unconditional prime-count estimate as an explicit hypothesis. [Frequency and remaining work](../PrimeFactors/ScoreOrderFavoredCost.lean)

## What the small searches cost

At fourteen bits, constructing the common candidate lists took 39,458,306 lookups modulo 25. The measured merge prepared 5,529,755 discriminants on the square-product groups. It needed 2,196,487 comparisons to produce all the lists, of which 1,222,053 were needed through the successful tests. The reference full sort used 22,374,407 comparisons and produced exactly the same candidate order for every product. These operations are separate from the table of square-test counts.

A cheaper alternative replaced the discriminant by the distance from the start. That changed 43,479 full candidate lists and 2,839 stopping positions at fourteen bits. Its total was 4,390,085 square tests, 35 fewer than the model-derived rule. At eight bits, trying all favored remainders first took 164 tests, while the new order and ascending order both took 165. The model gives a reason to try the rule. Finite prime populations and the cost of generating the guesses can affect its measured performance. [Direct checks for all widths from two through fourteen](../experiments/location_weighted_sum_order.py) · [Separate model calculation](../experiments/sum_order_density_model.py)
