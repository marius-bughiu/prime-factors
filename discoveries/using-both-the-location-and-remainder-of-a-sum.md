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

At fourteen bits, constructing the common candidate lists took 39,458,306 lookups modulo 25. The measured merge prepared 5,529,755 discriminants on the square-product groups. It needed 2,196,487 comparisons to produce all the lists, of which 1,222,053 were needed through the successful tests. The reference full sort matched the merge order for every product on both interpreters, using 22,374,407 comparisons on CPython 3.9.6 and 22,516,175 on CPython 3.14.7. These operations are separate from the table of square-test counts.

A cheaper alternative replaced the discriminant by the distance from the start. That changed 43,479 full candidate lists and 2,839 stopping positions at fourteen bits. Its total was 4,390,085 square tests, 35 fewer than the model-derived rule. At eight bits, trying all favored remainders first took 164 tests, while the new order and ascending order both took 165. The model gives a reason to try the rule. Finite prime populations and the cost of generating the guesses can affect its measured performance. [Direct checks for all widths from two through fourteen](../experiments/location_weighted_sum_order.py) · [Separate model calculation](../experiments/sum_order_density_model.py)

## Does the combined order help across all full-size products?

**Yes. Across every eligible pair of distinct 1,024-bit primes giving a 2,048-bit product, it saves more than 2.59% of the ascending search’s exact square tests in total.** Switching from the earlier favored-first rule to the combined rule saves an additional number of tests exceeding **1.54% of the original ascending total**. Both percentages use the same denominator and include every slower case. The proof assumes the published unconditional prime-count estimate at modulus five. It gives no practical runtime for a 2,048-bit input. [Full-population comparison](../PrimeFactors/MeanScoreOrderWork.lean) · [Prime-count input, Theorem 1.3](https://personal.math.ubc.ca/~bennett/BeMaObRe-IJM-2018.pdf#page=5)

The earlier rule reaches a favored true sum as early as it possibly can while keeping the favored group in ascending order. The combined rule may pay for earlier ordinary guesses on those inputs. It gains on ordinary targets by avoiding distant favored guesses above them. For either type, solving the score comparison gives a square-root expression for the furthest opposing guess that can get ahead of the target. We bound those distances on each rectangle in the same finite partition used for the earlier rule, credit only complete rectangles for gains, and charge every possible rectangle for losses. [Costs on individual pairs](../PrimeFactors/ScoreVsGlobal.lean) · [Checked rectangle bounds](../PrimeFactors/ScoreGridGeometry.lean) · [Independent rectangle calculation](../experiments/score_prime_grid.py)

## How much work is still unavoidable?

**Fewer than one in $2^{35}$ eligible products can finish in fewer than $2^{893}$ square tests** under the combined order. This bound on the exceptions is unconditional and its prime count is proved inside the repository. The result applies to a wider family of searches as well. If the method visits each remainder class in ascending order and keeps the entire class containing the true sum, then all earlier sums in that class must be tested before reaching it. Even allowing a different period of up to $2^{128}$ for each input still leaves at least $2^{772}$ visits on all but the same fraction. A method able to skip individual members of the true remainder class is outside this argument. [General lower bound and application to the search orders](../PrimeFactors/WithinResidueSearchFloor.lean)

Here is where the large number comes from. Except on that small fraction of products, the true sum lies at least $2^{900}$ integers beyond the public starting point. At period 100, every hundred integers contain another member of its exact remainder class. Choosing which class to visit next cannot avoid the earlier members of that same progression. [Counting closely separated factors](../PrimeFactors/FullRangeLongSumPrefix.lean) · [Unconditional prime-population size](../PrimeFactors/ChebyshevPrimeSample.lean)

## Can we avoid building the whole list of guesses?

Yes. Each surviving remainder starts a progression of sums 100 apart. Keep only the first untested sum of each progression and take the one with the smallest score, then advance that progression. For a current sum $s$, its next discriminant is $d+200s+10{,}000$. The increment itself increases by 20,000 each time. This produces exactly the same candidate order using at most ten live sums for products coprime to five. Lean proves completeness of the progressions, the update identities, and why the lowest-scoring current sum comes before every other untested candidate. [Progression proofs](../PrimeFactors/StreamSumScores.lean)

We ran the two streaming searches through their actual square hits on every eligible 2- through 14-bit prime pair with a full-width product. Independent counts agreed on all 320,981 pairs. Both versions had at most ten live candidates. The implementation uses a heap, and its behavior was tested separately from the mathematical invariants. [Streaming experiment](../experiments/stream_sum_scores.py) · [Regression tests](../tests/test_stream_sum_scores.py)

| Operation across all 320,981 pairs | Ascending | Combined order |
| --- | ---: | ---: |
| Exact square tests | 5,426,224 | 5,146,749 |
| Comparisons between heap entries | 19,345,532 | 18,863,910 |
| Additions to advance the progressions | 14,783,139 | 13,781,688 |
| Multiplications to form priority scores | 0 | 2,748,875 |

For example, $132{,}289=263\times503$ has public sum range 728–769. The combined order finds the factors on its third square test, while ascending order takes four. Both searches pay to initialize each live progression. The counts leave wall-clock time open.
