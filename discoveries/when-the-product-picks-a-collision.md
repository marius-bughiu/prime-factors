# When the product tells us which matches can reveal a prime

The product alone sometimes identifies a useful difference between its two unknown primes. If dividing the product by 12 leaves 5 or 7, exactly one prime can be found by the extra comparison below. We can test an entire batch for that prime with one final gcd. Across all 19,546 eligible products of two 12-bit primes, combining the old and new comparisons split 10,949 products on the same draws. The old search split 8,470. Both 2,048-bit controls remained unresolved after 128 draws. [Lean proof](../PrimeFactors/ComplementaryKeys.lean) · [Benchmark inputs and checks](../benchmarks/complementary-keys.json)

Take $N=1{,}022{,}117$, which leaves remainder 5. Of eight reproducible draws, the two numbers 375,951 and 882,388 receive labels 501,444 and 88,822 under the existing twelve-remainder rule. Their labels sum to 590,266. Subtract 1 and take a gcd with $N$ to get **1,009**. Division gives the other prime, 1,013. Direct label equality missed on all eight draws. The experiment computed the labels from $N$ alone. [How to compute a label](comparing-twelve-remainders-at-once.md) · [Search and directed product](../experiments/complementary_keys.py)

## Why adding two labels works

Write $J(x)$ for the old label and screen for the same exceptional remainders as before. Over a prime field every regular label has exactly twelve input remainders. The label is a square, and the identity

$$
1-J(x)=3\left(\frac{6x(x^2-1)(x^2-9)}{(x^2+3)^3}\right)^2
$$

has a nonzero right-hand side on regular inputs. Thus $J(y)=1-J(x)$ requires 3 to have a square root modulo the prime. The converse holds for every regular $x$. If $s^2=3$, then $y=(sx-3)/(x+s)$ is regular and has exactly that complementary label. Lean proves this by clearing denominators. Computing $s$ would require additional work. The search simply computes each label and compares their sums. The calculation uses the same rational group action as the earlier search. [Identities and local fiber counts](../PrimeFactors/ComplementaryKeys.lean) · [Background on rational group invariants](https://arxiv.org/abs/2105.11247)

At a prime where 3 is a square the extra comparison gives twelve partners, disjoint from the old twelve unless the label equals its complement. At most twelve seed remainders have that middle value. At a prime where 3 is a nonsquare there are zero extra partners. Quadratic reciprocity and multiplicativity give $(3/N)=-1$ precisely for odd $N$ coprime to 3 with remainder 5 or 7 modulo 12. For a product of two primes, one local sign is then positive and the other negative. A successful complement comparison immediately gives the positive-sign prime. [Public residue test and local counts](../PrimeFactors/ComplementaryKeys.lean)

## Two ways to use the comparison

**Keep both kinds of matches.** Replace each label $u$ by $u(1-u)$, which costs one modular multiplication. Two new labels agree in a field precisely when the old ones agree or sum to one. Test the middle value separately and retain the original labels for resolving global ties. If the old labels agree globally, the old signed comparisons still apply. If two different old labels give the same new label globally, a gcd with their difference or their sum minus one detects a match that occurs at only one prime. This keeps every old success on the same draws. When the old labels sum to one at both primes, their sum gives the whole product as a gcd. The cleared equation factors into six integer expressions, each of the form $a^2-3b^2$. Checking those expressions separately found two additional small products the combined label calculation had missed. For 1,040,279, the seeds 4 and 11 give a shared complement, but two separate expressions yield 1,031 and 1,009. The timing below includes screening, resolving ties and finding the factor. [Six-factor identity](../PrimeFactors/ComplementaryNormBranches.lean)

**Look only for the distinguished prime.** For a mixed product and regular input labels $u_i$, put $v_i=2u_i-1$ and $F(T)=\prod_i(T-v_i)$. Evaluate $F(-v_i)$ at every position and multiply those results modulo $N$. Each factor in this product is a unit at the nonsquare-three prime. Hence a single final gcd gives either 1 or the square-three prime, even when many pairs match. The implementation reuses the product tree for the $v_i$ by evaluating $F(-T)$, obtained by negating the odd coefficients. Setup for regularity retains its own gcd cost. [Exact gcd theorem including repeated samples](../PrimeFactors/ComplementaryBatch.lean)

## What changed in the measurements?

| Prime bits | Products | Draws per product | Original splits | Combined splits | Extra splits | CPU seconds, original / combined |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 12 | 19,546 | 12 | 8,470 | 10,949 | 2,479 | 4.20 / 4.28 |
| 20 | 512 | 128 | 106 | 154 | 48 | 2.36 / 2.36 |
| 24 | 256 | 256 | 17 | 23 | 6 | 2.74 / 2.76 |

The first row enumerates all distinct prime pairs of the stated width with a product of twice that width. The other rows replay the two previously fixed samples without replacement. All three rows retained every original success. The direct complement product was run separately on the 9,804 mixed products in the first row. It found 2,152 factors with its one final gcd and 690 more during setup. The timed runs use Python on one machine. These comparisons measure the two stated methods. [Results by product remainder](../research/complementary-key-panel.json) · [Reproduction script](../experiments/complementary_key_panel.py)

## How large is the full-size saving?

Fix any two distinct 1,024-bit primes with a mixed product. Sample independently and uniformly among inputs regular at both primes and away from the middle label at either. These conditions can be checked using the public product. On this sample space, one coordinate has 24 inputs per folded label and the other has 12. Lean proves that the chance of at least one pair agreeing at exactly one prime exceeds 95% at $105\cdot2^{504}$ draws. This sufficient budget is **17.97% smaller** than the earlier sufficient budget of $2^{511}$ regular draws. Neither budget is asserted to be optimal. The new budget is still about $5.5\times10^{153}$ draws. The two full-size benchmark rows each used 128. [Finite probability theorem and exact budget ratio](../PrimeFactors/ComplementaryBirthday.lean) · [Earlier bound](counting-twelve-residue-keys.md)

For a trillion independent uniform raw draws, the probability that the setup, middle values, shared-key refinements or directed pair comparisons expose a factor is less than one in $2^{938}$ for any two distinct 1,024-bit primes, and less than one in $2^{939}$ on the mixed products. A later implementation also tests coefficients that can reveal factors without any matching pair. A subsequent determinant calculation bounds these additional hits below one in $2^{902}$ even at a trillion uniform draws. [Intermediate-coefficient bound](how-often-a-polynomial-pivot-splits.md) [Unrestricted sampling bound for matches](../PrimeFactors/ComplementaryPracticalBudget.lean) · [Coefficient search](checking-opposite-keys-with-one-polynomial.md)

For inputs at the upper end of the 2,048-bit range, Lean also compares both label searches on the very same sequence. At about $5.5\times10^{153}$ accepted draws, more than 7.5% of sequences produce a proper factor through the folded labels while the old labels have no local match. [Same-budget theorem and hypotheses](comparing-complementary-labels-at-the-same-budget.md) · [Refining a match shared by both primes](splitting-a-shared-complement.md)
