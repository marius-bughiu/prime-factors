# Can part of the product tell us which remainder to try?

Suppose someone multiplies two distinct 1,024-bit primes chosen uniformly from the pairs whose product has 2,048 bits. A searcher wants to guess the remainder of either prime modulo $R=2^{616}$. Each guess can also cover its negative. A correct guess lets the polynomial solver recover the factors. [Four-candidate theorem](polynomial-factor-lanes.md) · [An example where one guess worked](testing-one-factor-remainder.md)

Give the searcher 1,024 yes/no questions. Each question can depend on all earlier answers and can compute **any function of either the upper or the lower 1,024 bits** of the product. Afterward the searcher chooses up to $2^{40}$ remainders. Even with unlimited preprocessing, the chance of picking a correct one is less than $2^{-38}$, about one in 275 billion. Reading one entire half, with no questions about the other, gives a probability below $2^{-550}$. A selector that computes with the entire product at once can use information beyond this model.

## Why each half leaves so many possibilities

Set $X=2^{1023}$ and $M=2X$. The high word is $\lfloor N/M\rfloor$ and the low word is $N\bmod M$. The first belongs to $[X,2X)$, and the second is odd and below $2X$. Each set contains $X$ possible words.

Fix an odd first factor $p\in[X,2X)$. Either word determines at most one eligible partner $q$ for this fixed $p$. For the low word, $p$ is invertible modulo $M$ and $q<M$. For the high word, two different odd partners differ by at least two. Their products differ by at least $2p\ge M$, too far apart to give the same high word. [Lean proofs for both projections](../PrimeFactors/FactorLaneAdvice.lean)

An answer sequence restricts the possible words to a rectangle $H\times L$. This starts as the whole square. A question about the upper half splits the first set, and a question about the lower half splits the second. Thus the final rectangles are disjoint and their areas sum to $X^2$, including word combinations which never occur as prime products. The same rectangle construction is standard for deterministic two-party communication. [Roughgarden, *Communication Complexity (for Algorithm Designers)*](https://arxiv.org/abs/1509.06257)

Let each final answer sequence choose at most $T$ representatives. A hit means some orientation of the two primes has $p$ in one of at most $2T$ residue classes, after including negative signs. Checking the complementary remainder $N/u$ for the other prime requires no further representative. Because $R$ divides $X$, each class contributes exactly $X/R$ integer possibilities for $p$ before imposing primality. For every such $p$ there are at most $\min(|H|,|L|)$ partners. This also bounds the number of successful unordered pairs by counting oriented witnesses.

For $J$ answer sequences, Cauchy–Schwarz gives
$$
\left(\sum_i\min(|H_i|,|L_i|)\right)^2
\le J\sum_i |H_i||L_i| = JX^2.
$$
Thus at most $2TX^2\sqrt J/R$ pairs succeed. A depth-$c$ protocol has $J\le2^c$. If queries concern only one half, summing over its partition gives $X$ directly in place of $X\sqrt J$. Fixing any random coins gives a deterministic protocol, so averaging preserves the bounds. [Finite cell bound, rectangle inequality and arithmetic constants](../PrimeFactors/FactorLaneAdvice.lean)

There are more than $(0.22X/\log X)^2/2$ eligible unordered prime pairs, using just primes in $[\sqrt2X,2X)$. With $\log X<710$ the success probability is below $2^{26}T\sqrt J/R$. Inserting $T=2^{40}$ and $c=1024$ gives $2^{-38}$. With $T=1$ and no questions the same calculation gives $2^{-590}$. The finite combinatorial inequalities are checked in Lean. The decision-tree interpretation and the prime-density step use the argument here and the published prime estimates. [Prime-count constants for this exact population](stride-budget.md#an-explicit-bound-at-exactly-2048-bits) · [Rosser and Schoenfeld, Corollary 1](https://doi.org/10.1215/ijm/1255631807)

## What the best small lookup tables learn

We counted every eligible pair at each width. The entries give the maximum number of products recovered with one signed guess. A predicate may be chosen after seeing all the labels, and the word lookup is trained and evaluated on the same population. These counts describe how much an ideal lookup can fit. The full-size bound already allows such training.

| Prime bits | Radix | Eligible products | Fixed guess | One yes/no question about either half | Whole high word | Whole low word |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 8 | 128 | 148 | 28 | 49 | 87 | 98 |
| 9 | 128 | 543 | 97 | 152 | 251 | 262 |
| 10 | 256 | 1,718 | 181 | 294 | 552 | 577 |
| 11 | 256 | 5,530 | 413 | 671 | 1,378 | 1,321 |

A one-question strategy can use two guesses. For each candidate pair of guesses and each possible word, the best yes/no predicate takes the one that covers more labeled products with that word. The experiment checks every pair of guesses in both halves. [Reproduce the census](../experiments/factor_lane_advice.py)
