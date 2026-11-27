# How many factor sums pass together?

For **1,879,513**, the first 45 candidate sums in steps of four begin at 2,742. A test using only the product's remainder modulo 315 leaves **2,746 and 2,854**. The first fails the integer square test. For the second, $2854^2-4\cdot1879513=792^2$, giving the prime factors **1,031 and 1,823**. We used both the product and the fact that its two factors are odd. [Lean proof and checked example](../PrimeFactors/PrimeSumListPacking.lean)

## Why two guesses survived

For any product that is 1 modulo 3 and a nonsquare modulo both 5 and 7, a public table of 18 small numbers contains a step with the following guarantees, wherever the list starts. At most one of 13 consecutive guesses at that step can pass modulo 315. At most two of 45 can pass. At lengths 14 and 46 respectively, every choice of step has some starting position where those guarantees fail. These are sharp bounds for this modulus. In the example the step is four, so these guesses already follow the product's ordinary mod-4 constraint. [Choice of step, guarantees and sharpness](../PrimeFactors/PrimeSumListPacking.lean)

The calculation can use the 12 permitted sums per period of 315. It cost two large square tests after selecting the block and filtering its residues. For a longer interval one must cover the remaining positions, including the other progressions if the chosen step omits some candidates. Nothing in the local table identifies which block contains the true sum.

## A list that always loses exactly half

At the prime 31 a different rule works for **every** product coprime to 31. Start on a multiple of 31 and take 16 consecutive guesses with any step that is nonzero modulo 31. Exactly eight pass. For $7,294,033$, descending in steps of four from 5,518 gives the eight survivors 5,518, 5,510, 5,494, 5,482, 5,478, 5,474, 5,462 and 5,458. Their square tests select 5,474, giving $2,293\times3,181$. This certifies the work inside that block. The product and step alone give no guarantee the block covers the answer. [Checked list and general block theorem](../PrimeFactors/SumGuessIncidence.lean)

More generally, let $\ell$ be any prime that is 3 modulo 4. A guessed sum $s$ passes at product residue $n$ precisely when $s^2-4n$ is a square modulo $\ell$. Over the $\ell-1$ nonzero product residues, a single guess passes exactly half the time. Two guesses having different squares pass together at exactly $(\ell-3)/4$ products. Opposite guesses always pass together.

For a fixed list of $C$ guesses with distinct squared residues, let $K_n$ count how many pass at $n$. The resulting exact identity is

$$
\sum_{n=1}^{\ell-1}(2K_n-C)^2=C(\ell+1-2C).
$$

Taking one guess from each possible square gives $C=(\ell+1)/2$. The right side is zero, so every nonzero product admits exactly half the list. Conversely, any nonempty set of residues that always leaves exactly half must use every square once. Its guesses cannot contain a pair of distinct opposites. This characterizes when a half-sized workload can be guaranteed on every input to that modular test. The counts range over product residues; they require no distributional assumptions about large primes. [Incidence, variation and converse proofs](../PrimeFactors/SumGuessIncidence.lean)

The overlap calculation uses the classical Paley difference-set identity for quadratic residues. Hittmeir gives the broader modular-hyperbola sieve for integer factorization. These notes count the work for fixed lists of candidate sums and the product ranges specified above. [Ó Catháin, §4.2](https://www.combinatorics.org/ojs/index.php/eljc/article/view/v20i1p38) · [Hittmeir](https://arxiv.org/abs/2205.10074)
