# Can an accidental match find the primes?

Yes. We gave the search **33,017** and allowed it one guess. It tried **366** as the sum of the two primes. The correct sum is **378**. Even so, the calculation returned **241**, and division gave **137**. The reason is that the computed power left remainder 4,580 modulo 33,017, and the greatest common divisor of 4,579 and 33,017 is 241. Lean checked the calculation and both primes. [Reproduce the example and download its certificate](https://marius-bughiu.github.io/prime-factors/#weighted-accidental-33017) · [Arithmetic proof](../PrimeFactors/TraceCollisionLimit.lean)

**How often can even this kind of lucky match help on a 2,048-bit product?** Even if we try **all 4,194,303 integer bases** from 2 through $2048^2$, fewer than one in $2^{44}$ eligible prime pairs can produce *any* match within the budget below. That is fewer than one in 17.5 trillion. For any one base fixed in advance, including base 2, the upper bound is one in $2^{66}$. The count includes a match at either factor, a guess that gets the true sum, every accidental match, and the preliminary check for a short cycle. This rules out a practical general solution along this particular route. [Combined Lean theorem](../PrimeFactors/TraceCollisionLimit.lean)

## Which searches the bound covers

* Choose two distinct 1,024-bit primes uniformly, conditioned on their product having 2,048 bits. Each possible unordered pair is counted once.
* Use the usual stride-24 calculation with any or all integer bases from 2 to $2^{22}$, with up to $2^{64}$ starting powers and up to $2^{64}$ consecutive blocks **per weight pair**. A weight pair consists of coprime integers $1\le b\le2^{32}$ and $b\le a\le2b$. The choices and row lengths may depend on the whole product.
* Each row begins at its first allowed sum at or above $2\sqrt{abN}$. Every slot in the last block counts, including slots added to fill the block. The bounds refer to the ordinary search with the residue wheel disabled. Bases above that ceiling, different starting points and different factorization algorithms are outside this theorem.

The real search compares powers, and a product of their differences can have a common factor with $N$. Over either prime field a product vanishes only when at least one difference vanishes. Thus an individual equality modulo one of the two primes is necessary for that batch to split the product. An exact equality modulo $N$ also supplies such an equality. The preliminary gcd covers the case when a power first comes back to 1. The source of the engine is Python. The mathematical characterization of a comparison, the preliminary gcd condition and the frequency bound are Lean theorems. [Search engine](../experiments/weighted_stride_search.py) · [Identity for one emitted block and one starting power](../PrimeFactors/TraceCollisionOrder.lean)

## Counting the accidental matches

Fix either prime $p$ as the modulus. For the chosen base $v$, let $h$ be the multiplicative order of $v^{24}$ modulo $p$, the number of multiplications needed to return to 1. For a tested label $z$, equality of the powers implies

$$h\mid ap+bq-z.$$

This follows because the row compares powers for $a+bN$ and $z$ and $(a+bN)-(ap+bq)=(p-1)(bq-a)$. The factor $24$ in the base accounts for the different permitted steps. We count primes with $h\le H=2^{470}$ separately. Each divides at least one $v^{24j}-1$ with $1\le j\le H$. If $v\le2^s$, the base-two logarithm of the product of these integers is at most $12sH(H+1)$. Each distinct target-width prime contributes at least 1,023 to this logarithm. For base 2 there are fewer than $2^{934}$ such primes. For any fixed base in the whole range there are fewer than $2^{939}$. [Order theorem and exceptional-prime count](../PrimeFactors/TraceCollisionOrder.lean)

For a larger order, write $ap+bq-z=th$. Since $z$ is at or just above $2\sqrt{abN}$, the function

$$E(q)=(\sqrt{ap}-\sqrt{bq})^2$$

must lie between $th$ and $th+2^{133}$. Its value is nonnegative, and $h>2^{470}$, so $t$ is a nonnegative integer. Also $th\le ap+bq$, giving a finite list of possible $t$ for each prime and weight.

Put $U=2^{1024}$ and $R=2^{874}$. The region $|bq-ap|\le R$ has at most $2R+1$ integer partners for each prime and weight. Outside this region, on either side of the minimum of $E$, moving from $q_1$ to $q_2$ changes $E$ by at least $|q_2-q_1|R/(3U)$. An interval of width $2^{133}$ in $E$ can therefore contain at most $1+\lfloor 3U2^{133}/R\rfloor$ integer partners on each side. Summing these budgets and including the small-order primes bounds the number of possible matches at either factor. Taking the union over every base covers choosing a different base after reading each product, even if we grant perfect hindsight. [Separation on each side](../PrimeFactors/TraceCollisionWidth.lean) · [Finite count, parameters and exact constants](../PrimeFactors/TraceCollisionPopulation.lean)

The population normalization is the established unconditional estimate $2^{1023}P<44331T$, where $P$ counts possible first primes and $T$ counts eligible unordered target pairs. Lean proves the final fraction from this explicit numerical hypothesis. The published prime-count theorem justifies it on paper. The modular collision bound uses no RH assumption. The separate count for hits at the true sum can be made sharper using RH. [Prime-count derivation](stride-budget.md#an-explicit-bound-at-exactly-2048-bits) · [Rosser and Schoenfeld](https://doi.org/10.1215/ijm/1255631807) · [Frequency of direct hits](how-often-a-weighted-search-reaches-the-factors.md)

## How this relates to the small bases supplied by RH

The project previously used the Dirichlet zero-location result with a theorem of Lamzouri, Li and Soundararajan. For a target modulus, every proper subgroup of its units omits some prime base below the squared bit length. That result helps distinguish candidate sums once we know where to test them. The new bound allows testing *every* integer base up to that ceiling. Even together they rarely put a revealing equality in the initial blocks on a typical product. Combining small bases into a single larger base is a different option and can exceed the ceiling in this theorem. [Lamzouri, Li and Soundararajan, Theorem 1.1](https://arxiv.org/abs/1309.3595) · [Pinned Dirichlet statements](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab/src/Statements.lean) · [Project's base-combination result](combining-weighted-bases.md)
