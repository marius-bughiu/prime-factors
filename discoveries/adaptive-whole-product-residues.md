# Can remainders of the whole product select the right factor remainder?

A searcher can divide a 2,048-bit product by many chosen numbers, see every remainder, and use each answer to decide what to ask next. Suppose the least common multiple of the divisors used on any one input stays at or below $2^{1023}$. Even if the searcher gets **500 additional yes/no answers about any property of the whole product** and tries $2^{40}$ factor remainders modulo $2^{614}$, its chance of picking a correct one is below **one in 140 trillion** ($2^{-47}$) for the random prime pairs described below. With modular observations alone and a much larger allowance of $2^{1536}$, the chance is still below one in $2^{34}$. These bounds leave open algorithms that use other arithmetic on the whole product. The conditional polynomial theorem gives at most four candidates after a correct remainder has been selected. [Polynomial theorem](unit-newton-lanes.md) · [Previous bound for high and low words](factor-lane-advice.md)

## Which information can the selector use?

Set $X=2^{1023}$. Choose an unordered pair of distinct primes uniformly from $[X,2X)$ subject to $N=pq\ge 2X^2$, so the product has exactly 2,048 bits. The selector may ask for $N\bmod m$ at any positive modulus determined by earlier answers. Denote the maximum pathwise least common multiple by $Q$. Moduli on different branches can be unrelated. Every function of already observed remainders is free, including Jacobi symbols of $N$ with an observed odd denominator. In addition, up to $t$ yes/no queries can compute arbitrary predicates of $N$. Precomputation may use the whole labeled population. Independent random coins give a mixture of deterministic selectors, so the same bound applies.

Each final transcript guesses up to $T$ remainders modulo $R$, where $R\mid X$. A guess succeeds when either sign of either prime has that remainder. The complementary remainder $N/u\bmod R$ gives the other prime's residue up to the same sign whenever $u$ is a correct unit guess, so swapping the factors costs no extra guess. One can also try guesses sequentially and continue after a simple miss. Follow the all-miss branch and keep every guess made there. It includes the first actual hit. Extra arithmetic details produced while testing a guess are subject to the same observation budget.

## A counting bound with no common modulus across branches

First fix a string of answers to the $t$ unrestricted predicates, padding shorter strings. Follow those answers regardless of whether they are correct. In the resulting modular tree, every reachable leaf specifies one class $N\equiv a_i\bmod M_i$, with $0\le a_i<M_i\le Q$. Intersecting two consistent congruences at moduli $m,k$ gives one class modulo $\operatorname{lcm}(m,k)$. Two different leaves first disagree at a remainder query, so their classes are disjoint on **all integers**. These statements also apply to the tree obtained by stopping before any specified query. Branches exceeding the budget can be truncated before querying. [Lean refinement lemma](../PrimeFactors/CRTResidueAdvice.lean)

Orient a successful pair so its first prime $p$ agrees up to sign with a guess. In each leaf, at most $K=2TX/R$ first-factor integers are possible, since $[X,2X)$ contains $X/R$ complete radix blocks. For each fixed $p$ coprime to $M_i$, multiplication by $p$ is invertible. Hence all its possible partners $q$ at this leaf have the same remainder modulo $M_i$. Map each partner to

$$a_i+M_i\left\lfloor(q-X)/M_i\right\rfloor.$$

Different partners have different images, since they share a remainder and differ by at least $M_i$. Every image lies in the leaf's congruence class inside $[0,X+Q)$. Each leaf can charge that part of the interval at most $K$ times, once per first-factor integer. Different leaves charge disjoint parts. This proves a bound of $K(X+Q)$ successful unordered pairs with a coprime oriented witness. It also holds when every leaf chooses an arbitrary list of $K$ first-factor integers. [Lean finite union and factor-remainder bounds](../PrimeFactors/CRTResidueAdvice.lean)

When $Q\le X$, every sampled prime exceeds $X$ and is coprime to every path modulus. For $X<Q<X^2$, a query might use a multiple of one of the secret primes and immediately reveal it by a gcd. Count every such discovery as a success. Stop each branch immediately before the first proposed modulus containing any prime $r\ge X$. The cumulative modulus after the query has at most one such prime, since two distinct ones have product at least $X^2$. The previous modulus $M$ is coprime to $r$, so $Mr\le Q$ and $M\le\lfloor Q/X\rfloor<X$. If either secret prime ever divides a queried modulus, it must be this first $r$. Each stopped leaf can therefore nominate just **one** first-factor integer $r$, determined by the next query before its answer arrives. Apply the same bound to the truncated tree with $K=1$ and modulus cap $\lfloor Q/X\rfloor$. This adds at most $X+\lfloor Q/X\rfloor<2X$ pairs per answer string. [Lean large-prime and interval bounds](../PrimeFactors/CRTResidueAdvice.lean)

The union over the at most $2^t$ answer strings multiplies these bounds by at most $2^t$. The eligible population contains more than $(0.22X/\log X)^2/2$ pairs. This follows from counting primes in $[\sqrt{2}X,2X)$ using explicit prime-counting inequalities. Since $\log X<710$ and $4(710/0.22)^2<2^{26}$, the success probability is below

$$2^{26+t}\frac{T}{R}(1+Q/X)$$

for $Q\le X$. For $X<Q<X^2$ add $2^{26+t}/X$. At $R=2^{614}$, $T=2^{40}$ and $Q=X$, the bound is $2^{-547}$ before unrestricted questions and $2^{-47}$ after 500. For $Q=2^{1536}$ and $t=0$, substituting $Q/X=2^{513}$ gives the stated $2^{-34}$ bound including gcd discoveries. The finite combinatorial bounds are checked in Lean. The decision-tree interpretation and the prime-population normalization are deductions given here. [Prime-count constants for this population](stride-budget.md#an-explicit-bound-at-exactly-2048-bits) · [Rosser and Schoenfeld, Corollary 1](https://doi.org/10.1215/ijm/1255631807)

## An exact small example

Take $X=R=1024$. First read $N\bmod3$. For remainder one, next use the largest prime at most $\lfloor Q/3\rfloor$. For remainder two, use the second largest. Give every leaf all the factor labels for its training set and select its optimal single signed guess. There are exactly 5,530 eligible unordered prime pairs. The table counts actual hits using either factor and either sign.

| Path cap $Q$ | Two possible next primes | LCM across all branches | Occupied leaves | Best one-guess hits |
| ---: | ---: | ---: | ---: | ---: |
| 128 | 41, 37 | 4,551 | 76 | 306 |
| 512 | 167, 163 | 81,663 | 328 | 535 |
| 1,024 | 337, 331 | 334,641 | 666 | 815 |
| 4,096 | 1,361, 1,327 | 5,418,141 | 2,364 | 2,462 |
| 16,384 | 5,449, 5,443 | 88,976,721 | 4,368 | 4,376 |
| 65,536 | 21,841, 21,839 | 1,430,956,797 | 5,260 | 5,264 |

At $Q=1024$, the products $1061\cdot1999=2{,}120{,}939$ and $1063\cdot2027=2{,}154{,}701$ give the identical transcript $884\bmod993$. Their signed factor guesses reduce to the disjoint sets $\{37,49\}$ and $\{21,39\}$, so no choice at that leaf covers both. Reproduce every table entry with `python3 -m experiments.crt_residue_advice`. [Exhaustive census](../experiments/crt_residue_advice.py)
