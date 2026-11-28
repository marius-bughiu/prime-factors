# Which true factor sums can share the same leading and trailing bits?

Suppose we know the **first 232 bits and last 250 bits** of a 2,048-bit odd product, and we know both factors are distinct 1,024-bit primes. Even for one specified choice of those 482 bits, at least **$2^{244}$ different remainders of the true factor sum modulo $2^{250}$** can occur among products with those observations. The argument uses a published prime-count bound under Dirichlet GRH. Lean checks the implication from that bound. The unknown middle bits vary across the products being compared. [Factor-sum theorem and assumptions](../PrimeFactors/ObservedPrefixSumResidues.lean) · [Prime-count estimate, Corollary 2](https://arxiv.org/pdf/2003.01925#page=2)

A small example shows what “the same observations” means. Read the first twelve and last eight bits of a 24-bit product. In hexadecimal that leaves just one digit hidden. Each row below reads **BF0?B1**. The factors and their sums differ.

| Product in hex | Product in decimal | Verified primes | True sum | Sum modulo 256 |
| --- | ---: | --- | ---: | ---: |
| BF05B1 | 12,518,833 | 3,229 × 3,877 | 7,106 | 194 |
| BF08B1 | 12,519,601 | 3,251 × 3,851 | 7,102 | 190 |
| BF0BB1 | 12,520,369 | 3,329 × 3,761 | 7,090 | 178 |

We selected these three products because they share the displayed digits. Lean checks their primality, multiplication, and both observed pieces. The large result covers every allowed leading word and odd trailing residue at its stated widths. A method that reads the middle bits has additional information. [Small certificate and large theorem](../PrimeFactors/ObservedPrefixSumResidues.lean)

## Exactly which sum remainders can occur?

Fix a modulus $m$ and an invertible product residue $r$. A sum residue $s$ is *locally possible* if two residues $x,y$ satisfy $xy=r$ and $x+y=s$ modulo $m$. This is a necessary test for prime factors. It becomes sufficient **across products sharing the observations** if every invertible residue has two distinct prime representatives in the desired factor interval. Choose one prime in each of the two required classes. If the classes coincide, choose different primes in that class. For a squarefree modulus, having two representatives in each unit class is also necessary to realize all admissible product-and-sum pairs. [Equivalence and squarefree converse](../PrimeFactors/AdmissibleSumRealization.lean)

The small case $m=210$ needs no analytic estimate. Lean checked the complete interval of twelve-bit primes. All 48 invertible residue classes contain at least three primes between 2,048 and 4,096, with the upper endpoint excluded. Every locally possible sum at a unit product residue therefore occurs as the true sum modulo 210 of some pair of distinct twelve-bit primes. [Finite count and exact realization](../PrimeFactors/AdmissibleSumRealization.lean)

For an odd prime power $p^e$ with $e\ge2$, **one prime per invertible class is necessary and sufficient**. If two factor residues coincide at $a$, the pair $a+p^{e-1},a-p^{e-1}$ has the same sum and product modulo $p^e$, and the two new residues are distinct. For example, 113 is the only seven-bit prime congruent to 5 modulo 9. All six unit classes have a prime, and every admissible sum for every unit product modulo 9 occurs with two distinct seven-bit primes. [Odd-prime-power theorem and finite example](../PrimeFactors/PrimePowerSingleRepresentatives.lean)

## Why the leading word can also be fixed

Write $B=2^{1024}$. Prescribing the first $h$ bits of a 2,048-bit product gives an interval $[K,K+2^{2048-h})$. Take $A=\lceil\sqrt K\rceil$ and $W=2^{1022-h}$. Every pair of integers from the **same** interval $(A,A+W]$ has a product inside that leading-word interval, and both factors have 1,024 bits. This includes the first and last possible leading-word intervals. The geometric statement needs no hypothesis about prime distribution. [Factor band and endpoint proof](../PrimeFactors/ProductPrefixFactorBand.lean)

For any modulus $3\le m\le2^{485-h}$ and any invertible residue, the prime-count estimate then gives **more than $2^{526}$ primes** in this factor interval. Choosing disjoint sets of at least $2^{525}$ representatives for the two factor residues yields at least $2^{1050}$ distinct products for **each** locally possible sum remainder and the specified product remainder and prefix. Unique prime factorization makes these products distinct. [Counting distinct products](../PrimeFactors/ResiduePairMultiplicity.lean) · [Joint bound for every prefix](../PrimeFactors/ObservedPrefixSumResidues.lean)

At $h=232$ and $m=2^{250}$ the budget has three bits to spare. The existing binary residue count says at least one in 64 sum residues passes for every odd product remainder. This gives at least $2^{250}/64=2^{244}$ actual sum remainders across the compatible 2,048-bit products. A list with fewer entries misses an entire sum class containing at least $2^{1050}$ different products with those same observations. A method given the full product can use the bits that distinguish them. [Binary count](../PrimeFactors/LocalSumMenu.lean) · [List bound and distinct-product count](../PrimeFactors/ObservedPrefixSumResidues.lean)

## What the Riemann hypothesis work contributes

The relevant upstream statement concerns zeros of **Dirichlet** $L$-functions, which govern prime counts in individual residue classes. Ernvall-Hytönen and Palojärvi give an explicit error for these counts in their Corollary 2 under Dirichlet GRH. Across the factor interval, the main term is at least $W/(710\varphi(m))$. Each of the two endpoint errors is at most $13{,}200\cdot2^{512}$. Since $W/\varphi(m)\ge2^{537}$, subtracting both errors still leaves more than $2^{526}$ primes in each required class. [Paper and precise hypotheses](https://arxiv.org/pdf/2003.01925#page=2) · [Checked integral and numerical bounds](../PrimeFactors/WideResiduePrimeSupply.lean)

Our local Lean theorem takes those two published endpoint inequalities as inputs. The Dirichlet zero-location statement and its independent upstream verification are separate from this repository's proof. Earlier work used an unconditional prime-count estimate for one fixed modulus, 9,240. Here the modulus may grow as the leading word gets shorter. [Upstream statement](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab/src/Statements.lean) · [Independent verification](https://math.mit.edu/~drew/shortgrh/) · [Unconditional fixed-modulus comparison](which-small-signs-are-still-missing.md)
