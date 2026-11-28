# What the angle of one cyclotomic value reveals

Two products, 14,351 and 11,663, both leave remainder 1 on division by 7. The first has factors 113 and 127, which also leave the same remainder as each other. The second has factors 107 and 109, which leave different remainders. An average of seven polynomial readings distinguishes these cases. Keeping the complex angle of just one of the readings gives more information: the exact remainder of the prime sum modulo 7. [Exact controls and acquisition costs](../benchmarks/cyclotomic-root-readings.json)

## One angle gives the sum

Let $N=pq$ for distinct primes $B\le p<q<2B$. Use the polynomial $T_N(X)=(X-1)(X^N-1)/\Phi_N(X)$. Its index is the public product. In terms of the unknown primes it equals $(1-X^p)(1-X^q)$. At a primitive $m$th root of unity $z$, write $w=T_N(z)$. Provided $m$ divides neither prime,

$$w/\overline{w}=z^{p+q}.$$

Conjugation replaces $z$ by its reciprocal. Each of the two factors contributes its own exponent to the ratio. The result identifies the sum modulo $m$. Choosing $m=4B$ puts the whole sum within one turn of the circle. At $z=\exp(2\pi i/(4B))$ the exact sum is

$$p+q=4B\left(1+\frac{\operatorname{Arg}(w/\overline{w})}{2\pi}\right),$$

using the principal angle in $(-\pi,\pi]$. Both factors lie in the promised range and are distinct, so the sum lies strictly between $2B$ and $4B$. A supplied complex measurement of absolute error less than $1/(4B)$ still determines the sum uniquely when compared with exact candidate phases. For 1,024-bit primes this means error below $2^{-1025}$. The exact angle formula assumes exact arithmetic. The error theorem makes no assumption about the time to produce $w$. [Exact formula and noisy comparison](../PrimeFactors/CyclotomicRootPhase.lean)

## What averaging retains

Let $E_m$ be the average of $|T_N(z)|^2$ over **all** $m$th roots, including 1. The average of $z^j$ is 1 when $m$ divides $j$ and zero otherwise. Applied to the four terms of $T_N$, this gives

$$ E_m=4-4[m\mid p]-4[m\mid q]+2[m\mid p+q]+2[m\mid q-p].$$

Here brackets equal one for a true statement and zero otherwise. The formula includes factor moduli and $m=1,2$. For $m>2$ coprime to $N$, the value is 6 if the two prime residues agree up to sign and 4 otherwise. The ordinary complex mean of the same readings is $1+[m\mid p+q]$. [Both identities](../PrimeFactors/CyclotomicRootEnergy.lean)

At $m=7$, the remainder of $N$ tells us which collision is possible. For a nonzero square remainder (1, 2 or 4), a 6 means that 7 divides the prime gap. For a nonsquare remainder (3, 5 or 6), a 6 means that 7 divides the sum. The exact measurements below came from polynomial coefficients constructed using only the product. A separate Fermat search supplied the check factors. [Reproducible measurements](../experiments/cyclotomic_root_readings.py)

| Product | Product mod 7 | Mean square | Ordinary mean | Sum mod 7 from one phase | Checked factors |
| ---: | ---: | ---: | ---: | ---: | --- |
| 14,351 | 1 | 6 | 1 | 2 | 113 × 127 |
| 11,663 | 1 | 4 | 1 | 6 | 107 × 109 |
| 9,523 | 3 | 6 | 2 | 0 | 89 × 107 |
| 11,413 | 3 | 4 | 1 | 4 | 101 × 113 |

Over all pairs of units modulo $m$, the equal-or-opposite test is determined by the product remainder for every pair exactly when $m$ divides 24 or equals 5 or 10. For each of the other moduli, a particular unit product permits both answers exactly when it is a square or the negative of a square modulo $m$. This classifies information available from the remainder. A calculation using the entire integer may have more information. [Proof and witnesses](../PrimeFactors/CyclotomicEnergyResidues.lean)

## How often the value is six

At each fixed nonzero product remainder modulo 7 there are six choices for the first unit. Exactly two give equal or opposite factors. For actual unordered pairs of distinct 1,024-bit primes with a 2,048-bit product, the fraction giving 6 is within $1/17010$ of one third **in each of the six product classes**, using the published unconditional bounds for primes in progressions. With the Dirichlet-GRH bounds it is within $2/(9\cdot2^{480})$. Lean proves both transfers from the endpoint estimates. Without any external estimate the checked elementary count already gives more than one in 36 across the whole population. These are frequencies across inputs. They leave the evaluation on a specific input open. [Population proof](../PrimeFactors/CyclotomicEnergySevenPopulation.lean) · [Bennett, Martin, O’Bryant and Rechnitzer, Table 1](https://personal.math.ubc.ca/~bennett/BeMaObRe-IJM-2018.pdf#page=6) · [Ernvall-Hytönen and Palojärvi, Corollary 2](https://arxiv.org/pdf/2003.01925#page=2)

## Cost of obtaining the value

Across six 14-bit examples, constructing the inverse cyclotomic polynomial took 8,432–14,588 trial divisions. Its degree after scaling already equalled the prime sum. The seven-term phase comparison used only integer coordinates in the basis $1,z,\ldots,z^5$. Ordinary Fermat search found each pair in one to five midpoint tests. A separate exhaustive check over all 42 eligible seven-bit prime pairs confirmed the phase identity using known factors. [Acquisition counts and complete census](../benchmarks/cyclotomic-root-readings.json)

Bzdęga, Herrera-Poyatos and Moree give a character formula for the ordinary cyclotomic polynomial at roots of unity. Their formula uses a product over the prime divisors of the index. The pinned Dirichlet zero-location result can inform error estimates for prime counts; it supplies neither those divisors nor a numerical value of $T_N(z)$ for one specified product. At the fourth root $i$, a publicly checkable sum-of-two-squares representation does determine the value on a restricted family. [Classical character formula, Theorem 1](https://arxiv.org/pdf/1611.06783#page=2) · [Pinned Dirichlet statements](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab/src/Statements.lean) · [A product-only square test](when-a-square-remainder-narrows-the-prime-sum.md)
