# How many tests survive on the complete range?

We can skip whole groups of tests on the basis of the product alone. On our two 2,048-bit comparisons, the filter eliminates about **73.59%** and **78.57%** of the candidate pairs that already pass the coprimality check. Even after these exclusions, more than $2^{1019}$ candidate pairs remain on each number. We counted the range mathematically. We have not tested all those pairs or determined when a first success would occur. [What the complete range guarantees](complete-offset-search.md) · [Offset exclusion proof](offset-divisor-sieve.md)

## What one complete search would visit

Write $T=\lfloor\sqrt N\rfloor$, $h=N-T^2>0$ and $J=\lfloor\sqrt{4h/3}\rfloor$. For $1\le j\le J$, the range is $1\le k\le\lfloor Tj/h\rfloor+1$. Only coprime pairs are needed. Lean proves that the total number of primitive pairs exceeds $T/16$, while even the unfiltered list has at most $2T$ positions. This gives more than $2^{1019}$ distinct primitive positions before local filtering on **every** nonsquare with at least 2,048 bits. The only assumptions on the floor-root remainder are $0<h\le 2T$. Early success can take fewer tests. [Finite cardinality proof and specialization](../PrimeFactors/CompleteOffsetWork.lean)

The lower bound uses coprime pairs $1\le a\le b\le J$. When $T\ge h$, fixing $j=b$ and taking $k=a+tb$ for $0\le t<\lfloor T/h\rfloor$ embeds distinct copies of these pairs in the schedule. When $h>T$, folding $a$ to the near side of the interval $[0,b]$ produces an admissible multiplier with at most two original pairs per outcome, handling $a=b=1$ separately. Counting the original coprime pairs gives the bound. [Farey count](../PrimeFactors/FareyWork.lean) · [Embedding and reflection](../PrimeFactors/CompleteOffsetWork.lean)

## Whole offsets and actual pairs

A primitive square hit requires $-h$ to be a square modulo the entire offset $j$. For each prime $p\le10^6$ find the first power $q=p^e$ at which this congruence fails, if one exists through $J$. Every multiple of that $q$ can be skipped. Offsets differ in the number of multipliers they contain and in the proportion coprime to them. Counting offsets alone therefore gives a different saving from counting pairs. [Local arithmetic, including powers of two](offset-divisor-sieve.md)

| Input | Fraction of offsets retained | Fraction of primitive pairs retained | Lower bound for retained primitive pairs |
| --- | ---: | ---: | ---: |
| Fresh 2,048-bit comparison | 22.1724% | 26.410182%–26.410183% | $>2^{1020}$ |
| Crossed 2,048-bit comparison | 17.2352% | 21.432102%–21.432103% | $>2^{1019}$ |

The primitive-pair intervals are rounded outward. The offset column gives approximate percentages. They count potential tests before checking the sign or squareness of the discriminant. On the same first 64 raw positions on each full-size comparison, the filter through $p=251$ reduced actual integer square roots from 36 to 22 on the fresh number and from 37 to 10 on the crossed number. Both searches returned the original cofactor unresolved. In an exhaustive run with that cutoff over all 1,234 smaller prime pairs in the seven-, eight- and nine-bit panels, skipping obstructed offsets reduced the number of integer square roots from 161,418 to 59,301 while retaining every successful split. Stopping on the first split reduced square roots from 28,677 to 14,243. The filtered exhaustive runs performed 89,799 divisibility checks to reject whole offsets. In one local nine-bit timing comparison, completing the panel took 70.0 ms without the filter and 42.5 ms with it. Stopping at the first split took 17.8 ms without it and 18.7 ms with it. Timings vary by machine. [Reproduce the large counts](../experiments/complete_offset_density.py) · [Run the small comparisons](../experiments/complete_offset_filter.py)

## Can testing every offset divisor finish these examples?

Even if we could instantly test **every divisor of every offset**, a single offset on each comparison still leaves more than $2^{511}$ primitive multiplier choices with positive discriminant. For the fresh input take $j=7^{182}$, and for the crossed input take $j=13^{138}$. Each offset is in its sharp range. An explicit integer whose square equals $-h$ modulo $j$ supplies a root at every divisor of $j$. For $K=\lfloor Tj/h\rfloor$, each full block of $p$ consecutive multipliers through $K$ holds $p-1$ coprime choices when $j$ is a power of $p$. The kernel checks the roots, the two block counts, and the sign of the discriminant across each counted row. This bound applies even if we drop the extra endpoint. Additional tests that also use the multiplier can still reject candidates. [Concrete proofs for both products](../PrimeFactors/OffsetAllDivisors.lean)

## Bounding the finite counting error

Put $c=T/h$ and $K=cJ^2/(2\zeta(2))$. For a product $M$ of distinct listed prime powers, let $P_M$ count primitive pairs in the schedule with $M\mid j$. For a positive divisor index $d$ set $L=\operatorname{lcm}(d,M)$. Before the primitive constraint, summing over all $L\mid j$ and $d\mid k$ gives

$$A(d,L)=\sum_{i=1}^{\lfloor J/L\rfloor}\left\lfloor\frac{\lfloor cLi\rfloor+1}{d}\right\rfloor.$$

Each summand differs from $cLi/d$ by at most one. Writing $n=\lfloor J/L\rfloor$ gives $|L^2n(n+1)-J^2|\le JL$. Together these give the following unconditional finite bound, checked in Lean after clearing denominators. [Grid count](../PrimeFactors/OffsetGridCount.lean)

$$\left|A(d,L)-\frac{cJ^2}{2dL}\right|\le\frac{cJ}{2d}+\frac{J}{L}.$$

The following steps are paper deductions. By Möbius inversion, $P_M=\sum_{d\le J}\mu(d)A(d,\operatorname{lcm}(d,M))$. Since $L\ge d$, summing the grid errors and extending the main sum past $J$ costs at most

$$E=(c/2+1)J(1+\ln J)+cJ/2.$$

Absolute convergence permits factoring the main sum. Use $1/(dL)=\gcd(d,M)/(Md^2)$. At a prime $p\mid M$ the local factor changes from $1-1/p^2$ to $1-1/p$, and $1/M$ supplies $1/q$ for $q=p^e\parallel M$. We obtain

$$\left|P_M-K\prod_{p^e\parallel M}\frac{p}{p^e(p+1)}\right|\le E.$$

In particular $|P_1-K|\le E$. The Euler product here is evaluated at the absolutely convergent point 2. This argument is unconditional. [Mathlib's Euler product](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/EulerProduct/DirichletLSeries.html)

For a list of $s$ obstructions let $w_q=p/[q(p+1)]$, $\rho=\prod_q(1-w_q)$, $u=\sum_q w_q$, $B=\sum_{i=0}^{18}\binom{s}{i}$ and $\epsilon=E/K$. Use inclusion–exclusion up to orders 17 and 18 to bracket the count of surviving pairs. In each truncated sum, replacing $P_M/K$ by its product costs at most $B\epsilon$. The two ideal truncated sums bracket $\rho$ and differ by at most $u^{18}/18!$. Dividing by the actual primitive population $P_1$ then bounds the distance between the finite surviving fraction and $\rho$ by

$$\frac{u^{18}/18!+(B+1)\epsilon}{1-\epsilon}.$$

For the computations we bound $\zeta(2)<2$ by summing $1/n^2$ against the integral tail, and use $1+\ln J\le1+\operatorname{bitlength}(J)$. The program performs all products with outward integer rounding and all subsequent bounds with rational arithmetic. A lower bound for the number of remaining pairs comes from $K>cJ^2/4$, $P_1\ge K(1-\epsilon)$ and the lower surviving fraction. [Exact arithmetic](../experiments/complete_offset_density.py)


```sh
python3 -m experiments.complete_offset_density
python3 -m experiments.complete_offset_filter --controls --max-pairs 64
python3 -m experiments.complete_offset_filter --timings
```
