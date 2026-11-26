# How often does one number distinguish the true factor sum?

Pick two distinct 1,024-bit primes uniformly, keeping only 2,048-bit products. Given the product $N$, pick one number $g$ uniformly among the residues coprime to $N$. The chance that **any two sums** in the standard balanced interval give the same remainder $g^s\bmod N$ is below **one in $2^{972}$**. This is a statement about random inputs *and* a random base. For every individual product the earlier two-base guarantee remains available. [Lean theorem for one base](../PrimeFactors/SingleBasePopulation.lean) · [Two-base theorem and table costs](reading-the-factor-sum.md)

The right sum $S=p+q$ always satisfies $g^S=g^{N+1}\pmod N$. Thus one modular power per table entry almost always suffices for this sampling experiment. The table search still has to locate the sum. Its complete lists on our two full-size comparisons both exceed $2^{449}$ entries combined. A square test already recognizes $S$ if someone gives it to us. The purpose of the modular test is to compare many possible sums in one table lookup.

## Counting all the ways a repeat could happen

Let $X=2^{1023}$. For a specified positive gap $e$, exactly $\gcd(e,p-1)\gcd(e,q-1)$ bases satisfy $g^e=1\pmod{pq}$. Each prime has a cyclic group of units, and the Chinese remainder theorem combines their roots. A repeat anywhere in the interval requires such an $e$ no larger than its diameter $W$. [Exact count at a fixed gap](../PrimeFactors/SingleBaseRepeat.lean)

Write $\tau(e)$ for the number of divisors of $e$. Summing $\gcd(e,p-1)$ over candidate primes in $[X,2X)$ costs at most $2X\tau(e)$. Each divisor $d$ can divide at most $\lfloor2X/d\rfloor$ positive predecessors and contributes at most $d$ per occurrence in this upper bound. For sorted distinct pairs the two-factor sum is at most half the square of the single-factor sum. Each product has at least $X^2$ units. Dividing separately by its unit-group size before averaging gives

$$\Pr(\text{repeat})\;\le\;\frac{2}{\#\text{eligible pairs}}\sum_{e\le2^{1021}}\tau(e)^2.$$

Here $W\le2^{1021}$ for every eligible product. For any $Y\le2^b$, Lean verifies $\sum_{e\le Y}\tau(e)^2\le Y\binom{b+3}{3}$. Two divisors of $e$ determine an ordered factorization into four positive integers by taking their gcd, their two coprime quotients and the remaining factor. Group the first three factors by the integer parts of their binary logarithms. The three indices sum to at most $b$, and each such group contributes at most $Y$ possibilities including the fourth factor. Taking $b=1021$ gives $\binom{1024}{3}=178{,}433{,}024$. The final inequality uses the same unconditional Rosser–Schoenfeld prime-count input as our other finite population estimates. [Divisor-moment proof](../PrimeFactors/DivisorSecondMoment.lean) · [Population and analytic input](predicting-a-carry-from-both-ends.md#what-the-rule-sees)

## Reusing one random seed

Choose one integer $G=1+u$ with $u$ uniform among the $2^{1152}$ possible bit strings, independently of the prime pair. Since $0<G<N$, a nontrivial gcd with $N$ is already a proper factor. Otherwise the seed maps injectively into the unit group as it varies over the allowed range. Giving this seed range only a fraction of the full residue space weakens the joint failure bound to $2^{-76}$. Double counting shows that fewer than one in $2^{38}$ seeds collides on as much as a $2^{-38}$ fraction of eligible products. A prescribed seed needs its own check. [Reusable-base theorem](../PrimeFactors/ReusableSumBase.lean)

## What happens if we always use 2?

The random-base theorem leaves this question open for a prescribed constant. A finite test is available when we know enough about the two local orders $r=\operatorname{ord}_p(2)$ and $t=\operatorname{ord}_q(2)$. The period modulo $pq$ is their least common multiple. Since $\gcd(r,t)$ divides $\gcd(p-1,q-1)$, the strict inequality $rt>W\gcd(p-1,q-1)$ suffices to exclude a repeat. [Lean fixed-base criterion](../PrimeFactors/FixedBaseSignature.lean)

**One complete check at 2,048 bits.** On the existing independently constructed comparison, even the single fixed base 2 provably distinguishes the true sum from every other integer in the balanced interval. The two prime-generation chains supply distinct 513-bit primes that divide the two local orders of 2. Their product is 1,026 bits and exceeds the interval diameter by a factor greater than 21. Lean checks the modular powers, the orders they force, both endpoints, and the resulting equivalence for every candidate sum. The original construction deliberately required these base-2 order witnesses in order to certify primality. We used the published factors and generation record for this diagnosis. The capped search on the very same product still produced no factor. [Regenerable Lean certificate](../benchmarks/controls/PocklingtonControl.lean) · [Construction and assumptions](certified-fresh-control.md)

We checked the full set of distinct prime pairs at several small sizes, conditioning on a product with twice the factor bit length. A repeat somewhere in the interval can occur between two wrong sums. The last column counts the subset where a wrong sum actually matches the true target.

| Bits per prime | Eligible pairs | Some two powers of 2 match | A wrong sum matches the target |
| ---: | ---: | ---: | ---: |
| 9 | 543 | 0 | 0 |
| 10 | 1,718 | 0 | 0 |
| 11 | 5,530 | 0 | 0 |
| 12 | 19,546 | 6 | 5 |
| 13 | 64,719 | 17 | 12 |
| 14 | 228,713 | 27 | 17 |

For example $8{,}842{,}111=2351\cdot3761$. In the interval $[5948,6307]$, the true sum 6112 and the false sum 6300 give the same remainder $5{,}844{,}590$ at base 2. The false sum fails the separate local sieve modulo 3. [Lean counterexample](../PrimeFactors/FixedBaseSignature.lean)

The census is reproducible with the following integer calculation.

~~~python
from itertools import combinations
from math import isqrt, lcm

for bits in range(9, 15):
    x = 1 << (bits-1)
    order = {}
    for p in range(x+1, 2*x, 2):
        if any(p % d == 0 for d in range(3, isqrt(p)+1, 2)):
            continue
        r, power = 1, 2
        while power != 1:
            r, power = r+1, (2*power) % p
        order[p] = r
    eligible = repeats = wrong = 0
    for p, q in combinations(order, 2):
        n = p*q
        if n < 2*x*x:
            continue
        lo, hi = 1+isqrt(4*n-1), isqrt(9*n//2)
        period = lcm(order[p], order[q])
        eligible += 1
        repeats += period <= hi-lo
        wrong += period <= max(p+q-lo, hi-p-q)
    print(bits, eligible, repeats, wrong)
~~~

As factor size tends to infinity, **base 2 alone separates the interval for a fraction of eligible pairs tending to one**. This is a paper deduction from Pappalardi's unconditional rank-one result. Outside a density-zero set of primes, the order exceeds $\sqrt p(\log p)^2$. For $p,q\in[X,2X)$, pairs with $\gcd(p-1,q-1)>T$ number at most $\sum_{d>T}\lfloor2X/d\rfloor^2=O(X^2/T)$. Pick $T=(\log X)^3$. The prime number theorem supplies order $X^2/(\log X)^2$ eligible pairs, for instance already from the primes in $[1.5X,2X)$. The large-gcd exceptions and pairs containing an exceptional prime therefore have vanishing fraction. For the remaining pairs the joint period exceeds $\sqrt{pq}\log X$, which covers the interval diameter. This asymptotic argument gives no numerical failure rate for base 2 at 1,024 bits per prime. [Pappalardi, 1996](https://iris.uniroma3.it/handle/11590/141125) · [Finite order criterion](../PrimeFactors/FixedBaseSignature.lean)

## Doing less work per table entry

The first implementation raised the base to each table exponent separately. A child entry is formed by adding one local contribution to its parent's residue modulo the period. That addition wraps at most once. We now precompute the powers for both possible contributions, then use multiplication to form the child signature. This works on both lists, including the one whose exponent decreases when a digit is added. Each local digit needs at most one exponentiation per base, plus a fixed number per list and base. Each edge in the enumeration needs at most one component multiplication per base after setup. Both implementations still build the entire list. [Lean update identities](../PrimeFactors/SignatureUpdates.lean) · [Implementation](../experiments/sum_signature_join.py)

| Same 52-bit input and factor result | Full modular powers | Modular multiplications outside those powers | Additional inversions modulo the product |
| --- | ---: | ---: | ---: |
| Two bases, direct powers | 866 | 432 | 0 |
| Two bases, reused digit powers | 78 | 1,484 | 2 |
| One base (3), direct powers | 433 | 216 | 0 |
| One base (3), reused digit powers | 39 | 742 | 1 |

All four runs checked 15,902 local survivors, found one matching sum, and recovered the same two primes. On the small ambiguous example 109,969, the revised calculation still needed seven powers and used ten multiplications outside them, up from two. Both full-size comparisons still stopped at the table cap before exponentiation. The fixtures record setup, table operations, remaining cofactors and certificates. [Comparison fixtures](../benchmarks/sum-signature.json)

We froze two additional inputs with 40-bit and 44-bit factors before running either search. Both used only the product and base 2. On the 80-bit product the lists contained 7,200 and 7,056 entries and represented 14,419,339 admissible sums. Reuse cut 14,257 powers to 78 and recovered **864,821,852,333 × 1,018,267,251,481**. On the 88-bit product the lists contained 40,824 and 51,840 entries and represented **254,689,123** admissible sums. There was exactly one match, giving **14,430,605,773,673 × 15,019,712,637,103**. Full modular powers fell from **92,665 to 98**, while explicit modular multiplications outside those powers rose from 40,824 to 133,997. On one local comparison the times were about 0.65 and 0.17 CPU seconds. Timings vary with hardware. The exact operation counts and Lean certificates are reproducible. [Holdout fixtures](../benchmarks/sum-signature.json)

For a factor width $b$ and side name `left` or `right`, take the big-endian integer SHA-256 digest of the UTF-8 string `prime-factors/single-base-sum/holdout-v1/{b}/{side}`. Reduce it modulo $2^{b-2}$, add $3\cdot2^{b-2}$, set the low bit and take the first prime at or above that integer. The two widths, both side names, base 2 and the cap of 65,536 entries per side were fixed for these two examples. No pairs were skipped.
