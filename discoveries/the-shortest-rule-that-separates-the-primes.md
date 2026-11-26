# The shortest repeating rule that separates the primes

For 323, take the remainders 1, 2, 5, 16, 19 and 20 modulo 21. Between 16 and 31 the matching numbers are 16, 19, 20, 22, 23 and 26. Their product has gcd 19 with 323. The group also has a symmetry. Whenever it contains a remainder $r$, it contains $21-r$. Both the symmetry and the separation can be found from 323 alone. [Lean calculation](../PrimeFactors/SymmetricDivisorSelector.lean)

## When a rule exists

Suppose $N$ is a product of two distinct primes in the same known interval $[B,2B)$, and choose a period $W$ coprime to $N$. Each possible remainder $x$ coprime to $W$ has one partner $y=N/x\pmod W$. We want a rule that selects exactly one from **every** such pair, so it works whichever pair the primes occupy.

* An unrestricted rule exists exactly when $N$ has no square root modulo $W$. Otherwise some pair has identical remainders. When all partners are distinct, select the smaller remainder in each pair.
* A rule that also keeps $x$ and $-x$ together exists exactly when **neither $N$ nor $-N$ has a square root modulo $W$**. To build it, give each remainder the rank $\min(x,W-x)$, using representatives from 1 to $W-1$. Select the member of each partner pair with smaller rank. The two ranks coincide only if $y=x$ or $y=-x$, which are precisely the two square obstructions. The complement of either rule works as well. [Construction and sharp criteria](../PrimeFactors/SymmetricDivisorSelector.lean)

Reflection can make the group product cheaper to represent. In one wheel cycle the selected offsets $a$ and $W-a$ contribute $(X+a)(X+W-a)=X(X+W)+a(W-a)$. For a positive Jacobi selector on a period divisible by four times its magnitude, this gives a polynomial of degree exactly $\varphi(W)/4$ in $X(X+W)$. A negative Jacobi selector swaps signs under that reflection, though another reflection can still work. The earlier interpolation that pairs separate blocks works with any fixed mask. Its savings and this degree identity cannot simply be multiplied. [Reflection and degree proof](../PrimeFactors/CharacterColumnReflection.lean) · [Existing paired-block algorithm](folded-factorial.md)

## Finding the least period

A unit is a square modulo an odd prime power exactly when it is a square modulo its prime. For powers of two, the tests modulo 4 and 8 suffice. The Chinese remainder theorem combines these tests. Consequently every working modulus contains a divisor equal to 4, 8 or an odd prime witnessing the failure of the square test. A reflected rule can use two different witnesses, one for each sign. In the 323 example, 323 is a nonsquare modulo 3, and −323 is a nonsquare modulo 7. Neither constituent modulus permits reflection and separation together. Their product does. [Proof for arbitrary positive periods](../PrimeFactors/LeastSeparatingModulus.lean)

We tried multiples of the existing wheel of 30 in ascending order, caching each small test. Once a period succeeds, we count both complementary groups over the possible range of either factor and evaluate the smaller group with the forward block algorithm. On the third product in the original 60-bit panel the unrestricted rule used period 30 and recovered 686,073,211. Requiring reflection raised the least period to 330 and recovered the other prime, 1,043,950,709. The forward evaluator used 37,814 and 34,428 polynomial input coefficients respectively. The longer period also sieves multiples of 11. These measurements use the forward evaluator in both cases. [Reproducible search](../experiments/separating_period.py) · [Benchmark cases and expected factors](../benchmarks/separating-period.json)

On the fresh 2,048-bit input, 60 is the shortest multiple of 30 permitting reflection and separation. On the crossed input, the least such period is 330, down from the previous sign rule's period of 660. Lean checked that the selected periods work and every smaller coprime multiple fails the required test on each input. Both group products exceeded the two-million-unit evaluation budget before the first candidate. The least-period proof gives no factor on either input.

## Does the shorter rule find factors faster?

In an initial experiment on eight 60-bit products, a Jacobi group used 6.67% fewer polynomial input coefficients than searching the smaller-factor interval when both used wheel 210 and the same forward search that checks for factors as each block is built. On wheel 30 the ordinary interval used fewer coefficients. Folding whole blocks and evaluating them completely favored the ordinary interval on each of the eight products at both wheel settings. [Matched searches and counts](../research/character-column-backends.json)

We froze wheel 210, the forward search with growing blocks, the two-million-unit budget, and the seed for 32 new 60-bit products. On these inputs the initial saving reversed. A follow-up applied the least-period rule to the same 32 products, using the smaller complementary group by candidate count. Search used only the products. Lean checked the factors found. [Independent Jacobi validation](../research/character-growing-validation.json) · [Least-period follow-up](../research/least-period-growing.json)

| Search on the 32 products | Pairs recovered | Polynomial input coefficients | Charged arithmetic units |
|---|---:|---:|---:|
| Ordinary smaller-factor interval | 32 | 837,596 | 8,886,442 |
| Original Jacobi group | 31 | 910,762 | 10,822,114 |
| Least-period group | 32 | 936,604 | 10,301,836 |

The missed product was 636,051,676,003,808,521. The original group's period of 4,620 gave a conservative cost estimate of 2,003,122, just over budget, so that run stopped before interpolation. The shortest rule used period 2,310 and recovered 892,242,809. Across all 32 products the shortest rule still used 11.8% more polynomial inputs and 15.9% more charged arithmetic than the ordinary search. These units track the operations listed in the replay, including preprocessing and polynomial evaluation. [Search, charging rules and comparison](../experiments/least_period_growing.py)
