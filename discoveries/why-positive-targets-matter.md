# A product for which every negative target on the list fails

The search on ellipses tries to write multiples of a public number as $x^2+d y^2$ with $d>0$. Sometimes every choice from a large list is impossible, regardless of how far we search. For 2,336,879 this happens with every $d$ made by multiplying any number of primes up through 31, repetitions included. The signed search selects 2, 3 and 6. The very first target gives two useful solutions. [Lean proof and exact primes](../PrimeFactors/NegativeTargetObstruction.lean) · [Native benchmark](../benchmarks/signed-norm-arcs.json)

Here are the two solutions for $D=2$.

$$1679^2-2\cdot491^2=1721^2-2\cdot559^2=2{,}336{,}879.$$

The greatest common divisor of $1679\cdot559-1721\cdot491$ and the input is 1,871. Division gives 1,249. The worked input was selected to exercise the limitation of the earlier search. An independent eight-input comparison measures costs at two larger sizes. [Complete search measurements](scanning-signed-norm-arcs.md)

## Why changing the multiplier cannot rescue the negative targets

A point on $x^2+d y^2=mN$ whose denominator $y$ is invertible modulo $N$ would give a square root of $-d$ by division. But $N$ leaves remainder 3 modulo 4, so the Jacobi sign of $-1$ is negative. Every positive prime up through 31 has positive Jacobi sign at this $N$. Multiplying any selection of them preserves that positive sign, and multiplying by $-1$ makes it negative. Every modular square has nonnegative Jacobi sign. This rules out every such root, for every $m$. If a denominator already shares a proper divisor with $N$, the gcd itself yields a factor. Earlier implementations also check for such direct divisors. [General word exclusion](../PrimeFactors/NegativeTargetObstruction.lean) · [Earlier target selector](../experiments/norm_directions.py)

On the fresh 2,048-bit comparison, the new rule guarantees at least one viable target, and the complete search visits more than $2^{685}$ blocks. We tested 64. No factor was found. The asymptotic bound of $O(N^{1/3})$ blocks improves on direct enumeration of these curves. Other deterministic integer factorization methods have published bounds with a smaller exponent. [Full-size budget and search results](../research/signed-norm-arcs.json) · [Harvey, exponent one-fifth algorithm](https://arxiv.org/abs/2010.05450)
