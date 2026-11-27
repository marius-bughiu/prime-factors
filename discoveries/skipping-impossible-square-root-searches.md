# Skipping impossible searches for a square root

Given only 246,180,296,426,219, we found two square roots of 3 whose difference shares a prime with the input. Testing a local congruence before each continued-fraction search reduced the work from **34,830 to 5,902 updates**. Both versions found **15,230,737 × 16,163,387**. On each 2,048-bit comparison the same rule reduced 33,536 updates to 8,960, and neither version found a root of its chosen target.

## Why entire multipliers can be dropped

Choose the smallest positive squarefree product $D>1$ of the primes $2,3,5,7,11$ with Jacobi sign $+1$ at $N$. Our test products are coprime to these primes. The sign is necessary for a root at both hidden primes. We search the continued fraction of $\sqrt{kN}$ for a primitive convergent $X/Y$ with positive norm

$$X^2-kNY^2=DT^2.$$

If $T$ is invertible modulo $N$, then $X/T$ is a square root of $D$ there. If two roots differ by a multiple of one hidden prime and agree up to the opposite sign at the other, the gcd of their difference with $N$ returns a factor. Continued-fraction factorization and the use of multiple square roots are classical. The rule here targets a specific square class and discards entire walks that could never produce that class. [Classical continued-fraction algorithm](https://doi.org/10.1090/S0025-5718-1975-0371800-5) · [Targeted search](../experiments/target_norm_multipliers.py)

For a prime $\ell$ dividing $k$ **exactly once** and missing $N$, the coordinate $T$ must be invertible modulo $\ell$. Indeed $\ell\mid T$ would imply $\ell\mid X$, hence $\ell^2\mid kNY^2$, forcing $\ell\mid Y$ and contradicting primitivity. Thus $D$ must be a square modulo $\ell$. Also, modulo every divisor of $D$, $kN$ must be a square because $Y$ is invertible there. Finally $X$ and $Y$ cannot both be even. Checking the four square residues modulo 16 with this parity condition gives a third rejection test. Every rejection excludes the equation for all convergents of that multiplier, even arbitrarily deep ones. A rejected walk could still give evidence about some *other* square class. [Lean proofs](../PrimeFactors/TargetNormMultiplier.lean)

For the worked example the product selects $D=3$. At $k=167$, step 168 yields the positive remainder $84{,}875{,}283=3\cdot5319^2$ and the public root 189,325,693,069,900. At $k=299$, step 14 gives the root 156,855,619,935,814. The gcd of their difference with the input is 15,230,737. Of the 137 squarefree multipliers coprime to $3N$ reached up to this point, the filter rejected 113. Under a common cap of 8,192 updates the filtered search already has both factors, whereas the unfiltered version has yet to find its first target root. Median CPU time on this example fell from 12.48 to 2.63 ms. The earlier sum search finished in 0.21 ms. [Exact benchmark](../benchmarks/target-norm-multipliers.json) · [Earlier sum comparison](combining-remainders-to-skip-divisors.md)

## What changed on independent prime pairs?

We fixed a ceiling of 320 multipliers and 256 steps per walk after developing the method on the 48-bit example. For each method we checked its first target root, its split if any, its work through that point, and every failure. The table uses the last six pairs at each width from the project's existing independent small-prime panels. Their outcomes had already been published for other methods.

| Prime width | Target roots found | Products split | Updates before → after | Six-product CPU before → after |
|---|---:|---:|---:|---:|
| 20 bits | 3 of 6 | 3 of 6 | 153,600 → 37,632 | 57.22 → 16.20 ms |
| 24 bits | 4 of 6 | 3 of 6 | 160,596 → 41,556 | 58.52 → 17.12 ms |
| 1,024 bits, fresh control | 0 | 0 | 33,536 → 8,960 | 103.30 → 28.04 ms |
| 1,024 bits, crossed control | 0 | 0 | 33,536 → 8,960 | 102.96 → 28.30 ms |

All 24 small inputs and the two full-size inputs produced identical first target roots and target split outcomes in the two versions. The timed runs include target selection, multiplier screening, continued fractions and root readout. An additional untimed comparison checked gcds for unrelated divisors in every visited row. The limits concern this bounded, target-specific search. These experiments give no working multiplier for the two full-size controls. [Measurements, misses and work counts](../research/target-norm-multipliers.json) · [Replay](../experiments/target_norm_multipliers.py)

## How many multipliers can ever work?

There is a stronger count for the full-size examples' target $D=2$. For any fixed odd input $N$, a prime $\ell\equiv3,5\pmod8$ with $\ell\nmid N$ sees 2 as a nonsquare. So no working $k$ can contain exactly one factor of $\ell$. Of the $\ell^2$ residues modulo $\ell^2$, exactly $\ell-1$ contain it exactly once. For a finite collection $F$ of such primes, the Chinese remainder theorem bounds the fraction of residues that may work in each complete period by

$$\prod_{\ell\in F}\left(1-\frac{\ell-1}{\ell^2}\right).$$

This bound tends to zero as $F$ takes more primes in the two indicated classes. Mertens' theorem in arithmetic progressions gives divergence of the sum of their reciprocals. The sum of their inverse squares converges, and excluding the finitely many primes dividing $N$ has no effect. For any desired positive fraction, first fix $F$ to make the bound smaller, then let the multiplier ceiling grow to absorb the last partial period. Hence **the multipliers capable of representing the target have natural density zero among all positive integers**. This also applies to nonsquarefree multipliers. It does not bound how soon a useful root appears or how often it splits the input. Lean verifies the finite product and its connection to every primitive solution. The limiting deduction uses the published analytic theorem. [Finite CRT count](../PrimeFactors/TargetNormMultiplierDensity.lean) [Williams, *Mertens’ theorem for arithmetic progressions*](https://people.math.carleton.ca/~williams/papers/pdf/057.pdf)
