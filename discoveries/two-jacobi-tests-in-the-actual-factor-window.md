# Two Jacobi tests in the actual factor window

For the two 2048-bit comparison products, a pair of tests computed from each product limits where its smaller prime can be. Starting with the candidates coprime to 60, we obtained the following upper bounds over the **whole possible interval**. Both products remain unresolved. [Exact integer counts and public witnesses](../research/two-character-windows.json)

| Input | One Jacobi test, upper bound | Both tests, upper bound |
| --- | ---: | ---: |
| Fresh comparison product | 50.0072% | **33.7461%** |
| Crossed comparison product | 50.0002% | **26.5876%** |

These are bounds on candidate counts. Checking every surviving integer could still take roughly $10^{306}$ trials under the new ceilings. The comparison measures how much of the interval the tests can retain. It gives no measured speedup for finding either actual factor.

## Why both tests keep the smaller prime

Suppose $N=pq$ with $p\le q\le B=2^{1024}-1$. Then $p$ lies between $\lceil N/B\rceil$ and $\lfloor\sqrt N\rfloor$, inclusive. A bounded continued-fraction search supplies two coprime moduli $a,b$, each congruent to 3 modulo 4, with public square roots of $-a$ and $-b$ modulo $N$. Both moduli are coprime to $60N$. Quadratic reciprocity gives $(p/a)=(p/b)=1$, where the parentheses denote Jacobi symbols. The proof also applies to any odd divisor coprime to both moduli. [Divisor theorem](../PrimeFactors/ReciprocalDivisorClasses.lean)

## Counting before a full joint period

Write $\chi_d(x)=(x/d)$. At each integer $x$, the indicator that both tests pass is at most $(1+\chi_a(x))(1+\chi_b(x))/4$. This also holds if a symbol vanishes. Summing the product bound over a residue class modulo 60 produces three character sums, with moduli $a$, $b$ and $ab$. Multiplication by the invertible stride 60 converts each to a translated consecutive sum up to a sign. The joint period $ab$ can exceed the entire search window.

Frolenkov and Soundararajan's Corollary 1 bounds any consecutive sum of a nonprincipal character modulo $d\ge100$ in absolute value by $E(d)=\sqrt d\,[(\log d+6)/(\pi\sqrt2)+1]$. It allows imprimitive characters. Each receipt exhibits an integer with Jacobi symbol $-1$ at each of the three moduli. A residue class containing $L$ candidate positions therefore contributes at most $(L+E(a)+E(b)+E(ab))/4$. [Original paper](https://doi.org/10.1007/s11139-012-9462-y) · [Explicit statement in Johnston, Ramaré and Trudgian, Lemma 13](https://ramare-olivier.github.io/Maths/JRT_Submitted.pdf#page=5)

Lean takes the published interval inequality as an explicit hypothesis. It verifies the indicator bound, stride conversion, factor inclusion, all 16 wheel classes, conservative integer rounding of the three errors, and the aggregate percentages. Reproduce both numeric certificates with `python3 -m experiments.two_character_window --verify` after `lake build`. The search uses 32,768 continued-fraction steps for each input, followed by recovery and verification of the two selected roots. The result depends on the two moduli the search found for each particular input. [Lean module](../PrimeFactors/TwoCharacterWindow.lean) · [Reproducer](../experiments/two_character_window.py)
