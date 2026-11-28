# What shifted marks tell us about the two primes

Take the product 77 and the target 2. Mark an integer $x$ if $x^2-2$ shares a factor with 77. The marked coordinates are exactly those congruent to 3 or 4 modulo 7. There are 22 in one cycle of length 77. Shift that set by one position and 11 marks overlap. The gcd of $1^2-4\cdot 2$ and 77 is 7, so we can compute the overlap as $77/7=11$ without listing the 77 positions. Finding a shift that produces a useful gcd still costs work. [Lean proof](../PrimeFactors/CircleMarkAutocorrelation.lean) · [All 77 shifts](../benchmarks/circle-mark-spacing.json)

## One target and two marked classes

Let $N=pq$ for distinct odd primes. Choose a target $a$ with Jacobi symbol $-1$, which can be checked from the product. Exactly one prime admits a square root of $a$. Call it $p$ for this derivation. Its two roots give the two marked classes modulo $p$. Each class occurs $q$ times in the full cycle. A shift of $h$ therefore gives the following counts. [Autocorrelation](../PrimeFactors/CircleMarkAutocorrelation.lean)

| Shift modulo the square-side prime $p$ | Number of starts marked at both ends |
| --- | ---: |
| $h=0\pmod p$ | $2q$ |
| $h^2=4a\pmod p$ | $q$ |
| All other shifts | 0 |

When $h$ is coprime to $N$, compute $g=\gcd(N,|h^2-4a|)$. The answer is zero if $g=1$, and $N/g$ otherwise. Since 2 is invertible modulo the odd product, the informative shift is exactly an ordinary mark at $h/2\pmod N$. [Gcd formula and equivalence](../PrimeFactors/CircleMarkAutocorrelation.lean)

The shorter distance $s$ between the two marked classes can be anywhere from 1 through $(p-1)/2$ as the target varies. For the first $L<p/2$ positive shifts, the sum of overlap counts is $q$ if $s\le L$ and zero otherwise. Weight shift $h$ by $L+1-h$ and the sum becomes $q\max(0,L+1-s)$. Modulo 39, targets 14 and 17 give distances 2 and 4. Through shift 4 their ordinary totals are both 3, while the weighted totals are 9 and 3. These are identities for the exact aggregates. A cheaper way to obtain an aggregate that reveals the distance remains open. [Weighted counts and actual window moments](../PrimeFactors/CircleMarkWindows.lean)

## Two targets can ask a harder question

Mark the starting coordinate using $a$, and the shifted coordinate using $b$, both with Jacobi symbol $-1$. If their square roots occur at different primes, the Chinese remainder theorem gives exactly four marked starts at **every** shift. If the square roots occur at the same prime, the count is divisible by the other odd prime and cannot equal four. In particular, for any $z$ of Jacobi symbol $+1$, choosing $b=az$ gives four exactly when $z$ has no square root modulo $N$. A method that quickly answers the four-count question for arbitrary inputs would therefore decide quadratic residuosity on these inputs. The reduction gives no running-time lower bound. [Lean reduction](../PrimeFactors/CircleMarkCrossTargets.lean) · [Goldwasser and Micali on quadratic residuosity](https://www.sciencedirect.com/science/article/pii/0022000084900709)

There is a case that we *can* compute. Choose $b=ad^2$ ourselves, with $d$ a unit modulo $N$. Both targets have roots at the same prime. For a coprime shift take the gcd of $N$ with

$$
(h^2-a(d-1)^2)(h^2-a(d+1)^2).
$$

A proper gcd gives one prime, and the overlap equals the other. A gcd of one gives zero. With $N=77,a=2,b=8$, shift 3 yields gcd 7 and count 11. Shift 1 yields gcd 1 and count zero. Using $b=3$ instead gives four at every shift. [Resultant and examples](../PrimeFactors/CircleMarkResultant.lean) · [Direct census](../benchmarks/circle-mark-spacing.json)

## What one gcd buys

Fix the product and choose the target uniformly from **all** residues of negative Jacobi symbol. For a predetermined set of coordinates, write $c_p$ and $c_q$ for the numbers of distinct nonzero squares these coordinates represent at the two primes. The exact hit probability is $c_p/(p-1)+c_q/(q-1)$. Among sets of at most $L$ coordinates, the ordinary set 1 through $L$ attains the largest probability. Changing which of $K$ predetermined sets to test after seeing the target still cannot beat testing their union. For 1,024-bit primes and $K,L\le2^{64}$, the hit probability is below $2^{-893}$. A strategy that deliberately chooses a small target has a different distribution. [Fixed-product proof](../PrimeFactors/CircleMarkTargetFrequency.lean) · [Small targets chosen from the product](which-marked-coordinate-tests-can-be-skipped.md)

Choose $d=2L$ in the two-target formula. If $2(2L+1)L<\min(p,q)$, testing the first $J\le L$ shifts covers as many targets as testing $2J$ ordinary consecutive coordinates. Two ordinary differences can also be multiplied before taking one gcd. Since a negative-Jacobi target has roots at only one prime, this product cannot hide a hit by including both factors of $N$. Thus the two methods have exactly the same distribution of the first successful gcd, including misses, over the stated target population. They can succeed on different individual targets. [Lean coverage proof and a small-modulus exception](../PrimeFactors/CircleMarkPackedMenu.lean)

| Product | Targets tested | Gcd budget per target | One coordinate per gcd | Two scaled coordinates per gcd | Two consecutive coordinates per gcd |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 77 | 30 | 1 | 8 hits | 16 | 16 |
| 7,387 | 3,608 | 4 | 340 hits | 680 | 680 |
| 82,919 | 41,172 | 8 | 2,296 hits | 4,592 | 4,592 |

At 7,387, the scaled rule finds a factor on its third gcd for target 2 while the consecutive pair misses within four. Target 92 reverses the outcome. Both examples were selected after checking all targets. An ascending target search encounters the factor 83 itself before it reaches 92. At 82,919 the two paired methods each used 313,304 search gcds, stopping each target at its first hit. This comparison counts gcds, with different arithmetic needed to construct their inputs. [Census and first-hit ranks](../benchmarks/circle-mark-spacing.json) · [Reproduction and certificate checks](../experiments/circle_mark_spacing.py)
