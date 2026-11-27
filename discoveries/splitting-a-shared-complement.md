# When the same complementary label hides two different matches

Two public tests on 1,040,279 gave gcds of one and the entire input. Looking inside the second test found **1,009 × 1,031**. Both seeds, 4 and 11, came from a scan of pairs of small integers. This new step also recovered two additional products in the existing exhaustive panel of 19,546 products of 12-bit primes. [Lean proof and exact small example](../PrimeFactors/ComplementaryNormBranches.lean) · [Search implementation](../experiments/complementary_keys.py)

## Why a shared label can split

For the existing rational label, write $v(x)=A(x)/B(x)$. Suppose that $v(x)+v(y)=1$ modulo the whole product. Removing the denominators gives $A(x)B(y)+A(y)B(x)-B(x)B(y)=0$. The two hidden primes can make different factors of that expression vanish.

There are six factors. For each of $(u,v)=(xy+3,x-y)$ and $(u,v)=(3-xy,x+y)$ take the following three integers.
$$
u^2-3v^2,\qquad (u+3v)^2-12v^2,\qquad (u-3v)^2-12v^2 .
$$
Their product is exactly the cleared expression. Every factor has the form $a^2-3b^2=(a+b\sqrt3)(a-b\sqrt3)$, so it tests both choices of square root at once. Computing any of them requires only integer arithmetic. [Integral identities and equivalence for unit denominators](../PrimeFactors/ComplementaryNormBranches.lean)

For seeds 4 and 11 on 1,040,279 the original labels are 1,001,365 and 38,915. Their difference is coprime to the input. Their sum is one modulo the input. The six individual gcds, in the displayed order, are **1,031, 1, 1,009, 1, 1, 1**. The search stops on the first proper divisor. If an individual label is exactly its own complement modulo the product, the same calculation also works with the seed paired with itself. [Regression tests for two distinct seeds and a singleton](../tests/test_complementary_norm_branches.py)

The six forms usually resolve a global complement tie when three is a square at both primes. Fix one regular seed. Each prime has twelve possible complementary partners, giving 144 partner residues by the Chinese remainder theorem. A single norm has degree at most two in the partner seed. Since the six forms cover twelve distinct residues at each prime, each form accounts for exactly two and their sets are disjoint. Exactly $6\cdot2\cdot2=24$ partners have a common branch at both primes. **Exactly 120 of the 144 complementary partners therefore reveal a factor by a norm gcd.** This is conditional on obtaining a global complement tie in the first place. [Finite partner count and separating branch](../PrimeFactors/ComplementaryNormBranches.lean)

At 12-bit prime width the six extra gcd calls across the entire panel supplied two additional splits. For 8,740,307 the third branch found 3,467. For 11,653,547 the first found 3,457. In each case, disabling only the six-form refinement leaves the product unresolved on those same twelve draws. None of the 20-bit or 24-bit holdouts reached the new gcd calls. Both existing 2048-bit controls missed under their original budgets. [Matched panel](../research/complementary-key-panel.json)

## Can we choose the match in advance?

There is a tempting way to pick $y$ from a trial square root $t$. Put $y=(tx-3)/(x+t)$ so the first branch should vanish if $t^2=3$. Substitution gives the exact identity
$$
(x+t)^2\big((xy+3)^2-3(x-y)^2\big)=(t^2-3)(x^2+3)^2 .
$$
For an invertible denominator and an invertible $x^2+3$, the resulting gcd is precisely $\gcd(N,t^2-3)$. Reusing the same $t$ with many seeds repeats this observation. The proof covers rational approximations $t=r/s$ and all six branches in homogeneous coordinates. In particular, any Pell approximation satisfying $r^2-3s^2=1$ gives gcd one under the stated unit conditions. [Proof for equivalent gcds](../PrimeFactors/ComplementaryNormBranches.lean)

We tried a product-dependent rule, $t=\lfloor\sqrt{aN+3}\rfloor+\delta$, for $1\le a\le256$ and $\delta=-1,0,1$. We compared the direct gcd with the three different forced projective quadratics at $x=2$. On the 20-bit control all three agreed with the direct test at each trial. The 440th direct gcd found 1,009 in 1,022,117, and the three-form comparison took 1,320 gcds. On each 2048-bit control, all 768 direct and 2,304 forced gcds agreed and missed. The rule and arithmetic cap were the same for all three products. [Reproduce the experiment](../experiments/complementary_norm_roots.py)

We can also rule out a deterministic family of small seeds. Every integer form above is nonzero, and its absolute value is at most $((|x|+4)(|y|+4))^2$. In particular, two signed seeds of magnitude at most $2^{255}$ cannot produce any complementary match at a 1024-bit prime. The remaining question is how to choose larger seeds for which the hidden primes select different norm branches. The measured panel gains occur after a global tie has already been found. [Formal size exclusion](../PrimeFactors/ComplementaryNormBranches.lean)
