# How far can factorial blocks be folded?

The factorial search multiplies possible divisors in blocks. A block moving right and another moving left can share the address $j(j+1)$. This halves the polynomial degree needed to represent the two blocks. Could three or four blocks share a higher-degree address? For equal strides up to sign, **degree two is the maximum** whenever the stride is a unit modulo the input and the number of blocks is nonzero modulo the input. This limits one proposed shortcut in a Pollard–Strassen interval search. Other ways to evaluate its product remain possible. [Existing algorithm and timings](folded-factorial.md) · [Costa and Harvey on deterministic interval products](https://arxiv.org/abs/1201.2116)

## Why a cubic address is different

Write $x$ for the common offset and $t$ for the block index. Suppose block $i$ contributes $x+a_i+s_i t$, and put $F(x,t)=\prod_i(x+a_i+s_i t)$. We ask for a polynomial address $U(t)$ such that each coefficient of $F$ in $x$ is a polynomial in $U$. The leading coefficient of $U$ must be a unit. Over a field, with $m$ blocks, the same condition already follows if the product at each of $m+1$ distinct offsets is a polynomial in $U(t)$. Interpolation in the offset gives the coefficient formulas. The identity must hold as a polynomial in $t$.

Let $e_1,e_2$ be the first two elementary symmetric functions of the terms $a_i+s_i t$. Both occur as coefficients of the product, and

$$
e_1^2-2e_2=\sum_i(a_i+s_i t)^2.
$$

If $U$ has degree at least three, every polynomial in $U$ having degree at most two must be constant. The unit leading coefficient makes this true even modulo a composite number. Applying it to $e_1$ and $e_1^2-2e_2$ forces both $\sum_i s_i=0$ and $\sum_i s_i^2=0$ in the coefficient ring. For strides $\pm B$ the latter sum is $mB^2$. For arbitrary integer strides modulo $N$, a nontrivial cubic fold therefore requires $\sum_i s_i^2\ge N$. At least one stride has magnitude at least $\sqrt{N/m}$. [Proof over commutative rings and finite-offset interpolation](../PrimeFactors/AffineFactorialAddress.lean)

A modular exception is visible on 91. Its public value satisfies $9^2+9+1=91$, giving the exact identity $(x+t)(x+9t)(x-10t)=x^3+t^3$ modulo 91. At $x=1,t=3$, the first linear candidate 4 is coprime to 91, while the cubic value 28 gives $\gcd(28,91)=7$ and hence $91=7\times13$. The three strides have squared sum 182. The middle linear candidate itself is 28, so this example establishes the modular identity without demonstrating a runtime gain.

## Can a polynomial just detect a divisor?

The existing two-block fold uses one root for each retained offset $0\le r<B$. Over a prime factor $p>B$ of $N$, its root is

$$
u_r=(A+r)(A+r-B)/B^2.
$$

Each $u_r$ is a possible quadratic address because it equals $j(j+1)$ at $j=(A+r)/B-1$ modulo $p$. Distinct offsets $r,s$ can name the same root only if $p$ divides $2A-B+r+s$. Every such integer lies in $[2A-B,2A+B-2]$. Take the gcd of $N$ with the product of that short interval first. If the gcd is one, the nodes are distinct at every prime factor larger than $B$. **Even a nonzero polynomial required only to vanish at all those nodes has degree at least the number of retained offsets.** This statement concerns all possible block indices modulo that prime. A method that only needs correctness at a shorter list of actual indices has a weaker requirement. [Folded root bound and checked examples](../PrimeFactors/AffineFactorialAddress.lean)

On 11,413 the equal-width smaller-factor interval is $[90,106]$. Taking its midpoint $A=98$ and $B=10$, the offsets 7 and 9 collide modulo 101. The product of the 19 integers in the short interval has gcd 101 with the input. Lean also checks $11,413=101\times113$ and the primality of both factors.

For the fresh and crossed 2,048-bit controls, we set $A=\lfloor(L+U)/2\rfloor$ using the public equal-width interval and fixed $B=840$. Keeping the offsets coprime to 210 leaves 192. On each input the 1,679 consecutive integers in the precheck gave gcd one. Consequently the degree floor is 192 on both sides for this block size. These two individual checks used 1,679 modular multiplications and one gcd each. Neither found a factor. Reproduce the precheck from each published $N$ by starting at one and multiplying the integers from $2A-B$ through $2A+B-2$ modulo $N$. [Public inputs](../benchmarks/short-pascal.json) · [Equal-width endpoints](a-shorter-pascal-row-for-equal-width-primes.md)
