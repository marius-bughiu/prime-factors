# When a soluble norm never appears among the convergents

For the target 2, we can decide exactly when the equation
$$
X^2=kNY^2+2T^2
$$
has a positive primitive solution, if we know the prime divisors of $kN$. Even when the answer is yes, searching every ordinary continued-fraction convergent of $\sqrt{kN}$ can miss every solution.

## The precise local test

Suppose $A=kN>1$ is odd and squarefree. The following conditions are equivalent.

- There are positive integers $X,Y,T$ with $\gcd(X,Y)=1$ satisfying the equation.
- There are positive integers $X,T$ satisfying $X^2=A+2T^2$, so one can take $Y=1$.
- The residue 2 has a square root modulo $A$.
- Every prime divisor of $A$ is congruent to 1 or 7 modulo 8.

For a primitive point, a prime dividing both $A$ and $T$ would divide $X$. Its square would then divide $AY^2$, forcing it to divide $Y$ because $A$ is squarefree. Thus $T$ is invertible modulo $A$, and $X/T$ gives the modular root. In the other direction, the repository’s Euclidean reduction takes a supplied modular root, gives a representation of signed $A$, and flips a negative norm using $1+\sqrt2$. Quadratic reciprocity gives the two allowed residues at each odd prime, and the Chinese remainder theorem combines the local roots. Lean proves the equivalence end to end. [Local-to-global theorem](../PrimeFactors/TargetNormLocalGlobal.lean) · [Positive Euclidean construction](../PrimeFactors/ShortRootNormPositive.lean)

Classically this is the case $(1,-A,-2)$ of Legendre’s theorem on rational conics. The congruence conditions modulo 1 and 2 are automatic. The substantive part of the solubility certificate is a square root of 2 modulo $A$. Clearing denominators in a rational solution and dividing the three coordinates by their gcd gives $\gcd(X,Y)=1$, since any common prime in these two coordinates must also divide $T$. [Cremona and Rusin, Lemma 2.1 and congruences (6)](https://johncremona.github.io/papers/conics.pdf)

When the small multiplier $k$ is known and coprime to $N$, its prime divisors can be screened first. The public modulo-16 test accepts precisely $A\equiv1,7\pmod8$ for odd $A$. For example, $551=19\cdot29$ passes that test at $k=1$, as well as $(2\mid551)=+1$. Both factors have negative local sign, so the conic has no primitive point. More generally, an inert prime dividing $N$ prevents a primitive solution for every coprime squarefree multiplier. Given a representation $u^2-2v^2=k$, multiplication by $u+v\sqrt2$ gives an explicit bijection between rational solutions of the normalized equations for $N$ and $kN$. Its inverse uses $(u-v\sqrt2)/k$. [Root extraction, multiplier bijection and the example 551](../PrimeFactors/TargetNormConic.lean)

The cost is asymmetric. Given the factors, one can find the local square roots and combine them. Given a root modulo $N$ and one modulo the coprime $k$, the construction starts with a single CRT and ordinary Euclidean divisions, taking $O(\log(kN))$ division steps. Given only $N$, the missing square root modulo $N$ is itself the output of any primitive witness. One root gives a necessary divisor test. Two roots with different relative signs at the two hidden primes give a proper divisor by one gcd. [Euclidean algorithm and invariant](../PrimeFactors/ShortRootNorm.lean) · [Constructive conic algorithms and their required certificate](https://johncremona.github.io/papers/conics.pdf)

## A full period can miss a positive point

Set $a=u^2$ and $N=u^4+1$, with $u\ge1$. The complete quotients of $\sqrt N$ give $[a;\overline{2a}]$. Its complete denominators are always 1. The numerator and denominator of every ordinary convergent satisfy $x_j^2-Ny_j^2=(-1)^{j+1}$, with $j=0$ at $a/1$. Increasing the budget cannot produce a norm $2T^2$. Yet the very first **intermediate convergent** $[a;1]=(a+1)/1$ satisfies $(a+1)^2-N=2u^2$. On this family the single candidate $X=\lfloor\sqrt N\rfloor+1$ exhibits the target.

For $u=78$, this gives $37{,}015{,}057=5{,}449\cdot6{,}793$, with two 13-bit primes and a 26-bit product. For $u=2^{512}-2$ the same formula gives a 2,048-bit integer and the same complete exclusion. The proof checks its width without assuming a factorization. A second small example has $697=17\cdot41$ and $\sqrt{697}=[26;\overline{2,2,52}]$. Its complete denominators repeat $21,21,1$, while the first intermediate convergent $27/1$ gives $27^2-697=2\cdot4^2$. These statements concern the ordinary scan at $k=1$. [Lean recurrence proofs, prime factors and intermediate points](../PrimeFactors/TargetNormConvergents.lean)

## Historical comparison

D. H. Lehmer and Emma Lehmer already gave a product-only choice of three equations $\lambda N=x^2-Dy^2$ for semiprimes coprime to 6. They select by $N\bmod24$, using $D\in\{-1,2,-2,3,-3,6,-6\}$ and $\lambda\in\{1,-1,2\}$. At least one chosen equation has two inequivalent representations in their stated intervals. Their determinant gcd recovers a factor. The intervals for $y$ have length proportional to $\sqrt N$. For seven of the eight unit classes modulo 24, the repository’s signed three-target rule selects the same set of discriminants, ignoring order. At residue 1 the Lehmer selection uses $\{-2,-3,6\}$, while the present rule uses $\{-1,2,-2\}$. [Lehmer and Lehmer, pp. 625–627, theorem and equations (2)–(4)](https://doi.org/10.2307/2005939) · [Lean three-target rule](../PrimeFactors/ThreeRootTargets.lean)

There is also a classical short-vector explanation for the small multipliers. Given an actual root $r^2\equiv D\pmod N$, scale the lattice $x\equiv ry\pmod N$ by measuring the second coordinate as $\sqrt{|D|}\,y$. Its determinant is $N\sqrt{|D|}$. In a Lagrange-reduced planar basis the acute angle between the two basis directions is at least $60^\circ$, so its shortest vector satisfies $x^2+|D|y^2\le 2N\sqrt{|D|/3}$. For a nonsquare $D$, the nonzero norm $x^2-Dy^2=\lambda N$ therefore has $|\lambda|\le1,1,2,2$ for $|D|=1,2,3,6$, respectively. This calculation begins with the root $r$. With $y$ a unit, the recovered ratio $x/y$ gives that very root again. The Lehmer factor readout requires a second root with the opposite relative sign at exactly one hidden prime. Cornacchia’s algorithm has the same modular-root input for positive definite equations. [Gauss, *Disquisitiones Arithmeticae*, article 171](https://edoc.hu-berlin.de/items/4a65bbe3-c434-4581-8d40-2c3b426d3cf2) · [Morain and Nicolas on Cornacchia’s algorithm](https://www.lix.polytechnique.fr/~morain/Articles/cornac.pdf)
