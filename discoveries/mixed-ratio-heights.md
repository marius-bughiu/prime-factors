# Which pairs can come from a square?

Take two distinct odd primes $p,q$, their product $N$, and two coprime positive integers $u<v$ that are units modulo $N$. Suppose that $z=u/v\pmod N$ equals $+1$ at one prime and $-1$ at the other. Write $W=uv$. We ask for two primitive signed fractions representing the same residue modulo $N$ whose quotient as ordinary rationals is $(u/v)^2$. The height of $a/b$ is $|a|b$ with $b>0$. A pair is short when twice the larger of its two heights is less than $N$. Any such pair reveals a factor. This question asks which of the candidate ratios from the two mixed-root chains can actually occur. [Proof that a pair gives a factor](same-source-pairs.md)

**For an unrestricted unit source, the smallest possible maximum height is exactly $W$.** The fractions $u/v$ and $v/u$ already represent the same residue, since $z^2=1$. Both have height $W$. For square sources the same minimum holds if either prime is 1 modulo 4. To see this, choose the common sign so that the coordinate at a prime congruent to 3 modulo 4 is $+1$, if such a prime occurs. At a prime congruent to 1 modulo 4, both signs are squares. The Chinese remainder theorem then supplies a square root of the chosen residue.

**If both primes are 3 modulo 4, two integers give the exact answer.** Let $L$ be the smallest positive integer with Jacobi symbol $-1$ modulo $N$. Let $D$ be the largest divisor of $W^2$ at most $W$ whose Jacobi symbol is $+1$. The smallest possible maximum height at a square source is

$$ H=\min\{W^2/D,\;LW\}. $$

Consequently the ratio occurs at a short square source exactly when $2H<N$. All Jacobi evaluations in this formula use $N$ alone. Computing $D$ also requires the proposed $W$ and a search for a divisor of $W^2$. Knowing $u/v$ in modular arithmetic would already give a factor by $\gcd(v-u,N)$. These minima measure what a source could produce once the ratio is specified. They supply no way to obtain the hidden ratio cheaply from $N$.

## Why the minimum is exact

Consider two primitive fractions $a/b,c/e$ with $b,e>0$. Their numerators have the same sign because their quotient is $(u/v)^2$. Extract $m=\gcd(|a|,|c|)$ and $n=\gcd(b,e)$, writing $(|a|,|c|,b,e)=(mA,mC,nB,nE)$. The four pairwise conditions $\gcd(A,C)=\gcd(B,E)=\gcd(A,B)=\gcd(C,E)=1$ imply $\gcd(AE,CB)=1$. Since $AE/(CB)=(u/v)^2$, we have $AE=u^2$ and $CB=v^2$. With $g=mn$, the heights are $gAB$ and $gCE$ and $(AB)(CE)=W^2$. Call the smaller unscaled height $d$ and the other $W^2/d$. The larger height is at least $W$.

For primes both congruent to 3 modulo 4, a unit residue or its negative is a square exactly when its Jacobi symbol is $+1$. Indeed, Jacobi $+1$ means equal local signs, and negation reverses both. A fraction and its signed norm have the same local square classes, since multiplying the fraction by its denominator squared produces the norm. Also $-1$ has Jacobi symbol $+1$ here. Thus the positive magnitude $gd$ must have Jacobi $+1$ for a square source. If $d$ has symbol $+1$ then $d\le D$, so the larger height is at least $W^2/D$. Otherwise $g$ has symbol $-1$, so $g\ge L$ and the larger height is at least $LW$. This proves the lower bound.

For any divisor $d\mid W^2$, let $A=\gcd(d,u^2)$ and $B=\gcd(d,v^2)$, so $AB=d$. Use the fractions

$$ \frac AB,\qquad \frac{v^2/B}{u^2/A}. $$

Their cross products are $u^2$ and $v^2$, which are congruent modulo $N$. Both fractions are primitive because $u$ and $v$ are coprime. Their heights are $d$ and $W^2/d$. Setting $d=D$ and choosing the common sign realizes the first bound. For the second bound, multiply both canonical fractions $u/v,v/u$ by $L$. Their common residue then has Jacobi symbol $+1$ since $z$ is a mixed root at two primes congruent to 3 modulo 4 and therefore has symbol $-1$. Reducing each fraction preserves the ordinary rational quotient $(u/v)^2$ and its modular value, and can only decrease each height. Changing both numerator signs if necessary supplies a square source. The two constructions and the lower bound force the stated minimum. [Lean proofs of reciprocity of the two rows, divisor redistribution and the lower bound](../PrimeFactors/MixedRatioHeight.lean)

## A missing ratio at 437

For $437=19\cdot23$, both primes are 3 modulo 4 and $L=2$. At ratio $2/21$, the formula gives $W=42$, $D=36$, and $H=49$. The fractions $4/9$ and $49/1$ both represent $49=7^2$ modulo $437$. Their heights are 36 and 49. At ratio $1/208$, it gives $W=208$, $D=169$, and $H=256$. The unrestricted unit source realizes the ratio with heights 208 and 208. Every square source exceeds the shortness limit of $437/2$ for this ratio.

We checked the exact minimum on all 281 eligible mixed ratios from the 111 products of distinct odd primes of equal bit length through 127. For each product, the direct check generated every primitive positive fraction up to the largest proposed minimum, including heights above the shortness cutoff. It grouped them by residue whenever at least one common sign gave a square and compared every pair of fractions in each group. The measured minimum matched the prediction for every ratio. All 204 ratios on products with a prime congruent to 1 modulo 4 were short at a square source. Among the other 77 ratios, 49 were short at a square source. The remaining 28 explain the entire discrepancy in the earlier census. Run `python3 -m experiments.mixed_ratio_heights --prime-limit 127` to repeat this comparison. [Census and witness construction](../experiments/mixed_ratio_heights.py)

## A bound from Dirichlet GRH

The released Dirichlet GRH statement also bounds the price of requiring a square source. Apply Theorem 1.1(2) of Lamzouri, Li and Soundararajan to the kernel of the nontrivial Jacobi character modulo $N$. A 2,048-bit product of two 1,024-bit primes has no prime divisor below $(\log N)^2$. Thus the least Jacobi nonresidue $L$ is at most $(\log N)^2<2^{21}$. For every proposed mixed ratio with $W<N/2^{22}$ the formula above guarantees a short pair at a square source. It takes at most $2^{21}$ public Jacobi tests to find such a multiplier if needed. Locating the mixed ratio from the product is a separate cost. This application uses the cited analytic theorem on paper. [Least prime outside a subgroup](https://arxiv.org/pdf/1309.3595#page=2) · [Dirichlet statement and verification record](https://math.mit.edu/~drew/grh/)
