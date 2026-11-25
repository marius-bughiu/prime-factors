# Reading a prime from a quadratic-extension character sum

For a fixed selector, a randomized row halves the mean number of individual norm tests. A second mark exposes one bit that decides whether a given unit is a square at a selected hidden prime. Directly reading that bit still requires the full grid. [How far the search must go](marked-support-boxes.md) · [What the fifth bit tells us](marked-trace-bit.md)

On $N=77$, an ordinary elliptic trace vanishes at both hidden primes. A different sum, over pairs of residues modulo 77, equals **21**. Adding one and halving gives the prime **11**. With another public choice of parameter the same sum equals **13**, giving **7**. These are exact formulas, but direct evaluation takes $N^2$ terms. A simpler one-variable count below already gives a factor in $N$ terms. [Bounded smooth-curve reference](../experiments/extension_trace.py) · [Checked examples and capped 2,048-bit run](../benchmarks/extension-trace.json)

## The formula for two primes 3 modulo 4

Let $N=pq$ for distinct primes greater than 3. Pick $D$ with public Jacobi symbol $(D/N)=-1$. Label the primes so $D$ is a square at $p$ and a nonsquare at $q$. Define $R=(\mathbb Z/N\mathbb Z)[w]/(w^2-D)$, with $\operatorname{Norm}(x+yw)=x^2-Dy^2$. For a polynomial $g$ take the complete integer sum

$$B_D(g)=\sum_{x,y\bmod N}\left(\frac{\operatorname{Norm}(g(x+yw))}{N}\right).$$

Use $f(z)=z^3-z$ and mark the point $z=2$ by setting $g(z)=(z-2)^2f(z)$. If **both hidden primes are 3 modulo 4**, then $B_D(g)=2q-1$ exactly. For $N=77$ the selectors $D=2$ and $D=3$ give 21 and 13. The numerator for a grid point is easy to write as an integer. Put $L_j=(x-j)^2-Dy^2$. The four linear factors of $g$ give the norm $L_2^2 L_0 L_1 L_{-1}$. [Lean identity and 77 examples](../PrimeFactors/PuncturedTrace.lean)

To see where $q$ enters, put $u=\sum_{x\bmod p}(f(x)/p)$ and $v=\sum_{x\bmod q}(f(x)/q)$. At $p$ the algebra is two copies of the prime field, so summing the norm character gives $u^2$. At $q$ it is the quadratic extension field and the sum is $2q-v^2$. Lean proves the latter identity using finite quadratic-character sums. The proof combines the square and nonsquare choices of $D$, then evaluates the resulting second moment by a quadratic-character correlation. In elliptic-curve terms the two Frobenius eigenvalues have sum $-v$ and product $q$, so their squares have sum $v^2-2q$. [Elementary finite-field proof](../PrimeFactors/ExtensionTrace.lean) · [Frobenius interpretation](https://www.numdam.org/item/JTNB_1995__7_1_219_0.pdf)

Marking $z=2$ removes one term in each field. Since $f(2)=6$, the base-field contributions removed are $s=(6/p)$ and $t=(6/q)$. In the extension field the removed term is always one, since its norm is $6^2$. Write $U=su$ and $V=tv$. The split algebra has two independent coordinates, so marking there gives $(u-s)^2=(U-1)^2$. Therefore

$$B_D(g)=(U-1)^2(2q-V^2-1).$$

At a prime 3 modulo 4, the summands for $x$ and $-x$ cancel for this odd cubic. Both $U$ and $V$ vanish on the stated inputs, giving $B_D(g)=2q-1$. [Marked split, inert, and gcd theorems](../PrimeFactors/PuncturedTrace.lean)

## Extending the calculation to other prime pairs

Let $A(h)=\sum_{x\bmod N}(h(x)/N)$ and compute the public sign $e=(6/N)=st$. CRT gives $eA(f)=UV$ and $eA(g)=(U-1)(V-1)$. Hence $T=eA(f)$ and $S=T+1-eA(g)$ are the product and sum of the unknown signed traces. They are the integer roots of $X^2-SX+T$, including the case of a repeated root. Both traces are even. At a prime 3 modulo 4 the trace is zero, and at a prime 1 modulo 4 the unmarked sum is 2 modulo 4. Thus $U-1$ is always nonzero. For each possible ordering of the roots test

$$q=\tfrac12\big(B_D(g)/(U-1)^2+V^2+1\big).$$

Keep only exact divisions and a proper divisor of $N$. Lean proves that integer roots exist and that the correct ordering returns $q$. For $N=91$, $D=2$ gives $e=1$, $A(f)=0$, $A(g)=-5$ and $B_D(g)=-11$. Taking $U=0$, $V=6$ gives $q=13$. At $N=65$, $D=3$ the public sign is negative. The three measured sums are $-12,-5,125$, yielding signed traces $2,6$. Taking $U=6$, $V=2$ gives $q=5$. [Checked general decoder](../PrimeFactors/PuncturedTrace.lean)

At most two sums are needed if the computation branches on $N\bmod4$. When $N\equiv3\pmod4$, one of $U,V$ is zero, so $A(f)=0$ is known in advance. When $N\equiv1\pmod4$, first read the base quartic sum from the companion article. If that is nonzero, both primes are 1 modulo 4 and one more ordinary quartic sum recovers a prime. If it is zero, both primes are 3 modulo 4 and $B_D(g)$ alone supplies the remaining measurement. A divisor of 3 is tested directly before using the curve. [Quartic sum, coverage bit and factor formula](quartic-trace.md)

## The cost of acquiring the measurements

For comparison, even with an arbitrary smooth cubic $f$ there is a factor identity $A(f)^2+B_D(f)=2q\,u^2$. Its gcd with $N$ is $q$ whenever the split-side trace is nonzero, since Hasse's bound gives $0<|u|<p$ for $p\ge5$. For uniformly random nonsingular curves $y^2=x^3+ax+b$, a sufficient event is an irreducible cubic at $p$, when the group has odd order and the trace is odd. This event has exact probability $(p+1)/(3p)$. Of the $(p^3-p)/3$ monic irreducible cubics, translation gives exactly $(p^2-1)/3$ with zero quadratic coefficient. The $p$ singular coefficient pairs have the form $(-3t^2,2t^3)$, leaving $p(p-1)$ nonsingular choices. CRT makes the local choices independent when sampling good curves modulo $N$. The fixed puncture above removes the dependence on a random curve. For a direct comparison on $77$, the smooth cubic $x^3+x+1$ gives $A=-6$ and $B=162$, whence $\gcd(77,36+162)=11$. The smooth cubic $x^3-x$ gives zero twice at the same selector. [Algebraic readout](../PrimeFactors/ExtensionTrace.lean) · [Bounded comparisons](../benchmarks/extension-trace.json)

A direct quadratic-extension measurement traverses $N^2$ pairs. For a 2,048-bit $N$ that is at least $2^{4094}$ pairs. The extraction is elementary once the sums are known. If arbitrary character sums with square factors are available, the degree-four polynomial $(x^2-D)^2$ gives a cheaper comparison. Its Jacobi value is 1 unless $p\mid x^2-D$. The two roots at $p$ each have $q$ lifts modulo $N$, and there are no roots at $q$. Thus

$$A((x^2-D)^2)=N-2q.$$

One can cease direct evaluation at the first zero and recover $p$ by a gcd. These measurements do not improve the computational search on ordinary 2,048-bit inputs. The extension formula explains how an exact trace can reveal a prime even when every ordinary prime-field trace in the chosen family vanishes.

## How often a Legendre curve works without removing a point

There is also a guarantee when the search varies the smooth cubic itself. Keep the same selector $D$, and set $f_\lambda(x)=x(x-1)(x-\lambda)$. For $\lambda$ different from 0 and 1 at both primes, the gcd of $N$ and $A(f_\lambda)^2+B_D(f_\lambda)$ gives $q$ whenever the ordinary sum at the split prime $p$ is nonzero. For this family Lean proves the extension identity by finite-field character sums. An elementary bound on the absolute trace follows because the visible root $x=0$ contributes zero. [Extension identity and gcd theorem](../PrimeFactors/ExtensionTrace.lean)

At most $(p-1)/2$ of all $p$ choices of $\lambda$ have zero trace. To see why, let $m=(p-1)/2$ and reduce the ordinary integer trace modulo $p$. Euler's criterion makes it the value at $L=\lambda$ of the polynomial
$$H(L)=\sum_{x\bmod p}\chi(x(x-1))(x-L)^m \quad\text{over }\mathbb F_p.$$
It has degree at most $m$. At $L=0$, the trace is the sum of $\chi(x-1)$ with the $x=0$ contribution removed, so $H(0)=-\chi(-1)\ne0$. Every zero integer trace is therefore a root of a nonzero polynomial of degree at most $m$. Among the $p-2$ nonsingular parameters at least $(p-3)/2$ work. For a uniform residue modulo $N$, conditioned on nonsingularity at both primes, CRT preserves uniformity modulo $p$. Each independent trial has success probability at least $(p-3)/(2(p-2))$. Its cost still includes the complete extension sum. [Checked polynomial and root-count bound](../PrimeFactors/LegendreTraceSelection.lean)

For the simpler one-variable support count above, a uniform trial hits one of the two roots modulo $p$ with probability $2/p$. With independently chosen positions the expected number to the first hit is $p/2$. The earlier bounded two-coordinate norm search and the grouped divisor-interval method give faster alternatives for balanced inputs. [Bounded norm search](short-norm-boxes.md) · [Complete interval search](factorial-progressions.md)
