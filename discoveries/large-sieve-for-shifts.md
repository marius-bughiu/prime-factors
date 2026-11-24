# How often a rational shift can find the factor sum

Fix $X=2^b$. Before seeing the product, select nonzero integer polynomials $A(T),B(T)$ and use the shift $A(N)/B(N)$ at inputs where it is defined. The shift can succeed only if
$$
F(x,y)=\big(2B(xy)x+A(xy)\big)\big(2B(xy)y+A(xy)\big)
$$
is an integer square for $N=xy$. This allows negative shifts and counts zero as a square. The equivalence with rational squareness follows by clearing $B(N)^2$ and using that a rational square which is an integer has an integer square root.

**Unconditional paper bound.** Suppose a fixed polynomial in $b$ bounds the degrees and the bit lengths of all coefficients. The number of integer pairs in $[X/2,X]^2$ at which the shift succeeds is $O(X^{3/2}\log X)$ for sufficiently large $b$, uniformly over the permitted polynomials. Consequently, a list of at most $\sqrt X/b^4$ such shifts succeeds on at most an $O(1/b)$ fraction of the balanced prime pairs in $[0.75X,0.80X]\times[0.90X,0.95X]$. These pairs have exactly $b$-bit factors and $2b$-bit products. The same fraction bound applies among all distinct $b$-bit prime pairs with $2b$-bit products, since the indicated rectangle already supplies order $X^2/(\log X)^2$ such pairs. A search can choose among the listed shifts after inspecting $N$. The theorem concerns this class of formulas and gives no numerical threshold at 2048 bits.

This is a quantitative Hilbert irreducibility or large-sieve argument. The exponent $3/2$ in two variables is classical. Here the product-fiber equation yields uniform local estimates even when the formulas vary with the bit width. No GRH or distribution theorem for primes in progressions is needed. [Zywina on quantitative Hilbert irreducibility and sieves](https://arxiv.org/abs/1011.6465)

## A cubic on each product fiber

Choose primes $\ell$ between $\sqrt X/2$ and $\sqrt X$. Discard primes for which either $A$ or $B$ is identically zero modulo $\ell$. Any selected nonzero coefficient of each polynomial bounds the number discarded by its bit length. Thus $K\asymp\sqrt X/\log X$ primes remain. For a fixed nonzero residue $n=xy$, put $a=A(n)$, $d=B(n)$. Exclude the residues where $ad(a^2-4nd^2)=0$. There are $O(1+\deg A+\deg B)$ excluded residues, since the polynomial $A^2-4TB^2$ is nonzero over the odd prime field by parity of degrees.

As $x$ varies over the nonzero residues, $y=n/x$. Multiplying $F$ by the square $x^2$ gives
$$
C_n(x)=x(2dx+a)(ax+2dn).
$$
The three roots $0,-a/(2d),-2dn/a$ are distinct on these fibers. The curve $z^2=C_n(x)$ is therefore a smooth genus-one cubic with one rational point at infinity. Hasse's bound shows that the absolute value of the quadratic character sum over $x$ is at most $2\sqrt\ell$. At least $(\ell-3-2\sqrt\ell)/2$ of the $\ell-1$ nonzero $x$ give a nonsquare. Accounting for excluded fibers, a uniform pair in $\mathbb F_\ell^2$ has rejection probability at least $1/3$ for all sufficiently large $b$. [Lean square equivalence and distinct roots](../PrimeFactors/ShiftCubic.lean) · [Hasse's bound, Silverman V.1.1](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf)

## A probability measure covering the integer box

Let $Q$ be the product of the $K$ auxiliary primes and $H=\lfloor Q/(4X)\rfloor$. Center the integer box at $c=3X/4$. On residues $z\bmod Q$ take the probability weight
$$
w(z)=\frac{1}{QH}\left|\sum_{j=0}^{H-1}e^{2\pi i j(z-c)/Q}\right|^2 .
$$
The product $Q$ is a proof device. A factoring algorithm need not construct it.

For each $m\mid Q$ with $m\le4X$, this measure assigns mass exactly $1/m$ to every class modulo $m$. Expanding the square and summing along the class annihilates terms with $j\ne k$, since $|j-k|<H\le Q/m$. The diagonal terms give the claim, including total mass one when $m=1$. For each integer $z\in[X/2,X]$ all phases are within $\pi/3$ of zero, so each summand has real part at least $1/2$. Hence $w(z)\ge H/(4Q)\ge 1/(32X)$ for large $X$. These box points are distinct modulo $Q$. [Lean marginal and central mass theorems](../PrimeFactors/FejerProjection.lean)

Take two independent coordinates with this weight. For distinct primes $\ell_1,\ell_2$ in the list, $\ell_1\ell_2\le X$. The exact marginal and CRT make their rejection indicators pairwise independent. Let $Z$ count rejections and let $\mu=\mathbb E Z\ge K/3$. Then $\operatorname{Var} Z\le\mu$ by pairwise independence. The weight of $Z=0$ is at most $1/\mu$, because on that event $(Z-\mu)^2=\mu^2$. A global square has $Z=0$. Each box point has product weight at least $(32X)^{-2}$, so at most $O(X^2/K)=O(X^{3/2}\log X)$ box points can give a square. [Lean finite second-moment estimate](../PrimeFactors/PairwiseSieve.lean)

Finally take a union bound over the list of shifts and divide by the prime-pair count from the ordinary prime number theorem. For a list of length $m$, the resulting upper bound on the successful fraction is $O(m(\log X)^3/\sqrt X)$. The local cubic, Fourier facts and second-moment inequality are separately checked in Lean. Combining them with Hasse, asymptotics and the prime counts is a paper deduction. The [CRT argument](choosing-shifts.md) supplies explicit simultaneous failures at individual inputs.
