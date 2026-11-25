# Counting false midpoints beyond a full period

For every 2,048-bit product of two 1,024-bit primes, **more than $2^{819}$ wrong midpoints pass all prime-power square tests for every prime through 1,109**. These 186 primes have a combined period longer than the whole search interval. The elementary full-period argument already proves a larger count for the first 130 primes. For the extension we use Weil's bound on Kloosterman sums in a paper argument. Lean checks the change of variables, the finite constants and an independent example of the counting formula. [The elementary theorem through 733](persistent-local-survivors.md) · [Lean arithmetic and example](../PrimeFactors/PersistentFourierBound.lean) · [Weil's original paper](https://doi.org/10.1073/pnas.34.5.204)

## A frequency bound at one prime

Put $W=2^{1019}$. The balanced interval contains a subinterval of $W$ consecutive midpoints. Choose the four guaranteed midpoint classes modulo 128 and the two modulo 27 from the elementary proof. CRT gives eight distinct classes modulo $Q=3456$. In each one, take the first $L=\lfloor W/Q\rfloor$ members of the subinterval. Write these as $h=a+Qt$ with $0\le t<L$. Every chosen midpoint already passes the dyadic and triadic tests at all precisions.

Let $P$ be the primes from 5 through 1,109, and $M=\prod_{p\in P}p$. For $p\in P$, define $f_p(t)$ as the indicator that $(a+Qt)^2-N$ is a nonzero square modulo $p$. Write $e_p(z)=\exp(2\pi i z/p)$ and normalize the Fourier transform by
$$
\widehat f_p(k)=\frac1p\sum_{t\bmod p} f_p(t)e_p(-kt).
$$
The inverse transform has no factor $1/p$. The zero coefficient $\alpha_p$ is the local density, at least $(p-3)/(2p)$. We claim that every nonzero coefficient satisfies $|\widehat f_p(k)|\le(\sqrt p+1)/p$.

The invertible change $h=a+Qt\bmod p$ only changes the frequency by a unit and multiplies the transform by a complex number of absolute value one. For $D=h^2-N$ and Legendre symbol $\chi$, twice the indicator is $1+\chi(D)-\mathbf1_{D=0}$. At a nonzero frequency the constant term vanishes, and the last term has at most two summands. The solutions of $y^2=h^2-N$ are in bijection with $x\ne0$ via $x=h+y$, $N/x=h-y$. Thus the transform numerator for $\chi(D)$ is a sum over $x\ne0$ of $e_p(bx+bN/x)$ for some $b\ne0$. Both coefficients are nonzero because $p\nmid N$. Weil's bound is $2\sqrt p$ for this complete Kloosterman sum. Division by $2p$ proves the claim. [Weil, On Some Exponential Sums](https://doi.org/10.1073/pnas.34.5.204)

## Completing the interval sum

Let $\alpha=\prod_{p\in P}\alpha_p$. Expand $\prod f_p(t)$ in Fourier modes and group each term according to which local frequencies are nonzero. A set of active primes has product $d\mid M$. As their nonzero frequencies vary, the resulting frequencies are precisely $j/d$ for $j$ coprime to $d$, each once by CRT. A term of this kind has coefficient of absolute value at most
$$
\alpha\prod_{p\mid d}\frac{\sqrt p+1}{p\alpha_p}.
$$
For $1\le j<d$, the geometric series on the interval has absolute value at most $1/|\sin(\pi j/d)|\le d/(2\min(j,d-j))$. Summing this bound over all nonzero $j$ costs at most $d(1+\log d)$ by the harmonic sum inequality. This bound also applies to the subset coprime to $d$.

The coefficient with $d=1$ contributes the exact main term $L\alpha$. Summing the error over the remaining divisors, using $\log d\le\log M$, and adding the harmless empty-product term for an upper bound gives
$$
\left|\sum_{0\le t<L}\prod_{p\in P} f_p(t)-L\alpha\right|
\le \alpha E,\qquad
E=(1+\log M)\prod_{p\in P}\left(1+\frac{\sqrt p+1}{\alpha_p}\right).
$$
The factor $d$ from interval completion cancels the local factors $p$ in the denominator. This bound holds for every starting residue $a$ and every possible pattern of square and nonsquare values of $N\bmod p$.

## The numerical margin

For a uniform estimate replace each $\alpha_p$ in the denominator of $E$ by $(p-3)/(2p)$. Replace $\sqrt p+1$ by $(257+\lfloor\sqrt{65536p}\rfloor)/256$ and $1+\log M$ by 1,559, since $M<2^{1558}$. Exact integer comparisons give
$$
10E<L,\qquad
8L\prod_{p\in P}\frac{p-3}{2p}>\frac54(2^{819}+1).
$$
Thus each progression retains more than nine tenths of its own zero-frequency term. Adding the eight progressions gives more than $(9/10)(5/4)(2^{819}+1)$ candidates. Removing the one possible true midpoint leaves more than $2^{819}$ false ones. The upper estimate for $E/L$ before rounding this ratio to one tenth is about 0.0960. The minimum-density zero-frequency total over the eight progressions is about $1.3125\cdot2^{819}$. [Exact integer comparisons](../PrimeFactors/PersistentFourierBound.lean)

For a small check, use $N=713$, $h=27+3456t$, $0\le t<137$, and primes 5, 7 and 11. The three densities are $2/5,3/7,4/11$. To get the contribution with exact denominator $d$, use $f_p-\alpha_p$ on the primes dividing $d$ and $\alpha_p$ on the others. Multiplying the contributions for $d=1,5,7,11,35,55,77,385$ by 385 gives $3288,72,16,-54,-16,-6,138,-358$. Their sum is $8\cdot385$, and direct enumeration gives exactly eight survivors. [Checked exact-conductor expansion and direct count](../PrimeFactors/PersistentFourierBound.lean)
