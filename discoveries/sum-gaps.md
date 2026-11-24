# How many local factor sums survive in a short block?

Let $M$ be a squarefree product of odd primes coprime to the public input $N$. Write $A_M$ for the residues $s\bmod M$ for which $s^2-4N$ is a square modulo each prime divisor, with zero allowed. For every fixed $\varepsilon>0$, **every interval of $W$ consecutive integers contains $W^{1-o(1)}$ survivors when $M\le W^{2-\varepsilon}$**, uniformly in $N$ as $W\to\infty$. The previous complete-period argument reached $M\le W$. This extends the obstruction to a sieve that visits every survivor before testing integer discriminants. It also covers even candidate sums and fixed residue classes of sums whose step is coprime to $M$. [Complete-period count](factor-sum-residues.md) · [Hittmeir’s hyperbolic sieve, §§3–5](https://arxiv.org/html/2205.10074v2#S3)

## An explicit bound for every block

Let $n_p=|A_p|=(p+(\frac Np))/2$, $z_p=1+(\frac Np)$, and $\alpha=|A_M|/M=\prod_{p\mid M}n_p/p$. Define
$$
 b_p=\min\{1,(\sqrt p+z_p/2)/n_p\},\qquad
 B_M=\prod_{p\mid M}(1+p b_p)-1 .
$$
For every integer $h\ge1$, a block of $2h-1$ positions contains at least $\alpha(h-B_M)$ survivors, counted at their integer positions. In particular $h>B_M$ guarantees a survivor. The calculation only needs the primes of the chosen sieve and the Legendre symbols of $N$. It also works with any larger certified upper bounds for the $b_p$.

To prove it, use the unnormalized Fourier transform $\widehat f(k)=\sum_{s\bmod M} f(s)e^{2\pi i k s/M}$ for $f=1_{A_M}$. Locally $A_p$ is the image of $x\mapsto x+N/x$ on $\mathbb F_p^\times$. A sum usually has two preimages. The $z_p$ roots of $x^2=N$ are the exceptions, each with one preimage. Thus twice the local Fourier coefficient is the Kloosterman sum $\sum_{x\ne0}e_p(kx+kN/x)$ plus $\sum_{x^2=N}e_p(2kx)$. Weil bounds the first sum by $2\sqrt p$ when $p\nmid k$. At zero the local coefficient is $n_p$. CRT now gives $|\widehat f(k)|/|A_M|\le b_d:=\prod_{p\mid d} b_p$ when the frequency $k/M$ has reduced denominator $d\mid M$. Multiplying all positions by a unit just permutes frequencies of each local conductor. [Local fibre counts in Lean](../PrimeFactors/ResidueCount.lean) · [Weil, *On some exponential sums*](https://doi.org/10.1073/pnas.34.5.204)

Set $D_h(t)=\sum_{j=0}^{h-1}e^{2\pi i jt}$. For $r=h\bmod d$, orthogonality gives
$$
 \sum_{a=1}^{d-1}|D_h(a/d)|^2=r(d-r)\le dh .
$$
At nonzero frequencies, each complete block of $d$ terms vanishes. Summing the remaining $r$ terms in squared modulus over all $d$ frequencies gives $dr$. The zero frequency for this shortened sum contributes $r^2$.

Center the block at $c$. The triangularly weighted survivor count is $T=\sum_{0\le i,j<h} f(c+i-j)$. The zero Fourier mode gives $\alpha h^2$. Each conductor $d>1$ contributes at most $\alpha b_d\,r(d-r)$ in absolute value, since the primitive frequencies form a subset of the nonzero frequencies modulo $d$. Therefore
$$
 |T-\alpha h^2|
 \le\alpha\sum_{\substack{d\mid M\\d>1}} b_d (h\bmod d)(d-(h\bmod d))
 \le\alpha h B_M.
$$
Each integer position in the block has weight at most $h$. Dividing the lower bound for $T$ by $h$ proves the count. The divisor sum also gives a sharper input-dependent guarantee when some $d$ divide $h$.

Uniformly in $N$, $1+p b_p=O(\sqrt p)$ and $n_p/p\ge1/3$. Since $\omega(M)=O(\log M/\log\log M)$, this gives $B_M\le M^{1/2+o(1)}$ and $\alpha\ge M^{-o(1)}$. Choose $h=\lfloor(W+1)/2\rfloor$. Under $M\le W^{2-\varepsilon}$, the resulting $B_M=o(W)$ proves the opening assertion, including when the prime set is chosen from $N$. The exponent $1/2$ is a sufficient uniform scale for this Fourier estimate. The optimal worst-case block length remains open here.

For example, take $N=143$ and $M=17\cdot19\cdot23=7429$. The three local sets leave 792 residues. The formula gives a survivor in every block of 2,195 consecutive positions. Explicitly sorting the 792 residues gives maximum cyclic gap 46, so 46 positions suffice in this example. One can reproduce the check by marking all $s$ with $s\bmod p\in\{(x+N x^{-1})\bmod p:1\le x<p\}$ at each of the three primes and including the gap that wraps across zero.

## Typical blocks and the mean spacing

For a uniform random starting residue $c\bmod M$, let $Z_H(c)=\sum_{j=0}^{H-1}f(c+j)$ and $C(d)=\sum_z f(z)f(z+d)$. Exact finite identities give
$$
 \mathbb E Z_H=\alpha H,\qquad
 \mathbb E Z_H^2=\frac1M\sum_{0\le i,j<H}C(j-i).
$$
They hold even when $H>M$. Parseval applied to the centered count gives the following finite upper bound for every $H\ge1$:
$$
 \frac{\operatorname{Var} Z_H}{(\alpha H)^2}
 \le \frac1{H^2}\sum_{\substack{d\mid M\\d>1}} b_d^2 (H\bmod d)(d-H\bmod d)
 \le \frac{\prod_{p\mid M}(1+p b_p^2)-1}{H}.
$$
An empty block differs from its mean by the whole mean. Its probability is at most this relative variance. The same calculation bounds the proportion losing a prescribed fraction of their mean by Chebyshev’s inequality. [Finite moment identities in Lean](../PrimeFactors/SumGaps.lean)

There is also an asymptotic law at the finer scale $s_M=1/\alpha$, the exact mean distance between survivors. For fixed $N$ and squarefree wheels coprime to $2N$ with $\omega(M)\to\infty$, successive cyclic gaps divided by $s_M$ have joint limiting distribution equal to independent exponentials of mean one. In particular, the proportion of survivor-to-survivor gaps larger than $\lambda s_M$ tends to $e^{-\lambda}$ for fixed $\lambda\ge0$. This is an application of Granville and Kurlberg’s general CRT spacing theorem. They already describe related hyperelliptic applications. [Granville–Kurlberg, Theorem 1 and remarks following Corollary 2](https://kurlberg.github.io/eprints/crt.pdf#page=3)

The same limit answers a question about uniformly chosen *starting positions*. A cyclic gap of integer length $g$ contributes exactly $\max(g-H,0)$ starts of empty length-$H$ blocks. With $H=\lfloor\lambda s_M\rfloor$, the empty fraction is therefore the empirical average of $(g/s_M-H/s_M)_+$. Each normalized gap distribution has mean exactly one, so this average equals $1-\mathbb E\min(g/s_M,H/s_M)$. The clipped function is bounded and continuous. The exponential spacing law gives the limit $e^{-\lambda}$. Thus the mean spacing is the sharp transition scale for a randomly translated block.

Here is the local hypothesis of that theorem for the factor-sum sieve. Fix $k$ and $k$ distinct shifts modulo $p>k$. The number of translates on which all $k$ positions survive is
$$
 p(n_p/p)^k+O_k(\sqrt p),
$$
uniformly in the shifts and in $p\nmid 2N$. Away from at most $2k$ branch roots, the local indicator is $(1+\chi(X^2-4N))/2$. Expand the product. Every nonempty term is a quadratic character of a product of shifted quadratics. Over the algebraic closure each quadratic has roots $h+a,h+b$ for distinct $a,b$, with the shifts relabeled by negation if necessary. In any nonempty set of fewer than $p$ shifts there exists $h$ in the set with $h+a-b$ outside it. Otherwise the set would contain the $p$ points of an entire orbit under translation by $a-b$. Hence $h+a$ occurs once in the product. The character-sum polynomial has a simple root and Weil's bound gives $O_k(\sqrt p)$, including when other roots coincide. The empty term gives $p/2^k$, within $O_k(1)$ of $p(n_p/p)^k$. For each $k$ the finitely many primes $p\le k$ are absorbed in the constant. The densities $n_p/p$ stay bounded away from zero and one. These are the hypotheses of the CRT spacing theorem. [Simple-root proof in Lean](../PrimeFactors/SumGaps.lean) · [Cochrane–Pinner on Weil bounds for rational-function sums](https://www.math.ksu.edu/~cochrane/research/stepmix.pdf)

The cyclic spacing law describes typical positions in the full residue system. A balanced factor sum selects one particular interval from $N$. The finite all-block bound applies to that interval whenever its wheel is in range. Deciding which local survivors give an integer-square discriminant, or efficiently searching a wheel outside this range, remains the factoring problem. Lean checks the simple-root obstruction, the exact first and second moments, and the nonzero Fourier energy at each conductor. The uniform bound uses the classical Kloosterman estimate and Fourier argument above, and the spacing limit uses the cited analytic theorems.
