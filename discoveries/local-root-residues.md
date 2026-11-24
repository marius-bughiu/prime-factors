# How much does the product residue tell us about the mixed root?

For balanced semiprimes with a specified residue $N\bmod M$, the unknown quotient in the Salié decoder can attain every value modulo an odd prime $\ell\mid M$ allowed by the elementary square test. On the family below, its limiting distribution is exactly the distribution obtained by squaring a uniform residue. Consequently a predictor using the product residue alone can guess the quotient with probability at most $2/\ell+o(1/\ell)$. This is an asymptotic statement about a specified input distribution. The decoder itself has access to the entire product. [Recovering residues from Salié samples](recovering-residues-from-sums.md)

## What completing the period gives

Let $N$ be a product of distinct odd primes, $(b,N)=1$, and $\ell$ an odd prime coprime to $N$. For each $j\bmod\ell$, the number of $a\bmod N\ell$ satisfying $a^2\equiv b^2+Nj\pmod{N\ell}$ is exactly

$$
 4\bigl(1+\chi_\ell(b^2+Nj)\bigr),
$$

where $\chi_\ell$ is the Legendre symbol extended by zero. There are four roots modulo $N$ and independently zero, one or two roots modulo $\ell$. This complete-period count is identical for all semiprimes with the same $N\bmod\ell$. The decoder asks which residue belongs to a particular integer representative of a mixed root inside a short interval. [Four-root identity](divisor-samples.md#which-root-enters-the-answer)

## A balanced family with the same observed product residue

Fix a large prime $p$, an integer $M<p$, an odd prime $\ell\mid M$ and a unit $s\bmod M$. Let $q$ range over primes in $[p/2,p)$ with $q\equiv s\pmod M$ and let $P$ be their number. Thus all inputs $N=pq$ give the observer the same residue $ps\bmod M$. For each $q$ let $k$ be the least positive residue of $2q^{-1}\bmod p$. **Condition on $k\le p/3$** and choose $q$ uniformly in this subfamily. Then $a=kq-1$ satisfies $a\equiv1\pmod p$, $a\equiv-1\pmod q$, and $0<a<N/3$. This is the decoder’s centered branch $b=1$. Its quotient is the integer

$$
 \kappa=\frac{a^2-1}{N}=\frac{k(kq-2)}p.
$$

For any fixed $A>0$, uniformly for $M\le(\log p)^A$ and the indicated choices of $s,\ell$, write $\nu=ps\bmod\ell$. For each $j\bmod\ell$ we claim

$$
 \Pr(\kappa\equiv j\pmod\ell\mid k\le p/3,\ q\equiv s\pmod M)
 =\frac{1+\chi_\ell(1+\nu j)}{\ell}+o_A(1/\ell).
$$

In particular the singular square value occurs with probability asymptotic to $1/\ell$, and every nonzero square value with probability asymptotic to $2/\ell$. A nonsquare gives probability zero exactly. As $p$ grows, the conditioning keeps a fraction tending to $1/3$ of the primes in the specified progression.

## Counting the possible residues

For each $r\bmod\ell$, let $B_r$ be the arithmetic progression $1\le k\le p/3$ with $k\equiv r\pmod\ell$, viewed inside $\mathbb F_p$. Let $D$ be the progression of all integers $q\in[p/2,p)$ congruent to $s\bmod M$. The number of primes $q$ in $D$ with $2q^{-1}\in B_r$ equals

$$
 \frac{|B_r|}{p}P+O_\epsilon\!\left(p^{31/32+\epsilon}\log^2p\right),
 \qquad |B_r|=\frac{p}{3\ell}+O(1).
$$

To see this, expand both progression indicators in normalized additive Fourier series modulo $p$. For any such progression the sum of absolute Fourier coefficients is $O(\log p)$ uniformly in its length and step. Multiplication by the nonzero step permutes the frequencies, and the geometric-series bound for frequency $0<|h|\le p/2$ is $1/(2|h|)$ after this permutation. Keep the zero frequency of $B_r$ before expanding $D$. It gives $|B_r|P/p$ exactly. Every remaining term is a sum over primes $q<p$ of

$$
 e_p(uq+v/q),\qquad v\ne0,\qquad e_p(z)=\exp(2\pi i z/p).
$$

Fouvry and Michel’s Theorem 1.1 bounds each sum uniformly by $O_\epsilon(p^{31/32+\epsilon})$. Its prime modulus is $p$, and its prime summation limit is also $p$. For $u\ne0$ one takes the rational function $(X^2+c)/X$ with $c\equiv v/u\pmod p$ nonzero and the nontrivial character $z\mapsto e_p(uz)$. For $u=0$ take $1/X$ and $z\mapsto e_p(vz)$. In both cases the numerator and denominator are monic and coprime and the reduction has a genuine pole. The theorem’s constant depends only on the degrees and $\epsilon$. Its exponents at length $p$ add to $3/16+25/32=31/32$. Summing against the two Fourier coefficient sequences proves the displayed count. [Fouvry and Michel, Theorem 1.1](https://numdam.org/item/10.1016/s0012-9593%2898%2980019-0.pdf)

The same calculation for the whole interval $1\le k\le p/3$ gives $(1/3+O(1/p))P$ with the same error. The Siegel–Walfisz theorem gives $P\sim p/(2\varphi(M)\log p)$ uniformly in the stated range. Thus the errors are $o_A(P/\ell)$, for example on fixing $\epsilon=1/64$. Conditionally, $k\bmod\ell$ is uniform up to $o_A(1/\ell)$ per class. Multiplication by $s$ and subtraction of one permute the residues, so the same holds for $a\equiv ks-1\pmod\ell$. Finally $a^2\equiv1+\nu\kappa\pmod\ell$. Every target square has at most two preimages, which gives the claimed distribution and the sharp maximum prediction probability. [Walfisz’s prime progression estimate](https://doi.org/10.1007/BF01218882)

The missing information is the position of the mixed root inside the chosen interval. The complete-period formula requires one Legendre-symbol calculation, whereas observing the centered representative by the available contraction costs $2^{O(n/\sqrt{\log n})}$ bit operations for an $n$-bit input. The distribution proof gives neither a lower bound on algorithms using the full $N$ nor numerical prediction odds at 2,048 bits. [Counting a centered Salié phase](counting-salie-phases.md)
