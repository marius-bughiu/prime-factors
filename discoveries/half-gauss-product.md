# Can a product of the first half of the units reveal a prime?

For every product of two distinct odd primes with at least one prime congruent to 3 modulo 4, a single integer determined by the product reveals a prime by gcd. Even an approximation to this integer within $2^{512}$ suffices on a 2,048-bit input. The unresolved step is computing that approximation cheaply from the product. A direct evaluation checks at least $2^{2046}$ positions. [Lean results](../PrimeFactors/HalfGaussProduct.lean)

## The integer and the split

Given $N=pq$, form the **half Gauss factorial**. Multiply the positive integers through $\lfloor N/2\rfloor$ that are coprime to $N$, and take the least residue $R$ modulo $N$. All inputs to this definition are public. For example, $N=15$ gives the product $1\cdot2\cdot4\cdot7=56$, hence $R=11$ and $\gcd(15,12)=3$. [Cosgrave and Dilcher, *Extensions of the Gauss-Wilson theorem*, Theorem 2 and §4](https://ftp.gwdg.de/pub/misc/EMIS/journals/INTEGERS/papers/i39/i39.pdf)

| Input | Prime factors | $R$ | $\gcd(N,R+1)$ |
|---|---|---:|---:|
| 15 | 3 and 5 | 11 | 3 |
| 65 | 5 and 13 | 64 | 65 |
| 77 | 7 and 11 | 34 | 7 |
| 91 | 7 and 13 | 27 | 7 |

The residue is a sign modulo each prime. More precisely, using the Legendre symbol,
$$
R\equiv(-1)^{(q-1)/2}\left(\frac qp\right)\pmod p,
\qquad
R\equiv(-1)^{(p-1)/2}\left(\frac pq\right)\pmod q.
$$
Quadratic reciprocity gives opposite signs whenever at least one prime is 3 modulo 4. This includes every odd semiprime $N\equiv3\pmod 4$. Then $\gcd(N,R+1)$ is one prime, and $\gcd(N,R-1)$ is the other. If both primes are 1 modulo 4, the signs agree and $R$ is either $1$ or $N-1$. Cosgrave and Dilcher classified these residues and their multiplicative orders in 2008. Lean checks the two-prime formula directly from Wilson’s theorem, Euler’s criterion and quadratic reciprocity. [Published classification, §4](https://ftp.gwdg.de/pub/misc/EMIS/journals/INTEGERS/papers/i39/i39.pdf#page=9) · [Lean derivation and examples](../PrimeFactors/HalfGaussProduct.lean)

To see where the formula comes from, first skip only multiples of $p$. There are $(q-1)/2$ complete blocks of length $p$, each contributing $-1$ modulo $p$, and a tail contributing $((p-1)/2)!$. The remaining multiples of $q$ contribute $q^{(p-1)/2}((p-1)/2)!$. Removing them cancels the factorial. Euler’s criterion evaluates the remaining power of $q$ as the Legendre symbol. Interchanging $p$ and $q$ gives the second formula.

## How accurate would a shortcut have to be?

Let $q$ be the larger prime in an opposite-sign case. Exactly one of $R-1,R+1$ is a multiple $kq$ with $p\nmid k$. Consequently a public estimate $A$ with $|A-R|\le B$ satisfies $|A-kq|\le B+1$. May’s Theorem 10 gives a deterministic polynomial-time factoring algorithm from an approximation to such a multiple within $2N^{1/4}$, even when $k$ is unknown. For any 2,048-bit $N$ the inequality $(2^{512}+1)^4<16N$ leaves enough room for $B=2^{512}$. For example, the upper 1,536 bits of a zero-padded 2,048-bit representation of $R$ would suffice. The theorem gives an asymptotic complexity bound. Wall-clock performance at this bit length remains unmeasured. [May, Theorem 10](https://digital.ub.uni-paderborn.de/hsmig/download/pdf/3235#page=40) · [Lean proper-multiple reduction and width check](../PrimeFactors/HalfGaussProduct.lean)

Conversely, given the primes, evaluate the two Legendre symbols by the Jacobi algorithm and combine the resulting signs by the Chinese remainder theorem. This takes polynomial time in the bit length. Thus supplying the approximation above on this family is polynomial-time equivalent to supplying the factors.

## Costs and two possible shortcuts

A literal loop performs $\lfloor N/2\rfloor$ coprimality checks. For a 2,048-bit input that is at least $2^{2046}$ checks. An increasing scan that stops on a nonunit encounters the smaller prime $p$ after $p$ checks starting at 1. For two 1,024-bit primes this is at least $2^{1023}$. These are costs of the named evaluation methods. [Definition and proofs](../PrimeFactors/HalfGaussProduct.lean)

Choosing the more convenient member of each pair $\{u,-u\}$ multiplies the answer by a single overall sign. The same conclusion holds if each choice uses the whole input. Therefore any collection of such choices still produces only the two residues $R$ and $-R$ and gives the same unordered gcds. Extending the modulus by a fresh odd prime also loses the signal. Cosgrave and Dilcher’s Theorem 2 gives half Gauss factorial $1$ modulo any odd modulus with three distinct prime factors, hence also $1$ modulo its divisor $N$. [Lean representative-choice theorem](../PrimeFactors/HalfGaussProduct.lean) · [Cosgrave and Dilcher, Theorem 2(3)](https://ftp.gwdg.de/pub/misc/EMIS/journals/INTEGERS/papers/i39/i39.pdf#page=4)

## Public benchmark

The 77 fixture checks 38 positions and obtains residue 34, whose final gcd is 7. The 65 fixture checks 32 positions and obtains residue 64, whose final gcd is 65. The increasing scan encounters a proper divisor during the coprimality checks on both inputs, at positions 7 and 5 respectively. The fresh 2,048-bit control stops after 256 coprimality checks, all units. It leaves the product unfinished and more than $2^{2046}$ positions untested. The benchmark keeps that cofactor unresolved. Each row has a Lean receipt for its paid prefix and the two complete factorizations have prime certificates. [Benchmark fixtures](../benchmarks/half-gauss.json) · [Bounded product computation](../scripts/half_gauss_benchmark.py)
