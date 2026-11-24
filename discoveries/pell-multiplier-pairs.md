# Reusing unsuccessful continued-fraction searches

The input is the product of two distinct odd primes. On $77{,}837$, three continued-fraction calculations each ended with a number coprime to the input. Combining their three remainders gave $277$ and $281$. Every calculation used only the product and public search limits. On an existing 2,048-bit example, the same method exhausted 65,536 steps before reaching even its first useful remainder. [Benchmark and controls](../benchmarks/pell-pairs.json) · [Implementation](../experiments/pell_pairs.py)

Schoof’s classical factoring algorithm tries auxiliary primes, or pairs of primes, to find an ambiguous quadratic form that splits the input. Here we analyze a schedule in which every pair shares one publicly selected prime. We also retain the square congruence obtained when a pair fails. Combining square relations is classical in continued-fraction factorization. We make no historical priority claim for that operation. Schoof used estimates of regulators and giant steps. The bounded experiment here uses an ordinary continued-fraction walk. [Schoof, §6, pp. 272–274](https://gkorpal.github.io/files/Schoof1982.pdf#page=38) · [Morrison and Brillhart](https://doi.org/10.1090/S0025-5718-1975-0371800-5)

## What happens at the middle of a period

First suppose $N=pq$ with both primes $1\bmod 4$. List distinct auxiliary primes $r\equiv3\bmod4$ with Jacobi symbol $(r/N)=-1$. Test each gcd first. Attach a hidden label according to which of $p,q$ sees $r$ as a quadratic nonresidue. Exactly one does. The labels are used only in the proof. For two listed primes $r,s$ satisfying $4rs\le N$, expand the ordinary continued fraction of $\sqrt D$ with $D=Nrs$.

In the standard complete quotients $(P_j+\sqrt D)/Q_j$, the period is even. An odd period would solve $x^2-Dy^2=-1$, which is impossible modulo $r$. At the middle of the period $P_j=P_{j+1}$, equivalently $2P_j=a_jQ_j$. The preceding convergent $A/B$ satisfies $A^2-DB^2=(-1)^jQ_j$. Here $1<Q_j<2\sqrt D\le N$ and $D=P_j^2+Q_jQ_{j-1}$. The strict lower bound follows because the first return to denominator one ends the period. These are classical continued-fraction identities. The code updates $A$ modulo $N$ throughout. [Continued fractions and factoring](https://arxiv.org/abs/2103.14861)

Write $Q=Q_j$. It is odd. If $4\mid Q$, the center equation makes $P_j$ even, inconsistent with $D\equiv1\bmod4$. If $Q\equiv2\bmod4$, the signed norm is impossible because squares modulo four are zero or one. Thus $Q\mid P_j$ and $Q\mid D$. A proper $\gcd(Q,N)$ gives the split immediately. Otherwise $Q\mid rs$. The only remaining possibility is $Q=rs$. Indeed $Q=1$ was excluded, and either sign of a single auxiliary prime has Jacobi symbol $-1$ modulo $N$, whereas the coprime square $A^2$ has symbol $+1$. [Lean center and denominator lemmas](../PrimeFactors/PellMultiplier.lean)

The **sign is positive** on a failed pair. If $A^2-NrsB^2=-rs$, both distinct primes $r,s$ divide $A$. Division by $rs$ then gives $NB^2\equiv1\pmod r$. This contradicts $(N/r)=(r/N)=-1$ by quadratic reciprocity, since $N\equiv1\bmod4$. The remainder of $A$ is therefore a square root of $rs$ modulo $N$. If $r,s$ have different hidden labels, their product is a nonresidue at both input primes. This proves that every pair of opposite labels splits $N$ at its center. [Lean sign and nonresidue proofs](../PrimeFactors/PellMultiplier.lean)

## Which auxiliary pairs need a walk?

Choose the first eligible prime as an anchor. If both hidden labels occur in a list of $m$ eligible primes and all pair products satisfy the size limit, at least one of the $m-1$ pairs joining the anchor to the other primes splits $N$. This replaces trying up to $m(m-1)/2$ pairs from the same list. It bounds the number of walks. A walk up to its midpoint can still take many continued-fraction steps.

The public cutoff can be made explicit. The residue modulo four and the two Legendre symbols define a surjection from the units modulo $4N$ to three independent signs by CRT. Each orientation with auxiliary prime $3\bmod4$ is therefore an index-eight coset. Theorem 1.4 of Lamzouri, Li and Soundararajan, assuming Dirichlet GRH, puts a prime in each such coset by $\max(10^9,(7\log(4N)+27+\tfrac52(\log\log(4N))^2)^2)$ for $4N\ge20000$. At 2,048 bits $\log(4N)<1422$ and $\log\log(4N)<8$, so the bound is one billion, and $4(10^9)^2<N$. No one-billion-prime search was run. This use of the released Dirichlet result and the published small-prime bound is a paper argument. [Least prime in a coset, Theorem 1.4](https://arxiv.org/html/1309.3595v3#S1.SS2) · [RH source and scope](../docs/research.md)

Given only $N\equiv1\bmod4$, try $D=N$ before the pair schedule. The product alone does not tell which of the two equal residue classes contains the primes. There are simpler choices for the other congruence classes. If both unknown primes are $3\bmod4$, take $D=N$. The same midpoint argument guarantees a nontrivial divisor of $N$ with no auxiliary prime. If $N\equiv3\bmod4$, use $D=rN$ with $r\equiv3\bmod4$, $(r/N)=-1$ and $4r\le N$. Among the two hidden orientations choose the one with $r$ a nonresidue at the input prime that is $1\bmod4$. Both $r$ and $-r$ are nonsquares there, so the center cannot give $Q=r$. The same coset bound guarantees this orientation somewhere in the public list. The pair benchmark below specifically exercises the case $N\equiv1\bmod4$.

## Three missed divisors can still give a factor

Suppose the three walks for pairs $(r,s),(r,t),(s,t)$ all miss. They yield $a^2\equiv rs$, $b^2\equiv rt$, $c^2\equiv st$ modulo $N$. Then $z=abc/(rst)\bmod N$ satisfies $z^2\equiv1$. The denominator is a unit. A proper $\gcd(z-1,N)$ is a factor. If $z\equiv\pm1$, the cycle has yielded no split. This requires one additional walk beyond the two anchor pairs. It makes no independence assumption about the three roots. [Lean triangle identity and numerical example](../PrimeFactors/PellMultiplier.lean)

For $N=77{,}837$ the first three eligible primes are 3, 19 and 23. The following are counts of continued-fraction updates. The symmetry test uses the newly computed quotient in the same update.

| Auxiliary pair | Steps to center | Center denominator | Convergent numerator modulo $N$ |
| --- | ---: | ---: | ---: |
| 3, 19 | 182 | 57 | 65,162 |
| 3, 23 | 90 | 69 | 28,501 |
| 19, 23 | 554 | 437 | 64,425 |

All three denominators are coprime to the input. Combining the three roots gives $z=39{,}058$ and $\gcd(z-1,N)=277$. The other factor is 281. The two anchor pairs alone exhausted this list after 272 updates. A total cap of 825 stopped one update before the third center and left the input unresolved. Trial division is faster at this size. The example demonstrates how to reuse the outputs of unsuccessful walks. [Reproducible fixture](../benchmarks/pell-pairs.json)

A triangle can also give the trivial root. For $N=2173=41\cdot53$, the eligible primes 7, 11 and 47 give positive square roots 990, 1598 and 1563 for the pair products 77, 329 and 517, in that order. Their normalized product is one. On the 2,048-bit fixture the first pair, 7 and 19, used the whole budget without reaching a center. Computing centers cheaply enough on ordinary large products remains the main open question on this route.
