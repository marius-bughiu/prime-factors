# How many random square relations split the product?

Suppose $N=pq$ for distinct odd primes. If independently sampled random squares have already given us $d$ independent ways to make a square product, the exact chance that at least one of those ways reveals a factor is **$1-2^{-d}$**. Ten independent dependencies suffice for a chance of $1023/1024$. Finding the relations that give those dependencies is the expensive step.

## What we sample and what we observe

Draw $x_i$ independently and uniformly from the units modulo $N$. This is possible using only $N$ by drawing a uniform residue and checking its gcd with $N$. A proper gcd already gives a factor. Observe $x_i^2\bmod N$ and use the observed residue to choose a nonzero signed integer $a_i\equiv x_i^2\bmod N$. A typical rule chooses the representative nearest zero and accepts it if its absolute value factors over a chosen list of small primes.

Condition on the positive-probability transcript of square residues, the accepted indices, and any independent randomness used to choose them. Selection, stopping, and the choice of signed representatives may depend on this information. For the probability calculation, keep the particular roots $x_i$ hidden until the gcd tests. With $m$ accepted rows there are exactly $4^m$ equally likely root tuples, even if several rows have the same residue. A deterministic choice of root or a selection rule that inspects its CRT signs needs a separate analysis. For example, three copies of the root $1$ modulo $65$ yield only trivial square congruences. A continued-fraction walk has its own source of roots. [A deterministic walk where every dependency fails](square-neighbor-period.md)

## Why the dimension gives the probability

Write the parity of each prime exponent of $|a_i|$ in a column, and include a coordinate recording whether $a_i<0$. Over $\mathbb F_2$, a vector in the kernel selects a subset $S$ in which each exponent and the number of negative entries are even. Let $D$ be this kernel or any chosen subspace of it, and write $d=\dim D$. Compute

$$X_S=\prod_{i\in S}x_i\bmod N,\qquad Y_S=\sqrt{\prod_{i\in S}a_i}\in\mathbb N.$$

The positive integer root $Y_S$ is obtained by halving the summed prime exponents. It is invertible modulo $N$ because every row came from a unit. Thus $z_S=X_S/Y_S$ modulo $N$ equals $+1$ or $-1$ at each of $p$ and $q$. Define $b(S)=1$ when those local signs differ and $b(S)=0$ otherwise. Exactly when $b(S)=1$, $\gcd(X_S-Y_S,N)$ gives one of the primes.

**The outcomes add under symmetric difference.** For $U=S\mathbin{\triangle}T$ and $I=S\cap T$, multiplying the two numerators gives $X_U\prod_{i\in I}a_i$ modulo $N$. Multiplying the two positive roots gives $Y_U\prod_{i\in I}|a_i|$. Consequently $z_Sz_T$ equals $z_U$ times the ordinary sign of $\prod_{i\in I}a_i$. That sign flips both CRT coordinates together, preserving their disagreement. Hence $b(S)+b(T)=b(U)$ over $\mathbb F_2$. Including the sign row and taking coherent positive integer square roots justify this identity for signed relations.

**Every linear outcome pattern is equally likely.** Fix one reference root of each residue for the proof. By CRT, the actual root differs by independent fair signs at $p$ and $q$. Their disagreement gives a fair bit $h_i$ in each row, independently across rows. Relative to the reference outcome $b_0$, the new outcome at $S$ is

$$b(S)=b_0(S)+\sum_{i\in S} h_i\pmod 2.$$

Every linear functional on $D$ extends to the $m$-dimensional row-selection space, with exactly $2^{m-d}$ possible extensions. Every disagreement vector has $2^m$ choices of the two local sign vectors. Therefore **each prescribed functional on $D$ occurs for exactly $2^{2m-d}$ of the $4^m$ root tuples**. In particular, the all-failure functional has probability $2^{-d}$. For an observed nonzero functional exactly $2^{d-1}$ members of $D$ split the number. Testing a basis suffices. Adding together previously tested dependencies gives an outcome fixed by their results. [Lean proofs of the CRT bijection, signed overlap identities and exact counts](../PrimeFactors/RandomRelationSigns.lean)

## An example with negative representatives

For $N=65$, condition on the signed representatives $-1,-4,-9$. Each has four roots, and the even-size subsets form a space of dimension two. Basis pairs $(1,2)$ and $(1,3)$ have positive roots $2$ and $3$. Across the 64 possible root triples, each of the four possible basis outcomes occurs 16 times. Thus 48 triples reveal a factor. For the particular roots $(8,16,54)$, the first gcd is $\gcd(8\cdot16-2,65)=1$ and the second is $\gcd(8\cdot54-3,65)=13$. The third pair must also split, and $\gcd(16\cdot54-6,65)=13$. Lean enumerates the 64 triples and the 16 that fail both basis tests. [Checked example](../PrimeFactors/RandomRelationSigns.lean)

## What it costs to collect the rows

For a fixed residue-only acceptance set containing $A>0$ distinct unit square classes, each uniform unit draw succeeds with probability $4A/\varphi(N)$. The expected number of such draws for $m$ accepted rows, allowing repetitions, is $m\varphi(N)/(4A)$. With $k$ prime coordinates plus the sign coordinate, $m\ge k+1+d$ guarantees kernel dimension at least $d$. These counts leave the cost of testing the representatives and finding dependencies to the implementation.

There is a concrete limit for a fixed list of $k$ primes and representatives with $0<|a_i|\le N$. Each exponent is at most $\lfloor\log_2 N\rfloor$, so $A\le 2(1+\lfloor\log_2 N\rfloor)^k$. For fixed $k$, even one accepted row therefore costs at least $\varphi(N)/(8(1+\lfloor\log_2 N\rfloor)^k)$ uniform unit draws in expectation. Growing the factor base changes both the acceptance rate and the number of rows needed. Dixon's original random-squares algorithm analyzes this tradeoff and gives a subexponential expected operation bound. The joint sign count here explains the usefulness of extra dependencies once collected. It supplies no cheaper way to obtain them for a general 2048-bit product. [Dixon, *Asymptotically Fast Factorization of Integers*, §§2–3 (1981)](https://pages.cs.wisc.edu/~cs812-1/dixon.pdf)
