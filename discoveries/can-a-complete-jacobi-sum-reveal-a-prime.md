# Can a complete Jacobi sum reveal a prime?

Yes, if we can obtain the sum cheaply. For 2,183, six sums chosen using only the product reveal that its smaller prime is 37. The direct computation took 13,098 Jacobi-symbol evaluations. Trying the odd candidates allowed by the same size information took two divisions to find 37. The proofs identify exactly what the sums would have to tell us on a 2,048-bit input. An efficient way of obtaining those readings remains open. [Measured comparison](../benchmarks/square-mask-digit-queries.json) · [Full-width theorem](../PrimeFactors/CircleMarkMaskDigitReadout.lean)

## How one sum gives the smaller prime

Write $N=pq$ with distinct odd primes $p<q$. The Jacobi symbol modulo $N$ gives a score of $-1$, $0$ or $1$. Choose an integer polynomial $Q$ and add the score of $tQ(t)^2$ over **all** residues $t$ modulo $N$. Call this total $S_N(Q)$. Modulo each prime, multiplying by a nonzero square preserves the score. A root of $Q$ sets the score to zero. The unmodified scores sum to zero modulo each prime, and the Chinese remainder theorem makes the total modulo $N$ the product of the two local totals. [Factorization and root-count identities](../PrimeFactors/CircleMarkJacobiMask.lean)

Choose the roots $1^2,2^2,\ldots,L^2$ and write the resulting polynomial as $Q_L(X)=\prod_{i=1}^L(X-i^2)$. Put $u=(p-1)/2$, $v=(q-1)/2$ and $K=\lfloor\sqrt N/2\rfloor$. The positive square representatives visit every nonzero square modulo $p$ once before they start repeating. This gives

$$
S_N(Q_L)=\min(L,u)\min(L,v),\qquad
S_N(Q_K)=uK,\qquad p=1+2S_N(Q_K)/K.
$$

For $N=2{,}183$, the cutoff is 23 and the sum is 414, giving $1+2(414)/23=37$. This polynomial is optimal in degree for the specified reading. Every degree-$d$ integer polynomial satisfies $|S_N(Q)|\le\min(d,u)\min(d,v)$, and $Q_d$ attains that bound. Degree 22 can reach only 396 here. Polynomial degree alone does not price the operations needed to evaluate a polynomial or its complete sum. [Degree bound and approximation](../PrimeFactors/CircleMarkJacobiMaskDegree.lean) · [Measured prefix sums](../benchmarks/jacobi-square-masks.json)

## What changes at the next square?

Moving from $K$ roots to $K+1$ increases the total by exactly $u$. Each changed residue contributes an increase of one. These residues equal $(K+1)^2$ modulo $q$ and are nonsquares modulo $p$. For 35 the only two are 2 and 23. [Pointwise proof and example](../PrimeFactors/CircleMarkJacobiMaskIncrement.lean)

If the primes are balanced, meaning $q<2p$, evaluating the old polynomial at this one new square has a simpler interpretation. Its value is $(2K+1)!/(K+1)$. Exactly one index $i$ in the evaluation contributes a multiple of $p$, namely $i=p-K-1$, and none contributes a multiple of $q$. The gcd with $N$ is therefore $p$. For 2,183 this is $47!/24$, and index 13 gives $24+13=37$. This locates the factor in a product of consecutive integers, where factorial and product-tree methods already apply. [Boundary proof](../PrimeFactors/CircleMarkJacobiMaskEdge.lean) · [Related factorial methods](factorial-progressions.md)

## Can a polynomial with just two terms do the job?

For $Q=X^e-c$, the largest possible $|S_N(Q)|$ over all exponents and constants is $uv/2^{|v_2(u)-v_2(v)|}$, where $v_2$ counts factors of two. At 2,183 the maximum is 261, attained by $X^{261}-1$. The desired sum is 414. More generally, for balanced primes with $p\ge11$, every individual binomial misses $uK$ by more than $K/2$, the tolerance for rounding the inferred prime to the nearest odd integer. The proof of the maximizing exponent uses the hidden half-periods $u,v$. [Maximum and attaining exponent](../PrimeFactors/CircleMarkBinomialMaximum.lean) · [Rounding gap](../PrimeFactors/CircleMarkBinomialMask.lean)

A product of binomials with one common exponent and several constants has a different constraint. An exact match in magnitude requires at least $K/\gcd(v,uK)$ distinct constants modulo $q$. If $v$ is prime, this requires all $K$ constants. For $q=59$ that means 23, and the prefix construction attains 23 with exponent one. [Constant-count proof](../PrimeFactors/CircleMarkPowerTargets.lean)

## Reading one bit at a time

Choose a finite set $C$ of $d$ positive coordinates, all below $p$, with every distinct pair summing to less than $q$. Form $Q_C(X)=\prod_{x\in C}(X-x^2)$. Modulo $q$ the coordinates give distinct squares. Modulo $p$, two coordinates give the same square precisely when their sum is $p$. If $c$ unordered pairs have that sum, then $S_N(Q_C)=d(d-c)$. For a nonempty set, a reading within $d/2$ of the exact total suffices to decide whether any such pair exists. [Collision formula](../PrimeFactors/CircleMarkSparseMaskProbe.lean) · [Precision threshold](../PrimeFactors/CircleMarkMaskDigitReadout.lean)

For balanced primes, write the unknown offset $s=(2K+1-p)/2$ as a quotient and remainder in base $m=\lfloor\sqrt K\rfloor+1$. To test a bit, choose coordinates of the forms $K-2mj$ and $K+1-2i$. Their sum is $p$ precisely when $mj+i=s$. The construction keeps only positive coordinates and chooses the digit indices according to the bit being tested. For two 1,024-bit primes, at most 1,024 yes-or-no answers suffice, with polynomial degree at most $2^{513}$ per question. All questions can be chosen from $N$ before receiving the first answer. Each digit question can contain only one complementary pair, so its exact sum is $d(d-1)$ for yes and $d^2$ for no. [Two possible readings](../PrimeFactors/CircleMarkDigitQueryValue.lean) · [Coordinate construction](../PrimeFactors/CircleMarkDigitCoordinates.lean) · [Bit recovery and full-width bounds](../PrimeFactors/CircleMarkMaskDigitReadout.lean)

At 2,183 the six complete sums are 30, 36, 25, 25, 25 and 16. Only the first falls below its collision-free total of 36. The base-five digits are therefore 1 and 0, so $s=5$ and $p=47-2(5)=37$. Multiplication verifies $37\cdot59=2{,}183$. The recorded operations below count different kinds of work. [Six readings and operation counts](../benchmarks/square-mask-digit-queries.json) · [Single-prefix counts](../benchmarks/jacobi-square-masks.json)

| Method on 2,183 | What it returned | Recorded work |
| --- | --- | --- |
| Single degree-23 prefix | Sum 414 | 2,183 Jacobi evaluations and 50,209 modular multiplications by root terms |
| Six bit questions of degrees 4 through 6 | Digits 1 and 0 | 13,098 Jacobi evaluations, 67,673 modular multiplications by root terms and one final divisibility check |
| Try the six odd candidates from 35 through 45 | Factor 37 | Two divisibility checks in ascending order, five in descending order |

There is also a limit on how much these bit questions can cover. An odd pair sum needs one even and one odd coordinate. A set of $d$ coordinates can therefore cover at most $\lfloor d^2/4\rfloor$ distinct odd sums. This is attained for every even $d$. If $B$ fixed pair-membership questions distinguish $W$ abstract odd candidates, at most one candidate can receive all negative answers, so $4(W-1)\le B d^2$. The bound concerns this specific question format. An algorithm using divisibility or other information about $N$ can distinguish candidates in other ways. [Sharp one-set bound and fixed-question limit](../PrimeFactors/CircleMarkSparseMaskCapacity.lean)

## Where the Riemann hypothesis enters

The pinned Riemann-hypothesis repository's statements about zeros of zeta and Dirichlet $L$-functions motivated looking at character sums. Here the needed quantity is the signed count of roots of a specified polynomial at one specified composite modulus. The finite identities above have unconditional Lean proofs. We found no result in the cited statements that computes these readings at the required precision and cost from $N$ alone. [Pinned analytic statements](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab/src/Statements.lean) · [Project notes on RH assumptions](../docs/research.md)
