# A prime from the direction of two sums

Starting with 26,441, we computed two sums using only the product and kept their last ten binary digits. This gave the residues 308 and 112. They encode the pair $(11,4)$, and $11^2+4^2=137$ divides 26,441. The other prime is 193. Getting the residues took 26,440 Jacobi-symbol evaluations. The short step was recovering 137 once the residues were available. [Certified example](https://marius-bughiu.github.io/prime-factors/#quartic-odd-direction) · [Search and decoder](../experiments/quartic_trace.py)

## Which inputs the formula covers

Suppose the only input is $N=pq$, with distinct primes $p,q\equiv1\bmod4$. Choose a public integer $d$ whose Jacobi symbol at $N$ is $-1$. Exactly one prime sees $d$ as a nonsquare. Call that prime $p$ for the remainder of the derivation. For any $c$, write $A(c)$ for the sum of the Jacobi symbols of $x(x^2-c)$ over $0\le x<N$. The complete-sum identity already recovers $p$ by taking the gcd of $N$ and $A(1)^2+A(d)^2$. We asked what information from the two sums the decoder actually needs. [Definition and proof of the identity](quartic-trace.md)

There are signed integers $h,u,v$ such that

$$A(1)=4hu,\qquad A(d)=4hv,\qquad u^2+v^2=p.$$

Here $h$ and $u$ are odd, and $u,v$ are coprime. To see this, factor each global sum into its local sums at $p$ and $q$. At $q$ the twist can change only the sign of the base sum. At $p$ the squared sums add to $4p$. Each base sum is 2 modulo 4, so halving the two base sums gives odd $u$ and $h$. The norm identity makes the other local sum even. Divide it by two and absorb the sign from $q$ to obtain $v$. Any common prime divisor of $u$ and $v$ would have its square divide $p$. Lean proves this decomposition for the actual Jacobi sums. [Formal decomposition](../PrimeFactors/TraceDirection.lean)

## Reading the direction

Choose $M=2^k>p$. For two 1,024-bit primes, $k=1024$ suffices whichever prime the selector picks. Given the two residues modulo $4M$, divide each by four and compute

$$r=\big(A(d)/4\big)\big(A(1)/4\big)^{-1}\pmod M.$$

The inverse exists since $hu$ is odd. The common $h$ cancels, so $v\equiv ru\bmod M$. A single $k$-bit slope $r$ is enough from here. Find a shortest nonzero integer vector $(x,y)$ satisfying $y\equiv rx\bmod M$ by two-dimensional Gauss reduction. Return $x^2+y^2$ after a divisibility check.

Every such vector has $M\mid uy-vx$. If its squared length is at most $p$, the determinant has absolute value at most $\sqrt{(u^2+v^2)(x^2+y^2)}\le p<M$. It must be zero. Primitivity of $(u,v)$ forces $(x,y)$ to be an integer multiple of it, and the only nonzero multiples of this length are its two signs. Since $(u,v)$ itself is available in the lattice, a shortest vector has norm squared exactly $p$. The proof checks the decoder's conclusion given the shortest-vector property. The executable uses the repository's exact integer Gauss reduction. [Lean recovery theorem](../PrimeFactors/TraceDirection.lean) · [Gauss reduction](../experiments/short_basis_sieve.py)

For 26,441 the decoder uses $M=256$. The inverse of $308/4=77$ gives $r=140$ after multiplication by $112/4=28$ modulo 256. Indeed $140\cdot11\equiv4\bmod256$. Reducing precision to $M=64$ gives the shorter vector $(5,-4)$. Its squared length is 41, which fails the divisibility check. Both runs computed the complete sums, and only the precision changed. [Precision comparison](../benchmarks/quartic-trace.json)

## Cost at 2,048 bits

With the equal-width promise the inputs to the slope calculation are two residues of 1,026 bits. The complete signed sums already have magnitude at most $4\sqrt N$ on this family, by the local norm identities. Thus halving the output width relative to $N$ alone does little for a direct sum. Its cost is $N-1$ Jacobi evaluations, each on integers of $O(\log N)$ bits, followed by a polynomial-time lattice calculation. On the 2,048-bit control the search chose $d=11$ and spent its budget of 128 symbol evaluations. The complete residues and both factors remain unknown to that run. [Capped control](https://marius-bughiu.github.io/prime-factors/#quartic-crossed-2048)

The open problem is how to compute the slope, or enough information about it, from the product at lower cost. Even a particular low bit can express a quadratic-residuosity decision. [What one bit determines](quartic-slope-bits.md)
