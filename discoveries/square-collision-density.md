# When two Fermat discriminants give a factor

For a positive input $N$, write $D(a)=a^2-N$ for the Fermat discriminant at an integer midpoint $a\ge\sqrt N$. Call two distinct midpoints a collision if $D(a)D(c)$ is an integer square. Such discriminants give identical quadratic-character signs at every odd prime coprime to their product. The dependence itself supplies a factor in the balanced search interval. The underlying congruence-of-squares method is classical. [Pomerance, *The Quadratic Sieve Factoring Algorithm*](https://math.dartmouth.edu/~carlp/PDF/paper52.pdf)

## Recovering a factor from two midpoints

Given $N,a,c$ with $a<c$, check the product with an integer square root. If $D(a)D(c)=r^2$, put $k=c-a$ and $h=ac-N$. Expansion gives
$$
(h-r)(h+r)=Nk^2.
$$
Here $h\ge0$ and $h^2>r^2$, so $h-r>0$. If $2c^2\le3N$, then $h+r\le 2h<2(c^2-N)\le N$. Thus both factors of $Nk^2$ are positive and less than $N$. If $N$ were coprime to $h-r$, it would divide $h+r$, which is too small. Consequently $1<\gcd(N,h-r)<N$. These range conditions include the entire midpoint interval $N\le a^2<c^2\le 9N/8$ for two distinct odd balanced primes. Lean proves the identity and the gcd result for every positive integer input. Given the pair, extraction takes one integer square root, one gcd and a constant number of arithmetic operations on $O(\log N)$-bit integers. [Lean proofs](../PrimeFactors/DiscriminantPencil.lean)

For $N=9017$ both 95 and 97 satisfy the factor-sum parity constraint. Their discriminants are 8 and 392, whose product is $56^2$. Taking $h=198$ gives $h-r=142$, $h+r=254$ and $\gcd(9017,142)=71$. The cofactor is 127. Neither midpoint is the true one, 99. For $N=2701$, the adjacent midpoints 52 and 53 have discriminants 3 and 108. In this case $k=1$, so the formula gives the exact factors $55-18=37$ and $55+18=73$. [Checked examples](../PrimeFactors/DiscriminantPencil.lean)

**The cutoff is sharp over integer inputs.** For every positive $t$, take $N=6t^2+6t+1$, $a=3t+1$ and $c=3t+2$. The discriminants are $3t^2$ and $3(t+1)^2$, but $h-r=1$. The excess $2c^2-3N=6t+5$ is linear in $t$ while $N$ is quadratic, so $c^2/N$ approaches $3/2$ from above. Every larger constant therefore admits trivial splits. The family includes the balanced semiprime $2773=47\cdot59$ at $t=21$. The sharpness assertion over infinitely many inputs does not require the members to be semiprime. [Lean cutoff family](../PrimeFactors/DiscriminantPencil.lean)

## A family with a product-only formula

Suppose $N=pq$ with $p\le q\le2p$ and $(2p+1)(2q+1)$ a square. Its root is odd, say $2a+1$. Expanding gives $a(a+1)=N+(p+q)/2$. In fact $a=\lceil\sqrt N\rceil$. If $a^2<N$, then $(p+q)/2<a<\sqrt N$, contradicting arithmetic–geometric mean. Write $m=\lceil\sqrt N\rceil$. If $a\ge m+1$, then $a(a+1)\ge m^2+3m+2>N+(p+q)/2$, since $p\le m$ and $q\le2m$. Thus $h=m(m+1)-N$ is the exact midpoint. Return $h\pm\lfloor\sqrt{h^2-N}\rfloor$ and check the product. The formula uses only $N$ and has polynomial bit complexity on this family. The unknown shifted-square condition is needed for guaranteed success. [Lean implementation and correctness](../PrimeFactors/DiscriminantPencil.lean)

### A checked 2048-bit instance

We constructed $u=88433\cdot 2^{495}+1$ and $v=102357\cdot 2^{495}+1$, then took $p=(3u^2-1)/2$ and $q=(3v^2-1)/2$. The two shifted factors have product $(3uv)^2$. Both primes have 1024 bits, $q/p$ is about 1.34, and their product has 2048 bits. The distance from the first Fermat midpoint to the true midpoint has 1018 bits. The shift test needs two integer square roots on this product, followed by exact divisibility and primality verification.

The benchmark reads just $N$, calls the formula with zero Fermat budget and compares the returned primes to the fixture. A second product, $34387$, reaches the same zero budget with its cofactor unresolved. For the larger primes the certificate generator proves that a known order $F$ divides $r-1$ for every prime divisor $r$ of the claimed prime. The inequality $F^2\ge p$ excludes a composite $p$ by its least prime divisor. This is a partial-factorization primality criterion of the Pocklington type. All modular powers and coprimality statements are checked by Lean. [Checked criterion](../PrimeFactors/PartialOrder.lean) · [Decimal benchmark inputs and outputs](../benchmarks/shifted.json)

## How frequently can short gaps work?

**Paper bound.** Let $X\ge3$ and $1\le K\le X$ be integers. Choose two distinct primes $X\le p<q\le 2X$. Among all these sorted pairs, the number admitting any collision at integer midpoints $N\le a^2<c^2\le 3N/2$ with $1\le c-a\le K$ is
$$
O\big(KX\log(2X)\log^2(2K)\big).
$$
In particular, for any fixed $\varepsilon>0$, the fraction admitting a gap at most $X/(\log X)^{5+\varepsilon}$ tends to zero as $X$ grows. The bound permits every midpoint in an interval larger than the balanced search interval. There is no assumption of randomness or independence among discriminants.

1. Write $u=h-r$ and $v=h+r$. Since $uv=pqk^2$ and $0<u,v<pq$, the primes must divide opposite sides. If both divided one side their product would divide it, and if one divided both sides it would share one side with the other prime. Thus for a given collision each prime has a unique side. Write the side containing $p$ as $Ap$ and the side containing $q$ as $Bq$. Then $AB=k^2$ and $2(ac-N)=Ap+Bq$. Substituting $c=a+k$ gives
   $$
   (2a+k)^2=(2p+B)(2q+A).
   $$
   For fixed $k$ there are at most $\tau(k^2)$ ordered pairs $(A,B)$, including either assignment to the smaller prime. Here $\tau$ counts positive divisors.
2. Fix such $A,B$. The two positive shifted integers on the right must have the same squarefree part $d$, so each has the form $dt^2$. Since $\min(A,B)\le k\le X$, the smaller shift gives $d\le5X$. An interval of length $2X$ contains at most $1+\sqrt{2X/d}$ numbers of the form $dt^2$ for nonnegative $t$. Indeed if its first and last indices differ by $j$, the terms differ by at least $dj^2$. This holds for both shifted intervals regardless of their positions. Summing $(1+\sqrt{2X/d})^2$ over all integers $1\le d\le5X$ gives $O(X\log(2X))$ possible pairs, even allowing composite $p,q$.
3. The divisor bound $\tau(k^2)\le\tau_3(k)$ follows on prime powers from $2e+1\le(e+1)(e+2)/2$. Here $\tau_3(k)$ counts ordered positive triples with product $k$. Summing over the first two coordinates gives $\sum_{k\le K}\tau_3(k)\le K(\sum_{i\le K}1/i)^2$. Summing the previous count over $k$ proves the bound. The prime number theorem gives $\binom{\pi(2X)-\pi(X-1)}2\asymp X^2/(\log X)^2$ sorted prime pairs. Dividing gives the claimed fraction. [Prime number theorem project](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd)

This also applies to any fixed power saving $K\le X^{1-\varepsilon}$ for $0<\varepsilon<1$. For most inputs in this distribution, searching harder for collisions at those distances cannot succeed even if the smaller midpoint can be chosen anywhere in the interval. Long-distance pairs, relations among three or more discriminants, and differently generated congruences remain open routes. The Lean library checks extraction once a pair is supplied. The count above is a paper deduction.
