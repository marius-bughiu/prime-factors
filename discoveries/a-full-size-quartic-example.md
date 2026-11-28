# A 2,048-bit example for the quartic formula

Take $y=21{,}114{,}860\cdot2^{487}$ and form $N=1+4y^4$. Given only this $N$, the fourth-root formula returns two distinct **1,024-bit primes**. Lean verified the product has 2,048 bits, the two returned values are prime, and their product is exactly $N$. The fixture was constructed for the identity. [Lean proof](../PrimeFactors/FullWidthQuarticFixture.lean) · [Exact decimal input and outputs](../benchmarks/cases.json)

The construction lets us check what the search actually had to find. Integer division gives $\lfloor N/4\rfloor=y^4$, so its integer fourth root recovers $y$ directly. The remainder $N-4y^4=1$ gives the other coordinate. Sophie Germain’s identity then gives

$$p=2y(y-1)+1,\qquad q=2y(y+1)+1.$$

There is an equally short route using ordinary Fermat. Since $N=(2y^2)^2+1$, its first midpoint is $m=\lceil\sqrt N\rceil=2y^2+1$. The difference $m^2-N=(2y)^2$ gives $m-2y=p$ and $m+2y=q$. This holds for every positive $y$. The benchmark tests the published input with one midpoint and records the ordinary generated Lean certificate. [General first-midpoint and fourth-root identities](../PrimeFactors/FullWidthQuarticFixture.lean)

To find a prime-output fixture, we tried 28,669 successive multiples of five as multipliers $k$ in $y=k\cdot2^{487}$, starting at $5\cdot2^{22}$. We used small-prime screening before producing prime certificates. Both specific predecessors are divisible by $F=2^{490}$. The standalone Lean proof uses this order and the two digits of $(p-1)/F$ or $(q-1)/F$ in base $F$ to certify primality. The benchmark independently replays the repository’s ordinary certificates. These construction attempts measure the effort to select an example inside a special family. [Primality criterion](../PrimeFactors/CubicPlantedPrimality.lean) · [Verified population bound for the two formulas](reading-the-other-fourth-power.md)
