# How many products admit a short rational shift?

Every product of two distinct primes has an exact positive rational shift at its floor square root. The denominator can be large. Among all unordered pairs of distinct 1,024-bit primes whose product has 2,048 bits, **fewer than one pair in $2^{416}$** has a reduced shift denominator at most $2^{128}$. This counts successes even when the best numerator and denominator can be selected after seeing the product. [Lean population bound](../PrimeFactors/RationalFloorShift.lean)

## What the product supplies

Given $N=pq$, compute $r=\lfloor\sqrt N\rfloor$ and $D=N-r^2$. The outstanding quantity is $J=p+q-2r$. Expanding $(p-h)(q-h)=(r-h)^2$ gives $hJ=D$. Both $D$ and $J$ are positive for distinct primes. Hence the unique shift is $h=D/J$, with reduced denominator $J/\gcd(D,J)$. A denominator of one recovers the previously counted integer family. [Integer shift identity](../PrimeFactors/FloorSquareShift.lean) · [Integer shift coverage](../PrimeFactors/FloorSquareShiftPopulation.lean) · [Reduced denominator](../PrimeFactors/RationalFloorShift.lean)

If a reduced shift $a/b$ is supplied, then $a\mid D$ and $J=b(D/a)$. The proposed sum $2r+J$ can be checked by an ordinary discriminant square test and a multiplication. Giving only $b$ leaves a choice of divisors $a$ of $D$ coprime to $b$. Listing all such choices requires finding the divisors or testing candidates individually. The population bound grants the correct shift for free and assigns no time saving to finding it. [Shift proof](../PrimeFactors/RationalFloorShift.lean)

## Why bounding the denominator matters

Write $D=ag$, $J=bg$ in lowest terms. The identity $(r-p)^2=pJ-D=(bp-a)g$ shows $a\le bp$. In the strict case two positive integers have square product, so $bp-a=ux^2$ and $g=u\ell^2$ for positive integers $u,x,\ell$. It follows that

$$
 bp=a+ux^2,\qquad bq=a+u(x+b\ell)^2,\qquad br=a+ux(x+b\ell).
$$

Thus the two square coordinates differ by a multiple of $b$. These identities use $br$, which can be smaller than $\lfloor\sqrt{b^2N}\rfloor$. If $a=bp$, then $r=p$ and $q\le p+2$. [Coordinate and edge proofs](../PrimeFactors/RationalFloorShift.lean)

For $p<q\le H$, one has $D=a u\ell^2\le 2H$, $bu\ell^2\le H$, and $x\le\sqrt{bH/u}$. Fixing $b,u,\ell,x$ confines $a$ to one residue class modulo $b$. There are at most $3H/(bu\ell^2)$ possible smaller factors. Summing over the coordinates gives at most $18H\sqrt{H}/\sqrt b$ pairs for a fixed denominator, apart from the edge. Summing through denominator $B$ and including the edge gives the unconditional bound $36H\sqrt H\sqrt B+2H$. It counts integer pairs before any primality requirement. The full-width bound uses the project's independently proved lower bound on the number of eligible prime pairs. [Finite count](../PrimeFactors/RationalFloorShift.lean) · [Prime population denominator](../PrimeFactors/ChebyshevPrimeSample.lean)

## Three small products

For $713=23\cdot31$, $r=26$ and $D=37$. The true shift is $37/2$. After multiplying through by two, the shifted factors are $46-37=9$ and $62-37=25$, whose product is $15^2=(2r-37)^2$. The floor square root of $4\cdot713$ is 53 while $2r=52$.

Two other 14-bit products both have $D=45$ and reduced denominator 2. For $8509=67\cdot127$, the shift is $9/2$ and $J=10$. For $8881=83\cdot107$, the shift is $45/2$ and $J=2$. Those two pieces of information alone leave the true numerator undetermined. [Arithmetic controls](../PrimeFactors/RationalFloorShift.lean)
