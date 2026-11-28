# Which modular counts reveal the prime sum?

For a product $N=pq$ of distinct odd primes $p<q$, exactly **$N(p+1)(q+1)$** ordered triples of residues satisfy $x^2+y^2+z^2\equiv-1\pmod N$. Call this count $C_N(-1)$. If someone supplies it, division by $N$ and subtraction of $N+1$ give $p+q$. For $N=15$, counting the triples gives 360. The sum is $360/15-16=8$, and the two numbers with product 15 and sum 8 are 3 and 5. Evaluating the formula as written requires the hidden primes. Finding a cheaper way to obtain the count from one large $N$ remains open. [Lean proof](../PrimeFactors/ConeUnitTarget.lean) · [Tóth, Proposition 14, specializing to three squares](https://arxiv.org/pdf/1404.4214#page=8)

## Which targets give the sum, and which give the gap?

For any target $t$ coprime to $N$, the Jacobi symbol $J=\left(\frac{-t}{N}\right)$ can be computed from $t$ and $N$ alone. It tells us how to interpret the exact count $C_N(t)$. The distance from $C_N(t)/N$ to $N+J$ equals $p+q$ when $J=1$ and $q-p$ when $J=-1$. For the same product 15, the target $t=1$ gives 180 triples and $J=-1$. The distance from $180/15=12$ to $15-1=14$ gives the gap 2. Either the sum or the gap determines the prime pair once the product is known. [Lean proof of the two cases](../PrimeFactors/ConeUnitTarget.lean)

## When another count repeats the information

| Count | What its exact value adds |
| --- | --- |
| Three squares at a coprime target, now modulo $N^2$ | The count is exactly $N^2 C_N(t)$ for every lift of $t$. At $N=15$, target $-1$ gives $225\cdot360=81{,}000$ triples modulo 225. The extra digit of the target leaves the count unchanged. [Lifting proof](../PrimeFactors/ConeTargetLifts.lean) |
| A projective line, with a slope or infinity chosen separately at each prime | There are $(p+1)(q+1)=C_N(-1)/N$ points. The ordinary slopes account for $N$ of them. The other three cases contribute $p$, $q$, and 1, so counting the boundary alone gives $p+q+1$. At 15, the 24 points include 9 on the boundary. [Chart counts](../PrimeFactors/ProjectiveChartComplement.lean) |
| Two squares, $x^2+y^2\equiv t\pmod N$, for coprime $t$ | Every such target gives the same circle count. Under the classical Gauss formula, six times this count gives the number of ordered, signed integer triples on the sphere of radius $N$ whose coordinates have gcd 1. Lean checks the modular identity unconditionally and takes the classical formula as a hypothesis for the sphere comparison. At 15 the counts are 16 and 96, both checked directly. [Circle and sphere proofs](../PrimeFactors/SphereCircleIdentity.lean) |

The coprimality condition matters. At target zero the three-square count modulo $N$ is always $N^2$, already known from the product. Keeping the target at zero and changing the modulus to $N^2$ gives the earlier prime-sum formula when $5\le p<q\le2p$. For targets $t=Nu$ with $u$ coprime to $N$, the squared-modulus count instead equals $N^2$ times the primitive zero-target count at modulus $N$. At $N=15$, the counts modulo 225 are 71,775 for target zero and 43,200 for target 15. [Proof covering every integer target](../PrimeFactors/ConeTargetLifts.lean) · [Zero-target counts and worked example](what-changes-when-we-count-modulo-the-square-of-the-product.md)
