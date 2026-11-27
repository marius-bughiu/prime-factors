# How much can higher prime powers save after the second digit?

Choose **any finite set of odd primes** that do not divide the product $N$. Check possible factor sums modulo the square of each chosen prime. Raising those same primes to **any higher powers**, with a different exponent allowed at each prime, can reduce the surviving fraction by **less than a factor of four**. In a direct comparison over a complete joint period, **more than one quarter** of the sums that passed the original tests still pass. The bound holds for every such product and set, however many primes are selected. [Lean theorem on the joint density](../PrimeFactors/PrimePowerWheelDensity.lean)

This gives a reason to distinguish a *new prime* from *another digit at a familiar prime*. The theorem caps what the second choice can accomplish once the first two digits are known. It measures the fraction of positions across a complete repeating pattern. A particular short interval can have a different fraction, and a new prime can rule out a sum that survives at every power of the earlier primes. [Finite-width examples](when-a-prime-square-rules-out-a-sum.md)

## Where four comes from

Let $H_e$ be the number of sum residues that pass modulo $p^e$. At a nonsquare product residue every allowed first digit lifts at every depth, so the passing fraction $H_e/p^e$ is constant. At a square product residue, some lifts are lost at **every** new digit. Yet $pH_e-H_{e+1}$ is just $2(p-1)$ for odd $e$ and $p-1$ for even $e$. Those are counts in the *whole* next period of $p^{e+1}$ positions, so the losses become small fractions very quickly. The exact local count uses the modular hyperbola formulas of Bower, Evans, Luo and Miller. [Original formulas](https://arxiv.org/abs/1212.2930) · [Exact losses at successive depths](../PrimeFactors/PrimePowerEssentialDigits.lean)

Dividing the density at $p^2$ by its lower bound at any deeper power gives at most

$$ R(p)=1+\frac{2p+4}{p(p^2-2p-1)}. $$

At $p=3$ the factor is $8/3$. At $p=5$ it is $6/5$. For large primes its excess over one decays as $2/p^2$. The Chinese remainder theorem lets us multiply these bounds exactly at the level of complete-period densities. [Local density inequality](../PrimeFactors/PrimePowerDensityRatio.lean) · [Multiplication of densities](../PrimeFactors/PrimePowerWheelDensity.lean)

The numerical constant needs only finite arithmetic and a telescoping product. Multiply the eight values $R(p)$ from 3 through 23. For each odd integer $m\ge25$, bound $R(m)$ by $m^2/((m-2)(m+2))$. Including every intervening odd integer enlarges the upper bound. In the product from 25 to an odd endpoint $M$, all interior factors cancel, leaving $(25/23)M/(M+2)$. Multiplying the first eight values by $25/23$ already gives less than four. [Uniform product bound](../PrimeFactors/PrimePowerRatioProduct.lean)

## How close does an example come?

At **94,579**, which is $271\times349$, the product is a square modulo every odd prime through 23. We selected this product for that property. Raising all eight of those primes from their squares to their eighth powers gives a reduction between **3.6466 and 3.6467 times** over the common period. The count comes from the local formulas. The factorization checks the example's origin. The calculation of the densities reads only $N$ and the moduli. [Example and exact integer comparison](../PrimeFactors/DeepDigitDensityExample.lean)

## Can a polynomial provide an independent test at the same modulus?

Suppose we try squaring both unknown factors, or applying the same polynomial $f$ to both, and ask whether the new product and sum are locally possible. Every candidate that passed the original test necessarily passes the transformed one. There is a short way to see exactly what was reused. Modulo $X^2-sX+N$, the polynomial has a remainder $uX+v$. The transformed sum is $us+2v$, the transformed product is $u^2N+uvs+v^2$, and the transformed discriminant is precisely $u^2(s^2-4N)$. An invertible $u$ gives an equivalent test. The proof includes even and composite moduli. [Polynomial remainder and equivalence proofs](../PrimeFactors/PolynomialSumFilters.lean)

At $N=40,309$, the candidate 402 fails modulo 9. Squaring both proposed factors gives transformed product 4 and sum 4 modulo 9, which the residues 2 and 2 satisfy. Applying this transformation alone would lose the original rejection. The redundancy theorem concerns the same modulus and the same proposed sum in both tests. [Checked example](../PrimeFactors/PolynomialSumFilters.lean)

## Powers of two

For odd $N$, the binary tests have their own periods. When $N$ is 3 or 7 modulo 8, the pattern stabilizes modulo 8. For $N$ equal to 5 modulo 8 it stabilizes modulo 32. For $N$ equal to 1 modulo 8 the move from 16 to 32 changes no decision, and from 64 onward the least period is the whole modulus. In that last case every further digit can distinguish some candidates. [Least periods and the exception at 32](../PrimeFactors/DyadicSumPeriods.lean)
