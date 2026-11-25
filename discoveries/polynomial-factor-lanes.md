# At most four possible factors for one remainder

Given a 2,048-bit odd number with two factors of comparable size, choose a possible remainder of one factor modulo $2^{616}$. From the product and that remainder alone, a polynomial of degree at most four gives **at most four integers** to test. Lean proves this for every remainder, including the correct one. We still need to find the correct remainder. [Universal Lean theorem](../PrimeFactors/QuarticWeightExistence.lean) · [Root-count proof](../PrimeFactors/QuarticFactorLane.lean)

Including the squares of both factors is what lets us use a smaller base. On the 2,048-bit comparison input, the complete search count fell from a 678-bit number to a 612-bit number, about **64 quintillion times fewer remainder pairs** than our earlier linear search. A quartic check costs considerably more. The first four groups took 12.01 seconds on our machine, against 0.044 seconds for four linear groups. Neither found a prime. A complete quartic search on that input still has more than $2^{611}$ groups. [Actual input, counts and times](../research/quartic-lane-holdout.json) · [What limits the linear search](curved-weight-limits.md)

One further saving comes from testing positive and negative roots of the same equation. On eight small inputs, this cut the number of equations from 2,068 to 1,036 and recovered all eight factorizations. The full-size comparison still has more than $2^{610}$ groups with this saving. [Proof and matched timings](quartic-sign-pairs.md)

For example, starting with **34,387**, the solver chooses base 70 and checks twelve remainder pairs. For the pair 41 and 67, write one candidate factor as $41+70k$. The polynomial returned for that group simplifies to $(2k^2+3k-27)^2=0$. Its only integer root is $k=3$, which gives $41+70\times3=251$. Dividing 34,387 by 251 gives **137**. The search needed only the product to generate all twelve groups and their equations. [Reproduce the example](../experiments/quartic_factor_lanes.py)

We subsequently recovered both primes of that same full-size comparison input by trying a remainder chosen after inspecting its published factors. A separate improvement tests more residues with each equation. [One-remainder result and control panel](testing-one-factor-remainder.md) · [New bounds using finite differences](difference-lanes.md)

The latest finite counting proof joins four of the original dyadic remainders in one degree-four equation. It applies to any balanced 2,048-bit prime pair. [Public theorem and explicit modulus](unit-newton-lanes.md)

## Why does a factor appear among the roots?

Let $N=xy$ with positive factors within a factor of two, $X=\lfloor\sqrt{2N}\rfloor$ and $R$ coprime to $N$. Both $x$ and $y$ are at most $X$. On the proposed remainder $x\equiv u\pmod R$, seek integer coefficients, at least one nonzero, for

$$P(x,y)=d y^2+b y+e+a x+c x^2.$$

Multiplying by $x^2$ and using $xy=N$ gives an ordinary polynomial
$$F(x)=dN^2+bNx+e x^2+a x^3+c x^4.$$
Expand $F(u+t)$ in powers of $t$. Require its first four coefficients to be divisible by $R^4,R^3,R^2,R$, respectively. When $x=u+Rk$, each term is divisible by $R^4$. Because $x$ is coprime to $R$, the same holds for $P(x,y)$. If the coefficients additionally give $|P(x,y)|<R^4$ on the balanced region, then $P(x,y)=0$. Distinct trace coefficients occur at distinct powers of $x$ in $F$. Thus $F$ is nonzero and has at most four integer roots. Division into $N$ and the original balance condition check each candidate. [Algebra and candidate guarantee](../PrimeFactors/QuarticFactorLane.lean)

For existence, put five nonnegative coefficients in a box with upper bounds $Q,L,C,L,Q$. There are $(Q+1)^2(L+1)^2(C+1)$ choices and at most $R^{10}$ possible lists of Taylor remainders. When the first count is larger, two choices agree. Their difference gives nonzero signed coefficients with the required divisibilities. It suffices that $2QX^2+2LX+C<R^4$. For every odd $N<2^{2048}$ the choices $R=2^{616}$, $Q=2^{413}$, $L=2^{1437}$, $C=2^{2461}$ meet both inequalities. Lean checks the full implication through to the four candidates. The solver constructs a relation directly by lattice reduction. [Finite counting proof and constants](../PrimeFactors/QuarticWeightExistence.lean)

## Constructing the polynomial

The solver uses the same five integer coordinates. Working from high to low powers in the Taylor expansion, it solves for one coefficient at a time modulo the appropriate power of $R$. The diagonal entries of this triangular lattice basis are $R^4,R^3,R^2,R,1$. The monomial coefficients $N^2,N,1,1,1$ are units modulo $R$. Thus these steps describe all solutions of the four congruences.

Scale the five columns by $X^2,X,1,X,X^2$. The scaled lattice has determinant $R^{10}X^6$. A short vector has small trace everywhere. The classical LLL bound in dimension five gives a first vector with Euclidean norm at most twice the fifth root of the determinant. Its sum of absolute coordinates is at most $\sqrt5$ times that norm. The implementation chooses $R$ with $R^{10}\ge 6^5 X^6$, verifies the sum is strictly below $R^4$, and checks all four congruences again before solving the polynomial in $k=(x-u)/R$. Rounding up to a smooth base allows the unordered remainder pairs to be streamed and counted exactly. The search reuses the repository's integer LLL and polynomial-root routines. The finite existence theorem is independent of that implementation. [Search implementation](../experiments/quartic_factor_lanes.py) · [LLL and integer-root routines](../experiments/norm_auxiliary.py) · [Original LLL theorem](https://doi.org/10.1007/BF01457454)

On eight fresh products of two 16-bit primes, the complete quartic, linear and trial searches all recovered every pair. Lean checked their primality and products. The quartic search used 2,068 lattice reductions and 4,994 root-isolation nodes. Its total of three-run median times was **0.847 seconds**, against **0.00337 seconds** for the linear method and **0.00231 seconds** for ordinary trial division. On 1,225 the search also recovered both balanced decompositions, $25\times49$ and $35\times35$. The resulting prime certificate records both copies of 5 and of 7. [Sampler and comparisons](../experiments/quartic_lane_holdout.py) · [Fixtures](../benchmarks/quartic-factor-lanes.json)

## Using higher powers

For $m\ge1$ use $y^m,\ldots,y,1,x,\ldots,x^m$. Multiplying by $x^m$ produces a polynomial of degree at most $2m$. Requiring the first $2m$ Taylor coefficients at $u$ to vanish at successively lower precisions again makes the trace zero. Lean proves membership among at most $2m$ roots for any supplied short relation. [General Taylor theorem](../PrimeFactors/PowerFactorLanes.lean)

In dimension $D=2m+1$ the scaled determinant is $R^{mD}X^{m(m+1)}$. The same LLL estimate suffices if

$$ R^m>\sqrt D\,2^{m/2} X^{m(m+1)/D}. $$

For fixed $m$, this puts the required base on the scale of $N^{(m+1)/(4m+2)}$. The exponent drops from $1/3$ to $3/10$ and approaches $1/4$. In each fixed dimension the basis reduction and extraction of integer roots can be done in time polynomial in the input bit length per remainder pair. Taking $m$ proportional to the input bit length in the explicit bound gives $R=O(N^{1/4})$. LLL in this growing dimension and polynomial root extraction have polynomial bit complexity per lane. There are still exponentially many pairs. This recovers the classical fourth-root scale for balanced divisors in a specified residue class. Faster general factoring algorithms exist. The contribution here is the explicit product-only construction, checked finite constants, and the comparison to what linear equations can cover. [Coppersmith, Howgrave-Graham and Nagaraj](https://dominoweb.draco.res.ibm.com/reports/rc23466.pdf) · [Harvey and Hittmeir](https://arxiv.org/abs/2105.11105)

For $N<2^{2048}$, the following powers of two suffice under that norm bound. The formal arithmetic uses $X^2\le2^{2049}$. The large degrees are theoretical estimates. In a separate full-size run at degree six, constructing and testing the first equation took 31.78 seconds and found no factor. The implementation can reproduce the bounded run with `python3 -m experiments.quartic_factor_lanes N --power 3 --max-orbits 1`, replacing `N` with the decimal fixture input. [Checked scale inequalities](../PrimeFactors/PowerFactorScale.lean) · [Full-size input](../benchmarks/quartic-factor-lanes.json)

| Maximum polynomial degree | 4 | 6 | 8 | 16 | 64 | 1,024 | 4,096 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Sufficient base | $2^{616}$ | $2^{587}$ | $2^{571}$ | $2^{544}$ | $2^{521}$ | $2^{514}$ | $2^{513}$ |
