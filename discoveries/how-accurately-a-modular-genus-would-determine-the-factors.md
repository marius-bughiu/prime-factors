# How accurately would a modular curve have to be counted?

**At 527, a count from the product alone gives the factor sum 48 and hence the primes 17 and 31.** The count is the genus of a modular curve, a nonnegative integer attached to its level. At level $4\times527=2{,}108$ the genus is 283. The count took 10,236 gcd tests. The 106th test had already exposed 17, and ordinary trial division reaches 17 in eight odd-divisor tests. Run `python3 -m experiments.modular_curve_counts --verify` to reproduce the counts and the Lean certificates for 15 and 527. [Reproducible enumeration](../experiments/modular_curve_counts.py) · [Checks against independent counts at levels 2–39](../tests/test_modular_curve_counts.py)

## Which number determines the factors?

Let $N=pq$ for distinct odd primes and put $D=(p+1)(q+1)$. Then $p+q=D-N-1$. Knowing that sum gives the two primes as the roots of $x^2-(p+q)x+N$. At level $4N$ the classical genus formula gives $D=2g+10$. The underlying count at 2,108 has index 3,456, twelve cusps and zero elliptic points of orders two and three. Substitution gives $g=283$, then $D=576$. The experiment builds the cosets using the level alone. Sage's standard index implementation explicitly factors its level. [Classical genus formula, §2](https://arxiv.org/pdf/math/0006096#page=2) · [Sage implementation](https://github.com/sagemath/sage/blob/develop/src/sage/modular/arithgroup/congroup_gamma0.py#L510-L527) · [Lean recovery from the divisor sum](../PrimeFactors/DivisorSum.lean)

An estimate can suffice even at this level. Given 527, its residue determines a spacing of 12 between admissible genus values. An estimate of 288 is within five of 283, so rounding to the admissible values still gives the right answer. The level-four proof also relates this count to four-square and four-triangular-number representations, with the classical counting identities as explicit hypotheses. [Level-four proof and examples](../PrimeFactors/ModularCurveGenus.lean)

## Increasing the level makes absolute error easier to tolerate

Choose $A=2^m$ and use level $L=8A^2N$. Its index is $12A^2D$, its cusp count is $16A$, and both elliptic counts vanish. The same classical formula gives

$$
g+8A-1=A^2D.
$$

Both primes are odd, so $D$ is a multiple of four. Successive multiples give possible genera spaced by $4A^2$. Given an integer estimate of $g$ with absolute error strictly below $2A^2$, one division and rounding recover $D$. The strict bound avoids ties. For $N=15$, enumerating the three levels with $A=1,2,4$ gave genera 17, 81 and 353. Their rounding radii are 2, 8 and 32. All three give $D=24$. Each fourfold increase in level also quadrupled the number of points our experiment had to visit. [Derivation of the local counts](https://arxiv.org/pdf/math/0006096#page=2) · [Lean rounding theorem](../PrimeFactors/DyadicGenusPrecision.lean) · [Enumeration](../experiments/modular_curve_counts.py)

For a 2,048-bit $N$, choose $A=2^{1025}$. The level then has 4,101 bits, and $A^2>2N$ implies $\sqrt L<2A^2$. **One integer genus estimate accurate to within $\sqrt L$ would determine both primes.** The local Lean proof takes the classical genus equation as a premise and verifies the precision bound, rounding, and recovery. Our enumeration must visit $12A^2D$ points, already more than $L$. An efficient pointwise estimator with this accuracy remains open here. [Full-size theorem](../PrimeFactors/DyadicGenusPrecision.lean)

Even a weaker guarantee, such as error at most $L^{3/4}$, would suffice at an 8,207-bit level. In general, fix an integer $t\ge1$ and suppose the estimate has error $E$ satisfying $E^{t+1}\le L^t$. Choose $A$ with $A^2\ge(8N)^t$. Then $L^t=(A^2)^t(8N)^t\le(A^2)^{t+1}$, so $E\le A^2$, inside the rounding radius. For a 2,048-bit input the verified choice $A=2^{1026t}$ adds $2052t+3$ bits. This identifies a precise computational equivalence on the stated family. Fast estimates with a fixed power saving would give the factors, and known factors give the genus with a few multiplications. [General error and level-size bounds](../PrimeFactors/DyadicGenusPrecision.lean)

## Two estimates we can rule out

**Using the next square above $N$.** A cheap estimate replaces $p+q$ in the formula with $2\lceil\sqrt N\rceil$, the first sum ordinary Fermat search tries. An incorrect even sum differs by at least two, making its genus error at least $2A^2$. At the chosen scale the estimate meets the square-root error target exactly when the first Fermat sum was already correct. For $N=8{,}509=67\times127$ and $A=256$, the estimated sum is 186 and the actual sum is 194. The genus error of 524,288 exceeds $\lfloor\sqrt L\rfloor=66{,}791$. [Lean proof for every odd prime pair](../PrimeFactors/DyadicGenusPrecision.lean)

**Using the published average genus.** Csirik, Wetherell and Zieve prove that the mean of $g(j)/j$ across levels tends to $c=5/(4\pi^2)$. On our levels, when $p,q\ge1024$, the estimate $cL$ exceeds the actual genus by more than $L/1024$. At the chosen full-size level this error exceeds $2^{2040}\sqrt L$. The source's average concerns all levels. The calculation here tests its coefficient on the particular levels where we would need it. The pinned RH statements about zeta and Dirichlet zeros supply no estimate for this individual genus in the material reviewed. [Average genus, §5](https://arxiv.org/pdf/math/0006096#page=5) · [Lean error bound](../PrimeFactors/DyadicGenusAverage.lean) · [Pinned RH statements](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab/src/Statements.lean)

Taking differences of a cumulative average runs into the same problem. Subtract $cB(B+1)/2$ from the sum of the genera through level $B$. The resulting errors at $L$ and $L-1$ differ by $g(L)-cL$. Consequently at least one of the two errors has magnitude greater than $L/2048$. This rules out a uniformly sublinear error for that particular smooth cumulative estimate. [Adjacent-level error bound](../PrimeFactors/DyadicGenusAverage.lean)
