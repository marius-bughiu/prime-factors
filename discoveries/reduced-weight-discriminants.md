# How large a square must a weighted midpoint test recognize?

For the 2,048-bit input named `midpoint-weights-capped-2048`, **every candidate square-root test can use at most 1,369 bits**. The bound covers every residue pair in the balanced search, including the unvisited pairs. Each candidate still has to be generated. The specific input, radix, and endpoints are checked in Lean. [Midpoint fixtures](../benchmarks/midpoint-weights.json) · [Checked bounds](../PrimeFactors/ReducedWeightDiscriminant.lean)

## Removing a known square

Suppose $N=xy$ and a search chooses weights $a,b$ to test the candidate trace $t=ay+bx$. If the candidate is correct, its discriminant $D=t^2-4abN$ equals $(ay-bx)^2$. There is also information on *every* candidate. For a low residue $u$ modulo the radix $R$, choose a lifted partner $y_0$ so that $uy_0\equiv N\pmod{R^2}$. A stationary weight satisfies $ay_0\equiv bu\pmod R$, and the candidate search uses $t\equiv ay_0+bu\pmod{R^2}$. Therefore

$$
D\equiv (ay_0-bu)^2\equiv 0\pmod{R^2}.
$$

Only the integer $D/R^2$ needs a square test. Negative values fail. Zero has root zero. For a positive square, multiply the smaller root by $R$ to recover the root used in the quadratic formula. Before taking an integer square root, the implementation tests the quotient against tables of square residues modulo 64, 63, 65, 11, 17 and 19. [Lean divisibility and square equivalence](../PrimeFactors/ReducedWeightDiscriminant.lean) · [Implementation](../experiments/reduced_weight_discriminant.py)

## A single bound for all remaining candidates

Write $L=\lceil\sqrt N\rceil$, $U=\lfloor\sqrt{9N/8}\rfloor$, $G=\lfloor\sqrt{N/8}\rfloor$, and $H=U-L$. If the larger factor is at most twice the smaller one, the midpoint is between $L$ and $U$ and the signed half-gap is between $-G$ and $G$. Set $A=|a+b|$ and $B=|a-b|$. Every trace in the search interval satisfies $|t|\le UA+GB$. Using $8U^2\le9N$, $8UG\le3N$, $8G^2\le N$, and $A^2-B^2=4ab$ gives

$$
8D \le N(A+3B)^2.
$$

If $3H\le2G$ and $H>0$, the search's weight criterion $HA+2GB<R^2$ gives $H(A+3B)<R^2$. Consequently $8H^2(D/R^2)<NR^2$. For the fixture `midpoint-weights-capped-2048`, the endpoint inequalities and $NR^2\le8H^2\,2^{1369}$ hold by direct integer arithmetic. Together these facts certify that every nonnegative quotient is smaller than $2^{1369}$. [General envelope and exact fixture arithmetic](../PrimeFactors/ReducedWeightDiscriminant.lean)

## Observed work

Across eight products of 49 or 50 bits, the ordinary scans performed 20,337 integer square roots. The short square-residue tables on the reduced discriminants left 326 integer square roots. The largest input to the ordinary square check was 68 bits, and the largest reduced radicand was 37 bits. The number of residue pairs in the search stays the same. [Paired holdout generator](../experiments/midpoint_weight_holdout.py) · [Per-input results and timings](../research/midpoint-weight-holdout.json)

On the **128-orbit** prefix of `midpoint-weights-capped-2048`, the 69 nonnegative discriminants shrank from a maximum of 2,731 bits to 1,368 bits. Two passed the residue tables and required an integer square root. The whole product remains unresolved. The 65,536-step continued-fraction experiment used the different 2,048-bit input named `pell-window-2048`. [Weighted midpoint input](../benchmarks/midpoint-weights.json) · [Continued-fraction input](../benchmarks/pell-local-windows.json)
