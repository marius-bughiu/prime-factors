# Fewer ranges to check by rounding the smaller equations first

On each of our two 2,048-bit products, a complete list of possible factor ranges is now **between three and four times shorter** than the previous list that used the same 24,576 coefficients per equation. The fresh example still has about $4.30\times10^{148}$ locations, and the crossed example about $7.65\times10^{148}$. This improvement comes from a proof about every range. We have not generated these enormous equations or found either product’s prime factors. [Coverage and checked comparisons](../PrimeFactors/RecursiveUnitCover.lean) · [Actual seven-row experiments](rounding-a-sifted-window.md)

## Where the extra width comes from

Suppose $N=pq$ is a 2,048-bit product of two 1,024-bit primes, ordered $p\le q$. At a proposed odd starting point $c$ write $d=c+2x$. The product implies that $x+2c$ is nonzero modulo 3 at a true divisor. The previous construction used this fact to build a monic polynomial $S_i$ whose values were all divisible by a common denominator $D_i$ throughout the eligible set. Its normalized row $S_i/D_i$ has leading coefficient $1/D_i$. Earlier work rounded its lower coefficients in the ordinary binomial basis. At higher degrees the resulting error bound could exceed the size of the target Chebyshev polynomial. [Denominator and earlier rounding rule](rounding-on-three-adic-units.md)

Now build degrees in ascending order. If the normalized rows of smaller degree fit the interval well, add integer multiples of those very rows when correcting the next one. Integer coefficients preserve integrality at every eligible factor position. To see the error, expand the difference from the target in the smaller rows and round each coefficient to its nearest integer. Each remaining coefficient has magnitude at most one half. If $W_j$ bounds the earlier normalized row, the total correction error is at most $\tfrac12\sum_{j<i}W_j$. This estimate depends on the small values of the completed rows. [Recursive construction](../PrimeFactors/RecursiveUnitWindows.lean)

For this set $D_i=\operatorname{lcm}(i!,3^{\lfloor i/2\rfloor}\lfloor i/2\rfloor!)$, and $D_{i+1}\le3(i+1)D_i$. This controls the growth of the error. On $0\le x\le4U$, when the degree cap $k$ satisfies $6k\le U$, the simple weights $W_i=\lfloor4U^i/D_i\rfloor$ suffice for the construction. The resulting polynomial vanishes at every eligible divisor offset inside the specified window. The public lower bound $\lceil N/2^{1024}\rceil$ supplies the required minimum divisor size. [Height and root proofs](../PrimeFactors/RecursiveUnitWindows.lean) · [Denominator growth and bit estimates](../PrimeFactors/RecursiveUnitScale.lean)

## Which costs are proved

| Coefficients per equation | Taylor depth | Guaranteed odd positions per chosen location |
|---:|---:|---:|
| 145 | 72 | $2^{515}+1$, using the earlier rounding rule |
| 513 | 256 | $2^{519}+1$, using recursive rounding |
| 24,576 | 12,287 | $2^{526}+1$, using recursive rounding |

The 513-row test passes the uniform budget at a width where the previous sufficient bound for the same degree and depth misses. At 24,576 rows the proof bounds the product of the denominators without constructing an integer with billions of bits. A separate calculation at half the width, $2^{525}+1$ positions, meets the stronger numerical size bound used in our LLL comparisons. Both high-rank results are mathematical guarantees. The large-input lattice reductions we actually ran for this change used seven rows. [513-row comparison](../PrimeFactors/RecursiveUnitComparison.lean) · [Full-rank inequalities](../PrimeFactors/RecursiveUnitScale.lean) · [Seven-row certificates](rounding-a-sifted-window.md)

For a public input $N$, the first possible smaller factor is at least $L=\lceil N/2^{1024}\rceil$ and the last one is at most $\lfloor\sqrt N\rfloor$. With $d=2j+1$, the number of odd positions in that range is

$$P=\max\big(0,\lfloor(\lfloor\sqrt N\rfloor+1)/2\rfloor-\lfloor L/2\rfloor\big).$$

Each full window contains $2^{526}+1$ positions and the final window covers the remainder. Lean proves that $\lceil P/(2^{526}+1)\rceil<2^{495}$ for every input in the target class. The previous guaranteed list had fewer than $2^{497}$ locations. For each of the two actual inputs, Lean checks that the previous schedule, including its endpoints, used strictly between three and four times as many locations. No factor labels enter these calculations. Each new location still requires constructing a short equation of degree at most 24,575 and checking any candidate roots. [Complete public grid](../PrimeFactors/UnitWindowCover.lean) · [Balanced-input theorem and comparison with the old grid](../PrimeFactors/RecursiveUnitCover.lean)

Selecting the location remains the biggest missing step. A separate conditional theorem shows that enough accurate readings of the missing Euler factors would recover the primes directly, with no interval search. Efficient evaluation of those readings from the product is open. [Exact recovery and its input assumptions](factor-recovery-from-boundary-readings.md)


There is also a limit to what these changes alone can accomplish. If a complete sweep sizes each window by the determinant bound and its columns are integral and bounded on the allowed residue classes, even choosing an entirely different basis leaves an enormous number of coefficients to process. Taking the possible factors coprime to 3 gives more than $2^{505}$ coefficient slots on the fresh input and more than $2^{506}$ on the crossed one. The proof allows different degrees, depths and windows in the same sweep. A direct comparison with those lower bounds shows that the new schedule uses less than 8.45 times the coefficient slots of any such sweep on the fresh input and less than 7.81 times on the crossed input. The comparison allows overlapping windows and arbitrary polynomial bases. A way to select a winning window directly would fall outside this bound. [Finite-difference obstruction](limits-of-sifted-window-covers.md)
