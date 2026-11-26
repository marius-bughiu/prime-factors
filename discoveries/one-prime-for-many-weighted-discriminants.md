# Can one small prime rule out many weighted traces at once?

On the project's wheel prime 211, ten consecutive candidate traces with ten distinct squares can be ruled out together for **at most two distinct weight-product residues**. Both slots can occur. At 19 consecutive traces every weight product passes the local test at least once. A single short lookup can therefore remove several directions in a favorable window, while this particular prime alone can never discard a complete 19-site window. A passing residue still needs a test against the integer input. [Checked 211 table](../PrimeFactors/DiscriminantRectangle211.lean)

For an input $N=pq$, the true weighted trace $t=ap+bq$ satisfies $t^2-4abN=(ap-bq)^2$. Fix an odd auxiliary prime $\ell$. If traces have the form $T+kj$ with $k\ne0\pmod\ell$, divide their discriminants by the nonzero square $k^2$. The normalized start is $s=T/k$, and the normalized weight product is $c=4abN/k^2$. These are public remainders. For any proposed set of indices, a direction is eliminated if every $(s+j)^2-c$ is a nonsquare in the field. Zero passes. Weight pairs with the same $c$ and the same normalized trace window share a lookup. The bound counts one such product class however many pairs it represents. [Weighted trace background](weighted-residue-tables.md)

## An exact ten-site example

For the ten values $170,171,\ldots,179\pmod{211}$, the complete list of rejected $c$ is **12 and 147**. For each of the other 209 product residues, some discriminant in the window is a square modulo 211. At the normalized start 101, opposite traces have the same square. Seven product classes then fail the whole window, the maximum over all starts. Finally, the 18-site window starting at 97 eliminates product 178. The theorem `any_stride` proves that no choice of product, origin or nonzero stride can extend a wholly rejected window to 19 sites. [Exact lists and witnesses](../PrimeFactors/DiscriminantRectangle211.lean)

For a product-only example, take $N=15049$ and stride 2. The ordered weights $(40,27)$ give $abN\equiv12\pmod{211}$ and $(30,19)$ give $abN\equiv147\pmod{211}$. The traces $8147,8149,\ldots,8165$ for the first pair and $6037,6039,\ldots,6055$ for the second all normalize to residues $170,\ldots,179$ after division by 2 in the field. The same table lookup therefore rules out both sets of ten integer traces.

The implementation stores two consecutive copies of the 211-bit nonsquare mask. At each site it shifts by $(s+j)^2\bmod 211$ and intersects with the running mask. The output bit at $-c\bmod211$ answers the query. Building the ten-site table for every possible start takes 2,110 shifts and intersections of these short integers, plus the squared-residue indices. After setup each direction still needs its public start and product class and one bit lookup. An implementation that groups many directions with the same residues must charge the work of finding those groups. Lean verifies the mask using field arithmetic, including that raising a square to power 53 produces a square root modulo 211. It then checks the finite limits in its kernel. Reproduce with `lake build PrimeFactors.DiscriminantRectangles PrimeFactors.DiscriminantRectangle211`. [Kernel-checked mask and its equivalence to the square test](../PrimeFactors/DiscriminantRectangle211.lean)

## Arbitrary shapes and primes

Let $X$ consist of the distinct squared trace residues in any proposed window and $Y$ of the distinct scaled product residues of a family of directions. If a single prime rejects **every** combination in $X\times Y$, then, writing $x=|X|$ and $y=|Y|$,

$$
\ell xy\;\le\;(\ell-x)(\ell-y).
$$

In particular, a nonempty fully rejected rectangle has fewer than $\ell$ distinct entries. At 211, even ten arbitrarily chosen distinct squared labels cannot eliminate 19 distinct product classes together. These bounds concern Cartesian families. Different trace windows chosen separately for each weight can give other patterns. [General theorem and application to weights](../PrimeFactors/DiscriminantRectangles.lean)

Write $H(c)=\sum_{v\in X}\chi(v-c)$ for the quadratic character, with $\chi(0)=0$. The shifted characters have inner product $\ell-1$ when their shifts coincide and $-1$ otherwise. Thus $\sum_c H(c)=0$ and $\sum_c H(c)^2=x(\ell-x)$. Applying Cauchy–Schwarz to $H$ and $\ell\mathbf1_Y-y$ gives $\ell(\sum_{c\in Y}H(c))^2\le xy(\ell-x)(\ell-y)$. A wholly rejected rectangle has sum $-xy$. This uses classical quadratic-character orthogonality. Earlier project results study how many products can admit two labels, or how to choose a different forbidden translation for each multiplier. The table here asks which multipliers can be discarded at the *same* window. [Paley's original paper](https://doi.org/10.1002/sapm1933121311) · [Earlier pair counts](../PrimeFactors/ShiftedResidues.lean) · [Translated runs](translated-image-runs.md)
