# What survives when nearby interval products are subtracted?

Take an odd product $N$ and $h+1$ consecutive windows of width $W$, where $h\le W$. Moving the first window by at most $h$ slots leaves $W-h$ slots in every window. One already computed product can save work on its neighbors. The open cost is obtaining the first measurement that distinguishes a factor. [Interval product and second-digit readout](../PrimeFactors/DivisorProductDerivative.lean) · [Lean proofs for neighboring windows](../PrimeFactors/IntervalReciprocalStencil.lean)

For the $j$-th window, write its product as $P_j(X)=\prod_{k=j}^{j+W-1}(X+k)$. Every $P_j$ factors into the same product on $h\le k<W$, a left edge on $j\le k<h$, and a right edge on $W\le k<j+W$. Thus an exact value of the common product and the $2h$ edge factors give all $h+1$ products with $O(h)$ additional multiplications using prefix and suffix products. This identity holds over the integers, modulo every power of $N$, and for formal polynomial values. It works when some entries are nonunits. In particular, exchanging two values inside the common interval preserves all the product polynomials, and therefore all digits obtained by evaluating those polynomials. This ambiguity concerns the location of entries when only the window measurements are consulted. A common product can still reveal the *values* of the factors, as the two-digit theorem demonstrates. [Common product identity](../PrimeFactors/IntervalReciprocalStencil.lean) · [Two-digit theorem](../PrimeFactors/DivisorProductDerivative.lean)

## A short difference and its exact cost

To measure the change under translation, consider the logarithmic derivative $P'_j/P_j$ as a rational function. More generally, take coefficients $c_0,\dots,c_h$ in a field and any positive integer $m$. In the sum
$$
\sum_{j=0}^h c_j\sum_{k=j}^{j+W-1}\frac{1}{(X+k)^m},
$$
the coefficient of the term at slot $k$ is $b_k=\sum_{j:\,j\le k<j+W}c_j$. Throughout the common interval this equals the single number $C=\sum_jc_j$.

* If $C=0$, at most $2h$ boundary slots survive. Consecutive partial sums of the $c_j$ give their coefficients in $O(h)$ additions. Interchanging any two common-interior observations preserves every such reading, even if different coefficients are chosen at each step.
* If $C\ne0$ and the offsets at the surviving poles are distinct in the field, **every rational formula for this function has denominator degree at least $m(W-h)$**. In fact, its reduced denominator is exactly $\prod_{b_k\ne0}(X+k)^m$, up to a scalar. After clearing this product and evaluating the numerator at $-k$, the only surviving summand is $b_k$ times a nonzero product. Consequently no copy of the factor $X+k$ cancels.

For the full band of $W=2^{1022}$ odd candidates at 1,024-bit factor width, the same argument applies with spacing two, since the offsets are distinct modulo either hidden odd prime when $W+h$ is smaller than that prime. With $h=64$, the cut to the two edges touches at most 128 slots. Keeping a nonzero interior coefficient requires denominator degree at least $m(2^{1022}-64)$. Degree measures the size of an expanded rational representation. Fast product algorithms can evaluate high-degree expressions through a short representation. The theorem supplies no operation lower bound for evaluation or for factoring. Rational summation by discrete residues and fast factorial evaluation have established general theories. [Chen and Singer on rational summation](https://arxiv.org/abs/1203.4200) · [Bostan, Gaudry and Schost on fast factorial evaluation](https://doi.org/10.1137/S0097539704443793)

## A factor inside can give a unit

With spacing one, the first change is $1/(X+W)-1/X=-W/[X(X+W)]$. This reduced expression can be evaluated modulo $N$ whenever the two endpoints are units, including when an interior factor would make the two original logarithmic derivatives individually undefined. If $W$ is also a unit, its gcd with $N$ is always one.

For $N=143=11\times13$ and $W=5$, the common interiors of adjacent windows starting at 15, 7 and 9 contain respectively no factor, only 11, and both 11 and 13. The endpoint denominators are all units. The direct gcd of the first-difference value is one on each example. Other differences may yield a proper gcd from an expression in their endpoints. This example rules out using the gcd of this particular difference to decide whether the common interior contains a factor. [Checked examples and unit criterion](../PrimeFactors/IntervalReciprocalStencil.lean)
