# How hard is it to locate a working center?

For **9,271**, only two positions before the true Fermat midpoint admit a positive integer shift. They are **97 and 99**. Knowing that 99 is the last one gives the factors. The product is 3 modulo 4, so the true midpoint is one higher, 100. Its square exceeds the product by $729=27^2$, giving $100-27=73$ and $100+27=127$. The earlier successful position, 97, does not carry the same information. For **8,509** the entire list is just **95**. [Lean checks for both complete lists](../PrimeFactors/CeilingShiftSmallLists.lean) · [What the last position determines](../PrimeFactors/CeilingShiftLastCenter.lean)

## Which positions can work?

Write $N=pq$, $M=(p+q)/2$, and $d=(q-p)/2$. We count integer positions $m$ from $\lceil\sqrt N\rceil$ up to but excluding $M$. A position works if some positive integer $a$ satisfies $(p+a)(q+a)=(m+a)^2$. Let $b=M-m$, the distance from this position to the true midpoint. The exact condition is

$$
b\mid d^2 \qquad\text{and}\qquad b+d^2/b\text{ is even}.
$$

Indeed, the equation gives $d^2=b(2m+b+2a)$. Conversely, a divisor pair with the required parity gives $a=(b+d^2/b)/2-M$. The condition $m^2>N$ makes $a$ positive. For 9,271 the squared half-gap is 729. Among the three distances 1, 2 and 3, just 1 and 3 divide 729 and meet the parity test. This calculation uses the known half-gap to explain the result. Obtaining the half-gap from the product would itself give the factors. [Equivalence and computable check with a supplied gap](../PrimeFactors/CeilingShiftDistances.lean)

## Almost every product has a hit, but how often does a position hit?

| Draw | Verified result |
| --- | --- |
| One uniformly chosen eligible product | The chance that at least one earlier position works is greater than $1-2^{-498}$. |
| One uniformly chosen eligible product | The **mean number of working positions** is less than 10,377,335,088. |
| One uniformly chosen pair consisting of an eligible product and one of its earlier positions | The chance that the position works is **less than $2^{-951}$**, even if its shift is supplied for free. |

Eligibility requires two distinct 1,024-bit primes and a 2,048-bit product. The last row gives an input with twice as many earlier positions twice the weight. The first two rows give every product equal weight. None of the three bounds uses a prime-distribution hypothesis. [Existence bound](../PrimeFactors/CeilingShiftPopulation.lean) · [Mean count and position-weighted bound](../PrimeFactors/CeilingShiftCenterDensity.lean)

Different working positions have different distances $b$, each a divisor of $d^2$. Every eligible pair therefore has fewer than $2^{239}$ such positions. To get the sharper mean, write a divisor as $ta^2$ with $d=tab$ and count all positive triples as the half-gap varies. Two harmonic sums bound the count. Meanwhile, more than two thirds of eligible pairs have gaps of at least $2^{1006}$, leaving at least $2^{985}$ earlier positions per such pair. These counts explain how almost universal existence coexists with such low density. [Individual and interval bounds](../PrimeFactors/CeilingShiftDistances.lean) · [Counting proof](../PrimeFactors/CeilingShiftCenterDensity.lean)

## What a suffix query would tell us

Suppose someone can answer whether **any** position at or beyond a given cutoff $k$ works before the hidden midpoint. Take the first odd integer $t$ at or above both $k$ and $\lceil\sqrt N\rceil$. Lean proves that the answer is yes **exactly when $t<M$**. Every working center is odd, and the last odd position before $M$ always works when it is in the interval. For 9,271 the answer at cutoff 98 is yes even though 98 itself fails. [Suffix equivalence](../PrimeFactors/CeilingShiftLastCenter.lean)

If a final successful center is supplied, add one when $N\equiv3\pmod4$ and two when $N\equiv1\pmod4$. This recovers the true midpoint in either case. An efficient way to obtain that last position, or to answer the suffix query from the product alone, remains open. [Recovery formula](../PrimeFactors/CeilingShiftLastCenter.lean)
