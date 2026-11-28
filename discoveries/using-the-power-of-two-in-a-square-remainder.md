# When the power of two in a remainder gives the prime sum

The product $36{,}696{,}721$ has integer square root $6{,}057$. Subtracting its square leaves $9{,}472$, whose largest power-of-two divisor is 256. Add 256 to twice the root and the answer is **12,370**, the exact sum of the primes. One integer square test then gives **4,937 and 7,433**. We constructed this example to meet the rule. Even allowing every possible shift in the square identity behind it covers **fewer than one in $2^{482}$** distinct pairs of 1,024-bit primes with a 2,048-bit product. [Product-only formula and checked example](../PrimeFactors/FloorSquareShift.lean) · [Unconditional population bound](../PrimeFactors/FloorSquareShiftPopulation.lean)

## What the calculation costs

Given a product $N$ of two distinct odd primes, compute $r=\lfloor\sqrt N\rfloor$ and $D=N-r^2$. The proposed sum is $S=2r+2^j$, where $2^j$ is the largest power of two dividing $D$. Counting the trailing zero bits of $D$ gives $j$. The Lean definition obtains the same power with one gcd of $D$ and $2^{\lfloor\log_2 D\rfloor}$. This takes one integer square root to form the prediction, plus at most one integer square root to check whether $S^2-4N$ is a nonnegative square. If the square root is $g$, the two candidates are $(S-g)/2$ and $(S+g)/2$. Multiplying them verifies the split. [Formula and exact success criterion](../PrimeFactors/FloorSquareShift.lean) · [Recovering factors from a square discriminant](../PrimeFactors/Isolation.lean)

For $36{,}696{,}721$, the discriminant is $6{,}230{,}016=2{,}496^2$. Ordinary Fermat starts at 6,058 and first succeeds at 6,185, on its 128th consecutive midpoint. A search that already expects the midpoint's distance above $r$ to be a power of two would try 1, 2, 4, 8, 16, 32, 64 and 128. Reading the remainder selects 128 directly. A parity- and modulo-256-screened Fermat scan checks eight discriminants on the same input. These are arithmetic counts for this example. [Prime and square-root checks](../PrimeFactors/FloorSquareShift.lean)

## Why a shift can reveal the sum

Write $N=pq$ with $p<q$, and let $J=p+q-2r$. This is the positive amount missing from twice the root. For an integer shift $0<h\le p$, expanding the squares gives

$$
(p-h)(q-h)=(r-h)^2 \quad\Longleftrightarrow\quad D=hJ.
$$

Thus a successful shift exists exactly when $J$ divides $D$, and that shift must be $D/J$. The identity $pJ-D=(r-p)^2$ guarantees $D/J\le p$. A search may use a proposed $h$ to form $2r+D/h$ once it has checked that $h$ divides $D$ exactly. At $h=1$ this agrees with the previously checked square-totient formula. For odd primes, $J$ is even, so an odd $D$ rules out every positive shift immediately. [Shift equivalence, uniqueness and parity](../PrimeFactors/FloorSquareShift.lean) · [Earlier predecessor-square formula](discriminant-strides.md)

The one-gcd prediction is correct exactly when the successful shift is odd and $J$ is a power of two. A family that guarantees this starts with $p=x^2+h$ and $q=(x+k)^2+h$, where $h$ is odd and $k$ is a power of two. Their product is $(h+x(x+k))^2+hk^2$. When $hk^2\le 2(h+x(x+k))$, the first term is the floor square, so $D=hk^2$ and $J=k^2$. Our constructed example used $x=70$, $k=16$ and $h=37$. The prediction itself uses only $N$. In the wider family with an arbitrary $k$ and squarefree $h$, a certified squarefree part of $D$ also gives $h$. The cost of finding that decomposition would be additional. [Family and squarefree-part theorems](../PrimeFactors/FloorSquareShift.lean)

## The same remainder can require different shifts

These products both have 16 bits, both factors have eight bits, and both leave **the same squarefree remainder, 138**. Its largest power-of-two divisor is 2. [Both prime certificates and predictions](../PrimeFactors/FloorSquareShift.lean)

| Product | Floor root | Predicted sum | Actual factors and sum | Successful shift |
| --- | ---: | ---: | --- | ---: |
| 32,899 | 181 | 364 | $167+197=364$ | 69 |
| 41,347 | 203 | 408 | $173+239=412$ | 23 |

On the second product, the predicted discriminant is 1,076, strictly between $32^2$ and $33^2$. The true excess is 6. Both products admit a shifted square, but even the complete remainder and the factor width do not specify which shift to use. [Matched controls](../PrimeFactors/FloorSquareShift.lean)

## Why trying more shifts has limited reach

For any positive integers $p<q\le H$, a successful shift below $p$ forces
$p=h+ux^2$ and $q=h+u(x+k)^2$ for positive integers $u,x,k$. This follows by removing the gcd from the two shifted factors whose product is a square. The remainder is then $huk^2$, which is at most $2r\le2H$ because the next square is $(r+1)^2$. For fixed $u,k$, there are at most $\sqrt{H/u}$ choices for $x$ and $2H/(uk^2)$ choices for $h$. Summing gives at most $12H\sqrt H$ pairs. The endpoint $h=p$ forces $q\le p+2$ and adds at most $2H$ more. This count includes composite factors. [Coordinate representation](../PrimeFactors/FloorSquareShift.lean) · [Finite counting proof](../PrimeFactors/FloorSquareShiftPopulation.lean)

Take $H=2^{1024}$ and compare with the proved population of unordered **distinct 1,024-bit prime pairs whose product has exactly 2,048 bits**. The fraction admitting any successful shift is below $2^{-482}$. The bound grants the entire list of divisors of $D$ for free and uses an unconditional lower bound on the prime population. [Full-width theorem](../PrimeFactors/FloorSquareShiftPopulation.lean) · [Prime-pair denominator](../PrimeFactors/ChebyshevPrimeSample.lean)

Granting the factors for free on every pair admitting any shift would save less than one part in $2^{434}$ of all exact square tests in the parity- and modulo-256-screened Fermat search over eligible full-size pairs. This accounts for the chance that the hits might otherwise take unusually long. [Aggregate cost proof](../PrimeFactors/FloorShiftAggregateCost.lean)

## Does testing the prediction first save work?

Across all 228,713 unordered pairs of distinct 14-bit primes with a 28-bit product, the prediction gave the correct sum **12,356 times**. On **11,833** of those products, a search that already checks parity and possible squares modulo 256 finds the factors on its very first exact square test. Only **523** hits saved any tests. Moving the guess first saved 1,009 tests on hits but added 1,881 tests on wrong guesses that lay beyond the true midpoint. Across the cohort it **cost 872 extra exact square tests**, even after avoiding duplicate tests on misses. Reordering cost extra tests at every width from 9 through 14. [Exact counts for each width](../benchmarks/floor-shift-census.json) · [Reproduce the comparison](../experiments/floor_shift_census.py)

The comparison generates a guess using the product alone and checks the same width, parity and modulo-256 conditions the baseline uses. A surviving guess gets one integer square test. On a miss, the scan resumes from the beginning and skips the guess it already tested. These totals count discriminant square tests. Both searches also need the starting integer square root, and the totals give the new rule its extra low-bit arithmetic and residue lookup for free. The more general identity admits some positive integer shift on 23,270 of these products. That last count uses the known primes to evaluate coverage. It does not give the search the shift.
