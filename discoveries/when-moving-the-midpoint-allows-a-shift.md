# When moving the midpoint allows a shift

For $8{,}509=67\cdot127$, the first integer at or above the square root is 93. No positive integer $a$ makes $(67+a)(127+a)=(93+a)^2$. Move the center just two places to 95 and $a=129$ works, since $196\cdot256=224^2$. The true Fermat midpoint is 97. A second product, $9{,}271=73\cdot127$, already works at its first center 97 with $a=23$, since $96\cdot150=120^2$. [Lean checks for both products](../PrimeFactors/CeilingShiftPopulation.lean)

For distinct 1,024-bit primes whose product has 2,048 bits, the following unconditional bounds apply to the entire population of unordered pairs. Every row allows all positive integer values of $a$ for free. [First and unrestricted centers](../PrimeFactors/CeilingShiftPopulation.lean) · [First trillion centers](../PrimeFactors/CeilingShiftWindow.lean)

| Centers available | Fraction of products admitting a shift |
| --- | --- |
| First Fermat center | Less than $2^{-479}$ |
| Any of the first $2^{40}$ consecutive centers | Less than $2^{-442}$ |
| Any center from the first up to, but excluding, the true midpoint | Greater than $1-2^{-498}$ |

## Why the last odd center works

Let $N=pq$ and $M=(p+q)/2$. At an integer center $m$ with $\lceil\sqrt N\rceil\le m<M$, expansion gives

$$
(p+a)(q+a)=(m+a)^2
\quad\Longleftrightarrow\quad
m^2-N=2a(M-m).
$$

There is exactly one possible value of $a$ at each such center. It is positive because $N$ is the product of distinct primes and so cannot be a square. For $8{,}509$ at $m=93$, the identity would require $140=8a$.

Take the last odd center before $M$, provided it lies in the search interval. If $M$ is even, that center is $M-1$, and the even number $m^2-N$ is divisible by 2. If $M$ is odd, the center is $M-2$. The primes then agree modulo 4, so $N\equiv1\pmod4$ and $m^2-N$ is divisible by 4. These are exactly the divisors the identity requires. The construction applies whenever the true midpoint is at least two places beyond the first. An existing bound on the first two Fermat tests limits the exceptions to fewer than one pair in $2^{498}$. Choosing this center uses the unknown prime sum. [Odd-center proof and population estimate](../PrimeFactors/CeilingShiftPopulation.lean) · [Bounds on early Fermat midpoints](../PrimeFactors/CyclotomicDiagonalPopulation.lean)

## Why early centers cover so few products

At the first center $m$, the difference $m^2-N$ is less than $2m$. Consequently a successful shift has $a\le m$. Adding $2a$ to both factors turns the ceiling witness into an instance of the earlier floor-square identity, with new floor root $m+2a$ and shift $a$. That floor shift is unique, so two different original pairs cannot map to the same new pair. The earlier finite count bounds the number of first-center successes even though the translated factors can be composite. [Reflection proof](../PrimeFactors/CeilingShiftPopulation.lean) · [Floor-shift count](../PrimeFactors/FloorSquareShiftPopulation.lean)

For the first $T$ centers, put $H=2^{1024}$, an upper bound for both primes. Now $m^2-N<2HT$. If $a>H$, the identity forces $M-m<T$, so the product would already factor in the first $2T$ ordinary Fermat tests. If $a\le H$, the square product forces $p+a=u x^2$ and $q+a=u(x+k)^2$. These coordinates satisfy $a u k^2=m^2-N$ and $u x^2\le2H$. Also $u k^2=2(M-m)$, so at least one of $u,k$ is even. Counting the integer coordinates in those two cases bounds the entire union of centers at once. Setting $T=2^{40}$ and including the large shifts gives the middle row of the table. [Finite coordinate count and prime-population comparison](../PrimeFactors/CeilingShiftWindow.lean)

Given only $N$ and $m$, we know $m^2-N$. To obtain the sum from the identity we would also need the correct divisor $a$, since $p+q=2m+(m^2-N)/a$. The counts establish how often such a divisor exists in each window. They supply neither its value nor the location of a successful center. [Earlier product-only divisor guess and its measured cost](using-the-power-of-two-in-a-square-remainder.md)

## Which candidate sums can the power-of-two reading produce?

For an odd nonsquare product $N$, let $r=\lceil\sqrt N\rceil$. At a center $m\ge r$, form the sum guess $2m+$ the largest power of two dividing $m^2-N$. Given a proposed midpoint $C$, we can decide whether **any** center below it produces the guess $2C$. The table gives the nearest such center. The condition $C\ge r+b$ is required in every row. [Exact equivalence, boundaries and class counts](../PrimeFactors/CeilingShiftCandidateClasses.lean)

| Public product | Condition on $C$ | Nearest center $m=C-b$ | Allowed midpoint residues per 16 |
| --- | --- | --- | ---: |
| $N\equiv3\pmod4$ | $C$ even | $C-1$ | 8 |
| $N\equiv5\pmod8$ | $C$ odd | $C-2$ | 8 |
| $N\equiv1\pmod8$ | $C^2\equiv N\pmod{16}$ | $C-4$ | 4 |

This replaces a scan of possible centers by a low-bit test on $N$ and $C$. An ordinary Fermat screen tests whether $C^2-N$ can be a square modulo 16. For every odd product, precisely four of the sixteen midpoint residues survive that screen. All four already satisfy the table. Once $C\ge r+b$, adding the power-of-two rule therefore saves **zero exact square tests** over this screen. Within the first four midpoint positions the cutoff can remove candidates whose required center would lie below $r$. [Equality of filtered candidate lists](../PrimeFactors/CeilingShiftCandidateClasses.lean)

At $N=8{,}509$, center 93 predicts $C=95$ and center 95 predicts $C=97$. Both candidates pass the modulo-16 screen. The first gives $95^2-N=516$, between $22^2$ and $23^2$. The second gives $97^2-N=30^2$ and the original factors. A candidate center is cheap to identify. Checking the exact square still distinguishes these two outcomes. [Checked readings](../PrimeFactors/CeilingShiftCandidateClasses.lean)
