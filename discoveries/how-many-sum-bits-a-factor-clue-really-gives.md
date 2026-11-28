# How many sum bits do the low bits of one prime actually give?

Choose uniformly among pairs of distinct 1,024-bit primes whose product has 2,048 bits. Suppose someone supplies the lowest 160 bits of either prime. Under the stated Dirichlet-GRH prime-count estimate, **about 162 low bits of the prime sum are then fixed on average.** The strongest possible outcome is 321 fixed sum bits, but this requires the primes to agree in their first 160 low bits and differ in the next bit. That event has frequency within $2^{-306}$ of $2^{-160}$ in the same population. This comparison grants the true factor clue for free. [Exact condition](../PrimeFactors/FactorClueSumGap.lean) · [Full-size frequency](../PrimeFactors/MaximalFactorCluePopulation.lean)

## A formula for an arbitrary factor remainder

Let $N=pq$ and suppose one knows $p\equiv a\pmod m$, with $m>0$ and $\gcd(a,m)=1$. This fixes an ordinary sum remainder at the following modulus, computable from $N,a,m$:

$$G=\gcd\!\left(m(a^2-N+am),\;\begin{cases}2m^2&m\text{ even},\\ m^2&m\text{ odd}.\end{cases}\right).$$

The sum satisfies $aS\equiv a^2+N\pmod G$. Since $a$ is invertible modulo $G$, this specifies one residue. The formula is **sharp**. Among moduli using only primes that divide $m$, every compatible modular factor pair has the same sum modulo $M$ if and only if $M$ divides $G$. When a larger precision fails, there are modular pairs with different sums. Other constraints such as primality, factor widths or the size of the actual integer $N$ can exclude such pairs. [Fixed-divisor proof and sharpness](../PrimeFactors/FactorClueSumPrecision.lean)

To see where the gcd comes from, write the first modular factor as $x=a+mt$ and its partner as $y$, with $xy=N$ modulo $M$. Multiplying the possible sum error by the unit $x$ gives $(x-a)(ax-N)=mt(a^2-N+amt)$. The first value at $t=1$ is $m(a^2-N+am)$, and the value at $t=2$ minus twice the first is $2am^2$. These two differences determine every value, because $t(t-1)/2$ is an integer. Removing factors outside $m$ gives the stated $G$. [General theorem](../PrimeFactors/FactorClueSumPrecision.lean)

With the factors disclosed, there is a second expression for the very same $G$. For even $m$ it is $m\gcd(p-q+m,2m)$, and for odd $m$ it is $m\gcd(p-q,m)$. In particular, a large gain measures how the two factors agree at the chosen modulus. The first formula needs only the supplied clue and the product. [Factor-gap interpretation](../PrimeFactors/FactorClueSumGap.lean)

## Where the average comes from

Give the observer a fixed odd factor remainder $a$ modulo $2^k$, with $k\ge1$. Gaining at least $j$ extra low sum bits is equivalent to $j\le k+1$ and $N\equiv a^2+a2^k\pmod{2^j}$. Among the odd product remainders modulo $2^{k+1}$, each counted once, exactly half gain at least two extra bits, one quarter gain at least three when $k\ge2$, and so on. The first extra bit is certain, and the finite sum of these fractions is exactly $2-2^{-k}$. At $k=3$ and $a=1$, the eight odd product remainders in order have extra gains **3, 1, 2, 1, 4, 1, 2, 1**. [Exact tail counts, mean and example](../PrimeFactors/DyadicFactorClueGain.lean)

For actual balanced prime products and every $1\le k\le160$, the mean extra gain differs from $2-2^{-k}$ by at most $(2-2^{-k})2^{-146}$ under the stated prime-count estimates. At 160 bits the absolute error is less than $2^{-145}$. Either prime gives exactly the same gain on each pair. [Full-size mean and either-factor theorem](../PrimeFactors/DyadicClueMeanPopulation.lean)

The equal-weight residue calculation is unconditional. To count actual 1,024-bit primes, each residue pair must be weighted by how many prime pairs have those residues and a 2,048-bit product. The population estimates use Ernvall-Hytönen and Palojärvi’s explicit arithmetic-progression bound under the generalized Riemann hypothesis for Dirichlet $L$-functions. Lean takes the published estimates as explicit hypotheses. The elementary congruences and the formula for $G$ need no analytic hypothesis. [Prime counts and assumptions](../PrimeFactors/MaximalFactorCluePopulation.lean) · [Ernvall-Hytönen and Palojärvi, Corollary 2](https://arxiv.org/pdf/2003.01925#page=2)

## Can the product identify the clues that would give the biggest gain?

For an odd product and $k\ge3$, a maximal-gain candidate suffix $a$ must satisfy $a^2\equiv N-2^k\pmod{2^{k+1}}$. If $N$ is 1 modulo 8, there are **exactly two** such suffixes modulo $2^k$, opposite to one another. Otherwise there are none. This lets us specify both candidates from the product. Whether either is the true suffix remains unknown. At $k=160$ the full-size frequency above already grants both candidates. [Product-only candidate theorem](../PrimeFactors/TwoMaximalClueSuffixes.lean) · [Frequency of a true hit](../PrimeFactors/MaximalFactorCluePopulation.lean)

At three bits, $5,609=71\times79$ gives candidates 1 and 7. The primes both end in 7 modulo 8, so the list contains the truth. The equally eligible three-bit test on $7,313=71\times103$ gives candidates 3 and 5. Both actual primes again end in 7, so the list misses. These are small examples selected to show both outcomes. [Exact menus](../PrimeFactors/TwoMaximalClueSuffixes.lean) · [Prime certificates and gain comparison](../PrimeFactors/DyadicClueControls.lean)

## What happens on the two existing 2,048-bit examples?

| Input | Supplied low 160 bits of the smaller prime | Fixed low sum bits | Sum remainder |
| --- | ---: | ---: | ---: |
| Independently generated comparison | 347304353813149557101162729845850277667140887327 | 161 | 1513878057010853217856674867035423563804221996176 |
| Constructed fourth-power example | 1 | 320 | 2 |

The clue in the first row comes from the published factor labels after generation. The second product was designed with both primes in the same class to many binary places. The table measures the precision furnished by those supplied clues. [Checked remainders](../PrimeFactors/DyadicClueControls.lean) · [How the comparison input was generated](certified-fresh-control.md) · [Construction of the fourth-power example](when-a-quartic-reading-beats-consecutive-fermat.md)

Even with the correct 160-bit clue, scanning only its fixed sum remainder upward from $\lceil2\sqrt N\rceil$ still visits at least $2^{579}$ wrong sums before the correct one on all but fewer than one in $2^{35}$ eligible full-size products. This bound uses the most favorable possible precision, 321 bits, and requires no prime-distribution hypothesis. It concerns this ascending scan. [Population bound for the scan](../PrimeFactors/FactorClueSumPrefix.lean)
