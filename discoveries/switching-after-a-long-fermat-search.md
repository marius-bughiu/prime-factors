# When can switching multipliers find more prime pairs?

Consider two searches run on every eligible 2,048-bit product. They agree on the first stage. On products in a specified range, one then continues ordinary Fermat search and the other switches to multiplier six. Using an explicit prime-count bound under the Riemann hypothesis, the switch finds **at least 80% more additional prime pairs in that range**. The comparison grants ordinary Fermat an extra test for its competitor's new starting square root. The first stage alone takes $2^{52}$ tests. This is a gain in the number of inputs split by a long search, and the absolute chance of success remains very small. [Finite comparison](../PrimeFactors/InteriorBatchPopulation.lean) · [Upper bound on the chance of a split](sharing-square-tests-across-factor-ranges.md#how-often-can-this-approach-find-the-actual-prime)

The distinction from the small experiments matters. The experiment that found 1,733 pairs versus 1,727 used only 34 or fewer square roots per product. Its paired outcomes gave no clear winner. The calculation here uses a different public rule and a substantially longer prefix, and counts actual prime pairs. Each pair is counted once. [Independent 6,144-product comparison](../research/cheap-multiplier-confirmation.json)

## What the two searches do

Put $U=2^{1024}$ and $B=2^{40}$. Each product $N=pq$ has distinct primes $U/2\le p<q<U$. We compare searches in the bin $9U^2/16\le N\le5U^2/8$, identified from the product alone. Both begin with $4096B$ ordinary traces from $\lceil2\sqrt N\rceil$, skipping impossible sums modulo 24. The next batch depends on the method.

- **Continue.** Check the next $B+1$ ordinary admissible traces.
- **Switch.** Starting at $\lceil2\sqrt{6N}\rceil$, check the first $B$ consecutive integer traces for multiplier six. At a square $S^2-24N=d^2$, take the gcd of $(S+d)/2$ with $N$.

Outside this public bin the searches can use the same schedule. The proof compares additional splits after their common prefix. Neither search receives any information about $p$ or $q$.

## Where the additional splits come from

Let $V=2^{532}=\sqrt{UB}$. Take any prime $79U/128\le p\le82U/128$ and any prime $q$ within $V$ of $3p/2$. Their product lies in the stated bin and both factors have the required width. For $S=3p+2q$, the discriminant is $(3p-2q)^2\le4V^2$. The weighted trace is strictly less than $2\sqrt{6N}+B$, so the switch reaches it. Meanwhile the ordinary sum has excess $(\sqrt q-\sqrt p)^2>24(4097B)+24$. It lies past even the end of the ordinary continuation. For an ordinary square to yield a proper gcd of this semiprime, its trace must be $p+q$. [Arithmetic of the interior region](../PrimeFactors/InteriorBatchPopulation.lean) · [Square-to-factor allocation](../PrimeFactors/ShiftedEndpointPopulation.lean)

For ordinary Fermat, an admissible trace modulo 24 has the form $(1+N)v$ for a unit $v$ modulo 24. The resulting period has 4, 2 or 1 residues, with respective mean spacing $s=6,12,24$. At a block boundary divisible by all three period sizes, the admitted trace advances by exactly $s$ times the block size. The first admissible trace lies less than 24 above the real minimum. Thus every extra ordinary hit satisfies

$$
s(4096B)\le(\sqrt q-\sqrt p)^2\le s(4097B)+24.
$$

For each fixed $p$ and each of the three spacings, the possible extra $q$ values span at most $V/12$ integers of difference between their endpoints. To see this, bound the difference of the square roots of the upper and lower excesses by $2^{20}/24$, then multiply by $\sqrt{q_{\max}}+\sqrt{q_{\min}}\le2\sqrt U$. All of these ordinary hits have $47U/64\le p\le51U/64$. Taking the union of the three shells counts every potentially successful ordinary product in the bin. [Shell and endpoint proofs](../PrimeFactors/InteriorBatchPopulation.lean)

## How the RH result enters

Write $P(l,u)$ for the number of primes between the integer endpoints $l,u$, inclusive. Schoenfeld's Corollary 1 bounds $|\pi(x)-\operatorname{li}(x)|$ under RH by $\sqrt x\log x/(8\pi)$ for $x\ge2657$. For $U/2\le l\le u\le U$, the sum of the two endpoint errors is less than $57\sqrt U$ and $709<\log(l-1)\le\log u<710$. Subtract at $u,l$ for a lower bound and at $u,l-1$ for an upper bound. The resulting inequalities are

$$
u-l\le710\big(P(l,u)+57\sqrt U\big),\qquad
709P(l,u)\le u-l+1+709\cdot57\sqrt U.
$$

This is the written deduction from the pinned zeta statement and the published bound. The Lean theorem takes these two interval inequalities as its explicit analytic premise. All prime-pair counts below are finite. [Schoenfeld, equation (6.18)](https://www.ams.org/mcom/1976-30-134/S0025-5718-1976-0457374-X/S0025-5718-1976-0457374-X.pdf) · [Zeta statement in the pinned release](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab/src/Statements.lean)

| Count | Bound from the two inequalities |
| --- | ---: |
| First primes $p$ used for the switch's guaranteed splits | More than $U/31{,}000$ |
| Guaranteed partner primes per such $p$ | More than $V/365$ |
| Possible first primes for any ordinary continuation split in the bin | At most $U/11{,}000$ |
| Possible partner primes per such $p$, including all three shells | At most $V/1{,}900$ |

The ratio of the lower count for the switch to the upper count for continuing exceeds $11{,}000\times1{,}900/(31{,}000\times365)>1.8$. The partners used in the lower count all yield genuine square/gcd splits and all miss the common prefix. This comparison uses a broad product bin. It gives no prediction that a particular product in that bin will split.


Lean also proves the comparison for the sets of **distinct input integers** on which each scheduled continuation finds a square with a proper gcd after the shared prefix missed. Its premise is the interval estimate above. [Scheduled product-count theorem](../PrimeFactors/SwitchedBatchComparison.lean)

## A constructed 2,048-bit example

We selected two 1,024-bit primes near the interior ratio to test the calculation end to end. Given only their product, the multiplier-six search found the two primes on its 15,264th odd trace. Discovery took about 0.052 seconds in one local run. Lean checked both primes, their product, the square and the gcd in 2.90 seconds. It also checked that the true ordinary trace exceeds its minimum by more than $2^{1015}$. The identical search used its full budget of 25,001 traces on each of the two existing comparison products and found neither prime. [Decimal inputs and expected factors](../benchmarks/interior-prime-family.json) · [Product-only search and separate example generator](../experiments/interior_prime_family.py)

The construction starts near $159U/256$ and uses numbers congruent to one modulo $2^{512}$ so their primality can be certified. For each accepted smaller prime we searched the fixed grid from 65 to 255 steps above the grid point below $3p/2$. We examined 220 candidates for the first prime and 175 for the second, stopping when both had primality witnesses. This produced one example in advance of running the factor search. The generator supplies no grid index, candidate factor or prime certificate to the search.

## Absolute scale

The guaranteed interior set alone contains more than $UV/(31{,}000\times365)>2^{1532}$ distinct products under the interval-count premise. It is still sparse among eligible prime pairs. Here is a separate upper estimate covering either search, including the shared first stage. Every tested trace is less than $2^{58}$ above its minimum and a proper split gives an allocation $ab=k$. Therefore $|\sqrt{ap}-\sqrt{bq}|<2^{29}$. For fixed $p,a,b$, the possible square roots of $q$ span less than $2^{30}/\sqrt b$, so there are at most $1+2^{543}$ integer partners below $U$. The multipliers 1 and 6 have five ordered allocations altogether. Combining fewer than $2^{546}$ partners per first prime with the project's unconditional prime-population ratio gives fewer than one successful pair in $2^{461}$ over the full eligible population. This last bound is a written deduction. [Prime-population ratio](../PrimeFactors/SquareRootPhasePopulation.lean) · [Allocation from a proper gcd](../PrimeFactors/ShiftedEndpointPopulation.lean)
