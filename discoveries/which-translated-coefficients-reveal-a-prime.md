# Which translated coefficients reveal a prime?

For **187**, the same polynomial calculation with three different shifts gives remainders **0, 143 and 33**. The first gives back 187 as a greatest common divisor. The next two each give **11**, leaving **17** by division. An adjacent coefficient goes the other way and gives 17 directly. For **77**, every shift gives remainder zero. These differences follow from the primes’ remainders modulo 4. The formulas take the product alone, but the coefficients they ask for become enormous. [Recorded examples](../benchmarks/translated-hasse.json) · [Checked gcd criterion](../PrimeFactors/TranslatedHasse.lean)

## What the shift changes

For an odd input $N$, set $m=(N-1)/2$ and form

$$H_N(c)=[X^{N-1}]\big((X+c)^3-(X+c)\big)^m.$$

The brackets ask for the coefficient of one power of $X$. Both its index and the integer shift $c$ are public. At an odd prime $p$, this gives the elliptic curve’s Hasse–Witt coefficient modulo $p$. Translation preserves that residue. For $y^2=x^3-x$, it vanishes when $p\equiv3\pmod4$ and is nonzero when $p\equiv1\pmod4$. At $c=1$ the cubic becomes $X(X^2+3X+2)$, and $H_N(1)$ is the central Delannoy number at index $m$. Coster and van Hamme explicitly studied this translated curve and congruences for these numbers at primes. [Harvey and Sutherland, definition of the Hasse–Witt matrix](https://arxiv.org/abs/1402.3246) · [Coster and van Hamme, Example 2](https://ir.cwi.nl/pub/1600/1600D.pdf)

For distinct odd primes $p,q$, Lean proves $H_{pq}(c)\equiv H_p(c)H_q(c)\pmod{pq}$. In characteristic $p$, write $m=(p-1)/2+p(q-1)/2$. Raising to the $p$th power changes every exponent to a multiple of $p$. The first factor has degree at most $3(p-1)/2<2p-1$, so only its coefficient at $p-1$ can contribute to the requested index $pq-1$. This gives the congruence modulo $p$ and, exchanging the primes, modulo $q$. The dependence of $H_p(c)$ on $c$ **modulo the other prime** is what makes the shift useful. [Proof of the product congruence](../PrimeFactors/TranslatedHasse.lean)

Suppose $N=rq$ with $r\equiv3\pmod4$, $q\equiv1\pmod4$ and $r<2q$. Then $r$ divides every reading. Among **all** integer shifts $0\le c<N$, at least **one third** give gcd exactly $r$. If $r<q$, at least **two thirds** do. The proof bounds how many residues can be roots of the nonzero polynomial $H_r(c)$ modulo $q$, using cancellation of binomial coefficients in characteristic $q$. These are guarantees for uniform shifts on each qualifying input. For two distinct odd primes, the mixed case can be recognized from $N\equiv3\pmod4$. When both primes are 3 modulo 4, as for 77, both divide every reading. [Full-period counting theorem](../PrimeFactors/TranslatedHasse.lean) · [Degree bound](../PrimeFactors/HasseShiftDegree.lean)

## A single coefficient gives the other prime

For $N=4a+3$, differentiating the polynomial $H_N(c)$ in the shift variable gives the exact integer identity

$$\frac{H'_N(0)}{N}=(-1)^a\binom{(N-1)/2}{(N+1)/4}.$$

The division takes place in the integers before reduction modulo $N$. If $N=rq$ is mixed as above and $q\le2r$, the gcd of this entry with $N$ is **$q$**, the prime congruent to 1 modulo 4. Equal-width prime factors satisfy both size conditions. For 187 the unsigned entry is $\binom{93}{47}$, whose residue is **51**, and $\gcd(187,51)=17$. The size condition matters. At $87=3\cdot29$ the same gcd is 87. [Derivative identity, Lucas proof and counterexample](../PrimeFactors/HasseBinomialDerivative.lean)

## How far into a power series does factor information appear?

Let $N=pq$ for distinct odd primes $p<q$. Work modulo $N$ and discard terms of degree $d$ and above, with $1\le d\le p$. For any polynomial or regular rational expression $g(T)$ normalized to have constant term 1, $g^N=1$. Its half-power $g^{(N-1)/2}$ is the unique inverse square root of $g$ with constant term 1. Comparing these two ways of obtaining that series always gives the same answer at this precision. For $g=1+T$, retaining degree $p$ changes the identity to $(1+T)^N\equiv 1+qT^p\pmod{N,T^{p+1}}$. The coefficient at degree $p$ is the other prime. [First correction and uniqueness proofs](../PrimeFactors/HasseTruncatedSeries.lean)

Individual coefficients can reveal a divisor **earlier**. For $0\le j<p$, the gcd of $N$ and $\binom{(N-1)/2}{j}$ is 1 when $2j<p$, is $p$ when $p\le 2j<q$, and is $N$ when $q\le 2j$. Under $q\le 2p$ the public index $j=\lfloor\lfloor\sqrt N\rfloor/2\rfloor+1$ always selects $p$. On 187 it gives $j=7$ and gcd 11, while $j=5$ gives gcd 1. The column still grows on the order of $\sqrt N$. The project's shorter Pascal row reduces the size of the entry whose gcd must be computed. [Exact coefficient thresholds and public column](../PrimeFactors/HasseTruncatedSeries.lean) · [Shorter row and measured costs](a-shorter-pascal-row-for-equal-width-primes.md)

## What was computed

The census includes every unordered pair of distinct odd primes with the same bit length from 4 through 7. Each search tried the fixed shifts 1, 2 and 3. The search used the product and those fixed shifts. The enumerated prime labels checked the results. [Census data](../research/translated-hasse.json) · [Replay with `python3 -m experiments.translated_hasse --verify`](../experiments/translated_hasse.py)

| Prime classes modulo 4 | Products | Split at shift 1 | Split at any of 1, 2, 3 |
|---|---:|---:|---:|
| One 1 and one 3 | 61 | 60 | 61 |
| Both 1 | 22 | 0 | 2 |
| Both 3 | 27 | 0 | 0 |
| **Total** | **110** | **60** | **63** |

At shift 1, 28 products gave remainder zero. The extra shifts recovered three additional products, leaving 47 unresolved. An independent exact Delannoy recurrence agreed at all 110 indices. Running that recurrence modulo the product encounters a noninvertible denominator at the smaller prime on all 110 inputs. Finding it by checking consecutive denominators amounts to trial division up to that prime. [Counters and recurrence](../experiments/translated_hasse.py)

The direct translated calculation shares binomial updates across shifts. On 187 it used 47 terms, 92 exact divisions and 141 modular updates for all three shifts. On each 2,048-bit comparison its required term count has **2,046 bits**. Both exceeded the maximum half-index of 8,192 before the first term was evaluated, so this coefficient evaluation found neither pair. The derivative reduces the task to one binomial coefficient, but even that coefficient has at least $2^m/(m+1)$ as its magnitude for $N=4a+3$, since it is a largest entry of Pascal row $m$. Efficient evaluation of its residue at an unfactored large input remains open here. These coefficient and counting results use finite algebra and require no Riemann hypothesis. [Benchmark budgets](../benchmarks/translated-hasse.json) · [Project scope of the verified RH results](../docs/research.md)

## Could a short recurrence jump to the useful coefficient?

For a fixed translation, consider a rule that obtains each new coefficient from a weighted sum of the previous $s$ coefficients, using the same weights at each step. A short rule of this type could be fast-forwarded by matrix powering. If the rule fits the sequence from its initial values through index $m$, then **$m<3(s+1)$**. This holds for every translation, even when the weights are chosen after seeing the product, as long as the product has a prime divisor at least five. For 187 the desired index is 93, so the rule needs at least 31 previous values. At 2,048 bits the required order exceeds $2^{2044}-1$. A formula for the single desired index, or a rule whose weights change between steps, remains an open possibility. [Lean proof for all translations](../PrimeFactors/HasseRecurrenceDegree.lean)

We can also combine the first few coefficients into a determinant whose entries are constant along each anti-diagonal. Lean proves that the determinants from the translated Hasse coefficients equal those from the simpler cubic $1+(3c^2-1)X^2+(c^3-c)X^3$ for every size. This gives exact, smaller expressions for testing proposed nonlinear recurrences. [Binomial translation and determinant identity](../PrimeFactors/HankelTranslation.lean)

### Can a failed recurrence still reveal a factor?

Yes, on **111,281**. Write $D_j$ for the determinant of size $j$, with $D_0=1$. We tested whether two weights $a,b$ could satisfy the first four equations of the form $D_jD_{j+4}=aD_{j+1}D_{j+3}+bD_{j+2}^2$. Each group of three equations gives a determinant that must vanish if the weights exist. At the public shift $c=\lfloor\sqrt{111281}\rfloor+1=334$, the first determinant shared the factor 257 with the input, and the second was coprime to it. Division gave the other prime, 433. This example was selected after the census because the first eight nearby trial divisors and the first eight Fermat checks also miss it. [Prime certificate and comparison budgets](../benchmarks/hasse-hankel-probe.json)

The shifts were fixed before the census as $2,3,\lfloor\sqrt N\rfloor,\lfloor\sqrt N\rfloor+1$, with two gcds at each shift. Among all 4,041 pairs of distinct primes of equal bit length from 4 through 10, the determinants split **298** products. Eight uniform random gcds split 141, and eight nearby odd trial divisors split **724**. The determinants found 177 products that the nearby trials missed. All eight gcds were 1 on both 2,048-bit comparisons, the independently generated fresh input and the constructed crossed input. The two searches used equal numbers of gcds. Constructing a determinant operand costs more than choosing a nearby odd number. [Full census and unresolved cofactors](../research/hasse-hankel-probe.json) · [Reproduce the census](../experiments/hasse_hankel_probe.py)

The first four recurrence equations cannot all hold for any rational shift $c\notin\{-1,0,1\}$. The same holds modulo every prime at least $2^{280}$ whenever $c^3-c$ is nonzero modulo that prime, even if the weights are chosen separately for each prime. Lean checks both determinants from the defining coefficients, and a Bézout identity shows why their nondegenerate residual factors cannot vanish together. The successful gcd on 111,281 needed just one determinant to vanish at a prime. [Four-equation obstruction](../PrimeFactors/HasseHankelBilinear.lean)

**At 2,048 bits, fewer than one in $2^{990}$ ordinary prime pairs could give a factor with these eight checks.** This is a bound on the whole population of distinct 1,024-bit prime pairs conditioned on a 2,048-bit product. It includes both possible orders of the local factor. For either fixed shift, the determinant operands are too small to contain a 1,024-bit prime. For the two square-root shifts together, any hit must give one of at most 202 square-root residues at the prime. For a fixed prime $p$, each residue can arise from at most two odd partners $q$ of the same bit length. Indeed $\lfloor\sqrt{pq}\rfloor$ lies in an interval of length at most $p$, and fixing this square root leaves fewer than four integers of separation between any two partners. Summing over the primes and using the project's formally verified prime count gives the stated fraction. The bound applies to this four-shift menu. [Determinant polynomials and the 202 residues](../PrimeFactors/HankelProbePolynomial.lean) · [Odd partner count](../PrimeFactors/SquareRootShiftPartners.lean) · [Unconditional population theorem](../PrimeFactors/HankelProbePopulation.lean)

## When both primes are 1 modulo 4

The earlier quartic method computes two complete sums of Jacobi symbols using $N$ and a selector $d$ with Jacobi symbol $-1$. Their signed values share a scale. Dividing their absolute values by their gcd gives coordinates whose squared lengths sum to one prime. For $N=65$ and $d=3$, the readings are $-12$ and $24$. Normalization yields $(1,2)$ and $1^2+2^2=5$. This run needed 64 symbol evaluations over 32 positions. The earlier squared-trace gcd also gives 5 from these readings. [Earlier quartic method and cost](quartic-trace.md) · [Checked primitive-direction decoder](../PrimeFactors/GaussianTraceRecovery.lean)

A different theorem starts with the magnitude of **one complete trace plus a supplied representation** $N=x^2+y^2$. At most eight sign and coordinate orientations, each yielding at most two candidate norms, suffice to include both primes. Testing which candidate norms strictly between 1 and $N$ divide $N$ identifies its factors. For 65 the representations $4^2+7^2$ and $1^2+8^2$ illustrate the additional input. If only the trace magnitude $t$ is available, the proof instead gives a search of up to $\lfloor(\lfloor\sqrt N\rfloor-t/4)/4\rfloor$ indices. Obtaining a complete trace or finding a sum-of-squares representation from a large product carries its own cost. [Theorems for one reading and for a supplied representation](../PrimeFactors/GaussianTraceRecovery.lean)
