# When two negative remainders give a factor

Take $N=43{,}423$. Subtract $193^2$ from $N$ and $264^2$ from $2N$. The two answers, 6,174 and 17,150, multiply to $10{,}290^2$. The difference $193\cdot264-10{,}290$ has gcd 251 with $N$, giving **43,423 = 173 × 251**. Lean proves that on any odd product congruent to 7 modulo 8, every such match between unit labels gives a proper factor. A unit label is an integer coprime to the product. A label sharing a proper divisor with $N$ already reveals a factor by itself. [Checked theorem](../PrimeFactors/MixedNegativeNorms.lean) · [Example and full-size controls](../benchmarks/mixed-negative-norms.json)

The example came from trying the last 32 integers below each square-root endpoint. Exactly one of the 1,024 pairs worked. We found this example by screening small products. Plain Fermat search reaches its factors in four midpoint tests. On each of the two original 2,048-bit controls the same 64 label gcds and 1,024 pair tests found no match. The theorem says what happens *when a match is found*. The work needed to locate one depends on the input and on where we look. [Reproducible census, example selection and work counts](../research/mixed-negative-norms.json)

## Why a match splits

More generally, suppose the public weights are $k,l$ and the two positive magnitudes below their endpoints are $D=kN-t^2$ and $E=lN-s^2$. Check whether $DE$ is a square. If it is, take $d=\gcd(D,E)$, $a=\sqrt{D/d}$ and $b=\sqrt{E/d}$. Since $D/d$ and $E/d$ are coprime with square product, these last two roots are integers. The supplied data give
$$t^2+da^2=kN,\qquad s^2+db^2=lN.$$
Checking these equations needs only integer arithmetic. Unit $t$ implies $d$ is coprime to $N$.

Ordinarily one takes $\gcd(N,ts-dab)$. If the two modular roots agree up to a global sign, change the sign of $b$ if necessary so that $ts-dab=jN$. Multiplying the two displayed equations gives
$$(ts-dab)^2+d(tb+sa)^2=klN^2.$$
Since $N$ is coprime to $d$, the other coordinate is also divisible by $N$. Write $tb+sa=vN$. Division gives the small, integral obstruction
$$kl=j^2+dv^2.$$
If this equation has no solution, the original gcd is proper. Lean also proves the converse with coordinate checks: for the chosen sign, global agreement is equivalent to a representation with $ks=jt+dva$ and $kb=vt-ja$. The argument accepts $d$ with square factors. It applies to any positive modulus satisfying the stated coprimality condition. [Quotient, transport equivalence and proper gcd](../PrimeFactors/MixedNegativeNorms.lean)

For $k=1,l=2$, if $d>2$ the equation is impossible. If $d=1$ or 2, it would require $N=t^2+a^2$ or $N=t^2+2a^2$. Reducing these two forms modulo 8 excludes $N\equiv7$. Both tests are public. On 8,633 the two magnitudes 5,929 and 11,025 are themselves squares. Their gcd 49 already certifies a split, and the difference of roots gives 97. In the other direction the pair $t=18,s=25$ on 2,173 gives $d=1$, a trivial gcd, and $2=(-1)^2+1^2$. [Checked and falsifying examples](../research/mixed-negative-norms.json)

## Which matches actually occur?

Every balanced pair $p<q\le2p$ of odd primes supplies an equal-magnitude match. Set $t=(q-p)/2$ and $s=(p+q)/2$. Then $s^2-t^2=N$ and $N-t^2=2N-s^2\ge7N/8$. Conversely, equality means $(s-t)(s+t)=N$. Looking for this match recovers Fermat's factorization problem. We counted unequal magnitudes separately. [Balanced height and exact gcd](../PrimeFactors/MixedNegativeNorms.lean)

We enumerated every positive unit label in both full intervals for all distinct 6-, 7- and 8-bit primes with a product of the full double bit length. For this *small* census we built squarefree kernels of the possible magnitudes and joined equal kernels. There were 9,335,493 possible mixed pairs and 3,285,459 possible within-weight-one pairs. The bounded full-size search directly tested products for squareness. Those two search costs differ. [Census and bounded search](../experiments/mixed_negative_norms.py)

| Bits in each prime | Eligible products | Unequal matches | Unequal matches giving a factor | Products with such a split |
|---:|---:|---:|---:|---:|
| 6 | 14 | 87 | 51 | 11 |
| 7 | 42 | 266 | 160 | 34 |
| 8 | 148 | 832 | 554 | 134 |

Across these 204 products, 179 had a splitting unequal match. A search for matches between two distinct labels at weight one alone split 195. Five products split only with unequal mixed matches, and 21 split only at weight one. Of the 53 products congruent to 7 modulo 8, 35 had an unequal match and all 54 such matches split. The products 2,183, 8,927 and 32,899 had no unequal match even after searching the entire intervals. [Counts by residue and all comparisons](../research/mixed-negative-norms.json)

## A guaranteed unequal match at every bit length

For a product $N\equiv5\pmod{12}$ of distinct balanced odd primes, $t=(p+q)/6$ and $s=(q-p)/4$ are integers. They satisfy $9t^2-4s^2=N$. The magnitudes $N-t^2$ and $2N-s^2$ are $4g$ and $9g$ for the same positive integer $g$, and their two gcds give $q$ and $p$. These labels use the hidden primes in the existence proof. The public search visits odd $t$ with $9t^2\ge N$ and $8t^2\le N$, testing whether $9t^2-N$ is an even square. It recovers $3t-2s$ and $3t+2s$. This is Fermat search with its midpoint restricted to $3\pmod6$. At 2,048 bits the complete schedule before further sieving still has at least $2^{1016}$ tests. For primitive scale pairs whose doubled scales divide 24, the checked classification finds only this unequal construction under the stated factor-allocation rule. [Constructive theorem, classification and cost](../PrimeFactors/MixedNegativeTemplates.lean)

Both previously tested large products fall outside this residue class. We generated a third pair by using separate hash streams for the two recursive Pocklington prime certificates and retaining the first pair with full product width and $N\equiv5\pmod{12}$. The seventh attempted pair qualified. We did not select the distance between the primes. The public 64-test search left its whole 2,048-bit input unresolved. Using the independently certified primes afterwards, the guaranteed witness was at a 305-decimal-digit position, beyond $2^{1010}$. On 33,017 the same schedule found 137 and 241 on the second test. [Product-only benchmarks](../benchmarks/mixed-negative-template.json) · [Control generation and exact position](../research/mixed-negative-control.json) · [Independent Lean reference certificate](../benchmarks/controls/MixedNegativeControl.lean)

Run `python3 -m experiments.mixed_negative_norms --verify-examples` for the census and witnesses, `python3 -m experiments.mixed_negative_templates` for the finite template classification, and `python3 -m experiments.mixed_negative_control --check` to regenerate the eligible full-size input and verify its reference certificate.

## How often two explicit constructions guarantee an unequal match

A second construction uses $p\equiv q\pmod7$ and $p\equiv-q\pmod5$. Put $t=(q-p)/14$ and $s=(p+q)/10$. Now $5s-7t=p$, $5s+7t=q$, and the two magnitudes are $25g$ and $49g$ for the same positive $g$. At $N=3{,}551$ the labels are 1 and 12, giving 53 and 67. The identities explain why it works. Locating the pair from $N$ is again a Fermat search with congruences. For example, when $N\equiv7\pmod8$ the midpoint must be a multiple of 20 and its square must equal $N$ modulo 49. On the applicable unit residues these constraints give two midpoint classes modulo 980. [Arithmetic, factor recovery and residue tests](../PrimeFactors/MixedNegativeCongruences.lean)

For uniformly drawn distinct 1,024-bit primes conditioned on the product having 2,048 bits, **more than 28%** of pairs satisfy at least one of these two constructions. This lower bound counts genuinely unequal remainders in the entire two intervals. It says nothing about their proximity to the first labels tried. Other constructions also give unequal matches, as the small census shows.

To count, work modulo 420, which has 96 unit residues. Given the two prime residues, set $v=q/p\bmod420$. The first construction applies when $v\equiv5\pmod{12}$, since $p^2\equiv1\pmod{12}$. The second applies when $v\equiv29\pmod{35}$. Among the 96 unit ratios, 24 meet the first condition, four the second and one both. Each ratio has 96 choices of the first residue. The union occupies $27/96=9/32$ of the unit residue pairs. Both conditions persist when the primes are interchanged.

At the target size the following estimate transfers this count to actual primes. Let $X=2^{1023}$ and let $\mu$ be the integral of $dx\,dy/(96^2\log x\log y)$ over $X\le x,y\le2X$, $xy\ge2X^2$. For either modulus 420 or 280 there are 96 unit classes. Theorem 1.3 of Bennett, Martin, O’Bryant and Rechnitzer gives error at most $2X/(840\cdot700^2)$ in the prime counting function at each endpoint for a particular unit class. Here $700<\log X<\log(2X)<710$, and the paper's threshold is below $X$. Each interval therefore has discrepancy at most $\epsilon=4X/(840\cdot700^2)$ and smooth mass at most $V=X/(96\cdot700)$. Applying the interval bound first to the eligible partners of each prime costs at most $\epsilon(V+\epsilon)$. Applying it again to the first coordinate costs at most $\epsilon V$ because the partner interval grows monotonically and each level set is an interval. Removing the equal-prime pairs costs at most $X$. Thus each ordered residue-pair count differs from $\mu$ by at most $\epsilon(2V+\epsilon)+X$. [Explicit prime counts, Theorem 1.3 and constants (1.10)–(1.11)](https://personal.math.ubc.ca/~bennett/BeMaObRe-IJM-2018.pdf)

The triangle $x+y\ge3X$ in the same square lies in the eligible region because $x(3X-x)-2X^2=(x-X)(2X-x)\ge0$. Hence $\mu\ge X^2/(2\cdot710^2\cdot96^2)$. The displayed error is less than $\mu/370$. Weighting the 27 favorable and 69 other ratios between $369\mu/370$ and $371\mu/370$ puts the proportion of this union between
$$\frac{9\cdot369}{9\cdot369+23\cdot371}\quad\text{and}\quad\frac{9\cdot371}{9\cdot371+23\cdot369}.$$
In particular, its share is between 28.0% and 28.3% unconditionally. As each pair has a unique prime product, passing from ordered pairs to products preserves the proportion.

Using the verified Dirichlet hypothesis and the published explicit error for primes in progressions sharpens the absolute difference from $9/32$ to less than $2^{-464}$. For these smaller moduli the same endpoint bound $2^{520}$ used in the earlier count applies. Two integrations over the eligible region and exclusion of the diagonal give a per-cell error below $2^{1546}$, and the total integral $96^2\mu$ exceeds $2^{2024}$. Lean checks the finite residue and error arithmetic. Applying the published prime-count theorems to the region is the written analytic step. [Finite counting and numerical inequalities](../PrimeFactors/MixedNegativeCongruences.lean) · [Region and explicit GRH error](polynomial-parities.md#a-finite-error-bound-from-dirichlet-grh) · [Ernvall-Hytönen and Palojärvi](https://arxiv.org/abs/2003.01925) · [Dirichlet verification](https://math.mit.edu/~drew/grh/)
