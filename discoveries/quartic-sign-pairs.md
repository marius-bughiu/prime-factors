# One quartic for both signs

A single quartic can test two unordered pairs of factor remainders. On eight complete 31–32-bit searches this cut the number of lattice reductions from 2,068 to 1,036 and the total discovery time from 0.800 to 0.426 seconds. Four of the eight factorizations came from a negative root. On the crossed 2,048-bit control the full search still has a 611-bit number of groups. [Original polynomial construction](polynomial-factor-lanes.md) · [Paired data](../research/quartic-sign-holdout.json)

## Why the same polynomial suffices

Suppose $N=pq$ with positive odd $p,q$ and $\max(p,q)\le2\min(p,q)$. A public coprime modulus $R$ gives the possible unordered remainder pairs $\{u,w\}$ with $uw\equiv N\pmod R$. For one orientation, the quartic construction produces coefficients such that
$$
T(x,y)=d y^2+b y+e+a x+c x^2,\qquad F(x)=x^2 T(x,N/x).
$$
It certifies $R^4\mid T(x,y)$ whenever $x,y$ are integers, $xy=N$ and $x\equiv u\pmod R$. Its magnitude estimate uses $|x|,|y|\le B=\lfloor\sqrt{2N}\rfloor$ and gives $|T(x,y)|<R^4$. Hence $F(x)=0$. Both statements apply when $x,y$ are negative.

A true pair $z,t$ with remainders $-u,-w$ gives $(-z)(-t)=N$ and $-z\equiv u\pmod R$. The equation already built for $u$ therefore has root $-z$. Setting $L=\lceil\sqrt{N/2}\rceil$, search $[L,B]$ and $[-B,-L]$ in the same coordinate $k=(x-u)/R$. Taking absolute values of the recovered coordinates gives positive factors. Both bands together have at most four distinct candidate magnitudes because the polynomial is nonzero of degree at most four. Each reported pair is checked against the original product, balance, and signed remainders. [Lean corollaries for negative roots and candidate count](../PrimeFactors/SignedFactorLanes.lean) · [Search implementation](../experiments/quartic_factor_lanes.py)

## Counting sign groups and retaining fixed pairs

Represent $u,w$ as ordinary unit residues from 1 through $R-1$. For $R>2$ simultaneously negating them replaces the sum $u+w$ by $2R-(u+w)$. The search keeps $u+w<R$ and tests both bands. When $u+w=R$, negation exchanges the two members of the same unordered pair, so the positive band suffices.

If $Q$ is the number of ordinary unordered pairs and $B_-$ is the number of roots of $v^2\equiv-N\pmod R$, exactly $B_-/2$ of the unordered pairs are fixed. Each is $\{v,-v\}$ with distinct members. The resulting number of groups is $(Q+B_-/2)/2$. The code computes $B_-$ locally on the prime powers of the public radix. For $R=1,2$, negation is already the identity on residues and the unsigned count applies. The unit tests enumerate the quotient directly on radices 1 through 69 and exercise fixed pairs and both signs. For example $247=13\cdot19$ has $R=16$; its successful pair $\{13,3\}$ is fixed. [Tests](../tests/test_quartic_factor_lanes.py) · [Fixed-pair fixture](../benchmarks/quartic-factor-lanes.json)

## Measurements on identical search spaces

We used the eight previously certified products generated from `quartic-lane-holdout-v1`. Both modes recomputed their own radix, tables, lattice bases and integer roots from the product. Each covered all the same positive remainder pairs. Times sum the per-input medians of three runs, alternating order with run and sample index, on arm64 macOS 27.0.1 and CPython 3.9.6. Lean verification is separate.

| Complete method | Positive pairs covered | Lattice reductions | LLL size reductions | LLL swaps | Root-isolation nodes | Seconds |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Positive bands | 2,068 | 2,068 | 167,131 | 114,183 | 4,994 | 0.800 |
| Shared polynomial for both signs | 2,068 | 1,036 | 83,899 | 57,359 | 5,022 | 0.426 |

The signed method retained every factorization while increasing the number of root-isolation nodes slightly. On these small inputs the earlier three-way comparison measured 0.00337 seconds for the linear midpoint search and 0.00231 seconds for ordinary trial division. [Signed comparison script](../experiments/quartic_sign_holdout.py) · [Separate linear and trial comparison](../research/quartic-lane-holdout.json)

For the 2,048-bit control we selected the first two sign groups, then compared the two methods on **exactly the same four unordered positive remainder pairs**. The reference method used the same canonical orientation as the original positive solver for each pair. These four pairs differ from the original four-orbit prefix in the earlier benchmark. With common modulus and group selection excluded from both timings, the positive method took 8.70 seconds and four lattice reductions; the signed method took 5.68 seconds and two. Each visited 820 root-isolation nodes and found zero factors in this single matched prefix. The full positive orbit count has 612 bits and the full signed group count has 611 bits. [Matched residues and counters](../research/quartic-sign-holdout.json) · [Capped end-to-end fixture](../benchmarks/quartic-factor-lanes.json)
