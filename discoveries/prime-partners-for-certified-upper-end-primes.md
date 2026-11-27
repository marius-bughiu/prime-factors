# How many prime partners work with an upper-end prime?

Let $U=2^{1024}$. The certified prime $q=U-26096496244809999$ has more than $2^{959}$ smaller prime partners in one explicit interval, assuming the Riemann hypothesis (RH). For every such product $N=pq$, the existing endpoint test recovers both factors with one integer square root. Ordinary Fermat search misses at least its first $2^{914}$ consecutive midpoint tests. The split and the Fermat comparison are unconditional for each prime in the interval. RH supplies the lower bound on how many primes it contains. [Prime certificate](../PrimeFactors/NearEndpointPrimes.lean) · [Partner theorem](../PrimeFactors/FixedEndpointPartners.lean)

The following two counts concern different intervals. Both upper-end primes in the second row can be paired with every prime in its smaller-factor interval.

| Upper-end prime choices | Smaller prime interval | Conditional count of distinct products | Ordinary midpoint misses per product |
|---|---|---:|---:|
| $U-26096496244809999$ | $[U-4W+1,U-3W]$, $W=2^{969}$ | $>2^{959}$ | $\ge 2^{914}$ |
| Either $U-26096496244809999$ or $U-580951370506755599$ | Same interval formula, $W=2^{964}$ | $>2^{955}$ | $\ge 2^{904}$ |

Both factors have 1,024 bits and the product has 2,048 bits. The endpoint algorithm receives just $N$ and $U$. Knowledge that an input uses one of these two particular upper primes also permits direct trial division by those primes. The fixed-prime counts describe a special family. The existing upper bound for a uniformly sampled eligible prime pair places the endpoint test's overall success probability below $2^{-987}$. [Endpoint algorithm and whole-population upper bound](when-the-product-is-near-the-largest-square.md)

## Why one square root suffices

Write $b=U-q$ and $a=U-p$. Choose $W$ such that $16W\le U$, $0<b$, $8b\le W$ and $Wb\le U$. For every partner in the stated interval, $3W\le a<4W$ and $ab<4U$. The public congruence of the factor sum gives $ab$ modulo $U\cdot\gcd(24,2(N+1))$. The modulus is at least $4U$. Its least residue therefore gives $ab$ exactly. From $N=(U-a)(U-b)$ the decoder obtains $a+b$, and an integer square root gives their difference. It also checks that the predicted factors multiply to $N$. [Endpoint proof](../PrimeFactors/EndpointOffsetProduct.lean)

For ordinary Fermat search put $m=(p+q)/2$ and $d=(q-p)/2$. Since $2d=a-b$, the interval guarantees $16d\ge23W$ and hence $d^2\ge2W^2$. Let $K=W^2/U$ for the two powers of two in the table. Then $m\le U$ implies $2mK\le d^2$. Consequently $N=m^2-d^2\le(m-K)^2$, giving $\lceil\sqrt N\rceil+K\le m$. Any successful square before $m$ would represent $N$ as $(x-y)(x+y)$ with smaller midpoint than the unique proper factor pair. The trivial pair $1,N$ has still larger midpoint. This rules out every one of the first $K$ square tests. [Unconditional comparison](../PrimeFactors/FixedEndpointPartners.lean)

## Where the prime count enters

Write $l=U-4W+1$ and $u=U-3W$. Schoenfeld's inequality (6.18) under RH bounds the error of $\pi(x)$ from the logarithmic integral by $\sqrt{x}\log x/(8\pi)$ for $x\ge2657$. Both endpoints lie in $[U/2,U]$, so their combined error is below $57\cdot2^{512}$. Since $\log u<710$ and $u-l=W-1$, the number $P$ of primes in the closed interval satisfies
$$
W-1\le710(P+57\cdot2^{512}).
$$
For $W\ge2^{530}$ this gives $W<1024P$. Distinct choices of the smaller prime produce distinct products for fixed $q$. The two-anchor count uses unique factorization and $p<q$ to rule out duplicates across both anchors. Lean proves these implications from the displayed lower bound, and also accepts the project's existing package of Schoenfeld interval estimates. [Schoenfeld, equation (6.18)](https://www.ams.org/mcom/1976-30-134/S0025-5718-1976-0457374-X/S0025-5718-1976-0457374-X.pdf) · [Zeta zero-location statement in the pinned release](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab/src/Statements.lean) · [Existing endpoint error calculation](switching-after-a-long-fermat-search.md)

## Two runs from the product alone

We constructed one product from each row of the table. The smaller prime was $p=U-4W+i\,2^{512}+1$. The first example uses $W=2^{969}$ and $i=85$, the second $W=2^{964}$ and $i=1261$. Both pairs consist of distinct 1,024-bit primes, and the two products share no prime. The search receives only the product, predicts one offset product and takes one square root. After recovery, Lean checks the factorization by combining the derived smaller prime's certificate with the corresponding upper prime's library theorem. The calculated distances of the ordinary Fermat midpoints are respectively 916 and 906 bits long. The separate baseline calculation uses one additional square root. [Benchmark fixtures](../benchmarks/endpoint-offset-product.json) · [Library prime certificates](../PrimeFactors/NearEndpointPrimes.lean)

## A wider partner interval from an unconditional estimate

For any prime $q$ with $U-255\le q<U$, the test works with **every prime** $p$ in $(63U/64,127U/128]$. Here $(U-p)(U-q) < (U/64)255<4U$. Ordinary Fermat's first successful midpoint is at least $2^{1006}$ steps beyond its starting point. Dusart's unconditional prime-count bounds, applied at both endpoints, give **more than $2^{1007}$** such smaller primes for each eligible $q$. Different choices of either prime yield different products. The Lean theorem accepts Dusart's published inequality as an explicit hypothesis. It also takes the primality of $q$ as an input. [Endpoint inequalities and exact counting argument](../PrimeFactors/TopPartnerInterval.lean) · [Dusart (2010), equation (6.6)](https://arxiv.org/pdf/1002.0442#page=9)

Only two offsets in that 255-integer interval can give a prime, 105 and 179. Lean rules out every other offset. Hence two direct divisibility tests suffice for any composite with a proper prime factor there, regardless of the other factor's size. This is a simpler baseline for the tiny endpoint interval. [Finite exclusions and two-test algorithm](../PrimeFactors/PrimesAtUpperEndpoint.lean)

PARI/GP 2.19.1 generated and verified elliptic-curve primality certificates for both remaining candidates. Together with Dusart's published bound, the two choices give more than $2^{1008}$ distinct products in the wider partner calculation. The project's pinned Lean toolchain verifies the deduction from the two primality hypotheses. A separate Lean 4.35.0-rc3 build verifies both complete elliptic-curve certificates. Its two theorems use only the same three standard axioms accepted by the project. The 4.19 package verifies the 55-bit and 60-bit offsets directly. [Reproduce the separate Lean proofs](../research/endpoint-ecpp/README.md) To reproduce the external check, run these two lines in GP. The output for each offset confirms both the certified input and the validity of its certificate. [PARI primecert and primecertisvalid](https://pari.math.u-bordeaux.fr/dochtml/html-stable/Arithmetic_functions.html#primecert)

```gp
default(parisizemax,512000000)
for(i=1,2,d=[105,179][i];n=2^1024-d;setrand(1);c=primecert(n);print([d,c[1][1]==n,primecertisvalid(c)]))
```
