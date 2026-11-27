# Sharing modular powers when a reduced predecessor is smooth

For the same base and the same set of possible prime factors, the reduced-predecessor search can do less arithmetic. At a smoothness bound of 1,000 and a factor width of 1,024 bits, the new search uses at most **123,531 modular multiplications** after setup, counting each square as one multiplication. Producing the old full exponent by a multiplication chain would take at least **171,327**. Both methods split a newly constructed 2,048-bit product. Both left the independently generated comparison unresolved. [Lean coverage proof](../PrimeFactors/SharedSmoothPowers.lean) · [Benchmark inputs and expected results](../benchmarks/shared-smooth-powers.json)

## Why one large prime power suffices

Suppose $N=pq$ with distinct 1,024-bit prime factors. For an accepted base $a$, the residue $v=a^{N-1}\bmod N$ differs from 1. Its orders at $p$ and $q$ divide $(p-1)/g$ and $(q-1)/g$, respectively, where $g=\gcd(p-1,q-1)$. The orders are coprime. The base can be accepted using $N$ alone, and the coverage proof uses elementary arithmetic once acceptance has been checked. Dirichlet GRH enters the earlier bound on how far a deterministic base search must go. Let $C=2^{1024}-1$ and choose a prime bound $B$. The earlier search used the full exponent $E=\prod_{\ell\le B}\ell^{\lfloor\log_\ell C\rfloor}$, where the product ranges over primes at most $C$. It splits if and only if at least one local order divides $E$. This includes every product for which either reduced predecessor has all prime divisors at most $B$. [Earlier proof and exact success condition](smooth-reduced-predecessors.md)

Write $L=\lfloor\sqrt C\rfloor$. Replace $C$ by $L$ in the exponent to obtain a common prefix $E_0$, and for each eligible prime put $t_\ell=\ell^{\lfloor\log_\ell C\rfloor-\lfloor\log_\ell L\rfloor}$. For every integer $1\le d\le C$,

$$d\mid E\quad\Longleftrightarrow\quad d\mid E_0\quad\text{or}\quad d\mid E_0t_\ell\text{ for some eligible }\ell.$$

Indeed, two powers of different primes which divide $d$ are coprime. If both powers exceed $L$, their product divides $d$ and exceeds $C$. Thus at most one prime can require more than the prefix supplies. Multiplication by its $t_\ell$ supplies every missing copy. The converse follows because every tested exponent divides $E$. Applying the equivalence to the two local orders preserves every success of the previous search, including bases that succeed when neither complete reduced predecessor is smooth. [Theorem `same_coverage`](../PrimeFactors/SharedSmoothPowers.lean)

For example, let $C=63$ and $B=5$. Then $L=7$, $E_0=4\cdot3\cdot5=60$, and the possible final multipliers are $8,9,5$. An order of 48 divides $60\cdot8$, an order of 27 divides $60\cdot9$, and an order of 50 divides $60\cdot5$. A factor of 7 in the order would survive every test at this bound.

## A single precomputation and a product gcd

Starting at $v$, apply the prefix powers successively. If an update reaches the global identity, the preceding residue yields a factor using the earlier one-gcd proof. If the finished prefix residue $z=v^{E_0}$ is 1 at exactly one prime, its gcd test finishes. Otherwise both local coordinates are nonidentity. A terminal power $z^{t_\ell}$ can equal 1 at at most one prime, since its two coprime local orders cannot both divide a power of $\ell$. [Local-order and saturation proofs](../PrimeFactors/SharedSmoothPowers.lean)

The remaining exponents all have the same base $z$. In radix 8 for 25 exponents, or radix 16 for 168 exponents, the code builds the digit powers for each position once, uses them in every result, and then discards that position's table. For each $\ell$ it needs only one multiplication per subsequent nonzero digit. A product tree then combines the differences $z^{t_\ell}-1$ modulo $N$. One gcd at its root detects a hit. If the gcd is $N$, the primes have hit at different leaves. At most $\lceil\log_2 k\rceil$ further gcds locate a proper factor among $k$ candidate powers. The tree has already computed the products needed for that descent. A miss takes two post-setup gcds. The search stores $O(k+2^w)$ modular residues at window width $w$, in addition to its sieve and integer exponents. [Search implementation](../experiments/shared_smooth_powers.py)

Fixed-base precomputation is classical. Pollard's method and later dynamic-scaling work also organize sweeps of prime powers. The coverage statement here uses the bound on a *single hidden local order* to justify independent tests with a shared base. Code and proofs in this project were written for these tests. [Brickell, Gordon, McCurley and Wilson](https://www.microsoft.com/en-us/research/publication/fast-exponentiation-with-precomputation-algorithms-and-lower-bounds/) · [Pollard](https://doi.org/10.1017/S0305004100049252) · [Dynamic Scaling Pollard’s P-1 Algorithm](https://doi.org/10.3390/cryptography10040057)

## Operations and elapsed time

| Prime bound | Terminal powers | Squares | Other modular multiplications, including product tree | Total | Full exponent chain lower bound |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 100 | 25 | 13,386 | 6,435 | 19,821 | 25,546 |
| 1,000 | 168 | 85,924 | 37,607 | 123,531 | 171,327 |

The executable counts each square and each other modular multiplication, including all table construction. Regression tests reproduce the counts on a small modulus because the schedule depends only on $B,C$. Lean proves the equivalence of the sets of covered orders. Prefix early exits can reduce them. For the full exponent comparison, the largest exponent an ordinary addition chain can reach after $s$ multiplications from the initial base is $2^s$. This gives $\lceil\log_2 E\rceil$ independently of its window parameters or how the prime powers are grouped. This lower bound applies to a chain producing the formal exponent $E$. Factors found at earlier checkpoints can cost much less. Computing the public exponent list, selecting a base and checking gcds have separate costs. The old and new methods have identical setup. [Operation counts and exhaustive small-order tests](../tests/test_shared_smooth_powers.py)

| Product | $B$ | Shared powers | Full prime-power checkpoints | One fused full power |
| --- | ---: | ---: | ---: | ---: |
| Previously constructed, early hit | 100 | Split, 0.158 s | Split, 0.027 s | Split, 0.254 s |
| Newly constructed, below threshold | 100 | Gcd 1, 0.152 s | Gcd 1, 0.223 s | Gcd 1, 0.216 s |
| Same newly constructed product | 1,000 | Split, 0.926 s | Split, 1.488 s | Split, 2.991 s |
| Fresh comparison | 100 | Gcd 1, 0.155 s | Gcd 1, 0.228 s | Gcd 1, 0.223 s |
| Fresh comparison | 1,000 | Gcd 1, 0.947 s | Gcd 1, 1.539 s | Gcd 1, 1.509 s |
| Crossed comparison | 1,000 | Gcd 1, 0.941 s | Gcd 1, 1.540 s | Gcd 1, 1.595 s |

Times come from one local run and exclude the common base selection and proof checking. Both control implementations use Python's built-in modular powering. One checks the gcd after each full prime-power block. The other applies the whole exponent at once, then replays checkpoints if both local orders were killed. The early-hit example shows the cost of waiting until all common prefix blocks have run. At $B=1{,}000$, the new example required a saturated product-tree descent. Its nine batch gcds include eight steps down the tree. [Benchmark controls](../scripts/shared_smooth_benchmark.py) · [Compared algorithms](../experiments/shared_smooth_powers.py)

For the new example set $g=2\cdot1{,}000{,}000{,}007$, $p=1+g\,991^{86}2^{113}3^{15}$ and $q=1+g\,997^{82}5^{54}7^{18}$. We selected these primes to put large powers near the end of the $B=1{,}000$ menu and verified both primes and their product in Lean. The searches received the decimal product, prime bound and factor width. The two comparison products remain unresolved. For each one, the checked full-exponent gcd equals 1 at $B=1{,}000$. Under the stated two-prime width assumption, each reduced predecessor therefore has a prime divisor above 1,000. The frequency of a smooth reduced predecessor among independently chosen large primes remains open here. [Decimal fixtures](../benchmarks/shared-smooth-powers.json) · [Exclusion certificate generator](../scripts/shared_smooth_benchmark.py)
