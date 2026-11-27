# Placing divisor checks from the product

Given $N=pq$ with distinct odd primes of the same bit length, we can use twelve-remainder keys to search a contiguous interval of possible smaller factors. With six small seeds and six comparison points, the new placement guarantees **96 consecutive odd candidates**, up from 72 using the same number of squared seeds. It split 8,571 of the 19,546 eligible products of two 12-bit primes. A faster existing factorial implementation split 17,442 of those products in less CPU time by searching four times the original span. [Search implementation](../experiments/twelve_rectangle.py) · [Complete 12-bit comparison](../research/twelve-rectangle-12.json)

## Where the guaranteed coverage comes from

Let $L$ be the first odd integer in the feasible interval for $p$. For $w=\lceil\operatorname{bitlen}(N)/2\rceil$, its lower endpoint before rounding to odd is $\max(2^{w-1},\lceil N/(2^w-1)\rceil)$. A row centered at $G_j=L+2R-1+4Rj$ covers $G_j\pm a$ for every odd $a$ from 1 through $2R-1$. The first $J$ rows cover the first $2RJ$ odd integers starting from $L$. Squared labels give this interval with $R=H$ baby seeds because $(G_j-a)(G_j+a)=G_j^2-a^2$. [Public factor interval](../experiments/short_pascal_row.py) · [Signed-row proof](../PrimeFactors/TwelveRectangle.lean)

The twelve-remainder map satisfies $J(1)=J(3)$ and $J(5)=J(9)$ as exact rational identities. Use all odd offsets up to $2(H+2)-1$ except 3 and 9. The other $H$ representatives cover the skipped offsets too. A candidate $p=G_j\pm3$ gives the signed branch $p$ at baby 1. A candidate $p=G_j\pm9$ gives $2p$ at baby 5, which has gcd $p$ with the odd semiprime. Set $R=H+2$ for $H\ge3$. This saves two polynomial roots for every row and guarantees **$2(H+2)J$ consecutive odd candidates**. Baby 1 has an invertible key denominator even though it is exceptional for the random-sampling theorem. This deterministic search screens denominators; if a denominator vanishes over the whole product it checks the affected signed comparisons directly. [Arithmetic identities and representative count](../PrimeFactors/TwelveRectangle.lean) · [Twelve signed transformations](comparing-twelve-remainders-at-once.md)

The implementation builds the polynomial whose roots are the distinct baby keys and evaluates it at all giant keys. Each nonunit row is refined against the babies. A shared key modulo the entire product is checked with its individual branches. For $N=8{,}417{,}663$, the old range ends at 2,199 and the new range ends at 2,247. The key of baby 1 and the key of center 2,200 yield a gcd of 2,203. The other prime is 3,821. Lean checks the gcd and both primes. [Normal benchmark fixtures](../benchmarks/twelve-rectangle.json)

## When a row can gain an incidental match

For every integer baby $16\le b\le B$, the ten nonidentity signed branches have the form $s+e/d$ with $0<|e|<d\le B+3$. Their numerators have absolute value at most $3B+3$. Suppose a giant is $G=kp+t$ for an unknown prime factor $p>108$. If

$$ (B+3)|t|+3B+3<p, $$

every nonidentity comparison is a nonzero integer of absolute value less than $p$ after replacing $G$ by $t$. Thus the only possible matches there are $t\equiv\pm b\pmod p$. For a public lower bound $L\le p$ the same test with $L$ on the right gives an explicit region in which these branches cannot help. On a short positive-odd offset interval with $(B+3)B+3B+3<p$, every offset at least 16 has a distinct key. Among $1,3,5,7,9,11,13,15$ the two displayed mergers are the only ones at a 1,024-bit prime. This bounds what further merging can save on this same interval. [No-wrap proof and finite classification](../PrimeFactors/TwelveRectangle.lean)

Outside that neighborhood the extra transformations occasionally recover a factor beyond the guaranteed prefix. At $N=551{,}694{,}615{,}343$, the original grid found $593{,}213\times930{,}011$ from baby 49 and giant 541,626, beyond a prefix ending at 542,521. Moving the centers for a larger contiguous prefix lost that particular match. [Checked positive and comparison](../benchmarks/twelve-rectangle.json)

## Measured work

The first row covers the complete population of distinct 12-bit prime pairs giving a 24-bit product. The two larger rows use the previously fixed samples of eligible pairs. Every search uses only $N$ and the public budget. The two rectangle methods have the same number of seed values and giant evaluations. CPU seconds for the whole group are in parentheses. The factorial comparison uses the project's optimized folded wheel-2 interval product and its binary multiplication backend. The last column was added after observing that the optimized implementation was faster on the original interval. It spends four times the candidate span. [Panel code](../experiments/twelve_rectangle_panel.py) · [Factorial algorithm](folded-factorial.md)

| Prime bits, products, $H=J$ | Squared keys | Twelve keys, old centers | Twelve keys, expanded centers | Folded factorial, original span | Folded factorial, fourfold span |
|---|---:|---:|---:|---:|---:|
| 12, 19,546, 6 | 5,753 (1.78) | 6,272 (1.70) | **8,571 (2.01)** | 5,753 (0.74) | 17,442 (1.07) |
| 20, 512, 64 | 85 (0.93) | 116 (0.99) | **130 (1.02)** | 85 (0.19) | 270 (0.38) |
| 24, 256, 128 | 5 (1.11) | 11 (1.17) | **10 (1.19)** | 5 (0.22) | 26 (0.47) |

At 12 bits the expanded centers gained 2,748 splits and lost 449 relative to the old twelve-key centers. At 24 bits they gained five and lost six. The guaranteed prefix grows by a factor $1+2/H$, approaching one as $H$ grows. These results count actual factors, and the timings cover search work before the separate Lean certification step. [12-bit counts](../research/twelve-rectangle-12.json) · [20-bit counts](../research/twelve-rectangle-20.json) · [24-bit counts](../research/twelve-rectangle-24.json)

On each of the fresh and crossed 2,048-bit products, the 64-by-64 expanded rectangle covered 8,448 odd candidates, evaluated 64 giant keys, took 64 row gcds and found no factor. To guarantee the entire feasible interval on the fresh example would require about $2.17\times10^{153}$ baby seeds and as many giant centers for a square rectangle. Neither the rectangle nor its factorial comparison offers a practical general 2,048-bit factorization. Reproduce a population with `python3 -m experiments.twelve_rectangle_panel --bits 12`, using 20 or 24 for the samples. [Full-size fixtures](../benchmarks/twelve-rectangle.json)
