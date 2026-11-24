# One gcd that returns the smaller prime

Start with the product $N=pq$ of two distinct odd primes, with $p<q$. Only $N$ is given. The following formula returns $p$. Its expensive step is building a product over many pairs of integers.

Set $U=\lfloor\sqrt N\rfloor$ and $H=\lfloor\sqrt U\rfloor$. Use the lower bound $L=3$, or $L=\lceil\sqrt{N/2}\rceil$ when the input comes with the promise $q\le2p$. For each odd $t$ between 1 and $H$, take the following values with $1\le a\le H$, retaining just those between $L$ and $U$ inclusive.

| Value | Second coordinate |
|---|---|
| $t^2+a^2$ | even $a$ |
| $t^2+2a^2$ | odd $a$ |
| $2a^2-t^2$ | even $a$ |

Let $P$ be the product of the retained values, with repeated occurrences included. Then
$$\boxed{p=\gcd(N,P),\qquad q=N/p.}$$
The prime $p$ itself occurs. If $p$ is 1 or 5 modulo 8, it is a sum of an odd square and an even square. If it is 3 modulo 8, it equals an odd square plus twice an odd square. If it is 7 modulo 8, it equals twice an even square minus an odd square. In each case the representation theorem supplies coordinates with both squares strictly below $p$. They therefore fit the coordinate budget and their value lies in the band. Every retained value is positive and at most $U<q$. Thus none is divisible by $q$ and the gcd is exactly $p$. These classical prime representations and their use here have an elementary proof via quadratic reciprocity and a short rational approximation. [Proof of the exact representations](../PrimeFactors/ShortNormBox.lean) · [Lean theorem for the full product-only formula](../PrimeFactors/NormBatchGCD.lean) · [Details of the three congruence cases](short-norm-boxes.md)

For example, $N=713$ gives $U=26$ and $H=5$. Even a cap of four in both coordinates works. The unrestricted row $2\cdot4^2-t^2$ contains both 31 at $t=1$ and 23 at $t=3$. The band drops 31 and keeps 23. With $L=3$, nine values survive across the three forms at that cap. Their gcd with 713, taken after multiplication, is 23. At full side five, ten values survive and give the same answer. [Search implementation](../experiments/norm_band_product.py) · [Comparison without the upper cutoff](../benchmarks/universal-norms.json)

The optional canonical search also requires $t<a$ in the third form. Each odd prime then occurs in exactly one representation; on a balanced input, the retained product contains its smaller prime only once. [Uniqueness and limits on guessing the right row](selecting-norm-rows.md)

## Computing the product

For fixed $a$ each form allows an interval of first coordinates. For the positive form $t^2+ca^2$ intersect $[L-ca^2,U-ca^2]$ with the possible squares. For the third form use $[2a^2-U,2a^2-L]$. Integer square roots and parity give an interval of array indices for the odd integers $t=2i+1$. Empty intervals cost no evaluations.

Build a binary tree of monic polynomials on these indices, each with factors $X-t^2$. Decompose each requested interval into maximal aligned power-of-two segments. There are at most two segments of any one size per requested interval. At each segment evaluate its polynomial together at all the assigned points $-a^2,-2a^2$ or $2a^2$, according to the form. Multiplying these residues modulo $N$ gives $P$ up to sign. The final gcd ignores this sign. This uses the same modular product and remainder trees as the repository's earlier batch searches. [Modular polynomial arithmetic](../experiments/wide_modulus.py) · [Earlier interval batching](batch-intervals.md)

There are $O(H)$ second coordinates and $O(H\log(2H))$ assigned evaluations. Summing the degrees of the used segment polynomials over all levels also costs $O(H\log(2H))$. Fast multiplication and multipoint evaluation thus give fourth-root bit complexity up to factors polynomial in $\log N$. The Python implementation counts segment requests explicitly and uses the platform's integer multiplication. For $1{,}900{,}014{,}700{,}027$ with the balanced promise it grouped 168,810 retained pairs into 7,767 evaluations and returned the smaller prime 1,000,003 in one gcd. Compare this with the separate one-form search, which can return the larger prime. [Benchmarks and expected work](../benchmarks/norm-band-product.json)

For two 1,024-bit prime factors the sufficient coordinate scale is roughly $2^{512}$. Through $2^{510}$ every nonzero candidate is smaller than either prime. The 2,048-bit control exhausted its coordinate budget. Existing general-purpose deterministic factoring has the stronger $N^{1/5+o(1)}$ bit bound. The theorem here gives an exact formula with a known cost and a limit on how small a search with these particular forms can be. [Size exclusion](norm-orbits.md) · [Harvey and Hittmeir](https://arxiv.org/abs/2105.11105)

Multiplying every odd integer in the same factor interval and taking a gcd also returns $p$. The three quadratic representations explain which coordinates and signs suffice for a different product. Their fourth-root bound alone gives no overall advantage over batching the ordinary interval. [Earlier interval search bound](batch-intervals.md)

## A fresh product and a direct comparison

The comparison input is $6{,}091{,}663{,}632{,}054{,}090{,}929=2{,}423{,}330{,}473\cdot2{,}513{,}756{,}873$. The compressed three-form search recovered its smaller prime as $28{,}677^2+40{,}012^2$. The benchmark regenerated a Lean certificate for both primes and their multiplicities. The comparison also batched the ordinary odd candidates between $L$ and $U$ into consecutive groups, using the same polynomial backend. On this input the odd interval took 3.66 seconds, the compressed quadratic search took 5.32 seconds, and the exact band product took 19.23 seconds. The published timings are individual local runs; the underlying operation counts are reproducible. [Measurements](../research/norms-ordinary-63.json) · [Comparison program](../experiments/norm_comparison.py) · [Lean-checked example](https://marius-bughiu.github.io/prime-factors/#short-boxes-ordinary-63)

We chose the first distinct pair of 32-bit primes whose product had 63 bits in a deterministic stream. For each attempt starting at zero and each ASCII side tag `p` or `q`, concatenate the ASCII seed `norm-search-width-2026-11-v1`, the tag, the attempt and a candidate counter. Both counters are unsigned four-byte big-endian integers; the candidate counter starts at zero for each side and attempt. Read four SHAKE256 output bytes as an unsigned big-endian integer, set the top and bottom bits, and take the first prime. Attempt four supplied the input. The searches received only the product, the balance promise and their public budgets.
