# Reading a semiprime from one weighted multiplication count

Given a product $N=pq$ of distinct odd primes, suppose a black box evaluates the sum of the weights of the ordered assignments $xy=N$ on binary input words $x,y<B$. It must count each assignment once and allow an independent scalar weight on each input bit of both words. One evaluation over an ordinary odd prime-power ring can recover both factors with polynomial postprocessing. The multiplier keeps its original gates and wires.

There are two precision bounds. A Lean-verified ternary decoder obtains the exact sum of the factors once the period exceeds the width of a public interval. A second, paper-only decoder uses lattice reduction and needs a ring element of about one quarter of the input bit length. These are precision and postprocessing results. The cost of obtaining the ring element is additional. The quantitative tensor-contraction theorem used elsewhere in this project has a power-of-two coefficient modulus, so its running-time guarantee does not cover these odd-modulus queries. [Lean proofs and executable ternary decoder](../PrimeFactors/ExponentialReadout.lean) · [Quantitative contraction theorem and coefficient ring](https://github.com/openai/math/blob/main/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/quantitative-reduction.tex)

## The scalar and its inverse

Choose an odd prime $r$, precision $k\ge0$, period $M=r^k$, and ring modulus $rM$. On **both** inputs, a zero bit always weighs 1. Bit zero also weighs 1 when set. Setting bit $i\ge1$ has weight $(1+r)^{2^{i-1}}\bmod rM$. Repeated squaring gives all local weights in linear time in the input width, measured in ring multiplications. In the box $q<B\le N$ with $p<q$, the two orientations have identical weights. The contraction returns

$$C=2(1+r)^h\pmod{rM},\qquad h=\lfloor p/2\rfloor+\lfloor q/2\rfloor=(p+q-2)/2.$$

If $N<B$, there are also $(1,N)$ and $(N,1)$. Subtract $2(1+r)^{\lfloor N/2\rfloor}$ in the ring before decoding. The ternary proof checks this correction for every positive target above 1. The encoded exponent depends on the sum, so exchanging the two accepting factors causes no ambiguity.

For positive $d$, lifting the exponent gives $v_r((1+r)^d-1)=1+v_r(d)$. The multiplier 2 is a unit. Thus two scalars are equal precisely when their exponents agree modulo $r^k$. Lean proves this equivalence for every odd prime. To invert, start with $a=0\bmod1$. At level $j$, test $a+t r^j$ for $0\le t<r$ against $C\bmod r^{j+2}$. Exactly one digit extends the previous solution. This is ordinary prime-power discrete-log digit lifting. It takes at most $k(r-1)$ modular powers, since the final digit candidate follows by elimination. The ternary executable and its correctness for all $k$ are checked in Lean. [Pohlig and Hellman](https://ee.stanford.edu/~hellman/publications/28.pdf)

## Exact public precision for the interval decoder

The decoded $h\bmod M$ gives $S=p+q\bmod M$. Oddness gives $S\equiv N+1\pmod4$ since $(p-1)(q-1)$ is divisible by 4. The Chinese remainder theorem therefore recovers $S\bmod4M$. If both factors lie below $B$, take $A=\lceil N/(B-1)\rceil$. Both are at least $A$, and

$$L=\lceil\sqrt{4N}\rceil\le S\le U=A+\lfloor N/A\rfloor.$$

For the upper bound, expand $(p-A)(q-A)\ge0$. A stronger supplied lower bound on both factors can increase $A$. Round $L$ upward and $U$ downward to the class $N+1\bmod4$, obtaining $L_0,U_0$. The smallest sufficient $k$ for this interval method is the first with **$4r^k>U_0-L_0$**. Equality of the two sides could identify both endpoints. If $L_0=U_0$, the interval already determines the sum. In every case the implementation shifts its CRT result to the first representative at least $L_0$. The factors then follow from $S^2-4N=(p-q)^2$ by one integer square root. An input-word width of $b$ bounds the factors by $2^b$ and permits a sum up to $2^{b+1}-2$.

## A quarter-width readout with lattice decoding

Choose an odd prime $r$ coprime to $N$ at which the factors are distinct modulo $r$. After decoding $h\bmod M$, form the monic polynomial $X^2-SX+N\bmod M$. Its reduction modulo $r$ has two simple roots. Search all $r$ field elements, then lift each root uniquely one digit at a time by Hensel's lemma. This yields two residues, one of them $q\bmod M$. The work is polynomial when $r$ is polynomial in $n=\lceil\log_2(N+1)\rceil$.

For balanced $p<q\le2p$, choose the least $k$ with $(r^k)^4\ge N$. For the correct residue $0\le a<M$, write $q=a+Mt$. Since $\sqrt N\le q\le\sqrt{2N}$, we have $0\le t<2N^{1/4}$. The monic polynomial $f(T)=T+(a M^{-1}\bmod N)$ vanishes at $t$ modulo the unknown divisor $q\ge N^{1/2}$. May's Theorem 7, with $\beta=1/2$, degree 1 and constant 2, finds all roots this small in polynomial time. Test each output with a gcd and verify the resulting factors. Theorem 7 reaches the stated endpoint via a polynomial number of translations of the smaller interval in Theorem 6. This gives $rM<r^2N^{1/4}$ and hence at most $\lceil(\log_2N)/4+2\log_2r\rceil$ bits per ring element. The lattice algorithm and the Hensel implementation are not part of the Lean decoder. [May, Theorems 6–7, printed pp. 33–38](https://digital.ub.uni-paderborn.de/hsmig/download/pdf/3235#page=35) · [Coppersmith, original small-root results](https://doi.org/10.1007/s001459900030)

The same precision also suffices on the full box without balance. Try dyadic bins $2^j\le q<2^{j+1}$ for the larger factor and put $\beta=j/n$. Then $q\ge N^\beta$ and $q<4N^\beta$, since $2^{n-1}\le N<2^n$ and $0\le\beta\le1$. Thus $t<4N^{\beta-1/4}\le4N^{\beta^2}$ by $(\beta-1/2)^2\ge0$. There are at most $n$ bins, and those containing the larger factor have $\beta$ bounded away from zero for large $n$. May's parameters in Theorem 6 with $\epsilon=1/n$ stay polynomial uniformly over the bins, and the constant-factor interval translations yield the endpoint in Theorem 7. The full-width multiplier and its contraction may cost more than the balanced-width instance.

**Deterministic selection from the product.** For odd prime $r$, the test $(N/r)=-1$ guarantees $r\nmid N$ and $p\not\equiv q\pmod r$. Otherwise their product would be a square in the field. Lean verifies that a nonsquare product gives two distinct simple roots of its factor-sum quadratic. Let $D=N$ if $N\equiv1\pmod4$ and $D=4N$ otherwise. The primitive quadratic character for the positive fundamental discriminant $D$ is nonprincipal. Induce it to the units modulo $4N$ to exclude the prime 2 in both cases. Its kernel is proper and for odd primes outside the modulus its value equals $(N/r)$. Under Dirichlet GRH, Lamzouri–Li–Soundararajan Theorem 1.1(1) therefore supplies such an $r=O((\log N)^2)$ for $4N\ge3000$. Here $\omega(4N)=3$. Smaller inputs can be checked directly. Sieve the small primes and evaluate the Legendre symbol by modular powering, using only $N$. This is the paper implication from the recently released Dirichlet theorem. The analytic least-prime bound has not been ported into this checkout. [Lamzouri–Li–Soundararajan, Theorem 1.1](https://arxiv.org/html/1309.3595v3#S1.SS1) · [Verification of the Dirichlet GRH release](https://math.mit.edu/~drew/grh/)

**Unconditional randomized selection.** Draw a uniform prime in $[n^2,2n^2]$ and first compute its gcd with $N$. If it divides the product, the gcd gives a factor for sufficiently large $N$ unless the product itself is prime, which the input promise excludes. Of the $\gg n^2/\log n$ primes in the interval, only $O(n/\log n)$ can divide $q-p$, since their product divides $0<q-p<N$. For the others the two roots are simple. A singular quadratic is detectable after the query, and a fresh draw costs another contraction. Thus the first contraction suffices with probability $1-O(1/n)$ for every such input. The deterministic selection above avoids spending an evaluation on a singular choice.

## Three expected queries using ordinary dyadic coefficients

A separate paper construction uses the same multiplier with coefficients in $\mathbb Z/2^P$. It requires no new wires and retains both orientations. Put $k=\lceil n/4\rceil$ and $P=k+2$ for $k\ge1$. Weight only the first input, producing a baseline $A=E_p+E_q$ with $E_f=5^{\lfloor f/2\rfloor}$. For a second query choose a uniformly random binary mask $c$ on the input bits. Multiply the existing weight of each set first-word bit $i$ by $(-1)^{c_i}$. This returns $B=\sigma_p E_p+\sigma_q E_q$, where $\sigma_f=(-1)^{\langle c,\mathrm{bits}(f)\rangle}$. Distinct bitstrings have different signs with probability exactly $1/2$. Opposite signs are observable because they give $B\equiv0\pmod4$ and equal signs give $B\equiv2\pmod4$. Keep the baseline when resampling. One baseline plus two sign trials in expectation recovers a split of the two contributions. Testing singleton masks instead guarantees a split in at most one more query than the input-word width.

On a split, divide the canonical even residues $A+B$ and $A-B$ modulo $2^P$ by two to obtain $E_p,E_q$ separately modulo $2^{P-1}$. The order of 5 modulo $2^{P-1}$ is $2^{P-3}$ for $P\ge3$, by the dyadic lifting-the-exponent identity. Binary digit lifting gives $\lfloor f/2\rfloor\bmod 2^{P-3}$, hence $f\bmod2^{P-2}=f\bmod2^k$ because $f$ is odd. Apply the same small-root theorem to the larger factor. In a full box subtract $E_1+E_N$ from the baseline and $\sigma_1E_1+\sigma_NE_N$ from each signed query. This variant uses the dyadic coefficient ring of Theorem D.1, subject to its other network hypotheses. The ternary decoder is the implementation certified in Lean.

An independent five-bit multiplier run on 93 at $P=6$ returned $A=18$. Mask 1 returned 46 and failed the sign test. Mask 4 returned 56 and passed. The two halves modulo 32 are 5 and 13, which yield residues 3 and 15 for the odd factors modulo 16. These observations used only the input, the masks and the precision.

## Checked examples and decoding cost

On $N=93$ with five-bit inputs, the rounded sum interval is $[22,34]$, leaving four candidates. The first sufficient ternary precision is $k=2$, so the modulus is 27. The contraction returns 17, the executable decoder gives $S=34$, and the two primes are 3 and 31. Lean checks the finite accepting box, scalar, sum and factorization. An independent schoolbook multiplier contraction given only the product, the binary width and the weights returns the same scalar. It joined 1,772 table rows and reached a largest table of 512 rows. Replay it from the repository root with the following commands. [Multiplier and contraction routines](../experiments/bit_marginals.py)

```sh
lake env lean -DwarningAsError=true PrimeFactors/ExponentialReadout.lean
python3 - <<'PY'
from experiments.bit_marginals import Table, contract, multiplier_tables

class Ring:
    tags = [1] + [pow(4, 2**i, 27) for i in range(4)]

    def gate(self, op, a, b):
        return (a+b if op == '+' else a*b) % 27

ring = Ring()
network = multiplier_tables(93, 5, ring)
for i, tag in enumerate(ring.tags):
    y = 1 << (5+i)
    network.tables.append(Table(y, {0: 1, y: tag}))
print(contract(network, ring))
PY
```

For the three synthetic 2,048-bit inputs below, the public interval calculation uses $B=2^{1024}$. Ternary decoding was measured with the pinned Lean 4.19 runtime on arm64 macOS, using the median of three runs per input. For these timing tests the known factors supplied the scalar before the timer started. The measurements cover the ternary decoder and CRT, excluding Lean startup, large multiplier contraction, certificate generation and lattice reduction. The rightmost column reports the required ring precision for the paper-only lattice method. [Shifted input](../benchmarks/shifted.json) · [Common-predecessor input](../benchmarks/reduced-orders.json) · [Cubic-period input](../benchmarks/cyclotomic-periods.json)

| Input | Ternary $k$ | Ring bits for exact sum | Lean decode | First $r$ with $(N/r)=-1$ | Lattice precision $k$ | Ring bits for lattice method |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Shifted | 642 | 1,020 | 0.585 s | 11 | 148 | 516 |
| Common predecessor | 643 | 1,021 | 0.604 s | 3 | 323 | 514 |
| Cubic period | 642 | 1,020 | 0.602 s | 3 | 323 | 514 |
