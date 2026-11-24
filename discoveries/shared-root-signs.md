# What extra fractions from one random square contribute

One sampled square can give several smooth fractions and even guarantee a factor. Their roots all come from the same draw. For example, modulo 437 the square of 60 is 104. There is no fraction for 104 with both denominator and absolute numerator at most 14. A full Euclidean chain finds $-21/4$ and $-1/21$. Together they give the primes 19 and 23, whichever of the four roots of 104 was sampled. [Lean certificates](../PrimeFactors/SharedRootSigns.lean)

## Enumerating the fractions on one Euclidean chain

Let $N>1$ and let $1\le r<N$ be a unit. Seek reduced signed fractions $b/a$ with $a>0$, $ar\equiv b\pmod N$ and $2a|b|<N$. Since $r$ is a unit, $b=0$ would imply $N\mid a$ and the fraction would fail to be reduced. For $b\ne0$, put $k=(ar-b)/N$. Every common divisor of $a,k$ divides $a,b$, so $k/a$ is reduced. The strict height bound gives

$$
\left|\frac rN-\frac ka\right|=\frac{|b|}{Na}<\frac1{2a^2}.
$$

By Legendre's theorem, $k/a$ is a convergent of $r/N$. If the Euclidean step gives the remainder $B$ and signed coefficient $t$ with $B\equiv tr\pmod N$, its fraction is $\operatorname{sign}(t)B/|t|$. Start from $(N,0),(r,1)$ and visit each positive remainder, testing the height and coprimality. Indeed consecutive Euclidean coefficient vectors have determinant $\pm1$. At a convergent, $\gcd(a,|b|)=\gcd(a,N)$, so a nonprimitive candidate inside this height bound also supplies a proper gcd with $N$. The chain has $O(\log N)$ steps. Extracting all eligible fractions this way already follows from classical rational reconstruction by applying the bounded theorem separately with limits $|b|,a$. [Monagan, *Maximal Quotient Rational Reconstruction*, Theorem 1(ii)](https://ftp.cecm.sfu.ca/personal/monaganm/papers/MQIRR.pdf) · [Lean application of Legendre's theorem](../PrimeFactors/SharedRootSigns.lean)

The first coefficient can matter. If $r<N/2$, the convergent $0/1$ supplies $b=r$. If $r>N/2$, the first division has quotient one and the convergent $1/1$ supplies $b=r-N$. The canonical expansion ending in a quotient at least two suffices. The alternative expansion ending in one adds a penultimate denominator $N-a_{\rm prev}\ge N/2$, since the last canonical step has $N\ge2a_{\rm prev}$. Every eligible nonzero $b$ requires $a<N/2$. The final convergent $r/N$ gives zero remainder and is omitted. The signed pairs use the strict bound throughout. [Euclidean completeness and endpoint test](../experiments/fraction_chains.py)

## How to count the independent outcomes

Now let $N=pq$ for distinct odd primes. Draw $x_s$ independently and uniformly from its units and expose just $r_s=x_s^2\bmod N$. Choose all fractions, smoothness tests, and the dependency space from these residues and independent randomness. Condition on this transcript. For each retained fraction $b_i/a_i$ from draw $s(i)$, the lifted square relation has left root $a_i x_{s(i)}$ and signed norm $a_i b_i$. All denominators and norms used below must be units. A proper gcd gives a divisor immediately. The sign of the integer norm gets its own parity column alongside the small primes. [Square relations from rational reconstruction](rational-square-search.md)

Let $D$ be the binary vector space of dependencies whose selected norms have positive square product. For $m$ sampled sources, define $P:D\to\mathbb F_2^m$ by adding each dependency's row-selection bits separately within each source. Fix one reference root per source in the proof. Changing that root's signs at $p,q$ contributes one fair bit $h_s$ recording whether its two signs changed differently. These bits are independent across draws, including draws that happen to give the same residue. For a dependency $v$ let $L_0(v)$ record whether the reference roots give a proper factor. The actual split bit is

$$
L(v)=L_0(v)+\sum_s h_s(Pv)_s.
$$

The split bit is a linear functional on the dependency space. When two subsets overlap, the sign of a repeated negative norm changes both CRT signs together. The only random shifts of $L_0$ are functionals of the form $h\circ P$. Their image is exactly the functionals on $D$ that vanish on $\ker P$. Every such shift has $2^{m-\operatorname{rank}P}$ preimages, since two shifts agree precisely when the source functionals agree on $\operatorname{im}P$. [Original independent-root theorem](random-relation-signs.md) · [Projected image and exact fiber counts](../PrimeFactors/SharedRootSigns.lean)

There are two cases.

* If any dependency in $\ker P$ splits the product, some gcd succeeds with probability one conditional on the transcript. Each source occurs $2k_s$ times there. Its contribution to the modular left root is $r_s^{k_s}$. Multiply these powers by the selected denominators and compare with the integer square root of the product of the norms. Everything needed for this test is public.
* If every dependency in $\ker P$ gives only a global sign, then the exact probability that all dependency gcd tests fail is $2^{-\operatorname{rank}P}$. Basis tests suffice. To distinguish the two cases, eliminate the prime and sign columns to obtain a basis for $D$, then eliminate its source parity vectors. The zero projections give a basis for $\ker P$ when the row operations are also carried on the dependency vectors. The remaining pivots count the independent random bits that these dependencies can use.

Keeping at most one smooth fraction per draw makes $P$ injective on $D$, so the earlier $2^{-\dim D}$ failure formula applies directly. Keeping every smooth fraction can add both kinds of dependencies. The rank formula assigns no success probability to the still-unmeasured event of gathering enough smooth fractions from a general large product. [Probability and deterministic product theorems](../PrimeFactors/SharedRootSigns.lean)

If a draw contributes exactly one selected fraction to a square dependency, every prime with odd exponent in its absolute norm must divide a selected norm from another draw. This lets us bound the chance of such a dependency by counting which prime divisors the other draws can supply. [Bound for fractions from distinct draws](smooth-fraction-budget.md)

## A factor from two rows of the same draw

For $N=437$ the balanced limit is $\lfloor\sqrt{(N-1)/2}\rfloor=14$. For $r=104$, the Euclidean remainders are $104,21,20,1$, with coefficients $1,-4,17,-21$. They give signed fractions $104/1,-21/4,20/17,-1/21$. The first contains the prime 13 and the third exceeds the height bound. At a prime cutoff of 7, the two negative rows remain. Each lies outside the balanced box and has a nonsquare signed norm.

Their signed norms are $-84$ and $-21$. The product is $42^2$. The lifted left root uses the sample twice, giving $4\cdot21\cdot104\equiv433\pmod{437}$. Thus $\gcd(433-42,437)=23$ and $\gcd(433+42,437)=19$. Here $D$ has dimension one, $P$ has rank zero, and the deterministic dependency splits. Lean checks the exact factors and exhausts the balanced box at this residue. [Checked example](../PrimeFactors/SharedRootSigns.lean)

## The same 16 sampled products at every balance

We reused the 16 certified 79-bit products and the exact root stream from the bounded-fraction trial. Each product received 8,192 draws at a prime cutoff of 4,096. Checking one balanced box had produced 61 smooth rows. Testing every eligible fraction raised this to **960 rows across 959 draws**. Keeping the first smooth fraction on each draw gave 959 rows. For each product both chain strategies still had zero independent square dependencies at this budget. [Paired results](../research/fraction-chain-panel.json) · [Original sample](rational-square-search.md#what-happened-in-the-tests)

On the first sampled input we tested each new dependency as it appeared, with the same ceiling of 2,097,152 draws. All three methods recovered 574,883,478,241 and 911,431,354,859. The table reports one sequential run on an arm64 Mac using Python 3.9.6. CPU time covers discovery, including the Euclidean walks, smoothness checks, elimination and the successful gcd.

| Fraction strategy | Draws until split | Smooth rows | Dependency gcds tested | CPU seconds |
| --- | ---: | ---: | ---: | ---: |
| One balanced box | 1,211,456 | 540 | 1 | 10.28 |
| First smooth fraction on each chain | 70,509 | 538 | 3 | 17.44 |
| Every smooth fraction on each chain | 70,166 | 538 | 2 | 18.62 |

Scanning all proportions needed about seventeen times fewer draws here. Its extra fraction checks took more CPU time in this implementation. The full-size control gave 27,583 eligible fractions across 32 draws and no smooth row. A separate probability bound covers all these proportions even with a list of up to a trillion primes. [CPU measurements and witnesses](../research/fraction-chain-first.json) · [CI fixtures](../benchmarks/fraction-chains.json) · [Uniform 2,048-bit bound](smooth-fraction-budget.md)

Reproduce the small panel with `python3 -m experiments.fraction_chains --panel` and the online comparison with `python3 -m experiments.fraction_chains --first-long`.
