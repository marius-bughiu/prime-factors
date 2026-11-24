# The part of the factor gap left after division by a smooth number

For odd $N=pq$ with $p\le q$, put $H=(p+q)/2$ and $D=(q-p)/2$. Fermat searches for the square $H^2-N=D^2$, starting at $r=\lceil\sqrt N\rceil$. If $D=mc$, then **at most $1+\lfloor c^2/(2r)\rfloor$ candidates in the correct residue class** suffice, however large $D$ itself is. The search can try a fixed list of bases and exponents without knowing which divide $D$. [Lean lifting algorithm, completeness and exclusion](../PrimeFactors/GapStride.lean)

## Where the square tests go

More generally, suppose $c^2\equiv s\pmod e$. Set $M=m^2e$ and lift the square roots of $N+m^2s$ modulo $M$. For each root choose the unique offset $0\le z<M$ such that $r+z$ belongs to that root class. Test the midpoints $r+z+Mj$ in increasing order for $j\ge0$. All these quantities come from $N$ and the chosen parameters. The correct midpoint belongs to one such class because

$$H^2=N+m^2c^2\equiv N+m^2s\pmod M.$$

Its index satisfies

$$2r Mj\le 2r(H-r)\le H^2-r^2\le m^2c^2,\qquad 2re j\le c^2.$$

Thus testing $B$ candidates per root finds the pair whenever $c^2<2reB$. Conversely, exhausting all the classes without a square proves $c^2\ge 2reB$ for any pair satisfying the hypothesized divisibility and residue. The formal statement handles the boundary at equality. Setting $e=1$ needs no promise about $c$. If $m$ includes the entire 2- and 3-primary parts of $D$, the remaining $c$ is coprime to 6 and its square is 1 modulo 24. The stronger stride $24m^2$ follows from a checked finite identity.

For $60701$, the ceiling square root is 247. With $m=25$, the two offsets modulo 625 are 27 and 104. The second gives $351^2-60701=250^2$, hence $101\cdot601$. Starting at $m=1$ and trying $m=5,25$ in succession took five midpoint square tests. The public lifting routine enumerates exactly the roots for arbitrary mixed radices, including at singular primes. [Checked numerical example](../PrimeFactors/GapStride.lean)

## Cost of discovering a useful divisor of the gap

For a fixed odd prime $\ell\nmid N$ and $e=1$, there are at most two roots modulo $\ell^{2v}$ for every $v\ge1$. A root modulo $\ell$ is nonzero and the derivative $2H$ is invertible there, so precisely one of its $\ell$ next digits lifts. Trying all $m=\ell^v$ through the bit length of $N$ takes $O(\ell\log N)$ modular digit trials for a fixed base, reusing roots between levels, and $O(B\log N)$ midpoint tests. For a fixed finite set of bases one may enumerate exponent tuples for $m\le N$. Their number is polynomial in $\log N$ with degree at most the number of bases. For $e=1$ and $\gcd(N,m)=1$, the Chinese remainder theorem gives at most $2^{\omega(m)+1}$ roots, including the possible factor of two at the dyadic prime. A common prime of $N$ and a tested base can be detected by a gcd.

For arbitrary factors there is no guarantee that a fixed set of bases removes much of $D$. One way to quantify the assumption is to count **integer gaps**, before any primality condition. Among $1\le D\le X$, the exact number whose $\ell$-free part is at most $Y$ is

$$\sum_{v=0}^{\lfloor\log_\ell X\rfloor}\left(L_v-\lfloor L_v/\ell\rfloor\right),\qquad L_v=\min\bigl(\lfloor Y\rfloor,\lfloor X/\ell^v\rfloor\bigr).$$

Each term counts possible $c$ for a different exact valuation. For fixed $\ell$ and $1\le Y\le X$, this is $O_\ell(Y(1+\log(X/Y)))$ by summing the geometric tail. Even across all powers of one base, this covers only a small fraction of possible integer gaps when $Y$ is on the order of $\sqrt X$. A separate prime-counting argument gives sharp coverage among actual prime pairs, with a comparison at equal budgets. [Frequency proof and measured work](gap-search-frequency.md)

McKee used the squared-modulus observation in his rational version of Fermat’s method. Steinfeld and Zheng and later Bahig, Nassr and Bhery investigated congruence relations between prime factors and the shared-binary-digit case. Here the verified statement concerns the residual half-gap $c$, the actual per-class search budget, and the exclusion after a miss. Its proof is elementary and unconditional. [McKee, *Speeding Fermat’s factoring method*](https://doi.org/10.1090/S0025-5718-99-01133-3) · [Steinfeld and Zheng](https://research.monash.edu/en/publications/an-advantage-of-low-exponent-rsa-with-modulus-primes-sharing-leas/) · [Bahig, Nassr and Bhery](https://www.naturalspublishing.com/files/published/01cuz818m162py.pdf)

## A certified 2048-bit product

The public benchmark tries $m=5^v$ in sequence for $0\le v\le256$, with $e=1$ and one midpoint per root. In the successful case the two unknown primes have 1,024 bits each, $q/p\approx1.19409$, and both $(p-1)/2$ and $(q-1)/2$ are prime. The four signed common divisors in the order $(p-1,q-1),(p-1,q+1),(p+1,q-1),(p+1,q+1)$ are $2,2,2,12$. The exact exponent of five in $D$ is 220. Already at $v=219$ a first midpoint yields both factors. The search uses just the public product and budgets. It performs **438 midpoint square tests and 4,375 small-digit modular tests**. The offset of the successful midpoint from $\lceil\sqrt N\rceil$ has 1,016 bits. [Fixture](../benchmarks/gap-stride.json) · [Product-only search](../experiments/gap_stride.py) · [Downloadable Lean certificate](https://marius-bughiu.github.io/prime-factors/proofs/gap-stride-2048.lean)

The input was constructed with $p=2u+1$ and $q=2v+1$. We chose prime $u,v$ with sufficiently smooth parts of $u-1,v-1$ to certify primality and imposed $v\equiv u\pmod{5^{220}}$. Its prime factors are distinct from the earlier public examples. Stopping at exponent 218 gives 437 unsuccessful midpoint tests and 4,355 modular tests. The previous cubic-period product, run under the full budget, stays unresolved after 513 midpoint tests and 5,115 modular tests. The fixtures separately record each remaining cofactor. [Published results](https://marius-bughiu.github.io/prime-factors/#runs)
