# Choosing a multiplier almost as large as the product

Given only the public product $N$, try a multiplier $r=a^2N+b$. Its size grows with $N$, and the first square above $4rN$ is easy to locate. On 10,961, two nonsquare remainders from different multipliers multiplied to a square. The resulting gcds gave 97 and 113. Ordinary Fermat search found the same pair on its first test. The new search found no additional split on the exhaustive small panels and found no factor on either 2,048-bit control. [Individual benchmark inputs](../benchmarks/affine-excess.json)

## What the large weights become

Take positive integers $a,b\le K$ and allow the first $J$ labels in the public congruence class. Put $l=\lceil b/a\rceil$. When $(l-1)^2<4N$, squaring the two neighboring integers gives $\lceil\sqrt{4rN}\rceil=2aN+l$. The permitted labels equal $r+N$ modulo $g=\gcd(24,2(r+N))$. Writing a label as $2aN+c$, both $g$ and the first permitted $c$ depend only on $a,b$ and $N\bmod24$. Each later label adds $g$. With $u=ac-b$, the exact remainder is

$$
(2aN+c)^2-4rN=4uN+c^2,\qquad
0<c<D=K+24J,\quad 0\le u<V=24KJ.
$$

For a second row $(v,d)$, a square product of remainders gives $z^2=(4uN+c^2)(4vN+d^2)$. The original large labels multiply to $cd$ modulo $N$, so the two gcds are $\gcd(z-cd,N)$ and $\gcd(z+cd,N)$. The finite test covers all pairs of these rows, including weights chosen after seeing the complete product. [Normalization and gcd identities](../PrimeFactors/AffineExcess.lean)

For 10,961, the rows $(12,5)$ and $(24,26)$ give 526,153 and 1,052,932. Their product is $744{,}314^2$. Subtracting and adding $5\times26$ before taking a gcd gives 97 and 113. Independently, $105^2-10{,}961=8^2$, so $105-8=97$ and $105+8=113$. The Lean example checks the nonsquare inequalities, the joint square, both gcds and the primality of the two outputs. [Checked example](../PrimeFactors/AffineExcess.lean)

## Counting the inputs the test can reach

For two positive slopes $u,v$, fix the rows and set $C=|ud^2-vc^2|$ and $x=8uvN+ud^2+vc^2$. A joint square requires

$$
x^2-4uvz^2=C^2.
$$

For $C=0$, the positive root satisfies $cz=d(4uN+c^2)$. On the target inputs $c$ is a unit modulo $N$. Consequently $z\equiv cd\pmod N$, and the two gcds are $N$ and 1. For $C>0$, distinct products yield distinct $x$. After removing the square from $uv$, the project's bound on solutions to the resulting Pell equation gives at most $2H\tau(C^2)$ products at fixed rows with $x<2^H$. Here $\tau$ counts positive divisors. This bound also covers square $uv$, when the equation factors directly. [Norm and injectivity](../PrimeFactors/AffineExcess.lean) · [Counting Pell points](../PrimeFactors/WeightedMultiplierPoints.lean)

Each of the eight possible residues of $N$ modulo 24 gives at most $m=K^2J$ rows, hence at most $8\binom m2$ nonsingular pairs across all classes. We use $C<VD^2$, $x\le 8V^2 2^{2048}+2VD^2$, and $\tau(C^2)^{336}\le 2^{14882}C^{64}$. Counting all squares on those pairs permits either gcd to be trivial. [Divisor estimate](../PrimeFactors/UniformDivisorCount.lean) · [Finite union over the public choices](../PrimeFactors/AffineExcessPopulation.lean)

A constant first remainder ($u=0$) forces $z=cw$, where $w^2=4vN+d^2$. If $v>0$ and $d^2<4X$, with $X=2^{1023}$, then $w$ is the first integer above $\sqrt{4vN}$. An ordinary search with the small multiplier $v$ therefore tests the same square immediately. For a proper split, the two factors $(w-d)/2,(w+d)/2$ receive different primes. Assigning $p<q$ gives $|sp-tq|=d$, $st=v$, $t\le s\le 2t$. Thus each smaller prime has at most $4D T+T(T+1)$ possible partners over all constant-row choices, for $T=\lfloor\sqrt{V-1}\rfloor$. If both slopes vanish, the two gcds are $N$ and 1. [Both signs, prime assignment and partner count](../PrimeFactors/AffineExcessSingle.lean)

The uniform population consists of distinct 1,024-bit primes whose product has 2,048 bits. The entries bound the fraction of those pairs for which *some* choice in the indicated family works. The third column counts any nonsingular positive-row square. The last column counts a proper gcd from either sign across all branches.

| Maximum $a,b$ | Labels per source | Nonsingular square fraction below | Any proper split fraction below |
|---:|---:|---:|---:|
| $2^{64}$ | $2^{64}$ | $2^{-1527}$ | $2^{-861}$ |
| $2^{128}$ | $2^{128}$ | $2^{-1094}$ | $2^{-733}$ |
| $2^{256}$ | 1 | $2^{-791}$ | $2^{-610}$ |
| $2^{256}$ | $2^{256}$ | $2^{-229}$ | $2^{-229}$ |

All four ranges satisfy the ceiling guard and $D^2<4X$ at target size. The bound grants all permitted labels even when iterating through them would be impractical. Its proof uses the unconditional prime-pair count. Other forms of product-dependent multiplier are outside this count. [Population theorem and integer constants](../PrimeFactors/AffineExcessPopulation.lean) · [Eligible prime-pair count](../PrimeFactors/ChebyshevPrimeSample.lean)

## Reproducing the comparison

The command below checks ordinary weight-one Fermat, the first raw and the first congruence-permitted tests at every positive normalized weight, each affine remainder individually, and every distinct pair. It records both gcd signs, direct square tests and squares inferred from component roots. The complete small panels use all unordered, distinct prime pairs of the specified width whose product has twice that width. [Implementation](../experiments/affine_excess.py) · [Counters and controls](../research/affine-excess.json)

    python3 -m experiments.affine_excess

| Prime width | Eligible pairs | Direct joint square tests at $K=4,J=1$ | Inputs split using a zero slope | Inputs with a nonsingular square |
|---:|---:|---:|---:|---:|
| 7 | 42 | 1,182 | 3 | 0 |
| 8 | 148 | 4,152 | 7 | 0 |
| 9 | 543 | 15,215 | 9 | 0 |
| 10 | 1,718 | 48,122 | 24 | 0 |

On the 42 seven-bit pairs, $K=8,J=2$ cost 163,364 direct joint square tests. The only input split by nonsingular rows was 10,961. Both corresponding small-weight baselines split all 42 inputs. Each full-size control used $K=8,J=1$, giving 45 distinct rows and 990 row pairs. Fresh required 600 direct joint square tests and 66 sign gcds. Crossed required 610 and 68. Both searches exhausted their specified choices with the original product still outstanding. [Reproducible report](../research/affine-excess.json)
