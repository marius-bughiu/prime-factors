# Recovering both factors from predetermined Salié measurements

Suppose the only input is a 2,048-bit product $N=pq$ of two distinct odd primes. **89 predetermined measurements, each rounded to 53 fractional bits, suffice to recover both factors by ordinary integer arithmetic.** Each measurement is a normalized Salié sum whose formula uses only $N$. A simpler schedule uses the first 233 primes and needs at most 29 fractional bits per sum. If a scheduled prime divides $N$, its gcd already splits the input. All frequencies and precisions can be listed before any measurement. Both schedules work for unequal factor sizes. [Lean arithmetic](../PrimeFactors/PhaseResidues.lean) · [Checked finite schedules](../PrimeFactors/PhaseSchedules.lean) · [Salié formula](divisor-samples.md)

For $667$, the first four measurements recovered $23\cdot29$ with 2,464 terms, down from 12,936 in the earlier experiment. The direct evaluation still examines the units modulo $N$. Just building their table encounters the factors. The 2,048-bit figures describe the measurements needed by the decoder. No practical method of producing those readings on a general input is known here. [Product-only examples and capped control](../benchmarks/salie-residues.json) · [An independent asymptotic evaluator](counting-salie-phases.md)

## Why one reading per small prime suffices

Pick a nontrivial square root $h$ of one modulo $N$. There are exactly two, differing by sign. Completing either one gives a factor through $\gcd(h-1,N)$. At frequency $t$ the normalized sum satisfies

$$F(t)=2\cos(2\pi t/N)+2\cos(2\pi th/N).$$

Subtract the public cosine term and divide by two to measure the hidden cosine. Inverting it gives a *folded phase*, the distance of $th/N$ from the nearest integer, expressed in turns between 0 and $1/2$. Write $H=\min(h\bmod N,-h\bmod N)$ using least nonnegative residues. Either $3H\le N$ or $3(N-2H)\le N$. Thus for at least one $b\in\{1,2\}$, the centered representative $a$ of $bh$ has $|a|\le N/3$. Try both $b$ values with the same observations.

At an auxiliary prime $\ell$, choose $t=\ell^{-1}\bmod N$. If $s$ is the folded integer representative of $th$, then $b\ell s=kN\pm a$ for some integer $k$. The true phase is $x=s/N$. Suppose its approximation is within $1/(16\ell)$ turns. For the good branch, $b\ell\hat x$ is within $1/3+1/8<1/2$ of $k$, so rounding gives the correct integer. Squaring removes the unknown sign and gives $a^2\equiv(kN)^2\pmod\ell$.

Since $a^2\equiv b^2\pmod N$, write $a^2=b^2+Nw$. For the good branch $w\ge0$. Indeed $a$ cannot equal $\pm b$ since the root is nontrivial and $N$ is odd, while $b^2<N$ for the inputs in question. The measured residue gives

$$ w\equiv\big((kN)^2-b^2\big)N^{-1}\pmod\ell. $$

Combine these congruences by the Chinese remainder theorem. Stop when their product $M$ satisfies $9M>N$. The bound $a^2\le N^2/9$ gives $w<M$, so its least residue is its exact integer value. Test $Nw+b^2$ for a square, divide its root by $b$ modulo $N$, and verify the resulting split. The other branch can give an invalid candidate or another valid split. The explicit square and gcd tests handle both outcomes. [Rounding and quotient reconstruction](../PrimeFactors/PhaseResidues.lean)

The stated precision allows for the flat parts of the cosine. For $x,y\in[0,1/2]$,

$$|\cos(2\pi x)-\cos(2\pi y)|=2\sin(\pi(x+y))\sin(\pi|x-y|)\ge 8|x-y|^2.$$

Here both $x+y$ and $1-x-y$ are at least $|x-y|$, and $\sin(\pi u)\ge2u$ for $0\le u\le1/2$. Hidden cosine error $1/(64\ell^2)$ therefore suffices, with slack for numerical inversion. The schedule rounds $F(t)$ at $\lceil\log_2(128\ell^2)\rceil$ fractional bits. The public cosine and inversion can be evaluated with rational error bounds in polynomial time. For the full 2,048-bit range, the primorial through 1,471 meets the stopping rule and the preceding primorial falls short. The 233 precisions sum to 5,835 fractional bits. They count transmitted precision, excluding the sign, integer part, and the cost of evaluating each sum.

For $N=221$, only the doubled-root branch succeeded. It obtained $w=1$, giving $221+4=15^2$ and $15/2\equiv118\pmod{221}$. The gcd with 117 yields 13. At $N=667$ a cap of 1,848 terms permits three of four sums and leaves 667 unresolved. Run `python3 experiments/salie_residues.py --project-bits 2048` to reproduce the large schedule without evaluating a sum. [Bounded evaluator and schedule](../experiments/salie_residues.py) · [Checked fixtures](../benchmarks/salie-residues.json)

## How much precision buys one fewer reading?

The rounding argument works for any positive modulus $d$ coprime to $N$. At a budget of $B$ fractional bits, the rule $128d^2\le2^B$ allows $d\le D=\lfloor\sqrt{2^B/128}\rfloor$. Take distinct primes in descending order starting at $D$, until $9M>N$. For the entire 2,048-bit input range the resulting counts are as follows. The lower bounds come from $M\le D^k$ for $k$ readings. They apply to this rounding rule and reconstruction criterion.

| Fractional-bit budget | Largest allowed modulus | Fixed prime readings | Lower bound from $D^k$ |
|---:|---:|---:|---:|
| 29 | 2,048 | 200 | 186 |
| 39 | 65,536 | 128 | 128 |
| 47 | 1,048,576 | 103 | 103 |
| 53 | 8,388,608 | 89 | 89 |

At 53 bits, the 89 primes from 8,387,117 through 8,388,593 in the schedule yield 4,717 fractional bits altogether. Any 88 allowed moduli have product at most $2^{2024}$. The arithmetic and the numerical threshold for the feasible schedule are kernel-checked. The fraction-bit budgets here specify absolute rounding precision. An actual implementation must also allow for the integer part and numerical errors inside each sum. [Lean schedules](../PrimeFactors/PhaseSchedules.lean) · [Projection, including the selected moduli](../experiments/salie_residues.py)

At 29 bits the exact minimum is **197** if we can use composite moduli. Pairwise coprime moduli suffice even for an argument using least common multiples: assign each maximal prime power to one of its supplying moduli, and replace each modulus by the product of its assigned powers. The resulting entries are at most the originals and have product equal to the original least common multiple. At most 14 pairwise coprime composite entries can be at most 2,048, since each uses a distinct prime below 46. The product of any 196 entries is at most $2048^{14}$ times the product of the largest 182 primes at most 2,048. Nine times this upper bound is below $2^{2047}$.

For attainment take the largest 183 primes at most 2,048, down through 709, and add

$$2048,\;3\cdot677,\;5\cdot409,\;7\cdot283,\;11\cdot181,\;13\cdot157,\;17\cdot113,\;19\cdot107,\;23\cdot89,\;29\cdot67,\;31\cdot61,\;37\cdot53,\;41\cdot47,\;43^2.$$

These entries are pairwise coprime and $9M>2^{2048}$. As with the other schedules, test each gcd with $N$. If a composite entry shares a prime with $N$, this immediately gives a proper divisor on a 2,048-bit semiprime. [Reproducible integer comparisons](../experiments/salie_residues.py)

## A shorter adaptive schedule with lattice postprocessing

A paper variant uses at most **133 measurements** at 2,048 bits. First use one coarse sample at $t=1$ to locate $H/N$ within $1/32$. Choose $b=1$ if the estimate is at most $1/3$, and $b=2$ otherwise. Then the centered representative $a$ of $bh$ has $|a|<2N/5$ in either case. For a unit modulus $d$, the reading at $bd^{-1}\bmod N$, localized to within $1/(16d)$ turns, gives the unordered pair $\{a,-a\}\bmod d$ by the same rounding argument.

Take primes until their product $M\ge\sqrt N$. Begin with $d=\ell$ at each prime. The class modulo 2 and all zero residues are unchanged by a change of sign. At the first odd prime $r$ giving a nonzero class, choose either sign there. For every later prime, take $d=r\ell$. Exactly one of the two signs agrees with the chosen value modulo $r$. Thus the accumulated CRT result $c$ is the residue of one consistent signed root $\pm a\bmod M$. If there is no such $r$, all classes already agree with both signs. [Sign consistency](../PrimeFactors/PhaseResidues.lean)

There is an integer $u$ of size $O(\sqrt N)$ with $(c+Mu)^2\equiv b^2\pmod N$. Multiplying by $M^{-2}$ makes this a monic quadratic modulo the full $N$. The univariate small-root theorem recovers the candidates in polynomial time, covering the range by constantly many translates if needed. Try them and verify the root and gcd conditions. At 2,048 bits the first 132 primes through 743 suffice for $M$. With $d$ at most the product of the largest two, the same precision rule needs at most 46 fractional bits, plus the one coarse reading. This variant is a paper reduction. The fixtures run the 233-prime scheme with its elementary decoder. [May, Theorems 7–8](https://digital.ub.uni-paderborn.de/hsmig/download/pdf/3235#page=38)

A randomized variant uses **45 moderately precise readings** and at most three coarse readings in expectation. Choose $A$ uniformly in $1,\ldots,N-1$, taking its gcd first. For a unit, estimate the hidden cosine at $A$ with error at most $1/64$ and accept if its measured magnitude is at most $2/3$. The folded residue $Y$ of $Ah$ then has $Y/N\in[1/8,3/8]$. Every folded angle in $[1/6,1/3]$ passes. Multiplication by the unit $h$ permutes the residues, and the two reflected closed arcs contain at least $(N-1)/3$ nonzero residues for odd $N$, as is seen separately for $N\bmod6=1,3,5$. Thus each draw accepts an anchor or gives a proper gcd with probability at least $1/3$.

At frequency $Ad^{-1}$ let $x$ be the folded phase. Then $dx=k\pm Y/N$. With error at most $1/16$ in $d\hat x$, both the nearest integer $k$ and the sign of its residual are correct. Reducing the equation modulo $d$ now gives a consistently **signed** residue of $Y$ using that single observation. The largest 45 primes below $2^{23}$ have a product exceeding $2^{1024}$, enough for CRT and the monic quadratic with $Y^2\equiv A^2\pmod N$. Dividing a recovered root by $A$ and checking its gcd finishes the split. The largest 44 such primes have product below $2^{1012}$. The expected trial count concerns anchor selection. Each Salié sum and the lattice postprocessing still have to be computed.

## A deterministic fixed schedule at constant precision

We can also keep the error of every hidden cosine at $1/1000$, independent of input size, with all measurements fixed in advance. Each modulus now needs $O(\log\ell)$ readings to localize its folded phase. The local decoder uses polynomial work in $\ell$, which is itself $O(\log N)$ at the primorial cutoff by the prime number theorem. Summing $\log\ell$ gives $O(\log N)$ readings in total. The construction below gives an explicit polynomial-time way to choose them. Its large finite constants make the moderately precise scheme above a simpler experimental target.

For a given $\ell$ put $m=2\ell$ and $L=16m$. On the folded interval $[0,1/2]$ make a grid with step $1/(4096m)$. For each pair $x,y$ of grid points separated by at least $1/(8m)$, we need one integer $0\le j<L$ that distinguishes their cosines. To see that many work, take $j=|U-V|$ with $U,V$ independent uniform integers in $[0,L)$. The expected cosine at any real $z$ equals the nonnegative kernel

$$K(z)=\left|L^{-1}\sum_{u=0}^{L-1}e^{2\pi iuz}\right|^2.$$

If $\|z\|$ is the distance to the nearest integer, the geometric sum gives $K(z)\le(2L\|z\|)^{-2}$ away from zero. Both $\|x-y\|$ and $\|x+y\|$ are at least $1/(8m)$. For $D_j=\cos(2\pi jx)-\cos(2\pi jy)$, expanding the square gives

$$\mathbb E D_j^2=1+\tfrac12(K(2x)+K(2y))-K(x-y)-K(x+y)\ge7/8.$$

Because $|D_j|\le2$, at least a sixth of the ordered choices $(U,V)$ have $|D_j|\ge1/2$. Tabulate the grid cosines to absolute error at most $1/64$ using rational numbers. Mark pairs whose tabulated difference is at least $7/16$. At every step some $j$ marks at least a sixth of the remaining pairs, by averaging. Greedily choose the best such $j$. Starting with $O(\ell^2)$ pairs, $O(\log(2\ell))$ choices suffice. All decisions use a finite rational table depending only on $\ell$. [Lean separation and covering lemmas](../PrimeFactors/PhaseSeparation.lean)

For each chosen $j$, measure the hidden cosine at frequency $j\ell^{-1}\bmod N$. A nonunit frequency with proper gcd already splits $N$. The zero frequency contributes no information and can be supplied directly. The nearest grid point to the true folded phase differs from it by at most $1/(8192m)$. Its largest discrepancy from the observations is below $1/32$, including table error, observation error and the variation $2\pi L/(8192m)$. A best-fitting grid point also has discrepancy below $1/32$. The marking rule forces those two grid points to be less than $1/(8m)$ apart. Thus the estimated phase has error less than $1/(7m)=1/(14\ell)$. Multiplying by $b\ell$ gives error below $1/7$. The rounding argument applies because $1/3+1/7<1/2$.

The result is specific to extracting this single hidden cosine from a semiprime Salié sum. Sampling several rates and combining their remainders has a broader history in sparse Fourier recovery. The measured quantity, noise allowance and running time are part of each formulation. We do not assume historical priority for this decoding technique. [Li, Liang and Xia on robust CRT frequency estimation](https://www.eecis.udel.edu/~xxia/LiLiangXia.pdf) · [Li and Nakos on deterministic sparse Fourier recovery](https://doi.org/10.4230/LIPIcs.ICALP.2020.77)

Replacing a measurement by the readily available value of $N\bmod d$ loses information. On a specified family of balanced prime pairs with a fixed product residue, every locally possible quotient residue occurs asymptotically with its ordinary square frequency. The conditioning and asymptotic range matter for this conclusion. [Which local residues remain possible](local-root-residues.md)
