# Midpoints that survive every power of the small primes

Suppose someone gives us just a 2,048-bit product of two 1,024-bit primes. We proved that **more than $2^{874}$ wrong guesses for the midpoint of the factors pass every square test at every power of every prime through 733**. Even an unlimited number of digits at these 130 primes leaves those guesses. This limits how much these particular tests can tell us. A search can still use other information to skip many of the survivors together. [Lean proofs and exact integer bounds](../PrimeFactors/PersistentLocalSurvivors.lean)

For $N=pq$, let $h=(p+q)/2$. Its defining property is $h^2-N=((q-p)/2)^2$. The balanced interval from $\lceil\sqrt N\rceil$ through $\lfloor\sqrt{9N/8}\rfloor$ contains the true midpoint because $p\le q\le2p$. The only other unordered positive factor pair of this semiprime is $1\cdot N$, whose midpoint exceeds the upper end. Thus at most one guess in this interval gives a genuine integer square. Each proposed midpoint can be tested by checking whether $h^2-N$ has a square root modulo a chosen prime power. These are the midpoint versions of the modular coordinate-sum tests. [Exact factor-pair characterization](../PrimeFactors/Isolation.lean) · [Bower, Evans, Luo and Miller](https://arxiv.org/abs/1212.2930)

## Classes that higher powers cannot remove

For each odd prime $s\ge5$ in the test, $N$ is a unit. Nonzero squares modulo $s$ lift to every positive power. Counting possible midpoints amounts to pairing each unit $x$ with $N/x$ and retaining $(x+N/x)/2$. When $N$ is a square modulo $s$, the two fixed points have $h^2-N=0$ and the remaining units give $(s-3)/2$ distinct midpoints with nonzero square discriminant. When $N$ is a nonsquare, the involution has no fixed point and gives $(s-1)/2$ such midpoints. Every integer in one of these classes passes at all precisions. [First-digit counts](../PrimeFactors/ResidueCount.lean) · [Prime-power lifting](../PrimeFactors/PrimePower.lean)

Write $d=h^2-N$. At two, retain a midpoint if $d\equiv1\pmod8$, $d\equiv4\pmod{32}$, or $d\equiv16\pmod{128}$. Each condition says that $d$ is a square factor times a unit $1\bmod8$. Such a unit $1+8t$ is a square at every dyadic precision. Indeed $z\mapsto z+2z^2$ permutes the residues modulo $2^e$ because its difference on two arguments is their difference times an odd unit. Taking $z+2z^2=t$ gives $(1+4z)^2=1+8t$. Testing all 64 odd residues for $N\bmod128$ gives at least **four** retained classes for $h\bmod128$. At three, retain $d\equiv1\pmod3$ or $d\equiv9\pmod{27}$. The second condition leaves a unit $1\bmod3$ after removing $3^2$. Testing all 18 unit residues for $N\bmod27$ gives at least **two** retained classes for $h\bmod27$. The finite counts and the lifting proofs are kernel-checked. [Small-prime counts](../PrimeFactors/PersistentLocalSurvivors.lean)

## Counting inside the actual interval

With a cutoff $C$, take
$$
M=128\cdot27\prod_{5\le s\le C,\;s\ {\rm prime}}s,\qquad
R=4\cdot2\prod_{5\le s\le C,\;s\ {\rm prime}}\frac{s-3}{2}.
$$
CRT gives at least $R$ persistent classes in every complete period of $M$ consecutive integers. The modulus of a higher prime power does not enter this period because every lift of a retained class passes. [CRT counting and lifting proofs](../PrimeFactors/PersistentLocalSurvivors.lean)

Set $W=2^{1019}$ and $r=\lfloor\sqrt N\rfloor$. Every integer from $r+1$ through $r+W$ lies in the balanced interval. Indeed $(18W)^2\le 2^{2047}\le N$ gives $18W\le r$, hence $8(r+W)^2\le9r^2\le9N$. The count of wrong guesses is therefore at least $\lfloor W/M\rfloor R-1$. Here are the two cutoffs checked using exact integer arithmetic. [Interval proof and numerical inequalities](../PrimeFactors/PersistentLocalSurvivors.lean)

| Primes tested | Number of primes | Period in bits | Lower bound on wrong midpoints |
|---|---:|---:|---:|
| All through 700 | 125 | 971 | More than $2^{880}$ |
| All through 733 | 130 | 1,019 | More than $2^{874}$ |

The larger cutoff fits one complete period in the stated subinterval. Including 739 would make this period 1,028 bits long. The same counting step would then give zero as its lower bound, leaving the actual number of survivors undetermined. [Earlier counts for individual prime powers](prime-power-counts.md)
