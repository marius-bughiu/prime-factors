# Lifting a signed gap across an interval

A guessed pair of coordinates $(s,v)$ can constrain a whole interval of offsets $j$. The earlier signed-gap method gives one affine residue modulo $4k^2$, where $k=sv$. A divisor $d$ of $k$ gives a new modulus $2k^2d^2$ using at most $d$ affine progressions. On odd traces, the known parity of the prime factors gives a further improvement. In particular, at $d=1$ the modulus increases from $4k^2$ to $16k^2$ with a single affine progression. A larger modulus gives fewer possible signed gaps for each trace. The count of surviving offsets also depends on where the residues fall within the search intervals. [Proofs](../PrimeFactors/OffsetGapLift.lean) · [Coordinate range](factoring-the-offset-multiplier.md)

## The next signed residue

Write $N=pq$, $T=\lfloor\sqrt N\rfloor$, and $S=j+2Tk$. For a successful primitive position, orient its coprime positive coordinates so that $A=ps^2$, $B=qv^2$, $k=sv$, $S=A+B$. Thus $AB=Nk^2$ and the desired signed gap is $z=A-B$. The theorem giving such coordinates assumes distinct prime factors. The congruence below holds for any integer factors and coordinates satisfying the displayed equations. [Coordinate witness](../PrimeFactors/OffsetSquareWitness.lean)

Fix $d\mid k$ and put $d_s=\gcd(d,s)$, $d_v=\gcd(d,v)$. Then $d=d_sd_v$. Choose $e\equiv1\pmod{(sd_s)^2}$ and $e\equiv0\pmod{(vd_v)^2}$, put $C=1-2e$, and let $U$ be an inverse of $S$ modulo $d^2$. Such an inverse exists at every primitive position because $\gcd(j,k)=1$. Then

$$
z\equiv C\big(S-2Nk^2U\big)\pmod{2k^2d^2}.
$$

Indeed, $A-Nk^2U=A(1-SU)+A^2U$ is divisible by $(sd_s)^2$. The corresponding expression for $B$ is divisible by $(vd_v)^2$. Subtract the two with coefficients $2e$ and $-2(1-e)$ to obtain the congruence. If $d$ is odd, combining it with the earlier parity residue $z_0$ gives a class modulo $4k^2d^2$. One representative is $(1-d^2)z_{\rm new}+d^2z_0$. This recovers the original class at $d=1$. [Theorems `signed_lift`, `chart_of_hit` and `combine_parity`](../PrimeFactors/OffsetGapLift.lean)

Along $S=S_0+di$ the inverse agrees with $U_0-diU_0^2$ modulo $d^2$. Substitution gives a fixed intercept and slope in the integer index $i$. An interval can therefore be tested by floor sums within each unit class modulo $d$. Choosing a small divisor trades the number of classes for the gain in precision. Selecting $d=s$ or $v$ uses a known divisor of $k$ even when its prime factorization is unavailable.

## Square residues of the factors

Suppose $p^2\equiv q^2\equiv1\pmod m$ and $U$ is an inverse of $S$ modulo $md^2$. Define $B_0=e s^4-(1-e)v^4$. The stronger residue is

$$
z\equiv C(S-2Nk^2U)+2B_0U\pmod{2mk^2d^2}.
$$

The proof uses $A-(Nk^2+s^4)U=A(1-SU)+s^4(p^2-1)U$ and its counterpart for $B$. At $d=1$ and $S^2\equiv1\pmod m$, take $U=S$. The signed residue is simply $[C(1-2Nk^2)+2B_0]S$.

- For odd factors and odd $S$, take $m=8$. In particular this covers every primitive offset at even $k$. Every odd integer squares to one modulo 8. The residue is affine modulo $16k^2$ throughout the chart.
- For primes $p,q\ge5$ and $\gcd(S,6)=1$, take $m=24$. Every unit modulo 24 squares to one. The same slope now applies modulo $48k^2$. On a chart with odd traces, subdividing by residue modulo 3 permits $m=24$ on the two unit trace classes and $m=8$ on the third. [Square residue modulo 24](../PrimeFactors/GapStride.lean) · [Signed lift](../PrimeFactors/OffsetGapLift.lean)

At arbitrary $d$, two initial inverses determine one affine progression on $S_0+Di$ whenever $md^2\mid2D^2$. For the modulus-8 enhancement choose $D=2d$, which gives at most $d$ classes among offsets of a fixed parity. For $m=24$, $D=6d$ suffices on unit trace classes. The exact integer interpolation proof uses the fact that $i(i-1)$ is even. [Theorem `inverse_secant`](../PrimeFactors/OffsetGapLift.lean)

## How much can one progression cover?

There is a restriction on this specific affine-counting strategy. At three consecutive unit traces $S,S+D,S+2D$, the second difference of their inverses modulo $M$ equals $2D^2/[S(S+D)(S+2D)]$. An affine inverse therefore requires $M\mid2D^2$. With the full second lift $M=k^2$ this forces $k\mid D$. It also constrains the signed residue if $\gcd(N,k)=1$, since the projector gives $C^2\equiv1\pmod{k^2}$ at $d=k$. Dividing a zero signed second difference by the common $2k^2$ then leaves an invertible coefficient $NC$. These statements assume three unit traces in the progression. Other ways of processing a nonlinear reciprocal across many offsets remain open. [Stride proof](../PrimeFactors/OffsetGapLift.lean)

At $N=117449=257\cdot457$, the unique winning position has $j=17$, $s=4$, $v=3$, $k=12$, $S=8225$ and $z=-1$. The $m=24$ predictions for $d=1,3,12$ are respectively $6911$ modulo $6912$, $62207$ modulo $62208$, and $995327$ modulo $995328$. Lean checks the full lifted residue and the unique successful slot. [Lifted residue](../PrimeFactors/OffsetGapLift.lean) · [Endpoint certificate](../PrimeFactors/CompleteOffsetExample.lean) An independent replay on all 1,265 products of two distinct same-width 5–9-bit primes checked every divisor at all 1,344 winning positions. The ordinary congruence passed 2,519 checks, the $m=8$ congruence passed 1,384 checks, and the $m=24$ congruence passed 1,188 checks on the traces invertible at the respective modulus. This replay checks necessary conditions at known winners. Finding those winners still requires selecting coordinates and excluding or testing the surviving offsets.

## Combining the two remainders

The product supplies two restrictions at the same coordinates. One comes from a divisor of $sv$. The other comes from the possible remainders of a prime modulo 24, including at traces divisible by 2 or 3. Intersect their finite progressions of possible indices $j$ first. Along any resulting progression, number its positions by $t$. If the two predicted signed gaps are $A+Bt$ modulo $M$ and $C+Dt$ modulo $m$, compatibility requires

$$
\gcd(M,m)\mid (C-A)+(D-B)t.
$$

This linear congruence leaves either no positions or one progression of $t$. On that progression, the Chinese remainder theorem combines the two predictions into a single affine signed-gap residue modulo $\operatorname{lcm}(M,m)$. It suffices to combine the initial value and the increment once each. The implementation uses the common trace residue and charges the inverses used in these intersections. Some trace residues admit an additional exclusion modulo 3 that this combined experiment leaves unused. [Compatibility and combination proofs](../PrimeFactors/OffsetUnitTrace.lean) · [Intersection implementation](../experiments/offset_class_intersection.py) · [Trace residues](nonunit-offset-traces.md)

For $502005281288939$ the earlier curved search examined 35,334 distinct positions. Combining the trace rule with a divisor of size at most eight reduced that count to **2,179** and gave the same factors, $17838631$ and $28141469$. A matched control used exactly the same 2,719 progressions and 38,893 bands, keeping the older gap modulus. It examined 11,383 positions. Of those, 10,631 passed the coprimality check, compared with 2,126 in the combined run. The trace rule on its own examined 5,303 positions and needed only 14,490 bands. Building and counting the bands takes work too. On all 1,265 products of two distinct same-width 5–9-bit primes, the combined search recovered precisely the 1,344 winning positions obtained independently from the factors. [Benchmark fixtures](../benchmarks/offset-gap-lifts.json) · [Separate controls and timings](signed-gap-lift-measurements.md)

For each 2,048-bit input, four coordinate pairs chosen from the product and three tested positions gave no factor. Across those four pairs, the combined rule left **more than $2^{492}$ positions** on the fresh input and **more than $2^{494}$** on the crossed input, before the coprimality check. The enclosures for the base-two logarithm of the counts, rounded outwards, were $[492.854,493.855]$ and $[494.120,495.121]$. With the older modulus on the same progressions the enclosures were $[499.936,500.937]$ and $[500.705,501.706]$. These are counts for the sampled pairs. A search for the factors must also find coordinates that contain a winning position. [Full-size fixtures and budgets](../benchmarks/offset-gap-lifts.json)

## Why 24 is the limit for this square identity

Could a larger fixed modulus work for every target because its factors are so large? Lean proves that $m$ divides both $p^2-1$ and $q^2-1$ for every pair of distinct 1,024-bit primes with a 2,048-bit product **if and only if $m$ divides 24**. Sufficiency follows because all such primes are coprime to 6. For necessity take $p=6308\cdot3^{638}+1$ and $q=3066\cdot5^{436}+1$. Lucas certificates establish primality, and direct integer arithmetic checks the widths and $\gcd(p^2-1,q^2-1)=24$. The pair was constructed to prove the limit. Its known factors provide no evidence for factor discovery. The theorem concerns a single modulus required to work on every input. Input-dependent congruences remain a possible source of additional information. [Target-size theorem and certificates](../PrimeFactors/TargetSquareModulus.lean)
