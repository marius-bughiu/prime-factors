# Counting tangent intervals over all factor coordinates

**For every product of two distinct 1,024-bit primes, fewer than $2^{692}$ line or singleton tests suffice to reach a prime factor.** The product specifies the search. Lean proves that one of its publicly described intervals contains the factor-revealing position. Finding that interval cheaply remains open. On each of the two 2,048-bit controls, exhausting this coordinate loop already entails at least $2^{503}$ coordinate visits. Both inputs were constructed from known primes so a discovery can be checked. The search takes only the product, and we have not exhausted either full-size schedule. [Target theorem](../PrimeFactors/TargetArcSchedule.lean) · [Measured inputs and checked coordinate floor](../PrimeFactors/OffsetCoordinateFloor.lean)

The earlier result priced four sampled coordinate pairs using a fixed partition and more than $2^{252}$ projected lines. Here the partition follows the changing curvature and the count includes every eligible coordinate pair. The two counts answer different questions. [Previous scope and orientation bound](lines-on-a-factor-arc.md)

## Making the estimate from the input

Suppose $N=pq$ with distinct 1,024-bit primes and $2^{2047}\le N<2^{2048}$. Put $T=\lfloor\sqrt N\rfloor$, $h=N-T^2$, $J=\lfloor\sqrt{4h/3}\rfloor$ and $K=\lfloor TJ/h\rfloor+1$. The complete square search contains a winner with $1\le j\le J$, $k=sv\le K$, and coprime $1\le v\le s$. The known lower bound $L$ on $p$ gives $L(s-1)<Tv$. Since $T\le 2L$, we can use $s\le2v$. The count below even allows $s\le2v+1$. [Complete square tests](complete-offset-search.md) · [Coordinate proof](../PrimeFactors/OffsetWinnerWindow.lean)

For both controls, Lean checks $T<2h$ and $4h<3(2^{512})^2$ directly against the public product. Thus $J<2^{512}$ and $K<2^{513}$. In particular $v<2^{257}$. A second finite bound covers inputs or searches with $2^{1022}\le T\le2^{1024}$, $N\le2^{2048}$, $J<2^{515}$ and $K<2^{515}$ under the displayed coordinate and trace conditions. It gives fewer than $2^{695}$ equations. For an arbitrary unshifted product the formula for $K$ can be much larger when $h$ is small, so the general statement retains its parameter conditions. [Parameter checks, coordinate box and two grid bounds](../PrimeFactors/OffsetGlobalArcs.lean)

## One line per short interval

Fix $(s,v)$, let $k=sv$ and $P=4Nk^2$. Use the ordinary parity progression of trace step 2, with signed-gap modulus $M=4k^2$. Start at the first allowed trace $A=2Tk+j_0$ whose square is at least $P$. Every later trace is $S=A+2i$ for $i\ge0$. Test index zero directly if it is in range. For positive indices use two dyadic partitions

$$
2^a\le v<2^{a+1},\qquad 2^b\le i<2^{b+1}.
$$

Throughout these bins, $k\ge v^2\ge2^{2a}$. The public floor height $u=\lfloor\sqrt{S^2-P}\rfloor$ satisfies

$$
u\ge 2^{511+a+\lfloor b/2\rfloor}.
$$

Indeed $S^2-P\ge A i\ge T k i$. The exponent on the right follows from $T\ge2^{1022}$. Also $u\le S\le2^{1026}k$, whence $P+2u\le2^{2051}k^2$. These loose powers hold throughout the bin and keep the count independent of unobserved factor gaps. [Integer height and curvature bounds](../PrimeFactors/OffsetGlobalArcs.lean)

Set the number of positions per chunk to $2^w$, where

$$
w=\min\big\{b,\max(0,4a-1),\max(0,a+\lfloor b/2\rfloor-174)\big\}.
$$

A full chunk has index width $W=2^w-1$. Clip the last one to the public end of the trace range. If $w=0$, the chunk is a single index. Otherwise $2W\le k^2$ and $2^{685}W\le u$. Together these imply $8W\le M$ and $4(P+2u)2^2W^3\le Mu^3$. The rounded tangent then encloses each signed branch in a strip of normalized area at most $1/4$. A continued fraction gives one public line containing every possible point on that branch. Intersecting it with the conic requires at most one square root and two candidate indices. [Composed theorem `chunk_line`](../PrimeFactors/OffsetGlobalArcs.lean) · [Rounded tangent proof](../PrimeFactors/OffsetTangentCover.lean) · [Public line proof](../PrimeFactors/OffsetArcLines.lean)

## Counting the complete schedule

For a fixed $a$, allow $2^a$ possible $v$ and all $s<2^{a+2}$. This rectangular cover gives $2^{2a+2}$ coordinate pairs, including choices outside the actual search. For each such pair there are at most $2^{b-w}$ chunks in epoch $b$. If $n_a,n_b$ bound the numbers of coordinate and index bins, the total number of signed equations, including both signs at index zero, is at most

$$
2\sum_{a=0}^{n_a-1} 2^{2a+2}
   \left(1+\sum_{b=0}^{n_b-1} 2^{b-w(a,b)}\right).
$$

For $a\le257$ and $b\le514$ each exponent $2a+2+b-w$ is at most $\max(516,176+a+\lceil b/2\rceil)$. Summing the two geometric series gives the following bounds. Integer operations to build a line, test it and check divisibility also cost time. For each fixed chart this work is polynomial in the bit length per interval. The analytic bound permits far more intervals than a modern PC could test in an hour. [Partition, finite sum and kernel checks](../PrimeFactors/OffsetGlobalArcs.lean)

| Public coordinate and index bounds | Bins $(n_a,n_b)$ | Complete upper bound |
| --- | ---: | ---: |
| Both 2,048-bit controls, ordinary charts | $(257,512)$ | $<2^{692}$ |
| Wider parameter range above | $(258,515)$ | $<2^{695}$ |
| All products of distinct 1,024-bit primes, shifted charts below | $(256,513)$ | $<2^{692}$ |

The numerical sum can be evaluated without visiting a coordinate or testing a square.

```python
def upper_bound(v_bins, index_bins):
    count = 0
    for a in range(v_bins):
        pairs = 1 << (2*a + 2)
        chunks = 1
        for b in range(index_bins):
            w = min(b, max(0, 4*a-1), max(0, a+b//2-174))
            chunks += 1 << (b-w)
        count += 2*pairs*chunks
    return count

assert upper_bound(257, 512).bit_length() == 692
assert upper_bound(258, 515).bit_length() == 695
assert upper_bound(256, 513).bit_length() == 692
```

## Moving the starting square on every target

Let $R=\lfloor\sqrt N\rfloor$. Choose $T=R-1$ and write $H=N-T^2$. Every nonsquare gives $2T+2\le H\le4T+3$, including numbers only one or two above $R^2$. For distinct primes $17\le p<q\le2p$, the positive quadratic form
$$
p s^2-2Tsv+qv^2
$$
has determinant $H$. Its minimum supplies a positive, primitive pair with $v\le s\le2v$ and a positive value $j$ satisfying $3j^2\le4H$. The square test at $k=sv$ recovers a factor. Interchanging the coordinates of a minimum proves the order, since the smaller prime multiplies the larger squared coordinate. For $T<2^{1024}$ the shifted schedule has $J<3\cdot2^{512}$ and $K<2^{512}$. Thus $v<2^{256}$ and the index $i=(j-j_0)/2$ is below $2^{513}$. [Shifted existence theorem and size bounds](../PrimeFactors/ShiftedOffsetBase.lean)

The target theorem combines the exact size of a finite set of addresses with the existence of a winning address. The address records a coordinate pair and a short interval, starting at the first offset of the required parity with nonnegative discriminant. Its first offset is computed by a square root and parity correction. At the winning position, one of the two public signed residue progressions contains the integer gap. A singleton check or one line on that progression includes the factor. All address ranges depend only on public quantities. On the unlifted parity progression with step 2 and modulus $4k^2$, the implementation can choose wider chunks whenever the same two integer inequalities permit them. Within each dyadic block this takes no more chunks than the power-of-two count above. [Address cardinality, first offset, and factor witness](../PrimeFactors/TargetArcSchedule.lean)

For example, $25{,}283=159^2+2$. At $T=158$ the remainder is $319$, and the caps are $J=20$, $K=10$. In the coordinate pair $(1,1)$ the weighted sum is $324=2\cdot158+8$. The square test gives gap $62$ and hence $131\times193$. Across all 1,265 products of two distinct same-width 5–9-bit primes the shifted search recovered all 1,298 winning positions in its range. The original and shifted bases define different positions. [Worked regression](../tests/test_offset_arc_lines.py) · [Implemented shifted search](../experiments/offset_tangent_cover.py)

A separate 59-bit input was selected independently of the factor search. For each of the ASCII suffixes `p` and `q`, hash `prime-factors/shifted-arc-holdout/v1/` followed by the suffix with SHA-256. Interpret the digest as a big-endian integer, reduce modulo $2^{29}$, add $2^{29}$, and round up to the first odd prime at least that large. This produced $556587319$ and $584628763$. The search received their product, $325396955808456397$, and exhausted 92,583 arcs across 364 coordinate pairs. The sole winning position was $(j,k)=(17799,1640)$. Lean checked the primes and their product. The benchmark uses the decimal factor strings only to validate the result. [59-bit certificate and benchmark](https://marius-bughiu.github.io/prime-factors/#offset-tangent-cover-shifted-holdout-59)

There is also a lower bound on the actual cost of exhausting this particular loop on each of the two full-size controls. For the public factor lower bound $L$ and shifted cap $K$, Lean checks $9L\le8T$ and $156\cdot2^{504}\le K$. Put $U=2^{252}$. For coprime $1\le x\le b\le U$ and $m=8,9,10,11$, take $(s,v)=((m+1)b+x,mb+x)$. Each pair is coprime, satisfies the public coordinate limits, and determines the original data through $b=s-v$ and $m=\lfloor(v-1)/b\rfloor$. Counting these disjoint pairs gives **at least $2^{503}$ coordinate visits** on each full-size control before charging the arc work. A run that stops upon finding a factor can terminate earlier. This lower bound is specific to enumerating this set of coordinates. [Two kernel-checked coordinate counts](../PrimeFactors/OffsetCoordinateFloor.lean)

The finite bounds here count equations, with additional work for selecting directions and checking roots. For comparison, Harvey and Hittmeir give a general deterministic algorithm with asymptotic bit complexity $O(N^{1/5}\log^{16/5}N/(\log\log N)^{3/5})$. The geometric argument explains how to reduce the work inside this particular factor search. [Harvey and Hittmeir](https://arxiv.org/abs/2105.11105)
