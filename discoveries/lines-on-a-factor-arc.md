# Covering a factor arc with public lines

On the fresh 2,048-bit control, a filter left more than $2^{492}$ offset positions in just four sampled coordinate pairs. The same search region can be checked with fewer than $2^{253}$ quadratic equations. Each equation tests an entire line for an intersection with the factor curve. The crossed control also needs fewer than $2^{253}$ equations on its four sampled coordinates. Both counts are still enormous, and the four sampled pairs need not include the winning coordinates. The search bounds, line directions and equations use only the product. [Earlier filter and inputs](lifting-a-signed-gap.md) · [Proofs](../PrimeFactors/OffsetArcLines.lean)

## Choosing a line before finding any points

Let $N$ be the product, $s,v$ a pair of positive coprime coordinates, $k=sv$ and $P=4Nk^2$. Within a single progression of candidate traces write $S=S_0+\Delta i$, $0\le i\le W$. A winning trace has signed gap $z$ with $z^2=S^2-P$. The product and coordinates give an affine residue $z\equiv r+\beta i\pmod M$. Run the following argument for each sign $\sigma\in\{-1,1\}$, using $w=|z|=\sigma(r+\beta i)+My$ for some integer $y$. The earlier construction bounds $w$ between lines with the same slope. In integers the band is $L\le bw-a\Delta i\le U$, with $b>0$. [Chord and integer bounds](counting-signed-factor-gaps.md) · [Signed residues](nonunit-offset-traces.md)

Write $D=bM$, $A=a\Delta-b\sigma\beta$, $l=L-b\sigma r$ and $u=U-b\sigma r$. Every possible point now lies in $l\le Dy-Ai\le u$. For a rational direction $p/q$ with $q>0$, set $E=qA-pD$. The integer line label $t=qy-pi$ satisfies

$$
\left\lceil\frac{ql+\min(0,EW)}{D}\right\rceil
\le t\le
\left\lfloor\frac{qu+\max(0,EW)}{D}\right\rfloor.
$$

Indeed $Dt=q(Dy-Ai)+Ei$. Both endpoints above are computed without a point on the arc. If $W>0$, $u\ge l$ and $4W(u-l)\le D$, one public line contains every candidate. Choose a continued-fraction convergent with $1\le q\le2W$ and $|E|\le D/(2W+1)$. Then $q(u-l)+W|E|<D$, and the upper endpoint identifies the only possible integer level, including as a harmless guess when the interval is empty. A zero-width index window already fixes $i$. [Theorems `level_bounds` and `public_line`](../PrimeFactors/OffsetArcLines.lean) · [Euclidean stopping bound](../PrimeFactors/RootIntervalSlope.lean)

For a thicker strip put $H=u-l$. When $0<H\le WD$, set $Q=\lfloor\sqrt{WD/H}\rfloor$ and take the last convergent to $A/D$ with denominator at most $Q$. Its residual has $|E|\le D/(Q+1)$. Both $qH$ and $W|E|$ are at most $\sqrt{WDH}$. There are therefore at most $1+2\sqrt{WH/D}$ integer levels. The quantity $WH/D$ is the Euclidean area in the integer $(i,y)$ coordinates. This makes a list of lines proportional to the square root of the area sufficient even when one line does not suffice. If $H=0$, the exact direction has $E=0$. If $H>WD$, the $W+1$ vertical lines fixing the index are cheaper under this bound. [Squared projection-width bound](../PrimeFactors/OffsetArcLines.lean)

## Checking each line

For fixed $t$, put $F=\sigma rq+Mt$ and $G=\sigma\beta q+Mp$. On the line, $qw=F+Gi$. The intersection equation has coefficients

$$
(G^2-q^2\Delta^2)i^2+2(FG-q^2 S_0\Delta)i+F^2-q^2(S_0^2-P)=0.
$$

For $q\Delta P\ne0$ the polynomial cannot vanish identically. Each line contributes at most two possible indices. One way to solve it forms $X=G S_0-\Delta F$, $V=G^2-q^2\Delta^2$ and checks whether $X^2-PV$ is a nonnegative square. At a solution its signed root is $Y=Gw-q\Delta S$. For $V\ne0$ the exact division $S=(GX+q\Delta Y)/V$ recovers the trace. For $V=0$ the displayed polynomial is linear or a nonzero constant. One integer square root per line suffices, with exact divisibility, bounds, signed residue and product checks on the results. [Quadratic, nondegeneracy and discriminant identities](../PrimeFactors/OffsetArcLines.lean)

## How much can changing the line direction save?

The length of the real projection interval for a given direction is $(qH+W|E|)/D$. It contains at least the floor of that length in integer levels, regardless of its offset. A primitive reference convergent $p_0/q_0$ with residual $E_0=q_0 A-p_0 D$ supplies a lower bound for **every direction within this fixed strip**. Put

$$
m=\left\lfloor\min\!\left\{\frac{W}{q_0},\frac{H}{|E_0|},
\frac{q_0H+W|E_0|}{D}\right\}\right\rfloor,
$$

omitting the middle term when $E_0=0$. For a nonparallel direction, $|q_0E-qE_0|$ is a positive multiple of $D$. The triangle inequality gives $mD\le W|E|+qH$. A parallel direction with integer coefficients has at least the reference width, since the reference is primitive. Vertical lines require $W+1\ge m$ levels. This certificate prices enumeration of every level between the two extreme projections. Subdividing the bands, directly testing points, sharing work between bands, or finding arithmetic relations among levels changes that cost. [Theorems `all_widths` and `consecutive_levels`](../PrimeFactors/OffsetArcLines.lean)

## Measured on the established coordinate schedules

The product-only calculation used the same lifted progressions and chord partition as the combined cap-8 filter. It counted levels for each sign separately; both signs can yield the same position. On each full-size input we counted the entire list for four coordinate pairs using integer arithmetic and performed no exhaustive search through the list. The bounds below round the lower exponent down and the upper exponent up. Each bound concerns the sum over all signed bands of this particular schedule. [Frozen coordinates, budgets and previous counts](../benchmarks/offset-gap-lifts.json)

| Input | Nonempty real bands, counting signs | Lower bound, all projected directions | Projected levels for the chosen directions |
| --- | ---: | ---: | ---: |
| Fresh 2,048-bit | 3,072 | $>2^{252.415}$ | $<2^{252.491}$ |
| Crossed 2,048-bit | 4,096 | $>2^{252.837}$ | $<2^{252.901}$ |

For the complete 49-bit test, 7,045 projected levels contained the sole winning slot $(2921,2322)$, recovering $17838631\cdot28141469$. The established direct route examined only 2,179 positions on that input. Choosing between lines and direct point tests separately for each band reduced the 49-bit schedule to 1,664 checks. On $117449$ five projected levels recovered $257\cdot457$. These line counts come from using projected directions on every band, with the denominator cap above and at least one allowed denominator. Different choices for a singleton index or for switching to vertical lines or point tests can change the work count. [Previously checked factors](../benchmarks/offset-gap-lifts.json)

For example, the winning 49-bit band at $(s,v)=(54,43)$ contains 40 offsets with $S=104051024105+6i$, $0\le i\le39$. Its negative-gap branch projects to the single level $770y-211i=548$. Intersecting with the factor curve gives $(i-12)(276959i-7146558)=0$, up to a nonzero constant. Only $i=12$ is integral. It yields signed gap $-16128185$ and trace $104051024177$. [Checked public band and integer root](../PrimeFactors/OffsetArcLines.lean) · [Reproducible scanner](../experiments/offset_arc_lines.py)

```sh
python3 -m experiments.offset_arc_lines 502005281288939 --all-vectors --max-vectors 1000 --max-tests 10000 --lines-only
```

Short arcs, determinant tests for collinearity, and recovery by auxiliary equations are established techniques. Hiary uses continued fractions and quadratics for short divisor intervals. Bombieri and Pila study integral points on convex arcs, and Elkies uses lattice reduction for rational points near curves. The earlier repository approach recovers a line in divisor coordinates using counts and moments of lattice points. Here the public signed-gap congruence specifies the lattice, a convergent gives a normal direction, and an integer interval gives the possible lines before finding points. All claims here use finite integer inequalities. [Hiary](https://arxiv.org/abs/1408.2608) · [Bombieri and Pila](https://people.maths.ox.ac.uk/pila/Ovals.pdf) · [Elkies](https://arxiv.org/abs/math/0005139) · [Divisor intervals and moment fitting](quotient-search.md)
