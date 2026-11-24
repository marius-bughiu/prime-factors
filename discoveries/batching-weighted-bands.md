# What can one shared power table cover?

Write $X=\sqrt N$. For positive integer weights $(a,b)$ and a putative smaller factor $x$, the weighted sum is
$$
 F_{a,b}(x)=ax+bN/x .
$$
At a true factor $x=p$ this is the integer $ap+bq$. Its congruence to $a+bN$ modulo $p-1$ gives a power collision that can be detected with batched gcds. A shared table of $m$ baby exponents and $G$ giant entries can cover every balanced factor profile in $O(N^{1/5})$ records. **The same exponent is necessary for any table required to cover the rounded sums of every integer candidate factor.** The lower bound allows arbitrary public weights and scattered exponent labels that depend on the entirety of $N$. [Existing collision and table proofs](../PrimeFactors/WeightedCollision.lean) · [Harvey, Algorithms 4.1–4.2](https://arxiv.org/pdf/2010.05450#page=9)

## The coverage requirement

Consider the integer interval $I_N=[3X/4,X]\cap\mathbb Z$, wholly inside the balanced range since $1\le N/x^2\le16/9<2$. A giant entry carries a positive pair $(a,b)$ and at most $m$ integer labels. The labels may even be chosen independently for each giant. Ordinary shared baby exponents plus a giant-specific offset are a special case. A candidate $x$ is covered when some giant at $(a,b)$ contains $\lfloor F_{a,b}(x)\rfloor$ among its labels. At genuine divisors the floor has no effect. One can generate all labels, weights and offsets from $N$.

For $m,G\ge1$, the number covered anywhere in $[1,X]\cap\mathbb Z$ is at most
$$
 3mG + 4\sqrt{5XmG^{3/2}}. \tag{1}
$$
Each label stands for a full unit interval of the relaxed trace. Giant entries and baby exponents need not be consecutive. Reusing the same weights in many entries, varying the number of labels per giant, and placing labels far above the minimum of the trace are all allowed.

Since $|I_N|\ge X/4-1$, complete coverage forces $m+G=\Omega(X^{2/5})=\Omega(N^{1/5})$. For instance, if $X\ge16$ and $m+G\le X^{2/5}/64$, the first term in (1) is at most $3X/4096$ and the second is at most $4\sqrt5\,X/64^{5/4}$. Their sum is less than $X/4-1$. Thus full coverage of this subinterval of a 2,048-bit input already requires more than $2^{403}$ nominal table records. Requiring coverage only of the prime $x$ in $I_N$ still gives $\Omega(N^{1/5}/(\log N)^{4/5})$, by the prime number theorem in a fixed proportional interval. The prime-candidate condition still includes primes that do not divide $N$.

## Proof of the capacity bound

Group the giant entries by weight. Let $L_w$ denote the number of distinct labels at weight $w=(a,b)$. Discard empty groups, so there are at most $G$ groups and $\sum_w L_w\le mG$. Set $r=\sqrt{bN/a}$. The trace decreases up to $r$ and increases thereafter.

For $0<x\le y\le X$ with $r\le x$, the exact difference satisfies
$$
 y(F(y)-F(x))-a(y-x)(y-r)=a(y-x)r(x-r)/x\ge0 .
$$
For $y\le r$, the corresponding identity is
$$
 x(F(x)-F(y))-a(y-x)(r-x)=a(y-x)r(r-y)/y\ge0 .
$$
Fix $D>0$. At most $2D+1$ integers lie within distance $D$ of $r$. On each remaining branch, two integer candidates with the same rounded label have trace difference less than one, and the identities imply $y-x\le X/(aD)$. Each label therefore covers at most $1+X/(aD)$ integers on that branch. Taking $D=\sqrt{XL_w/a}$ bounds a whole group's coverage by
$$
 1+2L_w+4\sqrt{XL_w/a}.
$$
This argument handles separated labels inside one group without enlarging them to their convex hull. [Lean single-slope estimate](../PrimeFactors/WeightedBands.lean)

If $b>a$, then for $x<y\le X$ the identity $F(x)-F(y)=(y-x)(bN/(xy)-a)$ gives $F(x)-F(y)\ge y-x$. Thus each label at such a slope covers at most one integer. For the remaining slopes it suffices to bound the reciprocal weight mass. At most $2a$ distinct positive $b\le2a$ can accompany each $a$. For any integer $B\ge1$, the terms with $a\le B$ therefore contribute at most $2B$ to $\sum_w1/a$, while all larger terms contribute at most $G/B$. Taking $B=\lceil\sqrt G\rceil$ bounds this sum by $5\sqrt G$. Cauchy–Schwarz now bounds the total square-root term by
$$
 4\sqrt{X\sum_w L_w \sum_w 1/a}\ \le\ 4\sqrt{5XmG^{3/2}}.
$$
The other terms, including the groups with $b>a$, total at most $G+2mG\le3mG$. Taking the union gives (1). Lean proves the arbitrary-label single-group bound, the reciprocal-mass inequality with arbitrary cutoff $B$, the Cauchy–Schwarz portfolio estimate, and injectivity for the outlying slopes. [Finite proofs and sparse example](../PrimeFactors/WeightedBands.lean)

## Matching exponent and scope

For an upper bound, apply Dirichlet approximation to the ratio $N/x^2\in[1,2]$. Some integers $1\le b\le K$, $b\le a\le2b$ satisfy $|a-bN/x^2|\le1/(K+1)$. Then
$$
 0\le F_{a,b}(x)-2\sqrt{abN}
 =\frac{(ax-bN/x)^2}{F_{a,b}(x)+2\sqrt{abN}}
 \ll \frac{X}{bK^2}.
$$
For this rounded cover start with $\lfloor2\sqrt{abN}\rfloor$ and cover the resulting integer interval in successive groups of $m$ labels. There are $O(K^2+X/(mK))$ groups across all slopes. Taking $K\asymp X^{1/5}$ and $m\asymp X^{2/5}$ attains the exponent in (1). The earlier repository bound applied to this particular complete slope list and its prescribed intervals. The lower bound in (1) also applies when the weights and the individual label sets are optimized. [Dirichlet windows](searching-the-balanced-interval.md)

For a finite distinction, take $N=15049$ and the four baby exponents $\{0,3,7,10\}$. Give each of $(1,1),(3,2),(2,1),(4,3)$ one giant with offset $\lceil2\sqrt{abN}\rceil$. These eight records cover 24 of the 30 integers in $I_N=[93,122]$. They include $101$ because $3\cdot101+2\cdot149=601$ is the offset at $(3,2)$. The six uncovered candidates are $94,115,118,119,120,122$. Exact integer division computes every rounded label in this example. [Lean-checked count](../PrimeFactors/WeightedBands.lean)

The obstruction measures table entries needed to justify coverage on the relaxed interval. It gives no lower bound for identifying the single genuine factor, incidental group-order collisions, implicit polynomial evaluations, or portfolios restricted using additional divisor information. Harvey and Hittmeir exploit residue classes of the actual factor in a coefficient lattice. Stănică’s 2026 preprint shows that an extra digit of the actual baby index is a quadratic image modulo selected primes and prunes the baby table by a subpower factor. An arbitrary integer $x$ and its rational partner $N/x$ need not obey those conditions. Distinguishing genuine divisor candidates before building the table is precisely where smaller searches can occur. [Harvey–Hittmeir, Proposition 3.3](https://arxiv.org/abs/2105.11105) · [Stănică, §3](https://arxiv.org/html/2611.06580v1#S3)

The balanced first-vector search uses divisor information of exactly this kind. It allows a small number of failed local restrictions, then searches normalized weights separately when the two coefficients have a large common divisor with the primorial. [Bound, derivation and computational checks](short-basis-sieve.md)
