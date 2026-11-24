# How often does minimizing a weighted sum find the factors?

Suppose two unknown primes lie between $X$ and $2X$, and their product $N$ is public. Draw all positive integer pairs $(x,y)$ with $xy\ge N$. For a chosen slope $s>0$, find the smallest value of $sx+y$ on that grid. Sometimes a minimizing pair multiplies to exactly $N$. For $N=143$ and $s=13/9$, the smallest integer cost $13x+9y$ is 260. Its discriminant $260^2-4\cdot13\cdot9\cdot143=26^2$ gives the pair $(11,13)$. The first integer above the continuous minimum is 259, so simply checking that first level would miss this example.

How much would a perfect minimizer help? Grant it for free, and credit a hit whenever the smaller prime and the larger prime, in that order, are *among* the minimizers, including ties. Among uniform pairs of distinct 1,024-bit primes conditioned on a 2,048-bit product, **any fixed list of $2^{40}$ slopes hits fewer than one pair in $2^{460}$**. If the list can be chosen by reading 1,025 bits from the ends of the product, with at most 502 from the low end, the bound is one in $2^{448}$. A method that learns how to select slopes from the full product or uses additional information in near misses has a different success criterion. [Lean arithmetic](../PrimeFactors/SupportingSlope.lean)

## What a supporting slope tells us

A factor pair $(p,q)$ is always a uniquely exposed point at $s=q/p$. Indeed $qx+py\ge2\sqrt{pqxy}\ge2pq$, with equality forcing $x=p,y=q$. This choice of direction uses the unknown ratio. At a supplied positive rational $s=a/b$, with $a,b$ integers, a minimizing integer cost $t=ax+by$ gives at most two candidates for the first factor via the square test $t^2-4abN=(ap-bq)^2$. The published integer-hull algorithm can enumerate vertices logarithmically many arithmetic operations per vertex. The complete hull has order $N^{1/3}\log N$ vertices. Those results count an entire list. Here we ask how much of a balanced *input population* any chosen collection of directions can cover. [Alcántara, Blanco, Criado and Santos](https://arxiv.org/abs/2501.19193) · [Balog and Bárány](https://arxiv.org/abs/2602.06897)

Suppose $sx+y$ attains its grid minimum at $(p,q)$. For a rational $a/b<s$, the point $(p-b,q+a)$ would have strictly smaller cost. If its coordinates are positive, its product must be less than $pq$. Similarly use $(p+d,q-c)$ for $s<c/d$. The resulting strict inequalities give

$$
\frac ab-\frac ap < \frac qp < \frac cd+\frac cp.
$$

Each side needs just its own strict slope inequality. In particular we may take the nearest fractions *strictly* to the left and right of $s$, even if $s$ itself is a simple fraction. [Checked displacement inequalities](../PrimeFactors/SupportingSlope.lean)

## Bounding a list of arbitrary real slopes

Write $X\le p<q<2X$. Partition $[1,2]$ using all reduced fractions with denominators at most $K$, where $2K<X$. Consecutive fractions $a/b,c/d$ have $bc-ad=1$ and $b+d>K$. Thus a cell has width $1/(bd)$, at most $2/(K\min(b,d))$. At a fixed slope strictly inside a cell, the two displacements place $q/p$ in that cell expanded by $2K/X$ at each end. At a cell boundary take both incident cells, so the competitors still have strictly lower cost. At 1 or 2 only the interior neighbor is needed because $q/p\in[1,2]$. For $s<1$ use the upper neighbor of 1, and for $s>2$ use the lower neighbor of 2. [Farey neighbor identities, Lecture 16](https://mathweb.tifr.res.in/Documents/Publications/Lectures/tifr02.pdf)

A list of $T$ slopes uses $J\le2T$ distinct cells. Assign each cell to the endpoint with smaller denominator $b$, breaking ties arbitrarily. There are at most $2b$ reduced fractions with that denominator in $[1,2]$, each incident to at most two cells. Summing widths assigned to denominators $b\le D$ costs at most $8D/K$. Each remaining width costs at most $2/(KD)$. After enlarging and clipping to $[1,2]$, the intervals have total length at most

$$
 L=\frac{8D}{K}+\frac{4T}{KD}+\frac{8TK}{X}.
$$

For any fixed $p$, their dilates contain at most $2XL+J$ integers $q$. Choosing $D\asymp\sqrt T$ and $K\asymp\sqrt X/T^{1/4}$ gives $L=O(T^{3/4}/\sqrt X)$ in the range $1\le T\le X^{2/3}$. This bound permits objectives with arbitrarily large coefficients and grants all points tied for the minimum.

The order is attainable for **integer pairs**. Choose all reduced $a/b\in[5/4,3/2]$ with $D/2\le b\le D$ for $D$ a small constant times $\sqrt T$. There are $\Theta(D^2)$ such fractions, by summing the elementary coprime-pair count in this fixed triangle (Möbius inversion gives an $O(D\log D)$ error). For $p\in[X,1.1X]$, take $|q/p-a/b|<c/\sqrt{bX}$ for a small absolute constant $c$. Now

$$
 ap+bq-2\sqrt{abpq}=\frac{(ap-bq)^2}{ap+bq+2\sqrt{abpq}}<1.
$$

The integer cost at the factor pair is the first possible level, hence the pair minimizes it. Distinct centers differ by at least $1/D^2$, so the bands are disjoint for $D^3\le X$ after choosing $c$ sufficiently small. Each contains order $\sqrt{X/D}$ integers $q$ per $p$, all inside the box. This supplies a fraction of order $T^{3/4}/\sqrt X$. Bounded $T$ is covered by a single fixed direction. The argument establishes the matching order on the integer population. The prime-population claim above is an upper bound.

## When the product chooses the slopes

Let a selector adaptively read leading or trailing bits of $N$. At a leaf, it has a product interval $[n,n+\Delta)$, a residue modulo $M=2^\ell$, and its own list of at most $T$ slopes. Intersect the ratio intervals of that list with $[1,2]$. In an interval $[l,u]$ of width $w$, take any two admissible first coordinates $p\le r$, with respective partners $q,t$. Since $n\le pq$, $rt<n+\Delta$, $q\le up$ and $t\ge lr$, we have

$$
 2X(r-p)\le l(r^2-p^2)\le\Delta+(u-l)p^2\le\Delta+4X^2 w.
$$

There are at most $A+B+1$ first coordinates, with $A=2Xw$ and $B=\Delta/X$. For each odd $p$, the second coordinate has one possible residue modulo $M$, and lies in an interval of length at most $\min(A,B)$. The pair count is at most $(A+B+1)(1+\min(A,B)/M)\le2AB/M+2(A+B)+1$. This also holds for $M=1$. Summing over the leaf's $J$ intervals and using $\Delta\ge MX$, the count is at most

$$
 (8L+3JM/X)\,\Delta/M .
$$

At $X=2^{1023}$ the allowed products lie in $[2X^2,4X^2)$. Reading $h$ leading bits, including the known leading one, gives $\Delta=2^{2048-h}$. The condition $h+\ell\le1025$ implies $\Delta\ge MX$. The leaf has exactly $\Delta/M$ **integers** because $M$ divides $\Delta$. The distinct leaves partition the input range if we include impossible transcripts as empty branches of the decision procedure. Thus their masses sum to at most $2X^2$ even for an adaptive selector. Independent randomness can be fixed before applying the same bound. [Lean horizontal-span inequality](../PrimeFactors/SupportingSlope.lean)

For $T=2^{40}$ choose $D=2^{20},K=2^{502}$. Then $L\le28\cdot2^{-482}$. For the fixed list, multiply $2XL+J$ by the prime count $P<1.511 X/\log X$. Divide by at least $(0.22X/\log X)^2/2$ eligible prime pairs and use $\log X<710$ to get the stated $2^{-460}$. For the adaptive selector, $M\le2^{502}$ implies $16L+6JM/X\le472\cdot2^{-482}$. Multiply by $X^2$ and divide by the same denominator to obtain $2^{-448}$. The portfolio counts and asymptotics are paper proofs. Lean checks the displacement, first-level criterion, product-cell span, and final numerical comparisons. [Prime-count derivation](stride-budget.md#an-explicit-bound-at-exactly-2048-bits) · [Formalized steps](../PrimeFactors/SupportingSlope.lean)
