# How many inputs can a trillion offsets reach?

Trying all offsets from 1 through $2^{40}$, roughly a trillion, still leaves almost every balanced 2,048-bit semiprime out of reach of this square test. Even if every eligible multiplier at every offset could be tested instantly, fewer than one in $2^{438}$ prime pairs would give a square. This is a bound over uniformly sampled distinct 1,024-bit primes, conditioned on their product having 2,048 bits. The sharper bound uses the divisor sum derived below on paper. A separate finite encoding checked in Lean gives fewer than one in $2^{422}$ and proves that even the offsets through $2^{461}$ cannot cover half the population. All three comparisons use the same explicit prime-count denominator. [Lean proofs](../PrimeFactors/OffsetSweepFrequency.lean) · [Population and sampling model](stride-budget.md#an-explicit-bound-at-exactly-2048-bits)

## Which observations are counted?

Write $T=\lfloor\sqrt N\rfloor$, $h=N-T^2$. A nonsquare has $1\le h\le 2T$. For $1\le j\le J$ and $1\le k\le Tj/h$, the test asks whether $j^2+4k(Tj-hk)$ is a square. If $x$ is its nonnegative square root, $x\ge j$ and $x$ has the parity of $j$. Thus $m=(x-j)/2$ is a nonnegative integer satisfying

$$m(m+j)+hk^2=kTj.$$

Every solution counts, including $m=0$ and cases where $\gcd(kT-m,N)$ is 1 or $N$. Any rule that chooses $j$ or $k$ from the whole product can succeed only on a subset of this union. The strict top multiplier $\lfloor(Tj-1)/h\rfloor$ is one such rule. The requirement $k>0$ matters because $k=m=0$ gives a square on every input. Square inputs form a separate family of at most $L$ integers for $0\le T<L$ and are already recognized by the first square-root computation. Products of distinct primes belong to the nonsquare family. [Discriminant equivalence and finite count](../PrimeFactors/OffsetSweepFrequency.lean) · [Original grouped test](grouped-norm-factors.md)

If a prime divides both $k$ and $j$, the equation implies it divides $m^2$ and hence $m$. Dividing $k,j,m$ by it preserves the equation and decreases $j$. Iteration produces a witness with $\gcd(k,j)=1$. This argument allows repeated prime factors everywhere. Dividing a witness can change its gcd with $N$. Counting every raw square makes the upper bound valid even in this case.

## A finite count checked in Lean

Set $L=S^2$ and take $1\le j\le J\le S$, $T<L$, and $LJ\le 2^e$. A primitive witness obeys $k<Lj$. Allocate the multiplier by writing $b=\gcd(k,m)$ and $a=k/b$. Then $b\mid m$ and $a\mid m+j$ by cancellation. If a prime divided both $a$ and $b$, it would divide $j$ as well as $k$. Thus they are coprime and the two congruences determine $m\bmod k$. Once $\lfloor m/k\rfloor$ is also supplied, they determine $m$.

For fixed $j,k,m$, put $v=m(m+j)/k$. The remaining equation $Tj=v+hk$ determines $T\bmod k$ and $h\bmod j$ by coprimality. Knowing either $\lfloor T/k\rfloor$ or $\lfloor h/j\rfloor$ recovers both $T$ and $h$. Store the latter quotient when $k\le j$ and the former otherwise. Denote it by $y$, and put $z=\lfloor\sqrt{Lj/k}\rfloor$. Then $\lfloor m/k\rfloor\le z$. The following inequalities bound the number of choices in each pair of dyadic ranges for $a,b$.

| Range | Inequalities |
| --- | --- |
| $k\le j$ | $kz\le Sj$, $k(z+1)\le2Sj$, and $j(y+1)\le3L$ |
| $j<k\le L$ | $z\le S$ and $k(y+1)\le2L$ |
| $k>L$ | $y=0$, $kz\le Lj$, and $k\le Lj\le LS$ |

In each case $k(z+1)(y+1)\le6S^3$. Store the two indices $\lfloor\log_2a\rfloor,\lfloor\log_2b\rfloor$, with lower endpoints $A,B$ in their respective ranges. The single integer

$$
(a-A)+A\big((b-B)+B(\lfloor m/k\rfloor+(z+1)y)\big)
$$

is strictly below $AB(z+1)(y+1)\le6S^3$. The indices let us recover $a,b$ first, giving $k$ and $z$. The remaining digits then recover $m,y,T,h$ in order. Together with $j$, the code therefore determines $N$. Choosing one witness per successful input injects those inputs into at most

$$J e^2(6 S^3)$$

codes. At $S=2^{512}, J=2^{40}, e=1064$ this is less than $2^{1599}$. Even $J=2^{461}, e=1485$ leaves the code count below half the prime-pair denominator. Lean proves these inequalities starting from any finite set of products that give raw squares, independently of the number of witnesses each input has. [Theorems `discriminant_square_iff`, `all_offsets_card`, `scale_2048`, and `half_scale_2048`](../PrimeFactors/OffsetSweepFrequency.lean)

## A sharper divisor sum

The following estimates are a paper deduction. Let $\tau(k)$ denote the number of positive divisors of $k$. For fixed primitive $j,k$, the preceding root allocation shows that there are at most $\tau(k)$ classes of $m\bmod k$. The bound $m^2\le kLj$ gives at most $1+\sqrt{Lj/k}$ possible $m$ in each class. For fixed $m$, both $T\bmod k$ and $h\bmod j$ are fixed, and either coordinate determines the other. Since $T<L$ and $h<2L$, at most $1+\min(L/k,2L/j)$ input pairs remain. Consequently the number of successful products is at most

$$
\sum_{j=1}^{J}\sum_{k\le Lj}\tau(k)
  (1+\sqrt{Lj/k})(1+\min(L/k,2L/j)).
$$

For $Z\ge1$, write $k=ab$ and sum over all ordered divisor pairs. The inequalities $\sum_{b\le u}1/b\le1+\ln u$ and $\sum_{b\le u}1/\sqrt b\le2\sqrt u$ give

$$
\sum_{k\le Z}\tau(k)\le Z(1+\ln Z),\qquad
\sum_{k\le Z}\frac{\tau(k)}{k}\le(1+\ln Z)^2,\qquad
\sum_{k\le Z}\frac{\tau(k)}{\sqrt k}\le2\sqrt Z(1+\ln Z).
$$

For the mixed term, split at $k=j$. The part with $k\le j$ costs at most $4L^{3/2}(1+\ln j)$ using $2L/j$. For the part with $k>j$, the divisor-pair expansion gives

$$
\sum_{k>j}\frac{\tau(k)}{k^{3/2}}\le\frac{9+3\ln j}{\sqrt j}.
$$

Indeed, for $a\le j$, sum first over $b>j/a$. For $x\ge1$, the tail $\sum_{b>x}b^{-3/2}\le2/\sqrt{\lfloor x\rfloor}\le3/\sqrt x$, so these $a$ contribute at most $3(1+\ln j)/\sqrt j$. For $a>j$, bound the outer tail by $2/\sqrt j$ and the full inner sum by $3$. Multiplying by $L\sqrt{Lj}$ bounds the remaining mixed term. With $M=LJ$, the total is at most

$$
3LJ^2(1+\ln M)+LJ(1+\ln M)^2+
L^{3/2}\sum_{j=1}^{J}(13+7\ln j).
$$

For $L=2^{1024}$ and $J=2^{40}$, we have $1+\ln M<740$. The mean of $\ln j$ for $1\le j\le J$ is at most $(39+40)\ln(2)/2$ by dividing at $J/2$. Use $\ln2<0.694$, which also follows from the positive terms through degree four of the exponential series at $0.694$. Substitution bounds the entire sum strictly below $205\cdot2^{1576}<2^{1584}$ products. Let $X=2^{1023}$. Explicit prime counts imply that more than $(22X/71000)^2/2$ distinct unordered pairs have both primes in $[X,2X)$ and an exactly 2,048-bit product. Unique factorization makes their products distinct. The ratio is below $2^{-438}$. Lean checks the final integer arithmetic in `paper_constants`. The divisor sums and the external prime-count bound enter on paper. [Integer comparisons](../PrimeFactors/OffsetSweepFrequency.lean) · [Prime-pair denominator](stride-budget.md#an-explicit-bound-at-exactly-2048-bits) · [Rosser and Schoenfeld, Corollary 1](https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf#page=6)

## Exhaustive check at small sizes

The following counts use every $32\le T<64$ and every $1\le h\le2T$, giving 3,040 distinct nonsquares. For each input, enumerate $1\le j\le J$ and $1\le k\le\lfloor Tj/h\rfloor$. Check each discriminant by integer square root, count the input once per column, and test $1<\gcd(kT-m,N)<N$ for the proper-gcd columns. The strict top column uses $k=\lfloor(Tj-1)/h\rfloor>0$. On this entire panel, restricting to coprime $k,j$ preserves the unrestricted raw-square column exactly.

| Largest offset $J$ | Any raw square | Any proper gcd | Strict top square | Strict top proper gcd |
| ---: | ---: | ---: | ---: | ---: |
| 1 | 580 | 576 | 306 | 306 |
| 2 | 942 | 934 | 558 | 558 |
| 4 | 1,504 | 1,486 | 900 | 900 |
| 8 | 2,080 | 2,045 | 1,346 | 1,346 |

The small panel shows that offsets can reach additional products. The finite upper bounds quantify how that gain scales when both prime factors have 1,024 bits.
