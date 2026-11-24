# Predicting a Salié sign from short frequency descriptions

Fix $N=pq$ with distinct odd primes $p<q$, and let $h$ be a mixed square root of one modulo $N$. Suppose a predictor sees the full product but reads at most 512 bits of the frequency $t$, taking the next unread bit from either end of its fixed-width binary expansion at each step. If both primes are 1,024 bits and $t$ is uniform modulo $N$, its probability of predicting $\operatorname{sign}\cos(2\pi th/N)$ is at most $1/2+2^{-510}$. The choices of bits and predictions may depend on $N$, earlier answers and random coins independent of $t$. This bounds one way of providing the weak sign predictions that would suffice for factoring. It leaves open how to compute them using arithmetic on the entire frequency. [Factoring from a weak predictor](predicting-random-salie-signs.md)

## A complete block of frequencies

The cosine is invariant under $h\mapsto-h$. Choose its representative $h=q u+1$ with $h\equiv-1\pmod p$. Then $qu\equiv-2\pmod p$, so $p\nmid u$. Along $t_i=L+di$, with $0\le i<p$ and $p\nmid d$, the turns are

$$
 \frac{t_i h}{N}=\frac{Lh}{N}+\frac{dui}{p}+\frac{di}{pq}.
$$

The middle term runs through a whole $p$-point grid. The last term moves all its points in the same direction by less than $d/q$ turns for $d>0$. The following integer count handles the endpoints and wrapped arcs directly.

Scale turns by $4N$. Fix any half-open interval $[C,C+2pq)$, interpreted modulo $4pq$, and write $b=4Lh$. Each hit has an integer period index $w_i$ such that

$$
 C\le b+4qv_i+4di<C+2pq,\qquad v_i=ud i-pw_i.
$$

The integers $v_i$ are distinct since their residues $udi\bmod p$ are distinct. For any two hits $i,j$, subtracting the lower bound at $j$ from the upper bound at $i$ gives $4q(v_i-v_j)<2pq+4d(j-i)\le2pq+4dq$. Hence $v_i-v_j<p/2+d$. Since $p$ is odd, at most $(p+1)/2+d$ distinct integers can occur. Apply the same argument to the complementary half-open arc $[C+2pq,C+4pq)$. Each half therefore contains between $(p-1)/2-d$ and $(p+1)/2+d$ of the $p$ phases. For the cosine take $C=N$; no endpoint at an odd quarter turn is attained because $4t_i h$ is divisible by four and $N$ is odd. This proves

$$
 \left|\sum_{i=0}^{p-1}\operatorname{sign}\cos(2\pi(L+di)h/N)\right|\le1+2d.
$$

Lean checks the unit condition, the injective integer lifts, both half-arc counts for arbitrary starting offset, and their discrepancy. [Integer block proof](../PrimeFactors/PhaseBlocks.lean)

## What a partition can predict

Partition the $N$ frequency representatives into at most $B$ disjoint progressions. Each consists of $H$ consecutive terms of a progression modulo $N$, with positive step $d\le D$ coprime to $p$. In particular all positive steps $d<p$ qualify. On one progression, complete blocks contribute at most $\lfloor H/p\rfloor(1+2d)$ to the absolute sign sum. Its last $H\bmod p$ terms contribute at most that remainder. A predictor assigning a constant in $[-1,1]$ to each cell therefore has absolute correlation bounded by

$$
 \left|\mathbb E_t\,g(t)\operatorname{sign}\cos(2\pi th/N)\right|
 \le \frac{1+2D}{p}+\frac{B}{q}.
$$

Indeed the cell lengths sum to $N$, and each unfinished block costs less than $p$. The inequality holds for each partition and all its labels, even if chosen with unrestricted knowledge of $N$. For a predictor returning signs, success probability minus $1/2$ is half its signed correlation. [Lean row bound including the exact remainder](../PrimeFactors/PhaseBlocks.lean)

For a tree inspecting at most $k$ bits from the two ends, each leaf fixes a prefix and a suffix. The prefix cuts out an interval after intersecting with $[0,N)$; the suffix selects one residue modulo $2^j$ if $j$ low bits were read. Thus $B\le2^k$, $D\le2^k$, and every step is coprime to the odd prime $p$. Randomized trees satisfy the same bound by conditioning on their coins. With $k=512$ and $p,q\ge2^{1023}$, the correlation is at most $2^{-1023}+3\cdot2^{-511}<2^{-509}$, giving the stated advantage. The bit restriction concerns $t$ alone. Algorithms inspecting interior bits in an arbitrary order or performing arithmetic on the full $t$ fall outside this bound.
