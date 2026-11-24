# How small can the selected quadratic-sieve values be?

Knowing only the odd semiprime $N$, choose positive $A$ and an integer $B$ with $A\mid B^2-N$. At an integer site $x$, write

$$ Q(x)=\frac{(Ax+B)^2-N}{A}. $$

Then $(Ax+B)^2\equiv A Q(x)\pmod N$. When the primes of $A$ are known, it can be cheaper to factor the smaller $Q(x)$ and retain the known exponents of $A$. The multiple-polynomial quadratic sieve traditionally chooses $A$ near $\sqrt{2N}/m$ on a centered block of $2m+1$ sites. The result below also bounds searches that inspect the product and select any *scattered* integer sites of one polynomial. [Pomerance, *The Quadratic Sieve Factoring Algorithm*](https://math.dartmouth.edu/~carlp/PDF/paper52.pdf) · [Alford and Pomerance, *Implementing the self-initializing quadratic sieve on a distributed network*](https://math.dartmouth.edu/~carlp/implementing.pdf) · [Lean proofs](../PrimeFactors/PolynomialHeight.lean)

## An exact bound with arbitrary sites

Write $H$ for the largest $|Q(x)|$ among the selected sites. The following bounds allow any distinct integer positions and even real $A>0,B$. In this relaxation equality is attainable in both rows.

| Number of selected sites | Lower bound on $H$ |
|---|---:|
| $2m+1$, $m\ge1$ | $m\sqrt{N/2}$ |
| $2m$, $m\ge1$ | $m(m-1)\sqrt N/\sqrt{2m^2-2m+1}$ |

For example, whenever $N$ has 2,048 bits, one polynomial has at most two sites of absolute value strictly below $2^{1023}$ on the whole integer line. Among any $2^{20}+1$ distinct sites, at least one absolute value is at least $2^{1042}$. The same inequalities applied to the $j$ smallest selected values bound each order statistic. For example, the $(2k+1)$st value is at least $k\sqrt{N/2}$. These estimates concern integer magnitudes. Even a large integer can factor entirely into small primes, and combinations from different polynomials are possible.

For the proof put $t=x+B/A$, so $Q(x)=A t^2-N/A$. Consider two points on the same side of the vertex, at distances $t$ and $y$ with $0\le c\le t$ and $t+d\le y$, $d>0$. Set $\Delta=(t+d)^2-t^2=d(2t+d)$. The bounds at the two sites give $N\le A^2t^2+AH$ and $A^2(t+d)^2\le N+AH$, hence $A\Delta\le2H$. Multiplying the first bound by $\Delta^2$ now yields
$$ N\Delta^2 \le 2H^2((t+d)^2+t^2). $$
The quantity $\Delta^2/((t+d)^2+t^2)$ increases with $t\ge0$ since it equals $2d^2(2t+d)^2/((2t+d)^2+d^2)$. Thus the same inequality holds with $t$ replaced by $c$.

For $2m+1$ sites sorted by position, the middle site is at least $m$ steps from each endpoint. Move from that middle site outward on its own side, taking $c=0,d=m$. For $2m$ sites the two middle sites are at least one step apart. At least one of them has distance at least $1/2$ from the vertex and has an endpoint on that same side at distance at least $m-1$ farther outward. Take $c=1/2,d=m-1$. For $m=1$ in the even case the lower bound is zero. The checked theorems use the single absolute-value hypothesis at each selected integer. [Branch estimate and arbitrary-site inequalities](../PrimeFactors/PolynomialHeight.lean)

To attain the relaxed minimum, choose a centered consecutive grid. The nearest and farthest distances are $c=0,r=m$ for an odd count and $c=1/2,r=m-1/2$ for an even count. Choose $A>0$ satisfying $A^2(r^2+c^2)=2N$ and center the grid using $B$. The inner and outer values then have opposite signs and common magnitude $A(r^2-c^2)/2$. Every interior value has smaller or equal magnitude. An integral leading coefficient and the congruence $B^2\equiv N\pmod A$ can prevent exact attainment. The lower bound still applies.

## Finding every small value of a fixed polynomial

For an integer height cap $H\ge0$, compute $L=\lceil\sqrt{\max(0,N-AH)}\rceil$ and $U=\lfloor\sqrt{N+AH}\rfloor$. Exactly the sites for which $Ax+B$ lies in $[L,U]$ or $[-U,-L]$ meet the cap. Integer division of each interval's endpoints gives the complete list with work proportional to its length after two square roots. A shared zero endpoint need only be visited once. The resulting number of sites on either sign branch is at most $1+\lfloor\sqrt{2H^2/N}\rfloor$, by the branch estimate with $c=0$. Thus a search can enumerate all sites under a size budget without first walking the full interval. Checking smoothness and extracting a nontrivial factor remain separate costs.

Searching across every root class at the same coefficient can also be inexpensive when $U-L$ is small. On a planted 2,048-bit product, one quadratic covered more than two trillion classes and found the two primes. [All-class search, crossed control and population bound](polynomial-packets.md)
