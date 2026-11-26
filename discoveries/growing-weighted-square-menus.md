# How far can a growing menu of weighted squares reach?

Even if testing every subset were free, a menu of small weights and labels near their square-root endpoints would leave almost every balanced semiprime unresolved as the prime size grows. This holds for **every fixed polynomial** in the input bit length bounding the weights and the label offsets. The proof counts inputs on which a factor-revealing square relation exists. It allows the search to choose weights, labels and subsets after seeing the full product. It gives an asymptotic population bound. At 2,048 bits the repository has a finite Lean bound for its 16-row menu and a written bound for up to 33,554,432 rows. [Finite budgets at 2,048 bits](finite-budgets-for-weighted-subsets.md) [Fixed-label Lean count](../PrimeFactors/WeightedSubsetFiber.lean) · [Finite population proof](../PrimeFactors/WeightedSubsetPopulation.lean) · [Finite comparison](testing-three-weighted-remainders.md)

## The menu and the exponent

Let $X\le p<q<2X$ be primes and $N=pq$. A row consists of positive integers $r,A$ satisfying

$$1\le r\le K,\qquad 0\le A-2\sqrt{rN}\le H,\qquad D=A^2-4rN.$$

A success means a subset has $\prod_iD_i=z^2$ and one of $\gcd(N,\prod_iA_i\pm z)$ is a proper divisor. We also count any proper factor already visible in $\gcd(N,A_i)$. The usual first $J$ admissible labels of stride $\gcd(24,2(r+N))$ fit with $H=24J$. Logarithms below are natural. All probabilities mean the fraction of distinct eligible products, counted once each.

**Theorem.** Suppose $K=O((\log X)^a)$ and $H+1=O((\log X)^b)$, for fixed $a,b\ge0$. Put $d=a+b$. The successful fraction is at most

$$ X^{-\min\{1/2,\,1/(d+1)\}+o(1)}. $$

The same estimate holds if only products $N\ge2X^2$ are eligible. For example, allowing both the weight and the offset to grow linearly with the prime bit length gives an upper bound $X^{-1/3+o(1)}$. The exponents describe this proof's upper bounds. A smaller catalogue can admit stronger bounds. A search visiting a few rows with unrestricted weights or offsets falls outside the theorem.

## One list of possible rows per interval

Write $T=\log X$ and $h=\lceil\sqrt K\rceil$. Split the range $[X,2X)$ of $\sqrt N$ at multiples of $1/h$. There are $O(Xh)$ cells. Within a cell $[v,v+1/h)$ every possible integer $A$ for a given $r$ lies in $[2\sqrt r\,v,\,2\sqrt r\,(v+1/h)+H]$. This interval has length at most $H+2$. The *entire* catalogue for one cell therefore contains at most $L=K(\lfloor H\rfloor+3)$ rows. Unused rows may be included. In particular, fixing one cell determines every allowable label across its inputs, without multiplying the numbers of choices at successive weights.

For an actual row,

$$0\le D\le Y:=H(8X\sqrt K+H).$$

For the bounds below one may replace $Y$ by $\max(1,Y)$. Eventually $K<X$ in all regimes considered here. For odd distinct $p,q$, the exponent of $p$ in $4rN$ is then one, so $D=0$ is impossible. If $p\mid A$, write $A=kp$. Then $k\le4\sqrt K+H/X$, and $0<D/p=k^2p-4rq\le Y/X$. For fixed $p,k,r$ and the integer $D/p$ there is at most one $q$. Interchanging the two primes covers either nonunit label. This bounds the exceptional products by $O(XK(1+\sqrt K+H/X)(1+Y/X))$, or $X^{1+o(1)}$ in the polynomial case.

For the remaining inputs all row labels are units modulo $N$. Two rows are proportional when $sA^2=rB^2$. In that case $E=B^2D/A^2$ and $\sqrt{DE}=BD/A$ is a positive integer, since its square is an integer. Moreover $A\sqrt{DE}=BD\equiv BA^2\pmod N$, hence $\sqrt{DE}\equiv AB\pmod N$. Removing the two rows preserves a square relation and each signed gcd, because $AB$ is a unit. A rational number whose square is an integer is an integer, which also ensures the remaining root is integral. Repeat until each proportionality class appears at most once. If the relation becomes empty, its signed gcds are $N$ and $1$ for odd $N$. Every proper split therefore has a nonempty reduced relation. [Checked pair removal](../PrimeFactors/WeightedSubsetReduction.lean)

## All subsets containing a particular row

Fix a cell and one row $(r,A)$ in it. Form $M$ as the product of the **nonzero** integers $|sA^2-rB^2|$ over all other rows $(s,B)$ in that cell's catalogue. An empty product is one. The crude bound $|sA^2-rB^2|\le 2K(4X\sqrt K+H+2)^2$ suffices. In particular $\log M=O(LT)$ under the polynomial bounds. This $M$ is fixed before the unknown product in the cell or its winning subset has been chosen.

If the fixed row belongs to a reduced relation, every prime appearing to odd exponent in $D$ divides another participating excess $E$. It then divides $sD-rE=sA^2-rB^2$, which is nonzero after reduction. Consequently $D=mu^2$ for a squarefree $m\mid M$ and a positive integer $u$. A fixed value of $D$ determines at most one $N$ because $A^2-D=4rN$. These statements also cover a singleton square through $m=1$. The common-prime elimination and squarefree support across finite partitions are checked in Lean. [WeightedTripleSupport.lean](../PrimeFactors/WeightedTripleSupport.lean)

For $1/2\le\theta<1$ the count for this row is bounded by

$$\sum_{\substack{m\mid M,\ m\le Y\\m\ {\rm squarefree}}}\left\lfloor\sqrt{Y/m}\right\rfloor
\le Y^\theta\prod_{\ell\mid M}(1+\ell^{-\theta}),$$

where the product runs over distinct primes. Indeed $Y/m\ge1$ in the sum. Expanding the product pays once for each squarefree divisor of $M$, covering all choices of the participating rows simultaneously. This use of a fractional power to bound a counting function is Rankin's method. [Rankin, *The Difference between Consecutive Prime Numbers* (1938)](https://doi.org/10.1112/jlms/s1-13.4.242)

Let $k$ be the number of distinct prime divisors of $M$. Their product is at least $k!$. For $k\ge4$, $\log(k!)\ge\lfloor k/2\rfloor\log(k/2)$. Since $\log M=O(T^{d+1})$, this gives $k=O(T^{d+1}/\log T)$ uniformly, including bounded $k$. The $j$th smallest possible divisor prime is at least $j+1$, so

$$\log\prod_{\ell\mid M}(1+\ell^{-\theta})\le\sum_{j=1}^k j^{-\theta}=O_\theta(1+k^{1-\theta}).$$

Choose $\theta=\max(1/2,1-1/(d+1))$. Then $(d+1)(1-\theta)\le1$, and even at equality the factor $(\log T)^{-(1-\theta)}$ makes the last bound $o(T)$. Since $Y\le X T^{O(1)}$, there are at most $X^{\theta+o(1)}$ possible products per row. The $O(XhL)$ choices of cell and row give $X^{1+\theta+o(1)}$ products. The nonunit exceptions fit inside this total. The prime number theorem gives $\gg X^2/(\log X)^2$ eligible products even if both primes are restricted to $[3X/2,7X/4]$, which ensures $N\ge2X^2$. Dividing proves the theorem. [Rosser and Schoenfeld, *Approximate Formulas for Some Functions of Prime Numbers*](https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf)

## Menus larger than any fixed polynomial

More generally let $V=\max(\log(K+1),\log(H+1),\log T)$ and suppose $V=o(\sqrt{T\log T})$. The fraction with a proper split is at most $\exp(-\Omega(T\log T/V))$. For example, this still tends to zero when both $K$ and $H$ equal $\exp(\sqrt{\log X})$.

Here are the estimates needed when the exponent varies. Put $z=\max(3,\log M)$ and $0<\eta\le1/2$. Primes larger than $z$ contribute at most $z^\eta/\log z$ to $\sum_{\ell\mid M}\ell^{-1+\eta}$, since there are at most $\log M/\log z$ of them. For the other primes, take $\sigma=1+1/\log z$. The Euler product and the integral bound for the convergent zeta series give

$$\sum_{\ell\le z}\ell^{-1}\le e\sum_{\ell\le z}\ell^{-\sigma}\le e\log\zeta(\sigma)\le e\log(1+\log z).$$

Thus the logarithm of our Euler product at $\theta=1-\eta$ is at most $z^\eta(e\log(1+\log z)+1/\log z)$. The cell estimates above give $\log z\le C V$ for an absolute $C\ge1$, $Y\le X\exp(O(V))$, and $O(XhL)=X\exp(O(V))$. Choose $\eta=\log T/(4CV)$, so the logarithmic cost of the Euler product is $O(T^{1/4}\log T)$. After division by the population, the logarithm of the fraction from unit labels is at most

$$-\eta T+O(V+T^{1/4}\log T).$$

Both error terms are $o(\eta T)$ under the hypothesis on $V$. The nonunit fraction is at most $\exp(-T+O(V))$ by the earlier integer count. This proves the stated decay.

## Constants at the square-root logarithmic scale

Put $S=\sqrt{T\log T}$. Suppose $\log K\le(\alpha+o(1))S$ and $\log(H+1)\le(\beta+o(1))S$ for fixed $\alpha,\beta\ge0$. If

$$(2\alpha+\beta)(\alpha+\beta)<\tfrac12,$$

the successful fraction is at most $\exp(-\delta S)$ for some $\delta>0$ and all sufficiently large $X$. With bounded weights, this includes every offset budget $H=\exp((c+o(1))\sqrt{\log N\log\log N})$ with $0\le c<1/2$. Indeed $\log N=2T+O(1)$ uniformly on the population, so $\beta=\sqrt2\,c$ is admissible when the offset bound holds uniformly. The strict inequality gives a range of exclusion. The behavior at the boundary and above it remains open here.

For the sharper count, partition $[X,2X)$ into half-open cells of width $(H+1)/h$, clipping the last cell at $2X$. There are $\lceil Xh/(H+1)\rceil$ cells. This is $O(Xh/(H+1))$ because $H+1=\exp(O(S))=o(X)$. Across a cell each lower endpoint $2\sqrt{rN}$ moves by at most $2(H+1)$. On one side or both sides of that endpoint, there are consequently $O(H+1)$ possible integer labels per weight, including endpoints. Each cell has $O(K(H+1))$ rows and the total number of cell-row pairs is $O(XKh)=O(XK^{3/2})$.

The original excess bound gives $\log\max(1,Y)\le T+(\alpha/2+\beta+o(1))S$. Every possible label in a cell is at most $4X\sqrt K+O(H+1)$, so each nonzero determinant has logarithm $O(T)$. Multiplying at most $O(K(H+1))$ determinants yields $\log z\le(\alpha+\beta+o(1))S$ uniformly, including $M=1$. Choose a fixed $t>2\alpha+\beta$ with $t(\alpha+\beta)<1/2$, and set $\eta=t\sqrt{\log T/T}$. The preceding Euler-product estimate gives

$$\log\prod_{\ell\mid M}(1+\ell^{-1+\eta})\le T^{t(\alpha+\beta)+o(1)}=o(S).$$

The exponent from $Y^{1-\eta}$ is at most $T+(\alpha/2+\beta-t+o(1))S$, as $\eta T=tS$. Counting all cell-row pairs adds at most $T+(3\alpha/2+o(1))S$ to this logarithm. Dividing by the eligible population subtracts $2T-O(\log T)$. The nonunit-label fraction is $\exp(-T+O(S))$ by the earlier count. Combining these bounds gives a fraction at most $\exp((2\alpha+\beta-t+o(1))S)$ as claimed. The same argument permits every fixed $t>0$ when $\alpha=\beta=0$.

**Offsets on both sides.** The estimates also hold for $|A-2\sqrt{rN}|\le H$ when the tested product of signed excesses must be an integer square. Each weight has at most $2H+3$ labels in a cell of width $1/h$, or $O(H+1)$ in the wider cells, and $|D|\le Y$. In the nonunit count allow either sign of $D/p$. For proportional rows use the signed integer $BD/A$ as their square root. It is still congruent to $AB$, and changing the sign of the remaining root only exchanges the two gcds. Prime support now constrains $|D|$, which specifies at most two input products per row. All these changes affect only constant factors.

The growing-menu estimates and the varying-exponent argument above are paper proofs. They cover gcds obtained from exact integer square products in the stated interval. Other polynomial families, larger intervals and other readouts require their own analysis. Classical quadratic-sieve research describes those choices of polynomials, sieving intervals and smoothness bounds. [Pomerance, *The Quadratic Sieve Factoring Algorithm*](https://math.dartmouth.edu/~carlp/PDF/paper52.pdf)

Balister, Bollobás and Morris proved a sharp threshold for a square product when the input integers are independent uniform draws. Granville and Selfridge study subsets of consecutive integer intervals and use primes with odd exponents to obstruct some square classes. Pomerance's quadratic-sieve analysis models the smoothness of values of a polynomial near its endpoint. Here the values all come from the same semiprime and the event requires a proper gcd. These distinctions matter when interpreting the constant $1/2$. [Balister, Bollobás and Morris](https://annals.math.princeton.edu/wp-content/uploads/annals-v188-n1-p02-p.pdf) · [Granville and Selfridge](https://dms.umontreal.ca/~andrew/PDF/selfridge.pdf) · [Pomerance on polynomial smoothness](https://websites.math.leidenuniv.nl/algebra/sieving.pdf)
