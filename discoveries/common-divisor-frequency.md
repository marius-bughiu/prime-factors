# How often two primes have a large common predecessor divisor

Fix $0<\alpha<1$ and let $X$ tend to infinity. Among products $N=pq$ of distinct primes $X\le p<q\le2X$, the number satisfying $\gcd(p-1,q-1)\ge X^\alpha$ is
$$
\Theta_\alpha\!\left(\frac{X^{2-\alpha}}{(\log X)^2}\right).
$$
The same order holds with both primes in $(3X/2,7X/4]$ and $q-p\ge\delta_\alpha X$ for some constant $\delta_\alpha>0$. In particular, taking $X=2^{b-1}$ gives two $b$-bit primes and a $2b$-bit product for every sufficiently large $b$. The fraction of all balanced products in the original box satisfying the gcd threshold has order $X^{-\alpha}$.

On these inputs the product-only common-predecessor algorithm takes expected $O_\alpha(N^{(1-\alpha)/4}\operatorname{polylog}N)$ bit operations. Indeed its work depends on the square root of $(p-1)/\gcd(p-1,q-1)$. For $\alpha>1/5$ the exponent falls below the deterministic one-fifth benchmark. The lower bound on the prime gap still forces order $\sqrt N$ consecutive Fermat midpoint tests. This is an unconditional asymptotic count proved on paper. It gives no explicit frequency at 2,048 bits. [Algorithm and Lean-verified arithmetic](common-predecessors.md) · [Fermat midpoint identity](shifted-square-infinitude.md#fifty-fixed-linear-forms)

## Counting prime–divisor incidences

Write $D=X^\alpha$, $I=(3X/2,7X/4]$, $d\sim D$ for integers in $[D,2D]$, and $P_d$ for the number of primes in $I$ congruent to $1\bmod d$. We first show $T=\sum_{d\sim D}P_d\gg_\alpha X/\log X$.

* If $\alpha<1/2$, Bombieri–Vinogradov at both endpoints gives total absolute error $O_A(X/(\log X)^A)$ against the prime count in $I$ divided by $\varphi(d)$. The main term has the required order from below since $\sum_{d\sim D}1/\varphi(d)\gg1$. [Bombieri–Vinogradov in prime-counting form, equation (1.2)](https://arxiv.org/pdf/2006.06572#page=2)
* If $\alpha>1/2$, sum instead over integers $X/D\le k\le1.1X/D$. Each prime $p\in I$ with $k\mid p-1$ supplies $d=(p-1)/k\sim D$. For a fixed $p$ distinct $k$ give distinct $d$. These $k$ are within the Bombieri–Vinogradov range for large $X$, and $\sum_k1/\varphi(k)\gg1$. This gives the same lower bound without a prime-distribution estimate for large $d$.
* If $\alpha=1/2$, use Maynard's Corollary 1.3 with $Q=D$, residue $1$, and parameter $1/1000$. At either endpoint $x$ of $I$, at most $18Q/1000$ moduli in $[Q,2Q]$ fail the relative estimate $\pi(x;d,1)=(1+O(1/\log x))\pi(x)/\varphi(d)$. The intersection of the two good sets contains $\gg D$ moduli. Subtracting the endpoint estimates gives $P_d\gg X/(\varphi(d)\log X)$ there. [Maynard, Corollary 1.3](https://arxiv.org/pdf/2006.06572#page=3)

Put $B=X^2/(D(\log X)^2)$. Cauchy–Schwarz now gives $\sum_{d\sim D}P_d^2\gg_\alpha B$. We can retain pairs separated by a fixed fraction of $X$. For fixed $0<\delta<1/10$, the interval Brun–Titchmarsh inequality bounds $P_d$ by $O_\alpha(X/(\varphi(d)\log X))$ and the number of partners within $\delta X$ of each prime by $O_\alpha(\delta X/(\varphi(d)\log X))$. These implied constants are uniform in $\delta$ once $X$ is sufficiently large depending on $\delta,\alpha$, because $\log(\delta X/(2D))\ge(1-\alpha)\log X/2$. The close pairs contribute $O_\alpha(\delta B)$ by the totient estimate below. The lower bound for the unrestricted incidences was obtained before choosing $\delta$. Choosing $\delta=\delta_\alpha$ small therefore retains $\gg_\alpha B$ ordered pair–divisor incidences and removes the diagonal. [Montgomery and Vaughan, Theorem 2, equation (1.10)](https://personal.science.psu.edu/rcv4/personal/Publications/large_sieve.pdf#page=3)

## Removing repeated divisors

The mean bound $\sum_{n\le Y}(n/\varphi(n))^2\ll Y$ follows by expanding $\prod_{\ell\mid n}(1+c_\ell)$ over prime divisors, where $c_\ell=(1-1/\ell)^{-2}-1$. Summing the expansion costs at most $Y\prod_\ell(1+c_\ell/\ell)=O(Y)$. In particular $\sum_{n\sim Y}1/\varphi(n)^2\ll1/Y$ for $Y\ge1/2$.

For each retained pair let $M_{pq}$ count its common divisors $d\sim D$ of $p-1,q-1$. Its second moment over these pairs is at most $\sum_{d,e\sim D}P_{[d,e]}^2$, where brackets denote lcm. Set $\beta=(1+\alpha)/2$. For $L=[d,e]\le X^\beta$, Brun–Titchmarsh gives $P_L\ll_\alpha X/(\varphi(L)\log X)$. To sum the squares, write $d=ha,e=hb$ with $h=\gcd(d,e)$, so $L=hab$ and $\varphi(L)\ge\varphi(h)\varphi(a)\varphi(b)$. Dropping the coprimality restriction on $a,b$ gives
$$
\sum_{d,e\sim D}\frac1{\varphi([d,e])^2}
\ll\sum_{h\le2D}\frac{(h/D)^2}{\varphi(h)^2}\ll\frac1D.
$$
For $L>X^\beta$, every prime counted has the form $1+jL$ with $1\le j\le2X/L$, so $P_L\le2X/L$. Here $h=de/L\le4D^2/X^\beta$. For each $h$ there are at most $(2D/h)^2$ pairs divisible by $h$, and $1/L^2=h^2/(de)^2\le h^2/D^4$ for pairs of gcd exactly $h$. Consequently
$$
\sum_{d,e\sim D,\ [d,e]>X^\beta}\frac1{[d,e]^2}
\ll\frac1{D^2}\left\lfloor\frac{4D^2}{X^\beta}\right\rfloor\ll X^{-\beta}.
$$
Together the two ranges give $\sum M_{pq}^2\ll_\alpha B+X^{2-\beta}\ll_\alpha B$. Since $\sum M_{pq}\gg_\alpha B$, a second application of Cauchy–Schwarz leaves $\gg_\alpha B$ distinct pairs. Ordering costs a factor of two. Unique prime factorization converts unordered pairs to distinct products.

For the matching upper bound on the whole box, count each pair using its gcd as one modulus $d\ge D$. For $D\le d\le X^\beta$, Brun–Titchmarsh and the dyadic totient estimate give a total at most $O_\alpha(B)$ after summing the squared progression counts. For $d>X^\beta$, summing $(2X/d)^2$ gives $O(X^{2-\beta})$. Cai's Lemma 11 already gives the $O(1/D)$ probability bound for equal-bit primes and $D$ up to the fourth root of the box endpoint by this argument. The cutoff $X^\beta$ here allows any fixed $\alpha<1$. At $\alpha=1$, distinct positive multiples of a common divisor at least $X$ cannot both lie in $[X-1,2X-1]$. [Jin-Yi Cai, Lemma 11](https://pages.cs.wisc.edu/~jyc/Shor-Algorithm-with-Noise.pdf#page=17)

## The leading constant through the square-root threshold

For $0<\alpha\le1/2$, the proportion of the whole box satisfying the gcd threshold is asymptotic to
$$
\frac{C}{X^\alpha},\qquad
C=\prod_{\ell\ \mathrm{prime}}\left(1+\frac1{\ell(\ell-1)}\right)
=\frac{\zeta(2)\zeta(3)}{\zeta(6)}.
$$
Here the sampling is uniform over distinct unordered pairs of primes. This statement concerns the whole box before imposing a gap condition.

Use $(X,2X]$ so the progression counts are differences at the two endpoints. Omitting a possible prime at $X$ changes the pair proportion by $O(\log X/X)=o(1/D)$. Let $U_m$ count primes $p$ in this interval with $m\mid p-1$, and let $W=U_1\sim X/\log X$. Exact Möbius inversion counts ordered pairs, including diagonals, with the required gcd by $\sum_{g\ge D,k\ge1}\mu(k)U_{gk}^2$. Removing diagonal pairs changes the normalized count by $O(1/W)=o(1/D)$.

We claim that replacing $U_{gk}^2/W^2$ by $1/\varphi(gk)^2$ in this sum costs $o(1/D)$. First truncate to $D\le g\le KD$, $k\le K$ for fixed $K\ge2$. For $gk\le X^\beta$, Brun–Titchmarsh bounds the normalized summand in absolute value by $O_\alpha(1/(\varphi(g)^2\varphi(k)^2))$. Its omitted tails sum to $O_\alpha(1/(KD))$ by the dyadic estimate. For $gk>X^\beta$ the unnormalized contribution is $O(X^2\sum_{m>X^\beta}\tau(m)/m^2)=O(X^{2-\beta}\log X)$, using $\sum_{m\le y}\tau(m)\ll y\log(2y)$ by counting divisor pairs. The model sum $\sum\mu(k)/\varphi(gk)^2$ has the same $O(1/(KD))$ truncation bound over its entire range.

In the truncated sum $D\le m=gk\le K^2D$ and each modulus occurs at most $K$ times. If $\alpha<1/2$, Bombieri–Vinogradov bounds $\sum_m|U_m-W/\varphi(m)|\ll_A X/(\log X)^A$. Brun–Titchmarsh gives $U_m/W+1/\varphi(m)\ll_\alpha\log X/D$ here, using $m/\varphi(m)=\sum_{d\mid m}\mu(d)^2/\varphi(d)\ll\log(2m)$ by the dyadic totient bound. Multiplying the two estimates and normalizing gives $o(1/D)$ for each fixed $K$.

If $\alpha=1/2$, cover $[D,K^2D]$ by dyadic intervals $[Q,2Q]$. Fix $K$ and $0<\varepsilon<1/55$. Each block satisfies $Q\le K^2\sqrt X\le X^{1/2+\varepsilon}$ once $X$ is sufficiently large, so Maynard's Corollary 1.3 applies at both $X$ and $2X$ with residue $1$. The union of the exceptional sets has size at most $36\varepsilon Q$. On the remaining moduli, subtracting the two estimates gives $U_m/W=(1+o(1))/\varphi(m)$ uniformly, since $W$ is comparable with $\pi(2X)$. On the exceptions Brun–Titchmarsh still applies. Their total weight $\sum_{m\ \mathrm{exceptional}}1/\varphi(m)^2$ is $O(\sqrt\varepsilon/Q)$ by Cauchy–Schwarz, since the same Euler-product argument as for the second moment gives $\sum_{m\le y}(m/\varphi(m))^4\ll y$. Summing the blocks costs $O_K(\sqrt\varepsilon/D)$, with absolute constants in the exception bound. Thus the limsup as $X\to\infty$ of $D$ times the absolute replacement error is at most $O(1/K)+O_K(\sqrt\varepsilon)$. Taking $\varepsilon\downarrow0$ before $K\to\infty$ proves the endpoint assertion. [Maynard, Corollary 1.3, accepted manuscript](https://ora.ox.ac.uk/objects/uuid%3A39a52f47-3770-4ddd-b7a2-b2a4f7300931/files/srj4305733#page=3)

It remains to evaluate the model tail. Set $h(g)=\sum_{k\ge1}\mu(k)/\varphi(gk)^2$ and $C_2=\prod_{\ell>2}(1-1/(\ell-1)^2)$ over primes. The absolutely convergent Euler product for $h(g)$ vanishes for odd $g$. For even $g$ it gives
$$
g^2h(g)=3C_2\prod_{\substack{\ell\mid g\\\ell>2}}
\frac{\ell^2-1}{\ell(\ell-2)}.
$$
Write the factors in this last product as $1+t_\ell$. Expanding the product and averaging over integers $g$, the even multiples of an odd squarefree $s$ have density $1/(2s)$. The series of mean contributions converges absolutely since $t_\ell=O(1/\ell)$. Thus $g^2h(g)$ has mean $(3/2)C_2\prod_{\ell>2}(1+t_\ell/\ell)=C$ by simplifying each prime factor. Partial summation gives $\sum_{g\ge D}h(g)\sim C/D$, as claimed.
