# Can Robin’s inequality reveal the sum of two primes?

Let $N=pq$ with distinct odd primes $p<q\le2p$, and write $X=\sqrt N$. Knowing the divisor sum $\sigma(N)=N+p+q+1$ determines the factors by a quadratic equation. A natural way to sharpen Robin’s upper bound is to apply it to $kN$, choosing a positive multiplier $k$ coprime to $N$ for which $\sigma(k)$ is easy to evaluate. For $kN>5040$, multiplicativity gives

$$
\sigma(N)<U_k(N):=e^\gamma N\frac{k\log\log(kN)}{\sigma(k)}.
$$

For a 2,048-bit product, even a multiplier that improves the elementary balanced upper bound must have **more than $2^{1023}$ bits** in its ordinary binary representation. There is also an exact positive result. The lower limit of these upper bounds determines both factors, and one unit of absolute precision suffices. Evaluating that limit cheaply from the product remains open. [Local Lean implications and decoder](../PrimeFactors/RobinMultiplier.lean)

Andrew Sutherland’s November 24 verification combines the RH release with Robin1984 at commit 5ce18bf3. Independent checkers accepted the comparison theorem for every integer greater than 5040. The earlier check at acab1a3 gives the same divisor-sum inequality. The local finite proofs take this analytic statement as an explicit hypothesis, using the repository’s pinned mathlib. [MIT verification and logs](https://math.mit.edu/~drew/grh/#arithmetic-consequences) · [Combined theorem](https://math.mit.edu/~drew/grh/ArithSolution.lean) · [Robin’s original paper, 1984](https://fr.scribd.com/document/812768752/Robin-1984-noBackground)

## What a finite multiplier must contain

For each positive $M\le N$ coprime to $k$ with $kM>5040$, Robin at $kM$ and monotonicity of $\log\log$ imply

$$ U_k(N)>N\,\sigma(M)/M. $$

Let $r<s$ be the first two primes that do not divide $k$, and suppose $krs>5040$. Since $p$ and $q$ are omitted, $r\le p$ and $s\le q$. Take $M=rs$. If $r<p$, replacing $s$ by $q$ in the comparison gives

$$ U_k-\sigma(N)>(q+1)(p-r)/r>1. $$

If $r=p$ and $s<q$, the lower bound instead gives $(p+1)(q-s)/s>1$, since $s,q$ are odd and $s<q\le2p$. Thus **$\lfloor U_k\rfloor=\sigma(N)$ forces $(r,s)=(p,q)$**. Knowing these two omitted primes already supplies the factorization. This is a necessary condition for taking the integer floor of the raw upper bound. [Lean proof using the two omitted primes](../PrimeFactors/RobinMultiplier.lean)

A single omitted prime $\ell\le X/3$ gives $U_k>N+N/\ell\ge N+3X$ if $k\ell>5040$. The balanced upper bound $\sigma(N)\le N+1+(3/\sqrt2)X$ is smaller for 2,048-bit products. Thus an improving $k>5040$ must contain **every prime through $X/3$**. The explicit inequality $\pi(t)>t/\log t$ for $t\ge17$ gives more than $2^{1012}$ distinct prime divisors, since $X\ge2^{1023.5}$ and $\log(X/3)<710$. [Rosser and Schoenfeld, Corollary 1](https://doi.org/10.1215/ijm/1255631807)

An independent comparison gives the stated binary size. For $k>5040$ put $t=\log k$. Robin at $k$ itself yields

$$ U_k>N\left(1+\frac{\log(1+\log N/t)}{\log t}\right). $$

If $t\le X/2$, use $\log(1+v)\ge v/(1+v)$ for $v\ge0$ and $\log t\le\frac12\log N$. The fraction is at least $4/(X+2\log N)>3/X$ at this input size. For $1\le k\le5040$, $\sigma(k)/k\le\sum_{i\le k}1/i\le1+\log k<10$, while $e^\gamma>3/2$ and $\log\log N>7$, so $U_k>1.05N>N+3X$ here as well. Consequently any finite multiplier improving the balanced bound has $\log_2 k>X/(2\log 2)>2^{1023}$. An implicit representation can describe such an integer with few symbols. The resulting evaluation cost depends on how the formula computes $\sigma(k)/k$ accurately.

## The lower limit and its precision

For each **fixed** $N>1$ one has the unconditional identity

$$ L_N:=\liminf_{\substack{k\to\infty\\(k,N)=1}}U_k(N)=\frac{N^2}{\varphi(N)}. $$

To see this, set $G(b)=\sigma(b)/(b\log\log b)$ for $b>e$. Grönwall proved $\limsup G(b)=e^\gamma$. If $(k,N)=1$, apply his bound to $kN^j$ with $j$ fixed. Multiplicativity and $\log\log(kN^j)/\log\log k\to1$ give $\limsup G(k)\le e^\gamma/(\sigma(N^j)/N^j)$ along the coprime inputs. As $j\to\infty$ the denominator tends to $N/\varphi(N)$. Conversely, take a sequence $n$ attaining Grönwall’s upper limit. Write $n=ab$ where $a$ contains exactly the prime-power factors supported on primes dividing $N$. Since $\sigma(a)/a\le N/\varphi(N)$ and $\sigma(n)/n\to\infty$, the coprime parts $b$ tend to infinity. Now $\log\log b\le\log\log n$ gives $G(b)\ge(\varphi(N)/N)G(n)$. This proves the matching lower bound. Taking reciprocals establishes the displayed identity. [Grönwall, original maximal-order theorem](https://www.jstor.org/stable/1988773)

One explicit sequence is $K_z=\operatorname{lcm}\{j\le z:(j,N)=1\}$. By Chebyshev’s bounds, $\log K_z=\Theta(z)$ for fixed $N$, since removing the finitely many prime-power contributions of primes dividing $N$ subtracts $O_N(\log z)$ from the logarithm of the full least common multiple. In the divisor-ratio product, each remaining prime $\ell\le z$ has exponent $a_\ell=\lfloor\log z/\log\ell\rfloor$. The sum of $\ell^{-a_\ell-1}$ is $O(z^{-1/2})$ by splitting at $\sqrt z$, so the product of $1-\ell^{-a_\ell-1}$ tends to one. Mertens’ product formula yields $\sigma(K_z)/K_z\sim e^\gamma (\varphi(N)/N)\log z$ and hence $U_{K_z}(N)\to L_N$. Constructing this sequence by checking individual integers through $p$ would already encounter a factor in a gcd. Convergence alone supplies no useful advance bound on the index needed for one-unit accuracy at 2,048 bits. [Mertens, 1874](https://doi.org/10.1515/crll.1874.78.46) · [Chebyshev-function bounds](https://doi.org/10.1215/ijm/1255631807)

For $9\le p<q\le2p$,

$$ L_N-\sigma(N)=\frac{p^2+q^2-1}{(p-1)(q-1)}\in(2,3). $$

The lower bound follows from $(p-q)^2+2p+2q-3>0$. For the upper bound, $3pq-p^2-q^2=p^2+(q-p)(2p-q)\ge p^2>3p+3q-4$. Thus $\lfloor L_N\rfloor=\sigma(N)+2$. Since $4\mid(p+1)(q+1)$, **every real $y$ satisfying $|y-L_N|\le1$ gives $\sigma(N)=4\lfloor y/4\rfloor$**. The factors are then the roots of $T^2-(\sigma(N)-N-1)T+N$. For example, $10403=101\cdot103$ has $L_N=108222409/10200$, and $y=10610$ recovers $\sigma(N)=10608$. Along the explicit coprime least common multiples, the rounded result therefore eventually stabilizes at the correct divisor sum. Trying the quadratic after each estimate and checking the candidate product supplies a stopping test. This reduces factoring to estimating the extremal constant. The elementary expression $N^2/\varphi(N)$ still contains the unknown totient. [Lean proof of precision and factor recovery](../PrimeFactors/RobinMultiplier.lean)

## The smallest multiplier giving unit accuracy

Using RH and Musin’s strong Ramanujan theorem gives a sharper asymptotic result. Uniformly for sufficiently large products of distinct primes $p<q\le2p$,

$$
U_k(N)>L_N\quad\text{for every }(k,N)=1,\qquad
\min_{\substack{(k,N)=1\\ |U_k(N)-L_N|\le1}}\log k
=\Theta\!\left(\frac{N^2}{(\log N)^2}\right).
$$

Thus the infimum over all positive coprime multipliers equals $L_N$, which no finite multiplier attains in this range. The minimum in the second formula measures the ordinary binary length up to a constant factor. This argument is a paper derivation that has not been peer reviewed or formalized here. Musin’s input theorem is published and has an unspecified cutoff. The numerical conclusion for 2,048 bits above uses the separate finite argument. [Musin, Theorem 1, Corollary 1 and equation (3)](https://amj.math.stonybrook.edu/pdf-Springer-final/020-0136.pdf)

Write $A(m)=\sigma(m)/m$, $D=N/\varphi(N)$, $s=\log N$, and $t=\log k$. For $t\le X/2$ the finite estimates above give $U_k>N+3X$ for all sufficiently large $N$, while $L_N<\sigma(N)+3\le N+4+(3/\sqrt2)X$. The gap is therefore of order at least $X$.

Suppose $t>X/2$ and put $j=\lfloor\sqrt t/(8s)\rfloor$. As $N$ tends to infinity, $j\ge1$ uniformly in this range. Musin proves $A(m)<e^\gamma\log\log m-1/\sqrt{\log m}$ for every sufficiently large integer $m$. Apply this at $m=kN^j$. Increasing the logarithm from $\log(t+s)$ to $\log(t+js)$ costs at most $e^\gamma js/t<1/(4\sqrt t)$ after multiplication by $e^\gamma$. Also $1/\sqrt{t+js}>3/(4\sqrt t)$ for large $t$. Using coprimality gives

$$ A(k)A(N^j)<e^\gamma\log(t+s)-1/(2\sqrt t). $$

We can replace $A(N^j)$ by $D$ while retaining half this margin. Indeed $A(N^j)=D(1-p^{-j-1})(1-q^{-j-1})$, $D\le9/4$ and $A(k)\le e^\gamma\log t$. Balance gives $\log p\ge s/3$ for $N\ge8$. Since $j+1>\sqrt t/(8s)$, the resulting error is $O(\log t\,e^{-\sqrt t/24})=o(t^{-1/2})$, with an absolute constant. Consequently $e^\gamma\log(t+s)-A(k)D>1/(4\sqrt t)$. Dividing by $A(k)$, which is $O(\log t)$, proves

$$ U_k-L_N\gg \frac{N}{\sqrt t\log t}. $$

In particular the difference is positive for every such $k$. If it is at most one then $\sqrt t\log t\gg N$. For $t<N^2$ use $\log t<2\log N$. For $t\ge N^2$ the claimed lower bound on $t$ already holds.

For the matching upper bound take $T=C N^2/s^2$ with a fixed sufficiently large $C$. Choose a colossally abundant integer $m$ with $T\le t'=\log m\le2T$. Such an integer exists for every large $T$. For consecutive colossally abundant integers $m_i$, Musin’s proof of Theorem 1 records $m_i/m_{i-1}\le P(m_i)^2$ and $P(m_i)\sim\log m_i$, where $P$ is the largest prime divisor. Thus $\log m_i-\log m_{i-1}=O(\log\log m_i)$ and consecutive **logarithms** have ratio tending to one. Musin’s equation (3), using Ramanujan’s estimates on these integers, gives $A(m)>e^\gamma\log t'-2/\sqrt{t'}$ for every sufficiently large such $m$. [Proof of Theorem 1 and the colossally abundant estimates](https://amj.math.stonybrook.edu/pdf-Springer-final/020-0136.pdf)

Remove from $m$ its part $b$ supported on $p,q$, leaving $k=m/b$ coprime to $N$. This operation can be performed by repeatedly dividing by $\gcd(m,N)$ and updating $m$ until that gcd is one. Since $A(b)\le D$, $A(k)=A(m)/A(b)$ and $k\le m$,

$$
U_k\le L_N\frac{e^\gamma\log(t'+s)}{e^\gamma\log t'-2/\sqrt{t'}}.
$$

The ratio exceeds one by $O((s/t'+1/\sqrt{t'})/\log t')$. Here $L_N=O(N)$ uniformly, so the excess above $L_N$ in this upper estimate is $O(1/\sqrt C)+o(1)$. The implied constant is independent of $N$ and $C\ge1$. Taking $C$ large gives $U_k\le L_N+1$, with $\log k\le2T$. This proves the claimed length bound. Locating or evaluating such a multiplier in a compressed representation is a separate computational question.
