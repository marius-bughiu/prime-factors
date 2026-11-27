# What can a Gaussian binomial coefficient reveal about an unknown prime?

Suppose the input is only $N=pq$, where $p<q\le 2p$ are distinct odd primes. Choose an integer base $g$ coprime to $N$. **If a Gaussian binomial coefficient in row $N$ at index $k<p$ reveals a factor, one of at most $2k$ ordinary gcd tests with the same base also reveals a factor.** Equal multiplicative orders of $g$ at the two primes prevent every coefficient in that range from splitting the product. These results apply to the entire balanced family, including 2,048-bit products. [Checked classification and elementary witnesses](../PrimeFactors/GaussianOrderRows.lean)

## What the coefficient measures

Use the coefficient $C_k$ of $X^k$ in

$$
F_N(X)=\prod_{i=0}^{N-1}(1-g^iX).
$$

The finite Gaussian binomial theorem gives $C_k=(-1)^k g^{k(k-1)/2}{N\brack k}_g$. The sign and the power of $g$ are units modulo $N$, so the gcd is the same for both coefficients. The polynomial product makes sense even when a quotient formula would require dividing by a zero divisor. Grouping a product into cycles at a root of unity is the mechanism behind the classical $q$-Lucas congruence. [Zudilin, *Congruences for q-Binomial Coefficients*](https://doi.org/10.1007/s00026-019-00461-8) · [Project's earlier coefficient recurrence](../PrimeFactors/ReflectedGeometricBlocks.lean)

Let $d$ be the multiplicative order of $g$ modulo $p$. For $0\le k<p$, the complete criterion is

| Local order | When $C_k$ is nonzero modulo $p$ |
|---|---|
| $d=1$ | $k=0$ |
| $d>1$ | $k\bmod d\le N\bmod d$ |

The same table holds at $q$. A split occurs precisely when the two answers differ. For example, the unknown orders being equal makes the answers identical at every index. Computing the orders from the product would itself require work. [Integer gcd theorem](../PrimeFactors/GaussianOrderRows.lean)

To see the table, write $p=da+1$, $q=db+t$ with $0\le t<d$. Balance and odd primality imply that neither prime divides the other's predecessor. Since $d$ divides $p-1$, this gives $t>0$ for $d>1$. A full orbit of the base contributes $1-X^d$. Since $pq=d(ta+pb)+t$, the product modulo $p$ is $(1-X^d)^{ta+pb}F_t(X)$. Every coefficient through degree $t$ in the short final block is nonzero. Its higher coefficients are zero. At degree $k$ only the term of degree $k\bmod d$ in this block can contribute. The other factor supplies, up to sign, the ordinary binomial coefficient $\binom{ta+pb}{\lfloor k/d\rfloor}$. Lucas's theorem reduces it modulo $p$ to $\binom{ta}{\lfloor k/d\rfloor}$. Here $\lfloor k/d\rfloor\le a\le ta<p$, so it is nonzero. Finally $t=N\bmod d$. For $d=1$, the polynomial reduces to $(1-X^p)^q$ modulo $p$. [Formal proof](../PrimeFactors/GaussianOrderRows.lean)

## The public comparison

The two families of integers whose gcds can be checked are

$$
g^i-1\quad(1\le i\le k),\qquad g^N-g^j\quad(0\le j<k).
$$

A prime divides the first expression exactly when its local order divides $i$. If the two orders differ and the smaller is at most $k$, the expression at the smaller order separates them. If both orders exceed $k$, the first family finds nothing. In that case the coefficient vanishes at a prime precisely when the remainder of $N$ modulo its order is less than $k$. That remainder gives the index $j$ of a match in the second family. Different coefficient outcomes therefore guarantee a proper gcd in one of the two families. The converse can fail for a particular coefficient. [Elementary witness theorem](../PrimeFactors/GaussianOrderRows.lean)

A direct scan computes $g^N\bmod N$ once by repeated squaring, generates $1,g,\ldots,g^k\bmod N$ successively and uses at most $2k$ gcds. It needs no factor, local order, or list of primes. Grouping many terms into a product can reduce the number of gcds. A batch whose gcd is $N$ may need subdivision because its two primes can occur in different terms. Bostan and Yurkevich give faster methods for evaluating long geometric products using polynomial multiplication and multipoint evaluation. The theorem compares which inputs can yield a split. An evaluator with a lower total cost than the elementary search could still be valuable, and arithmetic over the composite modulus must account for failed inversions. [Bostan and Yurkevich, *Fast Computation of the N-th Term of a q-Holonomic Sequence and Applications*](https://arxiv.org/abs/2012.08656)

## Two products

For $143=11\times13$, base 2 has orders 10 and 12. At $k=4$, the two comparisons are $4>143\bmod10=3$ and $4\le143\bmod12=11$. Direct multiplication modulo 143 gives $C_4=22\bmod143$ and hence gcd 11. The elementary scan sees $2^{143}\equiv85$ and $2^3\equiv8\pmod{143}$, with $\gcd(85-8,143)=11$. For $91=7\times13$, base 9 has order three at both primes. The seven gcds for $k=0,\ldots,6$ are $1,1,91,1,1,91,1$. Lean checks the 143 split for both methods and proves that all seven indices on 91 give a trivial gcd. [Checked examples](../PrimeFactors/GaussianOrderRows.lean)
