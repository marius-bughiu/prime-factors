# Choosing a shift from the product

Let $N=pq$ for distinct primes $p<q\le2p$. A positive integer shift $k$ is useful when $(2p+k)(2q+k)=r^2$. If we find the integer $r$, exact division gives $S=p+q=(r^2-4N-k^2)/(2k)$. The roots of $X^2-SX+N$ then recover the factors.

## Two candidates for a prime shift

Set $m=\lceil\sqrt{4N}\rceil$. Lean proves
$$
m+k\le r\le m+k+\lfloor k/16\rfloor,\qquad r^2\equiv4N\pmod k.
$$
For the lower bound, $(2\sqrt N+k)^2\le4N+2kS+k^2$. For the upper bound, balance gives $S^2\le9N/2$, hence $16S\le17m$. Squaring $m+17k/16$ gives an upper bound for $r^2$. The interval has length less than $k$, even for shifts much larger than the factors. [Lean window and modular decoding](../PrimeFactors/ShiftParameter.lean)

For a supplied prime $k\equiv3\pmod4$, compute $z=(4N)^{(k+1)/4}\bmod k$ by repeated squaring. If a solution exists, $\pm z$ are all possible roots modulo $k$. For each sign, lift the residue to its first representative at or above $m+k$, check the upper endpoint and recover a candidate sum by the division above. Test its discriminant and the product before accepting. The two trials take polynomially many bit operations in $\log N+\log k$. For $N=96113$ and $k=10163$, the negative sign gives $r=10815$, $S=654$, and the primes 223 and 431. The Lean example checks the computation. [Decoder and example](../PrimeFactors/ShiftParameter.lean)

All square-producing shifts satisfy $(S+k-r)(S+k+r)=(q-p)^2$. For odd primes write $h=S/2$ and $g=(q-p)/2$. The shift $k=g^2+1-2h=(h-1)^2-N$ always gives the square $(g^2-1)^2$. It is positive for sufficiently separated pairs. Choosing it by this expression requires the unknown midpoint. [Gap identities](../PrimeFactors/ShiftParameter.lean)

## Multiples of the product

For a positive numerator $cN$ and denominator $d$, the cleared square root would have to be a multiple of $N$, since its square is divisible by both distinct primes. It lies strictly above $cN$ and at most $cN+d(p+q)$. This is impossible when $d(p+q)<N$. In particular every positive integer multiple of $N$ fails. Taking $d=\lceil\sqrt N\rceil$ also fails on the balanced domain of the Lean theorem. Taking $d=\lfloor\sqrt N\rfloor$ forces $p+q\le 2\lfloor\sqrt N\rfloor+8$ there, so a few ordinary Fermat midpoints already suffice. [Exact range hypotheses and proofs](../PrimeFactors/MultipleShift.lean)

## A limit on fixed rational functions

Fix any finite list of rational functions $A_i(T)/B_i(T)$ with integer coefficients and nonzero denominators. A positive proportion of balanced prime pairs in $[X,2X]$ evade **every** shift on the list as $X\to\infty$, regardless of how large its values are. A zero shift always gives $4N$, a nonsquare on distinct prime pairs.

Choose a positive nonsquare $n_0$ away from the zeros of all nonzero numerators and denominators. For each remaining function write $A=A_i(n_0)$ and $B=B_i(n_0)$. Then $A^2-4n_0B^2\ne0$. Choose a different odd prime $\ell$ for each function, avoiding the divisors of $n_0AB(A^2-4n_0B^2)$. Impose the following unit residue classes modulo $\ell^2$:
$$
p\equiv(\ell-A)(2B)^{-1},\qquad q\equiv n_0p^{-1}.
$$
Then $N\equiv n_0\pmod{\ell^2}$ fixes both polynomial values. The integer $2B_i(N)p+A_i(N)$ is divisible by $\ell$ exactly once. If the complementary factor were also divisible by $\ell$, their congruences would imply $A^2\equiv4n_0B^2\pmod\ell$, excluded by construction. Their product therefore has odd valuation at $\ell$ and cannot be a square. Clearing the shift denominator multiplies its shifted product by $B_i(N)^2$ and preserves this obstruction. [Lean local certificate](../PrimeFactors/ShiftParameter.lean)

The Chinese remainder theorem combines these requirements into one reduced residue class for each prime modulo a fixed integer $M$. The prime number theorem in arithmetic progressions supplies order $X/(\varphi(M)\log X)$ primes from the first class in $[X,5X/4]$ and from the second in $[3X/2,7X/4]$. Every such pair is balanced and defeats the list. This density deduction is on paper. [Proof of the prime number theorem in progressions](https://academic.csuohio.edu/soprunov-ivan/wp-content/uploads/sites/93/2023/02/primes.pdf)

A separate unconditional counting bound shows that even much longer prescribed lists miss almost every pair of balanced primes, under polynomial degree and coefficient-length bounds. [Large-sieve proof](large-sieve-for-shifts.md)

## Portfolios that grow with the bit width

**Paper deduction using Dirichlet GRH.** At factor width $b$, prescribe $m=o(b/\log b)$ nonzero rational functions $A_i(N)/B_i(N)$ with integer polynomial numerators and denominators. Assume a fixed polynomial in $b$ bounds their degrees and the bit lengths of their coefficients. For every sufficiently large $b$ there are $2^{2b-o(b)}$ different products of balanced $b$-bit primes, themselves exactly $2b$ bits, for which **all** these shifts fail. The list may depend on $b$, and a search can choose among its entries after inspecting $N$. This covers only the specified rational functions. Digit operations, integer square roots and arbitrary programs for choosing shifts can use information outside this class.

1. Choose $n_0=t^2+1$ with $t\ge1$ avoiding all roots of all $A_i,B_i$. A polynomial has at most its degree in distinct integer roots, so $n_0\le b^{O(1)}$ suffices. It is nonsquare. Consequently every integer $J_i=2n_0 A_i(n_0)B_i(n_0)(A_i(n_0)^2-4n_0 B_i(n_0)^2)$ is nonzero and has at most $b^{O(1)}$ bits, by the degree and coefficient bounds.
2. Choose distinct odd primes $\ell_i\le b^C$ that do not divide their respective $J_i$, with a fixed sufficiently large $C$. Each $J_i$ has no more distinct prime divisors than its bit length. The prime number theorem therefore supplies enough choices after previously used primes are excluded. With $M=\prod_i\ell_i^2$ we have $\log M=O(m\log b)=o(b)$.
3. Write $A=A_i(n_0)$, $B=B_i(n_0)$. For $p$ choose the unit class $(\ell_i-A)/(2B)$ modulo $\ell_i^2$. For $q$ choose $n_0/p$ in the same ring. The Chinese remainder theorem gives two unit classes modulo $M$. For any pair in these classes, $N\equiv n_0\pmod{\ell_i^2}$, so the first cleared shifted factor is $\ell_i\bmod \ell_i^2$. Its companion is nonzero modulo $\ell_i$ by the condition on $A^2-4n_0B^2$. Thus an odd valuation prevents a rational square.
4. Put $X=2^b$. Choose $p$ in $[0.75X,0.80X]$ and $q$ in $[0.90X,0.95X]$. For either unit class the prime count in that interval has main term of order $X/(\varphi(M)\log X)$ and error $O(\sqrt X\log(MX))$. This follows by character orthogonality and the uniform GRH estimate for every nonprincipal character modulo $M$. The principal term uses the prime number theorem, omitting the primes dividing $M$. Since $M=2^{o(b)}$, each class contains $2^{b-o(b)}$ primes. Multiplication is injective on these ordered pairs. Their factors are balanced and $X^2/2<N<X^2$. This establishes the claimed count. The asymptotic allows the fraction of failing inputs to tend to zero. [Uniform character sum, Lemma 4.1](https://arxiv.org/pdf/2611.19610#page=5) · [Scope of the Dirichlet statements](../docs/research.md)

**A finite example.** Take the shifts $1,N+1,N^2+N+1,(N^2+1)/2,(N+1)/(N+3)$ and $n_0=2$. The table shows the classes obtained by the construction.

| Shift | Obstructing prime $\ell$ | $p\bmod\ell^2$ | $q\bmod\ell^2$ |
| --- | ---: | ---: | ---: |
| $1$ | 3 | 1 | 2 |
| $N+1$ | 5 | 1 | 2 |
| $N^2+N+1$ | 11 | 2 | 1 |
| $(N^2+1)/2$ | 13 | 2 | 1 |
| $(N+1)/(N+3)$ | 17 | 117 | 84 |

One balanced pair in these classes is $p=32433156901$, $q=34543964027$. Its product is $1120369805270190800327$. Lean checks that all five cleared products are nonsquares. [Finite obstruction certificate](../PrimeFactors/ShiftPortfolio.lean)
