# How often can polynomial division expose a factor by accident?

For the repository’s opposite-label search on a product of two distinct 1024-bit primes, the chance of finding an extra factor by an intermediate division step is **less than one in $2^{995}$ at 512 independent uniform draws**. Even a trillion draws put the chance below **one in $2^{902}$**. These bounds hold for each fixed eligible product, with randomness only in the inputs to the search. They also count every input rejected by the initial regularity mask. The earlier search found 13 extra factors in a census of small products. The size of the hidden primes makes this particular source of factors much rarer. [Checked 512-draw and trillion-draw bounds](../PrimeFactors/OppositePivotBudget.lean) · [Earlier census and timings](checking-opposite-keys-with-one-polynomial.md)

## Which division step exposed 3,947?

For $N=8{,}458{,}421$, the published seed 6703207913402786163 gives twelve regular labels. No two labels sum to one at either prime, including a label paired with itself. Euclidean division still exposes 3,947. To see where, center the twelve labels as $t_i=2v_i-1$ and write $F(X)=\prod_i(X-t_i)=X^{12}+c_1X^{11}+\cdots+c_{12}$. Put $c_0=1$ and use zero for coefficients outside the range $0$ through $12$. For each $k$, let $\Delta_k$ be the determinant of the $k$ by $k$ matrix with entry $c_{2j-i}$ in one-based row $i$, column $j$. Substitution of this word gives the following residues. [Replay seed, checked factors and comparison](../research/opposite-key-comparison.json)

| $k$ | $\Delta_k\bmod 2{,}143$ | $\Delta_k\bmod 3{,}947$ |
| ---: | ---: | ---: |
| 1 | 1,264 | 3,314 |
| 3 | 873 | 3,150 |
| 5 | 919 | **0** |
| 7 | 379 | 2,301 |
| 9 | 1,402 | 1,057 |
| 11 | 743 | 3,566 |

The fifth determinant vanishes at exactly one prime. At that step the remainder loses its expected degree modulo 3,947, so its nominal leading coefficient exposes that prime by a gcd with $N$. The last determinant is the resultant up to sign. Its two nonzero residues confirm the absence of a common polynomial factor in either prime field.

## Which determinants can cause an incidental split?

The search takes the public polynomial $F(X)=E(X^2)+X O(X^2)$ and divides its even and odd parts modulo $N$. It first checks the constant term for a zero root. With nonzero roots, an opposite pair at a prime is equivalent to a common nonconstant divisor of $E$ and $O$ over that field. While the leading coefficient of each divisor is a unit modulo $N$, division reduces to the ordinary field computation at both primes. An incidental split requires a loss of expected degree at one prime, prior to the final common-divisor test. For the implemented search, $N$ is 5 or 7 modulo 12 and both primes exceed 864. [Field equivalence](../PrimeFactors/OppositeKeyPolynomial.lean) · [Division trace](../PrimeFactors/OppositeKeyDivision.lean) · [Search implementation](../experiments/opposite_key_polynomial.py)

The intermediate indices for $m$ roots are

$$
I_m=\{k:1\le k<m-1,\quad k\not\equiv m\pmod 2\}.
$$

For $m=2n$, $E$ is monic of degree $n$ and $O$ has nominal degree $n-1$. Its expected leading coefficient is $\Delta_1=c_1$. Once that is nonzero, the $d$th principal subresultant coefficient is, up to row order and sign, $\Delta_{m-1-2d}$. Indeed, its leading square coefficient matrix takes $n-1-d$ shifted copies of $E$ and $n-d$ shifted copies of $O$. Interleaving them, starting with $O$, gives exactly $c_{2j-i}$. For $d=0$ this is the resultant. For positive $d$, a nonzero principal coefficient ensures the expected degree at that index in the Euclidean remainder sequence. This last implication is the classical subresultant theorem. [Brown and Traub, determinant definition on p. 508 and Fundamental Theorem on p. 511](https://iiif.library.cmu.edu/file/Traub_box00027_fld00059_bdl0001_doc0001/Traub_box00027_fld00059_bdl0001_doc0001.pdf)

For $m=2n+1$, $O$ is monic of degree $n$, and $E$ has nominal degree $n$. The interleaving now starts with $E$ and takes $n-d$ rows of each polynomial. Subtract $c_1O$ from $E$ in each of its rows. The new polynomial $C=E-c_1O$ has degree at most $n-1$, and its coefficient at degree $n-1$ is $c_3-c_1c_2=-\Delta_2$. When this is nonzero, expansion down the first column deletes the sole leading 1 of $O$ and gives the ordinary principal subresultant matrix of $(O,C)$ up to row order and sign. This handles $c_1=0$ too. If every intermediate determinant is nonzero at both primes, all degree drops take their expected sizes. A zero final resultant then requires a common divisor. For $m\le3$ there are no intermediate determinants.

## Counting the possible zeros

Each $c_j$ is $(-1)^j$ times the $j$th elementary symmetric polynomial in the roots. The alternating signs only multiply rows of the determinant by units. For any $k<m$, leave $c_0$ and $c_{2\lfloor k/2\rfloor+1}$ equal to one and set all other coefficients to zero. The resulting matrix has one 1 in each row and column, so its determinant is a unit in every characteristic. The elementary symmetric polynomials are algebraically independent, which carries nonvanishing from formal coefficients to the polynomial in the roots. Specializing the coefficients in this argument need not yield a split polynomial in the prime field. Algebraic independence is precisely what allows us to use the resulting nonzero polynomial in the root variables. [Characteristic-free witness and passage to root variables](../PrimeFactors/OppositePivotBudget.lean)

Each nonzero determinant term uses coefficient indices whose sum is $\sum_{i=1}^k (2\sigma(i)-i)=k(k+1)/2$. Thus the product of intermediate determinants has total degree at most

$$
D_m=\sum_{k\in I_m}\frac{k(k+1)}2\le\frac{m^3}{12}.
$$

For $m=2n$ with $n\ge1$, $D_m=n(n-1)(4n-5)/6$. For $m=2n+1$ with $n\ge1$, it is $n(n-1)(4n+1)/6$. At 512 draws there are 255 intermediate minors and $D_{512}=11{,}086{,}720$. The determinants are a counting device. The Euclidean search performs ordinary modular divisions and gcds without constructing these matrices. [Degree proofs and closed forms](../PrimeFactors/OppositePivotBudget.lean)

At a prime $r$, each regular centered label has twelve preimages, and there are $s_r=\lfloor(r-5)/12\rfloor$ distinct such labels. Independent uniform raw draws conditioned on regularity therefore give independent uniform labels. Schwartz–Zippel bounds the chance of a zero of the determinant product by $D_m/s_r$. On unrestricted draws, include $13m/r$ for an exceptional input. Adding the two prime bounds gives

$$
\frac{13m}{p}+\frac{D_m}{s_p}+\frac{13m}{q}+\frac{D_m}{s_q}.
$$

Substituting $p,q\ge2^{1023}$ gives the two headline limits. The counted event is an upper bound for an intermediate split without a complementary pair. No conditioning on the absence of a pair is needed. The calculation applies to independent random residues sampled with replacement and makes no prediction for adaptively designed batches. The benchmarks use a fixed pseudorandom seed to replay individual examples. [Finite label distribution and Schwartz–Zippel bound](../PrimeFactors/LabelPolynomialBudget.lean)

Lean checks the signed root-polynomial determinants, their nonvanishing and degree budgets, and the probabilities that a mask or determinant vanishes. The passage from a division in the Python implementation to a principal subresultant uses the classical proof above. Testing opposite pairs themselves has a separate probability analysis. [Euclidean implementation](../experiments/opposite_key_polynomial.py) · [Complementary pair analysis](comparing-complementary-labels-at-the-same-budget.md)
