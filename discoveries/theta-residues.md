# Reading a prime factor from a partition series

For an odd product $N=pq$ of distinct primes, a public quadratic character can select exactly one of the hidden primes. On the small example $667$, the coefficients of a classical partition series give $5$ as the remainder of that prime on division by $8$. The first two candidates in the balanced interval are $21$ and $29$, and $29$ divides $667$. Computing the coefficient took 222,111 convolution terms. The cost of obtaining such a residue at a 2,048-bit index remains open.

## The coefficient that selects a prime

Choose a prime $\ell\equiv1\pmod4$ with $\eta(N)=-1$, where $\eta(d)=(d/\ell)$ is its quadratic character. This condition is testable from $N$. Define the formal power series
$$
G_\ell(x)=\prod_{\eta(d)=1,\ d\ge1}(1-x^d)^{-1},\qquad
A_\ell(x)=\frac{xG_\ell'(x)}{G_\ell(x)}.
$$
Logarithmic differentiation gives $[x^N]A_\ell=\sum_{d\mid N,\ \eta(d)=1}d$. Multiplicativity makes the signs of $p$ and $q$ opposite. Exactly two divisors have positive sign, namely $1$ and the prime $r$ selected by the character. Thus **the coefficient is $1+r$**. Lean checks this divisor identity for every integer-valued multiplicative character with the stated public sign. If both signs are negative, the same coefficient is $1+N$, as happens at $91=7\cdot13$ for $\ell=5$. [Lean proof](../PrimeFactors/ThetaResidues.lean)

The same coefficient has a modular-form expression at odd indices coprime to $\ell$. Jacobi's four-square identity gives $[x^N]\theta^4/8=\sum_{d\mid N}d$. The weight-two Eisenstein series $E_{2,1,\eta}$ has coefficient $\sum_{d\mid N}\eta(d)d$. Averaging the two coefficients keeps precisely the positive class. The modular-form and power-series identities here are paper arguments. [Jacobi's four-square identity](https://dlmf.nist.gov/27.13.iv) · [Eisenstein coefficient formula and Theorem 5.8](https://wstein.org/books/modform/modform/eisenstein.html#explicit-basis-for-the-eisenstein-subspace)

For $k=\lceil\operatorname{bitlength}(N)/4\rceil$, the word $b=([x^N]A_\ell/2)\bmod 2^{k-1}$ gives $r\equiv2b-1\pmod{2^k}$. The coefficient is even at this input, so integer division after reduction modulo $2^k$ yields the same word. Lean proves that two odd candidate primes have the same word exactly when their residues modulo $2^k$ agree. Since each prime is odd, $N r^{-1}\bmod 2^k$ gives the other prime's residue. The known-low-bits theorem can then be applied to the larger prime, trying both residues. For a balanced 2,048-bit product this reduces recovery to obtaining one **511-bit word**, with polynomial-time lattice postprocessing on paper. [Small-root statement and decoding](quarter-width-count.md#why-the-residue-suffices)

The Dirichlet GRH connection concerns the choice of $\ell$. The residue modulo four and the Jacobi symbol $(\cdot/N)$ give two independent signs on the units modulo $4N$, by the Chinese remainder theorem. The common kernel has index four. The signs $1,-1$ specify one of its cosets. Every prime there has $(N/\ell)=(\ell/N)=-1$ by reciprocity. For $4N\ge20000$, Theorem 1.4 of Lamzouri, Li and Soundararajan bounds the smallest such prime by
$$
\max\bigl(10^9, (3\log(4N)+15+\tfrac52(\log\log(4N))^2)^2\bigr).
$$
At 2,048 bits this bound is one billion. It controls the search for a character. Evaluating the coefficient after choosing that character is a separate computation. [Theorem 1.4](https://arxiv.org/html/1309.3595v3#S1.SS2) · [Dirichlet theorems verified in the RH repository](https://math.mit.edu/~drew/grh/)

## An independent coefficient calculation at level five

For $\ell=5$ the positive classes are $1,4\bmod5$. The first Rogers–Ramanujan identity gives a way to compute $G_5$ without knowing divisors of the input.
$$
G_5(x)=1+\sum_{j\ge1}\frac{x^{j^2}}{(1-x)(1-x^2)\cdots(1-x^j)}.
$$
The experiment expands this sum using restricted partition counts modulo $2^k$, then solves $G_5 A_5=xG_5'$ coefficient by coefficient. Only after reading the residue does it test divisibility in the balanced interval $[\sqrt{N/2},\sqrt{2N}]$. [Rogers–Ramanujan identity](https://dlmf.nist.gov/17.2.E49) · [Implementation](../experiments/theta_residues.py) · [Benchmark fixtures](../benchmarks/theta-residues.json)

| Product | Modulus | Coefficient residue | Selected prime residue | Factor found | Convolution terms |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 143 | 4 | 0 | 3 | 11 | 10,153 |
| 667 | 8 | 6 | 5 | 29 | 222,111 |
| 1,457 | 8 | 0 | 7 | 31 | 1,060,696 |
| 1,537 | 8 | 6 | 5 | 29 | 1,180,416 |

The last two products each have eleven bits and both are $17\bmod40$. Their different factor residues disprove the proposed shortcut of reading this coefficient directly from the public residue modulo $5\cdot2^k$. For the unbalanced $57=3\cdot19$, the experiment gets $19\bmod4$ correctly and exhausts the balanced interval. Its 2,048-bit input passes the sign check and exceeds the index cap of 1,537, leaving the whole input unresolved. The dense division takes $N(N-1)/2$ convolution terms and $O(N)$ coefficient slots. A faster way to get just the selected coefficient, with cost measured in the bit length of $N$, would be needed to turn this identity into a practical improvement.
