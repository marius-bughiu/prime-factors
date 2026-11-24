# What the first quartic slope bit reveals

Let $N=pq$ be a product of distinct primes, both 1 modulo 4. Choose $d$ with Jacobi symbol $(d/N)=-1$. Exactly one of the two primes sees $d$ as a nonsquare. Call that prime $r$. The complete signed Jacobi sum is

$$
T_e(N)=\sum_{x=0}^{N-1}\left(\frac{x(x^2-e)}{N}\right).
$$

Write $A=T_1/4$ and $B=T_d/4$. Then $A$ is odd and the slope $s=BA^{-1}\bmod 2^k$ is defined. The direction theorem gives $A=hu$, $B=hv$, where $h,u$ are odd, $v$ is even and $u^2+v^2=r$. [Quartic direction](quartic-direction.md)

For $k\ge2$, the slope is **0 modulo 4 if $r\equiv1\pmod8$** and **2 modulo 4 if $r\equiv5\pmod8$**. Indeed, $u^2\equiv1\pmod8$, while $v^2\equiv0$ or $4\pmod8$ according as $v\equiv0$ or $2\pmod4$. Multiplying either even residue modulo 4 by an odd number preserves it. This also gives $T_d\equiv8\pmod{16}$ exactly when $r\equiv5\pmod8$. [Lean proof](../PrimeFactors/QuarticSlopeBit.lean)

## A public bit and a quadratic residuosity test

If $N\equiv5\pmod8$, the first integer with negative Jacobi symbol is $d=2$. Its nonsquare prime is the one congruent to 5 modulo 8, so the slope ends in the binary digits `10`. If $N\equiv1\pmod8$, both primes have the same residue modulo 8. The slope is then 0 modulo 4 exactly when 2 is a square modulo $N$, by the supplementary law for 2 and the Chinese remainder theorem.

More generally, suppose $p\equiv1\pmod8$ and $q\equiv5\pmod8$. For every Jacobi-negative $d$, $T_d\equiv8\pmod{16}$ exactly when $d$ is a nonsquare modulo $q$. Multiplication by 2 preserves the local square class at $p$ and flips it at $q$, so this is equivalent to $2d$ being a square modulo $N$. For any integer $a$ with Jacobi symbol $+1$, the choice $d=2a$ therefore gives the one-query equivalence

$$
a\text{ is a square modulo }N\quad\Longleftrightarrow\quad T_{2a}(N)\equiv8\pmod{16}.
$$

This identifies a specific computation required of any routine that could supply that trace bit for arbitrary Jacobi-positive $a$ on this prime class. The equivalence gives neither an evaluator nor a factoring lower bound. Goldwasser and Micali formulated the composite quadratic residuosity problem for a unit of Jacobi symbol $+1$. [Original paper, §4](https://people.csail.mit.edu/silvio/Selected%20Scientific%20Papers/Encryption/Probabilistic_Encryption.pdf)

Hittmeir gives another expression for exactly this decision. In this class $N\equiv5\pmod8$, so the power of two dividing $N-1$ is exactly four. His Theorem 6.2 gives $T_{2a}(N)\equiv8\pmod{16}$ precisely when the **rational eighth-power residue symbol** of $a^4$ at $N$ is $+1$. At $q\equiv5\pmod8$ every fourth power is already an eighth power. At $p\equiv1\pmod8$, $a^4$ is an eighth power exactly when $a$ is a square. This identifies a second route to the same bit. Computing that rational symbol efficiently from an unfactored $N$ is itself the missing step. [Hittmeir, Theorem 6.2 and definition of the symbol](https://arxiv.org/pdf/1604.07791#page=15)

## Which congruences can predict the bit?

Directly summing the Jacobi symbol at every $x\bmod N$, using the first $d\ge2$ of Jacobi symbol $-1$, gives the following values. The first pair shares $N\equiv761\pmod{1536}$ and gives opposite slope bits modulo 4. The second pair shares $N\equiv853\pmod{4096}$ on the $d=2$ branch and gives different slopes modulo 8. [Jacobi routine](../experiments/mixed_ratio_heights.py)

| $N$ | $d$ | $T_1$ | $T_d$ | $A$ | $B$ | $s\bmod32$ |
|---:|---:|---:|---:|---:|---:|---:|
| 33017 | 3 | 660 | −240 | 165 | −60 | 20 |
| 42233 | 3 | −572 | 440 | −143 | 110 | 14 |
| 66389 | 2 | −36 | 504 | −9 | 126 | 18 |
| 99157 | 2 | 1020 | 136 | 255 | 34 | 30 |

**For every fixed integer $M\ge1$, $N\bmod M$ fails to determine the slope modulo 4, even if $d=3$ and the bit length is given.** Set $K=\operatorname{lcm}(M,24)$. Choose a unit $C\bmod K$ that is 1 modulo the 2-power in $K$, −1 modulo its 3-power, and 1 modulo all remaining prime powers. For each $j\in\{1,5\}$, choose a unit $P_j\equiv j\pmod8$ modulo $K$ and set $Q_j=C/P_j\bmod K$. Both classes reduce to $j\pmod8$. The prime number theorem in arithmetic progressions supplies distinct primes in the classes $P_j,Q_j$ in the same interval $[2^m,1.1\cdot2^m]$ for every sufficiently large $m$. Both products have $2m+1$ bits and equal $C\bmod K$. In particular both are 17 modulo 24, giving Jacobi signs $+1,-1$ for 2 and 3. The two choices of $j$ force opposite slope bits. [Koukoulopoulos, prime number theorem for arithmetic progressions](https://www.cambridge.org/core/journals/compositio-mathematica/article/pretentious-multiplicative-functions-and-the-prime-number-theorem-for-arithmetic-progressions/9DBD8AD24A1E42CF6AC685EEE18628FF)

Any fixed number of trailing bits, or any fixed finite collection of congruences, is covered by a single $M$. One may also match the first $b$ bits for any fixed $b$. Replace $1.1$ by a fixed $1+\varepsilon$ with $(1+\varepsilon)^2<1+2^{1-b}$. Both products then start in binary with a 1 followed by $b-1$ zeros. The argument leaves open congruences chosen from the input and algorithms that use more of $N$.
