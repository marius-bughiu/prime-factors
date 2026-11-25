# Testing factor residues that have the same sum

For the 49-bit product $422240038488377$, seven stored powers of 2 and six table lookups tested **256 possible factor remainders together**. One block gave $16777259\cdot25167403$. Six more lookups against the same table excluded all 256 remainders in a second block. The example was constructed with its two primes congruent modulo 512. Large blocks require special congruences, and their combined coverage can be bounded using only the product.

## A public test for a block

Let $N=pq$ with distinct odd primes and $p<q\le2p$. Choose a radix $R=2^k$. An odd residue $u$ for a factor fixes its partner $v=Nu^{-1}\bmod R$. Group all residues with $u+v\equiv2h\pmod R$. For any unit $a\bmod N$ the true sum satisfies $a^{p+q}=a^{N+1}\bmod N$, since the exponents differ by $(p-1)(q-1)$. The admissible integer sums form the progression $L+Rj$ inside $[\lceil2\sqrt N\rceil,\lfloor3\sqrt{N/2}\rfloor]$, with $L$ the first sum congruent to $2h$. This applies Hittmeir’s hyperbolic sieve and discrete-logarithm search to the factor-remainder groups used in the repository. [Hittmeir, §§3, 6 and 7](https://arxiv.org/html/2205.10074v2) · [Earlier power-signature search](searching-the-balanced-interval.md) · [Lean block and collision proofs](../PrimeFactors/OrderLaneTests.lean)

If there are $J>0$ sums, choose $b=\lceil\sqrt J\rceil$. Store $(a^R)^j$ for $0\le j<b$. At giant index $i$, look up $a^{N+1}/[a^L(a^{Rb})^i]$. Each match supplies the index $bi+j$. Discard indices outside the interval and check the integer discriminant $S^2-4N$ and product at every remaining match. A missing match excludes every factor residue in the group. When baby powers are distinct, there is at most one match at each of $\lceil J/b\rceil$ probes. Distinctness is checked while building the table using public arithmetic, without either prime or an order oracle. If powers repeat, retain all matching indices to preserve coverage. The number of discriminant checks can then rise to $J$. Initial powers take $O(\log N)$ modular multiplications for the stated radix, and consecutive entries each take one multiplication. The table can be reused at other sum residues.

## How many factor residues share a sum?

For an odd $u$, multiplying the sum equation by $u$ and completing the square gives

$$
 u+Nu^{-1}\equiv2h\pmod{2^k}
 \quad\Longleftrightarrow\quad (u-h)^2\equiv D=h^2-N\pmod{2^k}.
$$

Every root gives an odd $u$, since $N$ is odd. The two choices of $h$ modulo $2^k$ representing the same sum produce the same congruence for $u$. If $R=m^2$ and $h^2\equiv N\pmod R$, the answer is exactly $u\equiv h\pmod m$. Thus a single sum covers exactly $m$ distinct remainders modulo $R$. This equivalence and count are proved in Lean for any square radix, with the usual unit hypothesis for cancellation. [Lean theorems](../PrimeFactors/OrderLaneTests.lean)

For a nonzero $D\bmod 2^k$ in an occupied group, write $v_2(D)=2t$. Dividing the square congruence by $2^{2t}$ leaves an odd square modulo $2^{k-2t}$. Each root has $2^t$ lifts for $u-h$ modulo $2^k$. An occupied odd square has one, two, or four roots as the exponent is one, two, or at least three. For the last count, all four odd classes modulo 8 square to one. At any subsequent step, pairing old roots that differ by half the old modulus pairs opposite next square bits. Two roots survive and each has two lifts. When $D=0\bmod 2^k$, its square roots are the multiples of $2^{\lceil k/2\rceil}$, giving $2^{\lfloor k/2\rfloor}$ roots.

The counts below concern **oriented** remainders $u$. For $k\ge5$, set $C_k(N)$ equal to the number of occupied sum residues.

| Public residue | Remainders per occupied sum | $C_k(N)$ |
| --- | --- | --- |
| $N\equiv3,7\pmod8$ | Exactly 4 | $2^{k-3}$ |
| $N\equiv5\pmod8$ | Exactly 8 | $2^{k-4}$ |
| $N\equiv1\pmod8$ | Depends on the sum | $4+\sum_{t=2}^{\lfloor(k-3)/2\rfloor}2^{k-2t-2}$ |

For the first row the two odd factors are opposite modulo 4. Their sum has even half $h$, and $u-h$ is odd. For the second row $u^2-N\equiv4\pmod8$ for every odd $u$. Since $u^2-N\equiv u(u-v)\pmod{2^k}$, we have $v_2(u-v)=2$ and $v_2(u-h)=1$. The root counts give the two uniform group sizes.

For the third row the congruence $u^2\equiv N\pmod{2^e}$ has exactly four roots for $3\le e\le k$. Therefore $4\cdot2^{k-e}$ remainders agree through bit precision $e$. Subtracting the next count gives $2^{k-t}$ remainders with $v_2(u^2-N)=t+1<k$. In this range $v_2(u-h)=t$, since $2(u-h)\equiv u-v\pmod{2^k}$. For $2\le t\le\lfloor(k-3)/2\rfloor$, each group has $2^{t+2}$ remainders. This gives the displayed summands. At the remaining levels write $k=2d$ or $2d+1$. If $k=2d$, the $2^{d+1}$ remainders at $t=d-1$ give two groups and the $2^{d+1}$ remainders with $2^{d+1}\mid u^2-N$ give two more. If $k=2d+1$, the $2^{d+1}$ remainders at $t=d$ give two groups and the $2^{d+1}$ remainders with $2^{d+2}\mid u^2-N$ give two more. The latter count in each case includes exact roots.

Bower, Evans, Luo and Miller proved the total image sizes in Theorem 3.3. Counting the number of factor remainders in each group gives the same totals and the power-of-two recurrence Hittmeir reported from computations in Remark 7.5, starting at $k=5$. His weighted sum $cu+v$ for odd $c$ has the same image as the ordinary sum at product $cN$, by replacing $u$ with $cu$. The distribution argument here is a paper proof. Direct enumeration agreed on all 1,008 odd product residues across $5\le k\le10$ and on the four representatives $1,3,5,7$ at each $11\le k\le17$. [Bower, Evans, Luo and Miller, Theorem 3.3](https://arxiv.org/pdf/1212.2930#page=5) · [Hittmeir, Remark 7.5](https://arxiv.org/html/2205.10074v2#S7)

## Coverage at 2,048 bits

If one occupied group contains at least $2^b$ remainders with $4\le b\le\lfloor k/2\rfloor$, each remainder in it satisfies $u^2\equiv N\pmod{2^{b-1}}$. Indeed, for a nonzero target the group size is at most $4\cdot2^t$, so $2^{b-2}\mid u-h$. For a zero target all roots satisfy the same divisibility. Multiplying $2(u-h)\equiv u-v$ by $u$ gives the claim. At most four classes at precision $b-1$ qualify. Even if **all** such large groups are chosen, they cover at most a fraction $2^{4-b}$ of the $2^{k-1}$ odd remainders. This deterministic bound counts possible residues for a fixed $N$. It assumes no probability distribution on the actual factor.

At $k=616$, a centered block contains $2^{308}$ remainders whenever $N\equiv1\pmod8$. On the 2,048-bit crossed benchmark the sum window and radix give approximately $2^{404.54}$ indices per block, hence about $2^{202.27}$ stored entries and as many probes. These are arithmetic size estimates. All groups containing at least $2^{204}$ remainders together cover at most $2^{-200}$ of the odd remainders. For three of the four possible odd product residues modulo 8, the table above limits each group to eight remainders. This leaves the general factor search open. [Quartic benchmark input](../benchmarks/quartic-factor-lanes.json)

## Reproducing the small example

Choose $p$ as the first prime above $2^{24}$, then $q$ as the first prime above $3p/2$ congruent to $p\pmod{512}$. This supplied the test product. Its search uses only $N=422240038488377$, $R=65536$ and $a=2$. The two distinct square-root centers modulo $R/2$ are 811 and 31,957. The sum ranges from 41,096,961 through 43,589,909.

| Center | First sum $L$ | Candidate sums | Baby entries | Probes | Matches $(i,j)$ |
| ---: | ---: | ---: | ---: | ---: | --- |
| 811 | 41,158,230 | 38 | 7 | 6 | $(1,5)$ |
| 31,957 | 41,154,986 | 38 | 7 reused | 6 | None |

For each row the baby entries are `pow(2, 65536*j, N)` for $0\le j<7$, and giant entries are `pow(2, N+1-L-65536*7*i, N)` for $0\le i<6$. The successful sum is 41,944,662. Its discriminant has square root 8,390,144. Lean independently checks the primes, their product, the two centers, the winning square and the modular square tests that reject every other index in both blocks. [Checked example](../PrimeFactors/OrderLaneTests.lean)
