# One degree chosen from the product gives a factor

For $493$, take the largest even integer at or below $\sqrt{493}$, which is 22. The complete Jacobi sum at that degree is 326 modulo 493. Subtract the middle entry of row 22 of Pascal’s triangle, 705,432. The difference is 377 modulo 493, and $\gcd(377,493)=29$. Both the choice of degree and the calculation use only 493. The middle entry alone also gives the other prime, since $\gcd(705432,493)=17$. [Lean proof](../PrimeFactors/JacobiMiddleDegree.lean) · [Four controls](../benchmarks/jacobi-middle-degree.json)

## Why that degree works

Let $N=pq$, where $p<q<2p$ are distinct odd primes. Put $k=2\lfloor\sqrt N/2\rfloor$, $C_k=\binom{k}{k/2}$ and $M_k=\sum_{x\bmod N} x^k(\frac{x^2-4}{N})\pmod N$, with the Jacobi symbol in parentheses. Then $p-1\le k<q-1$. Modulo $q$, $M_k$ still equals $C_k$. Modulo $p$, at $k=p-1$ the two values differ by one. At every later even degree in this interval, $C_k$ is divisible by $p$ and the moment agrees with a smaller, nonzero coefficient modulo $p$. Thus $\gcd(N,M_k-C_k)=q$ throughout the interval. Choosing $k$ from the product avoids having to search for the first degree where this happens. [Interval theorem and public degree](../PrimeFactors/JacobiMiddleDegree.lean) · [Earlier first-exception result](when-jacobi-moments-first-change.md)

The lower endpoint occurs exactly for twin primes, detected by $N+1$ being a square. Otherwise the ordinary coefficient already has gcd $p$. This is an instance of classical binomial divisibility. The numerator of $\binom{2h}{h}$ contains a multiple of each prime in $(h,2h]$, and the denominator contains none. [Erdős, 1932, §1](https://users.renyi.hu/~p_erdos/1932-01.pdf#page=2) · [Repository’s earlier Pascal-row result](a-shorter-pascal-row-for-equal-width-primes.md)

## Can the coefficient be removed?

Put $j=k/2$. For $p\ge7$ and $q-p\ge6$, the weighted difference

$$D=(j+1)M_{2j+2}-(4j+2)M_{2j}$$

has $\gcd(D,N)=q$. Modulo $q$ the two moments obey the ordinary recurrence between consecutive middle binomial coefficients. Modulo $p$ the index has passed its first repeat, so the same two weights leave a nonzero remainder. At gaps two and four, respectively, $N+1$ and $N+4$ are squares. Both moments in $D$ can be combined in a single sum with the same signs. [Weighted identity and gap cases](../PrimeFactors/JacobiWeightedMiddle.lean)

For $2{,}627=37\times71$ the weighted sum gave 355 and $\gcd(355,2627)=71$. It used 2,627 signs and 2,414 modular powers. Computing the two moments separately with the same zero terms skipped takes 4,828 powers. During the direct scan the sign at $x=35$ already exposed the factor 37. Ordinary Fermat search found 37 in three square tests, and the 47-bit middle binomial coefficient also had gcd 37. The comparison used the same product for each method. [Measured operations](../benchmarks/jacobi-weighted-middle.json) · [Bounded evaluator](../experiments/jacobi_weighted_middle.py)

The early factor in the scan is predictable for every $7\le p<q$. From $x=3$ through $p-3$, both $x-2$ and $x+2$ are positive and below $p$. At $x=p-2$, the second term becomes $p$ and $\gcd((x-2)(x+2),N)=p$. Lean proves that this is the first proper gcd on the increasing scan starting at 3. The conclusion concerns this direct way of obtaining the signs. [Lean first-gcd proof](../PrimeFactors/JacobiMiddleDegree.lean)

## Cost at 2,048 bits

A literal complete sum visits $N$ residues. A literal middle binomial coefficient needs more than $\lfloor\sqrt N/2\rfloor$ bits for these inputs. Only its residue is needed by the formula, so this storage bound applies to constructing the exact integer. A useful comparison is $\gcd(\lfloor\sqrt N\rfloor!,N)=p$, since $p\le\lfloor\sqrt N\rfloor<q$. The factorial method also has a single final gcd. Published product batching locates a prime divisor below $b$ using a block size on the order of $\sqrt b$. Taking $b=\lfloor\sqrt N\rfloor$ gives a block size on the order of $2^{512}$ at 2,048 bits. The missing step for the new identities is a less expensive way to evaluate the required residue directly from the product. [Lean coefficient-size bound](../PrimeFactors/JacobiMiddleDegree.lean) · [Bostan, Gaudry and Schost, Lemma 13](https://specfun.inria.fr/bostan/publications/BoGaSc07.pdf#page=15)
