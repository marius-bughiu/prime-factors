# How many shared yes-or-no tests isolate the correct midpoint?

Suppose someone hands us just a 2048-bit product of two distinct 1024-bit primes. We can draw **1,040 random integers** and use each as a yes-or-no test on a proposed factor midpoint. The true midpoint passes every test. With probability exceeding **99.9999%**, every wrong midpoint fails at least one. After only **998** such tests, at least **500,000 wrong midpoints in our chosen search interval** still pass with probability exceeding **99.999%**. These statements hold for every product of the specified kind. The only randomness is ours. Each random integer takes 2,202 bits.

A single integer square root already verifies any proposed midpoint exactly. The reason to study shared checks is the possibility of applying one to a whole group of guesses cheaply. On a 41-bit example, these checks reduced 41,807 possible midpoints to one. To do so, the implementation visited all 41,807 and performed 83,649 sign evaluations. Testing a square directly at every midpoint was faster. The open algorithmic problem is to find the sole survivor without this scan. [Measured example](../benchmarks/midpoint-readings.json) · [Product-only experiment](../experiments/midpoint_readings.py)

## A test shared by all guesses

Write $N=pq$, $p<q\le2p$. The midpoint $h=(p+q)/2$ is the unique integer in $[\sqrt N,\sqrt{9N/8}]$ for which $D_h=h^2-N$ is a square. Restrict to $h\equiv(N+1)/2\pmod2$, because $(p-1)(q-1)$ is divisible by four. Each integer in this interval has $D_h>0$ for nonsquare $N$.

Choose a seed $a$ uniformly in $1,\ldots,2^K$. Remove from $a$ all prime powers whose primes divide $2D$, leaving an odd denominator $a_D$ coprime to $D$. Repeatedly divide by $\gcd(a,2D)$ until that gcd is one. This needs no factorization of either integer. The test sign is
$$F_a(D)=\left(\frac{D}{a_D}\right),$$
the Jacobi symbol, with value one at denominator one. Positive squares always give $+1$. For a nonsquare $D$ the two signs are nearly equiprobable. Two nonsquares of distinct squarefree parts have nearly independent signs on the **same** seed. At the indicated bit widths, each joint sign probability differs from $1/4$ by at most $2^{-40}$. The corresponding single-sign probability differs from $1/2$ by at most $2^{-40}$. The seed analysis gives the unconditional bounds and their constants. [Seed length and character estimates](jacobi-seed-length.md) · [Exact finite character balance and square preservation in Lean](../PrimeFactors/JacobiReadings.lean)

For perspective, write each seed as $a=su$, where $s$ contains exactly the prime powers of $a$ supported on the primes of $2DE$ and $u$ is coprime to $2DE$. At a fixed $s$, each sign is a constant times a quadratic character of $u$ on the units modulo $8DE$. The product character is nonprincipal if $DE$ is nonsquare. Squarefree parts being distinct gives precisely this condition. Orthogonality balances the four signs over a full unit group. Bounding incomplete sums and then summing over $s$ gives the finite estimate. When two distinct values have the same squarefree part, stripping can still produce different signs. We account for those pairs separately.

Earlier work used the released Dirichlet hypothesis to select tests at small primes. Those prime tests depend only on the midpoint residue modulo the testing prime and support a CRT sieve. The present larger seeds give an unconditional threshold using Jacobi signs. Stripping depends on the individual discriminant. No comparable small lookup table for a block of midpoints follows from the sign formula. [Earlier prime tests and their assumptions](character-conjectures.md#how-many-primes-suffice-for-all-discriminants)

## Why exceptional correlations cannot dominate

**Each positive square class occurs at most twice in the entire balanced interval.** In other words, for fixed $d\ge1$, there are at most two distinct $h$ for which $h^2=N+d z^2$ with positive integer $z$ and $8h^2\le9N$. The class $d$ can even share a prime with $N$. [Lean proof](../PrimeFactors/MidpointClasses.lean)

For each solution, $z$ is invertible modulo both $p$ and $q$. If either prime divided $z$, it would divide $h$ as well and its square would divide $N$. The ratios $h/z$ modulo each prime square to $d$, so each ratio has at most two choices, differing by sign. For two solutions $(h,z),(j,w)$ the bounds imply $3z\le h$, $3w\le j$ and $hw+jz<N$. If their ratios agree at both primes, $N\mid hw-jz$. The bound forces equality of the cross products, and substituting the two norm equations gives $z=w$ and $h=j$. If their ratios have opposite signs at both primes, $N$ divides the positive integer $hw+jz<N$, which is impossible. Choose a common sign to align each solution's ratio at $p$ with that of a reference solution. Only two possible values of its signed ratio at $q$ remain, and the argument makes this assignment injective.

Two occurrences really are possible. For $9017=71\cdot127$, the discriminants at 95 and 97 are $8=2\cdot2^2$ and $392=2\cdot14^2$. A repeated class also gives a congruence of squares and a proper gcd in this window. Identifying classes by factoring all discriminants would introduce additional work. [Checked collision](../PrimeFactors/DiscriminantPencil.lean)

## Counting the survivors

Let $M$ be the number of **false** parity-compatible midpoints, $t$ the number of independent seeds, and $Z$ the number of false midpoints surviving all $t$ tests. For $N$ of exactly 2048 bits as above,
$$2^{1018}<M<2^{1019}.$$
Indeed the length of the midpoint interval is $(3/\sqrt8-1)\sqrt N$ and restricting to one parity divides its length by two, with rounding error at most one. Subtract one more for the true midpoint. The inequalities follow using $2^{1023.5}\le\sqrt N<2^{1024}$ and $1.0606<3/\sqrt8<1.061$.

The 998-test lower bound counts survivors in this specific interval. Other public restrictions can shrink it. For example, writing $Q=2^{1024}$, we know $q<Q$, so $(p+q)/2<(Q+N/Q)/2$ because $x+N/x$ is increasing for $x>\sqrt N$. When $N$ is near $Q^2$ this additional upper bound can be much sharper. The 1,040-test upper bound continues to hold on every smaller interval containing the true midpoint.

Put $m=M2^{-t}$. For $t\le1040$, raising each single and joint probability to the $t$th power changes the corresponding ideal probabilities $2^{-t}$ and $4^{-t}$ by relative error at most $e=10^{-8}$, using $(1+4\cdot2^{-40})^{1040}<1+10^{-8}$ and the analogous lower bound. Consequently
$$
 (1-e)m\le\mathbb E Z\le (1+e)m,\qquad
 \operatorname{Var}Z\le 2(1+e)m+3em^2.
$$
To see the second inequality, expand $Z^2$ over ordered pairs of false candidates. Including the diagonal, at most $2M$ pairs have the same square class, and their joint survival is bounded by single-candidate survival. All other pairs have the joint estimate. Subtract the square of the lower bound for the mean.

For 1,040 tests, $m<2^{-21}$, and Markov's inequality gives the headline isolation probability. For 998 tests, $m>2^{20}$, and the distance from the mean to 500,000 exceeds $m/2$. Chebyshev's inequality bounds the probability of falling below 500,000 by $8(1+e)/m+12e<10^{-5}$.

For growing bit length $b$ the same calculation gives a transition at $\log_2 M$ tests. With $t=O(b)$ and per-seed error $o(1/b)$, if $\log_2 M-t\to+\infty$, then $Z/(M2^{-t})\to1$ in probability. If $t-\log_2 M\to+\infty$, the probability of a false survivor goes to zero. This lower bound is for these randomly drawn checks. It does not bound all algorithms that select tests using the product.

The extra 1024-bit cap changes this count substantially on one of the project’s certified products. For the 2048-bit cubic-period fixture, set $U=\min(\lfloor\sqrt{9N/8}\rfloor,\lfloor(Q^2+N-1)/(2Q)\rfloor)$ and count only parity-compatible midpoints through $U$. At 998 tests, this gives $482951<m<482952$. Applying the variance bound above to the upper tail now puts the probability of at least 500,000 wrong survivors **below 0.335%**. This illustrates why a bound for one interval cannot serve as a lower bound on all product-only searches. [Certified input](../benchmarks/cyclotomic-periods.json)

Lean checks the two-per-class bound, the finite sign-count identity and square preservation. The character-sum estimates, the probability calculation and the 1,040/998 conclusions are mathematical arguments in these notes. The example below has a separate Lean certificate for its actual factors.

## Reproducible small run

The 41-bit benchmark uses the same public product as the earlier modular-hyperbola benchmark. It supplies a deterministic pseudorandom seed for reproducibility. The probability theorem assumes independent uniform seeds. Both the direct scan and the filtered scan below recover $1000003\cdot1900009$. The filtered scan has one candidate remaining by test 18 in this run. An illustrative local run took about 0.44 seconds for 24 sign tests and 0.007 seconds for the direct square checks. Wall times depend on the machine. [Benchmark fixture](../benchmarks/midpoint-readings.json)

```sh
python3 experiments/midpoint_readings.py 1900014700027 --tests 24 --seed 1 --compare
```
