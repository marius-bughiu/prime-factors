# How many primes still fit the product?

We derived 512 yes-or-no tests from each of two 2,048-bit products. The unknown smaller prime must pass every test. On the fresh example, **more than $10^{184}$ different primes still pass the first 400 tests**. All 512 together leave **fewer than $1.28\times10^{159}$ possible primes**. We have no way to list those survivors cheaply or identify which one divides the product. The fresh product remains unfactored.

The count uses a published prime-ideal theorem under Dirichlet GRH. The mathematical link to the released Lean proof is given below. We checked the public witnesses and numerical implications in this repository. The field theory and the application of the analytic estimate are written deductions. [Recorded inputs and bounds](../research/split-prime-panel.json) · [Independent check of the released Dirichlet result](https://math.mit.edu/~drew/shortgrh/)

| Tests applied | Fresh comparison, candidate primes | Crossed comparison, candidate primes |
|---|---:|---:|
| 0 | $[2.65,2.67]\times10^{304}$ | $[4.73,4.75]\times10^{304}$ |
| 16 | $[4.05,4.08]\times10^{299}$ | $[7.22,7.25]\times10^{299}$ |
| 400 | $[1.0300,1.0330]\times10^{184}$ | $[1.8327,1.8380]\times10^{184}$ |
| 512 | At least 1, at most $1.28\times10^{159}$ | At least 1, at most $1.28\times10^{159}$ |

Each entry is a conservative bound on an actual count in the possible smaller-factor interval. At 512 the promise that the product has the described factors gives the lower bound of one. With 16 tests the retained fraction of the *primes* in that interval is between one in 66,000 and one in 65,000. The [unconditional character-sum comparison](sixteen-tests-for-the-smaller-factor.md) counts integers coprime to 60 and selects its 16 moduli from a longer search.

## Does recognizing survivors make them easier to find?

We took the first existing 20-bit prime pair and the first 24-bit prime pair from the independent timing experiment. Their intervals contained 9,995 and 61,477 primes. Eight tests left 43 and 210. An ascending search needed just 30 and 116 actual divisions before finding the smaller factor. It still had to visit 6,258 and 33,676 primes, evaluating the tests to decide which primes to skip. Including setup, the median time rose from 2.32 to 10.58 ms on the first product and from 16.95 to 77.13 ms on the second. Lean checked both factorizations. [Counts and timing data](../research/split-prime-holdout.json) · [Reproduce with the prime search](../experiments/split_prime_holdout.py)

## Building the tests from the product

For $N=pq$ with two 1,024-bit primes and $p\le q$, put $L=\lceil N/(2^{1024}-1)\rceil$, $U=\lfloor\sqrt N\rfloor$ and $W=U-L+1$. Then $L\le p\le U$. Both inputs have $W>2^{1020}$. In the first 32,768 continued-fraction steps of $\sqrt{4N}$ we collect negative norms and remove known odd square factors. We keep short moduli $d_i\equiv3\pmod4$ with $\gcd(d_i,60N)=1$, requiring each to be coprime to all earlier choices. Each has an explicit witness $a_i$ with $a_i^2+d_i\equiv0\pmod N$. Computing these 512 witnesses took 0.78 CPU seconds on the fresh product and 1.03 on the crossed product in the recorded runs. These times cover finding the tests. [Search and witness digests](../experiments/split_prime_panel.py)

Quadratic reciprocity implies $(p/d_i)=+1$ for every $i$. The public root works for every odd divisor of $N$. For these panels $d_i<L$ throughout, which also keeps every prime in the interval away from the prime divisors of $2\prod_i d_i$. Restrictions on prime divisors arising from quadratic forms go back to Euler. The witness selection, two finite input intervals and measured costs are the objects of this experiment. [Lean witness checker](../PrimeFactors/DivisorSignPanel.lean) · [Euler, *On divisors of numbers contained in the form mxx + nyy*, §§1–6](https://old.maa.org/sites/default/files/images/upload_library/46/Bialek-Klyve/E744-translation-MAA-Convergence.pdf)

## Why the estimate counts ordinary primes

For the first $k$ moduli consider $K=\mathbb Q(\sqrt{-d_1},\ldots,\sqrt{-d_k})$. Each $d_i$ is 3 modulo 4, so it has a prime of odd valuation. Pairwise coprimality makes that prime unique to its own $d_i$. Consequently every nonempty product of the selected square classes has a prime of odd valuation. The classes are independent, the field has degree $m=2^k$, and the signs of its square roots can be changed independently by automorphisms. This conclusion permits composite moduli with repeated prime factors.

For a prime $\ell\in[L,U]$, the action of Frobenius on $\sqrt{-d_i}$ is multiplication by $(-d_i/\ell)=(\ell/d_i)$. All signs are positive precisely when $\ell$ splits completely in $K$. In that case there are $m$ prime ideals of norm $\ell$. Otherwise there are none with that norm. Thus the candidate primes can be counted using the prime ideals of a single abelian field. [Splitting and Frobenius, Proposition 8.6](https://math.mit.edu/classes/18.785/2015fa/LectureNotes8.pdf#page=2)

The absolute field discriminant satisfies $\log|\Delta_K|/m\le\tfrac12\sum_i\log d_i$. Indeed $\omega_i=(1+\sqrt{-d_i})/2$ is integral. Products using each $\omega_i$ at most once give an integral basis of an order of full rank. Its trace matrix is a tensor product of the quadratic trace matrices, whose determinants are $-d_i$. The order's absolute discriminant is $(\prod_i d_i)^{m/2}$, and division by the square of its index gives the field discriminant. For $k=0$ the field is $\mathbb Q$ and its discriminant is 1.

## Where the Dirichlet result enters

Since $K/\mathbb Q$ is abelian, its Dedekind zeta function is a product of primitive Dirichlet $L$-functions, including the ordinary zeta function. For these fields the released Dirichlet zero-location theorem, together with the functional equation, supplies GRH for $\zeta_K$. Grenié and Molteni's Corollary 1.2 gives the following bound on the normalized prime-ideal Chebyshev function at $x\ge100$. [Dirichlet factorization, Theorem 19.15](https://ocw.mit.edu/courses/18-785-number-theory-i-fall-2021/mit18_785f21_lec19.pdf#page=11) · [Pinned upstream statements](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab/src/Statements.lean) · [Grenié and Molteni, Corollary 1.2](https://arxiv.org/pdf/1312.4463#page=3)

$$
\left|\frac{\psi_K(x)}m-\frac{x}m\right|\le
\sqrt{x}\left[\left(\frac{\log x}{2\pi}+2\right)\frac{\log|\Delta_K|}{m}
+\frac{\log^2 x}{8\pi}+2\right].
$$

Apply the estimate at $U$ and $L-1$. In the difference, the terms of prime norm give the sum of $\log\ell$ over the passing primes after dividing by $m$. All other terms have norms that are powers $\ell^j$ with $j\ge2$, hence $\ell\le\sqrt U$. For each underlying rational prime, there are at most $m$ prime ideals above it. Summing the powers of any one prime ideal up to $U$ contributes at most $\log U$. The whole normalized extra contribution is therefore between zero and $\sqrt U\log U$.

Here $\sqrt U\le2^{512}$, $708\le\log\ell\le710$, and $\log|\Delta_K|/m\le355k$. Using $\pi>3$, each endpoint error is at most $2^{512}(121\cdot355 k+21007)$. Twice this error plus the extra prime-power terms fits below $E=2^{538}$ for every $k\le512$. If $H$ is the number of passing primes, this gives

$$m\,708\,H\le W+mE,\qquad W\le m\,710\,H+mE.$$

The interval arithmetic and rounding were checked in Lean. The bounds at zero tests apply the same argument to ordinary primes with $m=1$. The calculation requires neither constructing $K$ nor enumerating its prime ideals. Evaluating the sign tests at a proposed prime is feasible. Finding the prime that divides $N$ without scanning an enormous set remains open here. [Errors, logarithms and population implications](../PrimeFactors/SplitPrimeInterval.lean) · [Full-size receipt generator](../experiments/split_prime_receipt.py)

Run `python3 -m experiments.split_prime_panel` to reproduce the ordered witnesses and population bounds. After `lake build`, run `python3 -m experiments.split_prime_receipt` to check the public roots, coprimality, factor inclusion and rounded counts under the stated estimates.
