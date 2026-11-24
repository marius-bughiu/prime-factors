# What the Riemann hypothesis gives a factor search

The factor-sum investigation treats balanced semiprimes and studies which local constraints survive globally. It gives a separate application of the Dirichlet result to incorrect candidate sums. [Factor-sum research](../discoveries/factor-sum-residues.md)

Two later counting results use the Dirichlet theorems in different ways. Miller's reduction uses small character witnesses to turn a totient count into deterministic factorization, including for products with repeated factors. A prime at which the product is a quadratic nonresidue makes the two unknown primes distinct modulo that auxiliary prime. This permits a smaller weighted readout on the original multiplication network. [Totient count](../discoveries/counting-modular-inverses.md) · [Choice of a separating prime](../discoveries/exponential-readout.md)

In the signed short-period search, the public Jacobi symbol chooses between $N-1$ and $N+1$. Dirichlet GRH and a published coset bound guarantee a small prime discriminant realizing each pair of hidden signs. The quadratic-group arithmetic and a numerical example are checked in Lean. [Signed exponents and the character bound](../discoveries/jacobi-separation.md)

The same Dirichlet hypothesis bounds the work of finding a quadratic nonresidue at each auxiliary prime in a Fermat search. Testing all primes in a wide band doubles its limiting population coverage. A mean-value theorem also bounds the total work unconditionally. [Proof and explicit limiting fraction](../discoveries/gap-search-frequency.md#testing-every-auxiliary-prime)

## The November 2026 release

On November 20, 2026, Levent Alpöge released a Lean proof developed with Claude. On November 21 the Lean FRO and Mathlib Initiative certified that the proof establishes mathlib’s `RiemannHypothesis`. Andrew Sutherland’s November 24 verification record also covers the critical-strip and nonvanishing statements for Dirichlet L-functions. Those statements concern every modulus and every Dirichlet character. Clay’s Millennium Prize has a separate publication and acceptance process. [Author’s announcement](https://alpo.ge/remark.pdf) · [Lean community verification](https://leanprover-community.github.io/blog/posts/riemann-hypothesis/) · [Independent check logs](https://math.mit.edu/~drew/grh/) · [Prize rules](https://www.claymath.org/millennium-problems/rules/)

The original Lean release uses mathlib v4.33.1. The community mirror identifies `40e56bab` as the original source and says the submission was published without a license. This project cites the theorems and independently implements the arithmetic below. The Apache-2.0 notices on certain comparator declarations apply only to those files. [Original release tree](https://github.com/leanprover-community/riemann-hypothesis/tree/40e56bab) · [Mirror license notice](https://github.com/leanprover-community/riemann-hypothesis#license)

The zero-free Euler-factor lemma in the release uses a strict positive real part. Examining equality at the boundary led to a checked factor-comparison theorem. Separately, the released Dirichlet GRH statements supply the analytic hypothesis for a prime-character sum estimate used to sample modular square tests. [Derivations and proof scope](../discoveries/character-conjectures.md)

## A bounded witness search for structured semiprimes

Suppose the input is $N=pq$ for distinct primes $p<q$, with $p-1$ dividing $q-1$. The factors can be far apart. If $p<q$ are primes with the same bit length of at least three, $p-1<q-1<2(p-1)$, so this hypothesis fails throughout that family. [Equal-width obstruction](../PrimeFactors/Subgroup.lean) The search takes only $N$. For each integer base $a$ starting at 2, it first takes $\gcd(a,N)$. If that is 1, it computes $r=a^{N-1}\bmod N$ by modular exponentiation and takes $\gcd(r-1,N)$. Any gcd strictly between 1 and $N$ certifies a split.

For this family and $N\ge 3000$, it suffices to search through $(\ln N)^2$. Here is the argument.

1. A prime divisor of $N$ at or below the bound is found by the first gcd. Now suppose every prime at or below the bound is coprime to $N$.
2. Modulo $p-1$, both $p$ and $q$ are 1. Hence $p-1\mid N-1$. Fermat’s little theorem gives $a^{N-1}=1\pmod p$ for every unit $a$.
3. Modulo $q-1$, the remainder of $N-1$ is $p-1$, strictly between 0 and $q-1$. Since the units modulo $q$ are cyclic, some unit has $(N-1)$st power different from 1. The Chinese remainder theorem lifts it to a unit modulo $N$. Thus the units whose $(N-1)$st power equals 1 modulo $q$ form a **proper subgroup** $H$ of the units modulo $N$.
4. Under Dirichlet GRH, Theorem 1.1(2) of Lamzouri, Li and Soundararajan gives a prime base $a\le (\ln N)^2$ outside $H$. At that base $p$ divides $r-1$ and $q$ does not, so the second gcd equals $p$. The base is a modular exponentiation witness. It can be much smaller than either factor. [Theorem 1.1, p. 2](https://arxiv.org/pdf/1309.3595#page=2) · [Dirichlet theorems in the release](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab/src/Main.lean)

The executable uses $b^2$ as an integer upper bound, where $b$ is the binary length of $N$. This covers the analytic window because $\ln N<b\ln 2<b$. Scanning all integer bases includes every prime in the bound and requires constant-many working integers. For a composite outside this family, or with a user-supplied smaller cap, exhaustion means only that the tested bases produced no proper gcd. Miller’s primality test also uses small witnesses under Dirichlet GRH. A witness that proves compositeness alone can leave the gcd equal to 1. [Miller’s original paper](https://www.cs.cmu.edu/~glmiller/Publications/Papers/Mi76.pdf)

Lean checks that the subgroup is proper and that its small outside prime yields the stated gcd. The formal theorem takes the finite conclusion `SmallPrimeOutside N bound` as an explicit hypothesis. Proving this hypothesis from the released Dirichlet statements by formalizing Theorem 1.1(2) is the open analytic step. Individual certificates for complete prime factorizations already stand independently of the search bound. [Subgroup and gcd theorems](../PrimeFactors/Subgroup.lean) · [Search implementation](../experiments/subgroup_split.py) · [Factorization certificates](../PrimeFactors/Certificate.lean)

### Reproduce a split

```sh
python3 experiments/subgroup_split.py 5030251603021
```

Base 2 gives $r=2557237514825$ and $\gcd(r-1,N)=100003$. The cofactor is 50301007. The 1,050-bit fixture uses $p=223\cdot 2^{512}+1$ and $q=1197(p-1)+1$. Its stored decimal input goes to the same search, which finds a split at the first base. The 1,050-bit control keeps $p$ and takes $q'=266085\cdot 2^{512}+1$, for which $p-1$ fails to divide $q'-1$. Bases 2 through 65 yield 64 unsuccessful gcd trials. That result leaves all larger bases open. The fixture test checks Proth’s criterion for $p$, $q$ and $q'$ using bases 3, 5 and 7 respectively. The experiment sees only the decimal product and its base limit. [Inputs and expected outputs](../benchmarks/subgroup.json) · [Fixture checks](../tests/test_subgroup_split.py)

## Divisor sums and exact recovery

Sutherland combined the RH release with the independent Robin1984 project at `acab1a3`. The resulting verified inequality is $\sigma(N)<e^\gamma N\log\log N$ for $N>5040$, where $\sigma$ is the sum of all positive divisors. Robin1984’s original code is available under Apache-2.0, subject to its file-specific notices. [Combined theorem](https://math.mit.edu/~drew/grh/ArithSolution.lean) · [Verification evidence](https://math.mit.edu/~drew/grh/) · [Robin1984 licensing](https://github.com/kimihiro64/Robin1984/blob/main/LICENSING.md)

For distinct primes $p,q$, multiplicativity gives $S=\sigma(N)-N-1=p+q$. With **exact** $\sigma(N)$, the discriminant $S^2-4N$ is $(q-p)^2$ and the roots $(S\pm\sqrt{S^2-4N})/2$ are the two factors. For example, $N=10403$ has $\sigma(N)=10608$, giving $S=204$, discriminant 4 and factors 101 and 103. A fast way to obtain that exact divisor sum from $N$ would itself solve the factorization problem for this family. [Mathlib’s divisor-sum results](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/ArithmeticFunction/Misc.html)

Substituting Robin’s upper bound gives $S<e^\gamma N\log\log N-N-1$. Even at the lower endpoint $N=5041$, the right side exceeds $2N$. The elementary inequality $(p-2)(q-2)\ge 0$ already gives $S\le N/2+2$. The Robin consequence therefore yields no improvement to this search window throughout its applicable range. An input-specific upper bound for $\sigma(N)$ would have to beat the elementary estimate before it could prune additional midpoints.

## Reuse and contributions

- **Mathlib.** Its Apache-2.0 library provides primality, prime-factor lists and uniqueness. Its contributor guide asks authors to describe AI use and understand the changes they submit. The local certificate interface uses its existing mathematical definitions. [Factor API](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Factors.html) · [Contribution guide](https://leanprover-community.github.io/contribute/index.html#use-of-ai) · [License](https://github.com/leanprover-community/mathlib4/blob/master/LICENSE)
- **Physlib.** Its human-facing AI policy points to `AGENTS.md` for agent instructions and puts responsibility for theorem meaning on the submitter. This is a model for asking a contributor to explain why a theorem’s hypotheses match its advertised input class. [AI policy](https://github.com/leanprover-community/physlib/blob/master/AI-POLICY.md) · [Agent instructions](https://github.com/leanprover-community/physlib/blob/master/AGENTS.md) · [License](https://github.com/leanprover-community/physlib/blob/master/LICENSE)
- **CADO-NFS.** Its team publishes general-purpose factoring benchmarks with hardware, CPU time and wall time. These provide context for the one-hour goal. Results on a family with a guaranteed small witness need their own input description for a meaningful comparison. [Upstream benchmark table](https://cado-nfs.gitlabpages.inria.fr/)
