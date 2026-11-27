# Can prime-power samples predict the coefficient at the product?

**Two explicit modular forms have identical coefficients at every prime power, yet give 96 and 97 at index 77.** Both belong to the weight-two space at level 308 and have constant term zero and first coefficient one. Even perfect measurements at every prime power cannot distinguish these forms. The comparison tests an inference that uses the level and the sample values. A method that uses the identity of a particular form has additional information. [Lean example and sampling theorem](../PrimeFactors/OldformSamples.lean)

## How the disagreement arises

Let $N=pq$ with distinct odd primes. The positive-index coefficients of the weight-two series $F$ used here are

$$
f(n)=\sigma(n)-3\sigma(n/2)+2\sigma(n/4).
$$

Here $\sigma$ sums positive divisors, and a term with a nonintegral argument is zero. In particular, $f(1)=1$ and $f(N)=(p+1)(q+1)$. Normalize $E_2$ to have constant term one and positive-index coefficients $-24\sigma(n)$. Then $F$ is the Fourier expansion of $-(E_2(z)-3E_2(2z)+2E_2(4z))/24$, which is modular of level four. Raising the level allows both $F(z)$ and $F(Nz)$ in the space at level $4N$. In the second series the powers of the expansion variable have all been multiplied by $N$. We use the classical level-raising map and Eisenstein-series identity from the literature. The Lean proof works with their explicit coefficients. [Bruin, §2.1 and §2.3](https://www.numdam.org/item/10.5802/pmb.a-133.pdf) · [Lean coefficient definitions](../PrimeFactors/OldformSamples.lean)

Compare $F(z)$ with $F(z)+cF(Nz)$ for any integer $c$. The series $F(Nz)$ has zero constant term and its first nonzero coefficient occurs at $N$. It vanishes at every index indivisible by $N$. A power of one prime cannot be divisible by the two distinct primes $p$ and $q$, so every prime-power measurement agrees. At $N$ the additional coefficient is $c$. With $N=77$ and $c=1$ the values are 96 and 97. If a positive sample index with a known complete factorization does distinguish the two forms, its factor list already contains both $p$ and $q$. [Lean proof for arbitrary sample indices and prime lists](../PrimeFactors/OldformSamples.lean)

## What fast coefficient algorithms assume

Bruin's fast coefficient theorem takes the index **in factored form**. For variable weight and level, the polynomial expected-time conclusion uses RH for zeta functions of number fields. With both fixed, Bruin gives an unconditional expected-time bound. At weight two and level 308 the theorem represents a form by all its coefficients through index 5,760, so this input already includes index 77. The released Lean statements we reviewed concern the Riemann zeta function and Dirichlet $L$-functions. Even granting the running-time hypothesis leaves the input factorization requirement. [Bruin, Theorem 1.1 and Remarks 1.3–1.4](https://www.numdam.org/item/10.5802/pmb.a-133.pdf) · [Released Lean statements](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab/src/Statements.lean)

Preobrazhenskiĭ studies a different interpolation scheme for modular forms associated with elliptic curves. Its coefficient estimate requires a bound on the tail of a polynomial expansion. The paper's factoring complexity is explicitly conditional on that coefficient step working in polynomial time. Our two examples belong to the full weight-two space and concern sample values alone. They leave open what a fixed eigenform, a tail bound, or a separate arithmetic identity could establish. [Interpolation hypotheses and Theorem 2](https://arxiv.org/pdf/1008.5035) · [Bach and Charles on composite-index eigenform coefficients](https://arxiv.org/abs/0708.1192)
