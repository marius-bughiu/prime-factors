# Two product measurements give the sum of the primes

If you know the sum of two primes as well as their product, you can recover them by taking a square root. We found a way to get that sum from two measurements built entirely from the public number. Each measurement can represent an enormous product. On the numbers we timed, an ordinary search found the smaller factor faster. [Lean proof](../PrimeFactors/DivisorProductDerivative.lean) · [Reproducible comparison](../experiments/divisor_product_derivative.py)

For 143, suppose the unknown factors are distinct four-bit odd primes. Write down all the four-bit odd numbers, namely 9, 11, 13 and 15. Multiply them once. Then add 143 to each entry and multiply again. Both products have remainder zero modulo 143. Keep **one more base-143 digit** in each product by taking the remainder modulo $143^2$ before dividing by 143. The digits are 135 and 86. We want the unique number $S$ between 0 and 142 that satisfies $135(1+S)\equiv86\pmod{143}$. That gives $S=24$. The square root of $24^2-4\cdot143$ is 2, giving the two primes **11 and 13**. [Checked example](https://marius-bughiu.github.io/prime-factors/#divisor-product-derivative-143)

## Why the second digit knows the sum

Let $N=pq$ with distinct odd primes of the same bit width, and let $z$ range over the odd integers of that width. Each prime occurs once. Every other entry is coprime to $N$ because all entries are positive and smaller than twice either prime. Write $P(X)=\prod_z(z+X)$ and $C=P(0)/N$. Then $C$ is invertible modulo $N$.

The derivative $P'(0)$ is the sum of the products obtained by removing one entry at a time. Removing $p$ leaves $qC$, removing $q$ leaves $pC$, and every other removal leaves a multiple of $N$. Thus $P'(0)\equiv(p+q)C\pmod N$. Substituting $X=N$ into the polynomial gives $P(N)\equiv P(0)+NP'(0)\pmod{N^2}$. The second digits $c_0,c_1$ of $P(0),P(N)$ therefore satisfy

$$p+q = (c_1c_0^{-1}-1)\bmod N.$$

The ordinary representative of the residue is the actual sum because $p+q<N$. The same proof applies to every public duplicate-free list containing the two factors whose entries are positive and all below $2\min(p,q)$. Translating by $aN$ gives $c_a\equiv C(1+a(p+q))\pmod N$ for every natural $a$. Once two such digits are known, these translations all lie on the same line. [Exact recovery, all translations and assumptions](../PrimeFactors/DivisorProductDerivative.lean)

## What the measurements cost

At 1,024 bits per prime the complete band contains $2^{1022}$ odd entries. Products on a regularly spaced interval can use block multiplication and fast polynomial evaluation. The square-root-size block approach still takes roughly $2^{511}$ operations up to logarithmic factors on this band, with a modulus of up to 4,096 bits. We used the repository’s existing block evaluator. The full operation count depends on the multiplication algorithm, and the implementation records tails or any direct fallback. An ordinary block-product search can stop at the square root of $N$, where the smaller prime alone already gives a proper gcd. [Block evaluator](../experiments/divisor_product_derivative.py) · [Earlier interval product work](folded-factorial.md)

| Input | Factors recovered | Odd entries represented in each full product | Convolutions for the two digits | Convolutions for the ordinary product through $\sqrt N$ |
|---|---|---:|---:|---:|
| 54,253 | 227 × 239 | 64 | 6 | 3 |
| 7,371,899 | 2,593 × 2,843 | 1,024 | 10 | 4 |
| 2,397,917,251 | 43,517 × 55,103 | 16,384 | 14 | 6 |

On the last example the local median over 11 runs was about 2.28 milliseconds for the two digits, 0.43 milliseconds for the ordinary product through the square root and 0.19 milliseconds for trial division in the same smaller-factor band. The published fixtures separately measure discovery and verify the complete factors. On both 2,048-bit controls the first 64 odd positions had product coprime to $N$. Each run left $2^{1022}-64$ positions unexamined. The research question is whether the second digits, or enough information about their ratio, can be obtained more cheaply. [32-bit certificate](https://marius-bughiu.github.io/prime-factors/#divisor-product-derivative-32bit) · [Fresh budget](https://marius-bughiu.github.io/prime-factors/#divisor-product-derivative-fresh-2048) · [Crossed budget](https://marius-bughiu.github.io/prime-factors/#divisor-product-derivative-crossed-2048)
