# Two fourth roots reveal a special factor pair

Given **151,847,041**, its integer fourth root is 111. Subtract $111^4$ and the remainder is 40,000, exactly $4\times10^4$. Those two public calculations give the prime factors **10,301 and 14,741**. An ordinary Fermat search reaches the pair on its 199th square test. The example was chosen from a special family. Among all products of two distinct 1,024-bit primes with a 2,048-bit product, **fewer than one in $2^{1129}$** satisfy this recognizer. [Lean recognition and primality](../PrimeFactors/RecognizingQuarticProducts.lean) · [Full-size population bound](../PrimeFactors/QuarticPrimePopulation.lean)

## What the product has to tell us

Sophie Germain’s classical identity gives

$$x^4+4y^4=(x^2+2y^2-2xy)(x^2+2y^2+2xy).$$

If someone supplied $x$ and $y$, the identity would immediately give a factor pair. Here the input is just $N$. Take $x=\lfloor\sqrt[4]{N}\rfloor$, subtract $x^4$, then take the integer fourth root $y$ of the remainder divided by four. Check that $x,y>0$ and that $N=x^4+4y^4$ exactly. This finds precisely the positive representations satisfying $N<(x+1)^4$. Each integer fourth root requires two integer square roots. The identity also gives the sum directly as $2x^2+4y^2$. Both returned factors are proper except at $N=5$. For general inputs in the family, the two outputs can themselves be composite. [Classical identity, equation 1.2](https://periodicos.uem.br/ojs/index.php/BSocParanMat/article/download/78986/751375162842/751375344221) · [Soundness, completeness and exceptional input](../PrimeFactors/RecognizingQuarticProducts.lean)

The upper bound matters. The balanced semiprime $1{,}291{,}357{,}674{,}469=805{,}853\times1{,}602{,}473$ equals $1065^4+4\times187^4$, but its integer fourth root is 1066. The recognizer rejects it. [Checked counterexample](../PrimeFactors/RecognizingQuarticProducts.lean)

When both displayed factors are prime, their midpoint $x^2+2y^2$ is the first success of the ordinary Fermat search. If $x\ge2y$, the inclusive number $T$ of square tests to reach it satisfies $3y^2+1\le2T$ and $T\le2y^2$. Every recognized representation with $x\ge16$ meets that condition. The fourth-root calculation has a fixed number of operations on integers whose size grows with $N$. These are operation counts. [Fermat work and exact example rank](../PrimeFactors/QuarticFermatDistance.lean)

## How many inputs qualify?

Let $A(X)$ count distinct odd positive integers through $X$ that the recognizer accepts. Lean proved the following error bound for every nonnegative integer $X$:

$$\left|A(X)-\frac27X^{7/16}\right|\le3X^{1/4}+4.$$

Each odd $x$ has its own interval between two consecutive fourth powers. Its number of allowed positive $y$ values is about $x^{3/4}$. Summing those counts and allowing for rounding and the last partly filled interval gives the estimate. **It counts all accepted odd integers before asking whether either factor is prime.** [Exact interval counts and uniform error proof](../PrimeFactors/QuarticProductCoverage.lean)

| Odd inputs through | Recognized | Both factors prime | Equal-width primes with a full-width product |
| --- | ---: | ---: | ---: |
| $2^{16}$ | 35 | 9 | 0 |
| $2^{24}$ | 403 | 42 | 2 |
| $2^{32}$ | 4,636 | 266 | 30 |

The rows are cumulative. In the last column two $b$-bit primes must have a $2b$-bit product. The experiment checks each generated factorization and also scans every odd input through $2^{16}$ independently. [Reproduce the census](../experiments/quartic_product_strips.py)

At 2,048 bits, the inequalities require $13\cdot2^{508}\le x<2^{512}$ and $0<y<2^{384}$. The first parameter is odd on eligible products. Even counting every allowable parameter pair gives at most $3\cdot2^{891}$ eligible products, which implies the one-in-$2^{1129}$ upper bound. This argument gives no lower bound on how often both expressions are prime. [Counting proof](../PrimeFactors/QuarticPrimePopulation.lean)
