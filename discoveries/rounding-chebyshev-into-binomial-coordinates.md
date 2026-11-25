# A wider factor window at degree 128

One degree-128 equation is guaranteed to cover a preselected window of $2^{514}+1$ consecutive parity indices on a balanced 2,048-bit product. An index $x$ stands for the possible divisor $c+2x$, with a public odd left endpoint $c$. The result applies anywhere the candidate factor is at least $D=\lceil N/2^{1024}\rceil$ and coprime to $128!$. Every 1,024-bit prime factor meets both conditions when its partner also has 1,024 bits. This is an existence proof for each chosen window. We have yet to run a reduction at this scale or to find the correct window from the product. [Checked theorem](../PrimeFactors/RoundedChebyshevWindows.lean)

## Why rounding preserves the arithmetic

Write the indices as $0\le x\le H=4U$. Center a monic Dickson polynomial of degree $i$ at $2U$. Its magnitude is at most $C_i=2U^i$ on the window for $i>0$, and we use $C_0=1$. Expand that integer polynomial $P_i$ in the falling-factorial basis. Each basis polynomial $(X)_j$ is monic of degree $j$ and takes the value $j!\binom{x}{j}$ at nonnegative integers. We therefore have an expansion $P_i(x)=\sum_{j=0}^i b_j\binom{x}{j}$ with integer $b_j$ and $b_i=i!$. For $j<i$ round $b_j/i!$ to the nearest integer. Keep the top coefficient exactly one. The resulting row $R_i$ takes integer values on integer indices, has usual leading coefficient $1/i!$, and satisfies

$$\left|R_i(x)-\frac{P_i(x)}{i!}\right|\le \frac12\sum_{j<i}\binom{H}{j}.$$

For a simple integer certificate Lean uses the larger positive weight

$$w_i=1+\left\lfloor\frac{C_i}{i!}\right\rfloor+\sum_{j<i}\left\lfloor\frac{H^j}{j!}\right\rfloor.$$

The terms added by rounding have lower degree. The coefficient of $\binom{x}{i}$ remains one in every row, so all these rows together form an integer triangular change of the binomial basis with diagonal one. Multiplying every row by the common $k!$ puts it in $\mathbb Z[X]$. If the cleared value is divisible by $d^m$ and $\gcd(k!,d)=1$, the integer value before clearing is divisible by $d^m$ as well. A strict bound below $d^m$ therefore forces an exact zero. [Checked expansion, rounding and recovery](../PrimeFactors/RoundedChebyshevWindows.lean) · [Binomial denominator cancellation](../PrimeFactors/BinomialDivisorWindow.lean)

## What the finite test buys

Take degree $k=128$, dimension $r=129$, Taylor depth $m=64$, and prescribe a public anchor $t$ with $N\mid c+2t$. The box test needs

$$N^{2080}\,129^{129}\prod_{i=0}^{128}w_i<D^{8256}.$$

For $H=2^{514}$ the integer $129^{129}\prod_i w_i$ has 4,187,605 bits. From $2^{2047}\le N\le2^{1024}D$ and $2^{1023}\le D$, the available upper bound on that integer is $2^{4{,}188{,}128}$. The pigeonhole argument gives one nonzero polynomial selected from the public parameters. It vanishes at every eligible divisor offset in the window and has at most 128 distinct integer roots. Enumerating the box itself would be expensive. At $H=2^{513}$ Lean additionally checks the numerical short-vector inequality for classical LLL with $\delta=3/4$, using $N\le2^{2048}$ and $D\ge2^{1023}$. The stronger $2^{514}$ existence result uses the box inequality. [Finite arithmetic and hypotheses](../PrimeFactors/RoundedChebyshevWindows.lean) · [Product-coupled lower bound](../PrimeFactors/CoupledDivisorWindow.lean)

On both published 2,048-bit products the original one-sided binomial weights $\binom{H}{i}$ pass the same box comparison at $H=2^{512}$ and fail it at $H=2^{513}$, with each input's own $D$. Rounding therefore covers four times the one-sided **index span** in this dyadic comparison at the same degree and depth. Centering the ordinary binomial basis already recovers roughly one of these two bits. Sufficient comparisons can fail even when a particular reduction finds a good row. No wall-clock speedup or new full-size split is measured here. [Centered ordinary binomial bounds](../PrimeFactors/CenteredBinomialDivisorWindow.lean) · [Two-control comparison](../PrimeFactors/RoundedChebyshevWindows.lean)

The underlying integer-valued binomial polynomials and the use of capacity to study auxiliary-polynomial constructions have precedents. Chinburg, Hemenway, Heninger and Scherr give restrictions on improving certain small-root exponents using binomial polynomials. Our calculation concerns fixed finite constants for an unknown divisor, using the coprime-denominator condition above. It supplies a wider prescribed window and leaves the global factor-location problem open. [Original capacity paper](https://arxiv.org/abs/1605.08065)
