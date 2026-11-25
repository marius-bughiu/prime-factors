# A seven-row equation tests a wider interval

On two 2,048-bit products, Lean checked that the chosen interval contains **no divisor**. The interval widths were three times the original seven-row binomial width on the fresh product and twice that width on the crossed product. We used only the product and the same public center as before. Neither result locates a prime factor. On the small control, the same procedure recovered $132{,}079=269\times491$. [Fresh interval](https://marius-bughiu.github.io/prime-factors/#rounded-sifted-window-fresh-mid) · [Crossed interval](https://marius-bughiu.github.io/prime-factors/#rounded-sifted-window-crossed-440) · [Small factorization](https://marius-bughiu.github.io/prime-factors/#rounded-sifted-window-132079-24)

## How to keep a useful divisibility while changing the polynomial

A divisor candidate has the form $c+2x$ for a public odd center $c$. When the input is coprime to 3, 5 and 7, the allowed values of $x$ have a common divisibility property. For each degree $i$ up to six, our earlier polynomial $P_i(x+s)$ is divisible by a known $D_i$ at every allowed position. The shift $s$ uses only $c$. For example $D_6=45{,}360$. This lets us use a smaller integer in the height test. [Original nodes and denominators](sifting-a-divisor-window.md)

Any change to a coefficient by a multiple of $D_i$ preserves that property. Choose the monic Chebyshev polynomial $T_i$ for the target interval $[-R,R]$, with $R=2U$. In each degree below the leading one, subtract the coefficient of $T_i$ from that of $P_i$ and take the nearest residue modulo $D_i$. Let $E_i$ collect these residual coefficients. Then $A_i=T_i+E_i$ has the same residues as $P_i$ at **every integer**. The size of $T_i$ across the interval is at most $2U^i$ for positive degree. The correction costs at most $\sum_j |E_{ij}| R^j$. The implementation uses the actual correction coefficients and divides the sum of these bounds by $D_i$, rounding down because the value is integral at an eligible offset. [Implementation](../experiments/binomial_divisor_window.py) · [Chebyshev bound](../PrimeFactors/ChebyshevDivisorWindow.lean)

The certificate lists the correction coefficients, the coefficients of the short equation, and its ordinary integral polynomial. The Lean checker independently evaluates each degree-six row at seven points. A finite-difference theorem lifts agreement modulo $D_i$ there to all integral offsets, including negative ones. The checker also verifies the height, the three Taylor divisibilities, and absence of roots modulo the reported prime. Changing the constant coefficient of the last correction row by one in the fresh witness made the modular agreement check fail. [Certificate checker](../PrimeFactors/RoundedSiftedWindow.lean) · [Finite differences](../PrimeFactors/DifferenceLane.lean)

## Comparisons at a fixed center

All runs below use degree six, Taylor depth three and a common lattice-reduction implementation. The previous column uses the sifted nodes before rounding. A larger radius covers more possible odd divisors. Each measurement checks just the selected interval.

| Input | Radius $R$ in odd positions | Rounded result | Previous sifted result |
|---|---:|---|---|
| 132,079 | 24 | Found 269 in $[237,333]$ | Height test missed |
| Crossed 2,048-bit product | $2^{440}$ | Excluded modulo 11 | Height test missed |
| Fresh 2,048-bit product | $3\cdot2^{439}$ | Excluded modulo 11 | Height test missed |
| Both large products | $2^{441}$ | Both missed | Both missed |

The fresh radius was an intermediate follow-up after the larger power of two missed. The successful fresh reduction took 1,479 swaps and 2,656 size reductions. The crossed reduction took 1,469 swaps and 2,657 size reductions. On 132,079, division by 269 produced 491 and Lean verified primality of both factors. For the large examples the downloadable certificates establish the interval exclusions, and each full product is still listed as an unresolved cofactor. [Inputs, budgets and reference measurements](../benchmarks/rounded-sifted-window.json)

Two existence results give more context for these runs. Counting coefficient choices by their total size improves the general guarantee for seven rows. At degree 144, using the two nonzero residues modulo 3 gives an equation that covers $2^{515}+1$ consecutive odd positions at a chosen location. We have run the seven-row equations on the large inputs. Generating the 145-row equation and identifying a productive interval at full size are separate, open computational steps. [Sharper seven-row guarantee](counting-short-equations.md) · [Degree-144 theorem and control comparison](rounding-on-three-adic-units.md)


The tradeoff for selecting just one location is now explicit. If we could obtain at most 1,168 readings of the product’s missing Euler factors with absolute error at most $1/8$, they would select a seven-row window containing the larger factor. The readings can require heights up to $2^{584}$. The earlier rule used 1,000 readings and a 24,576-row equation. The seven-row theorem makes the remaining polynomial small enough for the kinds of reductions we ran, but it does not give a fast evaluator for the readings or a runtime guarantee for recovering the short equation. [Conditional selection theorem](../PrimeFactors/SevenRowBoundaryWindow.lean) · [Evaluation cost](two-batches-of-boundary-readings.md)
