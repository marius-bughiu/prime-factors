# Pairing blocks on opposite sides of the factor interval

For a product of two distinct odd primes of comparable size, the smaller prime lies in a known interval. We can multiply all its candidates in pairs of blocks by interpolating a polynomial of half the previous degree. On two 79-bit inputs this reduced the time to compute the identical interval product from 2.22 to 1.83 seconds and from 2.25 to 1.91 seconds. The approach still requires roughly fourth-root work in the input number for a fixed wheel. On our 2,048-bit control it covered 131,072 integers and found no factor. [Previous interval method](factorial-progressions.md) · [Reproducible fixtures](../benchmarks/factorial-progressions.json)

## How two blocks share a polynomial

Suppose the input is $N=pq$ with odd primes $p<q\le 2p$. The interval from $\lceil\sqrt{N/2}\rceil$ through $\lfloor\sqrt N\rfloor$ contains $p$ and no multiple of $q$. Keeping candidates coprime to a small wheel $W$ preserves $p$ whenever $\gcd(N,W)=1$. The gcd of the full candidate product with $N$ then returns $p$. Bostan, Gaudry and Schost gave fast polynomial shifts for factorial products, and Costa and Harvey used a small-prime wheel. We compare with the repository's implementation of those ideas. [Bostan, Gaudry and Schost](https://doi.org/10.1137/S0097539704443793) · [Costa and Harvey](https://arxiv.org/abs/1201.2116)

Take a wheel-aligned boundary $A$ in the middle of the region covered by complete blocks. For a half-block of $h$ cycles, write $B=hW$. Each position $r$ names one retained offset in those $h$ cycles. To evaluate pair $j\ge0$, take the blocks starting at $A+Bj$ and $A-B(j+1)$. Writing $x=A+r$, the two candidates with that offset have product

$$
(x+Bj)(x-B(j+1))=x(x-B)-B^2j(j+1).
$$

The paired product is therefore $G_h(j(j+1))$, where
$$
G_h(U)=\prod_r\bigl((A+r)(A+r-B)-B^2 U\bigr).
$$
For $\rho$ offsets per wheel cycle there are $h\rho$ linear factors here, covering $2h\rho$ candidates. The degree is exactly $h\rho$ modulo $N$ when $B$ is a unit, as holds for dyadic $h$, odd $N$, and a coprime wheel. Any shared offset mask works. The two blocks themselves need no internal reflection symmetry.

Let $P_h(j)=G_h(j(j+1))$. Grouping adjacent pairs gives $P_{2h}(j)=P_h(2j)P_h(2j+1)$. Multiplying pairs $0$ through $g-1$ covers the entire $2hg$ cycles between the two outer boundaries, once each. We evaluate the same leftover edge candidates directly as in the ordinary method. Lean checks the product identity, degree, doubling and coverage. [Lean proofs](../PrimeFactors/FoldedFactorial.lean)

## Interpolation on the quadratic grid

For a polynomial $G$ of degree at most $d$, set $u_i=i(i+1)$ and let $v_i=G(u_i)$ for $0\le i\le d$. The node differences factor as $u_t-u_i=(t-i)(t+i+1)$. At each source node,

$$
(2i+1)\prod_{0\le j\le d,\ j\ne i}(u_i-u_j)
  =(-1)^{d-i}(d-i)!(d+i+1)!.
$$

This follows by separating the factors $i-j$ and $i+j+1$ and cancelling $i!$. At a target $t>d$, multiplying the $d+1$ node differences gives $(t+d+1)!/(t-d-1)!$. Lagrange interpolation now gives the single-convolution formula

$$
G(u_t)=\frac{(t+d+1)!}{(t-d-1)!}
  \sum_{i=0}^d
  \frac{(-1)^{d-i}v_i}{(d-i)!(d+i+1)!}
  \left(\frac{1}{t-i}-\frac{1}{t+i+1}\right).
$$

Write $w_i$ for the signed factorial weight including $v_i$. Convolve $(-w_d,\ldots,-w_0,w_0,\ldots,w_d)$ with $(1,1/2,1/3,\ldots)$ starting at index zero. Coefficient $t+d$ is the required sum. The implementation checks invertibility of the largest required factorial using a gcd and obtains the inverse factorials with one modular inversion. A failed inversion can itself expose a divisor. Lean proves the node difference and reciprocal identity. The interpolation tests compare both convolution backends to direct polynomial evaluation over a composite modulus. [Implementation](../experiments/factorial_progressions.py) · [Tests](../tests/test_factorial_progressions.py)

## Exact savings for the chosen doubling schedule

Hold the ordinary final width $H=4\cdot 2^k$ and number of complete blocks $g$ fixed. The ordinary polynomial has degree $H\rho$, while the paired polynomial has degree $H\rho/2$. Both compute the product over the same $gH$ cycles. For a completed interpolation stage with input degree $d$, intermediate ordinary shifts submit $5d+2$ coefficients to convolution and the final shift submits $d+2g$. Intermediate paired shifts submit $7d+4$ and the final shift submits $3d+2g+2$. Pairing needs one fewer doubling. Summing the stage lengths subtracts precisely

$$
(H/2+2)\rho-2k
$$

input coefficients whenever interpolation reaches the final gcd. This is positive for every $\rho\ge1$ and $k\ge0$. The repository's width rule ensures the final shift needs fresh samples because $g\ge \rho H/2$. The count measures both input vectors of each convolution. Total runtime also includes the longer inverse table, twice as many initial seed candidates and the same edge products. [Exact count identity](../PrimeFactors/FoldedFactorial.lean)

## Paired comparisons

Times below are medians of three runs per variant, alternating their order, on an arm64 Mac running macOS 27.0.1 and CPython 3.9.6. Both use the decimal convolution backend, $W=210$, identical interval boundaries, and the same number of final blocks. Times cover discovery. The new 79-bit fixture is the first accepted draw from the ASCII seed `folded-factorial-holdout-v1`, at zero-based attempt 3. Its factors were supplied only for verification. [Sampler](../experiments/crt_holdout.py) · [Benchmark data](../benchmarks/factorial-progressions.json)

| Input | Ordinary / paired degree | Ordinary / paired convolution coefficients | Ordinary / paired seconds | Result |
| --- | ---: | ---: | ---: | --- |
| 63-bit comparison | 12,288 / 6,144 | 63,530 / 57,302 | 0.1134 / 0.0907 | Same complete product and factor |
| Existing 79-bit holdout | 196,608 / 98,304 | 1,091,570 / 993,190 | 2.2174 / 1.8309 | Same complete product and factor |
| Fresh 79-bit draw | 196,608 / 98,304 | 1,077,936 / 979,556 | 2.2524 / 1.9139 | Same complete product and factor |
| First 131,072 integers of the 2,048-bit control | 192 / 96 | 648 / 456 | 0.0455 / 0.0444 | Same residue, gcd 1 |

The two 79-bit results are $543283139603355533096543=622358546533\cdot872942361971$ and $514172788860282293409077=567635995831\cdot905814276467$. Lean verifies product equality and primality. For perspective, GNU coreutils 9.12 `factor` recovered the same factors in 0.0140 and 0.0207 seconds respectively, including process startup, over nine runs per number.

For the full 2,048-bit control, the width rule selects $H=2^{504}$. Pairing reduces the degree from $48\cdot2^{504}$ to $48\cdot2^{503}$. Even the smaller polynomial would require over $10^{152}$ samples under this algorithm. Both factors of the control remain unresolved by the capped search.
