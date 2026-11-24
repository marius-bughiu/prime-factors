# Shifting a factorial across the balanced factor interval

The search recovered both primes of the freshly sampled 79-bit product $543283139603355533096543=622358546533\cdot872942361971$ in 2.25 seconds on an arm64 Mac. It received the product, the promise that the two primes differ by a factor of at most two, and a public interval budget. It computed the full interval product before taking its final gcd. Lean then verified both prime factors and their multiplicities. On the 2,048-bit control the search covered its first 131,072 integers and left the full number unresolved. [Search](../experiments/factorial_progressions.py) · [Benchmark fixtures](../benchmarks/factorial-progressions.json)

## From the product to an interval

For $N=pq$ with distinct odd primes $p<q\le2p$, let $L=\lceil\sqrt{N/2}\rceil$ and $U=\lfloor\sqrt N\rfloor$. Then $L\le p\le U<q$. Choose a small modulus $W$ coprime to $N$ and keep the integers $k\in[L,U]$ coprime to $W$. Their product contains $p$ and has no multiple of $q$, so one gcd with $N$ gives $p$. Checking $\gcd(W,N)$ first can itself reveal a factor. The fixtures use $W=210$ and its 48 invertible residue classes.

The factorial method of Pollard and Strassen groups consecutive candidates into block products. Bostan, Gaudry and Schost evaluate the block polynomials on arithmetic progressions using fast interpolation. Costa and Harvey remove candidates divisible by small primes and extend the block-doubling method to the remaining residue classes. We specialize those published algorithms to a translated interval and use integer block indices throughout. The formulas below describe the implementation. [Bostan, Gaudry and Schost, Theorem 5](https://specfun.inria.fr/bostan/publications/BoGaSc07.pdf) · [Costa and Harvey, Propositions 4–7](https://arxiv.org/abs/1201.2116)

## One convolution per doubling

Let $R$ be the invertible residues between 1 and $W-1$, let $b$ be a multiple of $W$, and let $h$ count complete cycles of length $W$. Define the polynomial
$$
F_h(j)=\prod_{s=0}^{h-1}\prod_{r\in R}\bigl(b+W(hj+s)+r\bigr).
$$
Its degree is $d=h|R|$. Pairing neighboring blocks gives $F_{2h}(j)=F_h(2j)F_h(2j+1)$. Lean proves this identity for any commutative monoid and verifies that the blocks and their tail cover all complete wheel cycles. The implementation handles partial cycles at the original interval edges directly. The tests compare its full result with literal multiplication. [Block and coverage proofs](../PrimeFactors/FactorialProgressions.lean) · [Edge and interval tests](../tests/test_factorial_progressions.py)

Once $F_h(0),\ldots,F_h(d)$ are known, the next doubling needs more values at consecutive integer indices.

For $t>d$ the Lagrange formula at the nodes $0,\ldots,d$ is
$$
F_h(t)=\frac{t!}{(t-d-1)!}
\sum_{i=0}^d \frac{(-1)^{d-i}F_h(i)}{i!(d-i)!}\,\frac{1}{t-i}.
$$
The sum at each new index $t$ is coefficient $t-1$ of the convolution of the weighted samples with $1,1/2,1/3,\ldots$. A single convolution therefore supplies the entire extension for a doubling. A forward factorial table, one modular inversion and a backward pass give the needed inverses whenever the largest required factorial is a unit modulo $N$. A nonunit exposes a gcd, which the search refines if it equals the full modulus. At either edge the search multiplies the few wheel candidates outside complete blocks directly. [Exact implementation and tests](../tests/test_factorial_progressions.py)

The program offers two exact convolution backends. The binary backend uses the repository's existing packed integer multiplication. The decimal backend uses fixed-width digit groups and Python's standard-library decimal multiplication. Each digit group is wider than the largest possible coefficient of the ordinary convolution, and the decimal precision covers the full packed product. Each recovered coefficient can then be reduced modulo $N$ independently.

## What changed in the 63-bit comparison

All variants below used the same interval on $6{,}091{,}663{,}632{,}054{,}090{,}929$. Its smaller factor is $2{,}423{,}330{,}473$. Times are medians of three local runs with CPython 3.9.6 on an arm64 Mac running macOS 27.0.1. They measure discovery alone. [Earlier comparison](../experiments/norm_comparison.py)

| Evaluation | Candidates | Seconds |
| --- | --- | ---: |
| General polynomial trees, stop at first successful block gcd | Odd integers | 3.42 |
| General polynomial trees, compute the entire interval product | Odd integers | 3.46 |
| Consecutive-index shifts, binary packing, entire product | Odd integers | 0.56 |
| Consecutive-index shifts, decimal packing, entire product | Odd integers | 0.15 |
| Consecutive-index shifts, decimal packing, entire product | Coprime to 210 | 0.11 |

Both complete odd-only methods returned the identical modular product. Changing the evaluation algorithm with binary packing held fixed reduced the time about sixfold. With $W=210$ the 63-bit interval needed eight convolutions and 13,446 block products. Together with the directly handled edges these covered 165,233,925 admissible integers.

The independent 79-bit input is the first accepted draw from the repository sampler with ASCII seed `factorial-progression-holdout-v1` (attempt two, counting from zero). Twelve convolutions and 250,982 blocks covered 49,345,138,593 admissible integers. The resulting residue was $209796968848141314860187$, whose gcd with the input was $622358546533$. The prime labels served only to check the result. [Sampler](../experiments/crt_holdout.py) · [Inputs and work counts](../benchmarks/factorial-progressions.json)

For a fixed wheel, the degree and number of blocks both grow on the order of the square root of the interval length. For balanced semiprimes that gives fourth-root growth in $N$, up to logarithmic factors in the arithmetic cost. Using the full balanced interval on the crossed 2,048-bit control would require a polynomial of degree $48\cdot 2^{504}$ with the implemented block choice. Its capped run covered 29,959 wheel candidates with two convolutions and a final gcd of one. [2,048-bit control](../benchmarks/factorial-progressions.json)
