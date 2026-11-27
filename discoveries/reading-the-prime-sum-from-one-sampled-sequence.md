# Reading the prime sum from one sampled sequence

For $3{,}053=43\times71$, the complete even Jacobi sums repeat after 105 terms. Taking only every 1,526th term reduces the shortest repeat to 15. That length gives the prime sum 114. The experiment spent more time constructing the sequence than a direct search needed to find both factors. [Lean period theorem](../PrimeFactors/JacobiScalarStride.lean) · [Experiment and work counts](../experiments/jacobi_scalar_stride.py)

## Why the starting point matters

Here the first measured degree is $2s$, followed by $4s,6s,\ldots$. Projecting to a prime field groups the contributions with equal $s$th powers of square bases. In a group of odd size, a sum of signs $\pm1$ cannot vanish as an integer. Each group here is smaller than the field characteristic, so the same is true modulo the prime. One group can lose a term at the exceptional square 4. If the image has at least three elements, the surviving bases still give its full period. With even group sizes more cancellation is possible. At 221 and $s=110$, this specific sequence repeats after six terms even though a repeat shared by all offsets takes twelve. [Odd group sizes and the 221 counterexample](../PrimeFactors/JacobiScalarStride.lean) · [Checks at all starting points](testing-a-jacobi-stride-period.md)

## Removing the powers of two from the stride

For distinct odd primes $p<q<2p$, put $H=(N-1)/2$ and write $H=2^e s$ with $s$ odd. First try the two integer candidates $\lfloor(\lfloor\sqrt{8N+1}\rfloor+1)/4\rfloor$ and $\lfloor(\lfloor\sqrt{24N+1}\rfloor+1)/6\rfloor$ by division. These cover the cases where too few bases survive for the period proof. If neither is the smaller prime and $L$ is the shortest repeat of the sequence at degrees $2s,4s,6s,\ldots$, set

$$K=L\gcd(L,2^e),\qquad u=\left\lfloor\sqrt{\left\lfloor N/(4K)\right\rfloor}\right\rfloor,\qquad p+q=N+1-4u^2K.$$

The stride, the two trial candidates, and the conversion of $L$ to the sum use only $N$ and integer arithmetic. Measuring the exact $L$ is the outstanding cost. At 221, $s=55$ gives $L=24$, the correction factor is 2, and the formula gives 30. Blindly using the six-step repeat at stride 110 gives 6. [General balanced-input theorem and correction](../PrimeFactors/JacobiScalarStride.lean)

After the two division checks fail, a period guess at this odd stride can be tested **without computing any Jacobi sum**. Here the particular sequence has the same periods as a repeat shared by all starting positions. A proposed $t$ works if and only if every unit satisfies $x^{2st}=1\pmod N$. A single unit with a different power rejects it. If the exact scalar period $L$ is supplied, then removing $\gcd(L,2^e)$ from it by division also gives the shortest shared repeat at the original stride $H$. This accounts for the relationship between the two measurements and leaves the cost of selecting a useful guess explicit. [Lean single-sequence power test](../PrimeFactors/JacobiScalarPeriodProbe.lean)

## Work on the two small controls

The experiment calculated the Jacobi sign for every residue, grouped equal powered residues, and stopped when the full state of the nonzero weighted terms repeated. It then measured the shortest repeat of the scalar values within that cycle. This provides a finite check against mistaking a short coincidence for a repeat. At 3,053 the grouped-term updates fell from 77,070 to 210 with the shorter period. Each stride still needed 3,053 residue powers, on top of the shared 3,053 signs. Processing the 42nd sign already exposed a factor by gcd. Fermat's method took two square tests at 3,053 and one at 221. These examples measure the cost of the direct construction and were selected to exercise shortening and cancellation. [Decimal fixtures](../benchmarks/jacobi-scalar-stride.json) · [Period, gcd and Fermat comparisons](../experiments/jacobi_scalar_stride.py)
