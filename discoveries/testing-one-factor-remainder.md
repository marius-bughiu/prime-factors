# One guess that split a 2,048-bit test number

The first four groups in our earlier search missed both factors of the crossed 2,048-bit test number. We have since found them by testing a single different group. The search took 2.21 seconds on an arm64 Mac. Lean separately checked that the two 1,024-bit answers are prime and multiply to the input. **We picked the group after looking at the published factors.** Only the product was passed to the calculation. [Checked factors and certificate](https://marius-bughiu.github.io/prime-factors/#unit-lane-crossed-2048) · [Original construction](line-powers.md)

The guess was that one prime leaves remainder 1 when divided by $2^{616}$. One prime in this example actually leaves remainder 1 even when divided by $2^{984}$. That unusually long run of known binary digits is what made the recovery possible. On a smaller example, the same rule chooses the divisor 128 from the bit length of 69,133. Writing the unknown factor as $1+128k$ leaves the integer root $k=2$ in the allowed interval. That gives 257, and division gives 269. [Search code](../experiments/unit_factor_lane.py) · [Why the polynomial contains the factor](polynomial-factor-lanes.md)

## Replaying the guess on the full-size examples

We kept the guess fixed and replayed it on all nine distinct balanced 2,048-bit products with complete prime-factor labels in the benchmark at revision `4e5c2a6`, plus the crossed product. The same ten products and the same public rule can be replayed with `python3 -m experiments.unit_lane_panel`. Search times below exclude certificate generation and Lean verification. The input primes were constructed for earlier experiments. Two successes share one of their primes. [Replay and selection rule](../experiments/unit_lane_panel.py) · [All inputs, work counts and outcomes](../research/unit-lane-panel.json)

| Outcome | Products |
| --- | --- |
| Both primes recovered | Predecessor square (2.38 s), planted gap (0.05 s), crossed comparison (2.21 s) |
| Entire product left unresolved | Maximal-score Fermat, continued square, gap stride, Dickson square, polynomial packet, reduced order, shifted square |

The radix is chosen before any search. For a product of bit length $b$, choose the smallest power of two $R$ satisfying $R^{20}>5^5 2^{10+6(b+1)}$. This is the squared degree-four lattice bound with both balanced factors at most $X=\lfloor\sqrt{2N}\rfloor$ and $X^2<2^{b+1}$. The solver tests the entire group $x\equiv1\pmod R$ and checks every integer root against the product. When it misses, only this one group has been searched. Partial fixtures retain the full input as the unresolved cofactor. [Success and comparison fixtures](../benchmarks/quartic-factor-lanes.json)

For two randomly chosen 1,024-bit primes conditioned on a 2,048-bit product, the chance that even one of them has that fixed remainder is less than $2^{-590}$. Choosing a group from part of the product raises a different question. Even when a selector can ask 1,024 adaptive yes/no questions, each about either half of the product, and then try roughly a trillion guesses, its chance of hitting the correct group is less than one in 270 billion under this sampling model. Arithmetic that combines the two halves directly is outside that bound. [Counting proof and exact assumptions](factor-lane-advice.md)
