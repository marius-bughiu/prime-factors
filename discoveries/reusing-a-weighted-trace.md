# How far can one weighted factor equation reach?

On eight fresh 38–42-bit products, reusing one product-chosen equation until it ceased to cover the next integer took 2,285 equations to cover the complete eligible ranges. The same mod-24 equations on fixed windows took 5,404. Keeping a second separated interval saved just one more equation. Each search found all eight prime pairs from the products alone. [Search and sampling code](../experiments/weighted_trace_reuse.py)

For positive weights `a,b`, a possible divisor `d` gives the trace `F(d)=a*d+b*N/d`. Our earlier method chooses the weights by continued fractions at the requested center. All odd factor pairs have the same trace parity. If the product is coprime to six, shifted weights can force one residue modulo 24. Write `z` for the chosen trace and `s` for the stride (2 or 24). Every true divisor with `z-s < F(d) < z+s` must solve the single equation `a*d²-z*d+b*N=0`. Its discriminant needs at most one integer square root however many positions share it. [Existing prescribed-center proof](ruling-out-an-interior-interval.md) · [Mod-24 proof](../PrimeFactors/UniversalTraceWindow.lean)

The search obtains the exact integer endpoints by multiplying by the positive divisor coordinate. For an integer level `h`, the inequality `F(d)<h` is equivalent to `(2ad-h)² ≤ h²−4abN−1`. It computes that outer interval at `h=z+s`, then removes the closed interval `F(d)≤z−s`. This uses up to two extra integer square roots. The remaining set has at most two components. The connected version advances past the component at the current search frontier. The second version also records any later component in a priority queue. Both account for the mark before advancing, and every returned divisor is checked by division. [Endpoint arithmetic](../experiments/weighted_trace_reuse.py) · [Exhaustive endpoint tests](../tests/test_weighted_trace_reuse.py)

Hiary already proposed a variable rightward step depending on the quality of the continued-fraction approximation in section 4. The experiment compares that published 0.4/0.6 rule on the same public equal-width range, with a left allowance computed at the smaller, uncovered endpoint and with a parity check. The exact polynomial inversion, the bookkeeping of disconnected components and their measured costs are the comparisons here. The existing lower bound already allows both components free of any extra charge and permits the direction to depend on the product. On the fresh 2,048-bit input, covering the entire feasible interval with strips of width four still takes more than $2^{675}$ strips. The latter exponent applies to parity strips; a single mod-24 strip has greater width. [Hiary’s paper, section 4](https://arxiv.org/pdf/1408.2608#page=4) · [Strip-count assumptions](limits-of-linear-divisor-windows.md)

| Complete cover on the first eight products | Setups | Euclidean divisions | Boundary square roots | Discriminant square roots |
| --- | ---: | ---: | ---: | ---: |
| Hiary asymmetric comparison | 13,981 | 81,914 | 13,981 | 2,760 |
| Fixed parity | 12,387 | 69,619 | 0 | 3,468 |
| Connected parity | 5,191 | 30,045 | 5,326 | 3,950 |
| Both parity components | 5,139 | 29,812 | 5,259 | 3,963 |
| Fixed mod 24 | 5,404 | 27,940 | 0 | 1,507 |
| Connected mod 24 | 2,285 | 12,189 | 2,392 | 1,721 |
| Both mod-24 components | 2,284 | 12,191 | 2,391 | 1,725 |

On a separately seeded sample of eight more products, we selected the trace giving the longest certified forward extension among the positive convergents already generated at the frontier and either adjacent admissible trace. A fast guard compares the continuous minimum and maximum on a proposed extension. This is a choice among those trials; no optimality across arbitrary weights is assumed. Against taking the final eligible convergent and keeping both components, full-cover setups fell from 2,663 to 1,895 and discriminant roots from 2,060 to 1,890. Boundary roots rose from 2,765 to 3,454, with 16,791 additional guard checks. In one local run, CPU time rose from 12.2 to 23.2 ms. Stopping at the first factor took 1,045 versus 743 setups. Lean checked every factorization. On each 2,048-bit control, eight setups left the input unresolved. The selector used 3,082 and 3,381 extra guards respectively and advanced less than $2^{348}$ positions on either input.

The two SHAKE seeds, bit widths and draw order are in the experiment. Expected factors validate only the returned pair. Reproduce either comparison with a complete coverage and first-hit run, including primality checks:

~~~sh
python3 -m experiments.weighted_trace_reuse --verify
python3 -m experiments.weighted_trace_reuse --frontier --verify
~~~
