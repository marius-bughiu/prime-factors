# Can one search plan find the factors of a different number?

Yes, at the sizes where we can run the search. We made four plans before searching twelve new 88-bit and 89-bit numbers. Each search received only the product, picked a plan by taking the remainder after division by 12, and recovered both primes. For example, it split 182,657,281,181,428,171,915,664,953 into **12,695,994,837,749 × 14,387,000,271,797**. Each product in this experiment has 27 decimal digits. A 2,048-bit number has 617. [Experiment and input construction](../experiments/trace_cover_transfer.py)

## How much work did reuse save?

The twelve products were chosen by a fixed seed, six at each bit length. The input list spans all eight possible remainders modulo 24 for integers coprime to 6. We kept the weights, the table of 53,130 starting powers, and the factor-search engine fixed. We rotated the order of the four methods over four trials on each input. Times below sum the median wall time for each product. They cover finding the factors. The independent Lean checks run afterwards.

| How the search chose a plan | Search blocks across 12 inputs | Time across 12 inputs | One-time preparation |
| --- | ---: | ---: | ---: |
| Build four plans and reuse the matching one | 389,708 | 10.90 s | 0.81 s |
| Build a fresh fast plan for each product | 357,993 | 11.96 s | Included per input |
| Use the original weighted search | 490,051 | 14.51 s | Included per input |
| Reuse the same previously optimized 89-bit plan for every product | 467,512 | 12.63 s | 0.22 s to load and prepare it, plus 155 s to find it originally |

The four-plan search did more block checks than the fresh fast planner. Skipping repeated planning paid for those extra checks on this machine. Including all four preparations gives **11.70 seconds versus 11.96 seconds** for the panel, a difference of about 0.26 seconds. Timings can vary by that much on another run. The block counts are exact. The one-plan experiment also shows a limit of reuse. A plan carefully optimized for one product can be expensive on another. [Trial data, construction, timing scope and certificate replay](../research/trace-cover-transfer.json)

## Why a plan transfers

Suppose the hidden primes obey $p\le q\le 2p$. Partition the possible ratios $x=q/p$ from 1 to 2 into intervals. In one interval a chosen pair of weights $a,b$ tells us which values of the sum $ap+bq$ to search. At any fixed ratio its distance above the theoretical minimum is

$$ap+bq-2\sqrt{abN}=\sqrt N\left(\frac{a+bx}{\sqrt{x}}-2\sqrt{ab}\right).$$

The part in parentheses depends only on the ratio and weights. If the product gets smaller, the same interval therefore needs a narrower range of sums. The step between admissible integer sums depends only on the weights and the product modulo 12. Its starting point still changes with the product. Lean proves that **one extra candidate per interval is always enough** when transferring to a smaller positive product in the same class. The experiment reuses the intervals and recalculates the exact range from their endpoints, which can take advantage of further shrinkage. A template can be any appropriate public integer. We never need its factors. [Transfer theorem and exact rounding rule](../PrimeFactors/TraceCoverTransfer.lean)

For an example where that extra candidate matters, the weighted sum for $899=29\times31$ with weights 3 and 2 is $3\cdot29+2\cdot31=149$. At the ratio $31/29$, a template built on 1,763 needed one slot starting at 207. Moving to 899 gives a new first slot at 147. The *second* slot, 149, contains the true answer. Both products have remainder 11 modulo 12. Lean checks the primality, both starting values, and all the comparisons. [Checked example](../PrimeFactors/TraceCoverTransfer.lean)

For different step sizes $d_0,d$, let the old row have $t$ candidate sums and the two public products be $N_0,N$. A target budget $u$ suffices whenever $N[d_0(t+1)]^2\le N_0(du)^2$. The smallest integer satisfying this condition is computable from the products. An exact endpoint calculation can use fewer slots. The proof uses integer arithmetic and the shape of the weighted sum over the ratio interval. Costly operations still include building the table of powers and testing the blocks for each product. [General price and its proof](../PrimeFactors/TraceCoverTransfer.lean) · [Earlier measured table costs](the-minimum-weighted-search.md)

## What does this buy at 2,048 bits?

For **every** 2,048-bit product of two 1,024-bit primes, Lean checked that a plan built solely from the product contains the true weighted sum in at most **19 blocks**. Each block spans **$2^{1011}$ candidates**. Processing such blocks with the shared-table method calls for $2^{1011}$ starting powers, a 305-digit number of entries. We verified coverage algebraically. Building that table is beyond the resources of a normal PC. [Universal theorem](../PrimeFactors/UniversalTraceCover.lean)

The plan selects one of 32 templates by splitting the product range into eight equal intervals and then checking the product modulo 12. For interval $j=0,\ldots,7$ the public lower bound is $N\ge(8+j)2^{2044}$. Since $q<2^{1024}$, the ratio obeys $q/p=q^2/N<16/(8+j)$. The eight worst block totals across the four remainder classes are **19, 17, 16, 13, 12, 11, 8, 3** in order of increasing product size. A product near the top of the range forces the two primes closer together. The 32 short rational partitions can be regenerated independently. [Witness generator](../experiments/universal_trace_cover.py)

Even if someone picked the best weight in advance and let us vary the table size freely, the two full-size comparison products each need over $10^{152}$ entries to reach their true weighted sum this way. [Exact costs and how often early hits are possible](how-often-a-weighted-search-reaches-the-factors.md)
