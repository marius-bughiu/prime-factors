# Which genuine prime pairs can the weighted search miss?

For a family of actual 2,048-bit products, even a table of $2^{24}$ starting powers and $2^{894}$ blocks at **every** weight pair still stops before reaching the true weighted sum. The weights can depend on the entire product. The restrictions are that $1\le b\le2^{32}$, $b\le a\le2b$, and the blocks start at the usual first permitted value of $ap+bq$. Under the stated prime-count estimates, this family accounts for more than one in $2^{43}$ uniformly chosen target pairs. This answers a limitation of the continuous scheduling model, where a difficult ratio might never occur for two primes. [Lean gap and population proofs](../PrimeFactors/TraceGapPopulation.lean) · [What the complete schedules cost](the-minimum-weighted-search.md)

## How the gap makes every guess miss

Write $N=pq$ with $2^{1023}\le p<q<2^{1024}$. Consider the range $2^{975}\le q-p\le2^{990}$. If $a=b$, the distance between $ap$ and $bq$ is at least $b2^{975}$. If $a>b$, then $ap-bq=(a-b)p-b(q-p)\ge p-2^{32}2^{990}$, again at least $b2^{975}$. Every eligible direction therefore misses exact equality by a known amount, including directions chosen after reading the product.

The weighted trace obeys $(ap+bq)^2=4abN+(ap-bq)^2$. Its first candidate is the smallest integer at least $2\sqrt{abN}$ in its public residue class, with step $s\le24$. If the trace lies in the first $g$ blocks of $m$ labels, the previous candidate and the true trace give
$$
(ap-bq)^2 < 2(ap+bq)\,s(1+mg).
$$
Inserting the gap lower bound, $ap+bq\le3b2^{1024}$, and the stated budgets contradicts that strict inequality. The proof excludes a true weighted exponent at any of those indices. A search that can jump to a later index, use other weights, or split the input through an incidental group-order collision has additional ways to succeed. [Trace progression](../PrimeFactors/TraceProgression.lean)

## Why the gap occurs among primes of the target size

Put $X=2^{1023}$ and take the primes in $[\sqrt2X,2X)$. Every distinct pair gives a product of exactly 2,048 bits. The published prime-count estimates give more than $0.22X/\log X>2^{1011}$ primes there, and fewer than $1.511X/\log X<2^{1015}$ primes in all of $[X,2X)$. Thus the total number of eligible ordered pairs is below $2^{2030}$. These prime-count bounds are the explicit external inputs to the Lean population theorem. [Source and constants](stride-budget.md#an-explicit-bound-at-exactly-2048-bits) · [Rosser and Schoenfeld](https://doi.org/10.1215/ijm/1255631807)

Partition $[X,2X)$ into $2^{33}$ bins of width $2^{990}$. Within a bin, for each prime $p$, at most $2^{977}$ integers are closer to $p$ than $2^{975}$. A Cauchy–Schwarz count on the prime occupancies, subtracting this allowance in each bin, gives more than $2^{1987}$ ordered pairs at the required separation. Sorting the two primes preserves the fraction because each unordered pair occurs twice. No estimate for the number of primes in any individual bin is needed. [Finite counting inequality](../PrimeFactors/SeparatedPairs.lean)
