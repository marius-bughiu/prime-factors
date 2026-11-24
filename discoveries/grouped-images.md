# The cost of grouping giant steps by their quadratic signs

A giant record supplies a public sign at each selected prime where its quadratic coefficient is nonzero. Separate baby tables can use a single quadratic image at primes whose signs agree within the group. The saved entries must cover building and searching every group’s table. Equal sign frequencies rule out a gain in the exponential constant in this model. On actual lattice records, primes congruent to 3 modulo 4 exhibit an exact symmetry that forces equal frequencies. [Quadratic image of the actual index, Lemma 3.4](https://arxiv.org/html/2611.06580v1#S3)

## How much of the table must a group retain?

Let $A_i^+,A_i^-$ be an optimal translated pair of local images at coordinate $i$. Both contain $a_i$ points, and their union has $u_i$ points. Put $U=\prod_i u_i$, $M=\prod_i\ell_i$ and $\rho=U/M$. For any group of sign patterns $P\subseteq\{+,-\}^t$, its table size per complete period obeys
$$
 |B(P)|\ \ge\ \frac{|P|}{2^t}U.
$$
This allows a separate translation at every coordinate for every pattern. Coordinate compression reduces any such choice to the canonical sets without increasing its union. To count the compressed union, pick a uniform point in the full product of the local unions. Independently at each coordinate, select a sign containing the sampled point, breaking ties by a fair coin. The two exclusive regions have equal sizes, so each selected sign is fair and the sign vector is uniform. If it belongs to $P$, the point necessarily belongs to the compressed union. Lean proves the integer inequality by giving a unique sign two votes and each sign at a shared point one vote. [Finite sign-mass theorem](../PrimeFactors/GroupedImages.lean) · [Coordinate compression](coupled-image-sieve.md)

For example, splitting $k$ coordinates into all $2^k$ exact sign patterns multiplies the **sum** of the table sizes, at a common span, by $\prod_{i\le k}(2a_i/u_i)$. For large primes this is approximately $(4/3)^k$. Each table is smaller and each record is queried only in its own table.

## Different chunk widths and actual giant multiplicities

Take an original index span of length $L$ and $G$ public records. Group $j$ contains a fraction $p_j$ of the records and occupies local density $\rho_j$. For a positive integer chunk width $w_j\le L$, it charges $G p_j\lceil L/w_j\rceil$ giant records. A reusable complete-period table for the translated window of length $w_j+M$ has at least $\rho_j w_j$ entries and at most $\rho_j(w_j+2M)$. This accounts for the possible CRT translation in each chunk. The necessary baby and giant records together therefore cost at least
$$
 2\sqrt{GL}\sum_j\sqrt{p_j\rho_j}.
$$
If sign patterns occur equally often, $p_j=|P_j|/2^t$ for a partition and the finite inequality gives $\rho_j\ge\rho p_j$. The sum is at least $\sqrt\rho$. Varying the group widths cannot reduce the balanced continuous baby/giant benchmark $2\sqrt{\rho GL}$ in this model. The unconditional charge for visiting the $G$ original records also remains. A bound restricted to complete periods does not give a matching density estimate on arbitrary short partial intervals.

An actual input can have unequal frequencies. For groups fixing the signs at a prescribed $k$ primes, each nonempty group has density $\rho'=\rho\prod_{i\le k}(a_i/u_i)$. Clipping and rounding $w_j=\sqrt{G p_j L/\rho'}$ to $[1,L]$ gives a total upper bound
$$
 O\!\left(G+\sqrt{\rho'GL}\sum_{j:p_j>0}\sqrt{p_j}
                  + |\{j:p_j>0\}|\,\rho' M\right)
$$
on records, for nonempty groups. Local sets can be listed once at each prime. Enumerating each group's CRT product directly costs at most $t$ combinations per retained residue. Sorting, powers, exact-match checks and arbitrary-point multipoint evaluations add polylogarithmic factors as in the source. Counting the patterns and assigning records costs $O(tG)$ elementary operations. If $(\sum_j\sqrt{p_j})^2<\prod_{i\le k}(u_i/a_i)$, the square-root term improves over the ungrouped one. A speedup also requires controlling the original $G$ records, the per-group CRT periods and the other stages of factorization. Coordinates with zero quadratic coefficient need their separate exception allowance. [Collision and cost estimates, Lemmas 3.9–3.11](https://arxiv.org/html/2611.06580v1#S3)

## A symmetry of actual shortest-vector records

Fix a squarefree $m$, an interval anchor, and one attainable value of $\sigma^2\bmod m$. The lattice only depends on $N/\sigma^2\bmod m$. Use the same deterministic vector and global sign convention for this entire fiber. Write the common vector $(a,b)$. At a usable odd $\ell\mid m$, its local leading sign equals $\chi_\ell(aN\sigma^{-3})=\chi_\ell(aN\sigma)$. Independently replacing $\sigma$ by its negative at any chosen prime preserves its square, the selected vector and its degeneracy set. This flips the leading sign exactly at the changed usable primes that are $3\bmod4$. Each possible joint pattern on these coordinates thus occurs equally often, even after all the other leading signs in the fiber are fixed. This applies to the public enumerated records. It makes no distributional claim about the unknown factor.

For $N=150235091$, $m=77$, anchor $10007$ and $m_0=1$, the reference shortest-vector routine gives 14 square fibers with $\gcd(a,77)=1$. Each contains all four patterns at 7 and 11, so the 56 records give exactly 14 occurrences per pattern. With $m=65$ at the same input and anchor, the 40 regular records at 5 and 13 have counts $8,12,16,4$ in the order $(++,+-,-+,--)$. Each square fiber there has just one pattern. Building a separate table per fiber would need its own cost analysis. The counts follow by evaluating the source routine once for every unit $\sigma\bmod m$ and testing the displayed Legendre symbol. [Shortest-vector reference](../experiments/short_basis_sieve.py)

These results account for grouping the full translated images available to a record, even with adaptive public multiplicities and different group widths. A stronger worst-case factorization bound from grouping would require an additional restriction on the patterns or a way to share the work across groups.
