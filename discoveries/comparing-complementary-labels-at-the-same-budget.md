# Comparing two label searches on the same random inputs

Take a product $N=pq$ of two 1024-bit primes with $N \ge 0.99\cdot 2^{2048}$ and remainder 5 or 7 modulo 12. Give both searches the **same** sequence of randomly chosen inputs. With $105\cdot2^{504}$ accepted inputs, more than **7.5%** of sequences give the complementary-label search a factor even though the original search has no matching pair at either prime. This holds for each qualifying product. The randomness comes entirely from the search. [Lean comparison and joint event](../PrimeFactors/ComplementarySameBudget.lean)

The original search assigns a modular value $v$ to each input. The second assigns $v(1-v)$, so it recognizes both equal values and pairs whose values sum to one. A match at exactly one prime gives a proper divisor by a greatest common divisor calculation. Each input is drawn independently and uniformly, with replacement, from the residues passing two public tests. The original regularity mask must be coprime to $N$, and $2v-1$ must also be coprime to $N$. The theorem counts accepted draws. [Original mask and public values](../PrimeFactors/TwelveSeedBirthday.lean) · [Complementary values and their multiplicities](../PrimeFactors/ComplementaryBirthday.lean)

The complementary search finds a proper divisor on more than **95%** of these sequences. The original search has *any* local match on fewer than **87.5%**, even counting pairs that agree at both primes and could require extra tests to separate them. To prove the upper bound, let $d$ be the number of original values at one prime. For $m<d$ draws, the chance of seeing no repeat is at least

$$
\exp\!\left(-\frac{m(m-1)}{2(d-m)}\right).
$$

Each prime is at least $0.99\cdot2^{1024}$, and at most 25 residues per prime are filtered out. The remaining original values have exactly twelve preimages each. The two prime coordinates are independent, so the chances of avoiding a repeat multiply. [Finite probability and public gcd proofs](../PrimeFactors/ComplementarySameBudget.lean)

One checked example uses the primes $2^{1024}-26096496244809999$ and $2^{1024}-580951370506755599$. The improvement still takes about $5.5\times10^{153}$ accepted draws for this guarantee. Lean proves the probabilities without running a search of that size. [Prime certificates](../PrimeFactors/NearEndpointPrimes.lean)
