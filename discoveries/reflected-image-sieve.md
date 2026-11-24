# The exact saving from reflecting a giant step

Suppose a public giant step $v$ has a possible collision $\alpha^i=v\bmod p$ at an unknown prime factor $p$, with $0\le i\le L$. At each selected odd prime $\ell$, suppose the possible indices of this giant lie in a known translate of one quadratic image of nonzero leading coefficient. Stănică proves this property for the regular giant steps of the Harvey–Hittmeir search. The square class of the leading coefficient is known for each giant. A shared baby table must work with both possible classes. [Stănică, Lemma 3.4 and Proposition 3.12](https://arxiv.org/html/2611.06580v1#S3)

One may reflect the entire exponent $i$ once for each giant. If **all sign patterns must be supported** and a table is constructed for **complete periods of the sieve modulus**, the smallest possible table consists of the usual two-image union at every prime, except that one prime $\ell\equiv3\bmod4$ uses just the square image. The best such prime is the largest one available. The fraction of the ordinary table retained is exactly
$$
 \frac{2(\ell+1)}{3\ell-1}.
$$
It approaches $2/3$ even when arbitrarily many primes are available. If there is no prime congruent to 3 modulo 4, reflection leaves the optimum unchanged. This result permits arbitrary CRT translations dependent on the *whole* pattern, and arbitrary common table subsets.

## Construction and recovery

Write $Q_\ell$ for zero together with the nonzero squares, and $Q'_\ell$ for zero together with the nonsquares. Completing the square identifies the local image as $u_\ell+Q_\ell$ or $u_\ell+Q'_\ell$. A canonical pair of translated local sets is $A_\ell=Q_\ell$, $B_\ell=1+Q'_\ell$. Each has size $a_\ell=(\ell+1)/2$. Their union has the minimum possible size over all pairs of translations,
$$
 U_\ell=\ell-\frac{\ell-\chi_\ell(-1)}{4}.
$$
This is Stănică's exact local translation result. Multiplying the index by $-1$ reverses the leading sign at precisely those primes with $\chi_\ell(-1)=-1$. [Stănică, Propositions 3.5–3.6](https://arxiv.org/html/2611.06580v1#S3)

Choose a prime $j\equiv3\bmod4$. For a giant whose sign there is already positive, shift its exponent to $e=i+c$ and replace $v$ by $\alpha^c v$. For a negative sign there, use $e=L-i+c$ and replace $v$ by $\alpha^{L+c}v^{-1}$. In the latter case, the new local image is $L-u_\ell$ plus the quadratic class with its sign multiplied by $\chi_\ell(-1)$. In both cases, take $c$ modulo each prime to move the image into its canonical $A_\ell$ or $B_\ell$. CRT gives a unique $0\le c<M$, where $M$ is the product of the selected primes. The resulting index always belongs to $A_j$ at the chosen prime and $A_\ell\cup B_\ell$ at every other prime. Both orientations use the single span $0\le e<L+M$. The complete period therefore contains exactly $a_j\prod_{\ell\ne j}U_\ell$ exponents. [Lean collision and decoding proofs](../PrimeFactors/ReflectedImages.lean)

Store each giant's orientation and $c$. At an exact group match decode $i=e-c$ for an ordinary giant or $i=L-(e-c)$ for a reflected one, checking $c\le e\le c+L$ first. Use the original giant's coefficients and this $i$ in its usual integer factor test. Stănică's factor-order certification over the common span ensures that a genuine giant's exact match determines its correct exponent. At collisions modulo just one prime, the same difference gcd and product-tree search give the factor directly. Equality and inequality modulo any divisor are preserved by multiplying both group elements by a unit or by inverting both. [Stănică, Lemmas 3.9–3.11 and exact-match handling in Proposition 3.12](https://arxiv.org/html/2611.06580v1#S3)

## Why no pattern-dependent choice improves the table further

Let $T$ be the set of flippable coordinates, and suppose first that $T$ is nonempty. Reflection gives one involution on the sign cube that flips *all* coordinates in $T$ and fixes the rest. Supporting every pattern means that the chosen oriented patterns contain at least one member of each two-element orbit. For a lower bound, discard any additional representatives and retain one translated box per orbit.

**Compression of translations.** Fix a coordinate $\ell$ and a fiber obtained by holding all other residues fixed. The active boxes contribute zero sets, a collection of translates of just one sign, or a collection involving both signs. Their union sizes are respectively zero, at least $a_\ell$, or at least $U_\ell$. Replace the local factor of every positive box by $A_\ell$ and every negative one by $B_\ell$. This attains precisely the three lower bounds on every fiber simultaneously. The active boxes on a fiber were determined solely by the other coordinates. Repeating this step coordinate by coordinate shows that the union of the canonical boxes is no larger than any choice of pattern-dependent translations.

**Counting the canonical union.** Choose a uniform point of $\prod_\ell(A_\ell\cup B_\ell)$. Each coordinate forces one sign or allows both. By equality of the two set sizes, the forced sign is fair; the probability of allowing both is
$$
 e_\ell=\frac{2a_\ell-U_\ell}{U_\ell}.
$$
Different coordinates are independent. Condition on any point in the unflippable coordinates and select one compatible sign pattern there. Among its extensions, the chosen representatives define a function $f:\{-1,1\}^T\to\{-1,1\}$ with $f(-z)=-f(z)$, where $+1$ indicates selection. In particular $f$ is balanced. In $T$ the random point corresponds to revealing fair signs, independently erasing sign $\ell$ with probability $e_\ell$. The point lies in a selected box whenever the resulting restriction admits a $+1$ completion.

Under simultaneous reversal of the revealed signs, all-positive and all-negative restrictions have equal probability. Thus the probability of admitting a $+1$ completion is $(1+\Pr[\text{the restriction admits both outputs}])/2$. To bound the second probability, expand $f(z)=\sum_D\widehat f(D)\prod_{\ell\in D}z_\ell$ in the orthonormal sign characters. Its constant coefficient vanishes and the squared coefficients sum to one. Conditional expectation given the reveals kills each term involving an erased sign. Orthogonality therefore gives
$$
 \mathbb E\,\operatorname{Var}(f\mid\text{reveals})
 =1-\sum_{D\ne\varnothing}\widehat f(D)^2\prod_{\ell\in D}(1-e_\ell)
 \ge \min_{\ell\in T} e_\ell.
$$
Conditional variance is zero on a constant restriction and at most one otherwise. The claimed union fraction is consequently at least $(1+\min_{\ell\in T}e_\ell)/2=\min_{\ell\in T}a_\ell/U_\ell$. This bound holds for every conditioned point in the other coordinates. Fixing the sign at a single minimizing coordinate attains it. On $T$, $a_\ell/U_\ell=2(\ell+1)/(3\ell-1)$ decreases with $\ell$. If $T$ is empty, all sign patterns themselves must occur after orientation, and the compressed union is simply the full Cartesian union.

## Finite check and work

For $\ell=7,11,19$ the canonical union sizes are $5,8,14$. The ordinary table contains $560$ residues per period $1463$. Orienting at 19 reduces this to $400$. Each of the four antipodal sign pairs has two choices. Lean exhausts all $16$ choices after compression and verifies that none falls below $400$. [Finite counts and exhaustive check](../PrimeFactors/ReflectedImages.lean)

For the constructive optimum one can precompute each local retained list in $O(\sum_\ell\ell)$ word operations by marking squares and their translated complements. Assemble the $P=a_j\prod_{\ell\ne j}U_\ell$ CRT residues from these lists recursively, charging $O(sP)$ CRT combinations for $s$ primes. Sort them, then lift through complete periods and clip the last partial period. For a half-open exponent span of length $D=L+M$, the number $H$ of emitted baby exponents satisfies $P\lfloor D/M\rfloor\le H\le P\lceil D/M\rceil$. This construction uses $O((\sum_\ell\ell+sP+H)\operatorname{polylog}(N+M+L))$ bit operations, including forming the modular powers. For each of $G$ regular giants, computing its $s$ translated residues, combining them by CRT, and applying a power and possibly a unit inversion takes $(s+1)\operatorname{polylog}(N+M+L)$ bit operations once its coefficients are available. Known sparse multipoint evaluation and collision retrieval still cost $(G+H)\operatorname{polylog}(N+M+L)$. Other search stages, including generating regular coefficients and treating skinny giants, remain part of the overall runtime. [Stănică, Proposition 3.12](https://arxiv.org/html/2611.06580v1#S3)

The lower bound concerns explicit containment of **every complete local image box** for every pattern. A particular set of coefficient vectors may realize fewer patterns. The actual unknown divisor supplies only one index per relevant giant, and a partial period need not have the same density as the whole group. The constant saving therefore describes the universal complete-period baby table. It gives neither a factorization timing estimate nor an exponential improvement in the number of sieve primes.
