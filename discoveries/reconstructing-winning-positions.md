# Jumping to candidate positions from small remainders

We reduced the size of a **guaranteed complete search** for two distinct 1,024-bit primes. Listing coprime positions in the old range takes more than $2^{1019}$ entries on a 2,048-bit product. The new method covers every winning position using fewer than $2^{901}$ combinations of remainders. One combination reconstructs at most one possible position. Reconstruction takes more work than testing one old entry, and the resulting list is still far too large for practical full-size factorization. Known general factoring algorithms have better asymptotic bounds. [Old range and cost](complete-offset-work.md) · [Local counts and target bound](../PrimeFactors/OffsetProjectiveSlopes.lean) · [Reconstruction theorem](../PrimeFactors/OffsetCRTReconstruction.lean) · [Harvey and Hittmeir](https://arxiv.org/abs/2105.11105)

On 134,683,853 a complete run tested 4,536 combinations, reconstructed 157 positions in the search range, took 156 integer square roots, and returned **8,231 × 16,363**. The old complete scan visited 7,837 positions and took 4,710 square roots. The new scan computed 19,791 continued-fraction convergents. Locally the old and new complete scans took about 2.4 ms and 16.5 ms respectively. We selected this example from a panel for its smaller number of combinations. On 1,891 the new method tries 120 combinations for an old range of only 35 positions. [Run the search](../experiments/offset_crt_reconstruction.py)

## Which remainders survive?

Given the product $N$, compute $T=\lfloor\sqrt N\rfloor$, $h=N-T^2$, $J=\lfloor\sqrt{4h/3}\rfloor$, $K=\lfloor TJ/h\rfloor+1$. Every winning pair of positive coprime numbers $j,k$ lies in the box $j\le J$, $k\le K$. Its discriminant $D=(j+2Tk)^2-4Nk^2$ is a nonnegative square. We know one or two such pairs yield prime factors. [Winning-count proof](one-or-two-winning-tests.md)

For each selected odd prime $\ell$ coprime to $N$, record the slope $r=j/k\pmod\ell$ when $k\not\equiv0$. Otherwise record one special value $\infty$. At any winning finite slope, $(r+2T)^2-4N$ is a square modulo $\ell$. All the allowed values of $r$ can be computed as $x+N/x-2T$ for $x$ running over the nonzero residues. Pair $x$ with $N/x$. Fixed points occur precisely at square roots of $N$. Including $\infty$ gives exactly $(\ell+1)/2$ or $(\ell+3)/2$ choices according as $N$ is a nonsquare or a square modulo $\ell$. A prime which divides the composite input already gives a factor. [Finite-slope characterization and count](../PrimeFactors/OffsetProjectiveSlopes.lean)

Choose all primes from 5 through 743. This gives 130 prime moduli. Their product $M$ exceeds $2JK$ on every target input. Indeed $J^2\le4h/3$ implies $2JK\le 8T/3+2J$. The product of the 130 upper bounds $(\ell+3)/2$ is less than $2^{901}$. The bounds on $M$, the number of choices and the primality of the list are finite checks in Lean. A prefix can suffice on smaller inputs. [Target modulus and tuple bounds](../PrimeFactors/OffsetProjectiveSlopes.lean)

## How one combination determines a position

Let $I$ be the product of primes for which the chosen entry is $\infty$. Then $I\mid k$, so write $k=Iv$. Let $m=M/I$ and combine the remaining finite slopes by the Chinese remainder theorem into $R\bmod m$. Put $a=(RI)\bmod m$. The required congruence is $j\equiv av\pmod m$, hence $av-j=wm$ for an integer $w$. Coprimality of $j$ and $k$ implies that $w$ and $v$ are coprime. The strict bound $2JK<M$ gives

$$\left|\frac{a}{m}-\frac{w}{v}\right|=\frac{j}{mv}<\frac{1}{2v^2}.$$

By Legendre's criterion, $w/v$ appears among the continued-fraction convergents of the **known** rational $a/m$. For each convergent, compute $k=Iv$ and $j=av-wm$. Check the original positive bounds, coprimality, the sharper row limit $k\le\lfloor Tj/h\rfloor+1$, the discriminant and its gcd. To see uniqueness, two compatible primitive fractions have $jv'-j'v$ divisible by $m$ while its absolute value is smaller than $m$. Their cross-products agree and reduced fractions are unique. This handles denominators that vanish at some selected primes. The winning position in the 134,683,853 example has $k=35$, so it uses the infinity entry at both 5 and 7. [Lean proof](../PrimeFactors/OffsetCRTReconstruction.lean) · [Continued-fraction criterion used by the project](../PrimeFactors/SharedRootSigns.lean)

Enumeration can stream one tuple at a time. The prime masks, residue arithmetic and continued-fraction computation need polynomial space in the bit length and the sum of the mask sizes. Each reconstruction has polynomial arithmetic cost. The tuple count is a worst-case limit on the number of reconstructions, and it does not predict the first-hit time. On our two full-size inputs, the fixed masks give about $2^{898.58}$ and $2^{899.27}$ tuples. In the first 64 tuples on each input the program reached three and one square tests respectively, with no factor. The capped runs remain partial.

### How the size grows with larger inputs

The same construction can be extended beyond the fixed 2,048-bit theorem by taking successive primes from 5 until their product exceeds $2JK$. For nonsquare $N$, we have $T/2<JK\le 4T/3+J$. For the lower bound, $h\le2J^2$ follows from $4h<3(J+1)^2$ when $J\ge2$ and directly when $J=1$. Now use $K>TJ/h$. Thus the modulus threshold is of order $\sqrt N$. If the last prime is $y$, the prime number theorem gives $y\sim\tfrac12\log N$. The overshoot of the product is at most a factor $y$, and the number of primes used is $t=(\tfrac12+o(1))\log N/\log\log N$.

For each prime, the number of labels is $\ell/2$ times $1+O(1/\ell)$. Multiplying gives $\log(\#\mathrm{tuples})=\log M-t\log 2+O(\sum_{\ell\le y}1/\ell)$. The resulting full enumeration still has $N^{1/2-o(1)}$ combinations. For comparison, Harvey and Hittmeir give a general deterministic factorization algorithm taking $N^{1/5+o(1)}$ bit operations. This growth estimate is a paper derivation. The Lean bound for the fixed size uses finite arithmetic. [Prime number theorem project](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) · [Harvey and Hittmeir, Theorem 1.1](https://arxiv.org/html/2105.11105v1#S1)

### Choosing which primes to use

On 117,449 the ascending prime list gives 672 combinations. Choosing primes using the product reduces this to 168. Trying all 168 recovers $257\times457$ at position $(17,12)$. The selection program computes the two possible label counts from the quadratic character of $N$ at each eligible prime. It splits the optional primes into two lists, enumerates the subset products of each list, and finds the least expensive pair whose combined modulus exceeds $2JK$. The result minimizes the tuple count within the stated menu. On larger inputs most of the ascending list stays fixed, so the menu search remains bounded. Any eligible prime that already divides $N$ supplies a factor at setup. [Prime selection](../experiments/offset_crt_wheel.py) · [Fixtures with factors and work counters](../benchmarks/offset-crt.json)

On each full-size example, selection examined 12,288 half-list entries. The fresh example kept the same tuple count. On the crossed example the count went from about $2^{899.274}$ to $2^{899.158}$. Each selected list retained all winning positions. The 64-combination selected-list runs found neither factor.

### A limit that holds for every input of the target size

Could a completely different list of odd primes make this enumeration small? On **every** nonsquare 2,048-bit input, **every** list of distinct odd primes coprime to $N$ whose product exceeds $2JK$ has more than $2^{893}$ combinations. Together with the $2^{901}$ upper bound, this places our fixed list within a factor of 256 of the best full tuple count for any balanced 2,048-bit semiprime. A search that finds its first winning tuple early can of course stop.

For at most 130 primes, the number of combinations is at least $M/2^{130}$. We have $M>2JK>T\ge2^{1023}$, so this exceeds $2^{893}$. For at least 131 distinct odd primes, even taking the least possible label count $(\ell+1)/2$ at each of the first 131 odd primes already exceeds $2^{898}$. Replacing those primes by larger ones only increases that lower estimate. Lean proves both cases. [Universal lower and upper bounds](../PrimeFactors/OffsetProjectiveSlopes.lean) · [Rectangle size](../PrimeFactors/CompleteOffsetWork.lean)

For sharper bounds on the two comparison inputs, take any choice of distinct odd primes coprime to $N$ whose product exceeds $2JK$. Condition on which of the first 16 eligible primes occur. Write $m,c$ for the modulus and number of combinations from this subset. With $r$ further primes, the extra number of combinations is at least the larger of two quantities. The first is the product of the $r$ cheapest remaining label counts. The second is $1+\lfloor 2JK/(m2^r)\rfloor$, since each label count exceeds half its prime. The first bound increases with $r$, and the second decreases. Checking the two adjacent choices at their crossing suffices when $m\le 2JK$. When $m>2JK$, $c$ alone is a lower bound. The label counts are nondecreasing along the odd primes, including beyond the menu, so using the last known count for later primes gives a valid lower estimate.

Integer evaluation of these bounds proves that the chosen 168, 54 and 112 combinations are the minimum possible on 117,449, 9,017 and 50,629 respectively. On each full-size comparison, even the best such list still has more than $2^{897}$ combinations. The selected lists are within factors of 2.219 and 2.724 of the best possible counts respectively. These limits concern exhaustive enumeration with one prime list and the stated reconstruction threshold. [Integer bound and work counters](../experiments/offset_crt_wheel.py) · [Independent tests of the small optima](../tests/test_offset_crt_wheel.py)

Both lists also recovered the factors of each of eight previously published small products. Together they had nine winning positions. Selecting primes reduced the combinations tried from 642,816 to 84,948. It sent *more* positions to an integer square-root test, 7,660 compared with 4,522. Across the eight inputs, the reduction in continued-fraction reconstructions outweighed the extra square tests. [Eight input products](../research/quartic-lane-holdout.json)

These commands repeat the small complete searches and check their prime factors in Lean.

```sh
python3 -m experiments.offset_crt_reconstruction 134683853 --max-tuples 4536 --exhaust --verify
python3 -m experiments.offset_crt_reconstruction 117449 --optimize-wheel --max-tuples 168 --exhaust --verify
python3 -m experiments.offset_crt_wheel 117449 --prove-bound
python3 -m experiments.offset_crt_wheel --holdout --verify
```

## How far can pair-dependent prime tests go?

For the complete sharp range, one fixed prime cutoff suffices to distinguish a square discriminant from every nonnegative nonsquare **under Dirichlet GRH**. This is a separate result about the information in the tests. The 130-prime reconstruction above has unconditional coverage and finishes with an exact square test. The larger detector set adds a condition to each pair $(j,k)$. An offset-only test can leave more than $2^{511}$ multipliers on a single offset even when it checks every divisor. [Offset-only limitation](complete-offset-work.md#can-testing-every-offset-divisor-finish-these-examples)

The elementary identity $hD+(2hk-Tj)^2=Nj^2$ gives $3D\le4N$. For a positive nonsquare $D$ take the quadratic character of $\mathbb Q(\sqrt D)$ on units modulo $q=4096D$. Its conductor divides $q$, it is nontrivial, and at an odd prime outside $q$ it agrees with the Legendre symbol of $D$. Hence the primes outside its kernel reject $D$. For 2,048-bit $N$, we have $3000\le q<2^{2061}$. Lamzouri, Li and Soundararajan's Theorem 1.1(1) under Dirichlet GRH bounds a rejecting prime by $(\ln q+B(q))^2$. Their explicit formula has $A(q)\ge0$ and
$B(q)\le 2\ln\ln q+3+2\omega(q)(\ln\ln q)^2/\ln q$ in this range.
Use $2/3<\ln 2<7/10$, $\omega(q)\le\ln q/\ln 2$, $\ln q<1443$ and $\ln\ln q<8$. It follows that $B(q)<211$ and that some rejecting prime is below $1654^2=2{,}735{,}716$. The case $D=0$ passes as an actual square. Removing the known exceptional pair for $h=1$ leaves precisely the winning pairs among primitive positions passing the nonnegativity and all these local checks. [Finite implication and height bound](../PrimeFactors/OffsetSquareDetectors.lean) · [LLS Theorem 1.1](https://arxiv.org/html/1309.3595v3#S1.SS1) · [Dirichlet statements in the pinned RH release](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab/src/Statements.lean)

Lean checks the implication from the explicit finite detector hypothesis. The application of quadratic characters and the published GRH estimate is a paper deduction. Solving the combined constraints cheaply at full size remains open.
