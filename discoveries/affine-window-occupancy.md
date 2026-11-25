# Almost every 614-bit remainder passes the modular product test

For a balanced 2,048-bit product, at most **one in $2^{192}$** of the odd factor remainders modulo $R=2^{614}$ can be discarded by testing whether the balanced rectangle contains a pair with $xy\equiv N\pmod{R^2}$. This holds for every odd input of that size. The floor sums compute this test exactly. A positive count allows products differing from $N$ by a multiple of $R^2$. The exact quartic search still has to distinguish the target product. [Lean proof](../PrimeFactors/AffineWindowOccupancy.lean) · [Floor-sum search](modular-hyperbola.md) · [Quartic factor recovery](unit-newton-lanes.md)

## Why the rectangles contain points

In the remainder $u$, set $i=u^{-1}\bmod R$, $w=Ni\bmod R$, $x=u+Rv$ and $y=w+Rz$. The product congruence is equivalent to $z\equiv av+c\pmod R$, where $a=-wi$ and $c=i(N-uw)/R$ as residues modulo $R$. A pair of intervals for $x,y$ becomes a rectangle for the integer high digits $v,z$. [Exact affine equivalence](../PrimeFactors/ModularHyperbola.lean)

Write $R=HD$. Dirichlet approximation gives a reduced fraction $p/q$ with $1\le q\le H$ and $|aq-Rp|\le D$. If $q\ge D$, every translated rectangle of horizontal width $H$ and vertical radius $H+D$ contains a modular point. To construct it, start the horizontal interval at $X$, center the vertical interval at $Y$, and put $b=aX+c$. Set

$$
t=\lfloor (Y-b)q/R\rfloor,\qquad j=p^{-1}t\bmod q,\qquad
v=X+j,\qquad z=b+aj-R(pj-t)/q .
$$

The last quotient is an integer. Multiplication by $q$ gives $q(z-Y)=(aq-Rp)j-((Y-b)q\bmod R)$. Consequently $|z-Y|\le D+R/q\le D+H$. The Euclidean algorithm supplies the reduced fraction and modular inverse. [Formal construction](../PrimeFactors/AffineWindowOccupancy.lean) · [Mathlib’s Dirichlet approximation theorem](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/DiophantineApproximation/Basic.html#Real.exists_rat_abs_sub_le_and_den_le)

An empty rectangle thus forces $q<D$. The nonzero vector $(q,aq-Rp)$ has both coordinates of absolute value at most $D$, and its second coordinate equals $a$ times its first modulo $R$. At most $2D^2$ unit slopes admit such a vector. For each slope there are at most four original residues because $a=-Nu^{-2}$ and a unit has at most four square roots modulo a power of two. These bounds allow a different intercept and rectangle location at every residue. [Bound on the number of slopes](../PrimeFactors/WeightSlopeCover.lean) · [Dyadic square-root bound](../PrimeFactors/ConditionalStride.lean)

Take $H=2^{405}$ and $D=2^{209}$. For every $N\ge2^{2047}$, the smaller-factor interval from $\lceil\sqrt{N/2}\rceil$ to $\lfloor\sqrt N\rfloor$ contains $H$ consecutive high digits in every remainder. The larger-factor interval from $\lceil\sqrt N\rceil$ to $\lfloor\sqrt{2N}\rfloor$ contains $2(H+D)+1$. The previous bounds therefore exclude at most $4\cdot2D^2=2^{421}$ of $2^{613}$ odd remainders. The theorem applies to the fixed product precision $R^2$ and the original factor intervals. Finer product precision, smaller rectangles and rankings by the **magnitude** of positive counts present separate questions. [Integer endpoints and oriented-remainder theorem](../PrimeFactors/AffineWindowOccupancy.lean)

## Bounded checks

On the eight frozen products of two 16-bit primes, we used $e=\lceil614\,\mathrm{bitlength}(N)/2048\rceil=10$ and counted all 512 odd remainders modulo $2^e$ on each input. Only 1,114 of 4,096 remainders survived. The smaller prime’s remainder had exactly one witness on every input, tied with between 69 and 166 other remainders. The small examples give the appearance of an effective exclusion test. [Per-input results](../research/affine-window-occupancy.json)

On the fresh certified 2,048-bit control, a fixed SHAKE256 rule chose 256 distinct odd remainders from the product alone. Every count was positive and close to $9.67814\times10^{60}$. The largest and smallest counts differed by only 4,177. The constructive argument produced one pair per remainder. Each product agreed with $N$ modulo $R^2$, and all 256 differed from $N$. After fixing the sample, we opened the construction labels to score the true smaller-prime remainder. Its count exceeded 213 sampled counts, tied one and fell below 42. This one product gives a diagnostic for ranking by count. The uniform exclusion bound above holds independently of those measurements. [Stored counts and work](../research/affine-window-occupancy.json) · [Certified control](certified-fresh-control.md)

Run `python3 -m experiments.affine_window_occupancy` to reproduce the panel. Passing a product, radix and odd remainder prints the exact count and the Euclidean step count. The tests also check each count against direct enumeration on small inputs and check constructed points over translated rectangles. [Implementation](../experiments/affine_window_occupancy.py) · [Tests](../tests/test_affine_window_occupancy.py)
