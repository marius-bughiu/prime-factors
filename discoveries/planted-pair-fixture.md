# A 2,048-bit product with smallest successful fraction norm 49

This input was constructed so that a small pair of fractions reveals both 1,024-bit primes. A search given the product and a norm limit of 49 took 24 integer square roots to locate candidate gaps. Exactly one gap was small enough to test. The first 23 multipliers also rule out **every** pair of primitive short fractions with one norm at most 48, at every possible residue of this product. [Benchmark and cutoff](../benchmarks/guided-pairs.json) · [Search](../experiments/guided_pairs.py)

## The construction

Set $M=k\,2^{883}(97\#/7)$, where $97\#$ is the product of the primes through 97. Choose $k=2{,}490{,}290$. The two primes are $p=2M+1$ and $q=3M+1$ and the public input is $N=pq$. The complete decimal values are in the fixture. We screened 6,728 successive values of $k$ starting at 2,443,201 in increments of seven. This progression makes $M\equiv-1\pmod7$. We used GMP probable-prime tests on both linear expressions to find the candidate. Lean checks the primality of each factor and the exact product with the repository's order certificates. Running `python3 scripts/benchmark.py` regenerates the proof from the factor found by the search. [Decimal factors and budgets](../benchmarks/guided-pairs.json) · [Lean certificate generator](../scripts/factor.py)

The construction makes $3p-2q=1$. Put $U=3p+2q=12M+5$. Then

$$ U^2=24N+1,\qquad U-1=4q,\qquad U+1=6p. $$

Since $7\mid U$, the integer $D=(U/7)^2$ satisfies $49D=24N+1$. Thus the two fractions $49/1$ and $1/D$ both represent 49 modulo $N$. Their signed norms multiply to $U^2$, and $2D<N$. The gcd of $U-1$ and $N$ is $q$. When the search starts at the specially chosen residue 49, both fractions appear within three Euclidean states. The exact square test succeeds on its first comparison. [Fraction-pair theorem](../PrimeFactors/SameSourcePair.lean) · [Euclidean search](../experiments/pair_class_search.py)

## What each search uses

| Search | Information supplied | Work on this input |
|---|---|---|
| Scan the possible multipliers for a small row | $N$, norm limit 49 | 24 multiplier roots and one test of a candidate gap |
| Use the planted fraction | $N$, chosen residue 49 | Three Euclidean states and one exact pair test |
| Test the known small multiples | $N$, the specific hypothesis $\lvert3p-2q\rvert=1$ | One square test on $24N+1$, then one gcd |
| Ordinary Fermat search | $N$ | More than $2^{1017}$ consecutive midpoints to reach $(p+q)/2$ |

For an odd product of distinct primes the first successful Fermat midpoint is $(p+q)/2$, giving exactly $(p+q)/2-\lceil\sqrt N\rceil+1$ midpoint tests. The fixture factors give a count strictly between $2^{1017}$ and $2^{1018}$. A weighted search allowed to start with the ratio $3/2$ already succeeds immediately here.

For the minimum-norm claim, order and normalize the two cross products of a qualifying pair as $gU^2>gV^2$. They are congruent modulo $N$ and invertible there. Hence $U^2-V^2=hN$ for a positive integer $h$. If either norm is at most $S$, the strict height bound on its partner gives $2hV^2<S$. At $S=48$ this requires $h\le23$. The cutoff in the fixture runs the same 23 multipliers with the slightly larger limit 49 and finds no eligible gap. At $S=49$ the two fractions displayed above achieve the bound. [Kernel proof of the exact minimum](../PrimeFactors/PlantedHeightExample.lean) · [Cutoff result](../benchmarks/guided-pairs.json)

The same search on the existing crossed 2,048-bit control checked every multiplier through 32,767 at a norm limit of 65,536. It left the input unresolved. The small example $N=527$ also checks the case in which the second square above a multiple is the first successful one. [Comparison fixtures](../benchmarks/guided-pairs.json)

## Bounded seeds for arbitrarily large balanced products

A separate construction proves that **some fixed finite list of integer residues** works on infinitely many products of two primes with comparable sizes. For each listed residue $s$, the search asks whether its specific fraction $s/1$ has a qualifying partner. For a sufficiently large bit width, the fraction of inputs admitting such a partner for this list is $X^{-1+o(1)}$, where $X$ is the smallest integer of the target prime width. The asymptotic conclusion uses its own fixed list and gives no numerical onset at 2,048 bits.

Fix a tuple size $k\ge2$, put $A=k^2$, and choose $a_i=A+i$ for $1\le i\le k$. For each $i<j$ take a distinct prime $t_{ij}>3(A+k)k$. Restrict $M$ to a fixed arithmetic progression by the conditions

$$M\equiv0\pmod\ell\quad(\ell\text{ prime},\ \ell\le k),\qquad
2a_i a_j M\equiv-(a_i+a_j)\pmod{t_{ij}}.$$

The Chinese remainder theorem gives $M=M_0+Qn$. The forms $a_iM+1$ have positive coefficients of $n$, and their pairwise determinants after substitution are $Q(a_i-a_j)\ne0$. They are admissible: at a prime at most $k$, all values are 1 modulo that prime. At $t_{ij}$ the form with index $s$ is nonzero because

$$0<|2a_i a_j-a_s(a_i+a_j)|\le2(A+k)(k-1)<t_{ij}.$$

Indeed the harmonic mean $2a_i a_j/(a_i+a_j)$ is strictly below $(a_i+a_j)/2$ by $(a_i-a_j)^2/[2(a_i+a_j)]<1/2$, so it cannot be an integer. At any other prime there are at most $k$ roots of the forms in total. A vanishing leading coefficient there gives a constant 1.

Suppose $p=a_iM+1$ and $q=a_jM+1$ are prime. Take $U=a_jp+a_iq$ and $V=a_jp-a_iq=a_j-a_i>0$. Then $t=t_{ij}$ divides $U$ and $U^2-V^2=4a_i a_jN$. Write $g=\gcd(U,V)$, $u=U/g$ and $v=V/g$. Since $g\le V<t$, we have $t\mid u$, and for sufficiently large $M$ all of $g,t,u,v$ are units modulo $N$ (use $V<p$ and the square congruence). The fractions

$$t^2/1,\qquad v^2/(u/t)^2$$

are distinct and primitive, represent the same residue, and their norms multiply to $(uv)^2$. The second norm is at most $V^2(4a_i a_jN+V^2)/t^2$. Its double is less than $N$ for all sufficiently large $M$, since $t^2>8a_i a_jV^2$. The finite set of residues and the bound on the smaller norm are independent of $M$. A finite list of weighted Fermat tests at the known multipliers $4a_i a_j$ also suffices for this family, because $V$ takes only the fixed values $a_j-a_i$.

**A numerical bound for the cumulative family.** At $k=50$ one can take the first 1,225 primes above 382,500, ending at 398,059. Thus all seeds obey $t^2<2^{38}$. Kim's quantitative form of the Maynard–Tao theorem gives $\gg X/(\log X)^{50}$ parameters with two prime outputs at most $X$, for all sufficiently large $X$. Each product is counted at most $\binom{50}{2}$ times because each pair of indices determines at most one parameter for a specified product. At least one seed therefore succeeds on infinitely many products, and its prime ratio tends to a fixed $a_j/a_i\in(1,2)$. This cumulative theorem counts all eligible parameter sizes up to a cutoff. [Kim, Lemma 2.1](https://www.csun.edu/~sungjin/SJK_Totient2-3%281%29.pdf#page=4)

At a fixed seed $s=t^2<N/2$, the Euclidean walk on $(N,s)$ starts its row remainders at $s$. Every two steps at least halve the positive remainder, so $s<2^{38}$ gives at most 76 rows. For a positive row $c/d$ the difference $ds-c=eN$ is known and $s\cdot cd=c(eN+c)$. One integer square test decides whether its norm matches the planted row. Enumerating the entire 50-form list therefore takes at most $1{,}225\cdot76=93{,}100$ Euclidean rows, independent of the input size. The arithmetic operates on integers whose bit lengths grow with the input. [Euclidean correspondence for every short fraction](shared-root-signs.md#enumerating-the-fractions-on-one-euclidean-chain)

Assigning the primes in increasing order to the pairs in lexicographic order gives a 22,813-bit CRT period and a 22,810-bit least nonnegative parameter $M_0$. Even the product of the two smallest forms at $M_0$ has 45,643 bits. The concrete 2,048-bit fixture above uses the separate one-pair construction. [Finite CRT checks](../tests/test_guided_pairs.py)

**Counting within the specified bit widths.** Now use the fixed $k$ supplied by Maynard's short-interval theorem for two primes. If necessary start with a larger tuple and use any subset of the required size. Write $X=2^{b-1}$. Restrict $M$ to $[3X/(2A),8X/(5A)]$. For $k\ge 50$ and $X$ sufficiently large, all outputs lie strictly between $\sqrt2 X$ and $2X$. Thus both primes have $b$ bits and their product has $2b$ bits. The corresponding interval of $n$ has starting point $x\asymp X$ and length $y\asymp X$, with $x^{7/12+1/10}\le y\le x$ eventually. All coefficients of its affine forms are fixed. Maynard's Theorem 3.4 gives $\gg X/(\log X)^k$ parameters in this interval, with the log exponent of the required subset permitting the weaker exponent $k$. Dividing by the fixed pair multiplicity gives the same order of lower bound for distinct products in the specified bit widths. [Maynard, *Dense clusters of primes in subsets*, Theorem 3.4](https://ora.ox.ac.uk/objects/uuid%3Aa08a24aa-e17c-4323-8aea-a1782d68c694/files/m19d2e3b9605819f668974f67909377e6)

There are $\Theta(X^2/(\log X)^2)$ eligible prime pairs by the prime number theorem, since both can be taken in $[3X/2,2X)$. The finite list therefore succeeds with probability $\gg 1/[X(\log X)^{k-2}]$. In the other direction the bounded-norm partner count gives $O_S(1)$ possible larger primes per smaller prime for fixed $S=\max t_{ij}^2$, giving probability $O_S(\log X/X)$. Together these yield the exponent $X^{-1+o(1)}$. One fixed seed attains the lower exponent along an infinite subsequence of widths by pigeonholing. The short-interval result uses an unspecified constant $k$ and a corresponding fixed $S$; the explicit $2^{38}$ bound above refers to the cumulative construction. The analytic prime-count inputs and this asymptotic argument are on paper.
