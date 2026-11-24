# A square norm on the fourth step of a 2048-bit example

The ordinary continued fraction of $\sqrt N$ recovered the two 1024-bit primes of the existing `continued-square-2048` example in **four updates and two positive-norm square tests**. The first three updates yield no square dependency. We found this by pooling walks, then traced the entire result to a single row of the ordinary walk. On the five other distinct 2048-bit products with complete certificates in the benchmark fixtures at the time of this experiment, the first 128 updates of the same walk found no factor. The successful example was constructed with a particular relationship between its factors. [Fixtures](../benchmarks/pooled-relations.json) · [Construction and earlier decoder](near-square-families.md)

## When the ordinary walk sees hidden weights

Suppose $N=pq$ with distinct odd primes. For any positive integers $a,b$, put

$$A=a^2p+b^2q,\qquad B=2ab,\qquad Z=a^2p-b^2q.$$

Then $A^2-NB^2=Z^2$. Write $d=\gcd(A,B)$ and reduce to $x=A/d$, $y=B/d$, $z=|Z|/d$. The last quotient is integral because $d^2$ divides $Z^2$. If $pq$ is coprime to $2ab$, one of $x-z,x+z$ is divisible by $p$ and the other by $q$. A gcd then gives a prime factor. The factors and weights in this argument describe the input class. The search itself receives $N$ and a step budget.

There is a checkable condition that puts the hidden $x/y$ in the public continued fraction. Rationalizing the difference gives

$$\left|\frac xy-\sqrt N\right|=\frac{z^2}{y^2(x/y+\sqrt N)}.$$

Whenever $2z^2<x/y+\sqrt N$, Legendre's theorem places $x/y$ among the convergents of $\sqrt N$. Every second update at least doubles the denominator after the first two denominators, so a convergent of denominator at most $2ab$ occurs among the first $2\lceil\log_2(2ab)\rceil+2$ updates. One walk can test all qualifying weight pairs of bounded product at once. This bound counts continued-fraction updates and square tests. It assumes the stated inequality, and applies to the full ordinary walk. The pooled experiment also stops individual walks at the first center or period end. [Lean identities and convergence proof](../PrimeFactors/PooledRelations.lean) · [Mathlib's Legendre theorem](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/DiophantineApproximation/Basic.html#Real.exists_rat_eq_convergent)

For the existing family $P_i(t)=i^2t+2i+1$, take the factors $P_{ag}(t)$ and $P_{bg}(t)$ with $1\le a<b$ and $g\ge1$. Their weighted difference simplifies to

$$b^2P_{ag}(t)-a^2P_{bg}(t)=(b-a)(2abg+a+b).$$

Its independence of $t$ gives a sufficient condition uniform in $g$. If $(b-a)^2(2ab+a+b)^2<abt$, the squared difference is less than $g^2abt\le\sqrt N$. Division by $d$ only decreases it, and $x/y\ge\sqrt N$ by the square-norm identity, so Legendre's condition holds. With $a=13$, $b=15$, the threshold is $t>698896/195$. The fixture uses $t=10000$. Its fourth convergent has denominator $195$. With numerator $x$ and square root $z$ of its norm, $x-z=169p_{\rm large}$ and $x+z=225p_{\rm small}$. These identities explain the quick split using the public input. The earlier 65,536-row exclusion concerned a different walk, on $\sqrt{133N}$. [Earlier negative result](pell-cycles.md) · [Prior public-ratio method](near-square-families.md)

## What pooling buys

For each public multiplier $m$ coprime to $N$, a convergent $X/Y$ of $\sqrt{mN}$ gives a signed norm $R=X^2-mNY^2$, hence $X^2\equiv R\pmod N$. Rows from different multipliers can be combined in one square relation. If two signed norms agree, their residues give a split immediately whenever the residues differ modulo $N$ up to sign. Indeed $N$ divides $(X_1-X_2)(X_1+X_2)$, so $\gcd(N,X_1-X_2)$ is proper. The program also tests each distinct positive norm for a square on arrival. Square congruence factoring by continued fractions goes back to classical CFRAC. [Morrison and Brillhart](https://doi.org/10.1090/S0025-5718-1975-0371800-5)

For $N=21{,}490{,}481$, the third rows from multipliers 1 and 7 both have signed norm $-4847$. Their residues are $18543$ and $98121$. Their difference has gcd $4421$ with $N$, giving $N=4421\cdot4861$. Either walk alone has zero square dependencies after six updates. The pair takes six total updates, and multiplier 7 was identified by exploration. Trying **every** multiplier from 1 through 7 in numerical order gives the same split in 21 total updates. The unmultiplied walk first succeeds at 30. These counts cover continued-fraction work. Pooling also incurs a square root and initial gcd per multiplier and stores its rows. [Small Lean witness](../PrimeFactors/PooledRelations.lean) · [Same-budget controls](../benchmarks/pooled-relations.json)

For square multipliers $m=c^2$, $\gcd(|R|,c^2)=\gcd(X,c)^2$. Divide the norm by this square and the numerator residue by its square root modulo $N$. Two equivalent normalized rows with residues equal up to sign contribute a trivial square congruence together. Keeping one representative preserves the ability to find a split, since multiplying a trivial square relation into another preserves its gcd outcome up to exchanging the two factors. A nonsquare private cofactor in a retained row excludes it from an exact-square dependency. [Normalization proof](../PrimeFactors/PooledRelations.lean) · [Trivial relations and private cofactors](../PrimeFactors/PellCycles.lean) · [Short-prefix exhaustive tests](../tests/test_pooled_relations.py)

On the existing independently sampled 63- and 79-bit products, splitting the successful single-walk budgets of 767 and 5,138 updates across any of $(1,2),(1,3),(1,5),(1,7),(1,2,3,5)$ produced no factor. On the 79-bit input, pooling the first eight square multipliers consumed 5,138 updates, normalized 1,307 rows, and found 2,856 repeats. All 2,282 distinct rows were excluded in four rounds. On the structured 2048-bit input, pooling the first eight **prime** multipliers at 8,192 updates each produced 65,536 distinct rows. Every row had a private nonsquare cofactor even after removing all primes through $2^{24}$, with the smallest such cofactor having 888 bits. This rules out a square product for every nonempty subset of that pool even with arbitrary corrections supported on those primes. It took approximately 11 seconds in the local GMP run. The ordinary walk's square at step four illustrates how much the choice of multiplier matters. [Experiment](../experiments/pooled_relations.py) · [Bounded benchmark fixtures](../benchmarks/pooled-relations.json)

The full strengthened check uses optional gmpy2. The following commands obtain the public product from its fixture and pass only that product and the public budgets to the search.

```sh
n=$(python3 -c 'import json; print(json.load(open("benchmarks/continued-square.json"))[0]["n"])')
python3 experiments/pooled_relations.py "$n" --multipliers 1 --max-steps 65536
python3 experiments/pooled_relations.py "$n" --multipliers 2 3 5 7 11 13 17 19 --max-steps 65536 --gmp --external-smooth 16777216
```
