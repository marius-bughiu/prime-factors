# How eight small checks found the useful square

Starting with the product **1,915,966,849**, we found **36,151 × 52,999**. The clue came from combining 28 rows of a cubic polynomial chosen using the product alone. Lean checked the rows, the resulting square, both factor calculations and the primality of the answers. The experiment also tested seven other 31-bit products at the same budget. The cubic method found one of eight and the comparison quadratic sieve found six of eight, including the same product. The cubic search found no factor on either the fresh or the crossed 2,048-bit control. [Full panel](../research/cubic-trace-panel.json) · [Benchmarks with checked certificates](../benchmarks/cubic-trace.json)

## What made the successful example work?

We write the public input as $N=f(m)$ with a small-coefficient monic cubic. For the successful draw, $m=1242$ and $f(X)=X^3+82X+517$. This polynomial has no root modulo 17, which proves it is irreducible over the rationals. Each row $(a,b)$ gives an ordinary integer $a+bm$ and an algebraic number $a+b\alpha$, where $f(\alpha)=0$. Replacing $\alpha$ by $m$ preserves multiplication modulo $N$.

We tested 1,583 rows. In 63, both the ordinary integer and the algebraic norm factored over primes at most 127, with signs recorded. The ordinary square test combines rows whose prime exponents add up to even numbers on both sides. On this input it left $2^9-1=511$ nonempty combinations. A square norm alone cannot tell whether the algebraic number itself has a square root.

| Extra square-character checks | Surviving combinations | Combinations checked | Actual algebraic squares | Splits |
| ---: | ---: | ---: | ---: | ---: |
| 0 | 511 | 32 | 0 | 0 |
| 4 | 31 | 31 | 1 | 1 |
| 8 | 1 | 1 | 1 | 1 |

Each extra check substitutes a root of $f$ modulo a small prime and asks whether the product is a square there. Four checks found the successful combination on their third attempt. Eight checks left it as the sole candidate. Producing the rows and character table cost 88,417 trial-prime visits and 504 character evaluations. On one process-CPU measurement shared setup took 12.1 ms and the eight-check search after setup took another 2.5 ms. The comparison sieve took 1.55 ms on the same input. These costs apply to this example. [Implementation and replay](../experiments/cubic_trace_search.py)

## How do we tell that a surviving combination really works?

Let $\beta$ be the product of the selected algebraic rows and $z^2$ the ordinary product. Write $Y^3-A Y^2+B Y-w^2$ for the characteristic polynomial of $\beta$. If $\delta^2=\beta$, choose its sign so its norm is $w$. The sum $u$ of its three conjugates then satisfies

$$
(u^2-A)^2-8wu-4B=0.
$$

This is the classical quartic in Cohen and Thorne, Proposition 2.3(2). A proposed root gives $v=(u^2-A)/2$. For a nonscalar $\beta$ in the cubic field, $\delta=(u\beta+w)/(\beta+v)$ squares to $\beta$. Integral elements have integral trace, so an exact integer root search suffices. The implementation first tests the quartic modulo 5, then isolates all integer roots by interval subdivision. For coefficient bit length $L$, the fixed-degree isolation takes $O(L^3)$ bit operations using schoolbook arithmetic. This cost starts after a candidate combination has been found. Lean verifies the algebraic identities. The root-isolation cost is a written bound in the implementation. [Trace quartic and proof](https://people.math.sc.edu/thornef/papers/CT-quartic.pdf) · [Lean identities](../PrimeFactors/CubicTraceSquare.lean) · [Integer root isolation](../experiments/cubic_trace_roots.py)

Set $h(T)=T^3-uT^2+vT-w$. Then $h(z)h(-z)$ is zero modulo $N$. Either value can share a proper divisor with $N$. In the successful 31-bit search the two residues were 792,335,050 and 308,512,634. Their greatest common divisors with $N$ were 52,999 and 36,151. The number field sieve already uses a rational square paired with an algebraic square. Our experiment measures this particular cubic decoder and provides replayable evidence for its successes and misses. The implementation was written for this repository using its existing arithmetic routines. [Buhler, Lenstra and Pomerance, sections 6–9](https://scholarlypublications.universiteitleiden.nl/handle/1887/2149?m=9940748453702711&rep=01) · [Couveignes on the algebraic square root](https://www.math.u-bordeaux.fr/~jcouveig/publi/Cou94-2.pdf)

On the smaller example $989=10^3-11$, the three ordinary rows $8,28,14$ multiply to $56^2$. The corresponding algebraic product is $(7-2\sqrt[3]{11})^2$. The decoder gives 23 and 43. Another three rows on the *same input* have ordinary product $60^2$ and norm $703^2$. Their quartic has no root modulo 5. Lean proves that no rational-coefficient square root exists anywhere in the cubic field. These two row triples were supplied as unit examples. A separate search starting with 989 alone chose a different polynomial and also found its factors. [Checked examples](../PrimeFactors/CubicTraceSquare.lean)

A genuine square sometimes gives two trivial gcds because one of its other conjugates also matches the tested value. Suppose the distinguished roots at the two hidden primes give opposite signs, $z$ is a unit, the cubic has distinct roots at those primes, and both primes exceed three. Multiplying the algebraic root by $\alpha+j$ and the ordinary root by $m+j$ separates the signs for some integer $0\le j\le3$. Each unwanted conjugate can exclude at most one shift. Once the ordinary characteristic value vanishes at both primes, the first three shifts suffice. Lean proves the separating field statement; its use at the two prime factors is the residue-field argument above. [Shift bound and precise hypotheses](../PrimeFactors/CubicTraceMasks.lean)

## How much can small-prime tests tell us?

At a good odd prime, a cubic may have one, two or three irreducible factors. For a unit with square norm, all local components are automatically squares when the cubic is irreducible. With splitting type $1+2$ one character check suffices. With three linear factors any two checks determine the third. In general $r$ components realize exactly $2^{r-1}$ allowed sign patterns locally. The experiment used one linear root at each of eight distinct primes. [Finite-field norm and character proofs](../PrimeFactors/CubicLocalCharacters.lean)

There is an exact limit on what any fixed finite list of primes can establish. Write $\alpha=\sqrt[3]{11}$, $H=1+11t^3$, and $\beta=H(1+t\alpha)$. Its norm is $H^4$. Lean proves that for every positive product $M$ of test primes there is a multiple $t$ of $M$ for which $\beta$ is a nonsquare in the field. It reduces to 1 throughout every tested residue algebra. The proof chooses one additional prime congruent to 5 modulo 12. This explains why passing the whole list still calls for the exact quartic test. A particular bounded collection of rows can, of course, be separated by a finite list. [Unconditional construction](../PrimeFactors/CubicLocalCharacters.lean)

## What happened on the other products?

The initial comparison used 415 primitive rows, a smoothness bound of 127, and at most 32 dependency checks per arm. For four 31-bit products, four 39-bit products, one 79-bit product and the two 2,048-bit controls the cubic method found no dependency. The quadratic sieve, using the same number of positions, split three of the four 31-bit examples and none of the larger ones. On each full-size input, even the number of smooth **ordinary** rows was zero.

In the expanded comparison we used 1,583 rows for the four original 31-bit draws and four new draws from a separate seed. The sole cubic success was in the original group. The comparison sieve split all four original and two of the four new products. An additional 6,361-row sensitivity run on the first original 31-bit and 39-bit inputs produced one true algebraic square on the smaller input, but its gcds were trivial. All seven distinct prime factorizations displayed across the panels were replayed in Lean. The products used for generating the samples had known factors, held back from the searches. The counts compare equal numbers of candidate positions, which can cost different amounts of work. [Frozen inputs, counters and single-run timings](../research/cubic-trace-panel.json)

Run `python3 -m experiments.cubic_trace_search --check --verify` for the frozen panel. The standard benchmark publishes two successful cases and both capped full-size runs, and checks a separate relation certificate for each success. [Certificate generator](../scripts/cubic_trace_benchmark.py)
