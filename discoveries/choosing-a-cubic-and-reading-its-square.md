# Choosing a cubic and reading its square

The cubic search needs rows that pass two tests on the same input. Each test asks whether a number can be built entirely from the small primes in our list. We changed the polynomial so that the first test passed by construction. On each of the fresh and crossed 2,048-bit controls we obtained 130 such rows. None passed the second test. We also examined what happens after several rows have produced a real square. On 1,333, a square that returned only the whole input with the original calculation gave **31 and 43** with a different calculation. [Earlier cubic search](cubic-square-relations.md) · [Public inputs and work counts](../research/cubic-smooth-bases.json) · [Readout census](../research/cubic-readout-panel.json)

## Can we make suitable rows from the product?

We choose a public base $m$ and a monic cubic $f$ with $f(m)=N$. A primitive row $(a,b)$ gives the rational value $r=a+bm$ and signed algebraic norm $H$. Both must have all prime factors at most 127 for this experiment. The polynomial can change, but every such row obeys

$$
r\mid H+b^3N,\qquad \gcd(r,b)=1.
$$

This follows by substituting $a=-bm$ in the homogeneous norm modulo $r$. Replacing $f$ by $f+(uX+v)(X-m)$ keeps $N$ fixed. For a primitive row the exact set of new norms before testing irreducibility is $H+br\mathbb Z$. Thus we can choose the norm within an arithmetic progression. Small norms allowed by the progression can still have large prime factors. Polynomial rotations are classical in number field sieve polynomial selection. [Lean divisibility and rotation formulas](../PrimeFactors/CubicSmoothBaseChoice.lean) · [Bai, Brent and Thomé](https://maths-people.anu.edu.au/~brent/pd/rpb254.pdf)

We took all $s=2^i3^j$ in $[\sqrt[3]N/2,2\sqrt[3]N]$ with $j\le12$. Setting $m=s-t$ for $t=-2,-1,0,1,2$ guarantees that row $(t,1)$ has smooth ordinary value $s$. On each full-size input all 130 resulting cubics passed an irreducibility test. We scanned 415 primitive rows in each cubic and compared them with equally many bases near the ordinary cube root.

| Full-size control | Rows per choice of base strategy | Smooth ordinary values, selected bases | Smooth ordinary values, nearby bases | Smooth on both sides, either strategy |
| --- | ---: | ---: | ---: | ---: |
| Independently generated | 53,950 | 130 | 0 | 0 |
| Crossed prime pair | 53,950 | 130 | 0 | 0 |

Across the four 31-bit products, choosing the bases this way yielded 141 matches among the designated rows, compared with 112 for the same number of nearby bases. Across **all** rows the counts were 2,324 and 6,118. A relation must use rows from the same cubic. Summing these counts across different fields measures available rows. It does not turn them into a single pool of combinations. [Frozen search and reproducible counts](../experiments/cubic_smooth_bases.py)

## How often could the full-size search produce a row?

The population here consists of uniformly chosen distinct 1,024-bit primes, ordered by size and conditioned on a 2,048-bit product. The bounds cover even a choice that makes full use of the input.

| Allowed choice | Fraction admitting even one row |
| --- | ---: |
| $m=\lfloor\sqrt[3]N\rfloor+k$, $|k|\le4$, $|a|\le160$, $1\le b\le32$; only the ordinary side needs to be 127-smooth | $<2^{-522}$ |
| Any monic cubic and base with $f(m)=N$, $2^{681}\le r\le2^{688}$, $1\le b\le32$, both sides 127-smooth, $0<|H|\le2^{704}$ | $<2^{-411}$ |
| Same choices, allowing $0<|H|\le2^{2048}$ | $<2^{-327}$ |

For the first bound, fixing a row and its smooth value fixes the integer cube root, hence a short interval of inputs. For the other two, fixing $r,H,b$ fixes the residue of $N$ modulo $r$. A finite Euler product at exponent $1/16$ bounds the count of possible smooth values. The proof compares the resulting count with a lower bound on the number of eligible prime pairs. The finite counts and the population denominator used here are both proved in Lean. The result concerns the stated prime bound, sizes and slopes. [Coverage theorems](../PrimeFactors/CubicSmoothRows.lean) · [Unconditional population denominator](../PrimeFactors/ChebyshevPrimeSample.lean)

If we lift the norm-size restriction, every odd input with a chosen dyadic ordinary value $s\ge4$ admits an irreducible cubic whose designated row is smooth on both sides. Every odd residue modulo $s$ has a representative $\pm5^e$. We rotate the cubic to give that norm and arrange irreducibility modulo 2. On the full-size controls the smallest of the four displayed powers requires more than $2^{676}$ bits to write in ordinary binary. Its exponent is computable in fewer than 700 lifting steps. This construction gives one row; collecting a square relation still takes additional work. [Existence and irreducibility proofs](../PrimeFactors/CubicSmoothBaseChoice.lean) · [Compressed exponents](../research/cubic-smooth-bases.json)

## What if a useful relation already exists?

Suppose the selected ordinary rows multiply to $z^2$, and the corresponding cubic element $\beta$ is a field square $\delta^2$. The original characteristic-polynomial test can lose a factor when another conjugate matches the same sign. One way to recover the intended value is to express $\delta$ in the original basis $1,\alpha,\alpha^2$, cancel common integer content, and evaluate at $m$. A second way obtains just the required trace. Form

$$
G(X)=\frac{f(X)-f(m)}{X-m},\qquad U=\operatorname{Tr}(G(\alpha)\delta).
$$

At a simple residue root $m$, $G(m)=f'(m)$ and $G$ vanishes at the other distinct roots. We get $U$ from the integer trace quartic of $G(\alpha)^2\beta$. Its norm is $f(m)^4\operatorname{Norm}(\beta)$, so the signed norm needed for the quartic is already known. For every modulus $N\mid f(m)$, including repeated prime powers, every integral root of this projected quartic satisfies $U^2\equiv f'(m)^2z^2\pmod N$. A proper gcd of $U\pm f'(m)z$ gives a factor. At an unramified unit with opposite signs at the two primes, this reads those two signs directly. The trace calculation uses the data of the square candidate and needs no hidden factor. The divided-difference identity is classical algebra. Couveignes also uses the derivative in his number field sieve square-root algorithm. [Matrix, trace and gcd proofs](../PrimeFactors/CubicTraceProjection.lean) · [Couveignes](https://www.math.u-bordeaux.fr/~jcouveig/publi/Cou94-2.pdf)

On 1,333, the 59th candidate contained 14 rows. Both original gcds were 1,333. The projected trace was 566,316,738 and its two gcds were 31 and 43. On 3,239 the same change recovered 41 and 79 from an 18-row relation. These are retrospectively identified relations. Both products already split on an earlier relation. [Exact witness replay](../benchmarks/cubic-readout.json)

To measure this tradeoff, we compared identical candidates for every prime pair $17\le p<q\le83$, $q\le2p$. Twelve of 89 products had a ramified test polynomial and were set aside. On the remaining 77 we took up to 128 combinations each, after eight character checks, and compared only unit rational roots. Among 5,668 true squares, 2,898 gave a proper ordinary gcd and 2,837 gave a proper projected gcd. The projection recovered two relations the ordinary test missed. In the opposite direction the ordinary method found 63. An extra conjugate can accidentally give a factor even when the distinguished signs agree. Across distinct products the ordinary method split 74 and the projected method 73. The reconstructed-root and projected results agreed on every tested unit square. The quartic isolator visited 960,531 nodes for the projected method and 726,867 for the original. All 74 distinct displayed factorizations have checked prime certificates. [Census and replay command](../experiments/cubic_readout_panel.py)
