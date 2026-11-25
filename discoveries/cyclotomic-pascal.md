# What survives a short cyclotomic projection of Pascal’s row?

For `N=143`, exponentiating `1+x` modulo both 143 and `x⁴−x²+1` gives

```text
26 + 26x + 131x² + 129x³.
```

The gcd of the constant coefficient and 143 is 13. This is an inexpensive factor readout on this input. Repeated squaring takes only a logarithmic number of multiplications of polynomials of degree below four. Lean verifies the entire remainder, the gcd, and both primes in `143=11·13`. [Lean certificate](../PrimeFactors/CyclotomicPascal.lean)

**How often does it work?** Choose two distinct 1,024-bit primes uniformly and condition on their product having 2,048 bits. Reduce `(1+x)^N` modulo every cyclotomic polynomial of degree at most four. Test the gcd of **every individual coefficient** with `N`. The probability that any test gives a proper factor is **less than `2^-323`**. The bound covers all these projections simultaneously and uses no unproved hypothesis.

The [single Pascal coefficient](pascal-readout.md) at an index near `√N` gives an exact factor for every balanced input. The projection considered here mixes coefficients from the entire row when reducing powers of `x`. The resulting low-degree coefficients are cheap to evaluate. Their arithmetic has a different frequency of success. Reducing a power of a polynomial modulo a short polynomial also appears in the AKS primality test. That test certifies compositeness under its hypotheses. A proper gcd with a hidden prime is a stronger and different observation. [Agrawal, Kayal and Saxena, Section 2](https://www.cse.iitk.ac.in/users/manindra/algebra/primality_v6.pdf)

## Degrees one and two

Let `ζ` be a primitive `m`th root and `α=1+ζ`. Interpret a raw coefficient as an integer coordinate in the basis `1,ζ,…,ζ^(φ(m)−1)`, reduced modulo `N`. Degrees one and two have exactly the conductors `1,2,3,4,6`.

| Conductor | Projected power for odd `N=2e+1` |
| --- | --- |
| 1 or 2 | `2^N` or zero |
| 3 | `α=−ζ²`, so the answer depends only on `N mod 6` |
| 4 | `α²=2ζ`, so `α^N=2^e ζ^e(1+ζ)` |
| 6 | `α²=3ζ`, so `α^N=3^e ζ^e(1+ζ)` |

In the last two rows the coordinates of the rotated `1+ζ` belong to `{0,±1,±2}` by the relations `ζ²=−1` and `ζ²=ζ−1`. For products of primes greater than three, every coordinate gcd is 1 or the entire product.

A different test compares the whole power to rotated copies `ζ^jα` via resultants. For `m=4,6`, put `c=2,3` respectively. At a prime `p|N` greater than three, one such resultant vanishes exactly when `c^{m(N−1)/2}=1mod p`. Indeed, `α` is invertible here. In an algebraic closure the remaining scalar `c^e` must belong to the group of `m`th roots, and allowing all rotations tests all of them. If `N=pq`, the condition is precisely

```text
ord_p(c)/gcd(ord_p(c),m/2) divides q−1.
```

A single rational modular power thus tests the same local condition as these rotated cyclotomic comparisons. If both primes satisfy it, the single batched gcd can equal the entire product.

## The four degree-four projections

The remaining conductors are `m=5,8,10,12`. Put `v=2+ζ+ζ⁻¹` and let `w` be its other real conjugate. Both are positive and less than four.

| `m` | `v+w` | `vw` | `(v−w)²` |
| --- | --- | --- | --- |
| 5 | 3 | 1 | 5 |
| 8 | 4 | 2 | 8 |
| 10 | 5 | 5 | 5 |
| 12 | 4 | 1 | 12 |

Since `α²=ζv`, we have `α^N=αζ^e v^e`. Fix one of the four coordinate maps `ℓ` and an orientation `j=e mod m`. The integer sequence `f(n)=ℓ(αζ^j v^n)` satisfies the recurrence with characteristic polynomial `(X−v)(X−w)`. Its exact expression is

```text
(v−w) f(n) = (f(1)−w f(0)) v^n + (v f(0)−f(1)) w^n.
```

If the first two values are both zero as integers, this coordinate vanishes for the entire orientation, so its gcd is `N`. Otherwise they stay nontrivial modulo every prime `p>8`. In fact powers of `ζ` have basis coefficients in `{0,±1}` in each of the four fields, as one checks using `Φ₅=1+x+x²+x³+x⁴`, `Φ₈=1+x⁴`, `Φ₁₀=1−x+x²−x³+x⁴`, and `Φ₁₂=1−x²+x⁴`, reducing exponents modulo `m`. Thus `|f(0)|≤2` and `|f(1)|≤8` since `αζ^j v=ζ^(j−1)(1+ζ)³`.

Work in a finite field containing the two roots of the displayed quadratic modulo `p`. The table guarantees the roots are distinct and nonzero at every prime `p>8`. If this coordinate vanishes at indices `i,j'`, the recurrence identity implies `(v/w)^i=(v/w)^j'`. Indeed, after division by `w^n`, the vanishing condition is a linear equation in `(v/w)^n`. Both coefficients cannot be zero. The admissible exponents occupy at most one residue class modulo the multiplicative order `H` of `v/w`. Swapping the two roots inverts their ratio and preserves its order. [Lean recurrence and two-zero theorem](../PrimeFactors/CyclotomicPascal.lean)

For `m=5,12`, the table has `vw=1`. A comparison of the coordinate to any fixed nonzero integer `C` also restricts the exponent. For primes not dividing `C`, set `y=v^e`, substitute `w^e=1/y`, and multiply the expression by `y`. The result is a quadratic in `y` whose linear coefficient is `−(v−w)C≠0`. Thus at most two values of `y` work for each orientation and target. The order of `v` is at least the order of `v/w=v²`, so the same short-order exceptional set suffices.

## The finite prime-pair bound

A small value of `H` could make many partner primes eligible. Define the integer `U_n=(v^n−w^n)/(v−w)` over the real quadratic field. Its recurrence starts at 0 and 1 with the integer trace and norm from the table. For `n≥1`, choose `v>w` to see that `0<U_n≤4^n`. The inequality uses `v−w≥1`. Every prime with `H=n` divides `U_n`, by reducing the identity modulo that prime. [Lean integer recurrence](../PrimeFactors/CyclotomicPascal.lean) · [Baillie, Fiori and Wagstaff on Lucas sequences, Section 2.3](https://homes.cerias.purdue.edu/~ssw/bfw.pdf#page=3)

Set `X=2^1023` and let `P` be the number of primes in `[X,2X)`. For any positive integer `Y`, a prime with `H≤Y` divides the product of the first `Y` nonzero Lucas terms. Comparing logarithms and summing over all four fields gives at most

```text
2 ln(4) Y(Y+1) / ln X
```

exceptional anchor primes `p`. Each can have at most `P` partner primes. For every other anchor `p`, fix a conductor, coordinate and orientation. Writing the odd partner as `q=2u+1` gives `e=(pq−1)/2=pu+(p−1)/2`. Since `p` is coprime to the order of a nonzero finite-field element, the permitted `u` occupy at most one class modulo `H>Y`. In an interval of length `X/2` this gives at most `X/(2Y)+1` integers. There are `4(5+8+10+12)=140` choices. This counts every possible local hit at either prime by allowing either factor to be the anchor.

The explicit prime-count bounds give `P<1.511X/ln X`. Pairs with both factors in `[√2 X,2X)` alone supply at least `(0.22X/ln X)²/2` unordered distinct pairs satisfying the product condition. Dividing the successful-pair upper bound by this lower bound gives the probability estimate

```text
(2·1.511 / 0.22²) · [ 2 ln(4) Y(Y+1)/X + 140 ln(X) (1/(2Y)+1/X) ].
```

Take `Y=2^345`. Measured in units of `2^-341`, the two terms in brackets are below 720 and 3,110, respectively. The outside factor is below 63. Their product is below `2^18`, proving the advertised `2^-323` bound. [Finite population calculation](stride-budget.md) · [Rosser and Schoenfeld, Corollary 1](https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf#page=6)

## Fixed comparisons in higher degrees

There is also a uniform obstruction for a finite list of **whole-polynomial comparisons**. Fix `m<X`, `d=φ(m)`, and `J` target elements of `ℤ[ζ_m]` specified independently of the unknown prime pair. Compute `α^N` in the cyclotomic ring modulo `N` and take gcds with norms of its differences from the targets. The norm, equivalently the resultant with `Φ_m`, can be computed by a multiplication matrix over `ℤ/Nℤ`. An example menu consists of all `ζ^k(1+ζ^j)`. Choosing a target from this menu after seeing the product is covered by testing the entire menu.

For `m≠2,3`, some complex image of `α` has absolute value greater than one. Its powers never equal one in the number field. All conjugates have absolute value at most two. Apart from primes dividing the nonzero norm of `α`, any anchor where some reduced image of `α` has order at most `Y` divides an integer norm `Norm(α^j−1)` for some `1≤j≤Y`. There are at most

```text
[d ln 2 + d ln(3) Y(Y+1)/2] / ln X
```

exceptional anchors, since `|Norm(α)|≤2^d` and `|Norm(α^j−1)|≤3^(dj)`. For all other anchors, vanishing of a tested norm requires `α^(pq)=γ` in some finite-field image. There are at most `dJ` choices of image and target. In each case the partner `q` occupies at most one residue class modulo an order greater than `Y`, because multiplication by `p` is invertible on the group of exponents. There are therefore at most `dJ(X/Y+1)` candidate partners per anchor. With `Y` of order `X^(1/3)`, normalization as above gives `O(d(J+1) ln(X)/X^(1/3))` for the conditioned large-bit-width population. Neither conductors 2 and 3, where the power is zero or torsion, requires an order estimate.

The single-coordinate analysis and the norm comparison test different observations. The estimates here concern the specified gcds. Nonlinear decoders of several coefficients or targets synthesized from the input outside the specified menu require separate arguments. The recurrence identities and the example are machine checked. The frequency estimates are paper deductions.
