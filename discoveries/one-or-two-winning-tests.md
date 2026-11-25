# Only one or two tests win

For each product of two distinct 1,024-bit primes, the complete search range has **exactly one or two** positions that return a prime factor. This holds for each individual product. If its product has 2,048 bits, choosing a position uniformly at random from the primitive range has a success probability below $2^{-1018}$. We still lack an efficient rule to pick a winning position from the product alone. [Cardinality and probability comparison](../PrimeFactors/OffsetWinningCount.lean) · [Definition of the search](complete-offset-search.md)

Both outcomes occur. For 117,449, exactly one position works. For $1{,}891=31\times61$, let $T=43$ and $h=42$. The pair $(j,k)=(6,1)$ returns 31, and $(7,6)$ returns 61. Both lie in the sharp range $3j^2\le4h$. Across all 1,234 same-width pairs of seven-, eight- and nine-bit primes, 1,156 products had one winning position and 78 had two. [Single-position example](../PrimeFactors/CompleteOffsetExample.lean) · [Two-position example](../PrimeFactors/OffsetWinningCount.lean) · [Exhaustive search](../experiments/complete_offset_search.py)

## Why there cannot be a third

Write $T=\lfloor\sqrt N\rfloor$, $h=N-T^2$ and $N=pq$. A successful test gives positive roots $A,B$ with sum $j+2Tk$ and product $Nk^2$. Because $N$ is squarefree and $j,k$ are coprime, $A,B$ are coprime. Indeed, a shared prime would have to divide $k$ and then also $j$. A proper split puts $p$ and $q$ in different roots. Orient the roots by the prime they contain. After removing those primes their product is $k^2$, so each remaining coefficient is a square. Thus $A=ps^2$, $B=qv^2$ in the chosen orientation, with $s,v>0$, $\gcd(s,v)=1$ and $k=sv$. This recovers one factor-coordinate vector from each successful test. Given a vector, both indices are fixed by $k=sv$ and $j=ps^2-2Tsv+qv^2$. [Converse and uniqueness](../PrimeFactors/OffsetSquareWitness.lean)

The quadratic form $Q(s,v)=ps^2-2Tsv+qv^2$ has determinant $h$. Write $B(x,y)$ for its symmetric bilinear form. The identity

$$Q(x)Q(y)-B(x,y)^2=h\det(x,y)^2$$

forces any two different positive primitive vectors in the sharp range to have determinant $+1$ or $-1$. Parallel primitive vectors with the same positive orientation coincide. For independent vectors the determinant is an integer, and the cutoff gives $Q(x)Q(y)\le 4h/3<4h$.

If three such directions existed, the first two would form an integer basis and the third would have both basis coordinates equal to $+1$ or $-1$. Let the three form values be $A,B,C$ with $A$ largest. Expanding the form gives

$$3A^2-4h=2A(A-B)+2A(A-C)+(B-C)^2.$$

The cutoff makes the left side nonpositive, and all terms on the right are nonnegative. All three values must therefore coincide. The cross coefficient in this integer basis is then $+A/2$ or $-A/2$, so $A$ is even. In that basis the form represents only even numbers. But $Q(1,0)=p$ is odd. This rules out a third direction. The earlier reduction theorem guarantees the first winning position for balanced primes with smaller prime at least 17. [Short-vector geometry](../PrimeFactors/OffsetShortVectors.lean) · [Existence](../PrimeFactors/CompleteOffsetSearch.lean) · [Classical binary quadratic form reduction](https://www.wstein.org/edu/124/lectures/lecture23/lecture23/node1.html)

## Does a perfect square ever give the wrong answer?

At every primitive position in the sharp range, a nonnegative square discriminant produces a proper divisor whenever $h\ge2$. This statement holds for general $N$, including repeated prime factors. If the gcd were trivial, one root would contain all of $N$. Removing $N$ would leave two coprime positive integers whose product is $k^2$. Writing them as squares gives $j=(Ts-v)^2+hs^2\ge h$, contradicting $3j^2\le4h$ for $h\ge2$. For $h=1$, the only exception is $j=1,k=T$, which always gives discriminant 1. This explains the one extra square in the nine-bit census, on $111{,}557=334^2+1$. [Square-to-divisor theorem and exception](../PrimeFactors/OffsetSquareSplit.lean)

## Where were the winning positions on the large examples?

This diagnostic takes the **already published prime factors** along with the product. With the factors we can construct $Q$ and reduce its basis directly. Neither full-size product was factored from its digits by this experiment. The independently capped product-only searches remain partial. [Known-factor diagnostic](../experiments/offset_winner_positions.py) · [Fresh generation and certificate](certified-fresh-control.md) · [Crossed prime labels](../benchmarks/unit-quartic.json) · [Product-only runs](../benchmarks/complete-offset-search.json)

| Product | Winning positions | Bits in $j$ | Bits in $k$ | Location in the ascending raw list |
| --- | ---: | ---: | ---: | ---: |
| Fresh comparison | 1 | 510 | 511 | 5.99324%, after more than $2^{1019}$ positions |
| Crossed comparison | 1 | 506 | 507 | 0.03829%, after more than $2^{1011}$ positions |

To see why there is no second position in either case, take the known primitive shortest vector $x$, put $A=Q(x)$, and let $J=\lfloor\sqrt{4h/3}\rfloor$. Each example satisfies $AJ<h$. Any independent integer vector $y$ has $A Q(y)\ge h$ by the determinant identity, hence $Q(y)>J$. The diagnostic’s verification mode combines each position receipt with the separately checked prime certificate and runs the axiom audit on the resulting uniqueness theorem. The exact rank is one-based in the unfiltered order of increasing $j$, then increasing $k$. It is obtained from an integer floor sum, with no simulation of the preceding positions. [Concrete certificates](../PrimeFactors/OffsetWinnerExamples.lean) · [Exact ranks](../experiments/offset_winner_positions.py)

```sh
python3 -m experiments.offset_winner_positions --verify
lake build
lake env lean scripts/Audit.lean
```
