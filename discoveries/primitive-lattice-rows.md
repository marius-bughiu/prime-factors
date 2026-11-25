# Which lattice rows can contain a square?

On 502,005,281,288,939, the search recovered **17,838,631 × 28,141,469** while skipping 193,978 more candidate points than the previous row test. The new test uses the determinant of two integer directions to rule out an entire row before visiting its points. The median search time changed from 0.571 to 0.554 seconds over five runs. On the eight smaller products, the search took slightly longer despite visiting fewer points. Eight groups on each 2,048-bit control still left the entire product unresolved. [Checked fixtures](../benchmarks/offset-row-norm.json) · [Earlier grouping results](grouping-remainder-searches.md)

## Use the primitive direction

The input is a positive nonsquare integer $N$. Put $T=\lfloor\sqrt N\rfloor$, $h=N-T^2$ and $F(j,k)=(j+2Tk)^2-4Nk^2$. A winning position has coprime coordinates and $F(j,k)=z^2$ for an integer $z$. In a group with oriented lattice basis $x=(a,b),y=(c,d)$ and determinant $M>0$, row $u$ consists of the points $v=(j,k)=w x+u y$. The old test required $F(x)$ to be square modulo divisors of $u$. [Group definition and the previous pivot test](../PrimeFactors/OffsetLatticeBatches.lean)

Let $g=\gcd(|a|,|b|)$, $x_0=x/g$, $A=F(x_0)$. The integer
$$
  L=\det(x_0,v)=(M/g)u
$$
is known for the entire row. Bézout gives a vector $y_0$ with $\det(x_0,y_0)=1$, so $v=r x_0+L y_0$ for some integer $r$. If $v$ is primitive, then $r$ and $L$ are coprime. Thus $z^2\equiv r^2 A\pmod L$, and $A$ must be square modulo every divisor of $L$. Checking the prime powers in $L$ can demand more digits at a prime already included in the lattice. This implication holds for composite moduli and for either sign of the row index. [Determinant and coordinate proofs](../PrimeFactors/OffsetRowNorm.lean)

There is a second rejection even when $A$ is zero modulo the tested power. Let $p\nmid 2N$ be an odd prime, and let $t=v_p(L)>0$ be the exponent of $p$ in a nonzero $L$. If **$t$ is odd and $p^{t+1}\mid A$**, the whole row fails. Write $C=F(y_0)$ and $F(v)=A r^2+2BrL+C L^2$. The determinant identity gives $B^2-AC=4N$, so $2B$ and $r$ are units modulo $p$. Only the middle term has valuation $t$. The three terms therefore sum to an integer of odd valuation, which cannot be a square even modulo $p^{t+1}$. For example, with $N=91$, $T=9$, $x=(2,1)$, $y=(-3,0)$, the determinant is 3 and $F(x)=36$. Every row with $3\nmid u$ has $t=1$ and fails this test. [Modular exclusion and its application to primitive points](../PrimeFactors/OffsetRowNorm.lean)

For $p\nmid 2Ng$ these two rules characterize the entire odd-prime obstruction on a nonzero row. This converse is a paper argument. When $t>0$, $r$ can be any $p$-adic unit because the original free coefficient multiplies $g$. Thus $s=L/r$ ranges over elements of valuation $t$, and the problem is whether $A+2Bs+Cs^2$ can be a square. If $v_p(A)<t$, the leading unit and valuation agree with those of $A$; the test modulo $p^t$ decides. If $v_p(A)=t$, the derivative at zero is a unit, so the polynomial has a zero of valuation $t$. If $v_p(A)>t$, the valuation is exactly $t$; for even $t$, the first unit digit of $s/p^t$ can be chosen to make the leading digit equal to one, which lifts to a square. The case $t=0$ follows from the local points below. [Simple-root lifting](https://kconrad.math.uconn.edu/blurbs/gradnumthy/hensel.pdf)

## A limit on local tests of a whole row

For the original basis, put $A'=F(x)$, $C'=F(y)$, and define $B'$ by $F(wx+uy)=A'w^2+2B'wu+C'u^2$. A prospective square must solve the norm equation
$$
   (A'w+B'u)^2-A'z^2 = 4NM^2u^2.
$$
Every row has a public rational point. When $b\ne0$, choose $w=-du/b$ so that $k=0$ and $F(j,0)=j^2$. A second square direction is $(N+1-2T,1)$, where the square is $(N-1)^2$. If $a-b(N+1-2T)\ne0$, intersect the row with that direction. Since $M\ne0$, at least one construction applies. These witnesses need not be positive integer points in the search box. [Norm identity and rational witnesses](../PrimeFactors/OffsetRowNorm.lean)

At every prime $p\nmid Mu$, the construction also gives a **primitive square at every power of $p$**. If $b$ is a unit, the horizontal witness has $j=-Mu/b$, a unit. Otherwise $a-b(N+1-2T)$ is a unit and the second witness has $k=Mu/(a-b(N+1-2T))$, a unit. A congruence confined to these primes cannot eliminate a complete row. There is even a balanced product with a row that passes every prime-power test but has no integer square anywhere. For $N=1,247=29\times43$, take $x=(1,2)$, $y=(0,1)$, $u=-1$. Here $M=|u|=1$, and $F(w,2w-1)=-71w^2+212w-88$. The only nonnegative values are 53 and 52, at $w=1,2$. Both positions are in the search box. Lean proves local solvability and integral failure separately. [Checked local and integer example](../PrimeFactors/OffsetRowNorm.lean)

## Measured search work

Both modes used the same ordered groups, reduced bases, event caps and primes through 31. The normal search checks the two new row rules before calculating the interval of positions. A separate replay enumerates the excluded positions and confirms that all winning positions survive. Timings below are local medians over five repetitions in alternating order and exclude Lean certificate replay. [Normal entry point](../experiments/offset_lattice_batches.py) · [Comparison and timings](../experiments/offset_row_norm.py)

| Input | Groups checked | Point visits before → after | Square tests before → after | Median seconds before → after |
| --- | ---: | ---: | ---: | ---: |
| Eight published 32-bit inputs | 571 | 57,737 → 50,359 | 6,562 → 5,905 | 0.0376 → 0.0405 |
| 49-bit product above | 4,800 | 1,070,273 → 876,295 | 91,261 → 79,458 | 0.571 → 0.554 |
| Fresh 2,048-bit control | 8 | 1,106 → 788 | 102 → 72 | 0.0682 → 0.0678 |
| Crossed 2,048-bit control | 8 | 1,200 → 1,071 | 137 → 125 | 0.0691 → 0.0691 |

The 49-bit run still visited all 96,203 rows. The determinant test rejected 9,121 additional rows and the odd-valuation test rejected another 6,109. Setting up and applying them took 36,574 extra prime tests on the normalized axes and 74,278 extra modular divisibility tests on row indices. Across the eight smaller products the two tests rejected 389 and 522 additional rows, costing 3,097 extra prime tests and 4,148 divisibility tests. All nine winning positions were retained and Lean checked all eight prime pairs. On the full-size inputs the two tests saved 30 and 12 square roots respectively; the unvisited groups are reported with the remaining cofactors. [Frozen work counts](../benchmarks/offset-row-norm.json)

The same row filter also runs after the deterministic lifts of singular directions, using the four-prime reserve schedule. On the eight smaller inputs the extra filter reduced 43,459 visits to 40,936 and 4,821 square tests to 4,672; median time rose from 0.0285 to 0.0309 seconds. On the 49-bit input it reduced 563,759 visits to 522,152 and 46,350 square tests to 45,724; median time rose from 0.324 to 0.332 seconds. The combined search retained all nine small winning positions and the one 49-bit winner, and Lean checked every resulting factor pair. On the first eight lifted groups of each full-size control, both modes had the same point and square-test counts. [Deterministic lift and reserve schedule](lifting-singular-batches.md)

~~~sh
python3 -m experiments.offset_row_norm --timings 5 --verify
python3 -m experiments.offset_row_norm --timings 5 --forced --verify
python3 -m experiments.offset_row_norm
python3 -m experiments.offset_lattice_batches 502005281288939 --drop 2 --max-batches 4800 --max-events 2000000 --exhaust --primitive-rows --verify
~~~
