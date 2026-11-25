# A square test is guaranteed to exist

Suppose someone gives us only the product of two distinct 1,024-bit primes. Using its digits, we can now specify a list of tests and prove that at least one of them will return a prime factor. The proof applies to every such pair. Even after the product rules out whole groups, the two large comparisons each retain more than $2^{1019}$ candidate pairs. The open question is how to select a successful test cheaply. [Complete search theorem](../PrimeFactors/CompleteOffsetSearch.lean) · [Work before and after the filters](complete-offset-work.md)

For example, take 117,449. The preceding square is $342^2$, leaving a remainder of 485. Take adjustment 17 and multiplier 12. The weighted sum is $17+2\cdot342\cdot12=8{,}225$. Its square exceeds $4\cdot12^2\cdot117{,}449$ by exactly one. Halving $8{,}225-1$ gives 4,112. Its greatest common divisor with 117,449 is 257, and division gives the other prime, 457. All arithmetic in this test uses the product and the two search indices.

## What the product specifies

Let $T=\lfloor\sqrt N\rfloor$, $h=N-T^2$, and $J=\lfloor\sqrt{4h/3}\rfloor$. The coverage theorem assumes $N=pq$ for distinct primes $17\le p<q\le 2p$. In particular it covers two distinct primes of the same 1,024-bit width, in either input order. It gives at least one pair of coprime positive integers satisfying

$$1\le j\le J,\qquad 1\le k\le \lfloor Tj/h\rfloor+1.$$

At that pair, $D=(j+2Tk)^2-4k^2N$ is a nonnegative square. Write $d=\sqrt D$. The gcd of $N$ and $(j+2Tk-d)/2$ is one of the primes. For other pairs a square may have a trivial gcd. The executable Lean probe checks the sign, the square and the proper divisor. On a 2,048-bit input $T<2^{1024}$ and $h\le 2T$, so $J<2^{513}$. A single adjustment can still have many possible multipliers. [Executable test and theorems](../PrimeFactors/CompleteOffsetSearch.lean)

## Why the unknown primes imply a short adjustment

For the proof, use the primes to define the positive quadratic form

$$Q(s,v)=p s^2-2Tsv+q v^2,\qquad pQ(s,v)=(ps-Tv)^2+hv^2.$$

Its determinant is exactly the public remainder $h$. Pick an integer vector giving the least positive value $j$. Its two coordinates are coprime, since dividing both by a common factor shrinks the value by that factor squared. Extend the vector to an integer basis of determinant one. Adding multiples of the first vector to the second makes their cross coefficient $b$ satisfy $|2b|\le j$. The value $c$ at the second vector satisfies $c\ge j$ by minimality. Preservation of the determinant gives $h=jc-b^2\ge 3j^2/4$. This is the classical two-dimensional reduction bound. The Lean implementation proves the needed result directly. [Lean minimum theorem](../PrimeFactors/ReducedOffsetMinimum.lean) · [William Stein on reduced forms](https://www.wstein.org/edu/124/lectures/lecture23/lecture23/node1.html)

Under the stated size and balance assumptions $j<p\le q$. The coordinates therefore have the same sign and are nonzero. Use their positive absolute values. The completed-square identities for $pQ$ and $qQ$ imply $s<q$ and $v<p$. With $k=sv$ we have

$$j+2Tk=ps^2+qv^2,\qquad (j+2Tk)^2-4k^2N=(ps^2-qv^2)^2.$$

The smaller quadratic root is $ps^2$ or $qv^2$. Its gcd with $N$ is exactly $p$ or $q$ because the other prime exceeds the corresponding coordinate. The square identity and $j^2\le4h$ also imply $k\le\lfloor Tj/h\rfloor+1$. Finding the shortest vector directly would require the hidden coefficients $p,q$. What we can compute from $N$ alone is the search region and the test at any chosen point. These implications use elementary integer arithmetic and hold unconditionally. [Complete proof](../PrimeFactors/CompleteOffsetSearch.lean)

## How far the first adjustments can reach

For $T< L=S^2$, split all square hits according to the sign of $Tj-hk$. The earlier count handles the nonnegative case. For a negative sign we have $d<j$ and the same parity, so $a=(j-d)/2$ and $b=(j+d)/2$ are positive integers. They satisfy

$$a+b=j,\qquad h k^2=kTj+ab.$$

In particular $k\mid ab$. We can write $k=xu$ where $x\mid a$ and $u\mid b$. Knowing $T$ and the two ordered factor pairs $(x,a/x)$ and $(u,b/u)$ determines $N$. For $j\le J<2^f$ an ordered pair $(x,y)$ with $xy\le J$ takes at most $fJ$ possible labels. To see this, store the exponent $i=\lfloor\log_2 x\rfloor$ and the integer $2^i(y-1)+x-2^i$, which is less than $J$. Thus the extra side contributes at most $L(fJ)^2$ inputs, even counting trivial gcds. [Signed count and injective encoding](../PrimeFactors/SignedOffsetFrequency.lean) · [Earlier count](offset-sweep-frequency.md)

Combined with the earlier count and the published explicit lower bound for the number of target prime pairs, fewer than one in $2^{422}$ pairs can give any square through $J=2^{40}$. Even through $J=2^{461}$ fewer than half can. The sampling model is two uniformly chosen distinct 1,024-bit primes conditional on a 2,048-bit product. These bounds allow **every** positive multiplier. The numerical upper bounds count hits regardless of how quickly a method can choose among the tests. The prime-count denominator is a deduction from Rosser and Schoenfeld external to the Lean proof. [Finite comparisons](../PrimeFactors/SignedOffsetFrequency.lean) · [Denominator and exact sampling model](stride-budget.md#an-explicit-bound-at-exactly-2048-bits)

The sharper divisor-sum estimate in the earlier note improves the comparison on paper. At $J=2^{473}$ take $1+\ln(LJ)<1040$ and $\ln J<329$, using $\ln 2<0.694$. Add $L(474J)^2$ for the negative branch. The resulting upper bound still covers fewer than half of the target pairs. At $J=2^{40}$ the earlier numerator $205\cdot2^{1576}$ plus $L(41J)^2$ still gives fewer than one in $2^{438}$. Lean checks these last two integer comparisons. The divisor-sum inequalities are paper deductions, while the weaker exponents 461 and 422 use the Lean-checked finite encoding throughout the numerator. [Divisor-sum derivation](offset-sweep-frequency.md#a-sharper-divisor-sum) · [Integer comparisons](../PrimeFactors/SignedOffsetFrequency.lean)

## What happened when we searched

We tried every distinct pair of 7-bit primes, every distinct pair of 8-bit primes and every distinct pair of 9-bit primes. This covers 1,234 products. Every product gave a proper split. A generated Lean certificate checks the chosen indices, the prime returned by the probe, the other prime, and the product on all 1,234 inputs. For eight 9-bit pairs omitting the additional last multiplier removed every successful test. On 117,449 the only successful pair in all 241 raw positions was $(17,12)$. It was the 116th position visited and the 68th integer square root taken. [Only successful pair on 117,449](../PrimeFactors/CompleteOffsetExample.lean) · [Full census and replay](../experiments/complete_offset_search.py) · [Fixtures with expected factors](../benchmarks/complete-offset-search.json)

On each of the two 2,048-bit comparisons, a Euclidean floor sum counted the exact number of raw positions before the gcd filter. The fresh range contained about $2^{1023.23}$ positions and the crossed range about $2^{1023.002}$. Trying the first 64 positions on each took 36 and 37 integer square roots respectively, yielding no factors. These counts concern the full list. A successful test could occur early, as it did on the small example. [Exact counts and outstanding work](../benchmarks/complete-offset-search.json)

```sh
python3 -m experiments.complete_offset_search 117449 --max-pairs 241 --exhaust
python3 -m experiments.complete_offset_search --census --census-certificate /tmp/CompleteOffsetCensus.lean
lake env lean -DwarningAsError=true /tmp/CompleteOffsetCensus.lean
python3 -m experiments.complete_offset_search --controls --max-pairs 64
lake build
lake env lean scripts/Audit.lean
```
