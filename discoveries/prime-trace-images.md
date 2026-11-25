# Prime tests for one offset coordinate

On the 49-bit product $502005281288939$, masks for primes from 5 through 97 left one candidate among 731,911 parity-compatible offsets. That candidate gave the factors $17838631$ and $28141469$. At 2048 bits, a long trace interval can contain more than $2^{428}$ false candidates even when every power of each of 73 small primes is available. The size of the interval changes both the filtering power and the cost of representing it. [Experiment](../experiments/offset_trace_words.py) · [Proof](../PrimeFactors/OffsetTraceImage.lean) · [Benchmark fixtures](../benchmarks/offset-trace-words.json)

## Which residues does a coordinate select?

Write $N=pq$, $T=\lfloor\sqrt N\rfloor$. A winning coordinate has positive, coprime $s,v$, $k=sv$, weighted trace $S=j+2Tk=ps^2+qv^2$, and signed gap $z=ps^2-qv^2$. At any modulus coprime to $sv$, put $x=sp/v$ and $y=vq/s$. Then

$$
xy=N,\qquad S=k(x+y),\qquad z=k(x-y).
$$

The change of variables is invertible. At an odd prime $\ell\nmid Nsv$, the possible $j$ are exactly the existing projective slope mask multiplied by $k$, with the point at infinity omitted. The same normalized lookup works for every coordinate; its multiplier and translation change. Testing these masks again on positions already selected by the same projective primes adds no information. [Projective slopes](reconstructing-winning-positions.md) · [Scaled trace and signed gap](../PrimeFactors/OffsetTraceImage.lean)

For each trace the normalized labels are the two roots $x$ and $N/x$. They coincide exactly at $x^2=N$, giving $z=0$ and $S=2kx$. The trace image has $(\ell+1)/2$ elements when $N$ is square modulo $\ell$ and $(\ell-1)/2$ otherwise. In the two-root case the signed gaps are opposite. The Chinese remainder theorem multiplies the image sizes for distinct eligible primes, including after a translation or a change to any coprime step in the trace index. [Exact prime counts](../PrimeFactors/ResidueCount.lean) · [CRT counts](../PrimeFactors/FactorSumCRT.lean)

A finite set of these primes cannot eliminate an *unrestricted* coordinate. The public assignment $(p,q)=(1,N)$ gives $S_0=s^2+Nv^2$ and $z_0=s^2-Nv^2$. Every offset $j\equiv S_0-2Tk\pmod M$ passes the local equations at moduli dividing $M$. Under a bounded offset or signed-gap interval, all representatives can lie outside the interval.

## What remains after arbitrary prime-power tests?

Consider $W$ trace entries $S_i=a+di$ on a fixed coordinate, with $d$ coprime to every tested prime. Write $n=4Nk^2$. At an odd prime $\ell\nmid n$, every first digit for which $S_i^2-n$ is a **nonzero** square passes the signed-square test at every power of $\ell$. There are $(\ell-3)/2$ such digits when $n$ is square, and $(\ell-1)/2$ when it is nonsquare. If $\ell\mid n$, all $\ell-1$ nonzero trace digits work. These local conditions exclude $j\equiv0\pmod\ell$ whenever $\ell\mid k$. At primes coprime to $2sv$, the square root produces actual local weighted factor labels at every power. [Lifting regular roots](../PrimeFactors/PersistentLocalSurvivors.lean) · [Weighted label equivalence](../PrimeFactors/OffsetTraceImage.lean)

For a prime set $P$, put $M=\prod_{\ell\in P}\ell$ and $A=\prod_{\ell\in P}\big((\ell-3)/2\big)$. Every complete period has at least $A$ universally surviving classes, so every interval of $W$ entries has at least $\lfloor W/M\rfloor A$ survivors. For all primes from 5 through 379, $\log_2 M=506.45$ and $\log_2 A=427.31$ to two decimals. At $W\ge2^{508}$ the bound exceeds $2^{428}+1$. A fixed oriented coordinate can correspond to only one true trace, since $S=ps^2+qv^2$. The eight sampled parity windows on the two 2048-bit controls all have at least $2^{508}$ entries. This count considers the independent local congruences before any signed-gap interval is imposed. [Kernel-checked interval bound](../PrimeFactors/OffsetTraceImage.lean) · [Coordinate uniqueness](../PrimeFactors/OffsetSquareWitness.lean)

One can additionally require $\gcd(j,k)=1$ in the parity windows while retaining all prime-power tests through 373. Assume $0<k\le2^{513}$ and start with the parity prescribed by $s+v$. Each regular class repeats at least 1,108 times, even in the first $2^{508}$ entries. The test at 2 is automatic for primitivity because even $k$ requires odd $j$. Primes from 5 to 373 dividing $k$ were already excluded from $j$. Prime 3 can remove at most $\lfloor1108/3\rfloor+1$ of the repeats. Each prime above 373 dividing $k$ removes at most $\lfloor1108/374\rfloor+1$: the difference in $j$ between successive repeats is $2M$, which is coprime to every such prime. There are at most 64 of these primes, since $256^{65}>2^{513}$. At least 546 repetitions per regular class remain. Multiplying by the number of classes and discounting the one possible genuine trace still gives **more than $2^{428}$ primitive false offsets**. Lean checks the complete-period bound, the count of large prime divisors, the union bound per repeated class, and the numerical inequalities. The parity and coprimality argument above combines them. [Counting lemmas](../PrimeFactors/OffsetTraceImage.lean)

## Intersecting the masks on a bounded example

For the 49-bit input, the coordinate bound gives 613 primitive coordinate charts with 731,911 parity positions. The following counts use the primes in $[5,C]$. The empty-chart column includes one chart whose interval already contained no primitive offset. The procedure uses only the product and the equal-width factor promise during selection.

| Last prime $C$ | Primitive offsets left | Empty charts among 613 |
| ---: | ---: | ---: |
| No primes | 512,992 | 1 |
| 19 | 23,475 | 7 |
| 31 | 3,126 | 79 |
| 43 | 418 | 358 |
| 67 | 16 | 597 |
| 97 | 1 | 612 |

The implementation precomputes a word of $\ell$ bits for each nonzero $k\bmod\ell$. A bit at $i$ represents $j=2i$ and tests the trace $j/k+2T$. To handle a chart starting at $j_0$, rotate its word by $j_0/2\bmod\ell$, repeat the resulting pattern across the chart width, and intersect it with the current candidate word. Once a word is zero, the remaining masks for that chart can be skipped. At primes dividing $k$ the first-power discriminant imposes no restriction, and a final gcd enforces primitivity. Enumerating the set bits yields the actual offsets to test. This is exact at the chosen primes. [Implementation](../experiments/offset_trace_words.py)

The complete run filled 32,356 mask entries and performed 6,850 intersections on candidate words of at most 2,318 bits. One bit survived *before* the final gcd. Its $(j,k,s,v)=(2921,2322,54,43)$ yielded the factorization after one integer square test. The same complete search with no prime masks needed 512,992 square tests. Six alternating runs of the same two Python modes, including mask setup and excluding Lean verification, took median process CPU times of 0.0103 s with the masks and 0.2980 s without them on the development machine. Word operations cost more as their operands grow. The preallocation guard stops both 2048-bit inputs at a 4,096-bit budget with zero chart visits. The published rows retain the unresolved inputs. [Cases and budgets](../benchmarks/offset-trace-words.json)

```sh
python3 -m experiments.offset_trace_words 502005281288939 --prime-limit 97
python3 -m experiments.offset_trace_words 502005281288939 --prime-limit 0
python3 -m unittest tests.test_offset_trace_words
```
