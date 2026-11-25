# How soon must the marking reveal a factor?

Fix a product of distinct odd primes $N=pq$ and a public integer $D$ with Jacobi symbol $(D/N)=-1$. Label the prime at which $D$ is a square $p$. A one-row search can find this prime in **at most $(p-1)/2$ norm tests**. Randomizing the row once gives **exactly $(p+1)/4$ tests on average for every fixed $N,D$**, conditional on drawing a unit. Independent random positions took $p/2$ on average. Even the improved average exceeds $2^{1021}$ tests for a 1,024-bit split prime. [Lean proofs](../PrimeFactors/MarkedSupportBox.lean) · [Marked trace and independent-position comparison](quadratic-extension-trace.md)

## Which trace terms can change?

For the cubic $f(z)=z^3-z$, marking multiplies it by $(z-2)^2$. At a grid coordinate $(x,y)$ let $L=(x-2)^2-Dy^2$. The marked Jacobi value equals the original value when $\gcd(L,N)=1$, and equals zero otherwise. Thus a change requires a nonunit marker. At $x=2\pm u, y=v$, both signs give the same $L=u^2-Dv^2$. Whenever $q\nmid v$, this marker cannot vanish at the inert prime $q$. A zero at the split prime therefore gives $\gcd(L,N)=p$, even if the original cubic value was already zero. [Marker and gcd theorems](../PrimeFactors/MarkedSupportBox.lean)

For $p\ge7$, at least one of these two grid positions actually changes whenever $L\equiv0\pmod p$ and $q\nmid v$. At $p$, one split coordinate is 2 and the other is $2+2u$ or $2-2u$. Since $f(2)=6\ne0\pmod p$, a zero smooth term requires the other coordinate to be in $\{-1,0,1\}$. The two other coordinates sum to 4. No sum of two members of this set is 4 modulo a prime at least seven. At $q$ each of the three norm factors $(x-j)^2-Dv^2$ is nonzero for $j=-1,0,1$.

For example, at $N=77,D=8,u=v=1$, the marker is $-7$ and its gcd is 7. At $x=1$ the smooth and marked terms are both zero. At $x=3$ the smooth term is $-1$ and the marked term is zero. Lean checks all four Jacobi values. The gcd test detects the factor on either sign. [Checked example](../PrimeFactors/MarkedSupportBox.lean)

## A sharp rectangle for every possible selector

Take $1\le U,V<p$. A box tests $u^2-Dv^2$ for all $1\le u\le U, 1\le v\le V$. Its exact worst-case guarantee at the split prime is

$$
  \text{every nonzero square }D\bmod p\text{ has a hit}
  \quad\Longleftrightarrow\quad (U+1)(V+1)>p.
$$

For the forward construction, choose a local square root $s$ in the proof. Bounded rational approximation gives $1\le v\le V$ and an integer $j$ with $|vs-pj|(V+1)\le p$. Under the strict size bound, $u=|vs-pj|\le U$. It is positive since both $s$ and $v$ are nonzero modulo $p$. The actual box search needs neither the prime nor its square root. If also $V<q$, every hit gives the proper gcd $p$. The one-row construction below always has that property. [Bounded approximation](../PrimeFactors/RootIntervalSlope.lean) · [Sharp threshold and counterexample](../PrimeFactors/MarkedSupportBox.lean)

Conversely, if $(U+1)(V+1)\le p$, take $s=U+1$. For every allowed $v$, the integer $sv$ lies strictly between $U$ and $p-U$. Neither sign is represented in the first coordinate, so $D=s^2\bmod p$ misses the entire box. CRT pairs this square with any nonsquare at $q$, giving a legitimate public integer with negative Jacobi symbol. **For each prime and undersized rectangle there exists a missed selector**. A prescribed input-dependent rule for choosing $D$ can avoid this particular selector.

The minimum guaranteed square side is exactly $\lfloor\sqrt p\rfloor$. If direct tests cost one per leaf, $(U+1)(V+1)\le 2UV+2$ shows that at least $(p-1)/2$ leaves are needed. A single row of that width attains the bound. If polynomial batching instead charges a degree $U$ and $V$ evaluation points, the smallest possible axis sum is $\lceil2\sqrt{p+1}\rceil-2$. At fixed $S=U+V$, balancing the two sides maximizes $(U+1)(V+1)$ at $\lfloor(S+2)^2/4\rfloor$. Thus this cost is minimized by nearly square rectangles. The existing grouped norm search already achieves fourth-root order in $N$ on balanced inputs. [Earlier product and evaluation construction](short-norm-boxes.md)

## Scanning one randomized row

Draw $a$ uniformly from $1,\ldots,N-1$ and compute $\gcd(a,N)$. A nonunit immediately gives a proper factor. For a unit, scan $i=1,2,\dots$ and stop at the first $\gcd((ai)^2-D,N)>1$. The denominator coordinate is fixed at one, so $q$ never divides a tested value. The first hit gives $p$. A bound on $p$ can set a cap in advance, although the loop needs no such bound to stop.

To count the work, fix either square root $s$ of $D\bmod p$. The two solutions are $i\equiv\pm s/a\pmod p$. Exactly one is in $1,\ldots,(p-1)/2$. For each such $i$, exactly two choices of $a\bmod p$ put the first hit there, namely $s/i$ and $-s/i$. Each admits $q-1$ invertible lifts at $q$, so the first-hit index is uniform on that integer interval. A cap of $B\le(p-1)/2$ therefore has exact success probability $2B/(p-1)$. Conditional on a unit, the full run uses $(p+1)/4$ norm gcds on average, in addition to the initial unit gcd. [First-hit multiplicity at one prime and in CRT coordinates](../PrimeFactors/MarkedSupportBox.lean)

For $N=77,D=8$ the split prime is 7. Among the 60 units, exactly 20 first hit 7 at each of indices 1, 2 and 3. The mean is two norm tests. This enumeration uses only the product and selector.

```python
from collections import Counter
from math import gcd

n, d = 77, 8
counts = Counter()
for a in range(1, n):
    if gcd(a, n) == 1:
        i = 1
        while gcd((a*i)**2 - d, n) == 1:
            i += 1
        counts[i] += 1
assert counts == {1: 20, 2: 20, 3: 20}
```

In an equality-query model with a uniformly hidden square class at $p$, a single fixed rational slope tests only one of the $(p-1)/2$ possible classes. Distinct queries attain the best possible average and worst-case number of individual probes in that model. Algorithms that inspect $D$, batch many tests together, or use other information from $N$ have different costs. The row improves the direct early-stop count. It gives neither an efficient evaluation of the complete extension sum nor an improvement on the best grouped factoring searches.
