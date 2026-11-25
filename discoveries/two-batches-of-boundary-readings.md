# Choosing a divisor window with two batches of boundary readings

For a balanced 2,048-bit product, **at most 1,000 boundary readings of absolute error at most $1/8$ suffice to select one window containing the larger prime**. The second batch can run in parallel as soon as the first batch finishes. The guarantee includes nearly equal factors. It allows integer heights up to $2^{500}$. Obtaining them efficiently from the product is open. The selected window has a polynomial with at most 24,575 integer roots, and its construction at that dimension has only been costed mathematically. [Selection theorem](../PrimeFactors/BoundaryWindowSelection.lean) · [Centered binomial windows](integer-valued-factor-windows.md)

## How a reading determines the next batch

Let $N=pq$, with distinct odd primes $p<q\le 2p$, and set $\delta=(\log q-\log p)/2$. The public signal is the principal Dirichlet character modulo $N$, whose value at an integer is the indicator of coprimality with $N$. At positive height $t$, write $B(t)=\operatorname{Re}(e^{it\log(N)/2}L_N(it)/\zeta(it))$. Its two missing Euler factors give

$$
\cos(t\log N/2)-B(t)/2=\cos(t\delta).
$$

A boundary reading with error $1/8$ thus gives a cosine reading $y(t)$ with error $1/16$, assuming exact public arithmetic. The required bound applies to the total error after any numerical rounding. Earlier work used either one adaptive query per contraction or a fixed list of all dyadic pair sums. The latter list has a quadratic size bound in the requested bit resolution. Robust phase estimation with doubled frequencies and two phase measurements has precedents. Here every observation is the same real-valued boundary signal, and one shared shift is chosen from that signal. [Euler-factor identity](../PrimeFactors/AnalyticAccess.lean) · [Earlier fixed schedule and reflection counterexample](../PrimeFactors/MixedHeights.lean) · [Kimmel, Low and Yoder, revised paper and errata](https://arxiv.org/abs/1502.02677v3)

1. Choose an integer $K$. Read all $t=1,2,4,\ldots,2^K$. Let $h$ be the first of these heights with $y(h)<25/32$.
2. If no reading crosses that threshold, every compatible frequency lies in $[0,\pi/(3\cdot2^K))$. Otherwise read the shifted heights $2^i+h$ for $0\le i\le K$, reusing any repeated value.

The factor ratio obeys $0\le\delta\le\log(2)/2<\pi/6$. Before the first crossing, the error bound bounds the cosine below by $23/32>\cos(\pi/4)$. Induction through the doublings keeps the phase at each following step at most $\pi/2$. At the crossing the cosine is below $27/32<\cos(\pi/6)$. Thus every compatible frequency $u$ has $hu\in[\pi/6,\pi/2]$. This step prevents reflection about a multiple of $\pi$ from giving an indefinitely ambiguous dyadic transcript. [Reference and resolution proofs](../PrimeFactors/BoundaryWindowSelection.lean)

For two compatible frequencies $u\le v$, put $m=(u+v)/2$ and $d=(v-u)/2$. If $2^K d\ge\pi/6$, some dyadic $t\le2^K$ has $td\in[\pi/6,\pi/3]$. The reference interval gives $0\le hd\le\pi/6$ and $\sin(hm)\ge1/2$. Since $\sin(hm)=\sin((t+h)m)\cos(tm)-\cos((t+h)m)\sin(tm)$, at least one of the two midpoint sines has magnitude at least $1/4$. At both heights the gap sine has magnitude at least $1/2$. The cosine subtraction formula then forces the two predicted readings to differ by at least $1/4$ at one height. They could differ by at most $1/8$ if both matched the observed cosine to $1/16$. Consequently the full compatible interval has diameter at most $\pi/(3\cdot2^K)$, even when it contains zero. Lean proves the separation for each pair and the enclosure using its infimum. [Two-batch proof](../PrimeFactors/BoundaryWindowSelection.lean)

## Cost after the readings

There is a direct interval implementation. Starting from the reference interval, process each dyadic $t>h$ in ascending order. Intersect the current interval with the inverse cosine bands specified by $y(t)\pm1/16$ and $y(t+h)\pm1/16$, clipping cosine endpoints to $[-1,1]$. Retain the smallest closed interval containing the surviving pieces. Its width is at most $\pi/(3t)$. Indeed, the preceding width was at most $2\pi/(3t)$, so two surviving points whose distance reaches $\pi/(3t)$ satisfy the single-scale contradiction just proved. The initial interval at $t=h$ has the required width. During an update the phase spans at most $2\pi/3$ for the first reading and $4\pi/3$ for the second, so only a bounded number of inverse cosine arcs need inspection. This gives $O(K)$ elementary interval updates with exact real operations. The Lean endpoint is specified by an infimum. The interval implementation and its floating-point arithmetic are separate from that formal specification. [Single-scale lemma](../PrimeFactors/BoundaryWindowSelection.lean)

For $K=499$ there are at most 500 heights per batch, with at most 501 bits per height. Elementary range reduction at the largest heights needs an absolute error of order $2^{-500}$ in the input logarithm to keep the known phase error constant. The unknown frequency interval has width at most $\pi/(3\cdot2^{499})$. Since $q=\sqrt N e^\delta<2^{1024}$, the corresponding uncertainty in $q$ is at most $2^{1024}\pi/(3\cdot2^{499})$. Even after allowing one unit of outward rounding, this fits the physical width $4W$ for $W=5359\cdot13\cdot2^{507}$. Lean proves that the center derived solely from the readings and $N$ has an offset $x$ with $q=C+2x$, $|x|\le W$, and $F(x)=0$ for a single nonzero polynomial. The proof assumes $2^{2047}\le N$ and $q<2^{1024}$, so the height and polynomial bounds apply at the requested factor size. It yields no cost bound for the boundary evaluator and does not execute the 24,576-row lattice reduction. [Full-size composition](../PrimeFactors/BoundaryWindowSelection.lean)

How far could the highest query be reduced at the same accuracy? In the continuous phase model, the two values $u=1/8$ and $v=u+2^{-498}$ differ by more than $\pi/(3\cdot2^{499})$. Every height through $2^{495}$ admits the same adversarial reading within $1/16$ of both wave values, by the Lipschitz bound for cosine. This impossibility result applies even to adaptive choices. It concerns recovery of a continuous frequency. Extra integer or product information could distinguish factors by other means. [Checked height obstruction](../PrimeFactors/BoundaryWindowSelection.lean)

## A public-input check on 77

We computed the readings from the cyclic coprimality mask, supplying only $N=77$ and $K=8$. Grouping the Dirichlet series by residue class gives $L_N(s)=N^{-s}\sum_{1\le a\le N,\,\gcd(a,N)=1}\zeta(s,a/N)$, continued to $s=it$. The following Python reproduces the two numerical batches. It approximates each Hurwitz zeta by a finite sum with four Euler–Maclaurin corrections. [Dirichlet and Hurwitz relation](https://dlmf.nist.gov/25.15.E3) · [Euler–Maclaurin representation](https://dlmf.nist.gov/25.11.iii)

```python
import cmath
import math
from functools import lru_cache

n, k = 77, 8
units = [a for a in range(1, n+1) if math.gcd(a, n) == 1]

def hurwitz(s, x, terms):
    z = x + terms
    power = lambda y, e: cmath.exp(e*math.log(y))
    total = sum(power(x+j, -s) for j in range(terms))
    total += power(z, 1-s)/(s-1) + power(z, -s)/2
    rising = s
    for j, coefficient in enumerate((1/12, -1/720, 1/30240, -1/1209600)):
        total += coefficient*rising*power(z, -s-2*j-1)
        rising *= (s+2*j+1)*(s+2*j+2)
    return total

@lru_cache(maxsize=None)
def wave(t, terms):
    s = 1j*t
    partial = sum(hurwitz(s, a/n, terms) for a in units)
    principal = cmath.exp(-s*math.log(n))*partial
    boundary = (cmath.exp(s*math.log(n)/2)*principal/hurwitz(s, 1, terms)).real
    return math.cos(t*math.log(n)/2)-boundary/2

def reading(t):
    return round(16*wave(t, 512))/16

base = [2**i for i in range(k+1)]
first = [reading(t) for t in base]
h = next(t for t,y in zip(base, first) if y < 25/32)
second = [reading(t+h) for t in base]
queries = set(base) | {t+h for t in base}
change = max(abs(wave(t, 256)-wave(t, 512)) for t in queries)
print(h, len(queries), max(queries), change, first, second)

def cut(left, right, t, y):
    lo = math.acos(min(1, y+1/16))
    hi = math.acos(max(-1, y-1/16))
    for a, b in ((lo, hi), (-hi, -lo)):
        first_arc = math.ceil((t*left-b)/(2*math.pi))
        last_arc = math.floor((t*right-a)/(2*math.pi))
        for j in range(first_arc, last_arc+1):
            yield max(left, (2*math.pi*j+a)/t), min(right, (2*math.pi*j+b)/t)

left, right = math.pi/(6*h), math.pi/(2*h)
for t in base:
    if t <= h:
        continue
    pieces = [part for a,b in cut(left,right,t,reading(t))
              for part in cut(a,b,t+h,reading(t+h))]
    left, right = min(a for a,b in pieces), max(b for a,b in pieces)
print(math.sqrt(n)*math.exp(left), math.sqrt(n)*math.exp(right))
```

The first three rounded cosine readings were $1,7/8,5/8$, choosing $h=4$. The two batches used 17 distinct heights through 260. Inverse cosine interval updates gave approximately $[0.2258341,0.2262924]$ in log space, or $[10.9982572,11.0032985]$ for the larger prime. The only integer there is 11, and $77=7\cdot11$ with both factors prime, checked in Lean. Repeating the measurements with 256 and 512 summands changed the unrounded wave by at most $2.1\times10^{-7}$ across these heights. This is a numerical comparison, without a certified floating-point error enclosure. It took 77 gcd tests to form the mask, which by itself encountered both factors, and 796,416 finite-sum terms across both truncations. Repeating a full period at the target size would be infeasible. [Checked arithmetic and conditional decoder](../PrimeFactors/BoundaryWindowSelection.lean)

The pinned RH source gives Dirichlet $L$-function nonvanishing in the strict right half of the critical strip and locates zeros in its interior. The samples here are values of a quotient on the imaginary axis. The finite Euler-factor identity used by the decoder is unconditional. A fast way to obtain those particular values from a 2,048-bit product, at all the stated heights and with verified error, remains open. [Pinned statements](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab/src/Statements.lean) · [Pinned theorems](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab/src/Main.lean)
