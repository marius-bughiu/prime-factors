# Can floor sums locate the factor?

For $N=pq$ with $p\le q$ prime, an exact sum using only $N$ returns the smaller prime. A direct calculation still tests every candidate. We tested a shortcut that would replace a long list of quotients by a few floor sums of straight lines. On the 46-bit input 45,249,671,261,437 the exact minimum was **3,700 pieces** for the balanced odd interval. On the two 2,048-bit controls Lean proves that such a representation requires **more than $2^{507}$ pieces on the fresh input and $2^{508}$ on the crossed input**. The missing step is an efficient way to extract the much smaller difference of the quotient sums directly. [Lean prefix identity and lower bounds](../PrimeFactors/ReciprocalFloorPrefixes.lean)

## What an exact prefix tells us

For every positive $N$ and $x$ the jump $J_N(x)=\lfloor N/x\rfloor-\lfloor(N-1)/x\rfloor$ is one exactly when $x$ divides $N$, and zero otherwise. Thus for every $H\le\lfloor\sqrt N\rfloor$,

$$
\sum_{x=2}^H xJ_N(x)=
\begin{cases}0&H<p,\\p&H\ge p.\end{cases}
$$

Indeed the only divisor between two and the square root is $p$. This also holds for a square of a prime. Taking $H=\lfloor\sqrt N\rfloor$ recovers $p$ in one sum. When both primes are odd and $q\le2p$, restricting to odd $x$ in $[\lceil\sqrt{N/2}\rceil,\lfloor\sqrt N\rfloor]$ preserves the answer. Computing each summand separately amounts to trial division. [Prefix theorem](../PrimeFactors/ReciprocalFloorPrefixes.lean)

Ordinary floor sums of a rational affine function admit a Euclidean recurrence with logarithmic cost in the denominator. The weighted version also admits recurrences. It would therefore be attractive to represent the quotient sequence $\lfloor N/x\rfloor$ pointwise by a short list of such expressions, then obtain prefix sums by the recurrence. The existing triangle search uses affine functions to *enclose* the reciprocal curve and checks the integer points inside. Sladkey also computes an isolated value of the unweighted divisor summatory function with a geometric subdivision. Neither algorithm requires a piecewise exact description of this quotient sequence. [AtCoder floor sum](https://atcoder.github.io/ac-library/production/document_en/math.html) · [Weighted recurrences and the enclosing triangle](quotient-search.md) · [Sladkey, divisor summatory function](https://arxiv.org/abs/1206.3369)

## How much a single piece can represent

Give a piece an arbitrary affine term and any signed sum of rounded affine terms,

$$
F(x)=ax+b+\sum_i c_i\lfloor a_i x+b_i\rfloor,\qquad M=\sum_i|c_i|.
$$

All slopes and intercepts may be real. The $c_i$ are integers and all parameters and breakpoints may depend on $N$. For three equally spaced arguments the second difference of a rounded affine function is an integer strictly between $-2$ and $2$. Its magnitude is therefore at most one. The second difference of $F$ on the same three points has magnitude at most $M$. If it reproduces $\lfloor N/x\rfloor$ at $a,a+h,a+2h$, removing the three floor operations adds strictly less than two to the upper bound. Direct subtraction gives

$$
\frac{2Nh^2}{a(a+h)(a+2h)} < M+2.
$$

Inside the smaller-factor range $a+2h\le\sqrt N$. Counting in *odd positions*, a separation of $g$ places means $h=2g$, so $8g^2<(M+2)\sqrt N$. For any integer $J$ with $J^4\ge N$, a block of consecutive odd positions thus has length at most $(J+1)(M+1)$, allowing for both endpoints. For $M=1$, four times its length is at most $5J+8$. Summing these bounds across blocks even allows overlap. [Three-point and complete-cover proofs](../PrimeFactors/ReciprocalFloorPrefixes.lean)

On the two controls we counted every odd candidate from $\lceil N/(2^{1024}-1)\rceil$ through $\lfloor\sqrt N\rfloor$, using the published integer bounds on their square roots and fourth roots. For a single rounded line per piece, the number of pieces exceeds the quoted powers of two. In the general formula the **sum of the charges $1+M$** exceeds those same powers. With coefficients restricted to $\pm1$, this counts floor terms plus blocks. A large binary-encoded coefficient has arithmetic cost distinct from its absolute value. The theorem also assumes pointwise agreement throughout the represented blocks. Exact cancellation between two large sums, a separate correction at a few exceptional positions, or a calculation returning only the final aggregate could bypass this particular obstruction. [Full-size integer receipts](../PrimeFactors/ReciprocalFloorPrefixes.lean)

## Can a higher-degree curve represent more positions?

For a rational polynomial $P$ of degree less than $r$, its $r$th forward difference is zero. The reciprocal has an exact nonzero difference,

$$
\Delta_h^r(N/x)=\frac{(-1)^r r! N h^r}{x(x+h)\cdots(x+rh)}.
$$

If $P$ and $N/x$ have identical floors at the $r+1$ indicated positions, their difference has magnitude less than one there, so its $r$th forward difference has magnitude at most $2^r$. For $x+rh\le\sqrt N$, Lean proves $r!h^r\le2^r(x+rh)^{r-1}$. In particular a quadratic uses $r=3$. On odd candidates separated by $g$ positions, $h=2g$ and the necessary bound becomes $6g^3\le(x+6g)^2\le N$. This polynomial version permits a single rational polynomial of the chosen degree per piece. It shows that each fixed degree still leaves a growing number of pieces on intervals whose lengths are proportional to $\sqrt N$. [All-degree reciprocal identity and mesh bound](../PrimeFactors/ReciprocalFloorPrefixes.lean)

## Small exact comparison

We supplied only $N$. For this test the interval starts at the first odd integer at least $\sqrt{N/2}$ and ends at $\lfloor\sqrt N\rfloor$. For each piece we fitted a single function $\lfloor aj+b\rfloor$ of the odd-position index $j$. The separate weighted jump recovers the smaller prime in the table. The two large test cases below have previously checked prime-pair certificates. [41-bit certificate](https://marius-bughiu.github.io/prime-factors/#modular-hyperbola-41) · [46-bit certificate](https://marius-bughiu.github.io/prime-factors/#modular-hyperbola-holdout-binary-46)

| $N$ | Odd positions | Weighted jump | Minimum pieces | Longest piece | Slope comparisons | CPU seconds to segment and check |
|---|---:|---:|---:|---:|---:|---:|
| 34,387 | 27 | 137 | 4 | 9 | 92 | <0.001 |
| 132,079 | 54 | 269 | 6 | 11 | 253 | <0.001 |
| 1,900,014,700,027 | 201,863 | 1,000,003 | 1,285 | 791 | 18,011,481 | 3.464 |
| 45,249,671,261,437 | 985,115 | 6,045,709 | 3,700 | 1,526 | 148,833,349 | 26.267 |

The conjecture that the number of pieces never exceeds the square of the input bit length already fails on the last product, since $46^2=2,116$. The classifier below uses the genuine discrete floor conditions. For integer samples $y_j$, an intercept exists for slope $a$ precisely when every pair $u<v$ satisfies

$$
\frac{y_v-y_u-1}{v-u}<a<\frac{y_v-y_u+1}{v-u}.
$$

This is equivalent to requiring the interval from $\max_j(y_j-aj)$ to $\min_j(y_j+1-aj)$, excluding the upper endpoint, to have positive width. Each piece takes the longest feasible prefix. This minimizes the number of pieces because any suffix of a feasible piece is feasible. One can replace the start of any optimal cover by the longest prefix, truncating or deleting the pieces it reaches, without increasing its length. The code checks a rational line at every point of every accepted piece. The comparisons and minimum-piece argument here are exact integer computation and a paper proof. Lean verifies the independent general lower bound. The timings exclude forming the sample list and computing the jump readout, which both visit all listed positions.

```python
from math import isqrt
from time import process_time

def fit_count(y):
    begin, pieces, tests, longest = 0, 0, 0, 0
    while begin < len(y):
        ln, ld, un, ud = -y[0]-2, 1, y[0]+2, 1
        end = begin+1
        while end < len(y):
            saved = ln, ld, un, ud
            for j in range(begin, end):
                d, dy = end-j, y[end]-y[j]
                tests += 1
                if (dy-1)*ld > ln*d:
                    ln, ld = dy-1, d
                if (dy+1)*ud < un*d:
                    un, ud = dy+1, d
                if ln*ud >= un*ld:
                    break
            else:
                end += 1
                continue
            ln, ld, un, ud = saved
            break
        a, den = ln*ud+un*ld, 2*ld*ud
        b = max(y[j]*den-a*j for j in range(begin,end))
        assert all((a*j+b)//den == y[j] for j in range(begin,end))
        pieces += 1
        longest = max(longest, end-begin)
        begin = end
    return pieces, longest, tests

def run(n):
    first = isqrt((n-1)//2)+1
    first += int(first%2==0)
    xs = range(first,isqrt(n)+1,2)
    y = [n//x for x in xs]
    readout = sum(x*(v-(n-1)//x) for x,v in zip(xs,y))
    start = process_time()
    result = fit_count(y)
    print(n, len(y), readout, result, round(process_time()-start,3), flush=True)

if __name__=='__main__':
    for n in (34387,132079,1900014700027,45249671261437):
        run(n)

```
