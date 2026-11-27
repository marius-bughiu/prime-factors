# Which recurrence order reveals the larger prime?

Suppose the only input is a product $N=pq$ of two distinct odd primes, with $p<q$. There is a sequence defined entirely from $N$ whose shortest fixed linear recurrence has length exactly $d=(q-3)/2$. If we knew $d$, we could read off $q=2d+3$ and divide $N$ by $q$ to get $p$. For two 1,024-bit primes, however, this recurrence spans at least $2^{1022}$ positions. Obtaining its length cheaply from the product remains the open step. [Exact order and factor-width bound](../PrimeFactors/JacobiSharpComposite.lean)

## What the sequence measures

For each $i=0,1,2,\ldots$, compute the even Jacobi moment

$$u_i=\sum_{t=0}^{N-1}t^{2(i+1)}\left(\frac{t^2-4}{N}\right)\pmod N.$$

The Jacobi symbol in parentheses is a sign or zero computable from $t$ and $N$. A monic recurrence of order $d$ is a fixed rule that gives $u_{i+d}$ as a linear combination of the preceding $d$ entries modulo $N$ for every $i$. “Monic” means the coefficient of that last entry is one when all terms are moved to the same side. [Complete Jacobi moment](../PrimeFactors/ProjectiveWordMoments.lean)

Modulo either prime $\ell$, the sequence is a sum of powers of the nonzero squares except $4$. Each of these $(\ell-3)/2$ bases has nonzero weight, and a recurrence polynomial must vanish at every base. Taking one linear factor for each base attains that degree. To get a recurrence modulo $N$, multiply the shorter polynomial by a power of $X$ until both have the same degree. This shifts an identity already true at every index. The Chinese remainder theorem then combines the coefficients. The larger prime determines the minimum order. Including all positive moments, odd and even, gives minimum order $q-3$. [Prime-field argument](../PrimeFactors/JacobiMomentRecurrence.lean) · [Composite construction](../PrimeFactors/JacobiSharpComposite.lean)

## A check at 77

Using $N=77$ alone in the moment formula gives the first eight values $2,6,42,37,55,35,72,20$. One recurrence polynomial is

$$X^4+4X^3+16X^2+42X+14.$$

For example, $55+4\cdot37+16\cdot42+42\cdot6+14\cdot2=1155=15\cdot77$. The nonzero square bases other than $4$ are $1,2$ modulo $7$ and $1,3,5,9$ modulo $11$. The polynomial vanishes on both lists. Lean checks the recurrence for every subsequent position and proves that degree four is minimal. From four we obtain $2\cdot4+3=11$ and $77/11=7$. The first eight values can be reproduced from the repository root using the existing Jacobi implementation. [Lean certificate](../PrimeFactors/JacobiSharpComposite.lean) · [Jacobi implementation](../experiments/projective_word_moments.py)

```python
from experiments.projective_word_moments import jacobi

n = 77
moments = [
    sum(pow(t, 2*(i+1), n) * jacobi(t*t-4, n) for t in range(n)) % n
    for i in range(8)
]
assert moments == [2, 6, 42, 37, 55, 35, 72, 20]
```

## How much information the finite test uses

If $L$ is a known upper bound on $d$, any $2L$ consecutive even moments suffice to determine $d$ by fitting monic recurrences through degree $L$. The proof uses $L$ consecutive equations and works for any starting index. A direct evaluation of one moment sums $N$ terms. Even with all the moments supplied, writing a dense recurrence of the minimum degree would take at least $2^{1022}+1$ coefficient slots at the stated factor width. These costs describe this way of reading the order. The theorem leaves open whether some other calculation could obtain it more efficiently. [Finite-window theorem](../PrimeFactors/JacobiSharpComposite.lean)
