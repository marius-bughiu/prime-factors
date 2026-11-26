# Predicting a carry from both ends of the product

**Proof sketch awaiting Lean verification.** At base $D=2^{704}$, a checked result already limits predictions that can read the lowest 1,023 bits of the product. Could adding its first 640 bits *after* the mandatory leading 1 make accurate predictions common? The calculation below suggests the success fraction is still below $J/2^{71}$ for a list of $J$ proposed lower corrections per observation. It uses the same distinct-prime population and the same residual-product limit $0<|w|<D^2/4$ as the checked low-bit theorem. The upper correction may be chosen using the full product. [Checked theorem for low bits alone](../PrimeFactors/LowBitsCarryMenu.lean)

Let $Q=2^{1023}$ and $B=Q/D=2^{319}$. Fix the observed low word $c=N\bmod Q$, one proposed lower correction, and a signed factorization of its proposed residual $w$. The two signed divisors determine $r=p\bmod D$ and $s=q\bmod D$. Write $X=p/D=i+r/D$ and $Y=q/D=j+s/D$. In the square $B\le X,Y<2B$, the low word requires

$$rj+si\equiv(c-rs)/D\pmod B.$$

When the right side is integral, the permitted integer pairs lie in a translate of a lattice with determinant $B$. Since $r,s$ are odd, either coordinate determines the other modulo $B$. In this particular square each coordinate therefore occurs at most once.

With $h$ high bits after the leading 1, the product $XY$ lies in one interval $[T,T+U)$ of width $U=2B^2/2^h$. This is at most $1/2$ for $h\ge640$. Cut the range of $X$ into $2^{108}$ intervals of width $L=2^{211}$. Over each one, subtract the tangent line to $T/X$ at its left endpoint $x_0$. The identity

$$T/X-T/x_0+T(X-x_0)/x_0^2=T(X-x_0)^2/(Xx_0^2)$$

bounds the vertical spread of the remaining points by $4L^2/B+U/B$. The absolute determinant made by the differences of three points is less than $2L(4L^2/B+U/B)<B$. As this determinant is a multiple of $B$, all the points in the interval lie on a line. A line containing two of them has primitive integer direction $(a,b)$ with $ab\ne0$. Along this line the product is a quadratic of the integer line parameter with leading coefficient $ab$. Two integer parameter values on the same side of its vertex have product values at least one apart. At most two points can therefore fall in the permitted product interval.

This gives at most $2^{109}$ points per low word, high prefix and signed divisor. The earlier low-word count allows $2^{319}$. Charging for all $2^h$ possible additional prefixes gives the proposed fraction $J/2^{711-h}$ for $640\le h\le710$. Converting this geometric count into a Lean theorem with the exact observation map and finite-set cardinalities remains open.

**Small exact check.** With $D=B=32$ and $L=4$, we enumerated all 262,144 ordered pairs obtained by taking every odd $r,s<D$ and each $32\le i,j<64$. Across fixed residues, low word, half-unit product interval and slab, there were 260,598 cells with one pair and 773 with two. No cell held three. This checks a finite instance of the geometric claim. The target-width probability above still has proof-sketch status.

~~~python
from collections import Counter

D = B = 32
sizes = Counter()
for r in range(1, D, 2):
    for s in range(1, D, 2):
        cells = Counter()
        for i in range(B, 2 * B):
            for j in range(B, 2 * B):
                n = (D * i + r) * (D * j + s)
                cells[n % (B * D), (2 * n) // D**2, (i - B) // 4] += 1
        sizes.update(cells.values())
print(sizes)
~~~
