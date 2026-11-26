# Predicting a carry from both ends of the product

Suppose a rule can see 1,664 of the 2,048 binary digits of a product, including the leading 1. Can it usually predict the missing correction in our two-digit factoring test? At radix $D=2^{704}$, one guess succeeds on fewer than **one in $2^{72}$** eligible prime pairs. Even a million guesses per observation give a fraction below $2^{-52}$. The rule can do unlimited computation on the visible digits, and the second correction can use the entire product. The bound applies to this particular test with the residual limit below. [Earlier factor search](factoring-from-two-rounded-digits.md) · [Lean theorem for the actual sample](../PrimeFactors/MixedPrefixSample.lean)

## What the rule sees

Draw two distinct 1,024-bit primes uniformly, conditioned on their product having 2,048 bits. Let $X=2^{1023}$ and $B=X/D=2^{319}$. The rule reads $N\bmod X$ and the first $h$ bits after the mandatory leading 1. It proposes up to $J$ lower corrections per observation. Each proposed signed residual $w=N-D\operatorname{near}(N/D)+kD$ must satisfy $|w|<D^2/4$. For an odd product at this even radix, $w$ is nonzero. If any upper correction gives a proper factor, even by an accidental square, a signed factorization of $w$ fixes both residues $r=p\bmod D$ and $s=q\bmod D$. The bound for $640\le h\le711$ is $J/2^{712-h}$. [Observation map and success event](../PrimeFactors/MixedPrefixPopulation.lean) · [Signed residuals](../PrimeFactors/LowBitsCarryMenu.lean)

Write $p/D=i+r/D$ and $q/D=j+s/D$. Fix the low word $c$ and the residues. The permitted integer pairs satisfy $rj+si\equiv(c-rs)/D\pmod B$ whenever the right side is integral. Each coordinate determines the other modulo $B$. Fixing the high word confines $(p/D)(q/D)$ to $[T,T+U)$ with $U\le1/2$. Divide the horizontal range into $2^{107}$ strips of width $L=2^{212}$. The chord of $T/x$ across one strip has slope $-T/[x_0(x_0+L)]$. At $x=x_0+t$ the bend is proportional to $t(L-t)\le L^2/4$. After subtracting the chord the vertical spread is at most $(L^2+1/2)/B$. The area determinant of any three candidate points then has magnitude less than $B$, and the low-word congruence makes it divisible by $B$. The three points must be collinear. Three distinct points on such a line have a product spread of at least one, so at most **two** fit in a strip. This halves the strip count in the original tangent argument. [Chord and collinearity proof](../PrimeFactors/MixedPrefixSlab.lean) · [High-word interval](../PrimeFactors/MixedPrefixBand.lean) · [Lattice and count](../PrimeFactors/MixedPrefixWords.lean)

Lean combines this count with the bound on signed divisors and counts both possible orders of the primes explicitly. A finite calculation in Lean proves the needed lower bound on the number of primes in $[1.415X,2X)$. A published estimate gives an independent check. Rosser and Schoenfeld's Corollary 1 gives $M>(2\cdot1023/1024-1.25506\cdot1.415)X/\log X>0.2221X/\log X$ for that count. Since $\log X<710$, this implies $35500(M-1)>11X$, the exact premise of the Lean theorem. [Unconditional Lean theorem](../PrimeFactors/ChebyshevPrimeSample.lean) · [Prime-count argument](one-base-for-the-factor-sum.md#how-many-prime-pairs-are-in-the-sample) · [Rosser and Schoenfeld, p. 69](https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf#page=6)

## Finding the line within a strip

There is also a formula for the line. Given the two factor residues and one strip, write $i=i_0+t$ and $j=j_0+mt+Bz$ using the low-word congruence. Set $x_0=i_0+r/D$, $A=x_0(x_0+L)$, $b=j_0+s/D$, $v=T/x_0-L^2/B$, and $E=(L^2+1/2)/B$. Dirichlet approximation gives integers $d,e$ with $0<d\le2L$ and $|\delta|\le1/(2L+1)$ for $\delta=d(m+T/A)/B-e$. Then every point satisfies the same equation

$$et+dz=\left\lfloor-\frac dB(b-v)-\frac{\delta L}{2}+\frac{d E}{2B}+\frac12\right\rfloor.$$

The possible integer levels occupy an interval of width at most $2LE/B+L/(2L+1)<1$. The $+1$ in the denominator matters at this strip width. Thus the residues, the two product words, and the strip location supply the line before either integer point is known. Solving its linear equation leaves a one-variable quadratic product on the allowed parameter interval. There are still $2^{107}$ possible strips per fixed choice of residues, and the residues themselves depend on the proposed residual and its signed divisors. The formula prices one part of the search. The continued-fraction idea also appears in Hiary's interval method for an exact product. [Explicit line and rounding proof](../PrimeFactors/MixedPrefixLine.lean) · [Hiary, 2016](https://arxiv.org/abs/1408.2608)

For a small example take $D=B=32$, $L=4$, $r=5$, $s=19$, $c=159$, $T=1884$ and $i_0=32$. The residue equation gives $j=26+9t+32z$. The approximation $(d,e)=(3,1)$ gives the line $t+3z=3$. It contains the two positions $(i,j)=(32,58),(35,53)$. Both represent integer factor pairs of 1,929,375. Across all 262,144 ordered pairs in the small model below, 260,598 cells held one pair and 773 held two.

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
