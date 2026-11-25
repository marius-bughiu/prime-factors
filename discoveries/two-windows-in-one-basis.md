# How much does the gap between two factor windows cost?

For the balanced product $11{,}227$, the candidate smaller prime lies between 89 and 105 if both primes have seven bits. Consider the two groups of odd candidates $\{89,91,93\}$ and $\{101,103,105\}$. We can guarantee one quartic that vanishes at every divisor in those two groups, before learning whether either group contains one. The proof uses a smaller bound in each polynomial degree. On this example the improved bound crosses the threshold for that guarantee. The arithmetic selects the two symmetric groups in advance. Locating a useful pair of groups for a general large number remains a separate search. [Checked results](../PrimeFactors/PairedChebyshevWindows.lean)

## One basis for both groups

Write the possible divisor as $c+s x$, with $s$ coprime to the public product $N$. Fix an integer center distance $A$ and radius $W$, with $0<W<A$. The two real intervals have $A-W\le |x|\le A+W$. The monic quadratic $P(x)=x^2-A^2-W^2$ maps each component onto the same interval $[-2AW,2AW]$. The degree-$j$ monic Dickson polynomial $D_j(z,(AW)^2)$ has magnitude at most $2(AW)^j$ there for $j\ge1$. We use $1$ as the constant basis element. Pair each even-degree polynomial $D_j(P(x),(AW)^2)$ with the odd-degree polynomial $xD_j(P(x),(AW)^2)$. Up to degree $2h$, $h\ge1$, the product of these bounds is

$$2^{2h-1}(A+W)^h(AW)^{h^2}.$$

This divides the corresponding product for the ordinary paired powers by $2^{(h-1)^2}$. Both lists have a monic integer polynomial in every degree. Both therefore give an integer change of basis of determinant one. The determinant reduction comes entirely from the smaller bounds used to scale coefficients. [Original paired powers](../PrimeFactors/PairedDivisorWindows.lean) · [Dickson bounds](../PrimeFactors/GapPolynomialScale.lean)

The enclosing interval supplies another monic integer polynomial in every degree. Choose its polynomial whenever its bound is smaller. For the enclosing interval use half-radius $U=\lceil(A+W)/2\rceil$, which preserves integer coefficients. If $A+W$ is even, put $q=4AW/(A+W)^2$. The ratio of the paired to the enclosing bound in degree $2j$ is $q^j$ for $j\ge1$. In degree $2j+1$ the ratio is $2q^j$ for $j\ge1$. Both linear bounds equal $A+W$. Thus the enclosing polynomial can be preferable at low odd degrees, and the paired polynomial eventually wins at high odd degrees. Choosing by degree preserves determinant one. For every $W<A$ and total degree at least two, the product strictly improves on the enclosing bounds, including after rounding. [Basis, determinant and strict comparison](../PrimeFactors/PairedChebyshevWindows.lean)

## A finite difference in what can be guaranteed

For $N=11{,}227$, $c=97$, stride two, $A=3$, $W=1$, the public lower bound for tested divisors is $D=89$. Here are the five scale factors, in increasing degree.

| Basis | Scale factors | Product |
| --- | --- | ---: |
| Ordinary paired powers | $1,4,6,24,36$ | 20,736 |
| Chebyshev on the enclosing interval | $1,4,8,16,32$ | 16,384 |
| Chebyshev on the paired intervals | $1,4,6,24,18$ | 10,368 |
| Choose by degree | $1,4,6,16,18$ | 6,912 |

The degree-four, depth-two finite box test requires $5^5 N^3$ times the last column to be strictly less than $D^{10}$. Only 6,912 passes. The theorem gives a nonzero quartic with at most four integer roots across both windows. Its root at $x=3$ follows from $97+2\cdot3=103$ and $11{,}227=103\cdot109$. This comparison concerns a sufficient theorem. An explicit reduction can still find a short row when its basis fails the volume test. Producing a general row, isolating its roots and testing the proposed divisors all require work. [Finite comparison and root theorem](../PrimeFactors/PairedChebyshevWindows.lean)

## The exact continuous limit

For degree $2h$ with $h\ge1$, the smallest possible uniform magnitude of a monic real polynomial on these two intervals is exactly $2(AW)^h$. To see the lower bound, replace a competitor $f$ by its even part $(f(x)+f(-x))/2$, which can only decrease its supremum on a symmetric set. This even polynomial has the form $g(P(x))$ with $g$ monic of degree $h$. Since $P$ maps onto $[-2AW,2AW]$, it suffices to use the single-interval Chebyshev minimum. The scaled Chebyshev polynomial takes the alternating values $\pm2(AW)^h$ at the $h+1$ cosine extremal points. A strictly smaller monic competitor would force their difference, of degree at most $h-1$, to change sign $h$ times. Composition attains the bound. The Lean module checks the general integer upper bounds and the continuous quartic optimum. The argument in this paragraph gives the continuous result in arbitrary even degree. [Classical inverse polynomial images](https://projecteuclid.org/journals/acta-mathematica/volume-187/issue-1/Polynomial-inverse-images-and-polynomial-inequalities/10.1007/BF02392833.full) · [Schiefermayr on minimum deviation and capacity](https://arxiv.org/abs/1306.6181)

The exponential rate per degree is $\sqrt{AW}$, the logarithmic capacity of the union. One component alone has capacity $W/2$, the enclosing interval $(A+W)/2$, and a single interval of the same total length as both components has capacity $W$. A gap increases the price relative to that equally long connected interval. The mixed basis can save a second construction at two specified locations. The capacity formula gives no mechanism for selecting those locations. These comparisons use continuous intervals. A small finite set of integer candidates can admit stronger bounds. Chinburg, Hemenway, Heninger and Scherr study a related obstruction for auxiliary polynomials for roots of a monic congruence modulo a specified integer. The divisor modulus is unknown in this project. The finite comparison here follows directly from the jet and coefficient counts. [Capacity and small roots](https://arxiv.org/abs/1605.08065) · [One-window construction](../PrimeFactors/ChebyshevDivisorWindow.lean)

At a fixed allowed capacity $E>0$ and half-gap $g=A-W$, the radius of each component must satisfy $W(W+g)\le E^2$. Thus $W\le(\sqrt{g^2+4E^2}-g)/2$. The two components together have length $4W$, which is strictly less than the single connected length $4E$ when $g>0$. Two independent single-window constructions could each cover length $4E$ at the same capacity. A paired construction is useful when the two prescribed locations matter more than covering every point between them.
