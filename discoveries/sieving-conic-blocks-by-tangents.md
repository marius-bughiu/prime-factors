# Sieving conic blocks by their tangents

On four products with two 20-bit prime factors each, a complete search of the signed conics used 226,426 ordinary blocks. Using two small split primes reduced that to 170,293 blocks, with the same recovered points. The count of candidate lines fell from 96,065 to 64,492. All methods received only the product. [Experiment](../experiments/tangent_lattice_arcs.py) · [Results](../research/tangent-lattice-arcs.json)

## The extra congruence

Write a search chart as $bz^2-au^2=M$, allowing signed $a$ so that this includes the ellipses. Choose an odd modulus $h$ coprime to $abM$ such that $a/b$ has a square root $t$ modulo $h$. Every point satisfies

$$
(z-tu)(z+tu)=M/b\pmod h .
$$

The first factor is a unit. Once chosen, it determines the second and hence the residue pair $(u,z)$. Consequently the conic occupies exactly $\varphi(h)$ pairs modulo $h$. This equality also holds for products and powers of split primes. [Lean equivalence and exact count](../PrimeFactors/ConicTangentLattice.lean)

There is more information at each such pair $(r,s)$. Put $u=r+hi,\ z=s+hj$ and $c=(bs^2-ar^2-M)/h$. Expansion gives

$$
 c-2ar i+2bs j=0\pmod h .
$$

With $g=\gcd(2bs,h)$, this fixes $i$ modulo $g$. The remaining digits lie in a single affine lattice

$$
 u=r'+hgI,\qquad z=s'+h k I+(h^2/g)J .
$$

Its fundamental parallelogram has area $h^3$. A restriction to the old residue pair alone gives area $h^2$. The formulas also cover vertical tangents and prime powers. This is an elementary instance of the local congruence divisibility used by the $p$-adic determinant method. The use of small real arcs and integer determinants predates this application. [Heath-Brown, *The density of rational points on curves and surfaces*](https://ora.ox.ac.uk/objects/uuid%3A61776df1-3232-4fdc-87de-f3c01f6bce3f) · [Bombieri and Pila, *The Number of Integral Points on Arcs and Ovals*](https://people.maths.ox.ac.uk/pila/Ovals.pdf)

## Work in the transformed chart

For an ordinary height function $z=f(u)$, the new graph is

$$
 J(I)=\frac{f(r'+hgI)-s'-hkI}{h^2/g},\qquad J''(I)=g^3f''(r'+hgI).
$$

Given ordinary block width $W$, the search uses $\max(1,\lfloor W/g\rfloor)$ consecutive values of $I$ per block. A full block spans approximately $hW$ physical coordinates. It recovers its integer points by enclosing the transformed graph between rational lines and solving one quadratic per candidate line. All the endpoint and slope calculations use integers.

If $h\le W$, the physical distance between consecutive block starts in any single class is at least $h(W-h+1)$. In an inclusive chart $1\le u\le X$, this gives the finite upper bound

$$
 B_h\ \le\ \varphi(h)\left\lceil\frac{X}{h(W-h+1)}\right\rceil .
$$

The leading block-count ratio for $W$ large compared with $h$ is $\varphi(h)/h=\prod_{\ell\mid h}(1-1/\ell)$. Squaring an existing prime preserves this ratio. Adding a different good split prime lowers it. Initialization still has to find the modular slopes and form the individual lattices. This comparison concerns block setups. The time also depends on arithmetic per block and the number of candidate lines. Lean checks the class count, affine parametrization from the two Bézout identities, determinant, finite stride bound, and the transformed hyperbola's slope-error estimate. The complete Python enumerator is checked against direct enumeration. [Lean results](../PrimeFactors/ConicTangentLattice.lean) · [Ordinary signed arc search](scanning-signed-norm-arcs.md)

## Complete comparisons

The eight input products are the existing four 16-bit and four 20-bit prime-pair holdouts. Each run enumerates the same complete unit-reduced charts. Each chart chooses its smallest odd split prime coprime to its public coefficients, or its first two such primes. The table totals setup and line counts across the four products in each group. CPU time sums four per-product medians, with four rotated runs including prime selection, class initialization, and point reconstruction. Separate direct coordinate scans checked 210 small equations and choices of modulus. [Input selection](../experiments/signed_norm_arcs.py) · [Full measurements](../research/tangent-lattice-arcs.json)

| Bits per prime | Modulus | Classes initialized | Blocks | Candidate lines | CPU (ms) |
|---:|:---|---:|---:|---:|---:|
| 16 | Ordinary | 0 | 38,764 | 15,458 | 150 |
| 16 | First split prime | 86 | 32,321 | 11,309 | 131 |
| 16 | Its square | 522 | 32,017 | 10,538 | 135 |
| 16 | First two split primes | 1,040 | 30,300 | 9,936 | 134 |
| 20 | Ordinary | 0 | 226,426 | 96,065 | 1,048 |
| 20 | First split prime | 92 | 184,177 | 73,352 | 831 |
| 20 | Its square | 588 | 185,054 | 71,276 | 839 |
| 20 | First two split primes | 1,112 | 170,293 | 64,492 | 772 |

## Two 2048-bit products

For each full-size public control, the experiment computes the complete ordinary block count and the upper bound above, chart by chart, using all good split primes through 257. The fresh product's upper bound is 56.1697% of its ordinary count. The crossed product's is 52.4520%. Both ordinary counts have 686 bits. Even the sums of the numbers of residue classes have 174 and 167 bits, respectively. The benchmark generates a Lean proof for each product. It checks the selected targets, local representatives, all five chart dimensions and radii, the split-conic class counts, both decimal totals and their rounded ratio. The bound applies to every set of class counts obeying the chart’s pointwise start and stride rules. No full-size scan was run, and the entire product remains unresolved in each case. [Counting proof generator](../experiments/tangent_lattice_receipt.py) · [Native fixtures](../benchmarks/tangent-lattice-arcs.json) · [Counts and remaining cofactors](../research/tangent-lattice-arcs.json)
