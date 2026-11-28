# When a block swap is off by one

At radix 64, the prime 2,749 has blocks 42 and 61. Exchanging them gives 3,946. **One more gives the other prime, 3,947.** Starting with the product 10,850,303, the radix and the offset one, a division gives one block-product candidate. Fourteen comparisons locate two indices to check. The first, 61, gives the prime pair. The direct ascending Fermat scan on this product takes 55 midpoint tests. A rational comparison and an integer square test have different costs. [Checked reading](../PrimeFactors/OffsetTransposeReadout.lean) · [Ordinary Fermat fixture](../benchmarks/cases.json)

## What the product fixes

Let the two factors be $p=Ba+b$ and $q=Bb+a+t$, with $0<a\le b<B$ and a known positive offset $t$. The unknown quantity $C=b(a+t)$ has the public remainder $N\bmod B$. Put $E=\lfloor N/(B+1)^2\rfloor$. Lean proves

$$E<C\le E+Bt.$$

There are exactly $t$ integers with a specified remainder modulo $B$ in this interval. At $t=1$ this determines $C$ in one step. In the example $E=2568$ and $N\bmod64=63$, giving $C=2623$. The analogous exact reversal, with $t=0$, uses a different interval. [Remainder and interval proofs](../PrimeFactors/OffsetTransposeBlockWindow.lean) · [Exact reversal](when-exchanging-two-blocks-reveals-both-primes.md)

## Why three binary searches suffice for each candidate

Write $z=a+t$. If the candidate is right, $C=bz$ and the quantity $H=(N-(B^2+1)C)/B$ equals $b^2+z^2-t(Bb+z)$. Thus a positive candidate index $x$ for $b$ must satisfy

$$x^2-Btx+(C/x)^2-tC/x=H.$$

Over the relevant integer indices $1\le x\le\min(B-1,\lfloor C/(t+1)\rfloor)$, the difference between successive values on the left strictly increases. A first binary search locates where the values begin to rise. One search on each side then locates all possible equalities with $H$, including a pair of equal adjacent minima. Each of the two returned indices still needs the digit, divisibility and product checks. [Quartic identity, convexity and exact checks](../PrimeFactors/OffsetTransposeQuartic.lean) · [Threshold proof and adjacent-minimum control](../PrimeFactors/ConvexIntegerReadout.lean)

With $B\le2^k$, this costs at most **$3kt$ rational comparisons** across the $t$ rows, plus at most $2t$ final index checks and the work of forming the rows. In the example, $H=1623$ and the two indices are 61 and 62. Only 61 divides 2,623. It gives $z=43$ and $a=42$. Both indices can work for a composite product. With $B=8,t=1,N=700$, one row gives both $14\cdot50$ and $20\cdot35$. [Total comparison bound and prime example](../PrimeFactors/OffsetTransposeReadout.lean) · [Composite ambiguity](../PrimeFactors/OffsetTransposeQuartic.lean)

## How often the assumption holds

Choose any radix and any nonnegative offset up to $2^{128}$ after seeing the full product. **Fewer than one in $2^{361}$** of the eligible 2,048-bit products have this shape even with that latitude. The denominator counts all distinct 1,024-bit prime pairs with a 2,048-bit product. At fixed radix and offset, specifying the smaller prime determines the other word. At very large radices the factor width strongly limits the possible leading digits. The proof sums these counts over every allowed choice. The comparison budget above applies once a radix and offset are selected. [All-radix, all-offset population proof](../PrimeFactors/OffsetTransposePopulation.lean)
