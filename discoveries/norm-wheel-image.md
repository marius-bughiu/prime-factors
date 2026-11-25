# Every ordinary wheel residue occurs inside the canonical norm band

Can the three quadratic forms rule out whole residue classes of the smaller prime before the grouped factorial search starts? For any balanced product $N$, put $H=\lfloor N^{1/4}\rfloor$. If $H\ge256$ and $16\operatorname{lcm}(2,W)\le H$, **every unit modulo $W$ is represented by a canonical norm value in the actual balanced interval**. Thus a filter that accepts a residue whenever a canonical norm in the interval has that residue retains every ordinary wheel class. This includes wheels chosen from $N$. [Lean theorem](../PrimeFactors/NormWheelImage.lean) · [The three forms](norm-band-product.md)

Let $M=\operatorname{lcm}(2,W)$. Dirichlet's theorem supplies some odd prime in each unit class modulo $W$. The canonical representation theorem supplies a form and coordinates for that prime. This prime can be arbitrarily far from the interval. The following boxes let us move its two coordinates independently by multiples of $M$, preserving the value modulo $W$ and both parities. The entries are multiples of $H/32$. [Prime representation](../PrimeFactors/CanonicalNorm.lean) · [Dirichlet's theorem in mathlib](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LSeries/PrimesInAP.html)

| Form | Interval for $t$ | Interval for $a$ |
|---|---:|---:|
| $t^2+a^2$ | $[20,22]$ | $[20,22]$ |
| $t^2+2a^2$ | $[16,18]$ | $[16,18]$ |
| $2a^2-t^2$ | $[16,18]$ | $[23,25]$ |

Each coordinate interval has length $H/16\ge M$ and contains an integer in every class modulo $M$. The third box also enforces $t<a$. Evaluating at the extreme coordinates shows that every value $V$ in these boxes satisfies $734H^2/1024\le V\le H^2$. For $H\ge256$, this implies $V^2\le N\le2V^2$ because $H^4\le N<(H+1)^4$. Hence the relocated witness lies in $[\lceil\sqrt{N/2}\rceil,\lfloor\sqrt N\rfloor]$ with both coordinates within the public cap.

The 63-bit comparison has $H=49{,}680$, so the result applies to both wheels 210 and 2,310. It also applies at 2,048 bits whenever $\operatorname{lcm}(2,W)\le2^{507}$. It concerns a filter on the **value modulo one wheel**. It leaves open pruning inside individual coordinate blocks, using other information about a factor, or computing the same modular product more efficiently. [Grouped factorial baseline](factorial-progressions.md)
