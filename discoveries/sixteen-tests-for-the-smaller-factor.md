# Sixteen tests for the smaller factor

On the fresh 2,048-bit product, sixteen tests derived from the product leave at most **8.5580%** of the possible positions for its smaller factor after removing multiples of 2, 3 and 5. On the crossed product the corresponding ceiling is **6.1590%**. Both factors are assumed to have 1,024 bits. These tests recovered neither pair. The older fast result on the crossed product used a clue chosen from its published factors. [Public inputs, roots and integer bounds](../research/many-character-windows.json) · [Origin of the earlier clue](testing-one-factor-remainder.md)

These percentages count integers throughout the actual interval where the prime can lie. On the fresh input the 8.5580% ceiling still allows about $4.31\times10^{305}$ positions. There is no cheap way here to jump to the next survivor. In a separate eight-test experiment checking sampled divisors directly took less time than determining which of them passed the filters. [Same-position comparison](halving-the-sum-residues-on-a-fresh-product.md#trying-eight-moduli-on-the-same-positions)

## How the product gives the tests

Write $N=pq$ with $p\le q\le 2^{1024}-1$. Then $\lceil N/(2^{1024}-1)\rceil\le p\le\lfloor\sqrt N\rfloor$. Search the first $2^{20}$ continued-fraction steps of $\sqrt{4N}$, remove small square factors from the negative norms, and greedily select 16 pairwise coprime moduli $d_i$ in increasing order. Each is 3 modulo 4 and comes with a public integer $a_i$ satisfying $N\mid a_i^2+d_i$. Quadratic reciprocity forces the Jacobi symbol $(p/d_i)$ to equal $+1$ for every selected modulus. The search used only the input product. [Selection and reproduction](../experiments/many_character_window.py) · [Factor inclusion](../PrimeFactors/ReciprocalDivisorClasses.lean)

## Counting positions over a finite interval

Within one of the sixteen possible remainders modulo 60, suppose $L$ positions are available and $h$ pass all $k$ tests. Denote the signs at a position $x$ by $\chi_i(x)$. Every passing position contributes $(t+k)^2$ to $\sum_x(t+\sum_i\chi_i(x))^2$. The other contributions are nonnegative. Since each sign has square at most one, expanding gives

$$
(t+k)^2h\ \le\ (t^2+k)L+2t\sum_i U_i+\sum_{i\ne j}U_{ij},
$$

where $U_i$ and $U_{ij}$ bound the signed sums of the individual characters and their products over the progression. No independence assumption enters this inequality. Pairwise coprimality and the mod-4 condition ensure each off-diagonal product is a nonprincipal character. The explicit Pólya–Vinogradov bound of Frolenkov and Soundararajan applies to these characters and covers imprimitive ones. It is an unconditional published theorem. Our Lean proof takes its stated interval inequality as a hypothesis. [Finite second-moment proof](../PrimeFactors/CharacterWindowMoment.lean) · [Character bounds](../PrimeFactors/CharacterProductBound.lean) · [Frolenkov and Soundararajan](https://doi.org/10.1007/s11139-012-9462-y)

The calculation rounds each $\sqrt{d_i}$ up to an integer $r_i$. The pair errors are bounded by a common constant times $(\sum_i r_i)^2-\sum_i r_i^2$. Among the integer shifts from 0 to 16, $t=1$ minimized the resulting upper bound on both inputs. The final inequality includes the incomplete ends of all sixteen progressions. The Lean receipts check the interval endpoints, exact number of original positions, 32 public roots across the two inputs, coprimality, and the two rounded fractions. Reproduce the search with `python3 -m experiments.many_character_window`. After `lake build`, verify the archived results with `python3 -m experiments.many_character_receipt --verify`. [Complete window proof](../PrimeFactors/CharacterWindowRate.lean) · [Receipt generator](../experiments/many_character_receipt.py)
