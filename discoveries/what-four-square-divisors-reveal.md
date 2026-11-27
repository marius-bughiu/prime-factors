# What four square divisors reveal about the factors

On the 39-bit product $419{,}636{,}024{,}497$, a single supplied clue picks out the true factor sum from 78,590 integers. For most eligible 2,048-bit products, even four correct clues leave at least $2^{514}$ sums compatible with the tests below. Each clue supplies a square divisor of a product such as $(p+1)(q+1)$. [Small example and certificate](../PrimeFactors/SquareDivisorClueWindow.lean) · [Four-clue count](../PrimeFactors/FourSquareDivisorClues.lean)

## A 39-bit example with supplied clues

With seed 20261127, the first draw of two distinct primes from the ordered list of all 38,635 20-bit primes gave $556{,}559$ and $753{,}983$. Their product has 39 bits. The experiment kept that first draw. Using the disclosed factors, it factored $p-1,p+1,q-1,q+1$ and found the largest square dividing each shifted product. The roots were 2 for $(p-1)(q-1)$, 288 for $(p+1)(q+1)$, 24 for $(p-1)(q+1)$ and 12 for $(p+1)(q-1)$. The sum tests received only the product and those four labeled roots. [Seed, factorizations and counts](../benchmarks/square-divisor-clue-window.json) · [Replay](../experiments/square_divisor_clue_window.py)

| Test applied | Sums left |
| --- | ---: |
| Basic balanced interval, 1,295,587 through 1,374,176 | 78,590 |
| Correct remainder modulo four | 19,647 |
| Both same-sign clues | 1 |
| Both mixed-sign clues as well | 1 |
| Exact square discriminant | 1 |

The decisive clue was $288^2\mid(p+1)(q+1)$. Since $(p+1)(q+1)=N+1+S$, the sum $S$ must be 66,382 modulo 82,944. Only **1,310,542** has that remainder in the interval. Its discriminant is $197{,}424^2$, giving the two primes above. Lean verifies the factorization and proves uniqueness from that one clue alone. [Lean certificate](../PrimeFactors/SquareDivisorClueWindow.lean)

## Which sums count as compatible?

Write $N=pq$, $S=p+q$ and $G=q-p$ for odd primes $p<q<2p$. The basic sum window is $4N<s^2\le 9N/2$ for positive $s$. We keep even $s$ with $s\equiv N+1\pmod 4$. For each sign pair, the supplied positive integer $y$ means $y^2$ divides that particular shifted product. [Signed congruences and window definitions](../PrimeFactors/SquareDivisorClueWindow.lean)

| Shifted product | Test on a candidate sum $s$ |
| --- | --- |
| $(p-1)(q-1)$ | $s\equiv N+1\pmod{y^2}$ |
| $(p+1)(q+1)$ | $s\equiv -(N+1)\pmod{y^2}$ |
| $(p-1)(q+1)$ or $(p+1)(q-1)$ | Test $s^2-4N\equiv (N-1)^2\pmod{y^2}$ separately for each supplied root. |

The last two tests follow because the true discriminant is $G^2$ and the mixed clues give $G\equiv N-1$ or $G\equiv -(N-1)$ respectively. A compatible sum passes the listed window and remainder tests. Recovering factors still requires an integer square discriminant. Requiring each factor to have exactly 1,024 bits can also narrow the window. [Definition used in the four-clue proof](../PrimeFactors/FourSquareDivisorClues.lean)

## Bounds at 2,048 bits

Choose uniformly among sorted pairs of distinct 1,024-bit primes whose product has 2,048 bits. Each row gives a guarantee outside its own exceptional fraction. It holds for every valid choice of the supplied roots on such a pair, including the largest ones. [Exceptional fractions](../PrimeFactors/FourNeighborScaleFrequency.lean) · [Population and clue bounds](../PrimeFactors/SquareDivisorCluePopulation.lean)

| Clues supplied | Candidates guaranteed in the basic window | Fraction that can fall outside the guarantee |
| --- | --- | --- |
| One labeled square divisor | At least $2^{764}$ sums for matching signs, or $2^{767}$ positive gaps for mixed signs | Less than $2^{-77}$ |
| All four labeled square divisors | At least $2^{514}$ compatible sums | Less than $2^{-13}$ |
| All four labeled square divisors | At least $2^{258}$ compatible sums | Less than $2^{-45}$ |

For one mixed clue the gap window is $0<2g^2<N$ with $g>0$. The gap count retains its correct remainder modulo four and modulo the supplied square. For four clues, consider the sums sharing the true sum’s remainder modulo four and all four squares. Each passes the two sum tests, and squaring gives the required discriminant remainders. Counting this one arithmetic progression already gives the lower bounds. In the small example its modulus was 82,944 and it contained one sum. The experiment used the known sum only for this separate comparison. [Counting complete periods](../PrimeFactors/SquareDivisorClueWindow.lean) · [Common progression for four clues](../PrimeFactors/FourSquareDivisorClues.lean)
