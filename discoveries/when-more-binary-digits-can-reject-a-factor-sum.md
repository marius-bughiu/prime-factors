# When more binary digits can reject a candidate factor sum

Two 30-bit products have exactly the same last 14 bits. On the first, checking 14 binary digits reduced **12 earlier candidate sums to two**. On the second, eight earlier sums passed, and Lean proved that **all eight survive at every binary precision**. The extra information in this experiment was the correct three-bit ending of one factor. The two products were selected to show both outcomes. [Certified inputs, exact candidate sets and search endpoints](../PrimeFactors/DyadicClueScanControls.lean)

| Product $N$ | Certified factors | Supplied factor mod 8 | True sum | Earlier sums after the fixed congruence | Earlier sums after the 14-bit test |
| ---: | --- | ---: | ---: | ---: | ---: |
| 623,706,113 | 20,873 × 29,881 | 1 | 50,754 | 12 | 2 |
| 623,493,121 | 20,347 × 30,643 | 3 | 50,990 | 8 | 8 |

Start at the smallest integer at least $2\sqrt N$ and stop just before the true sum. A sum $s$ passes at precision $e$ when some integer $x$ has the supplied ending and $x(s-x)\equiv N\pmod{2^e}$. In the first row the two earlier sums are **50,178 and 50,242**. In the second row the eight are exactly the earlier sums equal to 46 modulo 128. Independent Fermat runs, given only the two products, take 403 and 526 ordinary midpoint tests respectively. Those midpoint counts measure a different search. [Formal search counts](../PrimeFactors/DyadicClueScanControls.lean) · [Fermat benchmark inputs](../benchmarks/cases.json)

## One test decides whether to read more digits

Let $a$ be the supplied odd factor remainder modulo $2^k$, with $k\ge3$. Check whether $a^2\equiv N\pmod{2^{k+1}}$. This check uses the product and the supplied remainder only. For an actual factor $p$ and its partner $q$, the check succeeds exactly when $p$ and $q$ agree in their lowest $k+1$ bits. [Square-root criterion and actual-factor equivalence](../PrimeFactors/SingularDyadicClueSuffixes.lean)

**If the check fails**, there is one congruence on the sum that captures every higher power-of-two test. In detail, let $t$ be the exact exponent of 2 in $a^2-N$. Then $t\le k$, and $aS\equiv a^2+N$ modulo $2^{k+t}$ if $t<k$, or modulo $2^{2k+1}$ if $t=k$. Every integer satisfying the congruence has modular factor witnesses at every finite binary precision, with the required factor ending. This proves when more digits eliminate zero candidates. [Equivalence at every precision](../PrimeFactors/DyadicClueFullSumClass.lean)

**If the check succeeds**, compute a square root $r$ of $N$ modulo the requested power $2^{2k+j}$ in the supplied factor class. Such a root exists at every depth. All permissible sums satisfy $s\equiv2r\pmod{2^{2k}}$. Write $s=2r+2^{2k}h$. The exact next test is whether **$rh$ is a square modulo $2^j$**. Completing the square in $x(s-x)=N$ gives this criterion. A unit equal to 1 modulo 8 has a square root at every power of two, which is where $k\ge3$ enters. [Square test and count of distinct sum lifts](../PrimeFactors/DyadicClueSquareBranch.lean)

Exactly **44 of the 256** ways to extend the fixed sum remainder by eight more bits pass in this case. More generally the number of passing extensions is $(2^j+8)/6$ for even $j\ge2$ and $(2^j+10)/6$ for odd $j\ge1$. Thus the surviving fraction approaches one sixth from above. These counts apply within the specified sum class for each product and factor suffix satisfying the check. [Square-residue count](../PrimeFactors/DyadicSquareValueCount.lean)

## How much searching remains at 2,048 bits?

Grant the true 160-bit ending of one prime and allow **all** power-of-two tests. For all but fewer than one in $2^{35}$ eligible prime pairs, the ascending scan still encounters **at least $2^{577}$ wrong sums** before the correct sum. This is an unconditional count on distinct 1,024-bit primes whose product has 2,048 bits. The bound concerns a scan that visits the surviving sums in numerical order. [Full-population bound](../PrimeFactors/AllDyadicClueScanFloor.lean)

The proof finds a complete residue class where every sum passes every binary test. One of the two one-bit extensions of any given factor ending always admits such a class. The guaranteed spacing is $2^{2k+3}$, which for $k=160$ leaves at least one survivor in each full block of $2^{323}$ consecutive sums. For product remainders 3 or 7 modulo 8, the exact spacing is $2^{161}$. For remainder 5 it is $2^{162}$. Outside the same small exceptional set these give at least $2^{739}$ and $2^{738}$ earlier wrong sums respectively. The fraction $2^{-35}$ uses the entire eligible population as denominator. [Persistent class](../PrimeFactors/DyadicCluePersistentClass.lean) · [Exact counts for three product remainders](../PrimeFactors/FullDyadicClueScan.lean)

When the supplied ending contains a square root of $N$ at every binary precision, $2^{2k+3}$ is the smallest power-of-two spacing for which an entire class survives. Try half that spacing and test $2k+4$ bits. Starting anywhere, at least one of the next three members fails. On the first product in the table, the 10-bit test accepts 50,178 and 50,434 and rejects 50,690. Successive candidates in this class differ by 256. At one bit less precision an entire class with that spacing can still pass. [Sharp spacing, first rejection depth and checked three-visit example](../PrimeFactors/SharpDyadicCluePeriod.lean)
