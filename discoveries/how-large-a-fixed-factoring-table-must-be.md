# How large must a fixed factoring table be?

There is a list of 1,022 integers, fixed in advance, such that at least one of their gcds with any eligible 2,048-bit product gives a prime factor. The cost lies in the integers on the list. Lean proves that **every** fixed list with this guarantee needs more than $2^{1021}$ bits in total if its entries are written out in binary. A short description of the list is possible. Evaluating the described integers modulo the input is the open computational step. [Construction and storage lower bound](../PrimeFactors/FixedDivisorSignatures.lean)

## The construction

Set $B=2^{1023}$. Both unknown primes lie between $B$ inclusive and $2B$ exclusive. Within that interval, the only multiple of either prime is the prime itself. A product of candidates is therefore divisible by a hidden prime exactly when that prime was included.

For each bit $j$ of $\lfloor(x-B)/2\rfloor$, take the product of all integers $x$ in the interval for which that bit is one. Distinct odd primes have distinct values of $\lfloor(x-B)/2\rfloor$, and these values fit in 1,022 bits. At their first differing bit, one prime divides the corresponding product and the other does not. Taking a gcd with $N$ returns that prime. The formula uses only the endpoints and the index $j$ to describe each constant. In the interval from 16 through 31 its second bit distinguishes 19 and 23, and the gcd with $437$ gives 23. [Bit test and checked example](../PrimeFactors/FixedDivisorSignatures.lean)

## Counting the information in the constants

Consider the 1,024-bit primes at least $283B/200$. Every two distinct primes in that set have a 2,048-bit product. For any table of $k$ fixed integers, record the $k$ yes/no answers to whether a prime divides each integer. Two primes with the same answers will give only gcds of one or of the entire product. Thus a successful table needs a different binary sequence for every one of those primes. The repository's elementary prime-count lower bound already implies $k\ge1012$. [Prime-count proof](../PrimeFactors/ChebyshevPrimeSample.lean)

At most one prime in this set can divide none of the positive table entries. Multiply all the entries together. Their product has to be divisible by every other prime in the set, each at least $2^{1023}$. Comparing binary lengths proves the storage bound above. Zero entries contribute no distinguishing information. The bound applies to tables whose answers are obtained by taking gcds with their fixed entries. It leaves open both input-dependent expressions and fast algorithms for evaluating a compressed product. [Finite proof, including zero entries](../PrimeFactors/FixedDivisorSignatures.lean)
