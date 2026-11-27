# Can short character averages reveal the primes?

For the product 143, one exact average equals $51/25$. That number tells us the two primes add to 24, which gives 11 and 13. We can prove the same decoding formula for arbitrarily large primes. The open question is how to obtain the average from the product alone. Even the number of objects in the average already determines both factors. [Decoding proof and precision bound](../PrimeFactors/PrimitiveEvenMean.lean)

## What is being averaged?

A Dirichlet character assigns complex values to integers, respects multiplication, and repeats modulo its conductor. For $N=pq$ with distinct odd primes, a primitive character of conductor $N$ is a product of two nonprincipal local characters, one at each prime. There are $T=(p-2)(q-2)$ such pairs. A pair is even when its value at $-1$ is $+1$, and odd when that value is $-1$. Lean takes the pairs of local characters as its family. The identification with primitive characters is the usual decomposition for a squarefree conductor. The finite sums here use classical character orthogonality. [Character family and kernels](../PrimeFactors/PrimitiveCharacterParityMoment.lean) · [Conrey, Iwaniec and Soundararajan, equation (1.3) and primitive characters](https://arxiv.org/pdf/1105.1176#page=2)

For each pair $\chi$, set $X=|1+\chi(2)|^2$. Let $U=T+1=N+5-2(p+q)$. For $p,q>8$, the even family has $U/2$ members and the odd family has $(U-2)/2$. The exact averages are

| Average | Even family | Odd family |
| --- | --- | --- |
| $X$ | $2+4/U$ | $2$ |
| $X^2$ | $6+20/U$ | $6$ |

At 143 the even family has 50 members, its $X$ values sum to 102, and the average is $51/25$. Subtracting two and taking $4/(51/25-2)$ gives $U=100$. Hence $p+q=(143+5-100)/2=24$. The discriminant is $24^2-4\cdot143=4$. Direct use of the known factors gives an independent check of the average. [Even and odd means](../PrimeFactors/PrimitiveParityAverages.lean) · [Worked example and decoder](../PrimeFactors/PrimitiveParityReadout.lean)

## How much precision would this require?

Consider two candidate sums separated by four at a fixed product. Their $U$ values differ by eight, and the corresponding means differ by $32/[U(U+8)]$. Across our balanced 2,048-bit population, $U\ge 2^{2046}$, so this difference is smaller than $2^{-4087}$. This comparison concerns two candidate sums during the search. The product itself has a unique prime factorization. [Spacing theorem](../PrimeFactors/PrimitiveEvenMean.lean)

The even-family variance is $2+4/U-16/U^2>2$. Even granting independent uniform samples from the correct even family, an ordinary mean of $m$ samples has root-mean-square error greater than $\sqrt{2/m}$. Bringing that error below $2^{-4087}$ would require more than $2^{8175}$ samples. This calculation applies to this estimator. An identity that evaluated the average exactly without enumerating the family would face a different question. [Variance proof](../PrimeFactors/PrimitiveEvenMean.lean)

Choosing different weights on the short inputs also has a limit. Write $D=\sum|a_n|^2$ for their total squared magnitude and $C=|\sum a_n|^2$. The even mean of $|P|^2$ is $D+2(C-D)/U$, and the odd mean is exactly $D$. With at most $2^{21}$ distinct positive indices and every pair of indices summing to less than either prime, the even mean is within $D/2^{2024}$ of $D$ for a balanced 2,048-bit product. Changing $U$ by eight changes the prediction by at most $D/2^{4067}$. These bounds allow arbitrary complex weights. They follow from $C\le mD$ for $m$ weights, with equality for constant weights. [Uniform bound for the actual even-family mean](../PrimeFactors/PrimitiveParityPrecision.lean)

## What cancels at the small inputs suggested by GRH?

Start with any finite weighted sum $P(\chi)=\sum_n a_n\chi(n)$ supported on positive integers through $B$. Add $|P(\chi)|^{2k}$ over the even family and subtract its sum over the odd family. If $2B^k<\min(p,q)$, the answer is exactly $|\sum_n a_n|^{2k}$. All dependence on the hidden prime pair disappears from this particular signed total. Expanding the powers reduces the proof to terms with two indices $u,v\le B^k$. Neither prime can divide $u+v$, and ordinary orthogonality with the principal character removed gives a contribution of one. [General moment proof](../PrimeFactors/PrimitiveCharacterParityMoment.lean)

The small-input range matters because Lamzouri, Li and Soundararajan give a prime at most $(\log N)^2$ outside any given proper subgroup under their Dirichlet GRH hypotheses. A product of two 1,024-bit primes meets the small-prime-divisor condition, and $(\log N)^2<2^{21}$ at 2,048 bits. Lean proves that even allowing *every* positive index through $2^{21}$, *every* choice of weights, and all even powers through 96 gives the same signed totals described above. The finite cancellation proof is unconditional. The recently checked Dirichlet results motivate the choice of input range. [Least-prime theorem 1.1(2)](https://arxiv.org/pdf/1309.3595#page=2) · [Verification of the shorter RH and Dirichlet GRH proofs](https://math.mit.edu/~drew/shortgrh/) · [Full-size finite theorem](../PrimeFactors/PrimitiveCharacterParityMoment.lean)

The cutoff can matter. At $77=7\cdot11$, use $P=\chi(3)+\chi(4)$. The signed sum of $|P|^2$ is $-8$. The short-input formula would give $4$. Here $3+4=7$ reaches the smaller prime, and the two cross terms change from $+1$ to $-5$. In this example a single gcd of 7 with 77 already gives the same factor. [Lean boundary example](../PrimeFactors/PrimitiveCharacterParityMoment.lean)

## One longer sum that does determine the answer

Choose $B=\lfloor\sqrt{N/2}\rfloor$ from the product and give every integer from 1 through $B$ weight one. Let $V$ be the even-minus-odd total of the squared magnitude of that sum. For distinct primes $p<q<2p$, the factor sum is

$$p+q=B+1+\sqrt{V+2N-2B-1}.$$

At $143$, the cutoff is 8 and the unweighted baseline is $8^2=64$. Six ordered pairs of indices sum to 11, lowering the total by $6\cdot10$. Four sum to 13, lowering it by another $4\cdot12$. This gives $V=-44$. The formula returns $9+\sqrt{225}=24$. The two groupings explain where the information resides. One can group the $B^2$ terms by the public index sum and check its gcd with $N$. At full size $B\ge 2^{1023}$, and any nontrivial gcd encountered already gives a factor. Any existing factoring method also gives the total through this identity. The open question is whether evaluating the total independently can save work over factoring first. [Interval identity, count and inverse](../PrimeFactors/PrimitiveIntervalMoment.lean)

For odd primes the sum is known modulo four. That spacing lets us decode an *approximation* to the long total. At 143, every integer reading from $-96$ through $23$ gives the correct sum 24 under the stated tie rule. At full size an absolute error at most $2^{1025}$ suffices. Although that is a large error in integer units, choosing random index pairs almost always returns the baseline. Among $2^{64}$ independent uniform draws with replacement, the chance of seeing even one changed term is at most $2^{-958}$. At 143 the corresponding one-draw probability is $10/64$. These counts concern this particular sampling strategy. [Rounding and recovery](../PrimeFactors/PrimitiveIntervalPrecision.lean) · [Finite sampling proof](../PrimeFactors/PrimitiveIntervalSampling.lean)

This gives a two-way reduction on the balanced odd-semiprime family. From the primes, evaluate the integer expression for $V$ directly. From an integer within $4B$ of $V$, one integer square root and a remainder modulo four give the sum. A second integer square root recovers the gap and hence the primes. Both conversions take a fixed number of arithmetic operations on integers of size comparable to $N$. The missing operation is the approximation at a single supplied product. [Exact value](../PrimeFactors/PrimitiveIntervalMoment.lean) · [Uniform $4B$ tolerance](../PrimeFactors/PrimitiveIntervalPrecision.lean)

Tóth’s weighted gcd identity also evaluates this sum exactly when the divisors of $N$ are known. In the triangular interval only the unknown divisors $p$ and $q$ can contribute a change from the baseline. Averaging gcds over the complete period introduces a measurable error. At 143 the exact weighted gcd total is 172. The full-period mean is $525/143$, so multiplying it by 64 gives an error of $9004/143$, exceeding the guaranteed tolerance of 32. Published estimates that sum over many moduli answer a different averaging question. For a direct comparison on 143, testing the odd integers from $B+1$ to $\lfloor\sqrt{N}\rfloor$ takes just the gcds at 9 and 11. [Tóth, Proposition 1(i)](https://cs.uwaterloo.ca/journals/JIS/VOL14/Toth/toth9.pdf#page=2) · [Sums of Averages of GCD-Sum Functions II, equation (1)](https://link.springer.com/article/10.1007/s00025-021-01357-x#Sec1)
