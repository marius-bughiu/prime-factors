# When exchanging two blocks reveals both primes

Suppose the two factors use the same two blocks in reverse order. For instance, in radix 31 the blocks 17 and 30 give the primes $31\cdot17+30=557$ and $31\cdot30+17=947$. Starting with **527,479 and the radix**, division and two ordinary integer square roots recover both blocks. The multiplication can have carries. [Quotient formula and checked example](../PrimeFactors/TransposedBlockQuotient.lean)

## How the product gives the blocks

Write the putative factors as $Ba+b$ and $Bb+a$, with $0<a<b<B$. Their product satisfies

$$N=(B+1)^2ab+B(b-a)^2.$$

Let $T=\lfloor N/(B+1)^2\rfloor$. Since $b-a<B$, the unknown block product lies in the short interval $T-B<ab\le T$. Its remainder modulo $B$ is the public remainder $N\bmod B$. Exactly one integer in that interval has this remainder. For the worked example, $T=515$, and $N\bmod31=14$. The integer is **510**. Then

$$(b-a)^2=\frac{N-(B+1)^2\cdot510}{B}=169,\qquad (a+b)^2=169+4\cdot510=2209.$$

The square roots are 13 and 47, giving blocks $(47-13)/2=17$ and $(47+13)/2=30$. Reassemble the two numbers and check their product. Lean proves this returns exactly the positive, distinct reversed-block pairs at the selected radix. The same proof handles odd and even radices. [Recovery and converse](../PrimeFactors/TransposedBlockQuotient.lean)

There is a second formula for even $B$ and odd blocks. The identity $N=4B((a+b)/2)^2+(B-1)^2ab$ gives the exact square $((a+b)/2)^2$ as the least remainder of $N/(4B)$ modulo $(B-1)^2$. The division here uses a modular inverse, which exists for every even radix. Both square roots used by this version have radicands below $(B-1)^2$. At radix 32, it gives $790{,}037=829\cdot953$ and rejects $789{,}827=797\cdot991$. [Even-radix proof and matched controls](../PrimeFactors/TransposedRadixProducts.lean)

## A 2,048-bit product recovered from its two blocks

We chose $B=2^{512}$ and constructed two 512-bit blocks $a=1+6048F$ and $b=1+7920F$, with $F=2^{499}$. Both $Ba+b$ and $Bb+a$ are 1,024-bit primes, and their product has 2,048 bits. A separate replay reads only the decimal product, sets the block width to one quarter of its bit length, and applies the quotient formula. Both returned factors passed an independent Lean primality and product check. The correction $T-ab$ exceeds $2^{507}$ here, so the multiplication has substantial carries. [Exact decimal input and outputs](../benchmarks/transposed-blocks.json) · [Both recognition proofs and prime certificates](../PrimeFactors/FullWidthTransposedFixture.lean) · [Replay from the product](../experiments/transposed_block_receipt.py)

On this particular product ordinary Fermat search first succeeds strictly between tests $2^{1016}$ and $2^{1017}$. The construction also makes an easier comparison possible. Given the planted value of $F$ and the block pattern, the public quantity $((N-1)/F)\bmod F$ determines $6048+7920$ and thus the prime sum. To select the example we tested 500,717 pairs in lexicographic order, with $5800\le i\le6200$ and $i+256\le j\le8191$. Of these, 26,458 passed a sieve at the odd primes through 997. Four pairs passed both base-two Fermat tests, and the reported pair was the first for which the repository's default routines supplied both primality certificates. [Fermat rank, first hit and second shortcut](../PrimeFactors/FullWidthTransposedFixture.lean)

## How often can the radix help?

Count each pair of distinct 1,024-bit primes with a 2,048-bit product once. At a fixed even radix the fraction covered is below $2^{-1008}$. Each matching pair uses two prime entries, and reversing the blocks of either entry determines its only possible partner. Trying **every binary block width** raises the upper bound to less than $2^{-1006}$. For wider blocks the two leading digits have to be much smaller, which limits what the extra widths can add. These bounds are unconditional. [Prime counts and the sum over widths](../PrimeFactors/TransposedBlockPopulation.lean)

Even if every positive integer radix is available, including odd ones, **fewer than one in $2^{490}$** eligible products can be recovered this way. For smaller radices, reversing the digits still assigns at most one partner to each prime. At larger radices, keeping both words below $2^{1024}$ leaves fewer choices for the two digits. Summing these two bounds covers all possible radix choices, including a choice tailored to each product. [All-radix coverage proof](../PrimeFactors/ArbitraryRadixTransposePopulation.lean)

At most one binary block width can work for a given pair. If width $k$ works then $2^k-1$ divides the gap between the primes. For two eligible widths the least common multiple of those divisors would exceed the entire available gap. [Uniqueness across binary widths](../PrimeFactors/BinaryTransposeUniqueness.lean)

There is a faster rejection for binary widths $k\ge683$ in the full-size range. The coefficients $ab,a^2+b^2,ab$ then fit as three separate base-$2^k$ digits without a carry. The first and last $2(1024-k)$ bits of a qualifying 2,048-bit product must agree. At a smaller scale, the 26-bit product $43{,}431{,}077=5{,}647\cdot7{,}691$ starts and ends with the byte 165. Changing the second prime to 7,699 gives first and last bytes 165 and 29, ruling out the same width. The general connection between carry-free multiplication and digit reversal also appears in work by Ezerman, Meyer and Solé. [Lean screen and both examples](../PrimeFactors/TransposedProductDigits.lean) · [On Polynomial Pairs of Integers](https://cs.uwaterloo.ca/journals/JIS/VOL18/Ezerman/eze3.pdf)

## What if only divisibility of the sum and gap is known?

Take fixed positive coprime integers $u,v$. Suppose the midpoint $(p+q)/2=uc$ and the half-gap $(q-p)/2=ve$. The product then satisfies $N+v^2e^2=u^2c^2$. The least remainder of $-N/v^2$ modulo $u^2$ gives $e^2\bmod u^2$. When $e<u$, it gives $e^2$ itself. For larger $e$ the correct lift has index $\lfloor e^2/u^2\rfloor$. This gives an exact count of how many lifts an increasing search would need to reach that square. [Residue and lift proofs](../PrimeFactors/SumGapDivisorReadout.lean)

At $u=11,v=7$ the first remainder for $37{,}979$ is 25. The half-gap is $7\sqrt{25}=35$, and $\sqrt{37{,}979+35^2}=198$ gives the primes **163 and 233**. For $536{,}113$ the first remainder is 23. One more lift gives $23+121=144$, revealing the primes **653 and 821**. These examples were chosen to satisfy the divisibility conditions. For fixed $u,v$ fewer than one in $2^{1007}$ eligible full-size products satisfies both conditions with $e<u$. Fixing the smaller prime forces $e$ into one residue class modulo $u$, so there is at most one such partner. [Counts, assumptions and extension to longer intervals](../PrimeFactors/SumGapDivisorPopulation.lean)

## When three blocks are reversed

For a three-block word $aB^2+bB+c$ and its reverse, assume $0<a<c$ and $a^2+b^2+c^2<B$. The product then has five digits $A,D,C,D,A$, where $A=ac$, $D=b(a+c)$ and $C=a^2+b^2+c^2$. The square roots of $C+2A+2D$ and $C+2A-2D$ give $a+b+c$ and $|a+c-b|$. These identify the unordered pair of values $b$ and $a+c$. For each assignment of the two values, the outside digits follow from one more square-root test. At most four ordinary roots are needed altogether. If either word is prime, only one assignment can produce a distinct valid digit triple. [Recovery, two-candidate bound and uniqueness](../PrimeFactors/ThreeBlockReversal.lean)

The product $172{,}659{,}841$ at radix 61 gives the single triple $(3,4,4)$ and the primes **11,411 and 15,131**. At radix 512 the composite example $1{,}048{,}048{,}107{,}535$ admits both $(1,8,15)$ and $(3,16,5)$, giving different pairs of composite factors. The no-carry assumption is restrictive. At radix $2^k$ for $k\ge2$, both words have fewer than $3k$ bits under this condition. [Checked controls and bit-width limit](../PrimeFactors/ThreeBlockReversal.lean)
